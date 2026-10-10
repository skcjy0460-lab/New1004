# -*- coding: utf-8 -*-
"""
Wivo Daily News Intelligence Report
-----------------------------------
지정한 날짜 · 카테고리의 한국 뉴스를 수집 → 원문 검증 → AI 요약 → HTML A4 보고서로 생성합니다.

핵심 원칙
1. 기사 "발견"은 검색/피드(Google News RSS, Naver 검색 API)로 하고, AI가 기사를 지어내지 않습니다.
2. 모든 기사는 원문 페이지에 실제 접속해 발행일·기자명·본문을 직접 추출/검증합니다.
3. AI(Gemini)는 "추출된 원문 본문"만 근거로 요약하며, 추측/전망/칼럼/광고성 기사는 제외합니다.
4. 보고서에는 원문 URL · 언론사 · 기자명 · 발행일이 반드시 표기됩니다.
"""
from __future__ import annotations

import base64
import difflib
import hmac
import html
import io
import json
import re
import time
import xml.etree.ElementTree as ET
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta
from email.utils import parsedate_to_datetime
from pathlib import Path
from typing import Any, Callable
from urllib.parse import quote_plus, urlparse
from zoneinfo import ZoneInfo

import requests
import streamlit as st
import streamlit.components.v1 as components
from bs4 import BeautifulSoup

try:
    import trafilatura
except Exception:  # pragma: no cover
    trafilatura = None
try:
    from googlenewsdecoder import gnewsdecoder
except Exception:  # pragma: no cover
    gnewsdecoder = None
try:
    from dateutil import parser as dateparser
except Exception:  # pragma: no cover
    dateparser = None
try:
    from google import genai
    from google.genai import types as gtypes
except Exception:  # pragma: no cover
    genai = None
    gtypes = None

# ──────────────────────────────────────────────────────────────────────────────
# 상수
# ──────────────────────────────────────────────────────────────────────────────
APP_TITLE = "Wivo 뉴스 인텔리전스 리포트"
KST = ZoneInfo("Asia/Seoul")
BASE_DIR = Path(__file__).parent
LOGO_PATH = BASE_DIR / "assets" / "wivo_logo.png"
WEEK = "월화수목금토일"
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept-Language": "ko-KR,ko;q=0.9,en;q=0.5",
}
DEFAULT_MAIN_MODEL = "gemini-3.6-flash"
DEFAULT_LIGHT_MODEL = "gemini-3.5-flash-lite"
FALLBACK_MODELS = ["gemini-2.5-flash", "gemini-2.0-flash"]

# 카테고리 프리셋: 이름 → 검색 키워드(여러 개를 돌려가며 수집해 다양성 확보)
PRESETS: dict[str, list[str]] = {
    "경제": ["경제", "코스피 증시", "금리 환율", "물가 부동산", "기업 실적"],
    "의료": ["의료 병원", "보건복지부 의료", "건강보험 수가", "제약 바이오 식약처", "의사 의대"],
    "연예계": ["연예", "가수 컴백 음원", "드라마 시청률", "영화 개봉 관객", "배우 출연"],
    "스포츠": ["스포츠", "프로야구 KBO", "프로축구 K리그", "농구 배구", "골프 올림픽"],
    "정치": ["정치", "국회 여야", "대통령실"],
    "사회": ["사회 사건", "교육 학교", "노동 고용"],
    "IT·과학": ["IT 인공지능", "반도체 전자", "과학 우주"],
    "국제": ["국제 뉴스", "미국 중국", "일본 유럽"],
}

NAME_BLACKLIST = {
    "편집", "뉴스", "디지털", "온라인", "취재", "사진", "영상", "특별", "본사", "자료",
    "데스크", "제보", "연합", "속보", "종합", "인턴", "무단", "저작", "배포", "금지",
    "이메일", "기자", "서울", "경제", "정치", "사회", "문화", "스포츠", "산업", "금융",
}
TITLE_SUFFIX = r"(선임기자|수습기자|전문기자|논설위원|편집위원|특파원|기자|위원)"


# ──────────────────────────────────────────────────────────────────────────────
# 데이터 구조
# ──────────────────────────────────────────────────────────────────────────────
@dataclass
class Article:
    category: str
    title: str
    url: str
    outlet: str = ""
    published: datetime | None = None
    pub_basis: str = ""
    reporter: str = ""
    body: str = ""
    coverage: int = 1
    summary: str = ""
    detail: list[str] = field(default_factory=list)
    key_points: list[dict] = field(default_factory=list)
    numbers: list[dict] = field(default_factory=list)
    quotes: list[str] = field(default_factory=list)
    importance: int = 5
    subtopic: str = ""
    article_type: str = ""
    no: int = 0


@dataclass
class Category:
    name: str
    keywords: list[str]


@dataclass
class Config:
    target: date
    categories: list[Category]
    per_cat: int
    strict_reporter: bool
    sources: list[str]
    exclude: list[str]
    main_model: str
    light_model: str
    api_key: str
    naver_id: str = ""
    naver_secret: str = ""
    oversample: int = 3


# ──────────────────────────────────────────────────────────────────────────────
# 공통 유틸
# ──────────────────────────────────────────────────────────────────────────────
def esc(x: Any) -> str:
    return html.escape("" if x is None else str(x), quote=True)


def secret(name: str, default: Any = None) -> Any:
    try:
        return st.secrets[name]
    except Exception:
        return default


def parse_dt(s: str | None) -> datetime | None:
    if not s:
        return None
    s = s.strip()
    dt = None
    try:
        dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
    except Exception:
        if dateparser is not None:
            try:
                dt = dateparser.parse(s)
            except Exception:
                dt = None
        if dt is None:
            m = re.search(r"(\d{4})[.\-/년\s]+(\d{1,2})[.\-/월\s]+(\d{1,2})(?:[일\sT]+(\d{1,2}):(\d{2}))?", s)
            if m:
                y, mo, d, hh, mm = m.groups()
                try:
                    dt = datetime(int(y), int(mo), int(d), int(hh or 0), int(mm or 0))
                except ValueError:
                    dt = None
    if dt is None:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=KST)
    return dt.astimezone(KST)


def norm_title(t: str) -> str:
    return re.sub(r"[^0-9A-Za-z가-힣]", "", t or "")


def clean_title(title: str, outlet: str = "") -> str:
    t = re.sub(r"<[^>]+>", "", html.unescape(title or "")).strip()
    if outlet and t.endswith(f" - {outlet}"):
        t = t[: -len(f" - {outlet}")].strip()
    else:
        m = re.match(r"^(.*)\s-\s([^-]{1,20})$", t)
        if m and (not outlet or m.group(2).strip() == outlet):
            t = m.group(1).strip()
    return t


def domain_of(url: str) -> str:
    try:
        return urlparse(url).netloc.replace("www.", "")
    except Exception:
        return ""


# ──────────────────────────────────────────────────────────────────────────────
# 1) 기사 발견 (Google News RSS / Naver 검색 API)
# ──────────────────────────────────────────────────────────────────────────────
def fetch_google_news(keyword: str, target: date, category: str, limit: int = 50) -> list[Article]:
    d0 = (target - timedelta(days=1)).isoformat()
    d1 = (target + timedelta(days=2)).isoformat()  # 경계 시간대 오차 보정, 이후 KST 일자로 재필터
    q = f"{keyword} after:{d0} before:{d1}"
    url = f"https://news.google.com/rss/search?q={quote_plus(q)}&hl=ko&gl=KR&ceid=KR:ko"
    r = requests.get(url, headers=HEADERS, timeout=20)
    r.raise_for_status()
    root = ET.fromstring(r.content)
    out: list[Article] = []
    for it in root.iter("item"):
        link = (it.findtext("link") or "").strip()
        src = it.find("source")
        outlet = (src.text or "").strip() if src is not None else ""
        title = clean_title(it.findtext("title") or "", outlet)
        pub = None
        try:
            pub = parsedate_to_datetime(it.findtext("pubDate")).astimezone(KST)
        except Exception:
            pub = None
        if pub is not None and pub.date() != target:
            continue
        if link and title:
            out.append(Article(category=category, title=title, url=link, outlet=outlet,
                               published=pub, pub_basis="뉴스 피드(RSS)" if pub else ""))
        if len(out) >= limit:
            break
    return out


def fetch_naver_news(keyword: str, target: date, category: str, cid: str, csecret: str) -> list[Article]:
    out: list[Article] = []
    for start in (1, 101, 201):
        r = requests.get(
            "https://openapi.naver.com/v1/search/news.json",
            params={"query": keyword, "display": 100, "start": start, "sort": "date"},
            headers={"X-Naver-Client-Id": cid, "X-Naver-Client-Secret": csecret},
            timeout=15,
        )
        r.raise_for_status()
        items = r.json().get("items", [])
        if not items:
            break
        oldest = None
        for it in items:
            try:
                pub = parsedate_to_datetime(it.get("pubDate")).astimezone(KST)
            except Exception:
                continue
            oldest = pub if oldest is None or pub < oldest else oldest
            if pub.date() != target:
                continue
            link = it.get("originallink") or it.get("link") or ""
            if not link.startswith("http"):
                continue
            out.append(Article(category=category, title=clean_title(it.get("title", "")), url=link,
                               outlet=domain_of(link), published=pub, pub_basis="뉴스 피드(Naver)"))
        if oldest is not None and oldest.date() < target:
            break  # 더 과거로 넘어가면 이후 페이지는 불필요
    return out


def discover(cat: Category, cfg: Config, log: Callable[[str], None]) -> list[Article]:
    per_query: list[list[Article]] = []
    for kw in cat.keywords:
        items: list[Article] = []
        if "google" in cfg.sources:
            try:
                items += fetch_google_news(kw, cfg.target, cat.name)
            except Exception as e:
                log(f"  · Google News 조회 실패({kw}): {type(e).__name__}")
        if "naver" in cfg.sources and cfg.naver_id and cfg.naver_secret:
            try:
                items += fetch_naver_news(kw, cfg.target, cat.name, cfg.naver_id, cfg.naver_secret)
            except Exception as e:
                log(f"  · Naver 조회 실패({kw}): {type(e).__name__}")
        per_query.append(items)
    merged: list[Article] = []  # 키워드별 라운드로빈 → 한 주제 쏠림 방지
    i = 0
    while any(i < len(q) for q in per_query):
        for q in per_query:
            if i < len(q):
                merged.append(q[i])
        i += 1
    ex = [e.lower() for e in cfg.exclude if e]
    if ex:
        merged = [a for a in merged if not any(e in (a.outlet or "").lower() or e in a.url.lower() for e in ex)]
    return merged


def cluster_articles(arts: list[Article], thr: float = 0.62) -> list[list[Article]]:
    clusters: list[dict] = []
    for a in arts:
        nt = norm_title(a.title)
        if len(nt) < 6:
            continue
        for c in clusters:
            if difflib.SequenceMatcher(None, nt, c["key"]).ratio() >= thr:
                c["items"].append(a)
                break
        else:
            clusters.append({"key": nt, "items": [a]})
    clusters.sort(key=lambda c: -len({x.outlet for x in c["items"]}))
    return [c["items"] for c in clusters]


# ──────────────────────────────────────────────────────────────────────────────
# 2) 원문 접속 · 검증 (발행일 / 기자명 / 본문)
# ──────────────────────────────────────────────────────────────────────────────
def _decode_google_builtin(u: str) -> str | None:
    """googlenewsdecoder 패키지 없이 Google News 링크를 원문 URL로 변환 (내장 디코더)."""
    gid = urlparse(u).path.rstrip("/").split("/")[-1]
    if not gid:
        return None
    # 구형 포맷: base64 안에 URL이 그대로 들어있음
    try:
        raw = base64.urlsafe_b64decode(gid + "=" * (-len(gid) % 4))
        if raw.startswith(b"\x08\x13\x22") and raw.endswith(b"\xd2\x01\x00"):
            raw = raw[3:-3]
            ln = raw[0]
            raw = raw[2:] if ln >= 0x80 else raw[1:]
            cand = raw.decode("utf-8", "ignore")
            if cand.startswith("http") and not cand.startswith("AU_yq"):
                return cand
    except Exception:
        pass
    # 신형 포맷: batchexecute 호출
    sig = ts = None
    for page in (f"https://news.google.com/articles/{gid}", f"https://news.google.com/rss/articles/{gid}"):
        try:
            r = requests.get(page, headers=HEADERS, timeout=15)
            div = BeautifulSoup(r.text, "html.parser").select_one("c-wiz > div[jscontroller]")
            if div and div.get("data-n-a-sg") and div.get("data-n-a-ts"):
                sig, ts = div["data-n-a-sg"], div["data-n-a-ts"]
                break
        except Exception:
            continue
    if not sig:
        return None
    inner = ('["garturlreq",[["X","X",["X","X"],null,null,1,1,"US:en",null,1,null,null,null,null,null,0,1],'
             f'"X","X",1,[1,1,1],1,1,null,0,0,null,0],"{gid}",{ts},"{sig}"]')
    body = "f.req=" + quote_plus(json.dumps([[["Fbv4je", inner]]]))
    try:
        r = requests.post(
            "https://news.google.com/_/DotsSplashUi/data/batchexecute",
            headers={"Content-Type": "application/x-www-form-urlencoded;charset=UTF-8",
                     "User-Agent": HEADERS["User-Agent"]},
            data=body, timeout=15)
        parsed = json.loads(r.text.split("\n\n")[1])[:-2]
        url = json.loads(parsed[0][2])[1]
        return url if str(url).startswith("http") else None
    except Exception:
        return None


def resolve_google_url(u: str) -> str | None:
    if "news.google.com" not in u:
        return u
    if gnewsdecoder is not None:
        try:
            res = gnewsdecoder(u, interval=0.2)
            if res.get("status") and res.get("decoded_url"):
                return res["decoded_url"]
        except Exception:
            pass
    for _ in range(2):
        out = _decode_google_builtin(u)
        if out:
            return out
        time.sleep(0.8)
    return None


def fetch_page(url: str) -> tuple[bytes, str]:
    r = requests.get(url, headers=HEADERS, timeout=20, allow_redirects=True)
    r.raise_for_status()
    return r.content, r.url


def jsonld_objects(soup: BeautifulSoup) -> list[dict]:
    out: list[dict] = []
    for s in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(s.string or s.get_text() or "")
        except Exception:
            continue
        stack = [data]
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                stack.extend(x)
            elif isinstance(x, dict):
                out.append(x)
                if "@graph" in x:
                    stack.append(x["@graph"])
    return out


def _names(a: Any) -> list[str]:
    if a is None:
        return []
    if isinstance(a, str):
        return [a]
    if isinstance(a, list):
        return [n for i in a for n in _names(i)]
    if isinstance(a, dict):
        return _names(a.get("name"))
    return []


def meta_content(soup: BeautifulSoup, keys: list[str]) -> list[str]:
    found = []
    lk = {k.lower() for k in keys}
    for m in soup.find_all("meta"):
        key = (m.get("property") or m.get("name") or m.get("itemprop") or "").lower()
        if key in lk and m.get("content"):
            found.append(m["content"].strip())
    return found


def extract_published(soup: BeautifulSoup, ld: list[dict]) -> datetime | None:
    keys = ["article:published_time", "og:article:published_time", "datepublished", "pubdate",
            "date", "dc.date.issued", "article:published", "og:regdate", "parsely-pub-date"]
    for v in meta_content(soup, keys):
        dt = parse_dt(v)
        if dt:
            return dt
    for o in ld:
        if o.get("datePublished"):
            dt = parse_dt(str(o["datePublished"]))
            if dt:
                return dt
    return None


def norm_name(raw: str, outlet: str = "") -> str | None:
    s = re.sub(r"\(.*?\)|\[.*?\]|<.*?>", "", raw or "").strip()
    s = re.sub(r"\S+@\S+", "", s).strip()
    s = re.sub(rf"\s*{TITLE_SUFFIX}\s*$", "", s).strip()
    if not re.fullmatch(r"[가-힣]{2,4}", s):
        return None
    if s in NAME_BLACKLIST or (outlet and s in outlet):
        return None
    return s


BYLINE_RE = re.compile(r"([가-힣]{2,4})\s*(?:선임|수습|전문|논설|편집)?\s*(?:기자|특파원)(?![가-힣])")


def extract_reporter(soup: BeautifulSoup, ld: list[dict], body: str, outlet: str) -> str:
    cands: list[str] = []
    for o in ld:
        cands += _names(o.get("author"))
    cands += meta_content(soup, ["author", "article:author", "dable:author", "byline", "og:article:author",
                                 "parsely-author", "sailthru.author"])
    for el in soup.select('[class*="byline"],[class*="reporter"],[class*="writer"],[class*="journalist"],'
                          '[class*="author"],[id*="byline"],[id*="reporter"]')[:12]:
        t = el.get_text(" ", strip=True)
        if 2 <= len(t) <= 80:
            cands.append(t)
    names: list[str] = []
    for c in cands:
        for part in re.split(r"[,/·&]|\s+and\s+", c):
            n = norm_name(part, outlet)
            if n is None:  # "홍길동 김철수 기자" 같은 복수 표기
                for m in BYLINE_RE.finditer(part):
                    n2 = norm_name(m.group(1), outlet)
                    if n2 and n2 not in names:
                        names.append(n2)
            elif n not in names:
                names.append(n)
    if not names and body:
        edge = body[:500] + "\n" + body[-700:]
        for m in BYLINE_RE.finditer(edge):
            n = norm_name(m.group(1), outlet)
            if n and n not in names:
                names.append(n)
    return ", ".join(names[:3])


def extract_body(content: bytes, soup: BeautifulSoup) -> str:
    text = ""
    if trafilatura is not None:
        try:
            text = trafilatura.extract(content, include_comments=False, include_tables=False,
                                       favor_precision=True) or ""
        except Exception:
            text = ""
    if len(text) < 250:
        node = soup.find("article") or soup
        ps = [p.get_text(" ", strip=True) for p in node.find_all("p")]
        text = "\n".join(p for p in ps if len(p) > 30)
    return text.strip()


def enrich_article(a: Article, target: date, strict: bool) -> str | None:
    """원문 검증. 통과하면 None, 실패하면 제외 사유(str)를 반환."""
    try:
        url = resolve_google_url(a.url)
        if not url:
            return "원문 URL 해석 실패"
        content, final_url = fetch_page(url)
    except Exception as e:
        return f"원문 접속 실패({type(e).__name__})"
    soup = BeautifulSoup(content, "html.parser")
    ld = jsonld_objects(soup)
    a.url = final_url

    pub = extract_published(soup, ld)
    if pub is not None:
        if pub.date() != target:
            return f"발행일 불일치(원문 {pub:%Y-%m-%d})"
        a.published, a.pub_basis = pub, "원문 메타데이터"
    elif a.published is not None:
        a.pub_basis = a.pub_basis or "뉴스 피드"
    else:
        return "발행일 확인 불가"

    body = extract_body(content, soup)
    if len(body) < 250:
        return "본문 추출 실패(유료·로그인 또는 짧은 기사)"
    a.body = body

    if not a.outlet or "." in a.outlet:
        site = meta_content(soup, ["og:site_name"])
        if site:
            a.outlet = site[0]
    og = meta_content(soup, ["og:title"])
    if og and 8 < len(og[0]) < 160:
        a.title = re.split(r"\s+[|｜]\s+", og[0])[0].strip()
    a.reporter = extract_reporter(soup, ld, body, a.outlet)
    if strict and not a.reporter:
        return "기자명 미확인"
    return None


def enrich_cluster(items: list[Article], target: date, strict: bool):
    rejects: list[tuple[Article, str]] = []
    for a in items[:3]:  # 같은 사건의 다른 매체 기사로 대체 시도
        reason = enrich_article(a, target, strict)
        if reason is None:
            a.coverage = len({x.outlet for x in items})
            return a, rejects
        rejects.append((a, reason))
    return None, rejects


# ──────────────────────────────────────────────────────────────────────────────
# 3) Gemini (요약 · 브리핑)
# ──────────────────────────────────────────────────────────────────────────────
class GeminiRunner:
    def __init__(self, api_key: str, main: str, light: str):
        if genai is None:
            raise RuntimeError("google-genai 패키지가 설치되지 않았습니다. (pip install google-genai)")
        self.client = genai.Client(api_key=api_key)
        self.main, self.light = main, light
        self.used: dict[str, int] = {}

    def chain(self, first: str) -> list[str]:
        out: list[str] = []
        for m in [first, self.main, self.light, *FALLBACK_MODELS]:
            if m and m not in out:
                out.append(m)
        return out

    @staticmethod
    def parse_json(text: str) -> Any:
        t = (text or "").strip()
        t = re.sub(r"^```(?:json)?|```$", "", t, flags=re.M).strip()
        try:
            return json.loads(t)
        except Exception:
            m = re.search(r"\{.*\}", t, flags=re.S)
            if m:
                return json.loads(m.group(0))
            raise

    def generate_json(self, prompt: str, system: str, first: str, retries: int = 2) -> dict:
        last: Exception | None = None
        for model in self.chain(first):
            for attempt in range(retries):
                try:
                    resp = self.client.models.generate_content(
                        model=model,
                        contents=prompt,
                        config=gtypes.GenerateContentConfig(
                            system_instruction=system, temperature=0.1,
                            response_mime_type="application/json"),
                    )
                    data = self.parse_json(resp.text)
                    if isinstance(data, list) and data and isinstance(data[0], dict):
                        data = data[0]
                    if not isinstance(data, dict):
                        raise ValueError("JSON 객체가 아님")
                    self.used[model] = self.used.get(model, 0) + 1
                    return data
                except Exception as e:
                    last = e
                    msg = str(e).lower()
                    if any(k in msg for k in ("404", "not found", "not_found", "is not supported")):
                        break  # 모델 ID 오류 → 다음 모델로
                    time.sleep(1.5 * (attempt + 1))
        raise RuntimeError(f"모든 모델 호출 실패: {last}")


ARTICLE_SYSTEM = """당신은 한국 언론 기사를 '사실 중심'으로 정리하는 편집 보조자입니다.
규칙:
- 제공된 [본문]에 적힌 내용만 사용합니다. 외부 지식·추측·평가·과장 표현을 추가하지 않습니다.
- 숫자, 고유명사, 날짜, 직함은 본문 그대로 옮깁니다. 본문에 없으면 쓰지 않습니다.
- 기사 유형을 판정합니다: "사실보도" | "전망·추측" | "칼럼·사설" | "광고성".
  · 확인되지 않은 소문, 익명 관계자 발 관측, '~할 듯/~전망/~가능성' 중심의 기사는 "전망·추측".
  · 공식 발표, 확정된 사건, 공시, 경기 결과, 정부 발표, 수치 발표 등은 "사실보도".
- detail은 기사 내용을 순서대로 빠짐없이 '자신의 문장으로 다시 쓴' 정리입니다. 본문 문장을 그대로 복사하지 않습니다.
- quotes는 본문에 글자 그대로 존재하는 문장만 넣습니다(한 글자도 바꾸지 않음). 없으면 빈 배열.
- 반드시 JSON 객체 하나만 출력합니다."""


def summarize_article(runner: GeminiRunner, a: Article) -> dict:
    prompt = f"""[메타]
제목: {a.title}
언론사: {a.outlet}
기자: {a.reporter or '미확인'}
발행: {a.published:%Y-%m-%d %H:%M}

[본문]
{a.body[:9000]}

[출력 JSON 스키마]
{{
  "article_type": "사실보도|전망·추측|칼럼·사설|광고성",
  "type_reason": "유형 판정 근거 한 문장",
  "summary": "핵심 요약 3~4문장 (보도체 '~했다/~밝혔다')",
  "detail": ["기사 내용을 순서대로 재구성한 문단 3~4개, 전체 600~900자"],
  "key_points": [{{"point": "중점 소제목 15자 내외", "desc": "근거 사실 1문장"}}],   // 3~4개
  "numbers": [{{"label": "지표명", "value": "수치(단위 포함, 본문 표기 그대로)", "note": "부연 15자 이내"}}],   // 0~3개, 본문에 명시된 수치만
  "quotes": ["본문 그대로의 인용 문장 (각 100자 이내)"],   // 0~2개
  "importance": 1~10 정수 (사회적 파급력·공공성 기준),
  "subtopic": "소분류 2~8자"
}}"""
    return runner.generate_json(prompt, ARTICLE_SYSTEM, runner.light)


def fill_article(a: Article, d: dict) -> None:
    """모델 응답을 검증하며 Article에 반영 (인용문·수치는 원문 대조)."""
    nb = re.sub(r"\s+", "", a.body)
    det = d.get("detail", [])
    if isinstance(det, str):
        det = [x for x in det.split("\n") if x.strip()]
    a.detail = [str(x).strip() for x in det if str(x).strip()][:6]
    kps = []
    for p in d.get("key_points", [])[:4]:
        if isinstance(p, dict) and p.get("point"):
            kps.append({"point": str(p["point"]).strip(), "desc": str(p.get("desc", "")).strip()})
        elif isinstance(p, str) and p.strip():
            kps.append({"point": p.strip()[:20], "desc": p.strip()})
    a.key_points = kps
    nums = []
    for n in d.get("numbers", [])[:3]:
        if not isinstance(n, dict) or not n.get("value") or not n.get("label"):
            continue
        tok = re.search(r"\d[\d,\.]*", str(n["value"]))
        if tok and re.sub(r"\s+", "", tok.group(0)) in nb:  # 본문에 없는 수치는 버림
            nums.append({"label": str(n["label"]).strip(), "value": str(n["value"]).strip(),
                         "note": str(n.get("note", "")).strip()})
    a.numbers = nums
    qs = []
    for q in d.get("quotes", [])[:3]:
        q = str(q).strip().strip('"“”\'')
        if 8 <= len(q) <= 120 and re.sub(r"\s+", "", q) in nb:  # 원문에 그대로 있는 문장만 인용
            qs.append(q)
    a.quotes = qs[:2]


BRIEF_SYSTEM = """당신은 뉴스 브리핑 편집자입니다.
- 입력된 기사 요약 목록에 있는 내용만 사용합니다. 목록에 없는 사실, 전망, 원인 추정, 평가를 쓰지 않습니다.
- issues[].article_ids에는 근거가 되는 기사 번호(정수)만 넣습니다. 근거 없는 이슈는 만들지 않습니다.
- 반드시 JSON 객체 하나만 출력합니다."""


def category_brief(runner: GeminiRunner, cat: str, arts: list[Article]) -> dict:
    listing = "\n".join(f"[{a.no}] ({a.outlet}) {a.title} — {a.summary}" for a in arts)
    prompt = f"""분야: {cat}
기사 목록:
{listing}

[출력 JSON 스키마]
{{
  "headline": "이 분야의 하루를 한 줄(40자 내외)로 요약한 제목",
  "overview": "3~4문장 개관 (사실만)",
  "issues": [ {{"title": "이슈 제목", "detail": "1~2문장", "article_ids": [번호,...]}} ]  // 최대 3개
}}"""
    d = runner.generate_json(prompt, BRIEF_SYSTEM, runner.main)
    valid = {a.no for a in arts}
    issues = []
    for it in d.get("issues", [])[:3]:
        ids = [i for i in it.get("article_ids", []) if isinstance(i, int) and i in valid]
        if ids and it.get("title"):
            issues.append({"title": str(it["title"]), "detail": str(it.get("detail", "")), "article_ids": ids})
    return {"headline": str(d.get("headline", "")), "overview": str(d.get("overview", "")), "issues": issues}


def executive_summary(runner: GeminiRunner, briefs: dict[str, dict], target: date) -> list[str]:
    listing = "\n".join(f"- {k}: {v['headline']} / {v['overview']}" for k, v in briefs.items())
    prompt = f"""{target:%Y년 %m월 %d일} 분야별 브리핑:
{listing}

위 내용만 근거로, 하루 전체를 관통하는 핵심 포인트를 분야당 1문장씩(총 {len(briefs)}문장 이내) 정리하세요.
[출력 JSON 스키마] {{"points": ["문장", ...]}}"""
    d = runner.generate_json(prompt, BRIEF_SYSTEM, runner.main)
    return [str(x) for x in d.get("points", [])][: len(briefs) + 1]


# ──────────────────────────────────────────────────────────────────────────────
# 4) 파이프라인
# ──────────────────────────────────────────────────────────────────────────────
def build_report(cfg: Config, log: Callable[[str], None], prog: Callable[[float], None]) -> dict:
    runner = GeminiRunner(cfg.api_key, cfg.main_model, cfg.light_model)
    rejected: list[dict] = []
    stats: dict[str, dict] = {}
    categories_out: list[dict] = []
    counter = 0
    n_cat = len(cfg.categories)

    for ci, cat in enumerate(cfg.categories):
        base = ci / n_cat
        span = 1 / n_cat
        log(f"■ [{cat.name}] 기사 검색")
        raw = discover(cat, cfg, log)
        clusters = cluster_articles(raw)
        st_ = {"raw": len(raw), "clusters": len(clusters), "verified": 0, "rejected": 0, "final": 0}
        log(f"  · 후보 {len(raw)}건 → 동일 사건 묶음 {len(clusters)}개")
        pool = clusters[: cfg.per_cat * cfg.oversample]

        verified: list[Article] = []
        with ThreadPoolExecutor(max_workers=6) as ex:
            futs = [ex.submit(enrich_cluster, c, cfg.target, cfg.strict_reporter) for c in pool]
            for k, f in enumerate(as_completed(futs), 1):
                try:
                    art, rej = f.result()
                except Exception as e:
                    art, rej = None, []
                    log(f"  · 검증 오류: {type(e).__name__}")
                for a, reason in rej:
                    rejected.append({"category": cat.name, "title": a.title, "outlet": a.outlet,
                                     "url": a.url, "reason": reason})
                    st_["rejected"] += 1
                if art:
                    verified.append(art)
                prog(base + span * 0.45 * k / max(len(futs), 1))
        st_["verified"] = len(verified)
        log(f"  · 원문 검증 통과 {len(verified)}건")

        summarized: list[Article] = []
        with ThreadPoolExecutor(max_workers=4) as ex:
            futs = {ex.submit(summarize_article, runner, a): a for a in verified}
            for k, f in enumerate(as_completed(futs), 1):
                a = futs[f]
                try:
                    d = f.result()
                except Exception as e:
                    rejected.append({"category": cat.name, "title": a.title, "outlet": a.outlet,
                                     "url": a.url, "reason": "AI 요약 실패"})
                    continue
                a.article_type = str(d.get("article_type", ""))
                if a.article_type != "사실보도":
                    rejected.append({"category": cat.name, "title": a.title, "outlet": a.outlet, "url": a.url,
                                     "reason": f"{a.article_type or '유형 미상'} 기사 제외: {d.get('type_reason', '')}"})
                    continue
                a.summary = str(d.get("summary", "")).strip()
                fill_article(a, d)
                try:
                    a.importance = max(1, min(10, int(d.get("importance", 5))))
                except Exception:
                    a.importance = 5
                a.subtopic = str(d.get("subtopic", ""))[:12]
                if a.summary:
                    summarized.append(a)
                prog(base + span * (0.45 + 0.35 * k / max(len(futs), 1)))

        summarized.sort(key=lambda a: -(a.importance + 0.6 * min(a.coverage, 5)))
        chosen = summarized[: cfg.per_cat]
        for a in chosen:
            counter += 1
            a.no = counter
        st_["final"] = len(chosen)
        stats[cat.name] = st_
        log(f"  · 최종 선정 {len(chosen)}건")

        brief = {"headline": "", "overview": "", "issues": []}
        if chosen:
            try:
                brief = category_brief(runner, cat.name, chosen)
            except Exception as e:
                log(f"  · 브리핑 생성 실패: {e}")
        prog(base + span)
        categories_out.append({
            "name": cat.name, "brief": brief,
            "articles": [{
                "no": a.no, "title": a.title, "url": a.url, "outlet": a.outlet, "reporter": a.reporter or "미확인",
                "published": f"{a.published:%Y-%m-%d %H:%M}", "pub_basis": a.pub_basis, "summary": a.summary,
                "detail": a.detail, "key_points": a.key_points, "numbers": a.numbers,
                "quotes": a.quotes, "importance": a.importance, "subtopic": a.subtopic,
                "coverage": a.coverage,
            } for a in chosen],
        })

    briefs = {c["name"]: c["brief"] for c in categories_out if c["brief"]["headline"]}
    exec_points: list[str] = []
    if briefs:
        try:
            log("■ 종합 핵심 브리핑 생성")
            exec_points = executive_summary(runner, briefs, cfg.target)
        except Exception as e:
            log(f"  · 종합 브리핑 실패: {e}")

    return {
        "target_date": cfg.target.isoformat(),
        "weekday": WEEK[cfg.target.weekday()],
        "generated_at": datetime.now(KST).strftime("%Y-%m-%d %H:%M"),
        "models": runner.used,
        "sources": cfg.sources,
        "strict_reporter": cfg.strict_reporter,
        "executive": exec_points,
        "categories": categories_out,
        "stats": stats,
        "rejected": rejected,
        "total_articles": sum(len(c["articles"]) for c in categories_out),
    }


# ──────────────────────────────────────────────────────────────────────────────
# 5) HTML A4 보고서 렌더링 (원무일일보고서 adr-a4 디자인 시스템과 통일)
# ──────────────────────────────────────────────────────────────────────────────
REPORT_CSS = """
@page{size:A4 portrait;margin:8mm 9mm 9mm}
*{box-sizing:border-box}
:root{--ink:#0b2334;--muted:#617282;--line:#dce7e8;--wash:#f6f9fa;--brand:#0f9a8c;--brand-dark:#08766d;--brand-soft:#e7f5f3;--accent:#d8b879;--blue:#155EEF}
html,body{margin:0}
.adr-a4-body{margin:0;background:#eef2f3;color:var(--ink);font-family:Pretendard,'Noto Sans KR','Malgun Gothic',Arial,sans-serif;font-size:11.2px;line-height:1.42;-webkit-print-color-adjust:exact;print-color-adjust:exact}
.adr-a4-preview-frame{padding:16px 0 70px}
.adr-a4-report{width:210mm;max-width:100%;margin:0 auto 18px;background:#fff;color:var(--ink);box-shadow:0 2px 12px rgba(11,35,52,.14)}
@media screen{.adr-a4-report{min-height:297mm}}
.adr-a4-head{position:relative;padding:9mm 11mm 6mm;border-bottom:1px solid #e8eeee}
.adr-a4-head.small{padding:8mm 11mm 4mm}
.adr-a4-brandline{position:absolute;left:0;right:0;top:0;height:4px;background:linear-gradient(90deg,var(--ink) 0 24%,var(--brand) 24% 82%,var(--accent) 82%)}
.adr-a4-header-grid{display:grid;grid-template-columns:minmax(0,1fr) 54mm;gap:10mm;align-items:start}
.adr-a4-header-grid.single{grid-template-columns:1fr}
.adr-a4-brand{display:flex;align-items:center;gap:9px;margin-bottom:4mm}
.adr-a4-logo{height:30px;width:auto;display:block}
.adr-a4-mark{width:28px;height:28px;border-radius:8px;background:linear-gradient(145deg,#0c2c3d,#0f9a8c);flex:none}
.adr-a4-brandword strong{display:block;font-size:17px;line-height:1;letter-spacing:.02em;font-weight:800;color:var(--ink)}
.adr-a4-brandword span{display:block;margin-top:3px;font-size:7px;letter-spacing:.10em;color:var(--muted)}
.adr-a4-eyebrow{display:flex;align-items:center;gap:7px;color:var(--brand-dark);font-size:8.3px;font-weight:800;letter-spacing:.12em;margin-bottom:3px;text-transform:uppercase}
.adr-a4-eyebrow:before{content:"";width:20px;height:2px;background:var(--brand)}
.adr-a4-title{margin:0;font-size:22px;word-break:keep-all;line-height:1.2;letter-spacing:-.03em;color:var(--ink)}
.adr-a4-head.small .adr-a4-title{font-size:19px;line-height:1.3}
.adr-a4-subtitle{margin:4px 0 0;color:var(--muted);font-size:9.6px}
.adr-a4-approval{width:54mm;border:1px solid var(--line);border-radius:5px;overflow:hidden;background:#fff;margin-top:9mm}
.adr-a4-approval-head{text-align:center;background:var(--ink);color:#fff;font-size:7.5px;font-weight:800;padding:3px}
.adr-a4-approval-grid{display:grid;grid-template-columns:repeat(3,1fr)}
.adr-a4-approval-grid div{height:15mm;border-right:1px solid var(--line);padding:4px;text-align:center;font-size:8px;color:#657684}
.adr-a4-approval-grid div:last-child{border-right:0}
.adr-a4-meta{display:grid;grid-template-columns:1fr 1.2fr 1fr;margin-top:8px;border-top:1px solid var(--ink);border-bottom:1px solid var(--line)}
.adr-a4-meta.c4{grid-template-columns:1fr 1.1fr .95fr 1.3fr}
.adr-a4-meta>div{padding:6px 9px 5px 0;min-height:34px}
.adr-a4-meta>div+div{padding-left:9px;border-left:1px solid var(--line)}
.adr-a4-meta small{display:block;font-size:7px;letter-spacing:.08em;color:#7a8a95;font-weight:700;margin-bottom:2px}
.adr-a4-meta b{font-size:9.8px;color:var(--ink)}
.adr-a4-content{padding:3.5mm 11mm 7mm}
.adr-a4-kpis{display:grid;grid-template-columns:repeat(4,1fr);gap:5px;margin-bottom:3mm}
.adr-a4-kpi{border:1px solid var(--line);border-top:2.5px solid var(--brand);padding:7px 8px;border-radius:6px;background:#fff;min-height:52px}
.adr-a4-kpi small{display:block;color:var(--muted);font-size:7.8px;font-weight:700}
.adr-a4-kpi b{display:block;font-size:13.2px;margin:2px 0 1px;color:var(--ink);word-break:keep-all}
.adr-a4-kpi span{font-size:8px;color:#6f7f8c}
.adr-a4-section{padding:2.5mm 0 1.8mm;border-top:1px solid #edf1f2}
.adr-a4-block{padding:0 0 1.8mm}
.adr-a4-stitle{display:flex;align-items:center;gap:7px;margin:0 0 5px;padding-bottom:4px;border-bottom:1px solid #dce8e8;font-size:13px;color:var(--ink)}
.adr-a4-num{background:var(--ink);color:#fff;border-radius:4px;padding:2px 5px;font-size:8.4px}
.adr-a4-desc{margin-left:auto;color:#8795a0;font-size:8px;font-weight:500}
.adr-a4-table{width:100%;border-collapse:collapse;font-size:8.8px}
.adr-a4-table th,.adr-a4-table td{padding:4px 5px;border-bottom:1px solid #e2eaea;text-align:left;vertical-align:middle}
.adr-a4-table thead th{background:var(--ink);color:#fff;font-size:8.2px}
.adr-a4-table tbody tr:nth-child(even){background:#f8fbfb}
.adr-a4-table td.no{font-weight:800;color:var(--brand-dark);text-align:center}
.adr-a4-table .m{color:var(--muted);font-size:8px}
.adr-a4-table .sub{color:#4b5d6b;font-size:8.2px;margin-top:1px}
.adr-a4-table.kv th{width:22%;background:var(--wash);color:var(--muted);font-size:8.4px;border-right:1px solid #e2eaea}
.adr-a4-link{color:var(--blue);text-decoration:none;word-break:break-all}
.adr-a4-link.dark{color:var(--ink);font-weight:700}
.adr-a4-ai-box{border:1px solid #d9e8e6;border-left:3px solid var(--brand);background:#f7fbfb;border-radius:6px;padding:8px 10px;margin-bottom:1.8mm}
.adr-a4-ai-box strong{display:block;color:var(--brand-dark);font-size:9px;margin-bottom:3px}
.adr-a4-ai-box p{margin:0;color:#3e505e;font-size:9.4px;line-height:1.55}
.adr-a4-ai-box ul{margin:0;padding-left:15px;color:#3e505e;font-size:9px;line-height:1.55}
.adr-a4-issue{margin:0 0 3px;font-size:9px;color:#3e505e}.adr-a4-issue b{color:var(--blue)}
.adr-a4-ref{color:var(--brand-dark);font-weight:700;font-size:8px}
.adr-a4-p{margin:0 0 6px;font-size:10.6px;line-height:1.72;color:#25384a;text-align:justify;word-break:keep-all}
.adr-a4-special{display:grid;grid-template-columns:62px 1fr;gap:8px;padding:7px 8px;border:1px solid #e5dfcc;border-left:3px solid var(--accent);border-radius:6px;background:#fbfaf5;margin:1mm 0 1.8mm}
.adr-a4-special b{font-size:8.8px;color:#70581e}
.adr-a4-special p{margin:0 0 3px;font-size:9.4px;color:#55636e;line-height:1.55}
.adr-a4-point{display:grid;grid-template-columns:22px 1fr;gap:8px;padding:5px 0;border-bottom:1px solid #edf1f2}
.adr-a4-point i{font-style:normal;width:20px;height:20px;border-radius:5px;background:var(--brand);color:#fff;font-weight:800;font-size:9px;text-align:center;line-height:20px}
.adr-a4-point strong{display:block;font-size:10.2px;color:var(--ink)}
.adr-a4-point p{margin:1px 0 0;font-size:9.4px;color:#4b5d6b;line-height:1.55}
.adr-a4-chip{display:inline-block;border:1px solid var(--line);border-radius:10px;padding:0 7px;margin:0 3px 2px 0;font-size:7.6px;color:var(--muted)}
.adr-a4-chip.ok{border-color:var(--brand);color:var(--brand-dark);background:var(--brand-soft)}
.adr-a4-empty{color:var(--muted);padding:12px;border:1px dashed var(--line);border-radius:6px;text-align:center}
.adr-a4-footer{display:flex;justify-content:space-between;gap:20px;font-size:7.2px;color:#93a0a8;margin-top:2mm;padding-top:4px;border-top:1px solid #edf1f2}
.nr-toolbar{position:fixed;right:18px;bottom:18px;display:flex;gap:8px;z-index:9}
.nr-toolbar button{background:var(--ink);color:#fff;border:0;border-radius:6px;padding:10px 14px;font-weight:700;cursor:pointer;font-family:inherit;font-size:12px}
.nr-toolbar button.b2{background:var(--brand)}
.nr-toolbar button:disabled{opacity:.6;cursor:wait}
.nr-panel{position:fixed;inset:0;background:rgba(11,35,52,.9);z-index:20;overflow:auto;padding:20px}
.nr-panel .nr-ph{display:flex;gap:8px;align-items:center;justify-content:space-between;color:#fff;margin:0 auto 14px;max-width:1100px;font-weight:700;font-size:13px}
.nr-panel .nr-ph button{background:var(--brand);color:#fff;border:0;border-radius:6px;padding:9px 14px;font-weight:700;cursor:pointer;margin-left:6px;font-family:inherit}
.nr-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(230px,1fr));gap:14px;max-width:1100px;margin:0 auto}
.nr-grid figure{margin:0;background:#fff;border-radius:6px;padding:8px;text-align:center}
.nr-grid img{width:100%;display:block;border:1px solid var(--line)}
.nr-grid a{display:inline-block;margin-top:6px;font-size:12px;color:var(--blue);font-weight:700;text-decoration:none}
.adr-a4-body.nr-blog{font-size:13px;background:transparent}
.adr-a4-body.nr-blog .adr-a4-report{width:auto;max-width:820px;min-height:0;box-shadow:none;border:1px solid var(--line)}
@media print{
html,body{width:auto!important;min-width:0!important;margin:0!important;padding:0!important;background:#fff!important}
.adr-a4-body{font-size:10.5px!important;line-height:1.38!important}
.adr-a4-preview-frame{padding:0!important}
.adr-a4-report{width:100%!important;max-width:none!important;min-height:0!important;margin:0!important;box-shadow:none!important;border:0!important;break-after:page;page-break-after:always}
.adr-a4-report:last-of-type{break-after:auto;page-break-after:auto}
.adr-a4-head{padding:5mm 0 4mm!important;border-bottom:1px solid #e8eeee!important}
.adr-a4-brandline{top:0!important;height:3px!important}
.adr-a4-header-grid{grid-template-columns:minmax(0,1fr) 51mm!important;gap:8mm!important}
.adr-a4-header-grid.single{grid-template-columns:1fr!important}
.adr-a4-approval{width:51mm!important;margin-top:8mm!important}
.adr-a4-approval-grid div{height:13mm!important}
.adr-a4-content{padding:3mm 0 0!important}
.adr-a4-stitle{break-after:avoid-page!important;page-break-after:avoid!important}
.adr-a4-kpi,.adr-a4-approval,.adr-a4-ai-box,.adr-a4-special,.adr-a4-point,.adr-a4-table tr,.adr-a4-issue,.adr-a4-p{break-inside:avoid-page!important;page-break-inside:avoid!important}
.adr-a4-table{break-inside:auto!important}.adr-a4-table thead{display:table-header-group}
.adr-a4-p{font-size:9.8px!important;line-height:1.6!important;margin-bottom:4px!important}
.adr-a4-section{padding:1.8mm 0 1.2mm!important}
.adr-a4-point{padding:3px 0!important}.adr-a4-point p{font-size:9px!important;line-height:1.45!important}
.adr-a4-kpi{min-height:42px!important;padding:5px 7px!important}
.adr-a4-ai-box p{font-size:9px!important}
.nr-toolbar,.nr-panel{display:none!important}
}
@media(max-width:800px){.adr-a4-report{width:100%}.adr-a4-head,.adr-a4-content{padding-left:16px;padding-right:16px}.adr-a4-header-grid{grid-template-columns:1fr}.adr-a4-approval{width:100%;margin-top:0}.adr-a4-kpis{grid-template-columns:1fr 1fr}}
"""


def logo_b64() -> str:
    for p in (BASE_DIR / "assets" / "wivo_logo_small.png", LOGO_PATH):
        try:
            return base64.b64encode(p.read_bytes()).decode()
        except Exception:
            continue
    return ""


def toolbar_html(show_art_btn: bool) -> str:
    art = '<button id="nr-btn-jpg-art" class="b2">기사 페이지만 JPG</button>' if show_art_btn else ""
    return ('<div class="nr-toolbar"><button onclick="window.print()">인쇄 / PDF</button>'
            '<button id="nr-btn-jpg" class="b2">JPG 저장</button>' + art + "</div>")


EXPORT_JS = r"""
<script src="https://cdnjs.cloudflare.com/ajax/libs/html2canvas/1.4.1/html2canvas.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js"></script>
<script>
(function(){
  var SCALE=2, Q=0.92, RATIO=297/210, GAP=8;
  function toBlob(c){return new Promise(function(res){c.toBlob(res,'image/jpeg',Q);});}
  function dl(blob,name){var a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;
    document.body.appendChild(a);a.click();setTimeout(function(){a.remove();},500);}
  function setDisabled(v){Array.prototype.forEach.call(document.querySelectorAll('.nr-toolbar button'),function(b){b.disabled=v;});}
  async function run(btn,onlyArt){
    if(!window.html2canvas){alert('이미지 변환 라이브러리를 불러오지 못했습니다. 인터넷 연결을 확인해 주세요.');return;}
    var label=btn.textContent; setDisabled(true);
    var pages=Array.prototype.slice.call(document.querySelectorAll('.adr-a4-report'));
    if(onlyArt) pages=pages.filter(function(p){return p.getAttribute('data-kind')==='article';});
    if(!pages.length){alert('변환할 페이지가 없습니다.');setDisabled(false);return;}
    var date=document.body.getAttribute('data-date')||'report';
    var out=[];
    try{
      for(var si=0;si<pages.length;si++){
        btn.textContent='변환 중 '+(si+1)+'/'+pages.length;
        var sh=pages[si], tag=sh.getAttribute('data-label')||('p'+(si+1));
        var canvas=await html2canvas(sh,{scale:SCALE,backgroundColor:'#ffffff',useCORS:true,logging:false});
        var sr=sh.getBoundingClientRect(), W=sr.width, k=canvas.width/W;
        var headEl=sh.querySelector('.adr-a4-head'), cont=sh.querySelector('.adr-a4-content');
        var kids=cont?Array.prototype.slice.call(cont.children):[];
        var rc=kids.map(function(e){var r=e.getBoundingClientRect();return {t:r.top-sr.top,b:r.bottom-sr.top};});
        var fi=(kids.length&&kids[kids.length-1].classList.contains('adr-a4-footer'))?kids.length-1:-1;
        var body=[]; kids.forEach(function(e,i){if(i!==fi) body.push(i);});
        var headH=headEl?(headEl.getBoundingClientRect().bottom-sr.top)+GAP:0;
        var footH=fi>=0?(rc[fi].b-rc[fi].t)+GAP+6:0;
        var pageH=W*RATIO, cap=pageH-headH-footH-24;
        var groups=[], cur=[];
        var total=body.length?(headH+(rc[body[body.length-1]].b-rc[body[0]].t)+footH+24):0;
        if(body.length&&total<=pageH*1.2){ groups.push(body.slice()); }   // 약간 넘치는 정도면 한 장을 조금 길게 (분할하지 않음)
        else{
          body.forEach(function(i){
            if(cur.length&&(rc[i].b-rc[cur[0]].t)>cap){groups.push(cur);cur=[];}
            cur.push(i);                     // 블록(카드/표/박스)은 중간에서 자르지 않음
          });
          if(cur.length) groups.push(cur);
        }
        if(!groups.length) groups.push([]);
        groups.forEach(function(g,gi){
          var bt=g.length?rc[g[0]].t:0, bh=g.length?rc[g[g.length-1]].b-bt:0;
          var H=Math.max(pageH, headH+bh+footH+24);
          var pc=document.createElement('canvas'); pc.width=canvas.width; pc.height=Math.round(H*k);
          var ctx=pc.getContext('2d'); ctx.fillStyle='#fff'; ctx.fillRect(0,0,pc.width,pc.height);
          if(headEl) ctx.drawImage(canvas,0,0,canvas.width,headH*k,0,0,canvas.width,headH*k);
          if(g.length) ctx.drawImage(canvas,0,bt*k,canvas.width,bh*k,0,(headH+6)*k,canvas.width,bh*k);
          if(fi>=0) ctx.drawImage(canvas,0,rc[fi].t*k,canvas.width,(rc[fi].b-rc[fi].t)*k,0,(H-footH-6)*k,canvas.width,(rc[fi].b-rc[fi].t)*k);
          out.push({c:pc,tag:tag+(groups.length>1?'-'+(gi+1):'')});
        });
      }
      btn.textContent='이미지 생성 중…';
      var files=[];
      for(var i=0;i<out.length;i++){
        var b=await toBlob(out[i].c);
        files.push({blob:b,name:'wivo_news_'+date+'_'+String(i+1).padStart(2,'0')+'_'+out[i].tag+'.jpg'});
      }
      showPanel(files,date);
    }catch(e){alert('JPG 변환 중 오류가 발생했습니다: '+e);}
    setDisabled(false); btn.textContent=label;
  }
  function showPanel(files,date){
    var old=document.querySelector('.nr-panel'); if(old) old.remove();
    var p=document.createElement('div'); p.className='nr-panel';
    var h=document.createElement('div'); h.className='nr-ph';
    h.innerHTML='<span>JPG '+files.length+'장 생성 완료 · 개별 저장하거나 ZIP으로 한 번에 저장하세요</span>';
    var box=document.createElement('span');
    if(window.JSZip){var z=document.createElement('button');z.textContent='전체 ZIP 저장';
      z.onclick=async function(){var zip=new JSZip();files.forEach(function(f){zip.file(f.name,f.blob);});
        dl(await zip.generateAsync({type:'blob'}),'wivo_news_'+date+'_jpg.zip');};box.appendChild(z);}
    var c=document.createElement('button');c.textContent='닫기';c.onclick=function(){p.remove();};box.appendChild(c);
    h.appendChild(box); p.appendChild(h);
    var g=document.createElement('div'); g.className='nr-grid';
    files.forEach(function(f,i){var fg=document.createElement('figure');var u=URL.createObjectURL(f.blob);
      fg.innerHTML='<img src="'+u+'" alt="page '+(i+1)+'"><a href="'+u+'" download="'+f.name+'">'+(i+1)+'장 저장 (JPG)</a>';
      g.appendChild(fg);});
    p.appendChild(g); document.body.appendChild(p);
  }
  var b1=document.getElementById('nr-btn-jpg'), b2=document.getElementById('nr-btn-jpg-art');
  if(b1) b1.addEventListener('click',function(){run(b1,false);});
  if(b2) b2.addEventListener('click',function(){run(b2,true);});
})();
</script>
"""


def first_sentence(t: str, n: int = 100) -> str:
    t = (t or "").strip()
    m = re.match(r"(.+?(?:다|요)\.)(?:\s|$)", t)
    s = m.group(1) if m else t
    return s if len(s) <= n else s[: n - 1] + "…"


def _brand_html(logo: str) -> str:
    if logo:
        return f'<div class="adr-a4-brand"><img class="adr-a4-logo" alt="Wivo Company" src="data:image/png;base64,{logo}"></div>'
    return ('<div class="adr-a4-brand"><div class="adr-a4-mark"></div><div class="adr-a4-brandword">'
            '<strong>Wivo</strong><span>CONNECT · WORK · TOGETHER</span></div></div>')


def _head(logo: str, eyebrow: str, title: str, subtitle: str, meta: list[tuple[str, str]],
          approval: bool = False, small: bool = False) -> str:
    appr = ""
    if approval:
        appr = ('<section class="adr-a4-approval"><div class="adr-a4-approval-head">결재</div>'
                '<div class="adr-a4-approval-grid"><div>작성</div><div>검수</div><div>게시</div></div></section>')
    sub = f'<p class="adr-a4-subtitle">{esc(subtitle)}</p>' if subtitle else ""
    metas = "".join(f"<div><small>{esc(k)}</small><b>{esc(v)}</b></div>" for k, v in meta)
    grid = "adr-a4-header-grid" + ("" if approval else " single")
    cls = "adr-a4-head" + (" small" if small else "")
    mc = " c4" if len(meta) == 4 else ""
    return (f'<header class="{cls}"><div class="adr-a4-brandline"></div>'
            f'<div class="{grid}"><div>{_brand_html(logo)}<div class="adr-a4-eyebrow">{esc(eyebrow)}</div>'
            f'<h1 class="adr-a4-title">{esc(title)}</h1>{sub}</div>{appr}</div>'
            f'<div class="adr-a4-meta{mc}">{metas}</div></header>')


def _sec(num: str, title: str, desc: str, inner: str) -> str:
    d = f'<span class="adr-a4-desc">{esc(desc)}</span>' if desc else ""
    return (f'<section class="adr-a4-section"><h2 class="adr-a4-stitle"><span class="adr-a4-num">{esc(num)}</span>'
            f'{esc(title)}{d}</h2>{inner}</section>')


def _foot(label: str) -> str:
    return f'<footer class="adr-a4-footer"><span>Wivo · News Intelligence</span><span>{esc(label)}</span></footer>'


def _href(u: str) -> str:
    return esc(u) if str(u).startswith("http") else "#"


def _page(kind: str, label: str, head: str, blocks: list[str]) -> str:
    return (f'<main class="adr-a4-report" data-kind="{kind}" data-label="{esc(label)}">{head}'
            f'<div class="adr-a4-content">{"".join(blocks)}</div></main>')


def _art_table(arts: list[dict]) -> str:
    rows = []
    for a in arts:
        rep_name = f'{esc(a["reporter"])} 기자' if a["reporter"] != "미확인" else "기자명 미확인"
        rows.append(
            f'<tr><td class="no">{a["no"]}</td>'
            f'<td><a class="adr-a4-link dark" href="{_href(a["url"])}" target="_blank" rel="noopener">{esc(a["title"])}</a>'
            f'<div class="sub">{esc(first_sentence(a["summary"]))}</div></td>'
            f'<td>{esc(a["outlet"])}<br><span class="m">{rep_name}</span></td>'
            f'<td class="m">{esc(a["published"][5:])}</td></tr>')
    return ('<div class="adr-a4-block"><table class="adr-a4-table"><thead><tr><th style="width:26px">No</th>'
            '<th>기사 · 한줄 요약</th><th style="width:22%">언론사 · 기자</th><th style="width:70px">발행</th></tr></thead>'
            f'<tbody>{"".join(rows)}</tbody></table></div>')


def _summary_page(rep: dict, logo: str, date_kr: str) -> str:
    cats = rep["categories"]
    arts_all = [a for c in cats for a in c["articles"]]
    outlets = {a["outlet"] for a in arts_all}
    raw = sum(v["raw"] for v in rep["stats"].values())
    ver = sum(v["verified"] for v in rep["stats"].values())
    models = ", ".join(rep["models"].keys()) or "-"
    head = _head(logo, "Daily News Intelligence Report", f"{date_kr} 뉴스 인텔리전스 리포트",
                 "원문 확인된 사실 보도만 선별한 분야별 일일 브리핑 · 요약편",
                 [("REPORT DATE", rep["target_date"]), ("GENERATED", rep["generated_at"]), ("ANALYSIS", "WIVO AI · " + models.upper()[:38])],
                 approval=True)
    kpis = ('<div class="adr-a4-kpis">'
            f'<div class="adr-a4-kpi"><small>수록 기사</small><b>{len(arts_all)}건</b><span>사실 보도 선별</span></div>'
            f'<div class="adr-a4-kpi"><small>분야</small><b>{len(cats)}개</b><span>{esc(" · ".join(c["name"] for c in cats))[:30]}</span></div>'
            f'<div class="adr-a4-kpi"><small>보도 매체</small><b>{len(outlets)}곳</b><span>중복 매체 제외</span></div>'
            f'<div class="adr-a4-kpi"><small>원문 검증</small><b>{ver}건</b><span>검색 후보 {raw}건 중</span></div></div>')
    pts = "".join(f"<li>{esc(p)}</li>" for p in rep["executive"]) or "<li>종합 브리핑이 생성되지 않았습니다.</li>"
    blocks = [kpis,
              f'<section class="adr-a4-section"><h2 class="adr-a4-stitle"><span class="adr-a4-num">00</span>오늘의 핵심 브리핑'
              f'<span class="adr-a4-desc">분야별 핵심 요약</span></h2><div class="adr-a4-ai-box"><strong>WIVO AI DAILY BRIEF</strong><ul>{pts}</ul></div></section>']
    for idx, c in enumerate(cats, 1):
        b = c["brief"]
        inner = ""
        if c["articles"]:
            if b.get("headline"):
                inner += (f'<div class="adr-a4-ai-box"><strong>{esc(b["headline"])}</strong><p>{esc(b.get("overview", ""))}</p></div>')
            for i in b.get("issues", []):
                refs = " ".join(f"[{n}]" for n in i["article_ids"])
                inner += (f'<div class="adr-a4-issue"><b>{esc(i["title"])}</b> — {esc(i["detail"])} '
                          f'<span class="adr-a4-ref">{refs}</span></div>')
        else:
            inner = '<div class="adr-a4-empty">조건(발행일·기자명·사실보도)을 모두 충족한 기사가 없습니다.</div>'
        blocks.append(_sec(f"{idx:02d}", c["name"], f'{len(c["articles"])}건 수록', inner))
        for k in range(0, len(c["articles"]), 6):  # 표를 6행씩 끊어 JPG/인쇄 시 안전하게 분할
            blocks.append(_art_table(c["articles"][k:k + 6]))
    blocks.append(_foot("SUMMARY"))
    return _page("summary", "summary", head, blocks)


def _article_page(rep: dict, logo: str, cat_name: str, a: dict) -> str:
    reporter = f'{a["reporter"]} 기자' if a["reporter"] != "미확인" else "미확인"
    sub = f' · {a["subtopic"]}' if a.get("subtopic") else ""
    head = _head(logo, f"News Article · {cat_name} {a['no']:02d}", a["title"], "",
                 [("언론사", a["outlet"]), ("기자", reporter), ("발행일시", a["published"]), ("분야", cat_name + sub)], small=True)
    blocks: list[str] = []
    nums = a.get("numbers") or []
    if nums:
        cells = "".join(f'<div class="adr-a4-kpi"><small>{esc(n["label"])}</small><b>{esc(n["value"])}</b>'
                        f'<span>{esc(n.get("note", ""))}</span></div>' for n in nums)
        blocks.append(f'<div class="adr-a4-kpis" style="grid-template-columns:repeat({len(nums)},1fr)">{cells}</div>')
    paras = a.get("detail") or [a["summary"]]
    blocks.append(_sec("01", "원문 내용 정리", "기사 본문을 순서대로 재구성 (전문 게재 아님)",
                       "".join(f'<p class="adr-a4-p">{esc(p)}</p>' for p in paras)))
    qs = a.get("quotes") or []
    if qs:
        who = f'{a["outlet"]}{" · " + a["reporter"] + " 기자" if a["reporter"] != "미확인" else ""}'
        blocks.append('<div class="adr-a4-special"><b>원문 인용</b><div>'
                      + "".join(f'<p>“{esc(q)}”</p>' for q in qs)
                      + f'<p style="color:#8a7a4e;font-size:8px">— {esc(who)}</p></div></div>')
    blocks.append(_sec("02", "요약 내역", "AI가 원문을 근거로 작성",
                       f'<div class="adr-a4-ai-box"><strong>KEY SUMMARY</strong><p>{esc(a["summary"])}</p></div>'))
    kp = a.get("key_points") or []
    if kp:
        items = "".join(f'<div class="adr-a4-point"><i>{i}</i><div><strong>{esc(p["point"])}</strong>'
                        f'<p>{esc(p["desc"])}</p></div></div>' for i, p in enumerate(kp, 1))
        blocks.append(_sec("03", "중점 부분", "기사에서 꼭 짚어야 할 핵심 사실", items))
    chips = [f'<span class="adr-a4-chip ok">발행일 검증 · {esc(a["pub_basis"])}</span>', '<span class="adr-a4-chip ok">사실 보도 판정</span>']
    if a["reporter"] != "미확인":
        chips.append('<span class="adr-a4-chip ok">기자명 확인</span>')
    if a["coverage"] > 1:
        chips.append(f'<span class="adr-a4-chip">{a["coverage"]}개 매체 보도</span>')
    src = ('<table class="adr-a4-table kv"><tbody>'
           f'<tr><th>언론사</th><td>{esc(a["outlet"])}</td></tr>'
           f'<tr><th>기자명</th><td>{esc(reporter)}</td></tr>'
           f'<tr><th>발행일시</th><td>{esc(a["published"])}</td></tr>'
           f'<tr><th>원문 주소</th><td><a class="adr-a4-link" href="{_href(a["url"])}" target="_blank" rel="noopener">{esc(a["url"])}</a></td></tr>'
           f'<tr><th>검증</th><td>{"".join(chips)}</td></tr></tbody></table>')
    blocks.append(_sec("04", "출처 및 검증", "언론사 · 기자 · 원문 주소", src))
    blocks.append(_foot(f"{cat_name} · ARTICLE {a['no']:02d}"))
    return _page("article", f"a{a['no']:02d}", head, blocks)


def _notice_page(rep: dict, logo: str) -> str:
    head = _head(logo, "Method & Notice", "조사 방법 및 유의사항", "",
                 [("REPORT DATE", rep["target_date"]), ("SOURCES", ", ".join(rep["sources"])),
                  ("기자명 필수", "ON" if rep["strict_reporter"] else "OFF")], small=True)
    rows = "".join(f'<tr><td>{esc(k)}</td><td>{v["raw"]}</td><td>{v["verified"]}</td><td><b>{v["final"]}</b></td></tr>'
                   for k, v in rep["stats"].items())
    t1 = ('<table class="adr-a4-table"><thead><tr><th>분야</th><th>검색 후보</th><th>원문 검증 통과</th><th>최종 수록</th></tr></thead>'
          f'<tbody>{rows}</tbody></table>')
    cnt: dict[str, int] = {}
    for r in rep["rejected"]:
        key = re.sub(r"\(.*?\)|:.*$", "", r["reason"]).strip()
        cnt[key] = cnt.get(key, 0) + 1
    rr = "".join(f"<tr><td>{esc(k)}</td><td>{v}건</td></tr>" for k, v in sorted(cnt.items(), key=lambda x: -x[1])) or "<tr><td>제외 없음</td><td>-</td></tr>"
    t2 = f'<table class="adr-a4-table"><thead><tr><th>제외 사유</th><th>건수</th></tr></thead><tbody>{rr}</tbody></table>'
    notes = ('<div class="adr-a4-ai-box"><strong>유의사항</strong><ul>'
             '<li>요약·정리문은 AI가 원문 본문을 근거로 작성했으며, 정확한 내용은 반드시 원문 링크에서 확인하시기 바랍니다.</li>'
             '<li>기사의 저작권은 각 언론사 및 기자에게 있으며, 본 보고서는 기사 전문을 게재하지 않고 재구성한 정리와 출처, 짧은 인용만 제공합니다.</li>'
             '<li>기자명은 원문 페이지의 메타데이터·바이라인에서 추출한 값입니다.</li>'
             '<li>추측·전망·소문 위주 기사, 칼럼·사설, 광고성 기사는 AI 판정으로 제외했습니다.</li></ul></div>')
    blocks = [_sec("01", "분야별 처리 현황", "검색 → 원문 검증 → 최종", t1),
              _sec("02", "제외 사유 집계", "", t2),
              _sec("03", "유의사항", "", notes), _foot("NOTICE")]
    return _page("notice", "notice", head, blocks)


def render_report(rep: dict, mode: str = "print", only_no: int | None = None) -> str:
    blog = mode == "blog"
    logo = logo_b64()
    y, m, d = rep["target_date"].split("-")
    date_kr = f"{int(y)}년 {int(m)}월 {int(d)}일 ({rep['weekday']})"
    pages: list[str] = []
    if only_no is None:
        pages.append(_summary_page(rep, logo, date_kr))
    for c in rep["categories"]:
        for a in c["articles"]:
            if only_no is None or a["no"] == only_no:
                pages.append(_article_page(rep, logo, c["name"], a))
    if only_no is None:
        pages.append(_notice_page(rep, logo))
    tools = "" if blog else toolbar_html(only_no is None) + EXPORT_JS
    cls = "adr-a4-body nr-blog" if blog else "adr-a4-body"
    title = f"{date_kr} 뉴스 인텔리전스 리포트 - Wivo"
    return (f'<!DOCTYPE html><html lang="ko"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{esc(title)}</title><style>{REPORT_CSS}</style></head>'
            f'<body class="{cls}" data-date="{esc(rep["target_date"])}"><div class="adr-a4-preview-frame">'
            f'{"".join(pages)}</div>{tools}</body></html>')


# ──────────────────────────────────────────────────────────────────────────────
# 6) Streamlit UI
# ──────────────────────────────────────────────────────────────────────────────
def license_gate() -> None:
    keys = secret("LICENSE_KEYS")
    if not keys:
        st.sidebar.warning("라이선스 키가 설정되지 않은 개발 모드입니다.")
        return
    if isinstance(keys, str):
        keys = [k.strip() for k in keys.split(",") if k.strip()]
    if st.session_state.get("licensed"):
        return
    st.title(APP_TITLE)
    st.caption("유료 서비스입니다. 발급받은 라이선스 키를 입력하세요.")
    with st.form("license"):
        entered = st.text_input("라이선스 키", type="password")
        ok = st.form_submit_button("인증", type="primary")
    if ok:
        if any(hmac.compare_digest(entered.encode(), str(k).encode()) for k in keys):
            st.session_state["licensed"] = True
            st.rerun()
        else:
            st.error("유효하지 않은 키입니다.")
    st.stop()


def parse_custom(text: str) -> list[Category]:
    out = []
    for line in (text or "").splitlines():
        if ":" in line:
            name, kws = line.split(":", 1)
            kw = [k.strip() for k in kws.split(",") if k.strip()]
            if name.strip() and kw:
                out.append(Category(name.strip(), kw))
    return out


def main() -> None:
    st.set_page_config(page_title=APP_TITLE, page_icon="📰", layout="wide")
    st.markdown("""
<style>
.block-container{padding-top:1.6rem;max-width:1200px}
h1,h2,h3{color:#0b2334}
div[data-testid="stSidebar"]{background:#f4f7fa}
</style>""", unsafe_allow_html=True)
    license_gate()

    if LOGO_PATH.exists():
        st.image(str(LOGO_PATH), width=190)
    st.title(APP_TITLE)
    st.caption("지정일 · 분야별 뉴스를 원문 검증 후 HTML A4 보고서로 생성합니다. (인쇄 / 블로그 업로드용)")

    # ── 사이드바
    with st.sidebar:
        st.subheader("API 설정")
        api_key = secret("GEMINI_API_KEY", "")
        if api_key:
            st.success("Gemini API 키: 서버 설정 사용")
        else:
            api_key = st.text_input("Gemini API 키", type="password")
        main_model = st.text_input("메인 모델 (브리핑)", DEFAULT_MAIN_MODEL)
        light_model = st.text_input("경량 모델 (기사 요약)", DEFAULT_LIGHT_MODEL)
        st.caption("모델 ID가 유효하지 않으면 자동으로 다음 모델로 폴백합니다.")
        st.subheader("기사 소스")
        srcs = st.multiselect("검색 소스", ["Google News", "Naver 검색 API"], default=["Google News"])
        naver_id = secret("NAVER_CLIENT_ID", "")
        naver_secret = secret("NAVER_CLIENT_SECRET", "")
        if "Naver 검색 API" in srcs and not (naver_id and naver_secret):
            naver_id = st.text_input("Naver Client ID")
            naver_secret = st.text_input("Naver Client Secret", type="password")
        if "Naver 검색 API" in srcs:
            st.caption("Naver 검색 API는 최신순만 지원하여, 며칠 지난 날짜는 Google News 중심으로 수집됩니다.")

    # ── 본문 입력
    today = datetime.now(KST).date()
    c1, c2 = st.columns([1, 2])
    with c1:
        target = st.date_input("조사 기준일", value=today - timedelta(days=1), max_value=today)
        per_cat = st.slider("분야별 수록 기사 수", 3, 10, 5)
        strict = st.checkbox("기자명이 확인된 기사만 수록 (권장)", value=True)
    with c2:
        picked = st.multiselect("분야 선택", list(PRESETS.keys()), default=["경제", "의료", "연예계", "스포츠"])
        custom = st.text_area("직접 추가 분야 (한 줄에 `분야명: 키워드1, 키워드2`)",
                              placeholder="치과: 임플란트, 치과의사협회\n건설: 부동산 PF, 건설사", height=80)
        exclude = st.text_input("제외할 매체/도메인 (쉼표 구분)", placeholder="예: 위키트리, blog.")
    if target == today:
        st.info("오늘 날짜는 하루가 끝나기 전이라 기사가 일부만 포함될 수 있습니다.")

    run = st.button("보고서 생성", type="primary", use_container_width=True)
    if run:
        cats = [Category(n, PRESETS[n]) for n in picked] + parse_custom(custom)
        if not cats:
            st.error("분야를 1개 이상 선택하세요.")
            st.stop()
        if not api_key:
            st.error("Gemini API 키가 필요합니다.")
            st.stop()
        if not srcs:
            st.error("검색 소스를 1개 이상 선택하세요.")
            st.stop()
        cfg = Config(
            target=target, categories=cats, per_cat=per_cat, strict_reporter=strict,
            sources=[k for label, k in (("Google News", "google"), ("Naver 검색 API", "naver")) if label in srcs],
            exclude=[e.strip() for e in exclude.split(",") if e.strip()],
            main_model=main_model.strip() or DEFAULT_MAIN_MODEL,
            light_model=light_model.strip() or DEFAULT_LIGHT_MODEL,
            api_key=api_key, naver_id=naver_id, naver_secret=naver_secret,
        )
        bar = st.progress(0.0)
        with st.status("보고서 생성 중…", expanded=True) as status:
            try:
                rep = build_report(cfg, lambda m: status.write(m), lambda p: bar.progress(min(max(p, 0.0), 1.0)))
                bar.progress(1.0)
                st.session_state["report"] = rep
                st.session_state["html_print"] = render_report(rep, "print")
                st.session_state["html_blog"] = render_report(rep, "blog")
                buf = io.BytesIO()
                with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
                    for c in rep["categories"]:
                        for a in c["articles"]:
                            zf.writestr(f"article_{a['no']:02d}.html", render_report(rep, "print", only_no=a["no"]))
                st.session_state["zip_articles"] = buf.getvalue()
                status.update(label=f"완료 — 총 {rep['total_articles']}건 수록", state="complete", expanded=False)
            except Exception as e:
                status.update(label="실패", state="error")
                st.error(f"보고서 생성 중 오류: {e}")

    rep = st.session_state.get("report")
    if not rep:
        return

    fname = f"wivo_news_report_{rep['target_date']}"
    st.divider()
    st.subheader(f"{rep['target_date']} 보고서 — 총 {rep['total_articles']}건")
    d1, d2, d3, d4 = st.columns(4)
    d1.download_button("전체 A4 HTML", st.session_state["html_print"], f"{fname}_a4.html",
                       "text/html", use_container_width=True, type="primary")
    d2.download_button("기사별 페이지 ZIP", st.session_state.get("zip_articles", b""), f"{fname}_articles.zip",
                       "application/zip", use_container_width=True, disabled=not rep["total_articles"])
    d3.download_button("블로그용 HTML(전체)", st.session_state["html_blog"], f"{fname}_blog.html",
                       "text/html", use_container_width=True)
    d4.download_button("원본 데이터(JSON)", json.dumps(rep, ensure_ascii=False, indent=2), f"{fname}.json",
                       "application/json", use_container_width=True)

    st.info("📷 **JPG 저장**: 'A4 미리보기' 탭 우측 하단의 [JPG 저장](전체) 또는 [기사 페이지만 JPG] 버튼을 누르면 "
            "페이지별 JPG가 생성됩니다. 기사 1건 = A4 1장이며, 카드·표가 중간에서 잘리지 않도록 블록 단위로 쪽을 나눕니다. "
            "(다운로드한 HTML 파일을 브라우저에서 열어도 동일하게 동작 / 인터넷 연결 필요)")
    t1, t_art, t2, t3 = st.tabs(["A4 미리보기", "기사별 블로그 페이지", "블로그 미리보기", "검증·제외 내역"])
    with t1:
        components.html(st.session_state["html_print"], height=1000, scrolling=True)
    with t_art:
        opts = {a["no"]: f"[{c['name']}] {a['no']}. {a['title']}" for c in rep["categories"] for a in c["articles"]}
        if opts:
            sel = st.selectbox("기사 선택", list(opts.keys()), format_func=lambda n: opts[n])
            one = render_report(rep, "print", only_no=sel)
            st.download_button("이 기사 페이지 HTML 다운로드", one, f"{fname}_article{sel:02d}.html", "text/html")
            components.html(one, height=1150, scrolling=True)
        else:
            st.info("수록된 기사가 없습니다.")
    with t2:
        components.html(st.session_state["html_blog"], height=1000, scrolling=True)
    with t3:
        st.markdown("**분야별 처리 현황**")
        st.dataframe([{"분야": k, "검색 후보": v["raw"], "동일사건 묶음": v["clusters"],
                       "원문 검증 통과": v["verified"], "최종 수록": v["final"]} for k, v in rep["stats"].items()],
                     hide_index=True, use_container_width=True)
        st.markdown(f"**제외된 기사 {len(rep['rejected'])}건**")
        st.dataframe([{"분야": r["category"], "제목": r["title"], "언론사": r["outlet"], "사유": r["reason"],
                       "URL": r["url"]} for r in rep["rejected"]], hide_index=True, use_container_width=True)


if __name__ == "__main__":
    main()
