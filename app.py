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
import json
import re
import time
import xml.etree.ElementTree as ET
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
    key_facts: list[str] = field(default_factory=list)
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


ARTICLE_SYSTEM = """당신은 한국 언론 기사를 '사실 중심'으로 요약하는 편집 보조자입니다.
규칙:
- 제공된 [본문]에 적힌 내용만 사용합니다. 외부 지식·추측·평가·과장 표현을 추가하지 않습니다.
- 숫자, 고유명사, 날짜, 직함은 본문 그대로 옮깁니다. 본문에 없으면 쓰지 않습니다.
- 기사 유형을 판정합니다: "사실보도" | "전망·추측" | "칼럼·사설" | "광고성".
  · 확인되지 않은 소문, 익명 관계자 발 관측, '~할 듯/~전망/~가능성' 중심의 기사는 "전망·추측".
  · 공식 발표, 확정된 사건, 공시, 경기 결과, 정부 발표, 수치 발표 등은 "사실보도".
- 반드시 JSON 객체 하나만 출력합니다."""


def summarize_article(runner: GeminiRunner, a: Article) -> dict:
    prompt = f"""[메타]
제목: {a.title}
언론사: {a.outlet}
기자: {a.reporter or '미확인'}
발행: {a.published:%Y-%m-%d %H:%M}

[본문]
{a.body[:7000]}

[출력 JSON 스키마]
{{
  "article_type": "사실보도|전망·추측|칼럼·사설|광고성",
  "type_reason": "유형 판정 근거 한 문장",
  "summary": "본문 근거 사실 요약 2~3문장 (해요체 금지, '~했다/~밝혔다' 보도체)",
  "key_facts": ["핵심 사실 2~4개, 각 60자 이내"],
  "importance": 1~10 정수 (사회적 파급력·공공성 기준),
  "subtopic": "소분류 2~8자"
}}"""
    return runner.generate_json(prompt, ARTICLE_SYSTEM, runner.light)


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
                a.key_facts = [str(x) for x in d.get("key_facts", [])][:4]
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
                "key_facts": a.key_facts, "importance": a.importance, "subtopic": a.subtopic,
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
# 5) HTML A4 보고서 렌더링
# ──────────────────────────────────────────────────────────────────────────────
REPORT_CSS = """
:root{--ink:#0b2334;--brand:#0f9a8c;--blue:#155EEF;--accent:#d8b879;--mute:#5b6b78;--line:#dde4ea;--soft:#f4f7fa}
.nr-root{font-family:'Pretendard','Noto Sans KR','Malgun Gothic','Apple SD Gothic Neo',sans-serif;color:var(--ink);
 line-height:1.62;font-size:10.5pt;background:#e9eef3;padding:16px 0;-webkit-print-color-adjust:exact;print-color-adjust:exact}
.nr-root *{box-sizing:border-box}
.nr-sheet{width:210mm;min-height:297mm;margin:0 auto 16px;background:#fff;padding:14mm 14mm 12mm;
 box-shadow:0 2px 12px rgba(11,35,52,.15);position:relative}
.nr-top{display:flex;justify-content:space-between;align-items:center;border-bottom:2px solid var(--ink);padding-bottom:8px;margin-bottom:14px}
.nr-top img{height:34px;display:block}
.nr-top .nr-tag{font-size:8pt;letter-spacing:.16em;color:var(--mute);font-weight:700;text-align:right}
.nr-cover-title{margin:22mm 0 6mm}
.nr-eyebrow{color:var(--brand);font-weight:800;font-size:9pt;letter-spacing:.18em}
.nr-h1{font-size:26pt;line-height:1.25;margin:6px 0 8px;font-weight:800;color:var(--ink)}
.nr-sub{color:var(--mute);font-size:10.5pt}
.nr-meta{width:100%;border-collapse:collapse;margin:8mm 0;font-size:9.5pt}
.nr-meta th{width:26%;text-align:left;background:var(--soft);color:var(--mute);font-weight:700;padding:7px 10px;border:1px solid var(--line)}
.nr-meta td{padding:7px 10px;border:1px solid var(--line)}
.nr-box{border:1px solid var(--line);border-top:3px solid var(--brand);border-radius:6px;padding:12px 14px;margin:0 0 12px;background:#fff}
.nr-box h3{margin:0 0 6px;font-size:11pt;color:var(--ink)}
.nr-box ul{margin:0;padding-left:18px}.nr-box li{margin:3px 0}
.nr-brief{background:var(--soft);border-left:4px solid var(--accent);border-radius:4px;padding:10px 14px;margin:0 0 12px}
.nr-brief .nr-bh{font-weight:800;font-size:12pt;margin:0 0 4px}
.nr-sec{display:flex;align-items:center;gap:10px;margin:0 0 10px;padding-bottom:6px;border-bottom:2px solid var(--ink)}
.nr-badge{background:var(--ink);color:#fff;border-radius:4px;font-weight:800;font-size:11pt;padding:2px 9px}
.nr-sec h2{margin:0;font-size:16pt}
.nr-issue{margin:0 0 6px;font-size:10pt}.nr-issue b{color:var(--blue)}
.nr-ref{color:var(--brand);font-weight:700;font-size:8.5pt}
.nr-card{border:1px solid var(--line);border-left:4px solid var(--brand);border-radius:6px;padding:10px 12px;margin:0 0 10px;
 break-inside:avoid;page-break-inside:avoid;background:#fff}
.nr-card .nr-no{display:inline-block;background:var(--brand);color:#fff;font-size:8pt;font-weight:800;border-radius:3px;padding:0 6px;margin-right:6px;vertical-align:2px}
.nr-card h4{margin:0 0 4px;font-size:11pt;line-height:1.4}
.nr-card h4 a{color:var(--ink);text-decoration:none}
.nr-row{font-size:8.5pt;color:var(--mute);margin:0 0 6px}.nr-row b{color:var(--ink)}
.nr-sum{margin:0 0 6px;font-size:10pt}
.nr-facts{margin:0 0 6px;padding-left:16px;font-size:9.5pt}.nr-facts li{margin:1px 0}
.nr-src{font-size:8pt;color:var(--mute);border-top:1px dashed var(--line);padding-top:5px;word-break:break-all}
.nr-src a{color:var(--blue);text-decoration:none}
.nr-chip{display:inline-block;border:1px solid var(--line);border-radius:10px;padding:0 7px;margin:0 3px 0 0;font-size:7.5pt;color:var(--mute)}
.nr-chip.ok{border-color:var(--brand);color:var(--brand)}
.nr-note{font-size:8.5pt;color:var(--mute);line-height:1.6}
.nr-foot{margin-top:10px;padding-top:6px;border-top:1px solid var(--line);font-size:7.5pt;color:var(--mute);display:flex;justify-content:space-between}
.nr-toolbar{position:fixed;right:18px;bottom:18px;display:flex;gap:8px;z-index:9}
.nr-toolbar button{background:var(--ink);color:#fff;border:0;border-radius:6px;padding:10px 16px;font-weight:700;cursor:pointer;font-family:inherit}
.nr-toolbar button.nr-b2{background:var(--brand)}
.nr-toolbar button:disabled{opacity:.6;cursor:wait}
.nr-panel{position:fixed;inset:0;background:rgba(11,35,52,.88);z-index:20;overflow:auto;padding:20px}
.nr-panel .nr-ph{display:flex;gap:8px;align-items:center;justify-content:space-between;color:#fff;margin:0 auto 14px;max-width:1100px;font-weight:700}
.nr-panel .nr-ph button{background:var(--brand);color:#fff;border:0;border-radius:6px;padding:9px 14px;font-weight:700;cursor:pointer;margin-left:6px;font-family:inherit}
.nr-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(230px,1fr));gap:14px;max-width:1100px;margin:0 auto}
.nr-grid figure{margin:0;background:#fff;border-radius:6px;padding:8px;text-align:center}
.nr-grid img{width:100%;display:block;border:1px solid var(--line)}
.nr-grid a{display:inline-block;margin-top:6px;font-size:10pt;color:var(--blue);font-weight:700;text-decoration:none}
.nr-sec,.nr-brief,.nr-issue,.nr-box,.nr-meta tr,.nr-top{break-inside:avoid;page-break-inside:avoid}
.nr-sec{break-after:avoid;page-break-after:avoid}
.nr-empty{color:var(--mute);padding:14px;border:1px dashed var(--line);border-radius:6px;text-align:center}
.nr-root.nr-blog{background:transparent;padding:0}
.nr-root.nr-blog .nr-sheet{width:auto;max-width:820px;min-height:0;box-shadow:none;padding:22px;border:1px solid var(--line);margin:0 auto 18px}
.nr-root.nr-blog .nr-cover-title{margin:10px 0}
@page{size:A4;margin:13mm 12mm}
@media print{
 .nr-root{background:#fff;padding:0}
 .nr-sheet{width:auto;min-height:0;margin:0;padding:0;box-shadow:none;page-break-after:always}
 .nr-sheet:last-child{page-break-after:auto}
 .nr-toolbar,.nr-panel{display:none!important}
}
"""


def logo_b64() -> str:
    try:
        return base64.b64encode(LOGO_PATH.read_bytes()).decode()
    except Exception:
        return ""


def _top(logo: str, tag: str) -> str:
    img = (f'<img alt="Wivo Company" src="data:image/png;base64,{logo}">' if logo
           else '<b style="font-size:16pt;color:#155EEF">Wivo</b>')
    return f'<div class="nr-top">{img}<div class="nr-tag">{esc(tag)}</div></div>'


def _foot(rep: dict, label: str) -> str:
    return (f'<div class="nr-foot"><span>Wivo Company · {esc(rep["target_date"])} 뉴스 인텔리전스 리포트</span>'
            f'<span>{esc(label)}</span></div>')



TOOLBAR_HTML = """<div class="nr-toolbar"><button id="nr-btn-print" onclick="window.print()">인쇄 / PDF</button>
<button id="nr-btn-jpg" class="nr-b2">JPG 저장</button></div>"""

EXPORT_JS = r"""
<script src="https://cdnjs.cloudflare.com/ajax/libs/html2canvas/1.4.1/html2canvas.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js"></script>
<script>
(function(){
  var SCALE=2, Q=0.92, RATIO=297/210, GAP=8;
  var btn=document.getElementById('nr-btn-jpg');
  if(!btn) return;
  function toBlob(c){return new Promise(function(res){c.toBlob(res,'image/jpeg',Q);});}
  function dl(blob,name){var a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;
    document.body.appendChild(a);a.click();setTimeout(function(){a.remove();},500);}
  async function exportJpg(){
    if(!window.html2canvas){alert('이미지 변환 라이브러리를 불러오지 못했습니다. 인터넷 연결을 확인해 주세요.');return;}
    var label=btn.textContent; btn.disabled=true;
    var root=document.querySelector('.nr-root');
    var date=(root.getAttribute('data-date')||'report');
    var sheets=Array.prototype.slice.call(root.querySelectorAll('.nr-sheet'));
    var out=[];
    try{
      for(var si=0;si<sheets.length;si++){
        btn.textContent='변환 중 '+(si+1)+'/'+sheets.length;
        var sh=sheets[si];
        var canvas=await html2canvas(sh,{scale:SCALE,backgroundColor:'#ffffff',useCORS:true,logging:false});
        var sr=sh.getBoundingClientRect(), W=sr.width, k=canvas.width/W;
        var kids=Array.prototype.slice.call(sh.children);
        var rc=kids.map(function(e){var r=e.getBoundingClientRect();return {t:r.top-sr.top,b:r.bottom-sr.top};});
        var hi=kids[0].classList.contains('nr-top')?0:-1;
        var fi=kids[kids.length-1].classList.contains('nr-foot')?kids.length-1:-1;
        var body=[]; kids.forEach(function(e,i){if(i!==hi&&i!==fi) body.push(i);});
        var headH=hi>=0?rc[hi].b+GAP:0;
        var footH=fi>=0?(rc[fi].b-rc[fi].t)+GAP+6:0;
        var pageH=W*RATIO;
        var cap=pageH-headH-footH-24;          // 본문이 들어갈 수 있는 높이
        var groups=[], cur=[];
        body.forEach(function(i){
          if(cur.length && (rc[i].b-rc[cur[0]].t)>cap){groups.push(cur);cur=[];}
          cur.push(i);                          // 블록(카드/표/박스)은 절대 중간에서 자르지 않음
        });
        if(cur.length) groups.push(cur);
        if(!groups.length) groups.push([]);
        groups.forEach(function(g){
          var bodyTop=g.length?rc[g[0]].t:0, bodyH=g.length?rc[g[g.length-1]].b-bodyTop:0;
          var H=Math.max(pageH, headH+bodyH+footH+24);   // 큰 카드 하나가 넘치면 그 페이지만 길게
          var pc=document.createElement('canvas'); pc.width=canvas.width; pc.height=Math.round(H*k);
          var ctx=pc.getContext('2d'); ctx.fillStyle='#fff'; ctx.fillRect(0,0,pc.width,pc.height);
          if(hi>=0) ctx.drawImage(canvas,0,0,canvas.width,headH*k,0,0,canvas.width,headH*k);
          if(g.length) ctx.drawImage(canvas,0,bodyTop*k,canvas.width,bodyH*k,0,(headH+6)*k,canvas.width,bodyH*k);
          if(fi>=0) ctx.drawImage(canvas,0,rc[fi].t*k,canvas.width,(rc[fi].b-rc[fi].t)*k,0,(H-footH-6)*k,canvas.width,(rc[fi].b-rc[fi].t)*k);
          out.push(pc);
        });
      }
      btn.textContent='이미지 생성 중…';
      var files=[];
      for(var i=0;i<out.length;i++){
        var b=await toBlob(out[i]);
        files.push({blob:b,name:'wivo_news_'+date+'_p'+String(i+1).padStart(2,'0')+'.jpg'});
      }
      showPanel(files,date);
    }catch(e){alert('JPG 변환 중 오류가 발생했습니다: '+e);}
    btn.disabled=false; btn.textContent=label;
  }
  function showPanel(files,date){
    var old=document.querySelector('.nr-panel'); if(old) old.remove();
    var p=document.createElement('div'); p.className='nr-panel';
    var h=document.createElement('div'); h.className='nr-ph';
    h.innerHTML='<span>JPG '+files.length+'장 생성 완료 · 이미지를 눌러 개별 저장하거나 ZIP으로 한 번에 저장하세요</span>';
    var box=document.createElement('span');
    if(window.JSZip){var z=document.createElement('button');z.textContent='전체 ZIP 저장';
      z.onclick=async function(){var zip=new JSZip();files.forEach(function(f){zip.file(f.name,f.blob);});
        dl(await zip.generateAsync({type:'blob'}),'wivo_news_'+date+'_jpg.zip');};box.appendChild(z);}
    var c=document.createElement('button');c.textContent='닫기';c.onclick=function(){p.remove();};box.appendChild(c);
    h.appendChild(box); p.appendChild(h);
    var g=document.createElement('div'); g.className='nr-grid';
    files.forEach(function(f,i){var fg=document.createElement('figure');var u=URL.createObjectURL(f.blob);
      fg.innerHTML='<img src="'+u+'" alt="page '+(i+1)+'"><a href="'+u+'" download="'+f.name+'">'+(i+1)+'쪽 저장 (JPG)</a>';
      g.appendChild(fg);});
    p.appendChild(g); document.body.appendChild(p);
  }
  btn.addEventListener('click',exportJpg);
})();
</script>
"""

def render_report(rep: dict, mode: str = "print") -> str:
    blog = mode == "blog"
    logo = logo_b64()
    y, m, d = rep["target_date"].split("-")
    date_kr = f"{int(y)}년 {int(m)}월 {int(d)}일 ({rep['weekday']})"
    cats = [c["name"] for c in rep["categories"]]
    models = ", ".join(f"{k}×{v}" for k, v in rep["models"].items()) or "-"
    ref_map = {a["no"]: a for c in rep["categories"] for a in c["articles"]}

    parts: list[str] = []
    # ── 표지 / 종합
    exec_html = "".join(f"<li>{esc(p)}</li>" for p in rep["executive"]) or "<li>종합 브리핑이 생성되지 않았습니다.</li>"
    parts.append(f"""
<section class="nr-sheet">
 {_top(logo, "DAILY NEWS INTELLIGENCE REPORT")}
 <div class="nr-cover-title">
  <div class="nr-eyebrow">NEWS INTELLIGENCE REPORT</div>
  <h1 class="nr-h1">{esc(date_kr)}<br>뉴스 인텔리전스 리포트</h1>
  <div class="nr-sub">원문 확인된 사실 보도만 선별한 분야별 일일 브리핑</div>
 </div>
 <table class="nr-meta">
  <tr><th>조사 기준일</th><td>{esc(date_kr)} (KST 00:00–24:00 발행 기사)</td></tr>
  <tr><th>포함 분야</th><td>{esc(' · '.join(cats))}</td></tr>
  <tr><th>수록 기사</th><td>총 {rep['total_articles']}건</td></tr>
  <tr><th>생성 일시</th><td>{esc(rep['generated_at'])}</td></tr>
  <tr><th>분석 모델</th><td>{esc(models)}</td></tr>
 </table>
 <div class="nr-box"><h3>오늘의 핵심 브리핑</h3><ul>{exec_html}</ul></div>
 <div class="nr-box"><h3>검증 기준</h3>
  <ul class="nr-note">
   <li>모든 기사는 원문 페이지에 직접 접속해 <b>발행일 · 본문 · 기자명</b>을 확인했습니다.</li>
   <li>추측·전망·소문 위주 기사, 칼럼·사설, 광고성 기사는 AI 판정으로 제외했습니다.</li>
   <li>요약은 원문 본문에 적힌 사실만 사용했으며, 각 기사에 원문 주소·언론사·기자명을 표기했습니다.</li>
  </ul></div>
 {_foot(rep, "COVER")}
</section>""")

    # ── 분야별
    for idx, c in enumerate(rep["categories"], 1):
        b = c["brief"]
        if c["articles"]:
            issues = "".join(
                f'<div class="nr-issue"><b>{esc(i["title"])}</b> — {esc(i["detail"])} '
                f'<span class="nr-ref">{" ".join(f"[{n}]" for n in i["article_ids"])}</span></div>'
                for i in b.get("issues", []))
            brief = (f'<div class="nr-brief"><div class="nr-bh">{esc(b.get("headline", ""))}</div>'
                     f'<div>{esc(b.get("overview", ""))}</div></div>') if b.get("headline") else ""
            cards = []
            for a in c["articles"]:
                facts = "".join(f"<li>{esc(f)}</li>" for f in a["key_facts"])
                facts = f'<ul class="nr-facts">{facts}</ul>' if facts else ""
                chips = [f'<span class="nr-chip ok">발행일 {esc(a["pub_basis"])}</span>']
                if a["reporter"] != "미확인":
                    chips.append('<span class="nr-chip ok">기자명 확인</span>')
                if a["coverage"] > 1:
                    chips.append(f'<span class="nr-chip">{a["coverage"]}개 매체 보도</span>')
                sub = f' · {esc(a["subtopic"])}' if a["subtopic"] else ""
                href = esc(a["url"]) if a["url"].startswith("http") else "#"
                cards.append(f"""
 <article class="nr-card">
  <h4><span class="nr-no">{a['no']}</span><a href="{href}" target="_blank" rel="noopener">{esc(a['title'])}</a></h4>
  <div class="nr-row"><b>{esc(a['outlet'])}</b> · {esc(a['reporter'])} 기자 · {esc(a['published'])}{sub}</div>
  <p class="nr-sum">{esc(a['summary'])}</p>{facts}
  <div class="nr-src">{''.join(chips)}<br>원문: <a href="{href}" target="_blank" rel="noopener">{esc(a['url'])}</a></div>
 </article>""")
            body = f'{brief}{issues}<div style="height:6px"></div>{"".join(cards)}'
        else:
            body = '<div class="nr-empty">조건(발행일·기자명·사실보도)을 모두 충족한 기사가 없습니다.</div>'
        parts.append(f"""
<section class="nr-sheet">
 {_top(logo, date_kr)}
 <div class="nr-sec"><span class="nr-badge">{idx:02d}</span><h2>{esc(c['name'])}</h2></div>
 {body}
 {_foot(rep, c['name'])}
</section>""")

    # ── 방법론 / 고지
    rej_count: dict[str, int] = {}
    for r in rep["rejected"]:
        key = re.sub(r"\(.*?\)|:.*$", "", r["reason"]).strip()
        rej_count[key] = rej_count.get(key, 0) + 1
    rej_rows = "".join(f"<tr><th>{esc(k)}</th><td>{v}건</td></tr>" for k, v in sorted(rej_count.items(), key=lambda x: -x[1]))
    rej_rows = rej_rows or "<tr><th>-</th><td>제외 없음</td></tr>"
    st_rows = "".join(
        f"<tr><th>{esc(k)}</th><td>후보 {v['raw']} → 원문 검증 {v['verified']} → 최종 {v['final']}</td></tr>"
        for k, v in rep["stats"].items())
    parts.append(f"""
<section class="nr-sheet">
 {_top(logo, "METHOD & NOTICE")}
 <div class="nr-sec"><span class="nr-badge">i</span><h2>조사 방법 및 유의사항</h2></div>
 <table class="nr-meta">{st_rows}</table>
 <div class="nr-box"><h3>제외 사유 집계</h3><table class="nr-meta" style="margin:0">{rej_rows}</table></div>
 <div class="nr-box"><h3>유의사항</h3>
  <ul class="nr-note">
   <li>본 보고서의 요약문은 AI가 원문 본문을 근거로 작성했으며, 정확한 내용은 반드시 원문 링크에서 확인하시기 바랍니다.</li>
   <li>기사의 저작권은 각 언론사 및 기자에게 있으며, 본 보고서는 기사 전문을 게재하지 않고 요약과 출처만 제공합니다.</li>
   <li>기자명은 원문 페이지의 메타데이터·바이라인에서 추출한 값입니다.</li>
   <li>사용 소스: {esc(', '.join(rep['sources']))} / 기자명 필수 모드: {'ON' if rep['strict_reporter'] else 'OFF'}</li>
  </ul></div>
 {_foot(rep, "NOTICE")}
</section>""")

    btn = "" if blog else TOOLBAR_HTML + EXPORT_JS
    cls = "nr-root nr-blog" if blog else "nr-root"
    return (f'<!DOCTYPE html><html lang="ko"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{esc(date_kr)} 뉴스 인텔리전스 리포트 - Wivo</title><style>{REPORT_CSS}</style></head>'
            f'<body style="margin:0"><div class="{cls}" data-date="{esc(rep['target_date'])}">{"".join(parts)}</div>{btn}</body></html>')


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
    d1, d2, d3 = st.columns(3)
    d1.download_button("인쇄용 A4 HTML 다운로드", st.session_state["html_print"], f"{fname}_a4.html",
                       "text/html", use_container_width=True, type="primary")
    d2.download_button("블로그용 HTML 다운로드", st.session_state["html_blog"], f"{fname}_blog.html",
                       "text/html", use_container_width=True)
    d3.download_button("원본 데이터(JSON)", json.dumps(rep, ensure_ascii=False, indent=2), f"{fname}.json",
                       "application/json", use_container_width=True)

    st.info("📷 **JPG 저장**: 'A4 미리보기' 탭 우측 하단의 [JPG 저장] 버튼을 누르면 페이지별 JPG가 생성됩니다. "
            "카드·표가 중간에서 잘리지 않도록 블록 단위로 쪽을 나누며, ZIP으로 한 번에 저장할 수 있습니다. "
            "(다운로드한 A4 HTML 파일을 브라우저에서 열어도 동일하게 동작합니다 / 인터넷 연결 필요)")
    t1, t2, t3 = st.tabs(["A4 미리보기", "블로그 미리보기", "검증·제외 내역"])
    with t1:
        components.html(st.session_state["html_print"], height=1000, scrolling=True)
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
