from __future__ import annotations

import concurrent.futures
import html
import json
import math
import os
import smtplib
import ssl
import time
from datetime import datetime, timezone
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from typing import Any, Callable, Dict, List, Optional, Tuple
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

# ============================================================
# BINANCE MULTI-MARKET SCREENER V3 — FILTERING PIPELINE
# Spot / Margin / USDⓈ-M / COIN-M / Options / Tokenized Stocks
# NO technical indicators. NO orders.
# ============================================================

HTTP_TIMEOUT_SECONDS = int(os.getenv("HTTP_TIMEOUT_SECONDS", "20"))
HTTP_RETRIES = int(os.getenv("HTTP_RETRIES", "3"))
EMAIL_HOST = os.getenv("EMAIL_HOST", "smtp.gmail.com")
EMAIL_PORT = int(os.getenv("EMAIL_PORT", "465"))
EMAIL_USER = os.getenv("EMAIL_USER", "")
EMAIL_PASS = os.getenv("EMAIL_PASS", "")
EMAIL_TO = os.getenv("EMAIL_TO", "")
EMAIL_TOP_RESULTS = int(os.getenv("EMAIL_TOP_RESULTS", "50"))
BINANCE_API_KEY = os.getenv("BINANCE_API_KEY", "").strip()

ENABLE_SPOT = os.getenv("ENABLE_SPOT", "true").lower() == "true"
ENABLE_MARGIN = os.getenv("ENABLE_MARGIN", "true").lower() == "true"
ENABLE_USDM = os.getenv("ENABLE_USDM_FUTURES", "true").lower() == "true"
ENABLE_COINM = os.getenv("ENABLE_COINM_FUTURES", "true").lower() == "true"
ENABLE_OPTIONS = os.getenv("ENABLE_OPTIONS", "true").lower() == "true"
ENABLE_TOKENIZED = os.getenv("ENABLE_TOKENIZED_STOCKS", "true").lower() == "true"

SPOT_BASE_URL = os.getenv("BINANCE_SPOT_BASE_URL", os.getenv("BINANCE_BASE_URL", "https://data-api.binance.vision"))
USDM_BASE_URL = os.getenv("BINANCE_USDM_BASE_URL", "https://fapi.binance.com")
COINM_BASE_URL = os.getenv("BINANCE_COINM_BASE_URL", "https://dapi.binance.com")
OPTIONS_BASE_URL = os.getenv("BINANCE_OPTIONS_BASE_URL", "https://eapi.binance.com")
TOKENIZED_BASE_URL = os.getenv("BINANCE_TOKENIZED_BASE_URL", "https://api.binance.com")

QUOTE_ASSETS = {x.strip().upper() for x in os.getenv("QUOTE_ASSETS", "").split(",") if x.strip()}
EXCLUDE_STABLECOINS = os.getenv("EXCLUDE_STABLECOINS", "true").lower() == "true"
EXCLUDE_LEVERAGED_TOKENS = os.getenv("EXCLUDE_LEVERAGED_TOKENS", "true").lower() == "true"
MIN_24H_QUOTE_VOLUME = float(os.getenv("MIN_24H_QUOTE_VOLUME", "1000000"))
MAX_SPREAD_PERCENT = float(os.getenv("MAX_SPREAD_PERCENT", "0.10"))
MIN_HISTORY_DAYS = int(os.getenv("MIN_HISTORY_DAYS", "30"))

ORDER_BOOK_DEPTH_ENABLED = os.getenv("ORDER_BOOK_DEPTH_ENABLED", "true").lower() == "true"
ORDER_BOOK_DEPTH_LIMIT = int(os.getenv("ORDER_BOOK_DEPTH_LIMIT", "100"))
ORDER_BOOK_DEPTH_PCT = float(os.getenv("ORDER_BOOK_DEPTH_PCT", "0.25"))
MIN_ORDER_BOOK_DEPTH_QUOTE = float(os.getenv("MIN_ORDER_BOOK_DEPTH_QUOTE", "25000"))
ORDER_BOOK_DEPTH_WORKERS = int(os.getenv("ORDER_BOOK_DEPTH_WORKERS", "8"))

# Reporting only; never used as a rejection rule.
BASE_ASSET_SUMMARY_LIMIT = int(os.getenv("BASE_ASSET_SUMMARY_LIMIT", "20"))

STABLECOIN_BASES = {
    "USDT", "USDC", "FDUSD", "BUSD", "DAI", "TUSD", "USDP", "USDE",
    "USDD", "FRAX", "PYUSD", "EURC", "USD1", "RLUSD", "XUSD", "EURI",
    "USDG", "USDS", "U", "AEUR", "USD0",
}
STABLECOIN_MARKERS = (
    "USDT", "USDC", "FDUSD", "TUSD", "USDP", "USDE", "USDD", "PYUSD",
    "USD1", "RLUSD", "USDG", "USDS", "USD0", "XUSD", "EURC", "EURI", "AEUR",
)
LEVERAGED_SUFFIXES = ("UP", "DOWN", "BULL", "BEAR")
LEVERAGED_PATTERNS = ("2L", "2S", "3L", "3S", "5L", "5S")

FUTURES_QUOTE_ASSETS = {x.strip().upper() for x in os.getenv("FUTURES_QUOTE_ASSETS", "USDT,USDC").split(",") if x.strip()}
FUTURES_CONTRACT_TYPES = {x.strip().upper() for x in os.getenv("FUTURES_CONTRACT_TYPES", "PERPETUAL").split(",") if x.strip()}
MIN_FUTURES_QUOTE_VOLUME = float(os.getenv("MIN_FUTURES_QUOTE_VOLUME", "5000000"))
MIN_FUTURES_TRADES = int(os.getenv("MIN_FUTURES_TRADES", "1000"))
MAX_FUTURES_SPREAD_PERCENT = float(os.getenv("MAX_FUTURES_SPREAD_PERCENT", "0.20"))
MIN_FUNDING_RATE_PERCENT = float(os.getenv("MIN_FUNDING_RATE_PERCENT", "-1.0"))
MAX_FUNDING_RATE_PERCENT = float(os.getenv("MAX_FUNDING_RATE_PERCENT", "1.0"))

OPTIONS_QUOTE_ASSETS = {x.strip().upper() for x in os.getenv("OPTIONS_QUOTE_ASSETS", "USDT").split(",") if x.strip()}
MIN_OPTIONS_QUOTE_VOLUME = float(os.getenv("MIN_OPTIONS_QUOTE_VOLUME", "0"))
MIN_OPTIONS_TRADES = int(os.getenv("MIN_OPTIONS_TRADES", "0"))
MAX_OPTIONS_SPREAD_PERCENT = float(os.getenv("MAX_OPTIONS_SPREAD_PERCENT", "5.0"))
OPTIONS_MAX_ASSETS = int(os.getenv("OPTIONS_MAX_ASSETS", "500"))

TOKENIZED_MAX_ASSETS = int(os.getenv("TOKENIZED_MAX_ASSETS", "100"))
MAX_TOKENIZED_SPREAD_PERCENT = float(os.getenv("MAX_TOKENIZED_SPREAD_PERCENT", "1.0"))


class BinanceHTTPError(RuntimeError):
    pass


def http_get_json(base_url: str, path: str, params: Optional[Dict[str, Any]] = None,
                  headers: Optional[Dict[str, str]] = None) -> Any:
    url = base_url.rstrip("/") + path
    if params:
        query = urlencode({k: v for k, v in params.items() if v is not None})
        if query:
            url += "?" + query
    last: Optional[Exception] = None
    for attempt in range(HTTP_RETRIES + 1):
        try:
            req = Request(url, headers={"User-Agent": "BinanceMultiMarketScreener/3.0", **(headers or {})}, method="GET")
            with urlopen(req, timeout=HTTP_TIMEOUT_SECONDS) as response:
                return json.loads(response.read().decode("utf-8"))
        except HTTPError as exc:
            last = exc
            try:
                body = exc.read().decode("utf-8")
            except Exception:
                body = ""
            if exc.code not in {418, 429, 500, 502, 503, 504} or attempt >= HTTP_RETRIES:
                raise BinanceHTTPError(f"HTTP {exc.code} {path}: {body[:700]}") from exc
            retry_after = exc.headers.get("Retry-After")
            try:
                delay = float(retry_after) if retry_after else min(15.0, 2.0 ** attempt)
            except ValueError:
                delay = min(15.0, 2.0 ** attempt)
            time.sleep(delay)
        except (URLError, TimeoutError, json.JSONDecodeError) as exc:
            last = exc
            if attempt >= HTTP_RETRIES:
                raise BinanceHTTPError(f"Request failed {path}: {exc}") from exc
            time.sleep(min(10.0, 2.0 ** attempt))
    raise BinanceHTTPError(f"Request failed {path}: {last}")


def as_float(value: Any, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def as_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def spread_percent(bid: float, ask: float) -> Optional[float]:
    if bid <= 0 or ask <= 0 or ask < bid:
        return None
    mid = (bid + ask) / 2.0
    return (ask - bid) / mid * 100.0 if mid > 0 else None


def is_leveraged_symbol(base: str) -> bool:
    base = str(base).upper()
    return any(base.endswith(x) for x in LEVERAGED_SUFFIXES + LEVERAGED_PATTERNS)


def is_451(exc: Exception) -> bool:
    return "HTTP 451" in str(exc).upper()


def market_error(market: str, exc: Exception) -> Tuple[str, str]:
    if is_451(exc):
        return (f"{market} indisponible : Binance retourne HTTP 451 (restriction géographique / conditions d'éligibilité depuis le runner GitHub).", "unavailable")
    return (f"{market}: {exc}", "error")


class CriterionAudit:
    def __init__(self) -> None:
        self.rows: List[Dict[str, Any]] = []
        self.diagnostics: Dict[str, Any] = {}

    def add(self, name: str, before: int, selected: int) -> None:
        rejected = before - selected
        self.rows.append({
            "criterion": name,
            "before": before,
            "selected": selected,
            "rejected": rejected,
            "retention": selected / before * 100 if before else 0.0,
            "rejection": rejected / before * 100 if before else 0.0,
        })


def apply_criterion(assets: List[Dict[str, Any]], audit: CriterionAudit, name: str,
                    predicate: Callable[[Dict[str, Any]], bool]) -> List[Dict[str, Any]]:
    before = len(assets)
    selected = [a for a in assets if predicate(a)]
    audit.add(name, before, len(selected))
    return selected


# ----------------------------- SPOT -----------------------------
def spot_exchange_info() -> Dict[str, Any]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/exchangeInfo")


def spot_tickers() -> List[Dict[str, Any]]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/ticker/24hr")


def spot_book_tickers() -> List[Dict[str, Any]]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/ticker/bookTicker")


def spot_klines(symbol: str, limit: int) -> List[List[Any]]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/klines", {"symbol": symbol, "interval": "1h", "limit": limit})


def discover_quote_assets(exchange: Dict[str, Any]) -> set[str]:
    active = {str(x.get("quoteAsset", "")).upper() for x in exchange.get("symbols", []) if isinstance(x, dict) and str(x.get("status", "")).upper() == "TRADING"}
    return {q for q in active if q in STABLECOIN_BASES or any(m in q for m in STABLECOIN_MARKERS)}


def resolve_quote_assets(exchange: Dict[str, Any]) -> set[str]:
    active = {str(x.get("quoteAsset", "")).upper() for x in exchange.get("symbols", []) if isinstance(x, dict)}
    return QUOTE_ASSETS & active if QUOTE_ASSETS else discover_quote_assets(exchange)


def build_spot_universe(exchange: Dict[str, Any]) -> List[Dict[str, Any]]:
    result = []
    for x in exchange.get("symbols", []):
        if isinstance(x, dict):
            result.append({
                "market": "SPOT", "symbol": x.get("symbol", ""), "baseAsset": x.get("baseAsset", ""),
                "quoteAsset": str(x.get("quoteAsset", "")).upper(), "status": x.get("status", ""),
                "permissions": x.get("permissions", []), "permissionSets": x.get("permissionSets", []),
                "isSpotTradingAllowed": x.get("isSpotTradingAllowed"),
                "isMarginTradingAllowed": x.get("isMarginTradingAllowed"),
                "isTokenized": x.get("isTokenized"), "tokenized": x.get("tokenized"),
                "isTokenizedAsset": x.get("isTokenizedAsset"), "assetType": x.get("assetType"),
                "productType": x.get("productType"),
            })
    return result


def merge_spot_tickers(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for a in assets:
        t = by.get(a["symbol"], {})
        a.update(lastPrice=as_float(t.get("lastPrice")), quoteVolume=as_float(t.get("quoteVolume")),
                 trades=as_int(t.get("count")), priceChangePercent=as_float(t.get("priceChangePercent")))


def merge_spot_books(assets: List[Dict[str, Any]], books: List[Dict[str, Any]]) -> None:
    by = {x.get("symbol"): x for x in books if x.get("symbol")}
    for a in assets:
        b = by.get(a["symbol"], {})
        bid, ask = as_float(b.get("bidPrice")), as_float(b.get("askPrice"))
        a.update(bidPrice=bid, askPrice=ask, spreadPercent=spread_percent(bid, ask))


def spot_depth(symbol: str) -> Dict[str, Any]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/depth", {"symbol": symbol, "limit": ORDER_BOOK_DEPTH_LIMIT})


def depth_metrics(book: Dict[str, Any], mid: float) -> Dict[str, float]:
    if mid <= 0:
        return {"depthBidQuote": 0.0, "depthAskQuote": 0.0, "depthTotalQuote": 0.0}
    band = ORDER_BOOK_DEPTH_PCT / 100.0
    bid_total = sum(as_float(p) * as_float(q) for p, q, *_ in (book.get("bids") or []) if as_float(p) >= mid * (1 - band) and as_float(p) > 0 and as_float(q) > 0)
    ask_total = sum(as_float(p) * as_float(q) for p, q, *_ in (book.get("asks") or []) if as_float(p) <= mid * (1 + band) and as_float(p) > 0 and as_float(q) > 0)
    return {"depthBidQuote": bid_total, "depthAskQuote": ask_total, "depthTotalQuote": bid_total + ask_total}


def merge_depth(assets: List[Dict[str, Any]], warnings: List[str]) -> None:
    if not ORDER_BOOK_DEPTH_ENABLED or not assets:
        return
    workers = max(1, min(ORDER_BOOK_DEPTH_WORKERS, len(assets)))
    failures = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        futures = {ex.submit(spot_depth, a["symbol"]): a for a in assets}
        for f in concurrent.futures.as_completed(futures):
            a = futures[f]
            try:
                book = f.result()
                bid, ask = as_float(a.get("bidPrice")), as_float(a.get("askPrice"))
                a.update(depth_metrics(book, (bid + ask) / 2 if bid > 0 and ask > 0 else 0))
            except Exception as exc:
                failures += 1
                a["depthTotalQuote"] = 0.0
                a["depthError"] = str(exc)
    if failures:
        warnings.append(f"Order Book Depth Spot : {failures} actif(s) n'ont pas pu être interrogé(s).")


def check_history(assets: List[Dict[str, Any]], warnings: List[str]) -> None:
    if MIN_HISTORY_DAYS <= 0:
        for a in assets:
            a["historyAvailable"] = True
        return
    required = max(1, math.ceil(MIN_HISTORY_DAYS * 24))
    workers = max(1, min(ORDER_BOOK_DEPTH_WORKERS, len(assets)))
    results: Dict[str, Tuple[bool, Optional[str]]] = {}
    def one(a: Dict[str, Any]) -> Tuple[str, bool, Optional[str]]:
        try:
            rows = spot_klines(a["symbol"], required)
            return a["symbol"], len(rows) >= required, None
        except Exception as exc:
            return a["symbol"], False, str(exc)
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        for f in concurrent.futures.as_completed([ex.submit(one, a) for a in assets]):
            symbol, ok, err = f.result()
            results[symbol] = (ok, err)
    errors = 0
    for a in assets:
        ok, err = results.get(a["symbol"], (False, "historique absent"))
        a["historyAvailable"] = ok
        if err:
            errors += 1
            a["historyError"] = err
    if errors:
        warnings.append(f"Historique Spot : {errors} actif(s) ont retourné une erreur de données.")


def screen_spot(assets: List[Dict[str, Any]], quotes: set[str], warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Status TRADING", lambda a: str(a.get("status", "")).upper() == "TRADING")
    assets = apply_criterion(assets, audit, "2. Permission Spot", lambda a: not a.get("permissions") or "SPOT" in {str(v).upper() for v in a.get("permissions", [])} or a.get("isSpotTradingAllowed") is True)
    assets = apply_criterion(assets, audit, "3. Quote asset autorisé", lambda a: a.get("quoteAsset") in quotes)
    assets = apply_criterion(assets, audit, "4. Exclusion stablecoins", lambda a: str(a.get("baseAsset", "")).upper() not in STABLECOIN_BASES) if EXCLUDE_STABLECOINS else assets
    if EXCLUDE_STABLECOINS is False:
        audit.add("4. Exclusion stablecoins", len(assets), len(assets))
    assets = apply_criterion(assets, audit, "5. Exclusion tokens à levier", lambda a: not is_leveraged_symbol(a.get("baseAsset", ""))) if EXCLUDE_LEVERAGED_TOKENS else assets
    if EXCLUDE_LEVERAGED_TOKENS is False:
        audit.add("5. Exclusion tokens à levier", len(assets), len(assets))
    merge_spot_tickers(assets, spot_tickers())
    assets = apply_criterion(assets, audit, "6. Prix 24h disponible", lambda a: as_float(a.get("lastPrice")) > 0)
    assets = apply_criterion(assets, audit, "7. Volume quote 24h minimum", lambda a: as_float(a.get("quoteVolume")) >= MIN_24H_QUOTE_VOLUME)
    merge_depth(assets, warnings)
    for a in assets:
        vol, dep = as_float(a.get("quoteVolume")), as_float(a.get("depthTotalQuote"))
        a["depthToVolumePercent"] = dep / vol * 100 if vol > 0 else None
    assets = apply_criterion(assets, audit, "8. Profondeur carnet minimum", lambda a: as_float(a.get("depthTotalQuote")) >= MIN_ORDER_BOOK_DEPTH_QUOTE) if ORDER_BOOK_DEPTH_ENABLED else assets
    if not ORDER_BOOK_DEPTH_ENABLED:
        audit.add("8. Profondeur carnet minimum", len(assets), len(assets))
    assets = apply_criterion(assets, audit, "9. Spread maximum", lambda a: a.get("spreadPercent") is not None and as_float(a.get("spreadPercent")) <= MAX_SPREAD_PERCENT)
    check_history(assets, warnings)
    assets = apply_criterion(assets, audit, f"10. Historique minimum ({MIN_HISTORY_DAYS} jours en 1h)", lambda a: a.get("historyAvailable") is True) if MIN_HISTORY_DAYS > 0 else assets
    if MIN_HISTORY_DAYS <= 0:
        audit.add("10. Historique minimum", len(assets), len(assets))
    return sorted(assets, key=lambda a: as_float(a.get("quoteVolume")), reverse=True), audit


# ----------------------------- MARGIN -----------------------------
def build_margin(spot_assets: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [{**a, "market": "MARGIN", "marginEligibility": "ACCOUNT_DEPENDENT"} for a in spot_assets]


# ----------------------------- FUTURES -----------------------------
def futures_exchange(base: str, path: str) -> Dict[str, Any]:
    return http_get_json(base, path)


def futures_ticker(base: str, path: str) -> List[Dict[str, Any]]:
    return http_get_json(base, path)


def futures_book(base: str, path: str) -> List[Dict[str, Any]]:
    return http_get_json(base, path)


def futures_funding(base: str, path: str) -> Any:
    return http_get_json(base, path)


def build_usdm(exchange: Dict[str, Any]) -> List[Dict[str, Any]]:
    out = []
    for x in exchange.get("symbols", []):
        contract, quote = str(x.get("contractType", "")).upper(), str(x.get("quoteAsset", "")).upper()
        if contract in FUTURES_CONTRACT_TYPES and quote in FUTURES_QUOTE_ASSETS:
            out.append({"market": "USDⓈ-M FUTURES", "symbol": x.get("symbol", ""), "baseAsset": x.get("baseAsset", ""), "quoteAsset": quote, "contractType": contract, "status": str(x.get("status", "")).upper()})
    return out


def build_coinm(exchange: Dict[str, Any]) -> List[Dict[str, Any]]:
    out = []
    for x in exchange.get("symbols", []):
        contract = str(x.get("contractType", "")).upper()
        if contract in FUTURES_CONTRACT_TYPES:
            out.append({"market": "COIN-M FUTURES", "symbol": x.get("symbol", ""), "baseAsset": x.get("baseAsset", ""), "quoteAsset": str(x.get("quoteAsset", "")).upper(), "contractType": contract, "status": str(x.get("contractStatus", x.get("status", ""))).upper()})
    return out


def merge_futures(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]], books: List[Dict[str, Any]], funding: Any) -> None:
    tby = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    bby = {x.get("symbol"): x for x in books if x.get("symbol")}
    fby = {x.get("symbol"): x for x in (funding if isinstance(funding, list) else [funding]) if isinstance(x, dict) and x.get("symbol")}
    for a in assets:
        t, b, f = tby.get(a["symbol"], {}), bby.get(a["symbol"], {}), fby.get(a["symbol"], {})
        qv = as_float(t.get("quoteVolume")) or as_float(t.get("baseVolume"))
        bid, ask = as_float(b.get("bidPrice")), as_float(b.get("askPrice"))
        a.update(lastPrice=as_float(t.get("lastPrice")), quoteVolume=qv, trades=as_int(t.get("count")),
                 priceChangePercent=as_float(t.get("priceChangePercent")), bidPrice=bid, askPrice=ask,
                 spreadPercent=spread_percent(bid, ask))
        if "lastFundingRate" in f:
            a["fundingRate"] = as_float(f.get("lastFundingRate")) * 100


def screen_futures(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Contrat TRADING", lambda a: a.get("status") == "TRADING")
    assets = apply_criterion(assets, audit, "2. Prix disponible", lambda a: as_float(a.get("lastPrice")) > 0)
    assets = apply_criterion(assets, audit, "3. Volume quote minimum", lambda a: as_float(a.get("quoteVolume")) >= MIN_FUTURES_QUOTE_VOLUME)
    assets = apply_criterion(assets, audit, "4. Trades minimum", lambda a: as_int(a.get("trades")) >= MIN_FUTURES_TRADES)
    assets = apply_criterion(assets, audit, "5. Spread maximum", lambda a: a.get("spreadPercent") is not None and as_float(a.get("spreadPercent")) <= MAX_FUTURES_SPREAD_PERCENT)
    assets = apply_criterion(assets, audit, "6. Funding disponible", lambda a: "fundingRate" in a)
    assets = apply_criterion(assets, audit, "7. Funding dans la plage autorisée", lambda a: MIN_FUNDING_RATE_PERCENT <= as_float(a.get("fundingRate")) <= MAX_FUNDING_RATE_PERCENT)
    return sorted(assets, key=lambda a: as_float(a.get("quoteVolume")), reverse=True), audit


# ----------------------------- OPTIONS -----------------------------
def options_exchange() -> Dict[str, Any]:
    return http_get_json(OPTIONS_BASE_URL, "/eapi/v1/exchangeInfo")


def options_ticker() -> List[Dict[str, Any]]:
    return http_get_json(OPTIONS_BASE_URL, "/eapi/v1/ticker")


def build_options(exchange: Dict[str, Any]) -> List[Dict[str, Any]]:
    out = []
    for x in exchange.get("optionSymbols", []):
        quote = str(x.get("quoteAsset", "")).upper()
        if quote in OPTIONS_QUOTE_ASSETS:
            out.append({"market": "OPTIONS", "symbol": x.get("symbol", ""), "underlying": x.get("underlying", ""), "quoteAsset": quote, "status": str(x.get("status", "")).upper(), "strikePrice": as_float(x.get("strikePrice")), "expiryDate": x.get("expiryDate")})
    return out


def merge_options(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for a in assets:
        t = by.get(a["symbol"], {})
        bid, ask = as_float(t.get("bidPrice")), as_float(t.get("askPrice"))
        a.update(lastPrice=as_float(t.get("lastPrice")), quoteVolume=as_float(t.get("amount")), trades=as_int(t.get("tradeCount")), bidPrice=bid, askPrice=ask, spreadPercent=spread_percent(bid, ask))


def screen_options(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Option TRADING", lambda a: a.get("status") == "TRADING")
    assets = apply_criterion(assets, audit, "2. Prix disponible", lambda a: as_float(a.get("lastPrice")) > 0)
    assets = apply_criterion(assets, audit, "3. Volume quote minimum", lambda a: as_float(a.get("quoteVolume")) >= MIN_OPTIONS_QUOTE_VOLUME)
    assets = apply_criterion(assets, audit, "4. Trades minimum", lambda a: as_int(a.get("trades")) >= MIN_OPTIONS_TRADES)
    assets = apply_criterion(assets, audit, "5. Spread maximum", lambda a: a.get("spreadPercent") is not None and as_float(a.get("spreadPercent")) <= MAX_OPTIONS_SPREAD_PERCENT)
    assets = sorted(assets, key=lambda a: as_float(a.get("quoteVolume")), reverse=True)
    before = len(assets)
    if OPTIONS_MAX_ASSETS > 0:
        assets = assets[:OPTIONS_MAX_ASSETS]
    audit.add("6. Limite options maximale", before, len(assets))
    return assets, audit


# ----------------------------- TOKENIZED STOCKS -----------------------------
def tokenized_headers() -> Dict[str, str]:
    if not BINANCE_API_KEY:
        raise BinanceHTTPError("BINANCE_API_KEY absent")
    return {"X-MBX-APIKEY": BINANCE_API_KEY}


def tokenized_exchange() -> Dict[str, Any]:
    return http_get_json(TOKENIZED_BASE_URL, "/sapi/v1/equity/market/exchangeInfo", headers=tokenized_headers())


def tokenized_assets() -> Any:
    return http_get_json(TOKENIZED_BASE_URL, "/sapi/v1/equity/market/tokenized-assets", headers=tokenized_headers())


def tokenized_quote(symbol: str) -> Dict[str, Any]:
    return http_get_json(TOKENIZED_BASE_URL, "/sapi/v1/equity/market/quote", {"symbol": symbol}, tokenized_headers())


def build_tokenized(exchange: Dict[str, Any], meta: Any) -> List[Dict[str, Any]]:
    by_code = {str(x.get("assetCode")): x for x in (meta if isinstance(meta, list) else []) if isinstance(x, dict) and x.get("assetCode")}
    out = []
    for x in exchange.get("symbols", []):
        if not isinstance(x, dict) or str(x.get("tradability", "NONE")).upper() == "NONE":
            continue
        code = str(x.get("symbol", ""))
        m = by_code.get(code, {})
        out.append({"market": "TOKENIZED STOCKS", "symbol": code, "tradability": str(x.get("tradability", "")).upper(), "underlyingEquitySymbol": m.get("underlyingEquitySymbol", ""), "assetName": m.get("assetName", ""), "fractionable": x.get("fractionable", False), "overnightSupported": x.get("overnightSupported", False)})
    return out


def merge_tokenized_quotes(assets: List[Dict[str, Any]]) -> None:
    def one(a: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return a["symbol"], tokenized_quote(a["symbol"])
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, min(8, len(assets)))) as ex:
        futures = {ex.submit(one, a): a for a in assets}
        for f in concurrent.futures.as_completed(futures):
            a = futures[f]
            try:
                _, q = f.result()
                bid, ask = as_float(q.get("bidPrice")), as_float(q.get("askPrice"))
                a.update(bidPrice=bid, askPrice=ask, spreadPercent=spread_percent(bid, ask))
            except Exception as exc:
                a["quoteError"] = str(exc)


def screen_tokenized(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Tradabilité", lambda a: a.get("tradability") in {"BUY_SELL", "BUY", "SELL"})
    assets = apply_criterion(assets, audit, "2. Bid/ask disponibles", lambda a: as_float(a.get("bidPrice")) > 0 and as_float(a.get("askPrice")) > 0)
    assets = apply_criterion(assets, audit, "3. Spread maximum", lambda a: a.get("spreadPercent") is not None and as_float(a.get("spreadPercent")) <= MAX_TOKENIZED_SPREAD_PERCENT)
    assets = sorted(assets, key=lambda a: as_float(a.get("bidPrice")), reverse=True)
    before = len(assets)
    if TOKENIZED_MAX_ASSETS > 0:
        assets = assets[:TOKENIZED_MAX_ASSETS]
    audit.add("4. Limite tokenized maximale", before, len(assets))
    return assets, audit


# ----------------------------- REPORT -----------------------------
def esc(v: Any) -> str:
    return html.escape("" if v is None else str(v), quote=True)


def fmt(v: Any, d: int = 2) -> str:
    try:
        return f"{float(v):,.{d}f}"
    except (TypeError, ValueError):
        return "-"


def spot_category(a: Dict[str, Any]) -> str:
    explicit = a.get("isTokenized") is True or a.get("tokenized") is True or a.get("isTokenizedAsset") is True
    explicit = explicit or str(a.get("assetType", "")).upper() in {"TOKENIZED", "TOKENIZED_STOCK", "STOCK_TOKEN"}
    explicit = explicit or str(a.get("productType", "")).upper() in {"TOKENIZED", "TOKENIZED_STOCK", "STOCK_TOKEN"}
    return "SPOT / TOKENIZED / SPECIAL" if explicit else "SPOT / CRYPTO"


def audit_html(audit: CriterionAudit) -> str:
    out = ["<h3>Audit du pipeline de filtrage</h3><table border='1' cellpadding='5' cellspacing='0' style='border-collapse:collapse;width:100%;font-size:12px'>", "<tr><th>Étape</th><th>Avant</th><th>Sélectionnés</th><th>Rejetés</th><th>Rétention</th><th>Rejet</th></tr>"]
    for r in audit.rows:
        out.append(f"<tr><td>{esc(r['criterion'])}</td><td>{r['before']:,}</td><td>{r['selected']:,}</td><td>{r['rejected']:,}</td><td>{r['retention']:.1f}%</td><td>{r['rejection']:.1f}%</td></tr>")
    out.append("</table>")
    return "".join(out)


def base_summary(assets: List[Dict[str, Any]]) -> str:
    if not assets:
        return ""
    groups: Dict[str, Dict[str, Any]] = {}
    for a in assets:
        base = str(a.get("baseAsset", "")).upper()
        if not base:
            continue
        g = groups.setdefault(base, {"pairs": 0, "volume": 0.0, "symbols": []})
        g["pairs"] += 1
        g["volume"] += as_float(a.get("quoteVolume"))
        if len(g["symbols"]) < 5 and a.get("symbol"):
            g["symbols"].append(a["symbol"])
    ordered = sorted(groups.items(), key=lambda kv: kv[1]["volume"], reverse=True)
    limit = BASE_ASSET_SUMMARY_LIMIT if BASE_ASSET_SUMMARY_LIMIT > 0 else len(ordered)
    out = ["<h3>Vue consolidée par actif de base</h3><p>Cette vue regroupe les paires du même actif sous-jacent. Elle ne remplace pas le pipeline et ne supprime aucune paire.</p>", "<table border='1' cellpadding='5' cellspacing='0'><tr><th>Base</th><th>Catégorie</th><th>Paires</th><th>Volume cumulé</th><th>Paires représentatives</th></tr>"]
    for base, g in ordered[:limit]:
        out.append(f"<tr><td><b>{esc(base)}</b></td><td>SPOT / CRYPTO</td><td>{g['pairs']}</td><td>${fmt(g['volume'],0)}</td><td>{esc(', '.join(g['symbols']))}</td></tr>")
    out.append("</table>")
    return "".join(out)


def market_html(market: str, assets: List[Dict[str, Any]], audit: Optional[CriterionAudit]) -> str:
    if market == "MARGIN":
        return f"<h2>MARGIN</h2><p><b>Univers sous-jacent :</b> {len(assets):,} actifs Spot éligibles.</p><p>Le screener ne dispose pas ici d'un jeu de données Margin indépendant permettant de recalculer volume, carnet et spread. L'analyse correspond donc au marché Spot sous-jacent. L'éligibilité réelle au Margin dépend du compte Binance.</p>"
    out = [f"<h2>{esc(market)}</h2><p><b>Survivants :</b> {len(assets):,}</p>"]
    if audit:
        out.append(audit_html(audit))
    if assets:
        rows = ["<table border='1' cellpadding='5' cellspacing='0' style='border-collapse:collapse;width:100%;font-size:12px'>", "<tr><th>Catégorie</th><th>Symbol</th><th>Volume 24h</th><th>Depth</th><th>Depth/Volume</th><th>Spread</th><th>Variation 24h</th><th>Historique</th></tr>"]
        for a in assets[:EMAIL_TOP_RESULTS]:
            hist = "OK" if a.get("historyAvailable") else ("NON" if market == "SPOT" else "-")
            rows.append(f"<tr><td>{esc(spot_category(a) if market == 'SPOT' else market)}</td><td><b>{esc(a.get('symbol','-'))}</b></td><td>${fmt(a.get('quoteVolume'),0)}</td><td>${fmt(a.get('depthTotalQuote'),0)}</td><td>{fmt(a.get('depthToVolumePercent'),3)}%</td><td>{fmt(a.get('spreadPercent'),4)}%</td><td>{fmt(a.get('priceChangePercent'),2)}%</td><td>{hist}</td></tr>")
        rows.append("</table>")
        if len(assets) > EMAIL_TOP_RESULTS:
            rows.append(f"<p><i>{len(assets)-EMAIL_TOP_RESULTS:,} actifs supplémentaires ne sont pas affichés dans le tableau détaillé.</i></p>")
        out.append("".join(rows))
    return "".join(out)


def build_report(results: Dict[str, List[Dict[str, Any]]], audits: Dict[str, CriterionAudit], errors: List[str], warnings: List[str], unavailable: List[str]) -> str:
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    out = ["<html><body>", "<h1>Binance Multi-Market Screener V3 — Filtering Pipeline</h1>", f"<p><b>Date :</b> {now}</p>", "<p><b>Principe :</b> aucune analyse technique ni aucun indicateur n'est calculé dans cette version. Le programme se concentre sur le filtrage de l'univers de marché, la liquidité, la tradabilité et les contraintes de marché explicites.</p><hr>"]
    if "SPOT" in results:
        out.append(f"<h2>Synthèse Spot</h2><p><b>Survivants :</b> {len(results['SPOT']):,}</p>")
        out.append(base_summary(results["SPOT"]))
    for market in ["SPOT", "USDⓈ-M FUTURES", "COIN-M FUTURES", "OPTIONS", "TOKENIZED STOCKS", "MARGIN"]:
        if market in results:
            out.append(market_html(market, results[market], audits.get(market)))
    out.append("<h2>Marchés non intégrés</h2><ul><li><b>P2P :</b> non intégré. Aucune API publique officielle adaptée au même type de screening n'est utilisée.</li></ul>")
    if unavailable:
        out.append("<h2>Marchés indisponibles</h2><ul>" + "".join(f"<li>{esc(x)}</li>" for x in unavailable) + "</ul>")
    out.append("<h2>Paramètres principaux</h2><ul>" +
               f"<li>Spot quotes : {'dynamiques — stablecoins actifs détectés depuis Binance exchangeInfo' if not QUOTE_ASSETS else ', '.join(sorted(QUOTE_ASSETS))}</li>" +
               f"<li>Spot volume minimum actif : ${MIN_24H_QUOTE_VOLUME:,.0f}</li>" +
               f"<li>Order Book Depth Spot : {'activé' if ORDER_BOOK_DEPTH_ENABLED else 'désactivé'} — profondeur minimale ${MIN_ORDER_BOOK_DEPTH_QUOTE:,.0f} dans ±{ORDER_BOOK_DEPTH_PCT:.2f}% (limit {ORDER_BOOK_DEPTH_LIMIT}, workers {ORDER_BOOK_DEPTH_WORKERS})</li>" +
               f"<li>Spread Spot maximum : {MAX_SPREAD_PERCENT:.2f}%</li>" +
               f"<li>Historique minimum Spot : {MIN_HISTORY_DAYS} jours en bougies 1h</li>" +
               f"<li>Futures volume minimum : ${MIN_FUTURES_QUOTE_VOLUME:,.0f}</li>" +
               f"<li>Futures trades minimum : {MIN_FUTURES_TRADES:,}</li>" +
               f"<li>Futures spread maximum : {MAX_FUTURES_SPREAD_PERCENT:.2f}%</li>" +
               f"<li>Funding autorisé : {MIN_FUNDING_RATE_PERCENT:.2f}% à {MAX_FUNDING_RATE_PERCENT:.2f}%</li>" +
               f"<li>Options spread maximum : {MAX_OPTIONS_SPREAD_PERCENT:.2f}% — maximum : {OPTIONS_MAX_ASSETS:,}</li>" +
               f"<li>Tokenized Stocks spread maximum : {MAX_TOKENIZED_SPREAD_PERCENT:.2f}% — maximum : {TOKENIZED_MAX_ASSETS:,}</li></ul>")
    if warnings:
        out.append("<h2>Avertissements</h2><ul>" + "".join(f"<li>{esc(x)}</li>" for x in warnings) + "</ul>")
    if errors:
        out.append("<h2>Erreurs techniques réelles</h2><ul>" + "".join(f"<li>{esc(x)}</li>" for x in errors) + "</ul>")
    else:
        out.append("<h2>Erreurs techniques réelles</h2><p><b>0</b></p>")
    out.append("<hr><p><b>Important :</b> ce programme effectue uniquement de la collecte et du filtrage de données de marché. Aucun ordre Binance n'est exécuté.</p></body></html>")
    return "".join(out)


def send_email(subject: str, body: str) -> None:
    if not (EMAIL_USER and EMAIL_PASS and EMAIL_TO):
        raise RuntimeError("EMAIL_USER / EMAIL_PASS / EMAIL_TO non configurés")
    msg = MIMEMultipart("alternative")
    msg["Subject"], msg["From"], msg["To"] = subject, EMAIL_USER, EMAIL_TO
    msg.attach(MIMEText(body, "html", "utf-8"))
    with smtplib.SMTP_SSL(EMAIL_HOST, EMAIL_PORT, context=ssl.create_default_context()) as server:
        server.login(EMAIL_USER, EMAIL_PASS)
        server.sendmail(EMAIL_USER, [EMAIL_TO], msg.as_string())


# ----------------------------- RUNNERS -----------------------------
def run_spot(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    exchange = spot_exchange_info()
    quotes = resolve_quote_assets(exchange)
    warnings.append("Quote assets Spot dynamiques : " + ", ".join(sorted(quotes)) if quotes else "Aucun quote asset Spot autorisé n'a été détecté.")
    assets = build_spot_universe(exchange)
    try:
        merge_spot_books(assets, spot_book_tickers())
    except Exception as exc:
        warnings.append(f"BookTicker Spot indisponible : {exc}")
        for a in assets:
            a["spreadPercent"] = None
    return screen_spot(assets, quotes, warnings)


def run_usdm() -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_usdm(futures_exchange(USDM_BASE_URL, "/fapi/v1/exchangeInfo"))
    merge_futures(assets, futures_ticker(USDM_BASE_URL, "/fapi/v1/ticker/24hr"), futures_book(USDM_BASE_URL, "/fapi/v1/ticker/bookTicker"), futures_funding(USDM_BASE_URL, "/fapi/v1/premiumIndex"))
    return screen_futures(assets)


def run_coinm() -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_coinm(futures_exchange(COINM_BASE_URL, "/dapi/v1/exchangeInfo"))
    merge_futures(assets, futures_ticker(COINM_BASE_URL, "/dapi/v1/ticker/24hr"), futures_book(COINM_BASE_URL, "/dapi/v1/ticker/bookTicker"), futures_funding(COINM_BASE_URL, "/dapi/v1/premiumIndex"))
    return screen_futures(assets)


def run_options() -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_options(options_exchange())
    merge_options(assets, options_ticker())
    return screen_options(assets)


def run_tokenized(warnings: List[str], errors: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    if not BINANCE_API_KEY:
        warnings.append("TOKENIZED STOCKS non exécuté : BINANCE_API_KEY absent.")
        return [], CriterionAudit()
    exchange = tokenized_exchange()
    try:
        meta = tokenized_assets()
    except Exception as exc:
        if is_451(exc):
            warnings.append(f"Classification TOKENIZED/SPECIAL dynamique indisponible : {exc}")
            errors.append(f"TOKENIZED STOCKS: {exc}")
            meta = []
        else:
            raise
    assets = build_tokenized(exchange, meta)
    merge_tokenized_quotes(assets)
    return screen_tokenized(assets)


def main() -> int:
    started = time.time()
    warnings: List[str] = []
    errors: List[str] = []
    unavailable: List[str] = []
    results: Dict[str, List[Dict[str, Any]]] = {}
    audits: Dict[str, CriterionAudit] = {}

    print("=" * 70)
    print("BINANCE MULTI-MARKET SCREENER V3 — FILTERING PIPELINE")
    print("No technical indicators | No orders")
    print("=" * 70)

    if ENABLE_SPOT:
        print("\n[SPOT]")
        try:
            results["SPOT"], audits["SPOT"] = run_spot(warnings)
            print(f"Spot survivors: {len(results['SPOT']):,}")
        except Exception as exc:
            msg, kind = market_error("SPOT", exc)
            (unavailable if kind == "unavailable" else errors).append(msg)

    if ENABLE_MARGIN:
        print("\n[MARGIN]")
        if "SPOT" in results:
            results["MARGIN"] = build_margin(results["SPOT"])
            print(f"Margin underlying Spot universe: {len(results['MARGIN']):,}")
            warnings.append("Margin : l'éligibilité réelle est dépendante du compte et n'est pas déclarée comme garantie par ce screener.")
        else:
            warnings.append("Margin ignoré car le scan Spot n'a pas abouti.")

    for enabled, label, runner in [
        (ENABLE_USDM, "USDⓈ-M FUTURES", run_usdm),
        (ENABLE_COINM, "COIN-M FUTURES", run_coinm),
        (ENABLE_OPTIONS, "OPTIONS", run_options),
    ]:
        if not enabled:
            continue
        print(f"\n[{label}]")
        try:
            results[label], audits[label] = runner()
            print(f"{label} survivors: {len(results[label]):,}")
        except Exception as exc:
            msg, kind = market_error(label, exc)
            (unavailable if kind == "unavailable" else errors).append(msg)

    if ENABLE_TOKENIZED:
        print("\n[TOKENIZED STOCKS]")
        try:
            assets, audit = run_tokenized(warnings, errors)
            if assets:
                results["TOKENIZED STOCKS"], audits["TOKENIZED STOCKS"] = assets, audit
                print(f"Tokenized Stocks survivors: {len(assets):,}")
            else:
                print("Tokenized Stocks: non disponible / aucun actif exploitable")
        except Exception as exc:
            msg, kind = market_error("TOKENIZED STOCKS", exc)
            (unavailable if kind == "unavailable" else errors).append(msg)

    report = build_report(results, audits, errors, warnings, unavailable)
    elapsed = time.time() - started
    try:
        send_email(f"Binance Multi-Market Screener — Filtering Pipeline — {datetime.now(timezone.utc):%Y-%m-%d %H:%M} UTC", report)
        print(f"\nEmail envoyé. Durée : {elapsed:.2f}s")
    except Exception as exc:
        print("\nERREUR EMAIL:", exc)
        print(report)
        return 1

    print(f"\nDurée totale : {elapsed:.2f}s")
    print(f"Marchés indisponibles : {len(unavailable)}")
    print(f"Avertissements : {len(warnings)}")
    print(f"Erreurs techniques réelles : {len(errors)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
