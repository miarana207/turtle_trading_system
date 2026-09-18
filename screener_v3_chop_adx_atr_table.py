from __future__ import annotations

import concurrent.futures
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
# BINANCE MULTI-MARKET SCREENER V3 — CHOP / ADX / ATR
# Spot / Margin / USDⓈ-M / COIN-M / Options / Tokenized Stocks
# P2P intentionally not integrated: no suitable official public
# market-data API is used by this scanner.
# NO ORDERS ARE EVER EXECUTED.
# ============================================================

HTTP_TIMEOUT_SECONDS = int(os.getenv("HTTP_TIMEOUT_SECONDS", "20"))
HTTP_RETRIES = int(os.getenv("HTTP_RETRIES", "3"))
EMAIL_HOST = os.getenv("EMAIL_HOST", "smtp.gmail.com")
EMAIL_PORT = int(os.getenv("EMAIL_PORT", "465"))
EMAIL_USER = os.getenv("EMAIL_USER", "")
EMAIL_PASS = os.getenv("EMAIL_PASS", "")
EMAIL_TO = os.getenv("EMAIL_TO", "")
EMAIL_TOP_RESULTS = int(os.getenv("EMAIL_TOP_RESULTS", "50"))
BINANCE_API_KEY = os.getenv("BINANCE_API_KEY", "")

ENABLE_SPOT = os.getenv("ENABLE_SPOT", "true").lower() == "true"
ENABLE_MARGIN = os.getenv("ENABLE_MARGIN", "true").lower() == "true"
ENABLE_USDM = os.getenv("ENABLE_USDM_FUTURES", "true").lower() == "true"
ENABLE_COINM = os.getenv("ENABLE_COINM_FUTURES", "true").lower() == "true"
ENABLE_OPTIONS = os.getenv("ENABLE_OPTIONS", "true").lower() == "true"
ENABLE_TOKENIZED_STOCKS = os.getenv("ENABLE_TOKENIZED_STOCKS", "true").lower() == "true"

SPOT_BASE_URL = os.getenv("BINANCE_SPOT_BASE_URL", os.getenv("BINANCE_BASE_URL", "https://data-api.binance.vision"))
USDM_BASE_URL = os.getenv("BINANCE_USDM_BASE_URL", "https://fapi.binance.com")
COINM_BASE_URL = os.getenv("BINANCE_COINM_BASE_URL", "https://dapi.binance.com")
OPTIONS_BASE_URL = os.getenv("BINANCE_OPTIONS_BASE_URL", "https://eapi.binance.com")
TOKENIZED_BASE_URL = os.getenv("BINANCE_TOKENIZED_BASE_URL", "https://api.binance.com")

# Si vide, le screener construit automatiquement la liste des stablecoins
# actuellement utilisés comme quoteAsset Spot par Binance. Une valeur explicite
# dans QUOTE_ASSETS reste possible pour forcer un univers précis.
QUOTE_ASSETS = {x.strip().upper() for x in os.getenv("QUOTE_ASSETS", "").split(",") if x.strip()}
EXCLUDE_STABLECOINS = os.getenv("EXCLUDE_STABLECOINS", "true").lower() == "true"
EXCLUDE_LEVERAGED_TOKENS = os.getenv("EXCLUDE_LEVERAGED_TOKENS", "true").lower() == "true"
MIN_24H_QUOTE_VOLUME = float(os.getenv("MIN_24H_QUOTE_VOLUME", "1000000"))
MAX_SPREAD_PERCENT = float(os.getenv("MAX_SPREAD_PERCENT", "0.10"))
MIN_HISTORY_DAYS = int(os.getenv("MIN_HISTORY_DAYS", "30"))

# Régime de marché Spot : CHOP + ADX + ATR, calculés au même niveau
# après le spread. Ces indicateurs sont descriptifs et ne rejettent aucun actif.
REGIME_ENABLED = os.getenv("REGIME_ENABLED", "true").lower() == "true"
REGIME_INTERVAL = os.getenv("REGIME_INTERVAL", "1h")
CHOP_PERIOD = int(os.getenv("CHOP_PERIOD", "14"))
ADX_PERIOD = int(os.getenv("ADX_PERIOD", "14"))
ATR_REGIME_PERIOD = int(os.getenv("ATR_REGIME_PERIOD", "14"))
CHOP_RANGE_THRESHOLD = float(os.getenv("CHOP_RANGE_THRESHOLD", "55"))
CHOP_TREND_THRESHOLD = float(os.getenv("CHOP_TREND_THRESHOLD", "40"))
ADX_TREND_THRESHOLD = float(os.getenv("ADX_TREND_THRESHOLD", "25"))
ADX_STRONG_THRESHOLD = float(os.getenv("ADX_STRONG_THRESHOLD", "40"))
ATR_LOW_PERCENT = float(os.getenv("ATR_LOW_PERCENT", "0.50"))
ATR_HIGH_PERCENT = float(os.getenv("ATR_HIGH_PERCENT", "1.50"))
ATR_EXTREME_PERCENT = float(os.getenv("ATR_EXTREME_PERCENT", "2.50"))

# Order Book Depth Spot : garde-fou de liquidité réelle autour du prix médian.
# Le seuil est exprimé en valeur notionnelle quote (ex. USD/USDT).
# On mesure la profondeur cumulée des bids + asks dans une bande de ±0,25 %.
ORDER_BOOK_DEPTH_ENABLED = os.getenv("ORDER_BOOK_DEPTH_ENABLED", "true").lower() == "true"
ORDER_BOOK_DEPTH_LIMIT = int(os.getenv("ORDER_BOOK_DEPTH_LIMIT", "100"))
ORDER_BOOK_DEPTH_PCT = float(os.getenv("ORDER_BOOK_DEPTH_PCT", "0.25"))
MIN_ORDER_BOOK_DEPTH_QUOTE = float(os.getenv("MIN_ORDER_BOOK_DEPTH_QUOTE", "25000"))
ORDER_BOOK_DEPTH_WORKERS = int(os.getenv("ORDER_BOOK_DEPTH_WORKERS", "8"))

FUTURES_QUOTE_ASSETS = {x.strip().upper() for x in os.getenv("FUTURES_QUOTE_ASSETS", "USDT,USDC").split(",") if x.strip()}
MIN_FUTURES_QUOTE_VOLUME = float(os.getenv("MIN_FUTURES_QUOTE_VOLUME", "5000000"))
MIN_FUTURES_TRADES = int(os.getenv("MIN_FUTURES_TRADES", "1000"))
MAX_FUTURES_SPREAD_PERCENT = float(os.getenv("MAX_FUTURES_SPREAD_PERCENT", "0.20"))
MIN_FUNDING_RATE_PERCENT = float(os.getenv("MIN_FUNDING_RATE_PERCENT", "-1.0"))
MAX_FUNDING_RATE_PERCENT = float(os.getenv("MAX_FUNDING_RATE_PERCENT", "1.0"))
FUTURES_CONTRACT_TYPES = {x.strip().upper() for x in os.getenv("FUTURES_CONTRACT_TYPES", "PERPETUAL").split(",") if x.strip()}

OPTIONS_QUOTE_ASSETS = {x.strip().upper() for x in os.getenv("OPTIONS_QUOTE_ASSETS", "USDT").split(",") if x.strip()}
MIN_OPTIONS_QUOTE_VOLUME = float(os.getenv("MIN_OPTIONS_QUOTE_VOLUME", "0"))
MIN_OPTIONS_TRADES = int(os.getenv("MIN_OPTIONS_TRADES", "0"))
MAX_OPTIONS_SPREAD_PERCENT = float(os.getenv("MAX_OPTIONS_SPREAD_PERCENT", "5.0"))
OPTIONS_MAX_ASSETS = int(os.getenv("OPTIONS_MAX_ASSETS", "500"))

TOKENIZED_MAX_ASSETS = int(os.getenv("TOKENIZED_MAX_ASSETS", "100"))
MAX_TOKENIZED_SPREAD_PERCENT = float(os.getenv("MAX_TOKENIZED_SPREAD_PERCENT", "1.0"))

# Classification Spot des actifs spéciaux : aucune inférence à partir d'un
# suffixe de ticker. TOKENIZED / SPECIAL n'est utilisé que si une métadonnée
# explicite le confirme, si l'API officielle Binance des actifs tokenisés le
# confirme dynamiquement (voir refresh_dynamic_tokenized_spot_bases), ou si le
# baseAsset est déclaré dans cette liste de secours (utilisée quand
# BINANCE_API_KEY est absent ou que l'API est temporairement indisponible).
TOKENIZED_SPOT_BASES = {
    x.strip().upper()
    for x in os.getenv(
        "BINANCE_TOKENIZED_SPOT_BASES",
        "AAPLB,CRCLB,DRAMB,MSTRB,MUB,NVDAB,QQQB,SNDKB,SKHYB,SNXXB,SPCXB,TSLAB",
    ).split(",")
    if x.strip()
}

# Ratio profondeur / volume très supérieur à 100 % : diagnostic uniquement.
# La profondeur est un instantané alors que le volume est cumulé sur 24 h.
DEPTH_VOLUME_ANOMALY_PERCENT = float(os.getenv("DEPTH_VOLUME_ANOMALY_PERCENT", "100"))

# Nombre maximal de bases affichées dans la vue consolidée.
BASE_ASSET_SUMMARY_LIMIT = int(os.getenv("BASE_ASSET_SUMMARY_LIMIT", "20"))

REGIME_WORKERS = int(os.getenv("REGIME_WORKERS", "8"))
REGIME_KLINES_LIMIT = int(os.getenv("REGIME_KLINES_LIMIT", "250"))

# Binance ne publie pas de champ public universel "isStablecoin" dans
# Spot /exchangeInfo. Cette base sert donc de reconnaissance de référence.
# Les actifs supprimés de Binance disparaissent automatiquement du résultat
# puisqu'ils ne sont plus présents dans exchangeInfo.
STABLECOIN_BASES = {
    "USDT", "USDC", "FDUSD", "BUSD", "DAI", "TUSD", "USDP", "USDE",
    "USDD", "FRAX", "PYUSD", "EURC", "USD1", "RLUSD", "XUSD", "EURI",
    "USDG", "USDS", "U", "AEUR", "PAXG", "USD0",
}
STABLECOIN_BASES.update({
    x.strip().upper()
    for x in os.getenv("BINANCE_STABLECOIN_QUOTES", "").split(",")
    if x.strip()
})

# Détection complémentaire prudente pour certains nouveaux tickers
# explicitement liés à USD/EUR, uniquement lorsqu'ils sont quoteAsset actifs.
STABLECOIN_QUOTE_MARKERS = (
    "USDT", "USDC", "FDUSD", "TUSD", "USDP", "USDE", "USDD",
    "PYUSD", "USD1", "RLUSD", "USDG", "USDS", "USD0", "XUSD",
    "EURC", "EURI", "AEUR",
)
LEVERAGED_SUFFIXES = ("UP", "DOWN", "BULL", "BEAR")
LEVERAGED_PATTERNS = ("3L", "3S", "5L", "5S", "2L", "2S")


class BinanceHTTPError(RuntimeError):
    pass


def is_geo_restriction_error(exc: Exception) -> bool:
    """Return True when Binance explicitly blocks the request by geography/eligibility."""
    text = str(exc).lower()
    return "http 451" in text or "451" in text and "unavailable" in text


def format_market_exception(market: str, exc: Exception) -> Tuple[str, str]:
    """Classify market failures so expected Binance restrictions are not reported as code errors."""
    if is_geo_restriction_error(exc):
        return (
            f"{market} indisponible : Binance retourne HTTP 451 (restriction géographique / conditions d'éligibilité depuis le runner GitHub).",
            "unavailable",
        )
    return (f"{market}: {exc}", "error")


def http_get_json(base_url: str, path: str, params: Optional[Dict[str, Any]] = None, headers: Optional[Dict[str, str]] = None) -> Any:
    url = base_url.rstrip("/") + path
    if params:
        query = urlencode({k: v for k, v in params.items() if v is not None})
        if query:
            url += "?" + query
    last_error: Optional[Exception] = None
    for attempt in range(HTTP_RETRIES + 1):
        try:
            request = Request(url, headers={"User-Agent": "BinanceMultiMarketScreener/2.0", **(headers or {})}, method="GET")
            with urlopen(request, timeout=HTTP_TIMEOUT_SECONDS) as response:
                return json.loads(response.read().decode("utf-8"))
        except HTTPError as exc:
            last_error = exc
            retryable = exc.code in {418, 429, 500, 502, 503, 504}
            if not retryable or attempt >= HTTP_RETRIES:
                try:
                    body = exc.read().decode("utf-8")
                except Exception:
                    body = ""
                raise BinanceHTTPError(f"HTTP {exc.code} {path}: {body[:500]}") from exc
            retry_after = exc.headers.get("Retry-After")
            try:
                delay = float(retry_after) if retry_after else min(15.0, 2.0 ** attempt)
            except ValueError:
                delay = min(15.0, 2.0 ** attempt)
            time.sleep(delay)
        except (URLError, TimeoutError, json.JSONDecodeError) as exc:
            last_error = exc
            if attempt >= HTTP_RETRIES:
                raise BinanceHTTPError(f"Request failed {path}: {exc}") from exc
            time.sleep(min(10.0, 2.0 ** attempt))
    raise BinanceHTTPError(f"Request failed {path}: {last_error}")


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


def safe_percent_spread(bid: float, ask: float) -> Optional[float]:
    if bid <= 0 or ask <= 0 or ask < bid:
        return None
    mid = (bid + ask) / 2.0
    return ((ask - bid) / mid) * 100.0 if mid > 0 else None


def is_leveraged_symbol(base_asset: str) -> bool:
    base = base_asset.upper()
    return any(base.endswith(x) for x in LEVERAGED_SUFFIXES + LEVERAGED_PATTERNS)


class CriterionAudit:
    def __init__(self) -> None:
        self.rows: List[Dict[str, Any]] = []
        self.diagnostics: Dict[str, Any] = {}

    def add(self, name: str, before: int, selected: int) -> None:
        rejected = before - selected
        retention = selected / before * 100 if before else 0.0
        rejection = rejected / before * 100 if before else 0.0
        self.rows.append({"criterion": name, "before": before, "selected": selected, "rejected": rejected, "retention": retention, "rejection": rejection})


def apply_criterion(assets: List[Dict[str, Any]], audit: CriterionAudit, name: str, predicate: Callable[[Dict[str, Any]], bool]) -> List[Dict[str, Any]]:
    before = len(assets)
    selected = [asset for asset in assets if predicate(asset)]
    audit.add(name, before, len(selected))
    return selected


# ----------------------------- SPOT -----------------------------
def spot_exchange_info() -> Dict[str, Any]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/exchangeInfo")


def spot_tickers() -> List[Dict[str, Any]]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/ticker/24hr")


def spot_book_tickers() -> List[Dict[str, Any]]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/ticker/bookTicker")


def discover_active_stablecoin_quotes(exchange_info: Dict[str, Any]) -> set[str]:
    """Découvre les stablecoins actuellement actifs comme quoteAsset Spot."""
    active_quotes = {
        str(x.get("quoteAsset", "")).upper().strip()
        for x in exchange_info.get("symbols", [])
        if isinstance(x, dict) and str(x.get("status", "")).upper() == "TRADING"
    }
    discovered = {q for q in active_quotes if q in STABLECOIN_BASES}
    for quote in active_quotes - discovered:
        if any(marker in quote for marker in STABLECOIN_QUOTE_MARKERS):
            discovered.add(quote)
    return discovered


def resolve_spot_quote_assets(exchange_info: Dict[str, Any]) -> set[str]:
    """Résout les quote assets effectifs du run courant."""
    active_quotes = {
        str(x.get("quoteAsset", "")).upper().strip()
        for x in exchange_info.get("symbols", [])
        if isinstance(x, dict)
    }
    if QUOTE_ASSETS:
        return QUOTE_ASSETS & active_quotes
    return discover_active_stablecoin_quotes(exchange_info)


def build_spot_universe(exchange_info: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Construit l'univers Spot en conservant les métadonnées utiles à la classification.

    La classification TOKENIZED / SPECIAL ne doit jamais être déduite d'un simple
    suffixe de ticker. On conserve donc les éventuels flags explicites publiés par
    Binance, ainsi que quelques champs structurels, pour permettre une classification
    sûre lorsque ces métadonnées existent.
    """
    result: List[Dict[str, Any]] = []
    for x in exchange_info.get("symbols", []):
        if not isinstance(x, dict):
            continue
        result.append({
            "market": "SPOT",
            "symbol": x.get("symbol", ""),
            "baseAsset": x.get("baseAsset", ""),
            "quoteAsset": x.get("quoteAsset", ""),
            "status": x.get("status", ""),
            "permissions": x.get("permissions", []),
            "permissionSets": x.get("permissionSets", []),
            "isSpotTradingAllowed": x.get("isSpotTradingAllowed"),
            "isMarginTradingAllowed": x.get("isMarginTradingAllowed"),
            "isTokenized": x.get("isTokenized"),
            "tokenized": x.get("tokenized"),
            "isTokenizedAsset": x.get("isTokenizedAsset"),
            "assetType": x.get("assetType"),
            "productType": x.get("productType"),
        })
    return result


def merge_spot_tickers(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for a in assets:
        t = by_symbol.get(a["symbol"], {})
        a.update(lastPrice=as_float(t.get("lastPrice")), priceChangePercent=as_float(t.get("priceChangePercent")), quoteVolume=as_float(t.get("quoteVolume")), trades=as_int(t.get("count")), volume=as_float(t.get("volume")), weightedAvgPrice=as_float(t.get("weightedAvgPrice")), highPrice=as_float(t.get("highPrice")), lowPrice=as_float(t.get("lowPrice")))


def merge_spot_books(assets: List[Dict[str, Any]], books: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in books if x.get("symbol")}
    for a in assets:
        b = by_symbol.get(a["symbol"], {})
        bid, ask = as_float(b.get("bidPrice")), as_float(b.get("askPrice"))
        a.update(bidPrice=bid, askPrice=ask, spreadPercent=safe_percent_spread(bid, ask))


def spot_order_book(symbol: str) -> Dict[str, Any]:
    return http_get_json(
        SPOT_BASE_URL,
        "/api/v3/depth",
        {"symbol": symbol, "limit": ORDER_BOOK_DEPTH_LIMIT},
    )


def order_book_depth_metrics(book: Dict[str, Any], mid_price: float) -> Dict[str, float]:
    """Calcule la profondeur notionnelle cumulée autour du prix médian."""
    if mid_price <= 0:
        return {
            "depthBidQuote": 0.0,
            "depthAskQuote": 0.0,
            "depthTotalQuote": 0.0,
        }

    band = ORDER_BOOK_DEPTH_PCT / 100.0
    min_bid = mid_price * (1.0 - band)
    max_ask = mid_price * (1.0 + band)

    bid_depth = 0.0
    ask_depth = 0.0

    for level in book.get("bids", []) or []:
        if not isinstance(level, (list, tuple)) or len(level) < 2:
            continue
        price = as_float(level[0])
        quantity = as_float(level[1])
        if price >= min_bid and price > 0 and quantity > 0:
            bid_depth += price * quantity

    for level in book.get("asks", []) or []:
        if not isinstance(level, (list, tuple)) or len(level) < 2:
            continue
        price = as_float(level[0])
        quantity = as_float(level[1])
        if price <= max_ask and price > 0 and quantity > 0:
            ask_depth += price * quantity

    return {
        "depthBidQuote": bid_depth,
        "depthAskQuote": ask_depth,
        "depthTotalQuote": bid_depth + ask_depth,
    }


def merge_spot_order_book_depth(assets: List[Dict[str, Any]], warnings: Optional[List[str]] = None) -> None:
    """Récupère et calcule la profondeur Spot pour les actifs déjà validés jusqu'aux données 24h."""
    if not ORDER_BOOK_DEPTH_ENABLED or not assets:
        return

    workers = max(1, min(ORDER_BOOK_DEPTH_WORKERS, len(assets)))
    failures = 0

    def fetch(asset: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asset["symbol"], spot_order_book(asset["symbol"])

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        future_map = {executor.submit(fetch, asset): asset for asset in assets}
        for future in concurrent.futures.as_completed(future_map):
            asset = future_map[future]
            try:
                symbol, book = future.result()
                bid = as_float(asset.get("bidPrice"))
                ask = as_float(asset.get("askPrice"))
                mid = (bid + ask) / 2.0 if bid > 0 and ask > 0 else 0.0
                metrics = order_book_depth_metrics(book, mid)
                asset.update(metrics)
                asset["orderBookDepthPct"] = ORDER_BOOK_DEPTH_PCT
            except Exception as exc:
                failures += 1
                asset.update(
                    depthBidQuote=0.0,
                    depthAskQuote=0.0,
                    depthTotalQuote=0.0,
                    orderBookDepthPct=ORDER_BOOK_DEPTH_PCT,
                    depthError=str(exc),
                )

    if failures and warnings is not None:
        warnings.append(f"Order Book Depth Spot : {failures} échecs de récupération sur {len(assets)} paires.")


def percentile(values: List[float], fraction: float) -> Optional[float]:
    if not values:
        return None
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = (len(ordered) - 1) * fraction
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    weight = position - lower
    return ordered[lower] + (ordered[upper] - ordered[lower]) * weight


# ============================================================
# DONNÉES ET CALCUL DU RÉGIME CHOP + ADX + ATR
# ============================================================
# Ces fonctions sont volontairement séparées de toute ancienne analyse
# technique : elles sont nécessaires au régime et ne constituent aucun
# filtre d'entrée supplémentaire.
SPOT_KLINES_CACHE: Dict[Tuple[str, str, int], List[List[Any]]] = {}


def spot_klines(symbol: str, interval: Optional[str] = None, limit: Optional[int] = None) -> List[List[Any]]:
    effective_interval = interval or REGIME_INTERVAL
    effective_limit = limit or REGIME_KLINES_LIMIT
    cache_key = (symbol, effective_interval, effective_limit)
    if cache_key in SPOT_KLINES_CACHE:
        return SPOT_KLINES_CACHE[cache_key]

    data = http_get_json(
        SPOT_BASE_URL,
        "/api/v3/klines",
        {"symbol": symbol, "interval": effective_interval, "limit": effective_limit},
    )
    if not isinstance(data, list):
        raise BinanceHTTPError(f"Réponse klines invalide pour {symbol}")
    SPOT_KLINES_CACHE[cache_key] = data
    return data


def atr(highs: List[float], lows: List[float], closes: List[float], period: int) -> Optional[float]:
    if period <= 0 or len(closes) <= period:
        return None
    trs = [
        max(
            highs[i] - lows[i],
            abs(highs[i] - closes[i - 1]),
            abs(lows[i] - closes[i - 1]),
        )
        for i in range(1, len(closes))
    ]
    if len(trs) < period:
        return None
    result = sum(trs[:period]) / period
    for value in trs[period:]:
        result = (result * (period - 1) + value) / period
    return result


def choppiness_index(highs: List[float], lows: List[float], closes: List[float], period: int) -> Optional[float]:
    """CHOP standard : élevé = plus oscillatoire, faible = plus directionnel."""
    if period <= 0 or len(closes) < period + 1:
        return None

    trs = [
        max(
            highs[i] - lows[i],
            abs(highs[i] - closes[i - 1]),
            abs(lows[i] - closes[i - 1]),
        )
        for i in range(1, len(closes))
    ]
    if len(trs) < period:
        return None

    tr_sum = sum(trs[-period:])
    highest = max(highs[-period:])
    lowest = min(lows[-period:])
    price_range = highest - lowest
    if tr_sum <= 0 or price_range <= 0:
        return None
    return 100.0 * math.log10(tr_sum / price_range) / math.log10(period)


def adx(highs: List[float], lows: List[float], closes: List[float], period: int) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    """ADX de Wilder + DI+ / DI-. Retourne force et direction du mouvement."""
    if period <= 0 or len(closes) < period * 2 + 1:
        return None, None, None

    trs: List[float] = []
    plus_dm: List[float] = []
    minus_dm: List[float] = []

    for i in range(1, len(closes)):
        up_move = highs[i] - highs[i - 1]
        down_move = lows[i - 1] - lows[i]
        plus_dm.append(up_move if up_move > down_move and up_move > 0 else 0.0)
        minus_dm.append(down_move if down_move > up_move and down_move > 0 else 0.0)
        trs.append(
            max(
                highs[i] - lows[i],
                abs(highs[i] - closes[i - 1]),
                abs(lows[i] - closes[i - 1]),
            )
        )

    if len(trs) < period:
        return None, None, None

    sm_tr = sum(trs[:period])
    sm_plus = sum(plus_dm[:period])
    sm_minus = sum(minus_dm[:period])
    dx_values: List[float] = []
    plus_di_values: List[float] = []
    minus_di_values: List[float] = []

    def append_di() -> None:
        if sm_tr <= 0:
            plus_di_values.append(0.0)
            minus_di_values.append(0.0)
            dx_values.append(0.0)
            return
        pdi = 100.0 * sm_plus / sm_tr
        mdi = 100.0 * sm_minus / sm_tr
        plus_di_values.append(pdi)
        minus_di_values.append(mdi)
        denom = pdi + mdi
        dx_values.append(100.0 * abs(pdi - mdi) / denom if denom > 0 else 0.0)

    append_di()
    for i in range(period, len(trs)):
        sm_tr = sm_tr - (sm_tr / period) + trs[i]
        sm_plus = sm_plus - (sm_plus / period) + plus_dm[i]
        sm_minus = sm_minus - (sm_minus / period) + minus_dm[i]
        append_di()

    if len(dx_values) < period:
        return None, None, None

    adx_value = sum(dx_values[:period]) / period
    for value in dx_values[period:]:
        adx_value = ((adx_value * (period - 1)) + value) / period

    return adx_value, plus_di_values[-1], minus_di_values[-1]


def interpret_market_structure(chop_value: Optional[float], adx_value: Optional[float]) -> Tuple[str, str]:
    """Croise CHOP et ADX sans transformer le régime en filtre."""
    if chop_value is None or adx_value is None:
        return "NON DISPONIBLE", "NON DISPONIBLE"

    if chop_value <= CHOP_TREND_THRESHOLD:
        if adx_value >= ADX_TREND_THRESHOLD:
            nature = "TENDANCE FORTE" if adx_value >= ADX_STRONG_THRESHOLD else "TENDANCE"
            structure = "DIRECTIONNELLE"
        else:
            nature = "TRANSITION"
            structure = "TENDANCE NAISSANTE"
    elif chop_value >= CHOP_RANGE_THRESHOLD:
        if adx_value < ADX_TREND_THRESHOLD:
            nature = "RANGE"
            structure = "RANGE"
        else:
            nature = "TRANSITION"
            structure = "CONFLIT"
    else:
        nature = "TRANSITION"
        structure = "DIRECTIONNELLE" if adx_value >= ADX_TREND_THRESHOLD else "NEUTRE"

    return nature, structure


def classify_market_regime(chop_value: Optional[float], adx_value: Optional[float], atr_percent: Optional[float]) -> str:
    if chop_value is None or adx_value is None or atr_percent is None:
        return "NON DISPONIBLE"

    nature, structure = interpret_market_structure(chop_value, adx_value)

    if atr_percent < ATR_LOW_PERCENT:
        intensity = "CALME"
    elif atr_percent < ATR_HIGH_PERCENT:
        intensity = "ACTIVE"
    elif atr_percent < ATR_EXTREME_PERCENT:
        intensity = "VOLATILE"
    else:
        intensity = "TRÈS VOLATILE"

    if nature in {"RANGE", "TENDANCE", "TENDANCE FORTE"}:
        return f"{nature} — {intensity}"
    return f"TRANSITION — {structure} — {intensity}"


def classify_market_direction(plus_di: Optional[float], minus_di: Optional[float], adx_value: Optional[float]) -> str:
    """Donne le sens directionnel uniquement lorsque l'ADX confirme une structure.

    ADX mesure la force, pas le sens. DI+ / DI- permettent ici de distinguer
    une tendance haussière d'une tendance baissière sans modifier le filtre.
    """
    if plus_di is None or minus_di is None or adx_value is None:
        return "NON DISPONIBLE"
    if adx_value < ADX_TREND_THRESHOLD:
        return "NEUTRE"
    if plus_di > minus_di:
        return "HAUSSIÈRE"
    if minus_di > plus_di:
        return "BAISSIÈRE"
    return "NEUTRE"


def merge_spot_regime(assets: List[Dict[str, Any]], warnings: Optional[List[str]] = None) -> None:
    """Calcule CHOP, ADX et ATR% sur les survivants du spread.

    Les trois indicateurs sont au même niveau conceptuel : aucun ne sert de
    filtre d'exclusion. Le résultat est ensuite interprété en régime de marché.
    """
    if not REGIME_ENABLED or not assets:
        return

    workers = max(1, min(REGIME_WORKERS, len(assets)))
    failures = 0
    error_counts: Dict[str, int] = {}
    error_examples: List[str] = []
    min_history = max(60, CHOP_PERIOD + 2, ADX_PERIOD * 2 + 2, ATR_REGIME_PERIOD + 2)

    def fetch(asset: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # Réutilise les bougies déjà récupérées par le filtre "10. Ancienneté
        # minimale" quand il a tourné (voir screen_spot) : on évite ainsi un
        # second appel /api/v3/klines pour le même actif juste après le premier.
        cached = asset.pop("_historyKlines", None)
        if cached is not None:
            klines = cached[-REGIME_KLINES_LIMIT:] if REGIME_KLINES_LIMIT else cached
        else:
            klines = spot_klines(asset["symbol"], REGIME_INTERVAL, REGIME_KLINES_LIMIT)
        if len(klines) < min_history:
            return asset["symbol"], {"error": "Historique insuffisant"}
        highs = [as_float(row[2]) for row in klines]
        lows = [as_float(row[3]) for row in klines]
        closes = [as_float(row[4]) for row in klines]
        chop_value = choppiness_index(highs, lows, closes, CHOP_PERIOD)
        adx_value, plus_di, minus_di = adx(highs, lows, closes, ADX_PERIOD)
        atr_value = atr(highs, lows, closes, ATR_REGIME_PERIOD)
        current = closes[-1] if closes else 0.0
        atr_percent = atr_value / current * 100.0 if atr_value is not None and current > 0 else None
        regime = classify_market_regime(chop_value, adx_value, atr_percent)
        market_nature, market_structure = interpret_market_structure(chop_value, adx_value)
        market_direction = classify_market_direction(plus_di, minus_di, adx_value)
        return asset["symbol"], {
            "chop": chop_value,
            "adx": adx_value,
            "plusDI": plus_di,
            "minusDI": minus_di,
            "regimeAtrPercent": atr_percent,
            "marketNature": market_nature,
            "marketStructure": market_structure,
            "marketDirection": market_direction,
            "marketRegime": regime,
        }

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        future_map = {executor.submit(fetch, asset): asset for asset in assets}
        for future in concurrent.futures.as_completed(future_map):
            asset = future_map[future]
            try:
                _, values = future.result()
                asset["regimeInterval"] = REGIME_INTERVAL
                asset["chopPeriod"] = CHOP_PERIOD
                asset["adxPeriod"] = ADX_PERIOD
                asset["atrRegimePeriod"] = ATR_REGIME_PERIOD
                asset.update(values)
                if values.get("error"):
                    asset["regimeError"] = values["error"]
                    failures += 1
            except Exception as exc:
                failures += 1
                error_text = str(exc) or exc.__class__.__name__
                error_counts[error_text] = error_counts.get(error_text, 0) + 1
                if len(error_examples) < 5:
                    error_examples.append(f"{asset.get('symbol', '?')}: {error_text}")
                asset["regimeError"] = error_text
                asset.update(chop=None, adx=None, plusDI=None, minusDI=None, regimeAtrPercent=None, marketNature="NON DISPONIBLE", marketStructure="NON DISPONIBLE", marketDirection="NON DISPONIBLE", marketRegime="NON DISPONIBLE")

    # Diagnostics visibles dans l'e-mail et la console : aucune erreur de régime
    # ne doit désormais être silencieusement masquée.
    if warnings is not None:
        if failures:
            warnings.append(f"Régime CHOP/ADX/ATR Spot : {failures} échecs de calcul sur {len(assets)} paires. Exemples : {' | '.join(error_examples)}")

    for asset in assets:
        pass

    return


def build_regime_diagnostics(assets: List[Dict[str, Any]]) -> Dict[str, Any]:
    valid_assets = [
        a for a in assets
        if a.get("chop") is not None and a.get("adx") is not None and a.get("regimeAtrPercent") is not None
    ]
    chop_values = [as_float(a.get("chop")) for a in valid_assets]
    adx_values = [as_float(a.get("adx")) for a in valid_assets]
    atr_values = [as_float(a.get("regimeAtrPercent")) for a in valid_assets]

    # family_counts reprend exactement la même classification (regime_family)
    # que la Synthèse en tête de rapport, pour que les deux tableaux restent
    # cohérents. L'ancienne version comptait ici "marketRegime" (qui inclut
    # l'intensité ATR, ex. "TENDANCE — ACTIVE") alors que le tableau HTML
    # cherchait des clés simples ("TENDANCE FORTE", "CONFLIT", ...) : la
    # correspondance ne pouvait jamais matcher et la table "Classification
    # finale" affichait 0 partout.
    family_counts: Dict[str, int] = {}
    nature_counts: Dict[str, int] = {}
    direction_counts: Dict[str, int] = {}
    atr_intensity_counts: Dict[str, int] = {}

    chop_zones = ("TENDANCE", "TRANSITION", "RANGE")
    adx_zones = ("FAIBLE", "TENDANCE", "FORTE")
    structure_matrix = {chop: {adx: 0 for adx in adx_zones} for chop in chop_zones}

    raw_contradictions = 0
    final_conflicts = 0
    for asset in assets:
        family = regime_family(asset)
        family_counts[family] = family_counts.get(family, 0) + 1
        nature = asset.get("marketNature") or "NON DISPONIBLE"
        nature_counts[nature] = nature_counts.get(nature, 0) + 1
        direction = asset.get("marketDirection") or "NON DISPONIBLE"
        direction_counts[direction] = direction_counts.get(direction, 0) + 1

        atr_value = asset.get("regimeAtrPercent")
        if atr_value is not None:
            atr_value = as_float(atr_value)
            if atr_value < ATR_LOW_PERCENT:
                intensity = "CALME"
            elif atr_value < ATR_HIGH_PERCENT:
                intensity = "ACTIVE"
            elif atr_value < ATR_EXTREME_PERCENT:
                intensity = "VOLATILE"
            else:
                intensity = "TRÈS VOLATILE"
            atr_intensity_counts[intensity] = atr_intensity_counts.get(intensity, 0) + 1

        chop = asset.get("chop")
        adx_value = asset.get("adx")
        if chop is None or adx_value is None:
            continue
        chop = as_float(chop)
        adx_value = as_float(adx_value)
        if chop <= CHOP_TREND_THRESHOLD:
            chop_zone = "TENDANCE"
        elif chop >= CHOP_RANGE_THRESHOLD:
            chop_zone = "RANGE"
        else:
            chop_zone = "TRANSITION"
        if adx_value < ADX_TREND_THRESHOLD:
            adx_zone = "FAIBLE"
        elif adx_value < ADX_STRONG_THRESHOLD:
            adx_zone = "TENDANCE"
        else:
            adx_zone = "FORTE"
        structure_matrix[chop_zone][adx_zone] += 1
        if (chop >= CHOP_RANGE_THRESHOLD and adx_value >= ADX_TREND_THRESHOLD) or (chop <= CHOP_TREND_THRESHOLD and adx_value < ADX_TREND_THRESHOLD):
            raw_contradictions += 1
        if regime_family(asset) == "CONFLIT":
            final_conflicts += 1

    def stats(values: List[float]) -> Dict[str, Optional[float]]:
        return {
            "minimum": min(values) if values else None,
            "p25": percentile(values, 0.25),
            "median": percentile(values, 0.50),
            "mean": sum(values) / len(values) if values else None,
            "p75": percentile(values, 0.75),
            "maximum": max(values) if values else None,
        }

    return {
        "universe_count": len(assets),
        "valid_count": len(valid_assets),
        "missing_count": len(assets) - len(valid_assets),
        "family_counts": dict(sorted(family_counts.items(), key=lambda x: (-x[1], x[0]))),
        "nature_counts": dict(sorted(nature_counts.items(), key=lambda x: (-x[1], x[0]))),
        "direction_counts": dict(sorted(direction_counts.items(), key=lambda x: (-x[1], x[0]))),
        "atr_intensity_counts": dict(sorted(atr_intensity_counts.items(), key=lambda x: (-x[1], x[0]))),
        "structure_matrix": structure_matrix,
        "conflict_count": final_conflicts,
        "raw_contradiction_count": raw_contradictions,
        "chop": stats(chop_values),
        "adx": stats(adx_values),
        "atr": stats(atr_values),
    }

def bars_per_day(interval: str) -> float:
    """Bougies par jour pour un intervalle Binance (ex. '1h', '15m', '1d').

    Généralise le calcul d'ancienneté minimale : la version précédente
    multipliait toujours par 24, ce qui n'est juste que pour REGIME_INTERVAL
    == "1h" et aurait donné un nombre de bougies requis erroné pour tout
    autre intervalle (le if/else en place ne changeait d'ailleurs rien,
    les deux branches calculaient exactement la même chose).
    """
    unit = interval[-1] if interval else "h"
    try:
        value = int(interval[:-1])
    except (ValueError, IndexError):
        value = 1
    minutes_per_bar = {"m": value, "h": value * 60, "d": value * 1440, "w": value * 10080}.get(unit, 60)
    return 1440.0 / minutes_per_bar if minutes_per_bar > 0 else 24.0


def screen_spot(assets: List[Dict[str, Any]], quote_assets: Optional[set[str]] = None, warnings: Optional[List[str]] = None) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    effective_quotes = quote_assets if quote_assets is not None else QUOTE_ASSETS
    assets = apply_criterion(assets, audit, "1. Status TRADING", lambda x: x["status"] == "TRADING")
    assets = apply_criterion(assets, audit, "2. Permission SPOT", lambda x: not x["permissions"] or "SPOT" in x["permissions"])
    assets = apply_criterion(assets, audit, "3. Quote asset autorisé", lambda x: x["quoteAsset"] in effective_quotes)
    if EXCLUDE_STABLECOINS:
        assets = apply_criterion(assets, audit, "4. Exclusion stablecoins", lambda x: x["baseAsset"].upper() not in STABLECOIN_BASES)
    if EXCLUDE_LEVERAGED_TOKENS:
        assets = apply_criterion(assets, audit, "5. Exclusion tokens à levier", lambda x: not is_leveraged_symbol(x["baseAsset"]))
    assets = apply_criterion(assets, audit, "6. Données 24h disponibles", lambda x: x["lastPrice"] > 0)

    # L'ordre demandé est volontairement : VOLUME 24h en premier, puis Order Book Depth.
    # Les deux critères occupent donc les positions 7 et 8, entre les données 24h et le prix minimum.
    # 7. Volume quote 24h minimum
    # Diagnostic indépendant du seuil actif : il permet d'évaluer le seuil de volume
    # après plusieurs runs sans modifier prématurément le filtre.
    volume_universe = [a for a in assets if a.get("quoteVolume", 0) > 0]
    audit.diagnostics["volume_distribution"] = {
        threshold: sum(1 for a in volume_universe if a.get("quoteVolume", 0) >= threshold)
        for threshold in (1_000_000, 2_000_000, 5_000_000, 10_000_000, 20_000_000, 50_000_000, 100_000_000, 500_000_000, 1_000_000_000)
    }
    audit.diagnostics["volume_universe_count"] = len(volume_universe)
    audit.diagnostics["volume_classes"] = {
        "< $250k": sum(1 for a in volume_universe if a.get("quoteVolume", 0) < 250_000),
        "$250k – $500k": sum(1 for a in volume_universe if 250_000 <= a.get("quoteVolume", 0) < 500_000),
        "$500k – $1M": sum(1 for a in volume_universe if 500_000 <= a.get("quoteVolume", 0) < 1_000_000),
        "$1M – $2M": sum(1 for a in volume_universe if 1_000_000 <= a.get("quoteVolume", 0) < 2_000_000),
        "$2M – $5M": sum(1 for a in volume_universe if 2_000_000 <= a.get("quoteVolume", 0) < 5_000_000),
        "$5M – $10M": sum(1 for a in volume_universe if 5_000_000 <= a.get("quoteVolume", 0) < 10_000_000),
        ">= $10M": sum(1 for a in volume_universe if a.get("quoteVolume", 0) >= 10_000_000),
    }
    assets = apply_criterion(assets, audit, "7. Volume quote 24h minimum", lambda x: x["quoteVolume"] >= MIN_24H_QUOTE_VOLUME)

    # 8. Order Book Depth : calculé uniquement après le filtre de volume,
    # afin d'éviter des appels /api/v3/depth inutiles sur les marchés à faible volume.
    if ORDER_BOOK_DEPTH_ENABLED:
        merge_spot_order_book_depth(assets, warnings)
        for asset in assets:
            volume = as_float(asset.get("quoteVolume"))
            depth = as_float(asset.get("depthTotalQuote"))
            asset["depthToVolumePercent"] = (depth / volume * 100.0) if volume > 0 else None
        asset["depthVolumeStatus"] = depth_volume_status(asset)
        assets = apply_criterion(
            assets,
            audit,
            "8. Épaisseur carnet d'ordres minimum",
            lambda x: x.get("depthTotalQuote", 0.0) >= MIN_ORDER_BOOK_DEPTH_QUOTE,
        )
    else:
        audit.add("8. Épaisseur carnet d'ordres minimum", len(assets), len(assets))

    # 9. Spread maximum
    assets = apply_criterion(assets, audit, "9. Spread maximum", lambda x: x["spreadPercent"] is not None and x["spreadPercent"] <= MAX_SPREAD_PERCENT)

    # 10. Ancienneté minimale : au moins MIN_HISTORY_DAYS jours de bougies
    # REGIME_INTERVAL disponibles. MIN_HISTORY_DAYS <= 0 désactive le filtre
    # sans appel réseau supplémentaire.
    #
    # Les bougies récupérées ici sont mises en cache sur chaque actif
    # (_historyKlines) et réutilisées telles quelles par merge_spot_regime()
    # pour le calcul CHOP/ADX/ATR, afin d'éviter un second appel
    # /api/v3/klines sur les mêmes actifs juste après. Avant ce correctif,
    # 720 bougies (30 jours à 1h) étaient récupérées ici puis jetées après
    # la seule vérification de longueur, puis 250 autres étaient
    # re-récupérées juste après pour le régime — ce doublon, en plus d'être
    # séquentiel (un appel HTTP à la fois), explique le passage d'environ 30s
    # à 118s de durée totale de run une fois ce filtre ajouté.
    if MIN_HISTORY_DAYS > 0 and assets:
        required_history_bars = max(1, int(math.ceil(MIN_HISTORY_DAYS * bars_per_day(REGIME_INTERVAL))))
        history_fetch_limit = max(required_history_bars, REGIME_KLINES_LIMIT) if REGIME_ENABLED else required_history_bars

        def fetch_history(asset: Dict[str, Any]) -> None:
            try:
                klines = spot_klines(asset["symbol"], REGIME_INTERVAL, history_fetch_limit)
            except Exception as exc:
                asset["historyError"] = str(exc)
                asset["_historyOk"] = False
                return
            asset["_historyKlines"] = klines
            asset["_historyOk"] = len(klines) >= required_history_bars

        history_workers = max(1, min(REGIME_WORKERS, len(assets)))
        with concurrent.futures.ThreadPoolExecutor(max_workers=history_workers) as executor:
            list(executor.map(fetch_history, assets))

        assets = apply_criterion(assets, audit, "10. Ancienneté minimale", lambda x: x.get("_historyOk", False))
    else:
        audit.add("10. Ancienneté minimale", len(assets), len(assets))

    # 11. Régime de marché : CHOP + ADX + ATR au même niveau.
    # Calculé sur tous les survivants du spread. Aucun des trois indicateurs
    # n'est un filtre d'exclusion à cette étape : ils servent à caractériser
    # la nature, la force directionnelle et l'amplitude de l'actif.
    if REGIME_ENABLED:
        merge_spot_regime(assets, warnings)
        audit.diagnostics["regime"] = build_regime_diagnostics(assets)
    else:
        audit.diagnostics["regime"] = build_regime_diagnostics(assets)
    audit.add("11. Interprétation CHOP + ADX + ATR", len(assets), len(assets))
    return assets, audit


# ----------------------------- MARGIN -----------------------------
def build_margin_market(spot_assets: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    result = []
    for asset in spot_assets:
        copied = dict(asset)
        copied["market"] = "MARGIN"
        copied["marginEligibility"] = "ACCOUNT_DEPENDENT"
        result.append(copied)
    return result


# ----------------------------- FUTURES -----------------------------
def futures_exchange_info(base_url: str, path: str) -> Dict[str, Any]:
    return http_get_json(base_url, path)


def futures_tickers(base_url: str, path: str) -> List[Dict[str, Any]]:
    return http_get_json(base_url, path)


def futures_book_tickers(base_url: str, path: str) -> List[Dict[str, Any]]:
    return http_get_json(base_url, path)


def futures_premium_index(base_url: str, path: str) -> Any:
    return http_get_json(base_url, path)


def build_usdm_universe(exchange_info: Dict[str, Any]) -> List[Dict[str, Any]]:
    result = []
    for x in exchange_info.get("symbols", []):
        contract = str(x.get("contractType", "")).upper()
        quote = str(x.get("quoteAsset", "")).upper()
        if contract not in FUTURES_CONTRACT_TYPES or quote not in FUTURES_QUOTE_ASSETS:
            continue
        result.append({"market": "USDⓈ-M FUTURES", "symbol": x.get("symbol", ""), "pair": x.get("pair", ""), "baseAsset": x.get("baseAsset", ""), "quoteAsset": quote, "contractType": contract, "status": x.get("status", x.get("contractStatus", ""))})
    return result


def build_coinm_universe(exchange_info: Dict[str, Any]) -> List[Dict[str, Any]]:
    result = []
    for x in exchange_info.get("symbols", []):
        contract = str(x.get("contractType", "")).upper()
        if contract not in FUTURES_CONTRACT_TYPES:
            continue
        result.append({"market": "COIN-M FUTURES", "symbol": x.get("symbol", ""), "pair": x.get("pair", ""), "baseAsset": x.get("baseAsset", ""), "quoteAsset": x.get("quoteAsset", ""), "marginAsset": x.get("marginAsset", ""), "contractType": contract, "status": x.get("contractStatus", x.get("status", ""))})
    return result


def merge_futures_tickers(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for a in assets:
        t = by_symbol.get(a["symbol"], {})
        quote_volume = as_float(t.get("quoteVolume"))
        if quote_volume <= 0:
            quote_volume = as_float(t.get("baseVolume"))
        a.update(lastPrice=as_float(t.get("lastPrice")), priceChangePercent=as_float(t.get("priceChangePercent")), volume=as_float(t.get("volume")), quoteVolume=quote_volume, trades=as_int(t.get("count")), highPrice=as_float(t.get("highPrice")), lowPrice=as_float(t.get("lowPrice")))


def merge_futures_books(assets: List[Dict[str, Any]], books: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in books if x.get("symbol")}
    for a in assets:
        b = by_symbol.get(a["symbol"], {})
        bid, ask = as_float(b.get("bidPrice")), as_float(b.get("askPrice"))
        a.update(bidPrice=bid, askPrice=ask, spreadPercent=safe_percent_spread(bid, ask))


def merge_funding(assets: List[Dict[str, Any]], funding_data: Any) -> None:
    if isinstance(funding_data, dict):
        funding_data = [funding_data]
    by_symbol = {x.get("symbol"): x for x in (funding_data or []) if x.get("symbol")}
    for a in assets:
        item = by_symbol.get(a["symbol"], {})
        if "lastFundingRate" in item:
            a["fundingRate"] = as_float(item.get("lastFundingRate")) * 100.0


def screen_futures(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Contrat TRADING", lambda x: x["status"] == "TRADING")
    assets = apply_criterion(assets, audit, "2. Données 24h disponibles", lambda x: x["lastPrice"] > 0)
    assets = apply_criterion(assets, audit, "3. Volume quote minimum", lambda x: x["quoteVolume"] >= MIN_FUTURES_QUOTE_VOLUME)
    assets = apply_criterion(assets, audit, "4. Trades minimum", lambda x: x["trades"] >= MIN_FUTURES_TRADES)
    assets = apply_criterion(assets, audit, "5. Spread maximum", lambda x: x["spreadPercent"] is not None and x["spreadPercent"] <= MAX_FUTURES_SPREAD_PERCENT)
    assets = apply_criterion(assets, audit, "6. Funding disponible", lambda x: "fundingRate" in x)
    assets = apply_criterion(assets, audit, "7. Funding dans la plage autorisée", lambda x: MIN_FUNDING_RATE_PERCENT <= x["fundingRate"] <= MAX_FUNDING_RATE_PERCENT)
    return assets, audit


# ----------------------------- OPTIONS -----------------------------
def options_exchange_info() -> Dict[str, Any]:
    return http_get_json(OPTIONS_BASE_URL, "/eapi/v1/exchangeInfo")


def options_tickers() -> List[Dict[str, Any]]:
    return http_get_json(OPTIONS_BASE_URL, "/eapi/v1/ticker")


def build_options_universe(exchange_info: Dict[str, Any]) -> List[Dict[str, Any]]:
    result = []
    for x in exchange_info.get("optionSymbols", []):
        quote = str(x.get("quoteAsset", "")).upper()
        if quote not in OPTIONS_QUOTE_ASSETS:
            continue
        result.append({"market": "OPTIONS", "symbol": x.get("symbol", ""), "underlying": x.get("underlying", ""), "quoteAsset": quote, "side": x.get("side", ""), "strikePrice": as_float(x.get("strikePrice")), "expiryDate": x.get("expiryDate"), "status": x.get("status", "")})
    return result


def merge_option_tickers(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for a in assets:
        t = by_symbol.get(a["symbol"], {})
        bid, ask = as_float(t.get("bidPrice")), as_float(t.get("askPrice"))
        a.update(lastPrice=as_float(t.get("lastPrice")), priceChangePercent=as_float(t.get("priceChangePercent")), volume=as_float(t.get("volume")), quoteVolume=as_float(t.get("amount")), trades=as_int(t.get("tradeCount")), bidPrice=bid, askPrice=ask, spreadPercent=safe_percent_spread(bid, ask))


def screen_options(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Option TRADING", lambda x: x["status"] == "TRADING")
    assets = apply_criterion(assets, audit, "2. Prix disponible", lambda x: x["lastPrice"] > 0)
    assets = apply_criterion(assets, audit, "3. Volume disponible", lambda x: x["quoteVolume"] >= MIN_OPTIONS_QUOTE_VOLUME)
    assets = apply_criterion(assets, audit, "4. Trades minimum", lambda x: x["trades"] >= MIN_OPTIONS_TRADES)
    assets = apply_criterion(assets, audit, "5. Spread maximum", lambda x: x["spreadPercent"] is not None and x["spreadPercent"] <= MAX_OPTIONS_SPREAD_PERCENT)
    assets.sort(key=lambda x: x["quoteVolume"], reverse=True)
    if OPTIONS_MAX_ASSETS > 0:
        assets = assets[:OPTIONS_MAX_ASSETS]
    return assets, audit


# ----------------------------- TOKENIZED STOCKS -----------------------------
def tokenized_headers() -> Dict[str, str]:
    if not BINANCE_API_KEY:
        raise BinanceHTTPError("BINANCE_API_KEY absent")
    return {"X-MBX-APIKEY": BINANCE_API_KEY}


def tokenized_exchange_info() -> Dict[str, Any]:
    return http_get_json(TOKENIZED_BASE_URL, "/sapi/v1/equity/market/exchangeInfo", headers=tokenized_headers())


def tokenized_assets_info() -> Any:
    return http_get_json(TOKENIZED_BASE_URL, "/sapi/v1/equity/market/tokenized-assets", headers=tokenized_headers())


def tokenized_quote(symbol: str) -> Dict[str, Any]:
    return http_get_json(TOKENIZED_BASE_URL, "/sapi/v1/equity/market/quote", params={"symbol": symbol}, headers=tokenized_headers())


def refresh_dynamic_tokenized_spot_bases(warnings: Optional[List[str]] = None) -> int:
    """Enrichit dynamiquement TOKENIZED_SPOT_BASES depuis l'endpoint officiel
    Binance des actifs tokenisés (tokenized-assets), indépendamment de
    ENABLE_TOKENIZED_STOCKS puisqu'il s'agit ici de classer des paires Spot,
    pas d'exécuter le screening du marché Tokenized Stocks lui-même.

    Convention utilisée : le baseAsset Spot d'une action tokenisée xStocks est
    toujours assetCode + "B" (ex. AAPL -> AAPLB, NVDA -> NVDAB). Cette
    convention n'est appliquée qu'à des codes renvoyés dynamiquement par l'API
    Binance ; elle ne sert jamais à deviner la nature d'un ticker Spot à partir
    de son seul texte. La liste statique BINANCE_TOKENIZED_SPOT_BASES reste en
    place comme filet de sécurité si la clé API est absente ou si l'appel échoue.

    Retourne le nombre de bases nouvellement ajoutées (0 si BINANCE_API_KEY est
    absent, si l'appel échoue, ou si tout était déjà couvert par la liste statique).
    """
    if not BINANCE_API_KEY:
        return 0
    try:
        tokenized_assets = tokenized_assets_info()
    except Exception as exc:
        if warnings is not None:
            warnings.append(f"Classification TOKENIZED/SPECIAL dynamique indisponible : {exc}")
        return 0
    if not isinstance(tokenized_assets, list):
        return 0
    dynamic_bases = {
        str(item.get("assetCode", "")).strip().upper() + "B"
        for item in tokenized_assets
        if isinstance(item, dict) and str(item.get("assetCode", "")).strip()
    }
    added = dynamic_bases - TOKENIZED_SPOT_BASES
    TOKENIZED_SPOT_BASES.update(dynamic_bases)
    return len(added)


def build_tokenized_universe(exchange_info: Dict[str, Any], tokenized_assets: Any) -> List[Dict[str, Any]]:
    token_map = {}
    if isinstance(tokenized_assets, list):
        for item in tokenized_assets:
            code = item.get("assetCode")
            if code:
                token_map[code] = item
    result = []
    for item in exchange_info.get("symbols", []):
        symbol = item.get("symbol", "")
        tradability = item.get("tradability", "NONE")
        if tradability == "NONE":
            continue
        token = token_map.get(symbol, {})
        result.append({"market": "TOKENIZED STOCKS", "symbol": symbol, "tradability": tradability, "overnightSupported": item.get("overnightSupported", False), "fractionable": item.get("fractionable", False), "underlyingEquitySymbol": token.get("underlyingEquitySymbol", ""), "assetName": token.get("assetName", "")})
    return result


def merge_tokenized_quotes(assets: List[Dict[str, Any]]) -> None:
    def fetch(asset: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asset["symbol"], tokenized_quote(asset["symbol"])
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(8, max(1, REGIME_WORKERS))) as executor:
        futures = [executor.submit(fetch, a) for a in assets]
        for future in concurrent.futures.as_completed(futures):
            try:
                symbol, quote = future.result()
                for asset in assets:
                    if asset["symbol"] == symbol:
                        bid, ask = as_float(quote.get("bidPrice")), as_float(quote.get("askPrice"))
                        asset.update(bidPrice=bid, askPrice=ask, bidSize=as_float(quote.get("bidSize")), askSize=as_float(quote.get("askSize")), spreadPercent=safe_percent_spread(bid, ask))
                        break
            except Exception:
                continue


def screen_tokenized(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Tradabilité", lambda x: x["tradability"] in {"BUY_SELL", "BUY", "SELL"})
    assets = apply_criterion(assets, audit, "2. Quote disponible", lambda x: x.get("bidPrice", 0) > 0 and x.get("askPrice", 0) > 0)
    assets = apply_criterion(assets, audit, "3. Spread maximum", lambda x: x.get("spreadPercent") is not None and x["spreadPercent"] <= MAX_TOKENIZED_SPREAD_PERCENT)
    return assets, audit


# ----------------------------- ANALYSE DU RÉGIME -----------------------------
# Le screener s'arrête volontairement ici pour l'analyse technique :
# CHOP + ADX + ATR sont les trois seuls indicateurs de marché interprétés.

# ----------------------------- REPORTING -----------------------------
def format_number(value: Any, decimals: int = 2) -> str:
    try:
        return f"{float(value):,.{decimals}f}"
    except (TypeError, ValueError):
        return "-"


def html_escape(value: Any) -> str:
    text = "" if value is None else str(value)
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def regime_family(asset: Dict[str, Any]) -> str:
    nature = asset.get("marketNature") or "NON DISPONIBLE"
    structure = asset.get("marketStructure") or "NON DISPONIBLE"
    if nature == "TENDANCE FORTE":
        return "TENDANCE FORTE"
    if nature == "TENDANCE":
        return "TENDANCE"
    if nature == "RANGE":
        return "RANGE"
    if nature == "TRANSITION" and structure == "DIRECTIONNELLE":
        return "TRANSITION DIRECTIONNELLE"
    if nature == "TRANSITION" and structure == "CONFLIT":
        return "CONFLIT"
    if nature == "TRANSITION":
        return "TRANSITION NEUTRE"
    return "NON DISPONIBLE"


def regime_priority(asset: Dict[str, Any]) -> int:
    return {
        "TENDANCE FORTE": 6,
        "TENDANCE": 5,
        "TRANSITION DIRECTIONNELLE": 4,
        "CONFLIT": 3,
        "TRANSITION NEUTRE": 2,
        "RANGE": 1,
        "NON DISPONIBLE": 0,
    }.get(regime_family(asset), 0)


def atr_intensity(asset: Dict[str, Any]) -> str:
    value = asset.get("regimeAtrPercent")
    if value is None:
        return "NON DISPONIBLE"
    value = as_float(value)
    if value < ATR_LOW_PERCENT:
        return "CALME"
    if value < ATR_HIGH_PERCENT:
        return "ACTIVE"
    if value < ATR_EXTREME_PERCENT:
        return "VOLATILE"
    return "TRÈS VOLATILE"


def final_interpretation(asset: Dict[str, Any]) -> str:
    family = regime_family(asset)
    direction = asset.get("marketDirection") or "NEUTRE"
    intensity = atr_intensity(asset)
    if family == "TENDANCE FORTE":
        return f"TENDANCE FORTE — {direction} — {intensity}"
    if family == "TENDANCE":
        return f"TENDANCE — {direction} — {intensity}"
    if family == "TRANSITION DIRECTIONNELLE":
        return f"TRANSITION DIRECTIONNELLE — {direction} — {intensity}"
    if family == "CONFLIT":
        return f"CONFLIT — {direction} — {intensity}"
    if family == "TRANSITION NEUTRE":
        return f"TRANSITION NEUTRE — {intensity}"
    if family == "RANGE":
        return f"RANGE — {intensity}"
    return "NON DISPONIBLE"


def asset_category(asset: Dict[str, Any]) -> str:
    """Classe le Spot sans jamais inférer la nature depuis le ticker seul.

    Priorité :
    1) métadonnée explicite Binance ;
    2) TOKENIZED_SPOT_BASES, enrichie dynamiquement en début de run par
       refresh_dynamic_tokenized_spot_bases() depuis l'API officielle Binance
       (tokenized-assets) quand BINANCE_API_KEY est configuré, avec la liste
       statique BINANCE_TOKENIZED_SPOT_BASES comme filet de sécurité ;
    3) SPOT / CRYPTO pour les autres actifs Spot.

    Dans les deux cas (dynamique ou statique), la classification part d'un
    code d'actif confirmé par Binance (jamais d'une règle implicite du type
    ``baseAsset.endswith("B")`` appliquée à un ticker Spot brut).
    """
    if asset.get("market") != "SPOT":
        return asset.get("market", "AUTRE")

    explicit_tokenized = (
        asset.get("isTokenized") is True
        or asset.get("tokenized") is True
        or asset.get("isTokenizedAsset") is True
        or str(asset.get("assetType", "")).upper() in {"TOKENIZED", "TOKENIZED_STOCK", "STOCK_TOKEN"}
        or str(asset.get("productType", "")).upper() in {"TOKENIZED", "TOKENIZED_STOCK", "STOCK_TOKEN"}
    )
    if explicit_tokenized:
        return "SPOT / TOKENIZED / SPECIAL"

    base = str(asset.get("baseAsset", "")).upper()
    if base in TOKENIZED_SPOT_BASES:
        return "SPOT / TOKENIZED / SPECIAL"

    return "SPOT / CRYPTO"


def depth_volume_status(asset: Dict[str, Any]) -> str:
    ratio = asset.get("depthToVolumePercent")
    if ratio is None:
        return "NON DISPONIBLE"
    return "EXCEPTIONNELLE" if as_float(ratio) >= DEPTH_VOLUME_ANOMALY_PERCENT else "NORMALE"


def enrich_spot_reporting(assets: List[Dict[str, Any]]) -> None:
    for asset in assets:
        asset["assetCategory"] = asset_category(asset)
        asset["regimeFamily"] = regime_family(asset)
        asset["atrIntensity"] = atr_intensity(asset)
        asset["finalInterpretation"] = final_interpretation(asset)
        volume = as_float(asset.get("quoteVolume"))
        depth = as_float(asset.get("depthTotalQuote"))
        asset["depthToVolumePercent"] = (depth / volume * 100.0) if volume > 0 else None
        asset["depthVolumeStatus"] = depth_volume_status(asset)


def spot_chop_adx_atr_table_html(assets: List[Dict[str, Any]]) -> str:
    """Croisement opérationnel CHOP × ADX × ATR pour le rapport Spot.

    CHOP = nature/structure, ADX = force directionnelle, ATR = intensité.
    Aucun de ces trois indicateurs ne constitue un filtre d'exclusion ici.
    """
    enrich_spot_reporting(assets)

    def chop_zone_of(value: float) -> str:
        if value <= CHOP_TREND_THRESHOLD:
            return "TENDANCE"
        if value >= CHOP_RANGE_THRESHOLD:
            return "RANGE"
        return "TRANSITION"

    def adx_zone_of(value: float) -> str:
        if value < ADX_TREND_THRESHOLD:
            return "FAIBLE"
        if value < ADX_STRONG_THRESHOLD:
            return "TENDANCE"
        return "FORTE"

    # On regroupe par zones BRUTES de CHOP et d'ADX (recalculées ici depuis les
    # valeurs réelles), pas depuis le nom de la famille finale : la famille
    # "TRANSITION NEUTRE" peut recouvrir deux zones CHOP différentes (CHOP ≤ 40
    # avec ADX faible, ou CHOP 40–55 avec ADX faible), et un libellage déduit du
    # seul nom de famille affichait alors une borne CHOP fausse pour une partie
    # du groupe. Grouper sur les zones réelles garantit que la borne affichée
    # correspond toujours aux valeurs effectivement recensées dans la ligne.
    groups = {}
    for asset in assets:
        chop_value = asset.get("chop")
        adx_value = asset.get("adx")
        if chop_value is None or adx_value is None:
            continue
        chop_value = as_float(chop_value)
        adx_value = as_float(adx_value)
        chop_zone = chop_zone_of(chop_value)
        adx_zone = adx_zone_of(adx_value)
        intensity = asset.get("atrIntensity", "NON DISPONIBLE")
        direction = asset.get("marketDirection", "NEUTRE")
        key = (chop_zone, adx_zone, intensity, direction)
        g = groups.setdefault(
            key,
            {
                "count": 0,
                "symbols": [],
                "chop": [],
                "adx": [],
                "atr": [],
                "family": asset.get("regimeFamily", "NON DISPONIBLE"),
            },
        )
        g["count"] += 1
        symbol = asset.get("symbol")
        if symbol and len(g["symbols"]) < 6:
            g["symbols"].append(symbol)
        g["chop"].append(chop_value)
        g["adx"].append(adx_value)
        atr_value = as_float(asset.get("regimeAtrPercent"))
        if atr_value is not None:
            g["atr"].append(atr_value)

    chop_zone_order = {"TENDANCE": 0, "TRANSITION": 1, "RANGE": 2}
    adx_zone_order = {"FORTE": 0, "TENDANCE": 1, "FAIBLE": 2}
    intensity_order = {"TRÈS VOLATILE": 0, "VOLATILE": 1, "ACTIVE": 2, "CALME": 3, "NON DISPONIBLE": 4}
    direction_order = {"HAUSSIÈRE": 0, "BAISSIÈRE": 1, "NEUTRE": 2}

    def mean(values):
        return sum(values) / len(values) if values else None

    ordered = sorted(
        groups.items(),
        key=lambda item: (
            chop_zone_order.get(item[0][0], 99),
            adx_zone_order.get(item[0][1], 99),
            intensity_order.get(item[0][2], 99),
            direction_order.get(item[0][3], 99),
            -item[1]["count"],
        ),
    )

    chop_zone_labels = {
        "TENDANCE": f"≤ {CHOP_TREND_THRESHOLD:.0f}",
        "TRANSITION": f"{CHOP_TREND_THRESHOLD:.0f}–{CHOP_RANGE_THRESHOLD:.0f}",
        "RANGE": f"≥ {CHOP_RANGE_THRESHOLD:.0f}",
    }
    adx_zone_labels = {
        "FAIBLE": f"< {ADX_TREND_THRESHOLD:.0f}",
        "TENDANCE": f"{ADX_TREND_THRESHOLD:.0f}–{ADX_STRONG_THRESHOLD:.0f}",
        "FORTE": f"≥ {ADX_STRONG_THRESHOLD:.0f}",
    }

    html = [
        "<h2>Croisement CHOP + ADX + ATR</h2>",
        "<p>Lecture à trois dimensions : <b>CHOP = nature du marché</b>, "
        "<b>ADX = force directionnelle</b>, <b>ATR = intensité du mouvement</b>. "
        "La direction HAUSSIÈRE/BAISSIÈRE est affichée en complément lorsque l'ADX est exploitable.</p>",
        "<table border='1' cellpadding='5' cellspacing='0' style='border-collapse:collapse;width:100%;font-size:12px'>",
        "<tr><th>CHOP</th><th>ADX</th><th>ATR</th><th>Lecture</th><th>Direction</th><th>Nb</th><th>CHOP moy.</th><th>ADX moy.</th><th>ATR moy.</th><th>Exemples</th></tr>",
    ]

    # Chaque ligne est désormais directement dérivée des zones CHOP/ADX réelles
    # du groupe ; la "Lecture" (famille) reste calculée par regime_family, donc
    # toujours cohérente avec la Synthèse et la table "Classification finale".
    for (chop_zone, adx_zone, intensity, direction), g in ordered:
        html.append(
            "<tr>"
            f"<td>{html_escape(chop_zone_labels[chop_zone])}</td>"
            f"<td>{html_escape(adx_zone_labels[adx_zone])}</td>"
            f"<td>{html_escape(intensity)}</td>"
            f"<td><b>{html_escape(g['family'])}</b></td>"
            f"<td>{html_escape(direction)}</td>"
            f"<td style='text-align:right'><b>{g['count']}</b></td>"
            f"<td>{format_number(mean(g['chop']), 2)}</td>"
            f"<td>{format_number(mean(g['adx']), 2)}</td>"
            f"<td>{format_number(mean(g['atr']), 3)}%</td>"
            f"<td>{html_escape(', '.join(g['symbols']))}</td>"
            "</tr>"
        )
    html.append("</table>")

    # Matrice compacte CHOP × ADX, avec le nombre d'actifs dans chaque case.
    matrix = {}
    for asset in assets:
        chop = as_float(asset.get("chop"))
        adx = as_float(asset.get("adx"))
        if chop is None or adx is None:
            continue
        cz = "TENDANCE" if chop <= 40 else ("TRANSITION" if chop < 55 else "RANGE")
        az = "FAIBLE" if adx < 25 else ("TENDANCE" if adx < 40 else "FORTE")
        matrix[(cz, az)] = matrix.get((cz, az), 0) + 1

    html.extend([
        "<h3>Matrice CHOP × ADX avec ATR comme troisième dimension</h3>",
        "<p>Cette matrice donne la structure de base. L'ATR est ensuite détaillé dans le tableau ci-dessus, "
        "ce qui évite de masquer l'intensité derrière une simple cellule CHOP × ADX.</p>",
        "<table border='1' cellpadding='6' cellspacing='0' style='border-collapse:collapse'>",
        "<tr><th>CHOP × ADX</th><th>ADX &lt; 25</th><th>ADX 25–40</th><th>ADX ≥ 40</th></tr>",
    ])
    for cz in ("TENDANCE", "TRANSITION", "RANGE"):
        html.append(
            f"<tr><td><b>{cz}</b></td>"
            f"<td>{matrix.get((cz, 'FAIBLE'), 0)}</td>"
            f"<td>{matrix.get((cz, 'TENDANCE'), 0)}</td>"
            f"<td>{matrix.get((cz, 'FORTE'), 0)}</td></tr>"
        )
    html.append("</table>")
    html.append(
        "<p style='font-size:11px'><b>Seuils :</b> CHOP ≤ 40 = tendance ; 40–55 = transition ; ≥ 55 = range. "
        "ADX &lt; 25 = faible ; 25–40 = directionnel ; ≥ 40 = fort. "
        "ATR &lt; 0,50 % = calme ; 0,50–1,50 % = active ; 1,50–2,50 % = volatile ; ≥ 2,50 % = très volatile.</p>"
    )
    return "".join(html)


def spot_base_asset_summary_html(assets: List[Dict[str, Any]]) -> str:
    """Vue consolidée par actif de base, sans supprimer les paires du screening."""
    if not assets:
        return ""
    groups: Dict[str, Dict[str, Any]] = {}
    for asset in assets:
        base = str(asset.get("baseAsset", "")).upper().strip()
        if not base:
            continue
        g = groups.setdefault(base, {"pairs": 0, "volume": 0.0, "directions": {}, "families": {}, "categories": {}, "symbols": []})
        g["pairs"] += 1
        g["volume"] += as_float(asset.get("quoteVolume"))
        category = asset.get("assetCategory", "SPOT / CRYPTO")
        g["categories"][category] = g["categories"].get(category, 0) + 1
        direction = asset.get("marketDirection", "NEUTRE")
        family = asset.get("regimeFamily", "NON DISPONIBLE")
        g["directions"][direction] = g["directions"].get(direction, 0) + 1
        g["families"][family] = g["families"].get(family, 0) + 1
        if len(g["symbols"]) < 6 and asset.get("symbol"):
            g["symbols"].append(asset["symbol"])
    ordered = sorted(groups.items(), key=lambda item: item[1]["volume"], reverse=True)
    limit = BASE_ASSET_SUMMARY_LIMIT if BASE_ASSET_SUMMARY_LIMIT > 0 else len(ordered)
    html = [
        "<h2>Vue consolidée par actif de base</h2>",
        "<p>Les paires restent toutes présentes dans le screening. Cette vue regroupe les quotes multiples d'un même actif (par exemple ETHUSDT et ETHUSDC) afin d'éviter de compter plusieurs fois un même sous-jacent dans la lecture du marché.</p>",
        "<table border='1' cellpadding='5' cellspacing='0' style='border-collapse:collapse'>",
        "<tr><th>Base</th><th>Catégorie</th><th>Paires</th><th>Volume cumulé</th><th>Direction dominante</th><th>Lecture dominante</th><th>Cohérence</th><th>Paires représentatives</th></tr>",
    ]
    for base, g in ordered[:limit]:
        dominant_direction, direction_n = (max(g["directions"].items(), key=lambda x: x[1]) if g["directions"] else ("NEUTRE", 0))
        dominant_family, family_n = (max(g["families"].items(), key=lambda x: x[1]) if g["families"] else ("NON DISPONIBLE", 0))
        dominant_category, category_n = (max(g["categories"].items(), key=lambda x: x[1]) if g["categories"] else ("SPOT / CRYPTO", 0))
        coherence = max(direction_n, family_n) / g["pairs"] * 100.0 if g["pairs"] else 0.0
        coherence_label = "FORTE" if coherence >= 80 else ("MOYENNE" if coherence >= 60 else "FAIBLE")
        html.append(
            "<tr>"
            f"<td><b>{html_escape(base)}</b></td>"
            f"<td>{html_escape(dominant_category)}</td><td>{g['pairs']}</td>"
            f"<td>${format_number(g['volume'], 0)}</td>"
            f"<td>{html_escape(dominant_direction)}</td>"
            f"<td>{html_escape(dominant_family)}</td>"
            f"<td>{html_escape(coherence_label)} ({coherence:.0f}%)</td>"
            f"<td>{html_escape(', '.join(g['symbols']))}</td>"
            "</tr>"
        )
    html.append("</table>")
    return "".join(html)


def spot_executive_summary(assets: List[Dict[str, Any]]) -> Dict[str, Any]:
    enrich_spot_reporting(assets)
    family_order = (
        "TENDANCE FORTE",
        "TENDANCE",
        "TRANSITION DIRECTIONNELLE",
        "TRANSITION NEUTRE",
        "CONFLIT",
        "RANGE",
        "NON DISPONIBLE",
    )
    counts = {family: 0 for family in family_order}
    direction_counts: Dict[str, int] = {}
    atr_counts: Dict[str, int] = {}
    category_counts: Dict[str, int] = {}
    for asset in assets:
        family = asset.get("regimeFamily", "NON DISPONIBLE")
        counts[family] = counts.get(family, 0) + 1
        direction = asset.get("marketDirection", "NON DISPONIBLE")
        direction_counts[direction] = direction_counts.get(direction, 0) + 1
        intensity = asset.get("atrIntensity", "NON DISPONIBLE")
        atr_counts[intensity] = atr_counts.get(intensity, 0) + 1
        category = asset.get("assetCategory", "CRYPTO / SPOT")
        category_counts[category] = category_counts.get(category, 0) + 1
    directional = sum(direction_counts.get(x, 0) for x in ("HAUSSIÈRE", "BAISSIÈRE"))
    return {
        "count": len(assets),
        "family_counts": counts,
        "direction_counts": dict(sorted(direction_counts.items(), key=lambda x: (-x[1], x[0]))),
        "atr_counts": dict(sorted(atr_counts.items(), key=lambda x: (-x[1], x[0]))),
        "category_counts": dict(sorted(category_counts.items(), key=lambda x: (-x[1], x[0]))),
        "directional_count": directional,
    }


def audit_to_html(audit: CriterionAudit) -> str:
    rows = []
    for row in audit.rows:
        rows.append(
            f"<tr><td>{html_escape(row['criterion'])}</td><td>{row['before']:,}</td>"
            f"<td>{row['selected']:,}</td><td>{row['rejected']:,}</td>"
            f"<td>{row['retention']:.2f}%</td><td>{row['rejection']:.2f}%</td></tr>"
        )
    html = (
        "<table border='1' cellpadding='5' cellspacing='0'>"
        "<tr><th>Critère</th><th>Avant</th><th>Retenus</th><th>Rejetés</th>"
        "<th>Rétention</th><th>Rejet</th></tr>" + "".join(rows) + "</table>"
    )

    distribution = audit.diagnostics.get("volume_distribution")
    if distribution:
        html += "<h3>Diagnostic de distribution du volume 24h</h3>"
        html += f"<p>Univers disponible pour ce diagnostic : <b>{audit.diagnostics.get('volume_universe_count', 0):,}</b> actifs</p>"
        html += (
            "<table border='1' cellpadding='5' cellspacing='0'>"
            "<tr><th>Seuil volume quote 24h</th><th>Actifs restant au-dessus du seuil</th></tr>"
        )
        for threshold, count in distribution.items():
            html += f"<tr><td>${threshold:,.0f}</td><td>{count:,}</td></tr>"
        html += "</table>"

        # Distribution par classes : plus utile que les seuls seuils cumulés pour
        # comprendre où se concentre la masse des actifs rejetés.
        volume_universe = audit.diagnostics.get("volume_universe_count", 0)
        if volume_universe:
            html += "<h4>Répartition par classes de volume</h4>"
            thresholds = (250_000, 500_000, 1_000_000, 2_000_000, 5_000_000, 10_000_000)
            cumulative = distribution
            classes = [
                ("< $250k", 0, 250_000),
                ("$250k – $500k", 250_000, 500_000),
                ("$500k – $1M", 500_000, 1_000_000),
                ("$1M – $2M", 1_000_000, 2_000_000),
                ("$2M – $5M", 2_000_000, 5_000_000),
                ("$5M – $10M", 5_000_000, 10_000_000),
                (">= $10M", 10_000_000, None),
            ]
            # The raw class distribution is computed in screen_spot and stored in diagnostics.
            volume_classes = audit.diagnostics.get("volume_classes", {})
            html += "<table border='1' cellpadding='5' cellspacing='0'><tr><th>Classe</th><th>Actifs</th></tr>"
            for label, _, _ in classes:
                html += f"<tr><td>{label}</td><td>{volume_classes.get(label, 0):,}</td></tr>"
            html += "</table>"

    regime = audit.diagnostics.get("regime")
    if regime is not None:
        html += "<h3>Régime de marché — CHOP + ADX + ATR (1h)</h3>"
        html += (
            f"<p>Univers analysé après le spread : <b>{regime.get('universe_count', 0):,}</b> actifs. "
            "Aucun filtre de rejet n'est appliqué à ces trois indicateurs.</p>"
        )
        html += "<table border='1' cellpadding='5' cellspacing='0'><tr><th>Classification finale</th><th>Actifs</th></tr>"
        family_counts = regime.get("family_counts", {})
        for family in ("TENDANCE FORTE", "TENDANCE", "TRANSITION DIRECTIONNELLE", "TRANSITION NEUTRE", "CONFLIT", "RANGE"):
            html += f"<tr><td>{family}</td><td>{family_counts.get(family, 0):,}</td></tr>"
        html += "</table>"

        html += "<table border='1' cellpadding='5' cellspacing='0'><tr><th>Indicateur</th><th>Min</th><th>P25</th><th>Médiane</th><th>Moyenne</th><th>P75</th><th>Max</th></tr>"
        for label, key in (("CHOP", "chop"), ("ADX", "adx"), ("ATR %", "atr")):
            stats = regime.get(key, {})
            cells = []
            for stat_key in ("minimum", "p25", "median", "mean", "p75", "maximum"):
                value = stats.get(stat_key)
                cells.append(f"{value:.4f}" if isinstance(value, (int, float)) else "-")
            html += f"<tr><td>{label}</td><td>" + "</td><td>".join(cells) + "</td></tr>"
        html += "</table>"

        html += "<h4>Croisement brut CHOP × ADX</h4>"
        html += (
            "<p><i>Ce tableau présente les zones brutes des indicateurs. Il peut donc différer de la classification finale, "
            "qui applique une hiérarchie d'interprétation.</i></p>"
        )
        html += "<table border='1' cellpadding='5' cellspacing='0'><tr><th>CHOP × ADX</th><th>FAIBLE</th><th>TENDANCE</th><th>FORTE</th></tr>"
        matrix = regime.get("structure_matrix", {})
        for chop_zone in ("TENDANCE", "TRANSITION", "RANGE"):
            row = matrix.get(chop_zone, {})
            html += f"<tr><td>{chop_zone}</td><td>{row.get('FAIBLE', 0)}</td><td>{row.get('TENDANCE', 0)}</td><td>{row.get('FORTE', 0)}</td></tr>"
        html += "</table>"
        html += (
            f"<p><b>Contradictions brutes CHOP/ADX :</b> {regime.get('raw_contradiction_count', 0):,}. "
            f"<b>Conflits finaux :</b> {regime.get('conflict_count', 0):,}. "
            "Les deux chiffres peuvent différer car la classification finale applique une hiérarchie d'interprétation. "
            f"<b>Valeurs valides :</b> {regime.get('valid_count', 0):,}/{regime.get('universe_count', 0):,}."
            "</p>"
        )
        html += "<p><b>Intensité ATR :</b> " + "; ".join(f"{label}: {count}" for label, count in regime.get("atr_intensity_counts", {}).items()) + "</p>"
        html += "<p><b>Direction ADX :</b> " + "; ".join(f"{label}: {count}" for label, count in regime.get("direction_counts", {}).items()) + "</p>"
    return html


def spot_top_assets_html(assets: List[Dict[str, Any]]) -> str:
    if not assets:
        return ""
    enrich_spot_reporting(assets)
    groups = [
        ("TENDANCE FORTE", "Tendance forte"),
        ("TENDANCE", "Tendance"),
        ("TRANSITION DIRECTIONNELLE", "Transition directionnelle"),
    ]
    html = ["<h2>Actifs à surveiller</h2>"]
    html.append(
        "<p>Classement descriptif fondé sur la structure CHOP/ADX, la direction DI+/DI−, "
        "l'intensité ATR et la liquidité. Aucun signal d'ordre n'est généré. "
        "Un ratio Depth/Volume exceptionnel est seulement signalé comme anomalie descriptive.</p>"
    )
    for family, title in groups:
        candidates = [a for a in assets if a.get("regimeFamily") == family]
        candidates.sort(
            key=lambda a: (
                as_float(a.get("adx")),
                as_float(a.get("depthToVolumePercent")),
                as_float(a.get("quoteVolume")),
            ),
            reverse=True,
        )
        if not candidates:
            continue
        html.append(f"<h3>{title} ({len(candidates)})</h3>")
        html.append(
            "<table border='1' cellpadding='5' cellspacing='0'>"
            "<tr><th>Rang</th><th>Catégorie</th><th>Symbol</th><th>Direction</th>"
            "<th>ATR%</th><th>ADX</th><th>CHOP</th><th>Volume 24h</th>"
            "<th>Depth ±0.25%</th><th>Depth/Volume</th><th>Ratio</th><th>Spread</th><th>Lecture</th></tr>"
        )
        for rank, asset in enumerate(candidates[:10], 1):
            html.append(
                "<tr>"
                f"<td>{rank}</td>"
                f"<td>{html_escape(asset.get('assetCategory', '-'))}</td>"
                f"<td><b>{html_escape(asset.get('symbol', '-'))}</b></td>"
                f"<td>{html_escape(asset.get('marketDirection', '-'))}</td>"
                f"<td>{format_number(asset.get('regimeAtrPercent'), 3)}%</td>"
                f"<td>{format_number(asset.get('adx'), 2)}</td>"
                f"<td>{format_number(asset.get('chop'), 2)}</td>"
                f"<td>${format_number(asset.get('quoteVolume'), 0)}</td>"
                f"<td>${format_number(asset.get('depthTotalQuote'), 0)}</td>"
                f"<td>{format_number(asset.get('depthToVolumePercent'), 3)}%</td>"
                f"<td>{format_number(asset.get('spreadPercent'), 4)}%</td>"
                f"<td>{html_escape(asset.get('finalInterpretation', '-'))}</td>"
                "</tr>"
            )
        html.append("</table>")
    return "".join(html)


def spot_conflicts_html(assets: List[Dict[str, Any]]) -> str:
    enrich_spot_reporting(assets)
    conflicts = [a for a in assets if a.get("regimeFamily") == "CONFLIT"]
    if not conflicts:
        return ""
    conflicts.sort(key=lambda a: (as_float(a.get("adx")), as_float(a.get("chop"))), reverse=True)
    html = [f"<h2>Situations conflictuelles ({len(conflicts)})</h2>"]
    html.append(
        "<p>CHOP et ADX ne décrivent pas une structure cohérente. Ces actifs sont conservés pour observation, "
        "mais ne doivent pas être assimilés à une tendance classique.</p>"
    )
    html.append(
        "<table border='1' cellpadding='5' cellspacing='0'>"
        "<tr><th>Symbol</th><th>Direction</th><th>CHOP</th><th>ADX</th><th>ATR%</th>"
        "<th>Volume 24h</th><th>Depth/Volume</th><th>Ratio</th><th>Spread</th><th>Lecture</th></tr>"
    )
    for asset in conflicts:
        html.append(
            "<tr>"
            f"<td><b>{html_escape(asset.get('symbol', '-'))}</b></td>"
            f"<td>{html_escape(asset.get('marketDirection', '-'))}</td>"
            f"<td>{format_number(asset.get('chop'), 2)}</td>"
            f"<td>{format_number(asset.get('adx'), 2)}</td>"
            f"<td>{format_number(asset.get('regimeAtrPercent'), 3)}%</td>"
            f"<td>${format_number(asset.get('quoteVolume'), 0)}</td>"
            f"<td>{format_number(asset.get('depthToVolumePercent'), 3)}%</td>"
            f"<td>{html_escape(asset.get('depthVolumeStatus', '-'))}</td>"
            f"<td>{format_number(asset.get('spreadPercent'), 4)}%</td>"
            f"<td>{html_escape(asset.get('finalInterpretation', '-'))}</td>"
            "</tr>"
        )
    html.append("</table>")
    return "".join(html)


def market_summary_html(market: str, assets: List[Dict[str, Any]], audit: Optional[CriterionAudit]) -> str:
    if market == "MARGIN":
        return (
            "<h2>MARGIN</h2>"
            f"<p><b>Univers sous-jacent :</b> {len(assets):,} actifs Spot éligibles.</p>"
            "<p>Le screener ne dispose pas ici d'un jeu de données Margin indépendant permettant de recalculer "
            "volume, carnet, spread et régime. L'analyse présentée correspond donc au marché Spot sous-jacent. "
            "L'éligibilité réelle au Margin dépend du compte Binance.</p>"
        )

    html = [f"<h2>{html_escape(market)}</h2>", f"<p><b>Survivants :</b> {len(assets):,}</p>"]
    if audit:
        html.append(audit_to_html(audit))
    if assets:
        if market == "SPOT":
            enrich_spot_reporting(assets)
        html.append(
            "<table border='1' cellpadding='5' cellspacing='0'>"
            "<tr><th>Catégorie</th><th>Symbol</th><th>Volume 24h</th>"
            f"<th>Depth ±{ORDER_BOOK_DEPTH_PCT:.2f}%</th><th>Depth/Volume</th><th>Ratio</th><th>Spread</th>"
            "<th>24h</th><th>CHOP</th><th>ADX</th><th>ATR%</th><th>Nature</th>"
            "<th>Structure</th><th>Direction</th><th>Interprétation</th></tr>"
        )

        def sort_key(asset: Dict[str, Any]):
            family = regime_family(asset)
            direction_bonus = 1 if asset.get("marketDirection") in {"HAUSSIÈRE", "BAISSIÈRE"} else 0
            return (
                regime_priority(asset),
                direction_bonus,
                as_float(asset.get("adx")),
                as_float(asset.get("depthToVolumePercent")),
                as_float(asset.get("quoteVolume")),
            )

        sorted_assets = sorted(assets, key=sort_key, reverse=True)
        for asset in sorted_assets[:EMAIL_TOP_RESULTS]:
            html.append(
                "<tr>"
                f"<td>{html_escape(asset.get('assetCategory', market))}</td>"
                f"<td><b>{html_escape(asset.get('symbol', '-'))}</b></td>"
                f"<td>${format_number(asset.get('quoteVolume', 0), 0)}</td>"
                f"<td>${format_number(asset.get('depthTotalQuote', 0), 0)}</td>"
                f"<td>{format_number(asset.get('depthToVolumePercent'), 3)}%</td>"
                f"<td>{html_escape(asset.get('depthVolumeStatus', '-'))}</td>"
                f"<td>{format_number(asset.get('spreadPercent', 0), 4)}%</td>"
                f"<td>{format_number(asset.get('priceChangePercent', 0))}%</td>"
                f"<td>{format_number(asset.get('chop', '-'), 2)}</td>"
                f"<td>{format_number(asset.get('adx', '-'), 2)}</td>"
                f"<td>{format_number(asset.get('regimeAtrPercent', '-'), 3)}%</td>"
                f"<td>{html_escape(asset.get('marketNature', '-'))}</td>"
                f"<td>{html_escape(asset.get('marketStructure', '-'))}</td>"
                f"<td>{html_escape(asset.get('marketDirection', '-'))}</td>"
                f"<td>{html_escape(asset.get('finalInterpretation', asset.get('marketRegime', '-')))}</td>"
                "</tr>"
            )
        html.append("</table>")
        if len(sorted_assets) > EMAIL_TOP_RESULTS:
            html.append(f"<p><i>{len(sorted_assets) - EMAIL_TOP_RESULTS:,} actifs supplémentaires ne sont pas affichés dans le tableau détaillé.</i></p>")
    return "".join(html)


def build_report(market_results: Dict[str, List[Dict[str, Any]]], market_audits: Dict[str, CriterionAudit], errors: List[str], warnings: List[str], unavailable_markets: List[str]) -> str:
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    spot_assets = market_results.get("SPOT", [])
    summary = spot_executive_summary(spot_assets) if spot_assets else None

    unique_market_assets = set()
    for market, assets in market_results.items():
        if market == "MARGIN":
            continue
        for asset in assets:
            symbol = asset.get("symbol")
            if symbol:
                unique_market_assets.add((market, symbol))
    unique_assets_count = len(spot_assets) if spot_assets else len(unique_market_assets)

    parts = [
        "<html><body>",
        "<h1>Binance Multi-Market Screener</h1>",
        f"<p><b>Date :</b> {now}</p>",
        f"<p><b>Actifs uniques :</b> {unique_assets_count:,}</p>",
        "<hr>",
    ]

    if summary:
        parts.append("<h2>Synthèse</h2>")
        parts.append(f"<p><b>Univers Spot après liquidité :</b> {summary['count']:,} actifs.</p>")
        parts.append("<table border='1' cellpadding='5' cellspacing='0'><tr><th>Classification</th><th>Actifs</th><th>%</th></tr>")
        for family in ("TENDANCE FORTE", "TENDANCE", "TRANSITION DIRECTIONNELLE", "TRANSITION NEUTRE", "CONFLIT", "RANGE"):
            count = summary["family_counts"].get(family, 0)
            pct = (count / summary["count"] * 100.0) if summary["count"] else 0.0
            parts.append(f"<tr><td>{family}</td><td>{count:,}</td><td>{pct:.1f}%</td></tr>")
        parts.append("</table>")

        parts.append("<p><b>Direction :</b> " + "; ".join(f"{k}: {v}" for k, v in summary["direction_counts"].items()) + "</p>")
        parts.append("<p><b>Intensité ATR :</b> " + "; ".join(f"{k}: {v}" for k, v in summary["atr_counts"].items()) + "</p>")
        parts.append("<p><b>Catégories :</b> " + "; ".join(f"{k}: {v}" for k, v in summary["category_counts"].items()) + "</p>")
        parts.append(
            "<p><i>Classification Spot : une paire n'est jamais classée <b>SPOT / TOKENIZED / SPECIAL</b> sur la "
            "seule base de son ticker. Elle l'est uniquement si une métadonnée Binance explicite le confirme, si "
            "l'API officielle des actifs tokenisés le confirme dynamiquement (quand BINANCE_API_KEY est configuré), "
            "ou si son baseAsset figure dans la liste de secours BINANCE_TOKENIZED_SPOT_BASES.</i></p>"
        )
        parts.append(
            f"<p><b>Lecture principale :</b> la majorité des actifs se trouvent hors tendance mature. "
            f"{summary['family_counts'].get('TENDANCE FORTE', 0) + summary['family_counts'].get('TENDANCE', 0):,} présentent une tendance établie, "
            f"{summary['family_counts'].get('TRANSITION DIRECTIONNELLE', 0):,} une transition directionnelle et "
            f"{summary['family_counts'].get('TRANSITION NEUTRE', 0):,} une transition sans direction confirmée. "
            "Lorsque la direction est identifiable, le biais observé doit être lu comme une photographie du marché analysé, "
            "et non comme un signal de marché global."
            "</p>"
        )
        parts.append(spot_chop_adx_atr_table_html(spot_assets))
        parts.append(spot_base_asset_summary_html(spot_assets))
        parts.append(spot_top_assets_html(spot_assets))
        parts.append(spot_conflicts_html(spot_assets))

    # Audit complet du pipeline après le résumé décisionnel.
    for market in ["SPOT", "USDⓈ-M FUTURES", "COIN-M FUTURES", "OPTIONS", "TOKENIZED STOCKS", "MARGIN"]:
        if market in market_results:
            parts.append(market_summary_html(market, market_results[market], market_audits.get(market)))

    parts.append("<hr><h2>Marchés non intégrés</h2><ul><li><b>P2P :</b> non intégré. Aucune API publique officielle adaptée au même type de screening n'est utilisée.</li></ul>")

    if unavailable_markets:
        parts.append("<h2>Marchés indisponibles</h2><ul>" + "".join(f"<li>{html_escape(m)}</li>" for m in unavailable_markets) + "</ul>")

    parts.append(
        f"<h2>Paramètres principaux</h2><ul>"
        f"<li>Spot quotes : {', '.join(sorted(QUOTE_ASSETS)) if QUOTE_ASSETS else 'dynamiques — stablecoins actifs détectés depuis Binance exchangeInfo'}</li>"
        f"<li>Spot volume minimum actif : ${MIN_24H_QUOTE_VOLUME:,.0f}</li>"
        f"<li>Order Book Depth Spot : {'activé' if ORDER_BOOK_DEPTH_ENABLED else 'désactivé'} — profondeur minimale ${MIN_ORDER_BOOK_DEPTH_QUOTE:,.0f} dans ±{ORDER_BOOK_DEPTH_PCT:.2f}% (limit {ORDER_BOOK_DEPTH_LIMIT}, workers {ORDER_BOOK_DEPTH_WORKERS})</li>"
        f"<li>Spread Spot maximum : {MAX_SPREAD_PERCENT:.2f}%</li>"
        f"<li>Régime Spot : {'activé' if REGIME_ENABLED else 'désactivé'} — CHOP({CHOP_PERIOD}) + ADX({ADX_PERIOD}) + ATR({ATR_REGIME_PERIOD}) sur {REGIME_INTERVAL}, sans filtre d'exclusion</li>"
        f"<li>Zones d'interprétation : CHOP tendance ≤ {CHOP_TREND_THRESHOLD:.1f}, CHOP intermédiaire entre {CHOP_TREND_THRESHOLD:.1f} et {CHOP_RANGE_THRESHOLD:.1f}, CHOP range ≥ {CHOP_RANGE_THRESHOLD:.1f}; ADX tendance ≥ {ADX_TREND_THRESHOLD:.1f}, ADX forte ≥ {ADX_STRONG_THRESHOLD:.1f}; intensité ATR : calme &lt; {ATR_LOW_PERCENT:.2f}%, active &lt; {ATR_HIGH_PERCENT:.2f}%, volatile &lt; {ATR_EXTREME_PERCENT:.2f}%, très volatile au-dessus</li>"
        f"<li>Futures volume minimum : ${MIN_FUTURES_QUOTE_VOLUME:,.0f}</li>"
        f"</ul>"
    )
    if warnings:
        parts.append("<h2>Avertissements</h2><ul>" + "".join(f"<li>{html_escape(w)}</li>" for w in warnings) + "</ul>")
    if errors:
        parts.append("<h2>Erreurs techniques réelles</h2><ul>" + "".join(f"<li>{html_escape(e)}</li>" for e in errors) + "</ul>")
    else:
        parts.append("<h2>État technique</h2><p><b>Erreurs techniques réelles : 0</b></p>")
    parts.append("<hr><p><b>Important :</b> ce programme effectue uniquement de la collecte et de l'analyse de données de marché. Aucun ordre Binance n'est exécuté.</p></body></html>")
    return "".join(parts)


def send_email(subject: str, html: str) -> None:
    if not (EMAIL_USER and EMAIL_PASS and EMAIL_TO):
        raise RuntimeError("EMAIL_USER / EMAIL_PASS / EMAIL_TO non configurés")
    message = MIMEMultipart("alternative")
    message["Subject"] = subject
    message["From"] = EMAIL_USER
    message["To"] = EMAIL_TO
    message.attach(MIMEText(html, "html", "utf-8"))
    context = ssl.create_default_context()
    with smtplib.SMTP_SSL(EMAIL_HOST, EMAIL_PORT, context=context) as server:
        server.login(EMAIL_USER, EMAIL_PASS)
        server.sendmail(EMAIL_USER, [EMAIL_TO], message.as_string())


# ----------------------------- MARKET RUNNERS -----------------------------
def run_spot(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    exchange = spot_exchange_info()
    assets = build_spot_universe(exchange)
    effective_quotes = resolve_spot_quote_assets(exchange)
    merge_spot_tickers(assets, spot_tickers())
    try:
        merge_spot_books(assets, spot_book_tickers())
    except Exception as exc:
        warnings.append(f"Spot bookTicker indisponible : {exc}")
        for asset in assets:
            asset["spreadPercent"] = None
    warnings.append(
        "Quote assets Spot dynamiques : " + ", ".join(sorted(effective_quotes))
        if effective_quotes
        else "Aucun stablecoin quote actif détecté dans Binance exchangeInfo."
    )
    return screen_spot(assets, effective_quotes, warnings)


def run_usdm(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_usdm_universe(futures_exchange_info(USDM_BASE_URL, "/fapi/v1/exchangeInfo"))
    merge_futures_tickers(assets, futures_tickers(USDM_BASE_URL, "/fapi/v1/ticker/24hr"))
    merge_futures_books(assets, futures_book_tickers(USDM_BASE_URL, "/fapi/v1/ticker/bookTicker"))
    merge_funding(assets, futures_premium_index(USDM_BASE_URL, "/fapi/v1/premiumIndex"))
    return screen_futures(assets)


def run_coinm(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_coinm_universe(futures_exchange_info(COINM_BASE_URL, "/dapi/v1/exchangeInfo"))
    merge_futures_tickers(assets, futures_tickers(COINM_BASE_URL, "/dapi/v1/ticker/24hr"))
    merge_futures_books(assets, futures_book_tickers(COINM_BASE_URL, "/dapi/v1/ticker/bookTicker"))
    merge_funding(assets, futures_premium_index(COINM_BASE_URL, "/dapi/v1/premiumIndex"))
    return screen_futures(assets)


def run_options(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_options_universe(options_exchange_info())
    merge_option_tickers(assets, options_tickers())
    return screen_options(assets)


def run_tokenized(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_tokenized_universe(tokenized_exchange_info(), tokenized_assets_info())
    if TOKENIZED_MAX_ASSETS > 0:
        assets = assets[:TOKENIZED_MAX_ASSETS]
    merge_tokenized_quotes(assets)
    return screen_tokenized(assets)


# ----------------------------- MAIN -----------------------------
def main() -> int:
    started = time.time()
    warnings: List[str] = []
    errors: List[str] = []
    unavailable_markets: List[str] = []
    market_results: Dict[str, List[Dict[str, Any]]] = {}
    market_audits: Dict[str, CriterionAudit] = {}
    print("=" * 70)
    print("BINANCE MULTI-MARKET SCREENER V3 — CHOP / ADX / ATR")
    print("=" * 70)

    if ENABLE_SPOT:
        added_dynamic_bases = refresh_dynamic_tokenized_spot_bases(warnings)
        if added_dynamic_bases:
            warnings.append(
                f"Classification TOKENIZED/SPECIAL : {added_dynamic_bases} base(s) ajoutée(s) dynamiquement "
                "depuis l'API Binance (tokenized-assets), en plus de la liste de secours."
            )
        elif not BINANCE_API_KEY:
            warnings.append(
                "Classification TOKENIZED/SPECIAL : BINANCE_API_KEY absent, classification basée uniquement "
                "sur la liste de secours BINANCE_TOKENIZED_SPOT_BASES."
            )
        print("\n[SPOT]")
        try:
            assets, audit = run_spot(warnings)
            market_results["SPOT"], market_audits["SPOT"] = assets, audit
            print(f"Spot survivors: {len(assets):,}")
            regime_diag = audit.diagnostics.get("regime", {})
            if regime_diag:
                print(
                    "Régime CHOP/ADX/ATR : "
                    f"{regime_diag.get('nature_counts', {})} | "
                    f"ATR {regime_diag.get('atr_intensity_counts', {})} | "
                    f"contradictions_brutes={regime_diag.get('raw_contradiction_count', 0)} | conflits_finaux={regime_diag.get('conflict_count', 0)}"
                )
                print(f"Croisement CHOP×ADX : {regime_diag.get('structure_matrix', {})}")
        except Exception as exc:
            message, kind = format_market_exception("SPOT", exc)
            if kind == "unavailable":
                unavailable_markets.append(message)
            else:
                errors.append(message)

    if ENABLE_MARGIN:
        print("\n[MARGIN]")
        if "SPOT" in market_results:
            market_results["MARGIN"] = build_margin_market(market_results["SPOT"])
            print(f"Margin underlying Spot universe: {len(market_results['MARGIN']):,}")
            warnings.append("Margin : l'éligibilité réelle est dépendante du compte et n'est pas déclarée comme garantie par ce screener.")
        else:
            warnings.append("Margin ignoré car le scan Spot n'a pas abouti.")

    if ENABLE_USDM:
        print("\n[USDⓈ-M FUTURES]")
        try:
            assets, audit = run_usdm(warnings)
            market_results["USDⓈ-M FUTURES"], market_audits["USDⓈ-M FUTURES"] = assets, audit
            print(f"USDⓈ-M survivors: {len(assets):,}")
        except Exception as exc:
            message, kind = format_market_exception("USDⓈ-M FUTURES", exc)
            if kind == "unavailable":
                unavailable_markets.append(message)
            else:
                errors.append(message)

    if ENABLE_COINM:
        print("\n[COIN-M FUTURES]")
        try:
            assets, audit = run_coinm(warnings)
            market_results["COIN-M FUTURES"], market_audits["COIN-M FUTURES"] = assets, audit
            print(f"COIN-M survivors: {len(assets):,}")
        except Exception as exc:
            message, kind = format_market_exception("COIN-M FUTURES", exc)
            if kind == "unavailable":
                unavailable_markets.append(message)
            else:
                errors.append(message)

    if ENABLE_OPTIONS:
        print("\n[OPTIONS]")
        try:
            assets, audit = run_options(warnings)
            market_results["OPTIONS"], market_audits["OPTIONS"] = assets, audit
            print(f"Options survivors: {len(assets):,}")
        except Exception as exc:
            message, kind = format_market_exception("OPTIONS", exc)
            if kind == "unavailable":
                unavailable_markets.append(message)
            else:
                errors.append(message)

    if ENABLE_TOKENIZED_STOCKS:
        print("\n[TOKENIZED STOCKS]")
        if not BINANCE_API_KEY:
            warnings.append("Tokenized Stocks non exécuté : BINANCE_API_KEY absent.")
        else:
            try:
                assets, audit = run_tokenized(warnings)
                market_results["TOKENIZED STOCKS"], market_audits["TOKENIZED STOCKS"] = assets, audit
                print(f"Tokenized Stocks survivors: {len(assets):,}")
            except Exception as exc:
                errors.append(f"TOKENIZED STOCKS: {exc}")

    print("\n[REGIME INTERPRETATION]")
    if "SPOT" in market_results:
        regime_diag = market_audits.get("SPOT", CriterionAudit()).diagnostics.get("regime", {})
        print(f"Nature : {regime_diag.get('nature_counts', {})}")
        print(f"Direction : {regime_diag.get('direction_counts', {})}")
        print(f"Intensité ATR : {regime_diag.get('atr_intensity_counts', {})}")
        print(f"Croisement CHOP×ADX : {regime_diag.get('structure_matrix', {})}")
        print(f"Contradictions brutes : {regime_diag.get('raw_contradiction_count', 0)} | Conflits finaux : {regime_diag.get('conflict_count', 0)}")

    html = build_report(market_results, market_audits, errors, warnings, unavailable_markets)
    elapsed = time.time() - started
    subject = f"Binance Multi-Market Screener — {datetime.now(timezone.utc):%Y-%m-%d %H:%M} UTC"
    try:
        send_email(subject, html)
        print(f"\nEmail envoyé. Durée : {elapsed:.2f}s")
    except Exception as exc:
        print("\nERREUR EMAIL:", exc)
        print(html)
        return 1
    print(f"\nDurée totale : {elapsed:.2f}s")
    if errors:
        print(f"Erreurs techniques réelles : {len(errors)}")
    if unavailable_markets:
        print(f"Marchés indisponibles : {len(unavailable_markets)}")
    if warnings:
        print(f"Avertissements : {len(warnings)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())