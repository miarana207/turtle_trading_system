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
# BINANCE MULTI-MARKET SCREENER V3 — FILTERING PIPELINE
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
# explicite le confirme ou si le baseAsset est déclaré ici.
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
    text = str(exc).lower()
    return "http 451" in text or ("451" in text and "unavailable" in text)


def format_market_exception(market: str, exc: Exception) -> Tuple[str, str]:
    """Classe les erreurs HTTP, réseau et données avec un libellé explicite."""
    text = str(exc); lower = text.lower()
    if "http 451" in lower:
        return (f"{market} indisponible : HTTP 451 — restriction géographique / conditions d'éligibilité depuis le runner GitHub.", "unavailable")
    for code, label in ((401, "AUTHENTIFICATION"), (403, "PERMISSION / ACCÈS"), (429, "RATE LIMIT")):
        if f"http {code}" in lower:
            return (f"{market} : HTTP {code} — {label}.", "error")
    if any(f"http {code}" in lower for code in (500, 501, 502, 503, 504)):
        return (f"{market} : ERREUR SERVEUR BINANCE — {text}", "error")
    if "timed out" in lower or "timeout" in lower or "urlopen error" in lower or "network" in lower:
        return (f"{market} : ERREUR RÉSEAU / TIMEOUT — {text}", "error")
    if "json" in lower or ("réponse" in lower and "invalide" in lower):
        return (f"{market} : ERREUR DONNÉES API / JSON — {text}", "error")
    return (f"{market} : ERREUR API — {text}", "error")


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
# HISTORIQUE MINIMUM
# ============================================================
SPOT_KLINES_CACHE: Dict[Tuple[str, str, int], List[List[Any]]] = {}

def spot_klines(symbol: str, interval: str = "1h", limit: Optional[int] = None) -> List[List[Any]]:
    effective_limit = limit or max(1, int(math.ceil(MIN_HISTORY_DAYS * 24)))
    cache_key = (symbol, interval, effective_limit)
    if cache_key in SPOT_KLINES_CACHE:
        return SPOT_KLINES_CACHE[cache_key]
    data = http_get_json(SPOT_BASE_URL, "/api/v3/klines", {"symbol": symbol, "interval": interval, "limit": effective_limit})
    if not isinstance(data, list):
        raise BinanceHTTPError(f"Réponse klines invalide pour {symbol}")
    SPOT_KLINES_CACHE[cache_key] = data
    return data


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
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as executor:
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


# ----------------------------- REPORTING -----------------------------
def format_number(value: Any, decimals: int = 2) -> str:
    try: return f"{float(value):,.{decimals}f}"
    except (TypeError,ValueError): return "-"

def html_escape(value: Any) -> str:
    text="" if value is None else str(value)
    return text.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;").replace('"',"&quot;")

def asset_category(asset: Dict[str,Any])->str:
    if asset.get("market")!="SPOT": return asset.get("market","OTHER")
    base=str(asset.get("baseAsset","")).upper()
    explicit=(asset.get("isTokenized") is True or asset.get("tokenized") is True or asset.get("isTokenizedAsset") is True or str(asset.get("assetType","")).upper() in {"TOKENIZED","TOKENIZED_STOCK","STOCK_TOKEN"} or str(asset.get("productType","")).upper() in {"TOKENIZED","TOKENIZED_STOCK","STOCK_TOKEN"})
    if explicit or base in TOKENIZED_SPOT_BASES: return "TOKENIZED"
    if base in {"EUR","GBP","AUD","BRL","TRY","RUB","PLN","UAH","RON","ARS","ZAR","JPY"}: return "FIAT"
    if base in {"PAXG","XAUT","XAG"}: return "COMMODITY"
    return "CRYPTO" if base else "OTHER"

def depth_volume_status(asset: Dict[str,Any])->str:
    ratio=asset.get("depthToVolumePercent")
    if ratio is None: return "NON DISPONIBLE"
    return "EXCEPTIONNELLE" if as_float(ratio)>=DEPTH_VOLUME_ANOMALY_PERCENT else "NORMALE"

def enrich_spot_reporting(assets: List[Dict[str,Any]])->None:
    for a in assets:
        a["assetCategory"]=asset_category(a); v=as_float(a.get("quoteVolume")); d=as_float(a.get("depthTotalQuote")); a["depthToVolumePercent"]=(d/v*100.0) if v>0 else None; a["depthVolumeStatus"]=depth_volume_status(a)

def percentile_rank(values: List[float], value: float)->float:
    if not values: return 0.0
    if len(values)==1: return 100.0
    return (sum(1 for x in values if x<=value)-1)/(len(values)-1)*100.0

def inverse_percentile_rank(values: List[float], value: float)->float:
    if not values: return 0.0
    if len(values)==1: return 100.0
    return (sum(1 for x in values if x>=value)-1)/(len(values)-1)*100.0

def rank_spot_survivors(assets: List[Dict[str,Any]])->List[Dict[str,Any]]:
    if not assets: return []
    enrich_spot_reporting(assets); volumes=[as_float(a.get("quoteVolume")) for a in assets]; depths=[as_float(a.get("depthTotalQuote")) for a in assets]; ratios=[as_float(a.get("depthToVolumePercent")) for a in assets]; spreads=[as_float(a.get("spreadPercent"),999.0) for a in assets]
    for a in assets:
        a["marketQualityScore"]=(.35*percentile_rank(depths,as_float(a.get("depthTotalQuote")))+.30*percentile_rank(volumes,as_float(a.get("quoteVolume")))+.20*percentile_rank(ratios,as_float(a.get("depthToVolumePercent")))+.15*inverse_percentile_rank(spreads,as_float(a.get("spreadPercent"),999.0)))
    return sorted(assets,key=lambda a:(a.get("marketQualityScore",0.0),as_float(a.get("depthTotalQuote")),as_float(a.get("quoteVolume"))),reverse=True)

def spot_base_asset_summary_html(assets: List[Dict[str,Any]])->str:
    if not assets:return ""
    groups={}
    for a in assets:
        base=str(a.get("baseAsset","")).upper().strip()
        if not base:continue
        g=groups.setdefault(base,{"pairs":0,"volume":0.0,"categories":{},"symbols":[]}); g["pairs"]+=1; g["volume"]+=as_float(a.get("quoteVolume")); c=a.get("assetCategory","OTHER"); g["categories"][c]=g["categories"].get(c,0)+1
        if len(g["symbols"])<6 and a.get("symbol"):g["symbols"].append(a["symbol"])
    ordered=sorted(groups.items(),key=lambda x:x[1]["volume"],reverse=True); limit=BASE_ASSET_SUMMARY_LIMIT if BASE_ASSET_SUMMARY_LIMIT>0 else len(ordered)
    html=["<h2>Vue consolidée par actif de base</h2>","<p>Les paires restent toutes présentes dans le screening. Cette vue regroupe les quotes multiples d'un même actif.</p>","<table border='1' cellpadding='5' cellspacing='0'><tr><th>Base</th><th>Catégorie</th><th>Paires</th><th>Volume cumulé</th><th>Paires représentatives</th></tr>"]
    for base,g in ordered[:limit]:
        c=max(g["categories"].items(),key=lambda x:x[1])[0] if g["categories"] else "OTHER"; html.append(f"<tr><td><b>{html_escape(base)}</b></td><td>{html_escape(c)}</td><td>{g['pairs']}</td><td>${format_number(g['volume'],0)}</td><td>{html_escape(', '.join(g['symbols']))}</td></tr>")
    html.append("</table>"); return "".join(html)

def spot_category_summary(assets: List[Dict[str,Any]])->Dict[str,int]:
    enrich_spot_reporting(assets); counts={}
    for a in assets:
        c=a.get("assetCategory","OTHER"); counts[c]=counts.get(c,0)+1
    return dict(sorted(counts.items(),key=lambda x:(-x[1],x[0])))

def audit_to_html(audit: CriterionAudit)->str:
    html="<table border='1' cellpadding='5' cellspacing='0'><tr><th>Critère</th><th>Avant</th><th>Retenus</th><th>Rejetés</th><th>Rétention</th><th>Rejet</th></tr>"+"".join(f"<tr><td>{html_escape(r['criterion'])}</td><td>{r['before']:,}</td><td>{r['selected']:,}</td><td>{r['rejected']:,}</td><td>{r['retention']:.2f}%</td><td>{r['rejection']:.2f}%</td></tr>" for r in audit.rows)+"</table>"
    d=audit.diagnostics.get("volume_distribution")
    if d:
        html+=f"<h3>Diagnostic de distribution du volume 24h</h3><p>Univers disponible : <b>{audit.diagnostics.get('volume_universe_count',0):,}</b> actifs</p><table border='1' cellpadding='5' cellspacing='0'><tr><th>Seuil</th><th>Actifs</th></tr>"+"".join(f"<tr><td>${t:,.0f}</td><td>{c:,}</td></tr>" for t,c in d.items())+"</table>"
        vc=audit.diagnostics.get("volume_classes",{}); html+="<h4>Répartition par classes de volume</h4><table border='1' cellpadding='5' cellspacing='0'><tr><th>Classe</th><th>Actifs</th></tr>"+"".join(f"<tr><td>{l}</td><td>{vc.get(l,0):,}</td></tr>" for l in vc)+"</table>"
    d=audit.diagnostics.get("depth_volume")
    if d:
        html+=f"<h3>Diagnostic Depth / Volume</h3><p>Mesure effectuée avant toute décision supplémentaire. Univers mesuré : <b>{d.get('count',0):,}</b> actifs.</p><table border='1' cellpadding='5' cellspacing='0'><tr><th>Min</th><th>P25</th><th>Médiane</th><th>Moyenne</th><th>P75</th><th>Max</th></tr><tr>"+"".join(f"<td>{format_number(d.get(k),4)}%</td>" for k in ("minimum","p25","median","mean","p75","maximum"))+"</tr></table><h4>Répartition Depth / Volume</h4><table border='1' cellpadding='5' cellspacing='0'><tr><th>Classe</th><th>Actifs</th></tr>"+"".join(f"<tr><td>{l}</td><td>{c:,}</td></tr>" for l,c in d.get("classes",{}).items())+"</table>"
    return html


def market_summary_html(market: str, assets: List[Dict[str,Any]], audit: Optional[CriterionAudit])->str:
    if market=="MARGIN": return f"<h2>MARGIN</h2><p><b>Univers sous-jacent :</b> {len(assets):,} actifs Spot éligibles.</p><p>Le screener ne dispose pas ici d'un jeu de données Margin indépendant permettant de recalculer volume, carnet et spread. L'analyse présentée correspond donc au marché Spot sous-jacent. L'éligibilité réelle au Margin dépend du compte Binance.</p>"
    html=[f"<h2>{html_escape(market)}</h2>",f"<p><b>Survivants :</b> {len(assets):,}</p>"]
    if audit: html.append(audit_to_html(audit))
    if assets:
        ordered=rank_spot_survivors(assets) if market=="SPOT" else sorted(assets,key=lambda a:as_float(a.get("quoteVolume")),reverse=True)
        html.append("<table border='1' cellpadding='5' cellspacing='0'><tr><th>Rang</th><th>Catégorie</th><th>Symbol</th><th>Score qualité</th><th>Volume 24h</th><th>Depth ±"+f"{ORDER_BOOK_DEPTH_PCT:.2f}%</th><th>Depth/Volume</th><th>Ratio</th><th>Spread</th></tr>")
        for rank,a in enumerate(ordered,1): html.append(f"<tr><td>{rank}</td><td>{html_escape(a.get('assetCategory',market))}</td><td><b>{html_escape(a.get('symbol','-'))}</b></td><td>{format_number(a.get('marketQualityScore'),2)}</td><td>${format_number(a.get('quoteVolume',0),0)}</td><td>${format_number(a.get('depthTotalQuote',0),0)}</td><td>{format_number(a.get('depthToVolumePercent'),3)}%</td><td>{html_escape(a.get('depthVolumeStatus','-'))}</td><td>{format_number(a.get('spreadPercent',0),4)}%</td></tr>")
        html.append("</table>")
    return "".join(html)

def build_report(market_results: Dict[str,List[Dict[str,Any]]], market_audits: Dict[str,CriterionAudit], errors: List[str], warnings: List[str], unavailable_markets: List[str])->str:
    now=datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC"); spot=market_results.get("SPOT",[]); cats=spot_category_summary(spot) if spot else {}
    unique={(m,a.get("symbol")) for m,items in market_results.items() if m!="MARGIN" for a in items if a.get("symbol")}; count=len(spot) if spot else len(unique)
    parts=["<html><body>","<h1>Binance Multi-Market Screener — Filtering Pipeline</h1>",f"<p><b>Date :</b> {now}</p>",f"<p><b>Actifs uniques :</b> {count:,}</p>","<p>Filtrage structurel et liquidité uniquement. Aucun indicateur technique et aucun ordre Binance.</p><hr>"]
    if spot: parts += ["<h2>Synthèse Spot</h2>",f"<p><b>Univers Spot après filtres :</b> {len(spot):,} actifs.</p>","<p><b>Catégories :</b> "+"; ".join(f"{k}: {v}" for k,v in cats.items())+"</p>","<p><b>Classement :</b> tous les survivants sont classés par un score de qualité de marché : Depth absolue 35 %, volume 24h 30 %, Depth/Volume 20 %, spread 15 %. Le classement n'ajoute aucun filtre.</p>",spot_base_asset_summary_html(spot)]
    for market in ["SPOT","USDⓈ-M FUTURES","COIN-M FUTURES","OPTIONS","TOKENIZED STOCKS","MARGIN"]:
        if market in market_results: parts.append(market_summary_html(market,market_results[market],market_audits.get(market)))
    parts.append("<hr><h2>Marchés non intégrés</h2><ul><li><b>P2P :</b> non intégré. Aucune API publique officielle adaptée au même type de screening n'est utilisée.</li></ul>")
    if unavailable_markets: parts.append("<h2>Marchés indisponibles</h2><ul>"+"".join(f"<li>{html_escape(m)}</li>" for m in unavailable_markets)+"</ul>")
    parts.append(f"<h2>Paramètres principaux</h2><ul><li>Spot quotes : {', '.join(sorted(QUOTE_ASSETS)) if QUOTE_ASSETS else 'dynamiques — stablecoins actifs détectés depuis Binance exchangeInfo'}</li><li>Spot volume minimum actif : ${MIN_24H_QUOTE_VOLUME:,.0f}</li><li>Order Book Depth Spot : {'activé' if ORDER_BOOK_DEPTH_ENABLED else 'désactivé'} — profondeur minimale ${MIN_ORDER_BOOK_DEPTH_QUOTE:,.0f} dans ±{ORDER_BOOK_DEPTH_PCT:.2f}% (limit {ORDER_BOOK_DEPTH_LIMIT}, workers {ORDER_BOOK_DEPTH_WORKERS})</li><li>Spread Spot maximum : {MAX_SPREAD_PERCENT:.2f}%</li><li>Historique minimum Spot : {MIN_HISTORY_DAYS} jours en bougies 1h</li><li>Futures volume minimum : ${MIN_FUTURES_QUOTE_VOLUME:,.0f}</li></ul>")
    if warnings: parts.append("<h2>Avertissements</h2><ul>"+"".join(f"<li>{html_escape(w)}</li>" for w in warnings)+"</ul>")
    if errors: parts.append("<h2>Erreurs techniques réelles</h2><ul>"+"".join(f"<li>{html_escape(e)}</li>" for e in errors)+"</ul>")
    else: parts.append("<h2>État technique</h2><p><b>Erreurs techniques réelles : 0</b></p>")
    parts.append("<hr><p><b>Important :</b> ce programme effectue uniquement de la collecte et de l'analyse de données de marché. Aucun ordre Binance n'est exécuté.</p></body></html>"); return "".join(parts)


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
    print("BINANCE MULTI-MARKET SCREENER V3 — FILTERING PIPELINE")
    print("=" * 70)

    if ENABLE_SPOT:
        print("\n[SPOT]")
        try:
            assets, audit = run_spot(warnings)
            market_results["SPOT"], market_audits["SPOT"] = assets, audit
            print(f"Spot survivors: {len(assets):,}")
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
                message, kind = format_market_exception("TOKENIZED STOCKS", exc)
                if kind == "unavailable": unavailable_markets.append(message)
                else: errors.append(message)

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