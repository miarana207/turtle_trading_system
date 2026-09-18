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
#
# This version intentionally contains NO technical indicators.
# It focuses only on market-universe construction, liquidity,
# tradability and other explicit filtering criteria.
# NO ORDERS ARE EVER EXECUTED.
# ============================================================

# ----------------------------- GLOBAL CONFIG -----------------------------
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

SPOT_BASE_URL = os.getenv(
    "BINANCE_SPOT_BASE_URL",
    os.getenv("BINANCE_BASE_URL", "https://data-api.binance.vision"),
)
USDM_BASE_URL = os.getenv("BINANCE_USDM_BASE_URL", "https://fapi.binance.com")
COINM_BASE_URL = os.getenv("BINANCE_COINM_BASE_URL", "https://dapi.binance.com")
OPTIONS_BASE_URL = os.getenv("BINANCE_OPTIONS_BASE_URL", "https://eapi.binance.com")
TOKENIZED_BASE_URL = os.getenv("BINANCE_TOKENIZED_BASE_URL", "https://api.binance.com")

# ----------------------------- SPOT FILTERS -----------------------------
QUOTE_ASSETS = {
    x.strip().upper()
    for x in os.getenv("QUOTE_ASSETS", "").split(",")
    if x.strip()
}
EXCLUDE_STABLECOINS = os.getenv("EXCLUDE_STABLECOINS", "true").lower() == "true"
EXCLUDE_LEVERAGED_TOKENS = os.getenv("EXCLUDE_LEVERAGED_TOKENS", "true").lower() == "true"
MIN_24H_QUOTE_VOLUME = float(os.getenv("MIN_24H_QUOTE_VOLUME", "1000000"))
MAX_SPREAD_PERCENT = float(os.getenv("MAX_SPREAD_PERCENT", "0.10"))
MIN_HISTORY_DAYS = int(os.getenv("MIN_HISTORY_DAYS", "30"))

# Order-book depth is a liquidity filter, not a technical indicator.
ORDER_BOOK_DEPTH_ENABLED = os.getenv("ORDER_BOOK_DEPTH_ENABLED", "true").lower() == "true"
ORDER_BOOK_DEPTH_LIMIT = int(os.getenv("ORDER_BOOK_DEPTH_LIMIT", "100"))
ORDER_BOOK_DEPTH_PCT = float(os.getenv("ORDER_BOOK_DEPTH_PCT", "0.25"))
MIN_ORDER_BOOK_DEPTH_QUOTE = float(os.getenv("MIN_ORDER_BOOK_DEPTH_QUOTE", "25000"))
ORDER_BOOK_DEPTH_WORKERS = int(os.getenv("ORDER_BOOK_DEPTH_WORKERS", "8"))

# Diagnostic only: does not reject an asset.
DEPTH_VOLUME_ANOMALY_PERCENT = float(os.getenv("DEPTH_VOLUME_ANOMALY_PERCENT", "100"))
BASE_ASSET_SUMMARY_LIMIT = int(os.getenv("BASE_ASSET_SUMMARY_LIMIT", "20"))

# Explicit known tokenized/special Spot bases. No ticker-suffix inference.
TOKENIZED_SPOT_BASES = {
    x.strip().upper()
    for x in os.getenv(
        "BINANCE_TOKENIZED_SPOT_BASES",
        "AAPLB,CRCLB,DRAMB,MRVLB,MSTRB,MUB,NVDAB,QQQB,SNDKB,SKHYB,SNXXB,SPCXB,TQQQB,TSLAB",
    ).split(",")
    if x.strip()
}

# Binance does not expose one universal public isStablecoin flag in Spot.
STABLECOIN_BASES = {
    "USDT", "USDC", "FDUSD", "BUSD", "DAI", "TUSD", "USDP", "USDE",
    "USDD", "FRAX", "PYUSD", "EURC", "USD1", "RLUSD", "XUSD", "EURI",
    "USDG", "USDS", "U", "AEUR", "PAXG", "USD0",
}
STABLECOIN_BASES.update(
    x.strip().upper()
    for x in os.getenv("BINANCE_STABLECOIN_QUOTES", "").split(",")
    if x.strip()
)
STABLECOIN_QUOTE_MARKERS = (
    "USDT", "USDC", "FDUSD", "TUSD", "USDP", "USDE", "USDD",
    "PYUSD", "USD1", "RLUSD", "USDG", "USDS", "USD0", "XUSD",
    "EURC", "EURI", "AEUR",
)
LEVERAGED_SUFFIXES = ("UP", "DOWN", "BULL", "BEAR")
LEVERAGED_PATTERNS = ("3L", "3S", "5L", "5S", "2L", "2S")

# ----------------------------- FUTURES FILTERS -----------------------------
FUTURES_QUOTE_ASSETS = {
    x.strip().upper()
    for x in os.getenv("FUTURES_QUOTE_ASSETS", "USDT,USDC").split(",")
    if x.strip()
}
FUTURES_CONTRACT_TYPES = {
    x.strip().upper()
    for x in os.getenv("FUTURES_CONTRACT_TYPES", "PERPETUAL").split(",")
    if x.strip()
}
MIN_FUTURES_QUOTE_VOLUME = float(os.getenv("MIN_FUTURES_QUOTE_VOLUME", "5000000"))
MIN_FUTURES_TRADES = int(os.getenv("MIN_FUTURES_TRADES", "1000"))
MAX_FUTURES_SPREAD_PERCENT = float(os.getenv("MAX_FUTURES_SPREAD_PERCENT", "0.20"))
MIN_FUNDING_RATE_PERCENT = float(os.getenv("MIN_FUNDING_RATE_PERCENT", "-1.0"))
MAX_FUNDING_RATE_PERCENT = float(os.getenv("MAX_FUNDING_RATE_PERCENT", "1.0"))

# ----------------------------- OPTIONS FILTERS -----------------------------
OPTIONS_QUOTE_ASSETS = {
    x.strip().upper()
    for x in os.getenv("OPTIONS_QUOTE_ASSETS", "USDT").split(",")
    if x.strip()
}
MIN_OPTIONS_QUOTE_VOLUME = float(os.getenv("MIN_OPTIONS_QUOTE_VOLUME", "0"))
MIN_OPTIONS_TRADES = int(os.getenv("MIN_OPTIONS_TRADES", "0"))
MAX_OPTIONS_SPREAD_PERCENT = float(os.getenv("MAX_OPTIONS_SPREAD_PERCENT", "5.0"))
OPTIONS_MAX_ASSETS = int(os.getenv("OPTIONS_MAX_ASSETS", "500"))

# ----------------------------- TOKENIZED STOCK FILTERS -----------------------------
TOKENIZED_MAX_ASSETS = int(os.getenv("TOKENIZED_MAX_ASSETS", "100"))
MAX_TOKENIZED_SPREAD_PERCENT = float(os.getenv("MAX_TOKENIZED_SPREAD_PERCENT", "1.0"))


class BinanceHTTPError(RuntimeError):
    pass


def is_geo_restriction_error(exc: Exception) -> bool:
    text = str(exc).lower()
    return "http 451" in text or ("451" in text and "unavailable" in text)


def format_market_exception(market: str, exc: Exception) -> Tuple[str, str]:
    if is_geo_restriction_error(exc):
        return (
            f"{market} indisponible : Binance retourne HTTP 451 (restriction géographique / conditions d'éligibilité depuis le runner GitHub).",
            "unavailable",
        )
    return (f"{market}: {exc}", "error")


def http_get_json(
    base_url: str,
    path: str,
    params: Optional[Dict[str, Any]] = None,
    headers: Optional[Dict[str, str]] = None,
) -> Any:
    url = base_url.rstrip("/") + path
    if params:
        query = urlencode({k: v for k, v in params.items() if v is not None})
        if query:
            url += "?" + query

    last_error: Optional[Exception] = None
    for attempt in range(HTTP_RETRIES + 1):
        try:
            request = Request(
                url,
                headers={
                    "User-Agent": "BinanceMultiMarketScreener/3.0",
                    **(headers or {}),
                },
                method="GET",
            )
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
    base = str(base_asset).upper()
    return any(base.endswith(x) for x in LEVERAGED_SUFFIXES + LEVERAGED_PATTERNS)


class CriterionAudit:
    def __init__(self) -> None:
        self.rows: List[Dict[str, Any]] = []
        self.diagnostics: Dict[str, Any] = {}

    def add(self, name: str, before: int, selected: int) -> None:
        rejected = before - selected
        retention = selected / before * 100.0 if before else 0.0
        rejection = rejected / before * 100.0 if before else 0.0
        self.rows.append(
            {
                "criterion": name,
                "before": before,
                "selected": selected,
                "rejected": rejected,
                "retention": retention,
                "rejection": rejection,
            }
        )


def apply_criterion(
    assets: List[Dict[str, Any]],
    audit: CriterionAudit,
    name: str,
    predicate: Callable[[Dict[str, Any]], bool],
) -> List[Dict[str, Any]]:
    before = len(assets)
    selected = [asset for asset in assets if predicate(asset)]
    audit.add(name, before, len(selected))
    return selected


# ----------------------------- SPOT DATA -----------------------------
def spot_exchange_info() -> Dict[str, Any]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/exchangeInfo")


def spot_tickers() -> List[Dict[str, Any]]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/ticker/24hr")


def spot_book_tickers() -> List[Dict[str, Any]]:
    return http_get_json(SPOT_BASE_URL, "/api/v3/ticker/bookTicker")


def spot_klines(symbol: str, interval: str, limit: int) -> List[List[Any]]:
    return http_get_json(
        SPOT_BASE_URL,
        "/api/v3/klines",
        {"symbol": symbol, "interval": interval, "limit": limit},
    )


def discover_active_stablecoin_quotes(exchange_info: Dict[str, Any]) -> set[str]:
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
    active_quotes = {
        str(x.get("quoteAsset", "")).upper().strip()
        for x in exchange_info.get("symbols", [])
        if isinstance(x, dict)
    }
    if QUOTE_ASSETS:
        return QUOTE_ASSETS & active_quotes
    return discover_active_stablecoin_quotes(exchange_info)


def build_spot_universe(exchange_info: Dict[str, Any]) -> List[Dict[str, Any]]:
    result: List[Dict[str, Any]] = []
    for x in exchange_info.get("symbols", []):
        if not isinstance(x, dict):
            continue
        result.append(
            {
                "market": "SPOT",
                "symbol": x.get("symbol", ""),
                "baseAsset": x.get("baseAsset", ""),
                "quoteAsset": str(x.get("quoteAsset", "")).upper(),
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
            }
        )
    return result


def merge_spot_tickers(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for asset in assets:
        ticker = by_symbol.get(asset["symbol"], {})
        asset.update(
            lastPrice=as_float(ticker.get("lastPrice")),
            priceChangePercent=as_float(ticker.get("priceChangePercent")),
            quoteVolume=as_float(ticker.get("quoteVolume")),
            trades=as_int(ticker.get("count")),
            volume=as_float(ticker.get("volume")),
            weightedAvgPrice=as_float(ticker.get("weightedAvgPrice")),
            highPrice=as_float(ticker.get("highPrice")),
            lowPrice=as_float(ticker.get("lowPrice")),
        )


def merge_spot_books(assets: List[Dict[str, Any]], books: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in books if x.get("symbol")}
    for asset in assets:
        book = by_symbol.get(asset["symbol"], {})
        bid = as_float(book.get("bidPrice"))
        ask = as_float(book.get("askPrice"))
        asset.update(
            bidPrice=bid,
            askPrice=ask,
            spreadPercent=safe_percent_spread(bid, ask),
        )


def spot_order_book(symbol: str) -> Dict[str, Any]:
    return http_get_json(
        SPOT_BASE_URL,
        "/api/v3/depth",
        {"symbol": symbol, "limit": ORDER_BOOK_DEPTH_LIMIT},
    )


def order_book_depth_metrics(book: Dict[str, Any], mid_price: float) -> Dict[str, float]:
    if mid_price <= 0:
        return {"depthBidQuote": 0.0, "depthAskQuote": 0.0, "depthTotalQuote": 0.0}

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


def merge_spot_order_book_depth(
    assets: List[Dict[str, Any]], warnings: Optional[List[str]] = None
) -> None:
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
            except Exception as exc:
                failures += 1
                asset["depthError"] = str(exc)
                asset["depthTotalQuote"] = 0.0

    if failures and warnings is not None:
        warnings.append(
            f"Spot Order Book Depth : {failures} actif(s) n'ont pas pu être interrogé(s)."
        )


def check_history_assets(assets: List[Dict[str, Any]], warnings: List[str]) -> None:
    if MIN_HISTORY_DAYS <= 0 or not assets:
        for asset in assets:
            asset["historyAvailable"] = True
        return

    required_bars = max(1, int(math.ceil(MIN_HISTORY_DAYS * 24)))
    workers = max(1, min(ORDER_BOOK_DEPTH_WORKERS, len(assets)))

    def check(asset: Dict[str, Any]) -> Tuple[str, bool, Optional[str]]:
        try:
            klines = spot_klines(asset["symbol"], "1h", required_bars)
            return asset["symbol"], len(klines) >= required_bars, None
        except Exception as exc:
            return asset["symbol"], False, str(exc)

    by_symbol = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        futures = [executor.submit(check, asset) for asset in assets]
        for future in concurrent.futures.as_completed(futures):
            symbol, ok, error = future.result()
            by_symbol[symbol] = (ok, error)

    errors = 0
    for asset in assets:
        ok, error = by_symbol.get(asset["symbol"], (False, "historique absent"))
        asset["historyAvailable"] = ok
        if error:
            asset["historyError"] = error
            errors += 1
    if errors:
        warnings.append(f"Historique Spot : {errors} actif(s) ont retourné une erreur de données.")


# ----------------------------- SPOT FILTER PIPELINE -----------------------------
def screen_spot(
    assets: List[Dict[str, Any]],
    quote_assets: set[str],
    warnings: List[str],
) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()

    assets = apply_criterion(
        assets, audit, "1. Status TRADING", lambda x: str(x.get("status", "")).upper() == "TRADING"
    )
    assets = apply_criterion(
        assets,
        audit,
        "2. Permission Spot",
        lambda x: (
            not x.get("permissions")
            or "SPOT" in {str(v).upper() for v in x.get("permissions", [])}
            or x.get("isSpotTradingAllowed") is True
        ),
    )
    assets = apply_criterion(
        assets, audit, "3. Quote asset autorisé", lambda x: x.get("quoteAsset") in quote_assets
    )

    if EXCLUDE_STABLECOINS:
        assets = apply_criterion(
            assets,
            audit,
            "4. Exclusion stablecoins",
            lambda x: str(x.get("baseAsset", "")).upper() not in STABLECOIN_BASES,
        )
    else:
        audit.add("4. Exclusion stablecoins", len(assets), len(assets))

    if EXCLUDE_LEVERAGED_TOKENS:
        assets = apply_criterion(
            assets,
            audit,
            "5. Exclusion tokens à levier",
            lambda x: not is_leveraged_symbol(x.get("baseAsset", "")),
        )
    else:
        audit.add("5. Exclusion tokens à levier", len(assets), len(assets))

    assets = apply_criterion(
        assets, audit, "6. Prix 24h disponible", lambda x: as_float(x.get("lastPrice")) > 0
    )
    assets = apply_criterion(
        assets,
        audit,
        "7. Volume quote 24h minimum",
        lambda x: as_float(x.get("quoteVolume")) >= MIN_24H_QUOTE_VOLUME,
    )

    if ORDER_BOOK_DEPTH_ENABLED:
        merge_spot_order_book_depth(assets, warnings)
        for asset in assets:
            volume = as_float(asset.get("quoteVolume"))
            depth = as_float(asset.get("depthTotalQuote"))
            asset["depthToVolumePercent"] = depth / volume * 100.0 if volume > 0 else None
        assets = apply_criterion(
            assets,
            audit,
            "8. Profondeur carnet minimum",
            lambda x: as_float(x.get("depthTotalQuote")) >= MIN_ORDER_BOOK_DEPTH_QUOTE,
        )
    else:
        audit.add("8. Profondeur carnet minimum", len(assets), len(assets))

    assets = apply_criterion(
        assets,
        audit,
        "9. Spread maximum",
        lambda x: x.get("spreadPercent") is not None
        and as_float(x.get("spreadPercent")) <= MAX_SPREAD_PERCENT,
    )

    if MIN_HISTORY_DAYS > 0:
        check_history_assets(assets, warnings)
        assets = apply_criterion(
            assets,
            audit,
            f"10. Historique minimum ({MIN_HISTORY_DAYS} jours en 1h)",
            lambda x: x.get("historyAvailable") is True,
        )
    else:
        for asset in assets:
            asset["historyAvailable"] = True
        audit.add("10. Historique minimum", len(assets), len(assets))

    # Diagnostic non bloquant pour la lecture du pipeline.
    volume_universe = [a for a in assets if as_float(a.get("quoteVolume")) > 0]
    audit.diagnostics["volume_distribution"] = {
        threshold: sum(1 for a in volume_universe if as_float(a.get("quoteVolume")) >= threshold)
        for threshold in (
            1_000_000, 2_000_000, 5_000_000, 10_000_000,
            20_000_000, 50_000_000, 100_000_000, 500_000_000, 1_000_000_000,
        )
    }
    audit.diagnostics["volume_universe_count"] = len(volume_universe)
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


# ----------------------------- FUTURES DATA -----------------------------
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
        status = str(x.get("status", x.get("contractStatus", ""))).upper()
        if contract not in FUTURES_CONTRACT_TYPES or quote not in FUTURES_QUOTE_ASSETS:
            continue
        result.append(
            {
                "market": "USDⓈ-M FUTURES",
                "symbol": x.get("symbol", ""),
                "pair": x.get("pair", ""),
                "baseAsset": x.get("baseAsset", ""),
                "quoteAsset": quote,
                "contractType": contract,
                "status": status,
            }
        )
    return result


def build_coinm_universe(exchange_info: Dict[str, Any]) -> List[Dict[str, Any]]:
    result = []
    for x in exchange_info.get("symbols", []):
        contract = str(x.get("contractType", "")).upper()
        status = str(x.get("contractStatus", x.get("status", ""))).upper()
        if contract not in FUTURES_CONTRACT_TYPES:
            continue
        result.append(
            {
                "market": "COIN-M FUTURES",
                "symbol": x.get("symbol", ""),
                "pair": x.get("pair", ""),
                "baseAsset": x.get("baseAsset", ""),
                "quoteAsset": str(x.get("quoteAsset", "")).upper(),
                "marginAsset": x.get("marginAsset", ""),
                "contractType": contract,
                "status": status,
            }
        )
    return result


def merge_futures_tickers(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for asset in assets:
        ticker = by_symbol.get(asset["symbol"], {})
        quote_volume = as_float(ticker.get("quoteVolume"))
        if quote_volume <= 0:
            quote_volume = as_float(ticker.get("baseVolume"))
        asset.update(
            lastPrice=as_float(ticker.get("lastPrice")),
            priceChangePercent=as_float(ticker.get("priceChangePercent")),
            volume=as_float(ticker.get("volume")),
            quoteVolume=quote_volume,
            trades=as_int(ticker.get("count")),
            highPrice=as_float(ticker.get("highPrice")),
            lowPrice=as_float(ticker.get("lowPrice")),
        )


def merge_futures_books(assets: List[Dict[str, Any]], books: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in books if x.get("symbol")}
    for asset in assets:
        book = by_symbol.get(asset["symbol"], {})
        bid = as_float(book.get("bidPrice"))
        ask = as_float(book.get("askPrice"))
        asset.update(bidPrice=bid, askPrice=ask, spreadPercent=safe_percent_spread(bid, ask))


def merge_funding(assets: List[Dict[str, Any]], funding_data: Any) -> None:
    if isinstance(funding_data, dict):
        funding_data = [funding_data]
    by_symbol = {x.get("symbol"): x for x in (funding_data or []) if x.get("symbol")}
    for asset in assets:
        item = by_symbol.get(asset["symbol"], {})
        if "lastFundingRate" in item:
            asset["fundingRate"] = as_float(item.get("lastFundingRate")) * 100.0


def screen_futures(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Contrat TRADING", lambda x: x.get("status") == "TRADING")
    assets = apply_criterion(assets, audit, "2. Prix disponible", lambda x: as_float(x.get("lastPrice")) > 0)
    assets = apply_criterion(
        assets,
        audit,
        "3. Volume quote minimum",
        lambda x: as_float(x.get("quoteVolume")) >= MIN_FUTURES_QUOTE_VOLUME,
    )
    assets = apply_criterion(
        assets, audit, "4. Trades minimum", lambda x: as_int(x.get("trades")) >= MIN_FUTURES_TRADES
    )
    assets = apply_criterion(
        assets,
        audit,
        "5. Spread maximum",
        lambda x: x.get("spreadPercent") is not None
        and as_float(x.get("spreadPercent")) <= MAX_FUTURES_SPREAD_PERCENT,
    )
    assets = apply_criterion(
        assets, audit, "6. Funding disponible", lambda x: "fundingRate" in x
    )
    assets = apply_criterion(
        assets,
        audit,
        "7. Funding dans la plage autorisée",
        lambda x: MIN_FUNDING_RATE_PERCENT <= as_float(x.get("fundingRate")) <= MAX_FUNDING_RATE_PERCENT,
    )
    assets.sort(key=lambda x: as_float(x.get("quoteVolume")), reverse=True)
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
        result.append(
            {
                "market": "OPTIONS",
                "symbol": x.get("symbol", ""),
                "underlying": x.get("underlying", ""),
                "quoteAsset": quote,
                "side": x.get("side", ""),
                "strikePrice": as_float(x.get("strikePrice")),
                "expiryDate": x.get("expiryDate"),
                "status": x.get("status", ""),
            }
        )
    return result


def merge_option_tickers(assets: List[Dict[str, Any]], tickers: List[Dict[str, Any]]) -> None:
    by_symbol = {x.get("symbol"): x for x in tickers if x.get("symbol")}
    for asset in assets:
        ticker = by_symbol.get(asset["symbol"], {})
        bid = as_float(ticker.get("bidPrice"))
        ask = as_float(ticker.get("askPrice"))
        asset.update(
            lastPrice=as_float(ticker.get("lastPrice")),
            priceChangePercent=as_float(ticker.get("priceChangePercent")),
            volume=as_float(ticker.get("volume")),
            quoteVolume=as_float(ticker.get("amount")),
            trades=as_int(ticker.get("tradeCount")),
            bidPrice=bid,
            askPrice=ask,
            spreadPercent=safe_percent_spread(bid, ask),
        )


def screen_options(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(assets, audit, "1. Option TRADING", lambda x: x.get("status") == "TRADING")
    assets = apply_criterion(assets, audit, "2. Prix disponible", lambda x: as_float(x.get("lastPrice")) > 0)
    assets = apply_criterion(
        assets,
        audit,
        "3. Volume quote minimum",
        lambda x: as_float(x.get("quoteVolume")) >= MIN_OPTIONS_QUOTE_VOLUME,
    )
    assets = apply_criterion(
        assets, audit, "4. Trades minimum", lambda x: as_int(x.get("trades")) >= MIN_OPTIONS_TRADES
    )
    assets = apply_criterion(
        assets,
        audit,
        "5. Spread maximum",
        lambda x: x.get("spreadPercent") is not None
        and as_float(x.get("spreadPercent")) <= MAX_OPTIONS_SPREAD_PERCENT,
    )
    assets.sort(key=lambda x: as_float(x.get("quoteVolume")), reverse=True)
    if OPTIONS_MAX_ASSETS > 0:
        assets = assets[:OPTIONS_MAX_ASSETS]
    audit.add("6. Limite options maximale", len(assets), len(assets))
    return assets, audit


# ----------------------------- TOKENIZED STOCKS -----------------------------
def tokenized_headers() -> Dict[str, str]:
    if not BINANCE_API_KEY:
        raise BinanceHTTPError("BINANCE_API_KEY absent")
    return {"X-MBX-APIKEY": BINANCE_API_KEY}


def tokenized_exchange_info() -> Dict[str, Any]:
    return http_get_json(
        TOKENIZED_BASE_URL,
        "/sapi/v1/equity/market/exchangeInfo",
        headers=tokenized_headers(),
    )


def tokenized_assets_info() -> Any:
    return http_get_json(
        TOKENIZED_BASE_URL,
        "/sapi/v1/equity/market/tokenized-assets",
        headers=tokenized_headers(),
    )


def tokenized_quote(symbol: str) -> Dict[str, Any]:
    return http_get_json(
        TOKENIZED_BASE_URL,
        "/sapi/v1/equity/market/quote",
        params={"symbol": symbol},
        headers=tokenized_headers(),
    )


def build_tokenized_universe(
    exchange_info: Dict[str, Any], tokenized_assets: Any
) -> List[Dict[str, Any]]:
    token_map: Dict[str, Dict[str, Any]] = {}
    if isinstance(tokenized_assets, list):
        for item in tokenized_assets:
            if not isinstance(item, dict):
                continue
            code = item.get("assetCode")
            if code:
                token_map[str(code)] = item

    result = []
    for item in exchange_info.get("symbols", []):
        if not isinstance(item, dict):
            continue
        symbol = item.get("symbol", "")
        tradability = str(item.get("tradability", "NONE")).upper()
        if tradability == "NONE":
            continue
        token = token_map.get(symbol, {})
        result.append(
            {
                "market": "TOKENIZED STOCKS",
                "symbol": symbol,
                "tradability": tradability,
                "overnightSupported": item.get("overnightSupported", False),
                "fractionable": item.get("fractionable", False),
                "underlyingEquitySymbol": token.get("underlyingEquitySymbol", ""),
                "assetName": token.get("assetName", ""),
            }
        )
    return result


def merge_tokenized_quotes(assets: List[Dict[str, Any]]) -> None:
    if not assets:
        return

    def fetch(asset: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asset["symbol"], tokenized_quote(asset["symbol"])

    workers = max(1, min(8, len(assets)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        future_map = {executor.submit(fetch, asset): asset for asset in assets}
        for future in concurrent.futures.as_completed(future_map):
            try:
                symbol, quote = future.result()
                asset = future_map[future]
                bid = as_float(quote.get("bidPrice"))
                ask = as_float(quote.get("askPrice"))
                asset.update(
                    bidPrice=bid,
                    askPrice=ask,
                    bidSize=as_float(quote.get("bidSize")),
                    askSize=as_float(quote.get("askSize")),
                    spreadPercent=safe_percent_spread(bid, ask),
                )
            except Exception:
                future_map[future]["quoteError"] = True


def screen_tokenized(assets: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    audit = CriterionAudit()
    assets = apply_criterion(
        assets,
        audit,
        "1. Tradabilité",
        lambda x: x.get("tradability") in {"BUY_SELL", "BUY", "SELL"},
    )
    assets = apply_criterion(
        assets,
        audit,
        "2. Bid/ask disponibles",
        lambda x: as_float(x.get("bidPrice")) > 0 and as_float(x.get("askPrice")) > 0,
    )
    assets = apply_criterion(
        assets,
        audit,
        "3. Spread maximum",
        lambda x: x.get("spreadPercent") is not None
        and as_float(x.get("spreadPercent")) <= MAX_TOKENIZED_SPREAD_PERCENT,
    )
    assets.sort(key=lambda x: as_float(x.get("bidPrice")), reverse=True)
    if TOKENIZED_MAX_ASSETS > 0:
        assets = assets[:TOKENIZED_MAX_ASSETS]
    audit.add("4. Limite tokenized maximale", len(assets), len(assets))
    return assets, audit


# ----------------------------- REPORTING -----------------------------
def html_escape(value: Any) -> str:
    return html.escape("" if value is None else str(value), quote=True)


def format_number(value: Any, decimals: int = 2) -> str:
    try:
        return f"{float(value):,.{decimals}f}"
    except (TypeError, ValueError):
        return "-"


def asset_category(asset: Dict[str, Any]) -> str:
    market = asset.get("market", "")
    if market != "SPOT":
        return market or "AUTRE"

    explicit_tokenized = (
        asset.get("isTokenized") is True
        or asset.get("tokenized") is True
        or asset.get("isTokenizedAsset") is True
        or str(asset.get("assetType", "")).upper() in {"TOKENIZED", "TOKENIZED_STOCK", "STOCK_TOKEN"}
        or str(asset.get("productType", "")).upper() in {"TOKENIZED", "TOKENIZED_STOCK", "STOCK_TOKEN"}
    )
    if explicit_tokenized:
        return "SPOT / TOKENIZED / SPECIAL"
    if str(asset.get("baseAsset", "")).upper() in TOKENIZED_SPOT_BASES:
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
        volume = as_float(asset.get("quoteVolume"))
        depth = as_float(asset.get("depthTotalQuote"))
        asset["depthToVolumePercent"] = depth / volume * 100.0 if volume > 0 else None
        asset["depthVolumeStatus"] = depth_volume_status(asset)


def audit_to_html(audit: CriterionAudit) -> str:
    rows = [
        "<h3>Audit du pipeline de filtrage</h3>",
        "<table border='1' cellpadding='5' cellspacing='0' style='border-collapse:collapse;width:100%;font-size:12px'>",
        "<tr><th>Étape</th><th>Avant</th><th>Sélectionnés</th><th>Rejetés</th><th>Rétention</th><th>Rejet</th></tr>",
    ]
    for row in audit.rows:
        rows.append(
            "<tr>"
            f"<td>{html_escape(row['criterion'])}</td>"
            f"<td>{row['before']:,}</td>"
            f"<td>{row['selected']:,}</td>"
            f"<td>{row['rejected']:,}</td>"
            f"<td>{row['retention']:.1f}%</td>"
            f"<td>{row['rejection']:.1f}%</td>"
            "</tr>"
        )
    rows.append("</table>")
    return "".join(rows)


def spot_base_asset_summary_html(assets: List[Dict[str, Any]]) -> str:
    if not assets:
        return ""
    enrich_spot_reporting(assets)
    groups: Dict[str, Dict[str, Any]] = {}
    for asset in assets:
        base = str(asset.get("baseAsset", "")).upper().strip()
        if not base:
            continue
        group = groups.setdefault(
            base,
            {"pairs": 0, "volume": 0.0, "symbols": [], "categories": {}},
        )
        group["pairs"] += 1
        group["volume"] += as_float(asset.get("quoteVolume"))
        category = asset.get("assetCategory", "SPOT / CRYPTO")
        group["categories"][category] = group["categories"].get(category, 0) + 1
        if len(group["symbols"]) < 6 and asset.get("symbol"):
            group["symbols"].append(asset["symbol"])

    ordered = sorted(groups.items(), key=lambda item: item[1]["volume"], reverse=True)
    limit = BASE_ASSET_SUMMARY_LIMIT if BASE_ASSET_SUMMARY_LIMIT > 0 else len(ordered)
    out = [
        "<h3>Vue consolidée par actif de base</h3>",
        "<p>Cette vue regroupe les paires du même actif sous-jacent. Elle ne remplace pas le pipeline de filtrage et ne supprime aucune paire.</p>",
        "<table border='1' cellpadding='5' cellspacing='0' style='border-collapse:collapse'>",
        "<tr><th>Base</th><th>Catégorie</th><th>Paires</th><th>Volume cumulé</th><th>Paires représentatives</th></tr>",
    ]
    for base, group in ordered[:limit]:
        category = max(group["categories"].items(), key=lambda x: x[1])[0]
        out.append(
            "<tr>"
            f"<td><b>{html_escape(base)}</b></td>"
            f"<td>{html_escape(category)}</td>"
            f"<td>{group['pairs']}</td>"
            f"<td>${format_number(group['volume'], 0)}</td>"
            f"<td>{html_escape(', '.join(group['symbols']))}</td>"
            "</tr>"
        )
    out.append("</table>")
    return "".join(out)


def market_summary_html(
    market: str, assets: List[Dict[str, Any]], audit: Optional[CriterionAudit]
) -> str:
    if market == "MARGIN":
        return (
            "<h2>MARGIN</h2>"
            f"<p><b>Univers sous-jacent :</b> {len(assets):,} actifs Spot ayant passé le pipeline Spot.</p>"
            "<p>L'éligibilité réelle au Margin dépend du compte Binance et n'est pas garantie par ce screener.</p>"
        )

    out = [f"<h2>{html_escape(market)}</h2>", f"<p><b>Survivants :</b> {len(assets):,}</p>"]
    if audit:
        out.append(audit_to_html(audit))

    if assets:
        if market == "SPOT":
            enrich_spot_reporting(assets)
        out.extend(
            [
                "<table border='1' cellpadding='5' cellspacing='0' style='border-collapse:collapse;width:100%;font-size:12px'>",
                "<tr><th>Catégorie</th><th>Symbol</th><th>Volume 24h</th><th>Depth</th><th>Depth/Volume</th><th>Spread</th><th>Variation 24h</th><th>Historique</th></tr>",
            ]
        )
        sorted_assets = sorted(
            assets,
            key=lambda x: (
                as_float(x.get("quoteVolume")),
                as_float(x.get("depthTotalQuote")),
            ),
            reverse=True,
        )
        for asset in sorted_assets[:EMAIL_TOP_RESULTS]:
            history = "OK" if asset.get("historyAvailable") else ("-" if market != "SPOT" else "NON")
            out.append(
                "<tr>"
                f"<td>{html_escape(asset.get('assetCategory', market))}</td>"
                f"<td><b>{html_escape(asset.get('symbol', '-'))}</b></td>"
                f"<td>${format_number(asset.get('quoteVolume', 0), 0)}</td>"
                f"<td>${format_number(asset.get('depthTotalQuote', 0), 0)}</td>"
                f"<td>{format_number(asset.get('depthToVolumePercent'), 3)}%</td>"
                f"<td>{format_number(asset.get('spreadPercent'), 4)}%</td>"
                f"<td>{format_number(asset.get('priceChangePercent'), 2)}%</td>"
                f"<td>{history}</td>"
                "</tr>"
            )
        out.append("</table>")
        if len(sorted_assets) > EMAIL_TOP_RESULTS:
            out.append(
                f"<p><i>{len(sorted_assets) - EMAIL_TOP_RESULTS:,} actifs supplémentaires ne sont pas affichés dans le tableau détaillé.</i></p>"
            )
    return "".join(out)


def build_report(
    market_results: Dict[str, List[Dict[str, Any]]],
    market_audits: Dict[str, CriterionAudit],
    errors: List[str],
    warnings: List[str],
    unavailable_markets: List[str],
) -> str:
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    parts = [
        "<html><body>",
        "<h1>Binance Multi-Market Screener V3 — Filtering Pipeline</h1>",
        f"<p><b>Date :</b> {now}</p>",
        "<p><b>Principe :</b> aucune analyse technique ni aucun indicateur n'est calculé dans cette version. Le programme se concentre sur le filtrage de l'univers de marché, la liquidité, la tradabilité et les contraintes de marché explicites.</p>",
        "<hr>",
    ]

    if "SPOT" in market_results:
        spot = market_results["SPOT"]
        parts.append(f"<h2>Synthèse Spot</h2><p><b>Survivants :</b> {len(spot):,}</p>")
        parts.append(spot_base_asset_summary_html(spot))

    for market in ["SPOT", "USDⓈ-M FUTURES", "COIN-M FUTURES", "OPTIONS", "TOKENIZED STOCKS", "MARGIN"]:
        if market in market_results:
            parts.append(market_summary_html(market, market_results[market], market_audits.get(market)))

    parts.append(
        "<h2>Marchés non intégrés</h2>"
        "<ul><li><b>P2P :</b> non intégré. Aucun ordre n'est exécuté.</li></ul>"
    )

    if unavailable_markets:
        parts.append(
            "<h2>Marchés indisponibles</h2><ul>"
            + "".join(f"<li>{html_escape(m)}</li>" for m in unavailable_markets)
            + "</ul>"
        )

    parts.append(
        "<h2>Paramètres actifs</h2><ul>"
        f"<li>Spot quotes : {', '.join(sorted(QUOTE_ASSETS)) if QUOTE_ASSETS else 'quotes stablecoin actives détectées automatiquement'}</li>"
        f"<li>Spot volume minimum : ${MIN_24H_QUOTE_VOLUME:,.0f}</li>"
        f"<li>Spot spread maximum : {MAX_SPREAD_PERCENT:.2f}%</li>"
        f"<li>Spot profondeur carnet : {'activée' if ORDER_BOOK_DEPTH_ENABLED else 'désactivée'} — minimum ${MIN_ORDER_BOOK_DEPTH_QUOTE:,.0f} dans ±{ORDER_BOOK_DEPTH_PCT:.2f}%</li>"
        f"<li>Spot historique minimum : {MIN_HISTORY_DAYS} jours en bougies 1h</li>"
        f"<li>Futures volume minimum : ${MIN_FUTURES_QUOTE_VOLUME:,.0f}</li>"
        f"<li>Futures trades minimum : {MIN_FUTURES_TRADES:,}</li>"
        f"<li>Futures spread maximum : {MAX_FUTURES_SPREAD_PERCENT:.2f}%</li>"
        f"<li>Funding autorisé : {MIN_FUNDING_RATE_PERCENT:.2f}% à {MAX_FUNDING_RATE_PERCENT:.2f}%</li>"
        f"<li>Options spread maximum : {MAX_OPTIONS_SPREAD_PERCENT:.2f}% — maximum affiché : {OPTIONS_MAX_ASSETS:,}</li>"
        f"<li>Tokenized Stocks spread maximum : {MAX_TOKENIZED_SPREAD_PERCENT:.2f}% — maximum : {TOKENIZED_MAX_ASSETS:,}</li>"
        "</ul>"
    )

    if warnings:
        parts.append(
            "<h2>Avertissements</h2><ul>"
            + "".join(f"<li>{html_escape(w)}</li>" for w in warnings)
            + "</ul>"
        )
    if errors:
        parts.append(
            "<h2>Erreurs techniques</h2><ul>"
            + "".join(f"<li>{html_escape(e)}</li>" for e in errors)
            + "</ul>"
        )
    else:
        parts.append("<h2>État technique</h2><p><b>Erreurs techniques réelles : 0</b></p>")

    parts.append(
        "<hr><p><b>Important :</b> ce programme effectue uniquement de la collecte et du filtrage de données de marché. Aucun ordre Binance n'est exécuté.</p>"
        "</body></html>"
    )
    return "".join(parts)


def send_email(subject: str, html_body: str) -> None:
    if not (EMAIL_USER and EMAIL_PASS and EMAIL_TO):
        raise RuntimeError("EMAIL_USER / EMAIL_PASS / EMAIL_TO non configurés")
    message = MIMEMultipart("alternative")
    message["Subject"] = subject
    message["From"] = EMAIL_USER
    message["To"] = EMAIL_TO
    message.attach(MIMEText(html_body, "html", "utf-8"))
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
        "Quote assets Spot : " + ", ".join(sorted(effective_quotes))
        if effective_quotes
        else "Aucun quote asset Spot autorisé n'a été détecté."
    )
    return screen_spot(assets, effective_quotes, warnings)


def run_usdm(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_usdm_universe(
        futures_exchange_info(USDM_BASE_URL, "/fapi/v1/exchangeInfo")
    )
    merge_futures_tickers(assets, futures_tickers(USDM_BASE_URL, "/fapi/v1/ticker/24hr"))
    merge_futures_books(assets, futures_book_tickers(USDM_BASE_URL, "/fapi/v1/ticker/bookTicker"))
    merge_funding(assets, futures_premium_index(USDM_BASE_URL, "/fapi/v1/premiumIndex"))
    return screen_futures(assets)


def run_coinm(warnings: List[str]) -> Tuple[List[Dict[str, Any]], CriterionAudit]:
    assets = build_coinm_universe(
        futures_exchange_info(COINM_BASE_URL, "/dapi/v1/exchangeInfo")
    )
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
    print("No technical indicators | No orders")
    print("=" * 70)

    if ENABLE_SPOT:
        print("\n[SPOT]")
        try:
            assets, audit = run_spot(warnings)
            market_results["SPOT"] = assets
            market_audits["SPOT"] = audit
            print(f"Spot survivors: {len(assets):,}")
        except Exception as exc:
            message, kind = format_market_exception("SPOT", exc)
            (unavailable_markets if kind == "unavailable" else errors).append(message)

    if ENABLE_MARGIN:
        print("\n[MARGIN]")
        if "SPOT" in market_results:
            market_results["MARGIN"] = build_margin_market(market_results["SPOT"])
            print(f"Margin underlying Spot universe: {len(market_results['MARGIN']):,}")
            warnings.append(
                "Margin : l'éligibilité réelle dépend du compte Binance et n'est pas garantie par le screener."
            )
        else:
            warnings.append("Margin ignoré car le scan Spot n'a pas abouti.")

    if ENABLE_USDM:
        print("\n[USDⓈ-M FUTURES]")
        try:
            assets, audit = run_usdm(warnings)
            market_results["USDⓈ-M FUTURES"] = assets
            market_audits["USDⓈ-M FUTURES"] = audit
            print(f"USDⓈ-M survivors: {len(assets):,}")
        except Exception as exc:
            message, kind = format_market_exception("USDⓈ-M FUTURES", exc)
            (unavailable_markets if kind == "unavailable" else errors).append(message)

    if ENABLE_COINM:
        print("\n[COIN-M FUTURES]")
        try:
            assets, audit = run_coinm(warnings)
            market_results["COIN-M FUTURES"] = assets
            market_audits["COIN-M FUTURES"] = audit
            print(f"COIN-M survivors: {len(assets):,}")
        except Exception as exc:
            message, kind = format_market_exception("COIN-M FUTURES", exc)
            (unavailable_markets if kind == "unavailable" else errors).append(message)

    if ENABLE_OPTIONS:
        print("\n[OPTIONS]")
        try:
            assets, audit = run_options(warnings)
            market_results["OPTIONS"] = assets
            market_audits["OPTIONS"] = audit
            print(f"Options survivors: {len(assets):,}")
        except Exception as exc:
            message, kind = format_market_exception("OPTIONS", exc)
            (unavailable_markets if kind == "unavailable" else errors).append(message)

    if ENABLE_TOKENIZED_STOCKS:
        print("\n[TOKENIZED STOCKS]")
        if not BINANCE_API_KEY:
            warnings.append("Tokenized Stocks non exécuté : BINANCE_API_KEY absent.")
        else:
            try:
                assets, audit = run_tokenized(warnings)
                market_results["TOKENIZED STOCKS"] = assets
                market_audits["TOKENIZED STOCKS"] = audit
                print(f"Tokenized Stocks survivors: {len(assets):,}")
            except Exception as exc:
                message, kind = format_market_exception("TOKENIZED STOCKS", exc)
                (unavailable_markets if kind == "unavailable" else errors).append(message)

    html_report = build_report(
        market_results,
        market_audits,
        errors,
        warnings,
        unavailable_markets,
    )
    elapsed = time.time() - started
    subject = f"Binance Multi-Market Screener — Filtering Pipeline — {datetime.now(timezone.utc):%Y-%m-%d %H:%M} UTC"

    try:
        send_email(subject, html_report)
        print(f"\nEmail envoyé. Durée : {elapsed:.2f}s")
    except Exception as exc:
        print("\nERREUR EMAIL:", exc)
        print(html_report)
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
