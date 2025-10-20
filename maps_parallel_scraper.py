#!/usr/bin/env python3
"""
Google Maps Public Data Research Tool - Webhook Ready Version
Scrapes Google Maps search results with full Supabase integration.
Designed for GitHub Actions webhook triggers.
"""

from seleniumbase import SB
import argparse
import base64
import csv
import json
import logging
import math
import mimetypes
import os
import re
import shutil
import sys
import time
import gzip
import zlib
import mycdp
from datetime import datetime, timezone
from functools import wraps
from html import unescape
from typing import Optional, List, Dict, Any, Tuple
from urllib.parse import parse_qs, quote, quote_plus, unquote, urlsplit, urlunsplit
from uuid import uuid4

from bs4 import BeautifulSoup
import requests

# Optional database driver support (psycopg3 or psycopg2)
psycopg = None  # type: ignore
psycopg2 = None  # type: ignore
sql = None  # type: ignore
Json = None  # type: ignore

try:  # pragma: no cover - optional dependency
    import psycopg  # type: ignore
    from psycopg import sql as psycopg_sql  # type: ignore
    from psycopg.types.json import Json as psycopg_json  # type: ignore
except ImportError:  # pragma: no cover - optional dependency
    psycopg = None  # type: ignore
else:
    sql = psycopg_sql
    Json = psycopg_json

if sql is None:  # pragma: no cover - optional dependency
    try:
        import psycopg2  # type: ignore
        from psycopg2 import sql as psycopg2_sql  # type: ignore
        from psycopg2.extras import Json as psycopg2_json  # type: ignore
    except ImportError:
        psycopg2 = None  # type: ignore
    else:
        sql = psycopg2_sql
        Json = psycopg2_json

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler('maps_scraper.log')
    ]
)
logger = logging.getLogger(__name__)

# Constants
PHONE_REGEX = re.compile(
    r"(?:\+?\d{1,3}[\s.-]?)?(?:\(?\d{3}\)?[\s.-]?)\d{3}[\s.-]?\d{4}"
)

DEFAULT_CONFIG = {
    "scroll_max": 40,
    "scroll_wait": 1.2,
    "scroll_settle_rounds": 3,
    "page_load_wait": 4.5,
    "sidebar_timeout": 14,
    "query_wait": 4.5,
    "max_parse_results": 0,  # 0 = unlimited
    "log_dir": "logs",
    "headless": True,
    "ad_block": True,
    "block_media": True,
    "zoom": 15,
    "proxy": None,
    "coordinates": None,
}

DEFAULT_BLOCKED_RESOURCE_PATTERNS: List[str] = [
    "*.png",
    "*.jpg",
    "*.jpeg",
    "*.webp",
    "*.gif",
    "*.svg",
    "*.ico",
    "*.bmp",
    "*.tif",
    "*.tiff",
    "*.mp4",
    "*.webm",
    "*.mp3",
    "*.m4a",
    "*.ogg",
    "*.wav",
    "*.avi",
    "*.mov",
    "*.woff",
    "*.woff2",
    "*.ttf",
    "*.eot",
    "*.otf",
    "https://lh*.googleusercontent.com/*",
]


def _env_int(name: str, default: int) -> int:
    """Read an integer environment variable safely with fallback."""
    raw = os.getenv(name)
    if raw is None:
        return default
    try:
        return int(raw)
    except (TypeError, ValueError):
        return default


try:
    import brotli  # type: ignore
except Exception:  # pragma: no cover
    brotli = None


# ============================================================================
# UTILITY FUNCTIONS
# ============================================================================

def retry_on_failure(max_attempts: int = 3, delay: float = 2.0):
    """Decorator to retry functions on failure with exponential backoff."""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            for attempt in range(max_attempts):
                try:
                    return func(*args, **kwargs)
                except Exception as exc:
                    if attempt == max_attempts - 1:
                        logger.error(f"{func.__name__} failed after {max_attempts} attempts: {exc}")
                        raise
                    wait_time = delay * (2 ** attempt)
                    logger.warning(
                        f"{func.__name__} attempt {attempt + 1} failed: {exc}. "
                        f"Retrying in {wait_time}s..."
                    )
                    time.sleep(wait_time)
            return None
        return wrapper
    return decorator


def safe_get(node: Any, *indices: int) -> Any:
    """Safely navigate nested list indexes; return None if any access fails."""
    current = node
    for index in indices:
        if not isinstance(current, (list, tuple)):
            return None
        if index is None or index < 0 or index >= len(current):
            return None
        current = current[index]
    return current


def slugify_label(text: str, default: str = "query") -> str:
    """Convert text to a filesystem-safe slug."""
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", (text or default).lower()).strip("-")
    if not slug:
        slug = default
    return slug[:48]


def looks_like_domain(value: str) -> bool:
    """Check if a string looks like a domain name."""
    if not value or " " in value:
        return False
    if value.count(".") == 0:
        return False
    if value.lower().startswith("http"):
        return True
    tld = value.rsplit(".", 1)[-1]
    return len(tld) in (2, 3, 4)


def resolve_external_url(href: str) -> Optional[str]:
    """Return destination of Google redirect URLs when possible."""
    if not href:
        return None
    href = unescape(href.strip())
    try:
        parsed = urlsplit(href)
    except Exception:
        return href
    if parsed.netloc.endswith("google.com") and parsed.path == "/url":
        params = parse_qs(parsed.query)
        target = params.get("q") or params.get("url")
        if target:
            return target[0]
    return href


def first_truthy(iterable):
    """Return the first truthy value from an iterable."""
    for item in iterable:
        if item:
            return item
    return None


def normalize_header_lookup(headers: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    """Return a case-insensitive mapping of header keys to values."""
    if not headers:
        return {}
    lookup = {}
    for key, value in headers.items():
        try:
            lookup[str(key).lower()] = value
        except Exception:
            continue
    return lookup


def process_response_body(
    body: Optional[str],
    is_base64: bool,
    headers: Optional[Dict[str, Any]],
) -> Tuple[Optional[str], Dict[str, Any]]:
    """Return decoded response text and metadata for logging."""
    meta: Dict[str, Any] = {
        "is_base64": bool(is_base64),
        "encoding": None,
        "size_bytes": 0,
        "decoded": False,
        "error": None,
        "base64": None,
    }

    if body is None:
        return None, meta

    raw_bytes: Optional[bytes]
    try:
        if is_base64:
            raw_bytes = base64.b64decode(body)
        elif isinstance(body, bytes):
            raw_bytes = body
        else:
            raw_bytes = str(body).encode("utf-8", errors="replace")
    except Exception as exc:
        meta["error"] = f"base64 decode failed: {exc}"
        return None, meta

    if raw_bytes is None:
        return None, meta

    headers_lookup = normalize_header_lookup(headers)
    encoding = headers_lookup.get("content-encoding")
    if encoding:
        meta["encoding"] = encoding
        encoding_l = str(encoding).lower()
        try:
            if "gzip" in encoding_l:
                raw_bytes = gzip.decompress(raw_bytes)
            elif "br" in encoding_l:
                if brotli is not None:
                    raw_bytes = brotli.decompress(raw_bytes)
                else:
                    meta["error"] = "brotli module not available"
            elif "deflate" in encoding_l:
                raw_bytes = zlib.decompress(raw_bytes)
        except Exception as exc:  # pragma: no cover - gzip edge cases
            meta["error"] = f"decompression failed: {exc}"

    if raw_bytes is None:
        return None, meta

    meta["size_bytes"] = len(raw_bytes)
    try:
        text = raw_bytes.decode("utf-8")
        meta["decoded"] = True
    except UnicodeDecodeError:
        text = raw_bytes.decode("utf-8", errors="replace")
        meta["decoded"] = False

    if raw_bytes:
        meta["base64"] = base64.b64encode(raw_bytes).decode("ascii")

    return text, meta


def normalize_zoom_value(zoom: Optional[Any], fallback: int = 15) -> str:
    """Convert zoom to a clean string representation with sensible fallback."""
    if zoom is None:
        return str(fallback)

    try:
        value = float(zoom)
    except (TypeError, ValueError):
        zoom_str = str(zoom).strip()
        return zoom_str or str(fallback)

    if not math.isfinite(value):
        return str(fallback)

    if value.is_integer():
        return str(int(value))

    return f"{value:.6g}"


def parse_coordinate_pair(value: str) -> Tuple[float, float]:
    """Parse "lat, lon" pairs from a single comma-separated string."""
    if not value:
        raise ValueError("Coordinate string is empty")

    parts = [part.strip() for part in value.split(",") if part and part.strip()]
    if len(parts) != 2:
        raise ValueError(
            "Coordinate string must contain exactly two comma-separated values"
        )

    try:
        lat = float(parts[0])
        lon = float(parts[1])
    except ValueError as exc:
        raise ValueError(f"Unable to parse coordinates '{value}': {exc}") from exc

    return lat, lon


def build_maps_search_url(query: str,
                          lat: Optional[float] = None,
                          lon: Optional[float] = None,
                          zoom: Optional[Any] = None) -> str:
    """Construct a Google Maps search URL with optional coordinates and zoom."""
    encoded = quote_plus(query)
    if lat is not None and lon is not None:
        zoom_str = normalize_zoom_value(zoom)
        return f"https://www.google.com/maps/search/{encoded}/@{lat},{lon},{zoom_str}z"
    return f"https://www.google.com/maps/search/{encoded}"


# ============================================================================
# APP STATE PARSING
# ============================================================================

def extract_app_state(page_source: str) -> Optional[Dict]:
    """Extract Google Maps APP_INITIALIZATION_STATE from page source."""
    match = re.search(
        r"window\.APP_INITIALIZATION_STATE=(.*?);window\.APP_FLAGS",
        page_source,
        re.DOTALL,
    )
    if not match:
        return None
    try:
        raw = match.group(1).replace("\n", "").replace("undefined", "null")
        return json.loads(raw)
    except Exception as exc:
        logger.debug(f"Failed to parse app state: {exc}")
        return None


def parse_results_from_app_state(page_source: str) -> Optional[List[Dict]]:
    """Parse structured search results from the embedded app state."""
    state = extract_app_state(page_source)
    if not state:
        return None

    blob = safe_get(state, 3, 2)
    if not isinstance(blob, str):
        return None

    try:
        search_data = json.loads(blob.replace(")]}'\n", ""))
    except Exception as exc:
        logger.debug(f"Failed to parse search data blob: {exc}")
        return None

    detailed_entries = safe_get(search_data, 64)
    if not detailed_entries:
        return None

    parsed = []
    for entry in detailed_entries:
        main = safe_get(entry, 1)
        if not isinstance(main, list):
            continue

        name = safe_get(main, 11) or safe_get(main, 12)
        if not name:
            continue

        cid = safe_get(main, 10)
        place_id = safe_get(main, 78)
        address_lines = safe_get(main, 2) or []
        full_address = (
            safe_get(main, 18)
            or safe_get(main, 39)
            or ", ".join(part for part in address_lines if part)
            or None
        )
        coords = safe_get(main, 9) or []
        lat = safe_get(coords, 2)
        lon = safe_get(coords, 3)
        rating = safe_get(main, 4, 7)
        reviews = safe_get(main, 4, 8)
        price_text = safe_get(main, 4, 2) or safe_get(main, 4, 10)
        website = safe_get(main, 7, 0)
        phone_info = safe_get(main, 178, 0)
        phone_local = safe_get(phone_info, 0) if phone_info else None
        phone_e164 = safe_get(phone_info, 3) if phone_info else None
        categories = safe_get(main, 13) or []
        plus_code = safe_get(main, 82, 0)
        gmaps_path = safe_get(main, 89)

        canonical_url = None
        if place_id:
            canonical_url = f"https://www.google.com/maps/place/?q=place_id:{place_id}"
        elif cid:
            canonical_url = f"https://www.google.com/maps?cid={cid}"
        elif gmaps_path:
            canonical_url = f"https://www.google.com/maps{gmaps_path}"

        result = {
            "name": name,
            "place_id": place_id or cid,
            "cid": cid,
            "maps_url": canonical_url,
            "url": canonical_url,
            "website": website,
            "phone": phone_local,
            "phone_e164": phone_e164,
            "address_lines": address_lines,
            "address": full_address,
            "latitude": lat,
            "longitude": lon,
            "rating": rating,
            "reviews": reviews,
            "price": price_text,
            "categories": categories,
            "plus_code": plus_code,
        }

        metadata = [part for part in address_lines if part]
        if price_text:
            metadata.append(price_text)
        result["metadata"] = metadata

        parsed.append(result)

    logger.info(f"Parsed {len(parsed)} results from app state")
    return parsed


# ============================================================================
# DOM PARSING (FALLBACK)
# ============================================================================

def parse_sidebar_cards(page_source: str, max_results: Optional[int] = None) -> List[Dict]:
    """Fallback: scrape visible sidebar cards for structured data."""
    soup = BeautifulSoup(page_source, "html.parser")
    feed = soup.find("div", {"role": "feed"})
    if not feed:
        logger.warning("No feed element found in page source")
        return []

    results = []
    seen_names = set()
    limit = max_results if max_results and max_results > 0 else None
    
    for card in feed.select("div.Nv2PK"):
        anchor = card.select_one("a.hfpxzc[href]")
        if not anchor:
            continue
        href = anchor["href"]
        if "https://www.google.com/maps/place" not in href:
            continue
        
        name = (anchor.get("aria-label") or anchor.get_text(strip=True) or "").strip()
        if not name or name in seen_names:
            continue
        
        # Extract rating and reviews
        rating_value = None
        review_count = None
        for node in card.find_all(attrs={"aria-label": True}):
            label = node.get("aria-label", "")
            if "star" in label.lower():
                rating_match = re.search(r"([0-5](?:\.\d)?)", label)
                if rating_match:
                    try:
                        rating_value = float(rating_match.group(1))
                    except ValueError:
                        pass
                reviews_match = re.search(r"([0-9,]+) review", label)
                if reviews_match:
                    try:
                        review_count = int(reviews_match.group(1).replace(",", ""))
                    except ValueError:
                        pass
                break

        # Extract IDs from URL
        place_id = None
        cid = None
        cid_match = re.search(r"!1s([^!]+)", href)
        if cid_match:
            cid = cid_match.group(1)
        pid_match = re.search(r"!19s([^!]+)", href)
        if pid_match:
            place_id = unquote(pid_match.group(1))
        
        canonical_url = href
        if place_id:
            canonical_url = f"https://www.google.com/maps/place/?q={place_id}"
        else:
            parts = urlsplit(href)
            canonical_url = urlunsplit((parts.scheme, parts.netloc, parts.path, "", ""))

        # Extract metadata
        metadata = []
        for span in card.find_all("span"):
            text = span.get_text(" ", strip=True)
            if text and text not in metadata:
                metadata.append(text)

        # Find website
        website = None
        for anchor_elem in card.find_all("a", href=True):
            resolved_href = resolve_external_url(anchor_elem["href"])
            if not resolved_href:
                continue
            if "google.com/maps" in resolved_href or resolved_href.startswith("/maps"):
                continue
            if resolved_href.startswith("http"):
                website = resolved_href
                break
        
        if not website:
            domain_candidate = first_truthy(
                looks_like_domain(text) and text for text in metadata
            )
            if domain_candidate:
                website = (
                    domain_candidate
                    if domain_candidate.lower().startswith("http")
                    else "https://" + domain_candidate
                )

        # Extract phone
        card_text = card.get_text(" ", strip=True)
        phone_match = PHONE_REGEX.search(card_text)
        phone = phone_match.group(0) if phone_match else None

        # Extract address
        address = first_truthy(
            text
            for text in metadata
            if "," in text and any(char.isdigit() for char in text)
        )

        # Extract category
        category = None
        for text in metadata:
            parts = [part.strip() for part in text.split("·") if part.strip()]
            if len(parts) >= 1 and not parts[0].isdigit():
                if parts[0] and parts[0] != address and len(parts[0].split()) <= 4:
                    category = parts[0]
                    break

        results.append({
            "name": name,
            "place_id": place_id or cid,
            "cid": cid,
            "maps_url": href,
            "url": canonical_url,
            "category": category,
            "address": address,
            "phone": phone,
            "website": website,
            "rating": rating_value,
            "reviews": review_count,
            "metadata": metadata[:8],
        })
        
        seen_names.add(name)
        if limit is not None and len(results) >= limit:
            break

    logger.info(f"Parsed {len(results)} results from DOM")
    return results


# ============================================================================
# RESULT MERGING
# ============================================================================

def merge_result_sets(primary: List[Dict], secondary: List[Dict]) -> List[Dict]:
    """Merge two result lists, preferring populated fields from primary."""
    def entry_key(entry):
        return (
            entry.get("place_id")
            or entry.get("cid")
            or (entry.get("name") or "").lower()
        )

    merged = {}
    order = []

    # Seed with secondary (DOM results)
    for item in secondary or []:
        key = entry_key(item)
        if not key:
            continue
        merged[key] = dict(item)
        order.append(key)

    # Overlay primary (app-state results) for richer data
    for item in primary or []:
        key = entry_key(item)
        if not key:
            continue
        base = merged.get(key, {})
        combined = dict(base)
        for field, value in item.items():
            if value is None:
                continue
            if not combined.get(field):
                combined[field] = value
            else:
                combined[field] = value
        if key not in merged:
            order.append(key)
        merged[key] = combined

    # Preserve primary ordering first, then any remaining secondary items
    output = []
    seen = set()
    for source in (primary or []):
        key = entry_key(source)
        if key and key in merged and key not in seen:
            output.append(merged[key])
            seen.add(key)
    for key in order:
        if key in merged and key not in seen:
            output.append(merged[key])
            seen.add(key)
    
    logger.info(f"Merged to {len(output)} unique results")
    return output


def parse_maps_feed(page_source: str, max_results: Optional[int] = None) -> List[Dict]:
    """Parse Maps results using app state data merged with DOM fallback."""
    app_state_results = None
    try:
        app_state_results = parse_results_from_app_state(page_source)
    except Exception as exc:
        logger.warning(f"APP state parsing failed: {exc}")

    dom_results = parse_sidebar_cards(page_source, max_results=None)
    merged = merge_result_sets(app_state_results or [], dom_results or [])

    if max_results and max_results > 0:
        return merged[:max_results]
    return merged


# ============================================================================
# BROWSER CONTROL
# ============================================================================

@retry_on_failure(max_attempts=3, delay=2.0)
def ensure_sidebar_feed(sb, timeout: int = 12) -> bool:
    """Ensure the Maps sidebar feed exists, recovering from detail views if needed."""
    feed_selector = 'div[role="feed"]'
    try:
        sb.wait_for_element_present(feed_selector, timeout=timeout)
        logger.info("Sidebar feed detected")
        return True
    except Exception:
        logger.debug("Feed selector not found, checking for back button")

    back_selectors = [
        'button[aria-label*="Back to results"]',
        'button[aria-label="Back to search results"]',
        'button[jsaction*="pane.backToList"]',
    ]
    
    for selector in back_selectors:
        if sb.is_element_present(selector):
            try:
                logger.info(f"Clicking back button: {selector}")
                sb.click(selector)
                sb.sleep(1.0)
                sb.wait_for_element_present(feed_selector, timeout=timeout)
                logger.info("Sidebar feed recovered")
                return True
            except Exception as exc:
                logger.debug(f"Back button {selector} failed: {exc}")
                continue

    is_present = sb.is_element_present(feed_selector)
    if not is_present:
        logger.warning("Sidebar feed could not be established")
    return is_present


def scroll_sidebar(sb, max_scrolls: int = 30, wait: float = 1.0, settle_rounds: int = 3):
    """Scroll the Google Maps sidebar until results stop increasing."""
    if not ensure_sidebar_feed(sb, timeout=10):
        logger.warning("Sidebar feed not available; skipping scroll")
        return
    
    last_count = 0
    stagnant = 0
    
    for scroll_num in range(max_scrolls):
        try:
            current_count = sb.execute_script(
                "return document.querySelectorAll('div.Nv2PK').length;"
            ) or 0
        except Exception:
            current_count = 0
        
        if current_count > last_count:
            logger.debug(f"Scroll {scroll_num + 1}: {current_count} items (+{current_count - last_count})")
            last_count = current_count
            stagnant = 0
        else:
            stagnant += 1
            if stagnant >= settle_rounds:
                logger.info(f"Results stabilized at {last_count} items after {scroll_num + 1} scrolls")
                break
        
        sb.execute_script(
            """
            var el = document.querySelector('div[role="feed"]');
            if (el) { el.scrollTop = el.scrollHeight; }
            """
        )
        sb.sleep(wait)
    
    logger.info(f"Sidebar scroll complete: {last_count} total items visible")


def run_secondary_query(sb, query: str, lat: Optional[float] = None,
                       lon: Optional[float] = None, zoom: Optional[Any] = None,
                       wait_after: float = 4.5):
    """Reload Google Maps directly with the follow-up query URL."""
    new_url = build_maps_search_url(query, lat=lat, lon=lon, zoom=zoom)
    logger.info(f"Loading follow-up query via URL: {new_url}")
    sb.cdp.open(new_url)
    sb.sleep(wait_after)
    ensure_sidebar_feed(sb, timeout=14)


def configure_network_blocking(page, loop, patterns: Optional[List[str]] = None) -> None:
    """Block heavy network resources via Chrome DevTools for faster loading."""
    if not patterns:
        return
    if loop is None or not hasattr(page, "send"):
        logger.debug("CDP loop unavailable; skipping network blocking.")
        return

    async def runner():
        await page.send(mycdp.network.enable())
        await page.send(mycdp.network.set_blocked_ur_ls(patterns))

    try:
        loop.run_until_complete(runner())
        logger.info(f"Blocking {len(patterns)} heavy resource pattern(s)")
    except Exception as exc:  # pragma: no cover - best-effort safeguard
        logger.debug(f"Unable to configure network blocking: {exc}")


# ============================================================================
# XHR MONITORING
# ============================================================================

def listen_for_xhr(page, requests: List, last_seen: Dict):
    """Set up listener for XHR-like network activity."""
    watched_types = {mycdp.network.ResourceType.XHR}
    # Capture fetch events as well, since Google Maps frequently uses Fetch API
    fetch_type = getattr(mycdp.network.ResourceType, "FETCH", None)
    if fetch_type:
        watched_types.add(fetch_type)
    # Some responses surface as "OTHER"; include them as a safety net
    other_type = getattr(mycdp.network.ResourceType, "OTHER", None)
    if other_type:
        watched_types.add(other_type)

    async def handler(event):
        if event.type_ not in watched_types:
            return
        response = event.response
        if not response:
            return
        url = getattr(response, "url", "")
        if not url:
            return
        parsed = urlsplit(url)
        host = parsed.netloc.lower()
        if not (host == "google.com" or host.endswith(".google.com")):
            return
        if parsed.path != "/search":
            return
        query = parsed.query or ""
        if "tbm=map" not in query:
            return
        requests.append({
            "url": url,
            "request_id": event.request_id,
            "status": response.status,
            "headers": dict(response.headers or {}),
            "resource_type": getattr(event.type_, "value", str(event.type_)),
        })
        last_seen["ts"] = time.time()

    page.add_handler(mycdp.network.ResponseReceived, handler)
    try:
        loop = getattr(page, "loop", None)
        if loop and hasattr(page, "send"):
            loop.create_task(page.send(mycdp.network.enable()))
    except Exception as exc:  # pragma: no cover - best-effort
        logger.debug(f"Unable to prime network events: {exc}")
    logger.debug("XHR listener registered")


async def receive_xhr(page, requests: List, last_seen: Dict, 
                     idle_wait: float = 2.0, max_retries: int = 5) -> List[Dict]:
    """Collect XHR response bodies."""
    retries = 0
    while True:
        last = last_seen["ts"]
        if last is None or retries > max_retries:
            break
        if time.time() - last <= idle_wait:
            retries += 1
            time.sleep(idle_wait)
            continue
        break

    await page
    responses = []
    for request in requests:
        request_id = request["request_id"]
        try:
            response_body = await page.send(mycdp.network.get_response_body(request_id))
        except Exception as exc:
            responses.append({**request, "error": str(exc)})
            continue
        
        if not response_body:
            continue
        
        body, is_base64 = response_body
        entry = {**request, "is_base64": bool(is_base64)}
        decoded_body, meta = process_response_body(body, bool(is_base64), request.get("headers"))
        entry["body"] = decoded_body
        entry["body_meta"] = meta
        responses.append(entry)
    
    logger.info(f"Collected {len(responses)} XHR responses")
    return responses


# ============================================================================
# SNAPSHOT CREATION
# ============================================================================

def capture_query_snapshot(
    sb,
    query_label: str,
    index: int,
    log_dir: str,
    max_results: Optional[int] = None,
    *,
    save_page_source: bool = True,
    save_screenshot: bool = True,
) -> Dict:
    """Capture page state and parse results for a single query."""
    slug = slugify_label(query_label or f"query-{index}")
    slug_with_index = f"{index:02d}-{slug}"
    
    page_source = sb.get_page_source()
    page_source_path: Optional[str] = None
    if save_page_source:
        page_source_path = os.path.join(log_dir, f"page_source_{slug_with_index}.html")
        with open(page_source_path, "w", encoding="utf-8") as f:
            f.write(page_source)
        logger.debug(f"Saved page source: {page_source_path}")
    else:
        logger.debug("Page source capture disabled for this snapshot")
    
    screenshot_path: Optional[str] = None
    if save_screenshot:
        screenshot_path = os.path.join(log_dir, f"screenshot_{slug_with_index}.png")
        sb.save_screenshot(screenshot_path)
        logger.debug(f"Saved screenshot: {screenshot_path}")
    else:
        logger.debug("Screenshot capture disabled for this snapshot")
    
    # Parse results
    parsed_results = parse_maps_feed(page_source, max_results=max_results)
    
    snapshot = {
        "query": query_label,
        "index": index,
        "slug": slug_with_index,
        "page_source": page_source_path,
        "screenshot": screenshot_path,
        "parsed_results": parsed_results,
        "parsed_count": len(parsed_results),
    }
    
    logger.info(f"Captured snapshot for '{query_label}': {len(parsed_results)} results")
    return snapshot


def print_query_summary(snapshot: Dict):
    """Log summary of query results."""
    parsed = snapshot.get("parsed_results", []) or []
    top_names = [entry.get("name") for entry in parsed if entry.get("name")]
    count = len(parsed)
    
    if top_names:
        preview = ", ".join(top_names[:5])
        logger.info(f"📊 {count} results for \"{snapshot['query']}\": {preview}...")
    else:
        logger.warning(f"❌ No results for \"{snapshot['query']}\"")


# ============================================================================
# SUPABASE INTEGRATION
# ============================================================================

def _resolve_supabase_endpoint(
    supabase_url: str, table_identifier: str
) -> Tuple[str, Optional[str]]:
    """Return the REST endpoint and optional schema from a table identifier."""
    if not table_identifier:
        raise ValueError("Supabase table identifier cannot be empty.")

    schema = None
    table_name = table_identifier
    if "." in table_identifier:
        potential_schema, remainder = table_identifier.split(".", 1)
        if potential_schema and remainder:
            schema, table_name = potential_schema, remainder

    endpoint = supabase_url.rstrip("/") + f"/rest/v1/{table_name}"
    return endpoint, schema


def _supabase_headers(
    supabase_key: str,
    schema: Optional[str],
    *,
    prefer_minimal: bool = False,
    read: bool = False,
) -> Dict[str, str]:
    """Build standard Supabase REST headers with optional profile targeting."""
    headers: Dict[str, str] = {
        "apikey": supabase_key,
        "Authorization": f"Bearer {supabase_key}",
        "Content-Type": "application/json",
    }
    if prefer_minimal:
        headers["Prefer"] = "return=minimal"
    if schema:
        headers["Accept-Profile" if read else "Content-Profile"] = schema
    return headers


def _detect_supabase_columns(endpoint: str, headers: Dict, column_names: List[str]) -> set:
    """Return the subset of columns that exist on the target table."""
    available = set()
    for column in column_names:
        try:
            check = requests.get(
                endpoint,
                params={"select": column, "limit": 0},
                headers=headers,
                timeout=15,
            )
        except Exception as exc:
            logger.debug(f"Column check failed for {column}: {exc}")
            continue
        if check.status_code < 400:
            available.add(column)
    
    logger.debug(f"Available Supabase columns: {available}")
    return available


def upload_results_to_supabase(results: Dict, supabase_url: str, 
                               supabase_key: str, supabase_table: str) -> Optional[Dict]:
    """Store the full run payload in a Supabase table via the REST API."""
    if not supabase_url or not supabase_key or not supabase_table:
        logger.info("Supabase configuration incomplete; skipping table upload")
        return None

    try:
        endpoint, profile_schema = _resolve_supabase_endpoint(supabase_url, supabase_table)
    except ValueError as exc:
        logger.error(str(exc))
        return {
            "status": "error",
            "code": None,
            "details": str(exc),
            "table": supabase_table,
        }

    run_id = results.get("run_id") or uuid4().hex
    results["run_id"] = run_id

    logger.info(f"📤 Uploading run {run_id} to Supabase table '{supabase_table}'")

    write_headers = _supabase_headers(
        supabase_key, profile_schema, prefer_minimal=True, read=False
    )
    read_headers = _supabase_headers(supabase_key, profile_schema, read=True)

    candidate_columns = [
        "run_id",
        "primary_query",
        "timestamp",
        "run_timestamp",
        "payload",
        "data",
    ]
    existing_columns = _detect_supabase_columns(endpoint, read_headers, candidate_columns)

    record = {}
    if "run_id" in existing_columns:
        record["run_id"] = run_id
    if "primary_query" in existing_columns:
        record["primary_query"] = results.get("primary_query")
    timestamp_value = results.get("timestamp")
    if "timestamp" in existing_columns and timestamp_value:
        record["timestamp"] = timestamp_value
    elif "run_timestamp" in existing_columns:
        record["run_timestamp"] = timestamp_value or datetime.utcnow().isoformat() + "Z"
    
    payload_column = "payload" if "payload" in existing_columns else None
    if not payload_column and "data" in existing_columns:
        payload_column = "data"
    if payload_column:
        record[payload_column] = results

    if not record:
        logger.error("No matching columns discovered on Supabase table")
        return {
            "status": "error",
            "code": None,
            "details": "No matching columns for record.",
            "table": supabase_table,
        }

    try:
        response = requests.post(
            endpoint,
            json=[record],
            headers=write_headers,
            timeout=30,
        )
    except Exception as exc:
        logger.error(f"Supabase upload failed: {exc}")
        return {"status": "error", "error": str(exc), "table": supabase_table}

    if response.status_code >= 400:
        logger.error(f"Supabase returned {response.status_code}: {response.text[:200]}")
        return {
            "status": "error",
            "code": response.status_code,
            "details": response.text,
            "table": supabase_table,
        }

    # Verify upload
    verify_status = None
    
    try:
        verify = requests.get(
            endpoint,
            params={"select": "run_id", "run_id": f"eq.{run_id}"},
            headers=read_headers,
            timeout=30,
        )
        if verify.status_code < 400:
            data = verify.json()
            matched = any(item.get("run_id") == run_id for item in data or [])
            if matched:
                verify_status = "confirmed"
                logger.info(f"✅ Supabase confirmed run {run_id}")
            else:
                verify_status = "unknown"
                logger.warning(f"⚠️ Supabase verification unclear for run {run_id}")
        else:
            logger.warning(f"Supabase verification failed: {verify.status_code}")
            verify_status = "verify_failed"
    except Exception as exc:
        logger.warning(f"Supabase verification error: {exc}")
        verify_status = "verify_error"

    logger.info(f"✅ Supabase upload succeeded (status {response.status_code})")
    return {
        "status": "uploaded",
        "code": response.status_code,
        "verify": verify_status,
        "table": supabase_table,
    }


STAGING_ENTRY_FIELDS = {
    "name",
    "place_id",
    "cid",
    "maps_url",
    "url",
    "website",
    "phone",
    "phone_e164",
    "address",
    "address_lines",
    "latitude",
    "longitude",
    "rating",
    "reviews",
    "price",
    "category",
    "categories",
    "plus_code",
    "metadata",
}

JSON_FIELDS = {"address_lines", "categories", "metadata", "raw_entry"}
FLOAT_FIELDS = {"lat", "lon", "latitude", "longitude", "rating", "zoom"}
INT_FIELDS = {"query_index", "result_index", "reviews"}
MAIN_JSON_COLUMNS = JSON_FIELDS | {"payload"}
ALLOWED_STAGING_COLUMNS = {
    "run_id",
    "primary_query",
    "query",
    "query_index",
    "result_index",
    "timestamp",
    "snapshot_slug",
    "target_url",
    "resolved_url",
    "lat",
    "lon",
    "zoom",
    "name",
    "place_id",
    "cid",
    "maps_url",
    "url",
    "website",
    "phone",
    "phone_e164",
    "address",
    "address_lines",
    "latitude",
    "longitude",
    "rating",
    "reviews",
    "price",
    "category",
    "categories",
    "plus_code",
    "metadata",
    "raw_entry",
}

STAGING_COLUMN_SEQUENCE = [
    "run_id",
    "primary_query",
    "query",
    "query_index",
    "result_index",
    "timestamp",
    "snapshot_slug",
    "target_url",
    "resolved_url",
    "lat",
    "lon",
    "zoom",
    "name",
    "place_id",
    "cid",
    "maps_url",
    "url",
    "website",
    "phone",
    "phone_e164",
    "address",
    "address_lines",
    "latitude",
    "longitude",
    "rating",
    "reviews",
    "price",
    "category",
    "categories",
    "plus_code",
    "metadata",
    "raw_entry",
]


def _coerce_float(value: Any) -> Optional[float]:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        stripped = value.strip()
        if not stripped:
            return None
        try:
            return float(stripped)
        except ValueError:
            return None
    return None


def _coerce_int(value: Any) -> Optional[int]:
    if value is None:
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        stripped = value.strip()
        if not stripped:
            return None
        try:
            return int(float(stripped))
        except ValueError:
            return None
    return None


def _parse_iso_timestamp(value: Any) -> Optional[datetime]:
    """Convert ISO8601 strings (or datetime) into timezone-aware datetime."""
    if value is None:
        return None
    if isinstance(value, datetime):
        if value.tzinfo is None:
            return value.replace(tzinfo=timezone.utc)
        return value.astimezone(timezone.utc)
    if isinstance(value, str):
        stripped = value.strip()
        if not stripped:
            return None
        if stripped.endswith("Z"):
            stripped = stripped[:-1] + "+00:00"
        try:
            parsed = datetime.fromisoformat(stripped)
        except ValueError:
            return None
        if parsed.tzinfo is None:
            return parsed.replace(tzinfo=timezone.utc)
        return parsed.astimezone(timezone.utc)
    return None


def sanitize_staging_value(key: str, value: Any) -> Any:
    """Prepare values for Supabase ingestion."""
    if key in FLOAT_FIELDS:
        return _coerce_float(value)
    if key in INT_FIELDS:
        return _coerce_int(value)
    if isinstance(value, str):
        stripped = value.strip()
        return stripped if stripped else None
    if isinstance(value, datetime):
        return value.isoformat()
    if isinstance(value, (list, dict)):
        return value
    if isinstance(value, (int, float, bool)) or value is None:
        return value
    return str(value)


def flatten_results_for_staging(results: Dict) -> List[Dict]:
    """Flatten parsed query results into row-per-profile records."""
    snapshots = results.get("query_snapshots") or []
    flattened: List[Dict] = []

    base_timestamp = results.get("timestamp")
    base_lat = sanitize_staging_value("lat", results.get("lat"))
    base_lon = sanitize_staging_value("lon", results.get("lon"))
    base_zoom = sanitize_staging_value("zoom", results.get("zoom"))

    for snapshot in snapshots:
        parsed_results = snapshot.get("parsed_results") or []
        query_label = snapshot.get("query")
        query_index = _coerce_int(snapshot.get("index"))
        snapshot_slug = snapshot.get("slug")

        for result_index, entry in enumerate(parsed_results, start=1):
            row = {
                "run_id": results.get("run_id"),
                "primary_query": results.get("primary_query"),
                "query": query_label,
                "query_index": query_index,
                "result_index": result_index,
                "timestamp": base_timestamp,
                "snapshot_slug": snapshot_slug,
                "target_url": results.get("target_url"),
                "resolved_url": results.get("resolved_url"),
                "lat": base_lat,
                "lon": base_lon,
                "zoom": base_zoom,
            }

            if isinstance(entry, dict):
                for key in STAGING_ENTRY_FIELDS:
                    if key in entry:
                        row[key] = sanitize_staging_value(key, entry.get(key))
                row["raw_entry"] = entry
            else:
                row["raw_entry"] = entry

            # Ensure JSON fields are serialisable
            for key in JSON_FIELDS:
                if key in row and row[key] is not None:
                    if not isinstance(row[key], (list, dict)):
                        row[key] = [row[key]]

            # Final type coercion for numeric fields
            for key in FLOAT_FIELDS:
                if key in row:
                    row[key] = _coerce_float(row[key])
            for key in INT_FIELDS:
                if key in row:
                    row[key] = _coerce_int(row[key])

            flattened.append(row)

    return flattened


def export_results_to_csv(results: Dict, output_path: str) -> Optional[str]:
    """Write flattened results to CSV for artifact downloads."""
    rows = flatten_results_for_staging(results)
    try:
        with open(output_path, "w", newline="", encoding="utf-8") as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=STAGING_COLUMN_SEQUENCE)
            writer.writeheader()
            for row in rows:
                serialisable = {}
                for column in STAGING_COLUMN_SEQUENCE:
                    value = row.get(column)
                    if isinstance(value, (dict, list)):
                        serialisable[column] = json.dumps(value, ensure_ascii=False)
                    else:
                        serialisable[column] = value
                writer.writerow(serialisable)
        return output_path
    except Exception as exc:
        logger.warning(f"Unable to export CSV results: {exc}")
        return None


def upload_profiles_to_supabase_staging(
    results: Dict,
    supabase_url: str,
    supabase_key: str,
    staging_table: str,
    chunk_size: int = 200,
) -> Optional[Dict]:
    """Upload flattened profile rows to a Supabase staging table."""
    if not supabase_url or not supabase_key or not staging_table:
        logger.info("Supabase staging configuration incomplete; skipping staging upload")
        return None

    rows = flatten_results_for_staging(results)
    total_rows = len(rows)
    if total_rows == 0:
        logger.warning("No parsed results available for Supabase staging upload")
        return {"status": "skipped", "reason": "no_rows"}

    normalized_rows: List[Dict[str, Any]] = []
    for row in rows:
        normalized = {}
        for key in ALLOWED_STAGING_COLUMNS:
            normalized[key] = row.get(key)
        normalized_rows.append(normalized)

    try:
        endpoint, profile_schema = _resolve_supabase_endpoint(supabase_url, staging_table)
    except ValueError as exc:
        logger.error(str(exc))
        return {"status": "error", "error": str(exc), "table": staging_table}

    write_headers = _supabase_headers(
        supabase_key, profile_schema, prefer_minimal=True, read=False
    )

    run_id = results.get("run_id")
    delete_status = None
    if run_id:
        try:
            delete_resp = requests.delete(
                endpoint,
                params={"run_id": f"eq.{run_id}"},
                headers=write_headers,
                timeout=30,
            )
            delete_status = delete_resp.status_code
            if delete_resp.status_code >= 400:
                logger.error(
                    f"Supabase staging delete failed ({delete_resp.status_code}): "
                    f"{delete_resp.text[:200]}"
                )
        except Exception as exc:
            logger.error(f"Supabase staging delete error: {exc}")

    inserted = 0
    errors: List[Dict[str, Any]] = []

    for index in range(0, total_rows, chunk_size):
        chunk = normalized_rows[index:index + chunk_size]
        try:
            response = requests.post(
                endpoint,
                json=chunk,
                headers=write_headers,
                timeout=60,
            )
        except Exception as exc:
            logger.error(f"Supabase staging upload failed: {exc}")
            errors.append({"offset": index, "size": len(chunk), "error": str(exc)})
            continue

        if response.status_code >= 400:
            logger.error(
                f"Supabase staging returned {response.status_code}: "
                f"{response.text[:200]}"
            )
            errors.append({
                "offset": index,
                "size": len(chunk),
                "code": response.status_code,
                "details": response.text,
            })
            continue

        inserted += len(chunk)

    if inserted:
        logger.info(
            f"✅ Supabase staging upload complete: {inserted}/{total_rows} rows "
            f"({staging_table})"
        )
    else:
        logger.warning("Supabase staging upload inserted 0 rows")

    status = {
        "status": "ok" if inserted == total_rows and not errors else "partial",
        "table": staging_table,
        "rows_total": total_rows,
        "rows_inserted": inserted,
    }
    if delete_status is not None:
        status["delete_status"] = delete_status
    if errors:
        status["errors"] = errors[:5]

    return status


def _psycopg_available() -> bool:
    return sql is not None and Json is not None and (psycopg is not None or psycopg2 is not None)  # type: ignore[arg-type]


def _get_db_connection(db_url: str):
    if psycopg is not None:  # type: ignore[attr-defined]
        return psycopg.connect(db_url)  # type: ignore[call-arg]
    if psycopg2 is not None:  # type: ignore[attr-defined]
        return psycopg2.connect(db_url)  # type: ignore[call-arg]
    raise RuntimeError("psycopg driver not installed")


def _sql_identifier(table_name: str):
    if sql is None:
        raise RuntimeError("SQL composition helper unavailable")
    parts = [part.strip() for part in table_name.split(".") if part.strip()]
    if not parts:
        raise ValueError("Invalid table identifier")
    return sql.Identifier(*parts)


def _prepare_staging_rows(rows: List[Dict[str, Any]]) -> List[List[Any]]:
    prepared: List[List[Any]] = []
    for row in rows:
        prepared_row: List[Any] = []
        for column in STAGING_COLUMN_SEQUENCE:
            value = row.get(column)
            if column == "timestamp":
                value = _parse_iso_timestamp(value)
            elif column in JSON_FIELDS and value is not None:
                value = Json(value)
            prepared_row.append(value)
        prepared.append(prepared_row)
    return prepared


def _build_staging_insert_sql(table_name: str):
    if sql is None:
        raise RuntimeError("SQL composition helper unavailable")
    return sql.SQL(
        "INSERT INTO {table} ({columns}) VALUES ({values})"
    ).format(
        table=_sql_identifier(table_name),
        columns=sql.SQL(", ").join(sql.Identifier(col) for col in STAGING_COLUMN_SEQUENCE),
        values=sql.SQL(", ").join(sql.Placeholder() for _ in STAGING_COLUMN_SEQUENCE),
    )


def _build_upsert_clause(columns: List[str]):
    if sql is None:
        raise RuntimeError("SQL composition helper unavailable")
    assignments = []
    for column in columns:
        if column in {"id", "run_id", "first_seen_at"}:
            continue
        if column == "last_seen_at":
            assignments.append(
                sql.SQL("{col} = NOW()").format(col=sql.Identifier(column))
            )
        else:
            assignments.append(
                sql.SQL("{col} = EXCLUDED.{col}").format(col=sql.Identifier(column))
            )
    if not assignments:
        assignments.append(sql.SQL("last_seen_at = NOW()"))
    return sql.SQL(", ").join(assignments)


def _build_main_upsert(table_name: str, record: Dict[str, Any]):
    if sql is None:
        raise RuntimeError("SQL composition helper unavailable")
    columns = list(record.keys())
    values: List[Any] = []
    for column in columns:
        value = record[column]
        if column in MAIN_JSON_COLUMNS and value is not None:
            value = Json(value)
        values.append(value)

    query = sql.SQL(
        "INSERT INTO {table} ({columns}) VALUES ({values}) "
        "ON CONFLICT (run_id) DO UPDATE SET {updates}"
    ).format(
        table=_sql_identifier(table_name),
        columns=sql.SQL(", ").join(sql.Identifier(col) for col in columns),
        values=sql.SQL(", ").join(sql.Placeholder() for _ in columns),
        updates=_build_upsert_clause(columns),
    )
    return query, values


def _build_local_main_record(results: Dict[str, Any], staging_rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    run_id = results.get("run_id")
    if not run_id:
        return {}

    snapshots = results.get("query_snapshots") or []
    top_entry = staging_rows[0] if staging_rows else {}

    run_timestamp = _parse_iso_timestamp(results.get("timestamp")) or datetime.now(timezone.utc)

    metadata: Dict[str, Any] = {
        "total_results": len(staging_rows),
        "query_count": len(snapshots),
    }
    artifacts = results.get("artifacts") or {}
    if artifacts:
        metadata["artifacts"] = sorted(artifacts.keys())
    coordinates = results.get("coordinates")
    if coordinates:
        metadata["coordinates"] = coordinates

    record: Dict[str, Any] = {
        "cid": top_entry.get("cid"),
        "run_id": run_id,
        "run_timestamp": run_timestamp,
        "primary_query": results.get("primary_query"),
        "query": results.get("query") or results.get("primary_query"),
        "query_index": _coerce_int(top_entry.get("query_index")),
        "result_index": _coerce_int(top_entry.get("result_index")),
        "snapshot_slug": top_entry.get("snapshot_slug"),
        "target_url": results.get("target_url"),
        "resolved_url": results.get("resolved_url"),
        "lat": _coerce_float(results.get("lat")),
        "lon": _coerce_float(results.get("lon")),
        "zoom": _coerce_float(results.get("zoom")),
        "name": top_entry.get("name"),
        "place_id": top_entry.get("place_id"),
        "maps_url": top_entry.get("maps_url"),
        "url": top_entry.get("url"),
        "website": top_entry.get("website"),
        "phone": top_entry.get("phone"),
        "phone_e164": top_entry.get("phone_e164"),
        "address": top_entry.get("address"),
        "address_lines": top_entry.get("address_lines"),
        "latitude": _coerce_float(top_entry.get("latitude")),
        "longitude": _coerce_float(top_entry.get("longitude")),
        "rating": _coerce_float(top_entry.get("rating")),
        "reviews": _coerce_int(top_entry.get("reviews")),
        "price": top_entry.get("price"),
        "category": top_entry.get("category"),
        "categories": top_entry.get("categories"),
        "plus_code": top_entry.get("plus_code"),
        "metadata": metadata,
        "raw_entry": top_entry.get("raw_entry"),
        "first_seen_at": run_timestamp,
        "last_seen_at": datetime.now(timezone.utc),
        "payload": results,
    }
    return record


def persist_results_to_local_db(
    results: Dict[str, Any],
    db_url: str,
    main_table: Optional[str],
    staging_table: Optional[str],
    chunk_size: int = 500,
) -> Optional[Dict[str, Any]]:
    """Persist scraper results into a local Postgres database."""
    if not db_url:
        logger.info("Local database URL not provided; skipping local persistence")
        return None
    if not _psycopg_available():
        logger.warning("psycopg driver not installed; skipping local database persistence")
        return {
            "status": "error",
            "error": "psycopg driver not installed",
            "run_id": results.get("run_id"),
        }

    chunk_size = max(1, int(chunk_size or 500))
    run_id = results.get("run_id")
    staging_rows = flatten_results_for_staging(results)

    status: Dict[str, Any] = {"run_id": run_id}
    inserted_staging = 0
    deleted_staging = 0

    try:
        conn = _get_db_connection(db_url)
    except Exception as exc:
        logger.error(f"❌ Failed to connect to local database: {exc}")
        status.update({"status": "error", "error": str(exc)})
        return status

    try:
        if psycopg2 is not None and psycopg is None:  # type: ignore[attr-defined]
            conn.autocommit = False  # type: ignore[assignment]

        with conn.cursor() as cur:
            if staging_table and staging_table.strip():
                if staging_rows:
                    logger.info(
                        "📝 Inserting %d rows into local staging table '%s'",
                        len(staging_rows),
                        staging_table,
                    )
                    if run_id:
                        delete_sql = sql.SQL("DELETE FROM {table} WHERE run_id = %s").format(  # type: ignore[arg-type]
                            table=_sql_identifier(staging_table)
                        )
                        cur.execute(delete_sql, (run_id,))
                        deleted_staging = cur.rowcount or 0

                    insert_sql = _build_staging_insert_sql(staging_table)
                    prepared_rows = _prepare_staging_rows(staging_rows)

                    for offset in range(0, len(prepared_rows), chunk_size):
                        chunk = prepared_rows[offset:offset + chunk_size]
                        cur.executemany(insert_sql, chunk)
                        inserted_staging += len(chunk)
                else:
                    logger.info("Local staging table configured but no rows to insert")

            if main_table and main_table.strip():
                record = _build_local_main_record(results, staging_rows)
                if record:
                    logger.info(
                        "🧾 Upserting scrape run %s into local table '%s'",
                        run_id,
                        main_table,
                    )
                    insert_sql, values = _build_main_upsert(main_table, record)
                    cur.execute(insert_sql, values)
                    status["main_rows"] = cur.rowcount
                else:
                    logger.debug("Local run payload missing required fields; skipping main table insert")

        conn.commit()
    except Exception as exc:
        conn.rollback()
        logger.error(f"❌ Local database persistence failed: {exc}")
        status.update({"status": "error", "error": str(exc)})
        return status
    finally:
        conn.close()

    status["status"] = "ok"
    if staging_table and staging_table.strip():
        status["staging_table"] = staging_table
        status["staging_rows"] = inserted_staging
        status["staging_deleted"] = deleted_staging
    if main_table and main_table.strip():
        status["main_table"] = main_table
    return status


def upload_artifacts_to_supabase_storage(
    artifacts: Dict,
    supabase_url: str,
    supabase_key: str,
    supabase_bucket: str,
    run_id: str,
    local_copy_root: Optional[str] = None,
) -> Optional[Dict]:
    """Upload run artifacts to Supabase Storage for long-term retention."""
    if not all([supabase_url, supabase_key, supabase_bucket, run_id, artifacts]):
        logger.info("Supabase storage configuration incomplete; skipping artifact upload")
        return None

    bucket = supabase_bucket.strip().strip("/")
    if not bucket:
        return None

    base_endpoint = supabase_url.rstrip("/") + f"/storage/v1/object/{bucket}"
    manifest = []

    logger.info(f"📦 Uploading artifacts to bucket '{bucket}'")

    local_copy_root = (local_copy_root or "").strip()
    local_copy_root = os.path.abspath(local_copy_root) if local_copy_root else ""
    local_copy_run_dir = None
    if local_copy_root:
        try:
            local_copy_run_dir = os.path.join(local_copy_root, run_id)
            os.makedirs(local_copy_run_dir, exist_ok=True)
            logger.debug(f"Mirroring artifacts locally under: {local_copy_run_dir}")
        except Exception as exc:
            logger.warning(f"Unable to create local artifact mirror '{local_copy_root}': {exc}")
            local_copy_run_dir = None

    for label, path in artifacts.items():
        if not path or not os.path.exists(path):
            logger.warning(f"Artifact not found: {label} -> {path}")
            continue

        object_name = f"{run_id}/{os.path.basename(path)}"
        object_path = quote(object_name, safe="/")
        upload_url = f"{base_endpoint}/{object_path}"

        guessed_type, _ = mimetypes.guess_type(path)
        content_type = guessed_type or "application/octet-stream"

        headers = {
            "apikey": supabase_key,
            "Authorization": f"Bearer {supabase_key}",
            "Content-Type": content_type,
            "x-upsert": "true",
        }

        record = {
            "label": label,
            "filename": os.path.basename(path),
            "object": object_name,
        }

        try:
            with open(path, "rb") as artifact_file:
                response = requests.post(
                    upload_url,
                    data=artifact_file,
                    headers=headers,
                    timeout=60,
                )
        except Exception as exc:
            logger.error(f"Failed to upload {label}: {exc}")
            record.update({"status": "error", "error": str(exc)})
            manifest.append(record)
            continue

        if response.status_code >= 400:
            logger.error(f"Upload failed for {label}: {response.status_code}")
            record.update({
                "status": "error",
                "code": response.status_code,
                "details": response.text,
            })
        else:
            public_path = (
                supabase_url.rstrip("/")
                + f"/storage/v1/object/public/{bucket}/{object_path}"
            )
            record.update({
                "status": "uploaded",
                "code": response.status_code,
                "public_url": public_path,
            })
            logger.info(f"✅ Uploaded '{label}' to {object_name}")

        manifest.append(record)

        if local_copy_run_dir:
            try:
                destination = os.path.join(local_copy_run_dir, os.path.basename(path))
                shutil.copy2(path, destination)
                record["local_copy"] = destination
            except Exception as exc:
                logger.warning(f"Unable to mirror artifact '{label}' locally: {exc}")

    if not manifest:
        return None

    uploaded_count = sum(1 for item in manifest if item.get("status") == "uploaded")
    logger.info(f"✅ Uploaded {uploaded_count}/{len(manifest)} artifacts")

    return {"bucket": bucket, "items": manifest}


# ============================================================================
# QUERY PROCESSING
# ============================================================================

def normalize_query_inputs(queries_str: str, fallback_query: str = "") -> tuple:
    """Return the primary query and an ordered list of follow-up queries."""
    parts = []
    
    if queries_str:
        parts = [part.strip() for part in queries_str.split(",")]
        parts = [part for part in parts if part]

    if not parts and fallback_query:
        parts = [fallback_query.strip()]

    if not parts:
        raise ValueError("Provide at least one query via --queries or --query")

    primary = parts[0]
    followups = []
    seen = {primary}
    
    for part in parts[1:]:
        if part not in seen:
            followups.append(part)
            seen.add(part)

    logger.info(f"Primary query: {primary}")
    if followups:
        logger.info(f"Follow-up queries: {', '.join(followups)}")
    
    return primary, followups


# ============================================================================
# MAIN SCRAPER EXECUTION
# ============================================================================

def run_scraper(config: Dict) -> Dict:
    """Execute the Maps scraping workflow with the given configuration."""
    
    # Extract configuration
    queries_str = config.get("queries", "")
    fallback_query = config.get("query", "dallas+bars")
    lat = config.get("lat")
    lon = config.get("lon")
    coordinates_str = config.get("coordinates")
    headless = config.get("headless", True)
    log_dir = config.get("log_dir", "logs")
    max_parse_results = config.get("max_parse_results", 0)
    capture_screenshots = config.get("capture_screenshots", True)
    capture_page_source = config.get("capture_page_source", True)
    proxy = config.get("proxy")
    scroll_config = {
        "max_scrolls": config.get("scroll_max", 40),
        "wait": config.get("scroll_wait", 1.2),
        "settle_rounds": config.get("scroll_settle_rounds", 3),
    }

    if coordinates_str:
        try:
            parsed_lat, parsed_lon = parse_coordinate_pair(coordinates_str)
            lat, lon = parsed_lat, parsed_lon
            logger.info(f"📍 Coordinates set from string: {lat}, {lon}")
        except ValueError as exc:
            logger.error(f"Invalid coordinates '{coordinates_str}': {exc}")
            raise
    
    # Supabase configuration
    supabase_url = config.get("supabase_url", "")
    supabase_key = config.get("supabase_key", "")
    supabase_table = config.get("supabase_table", "public.maps")
    supabase_bucket = config.get("supabase_bucket", "")
    supabase_staging_table = config.get("supabase_staging_table", "")
    
    # Parse queries
    try:
        primary_query, followup_queries = normalize_query_inputs(queries_str, fallback_query)
    except ValueError as exc:
        logger.error(str(exc))
        raise

    # Build initial URL
    zoom = config.get("zoom")
    url = build_maps_search_url(primary_query, lat=lat, lon=lon, zoom=zoom)
    if lat is not None and lon is not None:
        logger.info(
            f"🎯 Target: {primary_query} at ({lat}, {lon}) | zoom {normalize_zoom_value(zoom)}"
        )
    else:
        logger.info(f"🎯 Target: {primary_query}")

    # Create log directory
    os.makedirs(log_dir, exist_ok=True)
    logger.info(f"📁 Logs: {log_dir}")

    # Initialize tracking variables
    title = None
    current_url = None
    xhr_logs = []
    query_snapshots = []

    # Configure SeleniumBase
    sb_kwargs = {
        "uc": True,
        "test": True,
        "ad_block": config.get("ad_block", True),
        "headless": headless,
    }
    if proxy:
        sb_kwargs["proxy"] = proxy
        logger.info(f"🛡️ Proxy enabled: {proxy}")

    user_data_dir = config.get("user_data_dir")
    if user_data_dir:
        sb_kwargs["user_data_dir"] = user_data_dir
        os.makedirs(user_data_dir, exist_ok=True)
        logger.info(f"Using isolated user data dir: {user_data_dir}")

    logger.info("🚀 Starting browser...")

    # Execute scraping workflow
    with SB(**sb_kwargs) as sb:
        # Activate CDP mode
        sb.activate_cdp_mode("about:blank")
        tab = sb.cdp.page
        loop = sb.cdp.get_event_loop()
        
        if config.get("block_media", True):
            patterns = config.get("blocked_resource_patterns") or DEFAULT_BLOCKED_RESOURCE_PATTERNS
            configure_network_blocking(tab, loop, patterns)
        
        # Set up XHR monitoring
        xhr_requests = []
        last_xhr = {"ts": None}
        listen_for_xhr(tab, xhr_requests, last_xhr)

        # Load initial page
        logger.info(f"🌐 Loading: {url}")
        sb.cdp.open(url)
        sb.sleep(config.get("page_load_wait", 2.0))

        # Scroll sidebar for primary query
        logger.info(f"📜 Scrolling sidebar for primary query...")
        scroll_sidebar(sb, **scroll_config)
        
        # Capture primary query snapshot
        snapshot = capture_query_snapshot(
            sb,
            primary_query,
            0,
            log_dir,
            max_results=max_parse_results,
            save_page_source=capture_page_source,
            save_screenshot=capture_screenshots,
        )
        query_snapshots.append(snapshot)
        print_query_summary(snapshot)

        # Process follow-up queries
        for index, followup in enumerate(followup_queries, start=1):
            logger.info(f"🔄 Follow-up query {index}/{len(followup_queries)}: {followup}")
            run_secondary_query(
                sb,
                followup,
                lat=lat,
                lon=lon,
                zoom=zoom,
                wait_after=config.get("query_wait", 4.5),
            )
            scroll_sidebar(sb, **scroll_config)
            
            snapshot = capture_query_snapshot(
                sb,
                followup,
                index,
                log_dir,
                max_results=max_parse_results,
                save_page_source=capture_page_source,
                save_screenshot=capture_screenshots,
            )
            query_snapshots.append(snapshot)
            print_query_summary(snapshot)

        # Capture final state
        title = sb.get_title()
        current_url = sb.get_current_url()
        logger.info(f"📄 Page title: {title}")
        logger.info(f"🔗 Final URL: {current_url}")

        # Collect XHR logs
        loop = sb.cdp.get_event_loop()
        xhr_logs = loop.run_until_complete(receive_xhr(tab, xhr_requests, last_xhr))

    # Validate snapshots
    if not query_snapshots:
        raise RuntimeError("No query snapshots were captured")

    # Copy final artifacts
    final_snapshot = query_snapshots[-1]
    final_artifacts: Dict[str, Any] = {}

    final_screenshot_src = final_snapshot.get("screenshot")
    if final_screenshot_src and os.path.exists(final_screenshot_src):
        final_screenshot_path = os.path.join(log_dir, "screenshot.png")
        shutil.copyfile(final_screenshot_src, final_screenshot_path)
        final_artifacts["screenshot"] = final_screenshot_path
    else:
        if capture_screenshots:
            logger.debug("Final screenshot not available to copy")
        else:
            logger.info("🖼️ Screenshot capture disabled for this run")

    final_page_source_src = final_snapshot.get("page_source")
    if final_page_source_src and os.path.exists(final_page_source_src):
        final_page_source_path = os.path.join(log_dir, "page_source.html")
        shutil.copyfile(final_page_source_src, final_page_source_path)
        final_artifacts["page_source"] = final_page_source_path
    else:
        if capture_page_source:
            logger.debug("Final page source not available to copy")
        else:
            logger.info("📄 Page source capture disabled for this run")

    # Build results object
    results_path = os.path.join(log_dir, "result.json")
    
    final_artifacts["results_json"] = results_path

    results = {
        "run_id": uuid4().hex,
        "primary_query": primary_query,
        "query": primary_query,
        "lat": lat,
        "lon": lon,
        "zoom": normalize_zoom_value(zoom) if lat is not None and lon is not None else None,
        "proxy": proxy,
        "coordinates": f"{lat},{lon}" if lat is not None and lon is not None else None,
        "additional_queries": followup_queries,
        "all_queries": [snap["query"] for snap in query_snapshots],
        "target_url": url,
        "resolved_url": current_url,
        "title": title,
        "headless": headless,
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "query_snapshots": query_snapshots,
        "xhr_entries": len(xhr_logs),
        "config": {
            "scroll_max": scroll_config["max_scrolls"],
            "scroll_wait": scroll_config["wait"],
            "max_parse_results": max_parse_results,
            "zoom": normalize_zoom_value(zoom) if zoom is not None else None,
            "proxy": proxy,
            "coordinates": coordinates_str,
            "capture_screenshots": capture_screenshots,
            "capture_page_source": capture_page_source,
        },
        "artifacts": final_artifacts,
    }

    # Export flattened rows for quick review
    csv_path = os.path.join(log_dir, "result.csv")
    csv_artifact = export_results_to_csv(results, csv_path)
    if csv_artifact:
        results["artifacts"]["results_csv"] = csv_artifact
        logger.info(f"🧾 Results CSV saved: {csv_artifact}")

    # Save XHR logs
    xhr_path = os.path.join(log_dir, "xhr_log.json")
    try:
        with open(xhr_path, "w", encoding="utf-8") as xf:
            json.dump(xhr_logs, xf, indent=2)
        results["artifacts"]["xhr_log"] = xhr_path
        logger.debug(f"Saved XHR logs: {xhr_path}")
    except Exception as exc:
        logger.warning(f"Unable to save XHR logs: {exc}")

    # Upload flattened profiles to Supabase staging table
    staging_status = upload_profiles_to_supabase_staging(
        results,
        supabase_url,
        supabase_key,
        supabase_staging_table,
    )
    if staging_status:
        results["staging"] = staging_status

    # Upload to Supabase table
    supabase_status = upload_results_to_supabase(
        results, supabase_url, supabase_key, supabase_table
    )
    if supabase_status:
        results["supabase"] = supabase_status

    # Upload artifacts to Supabase storage
    storage_status = upload_artifacts_to_supabase_storage(
        results.get("artifacts"),
        supabase_url,
        supabase_key,
        supabase_bucket,
        results.get("run_id"),
        config.get("local_artifact_dir"),
    )
    if storage_status:
        results["storage"] = storage_status

    local_status = persist_results_to_local_db(
        results,
        config.get("local_db_url", ""),
        config.get("local_db_table"),
        config.get("local_db_staging_table"),
        chunk_size=config.get("local_db_chunk_size", 500),
    )
    if local_status:
        results["local_db"] = local_status

    # Save results JSON
    with open(results_path, "w", encoding="utf-8") as result_file:
        json.dump(results, result_file, indent=2)
    
    logger.info(f"💾 Results saved: {results_path}")
    
    # Summary
    total_results = sum(snap["parsed_count"] for snap in query_snapshots)
    logger.info(f"")
    logger.info(f"=" * 60)
    logger.info(f"✅ SCRAPE COMPLETE")
    logger.info(f"📊 Total Results: {total_results}")
    logger.info(f"🔍 Queries Processed: {len(query_snapshots)}")
    logger.info(f"🆔 Run ID: {results['run_id']}")
    logger.info(f"=" * 60)
    
    return results


# ============================================================================
# CLI INTERFACE
# ============================================================================

def parse_arguments() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Google Maps Public Data Research - Webhook Ready Version",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Single query
  python %(prog)s --queries "dallas bars"
  
  # Multiple queries (first is primary, rest are follow-ups)
  python %(prog)s --queries "dallas bars, dallas restaurants, dallas cafes"
  
  # With coordinates
  python %(prog)s --queries "restaurants" --lat 32.7767 --lon -96.7970
  
  # Custom configuration
  python %(prog)s --queries "shops" --scroll-max 50 --headed
  
  # With Supabase (uses environment variables or CLI args)
  python %(prog)s --queries "stores" --supabase-url "https://xxx.supabase.co"
  
Environment Variables:
  SUPABASE_URL              Supabase project URL
  SUPABASE_KEY              Supabase service role key
  SUPABASE_TABLE            Target table identifier (default: public.maps)
  SUPABASE_BUCKET           Storage bucket name
  MAPS_LOCAL_DB_URL         Local Postgres connection string
  MAPS_LOCAL_DB_TABLE       Local table for run payloads (default: public.maps)
  MAPS_LOCAL_DB_STAGING_TABLE Local staging table (default: public.maps_profiles_staging)
  MAPS_LOCAL_DB_CHUNK_SIZE  Batch size for local staging inserts (default: 500)
        """
    )
    
    # Query configuration
    parser.add_argument(
        "--queries",
        default="",
        help="Comma-separated list of queries. First is primary, rest are follow-ups.",
    )
    parser.add_argument(
        "--query",
        default="dallas+bars",
        help="Fallback single query if --queries is not provided.",
    )
    parser.add_argument(
        "--lat",
        type=float,
        default=None,
        help="Latitude coordinate for geographically-focused search.",
    )
    parser.add_argument(
        "--lon",
        type=float,
        default=None,
        help="Longitude coordinate for geographically-focused search.",
    )
    parser.add_argument(
        "--coordinates",
        default=os.getenv("MAPS_COORDINATES", ""),
        help="Comma-separated latitude,longitude pair (overrides --lat/--lon).",
    )
    parser.add_argument(
        "--zoom",
        type=float,
        default=15,
        help="Map zoom level when coordinates are provided (default: 15).",
    )
    parser.add_argument(
        "--proxy",
        default=os.getenv("MAPS_PROXY", ""),
        help="Optional proxy string (SERVER:PORT or USER:PASS@SERVER:PORT).",
    )
    
    # Browser configuration
    parser.add_argument(
        "--headed",
        action="store_true",
        help="Run browser with UI instead of headless mode.",
    )
    parser.add_argument(
        "--no-ad-block",
        action="store_true",
        help="Disable ad blocking.",
    )
    parser.add_argument(
        "--block-media",
        dest="block_media",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Block heavy media resources (images, fonts, videos) via CDP (default: enabled).",
    )
    parser.add_argument(
        "--user-data-dir",
        default=None,
        help="Chrome user data directory for browser isolation.",
    )
    
    # Scraping behavior
    parser.add_argument(
        "--scroll-max",
        type=int,
        default=40,
        help="Maximum number of sidebar scrolls (default: 40).",
    )
    parser.add_argument(
        "--scroll-wait",
        type=float,
        default=1.2,
        help="Wait time between scrolls in seconds (default: 1.2).",
    )
    parser.add_argument(
        "--scroll-settle-rounds",
        type=int,
        default=3,
        help="Number of unchanged scrolls before stopping (default: 3).",
    )
    parser.add_argument(
        "--page-load-wait",
        type=float,
        default=4.5,
        help="Wait time after initial page load (default: 4.5s).",
    )
    parser.add_argument(
        "--query-wait",
        type=float,
        default=4.5,
        help="Wait time after each follow-up query (default: 4.5s).",
    )
    parser.add_argument(
        "--max-parse-results",
        type=int,
        default=0,
        help="Maximum results to parse per query (0 = unlimited).",
    )
    
    # Output configuration
    parser.add_argument(
        "--log-dir",
        default="logs",
        help="Directory to store logs and artifacts (default: logs).",
    )
    parser.add_argument(
        "--local-artifact-dir",
        default=os.getenv("MAPS_LOCAL_ARTIFACT_DIR", ""),
        help="Optional directory to mirror Supabase bucket uploads locally.",
    )
    parser.add_argument(
        "--screenshots",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Capture per-query screenshots and final snapshot (default: enabled).",
    )
    parser.add_argument(
        "--page-source",
        dest="page_source",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Save HTML page sources for each snapshot (default: enabled).",
    )
    
    # Supabase configuration
    parser.add_argument(
        "--supabase-url",
        default=os.getenv("SUPABASE_URL", ""),
        help="Supabase project URL (env: SUPABASE_URL).",
    )
    parser.add_argument(
        "--supabase-key",
        default=os.getenv("SUPABASE_KEY") or os.getenv("SUPABASE_SERVICE_ROLE_KEY", ""),
        help="Supabase API key (env: SUPABASE_KEY or SUPABASE_SERVICE_ROLE_KEY).",
    )
    parser.add_argument(
        "--supabase-table",
        default=os.getenv("SUPABASE_TABLE", "public.maps"),
        help="Supabase table identifier (env: SUPABASE_TABLE, default: public.maps).",
    )
    parser.add_argument(
        "--supabase-bucket",
        default=os.getenv("SUPABASE_BUCKET", ""),
        help="Supabase Storage bucket name (env: SUPABASE_BUCKET).",
    )
    parser.add_argument(
        "--supabase-staging-table",
        default=os.getenv("SUPABASE_STAGING_TABLE", ""),
        help="Supabase staging table for flattened profile rows (env: SUPABASE_STAGING_TABLE).",
    )
    
    # Local database configuration
    parser.add_argument(
        "--local-db-url",
        default=os.getenv("MAPS_LOCAL_DB_URL", ""),
        help="Postgres connection string for local persistence (env: MAPS_LOCAL_DB_URL).",
    )
    parser.add_argument(
        "--local-db-table",
        default=os.getenv("MAPS_LOCAL_DB_TABLE", "public.maps"),
        help="Local table for run payloads (env: MAPS_LOCAL_DB_TABLE, default: public.maps).",
    )
    parser.add_argument(
        "--local-db-staging-table",
        default=os.getenv("MAPS_LOCAL_DB_STAGING_TABLE", "public.maps_profiles_staging"),
        help="Local staging table for flattened rows (env: MAPS_LOCAL_DB_STAGING_TABLE).",
    )
    parser.add_argument(
        "--local-db-chunk-size",
        type=int,
        default=_env_int("MAPS_LOCAL_DB_CHUNK_SIZE", 500),
        help="Batch size for local staging inserts (env: MAPS_LOCAL_DB_CHUNK_SIZE, default: 500).",
    )
    
    # Logging
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Enable verbose debug logging.",
    )
    
    return parser.parse_args()


def main():
    """Main entry point for the scraper."""
    args = parse_arguments()
    
    # Configure logging level
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
        logger.debug("Verbose logging enabled")
    
    coordinates_arg = (args.coordinates or "").strip()
    lat = args.lat
    lon = args.lon
    if coordinates_arg:
        try:
            parsed_lat, parsed_lon = parse_coordinate_pair(coordinates_arg)
            lat, lon = parsed_lat, parsed_lon
        except ValueError as exc:
            logger.error(f"Invalid --coordinates value '{coordinates_arg}': {exc}")
            return 1
    
    # Build configuration from arguments
    config = {
        "queries": args.queries,
        "query": args.query,
        "lat": lat,
        "lon": lon,
        "zoom": args.zoom,
        "proxy": args.proxy or None,
        "coordinates": coordinates_arg or None,
        "headless": not args.headed,
        "ad_block": not args.no_ad_block,
        "block_media": args.block_media,
        "user_data_dir": args.user_data_dir,
        "scroll_max": args.scroll_max,
        "scroll_wait": args.scroll_wait,
        "scroll_settle_rounds": args.scroll_settle_rounds,
        "page_load_wait": args.page_load_wait,
        "query_wait": args.query_wait,
        "max_parse_results": args.max_parse_results,
        "log_dir": args.log_dir,
        "local_artifact_dir": args.local_artifact_dir,
        "capture_screenshots": args.screenshots,
        "capture_page_source": args.page_source,
        "supabase_url": args.supabase_url,
        "supabase_key": args.supabase_key,
        "supabase_table": args.supabase_table,
        "supabase_bucket": args.supabase_bucket,
        "supabase_staging_table": args.supabase_staging_table,
        "local_db_url": args.local_db_url,
        "local_db_table": args.local_db_table,
        "local_db_staging_table": args.local_db_staging_table,
        "local_db_chunk_size": args.local_db_chunk_size,
    }
    
    # Log configuration summary
    logger.info("=" * 60)
    logger.info("🗺️  GOOGLE MAPS SCRAPER v2.0 - WEBHOOK READY")
    logger.info("=" * 60)
    
    # Run the scraper
    try:
        results = run_scraper(config)
        logger.info("✅ Script completed successfully")
        return 0
    except KeyboardInterrupt:
        logger.warning("⚠️ Script interrupted by user")
        return 130
    except Exception as exc:
        logger.error(f"❌ Script failed: {exc}", exc_info=True)
        return 1


if __name__ == "__main__":
    sys.exit(main())
