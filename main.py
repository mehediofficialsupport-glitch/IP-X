#!/usr/bin/env python3
"""
ProxyFlow — Residential Proxy Pool Manager
Manage, health-check, rotate and bandwidth-account proxies you own or are
authorized to use. Traffic tests run ONLY against user-authorized targets.

Python 3.11+  |  Deps: httpx, rich
Run:  python main.py            python main.py --test-server
      python main.py --check    python main.py --import file.txt
      python main.py --profile  python main.py --stats
"""

from __future__ import annotations

import argparse
import asyncio
import base64
import ipaddress
import json
import logging
import random
import re
import shutil
import sqlite3
import sys
import time
import uuid
from collections import deque
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse

import httpx
from rich.align import Align
from rich.console import Console, Group
from rich.live import Live
from rich.panel import Panel
from rich.progress import BarColumn, Progress, TextColumn
from rich.prompt import Confirm, Prompt
from rich.table import Table
from rich.text import Text

# --------------------------------------------------------------------------- #
# Constants / paths
# --------------------------------------------------------------------------- #
APP_NAME = "ProxyFlow"
APP_VER = "1.0.0"
ROOT = Path(__file__).resolve().parent
DATA_DIR = ROOT / "data"
LOG_DIR = ROOT / "logs"
BACKUP_DIR = DATA_DIR / "backups"
DB_PATH = DATA_DIR / "proxyflow.db"
LOG_FILE = LOG_DIR / "proxyflow.log"

console = Console()

STATUS = ("ONLINE", "OFFLINE", "CHECKING", "ERROR", "DISABLED", "UNKNOWN")
STRATEGIES = ("round_robin", "random", "lowest_latency", "least_used",
              "highest_success", "smart")

DEFAULT_SETTINGS = {
    "health_check_url": "",          # user MUST configure (own server)
    "connect_timeout": 10,
    "read_timeout": 15,
    "max_retries": 3,
    "cooldown_seconds": 60,
    "rotation_strategy": "least_used",
    "traffic_target_url": "",
    "test_duration_seconds": 30,
    "test_concurrency": 2,           # hard cap: 10
    "max_traffic_per_test_mb": 500,
    "global_limit_gb": 10.0,
    "warning_pct": 80,
    "per_proxy_limit_mb": 0,         # 0 = unlimited
    "session_limit_mb": 0,
    "daily_limit_mb": 0,
    "default_profile": "",
    "log_level": "INFO",
    "ui_refresh_interval": 0.7,
}

MAX_CONCURRENCY = 10
MAX_TEST_MB = 5000  # absolute ceiling


# --------------------------------------------------------------------------- #
# Utilities
# --------------------------------------------------------------------------- #
def human_bytes(n: float) -> str:
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{int(n)} B" if unit == "B" else f"{n:,.1f} {unit}"
        n /= 1024
    return f"{n:,.1f} TB"


def utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def today() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


# ---- Credential protection (local obfuscation; NOT cryptography-grade) ----- #
_CRED_KEY = (uuid.getnode().to_bytes(6, "big") + b"proxyflow") * 4


def protect_secret(secret: str | None) -> str | None:
    if not secret:
        return None
    raw = secret.encode("utf-8")
    x = bytes(b ^ _CRED_KEY[i % len(_CRED_KEY)] for i, b in enumerate(raw))
    return base64.b64encode(x).decode("ascii")


def reveal_secret(token: str | None) -> str | None:
    if not token:
        return None
    try:
        x = base64.b64decode(token.encode("ascii"))
        return bytes(b ^ _CRED_KEY[i % len(_CRED_KEY)]
                     for i, b in enumerate(x)).decode("utf-8")
    except Exception:
        return None


def mask_proxy(host: str, port, username: str | None) -> str:
    return f"{username}:********@{host}:{port}" if username else f"{host}:{port}"


# ---- Proxy line parsing ---------------------------------------------------- #
_SCHEME_RE = re.compile(
    r"^(?P<scheme>https?|socks5)://(?:"
    r"(?P<user>[^:@/\s]+):(?P<pass>[^@/\s]+)@)?"
    r"(?P<host>[^\s:/@]+):(?P<port>\d+)$", re.I)
_AT_RE = re.compile(
    r"^(?:(?P<user>[^:@/\s]+):(?P<pass>[^@/\s]+)@)?"
    r"(?P<host>[^\s:/@]+):(?P<port>\d+)$")
_HOST_RE = re.compile(r"^[A-Za-z0-9]([A-Za-z0-9.\-_]*[A-Za-z0-9])?$")


def is_valid_host(host: str) -> bool:
    if len(host) > 253 or not _HOST_RE.match(host):
        return False
    try:
        ipaddress.ip_address(host)
        return True
    except ValueError:
        pass
    return "." in host or host == "localhost"


def parse_proxy_line(line: str) -> dict | None:
    """Parse HOST:PORT | HOST:PORT:USER:PASS | USER:PASS@HOST:PORT |
    scheme://[user:pass@]host:port -> proxy dict or None."""
    line = line.strip()
    if not line or line.startswith("#"):
        return None
    scheme, user, pw, host, port = None, None, None, None, None

    m = _SCHEME_RE.match(line)
    if m:
        scheme = m["scheme"].lower()
        if scheme == "https":
            scheme = "http"
        user, pw, host, port = m["user"], m["pass"], m["host"], int(m["port"])
    else:
        m = _AT_RE.match(line)
        if not m:
            return None
        user, pw, host, port = m["user"], m["pass"], m["host"], int(m["port"])
        scheme = "http"

    if not (1 <= port <= 65535) or not is_valid_host(host):
        return None
    if bool(user) != bool(pw):
        return None  # malformed credentials
    if user and (len(user) > 128 or len(pw) > 256):
        return None
    return {"host": host, "port": port, "username": user, "password": pw,
            "protocol": scheme,
            "proxy_url": build_proxy_url(scheme, host, port, user, pw)}


def build_proxy_url(protocol: str, host: str, port: int,
                    user: str | None, pw: str | None) -> str:
    auth = f"{user}:{pw}@" if user else ""
    return f"{protocol}://{auth}{host}:{port}"


def fingerprint(proxy_url: str) -> str:
    """Duplicate-detection id that ignores credentials."""
    p = urlparse(proxy_url)
    return f"{p.hostname}:{p.port}"


# --------------------------------------------------------------------------- #
# Logging (sanitized — never logs passwords/tokens)
# --------------------------------------------------------------------------- #
class SanitizingFilter(logging.Filter):
    PATTERNS = (re.compile(r"(?i)(password|passwd|pwd|token|authorization|"
                           r"cookie|secret)\s*[:=]\s*\S+"),)

    def filter(self, record: logging.LogRecord) -> bool:
        msg = record.getMessage()
        for pat in self.PATTERNS:
            msg = pat.sub(r"\1=[REDACTED]", msg)
        record.msg, record.args = msg, None
        return True


def setup_logging(level: str = "INFO") -> logging.Logger:
    LOG_DIR.mkdir(exist_ok=True)
    lg = logging.getLogger("proxyflow")
    lg.setLevel(getattr(logging, level.upper(), logging.INFO))
    lg.handlers.clear()
    fh = logging.FileHandler(LOG_FILE, encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s | %(levelname)s | %(message)s"))
    fh.addFilter(SanitizingFilter())
    lg.addHandler(fh)
    lg.propagate = False
    return lg


log = setup_logging()


# --------------------------------------------------------------------------- #
# Database
# --------------------------------------------------------------------------- #
class Database:
    def __init__(self, path: Path = DB_PATH):
        DATA_DIR.mkdir(exist_ok=True)
        self.conn = sqlite3.connect(path, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA foreign_keys=ON")
        self.conn.execute("PRAGMA journal_mode=WAL")
        self._migrate()

    def _migrate(self):
        c = self.conn
        with c:
            c.executescript("""
            CREATE TABLE IF NOT EXISTS proxies (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                host TEXT NOT NULL,
                port INTEGER NOT NULL,
                username TEXT,
                password_enc TEXT,
                protocol TEXT NOT NULL DEFAULT 'http',
                proxy_url TEXT NOT NULL,
                fp TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'UNKNOWN',
                last_checked TEXT,
                latency_ms REAL,
                total_bytes INTEGER NOT NULL DEFAULT 0,
                session_bytes INTEGER NOT NULL DEFAULT 0,
                success_count INTEGER NOT NULL DEFAULT 0,
                failure_count INTEGER NOT NULL DEFAULT 0,
                consec_failures INTEGER NOT NULL DEFAULT 0,
                last_error TEXT,
                created_at TEXT NOT NULL,
                last_used TEXT,
                enabled INTEGER NOT NULL DEFAULT 1,
                cooldown_until REAL NOT NULL DEFAULT 0
            );
            CREATE UNIQUE INDEX IF NOT EXISTS ux_fp ON proxies(fp);
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY, value TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS profiles (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL UNIQUE,
                config TEXT NOT NULL,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ts TEXT NOT NULL,
                proxy_id INTEGER,
                event TEXT NOT NULL,
                status TEXT,
                latency_ms REAL,
                bytes INTEGER,
                error TEXT);
            CREATE TABLE IF NOT EXISTS usage_daily (
                day TEXT PRIMARY KEY,
                bytes INTEGER NOT NULL DEFAULT 0);
            CREATE TABLE IF NOT EXISTS kv (key TEXT PRIMARY KEY, value TEXT);
            """)

    def exec(self, sql: str, params: tuple = ()) -> sqlite3.Cursor:
        return self.conn.execute(sql, params)

    def commit(self):
        self.conn.commit()

    def one(self, sql, params=()):
        return self.conn.execute(sql, params).fetchone()

    def all(self, sql, params=()):
        return self.conn.execute(sql, params).fetchall()

    def log_event(self, proxy_id, event, status=None, latency=None,
                  nbytes=None, error=None):
        try:
            with self.conn:
                self.conn.execute(
                    "INSERT INTO events(ts,proxy_id,event,status,latency_ms,"
                    "bytes,error) VALUES(?,?,?,?,?,?,?)",
                    (utcnow(), proxy_id, event, status, latency, nbytes, error))
        except sqlite3.Error as e:
            log.error("database error: %s", e)

    def get_setting(self, key: str) -> str:
        row = self.one("SELECT value FROM settings WHERE key=?", (key,))
        return row["value"] if row else str(DEFAULT_SETTINGS.get(key, ""))

    def set_setting(self, key: str, value: str):
        with self.conn:
            self.conn.execute(
                "INSERT INTO settings(key,value) VALUES(?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                (key, value))

    def load_settings(self) -> dict:
        s = dict(DEFAULT_SETTINGS)
        for row in self.all("SELECT key,value FROM settings"):
            try:
                s[row["key"]] = json.loads(row["value"])
            except (json.JSONDecodeError, TypeError):
                s[row["key"]] = row["value"]
        return s

    def backup(self) -> Path | None:
        BACKUP_DIR.mkdir(parents=True, exist_ok=True)
        dest = BACKUP_DIR / f"proxyflow_{datetime.now():%Y%m%d_%H%M%S}.db"
        try:
            shutil.copy2(DB_PATH, dest)
            log.info("database backup created: %s", dest.name)
            return dest
        except OSError as e:
            log.error("backup failed: %s", e)
            return None

    def restore(self, src: Path) -> bool:
        if not src.is_file():
            return False
        self.backup()  # automatic safety backup before restore
        self.conn.close()
        shutil.copy2(src, DB_PATH)
        self.conn = sqlite3.connect(DB_PATH, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA foreign_keys=ON")
        self.conn.execute("PRAGMA journal_mode=WAL")
        return True

    def close(self):
        try:
            with self.conn:
                self.conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        except sqlite3.Error:
            pass
        self.conn.close()


# --------------------------------------------------------------------------- #
# Model
# --------------------------------------------------------------------------- #
class Proxy:
    __slots__ = ("id", "host", "port", "username", "password", "protocol",
                 "proxy_url", "fp", "status", "last_checked", "latency_ms",
                 "total_bytes", "session_bytes", "success_count",
                 "failure_count", "consec_failures", "last_error",
                 "created_at", "last_used", "enabled", "cooldown_until")

    def __init__(self, row: dict):
        for k in self.__slots__:
            setattr(self, k, row.get(k))
        if self.status not in STATUS:
            self.status = "UNKNOWN"
        self.enabled = bool(self.enabled)

    @property
    def masked(self) -> str:
        return mask_proxy(self.host, self.port, self.username)

    def success_rate(self) -> float:
        t = self.success_count + self.failure_count
        return (self.success_count / t * 100) if t else 0.0

    def score(self) -> float:
        """Smart score: success + latency + reliability − penalties."""
        sr = self.success_rate()                        # 0..100
        lat = self.latency_ms or 1000
        lat_score = clamp(100 - (lat / 20), 0, 50)
        rel = clamp(20 - self.consec_failures * 5, 0, 20)
        fail_pen = clamp(self.consec_failures * 10, 0, 60)
        usage_pen = clamp(self.total_bytes / (100 * 1024 * 1024), 0, 15)
        if self.status == "OFFLINE" or not self.enabled:
            return 0.0
        return round(clamp(sr * 0.5 + lat_score + rel - fail_pen - usage_pen,
                           0, 100), 1)


def row_to_proxy(row) -> Proxy:
    d = dict(row)
    d["password"] = reveal_secret(d.get("password_enc"))
    return Proxy(d)


# --------------------------------------------------------------------------- #
# Settings validation
# --------------------------------------------------------------------------- #
def validate_settings(s: dict) -> list[str]:
    errs = []
    s["connect_timeout"] = clamp(float(s["connect_timeout"]), 1, 120)
    s["read_timeout"] = clamp(float(s["read_timeout"]), 1, 300)
    s["max_retries"] = int(clamp(int(s["max_retries"]), 0, 10))
    s["cooldown_seconds"] = int(clamp(int(s["cooldown_seconds"]), 0, 3600))
    s["test_concurrency"] = int(clamp(int(s["test_concurrency"]), 1,
                                      MAX_CONCURRENCY))
    s["max_traffic_per_test_mb"] = int(clamp(
        int(s["max_traffic_per_test_mb"]), 1, MAX_TEST_MB))
    s["warning_pct"] = int(clamp(int(s["warning_pct"]), 1, 99))
    s["test_duration_seconds"] = int(clamp(int(s["test_duration_seconds"]),
                                           1, 3600))
    s["ui_refresh_interval"] = clamp(float(s["ui_refresh_interval"]), 0.3, 5)
    if s["rotation_strategy"] not in STRATEGIES:
        errs.append(f"Unknown rotation strategy: {s['rotation_strategy']}")
    if s["log_level"] not in ("DEBUG", "INFO", "WARNING", "ERROR"):
        errs.append(f"Invalid log level: {s['log_level']}")
    for k in ("health_check_url", "traffic_target_url"):
        v = str(s.get(k) or "")
        if v:
            p = urlparse(v)
            if p.scheme not in ("http", "https") or not p.netloc:
                errs.append(f"{k} must be an http(s) URL")
    return errs


# --------------------------------------------------------------------------- #
# Health Checker
# --------------------------------------------------------------------------- #
class HealthChecker:
    def __init__(self, db: Database, settings: dict):
        self.db, self.s = db, settings

    async def check_one(self, proxy: Proxy, url: str) -> Proxy:
        t0 = time.perf_counter()
        try:
            async with httpx.AsyncClient(
                    proxy=proxy.proxy_url,
                    timeout=httpx.Timeout(float(self.s["connect_timeout"]),
                                          read=float(self.s["read_timeout"])),
                    follow_redirects=True) as client:
                r = await client.get(url)
            ms = (time.perf_counter() - t0) * 1000
            if 200 <= r.status_code < 400:
                proxy.status, proxy.latency_ms = "ONLINE", round(ms)
                proxy.success_count += 1
                proxy.consec_failures = 0
                proxy.last_error = None
            else:
                proxy.status = "ERROR"
                proxy.last_error = f"HTTP {r.status_code}"
                proxy.failure_count += 1
                proxy.consec_failures += 1
                proxy.latency_ms = None
        except (httpx.TimeoutException, TimeoutError):
            proxy.status, proxy.last_error = "OFFLINE", "Connection timeout"
            proxy.failure_count += 1
            proxy.consec_failures += 1
        except (httpx.ConnectError, ConnectionError, OSError) as e:
            proxy.status = "OFFLINE"
            proxy.last_error = f"Connection error: {type(e).__name__}"
            proxy.failure_count += 1
            proxy.consec_failures += 1
        except httpx.ProxyError:
            proxy.status, proxy.last_error = "OFFLINE", "Proxy auth/protocol error"
            proxy.failure_count += 1
            proxy.consec_failures += 1
        except httpx.HTTPError as e:
            proxy.status = "ERROR"
            proxy.last_error = f"HTTP error: {type(e).__name__}"
            proxy.failure_count += 1
            proxy.consec_failures += 1
        except Exception as e:  # never crash on one bad proxy
            proxy.status = "ERROR"
            proxy.last_error = f"Unexpected: {type(e).__name__}"
            proxy.failure_count += 1
            proxy.consec_failures += 1
        proxy.last_checked = utcnow()
        self._persist(proxy)
        return proxy

    def _persist(self, p: Proxy):
        self.db.exec(
            "UPDATE proxies SET status=?,last_checked=?,latency_ms=?,"
            "success_count=?,failure_count=?,consec_failures=?,last_error=? "
            "WHERE id=?",
            (p.status, p.last_checked, p.latency_ms, p.success_count,
             p.failure_count, p.consec_failures, p.last_error, p.id))
        self.db.commit()
        self.db.log_event(p.id, "health_check", p.status, p.latency_ms,
                          None, p.last_error)


# --------------------------------------------------------------------------- #
# Proxy Manager (rotation + fallback)
# --------------------------------------------------------------------------- #
class ProxyManager:
    def __init__(self, db: Database, settings: dict):
        self.db, self.s = db, settings
        self.pool: list[Proxy] = []
        self.rr_index = 0

    def load_pool(self, only_enabled: bool = True):
        q = "SELECT * FROM proxies" + (" WHERE enabled=1" if only_enabled else "")
        self.pool = [row_to_proxy(r) for r in self.db.all(q + " ORDER BY id")]

    def reload_one(self, pid: int):
        for i, p in enumerate(self.pool):
            if p.id == pid:
                row = self.db.one("SELECT * FROM proxies WHERE id=?", (pid,))
                if row:
                    self.pool[i] = row_to_proxy(row)
                return

    def eligible(self) -> list[Proxy]:
        now = time.time()
        return [p for p in self.pool
                if p.enabled and p.status not in ("OFFLINE", "DISABLED")
                and p.cooldown_until <= now]

    def select(self, strategy: str | None = None) -> Proxy | None:
        strat = strategy or self.s["rotation_strategy"]
        cands = self.eligible()
        if not cands:
            return None
        if strat == "round_robin":
            p = cands[self.rr_index % len(cands)]
            self.rr_index += 1
            return p
        if strat == "random":
            return random.choice(cands)
        if strat == "lowest_latency":
            return min(cands, key=lambda p: p.latency_ms or 10_000)
        if strat == "least_used":
            return min(cands, key=lambda p: p.total_bytes)
        if strat == "highest_success":
            return max(cands, key=lambda p: p.success_rate())
        if strat == "smart":
            return max(cands, key=lambda p: p.score())
        return cands[0]

    def record_failure(self, proxy: Proxy, reason: str):
        proxy.failure_count += 1
        proxy.consec_failures += 1
        proxy.last_error = reason
        proxy.status = "OFFLINE"
        proxy.cooldown_until = time.time() + int(self.s["cooldown_seconds"])
        self.db.exec(
            "UPDATE proxies SET status='OFFLINE',failure_count=failure_count+1,"
            "consec_failures=consec_failures+1,last_error=?,cooldown_until=? "
            "WHERE id=?", (reason, proxy.cooldown_until, proxy.id))
        self.db.commit()
        self.db.log_event(proxy.id, "fallback_failure", "OFFLINE", error=reason)
        if proxy.consec_failures >= 5:
            log.warning("proxy #%s failed %s consecutive checks",
                        proxy.id, proxy.consec_failures)

    def record_success(self, proxy: Proxy, ms: float | None = None):
        self.db.exec(
            "UPDATE proxies SET status='ONLINE',consec_failures=0,"
            "success_count=success_count+1,last_used=?,"
            "latency_ms=COALESCE(?,latency_ms) WHERE id=?",
            (utcnow(), ms, proxy.id))
        self.db.commit()

    def add_bytes(self, proxy: Proxy, nbytes: int):
        self.db.exec(
            "UPDATE proxies SET total_bytes=total_bytes+?,"
            "session_bytes=session_bytes+? WHERE id=?",
            (nbytes, nbytes, proxy.id))
        self.db.exec("INSERT INTO usage_daily(day,bytes) VALUES(?,?) "
                     "ON CONFLICT(day) DO UPDATE SET bytes=bytes+?",
                     (today(), nbytes, nbytes))
        self.db.commit()
        proxy.total_bytes += nbytes
        proxy.session_bytes += nbytes

    def reset_session_usage(self):
        self.db.exec("UPDATE proxies SET session_bytes=0")
        self.db.commit()
        for p in self.pool:
            p.session_bytes = 0


# --------------------------------------------------------------------------- #
# Traffic Engine (authorized targets only, strict limits)
# --------------------------------------------------------------------------- #
class LimitReached(Exception):
    pass


class TrafficEngine:
    def __init__(self, db: Database, settings: dict, manager: ProxyManager):
        self.db, self.s, self.mgr = db, settings, manager
        self.last_stats: dict = {}

    def _limits_state(self) -> dict:
        daily = self.db.one("SELECT COALESCE(SUM(bytes),0) b FROM usage_daily "
                            "WHERE day=?", (today(),))["b"]
        glob = self.db.one("SELECT COALESCE(SUM(total_bytes),0) b "
                           "FROM proxies")["b"]
        return {"daily": daily, "global": glob}

    def preflight(self, session_bytes: int) -> str | None:
        st = self._limits_state()
        g_lim = float(self.s["global_limit_gb"]) * 1024**3
        if g_lim > 0 and st["global"] >= g_lim:
            return "Global bandwidth limit reached"
        d_lim = int(self.s["daily_limit_mb"]) * 1024**2
        if d_lim > 0 and st["daily"] >= d_lim:
            return "Daily bandwidth limit reached"
        s_lim = int(self.s["session_limit_mb"]) * 1024**2
        if s_lim > 0 and session_bytes >= s_lim:
            return "Session bandwidth limit reached"
        return None

    async def run_test(self, target: str, duration: int, concurrency: int,
                       max_mb: int, strategy: str) -> dict:
        stats = {"requests": 0, "ok": 0, "failed": 0, "bytes": 0,
                 "current_proxy": None, "rate": 0.0, "elapsed": 0.0,
                 "stopped_reason": None, "fallback_msg": None}
        self.last_stats = dict(stats)
        sem = asyncio.Semaphore(max(1, concurrency))
        max_bytes = int(max_mb) * 1024 * 1024
        g_lim = float(self.s["global_limit_gb"]) * 1024**3
        d_lim = int(self.s["daily_limit_mb"]) * 1024**2
        s_lim = int(self.s["session_limit_mb"]) * 1024**2
        session_base = sum(p.session_bytes for p in self.mgr.pool)
        start = time.perf_counter()
        bytes_window: deque[tuple[float, int]] = deque()
        stop = asyncio.Event()
        lock = asyncio.Lock()

        def within_limits() -> str | None:
            if stats["bytes"] > max_bytes:
                return "Per-test traffic cap reached"
            st = self._limits_state()
            if g_lim and st["global"] > g_lim:
                return "Global bandwidth limit reached"
            if d_lim and st["daily"] > d_lim:
                return "Daily bandwidth limit reached"
            if s_lim and (session_base + stats["bytes"]) > s_lim:
                return "Session limit reached"
            return None

        async def one_request():
            proxy = self.mgr.select(strategy)
            if proxy is None:
                stats["stopped_reason"] = "No healthy proxies available"
                stop.set()
                return
            stats["current_proxy"] = proxy.id
            got = 0
            try:
                t0 = time.perf_counter()
                async with httpx.AsyncClient(
                        proxy=proxy.proxy_url,
                        timeout=httpx.Timeout(
                            float(self.s["connect_timeout"]),
                            read=float(self.s["read_timeout"])),
                        follow_redirects=True) as client:
                    async with sem:
                        async with client.stream("GET", target) as resp:
                            async for chunk in resp.aiter_bytes(65536):
                                got += len(chunk)
                                async with lock:
                                    stats["bytes"] += len(chunk)
                                    stats["requests"] += 1
                                if got and got % (512 * 1024) < 65536:
                                    reason = within_limits()
                                    if reason:
                                        stats["stopped_reason"] = reason
                                        stop.set()
                ms = (time.perf_counter() - t0) * 1000
                async with lock:
                    stats["ok"] += 1
                self.mgr.record_success(proxy, round(ms))
                if got:
                    self.mgr.add_bytes(proxy, got)
                reason = within_limits()
                if reason:
                    stats["stopped_reason"] = reason
                    stop.set()
            except LimitReached:
                raise
            except Exception as e:
                reason = ("Connection timeout" if isinstance(
                    e, (httpx.TimeoutException, TimeoutError))
                    else type(e).__name__)
                self.mgr.record_failure(proxy, reason)
                nxt = self.mgr.select(strategy)
                async with lock:
                    stats["failed"] += 1
                    stats["fallback_msg"] = (
                        f"Proxy #{proxy.id} failed ({reason}) → "
                        f"switching to #{nxt.id}" if nxt else
                        f"Proxy #{proxy.id} failed ({reason}) — no fallback")
                self.db.log_event(proxy.id, "traffic_failure", "OFFLINE",
                                  error=reason)

        async def worker():
            while not stop.is_set():
                await one_request()
                await asyncio.sleep(0.05)

        async def ticker():
            while not stop.is_set() and time.perf_counter() - start < duration:
                await asyncio.sleep(float(self.s["ui_refresh_interval"]))
                now = time.perf_counter()
                while bytes_window and now - bytes_window[0][0] > 2:
                    bytes_window.popleft()
                async with lock:
                    stats["elapsed"] = now - start
                    if bytes_window:
                        span = max(0.5, now - bytes_window[0][0])
                        stats["rate"] = sum(b for _, b in bytes_window) / span
                self.last_stats = dict(stats)
            stop.set()

        tasks = [asyncio.create_task(ticker())] + \
            [asyncio.create_task(worker()) for _ in range(max(1, concurrency))]
        try:
            await asyncio.wait_for(asyncio.gather(*tasks), timeout=duration + 5)
        except (asyncio.TimeoutError, LimitReached):
            stop.set()
        for t in tasks:
            t.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        stats["elapsed"] = time.perf_counter() - start
        self.last_stats = dict(stats)
        return stats


# --------------------------------------------------------------------------- #
# Local safe test server
# --------------------------------------------------------------------------- #
class TestServerHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def _bytes(self, n: int):
        self.send_response(200)
        self.send_header("Content-Type", "application/octet-stream")
        self.send_header("Content-Length", str(n))
        self.end_headers()
        chunk = b"x" * 65536
        remaining = n
        while remaining > 0:
            w = min(len(chunk), remaining)
            self.wfile.write(chunk[:w])
            remaining -= w

    def do_GET(self):
        if self.path == "/health":
            body = b'{"status":"ok"}'
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif m := re.match(r"^/bytes/(\d+)mb$", self.path):
            self._bytes(int(m.group(1)) * 1024 * 1024)
        elif m := re.match(r"^/bytes/(\d+)kb$", self.path):
            self._bytes(int(m.group(1)) * 1024)
        else:
            self.send_response(404)
            self.end_headers()


def run_test_server(port: int = 8971):
    srv = ThreadingHTTPServer(("127.0.0.1", port), TestServerHandler)
    print(f"[✓] Safe local test server on http://127.0.0.1:{port}"
          f"  (/health, /bytes/1mb, /bytes/10mb)")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        srv.server_close()
        print("\n[✓] Test server stopped.")


# --------------------------------------------------------------------------- #
# UI helpers
# --------------------------------------------------------------------------- #
def status_color(s: str) -> str:
    return {"ONLINE": "green", "OFFLINE": "red", "CHECKING": "cyan",
            "ERROR": "red", "DISABLED": "grey50",
            "UNKNOWN": "yellow"}.get(s, "yellow")


def alert(msg: str, kind: str = "warning"):
    icon = {"warning": "⚠", "stop": "⛔", "info": "ℹ"}.get(kind, "⚠")
    style = {"warning": "yellow", "stop": "bold red",
             "info": "cyan"}.get(kind, "yellow")
    console.print(Panel(Text(f"{icon} {msg}", style=style, justify="center"),
                        border_style=style, padding=(0, 1)))


def confirm(msg: str, default=False) -> bool:
    try:
        return Confirm.ask(msg, console=console, default=default)
    except (KeyboardInterrupt, EOFError):
        return False


def ask(prompt: str, default: str = "") -> str:
    try:
        return Prompt.ask(prompt, console=console, default=default).strip()
    except (KeyboardInterrupt, EOFError):
        return ""


def render_status_bar(db: Database, profile_name: str):
    total_db = db.one("SELECT COUNT(*) c FROM proxies")["c"]
    online_db = db.one("SELECT COUNT(*) c FROM proxies WHERE status='ONLINE' "
                       "AND enabled=1")["c"]
    traffic = db.one("SELECT COALESCE(SUM(total_bytes),0) b FROM proxies")["b"]
    console.print(Text("━" * max(20, console.width - 1), style="grey30"))
    console.print(
        f"Profile: [magenta]{profile_name or '—'}[/]   "
        f"Proxies: [green]{online_db}[/]/{total_db} Online   "
        f"Traffic: [cyan]{human_bytes(traffic)}[/]   "
        f"Engine: [green]● READY[/]")
    console.print("[dim][B] Back   [R] Refresh   [H] Help   [Q] Quit[/dim]")


# --------------------------------------------------------------------------- #
# Application
# --------------------------------------------------------------------------- #
class App:
    PROFILE_DEFAULTS = {
        "rotation_strategy": "least_used", "max_retries": 3,
        "cooldown_seconds": 60, "max_traffic_per_test_mb": 500,
        "target_url": "", "proxy_ids": [], "health_check_url": ""}

    def __init__(self, db: Database, settings: dict):
        self.db = db
        self.s = settings
        self.manager = ProxyManager(db, settings)
        self.checker = HealthChecker(db, settings)
        self.engine = TrafficEngine(db, settings, self.manager)
        self.profile_name = ""

    # ---------------- loading ---------------- #
    def loading_screen(self):
        stages = ["Loading configuration", "Opening database",
                  "Loading saved proxy pools", "Checking local environment",
                  "Preparing traffic engine", "Starting dashboard"]
        checks = ["✓", "✓", "✓", "✓", "•", " "]
        progress = Progress(TextColumn("[progress.description]{task.description}"),
                            BarColumn(bar_width=28),
                            TextColumn("{task.percentage:>3.0f}%"))
        task = progress.add_task("", total=len(stages))
        for i, stage in enumerate(stages):
            progress.update(task, description=f"{checks[i]} {stage}",
                            completed=i)
            body = Group(
                Text("\n      ◈  PROXYFLOW  ◈\n      "
                     "Residential Proxy Manager\n",
                     style="bold magenta", justify="center"),
                Align.center(progress))
            console.clear()
            console.print(Panel(body, border_style="magenta", padding=(1, 4)))
            time.sleep(0.15)
        progress.update(task, completed=len(stages))
        time.sleep(0.2)

    # ---------------- session recovery ---------------- #
    def session_recovery(self):
        last = self.db.one("SELECT value FROM kv WHERE key='last_profile'")
        if not last:
            return
        try:
            name = json.loads(last["value"])
        except (json.JSONDecodeError, TypeError):
            return
        prof = self.db.one("SELECT * FROM profiles WHERE name=?", (name,))
        if not prof:
            return
        used = self.db.one("SELECT COALESCE(SUM(session_bytes),0) b "
                           "FROM proxies")["b"]
        console.print(Panel(Group(
            Text(f"\nPrevious profile found:\n{name}\n", style="magenta"),
            Text(f"Last session: {prof['updated_at']}"),
            Text(f"Used: {human_bytes(used)}\n"),
            Text("[1] Resume   [2] Choose Another   [3] Start Fresh")),
            title="SESSION RECOVERY", border_style="cyan"))
        choice = ask("Choice", "1")
        if choice == "1":
            self.load_profile_by_name(name)
            alert(f"Profile '{name}' loaded", "info")
        elif choice == "2":
            self.profiles_menu()
        # 3: start fresh — traffic is NEVER auto-started after restart

    # ---------------- dashboard ---------------- #
    def dashboard(self):
        while True:
            total = self.db.one("SELECT COUNT(*) c FROM proxies")["c"]
            online = self.db.one(
                "SELECT COUNT(*) c FROM proxies WHERE status='ONLINE'")["c"]
            offline = self.db.one(
                "SELECT COUNT(*) c FROM proxies WHERE status IN "
                "('OFFLINE','ERROR')")["c"]
            traffic = self.db.one(
                "SELECT COALESCE(SUM(total_bytes),0) b FROM proxies")["b"]
            sess = self.db.one(
                "SELECT COALESCE(SUM(session_bytes),0) b FROM proxies")["b"]
            lat = self.db.one(
                "SELECT AVG(latency_ms) a FROM proxies WHERE status='ONLINE' "
                "AND latency_ms IS NOT NULL")["a"]
            body = Table.grid(padding=(0, 2))
            body.add_row("[bold]Proxy Pool[/]", str(total))
            body.add_row("[bold]Online[/]", f"[green]{online}[/]")
            body.add_row("[bold]Offline[/]", f"[red]{offline}[/]")
            body.add_row("")
            body.add_row("[bold]Total Traffic[/]",
                         f"[cyan]{human_bytes(traffic)}[/]")
            body.add_row("[bold]Session Traffic[/]",
                         f"[cyan]{human_bytes(sess)}[/]")
            body.add_row("[bold]Avg Latency[/]",
                         f"{lat:.0f} ms" if lat else "—")
            body.add_row("")
            body.add_row("[bold]Active Profile[/]",
                         f"[magenta]{self.profile_name or '—'}[/]")
            body.add_row("[bold]Engine Status[/]", "[green]● READY[/]")
            console.print(Panel(body, title="PROXYFLOW",
                                border_style="magenta", padding=(1, 2)))
            menu = Table.grid(padding=(0, 3))
            rows = ["[1] Proxy Pool", "[2] Add Proxy", "[3] Import Proxies",
                    "[4] Health Check", "[5] Authorized Traffic Test",
                    "[6] Usage Statistics", "[7] Saved Profiles",
                    "[8] Settings", "[9] Logs", "[0] Exit"]
            for i in range(0, len(rows), 2):
                menu.add_row(rows[i], rows[i + 1] if i + 1 < len(rows) else "")
            console.print(menu)
            render_status_bar(self.db, self.profile_name)
            c = ask("Select").lower()
            if c in ("q", "0"):
                if confirm("Exit ProxyFlow?"):
                    return
            elif c == "h":
                self.help_screen()
            elif c == "1":
                self.pool_screen()
            elif c == "2":
                self.add_proxy_screen()
            elif c == "3":
                self.import_screen()
            elif c == "4":
                asyncio.run(self.health_check_screen())
            elif c == "5":
                asyncio.run(self.traffic_test_screen())
            elif c == "6":
                self.usage_screen()
            elif c == "7":
                self.profiles_menu()
            elif c == "8":
                self.settings_screen()
            elif c == "9":
                self.logs_screen()
            console.clear()

    # ---------------- add proxy ---------------- #
    def add_proxy_screen(self):
        console.print(Panel("Add Proxy — enter details\n",
                            title="ADD PROXY", border_style="cyan"))
        host = ask("Host")
        if not host:
            return
        port_s = ask("Port")
        user = ask("Username (blank for none)")
        pw = ask("Password (blank for none)")
        proto = (ask("Protocol [http/https/socks5]", "http") or "http").lower()
        try:
            port = int(port_s)
        except ValueError:
            alert("Invalid port", "warning")
            return
        if proto not in ("http", "https", "socks5"):
            alert("Protocol must be http, https or socks5", "warning")
            return
        if not is_valid_host(host):
            alert("Invalid hostname/IP", "warning")
            return
        if not (1 <= port <= 65535):
            alert("Port out of range", "warning")
            return
        d = parse_proxy_line(
            f"{proto}://{user + ':' + pw + '@' if user else ''}{host}:{port}")
        if d is None:
            alert("Malformed input", "warning")
            return
        console.print("[1] Save Proxy  [2] Test Proxy  [3] Save + Test  "
                      "[4] Cancel")
        c = ask("Choice")
        if c == "4" or not c:
            return
        if c in ("2", "3"):
            tmp = Proxy({"id": 0, "proxy_url": d["proxy_url"],
                         "status": "UNKNOWN", "success_count": 0,
                         "failure_count": 0, "consec_failures": 0,
                         "enabled": True, "host": d["host"], "port": d["port"],
                         "username": d["username"], "total_bytes": 0,
                         "session_bytes": 0, "cooldown_until": 0})
            asyncio.run(self._run_checks([tmp]))
            if c == "2":
                return
        fp = fingerprint(d["proxy_url"])
        if self.db.one("SELECT 1 FROM proxies WHERE fp=?", (fp,)):
            alert("Duplicate proxy (same host:port already saved)", "warning")
            return
        self.db.exec(
            "INSERT INTO proxies(host,port,username,password_enc,protocol,"
            "proxy_url,fp,created_at) VALUES(?,?,?,?,?,?,?,?)",
            (d["host"], d["port"], d["username"],
             protect_secret(d["password"]), d["protocol"], d["proxy_url"],
             fp, utcnow()))
        self.db.commit()
        self.db.log_event(None, "proxy_added", f"{d['host']}:{d['port']}")
        alert(f"Proxy {mask_proxy(d['host'], d['port'], d['username'])} saved",
              "info")

    async def _run_checks(self, proxies: list[Proxy]):
        url = self.s["health_check_url"]
        if not url:
            alert("Health check URL not configured (Settings)", "warning")
            return
        console.print(f"Checking {len(proxies)} proxies...\n")
        sem = asyncio.Semaphore(5)

        async def one(p: Proxy):
            async with sem:
                r = await self.checker.check_one(p, url)
                mark = "[green]✓" if r.status == "ONLINE" else "[red]✗"
                detail = (f"{r.latency_ms:.0f}ms" if r.latency_ms
                          else (r.last_error or "failed"))
                console.print(f"  {mark}[/] {p.masked}  {detail}")

        await asyncio.gather(*(one(p) for p in proxies))
        online = sum(1 for p in proxies if p.status == "ONLINE")
        rate = online / len(proxies) * 100 if proxies else 0
        console.print(Panel(
            f"{len(proxies)} Checked   {online} Online   "
            f"{len(proxies) - online} Offline   {rate:.2f}% Success Rate",
            title="RESULT", border_style="green" if online else "red"))

    # ---------------- import ---------------- #
    def import_screen(self, path: str | None = None):
        path = path or ask("Path to TXT file")
        p = Path(path).expanduser()
        if not p.is_file():
            alert(f"File not found: {p}", "warning")
            return
        try:
            lines = p.read_text(encoding="utf-8",
                                errors="replace").splitlines()
        except OSError as e:
            alert(f"Cannot read file: {e}", "warning")
            return
        parsed, invalid = [], 0
        for line in lines:
            d = parse_proxy_line(line)
            if d:
                parsed.append(d)
            elif line.strip() and not line.strip().startswith("#"):
                invalid += 1
        dups, unique, seen = 0, [], set()
        for d in parsed:
            fp = fingerprint(d["proxy_url"])
            if fp in seen or self.db.one("SELECT 1 FROM proxies WHERE fp=?",
                                         (fp,)):
                dups += 1
                continue
            seen.add(fp)
            unique.append(d)
        console.print(Panel(
            f"Imported: {len(parsed) + invalid}\nValid: {len(parsed)}\n"
            f"Duplicate: {dups}\nInvalid: {invalid}",
            title="IMPORT PREVIEW", border_style="cyan"))
        if unique and confirm("Save imported proxies?"):
            for d in unique:
                self.db.exec(
                    "INSERT INTO proxies(host,port,username,password_enc,"
                    "protocol,proxy_url,fp,created_at) "
                    "VALUES(?,?,?,?,?,?,?,?)",
                    (d["host"], d["port"], d["username"],
                     protect_secret(d["password"]), d["protocol"],
                     d["proxy_url"], fingerprint(d["proxy_url"]), utcnow()))
            self.db.commit()
            self.db.log_event(None, "proxies_imported", f"count={len(unique)}")
            alert(f"Saved {len(unique)} proxies", "info")

    # ---------------- pool ---------------- #
    def pool_screen(self):
        while True:
            rows = self.db.all("SELECT * FROM proxies ORDER BY id LIMIT 200")
            t = Table(title="Proxy Pool", border_style="cyan")
            for col, kw in [("ID", {"justify": "right"}), ("Proxy", {}),
                            ("Status", {}), ("Latency", {"justify": "right"}),
                            ("Used", {"justify": "right"}),
                            ("Success", {"justify": "right"}),
                            ("Failures", {"justify": "right"})]:
                t.add_column(col, **kw)
            for r in rows[:50]:
                lat = f"{r['latency_ms']:.0f}ms" if r["latency_ms"] else "---"
                t.add_row(str(r["id"]).zfill(2),
                          mask_proxy(r["host"], r["port"], r["username"]),
                          Text(r["status"], style=status_color(r["status"])),
                          lat, human_bytes(r["total_bytes"]),
                          str(r["success_count"]), str(r["failure_count"]))
            console.print(t)
            console.print("[1] Select  [2] Enable/Disable  [3] Test  "
                          "[4] Remove  [5] Reset Session Usage  [B] Back")
            c = ask("Choice").lower()
            if c == "b" or not c:
                return
            if c == "5":
                self.manager.reset_session_usage()
                alert("Session usage reset", "info")
                console.clear()
                continue
            try:
                pid = int(ask("Proxy ID"))
            except ValueError:
                continue
            row = self.db.one("SELECT * FROM proxies WHERE id=?", (pid,))
            if not row:
                alert("No such proxy", "warning")
                continue
            if c == "1":
                alert(f"Proxy #{pid}: "
                      f"{mask_proxy(row['host'], row['port'], row['username'])}",
                      "info")
            elif c == "2":
                self.db.exec("UPDATE proxies SET enabled=1-enabled WHERE id=?",
                             (pid,))
                self.db.commit()
            elif c == "3":
                asyncio.run(self._run_checks([row_to_proxy(row)]))
            elif c == "4":
                if confirm(f"Remove Proxy #{pid}?"):
                    self.db.exec("DELETE FROM proxies WHERE id=?", (pid,))
                    self.db.commit()
                    alert(f"Proxy #{pid} removed", "info")
            console.clear()

    # ---------------- health check ---------------- #
    async def health_check_screen(self):
        self.manager.load_pool(only_enabled=False)
        if not self.manager.pool:
            alert("Pool is empty — add proxies first", "warning")
            return
        await self._run_checks(self.manager.pool)

    # ---------------- traffic test ---------------- #
    async def traffic_test_screen(self):
        console.print(Panel(
            "[yellow]You are responsible for ensuring this endpoint is yours "
            "or you have permission to test it.[/]",
            title="AUTHORIZED TRAFFIC TEST", border_style="yellow"))
        target = ask("Target URL", str(self.s["traffic_target_url"] or ""))
        if not target:
            return
        p = urlparse(target)
        if p.scheme not in ("http", "https") or not p.netloc:
            alert("Target must be an http(s) URL", "warning")
            return
        try:
            dur = int(ask("Duration seconds",
                          str(self.s["test_duration_seconds"])))
            conc = int(ask(f"Concurrency (1-{MAX_CONCURRENCY})",
                           str(self.s["test_concurrency"])))
            cap = int(ask("Max traffic MB",
                          str(self.s["max_traffic_per_test_mb"])))
        except ValueError:
            alert("Invalid numbers", "warning")
            return
        conc = int(clamp(conc, 1, MAX_CONCURRENCY))
        cap = int(clamp(cap, 1, MAX_TEST_MB))
        dur = int(clamp(dur, 1, 3600))
        strategy = ask(f"Strategy ({'/'.join(STRATEGIES)})",
                       str(self.s["rotation_strategy"]))
        if strategy not in STRATEGIES:
            strategy = str(self.s["rotation_strategy"])
        self.manager.load_pool()
        pre = self.engine.preflight(0)
        if pre:
            alert(pre, "stop")
            return
        console.print(Panel(
            f"Target: {target}\nDuration: {dur}s   Concurrency: {conc}   "
            f"Max traffic: {human_bytes(cap * 1024**2)}   "
            f"Strategy: {strategy}", border_style="cyan"))
        if not confirm("[Y] Start  [N] Cancel"):
            alert("Cancelled", "info")
            return

        task = asyncio.create_task(self.engine.run_test(
            target, dur, conc, cap, strategy))
        with Live(console=console, refresh_per_second=2) as live:
            while not task.done():
                live.update(self._engine_panel(
                    target, self.engine.last_stats, dur))
                await asyncio.sleep(float(self.s["ui_refresh_interval"]))
        st = await task
        self._test_result_panel(target, st)

    def _engine_panel(self, target: str, st: dict, dur: int) -> Panel:
        st = st or {}
        sess = self.db.one("SELECT COALESCE(SUM(session_bytes),0) b "
                           "FROM proxies")["b"]
        total = self.db.one("SELECT COALESCE(SUM(total_bytes),0) b "
                            "FROM proxies")["b"]
        elapsed = st.get("elapsed", 0)
        body = Table.grid(padding=(0, 2))
        body.add_row("[bold]Target[/]", target)
        body.add_row("")
        body.add_row("[bold]Active Proxy[/]",
                     f"#{st.get('current_proxy')}" if st.get("current_proxy")
                     else "—")
        body.add_row("[bold]Status[/]",
                     "[green]● CONNECTED[/]" if st.get("current_proxy")
                     else "[yellow]● INIT[/]")
        body.add_row("")
        body.add_row("[bold]Session Traffic[/]", human_bytes(sess))
        body.add_row("[bold]Current Rate[/]",
                     f"{st.get('rate', 0) / 1024 / 1024:.1f} MB/s")
        body.add_row("[bold]Total Traffic[/]", human_bytes(total))
        body.add_row("")
        body.add_row("[bold]Requests[/]", str(st.get("requests", 0)))
        body.add_row("[bold]Successful[/]", f"[green]{st.get('ok', 0)}[/]")
        body.add_row("[bold]Failed[/]", f"[red]{st.get('failed', 0)}[/]")
        body.add_row("")
        body.add_row("[bold]Time[/]",
                     f"{int(elapsed // 60):02d}:{int(elapsed % 60):02d} "
                     f"/ {dur}s")
        if st.get("fallback_msg"):
            body.add_row("[yellow]→[/]",
                         f"[yellow]{st['fallback_msg']}[/]")
        return Panel(body, title="TRAFFIC ENGINE", border_style="magenta")

    def _test_result_panel(self, target: str, st: dict):
        if st.get("stopped_reason"):
            alert(f"TRAFFIC ENGINE STOPPED — {st['stopped_reason']}", "stop")
        rate = (st["ok"] / st["requests"] * 100) if st["requests"] else 0
        console.print(Panel(
            f"Target: {target}\n"
            f"Requests: {st['requests']}  OK: {st['ok']}  "
            f"Failed: {st['failed']}  ({rate:.1f}%)\n"
            f"Test Traffic: {human_bytes(st['bytes'])}  "
            f"Avg Rate: {st['bytes'] / max(0.1, st['elapsed']) / 1024 / 1024:.1f}"
            f" MB/s\nDuration: {st['elapsed']:.0f}s",
            title="TEST COMPLETE", border_style="green"))
        self.db.log_event(None, "traffic_test_complete", f"{rate:.0f}%",
                          nbytes=st["bytes"])

    # ---------------- usage ---------------- #
    def usage_screen(self):
        console.clear()
        total_used = self.db.one(
            "SELECT COALESCE(SUM(total_bytes),0) b FROM proxies")["b"]
        quota = float(self.s["global_limit_gb"]) * 1024**3
        pct = (total_used / quota * 100) if quota else 0
        warn = float(self.s["warning_pct"])
        bar_full = int(clamp(pct / 100 * 18, 0, 18))
        bar = ("█" * bar_full) + ("░" * (18 - bar_full))
        color = "green" if pct < warn else ("yellow" if pct < 100 else "red")
        if quota and pct >= 100:
            alert("⛔ TRAFFIC ENGINE STOPPED — Configured bandwidth limit "
                  "reached.", "stop")
        elif quota and pct >= warn:
            alert(f"⚠ WARNING — {pct:.0f}% of configured bandwidth has been "
                  "consumed.", "warning")
        console.print(Panel(
            f"Total Purchased: {human_bytes(quota) if quota else '—'}\n"
            f"Used:  {human_bytes(total_used)}\n"
            f"Remaining: {human_bytes(max(0, quota - total_used))}\n\n"
            f"[{color}]{bar}[/] {pct:.1f}%",
            title="USAGE", border_style=color))
        t = Table(border_style="cyan")
        for col, kw in [("Proxy", {"justify": "right"}),
                        ("Used", {"justify": "right"}),
                        ("Success", {"justify": "right"}),
                        ("Latency", {"justify": "right"})]:
            t.add_column(col, **kw)
        for r in self.db.all("SELECT id,total_bytes,success_count,failure_count,"
                             "latency_ms FROM proxies ORDER BY total_bytes DESC"):
            sr = (r["success_count"] /
                  max(1, r["success_count"] + r["failure_count"]) * 100)
            t.add_row(f"#{str(r['id']).zfill(2)}",
                      human_bytes(r["total_bytes"]), f"{sr:.1f}%",
                      f"{r['latency_ms']:.0f}ms" if r["latency_ms"] else "—")
        console.print(t)
        ask("(press Enter)")

    # ---------------- profiles ---------------- #
    def _profile_config(self, name: str) -> str:
        cfg = {k: self.s.get(k, v) for k, v in self.PROFILE_DEFAULTS.items()}
        cfg["name"] = name
        return json.dumps(cfg)

    def profiles_menu(self):
        while True:
            rows = self.db.all("SELECT id,name,updated_at FROM profiles "
                               "ORDER BY name")
            t = Table(title="Saved Profiles", border_style="magenta")
            t.add_column("Name")
            t.add_column("Updated")
            for r in rows:
                t.add_row(r["name"] +
                          (" [magenta]●[/]" if r["name"] == self.profile_name
                           else ""), r["updated_at"])
            console.print(t)
            console.print("[1] Create  [2] Load  [3] Duplicate  [4] Rename  "
                          "[5] Delete  [6] Export  [7] Import  [B] Back")
            c = ask("Choice").lower()
            if c == "b" or not c:
                return
            try:
                if c == "1":
                    name = ask("Profile name")
                    if name and not self.db.one(
                            "SELECT 1 FROM profiles WHERE name=?", (name,)):
                        now = utcnow()
                        self.db.exec("INSERT INTO profiles(name,config,"
                                     "created_at,updated_at) VALUES(?,?,?,?)",
                                     (name, self._profile_config(name),
                                      now, now))
                        self.db.commit()
                        alert(f"Profile '{name}' created", "info")
                elif c == "2":
                    name = ask("Profile name")
                    if name:
                        self.load_profile_by_name(name)
                elif c in ("3", "4"):
                    name = ask("Existing profile name")
                    new = ask("New name")
                    src = self.db.one("SELECT config FROM profiles WHERE "
                                      "name=?", (name,))
                    if new and src:
                        now = utcnow()
                        if c == "3":
                            self.db.exec("INSERT INTO profiles(name,config,"
                                         "created_at,updated_at) "
                                         "VALUES(?,?,?,?)",
                                         (new, src["config"], now, now))
                        else:
                            self.db.exec("UPDATE profiles SET name=?,"
                                         "updated_at=? WHERE name=?",
                                         (new, now, name))
                        self.db.commit()
                elif c == "5":
                    name = ask("Profile name")
                    if name and confirm(f"Delete profile '{name}'?"):
                        self.db.exec("DELETE FROM profiles WHERE name=?",
                                     (name,))
                        self.db.commit()
                elif c == "6":
                    self.export_profile(ask("Profile name"))
                elif c == "7":
                    self.import_profile()
            except sqlite3.Error as e:
                alert(f"Database error: {e}", "warning")
            console.clear()

    def load_profile_by_name(self, name: str) -> bool:
        row = self.db.one("SELECT config FROM profiles WHERE name=?", (name,))
        if not row:
            alert(f"Profile '{name}' not found", "warning")
            return False
        try:
            cfg = json.loads(row["config"])
        except json.JSONDecodeError:
            alert("Profile config is corrupted", "warning")
            return False
        for k in self.PROFILE_DEFAULTS:
            if k in cfg:
                self.s[k] = cfg[k]
        self.db.set_setting("last_profile", json.dumps(name))
        self.profile_name = name
        self.manager.load_pool()
        return True

    def export_profile(self, name: str):
        row = self.db.one("SELECT config FROM profiles WHERE name=?", (name,))
        if not row:
            alert("Profile not found", "warning")
            return
        out = {"name": name, "config": json.loads(row["config"]),
               "credentials": False}
        if confirm("Include proxy credentials (PLAINTEXT) in export? "
                   "Not recommended!"):
            out["credentials"] = True
            out["proxies"] = [
                {"host": r["host"], "port": r["port"],
                 "username": r["username"],
                 "password": reveal_secret(r["password_enc"]),
                 "protocol": r["protocol"]}
                for r in self.db.all("SELECT host,port,username,password_enc,"
                                     "protocol FROM proxies")]
        dest = ROOT / f"{name.replace(' ', '_')}_profile.json"
        try:
            dest.write_text(json.dumps(out, indent=2), encoding="utf-8")
            alert(f"Exported to {dest}", "info")
        except OSError as e:
            alert(f"Export failed: {e}", "warning")

    def import_profile(self):
        path = ask("JSON file path")
        p = Path(path).expanduser()
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
            name = data["name"]
            now = utcnow()
            self.db.exec(
                "INSERT INTO profiles(name,config,created_at,updated_at) "
                "VALUES(?,?,?,?) ON CONFLICT(name) DO UPDATE SET "
                "config=excluded.config, updated_at=excluded.updated_at",
                (name, json.dumps(data["config"]), now, now))
            if data.get("credentials") and data.get("proxies"):
                for d in data["proxies"]:
                    fp = fingerprint(build_proxy_url(
                        d.get("protocol", "http"), d["host"], d["port"],
                        d.get("username"), d.get("password")))
                    if not self.db.one("SELECT 1 FROM proxies WHERE fp=?",
                                       (fp,)):
                        self.db.exec(
                            "INSERT INTO proxies(host,port,username,"
                            "password_enc,protocol,proxy_url,fp,created_at) "
                            "VALUES(?,?,?,?,?,?,?,?)",
                            (d["host"], d["port"], d.get("username"),
                             protect_secret(d.get("password")),
                             d.get("protocol", "http"),
                             build_proxy_url(d.get("protocol", "http"),
                                             d["host"], d["port"],
                                             d.get("username"),
                                             d.get("password")),
                             fp, utcnow()))
            self.db.commit()
            alert(f"Imported profile '{name}'", "info")
        except (OSError, json.JSONDecodeError, KeyError, sqlite3.Error,
                ValueError, TypeError) as e:
            alert(f"Import failed: {e}", "warning")

    # ---------------- settings ---------------- #
    def settings_screen(self):
        while True:
            t = Table(title="Settings", border_style="cyan")
            t.add_column("Key")
            t.add_column("Value")
            for k, v in self.s.items():
                t.add_row(k, str(v) if v not in ("", None) else "—")
            console.print(t)
            console.print("Enter setting name to edit, [S] Save, [B] Back")
            k = ask("Setting").lower()
            if k == "b" or not k:
                return
            if k == "s":
                errs = validate_settings(self.s)
                if errs:
                    for e in errs:
                        alert(e, "warning")
                else:
                    for key, val in self.s.items():
                        self.db.set_setting(key, json.dumps(val))
                    self.db.commit()
                    alert("Settings saved", "info")
                continue
            if k in self.s:
                v = ask(f"New value for {k}", str(self.s[k]))
                cur = self.s[k]
                try:
                    if isinstance(cur, float):
                        self.s[k] = float(v)
                    elif isinstance(cur, int) and not isinstance(cur, bool):
                        self.s[k] = int(v)
                    else:
                        self.s[k] = v
                except ValueError:
                    alert("Invalid value type", "warning")

    # ---------------- logs ---------------- #
    def logs_screen(self):
        console.print("[1] Recent Events  [2] Errors Only  [3] Export Logs  "
                      "[4] Clear Logs  [B] Back")
        c = ask("Choice").lower()
        if c == "b" or not c:
            return
        if c == "1":
            self._events_table(self.db.all(
                "SELECT * FROM events ORDER BY id DESC LIMIT 50"))
            ask("(press Enter)")
        elif c == "2":
            self._events_table(self.db.all(
                "SELECT * FROM events WHERE status IN ('OFFLINE','ERROR') "
                "OR error IS NOT NULL ORDER BY id DESC LIMIT 50"))
            ask("(press Enter)")
        elif c == "3":
            dest = LOG_DIR / f"events_export_{datetime.now():%Y%m%d_%H%M%S}.csv"
            try:
                with open(dest, "w", encoding="utf-8") as f:
                    f.write("ts,proxy_id,event,status,latency_ms,bytes,error\n")
                    for r in self.db.all("SELECT * FROM events"):
                        f.write(",".join(
                            str(r[k2]) if r[k2] is not None else ""
                            for k2 in ("ts", "proxy_id", "event", "status",
                                       "latency_ms", "bytes", "error")) + "\n")
                alert(f"Exported to {dest}", "info")
            except OSError as e:
                alert(f"Export failed: {e}", "warning")
        elif c == "4":
            if confirm("Clear all event logs?"):
                self.db.exec("DELETE FROM events")
                self.db.commit()
                alert("Logs cleared", "info")

    def _events_table(self, rows):
        t = Table(border_style="cyan")
        for col in ("Time", "Proxy", "Event", "Status", "Latency", "Bytes",
                    "Error"):
            t.add_column(col)
        for r in rows:
            t.add_row(r["ts"], f"#{r['proxy_id']}" if r["proxy_id"] else "—",
                      r["event"], r["status"] or "—",
                      f"{r['latency_ms']:.0f}" if r["latency_ms"] else "—",
                      human_bytes(r["bytes"]) if r["bytes"] else "—",
                      (r["error"] or "—")[:60])
        console.print(t)

    # ---------------- help ---------------- #
    def help_screen(self):
        console.print(Panel(
            "[bold]1. Proxy Pool[/] — Manage saved proxies (enable/disable, "
            "test, remove).\n"
            "[bold]2. Health Check[/] — Check connectivity through your "
            "configured test endpoint.\n"
            "[bold]3. Traffic Test[/] — Controlled traffic ONLY against "
            "targets you own or are authorized to test.\n"
            "[bold]4. Profiles[/] — Save and restore proxy configurations.\n"
            "[bold]5. Statistics[/] — View bandwidth and reliability.\n"
            "[bold]6. Fallback[/] — Auto-switch from failed proxies with "
            "cooldown.\n\n"
            "[dim]Keys: [B] Back  [R] Refresh  [H] Help  [Q] Quit[/]",
            title="PROXYFLOW HELP", border_style="cyan"))
        ask("(press Enter)")

    # ---------------- shutdown ---------------- #
    def save_state(self):
        try:
            self.db.set_setting("last_profile", json.dumps(self.profile_name))
            self.db.commit()
            self.db.close()
        except sqlite3.Error:
            pass


# --------------------------------------------------------------------------- #
# CLI / entry point
# --------------------------------------------------------------------------- #
def run_cli_check():
    db = Database()
    s = db.load_settings()
    errs = validate_settings(s)
    mgr = ProxyManager(db, s)
    mgr.load_pool()
    online = sum(1 for p in mgr.pool if p.status == "ONLINE")
    print(f"[✓] Database OK ({DB_PATH})")
    print(f"[{'✓' if not errs else '✗'}] Settings"
          f"{': ' + '; '.join(errs) if errs else ' valid'}")
    print(f"[✓] Pool: {len(mgr.pool)} proxies, {online} online")
    print(f"[{'✓' if s['health_check_url'] else '✗'}] Health check URL"
          f"{': ' + str(s['health_check_url']) if s['health_check_url'] else ' not configured'}")
    db.close()


def run_cli_import(path: str):
    db = Database()
    app = App(db, db.load_settings())
    app.import_screen(path)
    db.close()


def run_cli_stats():
    db = Database()
    app = App(db, db.load_settings())
    app.usage_screen()
    db.close()


def run_cli_profile():
    db = Database()
    app = App(db, db.load_settings())
    app.profiles_menu()
    db.close()


def main():
    parser = argparse.ArgumentParser(
        description="ProxyFlow — Residential Proxy Pool Manager")
    parser.add_argument("--check", action="store_true",
                        help="Verify config, database and pool")
    parser.add_argument("--import", dest="import_file", metavar="FILE",
                        help="Import proxies from TXT")
    parser.add_argument("--profile", action="store_true",
                        help="Manage profiles")
    parser.add_argument("--stats", action="store_true", help="Usage statistics")
    parser.add_argument("--test-server", dest="test_server", action="store_true",
                        help="Run local safe test server (port 8971)")
    parser.add_argument("--port", type=int, default=8971,
                        help="Port for --test-server")
    args = parser.parse_args()

    if args.test_server:
        run_test_server(args.port)
        return
    if args.check:
        run_cli_check()
        return
    if args.import_file:
        run_cli_import(args.import_file)
        return
    if args.stats:
        run_cli_stats()
        return
    if args.profile:
        run_cli_profile()
        return

    # ------- Interactive mode with Ctrl+C handling ------- #
    exit_code = 0
    db = None
    app = None
    try:
        db = Database()
        settings = db.load_settings()
        for e in validate_settings(settings):
            print(f"[!] Setting issue: {e}")
        global log
        log.setLevel(getattr(logging, str(settings["log_level"]).upper(),
                             logging.INFO))
        app = App(db, settings)
        app.loading_screen()
        app.session_recovery()
        app.manager.load_pool()
        console.clear()
        app.dashboard()
    except KeyboardInterrupt:
        console.print("\n[yellow]Interrupted — shutting down cleanly…[/]")
        exit_code = 130
    except sqlite3.Error as e:
        alert(f"Database error: {e}", "stop")
        exit_code = 1
    except Exception as e:  # never show raw traceback
        log.exception("fatal error")
        alert(f"Unexpected error: {type(e).__name__}. See logs/ for details.",
              "stop")
        exit_code = 1
    finally:
        if app is not None:
            try:
                app.save_state()
            except Exception:
                pass
        elif db is not None:
            try:
                db.close()
            except Exception:
                pass
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
