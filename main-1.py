#!/usr/bin/env python3
"""
Telegram Self-Bot — Production Ready
Lightweight, Reliable, Async-Safe, Crash-Resistant
For VPS ~512MB RAM, Single Process, JSON Storage
"""
from __future__ import annotations

import asyncio
import html
import json
import logging
import os
import re
import shutil
import signal
import time
from collections import deque
from contextlib import suppress
from logging.handlers import RotatingFileHandler
from typing import Any, Deque, Dict, List, Optional, Set, Tuple

from telethon import TelegramClient, events, errors
from telethon.errors import RPCError
from telethon.tl.custom import Button
from telethon.tl.functions.channels import JoinChannelRequest, LeaveChannelRequest
from telethon.tl.functions.messages import CheckChatInviteRequest, ImportChatInviteRequest
from telethon.tl.types import Channel, Chat, MessageEntityTextUrl, MessageEntityUrl
from telethon.utils import get_display_name

# ─────────────────────────────────────────────────────────────
# Configuration
# ─────────────────────────────────────────────────────────────
API_ID = int(os.environ.get("TG_API_ID") or "0")
API_HASH = os.environ.get("TG_API_HASH") or ""
LOGIN_BOT_TOKEN = os.environ.get("TG_BOT_TOKEN") or ""
BOT_SESSION = os.environ.get("TG_BOT_SESSION") or "login_bot"

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
ACCOUNTS_DIR = os.path.join(BASE_DIR, "accounts")
ACCOUNTS_FILE = os.path.join(BASE_DIR, "accounts.json")
DATA_FILE = os.path.join(BASE_DIR, "data.json")
LOG_FILE = os.path.join(BASE_DIR, "bot.log")
DATA_VERSION = 2

MAX_GROUPS = 5000
MAX_ADS = 40
MAX_AD_LEN = 4000
PAGE_SIZE = 8
PENDING_TTL = 120
LOG_KEEP = 30
SEND_RETRIES = 3
MAX_FLOOD_WAIT = 600
BACKUP_KEEP = 3
BACKUP_INTERVAL = 300
IMPORT_MAX_BYTES = 512 * 1024
FLUSH_EVERY = 5
TIMEOUT_SEC = 60
MAX_AD_RESTARTS = 3
COOLDOWN_SEC = 300
OP_LABEL = {"ad": "تبلیغ", "join": "جوین", "clean": "پاکسازی"}

STATE_STOPPED = "stopped"
STATE_RUNNING = "running"
STATE_PAUSED = "paused"
STATE_FAILED = "failed"
STATE_RESTARTING = "restarting"

ERR_SUCCESS = "success"
ERR_RETRY = "retry"
ERR_WAIT = "wait"
ERR_SKIP = "skip"
ERR_FORBIDDEN = "forbidden"
ERR_UNKNOWN = "unknown"
ERR_STOP = "stop"

DEFAULT_SETTINGS: Dict[str, Any] = {
    "join_delay": 60,
    "send_delay": 20,
    "check_after": 5,
    "round_wait": 300,
    "scan_limit": 400,
    "default_join_count": 50,
    "leave_on_delete": True,
    "leave_on_forbidden": True,
}

BOUNDS = {
    "join_delay": (10, 600),
    "send_delay": (5, 300),
    "check_after": (1, 60),
    "round_wait": (30, 3600),
    "scan_limit": (50, 2000),
    "default_join_count": (1, 200),
}
SETTING_STEP = {
    "join_delay": 10,
    "send_delay": 5,
    "check_after": 1,
    "round_wait": 30,
    "scan_limit": 50,
    "default_join_count": 10,
}
SETTING_LABEL = {
    "join_delay": "فاصله جوین (ثانیه)",
    "send_delay": "فاصله ارسال (ثانیه)",
    "check_after": "چک بعد از ارسال (ثانیه)",
    "round_wait": "صبر بین دورها (ثانیه)",
    "scan_limit": "حداکثر پیام اسکن کانال",
    "default_join_count": "تعداد پیش‌فرض جوین",
}

SKIP_USERNAMES = frozenset({
    "joinchat", "addstickers", "addemoji", "share", "socks", "proxy",
    "iv", "login", "s", "c", "boost", "giftcode", "invoice", "contact",
    "confirmphone", "setlanguage", "addtheme", "socks5",
})
INVITE_RE = re.compile(
    r"(?:https?://)?(?:t\.me|telegram\.me)/(?:joinchat/|\+)([A-Za-z0-9_\-]+)",
    re.I,
)
PUBLIC_RE = re.compile(
    r"(?:https?://)?(?:t\.me|telegram\.me)/([A-Za-z][A-Za-z0-9_]{3,32})(?:/\d+)?",
    re.I,
)

FORBIDDEN_ERRORS = (
    errors.ChatWriteForbiddenError,
    errors.UserBannedInChannelError,
    errors.ChatAdminRequiredError,
    errors.ChannelPrivateError,
    errors.PeerIdInvalidError,
    errors.ChatIdInvalidError,
)
DEAD_ENTITY_ERRORS = (
    errors.ChannelPrivateError,
    errors.PeerIdInvalidError,
    errors.ChatIdInvalidError,
    errors.ChannelInvalidError,
)

log = logging.getLogger("selfbot")


# ─────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────
def as_bool(value: Any, default: bool = True) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value != 0
    if isinstance(value, str):
        v = value.strip().lower()
        if v in ("true", "1", "yes", "on"):
            return True
        if v in ("false", "0", "no", "off"):
            return False
    return default


def as_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def clamp_int(value: Any, key: str) -> int:
    lo, hi = BOUNDS[key]
    n = as_int(value, int(DEFAULT_SETTINGS[key]))
    return max(lo, min(hi, n))


def esc(text: Any) -> str:
    return html.escape(str(text), quote=False)


def format_ts(ts: Any) -> str:
    n = as_int(ts, 0)
    if n <= 0:
        return "-"
    return time.strftime("%Y-%m-%d %H:%M", time.localtime(n))


def flood_seconds(e: errors.FloodWaitError) -> int:
    return max(1, int(getattr(e, "seconds", 1) or 1))


async def tg_call(coro: Any, timeout: float = TIMEOUT_SEC) -> Any:
    return await asyncio.wait_for(coro, timeout=timeout)


def chat_from_updates(updates: Any) -> Any:
    chats = getattr(updates, "chats", None) or []
    return chats[0] if chats else None


def running(task: Optional[asyncio.Task]) -> bool:
    return task is not None and not task.done()


def extract_links_from_text(text: Optional[str]) -> List[Tuple[str, str]]:
    if not text:
        return []
    out: List[Tuple[str, str]] = []
    for m in INVITE_RE.finditer(text):
        out.append(("private", m.group(1)))
    cleaned = INVITE_RE.sub(" ", text)
    for m in PUBLIC_RE.finditer(cleaned):
        username = m.group(1)
        if username.lower() in SKIP_USERNAMES:
            continue
        out.append(("public", username))
    return out


def links_from_message(msg: Any) -> List[Tuple[str, str]]:
    found: List[Tuple[str, str]] = []
    found.extend(extract_links_from_text(msg.message or msg.text or ""))
    if msg.entities:
        raw = msg.message or msg.text or ""
        for ent in msg.entities:
            if isinstance(ent, MessageEntityTextUrl) and ent.url:
                found.extend(extract_links_from_text(ent.url))
            elif isinstance(ent, MessageEntityUrl):
                piece = raw[ent.offset: ent.offset + ent.length]
                found.extend(extract_links_from_text(piece))
    markup = getattr(msg, "reply_markup", None)
    if markup and getattr(markup, "rows", None):
        for row in markup.rows:
            for btn in row.buttons:
                url = getattr(btn, "url", None)
                if url:
                    found.extend(extract_links_from_text(url))
    return found


async def wait_or_stop(stop_event: asyncio.Event, seconds: float) -> bool:
    if seconds <= 0:
        return stop_event.is_set()
    try:
        await asyncio.wait_for(stop_event.wait(), timeout=seconds)
        return True
    except asyncio.TimeoutError:
        return False


async def wait_for_all(*events: asyncio.Event, timeout: float) -> str:
    """Wait for any event to be set. Returns which event triggered first."""
    pending = [e.wait() for e in events]
    done, _ = await asyncio.wait(pending, timeout=timeout, return_when=asyncio.FIRST_COMPLETED)
    if not done:
        return "timeout"
    for i, e in enumerate(events):
        if e.is_set():
            return f"event_{i}"
    return "timeout"


def parse_cb_int(data: str, index: int = 2) -> Optional[int]:
    parts = data.split(":")
    if len(parts) <= index:
        return None
    try:
        return int(parts[index])
    except ValueError:
        return None


# ─────────────────────────────────────────────────────────────
# Data Layer
# ─────────────────────────────────────────────────────────────
def blank_data() -> Dict[str, Any]:
    return {
        "version": DATA_VERSION,
        "settings": dict(DEFAULT_SETTINGS),
        "ads": [],
        "groups": [],
    }


def normalize_data(raw: Any) -> Dict[str, Any]:
    data = blank_data()
    if not isinstance(raw, dict):
        return data

    src_set = raw.get("settings") if isinstance(raw.get("settings"), dict) else {}
    merged = dict(DEFAULT_SETTINGS)
    merged.update(src_set)
    for k in BOUNDS:
        merged[k] = clamp_int(merged.get(k), k)
    merged["leave_on_delete"] = as_bool(merged.get("leave_on_delete"), True)
    merged["leave_on_forbidden"] = as_bool(merged.get("leave_on_forbidden"), True)
    data["settings"] = merged

    ads: List[Dict[str, Any]] = []
    seen_ids = set()
    if isinstance(raw.get("ads"), list):
        for item in raw["ads"][:MAX_ADS]:
            if not isinstance(item, dict):
                continue
            aid = as_int(item.get("id"), 0)
            if aid <= 0 or aid in seen_ids:
                continue
            text = item.get("text")
            if not isinstance(text, str) or not text.strip():
                continue
            ads.append({
                "id": aid,
                "text": text[:MAX_AD_LEN],
                "enabled": as_bool(item.get("enabled"), True),
                "sent_ok": max(0, as_int(item.get("sent_ok"), 0)),
            })
            seen_ids.add(aid)
    data["ads"] = ads

    groups: List[Dict[str, Any]] = []
    seen_g = set()
    if isinstance(raw.get("groups"), list):
        for item in raw["groups"][:MAX_GROUPS]:
            if not isinstance(item, dict):
                continue
            gid = as_int(item.get("id"), 0)
            if gid == 0 or gid in seen_g:
                continue
            title = item.get("title") if isinstance(item.get("title"), str) else str(gid)
            status = item.get("last_status") if isinstance(item.get("last_status"), str) else "unknown"
            err = item.get("last_error") if isinstance(item.get("last_error"), str) else ""
            groups.append({
                "id": gid,
                "title": title[:80],
                "enabled": as_bool(item.get("enabled"), True),
                "dead": as_bool(item.get("dead"), False),
                "last_status": status[:40],
                "last_error": err[:80],
                "last_sent": max(0, as_int(item.get("last_sent"), 0)),
                "ok_count": max(0, as_int(item.get("ok_count"), 0)),
                "fail_count": max(0, as_int(item.get("fail_count"), 0)),
            })
            seen_g.add(gid)
    data["groups"] = groups
    return data


def atomic_write(data: Dict[str, Any], data_file: str = DATA_FILE) -> None:
    tmp = data_file + ".tmp"
    payload = dict(data)
    payload["version"] = DATA_VERSION
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, data_file)


def backup_paths(data_file: str = DATA_FILE) -> List[str]:
    return [f"{data_file}.bak{i}" for i in range(1, BACKUP_KEEP + 1)]


def rotate_backup(data_file: str = DATA_FILE) -> None:
    if not os.path.isfile(data_file):
        return
    paths = backup_paths(data_file)
    for i in range(len(paths) - 1, 0, -1):
        src, dst = paths[i - 1], paths[i]
        if os.path.isfile(src):
            shutil.copy2(src, dst)
    shutil.copy2(data_file, paths[0])


def try_load_file(path: str) -> Any:
    if not os.path.isfile(path) or os.path.getsize(path) == 0:
        return None
    with open(path, "r", encoding="utf-8-sig") as f:
        return json.load(f)


def load_data(data_file: str = DATA_FILE) -> Dict[str, Any]:
    errors_found: List[str] = []
    for idx, path in enumerate([data_file] + backup_paths(data_file)):
        try:
            raw = try_load_file(path)
        except Exception as e:
            errors_found.append(f"{os.path.basename(path)}: {e}")
            continue
        if raw is None:
            continue
        data = normalize_data(raw)
        migrated = not (isinstance(raw, dict) and as_int(raw.get("version"), 0) == DATA_VERSION)
        if idx != 0:
            log.warning("بازیابی از %s", os.path.basename(path))
            atomic_write(data, data_file)
        elif migrated or not os.path.isfile(data_file):
            atomic_write(data, data_file)
        return data

    if os.path.isfile(data_file):
        ts = int(time.time())
        corrupt = f"{data_file}.corrupt.{ts}"
        with suppress(OSError):
            os.replace(DATA_FILE, corrupt)
    if errors_found:
        log.error("data.json خراب بود: %s", "; ".join(errors_found))
    data = blank_data()
    atomic_write(data, data_file)
    return data


def protect_session_file(session_base: str) -> None:
    path = session_base if session_base.endswith(".session") else session_base + ".session"
    if os.path.isfile(path):
        with suppress(OSError):
            os.chmod(path, 0o600)


def protect_bot_session_file() -> None:
    protect_session_file(os.path.join(BASE_DIR, BOT_SESSION))


def account_paths(account_id: int) -> Tuple[str, str]:
    root = os.path.join(ACCOUNTS_DIR, f"account_{account_id}")
    os.makedirs(root, exist_ok=True)
    return os.path.join(root, "session"), os.path.join(root, "data.json")


def load_accounts() -> Dict[str, Any]:
    if not os.path.isfile(ACCOUNTS_FILE):
        return {"version": 1, "accounts": []}
    try:
        with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
            raw = json.load(f)
        if isinstance(raw, dict) and isinstance(raw.get("accounts"), list):
            return raw
    except Exception:
        log.exception("accounts.json read failed")
    return {"version": 1, "accounts": []}


def save_accounts(registry: Dict[str, Any]) -> None:
    tmp = ACCOUNTS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(registry, f, ensure_ascii=False, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, ACCOUNTS_FILE)


# ─────────────────────────────────────────────────────────────
# Logging
# ─────────────────────────────────────────────────────────────
class MemoryLogHandler(logging.Handler):
    def __init__(self, buf: Deque[str]) -> None:
        super().__init__()
        self.buf = buf

    def emit(self, record: logging.LogRecord) -> None:
        try:
            self.buf.append(self.format(record))
        except Exception:
            return


def setup_logging(app: "App") -> None:
    log.handlers.clear()
    log.setLevel(logging.INFO)
    log.propagate = False
    fmt = logging.Formatter("%(asctime)s %(levelname)s %(message)s", "%m-%d %H:%M:%S")
    mem = MemoryLogHandler(app.logs)
    mem.setFormatter(fmt)
    fh = RotatingFileHandler(LOG_FILE, maxBytes=262144, backupCount=1, encoding="utf-8")
    fh.setFormatter(fmt)
    sh = logging.StreamHandler()
    sh.setFormatter(fmt)
    log.addHandler(mem)
    log.addHandler(fh)
    log.addHandler(sh)
    logging.getLogger("telethon").setLevel(logging.WARNING)


# ─────────────────────────────────────────────────────────────
# UI Buttons
# ─────────────────────────────────────────────────────────────
def main_buttons() -> list:
    return [
        [Button.inline("📊 وضعیت", b"m:st"), Button.inline("📝 تبلیغات", b"m:ad")],
        [Button.inline("👥 گروه‌ها", b"m:gr"), Button.inline("⚙️ تنظیمات", b"m:se")],
        [Button.inline("▶️ شروع", b"m:go"), Button.inline("⏸ توقف موقت", b"m:pa")],
        [Button.inline("⏹ توقف کامل", b"m:sp"), Button.inline("➕ جوین", b"m:jn")],
        [Button.inline("📋 لاگ‌ها", b"m:lg"), Button.inline("💾 خروجی", b"m:ex")],
        [Button.inline("📥 ورودی", b"m:im")],
    ]


def back_btn() -> list:
    return [Button.inline("◀️ بازگشت", b"m:home")]


def ads_buttons(app: "App", page: int = 0) -> list:
    items = app.ads()
    start = page * PAGE_SIZE
    chunk = items[start:start + PAGE_SIZE]
    rows = []
    for a in chunk:
        flag = "✅" if a["enabled"] else "❌"
        preview = a["text"].replace("\n", " ")[:22]
        rows.append([
            Button.inline(
                f"{flag} #{a['id']} ({a.get('sent_ok', 0)}) {preview}",
                f"a:v:{a['id']}".encode(),
            )
        ])
    nav = []
    if page > 0:
        nav.append(Button.inline("‹", f"a:p:{page-1}".encode()))
    if start + PAGE_SIZE < len(items):
        nav.append(Button.inline("›", f"a:p:{page+1}".encode()))
    if nav:
        rows.append(nav)
    rows.append([Button.inline("➕ افزودن متن", b"a:add")])
    rows.append(back_btn())
    return rows


def ad_view_buttons(aid: int) -> list:
    return [
        [Button.inline("🔛 فعال/غیرفعال", f"a:t:{aid}".encode()),
         Button.inline("✏️ ویرایش", f"a:e:{aid}".encode())],
        [Button.inline("🗑 حذف", f"a:d:{aid}".encode())],
        [Button.inline("◀️ تبلیغات", b"m:ad")],
    ]


def ad_del_confirm(aid: int) -> list:
    return [
        [Button.inline("بله، حذف شود", f"a:x:{aid}".encode()),
         Button.inline("خیر", f"a:v:{aid}".encode())],
    ]


def groups_nav(prefix: str, page: int, total: int) -> list:
    nav = []
    if page > 0:
        nav.append(Button.inline("‹", f"{prefix}{page-1}".encode()))
    if (page + 1) * PAGE_SIZE < total:
        nav.append(Button.inline("›", f"{prefix}{page+1}".encode()))
    return nav


def groups_buttons(app: "App", page: int = 0, items=None, prefix: str = "g:p:") -> list:
    if items is None:
        items = app.groups()
    start = page * PAGE_SIZE
    chunk = items[start:start + PAGE_SIZE]
    rows = []
    for g in chunk:
        mark = "☑️" if g["id"] in app.selected else (
            "💀" if g.get("dead") else ("✅" if g["enabled"] else "❌")
        )
        title = (g.get("title") or str(g["id"]))[:22]
        cb = f"g:s:{g['id']}" if app.select_mode else f"g:v:{g['id']}"
        rows.append([Button.inline(f"{mark} {title}", cb.encode())])
    nav = groups_nav(prefix, page, len(items))
    if nav:
        rows.append(nav)
    sel_n = len(app.selected)
    mode = "روشن" if app.select_mode else "خاموش"
    rows.append([
        Button.inline(f"انتخاب: {mode}", b"g:sm"),
        Button.inline(f"حذف انتخابی ({sel_n})", b"g:ds"),
    ])
    rows.append([
        Button.inline("🔍 جست‌وجو", b"g:qs"),
        Button.inline("💀 مرده‌ها", b"g:dead"),
    ])
    rows.append([
        Button.inline("🧹 بررسی نامعتبر", b"g:cl"),
        Button.inline("🗑 حذف همه", b"g:da"),
    ])
    rows.append(back_btn())
    return rows


def group_view_buttons(gid: int, selected: bool = False) -> list:
    pick = "از انتخاب درآور" if selected else "به انتخاب اضافه کن"
    return [
        [Button.inline("🔛 فعال/غیرفعال", f"g:t:{gid}".encode()),
         Button.inline("♻ زنده کردن", f"g:rv:{gid}".encode())],
        [Button.inline(pick, f"g:tg:{gid}".encode()),
         Button.inline("🚪 لفت/حذف", f"g:l:{gid}".encode())],
        [Button.inline("◀️ گروه‌ها", b"m:gr")],
    ]


def groups_del_all_confirm() -> list:
    return [
        [Button.inline("بله، همه حذف شوند", b"g:dy"),
         Button.inline("خیر", b"m:gr")],
    ]


def groups_del_sel_confirm(n: int) -> list:
    return [
        [Button.inline(f"بله، {n} مورد حذف شود", b"g:dyes"),
         Button.inline("خیر", b"m:gr")],
    ]


def dead_buttons(app: "App", page: int = 0) -> list:
    items = app.dead_groups()
    start = page * PAGE_SIZE
    chunk = items[start:start + PAGE_SIZE]
    rows = []
    for g in chunk:
        title = (g.get("title") or str(g["id"]))[:24]
        rows.append([Button.inline(f"💀 {title}", f"g:v:{g['id']}".encode())])
    nav = groups_nav("g:dp:", page, len(items))
    if nav:
        rows.append(nav)
    rows.append([Button.inline("🗑 پاک کردن مرده‌ها از لیست", b"g:pd")])
    rows.append([Button.inline("◀️ گروه‌ها", b"m:gr")])
    return rows


def settings_buttons(app: "App") -> list:
    s = app.st()
    rows = []
    for key in BOUNDS:
        val = s[key]
        step = SETTING_STEP[key]
        rows.append([Button.inline(f"{SETTING_LABEL[key]}: {val}", b"m:se")])
        rows.append([
            Button.inline(f"-{step}", f"s:-:{key}".encode()),
            Button.inline(f"+{step}", f"s:+:{key}".encode()),
        ])
    ld = "روشن" if s["leave_on_delete"] else "خاموش"
    lf = "روشن" if s["leave_on_forbidden"] else "خاموش"
    rows.append([Button.inline(f"لفت اگر پیام پاک شد: {ld}", b"s:td")])
    rows.append([Button.inline(f"لفت اگر ارسال ممنوع: {lf}", b"s:tf")])
    rows.append(back_btn())
    return rows


# ─────────────────────────────────────────────────────────────
# Text Helpers
# ─────────────────────────────────────────────────────────────
def uptime_str(app: "App") -> str:
    sec = max(0, int(time.time() - app.started_at))
    h, r = divmod(sec, 3600)
    m, s = divmod(r, 60)
    return f"{h:02d}:{m:02d}:{s:02d}"


def status_text(app: "App") -> str:
    s = app.st()
    ok, fail = app.totals()
    op = app.current_op()
    op_txt = OP_LABEL.get(op, "⏹ بیکار")
    ws = app.worker_state
    return (
        "<b>وضعیت</b>\n"
        f"uptime: {esc(uptime_str(app))}\n"
        f"عملیات: {esc(op_txt)}\n"
        f"worker تبلیغ: {esc(ws['ad'])} | جوین: {esc(ws['join'])} | پاکسازی: {esc(ws['clean'])}\n"
        f"گروه‌ها: {len(app.groups())}/{MAX_GROUPS} | فعال {len(app.live_groups())} | مرده {len(app.dead_groups())}\n"
        f"تبلیغ‌ها: {len(app.ads())}/{MAX_ADS} (فعال {len(app.enabled_ads())})\n"
        f"ارسال موفق (پایدار): {ok} | ناموفق: {fail}\n"
        f"runtime ok={app.stats['send_ok']} fail={app.stats['send_fail']} "
        f"retry={app.stats['retries']} flood={app.stats['flood_waits']} "
        f"unknown={app.stats['unknown']} rounds={app.stats['rounds']}\n"
        f"worker crashes={app.stats['worker_crashes']} restarts={app.stats['worker_restarts']}\n"
        f"آخرین خطا: {esc(app.stats['last_error'] or '-')}\n\n"
        f"join_delay={s['join_delay']} send_delay={s['send_delay']}\n"
        f"check_after={s['check_after']} round_wait={s['round_wait']}\n"
        f"scan_limit={s['scan_limit']} join_count={s['default_join_count']}\n"
        f"leave_on_delete={s['leave_on_delete']} leave_on_forbidden={s['leave_on_forbidden']}"
    )


def ads_list_text(app: "App") -> str:
    if not app.ads():
        return "هیچ متنی نیست. «افزودن متن» یا ریپلای + <code>!adadd</code>"
    total_ok = sum(a.get("sent_ok", 0) for a in app.ads())
    return f"<b>تبلیغات</b> — {len(app.ads())}/{MAX_ADS} مورد | مجموع ارسال موفق: {total_ok}"


def groups_list_text(app: "App", items=None, title: str = "گروه‌ها") -> str:
    items = app.groups() if items is None else items
    if not items:
        return "لیستی نیست. از «جوین» یا <code>!join @channel 50</code> استفاده کن."
    extra = f"\nانتخاب‌شده: {len(app.selected)}" if app.selected else ""
    if app.search_query:
        extra += f"\nجست‌وجو: {esc(app.search_query)}"
    return (
        f"<b>{esc(title)}</b> — {len(items)} مورد "
        f"(فعال {len(app.live_groups())} / مرده {len(app.dead_groups())})"
        f"{extra}"
    )


def group_view_text(g: Dict[str, Any]) -> str:
    flag = "مرده" if g.get("dead") else ("فعال" if g["enabled"] else "غیرفعال")
    return (
        f"<b>{esc(g['title'])}</b>\n<code>{g['id']}</code>\n"
        f"وضعیت: {flag}\n"
        f"آخرین وضعیت: {esc(g.get('last_status'))}\n"
        f"آخرین خطا: {esc(g.get('last_error') or '-')}\n"
        f"آخرین ارسال: {esc(format_ts(g.get('last_sent')))}\n"
        f"موفق: {g.get('ok_count', 0)} | ناموفق: {g.get('fail_count', 0)}"
    )


def settings_text() -> str:
    return "<b>تنظیمات</b>\nبا دکمه‌های +/− تغییر بده. ذخیره فوری است."


def logs_text(app: "App") -> str:
    if not app.logs:
        return "لاگی نیست."
    body = "\n".join(list(app.logs)[-15:])
    if len(body) > 3500:
        body = body[-3500:]
    return "<b>لاگ</b>\n<pre>" + esc(body) + "</pre>"


# ─────────────────────────────────────────────────────────────
# App Class
# ─────────────────────────────────────────────────────────────
class App:
    def __init__(self, client: TelegramClient, data_file: str = DATA_FILE) -> None:
        self.client = client
        self.data_file = data_file
        self.data = load_data(data_file)
        self.lock = asyncio.Lock()
        self.start_lock = asyncio.Lock()
        self.ad_task: Optional[asyncio.Task] = None
        self.join_task: Optional[asyncio.Task] = None
        self.clean_task: Optional[asyncio.Task] = None
        self.ad_stop = asyncio.Event()
        self.ad_paused = False
        self.join_stop = asyncio.Event()
        self.clean_stop = asyncio.Event()
        self.pending_by_chat: Dict[int, Dict[str, Any]] = {}
        self.ad_cursor = 0
        self.me = None
        self.notify_chat = None
        self.logs: Deque[str] = deque(maxlen=LOG_KEEP)
        self.selected: Set[int] = set()
        self.select_mode = False
        self.search_query = ""
        self.dirty = False
        self.last_backup = 0.0
        self.started_at = time.time()
        self.shutting_down = False
        self.worker_state = {
            "ad": STATE_STOPPED,
            "join": STATE_STOPPED,
            "clean": STATE_STOPPED,
        }
        self.stats = {
            "send_ok": 0,
            "send_fail": 0,
            "retries": 0,
            "flood_waits": 0,
            "unknown": 0,
            "rounds": 0,
            "worker_crashes": 0,
            "worker_restarts": 0,
            "last_error": "",
            "last_error_time": 0,
        }
        self.cooldowns: Dict[int, float] = {}

    def st(self) -> Dict[str, Any]:
        return self.data["settings"]

    def ads(self) -> List[Dict[str, Any]]:
        return self.data["ads"]

    def groups(self) -> List[Dict[str, Any]]:
        return self.data["groups"]

    def touch(self) -> None:
        self.dirty = True

    async def flush(self, backup: bool = False, force: bool = False) -> None:
        async with self.lock:
            if self.dirty or force:
                try:
                    atomic_write(self.data, self.data_file)
                    self.dirty = False
                    log.info("save")
                except Exception:
                    log.exception("save failed")
                    raise
            now = time.time()
            if backup or (now - self.last_backup >= BACKUP_INTERVAL):
                with suppress(OSError):
                    rotate_backup(self.data_file)
                self.last_backup = now
                if backup:
                    log.info("backup")

    def enabled_ads(self) -> List[Dict[str, Any]]:
        return [a for a in self.ads() if a.get("enabled") and (a.get("text") or "").strip()]

    def live_groups(self) -> List[Dict[str, Any]]:
        now = time.time()
        result = []
        for g in self.groups():
            if not g.get("enabled") or g.get("dead"):
                continue
            cd = self.cooldowns.get(g["id"], 0)
            if cd > now:
                continue
            if cd > 0 and cd <= now:
                self.cooldowns.pop(g["id"], None)
            result.append(g)
        return result

    def dead_groups(self) -> List[Dict[str, Any]]:
        return [g for g in self.groups() if g.get("dead")]

    def current_op(self) -> Optional[str]:
        if running(self.ad_task):
            return "ad"
        if running(self.join_task):
            return "join"
        if running(self.clean_task):
            return "clean"
        return None

    def busy_text(self) -> Optional[str]:
        op = self.current_op()
        if not op:
            return None
        return f"الان «{OP_LABEL[op]}» در حال اجراست. اول !stop"

    def next_ad(self) -> Tuple[Optional[int], Optional[str]]:
        items = self.enabled_ads()
        if not items:
            return None, None
        a = items[self.ad_cursor % len(items)]
        self.ad_cursor += 1
        return a["id"], a["text"]

    def find_ad(self, aid: int) -> Optional[Dict[str, Any]]:
        for a in self.ads():
            if a["id"] == aid:
                return a
        return None

    def find_group(self, gid: int) -> Optional[Dict[str, Any]]:
        for g in self.groups():
            if g["id"] == gid:
                return g
        return None

    def next_ad_id(self) -> int:
        if not self.ads():
            return 1
        return max(a["id"] for a in self.ads()) + 1

    def add_group_mem(self, gid: int, title: str) -> bool:
        if len(self.groups()) >= MAX_GROUPS:
            log.warning("MAX_GROUPS reached, skipping %s", gid)
            return False
        g = self.find_group(gid)
        if g:
            g["title"] = (title or g["title"])[:80]
            g["dead"] = False
            g["enabled"] = True
            g["last_status"] = "joined"
            self.touch()
            return False
        self.data["groups"].append({
            "id": int(gid),
            "title": (title or str(gid))[:80],
            "enabled": True,
            "dead": False,
            "last_status": "joined",
            "last_error": "",
            "last_sent": 0,
            "ok_count": 0,
            "fail_count": 0,
        })
        self.touch()
        return True

    def drop_group(self, gid: int) -> bool:
        before = len(self.data["groups"])
        self.data["groups"] = [g for g in self.data["groups"] if g["id"] != gid]
        self.selected.discard(gid)
        self.cooldowns.pop(gid, None)
        changed = len(self.data["groups"]) != before
        if changed:
            self.touch()
        return changed

    def drop_groups(self, ids: List[int]) -> int:
        idset = set(ids)
        n = sum(1 for g in self.data["groups"] if g["id"] in idset)
        if n:
            self.data["groups"] = [g for g in self.data["groups"] if g["id"] not in idset]
            self.selected -= idset
            for gid in ids:
                self.cooldowns.pop(gid, None)
            self.touch()
        return n

    def cleanup_selection(self) -> None:
        valid_ids = {g["id"] for g in self.groups()}
        self.selected &= valid_ids

    def bump_ok(self, gid: int, ad_id: Optional[int]) -> None:
        g = self.find_group(gid)
        if g:
            g["ok_count"] = g.get("ok_count", 0) + 1
            g["last_sent"] = int(time.time())
            g["last_status"] = "ok"
            g["last_error"] = ""
            g["dead"] = False
        a = self.find_ad(ad_id) if ad_id else None
        if a:
            a["sent_ok"] = a.get("sent_ok", 0) + 1
        self.stats["send_ok"] += 1
        self.cooldowns.pop(gid, None)
        self.touch()

    def bump_fail(self, gid: int, reason: str) -> None:
        g = self.find_group(gid)
        if g:
            g["fail_count"] = g.get("fail_count", 0) + 1
            g["last_sent"] = int(time.time())
            g["last_status"] = "fail"
            g["last_error"] = str(reason)[:80]
        self.stats["send_fail"] += 1
        self.stats["last_error"] = str(reason)[:80]
        self.stats["last_error_time"] = int(time.time())
        self.cooldowns[gid] = time.time() + COOLDOWN_SEC
        self.touch()

    def bump_unconfirmed(self, gid: int, reason: str) -> None:
        g = self.find_group(gid)
        if g:
            g["last_sent"] = int(time.time())
            g["last_status"] = "unconfirmed"
            g["last_error"] = str(reason)[:80]
        self.stats["unknown"] += 1
        self.stats["last_error"] = str(reason)[:80]
        self.stats["last_error_time"] = int(time.time())
        self.touch()

    def totals(self) -> Tuple[int, int]:
        ok = sum(g.get("ok_count", 0) for g in self.groups())
        fail = sum(g.get("fail_count", 0) for g in self.groups())
        return ok, fail

    def set_pending(self, kind: str, chat_id: int, extra: Optional[dict] = None) -> None:
        self.pending_by_chat[chat_id] = {
            "kind": kind,
            "chat_id": chat_id,
            "extra": extra or {},
            "expires": time.monotonic() + PENDING_TTL,
        }

    def take_pending(self, chat_id: int) -> Optional[Dict[str, Any]]:
        p = self.pending_by_chat.pop(chat_id, None)
        if p and time.monotonic() > p["expires"]:
            return None
        return p

    def peek_pending(self, chat_id: int) -> Optional[Dict[str, Any]]:
        p = self.pending_by_chat.get(chat_id)
        if not p:
            return None
        if time.monotonic() > p["expires"]:
            self.pending_by_chat.pop(chat_id, None)
            return None
        return p

    def clear_pending(self, chat_id: Optional[int] = None) -> None:
        if chat_id is not None:
            self.pending_by_chat.pop(chat_id, None)
        else:
            self.pending_by_chat.clear()

    def filter_groups(self, query: str) -> List[Dict[str, Any]]:
        q = (query or "").strip().lower()
        if not q:
            return list(self.groups())
        return [
            g for g in self.groups()
            if q in (g.get("title") or "").lower() or q in str(g["id"])
        ]

    async def notify(self, text: str) -> None:
        chat = self.notify_chat
        if chat is None:
            return
        try:
            await self.client.send_message(chat, text, parse_mode="html")
        except Exception as e:
            log.warning("notify failed: %s", e)

    async def leave_telegram(self, gid: int, stop_event: Optional[asyncio.Event] = None) -> bool:
        try:
            entity = await tg_call(self.client.get_entity(gid))
            try:
                await tg_call(self.client(LeaveChannelRequest(entity)))
            except errors.FloodWaitError as e:
                sec = flood_seconds(e)
                self.stats["flood_waits"] += 1
                log.warning("FloodWait لفت %s ثانیه", sec)
                if sec <= MAX_FLOOD_WAIT:
                    wait_for = stop_event if stop_event else asyncio.Event()
                    if stop_event:
                        evt, _ = await asyncio.wait(
                            [stop_event.wait(), asyncio.sleep(sec)],
                            timeout=sec + 1,
                            return_when=asyncio.FIRST_COMPLETED,
                        )
                        if stop_event.is_set():
                            return False
                    else:
                        await asyncio.sleep(sec)
                    await tg_call(self.client(LeaveChannelRequest(entity)))
                else:
                    log.info("لفت flood too long رد شد: %s", gid)
                    return False
            except errors.UserNotParticipantError:
                return True
            except DEAD_ENTITY_ERRORS:
                return True
            except (errors.ChatForbiddenError, errors.UserKickedError):
                return True
            except Exception:
                await tg_call(self.client.delete_dialog(entity))
            log.info("لفت از %s", gid)
            return True
        except errors.UserNotParticipantError:
            return True
        except DEAD_ENTITY_ERRORS:
            return True
        except errors.FloodWaitError as e:
            self.stats["flood_waits"] += 1
            log.warning("FloodWait لفت-entity %s", flood_seconds(e))
            return False
        except asyncio.TimeoutError:
            log.warning("timeout لفت %s", gid)
            return False
        except Exception as e:
            log.error("خطای لفت %s: %s", gid, e)
            return False

    async def mark_dead(
        self,
        gid: int,
        reason: str,
        do_leave: bool = False,
        stop_event: Optional[asyncio.Event] = None,
    ) -> None:
        g = self.find_group(gid)
        if not g:
            return
        g["dead"] = True
        g["enabled"] = False
        g["last_status"] = "dead"
        g["last_error"] = str(reason)[:80]
        self.touch()
        log.info("گروه مرده %s: %s", gid, reason)
        if do_leave:
            await self.leave_telegram(gid, stop_event)

    async def stop_task(self, name: str) -> None:
        if name == "ad":
            self.ad_stop.set()
            t, self.ad_task = self.ad_task, None
        elif name == "join":
            self.join_stop.set()
            t, self.join_task = self.join_task, None
        else:
            self.clean_stop.set()
            t, self.clean_task = self.clean_task, None
        if t and not t.done():
            t.cancel()
            with suppress(asyncio.CancelledError, Exception):
                await t
        self.worker_state[name] = STATE_STOPPED

    async def shutdown(self) -> None:
        if self.shutting_down:
            return
        self.shutting_down = True
        log.info("shutdown")
        for n in ("ad", "join", "clean"):
            with suppress(Exception):
                await self.stop_task(n)
        with suppress(Exception):
            await self.flush(backup=True, force=True)


# ─────────────────────────────────────────────────────────────
# Workers
# ─────────────────────────────────────────────────────────────
async def join_one(app: App, kind: str, val: str) -> Tuple[str, Any]:
    client = app.client
    if kind == "private":
        try:
            updates = await tg_call(client(ImportChatInviteRequest(val)))
            chat = chat_from_updates(updates)
            return "ok", chat
        except errors.UserAlreadyParticipantError:
            inv = await tg_call(client(CheckChatInviteRequest(val)))
            return "already", getattr(inv, "chat", None)
        except errors.InviteHashExpiredError:
            return "expired", None
        except errors.InviteHashInvalidError:
            return "invalid", None
        except errors.InviteRequestSentError:
            return "approval", None
        except errors.UsersTooMuchError:
            return "full", None
        except errors.ChannelPrivateError:
            return "private", None
        except errors.FloodWaitError as e:
            app.stats["flood_waits"] += 1
            return "flood", None
    try:
        updates = await tg_call(client(JoinChannelRequest(val)))
        chat = chat_from_updates(updates)
        if chat is None:
            chat = await tg_call(client.get_entity(val))
        return "ok", chat
    except errors.UserAlreadyParticipantError:
        chat = await tg_call(client.get_entity(val))
        return "already", chat
    except errors.ChannelPrivateError:
        return "private", None
    except errors.ChannelInvalidError:
        return "invalid", None
    except errors.InviteRequestSentError:
        return "approval", None
    except errors.UsersTooMuchError:
        return "full", None
    except errors.FloodWaitError as e:
        app.stats["flood_waits"] += 1
        return "flood", None


async def join_worker(app: App, channel_input: str, need_count: int, progress_chat: Any, progress_id: int) -> None:
    client = app.client
    s = app.st()
    app.worker_state["join"] = STATE_RUNNING

    async def progress(text: str) -> None:
        try:
            await client.edit_message(progress_chat, progress_id, text)
        except errors.MessageNotModifiedError:
            pass
        except Exception as e:
            log.warning("edit progress: %s", e)

    try:
        await progress(f"اسکن {channel_input} برای {need_count} لینک...")
        try:
            entity = await tg_call(client.get_entity(channel_input))
        except Exception as e:
            await progress(f"کانال پیدا نشد: {e}")
            log.error("کانال نامعتبر %s: %s", channel_input, e)
            app.worker_state["join"] = STATE_FAILED
            return
        if not isinstance(entity, (Channel, Chat)):
            await progress("ورودی باید کانال/گروه باشد.")
            app.worker_state["join"] = STATE_FAILED
            return

        collected: List[Tuple[str, str]] = []
        seen = set()
        async for msg in client.iter_messages(entity, limit=s["scan_limit"]):
            if app.join_stop.is_set():
                await progress("جوین متوقف شد.")
                return
            for kind, val in links_from_message(msg):
                key = (kind, val.lower() if kind == "public" else val)
                if key in seen:
                    continue
                seen.add(key)
                collected.append((kind, val))
                if len(collected) >= need_count:
                    break
            if len(collected) >= need_count:
                break

        collected = collected[:need_count]
        if not collected:
            await progress("هیچ لینکی پیدا نشد.")
            log.info("join: لینکی نبود")
            return

        log.info("join start links=%s", len(collected))
        await progress(f"{len(collected)} لینک. شروع جوین...")

        ok = already = skipped = 0
        total = len(collected)
        for i, (kind, val) in enumerate(collected, 1):
            if app.join_stop.is_set():
                await progress(f"متوقف شد. موفق {ok + already}/{total}")
                return
            status, chat = "fail", None
            try:
                status, chat = await join_one(app, kind, val)
            except errors.FloodWaitError as e:
                sec = flood_seconds(e)
                app.stats["flood_waits"] += 1
                log.warning("FloodWait جوین %s ثانیه", sec)
                await progress(f"FloodWait {sec} ثانیه...")
                if sec > MAX_FLOOD_WAIT:
                    skipped += 1
                    log.info("جوین رد شد flood-too-long")
                elif await wait_or_stop(app.join_stop, sec + 1):
                    await progress("متوقف شد.")
                    return
                else:
                    try:
                        status, chat = await join_one(app, kind, val)
                    except errors.FloodWaitError as e2:
                        app.stats["flood_waits"] += 1
                        log.warning("FloodWait دوباره %s", flood_seconds(e2))
                        status, chat = "flood", None
                    except Exception as e2:
                        log.error("join retry: %s", e2)
                        status, chat = "fail", None
            except asyncio.TimeoutError:
                app.stats["retries"] += 1
                log.warning("timeout جوین")
                status, chat = "fail", None
            except Exception as e:
                log.error("join error: %s", e)
                status, chat = "fail", None

            if status in ("ok", "already") and chat is not None:
                title = get_display_name(chat) or str(getattr(chat, "id", val))
                app.add_group_mem(chat.id, title)
                if i % FLUSH_EVERY == 0:
                    await app.flush()
                if status == "ok":
                    ok += 1
                    log.info("جوین موفق: %s", title)
                else:
                    already += 1
                    log.info("قبلاً عضو: %s", title)
            else:
                skipped += 1
                log.info("جوین رد شد %s", status)

            await progress(
                f"جوین {i}/{total}\nموفق {ok} | تکراری {already} | رد {skipped}"
            )
            if i < total:
                if await wait_or_stop(app.join_stop, s["join_delay"]):
                    await progress(f"متوقف شد. موفق {ok + already}/{total}")
                    return

        await progress(
            f"جوین تمام شد.\nموفق: {ok}\nقبلاً عضو: {already}\nرد شده: {skipped}\n"
            f"ذخیره شده: {len(app.groups())}\nشروع تبلیغ: !start یا دکمه ▶️"
        )
        log.info("join done ok=%s already=%s skip=%s", ok, already, skipped)
        await app.flush(backup=True)
        app.worker_state["join"] = STATE_STOPPED
    except asyncio.CancelledError:
        log.info("join worker cancel")
        app.worker_state["join"] = STATE_STOPPED
        raise
    except Exception:
        log.exception("join worker crash")
        app.worker_state["join"] = STATE_FAILED
        with suppress(Exception):
            await progress("جوین به‌خاطر خطای غیرمنتظره ایستاد. لاگ را ببین.")
    finally:
        with suppress(Exception):
            await app.flush()
        app.join_task = None


async def send_with_retry(app: App, gid: int, text: str) -> Tuple[str, Any, str]:
    client = app.client
    last = "unknown"
    for attempt in range(1, SEND_RETRIES + 1):
        if app.ad_stop.is_set():
            return ERR_STOP, None, last
        try:
            sent = await tg_call(client.send_message(gid, text, parse_mode=None))
            return ERR_SUCCESS, sent, ""
        except asyncio.TimeoutError:
            return ERR_UNKNOWN, None, "Timeout"
        except errors.FloodWaitError as e:
            sec = flood_seconds(e)
            last = f"FloodWait {sec}s"
            app.stats["flood_waits"] += 1
            log.warning("FloodWait ارسال %s ثانیه", sec)
            if sec > MAX_FLOOD_WAIT:
                return ERR_WAIT, None, last
            evt, _ = await asyncio.wait(
                [app.ad_stop.wait(), asyncio.sleep(sec)],
                timeout=sec + 1,
                return_when=asyncio.FIRST_COMPLETED,
            )
            if app.ad_stop.is_set():
                return ERR_STOP, None, last
        except errors.SlowModeWaitError as e:
            sec = min(flood_seconds(e), 120)
            last = f"SlowMode {sec}s"
            log.warning("SlowMode %s : %s", gid, sec)
            evt, _ = await asyncio.wait(
                [app.ad_stop.wait(), asyncio.sleep(sec)],
                timeout=sec + 1,
                return_when=asyncio.FIRST_COMPLETED,
            )
            if app.ad_stop.is_set():
                return ERR_STOP, None, last
        except errors.PeerFloodError:
            return ERR_STOP, None, "PeerFlood"
        except FORBIDDEN_ERRORS as e:
            return ERR_FORBIDDEN, None, type(e).__name__
        except (ConnectionError, OSError) as e:
            last = type(e).__name__
            app.stats["retries"] += 1
            log.warning("خطای موقت ارسال %s: %s", gid, e)
            if attempt >= SEND_RETRIES:
                break
            delay = min(5 * (2 ** (attempt - 1)), 20)
            evt, _ = await asyncio.wait(
                [app.ad_stop.wait(), asyncio.sleep(delay)],
                timeout=delay + 1,
                return_when=asyncio.FIRST_COMPLETED,
            )
            if app.ad_stop.is_set():
                return ERR_STOP, None, last
        except RPCError as e:
            code = getattr(e, "code", None)
            last = type(e).__name__
            if code in (500, 502, 503) or "timeout" in str(e).lower():
                app.stats["retries"] += 1
                log.warning("RPC موقت %s: %s", gid, last)
                if attempt >= SEND_RETRIES:
                    break
                delay = min(5 * (2 ** (attempt - 1)), 20)
                evt, _ = await asyncio.wait(
                    [app.ad_stop.wait(), asyncio.sleep(delay)],
                    timeout=delay + 1,
                    return_when=asyncio.FIRST_COMPLETED,
                )
                if app.ad_stop.is_set():
                    return ERR_STOP, None, last
                continue
            log.error("RPC ارسال %s: %s", gid, e)
            return ERR_SKIP, None, last
        except Exception as e:
            last = type(e).__name__
            msg = str(e).lower()
            log.error("خطای ارسال %s: %s", gid, e)
            if any(x in msg for x in ("banned", "forbidden", "kicked", "not a member", "invalid", "private")):
                return ERR_FORBIDDEN, None, last
            return ERR_SKIP, None, last
    return ERR_SKIP, None, last


async def message_gone(app: App, gid: int, msg_id: int) -> Optional[str]:
    client = app.client
    try:
        got = await tg_call(client.get_messages(gid, ids=msg_id))
        return "gone" if not got else "alive"
    except DEAD_ENTITY_ERRORS:
        return "gone"
    except errors.FloodWaitError as e:
        sec = flood_seconds(e)
        app.stats["flood_waits"] += 1
        log.warning("FloodWait چک %s", sec)
        if sec > MAX_FLOOD_WAIT:
            return "unknown"
        evt, _ = await asyncio.wait(
            [app.ad_stop.wait(), asyncio.sleep(sec)],
            timeout=sec + 1,
            return_when=asyncio.FIRST_COMPLETED,
        )
        if app.ad_stop.is_set():
            return None
        try:
            got = await tg_call(client.get_messages(gid, ids=msg_id))
            return "gone" if not got else "alive"
        except DEAD_ENTITY_ERRORS:
            return "gone"
        except Exception as e2:
            log.warning("چک مجدد %s: %s", gid, e2)
            return "unknown"
    except (asyncio.TimeoutError, ConnectionError, OSError) as e:
        log.warning("چک موقت %s: %s", gid, type(e).__name__)
        return "unknown"
    except Exception as e:
        log.warning("چک پیام %s: %s", gid, e)
        return "unknown"


async def ad_worker(app: App) -> str:
    log.info("تبلیغ‌گر شروع شد")
    await app.notify("تبلیغات <b>شروع</b> شد. توقف: !stop")
    ops = 0
    try:
        while not app.ad_stop.is_set():
            # Pause check — at start of each round
            if app.ad_paused:
                app.worker_state["ad"] = STATE_PAUSED
                log.info("تبلیغ‌گر pause شد")
                while app.ad_paused and not app.ad_stop.is_set():
                    await asyncio.sleep(1)
                if app.ad_stop.is_set():
                    return "stopped"
                app.worker_state["ad"] = STATE_RUNNING
                log.info("تبلیغ‌گر resume شد")

            s = app.st()
            groups = list(app.live_groups())
            if not groups:
                await app.notify("گروه فعالی نیست. تبلیغ‌گر ایستاد.")
                log.info("تبلیغ‌گر: گروه فعال نبود")
                return "empty"
            if not app.enabled_ads():
                await app.notify("متن فعال نیست. تبلیغ‌گر ایستاد.")
                log.info("تبلیغ‌گر: متن فعال نبود")
                return "empty"

            for gid in [g["id"] for g in groups]:
                if app.ad_stop.is_set():
                    return "stopped"
                # Pause check between groups
                if app.ad_paused:
                    app.worker_state["ad"] = STATE_PAUSED
                    while app.ad_paused and not app.ad_stop.is_set():
                        await asyncio.sleep(1)
                    if app.ad_stop.is_set():
                        return "stopped"
                    app.worker_state["ad"] = STATE_RUNNING

                g = app.find_group(gid)
                if not g or not g.get("enabled") or g.get("dead"):
                    continue
                ad_id, text = app.next_ad()
                if not text:
                    await app.notify("متن فعال نماند. ایستاد.")
                    return "empty"

                status, sent, err = await send_with_retry(app, gid, text)
                if status == ERR_STOP:
                    return "stopped"
                if err == "PeerFlood":
                    app.bump_fail(gid, "PeerFlood")
                    log.error("PeerFlood — تبلیغ‌گر متوقف می‌شود")
                    await app.notify("PeerFlood: تلگرام ارسال را بست. تبلیغ‌گر ایستاد.")
                    return "peer_flood"
                if status == ERR_WAIT and "FloodWait" in err:
                    app.bump_fail(gid, err)
                    await app.notify(f"FloodWait طولانی ({esc(err)}). تبلیغ‌گر ایستاد.")
                    return "flood_long"
                if status == ERR_FORBIDDEN:
                    app.bump_fail(gid, err)
                    log.info("ارسال ممنوع %s: %s", gid, err)
                    await app.mark_dead(gid, err, do_leave=bool(s["leave_on_forbidden"]), stop_event=app.ad_stop)
                    ops += 1
                    if ops % FLUSH_EVERY == 0:
                        await app.flush()
                    evt, _ = await asyncio.wait(
                        [app.ad_stop.wait(), asyncio.sleep(s["send_delay"])],
                        timeout=s["send_delay"] + 1,
                        return_when=asyncio.FIRST_COMPLETED,
                    )
                    if app.ad_stop.is_set():
                        return "stopped"
                    continue
                if status == ERR_UNKNOWN:
                    app.bump_unconfirmed(gid, err or "unknown")
                    log.info("ارسال نامشخص %s: %s", gid, err)
                    ops += 1
                    if ops % FLUSH_EVERY == 0:
                        await app.flush()
                    evt, _ = await asyncio.wait(
                        [app.ad_stop.wait(), asyncio.sleep(s["send_delay"])],
                        timeout=s["send_delay"] + 1,
                        return_when=asyncio.FIRST_COMPLETED,
                    )
                    if app.ad_stop.is_set():
                        return "stopped"
                    continue
                if status != ERR_SUCCESS or sent is None:
                    app.bump_fail(gid, err or "send_error")
                    log.info("ارسال ناموفق %s: %s", gid, err)
                    ops += 1
                    if ops % FLUSH_EVERY == 0:
                        await app.flush()
                    evt, _ = await asyncio.wait(
                        [app.ad_stop.wait(), asyncio.sleep(s["send_delay"])],
                        timeout=s["send_delay"] + 1,
                        return_when=asyncio.FIRST_COMPLETED,
                    )
                    if app.ad_stop.is_set():
                        return "stopped"
                    continue

                log.info("ارسال به %s id=%s ad=%s", gid, sent.id, ad_id)
                evt, _ = await asyncio.wait(
                    [app.ad_stop.wait(), asyncio.sleep(s["check_after"])],
                    timeout=s["check_after"] + 1,
                    return_when=asyncio.FIRST_COMPLETED,
                )
                if app.ad_stop.is_set():
                    return "stopped"

                gone = await message_gone(app, gid, sent.id)
                if gone is None:
                    return "stopped"
                if gone == "gone":
                    log.info("پیام پاک شد در %s", gid)
                    app.bump_fail(gid, "deleted")
                    if s["leave_on_delete"]:
                        await app.mark_dead(gid, "deleted", do_leave=True, stop_event=app.ad_stop)
                elif gone == "alive":
                    app.bump_ok(gid, ad_id)
                else:
                    app.bump_unconfirmed(gid, "check_failed")
                    log.info("چک نامشخص %s — موفق شمرده نشد", gid)

                ops += 1
                if ops % FLUSH_EVERY == 0:
                    await app.flush()
                evt, _ = await asyncio.wait(
                    [app.ad_stop.wait(), asyncio.sleep(s["send_delay"])],
                    timeout=s["send_delay"] + 1,
                    return_when=asyncio.FIRST_COMPLETED,
                )
                if app.ad_stop.is_set():
                    return "stopped"

            if app.ad_stop.is_set():
                return "stopped"
            app.stats["rounds"] += 1
            await app.flush()
            log.info("انتظار دور بعد %s ثانیه", app.st()["round_wait"])
            evt, _ = await asyncio.wait(
                [app.ad_stop.wait(), asyncio.sleep(app.st()["round_wait"])],
                timeout=app.st()["round_wait"] + 1,
                return_when=asyncio.FIRST_COMPLETED,
            )
            if app.ad_stop.is_set():
                return "stopped"
        return "stopped"
    finally:
        with suppress(Exception):
            await app.flush(backup=True)
        with suppress(Exception):
            await app.notify("تبلیغات <b>متوقف</b> شد.")
        log.info("تبلیغ‌گر تمام شد")


async def run_ad_supervised(app: App) -> None:
    app.worker_state["ad"] = STATE_RUNNING
    crashes = 0
    try:
        while not app.ad_stop.is_set() and not app.shutting_down:
            try:
                result = await ad_worker(app)
                if result in ("empty", "stopped", "peer_flood", "flood_long"):
                    app.worker_state["ad"] = STATE_STOPPED
                    return
                app.worker_state["ad"] = STATE_STOPPED
                return
            except asyncio.CancelledError:
                app.worker_state["ad"] = STATE_STOPPED
                raise
            except Exception:
                crashes += 1
                app.stats["worker_crashes"] += 1
                app.worker_state["ad"] = STATE_FAILED
                app.stats["last_error"] = "ad_worker crash"
                log.exception("ad crash %s/%s", crashes, MAX_AD_RESTARTS)
                if crashes > MAX_AD_RESTARTS or app.ad_stop.is_set() or app.shutting_down:
                    await app.notify("تبلیغ‌گر بعد از چند crash متوقف شد.")
                    return
                app.worker_state["ad"] = STATE_RESTARTING
                app.stats["worker_restarts"] += 1
                delay = min(15 * crashes, 60)
                log.info("ad restart in %ss", delay)
                evt, _ = await asyncio.wait(
                    [app.ad_stop.wait(), asyncio.sleep(delay)],
                    timeout=delay + 1,
                    return_when=asyncio.FIRST_COMPLETED,
                )
                if app.ad_stop.is_set() or app.shutting_down:
                    app.worker_state["ad"] = STATE_STOPPED
                    return
                app.worker_state["ad"] = STATE_RUNNING
    finally:
        if app.worker_state["ad"] == STATE_RUNNING:
            app.worker_state["ad"] = STATE_STOPPED
        app.ad_task = None


async def clean_worker(app: App, chat_id: Any) -> None:
    log.info("بررسی گروه‌های نامعتبر شروع شد")
    app.worker_state["clean"] = STATE_RUNNING
    marked = 0
    try:
        for g in list(app.groups()):
            if app.clean_stop.is_set():
                break
            if g.get("dead"):
                continue
            gid = g["id"]
            try:
                await tg_call(app.client.get_entity(gid))
            except errors.FloodWaitError as e:
                sec = flood_seconds(e)
                app.stats["flood_waits"] += 1
                log.warning("FloodWait clean %s", sec)
                if sec > MAX_FLOOD_WAIT or await wait_or_stop(app.clean_stop, sec + 1):
                    break
                try:
                    await tg_call(app.client.get_entity(gid))
                except Exception as e2:
                    await app.mark_dead(gid, type(e2).__name__, do_leave=False)
                    marked += 1
            except DEAD_ENTITY_ERRORS as e:
                await app.mark_dead(gid, type(e).__name__, do_leave=False)
                marked += 1
            except (asyncio.TimeoutError, ValueError) as e:
                log.warning("clean %s: %s", gid, type(e).__name__)
            except Exception as e:
                log.warning("clean %s: %s", gid, e)
            await asyncio.sleep(1)
        await app.client.send_message(chat_id, f"بررسی تمام شد. علامت مرده: {marked}")
        log.info("clean done marked=%s", marked)
        await app.flush(backup=True)
        app.worker_state["clean"] = STATE_STOPPED
    except asyncio.CancelledError:
        app.worker_state["clean"] = STATE_STOPPED
        raise
    except Exception:
        log.exception("clean crash")
        app.worker_state["clean"] = STATE_FAILED
    finally:
        app.clean_task = None


async def start_ads(app: App, chat_id: Any) -> Tuple[bool, str]:
    async with app.start_lock:
        if running(app.ad_task):
            ws = app.worker_state.get("ad")
            if ws == STATE_PAUSED:
                return False, "تبلیغ‌گر قبلاً pause شده. از !resume استفاده کن."
            return False, app.busy_text() or "تبلیغ‌گر در حال اجراست."
        if not app.enabled_ads():
            return False, "حداقل یک متن فعال بگذار."
        if not app.live_groups():
            return False, "گروه فعالی نیست. اول جوین کن."
        app.ad_stop = asyncio.Event()
        app.ad_paused = False
        app.notify_chat = chat_id
        app.worker_state["ad"] = STATE_RUNNING
        app.ad_task = asyncio.create_task(run_ad_supervised(app))
        log.info("ad start")
        return True, "تبلیغ‌گر شروع شد."


async def start_join(app: App, channel: str, count: int, chat_id: Any, msg_id: int) -> Tuple[bool, Optional[str]]:
    async with app.start_lock:
        if running(app.join_task):
            return False, app.busy_text() or "جوین در حال اجراست."
        app.join_stop = asyncio.Event()
        app.worker_state["join"] = STATE_RUNNING
        app.join_task = asyncio.create_task(
            join_worker(app, channel, count, chat_id, msg_id)
        )
        log.info("join start")
        return True, None


async def start_clean(app: App, chat_id: Any) -> Tuple[bool, str]:
    async with app.start_lock:
        if running(app.clean_task):
            return False, app.busy_text() or "پاکسازی در حال اجراست."
        app.clean_stop = asyncio.Event()
        app.worker_state["clean"] = STATE_RUNNING
        app.clean_task = asyncio.create_task(clean_worker(app, chat_id))
        log.info("clean start")
        return True, "بررسی نامعتبرها شروع شد."


async def pause_ad(app: App) -> Tuple[bool, str]:
    if not running(app.ad_task):
        return False, "تبلیغ‌گر در حال اجرا نیست."
    if app.ad_paused:
        return False, "تبلیغ‌گر قبلاً pause شده."
    app.ad_paused = True
    return True, "تبلیغ‌گر pause شد. از !resume ادامه بده."


async def resume_ad(app: App) -> Tuple[bool, str]:
    if not running(app.ad_task):
        return False, "تبلیغ‌گر در حال اجرا نیست."
    if not app.ad_paused:
        return False, "تبلیغ‌گر pause نیست."
    app.ad_paused = False
    return True, "تبلیغ‌گر resume شد."


# ─────────────────────────────────────────────────────────────
# Command Parsers
# ─────────────────────────────────────────────────────────────
def parse_join_args(text: str, default_count: int) -> Tuple[Optional[str], Optional[int], Optional[str]]:
    parts = text.split()
    if len(parts) < 2:
        return None, None, "فرمت: !join @channel 50"
    channel = parts[1].strip()
    if not (channel.startswith("https://") or channel.startswith("http://") or channel.startswith("@")):
        channel = "@" + channel.lstrip("@")
    if len(parts) >= 3:
        try:
            count = int(parts[2])
        except ValueError:
            return None, None, "تعداد باید عدد باشد."
    else:
        count = default_count
    count = max(1, min(200, count))
    return channel, count, None


def parse_ids(parts: List[str]) -> Optional[List[int]]:
    ids = []
    for p in parts:
        try:
            ids.append(int(p))
        except ValueError:
            return None
    return ids


HELP = (
    "<b>دستورها</b>\n"
    "<code>!menu</code> منو\n"
    "<code>!join @channel 50</code> جوین\n"
    "<code>!start</code> / <code>!stop</code>\n"
    "<code>!pause</code> / <code>!resume</code>\n"
    "<code>!status</code> وضعیت و آمار\n"
    "<code>!adadd</code> افزودن متن (یا ریپلای)\n"
    "<code>!adset ID</code> ویرایش متن (یا ریپلای)\n"
    "<code>!gsearch متن</code> جست‌وجوی گروه\n"
    "<code>!gdel id1 id2</code> حذف چند گروه از لیست\n"
    "<code>!export</code> / <code>!import</code>\n"
    "<code>!backup</code> نسخه پشتیبان فوری\n"
    "<code>!logs</code> لاگ\n"
    "<code>!cancel</code> لغو ورودی\n"
    "<code>!help</code>"
)


# ─────────────────────────────────────────────────────────────
# Event Handlers
# ─────────────────────────────────────────────────────────────
def register(app: App) -> None:
    client = app.client

    async def add_ad_from_text(event: Any, body: str) -> None:
        body = (body or "").strip()
        if not body:
            await event.reply("متن خالی است.")
            return
        if len(app.ads()) >= MAX_ADS:
            await event.reply("ظرفیت متن پر است.")
            return
        aid = app.next_ad_id()
        app.ads().append({"id": aid, "text": body[:MAX_AD_LEN], "enabled": True, "sent_ok": 0})
        app.touch()
        await app.flush(backup=True)
        log.info("متن #%s اضافه شد", aid)
        await event.reply(f"متن #{aid} اضافه شد.", buttons=ad_view_buttons(aid))

    async def apply_ad_edit(event: Any, aid: int, body: str) -> None:
        ad = app.find_ad(aid)
        if not ad:
            await event.reply("متن پیدا نشد.")
            return
        body = (body or "").strip()
        if not body:
            await event.reply("متن خالی است.")
            return
        ad["text"] = body[:MAX_AD_LEN]
        app.touch()
        await app.flush()
        log.info("متن #%s ویرایش شد", aid)
        await event.reply(f"متن #{aid} ویرایش شد.\nارسال موفق این متن: {ad.get('sent_ok', 0)}")

    async def handle_import_bytes(event: Any, raw: bytes) -> None:
        try:
            obj = json.loads(raw.decode("utf-8-sig"))
        except Exception as e:
            await event.reply(f"JSON نامعتبر: {e}")
            return
        data = normalize_data(obj)
        if len(data["groups"]) > MAX_GROUPS:
            data["groups"] = data["groups"][:MAX_GROUPS]
            log.warning("Import truncated to MAX_GROUPS=%s", MAX_GROUPS)
        if len(data["ads"]) > MAX_ADS:
            data["ads"] = data["ads"][:MAX_ADS]
            log.warning("Import truncated to MAX_ADS=%s", MAX_ADS)
        app.data = data
        app.selected.clear()
        app.cleanup_selection()
        app.touch()
        await app.flush(backup=True, force=True)
        log.info("import ads=%s groups=%s", len(app.ads()), len(app.groups()))
        await event.reply(
            f"وارد شد.\nتبلیغ: {len(app.ads())}\nگروه: {len(app.groups())}",
            buttons=main_buttons(),
        )

    @client.on(events.NewMessage(outgoing=True))
    async def on_out(event: Any) -> None:
        text = (event.raw_text or "").strip()
        chat_id = event.chat_id
        peeked = app.peek_pending(chat_id)

        if peeked and peeked["kind"] == "import" and event.document:
            app.take_pending(chat_id)
            if app.current_op():
                await event.reply(app.busy_text())
                return
            size = int(getattr(event.document, "size", 0) or 0)
            if size <= 0 or size > IMPORT_MAX_BYTES:
                await event.reply("فایل بزرگ‌تر از 512KB یا خالی است.")
                return
            blob = await client.download_media(event.media, file=bytes)
            if not blob:
                await event.reply("دانلود نشد.")
                return
            await handle_import_bytes(event, blob)
            return

        if not text:
            return

        if peeked and text.lower() in ("!cancel", "/cancel"):
            app.clear_pending(chat_id)
            await event.reply("لغو شد.")
            return

        pending = None
        if peeked and not text.startswith("!"):
            pending = app.take_pending(chat_id)

        if pending:
            kind = pending["kind"]
            if kind == "ad_add":
                await add_ad_from_text(event, text)
                return
            if kind == "ad_edit":
                await apply_ad_edit(event, int(pending["extra"]["id"]), text)
                return
            if kind == "join":
                channel, count, err = parse_join_args("!join " + text, app.st()["default_join_count"])
                if err:
                    await event.reply(err)
                    return
                status = await event.reply(f"جوین {channel} × {count} ...")
                ok, msg = await start_join(app, channel, count, chat_id, status.id)
                if not ok:
                    await status.edit(msg)
                return
            if kind == "gsearch":
                app.search_query = text[:80]
                items = app.filter_groups(app.search_query)
                await event.reply(
                    groups_list_text(app, items, "نتیجه جست‌وجو"),
                    buttons=groups_buttons(app, 0, items, prefix="g:sp:"),
                    parse_mode="html",
                )
                return
            if kind == "import":
                await event.reply("یک فایل JSON بفرست. لغو: !cancel")
                app.set_pending("import", chat_id)
                return
            return

        low = text.split()[0].lower()
        if low == "!cancel":
            app.clear_pending(chat_id)
            await event.reply("لغو شد.")
            return
        if low in ("!menu", "!panel"):
            await send_panel(client, chat_id)
            return
        if low == "!help":
            await event.reply(HELP, parse_mode="html")
            return
        if low in ("!status", "!stats"):
            await event.reply(status_text(app), buttons=main_buttons(), parse_mode="html")
            return
        if low == "!logs":
            await event.reply(logs_text(app), parse_mode="html")
            return
        if low == "!start":
            ok, msg = await start_ads(app, chat_id)
            await event.reply(msg)
            return
        if low == "!stop":
            was = app.current_op()
            await app.stop_task("ad")
            await app.stop_task("join")
            await app.stop_task("clean")
            await event.reply("توقف ارسال شد." if was else "چیزی در حال اجرا نبود.")
            log.info("stop دستی")
            return
        if low == "!pause":
            ok, msg = await pause_ad(app)
            await event.reply(msg)
            return
        if low == "!resume":
            ok, msg = await resume_ad(app)
            await event.reply(msg)
            return
        if low == "!join":
            channel, count, err = parse_join_args(text, app.st()["default_join_count"])
            if err:
                await event.reply(err)
                return
            status = await event.reply(f"جوین {channel} × {count} ...")
            ok, msg = await start_join(app, channel, count, chat_id, status.id)
            if not ok:
                await status.edit(msg)
            return
        if low == "!adadd":
            if event.is_reply:
                src = await event.get_reply_message()
                body = (src.raw_text or "").strip() if src else ""
                await add_ad_from_text(event, body)
                return
            app.set_pending("ad_add", chat_id)
            await event.reply("متن تبلیغ را بفرست. لغو: !cancel")
            return
        if low == "!adset":
            parts = text.split(maxsplit=1)
            if len(parts) < 2:
                await event.reply("فرمت: <code>!adset 1</code> و متن جدید (یا ریپلای)", parse_mode="html")
                return
            rest = parts[1].strip()
            bits = rest.split(maxsplit=1)
            try:
                aid = int(bits[0])
            except ValueError:
                await event.reply("شناسه متن باید عدد باشد.")
                return
            body = bits[1] if len(bits) > 1 else ""
            if not body and event.is_reply:
                src = await event.get_reply_message()
                body = (src.raw_text or "").strip() if src else ""
            if body:
                await apply_ad_edit(event, aid, body)
                return
            app.set_pending("ad_edit", chat_id, {"id": aid})
            await event.reply(f"متن کامل جدید برای #{aid} را بفرست. لغو: !cancel")
            return
        if low == "!ads":
            await event.reply(ads_list_text(app), buttons=ads_buttons(app, 0), parse_mode="html")
            return
        if low == "!groups":
            app.search_query = ""
            await event.reply(groups_list_text(app), buttons=groups_buttons(app, 0), parse_mode="html")
            return
        if low in ("!gsearch", "!search"):
            q = text.split(maxsplit=1)[1] if len(text.split(maxsplit=1)) > 1 else ""
            if not q:
                app.set_pending("gsearch", chat_id)
                await event.reply("عبارت جست‌وجو را بفرست. لغو: !cancel")
                return
            app.search_query = q[:80]
            items = app.filter_groups(app.search_query)
            await event.reply(
                groups_list_text(app, items, "نتیجه جست‌وجو"),
                buttons=groups_buttons(app, 0, items, prefix="g:sp:"),
                parse_mode="html",
            )
            return
        if low == "!gdel":
            ids = parse_ids(text.split()[1:])
            if not ids:
                await event.reply("فرمت: <code>!gdel -1001 -1002</code>", parse_mode="html")
                return
            n = app.drop_groups(ids)
            await app.flush()
            log.info("حذف چندتایی n=%s", n)
            await event.reply(f"{n} گروه از لیست حذف شد.")
            return
        if low == "!dead":
            items = app.dead_groups()
            await event.reply(
                groups_list_text(app, items, "گروه‌های مرده"),
                buttons=dead_buttons(app, 0),
                parse_mode="html",
            )
            return
        if low == "!export":
            await app.flush(force=True)
            await client.send_file(chat_id, app.data_file, caption="data.json")
            log.info("export")
            return
        if low == "!import":
            if app.current_op():
                await event.reply(app.busy_text())
                return
            if event.is_reply:
                src = await event.get_reply_message()
                if src and src.document:
                    size = int(getattr(src.document, "size", 0) or 0)
                    if size <= 0 or size > IMPORT_MAX_BYTES:
                        await event.reply("فایل بزرگ‌تر از 512KB یا خالی است.")
                        return
                    blob = await client.download_media(src.media, file=bytes)
                    await handle_import_bytes(event, blob)
                    return
            app.set_pending("import", chat_id)
            await event.reply("فایل JSON را همین‌جا بفرست. لغو: !cancel")
            return
        if low == "!backup":
            await app.flush(backup=True, force=True)
            await event.reply("نسخه پشتیبان گرفته شد (bak1..bak3).")
            log.info("backup دستی")
            return

    @client.on(events.CallbackQuery)
    async def on_cb(event: Any) -> None:
        if app.me and event.sender_id != app.me.id:
            await event.answer("اجازه نداری.", alert=True)
            return
        data = event.data.decode("utf-8", "ignore")
        answered = False

        async def ack(text: Optional[str] = None, alert: bool = False) -> None:
            nonlocal answered
            if answered:
                return
            answered = True
            if text:
                await event.answer(text, alert=alert)
            else:
                await event.answer()

        if data in ("m:home",):
            await ack()
            await edit_or_answer(event, "<b>کنترل</b>", main_buttons())
            return
        if data == "m:st":
            await ack()
            await edit_or_answer(event, status_text(app), main_buttons())
            return
        if data == "m:ad":
            await ack()
            await edit_or_answer(event, ads_list_text(app), ads_buttons(app, 0))
            return
        if data == "m:gr":
            await ack()
            app.search_query = ""
            await edit_or_answer(event, groups_list_text(app), groups_buttons(app, 0))
            return
        if data == "m:se":
            await ack()
            await edit_or_answer(event, settings_text(), settings_buttons(app))
            return
        if data == "m:lg":
            await ack()
            await edit_or_answer(event, logs_text(app), [back_btn()])
            return
        if data == "m:go":
            await ack()
            ok, msg = await start_ads(app, event.chat_id)
            await edit_or_answer(event, esc(msg) + "\n\n" + status_text(app), main_buttons())
            return
        if data == "m:sp":
            await ack()
            await app.stop_task("ad")
            await app.stop_task("join")
            await app.stop_task("clean")
            log.info("stop از منو")
            await edit_or_answer(event, "توقف ارسال شد.\n\n" + status_text(app), main_buttons())
            return
        if data == "m:pa":
            await ack()
            ok, msg = await pause_ad(app)
            await edit_or_answer(event, esc(msg) + "\n\n" + status_text(app), main_buttons())
            return
        if data == "m:jn":
            if running(app.join_task):
                await ack(app.busy_text() or "", alert=True)
                return
            await ack()
            app.set_pending("join", event.chat_id)
            await edit_or_answer(event, "بفرست: <code>@channel 50</code>\nلغو: !cancel", [back_btn()])
            return
        if data == "m:ex":
            await ack()
            await app.flush(force=True)
            await client.send_file(event.chat_id, app.data_file, caption="data.json")
            log.info("export از منو")
            return
        if data == "m:im":
            if app.current_op():
                await ack(app.busy_text() or "", alert=True)
                return
            await ack()
            app.set_pending("import", event.chat_id)
            await edit_or_answer(event, "فایل JSON را بفرست. لغو: !cancel", [back_btn()])
            return

        if data.startswith("a:p:"):
            page = parse_cb_int(data)
            if page is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            await edit_or_answer(event, ads_list_text(app), ads_buttons(app, page))
            return
        if data == "a:add":
            if len(app.ads()) >= MAX_ADS:
                await ack("ظرفیت پر است", alert=True)
                return
            await ack()
            app.set_pending("ad_add", event.chat_id)
            await edit_or_answer(event, "متن تبلیغ را بفرست. لغو: !cancel", [back_btn()])
            return
        if data.startswith("a:v:"):
            aid = parse_cb_int(data)
            if aid is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            ad = app.find_ad(aid)
            if not ad:
                await edit_or_answer(event, "پیدا نشد.", ads_buttons(app, 0))
                return
            flag = "فعال" if ad["enabled"] else "غیرفعال"
            await edit_or_answer(
                event,
                f"<b>متن #{aid}</b> ({flag})\nارسال موفق: {ad.get('sent_ok', 0)}\n\n{esc(ad['text'][:1500])}",
                ad_view_buttons(aid),
            )
            return
        if data.startswith("a:t:"):
            aid = parse_cb_int(data)
            ad = app.find_ad(aid) if aid is not None else None
            if not ad:
                await ack("پیدا نشد", alert=True)
                return
            await ack()
            ad["enabled"] = not ad["enabled"]
            app.touch()
            await app.flush()
            log.info("متن #%s enabled=%s", aid, ad["enabled"])
            flag = "فعال" if ad["enabled"] else "غیرفعال"
            await edit_or_answer(
                event,
                f"<b>متن #{aid}</b> ({flag})\nارسال موفق: {ad.get('sent_ok', 0)}\n\n{esc(ad['text'][:1500])}",
                ad_view_buttons(aid),
            )
            return
        if data.startswith("a:e:"):
            aid = parse_cb_int(data)
            if aid is None or not app.find_ad(aid):
                await ack("پیدا نشد", alert=True)
                return
            await ack()
            app.set_pending("ad_edit", event.chat_id, {"id": aid})
            await edit_or_answer(
                event,
                f"متن کامل جدید برای #{aid} را همین حالا بفرست.\n"
                f"یا ریپلای + <code>!adset {aid}</code>\nلغو: !cancel",
                [back_btn()],
            )
            return
        if data.startswith("a:d:"):
            aid = parse_cb_int(data)
            if aid is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            await edit_or_answer(event, f"حذف متن #{aid}؟", ad_del_confirm(aid))
            return
        if data.startswith("a:x:"):
            aid = parse_cb_int(data)
            if aid is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            app.data["ads"] = [a for a in app.ads() if a["id"] != aid]
            app.touch()
            await app.flush(backup=True)
            log.info("متن #%s حذف شد", aid)
            await edit_or_answer(event, f"متن #{aid} حذف شد.", ads_buttons(app, 0))
            return

        if data.startswith("g:p:"):
            page = parse_cb_int(data)
            if page is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            app.search_query = ""
            await edit_or_answer(event, groups_list_text(app), groups_buttons(app, page))
            return
        if data.startswith("g:sp:"):
            page = parse_cb_int(data)
            if page is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            items = app.filter_groups(app.search_query)
            await edit_or_answer(
                event,
                groups_list_text(app, items, "نتیجه جست‌وجو"),
                groups_buttons(app, page, items, prefix="g:sp:"),
            )
            return
        if data.startswith("g:dp:"):
            page = parse_cb_int(data)
            if page is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            items = app.dead_groups()
            await edit_or_answer(
                event,
                groups_list_text(app, items, "گروه‌های مرده"),
                dead_buttons(app, page),
            )
            return
        if data == "g:dead":
            await ack()
            items = app.dead_groups()
            await edit_or_answer(
                event,
                groups_list_text(app, items, "گروه‌های مرده"),
                dead_buttons(app, 0),
            )
            return
        if data == "g:pd":
            await ack()
            ids = [g["id"] for g in app.dead_groups()]
            n = app.drop_groups(ids)
            await app.flush(backup=True)
            log.info("پاک کردن مرده‌ها n=%s", n)
            await edit_or_answer(event, f"{n} گروه مرده از لیست حذف شد.", groups_buttons(app, 0))
            return
        if data == "g:sm":
            await ack()
            app.select_mode = not app.select_mode
            await edit_or_answer(event, groups_list_text(app), groups_buttons(app, 0))
            return
        if data.startswith("g:s:"):
            gid = parse_cb_int(data)
            if gid is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            if gid in app.selected:
                app.selected.discard(gid)
            else:
                app.selected.add(gid)
            items = app.filter_groups(app.search_query) if app.search_query else None
            prefix = "g:sp:" if app.search_query else "g:p:"
            await edit_or_answer(
                event,
                groups_list_text(app, items),
                groups_buttons(app, 0, items, prefix=prefix),
            )
            return
        if data.startswith("g:tg:"):
            gid = parse_cb_int(data)
            if gid is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            if gid in app.selected:
                app.selected.discard(gid)
            else:
                app.selected.add(gid)
            g = app.find_group(gid)
            if not g:
                return
            await edit_or_answer(event, group_view_text(g), group_view_buttons(gid, gid in app.selected))
            return
        if data.startswith("g:v:"):
            gid = parse_cb_int(data)
            if gid is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            g = app.find_group(gid)
            if not g:
                await edit_or_answer(event, "پیدا نشد.", groups_buttons(app, 0))
                return
            await edit_or_answer(event, group_view_text(g), group_view_buttons(gid, gid in app.selected))
            return
        if data.startswith("g:t:"):
            gid = parse_cb_int(data)
            g = app.find_group(gid) if gid is not None else None
            if not g:
                await ack("پیدا نشد", alert=True)
                return
            await ack()
            if g.get("dead") and not g["enabled"]:
                g["dead"] = False
            g["enabled"] = not g["enabled"]
            app.touch()
            await app.flush()
            await edit_or_answer(event, group_view_text(g), group_view_buttons(gid, gid in app.selected))
            return
        if data.startswith("g:rv:"):
            gid = parse_cb_int(data)
            g = app.find_group(gid) if gid is not None else None
            if not g:
                await ack("پیدا نشد", alert=True)
                return
            await ack()
            try:
                ent = await tg_call(client.get_entity(gid))
                g["title"] = (get_display_name(ent) or g["title"])[:80]
                g["dead"] = False
                g["enabled"] = True
                g["last_status"] = "revived"
                g["last_error"] = ""
                app.touch()
                await app.flush()
                log.info("revive %s", gid)
            except Exception as e:
                g["dead"] = True
                g["enabled"] = False
                g["last_error"] = type(e).__name__[:80]
                app.touch()
                await app.flush()
                log.info("revive fail %s: %s", gid, type(e).__name__)
            await edit_or_answer(event, group_view_text(g), group_view_buttons(gid, gid in app.selected))
            return
        if data.startswith("g:l:"):
            gid = parse_cb_int(data)
            if gid is None:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            stop_ev = app.ad_stop if running(app.ad_task) else None
            await app.leave_telegram(gid, stop_ev)
            app.drop_group(gid)
            await app.flush()
            log.info("حذف/لفت %s", gid)
            await edit_or_answer(event, f"حذف/لفت {gid} انجام شد.", groups_buttons(app, 0))
            return
        if data == "g:ds":
            n = len(app.selected)
            if n == 0:
                await ack("چیزی انتخاب نشده", alert=True)
                return
            await ack()
            await edit_or_answer(
                event,
                f"{n} گروه از لیست حذف شود؟ (لفت نمی‌شود)",
                groups_del_sel_confirm(n),
            )
            return
        if data == "g:dyes":
            await ack()
            n = app.drop_groups(list(app.selected))
            app.selected.clear()
            await app.flush(backup=True)
            log.info("حذف انتخابی n=%s", n)
            await edit_or_answer(event, f"{n} گروه از لیست حذف شد.", groups_buttons(app, 0))
            return
        if data == "g:da":
            await ack()
            await edit_or_answer(event, "همه گروه‌ها از لیست حذف شوند؟ (لفت نمی‌شود)", groups_del_all_confirm())
            return
        if data == "g:dy":
            await ack()
            n = len(app.groups())
            app.data["groups"] = []
            app.selected.clear()
            app.touch()
            await app.flush(backup=True)
            log.info("همه گروه‌ها پاک شدند n=%s", n)
            await edit_or_answer(event, f"{n} گروه از لیست حذف شد.", groups_buttons(app, 0))
            return
        if data == "g:cl":
            ok, msg = await start_clean(app, event.chat_id)
            if not ok:
                await ack(msg, alert=True)
                return
            await ack()
            await edit_or_answer(event, esc(msg), groups_buttons(app, 0))
            return
        if data == "g:qs":
            await ack()
            app.set_pending("gsearch", event.chat_id)
            await edit_or_answer(event, "عبارت جست‌وجو را بفرست. لغو: !cancel", [back_btn()])
            return

        if data.startswith("s:+:") or data.startswith("s:-:"):
            parts = data.split(":")
            if len(parts) != 3 or parts[2] not in BOUNDS:
                await ack("داده نامعتبر", alert=True)
                return
            await ack()
            sign, key = parts[1], parts[2]
            step = SETTING_STEP[key]
            cur = app.st()[key]
            app.st()[key] = clamp_int(cur + (step if sign == "+" else -step), key)
            app.touch()
            await app.flush()
            log.info("setting %s=%s", key, app.st()[key])
            await edit_or_answer(event, settings_text(), settings_buttons(app))
            return
        if data == "s:td":
            await ack()
            app.st()["leave_on_delete"] = not app.st()["leave_on_delete"]
            app.touch()
            await app.flush()
            await edit_or_answer(event, settings_text(), settings_buttons(app))
            return
        if data == "s:tf":
            await ack()
            app.st()["leave_on_forbidden"] = not app.st()["leave_on_forbidden"]
            app.touch()
            await app.flush()
            await edit_or_answer(event, settings_text(), settings_buttons(app))
            return

        await ack()


async def edit_or_answer(event: Any, text: str, buttons=None) -> None:
    try:
        await event.edit(text, buttons=buttons, parse_mode="html")
    except errors.MessageNotModifiedError:
        pass
    except (errors.MessageIdInvalidError, errors.MessageAuthorRequiredError):
        await event.respond(text, buttons=buttons, parse_mode="html")


async def send_panel(client: TelegramClient, chat: Any, text: Optional[str] = None) -> None:
    await client.send_message(
        chat,
        text or "<b>کنترل</b>",
        buttons=main_buttons(),
        parse_mode="html",
    )


# ─────────────────────────────────────────────────────────────
# ─────────────────────────────────────────────────────────────
# Multi-account login / control bot
# ─────────────────────────────────────────────────────────────
class MultiAccountManager:
    """One control Bot, one API ID/Hash, and independent User sessions."""
    def __init__(self, bot: TelegramClient) -> None:
        self.bot = bot
        self.registry = load_accounts()
        self.apps: Dict[int, App] = {}
        self.clients: Dict[int, TelegramClient] = {}
        self.login_states: Dict[int, Dict[str, Any]] = {}
        self.next_id = max([as_int(a.get("id"), 0) for a in self.registry.get("accounts", [])] + [0]) + 1

    def allowed(self, event: Any) -> bool:
        # Each Telegram user may use the bot to connect their own User Account.
        # Keep the login state isolated by sender_id. For a private control bot,
        # this lets several accounts onboard independently.
        return bool(getattr(event, "is_private", True))

    async def reply(self, event: Any, text: str) -> None:
        await event.reply(text, parse_mode="html")

    def account_entry(self, account_id: int) -> Optional[Dict[str, Any]]:
        for item in self.registry.get("accounts", []):
            if as_int(item.get("id"), 0) == account_id:
                return item
        return None

    def create_account(self) -> Tuple[int, str, str]:
        account_id = self.next_id
        self.next_id += 1
        session_base, data_file = account_paths(account_id)
        self.registry.setdefault("accounts", []).append({
            "id": account_id,
            "session": os.path.relpath(session_base, BASE_DIR),
            "data": os.path.relpath(data_file, BASE_DIR),
            "user_id": 0,
            "name": "",
            "phone": "",
        })
        save_accounts(self.registry)
        return account_id, session_base, data_file

    async def restore_existing(self) -> None:
        for item in list(self.registry.get("accounts", [])):
            account_id = as_int(item.get("id"), 0)
            if account_id <= 0:
                continue
            session_rel = item.get("session") or os.path.join("accounts", f"account_{account_id}", "session")
            data_rel = item.get("data") or os.path.join("accounts", f"account_{account_id}", "data.json")
            session_base = os.path.join(BASE_DIR, session_rel)
            data_file = os.path.join(BASE_DIR, data_rel)
            if not os.path.isfile(session_base + ".session"):
                continue
            try:
                client = TelegramClient(session_base, API_ID, API_HASH)
                app = App(client, data_file=data_file)
                await client.connect()
                if not await client.is_user_authorized():
                    await client.disconnect()
                    continue
                app.me = await client.get_me()
                self.clients[account_id] = client
                self.apps[account_id] = app
                protect_session_file(session_base)
                register(app)
                item["user_id"] = int(app.me.id)
                item["name"] = get_display_name(app.me) or ""
                item["phone"] = getattr(app.me, "phone", "") or ""
                save_accounts(self.registry)
                log.info("restored account=%s user_id=%s", account_id, app.me.id)
            except Exception:
                log.exception("restore account=%s failed", account_id)

    async def install_handlers(self) -> None:
        @self.bot.on(events.NewMessage(incoming=True))
        async def on_message(event: Any) -> None:
            if not self.allowed(event):
                return
            text = (event.raw_text or "").strip()
            if not text:
                return
            uid = int(event.sender_id)

            if text in ("/start", "/help"):
                await self.reply(event,
                    "<b>🤖 مدیریت اتصال اکانت‌ها</b>\n\n"
                    "➕ <code>/add</code> — اتصال اکانت جدید\n"
                    "📋 <code>/accounts</code> — لیست اکانت‌ها\n"
                    "❌ <code>/cancel</code> — لغو ورود جاری\n\n"
                    "هر اکانت Session مستقل خودش را دارد و بعد از ورود، خودش را مدیریت می‌کند.")
                return

            if text == "/accounts":
                await self.show_accounts(event)
                return

            if text == "/cancel":
                state = self.login_states.pop(uid, None)
                if state:
                    client = self.clients.pop(state["account_id"], None)
                    if client and client.is_connected():
                        with suppress(Exception):
                            await client.disconnect()
                await self.reply(event, "لغو شد.")
                return

            if text == "/add":
                if uid in self.login_states:
                    await self.reply(event, "یک ورود در حال انجام است. /cancel یا ادامه همان ورود را انجام بده.")
                    return
                account_id, session_base, data_file = self.create_account()
                self.login_states[uid] = {
                    "stage": "phone",
                    "account_id": account_id,
                    "session_base": session_base,
                    "data_file": data_file,
                }
                await self.reply(event, f"➕ افزودن اکانت <b>#{account_id}</b>\n\n📱 شماره تلفن را با فرمت بین‌المللی بفرست:\n<code>+989121234567</code>")
                return

            state = self.login_states.get(uid)
            if not state:
                return

            try:
                account_id = state["account_id"]
                client = self.clients.get(account_id)
                if client is None:
                    client = TelegramClient(state["session_base"], API_ID, API_HASH)
                    await client.connect()
                    self.clients[account_id] = client

                if state["stage"] == "phone":
                    phone = text.replace(" ", "")
                    if not re.fullmatch(r"\+[1-9]\d{6,14}", phone):
                        await self.reply(event, "❌ شماره معتبر نیست. نمونه: <code>+989121234567</code>")
                        return
                    sent = await client.send_code_request(phone)
                    state.update({"stage": "code", "phone": phone, "phone_code_hash": sent.phone_code_hash})
                    await self.reply(event, "📨 کد ورود ارسال شد.\n\n🔢 کد را بفرست.")
                    return

                if state["stage"] == "code":
                    code = re.sub(r"\s+", "", text)
                    if not re.fullmatch(r"\d{3,8}", code):
                        await self.reply(event, "❌ کد ورود نامعتبر است.")
                        return
                    try:
                        await client.sign_in(phone=state["phone"], code=code, phone_code_hash=state["phone_code_hash"])
                    except errors.SessionPasswordNeededError:
                        state["stage"] = "password"
                        await self.reply(event, "🔐 این اکانت رمز دو مرحله‌ای دارد. رمز 2FA را بفرست.")
                        return
                    await self.finish_login(uid, event, state, client)
                    return

                if state["stage"] == "password":
                    await client.sign_in(password=text)
                    await self.finish_login(uid, event, state, client)
                    return

            except errors.PhoneCodeInvalidError:
                await self.reply(event, "❌ کد اشتباه است. دوباره بفرست.")
            except errors.PhoneCodeExpiredError:
                self.login_states.pop(uid, None)
                await self.reply(event, "⌛ کد منقضی شده. دوباره /add را بزن.")
            except errors.PhoneNumberInvalidError:
                self.login_states.pop(uid, None)
                await self.reply(event, "❌ شماره معتبر نیست. دوباره /add را بزن.")
            except errors.PhoneNumberBannedError:
                self.login_states.pop(uid, None)
                await self.reply(event, "🚫 این شماره توسط تلگرام مسدود شده است.")
            except errors.FloodWaitError as e:
                self.login_states.pop(uid, None)
                await self.reply(event, f"⏳ محدودیت موقت تلگرام: {flood_seconds(e)} ثانیه.")
            except errors.PasswordHashInvalidError:
                await self.reply(event, "❌ رمز 2FA اشتباه است. دوباره بفرست.")
            except Exception as e:
                log.exception("multi-account login failed")
                self.login_states.pop(uid, None)
                await self.reply(event, f"❌ ورود ناموفق بود: <code>{esc(type(e).__name__)}</code>")

    async def finish_login(self, uid: int, event: Any, state: Dict[str, Any], client: TelegramClient) -> None:
        account_id = state["account_id"]
        app = App(client, data_file=state["data_file"])
        app.me = await client.get_me()
        # If the bot user is the same Telegram account being connected, keep the
        # mapping explicit. A single bot can still serve multiple Telegram users.
        if int(app.me.id) == int(uid):
            identity_note = "این Session متعلق به همین اکانت تلگرام است."
        else:
            identity_note = "این Session برای همین فرایند ذخیره شد."
        self.apps[account_id] = app
        self.clients[account_id] = client
        protect_session_file(state["session_base"])
        register(app)
        item = self.account_entry(account_id)
        if item is not None:
            item["user_id"] = int(app.me.id)
            item["name"] = get_display_name(app.me) or ""
            item["phone"] = getattr(app.me, "phone", "") or state.get("phone", "")
        save_accounts(self.registry)
        self.login_states.pop(uid, None)
        await self.reply(event,
            f"✅ <b>اکانت #{account_id} با موفقیت وصل شد.</b>\n"
            f"👤 {esc(get_display_name(app.me))}\n"
            f"🆔 <code>{app.me.id}</code>\n\n"
            "💾 Session جداگانه ذخیره شد.\n"
            f"{identity_note}\n"
            "برای مدیریت این اکانت، در Saved Messages همان اکانت <code>!menu</code> را بفرست.")
        log.info("account added id=%s user_id=%s", account_id, app.me.id)

    async def show_accounts(self, event: Any) -> None:
        rows = ["<b>📋 اکانت‌های متصل</b>"]
        accounts = self.registry.get("accounts", [])
        if not accounts:
            rows.append("هنوز اکانتی اضافه نشده. <code>/add</code>")
        else:
            for item in accounts:
                aid = as_int(item.get("id"), 0)
                uid = as_int(item.get("user_id"), 0)
                name = item.get("name") or "بدون نام"
                status = "🟢 متصل" if aid in self.clients and self.clients[aid].is_connected() else "⚪ ذخیره‌شده"
                rows.append(f"#{aid} — {esc(name)} — <code>{uid}</code> — {status}")
        rows.append("\nبرای اکانت جدید: <code>/add</code>")
        await self.reply(event, "\n".join(rows))

    async def shutdown(self) -> None:
        for app in list(self.apps.values()):
            with suppress(Exception):
                await app.shutdown()
        for client in list(self.clients.values()):
            if client.is_connected():
                with suppress(Exception):
                    await client.disconnect()


# ─────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────
async def main() -> None:
    if not API_ID or not API_HASH:
        raise SystemExit("TG_API_ID و TG_API_HASH را تنظیم کن.")
    if not LOGIN_BOT_TOKEN:
        raise SystemExit("TG_BOT_TOKEN را تنظیم کن.")

    os.makedirs(ACCOUNTS_DIR, exist_ok=True)
    bot = TelegramClient(os.path.join(BASE_DIR, BOT_SESSION), API_ID, API_HASH)
    await bot.start(bot_token=LOGIN_BOT_TOKEN)
    protect_bot_session_file()

    # Configure logging after creating a lightweight App container.
    dummy_client = TelegramClient(os.path.join(BASE_DIR, "_log_dummy"), API_ID, API_HASH)
    dummy_app = App(dummy_client, data_file=os.path.join(BASE_DIR, "_log_dummy.json"))
    setup_logging(dummy_app)

    manager = MultiAccountManager(bot)
    await manager.restore_existing()
    await manager.install_handlers()

    loop = asyncio.get_running_loop()
    stopping = False

    def _ask_stop() -> None:
        nonlocal stopping
        if stopping:
            return
        stopping = True
        asyncio.create_task(manager.shutdown())
        asyncio.create_task(bot.disconnect())

    with suppress(NotImplementedError):
        loop.add_signal_handler(signal.SIGINT, _ask_stop)
        loop.add_signal_handler(signal.SIGTERM, _ask_stop)

    try:
        await bot.run_until_disconnected()
    finally:
        await manager.shutdown()
        if bot.is_connected():
            with suppress(Exception):
                await bot.disconnect()
        log.info("exit")


if __name__ == "__main__":
    with suppress(KeyboardInterrupt):
        asyncio.run(main())
