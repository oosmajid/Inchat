import http.server
import socketserver
import json
import urllib.parse
import threading
import time
import os
import logging
import sqlite3
import hashlib
import hmac
import secrets
import re
import html
import base64
import socket
import shutil
import subprocess
from datetime import datetime, timedelta
from collections import deque
from http.cookies import SimpleCookie
from contextlib import contextmanager

# --- تنظیمات لاگینگ ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# --- تنظیمات سرور ---
PORT = int(os.environ.get("PORT", "2026") or "2026")
# TLS اختیاری: اگر هر دو فایل گواهی/کلید معرفی شوند، روی HTTPS سرو می‌شود
# (برای دسترسی مرورگر به دوربین/میکروفون لازم است؛ getUserMedia فقط روی بستر امن کار می‌کند)
SSL_CERTFILE = os.environ.get("SSL_CERTFILE", "").strip()
SSL_KEYFILE = os.environ.get("SSL_KEYFILE", "").strip()
MAX_MESSAGES_IN_MEMORY = 500  # حداکثر تعداد پیام در حافظه
MESSAGE_EXPIRY_HOURS = 24  # مدت زمان نگهداری پیام‌ها

# رمزهای اتاق پیش‌فرض (گفت‌وگوی اصلی) — برای سازگاری با نسخهٔ قبلی
PASSWORD_TO_USER = {
    "2728": "USER_A",
    "9604": "USER_B",
}

# 🔑 رمز اصلی ادمین برای ورود به پنل ساخت اتاق (/admin). حتماً این را تغییر بده.
ADMIN_MASTER_PASSWORD = "admin-2026"

# اتاق پیش‌فرض که همهٔ پیام‌های قبلی در آن نگهداری می‌شود
DEFAULT_ROOM_ID = "main"
DEFAULT_ROOM_NAME = "گفت‌وگوی اصلی"

DB_FILE = "chat_history.db"
MEDIA_DIR = "encrypted_media"

# حداکثر حجم بدنه‌ی هر درخواست (کمی بالاتر از سقف ۲۰ مگابایتی آپلود فایل)
MAX_REQUEST_BYTES = 25 * 1024 * 1024

# واکنش‌های مجاز (هم برای جلوگیری از XSS و هم انباشت داده)
ALLOWED_REACTIONS = {"❤️", "👍", "😂", "😮", "😢"}

# --- مدیریت نشست امضاشده (جلوگیری از جعل کوکی) ---
SESSION_SECRET_FILE = ".session_secret"


def _load_or_create_session_secret():
    """کلید مخفی سرور برای امضای کوکی نشست؛ بین ری‌استارت‌ها حفظ می‌شود."""
    try:
        if os.path.isfile(SESSION_SECRET_FILE):
            with open(SESSION_SECRET_FILE, "rb") as f:
                data = f.read().strip()
                if len(data) >= 32:
                    return data
        secret = secrets.token_bytes(32)
        with open(SESSION_SECRET_FILE, "wb") as f:
            f.write(secret)
        try:
            os.chmod(SESSION_SECRET_FILE, 0o600)
        except Exception:
            pass
        return secret
    except Exception:
        # در صورت خطا از کلید موقت استفاده کن (نشست‌ها با ری‌استارت باطل می‌شوند)
        return secrets.token_bytes(32)


SESSION_SECRET = _load_or_create_session_secret()


def make_session_token(room_id, role):
    """ساخت توکن نشست امضاشده با HMAC که اتاق و نقش کاربر را در خود دارد."""
    payload = f"{room_id}|{role}"
    sig = hmac.new(SESSION_SECRET, payload.encode("utf-8"), hashlib.sha256).hexdigest()
    return f"{payload}.{sig}"


def verify_session_token(token):
    """اعتبارسنجی توکن نشست؛ در صورت معتبر بودن (room_id, role) را برمی‌گرداند وگرنه None."""
    if not token or "." not in token:
        return None
    payload, _, sig = token.rpartition(".")
    if "|" not in payload:
        return None
    expected = hmac.new(SESSION_SECRET, payload.encode("utf-8"), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(sig, expected):
        return None
    room_id, _, role = payload.partition("|")
    if role not in ("admin", "guest") or not room_id:
        return None
    return (room_id, role)


def make_admin_token():
    """توکن امضاشده برای دسترسی به پنل مدیریت اتاق‌ها."""
    sig = hmac.new(SESSION_SECRET, b"__admin__", hashlib.sha256).hexdigest()
    return f"__admin__.{sig}"


def verify_admin_token(token):
    """آیا کوکی ادمین معتبر است؟"""
    if not token or "." not in token:
        return False
    payload, _, sig = token.rpartition(".")
    if payload != "__admin__":
        return False
    expected = hmac.new(SESSION_SECRET, b"__admin__", hashlib.sha256).hexdigest()
    return hmac.compare_digest(sig, expected)


# --- محدودسازی نرخ ورود (جلوگیری از brute-force روی رمز عددی) ---
_LOGIN_FAILS = {}
_LOGIN_LOCK = threading.Lock()
LOGIN_MAX_FAILS = 8
LOGIN_LOCK_SECONDS = 300

# وضعیت درون‌حافظه‌ای به تفکیک اتاق:
# ROOMS_STATE[room_id] = {'messages': deque, 'typing': {role: ts}, 'last_seen': {role: ts}, 'loaded': bool}
ROOMS_STATE = {}

# استفاده از RLock برای امکان nested locking
LOCKED = threading.RLock()


# ==========================================================================
# ===  تماس صوتی/تصویری (WebRTC) — نصب خودکار TURN + سیگنالینگ بدون وابستگی  ===
# ==========================================================================
# طراحی:
#   • همهٔ مدیا (صدا/تصویر) مستقیماً بین دو مرورگر رد و بدل می‌شود (P2P، رمزنگاری‌شده).
#   • سرور فقط «سیگنالینگ» (تبادل SDP و ICE) و در صورت نیاز «رله TURN» را فراهم می‌کند.
#   • TURN/STUN روی همین سرور خودمان اجرا می‌شود (coturn) → هیچ وابستگی به سرویس خارجی،
#     کاملاً سازگار با شرایط قطع اینترنت بین‌الملل (همه‌چیز داخل کشور).
#   • اگر نصب/راه‌اندازی coturn به هر دلیلی شکست بخورد، فقط تماس غیرفعال می‌شود و
#     باقی اپ کاملاً سالم کار می‌کند (CALLS_ENABLED = False).

# قابل override با متغیرهای محیطی:
TURN_PUBLIC_IP = os.environ.get("TURN_PUBLIC_IP", "").strip()       # اگر سرور پشت NAT است، IP عمومی را اینجا بده
TURN_REALM = os.environ.get("TURN_REALM", "inchat.local").strip()
TURN_PORT = int(os.environ.get("TURN_PORT", "3478") or "3478")
TURN_MIN_PORT = int(os.environ.get("TURN_MIN_PORT", "49160") or "49160")
TURN_MAX_PORT = int(os.environ.get("TURN_MAX_PORT", "49300") or "49300")
USE_IRANIAN_MIRROR = os.environ.get("USE_IRANIAN_MIRROR", "1") == "1"
IRANIAN_UBUNTU_MIRROR = os.environ.get("IRANIAN_UBUNTU_MIRROR", "http://mirror.arvancloud.ir/ubuntu").rstrip("/")

TURN_SECRET_FILE = ".turn_secret"
TURN_CONF_FILE = "turnserver.conf"
CALL_TTL = 3600  # عمر اعتبارنامهٔ موقت TURN (ثانیه)

# وضعیت سراسری تماس
CALLS_ENABLED = False
TURN_SECRET = None
_TURN_PROC = None
_DETECTED_IP_CACHE = None

# صندوق سیگنالینگ به تفکیک اتاق (در حافظه)
# CALL_SIGNALS[room_id] = {'seq': int, 'items': deque([{seq,to,frm,data,ts}])}
CALL_SIGNALS = {}
CALL_COND = threading.Condition()
SIGNAL_MAX_AGE = 60  # ثانیه؛ سیگنال‌های قدیمی‌تر دور ریخته می‌شوند


def _load_or_create_turn_secret():
    """کلید مشترک coturn (use-auth-secret)؛ بین ری‌استارت‌ها حفظ می‌شود."""
    try:
        if os.path.isfile(TURN_SECRET_FILE):
            with open(TURN_SECRET_FILE) as f:
                s = f.read().strip()
                if len(s) >= 32:
                    return s
        s = secrets.token_hex(32)
        with open(TURN_SECRET_FILE, "w") as f:
            f.write(s)
        try:
            os.chmod(TURN_SECRET_FILE, 0o600)
        except Exception:
            pass
        return s
    except Exception:
        return secrets.token_hex(32)


def _detect_public_ip():
    """تشخیص IP اصلی سرور بدون نیاز به اینترنت بین‌الملل (فقط route lookup)."""
    global _DETECTED_IP_CACHE
    if TURN_PUBLIC_IP:
        return TURN_PUBLIC_IP
    if _DETECTED_IP_CACHE:
        return _DETECTED_IP_CACHE
    ip = None
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        # هیچ بسته‌ای ارسال نمی‌شود؛ فقط interface خروجی پیش‌فرض پیدا می‌شود
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
    except Exception:
        pass
    if not ip or ip.startswith("127."):
        try:
            ip = socket.gethostbyname(socket.gethostname())
        except Exception:
            ip = None
    _DETECTED_IP_CACHE = ip or "127.0.0.1"
    return _DETECTED_IP_CACHE


def make_turn_credentials(ttl=CALL_TTL):
    """اعتبارنامهٔ موقت TURN (سازگار با use-auth-secret/REST API coturn)."""
    expiry = int(time.time()) + ttl
    username = str(expiry)
    digest = hmac.new(TURN_SECRET.encode(), username.encode(), hashlib.sha1).digest()
    cred = base64.b64encode(digest).decode()
    return username, cred


def build_ice_servers(host_hint=""):
    """لیست iceServers برای مرورگر؛ STUN و TURN هر دو روی coturn خودمان."""
    if not CALLS_ENABLED or not TURN_SECRET:
        return {"enabled": False, "iceServers": []}
    host = (host_hint or TURN_PUBLIC_IP or _detect_public_ip()).strip()
    username, cred = make_turn_credentials()
    return {
        "enabled": True,
        "ttl": CALL_TTL,
        "iceServers": [
            {"urls": [f"stun:{host}:{TURN_PORT}"]},
            {
                "urls": [
                    f"turn:{host}:{TURN_PORT}?transport=udp",
                    f"turn:{host}:{TURN_PORT}?transport=tcp",
                ],
                "username": username,
                "credential": cred,
            },
        ],
    }


def _turn_conf_text(secret, ext_ip):
    lines = [
        f"listening-port={TURN_PORT}",
        "fingerprint",
        "use-auth-secret",
        f"static-auth-secret={secret}",
        f"realm={TURN_REALM}",
        f"min-port={TURN_MIN_PORT}",
        f"max-port={TURN_MAX_PORT}",
        "no-cli",
        "stale-nonce=600",
        "no-multicast-peers",
    ]
    if ext_ip and not ext_ip.startswith("127."):
        lines.append(f"external-ip={ext_ip}")
    return "\n".join(lines) + "\n"


def _tcp_port_open(port, host="127.0.0.1"):
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.settimeout(0.6)
        rc = s.connect_ex((host, port))
        s.close()
        return rc == 0
    except Exception:
        return False


def _is_root():
    try:
        return os.geteuid() == 0
    except Exception:
        return False


def _run(cmd, timeout=600, env=None):
    try:
        r = subprocess.run(cmd, env=env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=timeout)
        return r.returncode == 0
    except Exception as e:
        logger.warning(f"TURN: اجرای «{' '.join(cmd)}» ناموفق: {e}")
        return False


def _apt_install_coturn():
    """نصب coturn؛ ابتدا با مخازن فعلی، در صورت شکست با میرور ایرانی."""
    if not shutil.which("apt-get"):
        logger.warning("TURN: این سیستم apt ندارد؛ coturn را دستی نصب کن (apt install coturn)")
        return False
    if not _is_root():
        logger.warning("TURN: برای نصب خودکار coturn به دسترسی root نیاز است (sudo python3 s.py)")
        return False
    env = dict(os.environ, DEBIAN_FRONTEND="noninteractive")
    _run(["apt-get", "update"], timeout=300, env=env)
    if _run(["apt-get", "install", "-y", "coturn"], env=env) and shutil.which("turnserver"):
        logger.info("TURN: coturn از مخازن پیش‌فرض نصب شد")
        return True
    if USE_IRANIAN_MIRROR:
        logger.info("TURN: نصب از مخازن پیش‌فرض ناموفق بود؛ تلاش با میرور ایرانی...")
        try:
            codename = "jammy"
            try:
                out = subprocess.run(["lsb_release", "-cs"], stdout=subprocess.PIPE,
                                     text=True, timeout=30).stdout.strip()
                if out:
                    codename = out
            except Exception:
                pass
            with open("/etc/apt/sources.list.d/inchat-ir-mirror.list", "w") as f:
                f.write(f"deb {IRANIAN_UBUNTU_MIRROR} {codename} main universe\n")
                f.write(f"deb {IRANIAN_UBUNTU_MIRROR} {codename}-updates main universe\n")
        except Exception as e:
            logger.warning(f"TURN: افزودن میرور ایرانی ناموفق: {e}")
        _run(["apt-get", "update"], timeout=300, env=env)
        if _run(["apt-get", "install", "-y", "coturn"], env=env) and shutil.which("turnserver"):
            logger.info("TURN: coturn از میرور ایرانی نصب شد")
            return True
    logger.warning("TURN: نصب coturn ناموفق بود")
    return False


def _launch_turnserver(conf_path):
    """اجرای turnserver به‌صورت پراسس فرزند (foreground) تا توسط watchdog کنترل شود."""
    global _TURN_PROC
    binary = shutil.which("turnserver")
    if not binary:
        return False
    try:
        _TURN_PROC = subprocess.Popen(
            [binary, "-c", conf_path],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except Exception as e:
        logger.error(f"TURN: اجرای turnserver ناموفق: {e}")
        return False
    for _ in range(24):  # تا ~6 ثانیه صبر برای بالا آمدن
        time.sleep(0.25)
        if _TURN_PROC.poll() is not None:
            logger.error("TURN: turnserver بلافاصله متوقف شد (احتمالاً پورت اشغال است)")
            return False
        if _tcp_port_open(TURN_PORT):
            return True
    return _TURN_PROC.poll() is None


def _turn_watchdog(conf_path):
    """در صورت کرش turnserver، آن را دوباره بالا می‌آورد."""
    while True:
        time.sleep(5)
        try:
            if _TURN_PROC is None or _TURN_PROC.poll() is not None:
                logger.warning("TURN: turnserver متوقف شده بود؛ ری‌استارت...")
                _launch_turnserver(conf_path)
        except Exception:
            pass


def setup_turn():
    """ویزارد راه‌اندازی خودکار TURN. هر خطایی غیرکشنده است (اصل اپ سالم می‌ماند)."""
    global CALLS_ENABLED, TURN_SECRET
    try:
        TURN_SECRET = _load_or_create_turn_secret()
        ext_ip = _detect_public_ip()

        already = _tcp_port_open(TURN_PORT)
        if already:
            # coturn از قبل بالاست (مثلاً اجرای قبلی همین اسکریپت با همان .turn_secret)
            logger.info(f"TURN: سرویسی روی پورت {TURN_PORT} فعال است؛ از همان استفاده می‌شود")
            CALLS_ENABLED = True
            return

        if not shutil.which("turnserver"):
            if not _apt_install_coturn():
                logger.warning("TURN: coturn در دسترس نیست؛ تماس صوتی/تصویری غیرفعال ماند "
                               "(اصل چت کاملاً سالم است)")
                return

        conf_path = os.path.abspath(TURN_CONF_FILE)
        try:
            with open(conf_path, "w") as f:
                f.write(_turn_conf_text(TURN_SECRET, ext_ip))
        except Exception as e:
            logger.error(f"TURN: نوشتن کانفیگ ناموفق: {e}")
            return

        if _launch_turnserver(conf_path):
            CALLS_ENABLED = True
            threading.Thread(target=_turn_watchdog, args=(conf_path,), daemon=True).start()
            logger.info(f"TURN: فعال شد ✓  پورت={TURN_PORT}  external-ip={ext_ip}  "
                        f"relay={TURN_MIN_PORT}-{TURN_MAX_PORT}")
        else:
            logger.warning("TURN: راه‌اندازی turnserver ناموفق؛ تماس غیرفعال ماند (اصل اپ سالم است)")
    except Exception as e:
        logger.error(f"TURN: خطای غیرمنتظره: {e}؛ اصل اپ بدون تماس ادامه می‌دهد")


# --- صندوق سیگنالینگ تماس (in-memory، long-poll) ---
def _call_state(room_id):
    st = CALL_SIGNALS.get(room_id)
    if st is None:
        st = {'seq': 0, 'items': deque()}
        CALL_SIGNALS[room_id] = st
    return st


def push_signal(room_id, frm, to, data):
    """افزودن یک سیگنال برای نقش مقصد و بیدارکردن long-pollها."""
    with CALL_COND:
        st = _call_state(room_id)
        st['seq'] += 1
        st['items'].append({'seq': st['seq'], 'to': to, 'frm': frm,
                            'data': data, 'ts': time.time()})
        cutoff = time.time() - SIGNAL_MAX_AGE
        while st['items'] and st['items'][0]['ts'] < cutoff:
            st['items'].popleft()
        CALL_COND.notify_all()


def fetch_signals(room_id, role, since_seq, timeout=20):
    """long-poll: تا «timeout» ثانیه منتظر سیگنال تازه برای این نقش می‌ماند."""
    deadline = time.time() + timeout
    with CALL_COND:
        while True:
            st = _call_state(room_id)
            out = [it for it in st['items'] if it['to'] == role and it['seq'] > since_seq]
            if out:
                return st['seq'], out
            remaining = deadline - time.time()
            if remaining <= 0:
                return st['seq'], []
            CALL_COND.wait(timeout=remaining)

# --- کلید رمزنگاری AES-like (ساده‌شده برای سازگاری با مرورگر) ---
# نکته: برای امنیت بیشتر باید از Web Crypto API استفاده شود
ENCRYPTION_SALT = "chat_secure_2024"

# --- فونت وزیرمتن (variable woff2) به‌صورت base64 امبد شده تا پروژه تک‌فایل و آفلاین بماند ---
VAZIR_FONT_B64 = "d09GMgABAAAAAbIwABQAAAADsWQAAbG6ACEAxQAAAAAAAAAAAAAAAAAAAAAAAAAAGotDG4HRKhy4Tj9IVkFSmmsGYD9TVEFUgRonLgCPdi9sEQgKhLs0g/EGMIaqVgE2AiQDqVQLlGwABCAFjlgH6CoMB1tqgJMJ/2vI3kewLtUdrlE6B2xbaQKgyLkFSYBcMnzaEHEVvaFjDAM2BQOy/EOOkNf25oJKb1Yuztr9dNbs////////FyaL8Dd/doHZz10OEgQkfIIaLNba9rV9oNEDmZGldrWgNlHbepPR24AufVu9PcEy0+sO2fWtX4vYofWC1VEr96hxOJR9h+fj82Y0EXHS+sNZuVydSnVfK9O496eJN/RHHFGtEARJDmk8m23DxpJDDiyl2EucHK/tEpHVKJK+Ew6nvXW8EdZRzBRziHTDPcb3QQTilaLAdibuxLc1rIcpR/Ew7Ke1PeMEC+UGihuF0d1Ewk2hw11+oDeRWeRzoC34XTxO4t3bZ0oXZkq5gz8kDV9qLnFc7pDbD/e1lsu7LHeIxHxXc3nTRSVVUn8VFXfUEOe4MmKRuQTl/LgokT57vNGlHzEgAl18IbtETRERqK/gJgbHlmJ7xzAoR91BOQl7UUmNoEou/LNqxP4d/SgiAjGKuCJm6cVRDiJiyPzAozRkW2iccSRqHSMEJxSXToZJGjE4Ivhwp8g1zCm2Tx8PZLfBkzT1l3pdyV3+XoqvTr9rSfRHCkPAOhNOGHoxE/+9NnQErTSVFC2E07a0xf58rlsnI067iDOY+KGYbboSM5g4K52haQTl/Esr16syXmByIzfnpcyL/da+HkjeqE4UfzhywYNcmxhcfFv69Fe9UulnN/wVl2sMt1S8UxsX4/atziYOhDEIN2EU9yImwlCVtLJRSbikmeWnLza1vtUi/q1wZmaKaQWHQyqt+/8DHV6+EAr7f5rpsQqnUCv1XFlbtcdANORuXxnDElGipCelXfs2tplHHBFdrzqf8Qsl0bKKTEnVBj4fAj8RgXd0xK/tZ3ffvgvqgONABERApPKAI0MB4RMqQosnYf8DwWrCJhQLsRAklNMmxC6sQmwslLjhcab+k8wyy5IssNCSJTOd7QPKYZCapCn9ZcS5823d74DaYWGYdoAdFjBlTNcAN5dLcpgcDk9z1r/RKGZFUqOmK9brAL27ryKZTEIMjwAxmYgJIZhWgCqVtW53vV0fnpaufzLiu57dZHezkaZpPTWoJ60DxfT/w0+QU+3MLH6OeDnloEhb/KDgLdCrSapJdzeyaqMQ/e8Xn1V1u9+b+TS7YTYajw8LReB0ZITRC0Pgtk7LpmPWdsxsqamlWG4UFQe4YKuIgIAyFAVBcA1AVBRUXCNLcSa2NLMx5pe1/+v79q8GeLv93easwxnrncwzklnGqaNCKDQo0S+roYwZWeOMQ5zM1fydkYwyDxWNaeyzzzlzvCGcaicHmzRtU6Kte1h/Tx1148LgefBEOEd54nE7KkIAm5hkZBlkSydZYJFtmWCE39YzfBhPfNbzXfELs7Cw+PXmMAqb77C4KOa4wmLYyBW/sLAZY34s5mcOoxlGccVFcc0VxnEZAPRPjP3rnhsiYWNNImxYRkgSOvN0iCW31YDja0Rd+394N+v/MGJCTdAWimiMBAkSKAGCBy0EvE7b1+k8Mf+6IvJm3871WZWR7qyIhbHB1lqaAf/8T7/fvj31lWk1v7T+/gdhcSi6kTm5mZm1UE21JjESC8ZhLIHn8fDfk3uT/M6hY1KtIGPSwIIUtDiW10tW4hK8l5uDKhWxuVhd4MuhLpVatsIAku4BQ+Q0bN+wdZk6DQBkeCjwEMytAwWLqJE5xsY2trFg3SxYNNuIwRiMHpFSNgj4oo2iqKjvXqz4SL/a+vA7QbGF2sm91HYUDLMBygd6oVAmrNt9i8RAEBYlPAmoshlt3xGCAJ4Y29fFwxxxQDF/x+5FBPHAsfetggY+gY1+Loo3HBU1Jg8koihSRzKxPKhq76OzM733vpShRKAAE4FiQBmQZBc3ASECbmpmQAyIwu01gsn3v2uqusBT5brsKW337VmdkTxN0hkZHeAC/8B75d9kzTqFPA/kP/jHM0m3AJyFkP9b63tvFXc1DOzsB2JF7P+JMLER8qvMm0SoGBVlwgphcebtYENxV9f/71zfxYSCDgpZUSYY0sbcNFtuuUW33Vbj4WzXbzvtDyn7DI/wiAo6Wafu+b+JW1JVFDoopHOlLYRNqzdOz7w5SOd/zn/ttyPOJ3pAGMACB26gvYHmUqBJ34A0GbMzoyYUCzc5oQelmauq6oPsdWQ4MGekBWxZc0nQwpJ99v/8+zxbAWqaLXrCyX2+SwXgzPP8FbrYbazRmglVCTTZJHsldu0DshMvHUG2LVlKXijyz5jpUF5wLV0LT4eop/efW/1XJWhVEqD7fZO1yUrEryDtSJphnJYkdxPO38GZXY+aI1+gssnk7f/f7rSCkpIQEoKyCI3HKIzjcuw/3WHeFZT4s4ASklW+vgdrbpROIzRSNgmJEpahTk1eTl6mKES4bMneprR7Si9C4QTCI/NVWAUMEXMLD8fGYMJYUkyWZAsGWzHU6GqRMQYgzc2KCZWVJ83KITxCw/P9L51NEWave2tc1rtM1KRSFP8gZKkSbwD67/c6/efJqLgYE+FjZaPtv7R+qEVWoZI+HrDdBhVLa4pBlipRMYbBonAgnEBphHPt/zfVz3YeQYigtLsWNkXKleQUW2pDqpzS6WN6uHfevJl5GAAESAjEkBQFSvwi+QNIKiRr582bGQ4CocQfpOVPChtCpPiTpA0p9Q4xF5UrF6XLf1SpdEhF6aJ00bjtXfS9efh+2s/e4/Lkl+v+c4nb9Q56Lj30HkepGoeTCEUopakdjEMyHq2wCsnfm65K/2u3DbMGWAdzDrZOV+IsBBkr4Iw3Qdb6X61Wq8UgzDgYWAHjYJwGxsGsUau7tSAJdgbEWM0a1jin0azRaJ1gnTtjjEtvow033PiC6ILQuujqoovyS8NLrUmSi5ILsuOhXPZJw/W7uH3OjG97KHGNViUnOYv5Mx/hK7NfRv4/VcsWw5l/NyCA9wDx9A68SMpBkp2LTtI6V5dKV24qcAbDATgcBQalER8VNmpzpDZxpY10yt2WW18lXQihvNLu3Lku3Zvnf+5ZlhPS2m1xWJNfRAaLj8ErUbCYirABB64NYYL7n6pli//fcY4gHQhCnOGOVxci6ayucVXrKMkrCYLiZi4uw4kXl06xu6J06fKa0iF3bg3/n7OfbXM/26vJRTVCuS6KHPawLuMZj0N9EJK/L9Wq638AISVV6mhQ1er6KDOR1LiXbZNj7qzi2NussWOPHXt2yYRQTCRJVRKUVEmw1JUCyyRBqfojKVUnQPU0SZQ0KqmdTDtprKRxVWNqpXbmJSRqPih1TxJq1UBcxzHG3dqaMd5c1133tnvdw2mPe9zrHo09HK8bC/jh9JXmx3EA6ZhsLILOQi1k+vfuvp0vOUt2xlq0Sw5ygtwQ1LACmGJY+Acup9d/t38D9QpD2gvjPMDuqLFILd9a/uyvLQOhudKVOhknmdkNd0PmUdsvluaw2ECXpxFO4f+r+rpeAIQk81O2iRP6wOXs9pZh/P8/Z2I60zktdpcFS25l0slUSgXoSriK6UoVt7S6KqVOiSdn9jBlmP23tAL/zo9n9dxIq/oGLKWEYQgl1Dpfurv8r/1G1TvvSexce9EMMog0YqQRIyIiUjGdyTL/cmdznNZ8e2WVw72c++GkrTFCCLGIYViGzfHV3h9fQXRq3UB0FQY7L/tuX/33TgLz1Xf2ot4WmlCIiIiIBBEJ4swOFWDbf1UzQLzY327kBdAI4TC++HNQXjrQHY1YtRQobeH2/Lqv+5E16wmKdlt7rZ3rYBiXMhghjRFiCOEZHjEif77FclX0xPQ1gkQIYyQDG2J0jcz7U6uVI1L6Pe/EM5d4bGyKBAgEqHQEmPu7QzatQeZ0wv/EUzEIUnnqlGfJcUlDxgtasgU1rRD43gNBpq5ZiZr2AovEcppL3IrSoT++nMT9RBA0eH7Q41i+CRgvICr+r6QBs5UHxKG6C9OUHpAkX9DJ3Z5nGWkmSLkyTVfQhdTGPFXLSguAtd1i1T4ftdarj6r2jtnW7ZTpMNFd1KnH0v2GMm+tPP0xO2crYTHX2gQW11Ha7+Po0LMTSu10vkCcERlTUvcWarG1/LGt4seuykZNz9850O9xNz7zIWH0pE+ipk+NJpSJ8hwqJGYZS7PX0Cdx4T/yImKOxbF4My3J4DAhaYYJzXtG1svkZaD8DFaYT8zLuGml6S9vSo2K5tLexIvDZoCqAFiLEdth9aEyxvStAZXEf9veV2oBAtgPE8BxAC4H3BfwaCBuCMRrAfF/IPgjfAIAZ/EB6wAEvODtT38n1iAcGZsoV6vWl9AGAArQL98dIrGxPo4pI8uFKqt6wQtiy2h3+4MRg0HBUb8BAgIBsydYUpVuAAbQQ3oEftH3SPmK3MoUOb0+sJ5cT62n12fX5zTilXHNLDWrld/m2ObZ5t8W0hbWFt4Ga0O0oduwbbg2chu9LbuN1cZvE2gCNAmdV7riujHdhb3hfRn94f1x/ch+XH96f3Y//2DsMHr0udZSa63drw3ThmsjtDHaWG2cFqGN1yZosVqcFj+eO5E5aTnlOsWYeToj3RCzBA6NFFXaIQnAEKFwK3NqeibzT92+jkZYiYpV64neKS88YoLx4iSkpFVUdaIw4grKKuSpcyQYaZGzb2WtAbyyCgIGDgJeUGDBgYeAPKpoQRecHuP496YWDiyYCEcvwwnSmjAJesmRp8YgQ6ywyuH9w3aUWSHtba5Fjd8BBQkRKU68BGmSbTrODGEi5POpLFy6XENHHHncsAnPOgw90A+rxiWTc1AeGJwXicLwYXF4AomfQhMUFhWXlJJWUdWAUsg73ecZOeQRLlK0BPkVViag8EY4CmlMR5IZzFyZii6h/KVVsvJ1oCf4gZZa7lgXxz3UYsttcJOfCSkqSVJVEmDg+ODgEZDQCBIjSYo0efZy13f+73TxXW2+r+oWc8JUDTKMEQ1neKMYzQRNyuTNxxyKtTFGEln8Pn4p81wGk0wq+q+coYk29IncB/mRCbljjMJKqRXzMfOdFmfmd/iVWB3KjEXyBidJR7R/GobwUXOJDKQuZoBOHkIAgQDoe+PR8vyXT/TyvnmZeyv8tBLmZYwEeNlVjI0UX9nCoJ8h6HfRnCBzwhSYWOBqgZcFhq+7QfHdRn6GIYHAIICHP0QdCA/UB5MHnoPhxyYeo94afov6SPcJ9ZN//+Q/P3n9J+/+TP5V7FcP/entf/zhX6Cehey6BGHAYAC11cgRxtKjFbYfrVMOAlggSS/keb+mZ8Hwpp/I8uBw88+3BfC71i5Uwe92tlsHPwwA3QYgYOFtih8wFK4TzdM48G/+304TvG6/t12HgJML88eNmACMd0mhrDvVmst3i2xVAANyyOPXeako9EsTZVRQRQ2gwMa0ITAcFOC2fIjrp0EJaN/397px6WtEL2KSVC7Jzo+d11wQnMnOVH+u/5if4+dHM26kSYoJ3djmHCc58FDmZy4a4JAw+BDwEyBImBgJUmTIUaBEhRYaAgQLE26c/8SZIMEkKdJkyDRVtlwzzDKHTL4C8yywiIDQIAmZISPGKKhM0tIzMrOiuYREJaRl5RV95gu7fe1/9jngkCOOOeGk084acV7CmAlpOQUlqtRpYWBLiEFcpIRUkbqYXikZWXlF/SqqBg0bNW7StB3mW2aRVU5YNov9iggZOnL8hElKjzpCQ622cWC4YPiLJkCqAwX46lSR4DDWdurlgAZPGoHixxQ4WnQzfD9+mDRxWpnjuAs4wtG+hLrykBf1KrlKpNdLI5k6Ih/zZFJ1V34fnuLtabTU4Q/apy00CjUV0LA1XgagOcy60QCjlv2FFFFOvUiyBRlm3HQL1OCiZ8pC0GgTrBPKNLxWjqjyGJf8KCcHqSzVlnGmdX3SCXAYv0Dc6hrx4PfRe6shAMUDDgEJBQOLgIgfmQBqs5NvFBvllq+6kCAvtaKRUTemGrp2vIGRSVpGXkHRp8bnxi7jS2NPY6/sKDOs/BZ/yikpOXkFRUqUW/Z/a5NYRRYqVmKkUUYbY7JpZttim1E588oqFlRWRYYsDZKwAgMJg8GQMDSMAyYcYqEYSqEcKqEax+NEqIdGaIV2GMaZsArruBZBERGxERfkSA5KpAY1srIqX+arfJNvsybrsj7fZ0M2Z0u2Z0d2Jj27sic/Z29+zW/5PX/kz/yVAzmYQzmcU7mRMzmbc3k1rw12AENuyA+FoTiU0SkqW3E35dwEKmoP94NmC8Frg3UcgcjByc3Dxy8gqENYVJcevfpMtczy8ff7B/jjWM3h5UpHHcc86RRdBs46x5QVa9fqbT96hzMXruMDRc2L9EWoMOEiRIoSLSaTziRL81aNWnWOAhwCARQMHBIKGgfhUUrhkCMJnmpaVHc27vbkoUc8ePLizYdvPjnPMKYj8CZOW1i8Y0mISSGf2kUq3j7X0BYfO5wv3frPJw38y9Be6ctvu/xhfhk0bNS4SVNm6pzMLli0ZNmq9brpfLdj95LDAQoPcYZHApJVyvlHjjwFiqH8EBDDrkj6vkluX6ULHRIcRE4efkFhXXpNtXw1519KE4o4rZgsJQop+CrrqPIUKYVKKxH+DbW0pbY73c6+66zpxtAtYmcOlrwLlCcUdVFxV+VKlZ1RASGU53ByURqlCUVcUtYfyheKlEKllQhpoZa21HaX2lk3/NGt2Fkfw5o1qzZtYmNjb2EXZQI7iJlbYFhdJ9+SxR/VtRhhF6EQOHDhxR+40jazMb9+NzY2Nja2EzY2NjY2NjY29vPZzNUejw64vW23d+DMhSsvvkKFCRchUpRoMZKleatGrbpFJs7AwfmgRnGwyHkqrqkkylSoOu6EM/lkn2FIWMzC2efO95sffhk1bjJmFujxtp+8w5kLV158hQoTLkKkKNFiJEvzVo3aqCuBQ5HzRFgklD73zQ+/jBo3GTOTOBUBUwxUiUIKvspCKE+RUqh02o63nX0XrW7g71bTndvw2ULUvxhYPTJCsAQCCgYJjYNw1TMt+gwQnWaTFPoMv6wvifa1/J8f4zhoRIeJqckHwIpPpmtRi6CQsIiouFr8uNMnXO9hM+biWnlYMkWAGqFnAGOlIQZyDlAqJRFBbdoyh+iRLMESCCgYJDQOwkEpHTQcUy8Fa+9XHfwZ2llg2pdiZm6eb2lNndkOaf3gd4btlKRXk+eXgyBXlGtIYLNx3P28a4Yb8/tfhBJNsWnPVLOEwFkSdd/F2oevjvVAdMZWV+OuSbcygudCQiJw5uIfsDJzSz7GzHNFg2xF/Rp5O3PNr2Xr+ChtrfgT2U8wB8j1cpjj0nA8by9m5r5KtN3zvvKKN3ry0H/eeXEp0yb/t3l/LjjbErn/QK7ZA+UDl5k0SqQQQq05HAG/roBmI4Je1hCAhb+L2XQh8LzWBldqetPcMNYZ3eJlWm5/t7TIeesseORWxlyuamPFWT4Tx9V+2/LCwWp5qcrFAX9pxta8Hi8/j8dQKAKga3FXVrDyX4IJiP5maf1iNSufhra8J2zrza7WhbHg6Nw6swLZouKEMjuxOtpaq7Rf6mUzgvpfl3X1+LmSNxgQVfM0u8ktbGaQ3dbBbWCkzHjWbNjUBmYqgyvd+/WOtWJcoHu17uuyYyAS7+b1rW85l4/HMZ4VV11nutjcreCv0vzKppcxz2jJqpe6xjUAWMO1t0veyuglraebV7e6pdxLwQ8T1WUselVRuSVKg5hXHTyReLqX3KSbJhp19pxoWBATP2GTBeIVCBlxs+c9S4iAj54Rt2M5tpbEdcpUGSiI4Dm1tCfg5bu0/EG6dFIVD+kNuk88bdX/7R1+rvfP+1avSrApCifMy1Sa/bNq90YNBDV+WAEI/rg3Nls7uv+obevO3nWe/Jd982j/WrerBR8d7X7mRfHjJ7o4IlL2qdCm927mBou01J7xt26q+VRt8HzYlvZ345trzqW2ey/5Y+ewBDvxcZ921d4nM5sva9Go8PhaLeeWo1NJWuWm00FiRqUMtNZEWivLjtwrw1ceue5E3yr/Ps6aM2/Bsm2GGm6scSaaZIqpkkyXbGYT2pQliSPJ7fLGJlObzJiuWhuHgrGYIX4yEy2sOJWn6rzoQ1SjVt071ii7DQ64ZHssDp9oM1rCHr4bNSUjwr/thjey0Y0B8+j3MGTXU6nBg+FTQxlGZasGI+BEA4wmJ1pgRJzogBnGyXAw+pwYghnJiTEYE05MwYzmxBxNmJsYNwluUtxkuMmBcGHHFYQbOxIQ7ux4gPHkxIsBX5QAlGCUMJRwlHEo/6HEoSSgpECkUqEYm1Js1uGwQSc/xGGTTu7Qwo/w+LEWfoLHz7VwJx53aeFuPO7Rwi/weADESTWcAdGqhjaQdiIdIGeJdIKcI3Ie5AKRSyCXiVwBuUrkDshdIvf4OQ/ymcQXUS6R+CbKFRK9oszi+ItjAIdieiNUD4MYXMSlhJSoIlXqugnFWpvgExVYMZVKBS/fIofdu6xsZWUrK1tZ2cqTTdZcsweP4jUlTUqb/py1gFHuFPwNFWy4SOPEmthxPMLp8we0GzLaf2VioC9bClNFCj36VmBqXWDqTEDVFgi9D4R6Hgn2/wNEOxanXlUMyFgOGQExxRQHc4kiWtuCyfqBsxooa/UIFhUrNsWLHyDxCLk8QLZjbemNPXA8N6j7i0HbB0OtlwfUKwLslQH3qoC5OEAuCYjXhnbfHmpdHjrit+FAHAqM2BegqA1oHAycqA+caAgt8feAxpGAhjygcTRAcSy0xn8DI06G9ngk1EZb4KI9hOKJwMbZehw+WJ8jhOOZ4IlngzOeCyguByquFK4eT18jkHE9MHGjcPME3DpBt0+oHxJgPAo4ugKMxwHH64DjXeCiO3DxMwjxK7Dxu/AnGvqi2X8JbHIDBsUGSxl/ASt5VdqCmr8tN4YLmD4k3uhmFypYKjf2vWyW2BnZGdkZ2RnZGdkZ2Rm3HYe4DhirfjbzgLGFGTsw9sw4gHFkxgmMMzMejHiykwkzBZepMFm4ZMPk4JILMw2XYj18Rw8PgDmJySkwZ8C0YtIG0Y6hA+Ishk6IcxjOQ1zYPy76+ngZDFcgrmK4AXEL4g7EXQwPoLCHvyvCLRzcpsMMB3fpsMDBfTpgHOzo4OBgTwcPCycqRErofqCP4G0Wl5BbwCXqlnAJvAMC4LEHVrCEH4xgiUAKgiUIqQiWOGRGsIQiSwIejdzkTlHAA1K9FeoxCgxMUlqhnqLAgCWla9RzHNCQuV7ggAzO9RIHZHyuVzggQ3S9xr8goxSNdrvdLwaeENTDdUABaXaBgArS+Q2pxBS6sdqQGnTN0WzdOksRhivMC8Mw3IwJAWQaYMwWINBi6OmasUwB4RaGgWF+MRer4LAXhYMeyxgO8ZkdF+p8BX1/PmAXBK4LA/K8gD3/Yiyo8IlkHAi8GV6tAiJwo15PwLwh1HljUYtnnG6O+ygg9EIgkIbjFKEuThe10J05c/vcfr8NhUZtGrcbgnZDxIIQAmoinvSA4mmA8SygeB5gvAgoXgYYrwKK14GINwHF2wME83rPgcTzEvsDgYyPNX0+sq9H9T1KfkSlYq4a4QlHddAH+YOHF70+DDjfFj5h+ViOPQygFzAh+CgSi51Z/deGYHtt6XQgUEaIryGk76LgReodbpW3zlocgQfyueb6DgKus+FLPL31l5F/uRuH2Bt307x0mTnW4/DTNDfMD8fI0UKniJRr+jGK/Mbd7h3e5tPgI+QP3vY5scc1QKqxIKTP4co1IoslZeLIm1i0x35fcf2CA6/1s2c9stgeZ3+jyrkH3B9WRg9YSbYdZCXxix+4aGCcx2AK6huUCdPCLm7sMY3efoY8UgXW+QcbTBF/yOmHGRGSZZT3Ka/43As5XuarKnCz3dYHc7vtzr4kdx8i0n3tHqxJvS/kuNcvrdUF2t9qpNynGqsy2/OOlFwTxzaaXS1+8YOe1eOTXun/9DGvm/DjPpTwCy6V01/2lZxfAV3k1yJ9K9K3pe76OYyyM8BcNDNLW/tplK39/AEx8gv/4pfyrcWvlFiypbDqsaKA8qz7/02mn4qzq+2DHVcGqrtiRmq8ag5qsbE85ZXs0jYEcACgjL90DICTgLZ97kZmXPv1AP6k/ba+l3+NV8mPYnYs5sSzDvv9wE/BBgdc1KHwgyM4pST7gjKnyPb8eSu0DgIIVSO+rugfZb08PeUgRun/3DbYCBHE6IVMz6U6hRSiWy6YXU5lNRVmJJVcCo0pSctU90570OJNVY1VMsz/IQLgQcsHeEpfAwYYYcK3r2VLa8gKsAJ/oH60GwkkTtCOCN1dkMPpQT+SSC5HgQmKVN9tiPEgi2eZxuxTODolOZTttg/zx3Qxj31MJrgL2uzvNM5Rw3Ly2MBLZpvDv9jC318CC9nP4Ul2UqJRvKS9lmlZmwx8EJWcSFqyY9+sdV6nYK6T8lNsRsp/pqzyDO/wkdVe5XO+UX+uuMNPwsgcz8pZ4UGH03fZWutOGzQJ68O1/wMTavpR6p70alP3w1MeXsrwT1iQEGzyt7FM06mm7+XSn6fXlBb4wV+MreHtQgitJmZfVV4K0M2PYR+kOoUqyj740qr6RXFKEs0x/i0NJX2H8QupplwxFJSCb6vMjwD92/YRn9IJlZrrOvp6IosndF6VNDboUfrO05BLsWME+UFuHL9QfoYtKBW4jDaHcOAHvQ25AOYhZSgzlBwwBL7Qj5A29BmkCe0JcUCAgFBGGOhZaAHAKtQb0Ah1AWRhuZkCBgYkQXm5YmlAPAgDpTJi+saCFKA/JvNXWhRQLZ2RtPFk5qLJxzcvSUl5IhE7b84GAcJgfzhmpeEECFjkMYLePG2UmSAooVRryBHyk1e3P8N+fgT5SzRr1AXYV9Oy3T9iYFKApcw5PwisAT7O214Czvw2oiBnMU0Ms/Hp/nSqc7TvxiIWHiKlhYc/05JW4u6+epfAt6Mjxl6dZ0ogdpUx5jMn1BgcxiIKReQBpVQLX3wOuR7S5bFPt51bhBfZHaL+s320cZ49r9lQ5SaU3DsTueXrQMD9h0kSTfFlh50Wh3kgTM0MNKQBPEPgxNvsIJF8GtD/mtBPNGxVgy8rwFGBForJYlKsFFCYg1BBqDffHFyjW/P9pnkQdQS08NH2frg0MKeeS1+3g+aHorPE1uFWPawJikyc68HUTfOJwYUh4sPzeeds5ZbFo7kDKAmz1ihue8htmclKqlbeRghYFkRXxCAmHTwtsB3mDjGfTnwBZbNhSzg7TgNTuRH5Wuanq8mRBT2sLbLS4GkUoZBKQ+Rw/VeL/IgYDtHi1rTsPyCNCW6cupJzmF2ow+Oh2X4q0CzSxCUj2Q0wqjs+N7sKqa6kQpAPRK7pnlwpNv8PwN1wN3S80fWrIrVRESwNXXA2hvmQFnQCuROgM5jB0RpWrSslJgOjLfKmKVf11Anzub7JA47Hu8CIe0vu28mpsBYU7w7ATmG/5iM4HZyA3xa7/6STCV55bf0l7hfEDfefci+A8QPQJcTTbdp7/mtn4H/pUkDmDtVu9nFQ8OVH/Bil/QNUXAiJgBsSDrkr3ffTfT/djek+TUJ9VDAQPATEx0/bUFQ1CM215Xl7BFS4Hr9RJZkRSu9Qbj1V3/iFDMDpc8sLsQoUbF2IQsP07mHRgYGryFH/qWcsJ7Y7Q8uJumb2ahiDdrJweuKS1nXnzyQnF1p4iSWXWnoL8y3QeiKGR/R/0CRKIqbJmDmrH0QvuNAu8AmJySupMPxgxTmCB8+zXu+97nnnW2zxLc7TZpmQWMKr5+RSZpOUAbGMmRiLKeprw7ilMYCZ+P7C5st0e1Co5/DoRRbd0rzzL9g+UAGi9nZaWNwLKHj12Nm0ac40DQtrTbmIddosJ+aBhBgQ1DcKR4ANgWDh3oDPYkAOaSX+fjrILw6xi90ahDUAJD+++hkRWVSXjGDT5PRs1YKZ4CzZTE5WCNNRzYzFaH4qMT1EVZA/XFpRzSZKeDe+sowoT2EySKlduDTkhQVkAr5o5MNArsmZsvJEO2MTCQuyDUZ6aB1FhUm5NdEwl7fBy+eAz0gaEMpm+LZVEeUREyaJkwuhJYUQiI/GqmtumFXmm3+BBVsvFMPKItPOEe1wwRCgN/X5c0u2PlQuT50CUAocmAaz2fx5kqaEtrmgf2l2WJ58BV1VeBBJXK0Fy1YahgQl35VUviStCD9byTVzUe0tQbPimpnQejdxb+KTy3Z2oL+RzdL+kfxlOpmDAcEJMXZmeX9/3WuwJr2b8uib0yTD082bSZtpFgwTb/GB6N7K4JREGX6eUni1+WcvqVZPYKawCGD6/fN3EvI65Bo6KEd10zeCzngGl+L0D5YaO+5hp3n3th5moPl3dmDXEiVwaCRRAUmjyf8T2Xai6Y7/J3mu0Gd7nuxOPSP5G3HHwM/jPauY/DVGPGCQZRBgEVMVcQa9cAn+dzhvTrhtcsf4ev0mCBK6UA4n8zAO63AeaQAzvtnOHxc4f1lmzREHXXwLlYYXYbRHfiZW+v46q+feU67mvDmmiwXwADKADWRDHcb98Xpd8lJEu79dl5Y71DpbdQNBzFt8j13WAAAXwE9fMVu5ktkfXP7ttwd8rupu3ufM2MNT90vhcYT4btHnTQVU6FCLUmjrEFoJRS8maACLOGI3406QERsAwACuDeUfs9qqv1S1XJv1qAxlLNOzhABD5r+9/c/vkXorHYizFF3RnuXix36Vhb32iZ+UeOp9sE/f5rtzf8Z79IyNtbBcN4Isb/b+9uvwjsl7wiJuKB9+LLO7kKY+0bwWdndLW96K5eRYa1p7A13xJTBM8ICAsPNA9FQZZYx3DWAZWhjHEu0rGgiPSo9MMHAWArRhGEpM4DnUuNnbxk1GrLCc9Eg6gIcZthbEcNGCrnSHV7kTO7ea1RXmrGtgDJNIYy4Z0FgOAjNhLhPGMsmiVPMen9MkLOggD8VkYs2s0TGxVKcrkmjGAbG/b6DWqrTSa0cQohtnh7E4gDUcaMUN/Zxne0jqpjnfp4ANNd18t1h29ZQ1wgPvxRyfSULcEopudFySAplwopuX0pQDDwTjwkjNT1srmIyMZke/TxryQG+y2yRlqJPbxxnDykRl3bTN6EjG0hZmeR6Nab4tAMHrsl5LXorONGWZW77CqIjRT8F+l/LpO7N29yClzpkOwIZ8VZ0wXeoqVNyPcJHal+qGtIiFQt6SUh9OAvjZVzVDobMCLVuFLtRb2bIq9ATcruAXJwGVr3smtU9qyke+MWzkSlfDlGL+s8AthdUWen1QA62JmPCNroFOnWi6pCrXXE2LA2uDC1Ek74omPy8NoDjuHL6POFeb/D7OXSwg3EoiJbWG4L4SGwjI3ttj/wdghCZhb9QaTsBSf87XlM31Ua502sKclq3bsnMHSo0gz44h5+WC/bJjyage84ALXx199FkNa5XsyVqgnA6vNfjj++vEda9kOZ168mkus6BIpB+5Vr4JA3tV2ytt0j4W2uqe2R9vhJ/ETZd/POfC32LP95oCNHPKLn0Ue4q97nH01zROwSyeHux6lTVA6PsCknAjSRF3/mG+rGJxr2wgPXthJwGzkMjS/qEAC8Ym8qlveAeiKnT5v4Vhu/xQT1GBmS5fwXwuUUuERYaAmIlmUp7p28EsXdbCZQqjAKOGVKCCalNnUK7YU65TQmHZ7XqWX8wlWUQ52k0JbvzmxEx8sj6aqKAFmsCE2RNloZechoXN9vyz14IZIy32juhfW7Xkfq2Q30z/0QDEcjB7Jxf7DoeAO582Ss07HF5LU+rSxs2ShPrkYD7zkJNkasGONfUqN6JM9V1BET54AfVvUT3iw0WNm2oTsG/KotOnrUrXPXLyX4za85asi+Ghxjzj/rnuUpL9kShbDRU/wZbot3ALptHmvkSOHIkXpZpcLl/+Fj/l9ZNHYxyLuWGOGzxWgYm4VP3yQ66rR4Xr2tVUiAgHlNNXKtcAIKKdlPOTXhNVRKD9wmflkzDIUGBDVQe7JmauFUCiSkARozymIurTWDuiomQNy1hKVGRyr9a3OqLasIbJzlUGjVbBBGr4dVNXtH7WlZkUjc8c6IWNoHtX9Il0xAlfpc5t22APMaAgudb6byITHAGSq0KfmEylpdpxjgEj95Tpf9rGl0ukVz6k1B5KihsTfSiKd3VT3NgRdK8VvFYjNQVImCjbQ12EZKPhSwaeCYEwSSANXU7pLE/15tE0IcYLF++qpPzfDuuLIk43sJpVl18obyTQkRXqNeRhW2tURQMpGqKNrKslYYOjzUswalVPzxoypkBOPLZ788uqSSH8x7eotE94lEz7SVJVYzLXKfZlkawKQYOvmJ1Jol5Igx5ix+WsE4cWh7OKtQpNVZrC4MsFqbRsokvO7aNQ3eNsYEe4d0aMnqvFZA2L8QAjVUbivw2TU6PC+buyx2xlFLtWZrPg9gisMEGX6d2NYM4piYSYrl0izP+gioQORm4A90VUU2ifElzlDu5zWpgvtvzJjKlWqA+BGR2uYUFRb2uDiEoxFxQQ5MtyzlE2eyLuQ4umC3aLug2ldcKnfSXlCAqEmw2BgKmf4Sop6kYZKaNC9VpZq/ziMxEa+FDuidDlEjn1SU3L6SqWyk4U0cLp3JYyG2nX8jCNuyk3DBT4aVm09LbplCLypNyIIIxykU/AYtelBFt2VYNNLxlZe94TiA2hlyXlr0pXOUBXJuylBAXBDppmET6YayJ3K/4Fm9xipFdH/CRdToRaTBjJHVmzObGTLlS+6yJTr/OUPTcVNaxYdWm1kifXqRoe1OOkwYXNaX2Q8tYw5aRWf5JerfIziJiRbESUkU6sRIU1V2sPwMZwJeVl2fVtCWn4VqR6qhPPSaik7FiB9BrmkH0/Tpq/hsEp+3VcME+D7R6ws2a00Cfcd39CG1409hDzcR0tmDWW8sUbwin48uQWAkva1zYHEPR/+pbkFHCrzDcWe4AfLrl87JPlHujuiQ9uBFEGnQ5Evo6oe61Eg1+7x4v1Zwd35feHn/o1xYP+6DHP+JsXveoN7/nIF/Y46Lgz4iblVUNb6AnW5JeTU5/SbBVyc5ySuFgHNcWQgyVZtF+8Xyy8Itwrwb4ba/HZ359vq9MzDxMkDjYYchXm9jOApOfmcaoDPfpzF+pNvHdyC+lJeFrU04+Lbr8YxHnElBY3whoe/F1rIWrFwQ8DXefPmV6mH+l95qqQaYMw0tvd8mcJKAZIEeC53osKtCwODkSzAyOxE/a9GXsR4QWr1O8qCbh9Q5DORq9wZPo3jRA9q16K2/VhMThgkuDu9g0Fh56dFJxt+WA8nU8taATcpynvGvKdXKTBE4zSyWhwLHoVezdyl9M9/GplOvwFcq37z/sZI8R9nuuLeGqz5P33T461XLoShjEI+hGu+esZ8E8aqrQYCb+6GTRGw8YvqcwjhpRXZh1Ddb7vDOv9W7b8Rf0c9NIG+3K28u+vrOr8V7nIZU75+lndyz/ssS/hMk9wdR/9Zb/lz/NfM77zsd/M7kuut1271ZoyH90i6ygv4f0ym9ms5ja/O3uwp1qTL/2A4l0rhnz5d6H5zBtwpwO7wVv+yGv5JFBBQzHYqEELBjGFdeigxw5Bqx8ZygQWspS8ZS11uRRRyhL2yveglZKr1PMNv8kSdBBBPooSqhTlqlhs3vN7cF+ADUM1uvSDqXol15y0ekmx0xhoIJeDhu2Pk51ixhcdfcyxxlnNY5njmu/Eu+Rej3kd8FnrLycmPEkpNk/ihJ+/IstUrhdq+PGAXO0zUYNOJpjzYs7wp2V6RzETo56b8wbGWb/kcjl1GctarnHldySr2s199D0ImehorWWyKX4piTq9eBEiQY46MSSRQR4lVNFAGz0MASxzC5s9cJSt33VzJVydWqQdKruWXedcqmvPhbugS3IRdA9Yyv7PPtQ+ATqlNCBCzhw69LzBJAt+q4dDjAOtHhNXV95PIpUWdEcGYx1/HT0cwx2TnE210OfNq0J3e7iqvOnn06Zk4P8wEQ6Co+A0WkZhToQXYbqjzGr02Tly+nPyciI7pRzzzl7dtVHpf+JazPyc5btzhmKRX4SAuCGhCFp6S9tQUeWdq7b6vpnxYH131/92p1ZdC6Lqs/TFw8454jyrxffr048/IXmn18mNA3XWgf3luk9u9QtQ5vFd/ckDdLAPhD//7kRPEz0PkCg8/+zCzW+Fsqy8Vzh5su6bxfKbK/bSR3uAg90snd3ckYEnRfzXtdP8AMc4xttlnwzDCFZ6mxbOxJ12DrxmXr5P5Jsm7BfGtu2GW4045Za3TZ/n+EeDJqJn+rjPv2JeiU9/ufr4rh/X3M3PQWn8vy2c+CXvnLnn9i+kbWOlibr+fLH16YGc/3G54YnK7rsZqG9gB30OF8RHYhN6F2aKN2wpZfXpZdhLz0GneFJsoEdgmrjf22R2bv+40i1r5eBQnullMb8nNu1F+Gt/MrplFv8lVP/EbfKuGbsmEEoD16e0f5KflzNLDzPF06PybL0rb0fd2WG18ecjzvIx/7yPBcWM57zP4tyLHqEbVXOVXtaFipJ1zCZSpCG2pfb9PRDHkR9YNK/wpWpakcd+hJPHhg+x2dV9lkv30LSQLVZorS6ExdLpfvvg40BLYYsG6oLyN/3XCPhr/wMqKFl0wEF3pxbwllwgFX3vgxON72V9f1QgvF3G/u06oGm5SvAPNGDu3K6RdtFIl6igvq5rYN5pJ19wYLHm5PV9a7jaF8mpq+VTj1tmd2hZOA/cha/X5dIT+Gp7lY7l9yiItmth5CgpUMgkDfxb48DyqXJz8/BlFMRc8HMoq+W2e/fdrrJNj+deKbfXIS9bX7cCYFnMuXYAPPPF0oT0tDAttHoqY/6EW+Xad30OvhFEiBfD1RVfDGdELDWnCZPbbwzDxauRJt/j9fFtUDBIByXF+Zf6ova4FZtv6feLqeFTDN9LC1T+cFqp9yRgGiJ3+NhkoaWuUDXvR+eWefzltBSe9oOVmL3taN3ciZOA1DhD7Rtu4RRx2Qvo5Z2lyDqwVrLZG8sesVKKXjO9vBcuxjes2ykUKfVL3rJa+7xXvpRmaY2e+mxfYeAvdx593Zf7C0mJpxPs9k6yQgJd8BetU5oMbCI7v8AwMMHIRu5WeLLfA5tN4Hb/GJYc2+/hnHhXYrk3AxEwZs5rVL8GC8OzObLH338JrOPddEIAP4MV3VqZNiBgs39Q8dy/w96/AKt5zjBZlOJiuXDTcOXApP1WNuyjD4kJW6VH3uQTfXzeeKNc+KG8fwUAHDP+YvmbH3AitOEWgD0wiTbRJhZmVNvUrOU4M3ucNkM+Apat4WSnffChj9hi6hS+wbwbv+cNF+FJ62i1AXN2vJXIZYYveZ+YjgCuizT6VJ6/33H+Wsq24u6dkXReUyyn139GkVl4utzZ2LvisQreHBHalf41wwURK25HySglcnG8KZdYTiHc/QVdPq8CFk+60SuOiG0j9rsZnWs/4qaJYD9uT+xYekYbOvzarwGrECVj97GUiP3389tEkBqTDuBmbbwWC+1LE7Ktxtt0o0CFUdca1x6Eg3ZyZkJyPgs0giE4gs1yp5sWqESpms8Xv/qAwTcSLurcgw8ftt7Uyp0tOA0lt3QdGTdAOqP2QakYHYzqmO4DMWtYtyfv7ccdgW2nSP1R25G/bLt0XDrabdu79CwIHWx7uva8gD0/z3C2WHaMnhlPRssN98l7XxK27dHLc/Zp+USWx533cAtSI1SL/fEdYOE6uf8VlvM2NLIvVTRVlw3Q8WaycHcE8ytybrNr9RoRilOm6Obl/vxCrA+49dye+0gz9iWV4oUrv4Sqpz22epPtO3fRBll5zwn2C9zUQZZixy19gGVWvat6YNsLW6xqurarb0cYd148Wvh4YL1mmJajZCeQJhKCxeUD28oBRLkjFzwBHkLLHd7TCr5hfqd5SbEAhbXlOZXMMs126ae3jzM1OfQnL3Y34pC+OOa+ccQcP6kpnf2t0tu//PL7vQ+dpozN/ur2sd/2PvcByWYxINlfKmh5CFam56ByPLPKaF6CuTKZJbJ8iNUyp/LR71nOfs+PW1Dorg5Cnh+4fuaVU0/5333TBiJsvpz67LxoIZyyzv0rtmD8opUg53Fdek6uwU8MZd0nh00fhgOYfc99VOMCo60l+Bb2GmXs++6KpQAdqOi0+aOG4CtMc3ovsnLmGw5j+enkz34Uc3zkncm09DcttPOYcZ7L+sbeXkHnzXpBdXHaeQsYf9mY+SJ+lSvntMv6QLLpFIXja7EtxGduqu3y1XTSpp90Y6715cPR2rnl4DlV6UR9uklZxXWGbkLrbK8ChA5GL8LIFKCWqM+1Vfhg5iX5D5LHcofqYolLgroBdivXshAMjv5suMTqtByDE5c7mY5Fb0NRny1/3iFlf0yeW4ZAzj1CvFF0tZn97MNYa7xHnrkn5nHgFtyJO1YSjes0YBFWmfO+iTMwLbvsS3MLCDPeIduXmaLSArpaMq/xBz1Fhtmd8ck5UHKHTFgEOCd/xpQ/P9touFyccvAI5NS1Kty+jL1mFy02rS9qOkk0A/rJpum9mokfDaeJ6AtVRcWT56vXYnwh1pxxQFylug3bFkQ/bMQeV2z3/7F8Q+NZ94xJyxpb02A+Trp22D5d/0+H5nDxMtfFHBBLfuqt55OijFSrrdu+pOA6j/C5aV+NBvSa99coYiXGXH63HeqYW3S4AKAvednuchSmNh+uATyjNNdzDTZ8aG1kjMXJKNTGb/gXVj0Ywzt5KgFXzu3adzqQ00yd8P6VyP7xnkv9T/h0QbPMvUjPdWC4a7xzQkOoM+udtqzVycxP89/40Z8Y1QXPD2XL9w3V6sDANVyBDtZx6OYEFh0HrB1wbaY2FV5cc3MPELimyyNuQN5KdHe9PNJHzeKaQtazEeDj0NDT4B8S1uPXtzVOQCijGDhb3M27A8U3nSceKE6y1Pt3EqlQzym5vyVc6Ty46TLGyL2r4hGl/bL0MbKzfYoVJYqugmYaSWNZ4X9XPbBcOGpdNj0cpyFY6DunOZmM1bZ1aP7FPMP0zt7ZjGVoZ3p1+z7O5Mls1PwGSP0/RPGLfV0sMWY5r+7q7LwLDSY5IuSToYIrcLamnkEbUOc0r5nnTT0gmKMqz4K4w0btX+hmGBTXiZ1d9dQV0ydOp8Fy1KZbgpWKdxD+Q6s3XuiJsvmCNlFVDDStnCQfZfssJ7Zf8S28a/RRs+I2V1rvkIJk7Sphmii6oYqrAv/PiaMz90CCgcLPQ/jP8vzMvFGF9Mo7kCk0Ib3pxZ+3LWrUXIMfs+LTAAfw0FZh5W1ZbhktQjc7YqJH5c+H+RtKVL8J9X/g7aN/KwfIUaFViAgxJkqRKccs+RZYRmaMmo6Fk19UWtFue0HrX1fP9k346vcP8zp5twWqtDewvWaCbdvWN2p/VL9+dgBHb51ptzeDUExT0va9P1BlA3zRvTnPvRPf9i32yyE9J3zLPD153W1zZvhOezWU7zqE9r+hyw68TbKxT5xqa1//bIY/0qG1h65Vn8RtOk/gS5N++s9QPp/BIR//qxDp/+drwMfn3Xs47lKEx+FiXPxwHfriuN6g8jS48FBCJVHYNEzlXVK6nY2Arvkboh8j7Uif1RA4nkYTws1sI9+MaywyDnqrLA0XleBMvgmzvYJSsM5Xz8kG91jRqulzoxmhPFwmDpsiGJpwe7RMEq7EKEXqXpCR0RGLTJM7x/J41HIl3/840T9OzFixIxttvER+nHRSWYsDvEy3efyAlu5oaAL1Z9zy8vTqnFo3+FY9zdsA/rx/wrvB0F+8WA1M3J9xCjC/GxtYIbz18kcej9aGkPCHXocnJOKE43AyzlT5vwnBqRDYLy03h6C8vlPlzb9ZCyG/MedbhTBbGhxNIfyWFhQ6ROp3PLiqtbHWEWK+rxTCi55ygzAD6eJQuqKifHYQItH+QIC7qSo6JKpuDBGV4ptGqIlX47FcjpG2luowFa1KI1jb+DtkYcIXx4yib+Pz4/76Lbz/Xon0d7bwYf2HzA+yDw0fNlY5tbEv2av09e9VXz7itUv2nWsER9DzOwyBzxNnCcnW8rbD+0+STnLIO8Ck9say4w5INR1Ba/9/Fc1eGp/ef/T0xavF5dX1ze3d/cOT86tbUdGbnf7AtIE3htEUEZaX1VxiUCKxVD48OqFUT+kMJovN4Q7HkplcoTQcTxerjSBBTL3QK73RO33QJyHNtZQlV75C6ECDhQDJqiVARhTxkDJSQxriktL65BSUlA2oGTJizIQpM3bKt9JSXzppzTwODF582CgJElXEU5XxD73BTd0HzNtgaWVYajRX1QiXlq7O5fH8rJdy04nTt4jIf3LpfEhRk6dBQjfabYFYOpvYrVidSJWAKmYUC9YUqlbCO1jtn2qaT6WafaVrrCXv0q22fTIcOnXp1qNXn0FDho0YNSZuwpRpiXlUKH3nGztkcYXhU47z8kzjixUrVa5SS+tKKlkfKj1GzLLKjhUnbgUVVlxGmSu+zPruXPVc+RVWnEHsbYyDQ9gFRQnVYfMPzQsNj4SCRp2/IKHGihQt1njJ9nDyiIhLeYGOJUYs4iMVJNAjEQR7VAqk6ExFaPoxk6tCcvlNEvoPKSn64dLZSaEJcyljL0Y/6VmF6MqXCIhdYCShVM7zltGBCPCRivakNZhUS0lGJu+lMkL5NrBCb1ni8s5dKIslMjdA64HBucXLpRGMLhg0fGIgAJuUdR0I3QpYdwKK+ztAMFSST9a3MsabGMubD+sbDg+hQBxJX1aBMKNwwP3jdYiXOaCaV1zRHoYUEthqghnm2+K/AF7AwmLVi8wF4tzoDo8EiuiEeVyNW3EvfCI/rsdAMIIVRylImTyXAVmctXkkr+dEMkuyTOp6+VQ+K3CBKkJoBAJEsIAlOc+BVIgWsI6eXpDa6QN2euXA3gIEAwcsCRBM7AFWIQgGmy37KoLS4CX+03efYFKZSJ8dCMAXeItl+m0epnoOn5+U46AXfxpuTHnhL44m7r+6Pln+zqJ/Lgt/IBH4DAfBZIeLEAnS9mSABfCeHUGLr4aPUE2HIX4ruTQX4hhwxuqipHeOaSLvOzHkT15bvvd0ggPzuhwe0vs/O1I4DU6yczBQ++jxr1CjT9jVuCUIzRvBOqeRpgwLNpdHIS4/byzbD2NQGx3LXTOELznamKKqJSpsFa4e4Zz2ky8zYGOR9lhyVn1G1m3ik9SCy3lxcExu5aUSkL46Qnvd+MPrJFXM57fsJ0Y/3Pd6kpDsiLf+4uMJ5FVeHzFz8nZ7mzcevJVSG3neUayhgwpEbJ00eWWgYbf1sVQ1/+M0T5nc0NlsWavtuJ3kwYLcliQPP2mVad+ss46lBe/uxwpALjDFHyzfFhNJZ9spF6+nu65dWJrxbme70HBZ8ewScczU0iU9cNhXzn3m32cGmXVUY/eE0+YdcMxJ5+XUpQf7WL/Rj1IZrwrryDf/qC32GBUfiTVdU/NBj6VExdZFj3130M7hkRWbD/aGMoDAvDfJSq4p8ZncC2S/b5FYuHWOBVGOmpH4hHvpWVS1BUQV9vgKsC64i+rRWzMHPO58GOjaVaFYTNStFSG0PVRSFbzepDt2pKMuOMCyp7ovsV1i1vU2z3NhgE1rjLXc1+5axMHFFBE+2r7ib02d8dcpkqSielu33bDSx0OOgpBInRMDC5THkJRUWifVI0ceEKR5EewMrF/bSlptma98444FHFR0uKjrmUSdB4hblwTdwayw2Odu2lVbkaWUue6li5oPP3lNeqXD2/XBHeHXTxW5YaPGqUwyMnPwCYlNzoCZIv/rKLFy8gqKSiC26oEcgayoQT9ATRlCCY8ZEUJsORKlhosoO4o8BYqqAFOqLHQ0BGT00IUIK1y0+KKDFQEFFzF8qZGlRYomA1WOvBAlkGTI8iDiJ5vc1DHndJPn6l9gwRknMD/juMvNObmLhRaun3CJysSTDwYiRYZMWXLkylcIqhgCGm4KCq20Mjk/AhxSgnjfk2HhERClSEWSjoyCK3c+Stxc6H98v6X97KJl4xYQkTDDzs0vLC4lOwyNI1KVtZi+tWsIhygxtuIrkiw9PDgUbJgYIKiYYYOCiRKXS7KiYMqWRaAzW1wyx91palqOeiLLUTMsQB+0b64BYQmfsRFXriRplSuBhKksOt95QNUwzbypixSTfYP6XwW6TDT5OrI+CJccn7sy4SrCpCyDlx/lTDqK3CInURchnqg9o4MRVhDRutbm5jKHLp9XWmtEXyaCwfpA5VOo3b0woXSo37LAiSCyKeQvGNFT80ScfYZ7w9E1ff4wHbzs6w1eIFd54tEPh9kgoLkbzNwPZB6EMA/3mS5v+1jQGzykrin3Rku0uFyK0Dhd9V9rNghze46ehMDEwVeQcyU1xq2FnpWdi+dYVBUQwlxfpSfEocmST5B9RdWVnYqWhY2T+zDKBxYeHITYkYWhvviM/O4/MwBvJa2QJLwryV5Vpp0KXJxHNHIHDUVcBNRk5TKhaSJe2dC57gO145CZLCDh994hL3QfUuXhoxdUaNBiqqdI70PmFxAWEZdQZmFj5+Lm4xcSbngz1XplLbpZXLPFymOqfU0tRhGMHU9O6zAgHTkmyrvwIMw5FG+hogsWBoYp09TMduJ8LqvRYhQSNFho1NKaqcKIgL/6gsc4ApFM1aCfc+M2YRPj9UiERmWWtVF8daAq2AriDDZprdJSgJkFIqUJDRJ5c6qRJifvTBEjRQY+wH2HzgHvni2k02YK8bDkHjfyhq+tlhQkA4mABzJWHR8kX4I344Mf9+Cj9512x+x9FzunYDXESU13TKpyknZKeXv7/xkn4rizbXWF1lW+54iNnl59DS66pu21Tm1RjBrVfATxAxK43/bf4yhHTpLyHUt+aVw3feBxOjo5aIfgyJDI0MjwyMiLjOb+ScbCyxRWDHwSwPImvN93DX7lCr921R/vYBEEtQwLqQhFKUZxC9TOYpFztvdigtu/FhPSloPH+YUvDcclf+f+8WJlykBIqfuiDD3llcTG2NwJ8NKQnFifjdkaK5t101wUq2P5I6+uQpK5PjbKleZcjheNA8nr1CyzveJe//Rv9/mfBzx0FPtE6CCRl7zsVf/wL//xX/d70Iq+uFgVa6I41sXa2BCboiLKY0tUoQeicL7plJUuzrLFigvuC7uOB1Oj7kHiAnCSM1wS1x0cOsRacfd0e+AdkggJtgwcbaeBbzxy8Q2e44H282qV00Jg/f2OPCP9/3pH6pvp31M/2OjO+aPtTTu1/EWF3KI/P1hWfLXkt48CpYdKf/Pox8eDZ4HK3zi78/x3V+gl79Vv3tx4v/fqJdqp6g+mP6/tr+t7uORx5vtff57VcK75lz46Px5q/801tHzbEx+8Z/uTDx0eObz38P7Ddxx+4P2HKI8tjqfaM/S9lPWOp+58mnorLUSN3iNoDKZaxdrMPTOnNiuLuHzXLffah/aue8kOOc4p/89RiFJeugGnkGoGM8Y5dtG5yfW07mMJpbaxPbpfn/jE9Qbxw9vMLJ9Xs7ksm1WytazPvvUMv7R5DH/XIL9A+002zVKuc8WLWhPtwcZNmWSHk8uuSQvj07Iv5nUrgYDBwZ+3FUKRlIqCj+mYT/a0/JH26EXbbFvrxrujXVAnGz7orC5rrtu6oSfoTD3PDDOcXe2EjvFWr/uCr/qd4XJAAhukOB63xNbx/iiPWnpY8dwaiP8UJolBLHc0Ansielr3tMMZ3Nm+s1DutXMr3MkndiWJ9nkK15s8nyMmCIDBuSoviTNy/xU++duBI9qEtkF4FmyPqCe7a/ukF7ghmEtvF4tBQCCQt0kgAkEAdA+XrOOfyVQVvORuvIkpa7/chUEPS3Ma+eHBoL1fwSNCNSH4b/wj+Ut+yb9PutwT1fgjr56typ9O7z0P3qPWP9D8xeDfqP8lz/4Qav4IBv4jM/+T6Tto8m5yPpiqZ9B11Xf8sZqhv8Hz1mXzwVN7pAOxJF/fOgC0PoBNeMTQRjJpFQ0jD4R02DtaEBwvnobVcsOZ6Y66eZw9n7vtNOZBBsMLXkiYWAs4+jJYuMjAi0Tzf15ttn7ZgLrykaiE/ZUx0p4eUGxm05u91mrxB3wYteqrmzgJ9M97f3pV1c5VaOjh0P9/9UjhYPBppkxzfxWdtY8X/zX//mEKS96vyEkw3V24dPKnsuvXN3VSPFqoti50mamstZfP8WWZ/kGy6VyVgfjFdyvyebT83r+bxEyWrz/bavaf5PgaAqjw6LMWYIJaBrBWK756Nfiu+P6+AMzWtdvf++CaXdQp0WRmJwYbb6seX25hVzakd7w9/6HE46KJv2WIEIb09H2n+uN1wRXk4beJSKGeDg/g82ZhXCkkbboonH7E2OIm1ot7OtFkry4gG4ptYpk+TVk+gOfQA7vcun7m4mTM+sre6U9lB5Ob/i0jAPwc8vrnL+cpscID+Ad94MxuHZNyraMBFl1ub9u2U3HMQJUWsLeIAJF3PpDP3Qoyx0ZR5FpPeh0gl2r6OESZNBWzqZUGLpCOQyRVuR+2XHVMMvFl+EO7pojh0cL0fHZ21aXpxp+8rT/om2IUdc2eD/7lsj2oxA9t76e1HUbiOWDuGg7mEA4iol/E1d0aUlaE4kHnu+jDhslsCGQy43gxu4bIbnUBnVRJMU/vfAE5Ir8JVpWsf7GuJM5td+V6S63vcABg3jmy/bDGYrJ0HHUwz1IMMuriICT+FQzun2J0xsXGa3C8UDCZ5Vzv/+zPILEwPvUmO2cr9bUTlDMQgPy2o0vl84y6wuE3YZvBolYHLxMoUk7whJfcB+ImVN0Un+fMbgrHBrIXOD+N2skRp8dP65WvmjFMgp2y+6072R+vW/UD+HjPColgAgisETGQ2AFEz4bjItCOB+6zPBasu40PDCeEeYeTc/P26E2Nb3RxIWbqzvEIZsCglFB+c3xDE30N2DwMoiueZRHkxIlty99H7v8a1HQB4IE76+n9sb/SLHXtIRMsw+fbm7qxomb6vtoS3Wz//RdUstfhNaZr+lftMpApnqeZx+1x9Gz+k0JZ+0YCWQp5SctiOIczCfYNvu8JyCnaN3x1Nz34WOtBE3PyLW7V/oN/Yn+3+gRRQvbWdhGktt/A2NUIyGEPIKfpW9Vhg6X5Hmrd3sv4CTmRw2O6HbFc92T9I10nZqbWUx5MWphMv3scCSTfPLqPHuDsnj5KuEG9ou8evGBDazacnI8fJx49cqGwhuqFwtklfl4ZIX5AQgIS2aybVyi5YvEqy1nDK5J9QpZYhbqCV5yYsErQXSCGgZ4jrR86GPw6JlVH7G2uvti3mdu14a+70DvfICCHhSlsT9n/DZArf2MPA8hjd57NcI8lwt9+zJjPmnmbOdgh+9TJAFHTxEJ2seBPwRmL9JzFvZOcfdkSQJ5y7QPYq32eBz9oORu/Fr73X8pdiV5+AwuHyNEqwkSZZiHp0oaM3JdrAi6uT2T1oRZF6z4cDfTzmgmPv2YOn7pmnhiuXyDLzHc2r62Ij11Z+sU7xgWXvvjV5m7LOVaAGf4jHRwib0N2gSG2baIryv+Y6qdXAGZshrMAsMyCxMpNt0SaK7LxruXb1LF6ckakBTwqSWq2XEqGsqZkZdO5qLiWrmU96zYNkhqnoDZFw8zGJyAmLW+GS0BUhqBRL0FHTgaCZpdTzrjkihs8oB/DWS5swQLCE5cqVWR1NNGXYY5c2rvshuGhT3zbrmNj5YvSt4BYeA8aJiKUdNDHKGPMMcI4UywAHv7WmmlYP44ibVnKhmVYNpgGAsAyUX5R9K7i9nb9fJDQDQOrwXpuFBaOPWnStJz28/bVsZOczITi1Ivgh9k2u2fvmZv7Qayc7L4FET7SN4WMKUII16SEYldZR/+VqS6b3PJXXpC5nHSpka2hC+9IIgMBlbTT2w+g5SQ3GYPBPAfmimCr74eX+mjyIpuExviyfUX60xDvm8PTAdyPm32zYUD7FZ35Ml88mtmkm4bXP/23QTGSjDgj2ogyIowEAPlnGg0sMJ4Z1CkA6b6RZqQCSDod1dlfSj6dy6sbjAoj7xv6qK4OQOg/pdSXeWA/+PTtb20fe/DbH7/677c/tf3J7Y0nB072HT968+z9rwG43+zDgwACwMOQY9uPXr93+h5y9GUA+ajFh08DsEY29yWz1aceSw/a4/mj7FFKHz7rEfuIeUQ9woDphGvsenKtYjkAY5X273KR66tE8//znccw7nI4LIyfmnEP8ps8ANIjbpXgxjOceIo48aSQ/YCS1XnON+kXnP/nv+nQT+jEwvi3Mmj5JXVais8tvv4Xjk984p32saXFpyiMv+OLeMuG7OkXha+iMkWX9PO22JFbVLRrsvNGF9rT4LplwZNDO2BRFwq2zA19pyCf+D8bknct+OSzs2cZL17Syp0IkQiR3PUWk8WJKMdpdU5EP0ikKh5ejrUlE1xsy/eTsnaTKDEi/aQnvRvS7N3m9gLlyczcB2T0y7w958+y78ZS9PVC2+Pcl1keHwybEyfnDI4FNUxBETDgwBq+Pdjubpn/ssAif+Coqo+UHfFFEgfqh7/YEhrFtG97lqI71oHBbnqPpYaNqoea+nT0Qfsv+KwHJpECC4uCUV6WHYhRVtnr1MZ1gVQ7ynKBURc22oWT9savADtdh6s+iUSfIq5ariVmXCX8dnX8OAl/3QR/2XghFZLbJP/SHD/sJLJ+cX/f+HXnebCfKIWQ32X+2B8e7Z9xnmyQ5xvh2YZ5oVH+3iwvx+at1tnRmorckJylDUPbAHx2Q3BqcHi82zm6u/jf7uTk7uejPczZPcjpPdDBovi46/i6j2u5Pq14NgPdq9kymvEsjamu7AqqGzBofCOmN2Zyo57kqw0iDp6JsYbgyJPXtsX9polX0N70ONVTzqvvjpqigtEDQFaOTzgvOxMQEUyI+0/KRMX1J/kEHgfMYx/Hq+RuVZ9r/lALTskgGRb5GWiALR7W5qumSBk0/r8d9BxEhKzDhTQ/LkfirEJFdpnfgTPrU6zazRVWsjGm7J4xTrIvs9mcv7W+NeuiBeaba95Ij+iIcPcPzRlBL+YXTtEUT4mLyK2cKofUzEbWs+FYek+01NNIM20KFcWUUMb9kYWJZdBwsblGSwoywOxYF49IC2FAOg0oI/hMZNFhylMM/4ip+DrmfCDmS+y1fQHPvECt8AJKHf/FLNwOyLcDzr4HbvUnOPADgJ2PwnxmOP6KrsewnWgwaPbqdCtDUEt4xYN99hlDmBsS9ScaCNOiHlsfdqsh/z42A61DTmLGhjm4GkWafQx4FEIIEs4yKNTJ11OCYZKaY0h5753QnAhJ4iDaFKp8D0aQMpKGlJHIJq+wZt3cxACbgcxFxo5MP3KKLNo8tDBqVNg3wUYFjs4sbFHkYK3xkBlzGAx/ooA2D5zHhwGyPp3QExPHzREvBkVkBP5R54afp7wRiegiGSeIYNYC4/02lxJkybnUxqsJa94SR8hs5eETlKCCcyCEE0njHgAWfgMRxankAI0Tq4wCKQwHcYuhVOo7vXA2ovxiYseFvOFZZAveJ7CGpA7pm1ySLdIJ3iQRJJ/JamKZFIFysmrPZPJbLs8rSY3zUEiZ0IK3hFeGKzATEuJDxwjlhITZSxw12XPmogzTd/3lTXnZF+159nXwEeQwFdzKgAoXe1RI8eKDUd0IUWcvoLqxTlyErC4n9kCY+LzkOCkYgGRG7MhAw93j73nxjSSVwXc0SiZXapde5OCCIOUzFzLotRg4ffuxkTR221MlFqoC3Mg540chh5WIrQ2kunlSt3s5neBrGKaGz6LhLzvszcZvqNerDjxDYJ+b7kEzRYR/tc6ce22a4CU67KladtdUngjAwXBsDFYOwWRZY+ScezzSbkHvDjNNHnqCA6YN0zXhbvDamda8erHHMN5QNzutpj0VYqyog6QikhpWYWoY6t2wU/f108cOR7y7B5lJ+XpufFXDij5JLNhN6uCxv0ie5dO6xmcEM7BDUWWnse0lvDgWdwpGSrXnzmOWuwDT9MagKsp/Mm6tQ9ND2G5Wy00CKFDJl/P+zlswvVj8bQXuc4Ckmm50otJ/eKVE/2EP2KY8PklyX7YOmAoxYSp79eJ+Ydc46GfuukJI1Y4/t4XO2vG+xldFXa8qj5oi8pXpqh2+U1ZSmD+TuURR/rlCZNQYRlfXTZl97XG3O6DZ7/F2ZkQfvynwuJbUBLOr6XTej52sPDQUyXQ+DoOpsq4IPQe98DNQpperlUrcTBYzuPf6K2Vt+57FftCNdX35AW4FMBYcRIax0Dgm37559H4Sgk4RIc82B9fvyn3B2E8D4rSvhztvorzoh3LUw8Obb9G3s3Q9mVW+4APHouPuSI8Fhr9HiWy0i+Pn+rw3eU7Pd56S5yq3U9sfLQJhlkY0f8638soabzOsjidJlLS6VsAJD77/QiUI2AM/HZbK6UD/6XjBD9uZuj3ngvWacS0iqoLsjpPLHuCXuYDNfh6HTvviVNi77PhDO6REZhxjL83i5RmUe0FuLnt8Oz5t74v2f+HzZ2s39m5XttULl+835em4X5w20utVB+z6tbJxp+WLc8HYUBxxDm+ukfRnRvvW2hEbMVWQ2hI85Cp1o4uv7aXftLKP3mlMQIbDSOltpiDf0foyeB9UukNKFwxCHbZZD02SiLEWwB3kl04axZc1WY/tYrkLaFOFLGoH/zAEVfBwX4tCig7WMoiZaoGDbdgiA5m0lhd9GnD+UL4CEretE5fp8tAXCbCJTZT68gXOHeX2mHZIcUIyn0ORxGDwCUenZNwG7f5igLFTtm9LKcoaO+N5BJDbVYhQp+mUt5uChj1itN24TCyaKIGIR0qdTsBG6PbOYVJVfuok+qUDjYGQs9YzlC0z1gRvqDQt1P+RzXnyUBZyRIGpKAylFkqU7zMZym5A6o+s6X51pygGGKFokw7BlWX5brAfckhGhyIUYijUJmX68D2gGY9SlOUd6QxDamKzb6XqcfIlRJ0hXNvpwsi4fDQymk3s4VHxxFJLLMAPuPPrsqy3KHqhBtauJWs4saxRuUUm/3cxcWpgWT8x4Df4L3m17aCxjjFA44GE1mh4TStBSSlK80SNsHLickXTxy1juxIyKwIioCOZtsYVOjI1naFsAc+LgQjDdHcWxlpimzw7spyJm1TimMzTHKc59TdkvIPxhZqqtMIlHR49MnCUCwgz+d21H67Si6aP8IBNIKt9Tkm9YHjVOAcUPe0Eb26h5F+9k9b8DNlGjbj7Oy6lKM1yJzQuzgxAptk0xo4OR4VZluPFjzZJItxZ56RiZIwcNJhep6M05pQp6paJy70wTjuSstuWgOD8HEUfmSDhqhdJ3HozcHpZTwBlPT/SIQxlHDCelw+e4znswI4ieGoQN+XXTZwZEnDfbd0EoM/CTTWpPa7octvpbCa7j800aZplOAYF2xbtJVg+waYh2i7dDusiKmmOo6ktdGFM5dwMcjK8wFmDoKaugMm+AzT2sirAsdE1vZbDRBynof7XlTomzzfWRaNV8dnPirlW5QgNlCX+exNimJvpwirdhAu+8KGUopxWp3HAkj9GHDqEFOlH94bI62LJmqPIDzAo1JX62DjYdcihoDqhjpZnCpSgm4MxfqFBy7Nj4CEQWN7BBoXOL4aznFGopvQkZjQKKBdWqTJlnJosn089LftZgVv1pDMrmKhrWbQaqmxBoFCVUiGUmm3/SZScYqKFDBTKPpqLlEsq02zxfJNWzVNrlan7372NGrzNChKUjPwStYWmUGtxmDUOlonOpj8+R02TrlaPhcPt/5qx2ypcizS7rtwgUXAHscrgnaGqeEC2PJfxZbbI16+h6KkE8uVEoDIvj0GXpopFNlCOZgpekhM8kAkg2RXUb6PBh7cVIS3xZ6Y0MDNT5qqqQHk8yVdsWKMpRLAhN4HqTQSpxcUmH5K+jplrvTsAGCSxyKnUsjnwB/rVQ2YjnHz+Xh2W99JedlMviHfB8TC1KqSeU1Jx5DfR/StvNmrjejNBLZ6cUtw0mg9L8k0rHWH57fdoL+ivzOnZMhercqYkykVThQ8HwDRP9PHRqy6Mw0j77a85hXhfHRrdGUm7R/r4pnP4okmYMCvbmgWbWJoVfgV4b1sEqdRvSOJozCgAreFGHNpxWzICE0Rkk0FNqPYHkoLbEfXg9wiD7nkw3ZgxM9GLzkF0Qhf9gnkcErjGHOW6PsfB65TmdIKS09YX8MAFWx01pTPtTS6BUjMUqYzMX32MZUzlz/MAIWksskNdtMZQKIGZFoSV6aYwFoxf+Z67CjFwdbZD+rP10NoG0R7V8h4QaAsj/RjqGIjcgSoGRIzKNd7RbaszxwyTWDEMUcmKTIfU+dgYQdeYfp9CoXSgG0KlZWQbHZ1f6pgDeWwAyAxDeAAVjOiODZDvgI5jRCXRr+MSybJ4qUTzQvaZTCE+hbTqvR6/CibXCpgfpTZ82xY4MYo97mpgKDWy/x7Yv4Y1XKLrxM2HKFsOIuR+AYMGxRbjvxawbGDIrmRVXgMIqRw2uqEmJYSdMmIEqo2BtzxW/EHnUQ7VuNscQetbS1PrYh72TPvgGcYqE0awNjV3R3oXFqyc/YFQTzb92lkmiu+9Poupudur61Wb0Wohm1IwgW8J6sZStuW1UnFk0iNnlODhaTJ8tBA3CKZLgfNlXGJoh2F2ZvbxddWYf9sGPWip6Rx4xZvyM2pJ7qTe/xObyhQy3A9G1G+unY9INrvKIKPOAW5VccERR696YM/+Z58hUGb4t2cJmXOc1tYXwXiFLhfnTYH83Zu/+nbVljOUbYOnWiyKforSJlB5HmiyBo/S9PqRDaFb8v7x569eoF93nfIQR2euEtdsBXlJcKBjBqidS0dJdK7TR5jDqxG2VunrfYrZOX2nsESNSL+M2YghBG1dNmv/gM4U1awlUNiaiSMhQUmKShoDu3cJawr9Yp0aqH0JtYjrIEK8nJKTsQQlBTHYWWvXVCNSSM3OROiesEc8QM2xi1zWbFqnxcvHnMpUrsqFNhgNbnuutbNxBz3lNR59VisP97LPwJJrjQxoxmK5IDt1jXOGlboqwBUAaWHt4XI8Igc76dTiC9lmtGE9KdYakL7v9AaI0KwX+F6zBobgTY2PQePR5ABm1FW26VSr+GTKWY/7OGZmpy7MY2GpVFk0eqY/t7PzykNrAS44GBNDeHmTa+CgH6hXCY88CMJMgLNW4UzsmTlTBUjduzLdYjHflKRbqxQ358nAjKXV9S4bRQmeSBUjSxCiI2NKazEaKrMY/LHPOKRWTfp13fBVrSGwygnGhjLqiZnY1cJckDw+OSmWVTCTv0xXpFnJOI7dyZyiWoY4jQTHeKt+jjXI8NTFcl92RJ7Tws2N2Fk8yf6JLh/ollzJafkiCUpz6QcjxCLyarGGg/0GM4bjE6EVSkwLg5aCZnJzX4GOpeWqSeTxl8VdlEZpf5rsDK4zGUp/fTdVk6KkyNkBHkAIeLbn0vD5nohXfaFyW4jXaFzqLFCX9TTMnnRggZxlG14MG5LW1kRKDtm02+roUW148VCIxGrYFHqoRXZjJcQ9zVKmCbxRA1Gw7qHboW7ixXkJj8feIGZmBNVLi8YxDX4dIPCS5FFk/ZTC13sB9sUFr+6tB8osE1r2OEVcWqOCWbXtomOT5YBrscKabKcoPVNoezr0+Taaw8idHz6m0TB/d3YTADOrt114Bw7dXNzliUjuloUtAQN8Lizf1bjbBZuPUCQb3TdRjQBgOBhz/wt0heAVJ05gLMfFG7Iy/KJUBDCVKqjhRFUZQ0QN25UdR2zIpC3iittJ8VPLP5Kg9NzbXN41IatMtxtHuLMzIwNA82hCMsYLGviEObfXLES6JmoyONztYRjTvw/QgAZnEPkcKRYA4rHpGfWW1QBcRmufoV+Yc8wO/MyePHChOyoXnY8QkMnjVz/vofPUcgYYvq2StDFOz3ELw57ZvHD8T2YGEX6dAnWQy7GwnznU4cMfZvzU6AfHhaHg7u1HbtXRT7HUo63n9DyCcYPSmZ4H5+F5aniYazgQGxLzUKHcXtVpcDUYm78bCMGdxfISssgGSMn5K06hdWsOh0Ke82KGsQj4Qw52+ZC/LpSW72EBigeTCQrMI6FEwF7VsKj4B2D3INn5yhJ7f6KarKyx8P61eaBA1MC7V7D0LEBqSQ8gTHHf5RXNwthFKluU5FKFE0tAFtk0LmZro7J1RV670O3LiZSwYn4wvQ48RXuWyYVJvSbNGap4Tjh/6hvxbufiai7R5YF9E560NZVqqHt7Jzo1uE5lbqmgh1F/VocxkOa/uFiiCc8uz3L+4YWueVsynBKnJyug678AihUL8WI3dhk79R0BPKqS8hyWIc8yqpWQ9Z9rg75C8sXb3Q98Ir9wcst6OHk4jPuDE9WbxPke0adGR6MgZSuB24wXu2CTtRJTvf5doRE+RwlwEIfUGOrVFtpbTGymPmBSv9GIKfr6CTn6Bry0N7mpoTqyaPvOv8t/3d02bQvj8jnqlv+l/nyrlrNvlv4KFKo9/IQ82z8rv/3QxKb6JxY+2d8uD6cBTczq7iYSHgeZQ1LIoOkdxaJhYcXgpggiSUaQIrYn9kdJpYP0bv9dOuTS6JlwFtRflznfUTiOp1/FyziQ4jthpi1goTL21Ic1En7UpWqHBDkcPXBAmjLHenil0vGhExKdkwI+tgz2qdCfqX0o631mR3No5oXcfHUu0+AvZobdNKUqLTdgWbbiIU6cxl/TznbgMtXFqYnZV31wWsxS5h4rHIlirEWTB629TTjODlsF+0Mi27WtxnHsy5iv2d7IKw2WY3wEI81sfwHTut/RlQJsZmPsEtxyKDTF6Zx1OjkNEhwTq/+DqxiBbVWcQb0nczis6C0RYmcQimJe3XoLRvYe7xyVyKPVS30cdJ9PjjbWrtB9fNXaZd+24rBXvdg880mHw+ufyKY6Iz4Xw92W3QoQXkatsrjFp+cSU38ttiOJczhmYEVNG6QsOr3ND+Pq2OptqlPprirkSdlGsTmMb8MGNCm13W3tbH4ksu4y3vtikEYjxS+SQcqTkatUlLjta8pUlFr6+jPh4r8PocKzEDBidzzLvUBNKbrYl+XzAcviVz4vn73hfVP4ylvlyceqq5OK9F4eTwzfx90RYmzb8yxzyLztxwnbIGAwOrSbGS49V8nWXhinYAISPdBXXsB8u2i0o8PXOqrBWDz/f4K0hQ8nQ7n/gDIMJk2uy3QrZ1y2/hDwQvluIEPr/o6XwUC5x4PRievf1nne1ioXfP63gmSc2WJ1tlx1yuM9pcP9CX8pFYaWylRQecDZAtUTTSQ01I9Ca/dvoGvufKaXzCpSGzb9XxasFuP6Kb4rYlph5bT3bU9ipA4vm3Fcgh7G2SbDq1SVWDEhp6SszvRhuFSd+HkEeI0ERrNy107A5E2hQ1CgHZmxLX9nnXINUVqQ+PzSYhNDC/SSmjvD0cSd3LAtCwwOTtzA2sahJh6aHhB7uo+n2+5iqJi9h8LxbtN4nORwoDJpIJudfzQJYrIuWaQRdT415pPjsjNyHa6/5m1Yr5cD8R/kNR7mKt7o+w8gNUszr57KzPWNsaeYDRZmiSF4PTa3aNfOYtm4OXcz8mBff8dMDYgKG9bilp33SimwYEdK/AoMvjA8O6Elo//EBlN7cZR7oP4YmyBEmHuEJH95GvLK81v6ekaERjK2WvJ8AZrR65pwuT3dqPRrYA0+V26tby90pHShLZ8eHQsyCBNBr6Md2e6/6/aof42DegcYrDnVZkjsTVK/y+kngItmzuzZfTvcDs/dtNjuTxIts2Bjp21Otpn9oVacVx+pP77u6RrGfsruDKnCAlen5QPOoTVkDL0H3ueYJnd6FvZwg4G+9hPXQoq4/t0WpqFHL9ToiR6nKfKxtpVKssXTiXLBjMVYShfjj+/fqqTZuu/afsN2GjXHqtUtoyGtOEAu5ip1q2bp6PeKDCxlpKgJNc2wK63yD5NaCZmY0i1/0+b8urAkeKjtOWkJKKRs3ajEMhpEs4HxEjdcsiXhJQ/tL00kHOkKrLkGoYZWmAjv1KyiPQFHkmCH0U/ASYS+jmd1UkMy6heWpD689KMUPC8JO7X/Uvxjyj3N4m7f6Avd8agZHSsm49b4WDIYLKA3RaeBKLlCnL+dDVvhdkOR1+GSQYbNzzygLzQhX/R09GFokefvRZu2mJqC9bhGt4yTLJeBtsvZ5JbkMxoPcxXZ/LZDns5vv+OgbFhEfSI0QpgPsj65xW9HbYvrIDjWB1CP18Vx0WGIJLb9tigjkmfAYysbSjFnwLny/MqG03eSc2mvqm9QnbiN6imhQ77k/inhpJ3//Sx3q2dQ0+xOysS29/BeHRptdgK02G3ol3Jn8BO9cak+4sNPT9c6V0oma35KH1Af8Unz3qriZ6g1FM+94BefANe3gW0ZfRdZpuBak5eOatcht9oZ8+uHbE+CTloZfMahq+eEts8PwCKm87e1qa5W0qejxZ74eaFPeRz9wfh+a8BX6R0eEI1efyS+UcsNswWs6lyTI/Esm73031iSy00XJv0DciRDwb8qKnPIz7GDwK7esTeIWokx+yB508Ed3eod9EZqOq4JvSPgRIwIHvyA63KBVFGP34HWcdqWHXPNILgYGFK9UDqHHnaPrW4U1aFV65CXAUub0XQgbOlALlcYplKLIZklcwt2Ydku1pXHka3LYng5ZGSErMo0zwNjQOO4NWKgTnFNuXhQEgrqJJDwkWXLefuyRmKEe9FyFWd117sJx9RaYg0vrhvOHIB2Pi9nbrB2MhDsRCnmkb2Yzt5kSnzJSheWByI2bAkT4YfLzfbPA7dPJikR36e+1Nvwm8W2bGXuEOhiE9uxaE28ogBoL13h31HEcoy8DQvlougi3wVhZ9R7AQWlxQWvBc8bTEdK/9MGlEcvPLwlJDL4WQCdj9iezIe/yOcPlMSGvxCMKtFlaF9WE/5ipODeZ/WyMiqQqW7RfhmSjCxJManYEPPb9RtsH3F7W2qdsYh8efj+FZDwWmk3Jv7gc+W61VsOHEfTiRF79ssolNgfaNZ+8fFz/OybtQBgy+QKQhZJMCXhbI2Az3xUnpc9XFQuFwRZH0gQ5mHj3iWan1568Mnd3lZ1ajQ+BWOwBHGmCoLcTsobbPkiUoTaeUrcE2/niulx0PHKDjT7tcLhZbOUvOk7a0altOowM3VbcGadzHf5xK+eGJQsd14aU0x86wiwrJJfZu1o11eULmUe1kSCXkPntB/qiyL520pduW4TkzbyaMVH03CedN+FnTzcvBFohQdkm8HcebC/s+uEVHdxucG7/OOpTLwn44bBdk52YBXxVkvZvNX2Uh/aqIiLdCLZEVnYCN2RIMf8RpLg1Od34/hsaY0eWIS/wQM6sjjzB2QsoCss3Jlc5s3BFnwR8TfN8HKaHho9D2NwGdVzunxKbAvl65BsFwjj4cLoWhQ4NgOHDjJyjQE38MRsCIFwGt5aUSDGnu2WiVbFgDUpbLYgNNp6XD4gdZi+YKHQVx8Y51OfDVsxroVPtU0mzBjx2A4JyhyzASIr6zgy52n9JgymuFMscwK4fHC7PXgR6LglGE4kmESGSAN9maGlkwsyvwqwc6oAuh5JpHEIq9isiN3pjlWBTqqmVIHU9ZaLMBYG6XLT1OYiRfrADikiwyHBAtG+M7mYojTvr10VwHucU8TTuQ3zEahr2WFnD8eKkBNrdA+bg1aV/sZfsk8Lu6Lo2oVLc3/p30p3QpGZTm6L9lNa8UaI1trbTV8itn9b+2RT+552MGrp3Yab745v/SINspyWbuj5YNgu2DotvTOimlQB37hjtg0jWi2tA4LqxB8rKl781lin+UivuN/7bp+5sCTm7FNjJn5Vr81w7Ik3pZ0ED82vCiVLFiNy6e4SXUsCRUo8dYA/dYvGmy3Q1J1ywd4HHn2b3chpj/ZZafNWOXSOvh4lBOWrHqv0+jYsu904q4PfY581x1OdYaoeqUCy7e6m/U03LJUflLuevd94F2c7HNl61jVnS27NuSZsU+o5/VLpjH6jFLTvnTzE7HmEz//jnCC7oh12e14b8VPgWyoQjSmEvViaL7X1UXt08Yr9OPr2OVuvJVbUVJCVX02XbwEGgXlAaY9/+/tiLwZb141lGEb3TzLawquaa/MRvq3dAfb4kJb8CuoqRTq8lXBpxV2IMqfp1WylBxKRGBEy7/GXVUrT4ht1b3hUjhSWviLMOJ/QvJHbmZqIotPzP4IioxyiviQuqDCi/8UA8C26OmdcJb7/tnB0+P9KitslxSWp24qByb6lgsIHxvI5q+Zm7VDRiAT1urVBHvuuv6aoQBEdqQAu7M7ZtSyvsUvk5qYn5fyv/W4Dgq/Pxdb6s+msibU5TSbc0CI5TYaHaYWU3KDxKhJdKRYBLXe9tt1tV4upv3egB2jvzgnqYO2wk7b9XXtuJt/s8nDp3+itBZQGPowE3q8Hzeiig8T48YJgcYK2FyvYNL+p/2d88rfnpIHa70d1QsulUp0UROF7WD4oVIlUwM5pm93itjPO5BX+pl+1+JfuBuJgR85Kc5tmuwacyjZXbQqps1yT2b2lUSozt5RaLNHiHLYOjgUEpGg0yzT6uYKoPJ6cZo0U/uG9/WchRPKn6glM/+avLY3SS6+ag5oVr9T1atADubR+Qr7/Cv5ah5+l9hBoAzin2OlWpZcmx7lXemaYU1s1K8f/1ezYhP8yN6MsP5v1B4NOU1BmAwFGvoJ288v6/MvZ3pwHqTJVFjF8eEptk/S+kdogCGUSZErBgvONUprqtMBg6N4SonSyoaFxlc3e80ZtL0MNjCsixuMIj1bRKo879XQrWjvLhAIBHpKnIYc/K/WZsVkWHSK+iX/HXxEJevPhpyr1/yoqCsiJecWi0yRbgNR59Oq92LrEo23YVTe1RT+LepeXrwuhMc4PE3VgU2NWtol/8x02+2nvse/7Zo+8M2NesWxwI230a5KNj5wYqdOuZQb9wf/95aMeCPfVnGTPHnl7bfsHWfvHdiAMZaefMeZAhbaqGFRGq0H4jdtWA7lpV2A9Y+Y9rd4P2PcrvAx6jw38xik8byaZN4yxLJLGsCoOSeL/6OUOUj7MioUUsT0PVRCmaAP+aXGzcmr05L7alj9Kyn/Qro7m/VjiOhtPExh9xpnvDwWk+n2MjXIidKIwqShhqoVAE7K9Wr/bWAf8/vykXH0PnZEnndASK0pOZsZEkUdp9D+c78Q70+JNcKeetQv6Xs3P423w6Q3C1LSK+IqE6txTL7ta89MHxlE5Pt4k0LnMX2Op2cpuo0xUmGsPPPRr1F1qR72zfAXHCcY3yuVJWrD27DwiLztX3PwWzPtUJSqgXSajVVqWIvhRajc/tHKOU5e7eCWjvPwqNveofL66UcyD5wdCJWDDZcglSHZ1+0gCizcbSVfzZqkFWAommz4GZ9YdtxifYvPKL+q5jf7Lxk2LHNW2JSIQ4ZDTFewyZJeUsV/vHwnsdqP9AH1wuydisGIO6++0sXI4eud9TYv+6ORmdwiGbEeB75xGc0+jT+b12YCrVqXKYeFjB6OXdYrgs6KAnTDN/QwW5ypPie5jA15X2tGtt3q2nu455mRj1m+b0vbpTeT73IiDvnCRxxUfYKOXjGzgbttA2jZiYymtcHCUajb9Xd8Q+kVaKNXVg9AlHhEOPJCz9VWn4dyzL54Z3mm/xwuWi4NwifIQGs9v3husi+LCcbOyqhPw7NNLFtpqNn1faEHjETBOSY0pp3bdIpFUw8C7l2e4Cf+DCuCWsFFRejnXTqsVl+Ly5VfJ2b/pTs+dEUY1K6BUfDssRxTUvckQ3T+541GfQh7Onj+5cXojzZ0qhQBbv0+2L6cGFhgcHBhllmrmBmfk2lN3hURfskBZMObllL37k1sTd837ElJDNrohVVDTGaiZ7gQZcP8NDguwaxH7YA4uTv3pRnH8yhZbfUrLZrv9MawoMikutpgXV7mu6wIQOj4dejIExvWswA3VQQwGxw6tGlRCHuAeNEJWDh4aWzlYBznhTTiF/zBaIMobK0j5cJgwmvpxvCCvcKQA+xEEjlOCtaJ/l6SWplcVRf/SjLWS/2akppYXFYX/Ta+eWxY9pSBQSApC7FRpaGnckXoCqXXoFjCH3o1WGgaj24PWNhrHeveno08r9igwZwbS2TGNxoFc7cErGoyiK38+SzbSuo/VGP5ospnapu6fd29HqavKmrQmC0mEb6rnZd5sCmUiSHCbnUqEcqUY7U7eGHfJypnl7mz4aipe15EZPsdOHbt5siIWFwDlhz6a9EAOMRgc75frHF+RpS1I3SDt49j/ROJTfyenDXWzm8HK6mIk32zLkWxfjK3NQgYbSumGk4WlpyM+ijnHa6x/dlT0/1OUbH2cUwj7WHJ6vJBmJA0yYlyOrnVddE5aWNLEan7XAA97amEDZ0BB4LAVBOgA03ks4FhedrxVl8dwAMdt9jvPd5zJ+/iyprfvZU3eR6Ujn/Q8u7kPRzcS2Fs1e/ddMXhacUq1XDWvAlG3f/fvj5D734nIfzng52/NZ5TTW592a7/4BEqkMk0ZuyY8UIyMCiypiWOjHK1P0jf2LbFzzxXV5i4uZQDHKbgaXiXgYBIFxVWbvugoN+VnCBm9dFZG55kkoBd4jO04kEe3/fLBwNxs3AdtPPvAmZA/hbmQ76cCu2HxBbzkjgxLr2s4M3ZL6e8PgJ+pfd77nMQ7JUuP623iUDer7uq1JVGrYNCCqMIm1YDdx0+i8akN50BmpSFYVS49eOvNkeGk0FIJBrW+bkKveXui14uAIZq7uRV/boz93bHiFNj+twbjZ8Zi+1pmoqtc5K432dxONlsw/oSi7H0hzDvHmUNCC6UwJqXsQGBt6AGuSRmVZ3tk901+eh+bJxpdIraQT+1rzyb0MueifOuqoRLbMGfNPpgbaHps99gF8/t6UvptjmMpFakEunwBUVx7JoXWmTqLFnPKRPyU8F3E0H6fzNQBm/EUfHVKapZ0EV6GOrizGoOoxM1CdiEUe2qTyPG+bcQI0CB4xrCrwvWi0H9GZB+Qnp/gNZdMKYhflbeaCF8vzfQVj+4b3i0T09wWHblvOY43779CuNoJMR0DVuYDTry86tvJ7cD0hVQ6Iw1X31Kn1uxTPPdBvPj+NB2gGsvgVhGn/R4z+2SBgIRwAdoDmgMYwzH7u9lh+3uGYxkbwDcpOqnHe/UbPql/pX51n1LXmUQ58OrTzt3vVdz/01PS+IFR/Ylx/+R9TnxDU3g6WYXwRX0O0LGUzhqWCsevoQtLrqDzxksNjxgmncsq8FL2NOYXgQDJHwtzgNKmzUyirulXtVz9p6VcdpPMfaZbmF8UxqgaoVT2PCV/BMR/0xdLkSenU5srMljBO4Yajes01qhIy9lOnRGCI860L/eGH/Zo062b1+2mtEqrr1rxxptej5R2fVoQbu9rP+6NPmJu8aPWutoip2DSMJFmTJoOvVi9zkobt7RkbLE0v85AW22m1Jo1/HA9WmN+2gkxAS5CTEryinZ9M11oKlxjKTXkurkWiuOOSEM9qyPiXWbeqYmNHaUmIcEH4gpjWLt3fwON5BX8rluBBxev3XmylOHjeBSEeD8CgknplnHr8cfVQarIx66zLrOPlJG1QYC3q5H/QPDgoQ1pu+28bf89Djx5nDVwbfwXe9j/Sd1WpHfiFzHX5qIN6OrUaB5o/HorfBYd87b7TNnmK9t724GXqUqFUXlZiFDDVvkB9yNmPIFqtwrYaXW7Upo57DCqGykasRpDq58jlPAmYzM6+T/2mvNLYuafmmTi1+oVHe0YTiNHUzIpiUXhcIqttIp2wOnC1e5HNfYmYuowIysnnwJO3YN5p6drnUDQ8en/HGc8uJHeIKCySljRR8wI9Yq5eLH2/tzJL4kltQbJ/nsrUFhedRptbxPUTIfwooipnTmk6WDxoWltY/vS4UdP63qeVXO/aFTb8z9flUvAg4cGv8kct2baiNE9XjgBK6YEj9B31rO1Cio3TwEzo2+OS4HM7wZmusSNvgeeoG2KmI3Ce3gsblzqodmZ3U90Yf48ixuaaRzU9bPc9mDw4u2A6tl2v+VdaBLcz2BNQKFzYkOJjVGJO+IhT7x6WCX1F1gcTFsPIovekhBfHR/m0ViFHba9E+7FsJgLEnmU1t6wlIR2uEgWeYbf35j4HZtQ2VwZGfcgLktxg8bW5eNiaqr5YC56/PKQMCOtNNF/4wnp9vB8bDgnODAQvpOAsmqqxm/6JNaiiV5ORkxMriyImFIDi+KF7SlA06OE29+l555aB6vHZZUez824VjGYB78RFt+ydigq7BZi5CLekSQ6g3M7C04xSiFBMj2M8veHE1yEjIKQ9+PkBb4MYYLzqY/Y7bKQoOgQt4+ycL6Mc5HT9A4PqFxJlKm1NbV3qw9NYOi6CKodcsGaj8qFWZazVFKb/K1u5w0YBevvnlndj/aAyfngAqhTvsOS3jkPTG6zXd8BgdzVzWAKckhBJiaXQqNDdqsxZXA1ndCpR7PpUxCJqMoIWGAq0h0dbc4FEZ3nLHahS2d2Za1Pzl6NV2pEzO3B3DEucJixmdwAbi76Ds87cZGoVuEYNcUnTDr2uDbscTWACRia7JIRjYwDzyzPxvyQuDhce3PD6+oIe/XnVWNRroevf2nciZp0XXBic3be24H/N/3leNda61WXF2Ae63lIj+vhGcOdgZ/YXDwwFBUKKUrCiJvXmxjhuw4dG6KmiZl7764tNhkV/9JNUhgF/l2qtIt4N7qAT4o7DbjdcAJC1Uyu1/oiCyHtad+PppRXHRGSX5locCYd5FfTwsrKY1WpP3SNVgzc+QI6LSzDjSff6Vr8xPe7mUSAwKYX0HzOgVUhzuG7tK4QwBJXANui/EUcjC4/4Mxuc9RdK7iaHtc9QpQJ2Gli5lVa4HRL9Zrv5s6czc4tVYHTtCvMNAlbIBshxnWTrxRgjgF0vteZPebUUh0wTbvKJIlZbOkoJq49/WoB+oTBSktnTpuT7krBFXKcZhQjZbFIEuYVWkCwpQoYTr1RZQN0Q7bqJGDJAJ5FqOYBS55XsQC6AZg43W3idTRW13Q28pr8QnTIuBA0sDTSbdD1f2vcgsiGXZM82QQiMzvJVe3JIhKYWcCwJDjbm2eGa5cTA3pPpnN7bjVSvyqUFdSvt+e7xcczGNrl2bTlwSR6VmAkR8L1OkvYbsGclXCAQN+vpqWmoc41/5lx/jRbA1Sxk2pCVDJBzVGuyFQTxr/ksAeeXxkOXF86287aru39Fz9rk6GrKDOw9wRzu1S0wUt/A8+ra1qUg42DqrVfTDB1P32jRfvw0RJQ0mAlx2cFaD9UYrEXkCFU2D87MInW8jkQ9yE2NmwqYn/32AZzbOciAOeGPNJvRw6d+D4TuTmVQu0AxOdJ9ZrxNnXH7J1D3EOzdzrUE62aehIhEReMDtrlF+VwMupIOHzi/68E7Mue4bvEgoI7xO7hOE9ZOXap++AdAnvuEnoOohvLOGUdTJOFy2BGQwOYceoC5TuQOXUVzEzPXLhUAu4LDm4M5UI0B/VxhaowFEqNUBHYRyAG9hiAMug5gnqGCWW4pe6hu2jZkFNWZgo9B6tld62DeRH+l/Tz5ZJKdvdYHnBiccX5S5AgzQtKxoNLdp58X7oMHFlvAKo2C1jIwTlTq77MHycTiiqnhBmvjDtwxhryqyPCKvFJWeZ3XY0VveKciJaO40WHiy2EP06rZnDjMty4zkK633lgbuCJgc6H56qfqFP2UuFYpznWl/6L8Fh94Ga36rGqoqJv8LvUicXdd3e6yQtsbeFyOD4uq5XHY/l97Gi1qMTfzcWLBeXlfAGewBeFeGIRQMUaED248h5ESaAcFzgNRTRYa8ugyRSu3AP+XNFgs1AoNtskOAdyHf/o4t/2l/uBsvNe9G70eq5t04zVWEHGWbpl7pyewqDXfrStu/bsTcvSsbn6zHtzDeXi5Q6Vh4ip4dAxloC4Ib8fer7RdKB9oGXldUOJ+ihipEa23HtJjWpU0O2paH2AwKgFilYt6Bn0BjXy/O8R9zPHu8Tx9rpVV6+Cww/p+bXjPwKFEkikVRKQaM5+MhL8zZzy2dEf70HQU3cmHL6buwKd9UatMS3b3KC1qAZM/KcHt7tEx7elO+2bZWVMbxVGdrMfQv8+USa4eM+ydOi6Ze7FkZzW86+5Vo5ed+WfX81WcAI9nEp1F4cVUKiYbQGqRtNNDXFn/6rzXLppK+y5ZctdqutrPHvTNK/npomkF4siKN4GukDgIZO9EhE5AsWiTH9kA/1nlIdN09ei2tqvi7zTHms9hEd+Ik4gOBnHlOsS/SqS6tx5fJo7ManC0J/ODKftIiU+FYsiV2jhbM4YPL0CRUmXayPZ7LHIDPkM0wsba9pJxXsJSAQrheBvLMHEgsJ+1iCnsPAgh0Ue5IklA7xWlJeERA2IJGG9tBmdKiaNNeBbWHx+KwtPN5L8NpYmZ/fv+/Z9dd8diBf6NUgIOtqMlIByyBjE8U+PXJuBcCI+Xgfpd/qpyEn9MFMhYfckomaUy4YOjqtswt43avt6nhoHmeFxwGWvv8ZDXMnzFTkdRgbhqA0zPI//n2XY+fOZcZOXXVFzcDPwDTyjR7nieflAWsPxZLk67iI3B3VBqZ5NTqv6rbb0cz7cfBPoTquBxJhmIWYltKjaoAqrLdaeVfuBc1Oq2/HMI+H/EyP/OtXk/31jrLL2TnH+o8oW7osLhUXsyUxaPzYUHHOI4AbSXfi2yqTwzixkSEtJGiFJSAue4qZr01aOHH8uwG1JZvJJGzwgLVY1V+onPNfrGVWoFlTdA9OQgRcCe6O59yd/SeOh0WO6ftvAda95TaEhm3R2atpLtixSlso+LjtBBrkF0al0NxZmIqrsYSlZrfN8W147NZPxCC8Lkh3m/rrF2J/JRGM+zpxubGepWdPm8KjEWILZrLl3qrNUuXHtIUAHjuu4yAtS977JVbOsUaW7uTADa8rfQ2br9Xxb/v8m5RGXm982g7TJBifYW++HY3ZM8gQu8tFTedQHypr0BxdFbag2d0E1vGk1mWZasK2Qh+LHBjaScSEKSSIBT/AAfNq86QqSaMJw0d5qndhJC+Khi/n0R8r6vA/va0cyz+3FkohVwZ6n3NLr1CkJA3RseH15EiEpzV4GdLc2OIYIBrvXOtmaMKX5XWOE1MN8Bnp0hirPnI7gKVbTawxREclpOTkV9IyyEkFC4jZw0SG0QdU9LcGvO+ESCSkVb6sUhAd0DUSmR5Z4xTuXhecFR7mRIqgKCjVaErGvGygsh8guGqxysAZY8Y1JwRkMy4Y5oxO6dsewTT5WCkfHrSgNLY0Dzpt9pdrChN7+NFviMNLl8vmMpVkiCANZ2WlZu/zZ29vd/ljc6fkNYP3HtQXwQuxTjetx5PIs6zrtM1868GHW+EpOqhSLV5CDlgvJL64sK5i30liB3OSznTnNlKDjNz3Q7oUMOsi5569QK3ya7OuQ7hwrMwTRGBAx1Fov878Lseqj/DiRUJqhCsssP3B8bZ7B0hSfkFG+zyRJ6/KiwxL9SQoNOQ8mXV9H9XTNYQsl5muL3kVdZ6/vPpkiFs+nMLpn8tZh9xMa/IQChl8FAZvosx/X4CPgM8P3/EKFyePMv7puEXm4Q6fuSVVwkeYDbbjpCpwmikSjhaWRQYZ74bvDveAxaNYoUc5u84vTurKtkUXXoDlOPKk/q9wg9vuxEClEaxRAGFqFmkE9vP9klDkYntqYE+dch8bXjgSDh2oosVQ0lB3NSVMehrH2tifYs3e4tjiVeodJU9xKYtHEIsRdaS5ifzEWJy+uIrLQVepdeEpLLVBvAm0FHXpOQO1/QXuMzPP8M5YnvVO7cr2t75/bVGuZE/PdGT525p9TijYTPXsOFAtmtlXlBb6THaICp4n4PuIkEkmYIBQSsAUK4RKdrl+woP4k5i1dV/DCgFGqAg/IBL2wvqDGYEeomDeWHPyE8fCTJ8U5g83d5xO8ENbtLhMYWUwtV4wCFYUSXuXyeplzqRFAq06Kq5b0oD8KAJehXSiI7neGVv0+AdfXa2S+OV1eQm+JTjgkW5w9m+jhsuzmcli+cufOQSAKy1iA3ndXviMMSx+UgXKL5aFA0Zb5SOPdK2iZanIinBjaDLRz7r3cfXXt7vmh3Wfu7wapT0ezeppBVKbLkoC/PCCUTiLNQoysbXc8J+PN9fk/7i8rGN0JvLLYRvfSM9vPPLxYZW7Z6NuNXv9Alf9z5tVmROFWODP7gICX5V9p86nPMem2V+UYCfWVaSx/Hj/bX9TgvJUOrDfv4P+8v1xPR8OUyenORh7JUNxT8X/MvN4cV7S10c3y528wWLH7Csaq7boc06uoTM0G7gFxw+IywOTMoYOdzTaV580VNzeYRsgTcQApNjp1RCPSvxbXSZcv6qONjDTAKQeZPaqsbZdtDN6QAaHKfjE/EMhG6nk/cNSKAMejMcy27vWJ8M8+67NoiLrzYVKWvma6NLDGcuTv4wAS6r48vIHE+u/TSoI150PKS6eftC3P8QKhjFIxwJn9NevvYI51t2Cy3zor0Rfpj1bXDL/VfHhOqapFN85C+zbVlrTAuZ4ZvzVqeAuWkspmSAA4uhzqOIWFQpUx9XBIz0TLreenLLzz3v1DbSo/Zz2C6hjbnkbuudxzKezxfRRo3FgK/qbr4+dzP3W6P7g1v6KnRrYOEiqLnUa0tSxznsszjjeFO1PXQ8Jf/fEWnjtaNJyScDhHJ+FRkFiqHLgv2XUHdHv+GZWkIwB73aHRSZ3GCboJJkKrNMqUxUQXl0Fl/w7lP/LGIl7X8Z+yLBBnBw9l/F7xY2gyQra4Que9bz0iK2nbKVBmG2boAW3yZvUygMod+b0C02G/eAbSqERgN+SHZMQblgoa7snvFADpiW7B61mB5a6NnND91wYX7yDNQrSbPydi0Oj0Zr5coVocu3hddy7Rx+nezVUyfRnOLYPHthQUhPCcrp6QVOd0IRKGq87Onsf6VLu28SimYhos2wQ0X/bJOmTAMYG0Chkw+2n7byhqhv3RVimC85xVqs2s/OyccT8pyYOS10t0OzY7MgPo0DFQBltjQnu01nStKa1hjckqY2qvrDEpAhzJn/ocjdp9FksxnXtYlSoBOlq081C8UuK2ADTPott/Q6u3WHSeRdObXU6Qn5ZFT4sJkUn5KP/51CTfvTlpaH8PSqXaU0+qqgzs5Ja0xuDqjsiTn+TVkJfOVzSKRklZA57Xs0PYW76Mu6nu/3a7xQIcvS48Xkj/9xjH6Z2L9TGFiIguAQ7aKUnFIHnuYpmTEV4TUsmdPUXMq7smYT2vHyh4eS1P3PhUIPr75BprNXBNz2Bww+b/naTm9EzgrjcXn4SQa3duib8gk9YTIyihe33sQA+fEwqHsfdzbE4Ykg6Z3xBHlwwwEONUFvGILqtMMVuIvlMaWgx5Uzvxxe2EBXi13Tj9iSeRrqyPj431o/PQ/mSoInQXI4e14Xd9vyTnPpaKGwxpk0aHFRbDMfgSOFRO9qzFHKBn9fiwo4HPlxb5+P8IkkfVELIruMvLrsN97QENKPA/aFtklnOPHTwiTE/Kq63r/vflCDM2MQiXUAu0zaa0dWaL2lUe5LE3kkZMa0wjW80mzMAW0yRN3veH083qR3WB0oi05f14OKVSPZITOVOzns6arGRQMioYVElfX8eerMgasKwaEOcOUT6qzotiLkfy+ZfMB5mdAuJ9qWDjbMomAS7QBEcjhBTow7JY2gpqelaj/xZYj4kuEY10TtJwv9+dblLfq+PU5XB+GEXVPMb9oUMX7UKxU8II/UjTni7l5JIs/6N29HGk3znjhDFlX+3xiZwomF8inbwT3Z0E72PPW8xaOQNog+56TsWA6VlgtQLc5kB29cDq82D+oq5udjQytf1dLzD4bGXVhr7rU5TKjY/8qv0eLe9JUAUdYFM5Ui9spyH5eUltkaa6CuKxNnm4b31kkRd4KLGJoW4l84E7NIWzG82yv/cPse9kd0gElKzB/IOAU2eBeGpmUdMxvdiKaJlabO+YWex+h8Ci+Di0OliEixZgsckCYJiz6ppLL8Dz/tdAG9NCUp2DmUVwqPaNhVV7aoRNV300j/bYpJmVznyle0TV0Q8jn5fQyXiZBZQnyIu0xDn6aeA7uyq56GE+62ZFObfxkN9hBvIxV2KpLU5sjVNno9/525INUM7wMBUdhShGaTSNclE+Kk2C6IYXGkNtjTji/wIge/N/4x64LzOynnG7i0v0NkVixB6YKAMTrX0J8ouf+/o5//jNcJ3fG1ar7lZzPjSvk2Y9vibpbaaUEALmseuctJPFlAxqqSDg9aIQmBOXE8LYBYzUqOj48IoyBI5Qigi746MRYRVuDo8vH+yu1kTvzuXN95TvhZblIEolyFwkF4m3Rnxf3mFtDLJIgjQx8MsQMNoRk0GisEORUl4MAxmnbcObzu5rz7SYWNemGQNuvoEEAiQQWTry3NUOmHMkReqkrjAgIZdAkTAav3bh0HCUEBEsPKIuQCQDN6KxYtchFSJEUifyJRciQirynHnd5fdCfUC6WQtNHZq01zvVuxxevOtIZJTrKC8hZx5QUX8/hqDvIhd/TiLBnw/71XPQQAaTnbZ4w0J97byORquiUSpUf7ZzVMA7XqtqVG1rvTFww7oU2xzSDCLIWsDGzgK6dMnLJ+I5AY6pBwDFmFytBXTIzWLMqi/jx5xSUTkjpEWoVmWkob6aFVaXzcky/skmPy1m5AhiI4rN+9UoAiTV/VEkYe6/AAzUsyDZtktE9qd/Ake6WdlUJo+KqiKAuzo91sMuXSL35LWLWgysiV3yj9Oovpvl/g4SNYpAelXBQbTxSQeYe6Pi3RwcJpfDQFWSCIEh9s4k5yzcOTuJhbVkl+r2OMOjktuZOx9ccCcxDn8GIEule3GK1q/XL1I1cP86QNo2GS3JpsF2c5G7kg4+Oz6LgMV58CnQ0mgBgwrbxUBPIIQAsQWS0Qj3id1B+7jMGMG24f0AKweLiDlk5io3A4VpJcB9inKCwv8yLHISkQn4ZmGapXcAJIkBjrS9TgeZTDIAwy7Fm5JaoIH5K2MMB6H3GotzLQlA+rq5dPaE3cuxglUkvtPa274JNONNRNlqTzVwHJc/0BP3PkvZT4qU+TnHrkvjrKYPFUqQWUzKljUM+OrKImsL9FOs4vS9BSuD40wVan2iMDaCGToeMfs6z8rMoqQCPharniRUATcIWFVa8k461xMTyN6NBPcdLhAwOKqYPv5w+nN/QjouDJqGi4SlYaBh6Zj4cAeUgwPwO+v5x3sPkPCw2WYfWudTl9CefDqakIdOSpNNJvGLj2BTVXhdSA4vK5qwGxYOhfLrdjkTh7cOx8fzk4mUuqNxhfJFMrkLM7ssygrFdSTCXS44KJBeHvfsYU3eZ41qe9FfPxUbmFlAvLeauZSNfFyPLxqFKKCEjVIGW1uezlR+e7G5mAia3HnCSjYqgK5ugVVuq3O5nMZsE2bn9TzEKF8aPL6liw4rrIgkaeqFySE+qtngGufGbdfJzFaR6q+Xj//jz89lJ4X4auZDZS4NrpdTGWrRyOqTj1N0O5pIqD7+jF6sgcce0JZeUafhY/yp8XNh5S4Kl2vk7HZhw+tR4EfWUp0uwBac+jZYqjbdzEtz+pV/cDQ2F7TSPkt48vKfrHP8+XdyfH+5pAYwEkRvurSI33V3AIL5es50IWbXXfPsfWV3XfcHrM71YwWadjV1xqYlzLea9ZJhoaojjGsDAo1dF59OqNv5TE3yhx1rXJ8+v4zKO2NtOUi864rfQyma+z6aAkpvTeMWYnqWKXVe1LTm+HSdOlXgppZ7OM7mLX52C4FnImCqOw1ts3LHwBGGbMXdZDkfpI1sOVFgfbU7ZpT21Y6az07IMc+sxKFN9hECs1XvVytVNJpQQaZyhewSTvautH0wUlUdhd/fM+eVcLsGuXrzmFg4ZcXXEA41+Y5WgJV5Bb8h9hWGI0CF/T8uvFWxRNorUegGD8Dr2nfzlS1Zo9RVdpFbS+JXGbRcckZNQV1GYO+3W89svZy8Wmvm00qT8Ld12zeWMvfOHYfObeQqEuwc+J7XDxR0hocGPC92wPc9FT2vvz33U2dMZ3jzjiZsayvPmKWEF87+NOv2SDMMjpHat1pettze5gTkHUlTl9wytg/HNHCl8uDjwHrmhG9AK3c+oNtQEfOBk/EfaiZzMcO2Xjq1iafC+7xEjbSNzPSKV73eCy/WrxheNOYGx/aVBerql9jt+6DefZNTQTUNsEHGWMfV1xzLLIu4Phdvt21VzPQFqOr+nWWVWJF/gmAGHmmtO7aouK39u7Kjgp/yXO0fUfz172/K6p4ru4/BToiKTiMNgRWz6Whds3J6EdZPBpat3T0dLlllvcXLrIYShZhLppptFxEdwU+PlYYqh88kTS7srF04OI0UbpZ7vHM3ZHPVs9BWJatbuYojyevg/KZeu969zdAFOC9fDeWTUfC/OXpCdMkCW2QfwMmHDrIbcfSqLmyVt0Dqre5DUnT0xtMdQ6IxlNqtWEDIyEwun4KmqbBCgO11lf7X1qpOXwb4AmKDtYKCYaRjp2CwbchAmIDQaKOSS+jp0x9BlYl0IJo7o0wSGGsF5fSCGXjuT4WVCTxjowDBKmDkw3LiohmDD06+ewYoS7NJ1dVek+PVmJSmbVtkUlaKJFkx/bzh4i4bcNZubk5X9ijOzmYdK/QQ64dmBbZ+IW1Eu9pd/9Kb+Vtf/fJeg63gVPcJoXxkETAhu4I//OQZczpDHy0oLENrHOUSWSeF06JY9bWuvuJdNnoEbZo105GdhlY6qUkMiNo5VdrQyTZ2jWKYLPfWOYY7OuyXXK7jtx3FqzcuZkawRn0jXAEvEZxY2K/xZEWxKBhtDurfChFXRNzH57WOcM2js4UNcveAVnZ6B4BNpGX5VK3M/S96E+lsysditH34wWpka8fC5YFLjcdSCXUGaFnbuJ68B/BNdmxlEnZtiRho1kvgsRbIz6L88ecrlCpAMv1vrlHlS/+1n8HGu/qNu+ZkH+dAWK/AzcTjOEwCgUPH4bl0Gn5udn5udF5BSG5+Dsj68viq+oYHh1bqmQ1rkLM6DAwLWzNAnDMI2VoZlcKlUBt4BnkPUJi6m3fSO4k6PJYCKYNaMYKrsVaiixBuGPRxt+7BlajSmDh59McOavTU7kNIpYUva6hXVZ3ckTz9447OrUZ1RiPEjIRFsQDWKqKw4VFRZJHjCYl0PtudJo4mqKSMmC0ppObLOcZ8Uk3nmAWdxzRaf9zuMszqTMr0h4QnIpuYRA6Qcfg5xnxjhdcxiGDoOTR5/bbK6+WN69c5/uhT1BSHV2bk0WrZ0J7K4kfEuuwEfkpbbeKuF+Df31jhYhk46d+UMFBXq8t2JrvRJv+OUdsixYH8bS93uaX6gViiWwhUoRqLEl0EdxcXPe4aFgKaEpK7DiAVZp68plZb4WFk1Ggebjnup0cVFw+h2n0L5RTKgGlZTDGFJYZ5FEXHipzEKZVDJSOKkZJutRrryX0sLmXy8wknciyr6uajd51C/EsZcHyYWK3nFasgdWUjl7l5HM1WdeVWNQPXxqfT0xk5sJTF65RCd3fq0rtSDUMaEyKEsu1AyOqTfv3/bBLF+nI68ym9Yuy7FtGm9rf79csLodJShl+vQCiuxUWn/770ZAmS4GRbAmEpS0Cq4ZCFnsosiw8IN6PL2s6181q+mDM/+L7Fi5LcBttHU+RcLU7feuUY/n5ghf3W+dCfyNsnDctqUPBFF/IbuPfJR9IZT/mthqVl2Z8NqrzlSMA5jG6KpEdc2NK1iXHlW9XMpR4ZZXdgx7UqMUO6sCvuws74ERqzUrsEB6Ubr+X/8myX3jFL/nO5zkfx2db8S+pOzXM3S0vtgXEnkK/i4eX5/FaZtRWQ51Rc9Yggu2OZJxC9sfpIZxk+1fwl/pqoaa08+l4ljkhKiasX+epMXm2apuLKidA0Ae2L9sn8lSDj2P4pmvisx1B0M/3mPlpBbckndduaw0ML3r3HPv1yKFj8Y5EGK/jHhwNKM1Mmo/W41QTMM3WGgw31jqUzac2ak7zlHSNPqsoLKJIExsvbZM/aFpOvpYrK0U0R30xLPQhtGD1anBUoB/TqprNVB0CCmG2HVt8Ez63GV/p3F8AzzXZ8hdhGaspuoNVbcXTaCUTpPsBsOqDodpDORDojj/9xmwTjmGo24YdLRXDGLj1liSKrDdZ6l524RDPGsNJF2XkwYNU+4bx9+snHxCD/FygXBGJRnfshwqPlOVrwzECKdPY4fSP+amxOLIifCuKDAMcK7rifnEYVeKsQCY6/9/hOZQ5xes2nrmSmIa8cvfdvdHd3/mrAt+QXx/qVkhtFb9EnvWppeBHLn87jM1PfebXUOlsR0xSbWCTJVMRkhbeWNKc1EnhaKrpGkaGIbY7PNiSSEJr1gJ/i/3YJHJeC+xM7BvbG8eb67p/VNHz7ZFnT4XcDj6NARSqMwuSzkuXJXgQ/6xeoDSvmwpEkLQ3tUbD0Me461KGIF7yiww7oDctrGOHu0Dp2y4Y9jB4PyzIUNKI6CipqRhWMKX239cpRep20k2Dy8ObBcrzSLmtssKlJmFKT1vEC2cXKtGpNrS3dz/uXvXTif86S3DTtEtDH2scPKdIUtWOgTHsyE/GcYccU3iLvEWkC8Gnh3ovqSWdHrCHaNXLgt4bKDNK+t6CSF7daq593pVMEiPRGvoKJ4sMxVZn9ayuXdRFgpW//F25lp3peJYG1uVnG4yQ9Uk2b6FCoEYq4YcLsbk4a1n1Y1DJKOe2gpTkoHFe+8FCZNhsprBrhPA2t4zJvsKYGLNUT70rWr88xIHsyC/0GncP6MXb7ax8ZmJv0PJ7JyiKWCzQFb57McG5v1iXzyulYyPpVs9JVHpnakQb59omh6XDoC1fJ7EY6xJWbHVaU+22h6B9gmBDpuLXC1o/dTT+NQDNRv3xwOSjH+gjLQHhwEMVGv2GOQzVs6I+HLoCUpSo2RJxepySUFN0twGnL5BFva1iw3AJkFewrxu8UOc+jYyH1sYZNrJyCltziDeG2AF1z2zY3FKq9I/WsTlkR3+XiJ5T7MQF4nS6naEpU8KRsCVLIOMFngFvRcZlquLwkKVdHqBRfEzBC/jRSA2G/bNHMH2J3vPox2Yi0vrrgIXRno9k5D9fT0hMfGt8ViK4HeU4R7g08qlkgoJk28F3hAlJXDV8qqeWTOsExq+u1c3h5UeDf7kOFIkB730jG1M7jd8JRGD/aAMNeffXm9WvX4MILSVh27VcLuoxRHiW949NHQCaXnIxSbpDByVn1lWyZsDqPq8uQmwqNDXvxGT6n1E2o0CnrM3bHWc/GovE9ObQX+ozWcAAR+aCxsLfstQ7DUEb2ySjFeg2cBKnFMtGI8bS6NeY1/v3hoG9Shu1NFOTlQrOUdG5xU6YU41OdjuxBTiLNRnYushufiewsB7tPk3AjAda4uL5l7HV6EXdnlCgKcuH+sKBINZAmJKOLczVVVfu13cUJR+VtkbJsNwzH4/UVVCY+sHNO32+WMfiifM6cR0psdDPAsaXF0zoZJZA/Ed2Z52/dMqPUCn9eTHWCHNDL1vxc+fqVr+0++qdoF5x7t6dYbRCCwI9t6afoN1/+CqmTaJp0EzNiXbxlTcTu8FXHZavzcupiMv/cvCkmcvevEhJPpNsMJ9JkiU+LIfvSQVidFj1zYjmY59+rgstr77u56uSkzcmbe+Hkrrk/ETIx+f6TXbsfguzEmKLoIESFn4uuEbySBOjax3Gef7lr5iGUD2RYJAj1yeNoWHaTUEUnCMuR1sRAKLfDGgVfhjoj30NAM+FV3WVIvBwqDLusvw2rhdih09qX6h1TSHdlr0jdXbKNo0H6zdypTIBYLJP7bG1s5REL+7hCXyImEKQyvM2QEvApjGm3N+tLJyQkS5RJgdvZnA12ZEXOHQ40jdCQtyAZUsadqjziTunMIZBzc9kH9kFzMuK90+BLfvfELz1zrIC06IO08krD4TH/uMVYyamSKBFkD0GiUA3kTa9jf6XRfwpMRV4F5mYZca2puKq1+j6s6Fimf2lz7FXoZaWl1LRd5UsOJtusjjBzzBOwbcFMHeNyBzd+PkZ2qiRSmLSLoeO2VB8MgtIY0lo1qs3j67MGrdYzApz0gIhVnydMCkLomhKkhhb9BLJyHFKBhvqhH+qad1BrFd1CVVfJTv7kUu1hf3MstV2/9HJVrcL7Bj568aatlI3I8YgkFByPWGpK9ao+MgnACr4lHDz92aGAoD9ktPiyc80IVCoPKOtXzZ4rqhMHe5ZOMvFNu3Ix00zmKu1vMzpKAMPosibDLADB2OrqdYAn40GDRaQtsDvSPoTMZoS2vxilyceUJGm/B/bG0/bitgZNBZJlRB8gN5hU+f3tvnvo53ugLihUo7hqdEVij0csrt+z+lPz1CvDaJjFddS7fpV87n4U9/JhHHtI+bfL4zuas9Km5XMrN8Qb7Qh2aXa9UEIdpB/XRtU3OsGuKTy5aiKlTbvlveQMqojbLtt46lJmGvKGaPVlW5+5LDjDLnlLv3+KZGeO3xryppZqDkKqo4EO79DURJIahkTZlNKCo0oZzlKKIKiVhLgPmPgPHk1WU/iEc4qZFqcuZA1FFFqCtqTyB4pSoj7LhKMR++x1fXQuq4duqyf2ULGZFoK+94ESyYHBCvAw3tEO53TjnfhILzhuCgSbRlftWszYhkbUz/TDr1snT9QM+VdN1C161UQKSK37OIqx1UplB9mhpPSpYK3reMRBTpx2Tu/LGk6YO378rSe4euJr3oz5gJS5pal/kjtTy0b5/zt7JW8NzivOz+H8ebqU0GNx2clOHJsv3Jc++I9z9y/dwei8BzHNxRMiUUulgObqYp4r+CwqSfVI4scKfCOwUyPO4bava4+7e5LLjHAYimkvFH0ubFtTh7WiEMV0fFPOrthjYZou3nNhG/yTsUkLTckfpX7cNAZlgNG5H8Y1wjj5SVtIflQQhdVFGmfS0vAn1n9skdQ7qY2bJqACgJp/voqt7WpDwTt8x40LxneHaWZvSsJYYRrGBIxXcnBvEUBPo7FVkcaZTWkFqPX7G8mwFYo/r9enzVGBFToBeV5e52R8KWzp/1A/lfZPKbDU396KaeXK8CQ6o8nsrb1pnzYU17f0Vzd/VR4jM0ZR/XZC5BTqQmpQEievt2jQcihKSoIXiaW057+IDSiRPTd+E3bOsNfcbmRrCq29+k6oe/3Tp+nROQ6q2rJ1b7LeelBum6lBphoIlW8FXcKYmqCj4QnKNuv/JO4pCOfiB+erYdqxM9I18/cnA93IgpW1Q/JKmf2Gy/xILvlasBI+JK9gfmqt+FFQ2C6eYmaMfFtcXxK5z5Rq6Y5LmDYpWShYs/MdQdn+aZrorAcXM5/u2Ecq8CWcZZf3/n+jZKu0TnZzjR6OIACZCkYGR6fGpLfjjXlR3C3pWjCB4O5f4dxgLVeg849aelyp1I8b2Lplz21h884RVonOT3tGxRKb4Ixi5rdPPdj9YZv0a2GW1VcjRUDZFWQd3nzoC3WIQlxeRRDrXHOM67n3Ilygd+Eh0eG1myNCpDlJoKYlWD8Nypt6HamLkfw0PMhwKE1YWwSNd2zKLN+EtiBhvwapIR3O3MYUK7JBWt/ok9mq4QmmGEN+TaqPMD2s7Kyrka+YsFyiYZys7bQbMAfeQFVhlBwIGFRn/PRO+SqPKHiBKbSOvf0rQeb1ytKlpnGHuOGZILxh3G6kpp0SPJn25ttpq1vcIEMSRt5+g1mTRWGNTewJPhM1ZrKko9ZRXoZksZBI5p4xJ1hMs/Uom2LABJ8zsyvuehzddmioyFsvSRgLV3eZCw8eJBSEGEkdCeLG2rVC9xqht1Yc71qnmk/kGVjpcHe8xFsfKuKumOs75Jn6hQUbPW33x51zlbmmAwfsTKDl56fvX1hbhoWjUX7+TTKGedJ9zaOdtdFVPaFYJe9/8LhoWQyy+/DDrkdBcgWvice+yw2+JwpPYdXPz7eoPWwPqIX70Df2FNLYbw+2jAs+fQqCuYadwRVz2+59NsgiwDb+isi4ZcuZ507aEgou9UlljFLZ3C+hGzc+XS0j/ke+CixM28OX1cGt75yGrPTZgzdvYeypMmJkJEaptIa0tb/yxZ1DVLzsX2H/PwCgldBfoYLi8HsFTQRb69FmbdD5Ts1IcVal7K2FU7YX2ET2aHkCDw2EjVunEZlQ9JlYxhpLYiUlLi+WbuBSvRAOPJ+N97v5gCvDnhctPxLNSbkeHd02VT9xT+NYxq3vlpdbFLySr2CqcPgtx4rqjyZ0Em+Kd6DZe1VIreinuO40g+5wZ+8sX2+oaQa8kSr2S9u2m6j13t1fyN56x2K1xNyXUXdiXIE4V6ktkEulsQfQ4ozVYefR1vAy+eBgbdZesPvhRVrdbAy97EbKBe857EFlf4lnYiYNCkbESfiTxnENrfvDD5zY8MezWvjOg6vCFNjF/5q66+PQEusYWL6Nb6CHGRbioyjSlC/syykW9E7zU0/S/eBkPaISAlrcp8fME5wfeiyfWUvLSoS10l/o85mcBED2AjdPH1ehrwEa/Go/12O1AtjCmUb4roXO/6+Y7XI4thY8+ZK5JgzKh0ua2g+u2q25P/Kcmn1WJsDN3WJOvvczXHu78Snrd+8E+okrGA7thB06iXpQB1kxOO6G2/j9aJpklI/5qK3JGx/x1TEbO5Bj4OPqMS3+wxhfnL+jUz9oj83OPmzwNRg8NM6y5b4PrSckkFkISBT7vdW8ZdZAg8XJ4f4D1fEcDEAKjD20qe8ZK+dMUa0xn1G1le2P24G8XK6SJ9MDykjlxD3p09efFvKrjnKlai6FPECnkwfniC2oZlEzGPnCugYaxBWEJieLEKEViOh43oZfySYXQIO5YTXeIcpwt4fWSKSkNAvxk1s4I8nkLh9Hr4XvKb1j7ZfOfnvlx3jrucpc9WCDq4RsevfNVrlO2/I4p3Ym5Cpmh7JUVIjzYnrfYl2GCGEgGLljK1Vmf59EiW9RJdIyVYnIFsqPNQg1qU6MV3efJ2FRLBx6vCQsCYOCSfsMBq2P9S0Ia3yxANfYeOkxnrbPBwK+i1IQW+lnKndePKbpmD5Wj+TC0faOmaPdLypjqrxGna6qstLTMBi0XuHXVVe028uIZ4D7JtncNm7FNKM4Us0/fOD1u/vwXImcJzvxw9SushTLZxbTtB8OZIaR2rK5m/TS908vp5waTRHQY2i0liULRvHf3TTyMPNTFgjEhUE0e9c/EtcdvcG50Bd0Xnb2n78HFycJh29iS87be3Nz+1rsg/aL7e2AuGAjarIQccDaaVB0zdMVdjKCcgE2N0jYckvWTctQ/C3/a1B6S04PTunvkxUz+vmq2bb1Tjj00jeo8RrST93c7SFELaz1SY/1+K47dd9tZU19gBI+yHIPRh6mUFy+hAPLLtiTl5Vam/gtqMsIb5yBiXVsscshxxpwy1jLxdrn1gp+ME42LIvgwyuwn5/YNCtCx6Fg+m0j5y3M1L3t3Ambdx19lZonDSpcW1L41roNvkjH8lR9+MX+oLqbanNxx7BmdgjqzMgydqIOx/LD2gl4UIArGy9ua5Z1kU171N40cGE4z4bhe/LUGTxVV01th23QyJo0piH4ltmZ/22/l85vYv/KM526nJnan5WI9ZXnfYgvxs0LFin1DJrgSYjzRbL1o1YPjv28dnF8c4o3K5hdIaZi7P5xQo2axab0G5uPyj6JiPyhQ2Q1/pCgRUQBPQ+hliTrPhcBy6hAflaqthXHIhsvrR+7R+SnNL+KqXaqLi+YU7eP4g5gVgN7xa4CPxOeI8NzI7zd7FpFf2kVO8jEORNrp/TvH6qgkbs7kmIA+iNewoWPIV6eF06UsQgp8ydqczqZoupcFq7Hd6q7G3MpMGOoobS8q9+t7dslOG+y0rd1yNX2MV/lpcKP6jVeK/tXdlrAq1JMj6NVCZaUI6guLhtcuhmsb572PPsbbXb9DBbIEiEyY1kkP3U7TKIOKhpf5+9rsQ+TvWea/hbJto8hb7N5sfnHnzeLJhKvRgGsgl6sUrqu3hUNOQiJZW0jcfEFVUR8xSPc3AmA8Mvv5MmQxu/FfV9cS6XpDecVNXzgwADpwVRVSj88ii1WMKvdpcQor1MPL5crA+5Oj+8qJXVMTWhp488OZOHeDrU2ZHNpe+l+/IPPM6rUBZ1e9VwWdHl4LMwVdCOHoctztl6Ve69qqY3GJ1hTPnZP81swTyeBJJgoNjEp5tz9XZq7QI7nvXJGnbytfppXNZ9dhEVQx/DHM2/jVTO/oK4RP9h/bhqyrfTJ3282nE4evqaYpMTYJw+4f9/BH1WBXJapJqrVY4tPz6QJI0cdgllavWaTVuPcn+UdLb5jXeijDEnGbs6nJoxS5qNlSv8YJf43ClNbh6iQ6FjMYhhfx55iW3OTF7PSiKHhhGAJ/scM5jo7Y2ypMjmylV4hQQRLOPqU9/tG892khgtB61s7h1/0PcASptbxCTz0nZPr885Yp0DO1KVydmUvxr02a07uYt/9LO2QJij27iaKmjVJ1/ING8L4nGz94Y80luykwr0lV2PbWmNZr/ehT8HoU9coV/NInKP/S3/PuId3UfQIhhv0hdF+9q5j8Dk3bN51+cNLX1I5v8115WhQuxCz/Tn8fgBElxCcAEz1jGo3foVmBV8Hk33UMfsLWnqTRO8mDAcLqe//OHpK9Qej+N0KDybF37/tEem0tSDkRkngvEl4C8P95llyJ3ECvYvEiyLi6UcntqyA3s+ruS36iF8EESW4pd+S2IRJXH3aXvpr3E3FzUs4IH2OGjIvZNXiF3gt+dOn1uU/kzkjPiwc504j45tJEGfuGG6WzE3pJb5cfUJwu9gfWPuV5Py85kRwQA5of3ujeZFGq+c8YqwiiLeMxHHx4fTMltzD4FA2WarYV9yJqYl45Z2EN4LrWczrFX0lCBbZC2SwIKyECWO3IOofQvL4K9s/JyoBdnOwUGDhQCpx9zYtrZy0cMXxsws+v0QJbsfl/6vY4MajTsybnFK3e2TFghTxpLg2PZhpqLaFWaLvVwrK1koKu51to5eVbXUqxrjIQcVNU9N1+oawyr/erFJhLPVQjTlo3LwjplSQLwhIQXWzjGMrbyHQIIXEDVmvp2c3YRSInqOYvvRgBkW+lp+vKPAB0vasu6yQQBjkKMTx17dh8RJMN1GTjkNW2Xz2fWBwjzvCupYZ9aRSMDNcgfJZ26ag4IJ5x3Y+Ufp9i//1vC2bw+gVOKkPWXWRl2x05M4zgpkUGaywJwzVqLpxTN2JucsvUJqzG+mbxMYjvwyeq405uoZ8VvvS6TSgE4xDIlEEuxhcPTi9YvuZBTssaRTTqp5aWu9EcEXRI1Qh5fid/HFz6bEoQfI/1ffUUhGAoMYODQbKBcmLUZ69w8V4f6twl/HA9O3I++d9r+ZezSxc1GU8k67dfkOYPG7CoWxGU79eBnfzgvwLyU5ykDx2N+sKRlKl1Tr41hJ5UrGWMYU4nCyRHk6eQqgZxUkwCcdUaalUA2AKE2yoeS32X/40/klBcDF9Z+y6SAsq0yekM4x1GAp+qFQEZ07rKScostoLTu+p+vL0RpQNPEotPRbZ1MyBQMUmkfCTFdy3oCKmTmZSKDM+7OI3h+buD7aHnYYsIxkF1cR76PtPBds8e9ZxYjMWhYqJTF2RiEAjW+7eoi4/nZrOOZMu2yzvyQ8W6pQ8yKRr+11d5Nkvq8Q3i1+cV/dz8MuyMssQs0tvmsA3wrBUejAdflBS12EdNAG/rwN07vKtIe9sex6VW5UezOxUNjc9vwSOy8H9ie3bALGReEDH3zr/596pF8czKjd3AK6WnuwWDVOlCmp0rlwmC6SFsepyRZnBbImWnt8sOL100+BNY/GZacSqzR6MjvjPtXs+yXgrYP/TbDcRPr7ZexhZDW0YSlowDS7EYvTAf7jBNVwj4ItEGcKUPW+88U0UVKtg2sqqp+SCOY9Xf/5IptcYEGs7uWO8ToOYVRSEC2y5MtaBF3zhrYUt2vlCgw3O8p2Tf7wdsBzd/L26Tiw9LZhawkNg9JH0eLNuZkdy7Xv5eJPnS+cmjT1kOIckNlIuKdEXsG11IpOlSzmQXlxhvtjhYjtO/gD64geZNVqotmsjU8f29bbhXfecZenbTjcPPTJ6B+IzHuTf9NQnIn8r0+Kh4ZVuEp3umeS4h5g34JGET6aSJJ9m18kHpqDvzG4sfdoastiqESaAeAH8fYF+HY+3tCecf6S2ghdX/HqcP9CcL1ZRr33zdW3iGsC5nmMdrbnTX7z9R2zQg1dAxGJPF1FXFMwX67RFp/oKq/nmDrg7n3pn4Px36u3Ac35xhtf8WxauwvfinckvfGLfcy9OP0RK9CWWAZ/QlwDC4xP8CeJfpn56dxtX//reHiLsEO6DUMtof/p2OeeSIX7ItpZEf6IWE/eP76Ap8C/fXqdGxz/egy9+chy6ZHUGeZVHXmkqDaCKNRTfbsCRtcmLT1WYXreMumL38SUYIZ8bFqIZcz4kcr3RTTjuriwqxbaD8+VRIXWQHWwyLcvENdJuXpOtt9Pl7u+0IRyhTxgLGO41BQikDPpkdhNHKDEOXwJuLqmgoAtX/T5fnJWexxc8pdUhjrZ+pKS/SSnWCvVqL6576uIj90oCeOdv57dEPx968MLBwiPLyQaZLcsNi7VEHAwVxX8Y/V00L2k4viGBFIichFhYqCy7hBuGIeDuVjNSl2D9itlEVd4aS4jxzWWmUyKLI5DARyJjB9HFt/Bsal4Qs2V04FWeOaZm/QiYtHCrGXMNjFXXMQ/f0RP5wXfXWtwrCb63NqTf/LZ27cQtr4cFFuqV/d5az0drSb/nLcgr5t7atRa3Ax6Ur1l67H8LCHohv1d9rLqfauXJe+fnzG5mP93BCgEPeZq/eeHMZsdnr91xovhML2Eia9NN2Oxlv454D27n2LC8zawB5narNGTD41hgMP5MFCLyQjsIWULKw3Wf193ebJHQbbYmQSR+6xnBZkyCa2jFHAs8xzcJPhY8Wsh/nA+VbR9YYP5iP/sV6bdEerN+bUKxvW+X3VUqC5UbKQu+cIRduZN7jodUL6mBzwT8yYfsja/wpTVX+eyN3z35wLJ4NbdG2kNagr6Xr77d3HtgUZCMQfGT/e/2bu4JuCDAo7D5+P0vgpD6OMtbpaveLlcpfy+rWHVKuFC+8v1ypepdWdnKmee7a+OPN6WQScqUhOO1u2sTTjSnksjKVOQJIBlHfP/ISMajyx79vVcbax6d/n/F4+2JomNM1/3VgMeLAYf9TR2HF18sBi81+f1LYOHG5OvOntKy7p5DNcOdvWVlXb2a4MVqrpHJ5BqrF6t5ZpbzAN/AJNA3hQIwITd/kbEVYMWfpCJABc+rVS5VQi5YVxkakW0Z3ybyOSjCqyAThZ2Vcj4buDu9pJRXLONnhG9PJmUSZrlsA35zK0jKNfa5m+d0Ju9s9x1c6+axbm3BDJoHUCoDGxCGEj1Jg2JZy3hQzC8wHxTrke4MuuiGZAZdGALeoIsCZPSNVE7LIBnUbmvEbFtVeiZ7WDafemQHKx4+wFrnNF5F+CosZep3/1YM/fsAt1Kux4TOlO4Bcbx1VGkuaivtmLLL4rRW28/hVYIlhsBbmG5W+GB4pNSg2UROZAN3h5dMlKZMYyiRdm2ZJikppTEhPUdKxSFlnE7I7iZl0uUCeUUcA7DCT4Pl/B3hByHlmvbczc4KyzvbfZZr3UKhqVswg9zgR5qH96yv+PyNWYDGVzOvWxUPHciA6hRrxV7mCKoe4O76WsrW0CxTBVnNtmBGhH2qEjMpq6OgkmwjFNsawPIwKKkPsD5BbohjArJh59sBL07sBxG/TGGWNinCS4Fl7RXhLyJfwJZMiYL/5uVd+UrIH77U3V6aK98Ox5TvB2bezlP4tn+noi04tQ000Q8SxQjFdqNQ6aAEhAYDrGsnUWd92ADCzWqwuUk0ujQrZf+eAxitBm1QiVmqBaAgSiOWsvUvOxT5sCjW5cPZ/lm+oVctFejDtk4FuW1zxl4b0aZcsA+UivX+fn4dh4uZuoJ7Gdg7kB4XM53GSMpFW+xl+1FUdd+1+6w6KOUdbMGp/I3cVVw1yh4pFyfiRFGXDOmBk2IYijVkooRlImMs5fcIXwEpk6SUcUTKFS3l/MEdco/wKCx185WMFDQiZ9woeFvFiA9ulr8Fp/JahspULHs8CrLIpqOLTBGVR+d06tmQXfDSJped0UXGYw28jDdK8XjFdhp4mQyH9AB3w9dSpooaVDG8AqC8lOaIlvQivMpKhNl2+6LStAue43MW6i5x5UvpKvgSToKzXfhdmjXVhz+C/sO62jdcVVwQJ/IhwjdAJkqepZwOpRZvqyrL+BLZq+OlTCosl0XAb64GSblSZYfOyg6+lB0KPuim7Z8pibpvLfrUuz9RkniBGRLGsogtWCwLGatXKX+r9pWjyr+fUjlZ7qkXcOotjFTd/TZqHYmN3SyXUBXf1YDqLFVXJG8AKbfllFy7yrKLbkqQGHLw2mApDaEXdsZL4ReQkN2J5fyMwnpT4Xhiiy/BqeVJdU6jP1jOXf3FBXoUhYlHQIeHrgDiRNShVHdndUpGB4hNGwaj95GXcztipvuO8HcoxAx0SjEo5jcoHXBB0RORx6m3YyZu16SBWBUToA5mitRbofQMAHsVs+NvCerQaHS1zP2JVPJUXXf/5khvJKpDsjL3F0g/Bjrtc9DqKVe0peWbgOdQAAdYKq0D62pESz+ux/A2ZG5AQiliLTKZkdUtEDjbVNgqNezes2sF4EDmVuG1bt5oaUBuddTCwdqBX0wpnFGY1tHW/Kbe1o4sYpEMuh78rS29JgQUc6RCvG6x6VDrMmIFOhtfJVTItz63XY+E36lb+SHQLY9A1tfKEaH88TPAPYN3tAYUu9sYttrjT9RFVcCXBjf9LHGgtTj+W8wW/+ytHnAdf6hTWevc0lLoPOhR2xI8mN27sx/HFEhvW4trMyy2LUgvtavbQQxk960hHNul+/7qbmnN9tt1Xwfqv3+gxwbO3BSO0K2y6E+knnPXbdRAhqpMz5Rzpb+DL7iRht4KCIv5MUceaG5FwnG28HhlCbk0v7P+6QejzmYllgbAgZLMRoEO3OCg77dMjSszp9s9XsHwmzMQU6vMhdhSZ0she3zJWOtMBFFvchS8Pfpb3xhWe2sOaF2ziJxbXiN6jmyInroLi8HOOLrWq1y/O/XRDNZSZ+K70qwlw8FBTY/ybMBhLRNsBgQMM0kuDl/GoZtclf9WoK91by6zilY1MTZ1yBQVsMc6wuVcOavU9yocSifzHs6zZ31LrUFh5t8Ba/d6kG1Z9CdSzWvouonaL6Mu7vP4GeYY/xQM228EjB2iaVw2jHLr7S/Qm1j41lh7uq3EgyATV8AUfBHeZjREhjZzYcG/DGTqKUCwfxri+tpO/gQYzxCltZn0x0auyUumusR3c+nwsLolc6VJgnzNbnl4+a4y9BSqsE5kjt+QkLwv9V9yIp/r5KSPoJRj9CNUbHO5VndiMvxWUl27AzP6pTGM32ybAWPha842eXxO3f7HJy00xaIiatYsAtR96IHhVSyBc3KhMYRV89vFtwqKmVasGgekB6fGI3P7ZepikGYzjCIM4x+FMOZTsxEIetpxflMYY7KPO367Gu6fHZIgFCNVmcIpwCYZmgLD4MWHixZVEom4pXhxykgROeoElRzP2yRrMydXvdg5pevb8I8Zx2sUF5wtZGmdhcPPNNOdcQY8xMXwCF8ko7oeWRY1B0YPgCrUXsAu4I2jwAe3EF/KTMZhL+5rFK5Romge2fkJcxQvxvmwr17gXa1vpVVzyAjYTNT353H8kocmrkMHmD03SN81FUfs+QOtyWbPP39ZeRaMnOtfHYDhgLDjYGCIqJEv075Blxf8uAvdnz+aXaoVmRJksHpze4cgrA9ZfP5f0r6HGwL+dxfDascqMuyWRcEKjyyPrDVhNvhYMVvcR2aHAw+1vdcXOlidcsQJY9bhWuCeKstfX5NtB4SmHruAHz6xHKMGB5rsFOhjG56ci+JmmkUpnSlkwD7LKNm5UayKHVBOMN50UniI6kDD/0bXCAsuN5MuHyNJS4DB3M81SJQx7NgRun2qGr/Sln8QbyAag/J++ppB7Z+8QW9kER+PCnP3/VGQYLoYnDON1i/IZS8+fXy8zLsIuc+C+wOklZm86ffcxXRLtvnORbS76eyk3LY7dGcbTFdvHsdY+KFd2kMMBhrdDIYCj2SS4TBBxK8acA1a6oPDnFEnXcQZp7mNZlYXsZjSfZWfg/W5iIU8+rh1NFMtTjTct8cisvpofuBS5zj6m3lImHD3wz2wr+wilvKKkRjNtpaj6cBRGl3gH1d5bLSF4uyHvknwugjTc3xCJhQSNTt38HJWAFUAbeJp3r5WXkymisV4XopD+BPzn2rYtGaXmPh/+Gefsf/c5riIC3mQdX8R8zwkW4nrWqCGetfSIEZUbLwP7y4RJr45xE7p31JuKMmxYh63/A5vgyX4k69nCRwkBFlUaZCz736mxMWmP2V/MD3bB5hq1rQAfgwPcTE8wgPEg3KRxADTm4ccAVwC3vg38aE4uB2CHxVH+46duZjNZbOiMpD4PcqHldevAP3YOoVvZ2AlzJct5cnjx3UpJfPKHasz/Y9mOZ+568u0tc3KmYssJ+/yIKV5ZUsura2/MDq3kS70b8cgZfeZw0hfM41tfVbOZL6iAveKv0EsfmPGe4w4DlokJ5XHcHBwOLSM7uHj52C+uzCbWIMnW/Xqz1duFOvgFbQABNULD2iplMBhXcFNIdLw9Ld9TkYYKMwF9AJzboQDm4N2NpKBelxKR3bnnSMXPUfmfwDFZeBfeo4y/zz2KnkiSzTJ0i8W0oobxYxToh8q46ZFWFGbAI8yDa7V82HBWv1SDz63QutBxcfA56AZoK9RIA5Uf2cOc1qXmxI5TPkTFdQoqZ2rtvv/VBFhptmIWGQuuhLL1rJXQObKPTreOa9UAmfWAA7gAKDTtgDoA+3Jlqkgn4ppEy8K2tgIoW0KgAbas1HRgnR0TFwZkjNwTF2X+RCZE64kZFeYY6wXC+Mhq7t6rCCCpGhyohYsCkdBQYPkRL74dQGOMEVf7HBlzKSeUW1XgP5MuSKeKef2QHvxIN/O9uiLdZol6RBH5nb6YoEZTs8olWcS+I2XwR0ux6krC93w7J6JbQpdrvprWPBuO/ei/ky5Avvl3IyLDxAoGrxNeu8jhnkgE3DUb/P1JWArauAdH9K0LPwP6Lklt1xS/WVdwDQoCDGQOQfPZGQlAcdJeyWERSWntMwkz1x664Hv8APLQyUO2ry4OXQc50DhSC8bPWHDEwbeoM6dyg9EOz0vR8A7eNJ61CFx5JOSjHJwx1Ut/zKJbst0R5LIKaKqnyOrvLuYZnFZx8ph4PPTo3a6xg7qyZz2rxJcj6d/POfFWuh0VVIw4nBoHNXDIbzNMNXrQn1X/e+VmMthBtAgX5odK1SIxRlbPVy/JnrL40Vu5XFveMVrqdPRdIjeFLyPRC8KkD4gfl/D33CR0fam4JIkelDwlMJDIJZdmCp+8O7aeZ7C7EPKfMTOChaC4nhqlfnEfCy7grs7/wvun5hkHuwkuUnOJZyfWtB1fNPq453vgZVbpn0enfkS2QkLFN6dw8E1q4z+pgFDX/a4IMRGdacGgZ4UDg8cVjOCMps7zhCCWmd2V7Wl0zVOE528IfWsO3Q+Q6zTebZYY3tc44jBLdJK8gl97ZNGaPuWTBnjItCfzRjdXJLYIeUJpJNl5JPaD4WAxMZNJ5OFnNw8oGL45BmlU4hR7I1bTiuSXKbdccjojvgYvdHRU4wgl7nk5JnRl9WVyA2Pn26qAXLLMePG26zu4IaTpx5JbV7Gaa8cvKgfSRy8aC7SK48tMeVLPTmJQ15Xcx4cVZ2+jtNZhttBc1qlLzfKEo7QY+K4UyIJnbR1fPXC19a/ftLp3PXW2PHW2O3k3iY3IHkO6tweSqvfuxVDmezSxDk4F0/DM/BMPGt89uDSsrqXagktgkHBe72DBJ4Apy8xEhzyZLlXzHs2EV+fM9dn/OBBN4sD9Eyp5HJyrSn/WeWEBJJB1/7fXNk1ebhDDahgGaxyV9rZalAgjgUOdTy7/8+m9h8CeoqeeJYaNx88+PfBI2VFT3vaz/ww/CyY/3nEi5N/WTgDQyMe/WX/piebQnAyzf5J5xDFa+4DqZ6sl5D2c+hMfBrgJi9ORtUgjuDKiALsdd5eZ1735q72UkYae03w/ieC4GSnuPpu757DXvrf+vPzpsaKfMhi29L+bKjox7AlVW+uCfamczX1/U/mAzZZ/am7HbFPv0UGv4qCafxkzGofVr0DYPeCwXQK4avmzAEw57DYneI0wuvV5i1Yh3rjEKZ/HD2Yhl6L0ImgRYsUQZNSorVbnSkgA4J1swZUeAKHQRYwc37k69UGJjtSzwr2A5Bga0nR8adFpxPaOwtCTz8gkBcmI2qUGFLrFdSTovUFTcZT0XByfN5htvR0B0TMq1+gS4y8oX8rt1MAB7wBRY0AvLgFWXhjGa5YvHTG06LRiaNZQidipjprO15wWIxOdvfFamScFcS1yVzSAdD9gxad7r5aFuRqFLcEOyckR0+H9G41okp651MYsx1tyahto1ryot8k1s7iiNpsZhIsu3uQCYoWkycOxVTBo6Y5cZiWTwyspJhWE/08XXRqfbCViLzFnLHctR8utHpJmvh6XDQMhq4ot6R0vYoFk1r//63jBwacj0TM5IzVKaDa65WJa2RLAszEp90U9CZNlk5GkbHSluPneHnTfMc5p1fVs0W5NtJheWzKYJW4Ao4Aa82jPI5L3KogDkbr3WT1BGKQqsSmdCgvAGYCky0u7QwFY8C8ux95h9UYjhspZ4WEAYAIfoPafPJYxTamOcBVSzG8Q73FMlJ/ihjZDaN4SZvk5ekUawTS1ATDSSXVMnTZqrYZ080Rh4XvpEfAWcmzU0Gga0nRGUuLTie8dxbABOwB7Z1cBTGYJewRZPnkTJNDH2cr0to3hZeTC//bKCUHxHohmKh69Nf61qGcm2MwBN7cil5KLO4XDikdmwLewJWEOJ2oJm2M0RtTQQE0a2MN81nvNz8gGJ+nU9gL6nu5OmmpHZGnJjGqVr0iuGOgd00/ofhCwXSKkJl4CThJpNyx+wo1QcNhhTkgd6/qx4vrRnYWV+iAaskb6EQ08xK0w00c88XC9MjSgNAC6fhHp5KsG6+06oBJtM7ZqwfrKQjOP9zxg1ea4h11jLLDkC06PhDf8TMC+UNKoVY9nYgtMwKF9MjBmsyB3Q//GVpMMsX7Pxx3diLMZNLP5gqtcvY626fsdPuRsyxLMNcr2RaN1InN2oDbrQfegPffiFQgXkxG1NbJsPXlTz/cJGCXOuqfxdH1t2+kVhE1FQKK3p1Uk4dQOmNiyWfr6VH1qvcmou6Dtu5OLmYf2X0s61c/W8YfHhbg6QJ2mrJmFcq02jZx/cAQNyyKg3O7ekAJu6nIMERcYuSOYrmKpMkCocN+irxEpJ96cx2DMAfQy5Knc1kYDwudAUGv6uexujWID/uGLwChnxQSzmYfrq3ECdSlLE0EbTiIO0FdO/SdWNSi4eYhxANhx5c65TtCt0ivnxx5ZTi4IiNGa/nGXzQLbc+HAUxLQcc/2kntq38smpYbEDh4nioow/BztvdWPbyRY5AUMGezB6uGJFNcV0dR2x6NqqHQkLC1eguzRjB+sxv+qUX+guu/qoMlUF+qeWsNXR0x5mkTSM0spqpsz+iAoFf1y1HdO+CiCq3yplfLik39Hk+Wm8uexR6IiDVrYpR0x+onYlEmLPnxOvrvjC/71MdhwsmqRlxn3GxNVscV55avhdqk+rf6eG+lFzXSSEbXLGDxMHMqmJOsR9pKVD1Ts2/eulFzK8UY4dgzs4AGvnT/Y9IVUcxCY4hlbZGMYvevCGPZvb0xe/ZAaclq/5fg+DLCHWGZDQg8ubVDrSqwF0L1EwvpuztUShu9faD2VSqk4VC/DC6FwJXvG8O0nMSXbAJiI+7hFXIh2B0O2Of6iT9trk9mVnhv7He+nkgt7kGeesbZryiVZYFanbp02kqr2hwV3qc3oYFR3SE71BI50x2OAlEPKkKfyDDNBR7St59lUzEGMdEDxtVKUAR5ibPF9YFvm6BWzEYfTaK+ou9T29iH6CbeAWOShAz79AhhY/747CTd8bxx+ESI1q//qGHDhpTbbxJmVArUWCvZkVf6PmpZHyNNTxaY7gfK63bRZ67UZ7p+Szx83KC/QIwtPT4Dcnzpko712hZh1aAAvmj5vKITRVGJUTlbX67YZ2BOIG0K6qXT0nIEpjReNtWIX/cpBCN2T21BVXEr3T1hlJ2iazuvZ4IqXUQ7k8WuFEO3wVolnmARXsKx6rFeTo4i0fmUjY6VvBb9vZ17XcMZCPV1H8tG5Ynvvr4uJNzFd1nMwvs8ZwknHZO/9h3NGlKz6PobW6M+FsMwarb23KXBu7C/GntaH3WYP1fBTKdtPKQaBZoWHGZ2zT89klDz7giLFKMxylLQ4XjECDKuZhItL4YVW01WIDtW9Nbf5fHn7QxpW1pp99saDGQ2OZs7mvl0DhtpZLU6s8/aC4/yzgg1RsLtRhqtP4ccVn4mTYftZ/W2sOyfT2x8egLZquqINnKLvLpBeLz8itNRWUzVgBFr+nDUgAf/zZ0veC6pSK62SHWRaRwFYD08haewXj/NDTUlNb6V5xzybU0HquqB0mPl9aL2zwdSEr0K4UguBxLSBNRSbiNTSBOIa3J0UFrXqxGyOVEsLhfq0wqljWxdVv4S6DzadYIoSydn6GM7oTRGC0VZruURoyTSkJRHTVihGmapyC9jGfbkTiGRYjAwlLLVoaljlYc9aioYOSASXfg6carz3W5uIhVfCei1s5RjryECqcLxpTPAn5IPiFikl5R7o1JDGyN6p2qMuU/2irZqoljPS6kf4kWIFVLpjnnZbJ+MqZ0U8LWVEl02JVO/6hcQs2t1uFPhTnXkDGLVvPE7MgQ5ONkwUhAn61WkU0erMbKIMCV42uuztcPuO1a8TYGFpjlcOg2q2yBhinlbsRJ1M1RMSSgoxe/Qj3jXF96UEZdELaxPPDOpPvhqP/fpiKJ3DtbCVjFvF7fstNQnb6qbHw8aZxfOLdGnPdVcDBnKFUz2L6RpALTAMqJP6xOdajpc6VSE2UTtFLUqVE11norW6ZPepBLDjy2pyfiXaWwtkm5veBI1Wv10KmsDljriDfMpJkMv51Q1sm4Y0mhiZ0lPyBrjjWXEqFafvA+tI8zL2xGzV+w8n7JocCXfFDYOigVaaqwaPFWYVm6sFsBtrmhfW0EFgVgupdnMkL28uig6KIZnoMzbgY0g1rdG9qyaPQQydvSsigzu+1BhtnJAUukjqJz5OLpJx2Ri0jHrOJOLOBsbpWRU4f7Q2hdtGSfW+uzNGs6qLVEys16cZYT1OsxWRmFKcN/Rl2dztoz4zM6WgUOUAWQyoFt2n/xKUawcNstxhq9TlSWxwxkNWG3vv5dad4jPP41k/f7w4PWlElN7x9vRQSRmQWD/FiGxMSeNzHpn+ucuBMuc9elshJ8b6s8G8KcadXmmk9HDKcOkpwS8dFh7RmG0Grl3ZKV7PKSZ5nQneUkodb8UpVJ6yE/MW8LNLMQ95iNTUo8G4x68nhNlOReR7l3ASuvmPNwAP2/KPA4xxNhlfrv5ezo6vGtsPaeSmXcRXlZYsIqke93lbfXflNVP9/S453kbYYpsqVC+F3/Skej65Yk7QIcd40bexXQVeObp6PHOwhsRFbe0pvOD5xWjR8Cr8XHwwrwXrc258on0NZlez6TveCGW8+BSkv3VO7MY7nVcAVdArHRuhbs8bNHm96m3SrQq6kB3UE+aAPpEumi0Yo/h2rkERwwbQTV1kkwTYYioLEo7VE7m4POdh5y9n8pKBc87cda6HNC6WJQIatf1CzIT/WJ0nZfTrysQh7FWKZJ2oDDF2+sYe4+IadbP4v8lF4BpGGBh0V8ijpaRp1/XOFiRuiusLGSv+wpUnDapWk1q1TWNiKkdc7CWZa1pkq39nx+5zd8DH8fDIC6EXdwN/4iO9bEj6uNk6mZgfiqRki2NItWlcqyHFVzkKq+HQ2jIDa0RNiijZTwee2vj0uqLpdRyXaoHtVnBypZSbTE6pSqrdmWoTC0aEmpFl0W0rfAYGe9xetyczvMy/fP/5vB8ve5cfat6OXpHq53t9s7o8m7r0f7cLfNOesglbvawJ7zmq6beccS0i4Ek94RTTFdyUp2uQKZzKjfyjg1wRFnHMBe4zwYx8tS3yXV1qa6cq10ztULbdETPunZcirkemx07FrsYeycOGhcdlxkHj1PGPR13Ox4dnxRfEI+NZ8Yr4q3x3vie+Mn4+fhvEgwTjkESIfkQDIQBkUPMkAZIN2QCMgc5lhiXmJ2ITKQkihNvJ2kkbUv6Mmk7OTw5ITk32Zi8M/mHFF7KeMoLKf0psykbqWtS41JzUufTNqYlpxWl4dLYaco0W9qzaX/SptLW0sPTU9Ox6cx0Rbo13Zt+Kv3E+I+9cR8N4Y9cdGIVqRCiBpjImGMbV8BhEBWMEQaFAv70prnkS+mUT3XipLlLAtupkGVF0RA11ZP4UmuokCgVtByfHnntN/NdYYtDLrpvf35fRmVK5mVp9uVc8VYwIlj870qNFMsEKt/b/tk9N3BFDVJT6tp9z15W19SrKlUfaTu1jsPfYwa/x44jBJ+F3h5qnHJPI6fZkBH2CfPhxjntXHpuOZ+IOEWekR0XLnIhchA9FB26arGgWDTWccu6abG/AiayDFmL/Ab1CLUNdQZ1HZ2MLkRj0Uy0HG1Ge9BdZZvKksryyk5hkjH5GByGhVFgLJgzWAyWia3CurBvYkEdXhwV14TrxX1efqV8uvy18lG8Op6M34b/lHCcQCKICHsIVwjPE9aJEGI5kUWsIrqIj0i5pCXSRdJzpL8VNyuaKgYrjlTcI0uQneRh8mHyJ5RjFCTFSOmgjFNmKFcoz1PYlAPqRmoytZCKpbKoCloOrZrWTOun3aB9o+3TMfQyOpMup1vojfQe+iR9mf4Ow4YxxTjEeJnpzXQzB5hfMwdYHKwElorVxjrHusn6zOpnw9ix7Gz2LPswJ40zxvmG85cLcKVcI3eUe5/7lTvE4+Gl817gg5kav5s/wZ/nB/mv8z8JOIIEQZ4AI2AKTILLQmCeJmwS9go/Fv4QEUQm0fviBHGv+LDEIrkneSmFS8OkndL3ZP6yOtkp2TXZa7KfcmE5QW6U++Un5Zfk38oHFFyKBcX7Sj0lTDmrXFReUN6pHFFZWkmqfFL5T4VTZauIqkpVg6pLNakOUUeqU9SD6sfqbxqoZr3mY62tdlgb1H5XZVNFqZrXJetsurf0nnqhXqev1b9t0DZoDDbDtOEj40ij03jUeM74s0nFRDTxTRpTtanZdMN03fTE9MmMzJHmFHOBGWNmmGVmk7ne3GnebN5tPmI+Z75hvm5+av5o/mtBWyCWPAvaQrNILAZLraXdMmKZthy2nLPctHRbflohtz2tCuug9Snr7zZ7217bLbumvcV+wyFwZDtQDqpD6jA7PI5ux7hjzrFYnVwNrW6s7qk+VX3VaXF6XRGudFe/qweqo2xwQ90EN5+STMmg5FJKKQ2UDsow5QhlgXKV8oTygfI/dRf1BQ1Fo9J0mRvrDmZqMy9m3qYn0dn0UrqM/pb+LyOekcqgM3IZYsZhxnvGF8YQk8vkb0htaGV2MnXMG8w3zK9Zosa8xu6symz9bL7s6Gx59svsTyxxE4tVzJKxLrHusQPZ0Wwl+yD7Mgf44DgnOB8fK+SDFrELRmEi5mED/4wlWIk1hEr+IXqys9CCA82gCEqhItqg/9LdRYv2LIchGYWJWJsFLGffs1b2HxtnGqZjL5lpyZIgj8kXCmJRVhwrSeU7s0T0hLeEL4RfRIyIvyenB91D6xGKUCKqKE9ULmoQaUTvRd8LIcy8N78X23uscFK8p48pRor/kXBLNki2SXwkYRKEhCjJloglckmHZFRyUnJV8lTyvki8HB7/CxQcEIAcdEIWVEEbDIMCC3AG7oANR5CHOreGm+G+84f4f/O7PM4zfEH4jUilaOnrEpU2Jb+UlnipIkM58k9+LQtyVfmO0q08UaCi4E5UMY01XIW5WIVdyOMsnsSbaOER4sjiI1gGkrG1s6ZWk9uEm76Qj8mNcp88I1+EY1VWeXLzhaAj8AVU8M2QcsgyFBzKDy1PFtb72RSU1FJqL/WQBkijpVgpTZonLZM2SLuko9IT0kvSB9I30m8pSJmFzF7mLvOXwWUYGVXGk5XK6mWdshHZcdll2SPZ77K/Uznl6+XOci95iBwhT5Vny0XyGrk6uMk++eS3wnn5zTrbOnbdQt0vBU+hqN9Qz6q/0+DdEN4Q35DWwGqQNMga2hreNx5olDf+pvRQ1ihfN4U0tTf9yOJo3tDcoNqs2qHyU0WpUKp09Uq1hXqLeqd6vxquxqkZaqG6ssW8xbrFpWVfS3hLckt6C6vlcsvjVtdWQeuD1ldteW0lbbVtqrafBdaaFM2P86OnGG7Pt2HMYDIEDBnDkjglFsUtb6MfQg/v0Lv2nqupkaAyfWVc79yz3R6oPXC+81iX+cGag1e7LQ5t6Vl5xH8Ef4R+xHXEe2R3b0fvYO+ZI9+P6hylHjUedR596eifRZ5FarFgEbPIWqxcdCy2LA70y/rb+0cGHI4dHhgduH1s6tjqcbfj3uNnBn8uhSxtGWobOjQ0O3ThhPiJuhPPnpQ9WXaSeXLv8Jdl9PKVQxeWh5Znl5eXkW+lP99j+cfLLVpf+Uf9Wv+H8m62B/bsS/ud9VfBC7n/0A/yVx4YmvnL8OuFn8ibxfN0EwTnLvJt6Tm/KyhFsbTKiq3ox8NHSRS5i9wkFjkkMcKSKiUo9EGjtEw7aYbqrH5UHze3tF1aXRvRUPfTP6W/Np4w9gzc4I26SZq7+QnL3frbobZi32rP2f8ZzQ62kzWxPsazafaVqazuoMZpPI2aMW/sPNoV3ozpIGCncHoaD5gyptaazPUljb7/zW8tey0RS8nS/WosDovPIltaFOzEbnbeunWHdetPGHzr54AkvoXYgCgIyBMUgMWVoiG0q+657P/F4+Pv5UGqwBUHXPHjbwdzL6MA5wNFO+5+4FDv3ve4b+x4sQOWQpAWKtzORjyqQElmwEF2LOfzg8yjOf8BfFH5pOfTdfDc/9AJpDrI0UO1/6F1Wz+/id396KWVr7LPZt6igJM7WEGvLgd/O4bAl2DUbeyP92x4ebhPuHVvTZmXcBs8pmQ6tZonqwnCscsD5kxJD8h3bjXa0rs6bZLBg07DitCUyoo9MC3Oqei6OvF8oxRjgwrO0x1FddWG7OWb8uy7QM5z2KJlvCXPJ3pb7bRJwbeYmMXocKD9atJs+wmNa5TL91rD+RZEeQiyqn5vkFgkbLyYUKS++z9h3KzGfPaNaypyMDZpzZ2PU0QIetWqAZsMZnBjzv4i2F6MRIgipDWV+8hBFJSbJTad/jMo/XizMlB5p2v16g92bsoTOChGzbQPZ2slzoKcTgDhWoQgIjFCjtZrQ8VP/pP/D1bz8NWOjxmAq43MbrwqgH/csXtzU3Np47UUKD4oR/Hffp9JMbnvP5bbXjy3FszZeP498A8QTacgaeQGUQu6UnG7s1EuT/PdD0xw5GVR5b/evQa1f6Vbf+IN5x4RY37r/ZaGDCDvPIMVn+r9IvyEDVVfnITVR88bi7U57YXKxGe+Oegg5O36tgdbv/SfgxHYw3vvvB3s2cXv4NNQbAVGdZ8FIViGN/0HZG7J3PrGk0BAlBCF37n8a0A62qPzYP/JMAAKXQrZWUbMc6NokEulqTchl86pQMu5wm6IdA0OcEQ3sA9++h5YMHRRz00nnRNO+op5mdBn5Bv0LrGdXiP20RfkcfprcbS5gZk7B/rRYJRU8QGX/Ru3JR+ASiBJmu590LLgTonmNYmDUJkeTb8JeZedqsAiW9X3SrUZ5weey7Quk4yecDiWyK0k+SH2iI26jrffNQWaxTwTUuHErbc5zWqGkn8zzg/+5SVmOUlhsOW2D0ddiwSnuq7Wirz9rhiYe1XbnSrU7v6ArOYnLGrRkiT40zJhKcSybriHSJajg+HFsLMmeRL5fMniTLBlD3soXe3K2w9g60uOStzBE3dIq3oSbkz56HQ6EaMXOHXSWw/z9oOiPNyr/RnwHKe7/BvujFd94M1YBzU3z3Tr39CsSS5DPyAaPQeVxybloB8KCqsNULpegd93p9Mfj0I7axoegM6H+qvj0I6c+oNQXO+ehnblPKrAUe34E+TJCVgK1XXgTojJMRdBDe2/HwoRfH16BdZgI4uGFGm8sHVte1/0O9qfVfI6H18t61Nd0Sg/Zcy4nqAvLb1ZNoyGIwQ6AZyA3Rd4nGfHc/upqxjpcDhRfKThacpluSD03UlYJsfLtdhMl5XPCovqd8t35K/byl0b9KWYwoZEIX+dqJZcS53x9YVhHzoEzsH+zDzGE7YLo5QQq5Qqk7Sib/gBZceJa1EzuSdVtyEvmWE9xQIpXL/0/t7WjtIf7T+u43W+EzDrw0VCr27Ve7fpxxb2sKaxaChh57bc7ddel5dDld2GDuPa+B50pH5LufNF6zpodEHVqmZshsvCipVlvS/6dqTb7U+tU59jlTbECYVZ/aPx5e74utwgrbODabA/t6zlGf+MynhTtZaeZZz6u+X0hVmLs9b2dkOzDhrQC54I+fMbPntIbQoB+LZyxm2bV34yumssdGkEbcYeqq05m+ArcEFNcxOYlk+/xWtSGv1+r7erDI6alA+WDdPRljn06KMXF/v19mTIR03wnKCTs+k7HMvC5uE2xQ0PrESumQEXSIRzwUon6RaPKh0IqtHptGEIx+9l9xGtC7fHp5uVHVwR/k8eCHiTJctJoYmzJcS8geDHggcWElOT1F7qUYm7Gr4E52SoTGC6lN3nMSgNLo4ka7vAXpV41H3FEJmljjx5fpEAW1zET00SbF7nTyV/5lnNb+qbox3+vmXTxW1jDu0BwiUcU9pClSGIyypxcJu8WewShky3YIDd/kHYUF8MVkfMAfTiecSsqR2FI2ohuuBaVgvwnfmr8hGAXAxwJOPWKokCLSc9CnG3dF5DDBBPsGY1pfRTOUT46hHIM2u12C4zlf7g0IL0ZIaImYpfV5YLJa4CC8BA5jwt9s6F353qL78hVzAyGHuDbz1I+mDk+9+LA5aiiPWfXu8iZA14eRRwx2E6AnIrrR9U2ddvr+BV0ahd64omupEHaYNspF5QTKvZWtjf2zA9PVJ0ruaGylKhRFVCr0lytoijm5lbwj188ysY5ZU+FFsPhv0Q8l+6JKSevic9hGzCyxUwx0EmgAIk526xR2qrJq+oXrYAq6tlwWV9kCkdOnv3IoJAY4pMryHTIBjSc+L1QQCpKqSDK7M9WJb10GDUUUtk2anp8MIs2043hvcfSLyMMq+P7VO7t/B+koGnH0PYOFzTpHd8kGc7tWOXipwABDh7xIQhV4weCL39ZfW16eEHK4MDxmXIr99DP8gRyMng7gr0obRineaeQmEMctht+8MG/KKAgAME/cBbwDvfgwSXvoPNrdg7dbfv/4sNGhTXwuh8Mwv+Iz68xQBIaEYi2tO6UfIz8c/evHTp/OdkxJ/vgVnwkXsEeOCAsTS6wMNO3hnGQPTkM80XH+ONFtr9krYZ5AgeeP6bm0yP447rWxxRR/4Z4C34qwPfJVPqGxee49UvGFsJVti14I0vK9abuTViLTD39V8fvAPWslyFtMcaLRmk08ScxZnOZi9p7AnCfEy4IpOFO3Wn5+UEL4CtOoZQg8E3ee0Q4fbyKnXiedfmRqnO0pJaz7u2syr1pD3HEhik1pO1pItQMA1LQmjLbt7wqty4vQjXdpfxdRRQsK73A/vGUzWAaIawyadvY60IE1UmN5/oiUSunlulFzUIL55P/2BsCwbS4BUOd/qfcmaRZuVfsxTGNSc4j0xHi/QxBS45U2nf7yGq7oYOqmgtCxFE/qoMYXJE13EGPH1CLKSL5Vy6IBz0QbO28HSBHKSzopPeZ8YIfUqO0l+Ij+lpoh+mxxo/1aPPKCBeg1a4QnCC9Z+jUhL0VyIhZ1nqKFkGUCe+Lz2TsOgCQKzaE5Pwg8WWYIwloSIpKarTz7XHtGORX/feCsF0MCzH+tzcqp9xgAcFXw7BAdI7CoPx8/opJQstNXjge7X7Ovde/oPnJyHOTUD3Sq56vpBwBMhUp1uAFjeNj+Hfa7RqS8wrEyFdoxOU42Hq88cS587fK/ZUSEGZNihr9o+Y8DUKkTmbYDkInSUmGRg/o1EYWJvsnKJ860jif+HPhuS9Npn2mi/q9U65cVIuB6wVClOjVP9HZkZ6R8fw28hm1l0dYaA22kEgUFN/6ilVYH5wYDR6R0mrHKqBOU50+JRUPc2Ogh9gat9XRdee25PPg29/AcZOqSMAoTAHVwzid2sg2kTLxiUMihPI09JweJoiNRoVeY19WbcJiTWv1gSvDVpAw+035uImwTocgHWJAfY8RSlV17ZuLUNntjo53xyM3hGEqYWqIwsrSF45WdtOZd4HqAwKu9f03PX7rswbwOnHouSktSG9F/6qbtZ6Sa30+ZxK8uRm7EcvqcfBu5ezdXxA3yUOlueLX0cC93+0eQGs2mED6CPJxo5tZwqaDREhF0FgubYg9izT+PQRMY+CJfe60SgIy0nAoDaHOwH4EfXS+B7UEGu8eyXI5TPhq9M3d/veyd0WOo22WxFKuZwLy8RCni6ChDoQxCynemJzOEhDtw7hLwsf1Ga1oJdjPu16XTJ7TF1lKjXNTv/1q5GLwGFWKsm+9vaZ6bIfPpfRVRTo7wwRddWXiN8ouvypMoWoUb/LeGMj5Pefpqhs9/ke52a14B3VPKPRG78mLh/yXfiTDTdyvNKzp3dffnnveude8k3+Y2jbAD3imppK+q2m2JFMhUNBZX/HDhzUd4HqZr9/N3IpBRGQe2v1ytVOGpXbFaJVEj6hmlp4vl2ec8vIGfYt7jfC41wAh1HboBBqz/0lhXqMF/ox78kTMrxx+5ub+B3X7w05pk/r0ae3f5fcGD/HE19sffFQeujWl/HN1w+qzqkzh3xxQCeBcESwUC5O5ntcNCbNEoJeLxczP+8m5fqG/QQ1SNzvSmu7i4sHuUyeeB/fpssKafGe941blDbSKwiJ1WVxzOX6rfPqdHNHpvxm+VHq5OJi3FZppFI4NStgY2+xUrjPUxKGyzetknR20H1iyqjRPG8ACLJw+qmwEoW0o9AAUFwj/X7HxXEcvquuD6xu7ZL1ErfIu3kIqyEYoeUKilgAfOsQvCCpa8yq+W+VQ6NQ0XYaksx+O3C9IBziBjaQ3Q/F0BTSVBJ3s0allfKJYqwvK/absu8FZw1NU7M3C0+jJy4sxKyVRiqdpGKJMOmt+mOgIg6Xrm/D8ht64bRe/0wB5Q3MC6gRUiw15+U6GQi4tX/wu8YfFMWeQSFvRiO3qTvMvPDGg+0EyI5HFxALKFCoS7w2iLJIMGnuyNBfmwrXcbOpTzfdleUHQdlDz42HLQASWtNtGFlw69tsK7IgBcVlc/8+rqVWS0XcC63+/bEzc9S87uaNUhJuvz6YkggTxxqJmHkRpsPgBCKoXFa62eat6uXN5b2gvMn8d7ORxz/G69ibalwpG7CSUs9fE75u6+LG5Bo7u1E6Rz5YjBanrw4TzTShWnCIhc0kaZm3tqEvlEH0YBpggz5l5xi2usmZd0vE8xYdmpFHt+V4PgbGL52j58VMZq2lAB4R4g5mO+pQVfnXuO4flbz9n3wJST4/iSfH9lzff9t7yKMXYmDDCRu/qOMd/tjbcMFrfMXEyI7rb/3uU+Tp24NyzFQ4V+jjLxY0xO7UcvsXFh7u02+9uGcSWaDDM+tAueTjX3gD9/b97EIsYGjJaUNjXU7bH967/OegcOBfANpjEAFb4O966NuHAiTdtzdhYoYw6Y0vIUtV6Xkd7QK49u1kH8gyC/Z/uwxb/K8vBinE2D3CfX6w4lgCklbYFrw8HySW+87c/QGw2KnqVAok4xXgKle8SoDT8WKwyU2tmJsaviKadXIUD4ri32msyocBVIeqgUkxMUvyo0vkBXTJnCL0OXmC/lqEEVykkYftJ1NDFhtr5b+Um9TlPkt3TgZAqmL8Yc06mQ0SqRP3aTaFzG1t3nJwclLVQCLzIngdgzAjyJOJD5ef3B28ODsWYqoB9n3m0ZwtoXSwX1F+psl962vNwNcAfmCXDatM2+qeeInlo++inBfpaxNmRNqhF4pDMLp9SFx/YdlxBgg9CenPiXIOhUX5FaWuPDZbKzzToLhJns+jj+QsM0rNcvH8z7WVWmgjvAAcAI2uyljNev3Yqyy3gXK2uvsfpaI8UKVYGmoT/8CVnosXAA5gKfiSadcok+8tFjcIehgjWf/sE5jNebgFgtHdHyZngZexGN0up9535o+OF3nmU4UHn5kFDoRI4KZtAwldfHsS1eZ+3KdRoKDYe5G/7jdPu96xs0GwgaZ818rF646xpxnLqulEeav/d0Nlnn46+Bu9D6wQv7Dwklfpvq/Z9dEfZXiDMGS/nXDjYpG0A9wwVcDxHaGfG/kEx7Ylhky5H/nQROI+/GjxaXQF0OCRtc8ulwZfm8RaMkv40AYCKv+N6W/wuwchYGeCwIXvjj7Qd5x9zZiKUcbWMyP3U9D/5k9QJJrJb7ADUAUQdkAJIvrlJzWx/0UV7/AzIGdAffY7rg8dBN7DJuqxizreaVZoNvqtQVPuc/jFO15HXv5komlIrO04ciwRGOXlJLgDoN+RAwCAybGJDkhaxUgB88GDfNsm8vkzYBy0cZgm/t895HMnGWSEx5hzlePwyRgaFlm32XskAag6WXL6MPLgSXqZYNeKM6eRf13fxQi7gWbSFmXPYnM5m+2/4yMjbW3gOOj4baEzLcvwGeOq0AeN9RSaxWCSLNdqgCWgUydLU7v0cioCfNBftt+OXvSI0W5mhqbBkbbcNw6y7dPKNhVZkIlGG0ASmSb5b5QOYIAGcBdwz8jVffxarQoUNrZ8gbd9Yncx8Z1Xbhzp/KtKxRt4wvxBGu5DErATIuL1FWRw6kXQAPPunn1917u29xUK128QBS78X38D6Bol/oKPybyZsu9aKdeufOt97Gb+33o9T+0p63ud8CQAHRRMwXRBzb63yDvesz3O89cNV8/81g44AnDCg9QD2ANmAsncXmnJKHyAyngb2CJ50jmXwMhSofjyaTbPpBJ0XPaloHPAHl/y+SRCrLsBiNcWHGDZD3cUfQ1r/86GL+AaIH9czSIf+/OFm7dJruEPhSOy70mti2y7ryu+eMwpuIOtpAv2pWDhMUK28gt1SqxPwRcQY/+dyj6agHZVfU1LWDvkNl18a8YmVrOGBzkJXkgSrMP4V//+8U35jj8ch8+ADvg48I7DUQjclm35q3/4AFiAMuDp4W476QYgkzkgiVGzYJHZMEguhBzgKd/6PU7KpROZuC/sk7shUvvIvJdRbEG1ssg2pIVChXV01x6pTxF97M9dgcccnBDNp8Oa7LbdrNtVqbKTAey9ZruXX5/nJ2AogjLrx6rRPYi5zA/eCoOmpxHzJ5MTkJW1Sxf+WkuAxZeeR9zX02lkGViW4wJ7uPHRlX24knAQgAH8BZMmMDLIX3GhNazOYU1J7mkEJ4CBlDTaH350pw0KSMULNoPRPxiHB77QSuUn58pH6QoCrqrndBa6By7qBwKn28VTSN1x5p5thg8cfwPFoxuNgd3Pb599qiyTDJ8xzsJ7qKhGKyaOOT4RPI8axJfu3/QHe9MP/T07tJchofbnKLCl2FMYfc4X2DFsmkrQbEgNRfXwrtru0jR3x0k2j/AyCYd7YUyLZiM1PwkAzf6Hr2/WMOBT+7fCVTR/fOQDsydOScNQJs2tNzhEAkKVxY2qefCdn+eDLFzu44LarUw5Q0PycYqePDUPm2VFwGhaP2Lt0xXLFEEhxTGksNHbRj8PACvU5OjOO84reUq9KMiNbf0nOg2IYIQxfrKs7q3onu8BVPg1BjoJ+MJpRAT23xETLOSIPo6FIFhJgWSfck7XzjiPnFGb0DGqZ40jZwvSifML1r483bj94nft9qk5QnjxJ6k5UnjxS/PNNC7QB7SjnI4mQAoKkDCYyCX91ic0eksKe3mwDU1FGM4NwBbIyseJukI2CdMhv1lpYnomu4pBc7IXha1XXetlRau+WbRXRyNbUSXtx2kNWXuy39N47+l8q+fbCF6Cz10cA0gZWd5gJRUMyTsvlXXFs19uN3RuXOzcVDckNzdu56aaVu41QGhdUBNhZI1EsaGqMBHXBzU6W957cky0Lss7++C2/MRrbAPtssF3M0YH1TG5mYF8YZ82/pp7Ssfn0aPaGglBFSKACQ0h3Zkfa0L3dUyfINIX4X0vAERtXh/bvrRYqYTc+xVxMnJFU9i/XRKj64rD1lvYonisSP651KVNdpayHhfC181SXN+cWXl5rv9FyXqs2KTTHVccYWwcNmakAE0QaMvx/lw22O4ewdetr3pTk1J4oUTeHQz4waudAIBh1QxExJvJ1+LJp5YVROxSrHwOh6FooHk8uVhFM1bLlPbpJgJVU/vssyYwXpNqarWMCYX/nh4+tqa2md2kjID2aTWck/1azasA+ct0mi7US/hVaZlUhPCkeJkLKxeq42ssO7N+/0UNMzMVannHVweE4Tc58bkc068xGE0mEVeysQaFg8PDr+LqBZPjiFaql/+ranZFwnkmJ2g8WnlKEvr1RvvywPfexVFTweEcXx0Yhd+UqZqc4sk1c9Va7fd5lo01TOqok885D4KHBvcIK4QOvYEwNekByKz4S3o/QJaymADRSazKFwD0FDIcpodMX370QTmb/mF2E/oluZ9+LtL0q7LcfM32oLoVCahLHISJ7lisg8Lgt3NpMxrbEeQSLTjBUU679ltNyUhNO+d+Ol0oBwv71uEM3K9eqmu99lqkJC+ow1xzE3VrNUlbN6rRcYSpSOMCTXC5nv/FfExR8yf24iCJ/pckFzUxafgnUIc7krZe9Mw7fDE5YrNCFOjzsuGfZCLC4LC7tGCqJ/JgZP7ufrYfnbyXC9KfRWNzTYZOyXtaCxtutzpOkxqHWRoPu8KOoNbm9cj1yME7w/brb4ZBP+0oVlx2fcWz2FmqkPSteL7FgpnMQQtLKPWIklLJHMA2Xty5mlRBzncktCsJ+/UWCwwJO+vaHKCgNYh4sReGS7m4gpSMpkk5/P4Q7Z6VO+aJl/tM6aWTrIOBUYQDOM6cuzxxWabE92xPuzvVWu7UhQhqvILdetu2CZfM0IgI9c5yK+WGf/1rE463XBUZqHeSr7dmxlmJXTf2SK77fFqbX9KQugr0WUOYXwtS7lD3l/dOfJ3jXhgwaYMifsneWhmTFcERL3b9IzhUUhDYbCuOgzaCCkWoK17f5c2Cwp9JaCwJ+9FF5eX3Z9iR6ibuYXHUq9S1lEGznGFVnZOqROzx+IyMQNMkq9ROJqp1sJe2DeTEtMaViewj02/eudhYW63HMW0ch5U6mD+ZaeXqK2uNxcww8Pp1E44biwVrQf8VAbMMHiyOGdTll5eR2YheEH+h+8z+sy/1RaMi7BaXxFxX9Mca/7pH4r0xdRsO/Oh9Pf3/mD01pwVQGMjqIqGfC8zvrQI98Q3j3rAS7avVG76kDtfeKtITXzm+2qtM+/I/iA1jQa2Kay98oysP4D6U0GwmC7DMZHVuvLXAvBmP6ocakGaasKjLL06tqLviKTKXvMaK95Llmk19qAI+gzsz8tRURueJr+25KGPcHj4UaXaUx8Sy+5jIonap1FbxSoZPVY8vgulw34z0TjknfQYzJnG3ctrnNU0XcTgOrYneexfct0YyXUCG21veu/6VsPrcGvgK9kDylfFesIw1lLBeUggnm23FEa648AcLyY/aYV5Bc8vq0XkwFfa7icPjM/6lXoSmFnYC8zwFhNfPe+Ob5S+3BudLDbYNWxqlSdz3CY0dnfSeGA1YVkqu2gbyqX5K86GSoWe8ce0TKPGkD+K9tnb8H0N+2myUj4/BEATKatFldEn/v5JQanF0i0hLSyf8T7fG7J4Kn1cLpVLnMNz++IIvhb4q7sE3brAdcxE9Tve9df1Ka8KYzeLTmO+KvnD1N5rc0zF1/cKbPG07eQogYKybvDh6e2PX/sv1QagoZglcc3OB4Ysgkkzr0Ucvb8i3iT9k/tPogV/Q1xgGXCpBI+ZdVpILiOIDqDs6d20/eQXOq7qxnt37lFIvhDdWnLCLHbPYRWLf3rcnf/0/wd/uLoGLRDXYHYbiyJnoMVR7mlgZ3SGAi0Usq6AIJp9tCSehRCKaqr300tHFGwos3g8/NdX1Per/KAoMIGiAzJBnNxA4rJrtc+V3E1egauW+8Jf7Al0QLjY/buVDc46rRN7etyP9i2cjv95VBBtWhVmmKJYyJtM7VfEZ3vncaQvgVgvHKtmaCwaO+PD95tXmZcmq+9c6AzZYA6s+eR4AnWKLEii1a55QIS9l8k+ur1eyspkaSFjdDTezhWpl/9vgNSTmEuOL1udpnv9xmz6vj58TiWSRdyPpcihbQJzD6XRctGvfaKDwhg34Gi43EKy141OyFkBHW1wUwvUOlo0d1Gjk1XQgqdRyUlURqhxfqR25pJ+GDN1E2171FvkB3Jjjwv1SLFTq9349uNDpW7WIgywSo2d3IrpyjzNQbVhAWqramb7M4mezmrDlwCVgLLZniQr5/CFKswmlRRKq5ZPWztieTQW098qkQqzHaCsNZCKpVHUoW60X4DRNrSQhhH5pzA7pSU6SdtB6nqSorxX6ljx/A41H9qJZEXFyG/NS2w9JHesVw9/bgI/hCgNSrqUlJXG0TWliJZadtZO4M7xrKh2JMapSaClCQ+IlKTRjM0JGb6En3ghnbjVHKQ3aoimmu1T6tXV1pPppUHISbo+lqKhIoXpNqwyBfNtu8UO/Ju55bwqcge015NMRPBKjpKbikcRaZf9l486pvWC8UCjGWJdO4VqII8JFG94QB/Vad0fWfvJvvb8mTG5du/TKXysAVlorV33yUQA9tjCB+oasjzVYYB9Q1p7QVhuwieUEOYb2um2dPtD81tM+vKW4yQFyqqJmmes/iJAnl9b1lXsiDhmLGME8mAJ5oJxwOhxvDYDEzklw4Ib6UG+qEocefixRUUjHjOqlshGjeVjiMO4V+yMMKw+/a7Kmro9xE/dGLmso5LKPh5fGA1F6GCoFHHBsm/YwQ4EHgpGhTcjD2hv3D7xl+vQqi6E4I090tyHQM2PblXdzFZvlycv6bkitXW31NnmodBgWvgzQihpUtC38ZN557ZtEMrgn9N7fPvnOuk2QqiD0wZXiQE0PnJ5R77rxoXeHUpngvN9Ry7GZmbOvNwTRb0PHXoD6x5nyzHBG6J9Awd8Av5eeQSonuXhEklesa+fBkOoqgHXzJlw7ZwZBxy2CIanFakxyw7KGZG9THikdbnu34dDxViETiz6jtrZs+TrUESMclxb+BjihWrKgQgtQMV52P1opAdfAfmqrc/83Sjfi2xNDWfQBNXl96dwi7qjA24Eb4LU1Vo+IsYHpjDR7H5p2gcLluQNRGtHdbfg7dQ2UreecizzuxqimQPXYE9C91nohXkG36QuSbHbstn0hfQDjfv+qut2NZsbty3ROan0omFrvZD4un/HOO9ldu0c4r3tRFPODBKhd799vi5Db7VWi7DfB2ZortLXX299lsNWzFWvblp6xmNlpcexRV2179g3UEnc2mQz7Q3Va7iyvPKsFx1rT3T5rmg9JXndpW8utSRPsDzFQusSvr4rqNO8VNHaoqlLi5xxoQuvKdL1uhs16Xabr2XmDaKuq+v/+OqrGnFouy35TFZ90jr1hBkBjuou2pvl20esqbhbcQgzkAlmwNaE/j97wPYEfv6ysEwUe7PZy/IG8M34yOA4gZeT9mz5mAkYkKzP4Q6+OG8+eotCHpCf6bycsLD/I8vhipmyDfSVuQHrZ+l/CUg+YgD0bWK7AYn4zvTKNObe32jfX8wiVkAV05IaRv4//mlDFvrVXnPlrVUCE1GYRPC4rHfE6qkCiPyNDBDiiEzBB0Jm4HQz9oHcTnfRJg1PRO6RO7zCjBaR3mqkzeo/spN8WRHMv64BjzkgMecEYfzRoZBla3B8+C0sU+7oikYpjEPf9udLVNRTgIg4HbRAPgrmtBcu2a9lAQJardnWwzae1BaXzZS+dFqy/gH24ETyulZYglORKaG0f2GsTXAAM14PLbDNLHwPLtMGFhXI6k+SGLGCS79By6xgSd9QfzfBdD1ZyDJGwq7yh3R+FviySMbS9LO/x3XdTGIjvJi5+N1+Pso2GUGH1NUS2SJtm9139gjaQzJdV2fTU+1a7cV2w6UbnD0ugwe7ZbLQm4YwoKoU65RHrDCHV9VIjdNc9KpeJh00qu2frh1+WcskAelpWDR48jVacxEcZc3F10O810gwxZWuwRtddRS7QF+eLqnRS9WblTlSrioq+5CWEq7mWR5bit101glHQ7HKQVPDiMy0jUow+grEmII0cmG37zsh/hmTC4n3hrWdSi/aKdU1gV2RelnLu9WjFfVaMJCaO5uaiwF8EqkdQfQqL/PQXS0AiqswgQf3pHtAEBDsgOA2EjELCUKB3hxkQ3MX4fLDih8F01P4G/B6ZNHspo9zVgJecE+dq/ekzpSf3AysfaCrc+P1vbTR+Y0AGCoB0EZkeCLXurBZfP3TEs6ZSfzGt+/T3twt76M3OEfEI1bG2PbUv+V0mdbkVEKQg/j21Qo34KPF/pTUT24SleyTH3OJB/BkDq6fxPjWHxOX336a7AYGJSvDSwbf6sF3TPiCHAMj4wbofrDoALgMZh/2/PtU3oT9Qhex/R8Q2TTcx+tzN9Pf7mKApGIPwCiKygfARtz5wuouhb8Qb8UDl/pRsidYMZ7WBMbM+Ff2WvJSuFDz9Z+luRpkFP8p4WIC65/nxT/zwj+Uv3zwsdvTggB48CR+kCnDIRIQCHLGa4AO5P7ni+icu5NfPLQLRAjJvAKGuF4sNkpKUUUHqZz/246cKv/WVHyp6wAFeQOUNKBncY+FtNV4fof3/2b71lfev/78EhGmGlQNoZ6KmpGQwmCrt//7uXLyveALsshnECnDeBxkjIi+l/vJzM83femSgCx84AxbJlwIoOBvOocat1e8iX/1Iw/VA+k0DsAoQg6GoAil1N6rOZkYF7//Z0fN1oEpZ3wfCN8u/8wIdgCX0HAfM4eaQDak6OVLLmWhQ8J8g6v3L2wYLSVhzabrjJUuPR50+7nL6+B37+DNb4+Z81h67YB5DXvQX3qaNxqWlZ8icP4uO+1z81NRTnVcjt7+/7SDm/ThQUmpQ91afSfEzTF1SmEeFP5cwTvqTU080X40dOLIFuT8F5EWtA2Imlo4I2wRZmTe/0TztC7dmr/rk7QBKs5kJuG/mYFd+zDyY30nVJDuguQVqI/Bp5nOBcUPEowzb//qk2+qtmUp5PB5yWdHYtJz5gbETQW5f7Tch0q17YKKR9e6M7uOGppjyxVlVomCAEThurLyDeO5+mOBpBSdE70Reachumt+7Df6hY1oRQx3fX7NQbipkTcg5PB702P00yb+7prIlfo/FRxd0l0CUomk/Hh4cHY19cT0B1VzyrJAcakc0ppX6WaLscZkkrl4H43Cue9FzgXjFZDZbRQquFSbfcqUL5UZ3wXAEHuuEBt5jU6aS0RxTJjCjS5gDpApSrTuKrHR9BGbnTWBmQt/368OD6Vb/Czz5I1wDBViHxax5efiPCUjeAzY2Qn8zeVTKszAXTb2rdB/7v/m1+jsMGf9Gcmsxm9LUgY7Ru1d6/RJ+K3wRqEq+kH2TNx6R10pEozRqAR1ILIbeGJKUhBYrOomLhQYhOSQ0pDHgjxXVdFAyG1taLTRM5cbtBsl4ygS5Xx64ts4/xXJNQEJiA7tBM9YHe7Qnu7WmrPFVrFVPtHnM8Cx1iW9qEBqlrMXc3WuPPFD6sNkKDgoWnRdB9s60sfWGeDPUERUbDY8kN6EwQXpbPhHNre+4c5s9ODyvq8me3O23UfNsbq8QiKbRCTUbc2dhKqb6qGFDMD1dfkij3x5mVjWk3DQBMtVMLRpE+awc9izkoiRrutLVkIHnJmpOhwVX63CZB7F6AC6N92IeDwSbHPHHA1b7U9OgEWYW14jRJ+Cs2V7zS3kc4ltlB86UNWioqLexZi+gjfGipNa/ddKWZsdk9lTiZU3P5w+U/5N8Tk1vg/1cbrZawTkEbLOarzWyb9ucQ91iMMzzrdE3N48gbhsJY+DfW/Cx0QstgLqjq8DDzdIo4324t/bokEO6BBz0mKs6ra/0+VXG1nhY8DczGwwazREBuyzWfPgMNaO0RDGykn3nFe+zygjrRs0xsU0Rqc3z6fDpowh8/YInyCQ04ff92v2G5m8Opx0n8Igi9SvNXFMQdk2Iz1uxUum6sTwti2eYFzqRfDvxSDRdaQBY00uVCREJkQfgLtzDHWJOpJ2HRsd5s9I7EI5EcD1EJnVHsplsKzvjyOPe6wbacMSXcJwZckp9qjiKlTK4PxRDrz7zeXUvXF4b7MKhkP872WpGw3cEnxJHyYxp6R4hHjd8SWIyicSHvDqrw0ISpeFYJITEcgFAqqo51mpOrnqVNM7dxMmk/tzxaDKRVMRYAmPJsDdo2BvmiOBQ1bMXog5DgTlL0PlC3Q62NUWiUg5/mSFeNYmWSg1FxGgnHzcllnXReeWXMbe1iIJOMPXAiVeTxcq+C+a2N/rtK/aXP2jomHH4MCew0GS0i1qjpTdBuF9rnjaxQR4q6yltwE977KTSKYRkxR8I96ssRcr7InKjP5tdzZdbkttkoP2rz59FbfIw5OZyviOosxU/9Ww+ly+ihmNaPbfYoBomi/M4kERFKzG/RaWiMPpxl/UgCt7DgUGUatJbVBtOYJPteNJ4wTZnXERBk6kD/kiKTMsTnRbvtq4kwvtKP8kXd2P4WC3zgcC1/JrDaU20WAH39Ny/qpHirnm00xFXxfImSJLOiS3Gn2VRlpWjC9OuPbgxoAqnSOd5vR5M61ii1zVfd7kdQjPBorRdPA4xBwLgrWf9IBgZdYxV5NBw1O8UirAAGpCEtZDA79Vf8wEjkINlZYggZFwIjB2kzGnUdH3M1vYxSVf5sSDDUJRa+6HXyzB49ClJjyyelXPXYczfXa3XM9ACdzbawqKqJIlinonMqlo9eafOhERPWpKizMugj2yD6Vw+ssEpMPHDBH5/IPhhocCYjftgltnr8zPfsL/QQContST43MZnj4prvCbFXHgRxd8GFmjTkUGc6w8u4u2eJj4FnBZtlGrAGC4d6mC1AZL/bnn5T5d+OX0BZcsL488tADPIGq9T50Fn0PiAvEi0O6jq1iX7eHBeuNUB6fu49Cko3PNVfS0nvJztRqE4QgabBKyJgwF7McQyvL3GOX0CTH+A6eCEAxQ+ETjO9jeRiOdtCo9a69hzuLO5qWOSzDWu00eR6U/mEot8wqov8/sBdEfHiWHCzKWt1Rc6Oo4cmlp/IABaL0oCSgJkKHeKOWDv82xPwxVY/3C/eQwtgK8Q+94b6pAU8AcDToP1TUe6w/oUK0C+4w80/NBE5yTbDmrh8Ux3AJlI2pijOYFjy1e8jhKKu48Wcslobj6YUVveYPBIioC5ZMS95DEIC0QPCtXZhs9m0vJIxGNEjmyunxV5OJyrDUVZCDIM+67WNXjs+nf6C77+j2bfPbjkA+PUlva1bXt79uHStePzBzfKm/XG1pVxER2096WopCIWButVO8kwo3M9uz50HvL+aIid8Af2xa8V1doIolrojKei7MeGLvRkMu3xYqmSQfuJ0/ORSH67KprrbJIRpR5aENJx/v5gpJosd3aw3wIeQVyUz5g4IaCQtpvC7PbwAjjDMa/LQkD0mVRTO+01G0ooXPfSoRxO0gAWBpaIbBbAxhxjyKYEqjJuaP9Z5FzRkTaISMFtRVZG05Z2/4jC5c2rHo8dTOZWTwWDNwki49KD87c8LleQb2E3QzMUarI6pm3bVjeXDAYCUaqoI8EdTWhemwFDAVHcsizJ2WAollb6ne28kaJp6I0AHTxHdBBKdzrVNk43o+kCKKkpSyEztsYkzTGzEbJmxrqzWUnc9gNVPCgdTCHOCE+I/SIluK1YYa4c+dzUfoRQFcDm624iyPX7nyBzsJGKACnc+mcad8/uljr9UUbiOU4tT0R9dtt7wdOoPmmaDq1MZEHpJ9DNdsNDhAgM6S0Fjv29z4kxGte+0WYkg1Df6iK6kDmaulc3OU0E76Cn/32vxj16G9J0NpzqZDwehpwOZ1KhH7KygYcDeHqourhYsHkN6VkFgMsk0AWBYzqV1VHItqD/WFyYaDY6GI/PThGwhZPhX+l99WOQZ5tOfJpY18804KPmU/NPOnBoniTNGhojwa+eoJNf6oAADAE9qYSXoxeNpvDOGks4HtDIuZGA9sliLwqThvh2dsEIfHytmQbD6RUZ7wjN4SihGd/FIt/erbweLz+zgl9XDZW93Pv+VqdLHgNfFATf3ERqayn10VrtQtsX3+IiGIOPf+YQAREAZWRmxKtXG9YIgU8TxWTycA9FEnQIGwGD4KlQSnHXUkQ0s4lEozdfcgxLQx8c+dqFbY1dqfQiGAGcH7nD9uuh541SAgftw//Zpzn1Ymbolte4nCGxND5UR2IU0xeLJ1OioUfqsmF7SXoXPv6hHJb0zPbZiiTjYAzQ4XQTbZHI1bqJCXDh3GC71WciSN7pej9ZIOg6hFIl6IAV8Sf7rr1PvTaF6gNb/iho14m3fWJQP/3IvS+CzXhh46Xn+G3/gek86ANs5Q177z1yG0jt9FkQcL7+Il8xSJf7b6HNdk83PKOmUQNcq2CuOuHZmkOHmioQ/iS+G9858g6/QGfNM3R4RraBztg6fywCd6ja/8EHA3408YRve99BAPfn2DkoK7YzS2LSJiTEthN8pZfA7VOqVZwus7yKOoxMINqRFhxKchGsvutpVa5LFak3xwNbWRQ/vg4AE/24ECwUHy1UI0QZE/BxOWVdmle9vtj7Ucr5Gol2TUtgBMYWg32+VE7KE1BNk6HEK2w343RcuIVn6aGJEXj4soFC0vELIsLG0uZ2QWWJxKkymy80WbctU9XG0pv8luEm2gyeBS2oe4SYORJBm5jeZes6QqmDxVgMO6PkTJJPqmygSwCltm686TiaagHNLq2kLMuXqo88EnjSrwf1qS5mYuYhTdabcRqF54TVBtBUhps/3LoVWC6rqA9G8EgYmfpsdQ77m2oNaFqPtHNPQrQQ7n7tVTdvOZEOVGVcAmq+EckuBXkIIjckt+c2gwlINCUVc1WZ3m3zwwLgo9XGs5/iohGQxuVaTFh+3IMEWEE9xyEEUTGVui0U8GFmZKtO4+XokXxfcR39HjMwxDwWz0oVIcSyzyAVIjSveppRwRVqfhrvo8mHoMZmpF8DwzCHuVnunRZkmHW0tek+Yzo7PyV57EjjiwM+jgqlo7+g5zR20SdwGI/eX7gfGcAN4iNGGxAwCO4CbV/kX8+5Uum9JfUzJcuiTm60Z/RZeSmHAtuVNF0Qlf+TxECn+HizUju6H9VjBIJsaszlAp35PIw+nAc7RXHBcdI61wnIL/rHDDOW1/pVJoeNi7Zkzz59hiQBXzRIcxuG8P1HR1J2XXBv4dj4O/f0Xh0YhQdKPs0I2sHJfQUa3O4g07G9E3SztbJazLYBWLA7I+GN8kJ1HI9aUI5XvR4KHIGzfl43IEkltsxxywmtxUanNm5ZAQ2pjvUDS5vVJYXXoHtgxYrFs/ErjiGxaGPtlDrZ2mWyO6B+cQG1gh91eT2oGksNfkh3DMXa49hV4zUjYBSng3SxL9JGw7n0TdHumHdLGPBr7HEntykOSQArVGX+3LzbHeUtF6yU0apYraraj7sQvkCujkhdANcTt/HoKDbHkWQk0OCfY5Sep02oHkzQMIhM8p4VNnMTL/ABCP1vZuwf7QR6XBAIUxPKuiKSADv+qhMVQPWx26hzE2Ug9GTruhm/7UkeEKspbKNlznTJYMQ4w1ZhM0qeOj9z1rox9WHERpJsH4dBmwAoxEDnoxdZ6UvHiPAEjCEBU7q+I01XFCIgWXENwRcrDL1y51l43XMAffHJNb8HTQWJsJdlFpJ5ltIxr3FdqwQgjLh1j2cAqTjOKlkBLskOfC7dkf+q/535xdiFgRL8xokbWml02uzbIPByflGWJ879ELo1uwW9YCKRvxklf//1dJ5jSCIZDQbUB6NJgmS4fBqIZHrgzguHWPZQCIW/GLsw+BR+I2KdeHQuCwJL1cUsXWiYj8JmXYUMIyOjUbfcp2UlZp033S/O/UykbjNd46VytVyo05ST+SmX4KriyrZ4NBqL+K7itvPTYCxUGNLv3IuCcXBN0l0VvTVy9lprSGt2XJpVXlOMExwt4Qn1+Tm/u6HosvnN1z2hQQyU/VZX7Hsu2X9xLr2kFQonXCWqFl5dg28BCjZik0wJqUh8Z8A71mj3gj0ldBGX5wvRsH3q9sTbqKq8Go5b54cIE5899oluKPBmOHrOvOCep3JMD5K0IdiHDiOEAE5iavslXSLGJqDb/oPEb753nM6AHoUe/5s1t+Grdmc+hJwScgh2ssTzSHGGnaHbfTsNnmZa3+3Zsw89i84zzuiT/P034MS8vlqfvGVC8d8NAaYddbsXFvYOiCF6/jpzUR4EVuoU53lT3ZPPs5ciG90O0ralLlUVF7LZ1oxupww4Y35/Kyaq5q8FiBw60hGI2mHQ63ZIXi+VdBabtsbEUnlVFQWWFSTlFNJBoiBdRyF+tzJIGJgmygM9yM7Fvnpkymbb6z7OkRLohkLBCeBoXTMkR/pzdrnsm/9wcL5HgIiKSBLrfj0fBAKd2rQBr9ygyQSX27Sfmww1O6wWFuRNMtUwiOfm+4UwQk6eX/ReXO4Gy9sR3LMh1SMIF67W9+eGze8olS/tBWIkgAIwRouPjBESkkya7W+Hi/7I3W/bv2jY785j4XX8jTtygq9eQpcgwB0t9AAfpO8vbYn7xuEn3yznOfL3bp9PjU44nvcqKB6M2jc9/nhdTTf5FXtAbJqr8P6uOOyDTt2ROonrOQNU268Vq1EfhxqUZo52VW2tEds7xlqhISXc6YhBqmgqgtUoZaXolF5BrMgt9K1+jecDAZ/vl+bY43WmCo2kzPu5Qh/9rcjeeHr3CqigNbNdhRVPhTTWWMrlfturBjQa9MUbQI7G1hDdatTrLZ7KR7zpDCzXdMVrNC0rc5LY4euqjk+XIgpj5QiFSwgdgUChP5Zks3dcfcDnlB7l8mnrm+X1vkeqvuZuRi7zQ0icHYjV8oWQz+0OP2uQqzZ/qP0XBw2HRrAOucyELTQlaLEpqbH0j/TztygmI94x6Adw+DHRR4QHQskI3VkwJA7XmYbzSJ3KGcvg2HHZgiiyssQkFy8y7cVDuxeEA/1eNeD3Jd8dlNeUftiYWqA4Tn+J+10L9OFaqtGpmaPuCIJnn+AXy7dIsAnWgX+STK9ZGlCe5rDFWfFq4Cf66LGZH3f8d8DC3QpUOXOJiNx5c0cF7IHECM7hWm4owbZcezT6QaPe0csXtuJuZ37ZEDFkuktNHg/rUyQhLzHuCtSiprRt26JFZh3Vt0TLLeITNo6emyJBBBLjBGSJ6kQHy4PnLwwa3cBOI5pWuijQW/OkjPu1Kvag63lk+Th7IRg/Bgjo6CPiAnqvWZ8dvctMEHqSmI4LREDwnKVbphH4DvuDgIjKSrWyNrJoU6sVS7WfLwVOzcRf7NeMqIOf3qy4BpZek0Xl3oih84KNckaQf9h0H5sMv9yPN2bK3dJcq5qwD1wqtZTeVqlUTDEioTAJwj0QCyavXDYg3+oas+QtOJgBaKzBcwUHeJFf5r6WdEclG+rKFS05yWMorpSUOQ+fbvmtvaR5cnvWJIo6z2XDv/tLRvmeU4BKlH5UzLd+0T1fd8e2rRAzqfRcc16AgAxMQ2tisYXQbswFwlDOMmJF2TVcYbOAOMOsIhc25JSqCVWTC11WIfca142mvqCwjAIfz/4ICwi/GP+8cQnGKjn4BmyEiUJZKVaq9UaXtWYlJ5ZU1/GpqN29c/aeeqvtbT7PcpLWsmaLtCpZjv3WHHlsynpUXAkDka45O+fKkqpWDaXHqFaLGb6QWJjoROIT3BJnvvWGEYfbRk6OobFSh2l30PuZZ0CveD0X0VZXDKGmgEdfYKNGyDS+6K7AXpo6OYVdGCibFI8hT0krAx6l1PYlz2LTU/k8ZbNn3nWRhQoFNIssQMXjDO80j5bIYa5jfrV+Vl2tJsLeDDeSrGHBOIQ9UBCTObxc0aCEXs7wT/jOTgdfgtioBAa26XzFpqgF03n0B+lT0+EeaLKKtw/eBWq2lHa9XirIi5lBjRsz3mt8ZdAq6XkKK1zsCg9ypXsW11fVgTCLW+xaDWJc7HsJjTmmEKKlmtjLeSxgSgIyXu5Iqs505JEylmYKuICwrVy3+3gazkvgLAdS6wTnFmot3tAB5GA2J8jZKukfMtwNG7l/K9wQZQmY4RCtb3fRACgahOildbjuEtn5rlMZ2QoGsQ0HqcS/rU3sgPbeBQXPItE3AuhlrqZSZ6vaA7+aNZtvlKJ4yClRhCqQ6RSRUnf30cPV4PZ8wGoFwwiRtFQ2FNSgw5MN5ywtguFkKJFyXp5Bp96S+aXji8lDBZ+cpcwFE2U+HzNOR3LGiMdAZPzJGrkjkoTnxGAWgCpqFc+/f3Ss7jym3l3X2Slvcy+ojIKDz4IV2b762LsTs+OiKDdF+Tg50/DXOaSbqvE/hnNCQLdIJ0OUXdc0178kqFjCCtW3jgPeW4/NbLcBSztU0U4SRxWene9HqoaP4fkQEMJc+U4vU+vczgsPFkhGeBTeudb1PKLvskCkHvjnbK/5JL7oP3L0/94GiGEf8Y/fr488efADIH0uFoAAG470Vk1BWrOqxMM+VqxU+iNl0poQVOI7xFBcKhIMHW2gpVLc5rrkve7lMaq1jtSaUuxicqdxQwXyYHd9eorQ8n/stbsdqzKBrmXGcXY02oEmTCazbFlK8iHIR8bbop/epnwOvZzc6gvnCIkrYtptoWaj8w5niLjoiZTXuIOlzWqwYxeSs/r4lvAq8n60A87C3PodYpzekua877CmFdA1q2czkWWbGgXvA+fLwhs9K0e9yynj1Qdip+q7B0ZEd1txATpOGmsOdrpkEmD90QToQO2pCfaI6ayATkdFhzYwYD9f2EIYeGMcJr8ahysPKFqsJ5HuK/ggtLRa5XiiGRKr/6a8XgFYAikiLYjnAOQQ0qD+iTm/+UnppP/9vgtXLGyYIKCNxWIfjAAITQD3F0HSgPPsrfzlKnZWN7uJUcAPx6bFUvn0tEBuLxHI0NmKAWEocfGZrbZ52ef1+QJOz4pXoVhyDxjAwyIhAjbKgdq3fZfRO8aB3WdXfTf/bwm5Dkv41FAx3xWPU9T9AYCvU2a14kHrGXKaZRaU/yn067ZuEhQ92gz+HNaxhsOCaN5Kr7zzcE39JJuwLqVjK6sLCxGZbMndNmQZRYAf0zR45QcfQ9wz36wsOewfeahUrFX/MKScdC1xIw1KKunWgL6omTpyqafRMRoyarGGRPTM4N+uA6EnhfIEUMu9i55w/LhiZGTEmt9PYr8B/wFjRVl7To1KzKXdo2SobD5v2jooYmecjrJthNNYUAR2fPv9A49BdpGr94+0VDJbPTC20JxBQwEwK5b6g3KjCVvHwxcdqKTSqsXuq38JE1yuiHaP1jx1YhMQuoxAHIQUMG26UNS4YWZ6SpZeck+5thM1PA/L9hX4RT16E1SM7rxuAqQ000g8lBgUjcfQblA26PcelyTJcN9zhziQXGrb5bRoS5NkqpRUMolrwY9Xu6V7HaeUwYfbeQXApULuVHHnurkhYL8o8kgqwxaSy71ep/NWcQh2NWQ2UCDkFPl27r3aA5kksLldcEI5O6UsxnzeUMtybdLs8NO+X1u2BpTuMItjl+HsDGAA6fAjzICFH37mqBto3A9Af9PcKAd2gPDQkVSaNI+J3ONvFZbjvNfexhoZDhU5z4w38VsjFyYS50XEMM4m5DroBfoj6zkV9no0RUNBID0OpYGrDUIh8vyw9YqsnUNGLXjGUS0SuoCRuNY0gnNPXhKZH4JWWV5KKKjSKFcB0Y9btFcghheiNyjoqtAm5yfzX30HAcsBgttOxmr/ZTOACp+51dXNOJngFhFpx43soHatdjhXkHFDO42Kz0QNUEv11okp2trqozajICYxQ07XCO/f9i6/HkOawxJno9LMXes1xMl11ahxS6QuG4d7dAsJvLm9Y6Rn6+RU4aY/ECuaKlSZDlE85LhTnruRkgJOLpVueC4zwrmr8ttITlqqWbqhSEZD0w69Ci/VIx1Sa/NI9+/TXGFWXtVYNcBBe5bl7Ion/ltDJy56/8REWapTt0zxX6TrKMJI0edlXaO1QhtBlA/j+InpxSwGAkVLl27mlrtfLxe2mSRsWqxbfFgWHyq82+1dRWnUUEk0KMN9nhH25YFbXMFG1VZNUyS92mwOP7o1b1ZZonnYeQQOGv0U6nH47NAsuFqWTJP7JXMz76bE1kxCZwzn6jJ3MjGkx+o4TqCVWpJT2hMZ1qzn5sFHFAVXaYkF+Gw01+b2YyN9KE6CNIBnDOrkUIAA3GNYDpSnlBa3pDM0g8yW2ZliV9rlEiP06RyZEkgqalkqgS/wD/NJNsb/tKbOGnjJHoYCkyRuK5RiGGOs9/vNQj6PDHmhSrmazIse08mkR2j2RQu18uCW1hZsDG/BR/5leyU0xry71jvP0v0wpVQxRj09Mz4OnQQWrz8m2CsrYbZ7e+SeCvYeCvZBTj5QHtdDNzzx5xo/QRs/P/jvfxvxfTcO5EAu26Yf3SR4+Pkz4wo4mLxw0/5ycAciLqkvFNE92PMl+AdQvYhYKTxDPsp/OXZULEy3et+wlm+oR8TIFOnBF4CH4NtEcXBivYc4GlhBqW1YUfZ5O+5u+9WM5XEy4AcOJD5c85P7GPPoQ4/8T+byO/Cx9Wv8AtBDFwpMkvy8kzvvX/UdzIEU/NAt0gfKLQ9IaJoBJ1KO3e33H80CF69Yz5QWGYG+fNOtwpAs7bUIHHDkF5PhgmvAAM6AeLErRZVkmCNhkASxujyPuuEDGpS+/k4ZfgKfZx1PpYGHQ8eUyrlSu3yeYZFYJ+yc3G0hGwIrlcrFXJWkneSPwM7ZuLwppElVci5uPacGM5DNzY7RACFUOrtVOb6DAOj4CwW78p/sdnff+PDHRU9ZMskEm9+6AOX4FdhNeRJyhfGQ1eWyeCmOSsZ/QPyU1rWUNZ53xVdywDloZwO6IZs9NhKCcJM7dB2fwaUTvS+cEssUKA9/Fb4OVPIgNVHK0sqlca7BBqO5+zVzyhq5N024hy15x/RPrF3Mo1by4MxdBMvA1aOMe7KCDnt/Qd0F4Vc4NAzc3fvSMTj/PRbQkAZ2o3ZCOUWIk8vG8uIYi6KGVMwRBt5tpRXiuEdqg99tqSkxag1D7SRYMSgr1TI/y9hfozu1X/MNkhSC6CIq+L8Pr179DI1P6PkSFZzAVwSf+ZMau3eFN9BE4Z2ev7bREI3GUWPxVrUPERZw6Z5HlpDKmjPTd66PHgfJjYOgDBCKNCuN+ekoahUABFIt68at1ZpG8sLFEZR3TPbXEWTc4MYNzvQs7GuVphDmQzEInjDHeuy6mhfCMXVzqGUj3Tbamgy+clFYKJXKoFkzMuXadXf/WhkQtsQ7Cbjv08OXp0sdms/5Kn0Xeeb6qDB0B3yK/amvwhx1e9Rz+JJxMq3RmzgdiGcl3uCqy2Y2XYutJ4QdNXgxGfSnGRSR1TP4qhqMAvBc7oRzyAtMf7JakS1Iq1ZL2Qa06Uac85BennrS5YIs47K0B0KJUq7hQ49t9UUJNegz5n1y3Q8G6qMPbtM+nXjsr/Um+aTI4g5vmc51BQN8Eif7l2tysj3Rkk4IaEnItde8sxPAS2CJ5kqHttVWLs10vbSzJ5PPJNNRfLSzIYsfCh2LpZgxLmAIWAgyJSJjpjuc0XrrOmpXYjFLBoaPUt0OYBIfkvSN9UUA2Qkvg5XpC7OkSbzfNN1R/x0f39okgFixd1zor2fLcsiosq5+RUwkxEf1CgAblsD+55h3PTa++CixRUa+w+vgycPiXPfvKmDB6v8PIvTbI8NjdwUp42w/Z3pTDf7YAjZAzweu+pRn9X0PavvQ/4TQF14L4mVuJ8clwKIGtePrE0c/u0flg/FNEugNs+F2F1ePvZMko6Zi22IdqtL753BSjfg/HPT9WBkLgA7+xVDEHM5VwrxmxiuhEvtdp6OKGtusJflTqn5k96owo0R+ggCStEiILH30fpcPS84DEzpO5YuVljrSLXssUZf+Gyjd7tarqhmoQTh/SdVvPhN27/A9E3KtClvfXHWquetb3fZB13Y9xprJEDanEloWHJjR8AumQNnhBKobNRRKlhpC92zzau3oeimnis6j1rnBWXpEvTNaWVXuvnq2SjE/A1eqdP+mA2Iz6D2lAKImKbAJu73Goo7PNyymQsrtm5j56ORHE0AOFrrRKCeVqhyLgYDUkNWZecbu2PDsW6y7wCZAwA8LzNXu59fxPWx66k7cdwFqJQwNJm3AOQIZwNq0/6Hwox+29DRBZpJhn2/HMeC+HMDMYBcV0b4ROTEKHzYaMrN52+YSMchhpnnAOfcb9zcKuQhhKDScsK9VZ2/JtUh3Cbra+UFNs9N7+dT4sONCx9L+kqecBPnmHG8yc6IRZFkl19VC1tb5jPXkfCJbyzEy99Xck41/lB9XxnzaNWTp+vpu6EoIQGHJ5d5T8B0kOEc5ziikYYtC61eLOz/eoov2+dq2ExydHfsS90gHyUJDWrN5d4vjpQzJSGaKMlq1J3cPkLgjQNM5As4SZcBCLX6Avuz/CQSC8KFWZOgnS4x1Mvn51V+z98jgMQAuQ3AsA7iKNkA7Or7oXrzr8dbd2Q/PexkMEG46BflCkqhxPeRsSeshANoJ8T+Be37lxdxXDZTYYju4KwtgTVQYqhMgp/lZkuQ8Av2ApF04mClt4SNI3v9cKGgO4Gb5Zt+1nG22Pebp7p3lf2Ze8P2DQk3zeQpA7E+1R6J+P5AafmOTZhZ8lxEqZ2dTEu65mrqB6dnDemrnzyGm9vdLlpzxOIFlmjLtaWjDvE/oo+Jcc5iZsIHg/sFbtA7ES8SHjIAQ6WHfcq3iSwBa7hiHl+GOw3eNhHNyDMMJPMMIksDBHZHgoWaheXUkvKmLAOnCl5c3Qu2hX1SG5J3XaQeUS/sOzPnzjXq15vu1WmO+6c/963e/gRfPX+v3jhuqAFHtt8hzi4Vys1ku6oHOEg4UL2jTnv+Bv5D6KEcqiNlo6DKmhRiuMWp8XQ3NGEKVSwFmpGY8v75lNy6tRJecmvEcJzmB5nqtZRo9WR91x/qWzmJzplk9q4OcNF+U0VPRFj0tIq8iKtFSp9tNmmKypGCwfhQkURvrv634LBEMqnAQchryxSoD1XUEJNUVxqKNgaDKoQb5MOHiAqFAsY+5h28HH+w4IrmeWKFSKcTcBt5pUj4LGBJC6kOM8qpLibLAUwVzGoSw1dDJYMPphGAtggdUbs1qZOr0+SctstWAS6nkYNUDwj0V92gHQ5M6u6ovRWhi2xrwWJX11U0vmEPPSyCwNmHHSXQ+Xzjs9UcKj9caIhv2O7GwwzJPL9JgE+hGR9kQ/tNssPRgYwBtmxW+kW3kNh1tdt9bs+JIS2TVbHEiygQSy9Q6Hba6ee0iDX8m6ErlaKvVvbsiuCEVvFuC6SfUqmOVcijEty4H3jpuHxgSLBZlNRbXMQ05SEJAdtkuv6kYGoslGomFY4WPCZos2/L+Beg1Za0MfiNmwf9hmobYAVqtRnGpdFceldoKz/4+hmKeh15P2B/PsCxJboitWuWCHqXrGCAhQ7fUo82H4K7g/qnDsw5dXPgHdHj9mU9JcOCH4r9M6Z/V8vCPEMo0Ep//5cJPNntBs4QANQhSs/gKCTncnkQeCo9Ej4IcCkVeIvye+x11mDU/Cb8EgMoYFLxe1OsHWqiMVKDYH7D4DTeCkk+bWD3mW+ePI/XYQ+74deZI/uZfSuATQuQs/mhMD6m8O4n4dp5KHYVJfirGB7euT/9HQWIA/wr+vIK/9v6weqzvsUkLuObp6W4pUGfWXluAEcGyi68D/4BmasQhCctndoMuTWy80NRT0ViJkbuArYkZyKvPoSMG6I+i0Oq4X6CSRSwg56Ty9W4phAv/WR3ALcH13/7SR9/ri56kqQyeCJ5h3/Y5OADhAv37/m6sz94/144KQIHc/Zyp8w75sQI2GT3/2BMdbR1y6WpmoOPfbfD5XPdKb2A4vAKCfpktcMPQxMPP3jx59Mj1TXBdvGEVaL8OAodRxE63yxPLn1dPZ9OZDDPLxg2Fn+yfcc06LxSNo9b1KHjnMmsxQMtf8fi01hwoiOpBGOodLuXbRvPksPlzxzrHVyiibuXntAHNS14QuW4YEN0GkmVJxpMdCvzCntsU3owAXVrSJ9BwFCiOuUbD+S49eKvp7qdGm8BCmUTC9NrIy165y8wsCC93Z/gdBEvZdTDzydrse8JbZ4lpu9NlkRDg9v+KDikU0lSdph2eT7yhH563ngCVYuw93DK/fnXwaCRUaCCZ25TX/iqd26nI4DCN0N1bwekmJ2j5HEm+B35Wyn0WgwB1vG/Dz7yy10cRGO71ZtcJGEh4xjN/0F62aRUBX09kWAyt2er80Lh020jdQ+H1+5O5OiJUIzZNmagpzFGr1dr1skesoPaoyzzWOvbJm/3VVzePAwS2cbVGLPQv64Jhmc+2G14n8tGA2xp1WRcdm1HwEg4ekHKGXrPB9qdZ8L1tbDAe14JydT174sKPUZkqpcZHjm2wD5op479sGPJc4I99Rp+h9RMw5TZfUzRrFef+8fv7JHxkIRvSkzFiSDlucjpds9bwI6OgBA7zrnA8nRldE8vXDKmRWrsIdLea85+ZrLYVyhc7Ctqv1lVSgnk1sOtGDIxUUdXwSqGCVudg/1dQjhh0vrXwHDFfzD5H5ZBBAWU8Izdeakx6NIddcEhgC5uhcpuAzarr+gtPFsPcKUeWrogARV2TrczlM+Vy+2EKzNvlQgU8y/vWBu7U6Gn2tfvwbcT2S/QbtH8bQMgC2BZcgl8A23Eu9upPtYfuV3+AmdM889mxDXcAFgGh7iAMGAzvnPVjk1sjjDiTVpSp8Ms64DvNOFP7BvKg8mG9G+2rdAsCeASWvyC+5VYbPThsP0PDd4Xfr6PJOB0J+4SUGCXgUdvsjXcWOyyqSHsZbwNtFCan+5zenE6C2gKWm9YuBLU3j+JYuG0l5JsCfaMw1KjIzPot68qlokfONI941B+Lf6Xa7TTLqVlL2G+k+afDsfWl6rlcJiJLbjPL0KopTCwck5I3mbZIggnAmgbuGijcPGrcf7XJ8+m9hoJgdahnTjjOTY+n0Wk0XPSHzyOQ9Qea5YGv7mCPzbXhr6uDPUnCHEgywV71b1NWwcd/9zfuQwNqjsPmYWJa6975x5BzneoPJFxHsR4ygASFhop+BoGF0HEpMmVkKvfen8HucPILNPsNcw1hTKaLlWKplxMzosese1hv5r+SGyYgaVpyDldnFEbzdjX7C84O3grcBz17kHrV4J/FkrVAcPsJHwe2kLiC3sVjwpoBfC9sD5PidwEREm78kgLY1EnRDzibMZWegUNttL+OLWIX6XTJ/9bzqXIxnwr7XVQUzO0ovf53yxcq6ofC0A24tKUl1yf8l+uNpdvx/voyCALP+pQIbhgh5z1MPsP6FN+4skqsTx8OgtH/NTL7RT09kY8VnD6ILUIUr/pef8amzirzJlF3soUU5q0xj5fb/3vsTlfhT3n9DmjvNgPM47fDt3lpY0sSKHV6HgV6VXD2kQsouIV1qpStHya7V1UFxYYvBV+n5KY1YUd/lk+NBkSvjW5DdWgZO5OKZwUqtJzYGb4G4hx9AN0Q/WjP7N6BHNItct6TUr17q1gojiagLGdyxYqm8OFc0vXXMZl9VaEHWmP1Pj9mju/cXSs0mg3mGBd/GtKrS5G5UCZTDnAN0pDUDvv9zrbMEDVwxhQcWAa9XL4Z3dSsJ3jT1aUnkKXCVrvb9Br8vPcZRfJmHkXDhYoOa/0Bet752oh95c/tBWAPH4fWpKWoF1B4xhXs1Ws6UzaSty/e4V8sOznurWjAMj8XJ9QEMKvlujledC2doEl3nAS7ufj0dHzDT79pN0i50Mtg53WLjb50Oidakcthj4mIxmw0D+SbUQCu0UxTl9vBpzNJrQ5TbVkpdnya9tsslsVU0GZw5xfReLM1qy0si8RTEm3tESlwnr7IFG/+wGdHDv9PNFlqCxdu1DlVqKHdrTdQvWokhB6uKuWrDSJbkEW/l9viSGQBXAdzlYmGQce09jCrynHf6yKZaZnb0cX4DC0aQrntNhqsCXFfiLBbycEFEOfQ42D7XLvr0m27EXrsKrWgf+yFBrj6hlEjdUthvZz9lD/KN+ihCl7i+Gwg+WS8p+1tfh3dz0IG+eJq6lk9RdWJRcHSM588e4zahVvn3A3BysVco/P088i3kSv39eOpq9432ZpaaTiglB4qe4ML0oXp8iS3gq2QqojWdb2JquHkhPt1SZUdDJdLkp+xEQxDoAGzhXwmThB8xWyBFK3bQZvAU7xnkEt16fm4N3rSFNygoDSHIFRYiGKKLYRstOotjs2kSN7nUqoNw7RrjqHqZqNiIqi0TDhdBpcA1dhqGs8BNxf0EZByR6qGmnMV0I2JZXG90WyhYq6h21DncC3Xz0ZyjXktb8kevaYBB9Ld7FfyO5dbZBnADSfdPmmf6g7/Pd075QGqhlk/fOYxx4v82gGX3Dnfp9cis0O/sTEK7ugJkzDdidFyIdD+MGpc/5yXvOQNH/5cJN3s5mZW+vMc/bv4vShdU6YXTKRmD2/bg7ryeYRkGEKVNDdkAz3SuQoSfixGT+mqiWHufmX/wTJmER/3L8Q9weedodsemBZGL780eMD5xD9GY3M+EK4Agcfv60rFXnMpqn3dw+l+Dga2N98b2ldTw/PE/MpB0wNzjIDGCuVPZPPx6Gx4raf3EXeTdDeyVAL3EpRUmxVXieVdZctblUaqW1mwIlnfMeIi0EE/yPYpUApDC1yjoimevcrkUguGxskHNY7v4rupvmbH4HW5GoO55kZuZo5dvOvpOfz1AdXzpYaSnZp/oAUfgkBtgCgYFKwYtq1f5+H/CW/OfchOTitzpMgjtbJ1/ju+3vtatrQ7CbjvseHl6fr+M3yWrH4N91YvAgWuF1JCQVAywlkztSmaboNyVFl43oPTLlMgBjMNJsnrQrEFkG2UJ2iu/3pnybB1BG1ly9suObsqLJDHJsPHiYsv0QEJ4pw13hG/om3/Kq8rlSlbnL2FML6jaxxCMLIXTzXNJpP19HmXRdC4bt4ezU3NRAfoUWXxpdr5X87H1xVBqKayGuNVcvl9NCrwdMyWarOKBxTyj4KABNrbpz3TpixilCqe5B4EBD1YhYYQGcXnwxUlglHTZOp0Or2oxO4NsegfqE2FiXdrkJsdXeMQwsjuH0Awm8z13+oTD5aj7lC+VNFosbpTfNXHi4AxgD+q+awZfus2nuNCqUSAt9BRgWVMk3jRJWD/7H31ZDGXwym4ejvsg3wU3e1FD93Sha7QgrmumsrE3IxQng2tGqW7ss1eEoZKm3jKZEq5Xzyrqvsd7r0Xr2Nhdq5WrVWPmYePN1qHLRbM+8qTdIVyewSjxhodi/1gD/rkTOyVASvRz+hT0c2Kt68BXXAn+ZDJ5HL5UxUmRaXG5ribrl8ATtyyZ4x+8LIz37AyH0hfWe5yvQjigAOGoiXOtC+izN3Vh8Jt4ztwFLDDoJxNfFjnKrjhnN040EcyoXEEREz4nDBu5K6ZWfbTQPBwBYAfMmcznvY2efLS7om/scQh7eo/vnFq85sLY8y7Kg9H2sa381mVBBic+o3SfMK8XzMz/wMpAAzkF9nTsMqcmxiXNmNx4AIcgndu1EyFkRzcqwJm2CfRJ9vLoMT9KFw7CmZNsxISB7sb9z0Dtr0ZpCoH9sIHHE7K7gGLUTDSTXMfgx/3ic6/r7htdn6aOrECOxV/58RGJYqccr+swUhDi4dIHw491KKq0NlzXlXtBc6VkaiI4xiuYQhMcMbu9a2vT6qx2WlD3c+pifDlcokQ93O/qG0osqqiHQGgkTM4SsP3Q2jwkhmF84pWl93VqnYUi7WW3SgWwyq1tVpgpdesa1ameR06TBHQaNtwli+PhM1qZkZXoX0q1IjgHzNLWqAskFOBS4Ctlxs326qM62LFVmvjFyMX1G15PLKey5vdesa0IaFC22rRGWwbNUG3CRqYVnZBs5MxOxD4wDQwpYqh2W7ub+g6wH3F4Zc8w+YD+8U7AIOrV7kqfU+3JA3jqi+Py96QoeeZ7ruKvHaPOqPvPggsrkE9nq9+DDEfkqv6u0hEjY3XE/n9fERXIMYWi4WVYjMV9zsdHxCbBUfetZx66MRaXYqWV/m7UBIv9RkpPOBHIFlhrYMb79HY1+WhYvFIpj/Bsgl65uzGInc4PfzeBqFly2KbdznFvdSQa3xGBeAIEYIgkYJF8skPEuJEM1/d7NJU6RyxlP/3x7LC/Xy4XXby0ggM4DCMP32s71kU8A5EOElySOsHWAhsvvLSTeHLzVaXfx6vuf29ougc7rjispoBHX4jSXPOh5KFrQJw9my4iDfrLV31XRehlIIRGi2TKt2AVDTWFTkQTbAUWwns5UqtxVoNCK3UNaTMPZuTC9HeLzDEouSdMmdGeEVq+xnBT+LojXpxjQtVuEDxpiGZredoEuJLe6xgBVjJLzrDL7HkcuG4nVyOK9wZGmMdBIBMszyWupq7UQzgS9C4Ajh07QoGJHFEbv6/NsD6NcbKR0JQuQfj/auoI0JFWameeEPEdvPFO9X2zepcFn7F29yAgGzZffLzK5cbCwHjiyFNij2/ZAeLDUqwJjB1C4LdHxEnrzLhaQPtLq1RPHxpDb/1So01W1dutCiqp426QDG0BwllsjxGQnBaEtctrY/t3EAZpbN443mZQuF5AGjavFiiiH5gBGMO+0aM5pxUbozltSgdNkAG7cTuc+Zuy8pYl+Aejs/3r7NlreekOnxG2eycWpgaUlNhPIzjtNok2bc1pZSqo1XMwIW0efY1TUZj3UaEKRerpQunQgU2nOgOhw8OUiMLJznuFgl0oMDLEYMTW0WZ8i3jyJ0XyZJakplIY1CKxxqdPeswssgxt7wLIgL/MPBk/iL7rRTNmiwZHQGFWdRW1uZhvOjmymOUNIpj1ixJvovlBD0L2kmbLdvyiuK4tOU2aEVkBC6ZizE/DFQAxUZrPAqBJ8w+YAPWiTRcsi7xhR0L33Hw8E8UkwZnEkCvp+HcAcM5kJafCIZb7zR8fn5m4PHB166HAL4NALuqqr21zRgMPpPhRrs8C34lzlF5LIVc5JAcTosh3Gdf44fVuzVhHjMbDWwyXj4UP6LhgLdzrW8aMobBk6nk7R4HQ2EbI3nImp7HUmx9teda6uHSNBBTzM9jf6xUR23XNDic7EiW38p9U/i1cnVuAmzgWJKoz0E+VNgBH8Vo1UkQJ8MIE6syCTHEvJ3/TW28UpSjLS1RWRQ3RoddGKiFG9/x0TRmaGpDiWNW7GQGx4ti3yISliQLNB6GyIsISkWjyoj/uwLhABJg4y0TK2ywQnZJ2FRQXPw+CrRlH9gYwXZlkVA8/Q3zw762eo/gOz+lo70nk8NZQ2TSYtlKUD+ueJbEjNsRz2bJts4FKVBD6NeeBhHA232Af+WvtpCSl/ZrABgP8eScuGF4Oet45tYAbCKWp1MDOHt1VPUdpxtg2D62vRGT9kI86jmlvKaGCl5EWUYKXQpMchwIgW3JD9TOCbBw5Vhb8pVd+PZUIe1cBd3j84G448BIYxXWZl58xP47wGWnCPC1AMboQhPc1YNrpTzy8oERuOA7yE+zVf9drGh997FGh40/g/7mwHscj6tI4udoUOzK+J85JNGTri/fqweoIREahdktoWeOz+kVZkIvvOUxP2PfFQG3EmWGMyDly4TF64T/U6BzJipuCMiyIhPTUcu5afDXd8HIlMH0o6CcexOsgBpe1mT8gvoifqfbesXkcBi9FTcVc/iDoO/sFLk43tf0X7SMs5ZpLThUg0/ZDJb8lMtVLB1P7gmSo80QIxTqF6JL0L4vJyJW5ZbEe9V00yaFH15xrM/PeAOJWJG2xIXx0Ua3pUq7LxBRiTjnLK3+ZdI0iFUiu37wthrr1dFY2BHJdX3pW7T7KwutNGnrnELY74OPrprl+W1+kJxET1//TjmdDoVdq5BPN+U/Vn84yuk88Q1Q6Xw2xT0Y0gnVW4hlFeDD4BI1zk+H89WQ5AXjF18lRrBsZnvKHBXLQo8oFurxdR4ijgyNAlmfMyAQkaH/jC1kKN+0TXJR3V8o/TtRIdRRDZIXEy1141NWotWeJBa9QFjBbk45HFPaEnMJu+eS+0XQ/Z7daJMk00AwKbmt9EBnDk5O+VZaCDUR6UfdDRJGecZTMimI6PV7dcwJ5ne9is+mGgwjSnQ6xSEw6hffY7R6iwuGGyPeS4G5Tu33xR0WPJVr8APXiWhTiQDw5RMue41mc3H3IKBZVm6Q1hgOZdfHULQBB9T6pHmfDwxOy07gpSf94uY78cOYmM4T/w1/c2nsZAOgwUNr7p0vIXnhr6GKiXIQf6GxQHXUQo6vFXdHYc/KHSvA4YJLGZL4zgOS9xkt7C1k9cYlP95HTHymULYLzycSBZVAO9kBdspNOJt08oJbJKGxTpH7jRW5JFAkI1KU1vY5VxywDm8Yyf3dNu2DOEQw2COSJiVKZL8Agw87YYtXqUCAdMdAhKjjxiPijEqjiQEqxf7P51cj1q3xHm96S+ACtXF4bcDzboE/hZsccXm9mN3vNZ5HbSeuzfdD448MrfNDOA4qRTLFuWJ9LqkjqSZ3626qi8HlIbheBYH5V3QiEEiEfL5oOr31WCFLCd/DEP2Q8JliZG7bHGLk6DHueZExU0F19AjYOP9mGon6fKFEIEBOeuuZzRcH3C6lhmOpTQVrjiZiTHPheZaJsb0fTLnQ2Td4isrJDK2tDsANsVdg2uMK3qxpgA0f6TqMPDzJADj3YYsF/Bvd2feacT1PiALWJuw+MX/5fK1lU4lZuy+XWxM7aBo0AGw9+O96a2mEvzC3wbUUAFdbMQqtfzbOxmwNZ0yYF4RWMRAOwi8BCjOATanGSgfzOeiSaf9ncNPmdaw9qz5IXQlxBosPoCPP/dAbngu/TA+QYUPLUx08JIKK7oNWAbtwUPjml53TWru5wmgg5BPLVv0PHVtl2BtrZyqbvDAhMAoOhefccA+LydaM6ll0Vs31dfkY4emaUHR1V0uWad+4Z10yPwWGTxlC8AAR3xGq3lffABEWZkh2Xtgwoy3T2CNbeFqmWjuD4bRk01VDv4IJtIk8zdUC/uK6sNFva3Dp7VRd5X3F75XHxFotxEuWsyfOi1I9rDgO2RRB0VYP+ycyNs66ejHnE1fBVyDnfsltk0JIAr8QQcJHkQS/cnx+y171PmsfUinR4zDmPGVtjUPQ2IhwHGHJ6c8lR3GewPQx73y5PD2sUPlplt+iq4FaQy2ThvTTMMxSkbs3wxVr7Fs0m1P3PR6vz+f1HK8bS1gsidyQaYxgsiInAnC+qQtpyZUaBw2tzRhC46opkua8YH2laZu4TZbjxNwsn5uYXObTE3h8f/SkkgIkWDbaqJ31nxs6scijD980yzAb/LB8Xgk0skFLJLSoP9obdhuKlZZaCwCSgnfVQb236VVpgE50R1XThuyWNM2zDk8fTcBB3FSve+1dseKUPSPzbK1U5KVaK35gbNJ36xrgUNdN8CtzXXDDqZeJKUelZPElsbNMKuB2f8h79hR2TAwaCd4IOUxfN54MpxGi+NCQa5MbTLTDLuy05kmVyulIWLQrzVKIZWs+ElrRaNTVdDgSS6S4msJlAlbrzPCvBul76KVHFeOmZDUj0Z5Quu3h8C9/Qd5W7QwixuF0u9P3LPBpz9M1j+H9V4tHzisOqjguQyoc8EVIVqorXmyWyrmlkq8JJZMP+KP5oF2kFDbr/OdOrVOOUmUUIMOIPRW/C3adCcAcpv+GIjfgvfrVTRtc4baXRew+g+LpRNWubglSfQEq1++YTYBFH8JS2uh5LNhhSfAqvZYznLVclj3UZpOxq4EGl2VsuLGYeNh1B1dlKopzvstY6OZjYodEKKMtdgvZ9AbXAU1kaFGel0sM+c2ISkSZEaCHYRODdPhwRDlg9JiVNT2B/V01cESNO9NTigfzZrm8zYqUJ/n8HHxBZmRl+RFgD+6Cb/m1slJ0qBBydqrnCNBOuwJ9vqcZCzplfg6kD1Ywh3eU0r6esq9qE3GIzG/RbpLci3SZXj+1b6iRH5WFRfLS9OAolwdOwAbw9u3wOIwyaiPsIN3emV2u1qNPRbxBsgzCfd98R8QFsjeNs9m5pFR7wBVfoa9CTy61/Krmp61g4hZ6YpQ0vy4K7zSrk5QgI/ZoLnffTz/NpMZaV0QVfECNp6cbrwy2cVBFYkxrr6v1+o3Qyz6XhSBWgQ5u7PL23JmaLzSvrkeQGW82UOOKyiqPRrJX6USaYsWiblNCJDlRtu3Mi/1SvkGg9g5lWJ9kOg5/dZCNMC7CXPIcubimKu3zOKhxOG98fc8hd2qqWsgLAOFvBjZdnk6YBM0CVg4StYO69AKvRgAmr4OAeO3XzpPnrcT/MR+YAJ14TNCuu/bXJ2z/2CiqWwGqUmj1BhdAVjVi1r6PgOSED7Rf5fUDOucQsDruz0QRxcG3Liv8UPF9dM73aa/n1IUrO+G3rqhed0+vmSpqC59OLR433YsG55E+b+UvLIBGzngqNeBCE2v9DEowNp218A8iTg8cAlM24LsPwbakAUkxAd5NQOkFn4IKr3wuY1WjVafHzw9YfBabjDWEasQSBzk27n+pz9K0vvNf2py+7vTiaGMsguJmnZg+bAZxUDf6eWoRoI6+d+mRW76Rn4WZhjRrTUEcUuLE2ZxO7iYMyFaKcZcpeMvuJnGi+QdeKOT2bxfd/GURCD2NpMzXZamdJj1/S7adNBdXOxw02inMQ+jG/cTabhqOctTjuRfduk4iL21aVUVhuUt/YgpXcr3L64NdHzAknwnbSpGnax21nQm9x88L7IR8dbxKq5TN+Mwo1CoIjl7fcPhy6ppqymVxzwSdJ3AqcK7r96Eg4m1ykOAQRd0LLrr2fMHtr6j5ZwPBzditoJ8jSloMREGoMrI4rvPHWaOKeopob0Jg8NovC+oFawablmwPYZWdBWwmVFxDUX40Ghyjpr3E2l4/9HLYi/0evNmhxtK7blRnFe7p13D08bqHl5Thgs+7+0+bEtxOV3vYgM1hC8SrIlWyLLGOy8z3uuEazc7y9uvhGZMzFA3F0WSUFuXCa72YEZyHZ3UPdB9Ja6evyfd7wV5s5pFK09Jto+OaZhiFRBsRyEJnsu125cpRbiOLGVrus3SEYxyJ0QFWQkMgLK/liQFBAi54LHsSVKFrRXEOp816DGcrVDLfJN6NIoGgwqhWeSokkxZXguyeDnAjGbbcxjFsDbYHwGeIoa5/EHj7E6jf9XBA8LLRISjrhW32YChl8qLz/KCFlupO3cVsNZ90WK74NPGy63XTe/mqTx/x9bdNTlsku2COEb+Pj/hkmdfDrGiIJ1LupeiWKYXnmx4hgJSyWc0Fx/hPspRVtapC8WXdfp7WZf1A4E6/xsUCTos3+1Jru903oUWpOFZu52uerZAMfbw15L/yGMiiSC/4xL34eW+16Kcb9nHTgrTUyXJJlKyujajWeXyEnrDP3AiEK1ZvMt/Rsx1mXrjJJvKfq9xQtiGSG91kHYCQiQQ+tTv9+rNoYBMFzOrM0ddnz1YzNyKAxTpojSCsOdzHsGtzZIvdh6zu818z3xZCAd+IM9s1HVjbhvo1Z3uF/H0VkNgWw/dfvhN7/dqM3r4m2Vc9fl9BsukeQXqM3Iv1/QwNNpWah5CvsCBgemxsKf2p2EO4LaeoP1oTr7J3wDi1W77PW3D6COAApz1nb/99Lq/v59o+ZXKF+NWFiXR+Dc02d/2DI2AmsrTv+RYIhtiM2NJP4A6mRO955x6WvytSZ24h6CNyObYPdvE8SD9yH/rmim3rqV2IL79QUoZmE/5Q0BrwL0TsdtD98H1G1kIRjAdn8spOxa1+fkC9CD6KRh+hOvM8+ePki3y+gD/Is2+Y51FkfubJ9xDqQzTIGGeHN4iuEJo+3uJ7NNKS3UvwHMsqKumzGQ394GmvYcw0FXx746+qA95UK8xCnXgrn7o992uXJakki8FWX/MiMiH5/eJtvcVxjyhZ80vW+fMyMAllc4PPEctAKjc39K5t1PaE0pyrC3V2CJQZVkXVbDSt7lQvhdyZiszinCyHmZn7RIEPN3Quo4sOGcAJ6g8gtt9N1fmwp2+lJ/JKozX3lmpAVJlzpYycxqw2fQexQ3uxacMW6Q1pWInHm29SffrjBmSbVVd+d7f7VKrMUeEGi4qrk+171DWjcnWjDLtkYDUmGPx2hdO4LhrRpdYEQC/H5iEOlC+cUOHQ40GjxwGxbXZSMF9VDgxLgyqrw1Cp01ukF0ttEtjFe+SQ9PurCDQUnFbBCR9QQs+kX1yqPUieYbr04v/DgLprJ9wok1EgwIdu4zcZi6d1ZEMpGzHhHxZDoex7/VLdLdkC5SvWkS6CvMpLEtAKQ1ptAqJJFfwXJrkEOr92CoDY4WeVJOMTWZLk/27fQ0phJXYZlM3xAm4Gwc8mrbxjX3lmQ3r+Q+wKsZhRg/JwkN7CT9p9+UCFFNtozFuMH3w61vIxsXwFxKk9xNvO4C7afXmpg7BSZ/OI4FHmTMssu1QxFMkGOJRJLRmgFtWN8Xjz5Yg6bWRayZXc2ukw35m2Qa4Ry1yxjKoPcDlNBwI+q2VXTOLWVNBLSyefh9dV2HezWCJZqLPacX6CmejKOjUYQqXW0nmDwdaMwM7QmDFBFxB2Qd5PBjZ2t0sOrWSvBtraUAuqEPAMyfTzZCYDeY0SXOj37nuI1IvPzYEU3BEOXN0Ga0Z1GMZqKMbu5HTNKzZqDV3lzaPpAaR2VRkWxeZF3u29kmwykXT6ckEnsTvQ3OtirLzD4lZJN0y0RPFAwucAp8AdN3DR7OB2NRtEQkvHJNTZllZX6GqPlNwwVLg25Ub9CSx5doxqWdXNk+bBWjiT7k4ACvmw7BoReDdZE6RtDDpoIYNDmxiaWAC3vGbDZ9c+JjmsM+EdaWrfhqGRI1aHY5LESmSuu1quNk1VazSOXf5Pfkkc4Liymu1iB6YVop+9rLHHy4Z0PBRwTE/fy0YtCyWH0+kOk2BwqqpjmK44QpVWkiVUiQSwGZhOeq3tOtBO7Z58Lq5FNZ5itUxmptIwSUhJHiepAf8qq1PFDaXNZh1xvEPsCKajyezN0AcUFjcIiupqpFgXStCMG0anUKQig7p9QfOMx+1ox87FsFydZY2XxzNL+Qj88N1gMLMspm+R/Irq+5uc0bQprZiXahi28u3WzISe38SQUcC8algOh6R4qZ1ee4Ieyxn0sEsAmSwE38eNMcNhpb0iRKeAXaxVAuTFsZgOu9wLrQhnosGH8IEyQM8GnTZ0Iz9ibh+rFcHL7NM/kzhjvW73xC2kYs/M8C4cav2kqX3RBP3SHnfPWrygBrjHXfbeZFrKtNOnjuLTSmVbG76c9ZppYYZ2iAEDUKi6HRW3OIa11+uxR91uG6HgktUsp+hXqc5O/hgZX3HapK/r4rsXF5/NVHhudpWYac+Vw5DpgRzgoTquU+NLEu5+Dmwr4zhdgQ/dIoOORcPfqHUgQiMNy96eLQpOJVXg3Ip+Zd4JXhW8FKlYHhSrGRQK2bJHqHq8s6/fpPQ2hGDoLVT3tOCffAGJSKcsfYcbLG6M/qxQiXJ9UoIW7P97ich0Bg/UOXR6OpkgbCMGiN47CMRSpnsQqBpZccr+qgpDGewh37XATbygdeheOmN/UmwPODXWa/GOhWCUZEmwZvsiMUzWYRiPJN2GD+T34DaCTXdEuBH8qnV3OkMbzc0sp8rb00XsRDJb6662a1Umi7SqrJtXTzLltlsX/hpMIeYZuc1LqaWQ5GT4krfZawezz4LIXZn/gQVAtWo+wcUBPDWIRO31uowKJnoZR9vfqC9BKhXz6YRkAYQHZidLtVZTaEeOT38EGgAnaJ2K68BUVhCUUVXNgJPvA1nFcYF6tywTNdP44y9RNanj9W/ND4/xOjTeV5sUC1ux6aeKc5FW75+3a+PUQUOYXnMVn/f8GDGisLQwSkDnzpxp6A7CltvhBTHka2eipEDIywx+8pLe3+evoh1vRX9m6P+uZ7Ph7M3W0xrkwRmrgivu60ACwGMjJElAFRxBWwe2Xq1yaZ8jrtoAL+I66HDDhUscTYTsjv/KlSq4Up6x44My+Vbgn/Ye62bkXJPy/q/QBBecnnSeBb80Ma2I5cOlZC4336Q8JbL1iHDjoxOvpjNCVyib8z8CWxAaaa83ny8TpVQGoqBjlly0R9j43hhAN3ZB5TQbnLs+562vdwAnwflWrovvqT5PNroubtUOf174PfTTU7s30fHSBxzRzZShDPHwPHHRjuPvZ9iJPUbJa4F0tig1fWPYVlaOjiq+q/daPNEWLjqaWtgI1x+sjIHZhUtsqXGT4fzT7ew9tpM4fzYOgU3u6SRLlNp6fHt4JsMbrDsiwSgNpEd+Brp5qI0TENU8/ZQEt+qyEy9Lh7ZGUj3rLSBm2iajjs4eIkN96U1EX/OYRQzx+qodUJTTcQK5Zq7x0I1Cgtq24aUtmVDXFtPvSQIDiTWzYNpPCPMgoi9+DIErowo0mssmsoI6D4Lo6z+AqDJudZrwByOpCaK+5UNIzktiiqcYBkHeOkyy2hpOYqw635gcyxSD6pZ2SvYSpuL5PUR3uj7vOMzPkxP1cDr1gfP6A+bAnTE7+JUGGf7svMmGkV+4ONWPLakF/Wwxlc2SBLiBDE2g1nWvCmbJ3AqbqExenxO3hohV4ZCDcpEa1RIgzOWuYYhAiyjSRAOV8hK0CAi0iYIFORDt08XVpBDnIumw9ZLaIelTEpVOwpJQfK2YLhHmoMKJXCsM0CbgIeEe1G3lbhTnOYHa8c2aHLhg078I/DILWxfnEnvDf1jk548wDp5/FfhW12/begSUUWAS0E2rmp8vvpzzXlwB76wVA3QAZWWqie7cbHICH7VeVsonjFTj7f1gNQdfJ1d2/FyyfKsOvwjQ9wHfP84gSu8oLhrLrskGSSoA8g1isPvOnwB0CIUsrruLGsgTffKug3RABFZ+80kE7AyG9aDecXD5yxG6Wrezx+VPnL0k2lnJYSL8//VVyFWLqtZ7K3yuedY2zatb/GoVycIxHZde6HZ7e5qopRGZrfNu8dDF3P8jnYCpzcHljSpLr+ItiDrKVFlNx8xS7TCoyoireaFtu2n9pl+W7Hcc4LvK1PXnsDOi2hGoeqNkWcE5SgiCpgk5BH/RrztwcsK4AFYfsNQx0GBu4w00j3LPNz9f2GSbNXvp6oE5oiT+k7W0bO8MKibrRvcktKE17LIxXlj/rYmNV7zQVp70FGAVNCFKhRoh8BKqgkI01p4JRRkX7YVyTUep3ISLztcX7BmVeHcnLhdM04xQeSAbXnGBIaWx63YbHVfpHwB+Rm4YoAjbLGfL4ToTu4luQD5zcHAcDQGe+f6XX//uXNl6CJTB7+JnC7I988LO/dayZ/788PJj9MwD7nFdUWzPt+204kSoZyS5qgFFqAl5Jar5z6/jU2QmeFAUPirG4Lb5w5e7HB7+8fZD51rtAk7uUQ0+zcdWcOyN2a5yYcNtly/57R4yrEvzre5K2DtHR7U1O7kGD8MLV03T7X4ckrWeoM/t2yoZoLLhWRGHKJlxNoudkF2T0kamiTOPXDTLaS14UmzCNX4oeII2B8lDmf6ixLuMQYH3FBXhNdbOOTfUujhMUMxTYkUGNiV0Vmu7WIZmv+NOh932pi5BIkZc8K9CaZj2uOATPJzZNuvj5hMV7MRMiqJr3lSfajD8gYAfQndxuqHTgwk8Fgr4Ze/jFG6rkIyVdXHrCandZBPXvKKgdNvOiK3iBwA8VtrjSRQ9WrUaUmgnrMrOGVRa8Y1QuEAtemfJ+bnOMRe6gdNY3B7ahOms/fXcBizybNF1wdi47D4btlq9RhMBrz+GPgtoM8+OyeF8ixszC5eMsZTL2gXZrbv/vj41lcRSaoprz1HjhW77vnRgnDAqDXsx7QTbbKzP5xljSBni4BfoNNEiqK3OdYnOG1SgLdlYm9/NPJ8dsP282+m2Ux6mQi/wV9J/IxQnc2zJDB63L88TlKAoZDLqdVzYb9GzMHm2W+peQOdQfSziVxvJ766d4pp2E4wQm9UTp7PVKeMsunq2ekFOFn0+1MhaNwVZ4kRQJEnzakTLYCWTfNLe1+SvwS/SSUJQpLAqpVo8Zok7XW4n9nu4aqqOncpF5mtgMpiMwGwAVy9pkEYYMWUCplvWkSFRynrZsi6Wz6BME4j1JyKYOgw9c0jHe0wEDOuoW44dFjEHqtAvcuGchCJyJ5jvd+e817rED05SB6pPxYctyAOsv+NyuJnVtw3cK1zhRH4honXHsy8txwvbhQVtwOcVdJXs2V+OxGsuQ+95bbocg3LgIrJKNu89ATrpTFVrVCMSsGczMz5fQPFGFqJlvpvDPFRZgWvsYZHVKDlfD4P6WapDwkZLnX4t5MVmVMFRqx65tXNaE+hjx4TzbXMaJCRGUNmNijg59+41jLE6GGh4RZK9ClfoDOh255dWwLOh85e3rcDjdRQaZCwfQyddOgU+6v8qAtI6nDdzK2zrJg0y6lD5xTpZJQOYYeoBVBmDBrQrj3IcOgVnjbQ6q3erM7DU6mjxkh/QgckSAWFmt1oKxcAwQ9QeJENhog2PYS9TEuoA4B0XNQXOOWNIN3ZNHHj1YuHpr9lYDhCBwtZREBBlYLbiEN19Szi4aOAN+Um2lcYwZ2HdrIKN9qhQsvQE13VEqHE4qFP47tDTM55WY9nTCr6i25s6XyHG8GlDyEh6WSikB2LRZdFRDVB7+melBr0PhvK/kN0Lq8AQbLue6sztQWGQ9PSwas5Ibd0lJuXyHsSTVBDcDoepmrsWTvqdlHvW2ygcP6mscBHuGdJ6jnYfwnOkX6IMHlf+nA6LTBkouC+oFj2Dn1sZvy1Ohwb+YTEvg0+QsIwij6LzpstGIaHY/ananqnOaSRUe4v6MUe6hF2Ojsm9XEXGUoln4fKErRAbK6tu8zi2xgUqSzsTCGe7So9dxWs8xctcutsf5KZuEjmZqvJsdnWQfoEVRPT9fLTHTz7MSkjRsanesJqt7NlVzzLIsRafYdkwo/e/cZmweEMmQU//TnYBAVG81y4zLrZ5Ab8LmEv6OvCD32rcWF3r+FEWSRKBGprdxanZcHWjA51UgGaLgih4e8yiBbqloY46OTdkn5L5jJhyhR/B7iYll41MW2jNhG7/6ohy/9YUW4e+pezN0u6LzlLNV5/tz7rN8BGR4AGYy3tAh0R5IqrNRJkFz8rsxfH/3sslAywOPVOIJDhCQQVjAntNwJ/9hiBMberS5BtSFl9lOBLQ8ZxemDPMMISCgyeEfjbS7bu9SbXA6a5z80IE0PTBYHCzaTwwBGcG1TBU/kAndcfqS6lIUBwBUnd8CkFs7Gh2t+2+ka3RBifOwJkdW+qpcjlJZ/zMMOUAW5nlVmBmERy13M9lHIyk3t/Lnbg6qnLQdGgl5zqr1tB0lyRxhXE37z4T+4lSlsB7WMBc8K7OXVFIY07V9k3b8fAeIfALzGf5H8UsaOKg1SUI9+rFuasZBpOLUqxlmOO2ab5WArndSKCeD6eObrKfCwOzRFxWWI4pf99q0nhLTyDHDca7W0W8MR6+BKNUaUlmkUyGfI5ZusgZqJC2552rsObmQOU1bt4plTiaLPSd06QyN6Bn2oVkq0udiFlOAzpY6rAMW6w70MWQEq6kJ5qRgb8aJbagTVSujY06ikIeiyktBa5zuHe3jnHGm45XGIBQAUx9w4Y653ShfLDOQFq1Dnt6F6fn3AsSk3LWyRRDdNF0MIFubkYMseG2hmC56T4oWffUlVMhGwSQz0Q08XXwXISSIwkC0/eXMRgh8duQBEXi3mwmx1oimEmBUPQgkLOgBR9zMWutxbyG2SJx441DWhIVhuuoc0ZPCdWfPO5N0jrMo2C0T5hDyxMA/wET7QQwQJj9tZt/R0RxYFI2ROlbIQuQMwwFsEx4ND1QLkkg5VpHrJnEfgZJcCcsCB5XG7OcSck0jfGZ7lTUHk/9h5B8fjcju9hgcuqVfQRqChR+iRthJZ1Il2zqrRaTyYpFVYSDlSbzylOk2AM4TLKEFFmrq3Yjgbl4f8WwLqKM0XlvhcR/9oGgu9tFw+2ML+P2fJjValnyeZMVTySRoU4aDXS84owSmRB2jS6dhboKdPEpRuVzn9Wy+pFQiuPO8vu2sG0y4ruHHFFZmkvYvWRy4YtmG7z3nz++eqKYJ2loZ++nW1G3YwHe4tpgyazfwsIwzHY6SKDdEkz8X3+qqx//7DHg8SJ+7a990xY+n6dErDbUdgSa62qcJr1SNJc0NTW4LQadUiyUG+qbPYDP0cRLGzxu45dI+u/hYbMKabDxO8brC/shdwZ4C+42Z1VW7K4Ti9dfdQf+T5nNf118/wdP728GJ6HXPwRRVQxXIVdtrtA/WHKWgFHa9MB0cRQ5M5Ps7OtF1mLXqmucdEBmek0K+MZ1mzKFBPwKJcGmgCHMzkC3n2XZy890psASLEus3UkwXCMfc8jh9pBO/wKnFPMstF+hcXK7x1quQoHDsOnnt+1KAnpLiZ1gLQX/MmpJLPjSmuxnEwHsYuL+AAOBMl7silJi9glrOSCZL1wU14o+obo96sNUnOua2NFLeFmByX0hm+KKZJ1y3ENJMhdqBJC4NBzrgjWwDLbrco+VWG3yrmGbwhJpazSXVquzjpMj+N/C/O7Tl0sPcNKD+cbiEqcyl0htmRpMkhmkTKETpKLQ0ncBpi+qX2QpeY0vGeDUZeidpiedsW1tycpCI136rshYKarzYY5qxG1fWIlO4It+bCVs5BNcU7YPLsmdzk6mgkEb72zJdq3Hr3cGG0EX0hEG59PAEIi47dj5z9vaOjWSJdXxhZNtHntgFMHGu3I4yCkkjxQmYwgbwVAbXOvIbDJUHqgPqTXecbB0qnUKOTfj2E9c6ojsdTioaBztmroIPfRzI4MS0ZS/hEVbLQFixODRszkmHShlqGTqCvx1HD5z0obntSdtGBpRcA5t/GHpZt52zHYjWowOmGcPn2owHcel4byGCs/1fCLSbtgVry+DhBhhRaGf76q0ebC98F6lLDWAJNLZ41p8FD0YqX5qDQEyT6lEKLtzkxqHyD+DZyJnJJ7sqtdufCm06ME1niZ7mUKn5/RYi0xCr4oGT3EJCtM+i89glEHVV6JqV8W2f49JeowaYrPpsg1RyndlTCzdIjFVF3DE8i7SfFMqWFkVEjlGkN5eX0NcyXnV7Pa43ueBYA5xY6ltXDOkPRYQ79x8uhjQhAGF0rQ1je4aDoI7392mdPjhzv3SvZ1JzrwrMTBLk4fnJLRGozO1uNFw6ggD8nmOshsXRWNBXqRSWIFojuSaXRMb0yMCwk0Vk1PJVZUjhqXWzziZbeWGzM6fQ5z/jFn4gf1LwoexvzraZD6d2uEnwFdBtaGXyu1yz6wGNpdrTKnmc2GtXqmHqgq74snEb7qVTemrVhB8PwgvI8hSSQAUV6U+WMtzuFyX6njNekNGQzpHj+mqNbc3SD6ClMHhjrnPKBdqXpnvlHCGkunRHV2/WJeqBiaj7bCWftZD6xAhgOhvsWypbvNzGyqcqRgDLaIp5BQcriqBIWJCiL4DMV2c4Z91XCqWAsZy+PJGGNWGjSWjlFkbli6uYSRHBibzwZm1LLthImt4qq2fCWbDj+DP0Mue4y0QcsJPQDzUrN5sMk/JXGWG9lyZpVzXBorInY1t7nl+EJyB3S0tmKhUyuFMlIbC87UlWiYga2qKYO+aPVY4T1oqnMKoL9YdXMtP/ThRIXwWcZYRuU3vQvMJgoE+iHmKHmSxuMcpOod1XXKI+JhAy6JmpPcyrWHvBluWdr5iVTmaqsplrDsPL4RGfK5+MTe1m3RbOdk1NJE1/dExezPvlNh71qR4vOznx0XX5Niv33y5GFE98+deiFXasro0e8qqLgIveV17WxEgJSJTS8r5MBhjrxaV2qjjkJkgWWSRlxTl7eZyHfREyrwWHGVS5TnrWkfqyDBy0BOu7bsfhx7z5357VaLrFZATUh6guBKL/iBvnFIpzhW0O5Btse9vMRMNOcEI0YpFQ5VmSjFdnvudz0YDbBjAycAP7fx0g+UI5jB9DlnJYWIS6GJvNDHeMfjU0+Nq5fz3a4piWwl+tX/QMrXtj4Es6vJltwky/4sunrFLpQkPtsQbGbp5a4gju5KQ9+lE8hkwZPI/Q32m1f2xbqr6qwGxKcua0to7heExJB3TzF4uT+55a1PNlmKa8FxXmQRr3d5+p6mKQ2QLsRKj6XrxBH13urBtV9IkOvb39OJIH+7ydGKG4fKjXiapqYstZLUhVZSgOY6KjnFjdV2bWtm2XaetG0ayie2cH7O/nDNYiULuXS92I8Y43hk+hvACtC91dlcSiuCOrm5oLJgtMrktdvG6kFRbbJkLaWXtBKQotNEBRFnhKVWoYtLmh+qmUUrDEng5b9pbDOinzfiwkkzvTZMjNsXqGPjhdNtWrPZFemN8K2qeTkDh8tpmn/7WwKuSORTAP76fzfzhA9m0GBlJZn6RwkBvwFMgxcOHRdNUXhFy4+52gHnAwoe3nkQdXoD+aDFABArSHNuLQam5u6Iy118mSXzBMnM3w2j3CY4iJ/IbX5LuX/Pm5DMZ7VBcb7aqcWeawVq2vTCwGuR+YONBKaIlljJ0zQSC8bLjrqifw9TiK3WT4tC+d+qTd20MN7UuRotg8jLWgaQqEc7Z3EkVYjahMERqcd8ipSLg8jX0mPkdhkeSq3rpzADrdWO/8SUh7LP6WIKnZFykLRBJw1s0y5LmAiyFNk3LsYCrO0Z1WF/DiGNX9K5gOcnVO0f2NwvRix8+Bc2lvBua0xM9N0+S6B8TdAGu0nba1Q1wPv15/41oOJEvVpRNpxyK30LmhZTVSnuJlZizIXgNi5EatZzFSt+exjxu36vMYTuDtEB4d1Thvb5bQXzyJD7eq1marwKxDkbV696Gwo9JhcbEZD6fGRfFTpuYaveztLPgUcl0ltDzCu718lZ6jBZMzjjJdX7Sa7A2RCoVinngLgYo+U67lQOmxmigLBg3Eza95jkFp4wOznvxwY3gK6V+7wWMhwa6eGTWHsttQmgq1szn4ufCqXgADLHIxap5lzW2ATv+Y6Ex14G6GMJni2MBaQLarw6K+SXoJR9xVLIjfsX7r2Q5xFd96UomWuq/so3VVVPNKm3VV1I5ytJtHvGmqklHoeatDBXZRmBo/zGGFOdLDDSLS2OFNqclzBFLIi2HrwMi+HY/HQzbjAmIEtbAGGSSoxjHIUGZhEFnljvEbU2WjmMLqolYuwR3eqwlN0RaVTzLwF6dJdDPlCGgpHNVEmWan8+RF3G0HMrmbjh6Ov3pDboqUjxygqdpwJTIOm5oVUiNhVtVEuHk2p+G8rLfqFJi9GfKho3JXsDeyNMQXol0cjge9Wo5dYhwWeN+jrJZWhazYX4OBh2Do6kOy41YMeTxgaVrxpHA9LVClW3NUsBSpzNUaiUt2Jg353U2wFLEAT9jExn0OsEE9CnvnWZXh6wmX3YLlqWLEX2rPibLCEVww/kkI1dlx6YQdQRWY9lK0Uvh87qNrfA3mzdNZClTrPC11DbTyQlZ4JyWJPWfA8SVBFkiGrVd7xC4h7CAUVdJcYODqwf084cmJCKWJHttQRnKW9f5/xwYJZTr3/lqNaeIMBnHw66DPTN4LbUEbPhaSXvvHz9S0+JRU8fuDX/A1q40+Wn7tT20lfnhEFfq7OH0SwrnIeR07rkIFAAREl9MsvX5xa0EjPJZMxpUWXQzpK+yyTxeIldqOQIFKP+X7a5kPNujez6Mx5NQVOSi9sdBpaYG/IAOs68Usp7cHBroYuDku54Xfr5J7L1R36QHbWUKMOI8mJYJD6dIhIX6UYkLBeEtGPhsh0kd5xYHzLhgx7ONaTOsdGupY4ZvAnpgJzj8cE7eeyWomICdoCA1G9IgEvKxPpq8x2x3uQkmlgioceRebuOvEG77EQgKI1qtrVqdNCbT4cDjJM0YSKOldyN8EmuZcLkcS8g6h3iD5c6t2ZhgccgmpJq11dhsNiVuMhwlyTjLPhGJxjguxnq0LAZXJRsjpAA0aVKNiKZCbqK9baVu6gQp8me/3UKohTLTlN1IhwvOUOpYwFeIQeqqf8rjV1VJotchaE/FtSAPCgb32+hDMwwh4Ta1P+rtAeadZ772saDjzDzEN77MbZjDi17sUR0QG5HLOIthABLqPfE0AgKP4eZ2Z6buSi3vOJXIiXjbG1mtTIHNx4Er7QRtrtrvGoev1+pFjrwYuMTXeKAw7/iEqD/+th8AvLXN6CXEe/Td18OVG2yeu94JPpZOAJvHQ7DjmRWHdhO0Eg8jRXydxDSFHI+hXAYMBjdyuS7FO4AAm0Vfude5cGZduon7EAJkS13GpE4FBdT8b/f5nuXbl1p498qhYCxF7enK0G2ShO+5LYq+wWUUgK/bPWTTzhiwrk1e69fW/bRz+BlAAAAvStrBrrlJ8uSbq+l/vxA/aFphPQyDTlCe+xc9dCaC8ZPK1snDlihAcNQRr4CBTegxXZ04QKt+os3MXVPLJPJUgkFrdYUG+8Jr+T/2SiqF7qCqj77DlV6GN1fmuO58uhvvSobVJAcMITHOYLo92UZA5N2riUDTAZIjRGSBusdLEdrWdG4bttjU2mF9yCoIBC3Ol+NA45DSAKP0sh7s7w7IFGi768zrU+nNzBX5vYfC8JB5bD7oipLUSWb+6p8OJm6vyBkYF8by07uFTw4xXugB8xXctp4STj5Bin+Kija53t80sP46ugEawH2HnQ5gUT2hx3FjkV2JGh1Zis5iC7SSUIZsR7zyukQkrN3fEkmp8ciT9mAetgBQFozXhrqM23m/yIaKOeTEFTJAWL5xZbVcLulNPb2/iwLzD9JpPTbEJa2YA2WkWlMzL5RHJYILlPyj+Cc8GSzqKazX440lTZd1VNYBy6ood3cqHWuiviWnZfhP3GtA9piiuVu3O49gBAeg3cu5sTPRReaSpKxz02+sKV6QSBJdhLwLDLKsT5jn0q/dhi2/IMnk7F5WwWVgFxVSeVOmvEUMn+ByCEePn1BLllgg8UtThWoo5JzlxLRaRr2i2BlQ5zRpnHtRFd6Yray5xSZiramVwQ6g7aOa7YKGmB4dZynzDKPqQJlaKJSWdyZqy/WWamTDwcFR7qa8dVOXz+DQbr4T9yP+4VFUML2luYAA3yuf0qHFs25oORDYh1dDG6XWeRHxdAKfKLGdXOkCcxOZi5FltuHaaFxiAQMSYoujCanuNkBhHDr7ThaYYDXstHER0lWImgK/Pze0xIwkv6yoJTuCUm7QSdZih05yNKGWB/L5P4oLu+36+2dT4zX4GXNDFGTYHRDm87C4X31jtrhWr7IKY616RlmLdrz2WlznHYVbA4OL+o7iKfxcw7He3wdm77qY9YMidaQ+gsmAB44xLAEQ9DHoPkSIVnYhnvQF7mYuYsjtwccZtWqk6dDc896w/nGOPn1EFmTHfrMb4A9ekKxdv6lvg1gyY71P3SjlEbfmOHTyDluzLqtIHuZ5QRDzODUTFPjv9BRJ/Dh76EMfYzEgyqml1Ryjnkz5xeicBzhguJ7rfQJtjB4wyCxECDYCtAtBn0ed3c2rbLOuMjxhhWtpz4O5bDyZmvnfgujNByVHncGposNXcqGvP/xEB7NQaiXMQtwZ4lBuhTkYd24Yr2WmqXOTeGsgXEmw3oT8neiUWlsKVQg2KS5Ah1Ctp7uB/EN7Mh3LAi2K1NYNSCwY40e7iJpHu6tRlzFMP5OS20OArIPkndYj83wYBjIbelwBwHCHj0zW+BiFBHwvPQ3KR7uCMvusITWzYC7A/ADDyEBoKdHptdzlamGiEoHUpMA0G61Ft4ChRR5h4SzithjrJIWKMDmNJmlvJTUYAm9nu1ZwtuePx5WNosj0Zi1oBtramKLckC+UVsINlUKJ9ApopOdGwr59PEPYqpU7/r24edM7/7Y/PU3oO84r9nf0tZq59lWv1QxnDotUWvCW94e899XvyOwqqepMYPLWmEe7KtsTa8b2I77FmIZT1FTX+ji2UHgr4bE2YT2xVwFD4ossyBuFqjhLaF4Ew0OcZrrmFrP0XHt34yAEIFENH9g4SYzRwtQl/kCL4vWUzsGnlgTDiMd0U4JvpiXPBvD18zmuR91spHFz2G03dmMGY4uoE5UgHrMLfgL4cutKBVZQSVtLa/YlNt4FvcqzyPn8WKS3YcvLMJxnagvubEFKIU1adVU06T4OCfd8SyixRFBqP0pVCRqtshgXsyHGyPN4FmynplQy1q9jevYnWrVPa4RqtPuSNbNbE67ak2Wy+RZmUTfej6GBRypCLlcEo0+Z/hDXnk5a/kPhDCdIyfZgAn5CxVOmn+yyjbcUwfLGi1A/iPpHoNrszehkp2y5ln2sUR5083TlWjpiyCBhvppkpvkewvU4+B2c9hPP6y5GtJDOUtjZIwQXTIzaMN2A05RzeQXOoaN/HXDCvmdKPpaXzpPeoAoMwf1i7VlFQBjDY4Png4BB+1E37bdcmhDyqXHfjJvrtkemY/vldE5u/iORj4wQ6jHWPbPiUomrQuXOzZwfHFvuqjMkuydQF/HovNioSPPJLuYI2GS7JaLSF6KUnPk8Lu8jYsNrKEwRt+1WUUnpFBbT1/Yz8EVHZH+dH2tX+ALxalfxg/FfNTEsR1nDLmBUik9HoiWJdtqUkqY2w3rNuMu6em5+KQt0K4y1O9nsrW8c5Wc5UIDBc1jaV9UsoUE6XSpVk2iz/UjBJ2Is3wbuHgVr+BWhLplMyme+iQlS00y2biuftJ6cVEolEqp5F7ouDovEqPZZe6LpEebDx655tcxtSaVRCizectlsQQptR/rVNDiuuMD2Uy9RA+nrJiOWBfi+SPhGJeIbHsUE05sb8xuosXAzdzRbbY9Wl0ptpZkp7W4O6+xq+vAV6PMP7oskSiJ6oQsSZwg/b7G4EgXgmPpHQ3t/ff8LtYwic/1QNC4coMD8/TwKrZ9dxaSHa7Nn0K79oA537WFz9QQCdEcSBGYF6jCsRviCInkdFso4in0MhSgzmMvG/f78LOtkjhttfoSp2WUhoIxlcVXPgDrTO1fnXNrmW5vampdXA2/lFxxQLidvk/4+4eeShJQp3ATNvil+1ZZOYwu/n00bcHMYa9iMxDVwsyVKKY9zzQv7If1iA4OQR+c9mJNsOb2OhQ9vhpvIMS2ej+PTQezsiCF/x7r4R7zfsFTAYZxqPkK7bELuBes9DdmNPMsjVudt2TPN7Cr8pbTjYHMl6ZlOuZyvHkSieGBFo6ILN0qhyvpuPTJ43yN8EXaI5vjCxPAUHXvsTMWh2dPv9s+47eafge1bBhyXXCF2cHGNwZkLmbJ4BMJcmbSGPSsrSXiFqtuRUm7MNOvQTLh0lc4V+ZF97yxdImKGjPa/PR3cH6DpdmkYmzFOdGdIxELBO0X9fgGwS33tceOiUh3AXoQddankSmAiUUohJ6+CPLo3bctLKX0RemVBVD/29MH5SnLRlPisK+ZCIOHor+4mYYgiyih5jkyyd1BDF6Rp5GPf8DkZ5JDaepMT2tNnjmSq6zsbFAhYcx4SyYTqsLR3MhfwXTj+HkNdl5+h81ScpuPW48M69qTfstZtObs+4SdXqxnGCCEHgCeVRrIncUaT6ZLaMISAP0YH8WpYf1+rNALsQTHM8TyX37dQTxoX7zcgfyvsqUdlV4JSqULcjs8jl9C9ZUexnzGWmUWrkj8oCJy+WBtfds50ozXlPchR29BBkK/cEJD2MiX4IdHEEzfg1QK6SgdL/sB0MCkZqZfUzn/XPPFKlnBlSjMHus5bVmcsxdXtsjEao/NFNMCAiyTB5P3dfkYEe9aGARiUcSmakKjyWftsyFJUVOmzqJzlAhOoIvGDGbe6CrI8J3pxfS62m7jpBBWw4UCtE07AJGjBSLYIxjm8h4a9KSfN+1CiLgufoSYP169M26QX3akddEeiccei+rLiiCTnZR3E2Kr2C2k3mQ0/rHmekEPERsUojlhr2FvYy1cRtesm/XEP1PVlziFhO2qxBe0q+faDz/AuQ4vJeA0LRsvtTRDQ1DV9EIMgCmuatj6JAhp/ztRiRhFunBu/k2l/QNNkpkWzxhYDCk28gDU7jrEkzgaAFuLIX8eFuyQOOZn7LMAPsXfkDhEbQO8z6CzHJTRYs+CPCjNGhxPAjQiaNe2WUn7QwN7IIp1+eEhBDaDDGAZwN3Qzic2MpD3vKDCU4g2g2MvmBtMPugB8ESjDCFtvJ/2eMPbz7+7lNglmBcVM7y+2EZBHN4wMzVbWgTg+SwGa9DViSL2bnjK5RAxamiZ3M4hmEi/9VdabNpmFBPkEPWgvdBe50W5M6sjlLqzt3gJi3VjXs53ccbUmmuDtNVYk/+3j1EE8aIMv/ONNkNzdXYOdWXw+B1QvV6McTNOP9SwyIhivwVVI9uyJKN0DtIDEQNb9lr4ukJMhCAxm9T1MQSe74KxuFkysdyG6sV6vouQ8eok6KgtfLR/Jh26AGR1CHl6m086TbAAooRl0wtqUbQ5+CUdILngSwjP0IpUfoEMuUyRjO/PA6aD6OUoTcHZifGwPtoyIqBiDyhr2I65aQ4Ba3DzC0ClStXgeOk6bvZaDMq68AnTR8tnkW0VnLW2JiswME+qrg3xpYCowH3DM0hLSj+vHxr1zhiCtD1Tw6WHp1IQECzjrqlLWv012nfN4NX08Nuzmre37OChUoWBCs6LWwOEb4P6cSvER3QdEo6bywZBcDxPEwhzMmPY0OYWK/Nw/n/xxKn1Y9z2k7g8WFJfCi6AUf6hTqKRowO1OZYEeX4HJ6ZgZRWSO2ksHsYbt9sr0H1979teTIWuhh6/VW2dVuZqfTkFRGO21rd2WGel6NBoeBUN5zSyQAdMw8T64lLhU140OHHWk/0cdIHhgnLbtmaPAxhCrU+GOCT1zVIaglvXoc2aleD1Ua9kDgIwHcWrmhHbSUHDqBlG6w3VcDVOfZDxtCeRoL50VjgIeJSFAjITBeRyi7nJlMAXyoxNTcR88kEtE4bRxngfHGZ//T5z+0vbXjsH/nbLpG3WizOyKWRUhA2+ypahhoGEkvq9RiCxMWDfoK5BoKiqS/6XJgyChxjma7O9JiQj1NwMxNOAsBn/RIehIy0c3e26TOXwaPMdqqCW3xO8f/BGP4DzPCbpsJNwf+RK07GKaxU+OJ5nNdDoSVF67+ORMJUkcyqO1mgS1AruurLHLD0Xy5t3Ls7EuhB4yT6lcoZDGvPUVUQk1+1aixpMtybS4ZLbULJw819hiq9wqxRy6EkVzE8FLkSSp1TUvb6q1WVtKrW3M5C4snXK2TrXQzWUBAXDkg+Ha+y4CAUtfh9YO4ar7mSM3HkVPWCByL+xOL2y8/JpRd2GlisIIad7ZFnJCE33Eb25ZpVGyjLm2jVHbuXF2/r3QMpCkruTZRBz5q9N8MJxOv1PVWuuikyEIBJDXgLphaUqmHiBWfnVx6Pj2RHDocoAbupAQpwk+iJ/pYLwEEbRA/nFCgMZlZk1v2TD7yvwqHx8Bcno+2biC7lyfHww7foiyWICxAQAA6ESc3kGzx4H0R8iJQ02tSiP34FR/hLJie0aJoLj02PmC9PSG100TW2AGbfn310QAVlMyrR4UTE1nUG6RMMmamMaj//4VNHcE4Ki4jXrRFlR1UU0p7INAq4QbMU65sbYp+6PxajiczTDPKjXOKsH34ehyj3F6c99iBWoZml61uRzRVUDnKFkyPEknK16czstAtB3JY6+6b/hsJI/kYkYr7c0uEwVDhTv1oWsTimWjJdQFfKTWz3KeWjbgRU3poMTzu+I+a4hDGsVSXhTwPh6SEPgbm9oWtRczwBB39HOVQDoZRM084ogqRNus4lizuSnScoOE7Gc5a6kmhSSo5o00MSGg4JNhRgWCM6tBSiyRRNjnSMNJayq8ZpFDlWcgckb80xb2sYZOpo294AjwDRhhoFgLgAXG+W+iJEj2eLHAdqOR7FoC159J6OfHu0i730a9fiUcYrNVenk9YQcFJlTDgAgg9h+3/FUG/CbMIHQxjeDuOuEWmhO+vUC4RXnL1BqS7f6HN0AeDd8bdbXbRuPhhKZgZ4tC9CNNAFdILgqtkwZpPShUIUTXOaMgxD1GgscEgsxhQhVTBgR8NkJu4ErINbdgeAZijxlsUeVLsSCsrDl/BGjtFc55XVFwQKSRS9939ed425oi/L7sbw9NvbBL/WRkrxDIp+uNxy8OOz2s1teU6OdTePj8rZy2sXulmc2WPPfDU4hPBBityQzKeYK2PcVGXiaYcsbkNY8QtHwWHO+myYCpXJdAMkbWTNN1CFJ0w/l1MQHq3n34ioj9h1/1RfLqMD/ljJjWfyAEgZGfYwHjuUoMARKHEFUAhFTMmtZ2Nzjh22c8r0LubkKEU4UXGaGcjeEC8uzsKLpj8eN/xIggz/Z4bQinYxQSp5mU3IA1kt831eYp2/YURGf/X2vI+cqBcHxaatyCr6bhbl3VshD6hxPv7AQ5BtPaOMJku0ZiQJyrmeIcASmaP3w7rgXPv7n/PJyPDg1CV46cZ8KUsL2cgiCoGj1XOKLyFUWfoM8BM8NsLhTE/C5TWeQik1Zr6KyA5WTiV3PaxCZtWPb9p/PlLlCEBhKIyYyS4lvE5D3YK76EuumbdHmDUb9C3xtdqNON9OUD/ol41EuvIwE28/YlXVrx0P2S6DAX6fNI/BwvrrbkZyZW4EsYrHlnwtbeUpYNnfZE+fRZ6QVtyTzN6LdOT9861Wu5OP+cuT8MP60lOfutt3S4gJZbtd9xe5CA+3c7+oTUoD/pN24GxiIpWmx9zOU8zwv6I4TepEtGPUT6SENuc0IvLwEH9jl3Eu6q6CBKdOzbKnUgGzuQxqzEzML57PZ/ftA0g9ExHoV6pCGPcnJJg4HV5HwbiQA34UQAo3TsKzg3m23MIUjZtpkFL8+uPdKNOIUQ3nYYkPZpGUIP+uqUOfyZwCMfo97A1qKJhnoiYFhfL19JAx6BJBDDKKv/UizM2aw6cYAjbUJASVRsX4xX3PO5XJNmGBNHd31afbDNvu3745a/Fx/sAmdLcTcSC5z3ZvdzVdIATy4U7XeFQC+LOxx2i0HnKIXdU6agvbC1enwFBf+SaA8mVroDt1KYuBq0Oma8c1syLU20HuoiW5bbSTyqvfSEzf/Pg/uuPbql0jyP90npTfgYF0xEFDVcXk38OiDiIsuVM6hKbkRIdazYSDS145gyoebWwoKBBSguPRwPJRuj4wf0zdKwHh3wLlrFBLT28zh1LT6QfsgoYygEDGbEbrKhmBm1UXhnu8PldD1XehMCoIPXut1vU8u/WRuh+WK9WXdz4JX4OIb3ehZpqOcxsmLTaGic2FmuDBfeSIXDqLz3un/2siuzKpFFT/fHEziepmCfzsz6/Uy7Oozl0HnhvXQ4V/+kzwzNLunCFuPgBvRUKhTDeJzUcwfTXKE0kaPNZxRFfcZk8ShbY/jawlYBgcHoatUED3SNZz4ppvbnUJPNXrywB1rDyfWuG+Wz4XJHcUPctSjhYkljfNW1T9is0H8Gfey6ejDbsEW5ViZhDwii00Evb+qwacsUNis/YdIzOOh1vJYda1fxjdYwsYVowAxB/eRyHBMnIIlQ86I9lw8MLX0dIpY4sjyergKeGeVUP9evKhzXxbXeMYK/4odKHl56KUITNCCCENOWDwiFFj28ubKdgCFXqOWt8ajPbgvz7sNP/e7OL7muIupUgkpEez1YCCZKlfwodMgCOQYg9zFD31H26JM3Ij7fElnQqEWe0816TodObkNGom+sZGA/yzPW010/tnxCmUTG1hldovSPfMnstBiNK/HcnV5QaCnT6nnK3n6maacEIG1j5cZi9KFPICC74J2y5KjljlUsLt6fJopGFF5vKr8jpPHaqjRtsxkzIHKi81Rl/ANkPpX6ZNjilySKQhGKwFpkFjXgZfBNMbrfeP141G61z2za6CYsU4MAJatzvjhpjqRo+aO+UD7sPdTw8YNDlsyvlTDw+p+RqPI1yHWBgBFoNFJCRKGYlPRp8Wvwi8DgFRRo8tL1HVP3tvIV5PeZoHGJt7Z8GmjqBIpolo0hFg0UjxO7ARDoEirtwNA3WjP0Y3y3AJ3YcF7ZGt4HEH62p0Pb8vXzNFVTpQT9cQ7MdtHVSZC4ws2AiP3xQWCs1ZzIszSUOgLOjTgBTEulQCrDA9LrNe4fqYEQ4rG+0Anfuc7zHRAp952XRQ9CFhhCxmWzaeMzeFHhOW13zjiYAeDgnRiwizz44Xgc0C5bfQHeOoZu3cD00mOIubJkCH85GhyPx8CoM7XXfvSSgSkD9I/gwTGM6SQHqmPZFDJrqzqoj3SDIJt6Txjhcp4MQCgSP4vPg+nuLkEijgLs8FQcXDqSAL3B6feeQ6YmebUEpHczJhumww69t5Vdyr1W/JMxgG4w2CnBqI8BMzMOujU9BeL9OejOuvMvEPOahjugBj3ab80bfHvVfkWMxQfbtm2rj8Db2A/muSw1DMoZQbBKZUBfxgg4rdKAz8iDvYoESxntoE1VwakRCKgLTvIuSB3rLkOsl2TBSM1pFiE8/dYo1FU3pAyNz8aFWYQcW8QiZ1lREwDFnSDvnsW9pGbHknCMURd10F85aCIj67IL8dY07YUm6friHVCmY6yZ/UILboIF54nm9jEhqNRhLXrXMQjnvOqV/OmeMQ4/DVqln6w4bHrwrNxkk90HwiZ9+Qypsv14PLB2rWoTfSiMZHKaG2CyM7lGEwC2Js7qK+VQoK78ACSYbRm8kjUOQibq0bslS78EGgNoLyvWjOf+ymQfm7gNPSjyYcLvq3i+e0aoCTAzroG5bjo/kKGDkGqCKRkcEFUWNI9hjwqGbdKU3y+ZsIOozToMtjsxdopFkacSEaSPMHu3gbJPXOkWT4AzziFllj7QtLCXC2bHtiPWH/NFcGRamtcMxy6v6dJO+cC+wmyYEUo02Ko1pO2mbYKPYEGHwO5b0nafSYLDGi/TCc5sTzbsZS0L0Gxm6h1alQXshxkCIQ7G+FSPN2Bb5eBCPLS+BgYrocIDW+lmKDigoljoa/dD+R3GZy17t5QPye7uN7Bzpeq6L4LGJw2jlwKStAMKVl8QHNqnYB2MAIxlQK/GgMkrPwSH10HsHU3oUxiW2/AuP8ctJ/vADgL/FQpTe0PckcTpRT6fw/XfgG4s7xX6ICB5l1PvwedTn1pvVZ+qd++WFpzC9kGszwxA03e9ArLzuD7k+SyDHfLsCBatIwosgrxfjmene+XP+QyjFLZWC9+NDgwCV1L38vUfNmx/dbX3ANMTK/ARfYb/EIWdm49GSZNNpxvSQv7D5MhpB0mq+3V/6XWwv1v1BuJcup+8QsN5l6yyLCxDM/pqQMKzNPjvbw+Le4+R6nJf7IuzXRe3nOSNCFjSRe9l7JQMJMDWVj/6BPLBgG/CqBTar07AOKhV86XRJSQS6vNM4pYD1W14yudjy3Bq4UcWo/Q9Cwyobdw7EvxUipLJrXVY40aAtJhJA5InTtVaJHlEHXGnPRP49R+Fm+HDItCRzzznPoJAUeZ2yNz95Vd3f8dic37ngQ/en+icTia1CmP2KXATKmOrKiGE7U8MOT2qRRQO/0ffQkBlRS98G4HJrJWac/fTIvzstejFKdYZdFiNAhmPa/0zHawhM7Xjx1Mzosp8bC8ylmi2ZW7tfPBgUAbxV3d22FPRms8f6q9Ums3HcWCywpt3n1U75ljiP65YaniCcob/s0KrkHUbi3PbdcRjaSlwtU/bG3ECQ9vsSqmeik6nb2wB9xpvvIHsdyU2xGLRDqdPi+BfXjvd5JAGxCw7mSiB39JAIbkVSzGq7i729HkHChYtd3MLCDfmWPBMBGxnR/qNFrLWiIBjOYJlqjCNCW2pWRTjAAZvGeq/mg9fi64PwVi7dFr6cJLx60Ygu+kDoyHsQ9mtRl8ff4VCeGh27y4IoEskLcbbZhMbI3diIKJPfUYm0/OeSodG161KI539sH8wVbgs6e4gek5MTSkXEjH3yxlBGn3cNMrO8BfRXzfXOh9jS1a7Ht/UCjQ+N2rSWiCWrPJlTu6pI6qmLYb2fiJj2X0i2AQP4HT1EZbr/qiWuFgnY2sHXztWE3dlx/psIGpcmvC4Cun6WfmZOVmh+DAQZ6wlzeRjUFKLx7FDrfqRtRjm11zjxeziMA42wLySSD/C2tPK5TNmcaQoU9hIS7cAPdgJnaNryXY3BM51Nu/OwqqHqkk5i12blIx5zHaspy2xxbIVjuIzyzn35XMkN8A/QHbuZrdktZLGkeRdem+VreVvWY8vnQDbp+9NHlUOvTaBTLU9bVdP6uzLr5sSN6VqxmDEhDQeBboQ0eQ+N1Trf+eSdBIxvdN1oyx7Ffu/WHJNm2P3jfQk4ZcnUZCQW9QHTgE6k9afRpfGlKiY7QaejVFSh/5ZJvVgMLgCxvOrmkXXF//12R7g/39mCO6A/9ivvVpj9TEEwTY6MenwYEK1/bs11r++pEOjRG7bhBdOb687n0+hSWeyFM1gSGUz6RSXobPp+IVSWYbbjNXFUO+Vb/h+/qsldvAbBje9t306Yznk5sFUtu/WYXyTSppoOmDztY3ZfYJwTyWCdD20O2OIwL0vuRVOJoPN2EaD1uhs8qgYupMpObrThndyZpyY7ZeboCB7PGS7dip+dWNM09vJfq7vNx9VhzX9lM23jHxPBcF2EQhBSGS7Ad9GTru4reaLx7OFQjpVLqcT4XC6oHzr9z+/8Ged2FyZ04dFjHICga1gtOVBO75Qqv9zb+TKNa9+/xIre9xhJ3zyGRDsJToS0aqBmIF12wYG/E9vbBOZ+s1zl/0LYFxhasirRiBAGDitTCcMTWQNQNqJ+OixXVPEAoCwj+aQDRRr5Re1PlrYUWsxFb4DK1WXjRkLAZ4mna3lnBTxJqwKboqeTW94n6Mj1+817XhDQtpyuK/AJnv/BOG4dWVIW//qUmtPyJCtzST9lwGxSG4HyGr+ZWlL2CRHC+vDFQCnhDHasGAoVNUlnN0rTd/670c27TXBeQNw1Zw/yQZvbNTcP8kGOWNpDD87US9FJKzdNQ+yeFxpVSz/01Cxk8v8Qh0ev4R3094jDF9sfvIZ0gIcHrv5xeIVASYU/UJ+wOcDM48YrwyKmQdjdhRe83qwCJH5nFge9hnJRDh1YkJVI/n8gefRGxTH/oLXwFCPr1cLKyUJn4X5MQeNzHr0Fl6sNxFMix6DSP5gzA6vaxvOVYLC0SWf015stdbu9vqYSa3UCafPiaTKQFQul3dtShxoOvtiXIqLGlOeYSwiIBh1uuqbMybU4FBbhSxuOL/xyB4kHw8FdOxBmPXWai4qNM6OZiWBcMGem/U4onoCbIxjpOqkA7Ock6v05ywcjq1i9h7sO9Bt032ediadAuYrhL9Wh8idgE/ZDADR2N+skoEHtikVTHSuMoS7YO9BssgfVbvrA06HxkC5t/lKMBhxWrBDEv03zrH5O310x9FT+RctMaCvbjFAkEBSrVoLy5iFp5Qzlyh6p9bU9D89Ma0cTuxoNSK96jXG5sL5E2e3/c8/AnoVD2RahD53VF5rsNe9Ex0eCuFmsUQSei/ju7bb5QtYHISjPcSFMgAPUjFIR3Pvhhqfkxtwet37WljgKI8kIYskkr1MNUXOz/kIQ7s/T7m5Pbqru5/gBGAIzX9N9gpppP4u9/75cJ69ROCoP2xS6mPj+czYw4kObL8IJQZXEeErMH7Z7nRXpnzO5zHR0HjDqovOTA/382gC1q188Iiu1Zb86Yea99G5yjhGJiJx12nxZM3hqBIYPT7DX7kUXi87aNH1v2oLO/8Oy+wN++XX400NILFenuc4X6TVxXRwmKaeFiF2qxGMHabICfJDqX282FvIkIk1oYwIRv6gVUgpe+x6saTWWcIB7Z98OmY6ZsrFYLltshBC6vGV1gcS7j0wc263VYy+gFX/3XgEjMnwQefM8BnY4RZYZQBrQXfAAEDTlAb19O5VB4Qe03laULNPRhDhiajuURQX8H5hcc2bPBYwSgv7nXYY+ZOTq3ySsU4KeBgKrHYr00xJWZvuu6USSXJU0XTwLVjQzbCmlCd0AGe5vFsTCQKzpjCKsq6E3G5XeBlG6X5Jfsoy487PhVUoK5HMqBMMN0Pj8wWnB9S3S2I+Mv4J7zEfPcmTJXQ1pcqxmvzzZbqiGT5q11bGUjnuM0FiJggI4KBNB4OYbm4SF0HFMFNY8WX7L67wluMhvqdmEcQ+d3RvkJKvsBKGkxVDoSDC4XsUezHhXwjTE/h0yHSZ9iU291bPzDRBvKjzKHqaHK9Bu3PH7/WY1vUpW4gaxcWCsQ4/Yc0ZD3AByfUf5kqhnL5hqkyjtGhOBtPOsmn6vlg1VBaXLxappb6HszkKbo3emIDJtH5NSQhgjOtjFtrChM12WGQaLc2+bTCFAg6C5z6qWFFEK82b1PrdWq3ArNWCPuxcG/a62qaarFXv9FpPbN6dTTdhU7ktHS/bPir0ULCTFINq8VjISzvAxQuo6+C3MHObi8WV7txsnbtplQk0YcfYwZcMoxtHylTuNZPRkwu0c3OJdaGcaeM3z5ts3qDfLU5uwBKN0fwEHPSmzacu3e5LrOwnnpUtwrmRj1KzhvgcG/WuATOpS/dGx5KFfwck3lw4ujDSUF5e80Ft7174/2h9s692qukZvfz+/6GI/VgeodVGO/dvp7gzOoOCepXR6NpYm7Dt+C5xPj0ND44P3JNrYqDP97hsXp22i3I9BR3mDlJ5zDdqjcHff30L8PYLcDHSTynFSSR7BankIyuuc4FVJiSgaHnlclj5NxOxQeR//x2AINtgYK9hiyHL4HDB//5DKLzvPPaQDI4FUtLcGzVP++fp4mxOe+MNB1TOoiQzUmZ2NWtjPmdwMSnzbNQOikZs6RtlS3nVVBetYn5KbSpov1xaJeY3eyaeMHICEE2wsr5Qa7p5clw/mBD0WV9vneNCwZbBVIu1FxtWgE8ep/T0IasZjyktILNER/+YNYKbkQLDBVeF64Ja29nmY4LyWSAz/qxgMf1MH2X4eQUQ1r0HS8B32PQoqHEQS6+qrhBDxkPQZrdHIBU++E5GqprBwhmFCy+7MwtCbZyvDYWliwU0Hh4PztuNqZAXqVudTdJesku/6/q3cmJsdGIqGFlS9cZemxz5otDZnNaEGLkqg7JBdAb8xyXjMJpc4lRNDWgcjWkNs+rcXKtLlN1yvz+akc1FXr8hSbFoa4if53Crbi0KR6av7KJTMZxsCUKtVk9z4aprQNXlymTyX5QpLpuf8QNpuUHn9oMTL4RE9PBbkOxBjcYAzrltxzFR5YIU0uB2WGscV+GDzmxLz+JOJy5PSi5+d3zEAgXM92Nh5LPB89mxQ6uNraCeicN8VIXak6TxWmHCBi48/zjpc0LUKDtLqd0DIvM8yt8PuglxmhrhOEJXH2NTOJ8bv+8WIBwPPX5RkSSrYk0omCNbJMSOiAMHX3jIcX+Evtag7Zh6Ygt1jBbSnGNcEKHIiQw5Vo97De3xNw0D9k8KRYVdoQY/q3dXQ9FIe0uyCDWur4BVcwqvZ85MIFYUoJblEks1ZJvXm9jD0hXgbGHx+EJ7l7PUIq1dhDcM2iLAwaghxoOTV5bJlKlWL1ibT7gNf8iCLbJkoFmAQa0IXnCYqw9psELDMlXDbPC201x3QAU9pJ8wN0AzYu6qD80ma1j4lYeTE1zjIhJhUp8ZT/qvKD+b/2Qo7ORyO/PJV0iZLJPVxHcLdYluDm8yDZvP6SeUt4xLRGZvPaswOMuJ4XfjMXgcTyR5AmeqPIl7lozROAnvAzpIvFRGXxPgcKobe73u5FRmpHcSkmqf4/3osg6GYKUJzwbQvM5tYNod04BQY0xl9LWJESjgaMiN8zleRxVaOC0lgsq1FGj499EIm4leG4H7AQcvonqQugRxwaMMW+C4KlU5L1ezZLq8k1//Y0TP5HnjG7Ut+57OF0gkxocQjiayB5KqD86shJ56fKRGJEnMc1GSFS5LdY43JdLnkiPIVz+H2XHPTLoWF2CpvL6mg8Ouq8pR5zTnkSM9yYV5LZhiZdNpsrd5pUeQJXMp6JEgbhpCyRMsMt2yKAMuVp8dBMwS4310BImv6EwnLpc6kRrCov04usrwiOcy8/TzozZj44ohdUpaSmo1Tmd9b0vTmnkm7inutFdMolQYOkP67fGIE+7TQXqcHB71exwQ8iqCGRej2WNy63hcinSF1eopOvis901+zywMnEF2e3uSkCT/yxAGBcZ6FrMPZ05rUjONLOUyQ9j3yrli3dWoAQ2KEztJ9Yt0EKfTA/gJiydYmFvGpJ1eNc4EnLkV6VTudsXZjogYp5yhaNVnukjcTaJkmS1HqE9vt4YXYjEfbKLvrEZRQN+jlUTaK8xalna95Lbp4aEpZ7l2mp6Wj+vKLwqykYBJlloqYHK5c9hlunJ9kqxgPVt9I55K0TEmqo+XQ3GeTLJMBSeLohpJrYg8RJK0sZdHE7GgpgXLfQHyOWZcRLJK12pe82KLX41drVsOrrSOHpm4elGrNfsLlbW78NnGMTNfV7Ak55fzL6ejEPZadcun1SFmDKt9ZU/EpNMmQBRlKTcoArXW2gkKsZZTjEWUMIRiuZXCsV/5WsOtLhcKXcvBsdVicR4FIZH2PjMw2sxMpxSg5MP5P1/Zg6iYJeHOhDaSdzhPdAqvMFJuuLq+SsAorMn2gbo34NKpxWuHiquoZc65gmCwQ6RQ9x6ZL9IDSfyX5AeJmK1pnPqh5B6PD7QJJCzJjd0q0RF/SwIrZC7ZMSZWkskQ5vUVmEdmZpAxE57krGgfQu0ygCFgmLRl3pEtRJkpHwqrCMWjXytTdd98+SGE57kpdapWugEwMmwoGBVGMBXeYbX1FuPqDwQnqeJWWZNGPAZRchx0lZMy+8S1ZWKdbCP2Dt0qf5IFdsPUkOVQNhe7j1dOZjoiqZTh0gnlVHKC8iqF2I3cikieJSM3zAmyXMsOiV3ZikbKZbCFmDf6pAknjhVVNqqu7VSbI8mrZD17ZVY2qi6guYEvq66MbJpkXN4aG2JxwrpzfO7EqAEycoz/EUKYruQTYBIeQEMYUvZwVxFgNhkaTUM985iG8dpRyMeteiy1eW25kgBdkouhZJW0OvdDJXdTGLNQV6cYnTGRHany36nrJH3uA3lMOeoib/dkkJOA3Zh5e9cTnlDp3iONhwMeMn322nqWO4fZQISzppMv2W1CPr7nghu14bntKsGM3nYPchz8RLjdY9taWNNYrQ+KO2CVOr5639XgA+iGDx4QrWCPP6L2Unx8RfqLk0xXxVksLSCmaEtByJ1f+vwy+4FybTkrqwz6W73y3flYWnM2s6dsFdisqDzRzs33A+WzAbhNl4FNk7rNK3ZSBlf9JXPJHbrnXcjsB8rqe26FMuhvycnsLL0ZZxtVt4qTLHWLOME8V9Av5dZwV8QiutywExYeRm1d1QgkKDhcjNqvARd/4hnp6YjAejUEyJPdsk8dJ89iaX27kmofOCpIHESpL4eskfUJ1frPm557HdbmdUUXehM9s5qCW0nyQllX5BBYJEVwBCHr29BYgxaeZSP8lF+cwG9xAPI4NC4PxwXJPTaRiFIG3RQZ7IDWj35/QH7fJ54rv+ouuuQ/Ok48VfcaeN6PuhAC/eo5v31PrU+ofc2I9Qw00hDqRQavsEp2/ykKO1glmztm91NVbzPJgVSraYusQzSNvnh7z1WeElpXsvAkKQI1I5uvXLMQ/7SF9QIER0hS32E5DZ+0Ce+hF9xTknztST2kuTDekU/YwRsNveIRGUEvyCfg0KtURPspG92fidDVEUOigrljGb4COt9kIm8QWRHg+q9dRUHNM/vYfXakab9zA35QqyfDcXhYzCVSxB+Qkb7dZ/3u7HwrCaXUE87FZHnBUO80JTjI4RcE1+LaTCYVU1k30kzFphkKs/4ceurc4LAxtsjrNdxbW/nAhlOU1eNdX+n11n6sxfsC4u0aH7h6k5PPxFCqYaO6YzPp4CaoC9+zxeeoyQD9vRJpaqkr03tqsZAOr1RQQm4jqGveYDa2LWygeRx6KD+v386TCvNwj0bvp1IQbReAN0TfqKD4QbMyWXe6m7hqH2kQ/JkmIgQTtmvLHOh+KV3Q8oNC8Hact3pw7Chtc6wc/z/t8IaWPSG/O55zE0EvyDuInQKzQaiMkHU6WzBZwecIvzcAYeCi0ugpvx0lA4AB/k4rE6dosab5t1oKgezI5pmWX8qxlasEPFTu+e3ooZlcmLsJvyhJHe7fFCsn8W1X/uBNCaV+zev5OzhAlWJD4OikUaCIMXBb8WBtsg5Hf2SzlYtvR7q3zM4D9wXgp6Rjctdv/HMFQajX/wmyQOTJY9PdM15vCpqqlXmfoXrZc53B5Dx8ZTy2M7CjU3VgoYpIkR1r7xs5UV3F0ABVx9XNjras8loAHtITcg4qoZpoqVQdSe+XjriY/CQAqtIeu4D/txbAq8Xp+qky4eewErLmIzpk8zI9phsLuKCkxiMOE4QW4zmH58gx1BvPImU7/60c3k8diMvQ4GG/6ElaRY/StGoFi4fJ0S4pHc6iftSXqxhPPGd9H9RVilVNleGAIW2nsI4wE41yYh4fDnpf5KXGlovNf+e5/NxSPx/pOWDlj1o8RxCinApdqzkUtBYrKoBWYHMYqRCwrEn3N6CtLs+q0r2Q7M+DFT4JY7EO3lIW4BzXS4VdMQtE3uPELe3jnmXahjkOVWNOhVmZrjxsy5+fQbuKc7kseh3EKW2V4KLMk1TMTHFiAcw9XRjjn+UE86Jsb9dEzMLaY6tVX6y41G1LpaPPOdxeNskB0eRFOVlUKWZBQy4AAGtJYtt/pyxRnBZRpzvK+dQBXifLegSfhe3xjTYrVItjGf3RCcLKK6pEmKFkwLCJ5KpQUlk2dtxYQupZvDEMLFqG5FSP8HMrO+0OIjQrIAWGw7KLhlbJegADgZYFqVtGwb20u8g0EK7rvrx4V3DVvTeDv8BKSFnzCWWw02nHwjFDCULzrGeSkJ3e5qDp6BqBsHXOO+TKwdKM9j5ARAhrQqstw9fgcMk1Poe7OjUJE8b6oCR5MO29AUEJa1lBd4fVvexsraWl3lyQVhjP963Z6d0Pio7TZQaIhPnrp842IrWwiYiTE1VgX9uQ+VY2SzSMSWZbTVphJIMD0Ow5eB9XTWL8PAmop5T++obLbofzUK3CZJpYgWz5iqFH4OQB8HVTuGLrsIqcj+CVPYFKfCROsBh6nARznhyd8qdNwyfyLbzt0zIKFGYrSKZ/8jwATnuT2Lj6YNN+Z58FLLfM5lOvhIIk4lFsRweIfvJI7aw8nmJexQlOnXcyAF9aApzCkJGSlu5g662K07rqJH+AfZbT4MvE5zDiHBU1bV2Qw954gBm3WD1H6nsnI85ZtXMWw0IKcj6MV6QQlCr5MCeUZrdNwIUsj4X/yOX+hGR0Uui3s2qHXHcs6dYIvH0nzzlzRRJyTAbhynVBr3y6fR9Ymvp/HIPFa2k9+bt2XBoH+BR0VJvPa+26JupoQu9oNHnPdkqtoQ3NksQVsYZw3G4JRVeLEJpm3GoCCwnNP+iqOoLiUqgBbNNYo4OFX7ay2hjvB22NulLP8FGcNUxzrXHlMCD2yJY0eEBcBoAaScXt/PxnAyO2pqCxqnzWKMTXsIEyjmlxlZwF7Fy29+goNN4cHmkB+y6FKxaLX+w7Z51Jvg98XzHt4LE7KcTdNuHXzChaav0IHJlonlU2plMp2YFJp5CuVB6JxJloXsah3eBGaPJQnuCIHKfnXKb76H2UfruTNLP7RoeR8SOGVEtnMnr2eMgxo6IrFksgj1ZVyXYY88L8dn7qTcQpQrLsBDqZbWKLypLr4VIeTVrsdrWKtPWkNHiEv7gAEUdsV/gFHGloje9skKjMWYK+022awPWY+yf7TNNB07yzAVdDqwm5Zp24kB5VrpEXWRoWraeFfW38Yus7jrS6UKACEQK3lsL5vtDB0dlvPVJKm09QnYWzkcO3IN16881UyUYdRlmXB+fIi47EYKhFgCVP3SUnypoN+0KpbDpqUSRxFNZoOpcKutzURQn+PVuy6aAloqvriTOHrUFSggbYCCJU84Ut1f0DDLqQ1yhHwhI/im+4CCshctO/wNLq7FGWpix1XkqngnaAp3OjrLGhQb7E2RNai1YeiGaqrVYKigbX3AciO/75+UovnzXJ2VqKplckvXUP9/oIYyrXm8im+2mzCbcunc7lc9UK68BokpSX8ewz09N2n4+nXLPhdKXoSAEIFjNTlQDvtAq12xAQ9oAFtDNvZ08rFFeJiBAY4k2BTBGLFhUBGfizXmLLqmDldQGfApk6vNV2+JPp9FmlYVWlU2CSQfokotWkAdYdnztWrABA/RZAEJzD2QljhJ3Ih56S5JwsYdfiXVudbwpXSrWLu8c6XF3RPvgCtMc7eKi7I592KZxg/ORJnWUe4Aek1LRe2dRdny/GDIjMwAQ5B7iU3ZTx/spz0mue9hJsZdyn9nshyjholzvbYTsXaj/0kNIWyxSSbpPBMT1kndPsKKIyUdu+0qHXO2K5TMyqlFI4lPzYWyQrikewsBb7FNjFaV+1bltwKGS6eU0luQQMpstUQXi4W41SxuM66dGpXVy8k68Xltak7Zlpe/pc1p8uLHWyXrcvWuwsrq4fqibC7CZZha8G67CFVoGlXd5sZ2lhC4JP0kmkivDh3gzQHtozBtfAod6hD2kGEpNWqLkX0G/70A+Ppx3YCP18B3Vw0J0bCpBhTg1wpvAHOBeitjD0ix4ckxxNJUpU6yMJB6he8PGcqt4Wgdg2NwXB9HdOPah4iTBkKOu1xmYLDBEQoVGqC2vQ9W6uaEAsd+f2uGTADLwpsPljx2K6Z8HYg06QtKD2PtyGr+49VSCocD2QlrMXUMbX5npsBj2fQDtg0DySeeOOUQJGmO72TSITS4J2ntrgzagZj8Pli3mAQfHVsdQq+9soTFDYA4CG8cgLJoJBtu0NcARjIW6fYPFhWVh7g8fnWq4FUcjomWNJ09ImFbwoIpC5N1z45gTIwYisjLIHZkelOShWTyM2j1NqvqJSR+vkcHrdKgpTFOctvu2pqPGYetA1nZZfxJ3jNjkKYQoDEDoxxdUtRi65zdtuSfJ6z+EEWlpaBchCoqFKjxlf/DqsCFZgnNiU+S1tGBWkHO3AqupmwMDrNhjFVre5UAJXsuXhY/WJs1/QDbz2dnZpmSV2v0Mnj9QV2hr0QDU2ZQkfyziHoeAbEglFcuo3V9DhaqYaCKxmwIKeo0ow871qcjANUT+8rMBlPVMUG6SljVOUHk9kA6ud0sQ+PSGzPecnAokEOcpw6heCdqNoJTc60npGPEpVW4ghVcwT29guUHhucact+fIqIzUOFH8nouE4vCL4umsNo5CZZZ6gStPvPWWCLKE2oUKUezmQac+NdAlC05LPBRgRYiwxbRuHJixP9AotufLaE9lRdJ+cRfQHGXEMrBC5m55woWr6hFoUCzNQUmzBrX6MXtZiN5RyP/TEqHFce20dplADtXA21ChyyrUasEQCsRoHmZqDR91GdgJQeJ6NmBbTVQYUbtkypESdc/v8AZn1jrDcVo5sClm5rdDAPY5d8jHGFNpQOnNnorY052c19jSmAHXLcood66GyfhIVOJccTre06v0uYyiW5q0QRAGq5tNJEWUSNGxVNAw4EIJYsOd+GCb8sVBgfVpUL3Oi3bPRyrKTVlbXNyp9GmzwDVSdsAXKPTXGvvjAbUC46DEqFz1RAs4NyWAPdBQHo8CfUiswn01m9HVnoRVRzOiM5RJhbxN2I/ajhN9YhZLP23CjsEg6M2XSLq1xj1XBjchtzsSkMVw3yeewfBLGetkyY1GsHE/lZESgOgAFIm+E+iPpWnWT3M4Zo/ByiT592g3PVKbQ4sev6MifCvt07iDQ400OSbkFVEgLwtJ1jwJblbjl8tttgDap/h/HYPHqEJkwy+Sjup/g1CTGMQvptY7ARjCGDI7x0Myw3uO6j0ZhHBE9OVqibva5CfoZzpArTrgdtofoUxjfY3oKaeBbOUKnsN4E26szlA28sY1Qt8TQhihTBsLUcpwbUNBSYoLkY2xuzuuwAXuS4HOEaIhZGBL/b8Ny0aGzSkEabGelivTEe6EewX+033QeGUDXXJNs1sL6IPIsNg+ZvFLzSaFjB62HmoiRsMGWfvznRzIXOIBnaehBkMPnYJA42J7QXMt9D+dz1YrLlHqsb5+Kke12cdK+Wnb5PHge3SrAdkx5Ixy5rOnAVdcXpzsqolNHhLn9qSZ39e5sxhgBD6z2KubZi+H6jG4vaUyEwaIDXH4cDnCwmRtPqzsyjoqt+bdqrgj4MozbY0Xwcb7yWT2PxrMjJol/S+fPqG8wwWYwDmuwU61Z4jfJaiSJHJ+KxPbhBe9qsRUnSI0ab93Daoinh3ByU29seIIxMm/XsznG0tSnwM/zXDiBt9ZkKTGHieccs4nrAxd12e7TeJ8DxzRCL8Oi7hmBNFR5FgiB+3ZyPoCpPRkK61sL7xWPRJIpd4tJd77SoaW0w3UovKaCUgMjyWEr2BpN8Vk1pY9EMgI4PwH3x6IxnsJNJ8eWmF2OwIzlfI7byBKr5Mz7wEAtBd14SoqUqaDF98X6+NOuQEyQChyOtuc1prHZAVaoyRXqB5CFSh1ZhUag1T8b0lRUrTZkfQZgfH2KcFAdVG0c4h942kUnQFcbiBb4D9rm9ssC3xcAujAMADR1r0A0hAlpQjgGADq1UyqpCQfAMNi8FVcVY8uOoO7Bo2emI8mizWm7PZOOaX6/VYfyIMc5i+eZSTaHQIxhGDc7LfymyBNVGwelGueeZ8amUSrHR405LP8GjF0CrHxPIwbaTm242EejM6kG+1LYbPHF49k+jhnnwV13gE5kBkj4y5ul3B4KlDwnBypUiqkky7tprSs/hcIgMfbJ6nq+arYoYgySjDPshs4gsfByyMnArX59lQm6PBA6511xawIM+k1ZVbPNTrRVvHBpiB4uvagKb8ZzAI2IOsc+l+nA2fUuh0qBQwQjlMjuoRIAuBYLboOOmVtBd3NhrplvbJ/NU+ci5fZgG8dVkbPaARIlL9ePg39Au+U6fAs3t7P2uG9vdPXxPB0Yw4oZ8+HZOU2EK1YMCoKklAk330Iv7cq6jnBdOmrVHNa5Gn54smckOzqWNR0hsGg0pGEz9Ba314qEC+mogbP/AtTsVR8iM30SHQ2J5rh+OdsKoBLTAMyZQt6n+R+87tv29YeZtyJgEpAzgoJTmG/nH5VAxAmRgxL64D4wBpAccD7NEMbHTe/HU2en50b/pL+9X9vKPpO+9Y3ZL4lrRwCXDIIA5QMRagAhDngAKB05nB80Tx7U/2QXdMf7NwjNzNj70vgL7uef94A+iAhEWPMTmdAG7Qj8h0GXVNFnnQFcIQfVX7ku0IttZXiK5EEbOFuw1537Of37rrXuugvIB7a7tUXahnkEgl6Zu3D/EALTzmQa2MBOHsVurz/QPAq5VSBwkxOTQYa3gJ8zlPVNvYFwD/fzQTBaQng9AZ9rRKs6rzR/fK19MvcI8HlBIVVefS76UyC0y4/zqdLIWzdq0KJ5Vx4k/i/JRM29IeP/VRVOyW+knd2UMUL22TLd98nN65fWvvzaYTFXngECDMEHLwXQMnDrBxNDfKUvPIWAurj6q50333njbaBYom/DS1/dJIF03wUMH8j61p/hrFyp6bxd9IpyKBj8Oj535DTglMEOaL1hqexe66nHFUmWTwKSJ5q9MSg78bve2ibmvhVSiVrXarOlUFxcFA6DMJBm3s0BBwCfjKBIDBXuYf+OTM79TB4DV7bX1BBmmQDrZkDBVpc1vdg5ZoVuVStBabFlJVH0Gx+J//9F0zjPVkp5sB/9neuyFhiC2bnG8rkBRXz8E2u0GAWs4H6hTavMVQm/FiSpID86bn28DuJSGn2tdUvmmhlI/6Eg8gtswLjLOlhraDMCQziY2g1ChRQQWrz1LdFunZsVX3rbPvT1mcYS15OWRwlAZGbfBteLvaEv8eMGPuSkW5jm7v8zkbe7wqDIRKhtFwnGS5ARMO2uXhn8fhJgYP5Qm/mEZamz7Fs/9JsOjJf9XEcTFxYu2IJXv+tDfO9n/XJsBfum7tv5sn337K1m9/wOLNDj/saatQicymyCqf5J2VylfDf9PJi6fg84ddnqrVAb9ANNjKPcj8KWOi0OW8VyeSzxuTuo85OuZpyNuVgKdCVhH8R9ajMz2tWBndp4AiLiOOyfqs7ajRWzGoEPvqqu9zV7V2mmfR5zhcYa4/GlWr+kKSqbcntW2s3pPOMGD5ADcZ1GEAXj4Nj4TEnxlCun9ly8pgAHP9jz/lCP8Fy49jY5DfRBxFGy1EC+TksclugmD9lvafAjO/DSYBu+/bpj9Rx8DHZPlA2FNMr5jTZCaSKEyQ0N8GLfJDoRmzKo4RtoQ0GTDcXi7tWZS/FYKKs+IkbcylpdcWOwug6+1XD8VN+82RTpQaMQvU9rKSG9+XKwVRhjrT87P4ETT/vnN3QIL+w41kRKc4Q7auhiuQJEVCkV47FPZyYn5x8qJT6ZvjmRlyAVEJOC0rCwbnLC0WzR9S277adnh9Leew89uLrNi0RZ6PMwybYvW9zb1NUukSffu3QSp+81sqoQdTL4VodSR/lPbfrw2VLvbjq1+eYDnWpwEId9YKZYaYlqq1w89Uimb9p1OvaiFm2Dd4EtnaAgArIqilQbqW0eQj01M5K/xp+h3ZGMg0EVFTFS5INMgenKC4K5mAaudWnneJXXpQ1Gn6oOl4KqRaa6Zu4BLXqkdtWBeNdy0KvxdwoiEYAB7cr59GP7dhwlzgxjBpAND/zzWRXc4bP32Ex9pPWw08lkguk77AQGYAj9/+tyYP1xQduCD9LNvHKOZNID4fLeuKJPHJbtQ84V3KtLAk9K9gXVBkW258IccIAoatqZfEJIrZgDEUxZpHNtEaf1STit2B/JGmy5hyXJWW/e/ZdeT57eqJPo5jVsDeZ2ltJ5iIUQMw2Lh4VcnTsbAa9JV5KWCMthtpz28mbPrVgzBcpcwdYcrQ/MrXILqOlja9HUb6VpqfQleRdEs3mn1mZZp3izNqMtzBz+h28ksvDOd+C8aiPhQJvQTCw1GihF5Lq0kO76Eoqbya/BbQomDhU9doDUwqlbA+agvQaW9NthHSp9EzO/8FR/367hKLmC8cqLyeMDKVcJtFXuTISkU4eTsX3ZXYbDOjL/2dxwgERqjGSlMbCXF0a1+P5qQ4E0AZMdD0Hg+pJ2U4Yi5ox0qSYG8peitqOY+eTmHUoHc2nrJDNaruqg32evo0sMzyWEvfpz1wiQcBUXvhHNWKJ6+v67ghZZQk6yh7ke4CgKBLZNE7XVgYziet4wLCkW9997j0z+UWOuFgXZSEXA2PaKw3S3b0SwV11vIdcJbG9KMost14k9K4dRm1Bca4NGt5CxDZbGU3VpHsmmuD4x7cPUYEfiqZYUZMqgn1F1wBzuQAudE7ZifW1kqxGQWEfsWKHgkoW8W6ARDZEHhJFGcouRzCcsPmRpJkAmmVoWktUuf+ZrjVKBba7apwovEulS4bC9jIwqyhCQqmHbq0ttj9IlLBK17Wt3s5p6f98FVetQoonCVB0MIeonRb4IhfWydv3pJGnKE1ugaTVu8VeMuEMGy2Ldb9Xc9Z1qN/UUee91spzvUHdgD+WL26eM/TzEnDBS0WeEmrs262DKc/EVbO3DlpWle1nKyOjO810YtRjuIWUFehQhsC3RBySn+Y3lpFItBMlmuXj1UzbSPwXfoalIz4itSdcwEtLNo7gKe3uvnD0P9vQZxChmCFUoIe0cWquXqukbKYZhsq6O8zf2ok4IS/GkCiza2OOBuA7YxZd1MQ6wsjLGFwKKchB5SkRlQiWBVphSIhspeysOG79XNyNTQCzKQtK9jJAmihEQp/uxCae+2kwkFYH7dD/TThq4dcZ1jlSr4CCSGRupWTjDuccBBFT6K92x8RfWlJilw7geQc0VodKQmnw8AZyANLP9K3tg+wNl5F3WfOapXdsal2htNl21hK6nDBBGLcGkduporCTmE6J8eWNYZZU7yPefc0OT5MoldUBs2b2ycSxHyfVIaTvnoHk+nR/f+GUO1v/D9zs6bjKGGEnyqahLOpmhL5luDFWNK+HEeJkK1AgDi5+uDIe3HoBRvizO1JCBGjWYxcFwCmOJednvHlsh1lB8S5gLWT0a9IbPs4GpQjnWq7iOCSMg8h3Qav1WP86lxwyzKt10C2zttqk1jUBaq21RlPgCc5Cnjn+fKrHfD12TKpaTvRj1OOBhZhUzSEzxcQiQYhwboEcma793xwakC20LyIb2wKNX1R5ILQY4vTv4eI9C+2ff6OK2OcQTNhrX92ioTmXHaIJyQigjDNQIWvdNeCJiga3RVmV1gq/sC9QPWNE11YNtm0khxZDEGu5kDiM3KZA8l94V/vxShGmCFNNTbQ/2sfzB8Zg/9sbjd+ZAIvtus1zW7a6wND6Awzok6N1hVveE0FKelUnPrTSPJ1tiKx3Y6zCs5fNIHC5uD6DQse1BOnuSEm79OhPgFLsopzrb5vbt7HaMnUvH7WynPCTS7L/9UHeu4ax4J9e1VaXy1pUGHJo7UL9tRRpZu2nn5g8I5ZLyDtpwEZJoxodYxGqmE1kPYm3U2XmMaQjSDjZbkwrMQkS0DAfL6r48ZWazZrkG58t3JPlfuIL2cRodarivWg2pn+SLKvlgpbpApMMBd/sNLVOq1wIY1ayPaCuplmjGa1k1a7UPUkP5G7Lqo1DrguNL6RFThg40WHFTlXxldVSIkJxwgigVCEfgtmTqgtaWbwe3L4l3Eq6xVAp4UNZlutq2C0TZ1rg4wa4dpNX10Y/Pgd3sKyncKbWFjqLLCu+eobBFxRBkf5OxzNon++2aIQrZYzgeuPsSE14b7QItFR6FN1oC/eD7OdnXBC5ewcptqjpQIe3VjnTSWCT4yLPUHuZYm+Vp8xYfJeDBHK765H27+a2BXxNf6+GxQa7bapdCxBFIZepFVHkizaqXFWsAj0k7Sfiaupi85g7D82VAyylBFEYXPqJOzAQ5ilANHCyPkhOywwQMjmAKfP1Gjjv+GF9vEeQKctakZH3KVqCyHCfuwXAyyBCRWl5FsK6UP/DxeGByiUS6ehwwZw7wPs6bz2tSRS58wA5VK/o1BfFIjLx3N53M6Ln24QJHscGVQOwhspDFEj/s2gx8W8Vz+4ptPU93vlFz06f6ZkRRHvBSWGLOGC581Il2Hh24vSEQThd9C3mwws1IvpMdetG1w0/fa2BGhRcVUoy0n9TLvaDQv7i3Z+ExezrVxH1UsbxO0CLRmQ8hZlh8aqAoMxUvUn8aURJqAtv/Yz3JG+YedwVIv9ed1NbE+1azPQfZtdBMK0riVnAWxsazlhTfPoo9Ido0PLmjMErNGiFdSSMRMRgv1gzmu1bWqH1MsyLesrsfYKMYO3Ykn1y//upKt8fcNkIkG9uXcTV8RseKdu11tIAG+zfRftpdZaguZrKiWYYkK/rkE9SNNcaUgbGlMWr9to7fsUSOIEiggnOP/HDAs2B1IwrV2Ettb9mJWDa7jvb6BbTNvEjuKX4Nq8Mi+sjDsCLS8yQAc04k3HSYdFTFeMVoVa0depGs7GCBKRV1QBs1sgtjjTGsYnydGNfLKBoC9wFLurCuNXuFXhs8TLLGSpla9XqnMsz2O5Y4BBDDs7o3CWgTAg0dMmFQhTYTAYmumxgwKg4TBb1SltmMNZG5sPeK8kx8fFuJJhVklA5XVAVxh10NAtip60wIlOlVEwYufWgiIOwJEwN8+rMTNQFuBWLfsUMmDggWxsQFLqtr4oHGkrnf8IHPXtnJaZzkaeD5mFtZWl7n9AVAc8Msts1paDY5arIcxsbjnWIPjD0mPtaPMxmZ8sxJaHISxu4s9lovaAonzdaC3QqHi6mJmoMJCLLT5DQLTueFeo6gqO8caSB4QF7tmQtLptVdLtTuGuT1otW0zCmAqjaIG6o5Br1BU0lhDYOnipbHLNxVoDib0XnLiV0R6WcuHKB7A8w5Ye4bndV6HggDPcLasMncrbNgjT9ug6QgvbAKxvqZMhFqdPCYiYETgxeJXAtuLTsIp5eYII/1YQzCO0JTAD7iwYF6mjMdpw4BCJhRbLApIgCxolyww3CeyHHfs9bWggmRx319nC/HQqk+4wPj5npw7CQfzcS2a3I9Hi7iEqjQAvoE6K2GiQYejHBfJCKUTt2yBsG6DpIClgOdwQekN3+25GnWxBqyIJDQ9oC5xwm7vhM8rQUM9JJXvvkVK5cQUwQvU+KgCMS1NhaJxn19WqUGy1ZbF5S/YLK0m7g5FhVrNkLMdhw2ob2zpy2uiaSPu4YnJcuJZQ4lz+QgQIhpjUMtDgsDGjDTPVa+PT28E52LbK3DCZa7gJzEQiYsb/fCkC74gdELkwleqk6g6TrUBG/gOt3O6DwLmP0cX/c+CSFmEqRDDV7QfScx5Bsf9lYFTNjExFo75mZg208S1c96gDPqeL5/CBPBiMC6EIgiFi41hLiIh/hICS60FqlAWsZIDerD6hbVIyYuoVdSiuvaJKNPVo4/h1dAkUhAkn6W7GVF+7MnZ1U1VAUNGTZilPtSQ1PcBHvzMGXaDED1Zni2+yzxPEL1sbVY44UOG2Qw7rUS1jN/hJFG8aEPGm0M5hrEQkMi6PNK400w0SSTsdRG0WLEisNK2yRI5GpfNNU0rvUVrvdV/nknN/q6FKnSzJQuA2vdYpbZ2OiAbDlysdWnzJVnnvnyFVhAgu3m1VCJXSO52KpijTNesgkmnhxmHMUUHuxnAf6sejO4pNsJlsl6z5tlNhu9xJ/XwlbHzLfAQossxlgJ45VaZjmBKrisQ7yke3lZ9/nCl77ytW/8n1f0F2lW86gpvrbEPkv1vudV/cdGm2z2gx/5oFVe06O2wevWpFmLmFaOZePbndXBcRPrpf0GVKyVeG2TLNYRlshYP3lnzEpKCVmqkyzTKTLlZOX4oHkF8yzXBSVlxlNULbDG1D5xt5LWuMfO1lVVTXU11OSufsLqn3QZ/KdDQutf0cC06YOvVCoYc4tA3uyQJIUXdY9NesCPDHE+AHfeMngm5pYwTjOYQtFQcNqPLVHeEEKw1IgkhrnwZGvggQ1mbA1WgllmzxBmGm47VsVqWJCbP0yA+4UnGBaOYIKPENbm135yG6KiY3hsuyHNxsUnJCZxSJv9ySkFUnnIcy7atoJca3ph/t/AdiJyBxe3vIKf3q5ixTnK6UTJUvSZM08+I8//8yrLD+h2sjz982FgvpUYnF+VqrVUg+f2kQqiZsaFcNxDl+tS2KOU+4grBi2s8GBFFImeVwUvuphiWTtr8rFEmzsEheZpct8vhyy+BITU11+t0PykRonnGZhnz3z/WYWDMhWYqPOk3fsMqmyk8SuM+BWMc94SE58DR1VwxA7Pnt2KyBp39sVSiVsabxndXnpkVuiB9r4oUaOVGZ1hSthDRgOdZ7J8PlT69XHL4Qu/P33FEr7888ZvKpzcryugWIu/lKjCxPRyvQX7VmAvKv3/KyqqaPqvQUMCS4oU3Wk95Y0+IWqZPSur7HLK/YdQse0srGgfuzWlpl7j+a221FpbpsxZwrJmy54jp8zzaJGiU8fWJZpLlCkbuXdsP1Nu8diPnE9MSk5JreCSy6646prrbrjpljXrNmzasr1+7O70l+Z5pw8Oj443kLWFcDa3vfL5GE54SYpmfLTPJoQfClO7XCgcicbiiWQqnVFyni4US7P+7ldtqdWPT7icb3JxeXV9c8sLoiQrqjaebOlWu9Pt+T/XWeF6KD8YT2AYxck0RZhQluVFaQJNbfqOFExJfLxoUCyRyuRDw2e30bHxCYUSFvkqk1PTGq1ObzCazBar7UY2dc7wwi9fMNKKZ3P5wq1sCrVFRH8sfi+bz5YmMlmSgjSTYzleyIuSrKiFtuuPaOO/9BoY0/b5b03kGc8BQ0RMQkpGjlBgKVEcnoqaQENLR8/AyIQpM+bzzX4dazZs2bHnwJETZy5cuXH/J5lIptKZbC5fKJbKlWpLrX58cnp2fnF5dX1zywuiJCuqphuNZqvd6fb6g+HItGwHuN4EtOU1gWEUJ9MUYUJZlhflrKrnd6SAEooGxRKpTD40PDI6Ns7tPFepUk/e7GKzVqffjBarOnu4THu8PoRnBUMMz4rGIJ4vkkylM9lcvlA0kTwLs6I8y+FkeZbHC/OsQJDmebdINBbHEz7PShNCzyIpo2cxOaVn8YLTsyQZmVmF9u4Xyw86XA9Qm2vqdV91oVgqV2pq5da3XN4ii7LtzpTq1irI2z3CDXKBu++24tyEjqGBJtSFlcKxFnMtCHa2cpWvQhVHY+Gf3EzbPuO/C3MxneuxEIbu1oL+TgrW3K3kI8E3IKuEe1CeblPJ/L6TxdwO/pgAcNdYQuj9jZwxWLwz7iIdk1Mlr2CW6ms1y/BvQKPUCltzTcbD2Aqz6ouSpy/v6ax9qURj3AhB0lkpu8nCRBfRBjS8tRWI0QhKpV/jMXn1QQW7u115f65KVdWpa2VjQ4ouTge/Zi7hxrzL2jspKZWXhx29YrD8vGRsADhpeX8SUiKkso2+ThA8/UtQX7dJgQQVMvhGjBjIUsjrVm7onGmrtV0gViMopY8NhZKSgXK4Juq5yr5fstdQMhihbHPwcDckDhA4FE/Swf6epkbrdpVbtO3+NXlO26VxpaFTey1vh+scWnPF29SCAdq7QtrCIu4kc9qxL9GTbKxyw+4S1aV6GiIGQNLdRWDQxiPVmQqaVtQ3NUt/qNI10oalFporjhuvPEHL1j4NMZ3v6Cx8qcG0XGaMU8PjSX8IksjG/5lOqlMK8Q9rwv3t8OUXvG6NmH3KI3YjHyN/hfBObuIJut30BiWsQw2CJ0eUFwOpKOUiovrYNqIXpvCLexuqJrdUb/jGL4JPHPjbVS2IqFKzbtTIKOpK4yhsiyc+KibSCpPO17cl4xqTqGSUxiVNGhnTRSr5uVy7/uB27bG03094a4eAFqr7HJUKOShCjaY36I3cR/naO3RLvC962RtTUlX6S9Bl6WAINZWMalRr0JBsiGZjfJXIaAU9LwwPLMUHhkm7e6/lkuizRD9X9HTdIKVNdU5m1Gel3ukStzQ8MYC2UVb4KrwxyMRQIReLW40BJ0ZT1wLiEz4xAjWMIWuYjeuWcalIjYyhUw3VkxQ1ck0K5jcCTj4jRBbadDmbpQaIj4+kUUPTk36nzXazX2Nf46L+Xnmy7Fsk7a5qZ0Lbt7bbfLytSSVV2i47npSPdlqdvaUjOxdvQyeA2edOJGq6X/gyM4Fvw+fuOH4uwc/z701Nu0/jkbEd/CybSasMTLExS3MoDkWLI700r+LU5H+b+Z9GZz6cuFVt9DOzWTUo7/t2sPHjHqOxWPLXeR1ld9gNdRjHNxslN2xy3BLH+hsrcA4ocRHipBQ8uuaYYgFAa9gnts9L0FZOuuUs/7vI6+J1Et0mJC8FNZnXTOBSxUCbbKxB1EftBgKmhHWQ2dO/M5dw8jat3WGkGsx4z8EqSYsZO/JYB+GgY6iCzCfiA5BaMFwCLGM0VKA8S0MVljyLhJgDABjAIxCodwXXbiZeV3u3Tpgj7zt/I76FRflxHiB+nC/cz+eBVowRLzs+t+42XLMNkQUI2vxkFYxZ0Fk2oIP6WTlO2+N86cQO4ERk+j/SY9kBFMXxGKaz/ZFNG2z9Jr4EKCeAg9nVcLdNAp38eBEUFHriZqsjCxWeqwa2XhYgSrOgx35DoQy7K9kDJc9DYJFV53x/UVKm0bSItukQYQ4AYACPgDUDlz0LEHdEoPHJMxNXLG6bmsfp8QtGNisj0MM9IX3eUfF18xtIQA0NO2cyUys1W/GQbvZpHTJpfpQt0JRss2WPNIeubwR5+FNYgOubocm64LGCYwQAzIHTUg10m6PgecMvOMQAasgwrJiNFcLdfS2UdIqfJfjoTrCTlmqG3HUBAMBcgFTcxtzy86ETOs+3OWY5LYxQGoZhxVRAhi0hWTJGXOcQZ7AdtA1vk06ujII6gOXXb9ReR0kl30NdVaArD5KraL7FE4ITb3lMeFqb1i4aHRHHqoy5jnkuiFf5DQFAQoU0cRMBEiqkir6wX3rmTD4sf8Ww04pkj3YTEFEdm4QIE8q4kEob1+ssBiDChDIupMp72geloX3/H//v/3/58etc9x+4fEAH/FHO+WvIf/Gv3FLd5AEdcK/zElAQYUIZF1Jl//5Of9Fsjbveb3EfHrsUSPx9y27413P1xq5oskz5fR/3WiibjlDR3xicdlrqa2BBVAgXJkVoUVaMFxclZMlZQhs33xnGforG0E7T6lFt2bLXuxwUJDLntLSG1uhsxHsOPKolGbLR6TSWHrVFLVp0GiLztKSvvq9Eks+2ZelhW8OKzWCWfFVD6+Vr3PNccFSLOmSjswELFiw4RcleslKlaunSpUubMmXKuLFvW280htbo3PO266a20FJmq0r0/Ie7s/iYnaPBoKfnvrrxvRvyGlAw6YyiT60xuCvr2+Gbus82x7iYSdbZEmjTK1xmzrmiTMyLf7XtGrYtH9ABp5x+cRxyZ5cHdMCdOeewmFff5z2iHm77kN21FjpoJjAY9JXOkDvrksIk9WwlmYMb7/Lym4Vzf6Zfi2sKokK4MPlDvmw14MU/WovibPHpdhWzZR/3praMv92LixLyKr9wo8YYqlNrdMYhc3LS1Ba18Bv+hA8EauJOCkOLAYgw415sCmHGY1KFqug0wiZuehjXi82IyEwKzgLYUasDqbSJmxNSZZ/+4axpPeHr8WIfb5PauF5sPoAIE8q4kEob14vNBUgo4+IpfyOQDkSYUMZF5u/zk4W+OktEX1Bfk9LG9WIvLpfqbJTK5D3jg/g/hKAkctq5i/A3waNX9mfdYz5tKwjIeMbndtXZA5UqX+T7yo/Yd61Zs+QygwuptIk7PYxzviKQShvXi80EiDCh3oc9s654N226EFJp43q5f/W/Sp/bptVA4l//FhY7J866LAhlXEiljRebj7CIzB0336cb0BaodM2D592P3HetW/d6ny8/YnPp1XzzHCDChHEhlTauF5sBEGFCGRdSaeN6sZmQ+OlduwUu9H3RR+zhlSZDKEs/bYd+s+KIbc1MVPbZIswRZXozpXysJiHChDIupNLG9WKzASJMKONCKm1cLzYHIMKEMi6k0sb1YvMCRJhQxoVU2rhebD6AKPk0A+qSFJkqGBdS6W6i5XmeZ+3jNpI//dDbApUqX+T7ko/Yd61SpcpUGBdSaQOZrJVyGLnyY9+sj1D/75sC6/+DS8UG/uhIAu0YPzROk8DKjlLQupob9O3SLBsUZjclwfP84O9vhzzHC8QN5vJjHAAM4BG4egwp/rg9SwAAAAA="
FONT_FACE_CSS = (
    "@font-face{font-family:'Vazirmatn';font-style:normal;"
    "font-weight:100 900;font-display:swap;"
    "src:url(data:font/woff2;base64," + VAZIR_FONT_B64 + ") format('woff2');}"
)


def ensure_media_dir():
    """ایجاد پوشه ذخیره‌سازی فایل‌های رسانه‌ای"""
    os.makedirs(MEDIA_DIR, exist_ok=True)


def parse_media_file_data(data, expected_kind=None):
    """استخراج اطلاعات فایل رسانه‌ای از داده پیام"""
    if not data:
        return None
    try:
        parsed = json.loads(data) if isinstance(data, str) else data
    except Exception:
        return None
    if not isinstance(parsed, dict):
        return None
    if expected_kind is not None:
        if isinstance(expected_kind, (tuple, list, set)):
            if parsed.get('kind') not in expected_kind:
                return None
        elif parsed.get('kind') != expected_kind:
            return None
    file_name = parsed.get('file')
    if not file_name or '/' in file_name or '\\' in file_name:
        return None
    return parsed


def delete_media_file(message):
    """حذف فایل رسانه‌ای مرتبط با پیام"""
    message_type = message.get('type')
    if message_type not in ('voice', 'video_note', 'file'):
        return
    media_kind = 'voice' if message_type == 'voice' else ('video_note' if message_type == 'video_note' else 'file')
    media = parse_media_file_data(message.get('data'), media_kind)
    if not media:
        return
    file_path = os.path.join(MEDIA_DIR, media['file'])
    if os.path.isfile(file_path):
        try:
            os.remove(file_path)
        except Exception as e:
            logger.warning(f"خطا در حذف فایل رسانه‌ای {file_path}: {e}")


# --- مدیریت دیتابیس SQLite ---
def get_db_connection():
    """ایجاد اتصال به دیتابیس با thread safety"""
    conn = sqlite3.connect(DB_FILE, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn


ALLOWED_COLUMNS = {
    'sender_id', 'type', 'data', 'timestamp', 'time', 'seen', 'react',
    'reply_id', 'reply_text', 'deleted', 'edited', 'updated', 'pinned', 'room_id'
}


def init_database():
    """ایجاد و مهاجرت جداول دیتابیس (پشتیبانی از چند اتاق)"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor()

        cursor.execute('''
            CREATE TABLE IF NOT EXISTS messages (
                id TEXT PRIMARY KEY,
                sender_id TEXT NOT NULL,
                type TEXT DEFAULT 'text',
                data TEXT,
                timestamp REAL NOT NULL,
                time TEXT,
                seen INTEGER DEFAULT 0,
                react TEXT,
                reply_id TEXT,
                reply_text TEXT,
                deleted INTEGER DEFAULT 0,
                edited INTEGER DEFAULT 0,
                updated REAL
            )
        ''')

        # --- مهاجرت بدون‌نسخه: افزودن ستون‌های جدید در صورت نبود ---
        existing_cols = {r[1] for r in cursor.execute("PRAGMA table_info(messages)").fetchall()}
        if 'room_id' not in existing_cols:
            cursor.execute("ALTER TABLE messages ADD COLUMN room_id TEXT DEFAULT '%s'" % DEFAULT_ROOM_ID)
        if 'pinned' not in existing_cols:
            cursor.execute("ALTER TABLE messages ADD COLUMN pinned INTEGER DEFAULT 0")

        # جدول اتاق‌ها
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS rooms (
                room_id TEXT PRIMARY KEY,
                name TEXT,
                admin_pass TEXT NOT NULL,
                guest_pass TEXT NOT NULL,
                created_at REAL
            )
        ''')

        # جدول پیام‌های زمان‌بندی‌شده
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS scheduled (
                id TEXT PRIMARY KEY,
                room_id TEXT NOT NULL,
                sender_id TEXT NOT NULL,
                type TEXT DEFAULT 'text',
                data TEXT,
                reply_id TEXT,
                reply_text TEXT,
                deliver_at REAL NOT NULL,
                created_at REAL
            )
        ''')

        cursor.execute('CREATE INDEX IF NOT EXISTS idx_timestamp ON messages(timestamp)')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_room ON messages(room_id)')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_deleted ON messages(deleted)')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_sched_deliver ON scheduled(deliver_at)')

        # ساخت اتاق پیش‌فرض از روی رمزهای قدیمی (در صورت نبود)
        row = cursor.execute("SELECT room_id FROM rooms WHERE room_id = ?", (DEFAULT_ROOM_ID,)).fetchone()
        if not row:
            pw = list(PASSWORD_TO_USER.keys())
            admin_pw = pw[0] if len(pw) > 0 else "2728"
            guest_pw = pw[1] if len(pw) > 1 else "9604"
            cursor.execute(
                "INSERT INTO rooms (room_id, name, admin_pass, guest_pass, created_at) VALUES (?, ?, ?, ?, ?)",
                (DEFAULT_ROOM_ID, DEFAULT_ROOM_NAME, admin_pw, guest_pw, time.time())
            )

        # مهاجرت sender_id قدیمی به نقش‌ها در اتاق پیش‌فرض
        cursor.execute("UPDATE messages SET sender_id = 'admin' WHERE sender_id = 'USER_A'")
        cursor.execute("UPDATE messages SET sender_id = 'guest' WHERE sender_id = 'USER_B'")
        cursor.execute("UPDATE messages SET room_id = ? WHERE room_id IS NULL", (DEFAULT_ROOM_ID,))

        conn.commit()
        conn.close()
        logger.info("دیتابیس با موفقیت آماده شد")
    except Exception as e:
        logger.error(f"خطا در ایجاد دیتابیس: {e}")
        raise


def load_room_messages(room_id):
    """بارگذاری پیام‌های اخیر یک اتاق از دیتابیس (قدیمی به جدید). سنجاق‌شده‌ها صرف‌نظر از زمان."""
    out = []
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        expiry_time = time.time() - (MESSAGE_EXPIRY_HOURS * 3600)
        cursor.execute('''
            SELECT * FROM messages
            WHERE deleted = 0 AND room_id = ? AND (timestamp > ? OR pinned = 1)
            ORDER BY timestamp DESC
            LIMIT ?
        ''', (room_id, expiry_time, MAX_MESSAGES_IN_MEMORY))
        rows = cursor.fetchall()
        conn.close()
        for row in reversed(rows):
            out.append(dict(row))
    except Exception as e:
        logger.error(f"خطا در بارگذاری پیام‌های اتاق {room_id}: {e}")
    return out


def get_room_state(room_id):
    """وضعیت درون‌حافظه‌ای اتاق؛ در صورت نیاز یک‌بار از دیتابیس لود می‌کند."""
    with LOCKED:
        st = ROOMS_STATE.get(room_id)
        if st is None:
            st = {'messages': deque(maxlen=MAX_MESSAGES_IN_MEMORY), 'typing': {}, 'last_seen': {}, 'loaded': False}
            ROOMS_STATE[room_id] = st
        if not st['loaded']:
            for row in load_room_messages(room_id):
                st['messages'].append(row)
            st['loaded'] = True
        return st


def load_messages_to_memory():
    """پیش‌بارگذاری اتاق پیش‌فرض هنگام شروع (سازگاری با کد قبلی)."""
    try:
        st = get_room_state(DEFAULT_ROOM_ID)
        logger.info(f"{len(st['messages'])} پیام اتاق اصلی به حافظه بارگذاری شد")
    except Exception as e:
        logger.error(f"خطا در بارگذاری پیام‌ها: {e}")


def save_message_to_db(message):
    """ذخیره یک پیام در دیتابیس"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor()

        cursor.execute('''
            INSERT OR REPLACE INTO messages
            (id, sender_id, type, data, timestamp, time, seen, react, reply_id, reply_text, deleted, edited, updated, room_id, pinned)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ''', (
            message.get('id'),
            message.get('sender_id'),
            message.get('type', 'text'),
            message.get('data'),
            message.get('timestamp'),
            message.get('time'),
            1 if message.get('seen') else 0,
            message.get('react'),
            message.get('reply_id'),
            message.get('reply_text'),
            1 if message.get('deleted') else 0,
            1 if message.get('edited') else 0,
            message.get('updated'),
            message.get('room_id', DEFAULT_ROOM_ID),
            1 if message.get('pinned') else 0
        ))

        conn.commit()
        conn.close()
    except Exception as e:
        logger.error(f"خطا در ذخیره پیام: {e}")


def update_message_in_db(message_id, updates):
    """به‌روزرسانی یک پیام در دیتابیس (فقط ستون‌های مجاز)"""
    try:
        cols = [k for k in updates.keys() if k in ALLOWED_COLUMNS]
        if not cols:
            return
        conn = get_db_connection()
        cursor = conn.cursor()
        set_clause = ', '.join([f"{k} = ?" for k in cols])
        values = [updates[k] for k in cols] + [message_id]
        cursor.execute(f"UPDATE messages SET {set_clause} WHERE id = ?", values)
        conn.commit()
        conn.close()
    except Exception as e:
        logger.error(f"خطا در به‌روزرسانی پیام: {e}")


def cleanup_old_messages():
    """حذف پیام‌های قدیمی از دیتابیس (پیام‌های سنجاق‌شده حذف نمی‌شوند)"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor()

        expiry_time = time.time() - (MESSAGE_EXPIRY_HOURS * 3600)
        cursor.execute('SELECT type, data FROM messages WHERE timestamp < ? AND pinned = 0', (expiry_time,))
        old_rows = cursor.fetchall()
        for row in old_rows:
            if row['type'] in ('voice', 'video_note', 'file'):
                delete_media_file(dict(row))
        cursor.execute('DELETE FROM messages WHERE timestamp < ? AND pinned = 0', (expiry_time,))

        deleted_count = cursor.rowcount
        conn.commit()
        conn.close()

        if deleted_count > 0:
            logger.info(f"{deleted_count} پیام قدیمی حذف شد")
    except Exception as e:
        logger.error(f"خطا در حذف پیام‌های قدیمی: {e}")


# --- مدیریت اتاق‌ها ---
def get_room(room_id):
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        row = cur.execute("SELECT * FROM rooms WHERE room_id = ?", (room_id,)).fetchone()
        conn.close()
        return dict(row) if row else None
    except Exception as e:
        logger.error(f"خطا در خواندن اتاق: {e}")
        return None


def list_rooms():
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        rows = cur.execute("SELECT * FROM rooms ORDER BY created_at DESC").fetchall()
        conn.close()
        return [dict(r) for r in rows]
    except Exception as e:
        logger.error(f"خطا در فهرست اتاق‌ها: {e}")
        return []


def create_room(name, admin_pass, guest_pass):
    room_id = secrets.token_hex(8)
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute(
            "INSERT INTO rooms (room_id, name, admin_pass, guest_pass, created_at) VALUES (?, ?, ?, ?, ?)",
            (room_id, name, admin_pass, guest_pass, time.time())
        )
        conn.commit()
        conn.close()
        return room_id
    except Exception as e:
        logger.error(f"خطا در ساخت اتاق: {e}")
        return None


def delete_room(room_id):
    if room_id == DEFAULT_ROOM_ID:
        return False  # اتاق اصلی حذف نمی‌شود
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        rows = cur.execute("SELECT type, data FROM messages WHERE room_id = ?", (room_id,)).fetchall()
        for r in rows:
            if r['type'] in ('voice', 'video_note', 'file'):
                delete_media_file(dict(r))
        cur.execute("DELETE FROM messages WHERE room_id = ?", (room_id,))
        cur.execute("DELETE FROM scheduled WHERE room_id = ?", (room_id,))
        cur.execute("DELETE FROM rooms WHERE room_id = ?", (room_id,))
        conn.commit()
        conn.close()
        with LOCKED:
            ROOMS_STATE.pop(room_id, None)
        return True
    except Exception as e:
        logger.error(f"خطا در حذف اتاق: {e}")
        return False


def lookup_password(p):
    """رمز را در همهٔ اتاق‌ها جست‌وجو می‌کند؛ (room_id, role) یا None"""
    if not p:
        return None
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        rows = cur.execute("SELECT room_id, admin_pass, guest_pass FROM rooms").fetchall()
        conn.close()
    except Exception:
        rows = []
    match = None
    for r in rows:
        if hmac.compare_digest(p, r['admin_pass'] or ''):
            match = (r['room_id'], 'admin')
        elif hmac.compare_digest(p, r['guest_pass'] or ''):
            match = (r['room_id'], 'guest')
    return match


# --- پیام‌های زمان‌بندی‌شده ---
def add_scheduled(room_id, sender_id, mtype, data, reply_id, reply_text, deliver_at):
    sid = "s" + secrets.token_hex(8)
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute(
            "INSERT INTO scheduled (id, room_id, sender_id, type, data, reply_id, reply_text, deliver_at, created_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (sid, room_id, sender_id, mtype, data, reply_id, reply_text, deliver_at, time.time())
        )
        conn.commit()
        conn.close()
        return sid
    except Exception as e:
        logger.error(f"خطا در ثبت پیام زمان‌بندی‌شده: {e}")
        return None


def list_scheduled(room_id, sender_id=None):
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        if sender_id:
            rows = cur.execute("SELECT * FROM scheduled WHERE room_id = ? AND sender_id = ? ORDER BY deliver_at", (room_id, sender_id)).fetchall()
        else:
            rows = cur.execute("SELECT * FROM scheduled WHERE room_id = ? ORDER BY deliver_at", (room_id,)).fetchall()
        conn.close()
        return [dict(r) for r in rows]
    except Exception as e:
        logger.error(f"خطا در فهرست زمان‌بندی‌ها: {e}")
        return []


def delete_scheduled(sid, room_id):
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("DELETE FROM scheduled WHERE id = ? AND room_id = ?", (sid, room_id))
        conn.commit()
        conn.close()
        return True
    except Exception as e:
        logger.error(f"خطا در حذف زمان‌بندی: {e}")
        return False


def media_belongs_to_room(file_name, room_id):
    """بررسی تعلق فایل رسانه‌ای به اتاق کاربر (جلوگیری از دسترسی بین‌اتاقی)"""
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        row = cur.execute(
            "SELECT 1 FROM messages WHERE room_id = ? AND type IN ('voice','video_note','file') AND data LIKE ? LIMIT 1",
            (room_id, '%"' + file_name + '"%')
        ).fetchone()
        conn.close()
        return row is not None
    except Exception as e:
        logger.error(f"خطا در بررسی مالکیت رسانه: {e}")
        return False


def render_admin_page():
    """رندر سمت‌سرور پنل مدیریت اتاق‌ها"""
    rooms = list_rooms()
    rows_html = ""
    for r in rooms:
        name = html.escape(r.get('name') or '')
        rid = html.escape(r.get('room_id') or '')
        ap = html.escape(r.get('admin_pass') or '')
        gp = html.escape(r.get('guest_pass') or '')
        is_default = (r.get('room_id') == DEFAULT_ROOM_ID)
        del_btn = '' if is_default else (
            '<form method="POST" action="/delete_room" onsubmit="return confirm(\'این اتاق و همهٔ پیام‌هایش حذف شود؟\')" style="margin:0">'
            '<input type="hidden" name="room_id" value="' + rid + '">'
            '<button class="del-btn" type="submit">حذف اتاق</button></form>'
        )
        badge = '<span class="badge">اتاق اصلی</span>' if is_default else ''
        rows_html += (
            '<div class="room-card">'
            '<div class="room-top"><div class="room-name">' + (name or 'بدون نام') + ' ' + badge + '</div>' + del_btn + '</div>'
            '<div class="creds">'
            '<div class="cred"><span>رمز ادمین (شما):</span><code>' + ap + '</code></div>'
            '<div class="cred"><span>رمز دوست شما:</span><code>' + gp + '</code></div>'
            '</div></div>'
        )
    if not rooms:
        rows_html = '<p class="empty">هنوز اتاقی ساخته نشده.</p>'

    return (
        '<!DOCTYPE html><html lang="fa" dir="rtl"><head><meta charset="UTF-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=5.0, user-scalable=yes">'
        '<title>پنل مدیریت</title><style>' + FONT_FACE_CSS +
        ':root{--bg:#f5f6f8;--surface:#fff;--accent:#10a37f;--accent-strong:#0c8268;--text:#0f1a24;--muted:#6a7682;--hairline:#e9ecef;--danger:#e5484d}'
        '*{box-sizing:border-box;font-family:"Vazirmatn","Segoe UI",Tahoma,sans-serif}'
        'body{margin:0;background:var(--bg);color:var(--text);-webkit-font-smoothing:antialiased;min-height:100vh}'
        '.wrap{max-width:680px;margin:0 auto;padding:24px 16px}'
        '.head{display:flex;justify-content:space-between;align-items:center;margin-bottom:20px}'
        '.head h1{font-size:20px;font-weight:700;margin:0}'
        '.head a{color:var(--muted);text-decoration:none;font-size:13px;background:var(--surface);border:1px solid var(--hairline);padding:8px 14px;border-radius:12px}'
        '.panel{background:var(--surface);border:1px solid var(--hairline);border-radius:18px;padding:20px;margin-bottom:18px}'
        '.panel h2{font-size:15px;margin:0 0 14px;font-weight:700}'
        'label{display:block;font-size:13px;color:var(--muted);margin:10px 0 5px}'
        'input{width:100%;padding:12px 14px;border:1px solid var(--hairline);border-radius:12px;font-size:15px;background:var(--bg);color:var(--text);outline:none}'
        'input:focus{border-color:var(--accent);background:var(--surface)}'
        'button.primary{width:100%;margin-top:16px;background:var(--accent);color:#fff;border:none;padding:13px;border-radius:12px;font-weight:700;font-size:15px;cursor:pointer}'
        'button.primary:hover{background:var(--accent-strong)}'
        '.room-card{border:1px solid var(--hairline);border-radius:14px;padding:14px;margin-bottom:12px}'
        '.room-top{display:flex;justify-content:space-between;align-items:center;gap:10px}'
        '.room-name{font-weight:700;font-size:15px}'
        '.badge{font-size:11px;background:#e7f5f0;color:var(--accent-strong);padding:2px 8px;border-radius:8px;font-weight:500}'
        '.creds{margin-top:10px;display:flex;flex-wrap:wrap;gap:10px}'
        '.cred{font-size:13px;color:var(--muted);display:flex;align-items:center;gap:6px}'
        '.cred code{background:var(--bg);border:1px solid var(--hairline);padding:3px 10px;border-radius:8px;color:var(--text);font-size:14px;font-family:monospace}'
        '.del-btn{background:transparent;border:1px solid var(--danger);color:var(--danger);padding:7px 12px;border-radius:10px;font-size:12px;cursor:pointer}'
        '.del-btn:hover{background:var(--danger);color:#fff}'
        '.empty{color:var(--muted);font-size:14px;text-align:center;padding:16px}'
        '.hint{font-size:12px;color:var(--muted);margin-top:8px;line-height:1.7}'
        '</style></head><body><div class="wrap">'
        '<div class="head"><h1>🏠 پنل مدیریت اتاق‌ها</h1><a href="/logout">خروج</a></div>'
        '<div class="panel"><h2>ساخت اتاق گفت‌وگوی جدید</h2>'
        '<form method="POST" action="/create_room">'
        '<label>نام اتاق</label><input name="name" maxlength="60" placeholder="مثلاً: گفت‌وگو با علی" required>'
        '<label>رمز ورود شما (ادمین)</label><input name="admin_pass" maxlength="64" placeholder="رمز خودتان" required>'
        '<label>رمز ورود دوست شما</label><input name="guest_pass" maxlength="64" placeholder="رمزی که به دوستتان می‌دهید" required>'
        '<button class="primary" type="submit">ساخت اتاق</button>'
        '<div class="hint">پس از ساخت، رمز دوستتان را به او بدهید تا از همان صفحهٔ ورود وارد شود. کلید رمزنگاری گفت‌وگو (که در شروع چت وارد می‌شود) را هم باید جداگانه با او هماهنگ کنید.</div>'
        '</form></div>'
        '<div class="panel"><h2>اتاق‌های موجود</h2>' + rows_html + '</div>'
        '</div></body></html>'
    )


# --- پارس کوکی بهبود یافته ---
def parse_cookies(cookie_header: str) -> dict:
    """پارس کوکی‌ها با استفاده از کتابخانه استاندارد"""
    cookies = {}
    if not cookie_header:
        return cookies
    
    try:
        simple_cookie = SimpleCookie()
        simple_cookie.load(cookie_header)
        for key, morsel in simple_cookie.items():
            cookies[key] = morsel.value
    except Exception as e:
        logger.warning(f"خطا در پارس کوکی: {e}")
        # fallback به روش ساده
        try:
            for item in cookie_header.split(';'):
                if '=' in item:
                    key, value = item.strip().split('=', 1)
                    cookies[key] = value
        except Exception:
            pass
    
    return cookies


def parse_json_safely(data: str) -> dict:
    """پارس JSON با مدیریت خطا"""
    try:
        return json.loads(data)
    except json.JSONDecodeError as e:
        logger.warning(f"خطا در پارس JSON: {e}")
        return {}
    except Exception as e:
        logger.error(f"خطای غیرمنتظره در پارس JSON: {e}")
        return {}


# --- صفحه لاگین ---
LOGIN_PAGE = """
<!DOCTYPE html>
<html lang="fa" dir="rtl">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=5.0, user-scalable=yes">
    <meta name="theme-color" content="#eceff1">
    <title>ورود</title>
    <link id="app-favicon" rel="icon" type="image/png">
<style>
    /*__VAZIR__*/
    * { box-sizing: border-box; font-family: 'Vazirmatn', 'Segoe UI', Tahoma, sans-serif; }

    :root {
        --bg-color: #f5f6f8;
        --card-bg: #ffffff;
        --text-color: #0f1a24;
        --input-border: #e6e9ec;
        --button-bg: #10a37f;
        --button-hover: #0c8268;
    }

    [data-theme="dark"] {
        --bg-color: #0d1317;
        --card-bg: #1b262c;
        --text-color: #e7ecef;
        --input-border: #243139;
        --button-bg: #2dd4bf;
        --button-hover: #14b8a6;
    }

    body {
        font-family: 'Vazirmatn', 'Segoe UI', Tahoma, sans-serif;
        background: var(--bg-color);
        display: flex;
        justify-content: center;
        align-items: center;
        min-height: 100vh;
        min-height: 100dvh;
        height: 100%;
        margin: 0;
        padding: 16px;
        transition: background 0.3s;
        -webkit-font-smoothing: antialiased;
        -moz-osx-font-smoothing: grayscale;
    }

    .card {
        background: var(--card-bg);
        padding: 40px;
        border-radius: 24px;
        text-align: center;
        width: 100%;
        max-width: 340px;
        border: 1px solid var(--input-border);
        box-shadow: 0 16px 40px rgba(15,26,36,0.10);
        transition: background 0.3s;
    }

    h2 { color: var(--text-color); margin-bottom: 20px; font-weight: 700; letter-spacing: -0.01em; transition: color 0.3s; }

    input {
        width: 100%;
        padding: 15px;
        margin: 15px 0;
        border-radius: 14px;
        border: 1px solid var(--input-border);
        text-align: center;
        outline: none;
        font-size: 16px;
        background: var(--bg-color);
        color: var(--text-color);
        transition: all 0.2s;
    }
    input:focus { border-color: var(--button-bg); background: var(--card-bg); }

    button {
        width: 100%;
        background: var(--button-bg);
        color: white;
        border: none;
        padding: 15px;
        border-radius: 14px;
        cursor: pointer;
        font-weight: 700;
        font-size: 16px;
        transition: 0.2s;
    }

    button:hover { background: var(--button-hover); }
    button:active { opacity: 0.9; }

    .theme-toggle {
        position: fixed;
        top: 16px;
        right: 16px;
        left: auto;
        background: var(--card-bg);
        border: 1px solid var(--input-border);
        border-radius: 50%;
        width: 44px;
        height: 44px;
        cursor: pointer;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 20px;
        transition: all 0.3s;
        z-index: 10;
        -webkit-tap-highlight-color: transparent;
    }
    .theme-toggle:hover { opacity: 0.9; }
    .theme-toggle:active { transform: scale(0.95); }

    /* موبایل ویو */
    @media (max-width: 480px) {
        body { padding: 12px; align-items: center; }
        .card {
            padding: 28px 24px;
            border-radius: 20px;
            max-width: none;
        }
        h2 { font-size: 1.25rem; margin-bottom: 16px; }
        input, button {
            padding: 14px;
            margin: 12px 0;
            font-size: 16px;
            min-height: 48px;
        }
        .theme-toggle {
            top: 12px;
            right: 12px;
            width: 40px;
            height: 40px;
            font-size: 18px;
        }
    }

    @media (max-width: 360px) {
        .card { padding: 20px 16px; border-radius: 16px; }
        h2 { font-size: 1.1rem; }
    }

</style>
<script>
    const theme = localStorage.getItem('theme') || 'light';
    if (theme === 'dark') {
        document.documentElement.setAttribute('data-theme', 'dark');
    }
</script>
</head>
<body>
    <div class="theme-toggle" onclick="toggleTheme()">🌙</div>
    <div class="card">
        <h2>ورود به این‌چت</h2>
        <form method="POST" action="/login">
            <input type="password" name="p" placeholder="رمز عبور" required>
            <button type="submit">ورود امن</button>
        </form>
    </div>
    <script>
        function setLoginFavicon() {
            const canvas = document.createElement('canvas');
            canvas.width = 64;
            canvas.height = 64;
            const ctx = canvas.getContext('2d');
            if (!ctx) return;
            const rounded = (x, y, w, h, r) => {
                if (ctx.roundRect) {
                    ctx.beginPath();
                    ctx.roundRect(x, y, w, h, r);
                    return;
                }
                const radius = Math.min(r, w / 2, h / 2);
                ctx.beginPath();
                ctx.moveTo(x + radius, y);
                ctx.lineTo(x + w - radius, y);
                ctx.quadraticCurveTo(x + w, y, x + w, y + radius);
                ctx.lineTo(x + w, y + h - radius);
                ctx.quadraticCurveTo(x + w, y + h, x + w - radius, y + h);
                ctx.lineTo(x + radius, y + h);
                ctx.quadraticCurveTo(x, y + h, x, y + h - radius);
                ctx.lineTo(x, y + radius);
                ctx.quadraticCurveTo(x, y, x + radius, y);
                ctx.closePath();
            };

            const grad = ctx.createLinearGradient(0, 0, 64, 64);
            grad.addColorStop(0, '#00a884');
            grad.addColorStop(1, '#005c4b');
            ctx.fillStyle = grad;
            rounded(4, 4, 56, 56, 18);
            ctx.fill();

            ctx.fillStyle = '#ffffff';
            rounded(13, 18, 38, 27, 9);
            ctx.fill();

            ctx.beginPath();
            ctx.moveTo(25, 45);
            ctx.lineTo(19, 53);
            ctx.lineTo(20, 44);
            ctx.closePath();
            ctx.fill();

            ctx.fillStyle = '#00a884';
            [22, 32, 42].forEach((x) => {
                ctx.beginPath();
                ctx.arc(x, 31, 2.8, 0, Math.PI * 2);
                ctx.fill();
            });

            const favicon = document.getElementById('app-favicon') || document.createElement('link');
            favicon.id = 'app-favicon';
            favicon.rel = 'icon';
            favicon.type = 'image/png';
            favicon.href = canvas.toDataURL('image/png');
            if (!favicon.parentNode) document.head.appendChild(favicon);
        }

        function toggleTheme() {
            const currentTheme = document.documentElement.getAttribute('data-theme');
            const newTheme = currentTheme === 'dark' ? 'light' : 'dark';
            document.documentElement.setAttribute('data-theme', newTheme);
            localStorage.setItem('theme', newTheme);
            document.querySelector('.theme-toggle').textContent = newTheme === 'dark' ? '☀️' : '🌙';
        }
        
        // Set initial icon
        setLoginFavicon();
        const currentTheme = document.documentElement.getAttribute('data-theme');
        document.querySelector('.theme-toggle').textContent = currentTheme === 'dark' ? '☀️' : '🌙';
    </script>
</body>
</html>
"""

# --- صفحه چت ---
CHAT_PAGE = r"""
<!DOCTYPE html>
<html lang="fa" dir="rtl">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=5.0, user-scalable=yes">
    <title>این‌چت</title>
    <link id="app-favicon" rel="icon" type="image/png">
    <style>
        /*__VAZIR__*/
        :root {
            --bg-color: #f5f6f8;
            --header-bg: #ffffff;
            --header-text: #0f1a24;
            --surface: #ffffff;
            --card-bg: #ffffff;
            --accent: #10a37f;
            --accent-strong: #0c8268;
            --hairline: #e9ecef;
            --sent-msg-bg: #d6f0e8;
            --received-msg-bg: #ffffff;
            --input-bg: #eef1f4;
            --input-container-bg: #ffffff;
            --reply-preview-bg: #eef1f4;
            --input-border: #e6e9ec;
            --text-color: #0f1a24;
            --secondary-text: #6a7682;
            --msg-actions-color: #0c8268;
            --reaction-bg: #ffffff;
            --highlight-bg: #ffe8a3;
            --reply-area-bg: rgba(16,163,127,0.07);
            --reply-border: #10a37f;
            --icon-fill: #6a7682;
            --send-icon-fill: #10a37f;
        }

        [data-theme="dark"] {
            --bg-color: #0d1317;
            --header-bg: #141d23;
            --header-text: #e7ecef;
            --surface: #1b262c;
            --card-bg: #1b262c;
            --accent: #2dd4bf;
            --accent-strong: #14b8a6;
            --hairline: #243139;
            --sent-msg-bg: #114b44;
            --received-msg-bg: #1d282e;
            --input-bg: #222e35;
            --input-container-bg: #141d23;
            --reply-preview-bg: #1d282e;
            --input-border: #243139;
            --text-color: #e7ecef;
            --secondary-text: #93a1ab;
            --msg-actions-color: #2dd4bf;
            --reaction-bg: #243139;
            --highlight-bg: #4a5f3f;
            --reply-area-bg: rgba(45,212,191,0.10);
            --reply-border: #2dd4bf;
            --icon-fill: #93a1ab;
            --send-icon-fill: #2dd4bf;
        }

        * { box-sizing: border-box; font-family: 'Vazirmatn', 'Segoe UI', Tahoma, sans-serif; }

        body {
            background: var(--bg-color);
            margin: 0;
            height: var(--app-height, 100dvh);
            display: flex;
            flex-direction: column;
            overflow: hidden;
            transition: background 0.3s;
            -webkit-font-smoothing: antialiased;
            -moz-osx-font-smoothing: grayscale;
        }

        /* Header */
        #header { background: var(--header-bg); color: var(--header-text); padding: 13px 20px; border-bottom: 1px solid var(--hairline); z-index: 10; display: flex; flex-direction: column; align-items: center; transition: background 0.3s, border-color 0.3s; position: relative; }
        #header b { font-size: 17px; font-weight: 700; letter-spacing: -0.01em; }
        #status-bar { font-size: 12px; opacity: 0.85; margin-top: 3px; font-weight: 500; }
        .theme-toggle {
            position: absolute;
            left: 16px;
            top: 50%;
            transform: translateY(-50%);
            background: var(--input-bg);
            border: none;
            border-radius: 50%;
            width: 38px;
            height: 38px;
            cursor: pointer;
            display: flex;
            align-items: center;
            justify-content: center;
            font-size: 18px;
            transition: all 0.2s;
        }
        .theme-toggle:hover {
            filter: brightness(0.95);
            transform: translateY(-50%) scale(1.05);
        }

        /* Chat Area */
        #chat-box { flex: 1; overflow-y: auto; padding: 18px 16px; display: flex; flex-direction: column; gap: 6px; scroll-behavior: smooth; }
        #chat-box::-webkit-scrollbar { width: 7px; }
        #chat-box::-webkit-scrollbar-thumb { background: var(--hairline); border-radius: 8px; }
        #chat-box::-webkit-scrollbar-thumb:hover { background: var(--secondary-text); }

        /* Message Bubbles */
        .msg {
            max-width: 78%;
            padding: 9px 13px;
            border-radius: 18px;
            font-size: 14.5px;
            line-height: 1.55;
            position: relative;
            box-shadow: 0 1px 2px rgba(15,26,36,0.06);
            transition: background 0.25s, color 0.25s, box-shadow 0.2s;
            word-wrap: break-word;
            overflow-wrap: break-word;
            word-break: break-word;
            user-select: text;
            -webkit-user-select: text;
            -webkit-touch-callout: none;
            touch-action: manipulation;
        }

        /* فقط موبایل: انتخاب متن پیام‌ها غیرفعال */
        @media (hover: none) and (pointer: coarse) {
            .msg{
                user-select: none !important;
                -webkit-user-select: none !important;
            }
        }

        #copy-bubble{
            position: fixed;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            background: rgba(0,0,0,0.78);
            color: #fff;
            padding: 10px 14px;
            border-radius: 14px;
            font-size: 13px;
            z-index: 20000;
            display: none;
            backdrop-filter: blur(4px);
            -webkit-backdrop-filter: blur(4px);
        }

        .sent { background: var(--sent-msg-bg); color: var(--text-color); align-self: flex-start; border-top-left-radius: 6px; transition: background 0.3s, color 0.3s; }
        .received { background: var(--received-msg-bg); color: var(--text-color); align-self: flex-end; border-top-right-radius: 6px; border: 1px solid var(--hairline); transition: background 0.3s, color 0.3s, border-color 0.3s; }
        .pending-upload { opacity: 0.5; pointer-events: none; }
        .pending-upload-status { font-size: 10px; color: var(--secondary-text); margin-top: 6px; }
        .highlight { background: var(--highlight-bg) !important; }

        /* Reactions */
        .reaction { position: absolute; bottom: -10px; left: 10px; background: var(--reaction-bg); border-radius: 10px; padding: 2px 4px; font-size: 12px; box-shadow: 0 1px 3px rgba(0,0,0,0.2); transition: background 0.3s; }
        
        /* Reaction Menu */
        .reaction-menu {
            position: fixed;
            background: var(--reaction-bg);
            border-radius: 24px;
            padding: 8px;
            box-shadow: 0 4px 12px rgba(0,0,0,0.3);
            display: none;
            z-index: 10000;
            gap: 8px;
            flex-direction: row;
            align-items: center;
            justify-content: center;
            backdrop-filter: blur(10px);
            -webkit-backdrop-filter: blur(10px);
            pointer-events: auto;
        }
        .reaction-menu.show {
            display: flex;
        }
        .reaction-emoji {
            font-size: 28px;
            cursor: pointer;
            padding: 4px;
            border-radius: 50%;
            transition: transform 0.2s, background 0.2s;
            user-select: none;
            -webkit-user-select: none;
        }
        .reaction-emoji:hover {
            transform: scale(1.2);
            background: rgba(0,0,0,0.1);
        }
        [data-theme="dark"] .reaction-emoji:hover {
            background: rgba(255,255,255,0.1);
        }

        .reply-area { background: var(--reply-area-bg); padding: 6px; border-right: 4px solid var(--reply-border); font-size: 11.5px; margin-bottom: 6px; border-radius: 6px; cursor: pointer; color: var(--secondary-text); transition: all 0.3s; }

        .footer-info { display: flex; justify-content: space-between; align-items: center; font-size: 10px; color: var(--secondary-text); margin-top: 4px; }
        .seen-status { color: #53bdeb; font-weight: bold; margin-right: 4px; }

        .msg-actions { font-size: 10px; margin-top: 6px; display: flex; gap: 12px; color: var(--msg-actions-color); border-top: 1px solid rgba(0,0,0,0.05); padding-top: 4px; transition: color 0.3s, border-color 0.3s; }
        [data-theme="dark"] .msg-actions { border-top-color: rgba(255,255,255,0.1); }
        .msg-actions span { cursor: pointer; font-weight: 500; }

        #typing-status { height: 20px; font-size: 12px; color: var(--secondary-text); padding: 0 25px; font-style: italic; transition: color 0.3s; }

        /* Input Area */
        #input-container { background: var(--input-container-bg); padding: 10px 14px; display: flex; align-items: flex-end; gap: 8px; border-top: 1px solid var(--hairline); position: sticky; bottom: 0; z-index: 20; transition: background 0.3s, border-color 0.3s; }

        #composer-wrap {
            flex: 1;
            min-width: 0;
            background: var(--input-bg);
            border: 1px solid transparent;
            border-radius: 22px;
            padding: 3px 12px;
            transition: background 0.3s, color 0.3s, border-color 0.2s;
        }
        #composer-wrap:focus-within {
            border-color: var(--accent);
            background: var(--surface);
        }

        #msgInput {
            border: none;
            padding: 7px 5px;
            border-radius: 14px;
            outline: none;
            font-size: 16px;
            max-height: 120px;
            min-height: 34px;
            overflow-y: auto;
            background: transparent;
            color: var(--text-color);
            line-height: 21px;
            transition: color 0.3s;
            white-space: pre-wrap;
            word-break: break-word;
        }
        #msgInput:empty::before {
            content: attr(data-placeholder);
            color: var(--secondary-text);
            pointer-events: none;
        }
        #msgInput a { color: var(--accent); text-decoration: underline; }
        .spoiler-text,
        .composer-spoiler {
            background: rgba(0,0,0,0.18);
            color: transparent;
            border-radius: 6px;
            padding: 0 4px;
            cursor: pointer;
            transition: background 0.2s, color 0.2s;
        }
        .spoiler-text.revealed {
            color: inherit;
            background: rgba(0,168,132,0.15);
        }
        .composer-spoiler {
            color: inherit;
            background: rgba(0,168,132,0.18);
        }
        #composer-context-menu {
            position: fixed;
            display: none;
            z-index: 15000;
            background: var(--reply-preview-bg);
            border: 1px solid var(--input-border);
            border-radius: 14px;
            box-shadow: 0 8px 24px rgba(0,0,0,0.22);
            padding: 6px;
            gap: 4px;
            align-items: center;
            direction: rtl;
        }
        #composer-context-menu.show {
            display: flex;
        }
        .composer-menu-btn {
            border: none;
            background: transparent;
            color: var(--text-color);
            min-width: 34px;
            height: 34px;
            border-radius: 10px;
            padding: 0 10px;
            cursor: pointer;
            font-size: 13px;
            font-weight: 700;
            display: inline-flex;
            align-items: center;
            justify-content: center;
            transition: background 0.2s, color 0.3s;
            white-space: nowrap;
        }
        .composer-menu-btn:hover {
            background: rgba(0,0,0,0.08);
        }
        [data-theme="dark"] .composer-menu-btn:hover {
            background: rgba(255,255,255,0.1);
        }

        .icon-btn { background: transparent; border: none; cursor: pointer; padding: 8px; border-radius: 50%; display: flex; align-items: center; justify-content: center; transition: 0.2s; }
        .icon-btn:hover { background: rgba(0,0,0,0.05); }
        [data-theme="dark"] .icon-btn:hover { background: rgba(255,255,255,0.1); }
        .icon-btn svg { fill: var(--icon-fill); width: 24px; height: 24px; transition: fill 0.3s; }
        .send-btn svg { fill: var(--send-icon-fill); }
        #video-note-btn {
            background: transparent;
            border: none;
            box-shadow: none;
        }
        #video-note-btn::after {
            content: none;
        }
        #video-note-btn svg {
            width: 24px;
            height: 24px;
            fill: var(--icon-fill);
            filter: none;
        }

        /* Voice Player - مینیمال شبیه تلگرام */
        .voice-player {
            display: flex;
            align-items: center;
            gap: 10px;
            padding: 8px 12px;
            background: var(--reply-area-bg, rgba(0,0,0,0.04));
            border-radius: 12px;
            min-width: 200px;
            max-width: 280px;
        }
        .voice-play-btn {
            width: 36px;
            height: 36px;
            border-radius: 50%;
            background: var(--send-icon-fill, #00a884);
            border: none;
            cursor: pointer;
            display: flex;
            align-items: center;
            justify-content: center;
            flex-shrink: 0;
            transition: transform 0.2s, background 0.2s;
        }
        .voice-play-btn:hover { transform: scale(1.1); }
        .voice-play-btn:active { transform: scale(0.95); }
        .voice-play-btn svg { fill: white; width: 16px; height: 16px; }
        .voice-waveform {
            flex: 1;
            height: 32px;
            display: flex;
            align-items: center;
            gap: 2px;
            cursor: pointer;
        }
        .voice-bar {
            width: 3px;
            background: var(--secondary-text, #54656f);
            border-radius: 2px;
            transition: background 0.2s;
        }
        .voice-bar.played { background: var(--send-icon-fill, #00a884); }
        .voice-info {
            display: flex;
            flex-direction: column;
            align-items: flex-end;
            gap: 2px;
            min-width: 40px;
        }
        .voice-time { font-size: 11px; color: var(--secondary-text, #54656f); font-variant-numeric: tabular-nums; }
        .voice-speed {
            font-size: 9px;
            padding: 2px 5px;
            background: var(--secondary-text, #54656f);
            color: white;
            border-radius: 8px;
            cursor: pointer;
            user-select: none;
            transition: background 0.2s;
        }
        .voice-speed:hover { background: var(--send-icon-fill, #00a884); }
        .voice-speed.active { background: var(--send-icon-fill, #00a884); }
        .file-card {
            display: flex;
            align-items: center;
            gap: 12px;
            min-width: 220px;
            max-width: 300px;
            padding: 10px 12px;
            background: var(--reply-area-bg, rgba(0,0,0,0.04));
            border-radius: 14px;
            cursor: pointer;
        }
        .file-card-icon {
            width: 40px;
            height: 40px;
            border-radius: 12px;
            background: var(--send-icon-fill, #00a884);
            color: #fff;
            display: flex;
            align-items: center;
            justify-content: center;
            font-size: 20px;
            flex-shrink: 0;
        }
        .file-card-body {
            flex: 1;
            min-width: 0;
            display: flex;
            flex-direction: column;
            gap: 4px;
        }
        .file-card-name {
            font-size: 13px;
            font-weight: 600;
            color: var(--text-color);
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
        }
        .file-card-meta {
            font-size: 11px;
            color: var(--secondary-text, #54656f);
        }
        .file-card-action {
            font-size: 11px;
            color: var(--send-icon-fill, #00a884);
            font-weight: 700;
        }

        .video-note {
            width: 168px;
            height: 168px;
            border-radius: 50%;
            overflow: hidden;
            position: relative;
            background: #000;
            border: 2px solid rgba(255,255,255,0.18);
            cursor: pointer;
        }
        .video-note video {
            width: 100%;
            height: 100%;
            object-fit: cover;
            display: block;
        }
        .video-note-play {
            position: absolute;
            inset: 0;
            display: flex;
            align-items: center;
            justify-content: center;
            background: rgba(0,0,0,0.25);
            pointer-events: none;
            transition: opacity 0.2s;
        }
        .video-note.playing .video-note-play { opacity: 0; }
        .video-note-play svg { width: 34px; height: 34px; fill: white; }

        /* Recording UI - روی موبایل با کیبورد باز بالای تکست‌باکس قرار می‌گیرد (--bubble-bottom) */
        #recording-ui {
            display: none;
            position: fixed;
            bottom: var(--bubble-bottom, 70px);
            left: 50%;
            transform: translateX(-50%);
            background: var(--card-bg, white);
            border: 1px solid var(--hairline);
            padding: 16px 24px;
            border-radius: 22px;
            box-shadow: 0 12px 32px rgba(15,26,36,0.16);
            z-index: 1100;
            align-items: center;
            gap: 16px;
            animation: slideUp 0.3s ease;
        }
        #recording-ui.show { display: flex; }
        @keyframes slideUp {
            from { opacity: 0; transform: translateX(-50%) translateY(20px); }
            to { opacity: 1; transform: translateX(-50%) translateY(0); }
        }
        .recording-indicator {
            width: 12px;
            height: 12px;
            background: #f44336;
            border-radius: 50%;
            animation: pulse 1s infinite;
        }
        @keyframes pulse {
            0%, 100% { opacity: 1; transform: scale(1); }
            50% { opacity: 0.5; transform: scale(1.2); }
        }
        .recording-time { font-size: 16px; font-weight: 500; color: var(--text-color); font-variant-numeric: tabular-nums; min-width: 50px; }
        .recording-cancel {
            padding: 8px 16px;
            background: transparent;
            border: 1px solid var(--secondary-text, #54656f);
            border-radius: 20px;
            color: var(--secondary-text, #54656f);
            cursor: pointer;
            font-size: 13px;
            transition: all 0.2s;
        }
        .recording-cancel:hover { background: rgba(0,0,0,0.05); }
        .recording-send {
            padding: 8px 16px;
            background: var(--send-icon-fill, #00a884);
            border: none;
            border-radius: 20px;
            color: white;
            cursor: pointer;
            font-size: 13px;
            font-weight: 500;
            transition: all 0.2s;
        }
        .recording-send:hover { background: var(--accent-strong); }
        .mic-btn.recording svg { fill: #f44336 !important; }
        #video-note-ui {
            display: none;
            position: fixed;
            bottom: var(--bubble-bottom, 70px);
            left: 50%;
            transform: translateX(-50%);
            background: var(--reply-preview-bg);
            border: 1px solid var(--input-border);
            border-radius: 20px;
            box-shadow: 0 8px 28px rgba(0,0,0,0.28);
            padding: 14px;
            z-index: 1200;
            align-items: center;
            gap: 12px;
        }
        #video-note-ui.show { display: flex; }
        #video-note-preview {
            width: 120px;
            height: 120px;
            border-radius: 50%;
            object-fit: cover;
            background: #000;
            border: 2px solid rgba(0,0,0,0.12);
        }

        #reply-preview { display: none; background: var(--reply-preview-bg); color: var(--text-color); padding: 10px 20px; border-top: 1px solid var(--input-border); justify-content: space-between; align-items: center; transition: background 0.3s, border-color 0.3s, color 0.3s; }
        #edit-preview { display: none; background: var(--reply-preview-bg); color: var(--text-color); padding: 10px 20px; border-top: 1px solid var(--input-border); justify-content: space-between; align-items: center; transition: background 0.3s, border-color 0.3s, color 0.3s; border-top-color: #ff9800; }

        #key-overlay { position: fixed; top:0; left:0; width:100%; height:100%; background:var(--bg-color, #f5f6f8); z-index:10000; display:flex; justify-content:center; align-items:center; transition: background 0.3s; }

        #new-msg-bubble {
            display: none;
            position: fixed;
            bottom: var(--bubble-bottom, 85px);
            left: 50%;
            transform: translateX(-50%);
            background: var(--accent);
            color: white;
            padding: 8px 16px;
            border-radius: 20px;
            font-size: 13px;
            box-shadow: 0 6px 18px rgba(16,163,127,0.35);
            cursor: pointer;
            z-index: 1000;
            font-weight: 700;
            animation: fadeIn 0.3s;
        }
        #scroll-down-btn {
            display: none;
            position: fixed;
            bottom: var(--bubble-bottom, 85px);
            right: 20px;
            background: var(--surface);
            color: var(--accent);
            border: 1px solid var(--hairline);
            border-radius: 50%;
            width: 42px;
            height: 42px;
            cursor: pointer;
            z-index: 1000;
            box-shadow: 0 6px 18px rgba(15,26,36,0.14);
            font-size: 20px;
            transition: opacity 0.3s, transform 0.3s;
            opacity: 0;
            transform: scale(0.8);
        }
        #scroll-down-btn.show {
            display: flex;
            align-items: center;
            justify-content: center;
            opacity: 1;
            transform: scale(1);
        }
        #scroll-down-btn:hover {
            filter: brightness(0.97);
            transform: scale(1.1);
        }
        a { color: var(--accent); }
        @keyframes fadeIn {
            from { opacity: 0; bottom: calc(var(--bubble-bottom, 85px) - 15px); }
            to   { opacity: 1; bottom: var(--bubble-bottom, 85px); }
        }
        @keyframes spin {
            from { transform: rotate(0deg); }
            to { transform: rotate(360deg); }
        }
        .spinner-icon {
            animation: spin 1s linear infinite;
            display: inline-block;
            width: 24px;
            height: 24px;
        }

        /* --- منوی هدر، سنجاق، جست‌وجو، مودال‌ها (فیچرهای جدید) --- */
        #header-actions{position:absolute;right:12px;top:50%;transform:translateY(-50%);display:flex;align-items:center;gap:7px}
        #menu-btn{background:var(--input-bg);border:none;border-radius:50%;width:38px;height:38px;cursor:pointer;font-size:22px;color:var(--text-color);display:flex;align-items:center;justify-content:center;line-height:1;transition:all .2s}
        #menu-btn:hover{filter:brightness(.95)}
        #header-menu{position:absolute;top:58px;right:12px;background:var(--surface);border:1px solid var(--hairline);border-radius:14px;box-shadow:0 12px 32px rgba(15,26,36,.16);padding:6px;display:none;flex-direction:column;z-index:1300;min-width:215px}
        #header-menu.show{display:flex}
        #header-menu button{background:transparent;border:none;text-align:right;padding:11px 14px;border-radius:10px;font-size:14px;color:var(--text-color);cursor:pointer;font-family:inherit}
        #header-menu button:hover{background:var(--input-bg)}
        #header-menu .menu-danger{color:#e5484d}

        #pin-bar{display:none;align-items:center;gap:8px;background:var(--surface);border-bottom:1px solid var(--hairline);padding:8px 14px;z-index:9}
        #pin-bar.show{display:flex}
        #pin-bar-main{flex:1;min-width:0;display:flex;align-items:center;gap:9px;cursor:pointer;border-right:3px solid var(--accent);padding-right:9px}
        #pin-bar .pin-ico{font-size:15px}
        #pin-bar-text{flex:1;min-width:0;font-size:13px;color:var(--text-color);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
        #pin-bar-list{display:none;background:var(--input-bg);border:none;border-radius:9px;width:32px;height:32px;cursor:pointer;color:var(--text-color);font-size:14px;align-items:center;justify-content:center}
        #pin-bar-list:hover{filter:brightness(.95)}
        #pin-bar-unpin{color:var(--secondary-text);font-size:16px;cursor:pointer;padding:0 4px}

        #search-bar{display:none;align-items:center;gap:6px;background:var(--surface);border-bottom:1px solid var(--hairline);padding:8px 12px;z-index:11}
        #search-bar.show{display:flex}
        #search-input{flex:1;border:1px solid var(--hairline);background:var(--bg-color);border-radius:12px;padding:9px 12px;font-size:15px;color:var(--text-color);outline:none;font-family:inherit}
        #search-input:focus{border-color:var(--accent)}
        #search-count{font-size:12px;color:var(--secondary-text);min-width:42px;text-align:center}
        .search-nav{background:var(--input-bg);border:none;border-radius:9px;width:34px;height:34px;cursor:pointer;color:var(--text-color);font-size:13px}
        .search-nav:hover{filter:brightness(.95)}
        .search-hit{background:var(--highlight-bg) !important;color:#0f1a24 !important}
        .search-current{outline:2px solid var(--accent);outline-offset:1px}

        #modal-backdrop{display:none;position:fixed;inset:0;background:rgba(15,26,36,.45);z-index:15000;justify-content:center;align-items:center;padding:16px;-webkit-backdrop-filter:blur(2px);backdrop-filter:blur(2px)}
        #modal-backdrop.show{display:flex}
        .modal{display:none;background:var(--surface);border:1px solid var(--hairline);border-radius:20px;padding:22px;width:100%;max-width:380px;max-height:85vh;overflow-y:auto;box-shadow:0 20px 50px rgba(15,26,36,.25)}
        .modal.show{display:block}
        .modal-title{font-size:17px;font-weight:700;margin-bottom:14px}
        .modal-subtitle{font-size:13px;font-weight:700;color:var(--secondary-text);margin:18px 0 8px}
        .modal-hint{font-size:13px;color:var(--secondary-text);margin-bottom:12px;line-height:1.7}
        .modal-input{width:100%;border:1px solid var(--hairline);background:var(--bg-color);border-radius:12px;padding:12px 14px;font-size:15px;color:var(--text-color);outline:none;margin-bottom:12px;font-family:inherit}
        .modal-input:focus{border-color:var(--accent);background:var(--surface)}
        textarea.modal-input{resize:vertical;line-height:1.9}
        .modal-primary{width:100%;background:var(--accent);color:#fff;border:none;padding:13px;border-radius:12px;font-weight:700;font-size:15px;cursor:pointer;font-family:inherit}
        .modal-primary:hover{background:var(--accent-strong)}
        .modal-close{width:100%;background:transparent;border:1px solid var(--hairline);color:var(--secondary-text);padding:11px;border-radius:12px;font-size:14px;cursor:pointer;margin-top:12px;font-family:inherit}

        #wallpaper-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:10px}
        .wp-swatch{height:62px;border-radius:14px;cursor:pointer;border:2px solid transparent;transition:transform .15s}
        .wp-swatch:hover{transform:scale(1.05)}
        .wp-swatch.active{border-color:var(--accent);box-shadow:0 0 0 2px var(--accent)}

        .sched-item{display:flex;align-items:center;gap:10px;background:var(--bg-color);border:1px solid var(--hairline);border-radius:12px;padding:10px 12px;margin-bottom:8px}
        .sched-item .sc-text{flex:1;min-width:0;font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
        .sched-item .sc-time{font-size:11px;color:var(--secondary-text);white-space:nowrap}
        .sched-item .sc-cancel{background:transparent;border:none;color:#e5484d;cursor:pointer;font-size:18px}
        .sched-empty{color:var(--secondary-text);font-size:13px;text-align:center;padding:6px}

        .checklist{min-width:210px}
        .checklist-title{font-weight:700;font-size:14px;margin-bottom:8px}
        .checklist-item{display:flex;align-items:flex-start;gap:8px;padding:4px 0;cursor:pointer;font-size:14px;line-height:1.5}
        .checklist-item input{width:18px;height:18px;margin-top:2px;accent-color:var(--accent);cursor:pointer;flex-shrink:0}
        .checklist-item.done span{text-decoration:line-through;opacity:.55}

    </style>
    <script>
        // بارگذاری تم از localStorage
        const theme = localStorage.getItem('theme') || 'light';
        if (theme === 'dark') {
            document.documentElement.setAttribute('data-theme', 'dark');
        }
    </script>
</head>
<body>

<div id="key-overlay">
    <div id="key-overlay-card" style="padding:35px; border-radius:28px; width:340px; text-align:center; box-shadow:0 20px 50px rgba(0,0,0,0.3);">
        <h3 id="key-overlay-title" style="margin-top:0;">🔐 بازگشایی گفت‌وگو</h3>
        <input type="password" id="kInp" style="width:100%; padding:15px; margin-bottom:20px; border-radius:14px; text-align:center; font-size:18px;" placeholder="کلید محرمانه">
        <button onclick="startChat()" style="width:100%; background:var(--accent); color:white; border:none; padding:15px; border-radius:14px; font-weight:700; cursor:pointer; font-size:15px;">تایید</button>
    </div>
</div>

<div id="header">
    <button class="theme-toggle" onclick="toggleTheme()" title="تغییر تم">🌙</button>
    <b id="room-title">این‌چت</b>
    <div id="status-bar">درحال اتصال...</div>
    <div id="header-actions">
        <button id="call-audio-btn" class="call-hdr-btn" style="display:none" onpointerdown="event.preventDefault();" onclick="startCall('audio')" title="تماس صوتی">
            <svg viewBox="0 0 24 24"><path d="M6.62 10.79c1.44 2.83 3.76 5.14 6.59 6.59l2.2-2.2c.27-.27.67-.36 1.02-.24 1.12.37 2.33.57 3.57.57.55 0 1 .45 1 1V20c0 .55-.45 1-1 1-9.39 0-17-7.61-17-17 0-.55.45-1 1-1h3.5c.55 0 1 .45 1 1 0 1.25.2 2.45.57 3.57.11.35.03.74-.25 1.02l-2.2 2.2z"/></svg>
        </button>
        <button id="call-video-btn" class="call-hdr-btn" style="display:none" onpointerdown="event.preventDefault();" onclick="startCall('video')" title="تماس تصویری">
            <svg viewBox="0 0 24 24"><path d="M17 10.5V7c0-.55-.45-1-1-1H4c-.55 0-1 .45-1 1v10c0 .55.45 1 1 1h12c.55 0 1-.45 1-1v-3.5l4 4v-11l-4 4z"/></svg>
        </button>
        <button id="menu-btn" onpointerdown="event.preventDefault();" onclick="toggleHeaderMenu(event)" title="منو">⋮</button>
    </div>
    <div id="header-menu">
        <button onpointerdown="event.preventDefault();" onclick="openSearch()">🔍 جست‌وجو در گفت‌وگو</button>
        <button onpointerdown="event.preventDefault();" onclick="openChecklist()">☑️ چک‌لیست مشترک</button>
        <button onpointerdown="event.preventDefault();" onclick="openScheduled()">⏰ پیام‌های زمان‌بندی‌شده</button>
        <button onpointerdown="event.preventDefault();" onclick="openWallpaper()">🎨 پس‌زمینهٔ گفت‌وگو</button>
        <button class="menu-danger" onpointerdown="event.preventDefault();" onclick="location.href='/logout'">🚪 خروج</button>
    </div>
</div>

<div id="search-bar">
    <input id="search-input" type="text" placeholder="جست‌وجو..." oninput="runSearch()" autocomplete="off">
    <span id="search-count"></span>
    <button class="search-nav" onpointerdown="event.preventDefault();" onclick="searchStep(-1)" title="قبلی">▲</button>
    <button class="search-nav" onpointerdown="event.preventDefault();" onclick="searchStep(1)" title="بعدی">▼</button>
    <button class="search-nav" onpointerdown="event.preventDefault();" onclick="closeSearch()" title="بستن">✕</button>
</div>

<div id="pin-bar">
    <div id="pin-bar-main" onclick="pinBarGo()">
        <span class="pin-ico">📌</span>
        <div id="pin-bar-text"></div>
    </div>
    <button id="pin-bar-list" onpointerdown="event.preventDefault();" onclick="openPinnedList(event)" title="همهٔ پیام‌های سنجاق‌شده">☰</button>
    <span id="pin-bar-unpin" onpointerdown="event.preventDefault();" onclick="pinBarUnpin(event)" title="برداشتن سنجاق">✕</span>
</div>

<div id="chat-box" onscroll="handleScroll()"></div>
<div id="typing-status"></div>

<div id="reply-preview">
    <div style="border-right: 4px solid var(--accent); padding-right: 10px;">
        <div style="font-size:12px; color:var(--accent); font-weight:700;">پاسخ به:</div>
        <div id="reply-text" style="font-size:13px; color:var(--secondary-text);"></div>
    </div>
    <span onpointerdown="event.preventDefault();" onclick="cancelReply(true)" style="cursor:pointer; font-size:20px; color:var(--secondary-text);">✕</span>
</div>
<div id="edit-preview">
    <div style="border-right: 4px solid #ff9800; padding-right: 10px;">
        <div style="font-size:12px; color:#ff9800; font-weight:700;">در حال ویرایش:</div>
        <div id="edit-text" style="font-size:13px; color:var(--secondary-text);"></div>
    </div>
    <span onpointerdown="event.preventDefault();" onclick="cancelEdit(true)" style="cursor:pointer; font-size:20px; color:var(--secondary-text);">✕</span>
</div>
<div id="new-msg-bubble" onpointerdown="event.preventDefault();" onclick="scrollToBottom()">پیام جدید 👇</div>
<div id="scroll-down-btn" onpointerdown="event.preventDefault();" onclick="scrollToBottom()" title="اسکرول به پایین">⬇</div>
<div id="recording-ui">
    <div class="recording-indicator"></div>
    <span class="recording-time" id="recording-time">0:00</span>
    <button class="recording-cancel" onclick="cancelRecording()">انصراف</button>
    <button class="recording-send" onclick="sendRecording()">ارسال</button>
</div>
<div id="video-note-ui">
    <video id="video-note-preview" muted autoplay playsinline></video>
    <button class="recording-cancel" onclick="cancelVideoNote()">انصراف</button>
    <button class="recording-send" onclick="sendVideoNote()">ارسال</button>
</div>
<div id="input-container">
    <button class="icon-btn send-btn" onpointerdown="event.preventDefault();" onclick="sendTxt()">
        <svg viewBox="0 0 24 24"><path d="M2.01 21L23 12 2.01 3 2 10l15 2-15 2z"/></svg>
    </button>
    <div id="composer-wrap">
        <div id="msgInput" contenteditable="true" dir="auto" data-placeholder="پیام بنویسید..." role="textbox" aria-multiline="true"></div>
    </div>
    <button class="icon-btn" id="video-note-btn" onpointerdown="event.preventDefault();" onclick="toggleVideoNoteRecording()" title="Video Note">
        <svg viewBox="0 0 24 24"><path d="M17 10.5V7c0-.55-.45-1-1-1H4c-.55 0-1 .45-1 1v10c0 .55.45 1 1 1h12c.55 0 1-.45 1-1v-3.5l4 4v-11l-4 4z"/></svg>
    </button>
    <button class="icon-btn mic-btn" id="mic-btn" onpointerdown="event.preventDefault();" onclick="toggleRecording()">
        <svg viewBox="0 0 24 24"><path d="M12 14c1.66 0 3-1.34 3-3V5c0-1.66-1.34-3-3-3S9 3.34 9 5v6c0 1.66 1.34 3 3 3zm-1-9c0-.55.45-1 1-1s1 .45 1 1v6c0 .55-.45 1-1 1s-1-.45-1-1V5zm6 6c0 2.76-2.24 5-5 5s-5-2.24-5-5H5c0 3.53 2.61 6.43 6 6.92V21h2v-3.08c3.39-.49 6-3.39 6-6.92h-2z"/></svg>
    </button>
    <button class="icon-btn" onclick="document.getElementById('fInp').click()" title="ارسال فایل">
        <svg viewBox="0 0 24 24"><path d="M19 7v2.99s-1.99.01-2 0V7h-3s.01-1.99 0-2h3V2h2v3h3v2h-3zm-3 4V8h-3V5H5c-1.1 0-2 .9-2 2v12c0 1.1.9 2 2 2h12c1.1 0 2-.9 2-2v-8h-3zM5 19l3-4 2 3 3-4 4 5H5z"/></svg>
    </button>
    <input type="file" id="fInp" hidden onchange="sendAttachment(this)">
</div>
<div id="copy-bubble">✓ کپی شد</div>

<!-- مودال‌های فیچرها -->
<div id="modal-backdrop" onclick="closeModals(event)">
    <div id="wallpaper-modal" class="modal" onclick="event.stopPropagation()">
        <div class="modal-title">🎨 پس‌زمینهٔ گفت‌وگو</div>
        <div id="wallpaper-grid"></div>
        <button class="modal-close" onclick="closeModals()">بستن</button>
    </div>

    <div id="scheduled-modal" class="modal" onclick="event.stopPropagation()">
        <div class="modal-title">⏰ ارسال زمان‌بندی‌شده</div>
        <div class="modal-hint">متن داخل کادر پیام را در زمان دلخواه ارسال کن.</div>
        <input id="schedule-time" type="datetime-local" class="modal-input">
        <button class="modal-primary" onclick="scheduleCurrentText()">زمان‌بندی متن کادر پیام</button>
        <div class="modal-subtitle">در صف ارسال</div>
        <div id="scheduled-list"></div>
        <button class="modal-close" onclick="closeModals()">بستن</button>
    </div>

    <div id="pinned-modal" class="modal" onclick="event.stopPropagation()">
        <div class="modal-title">📌 پیام‌های سنجاق‌شده</div>
        <div id="pinned-list"></div>
        <button class="modal-close" onclick="closeModals()">بستن</button>
    </div>

    <div id="checklist-modal" class="modal" onclick="event.stopPropagation()">
        <div class="modal-title">☑️ چک‌لیست مشترک</div>
        <input id="checklist-title" class="modal-input" maxlength="80" placeholder="عنوان (مثلاً: خرید خونه)">
        <textarea id="checklist-items" class="modal-input" rows="5" placeholder="هر آیتم در یک خط&#10;شیر&#10;نان&#10;تخم‌مرغ"></textarea>
        <button class="modal-primary" onclick="sendChecklist()">ارسال چک‌لیست</button>
        <button class="modal-close" onclick="closeModals()">بستن</button>
    </div>
</div>
<div id="reaction-menu" class="reaction-menu">
    <span class="reaction-emoji" onclick="selectReaction('❤️')">❤️</span>
    <span class="reaction-emoji" onclick="selectReaction('👍')">👍</span>
    <span class="reaction-emoji" onclick="selectReaction('😂')">😂</span>
    <span class="reaction-emoji" onclick="selectReaction('😮')">😮</span>
    <span class="reaction-emoji" onclick="selectReaction('😢')">😢</span>
</div>
<div id="composer-context-menu">
    <button class="composer-menu-btn" type="button" onpointerdown="event.preventDefault();" onclick="runComposerMenuAction('regular')">Tx</button>
    <button class="composer-menu-btn" type="button" onpointerdown="event.preventDefault();" onclick="runComposerMenuAction('bold')">B</button>
    <button class="composer-menu-btn" type="button" onpointerdown="event.preventDefault();" onclick="runComposerMenuAction('italic')">I</button>
    <button class="composer-menu-btn" type="button" onpointerdown="event.preventDefault();" onclick="runComposerMenuAction('spoiler')">🙈</button>
    <button class="composer-menu-btn" type="button" onpointerdown="event.preventDefault();" onclick="runComposerMenuAction('link')">🔗</button>
</div>

<!-- ============ تماس صوتی/تصویری (WebRTC) ============ -->
<style>
#call-screen{position:fixed;inset:0;z-index:100000;background:#0b141a;display:none;flex-direction:column;overflow:hidden}
#call-screen.show{display:flex}
#call-remote-video{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;background:#0b141a}
#call-screen.audio-only #call-remote-video{display:none}
#call-local-video{position:absolute;top:18px;left:18px;width:104px;height:150px;object-fit:cover;border-radius:14px;background:#1b2a33;box-shadow:0 6px 20px rgba(0,0,0,.45);z-index:3;transform:scaleX(-1);transition:opacity .2s}
#call-screen.audio-only #call-local-video{display:none}
#call-overlay-top{position:absolute;top:0;left:0;right:0;z-index:4;padding:34px 22px 60px;text-align:center;color:#fff;background:linear-gradient(180deg,rgba(0,0,0,.55),transparent);pointer-events:none}
#call-avatar{width:118px;height:118px;border-radius:50%;margin:6vh auto 18px;background:linear-gradient(135deg,#2aabee,#1c84c6);display:flex;align-items:center;justify-content:center;font-size:54px;color:#fff;box-shadow:0 10px 40px rgba(0,0,0,.5)}
#call-screen:not(.audio-only) #call-avatar{display:none}
#call-peer-name{font-size:23px;font-weight:700;margin-bottom:8px;text-shadow:0 1px 6px rgba(0,0,0,.6)}
#call-status-text{font-size:15px;opacity:.92;text-shadow:0 1px 6px rgba(0,0,0,.6)}
#call-quality{display:inline-flex;align-items:center;gap:5px;margin-top:10px;font-size:12.5px;opacity:.9}
#call-quality .dot{width:8px;height:8px;border-radius:50%;background:#4caf50}
#call-quality.medium .dot{background:#ffb300}
#call-quality.bad .dot{background:#f44336}
#call-controls{position:absolute;bottom:0;left:0;right:0;z-index:4;padding:26px 22px calc(30px + env(safe-area-inset-bottom));display:flex;justify-content:center;gap:22px;background:linear-gradient(0deg,rgba(0,0,0,.6),transparent)}
.call-btn{width:62px;height:62px;border-radius:50%;border:none;cursor:pointer;display:flex;align-items:center;justify-content:center;background:rgba(255,255,255,.18);backdrop-filter:blur(6px);transition:transform .12s,background .15s}
.call-btn:active{transform:scale(.9)}
.call-btn svg{width:27px;height:27px;fill:#fff}
.call-btn.off{background:#fff}
.call-btn.off svg{fill:#0b141a}
.call-btn.hangup{background:#f44336}
.call-btn.accept{background:#4caf50}
#call-incoming{position:fixed;inset:0;z-index:100001;background:rgba(11,20,26,.97);display:none;flex-direction:column;align-items:center;justify-content:center;color:#fff}
#call-incoming.show{display:flex}
#call-incoming .ring-avatar{width:124px;height:124px;border-radius:50%;background:linear-gradient(135deg,#2aabee,#1c84c6);display:flex;align-items:center;justify-content:center;font-size:58px;margin-bottom:24px;animation:callPulse 1.4s ease-in-out infinite}
@keyframes callPulse{0%,100%{box-shadow:0 0 0 0 rgba(42,171,238,.55)}50%{box-shadow:0 0 0 24px rgba(42,171,238,0)}}
#call-incoming .ring-name{font-size:24px;font-weight:700;margin-bottom:6px}
#call-incoming .ring-sub{font-size:15px;opacity:.85;margin-bottom:48px}
#call-incoming .ring-actions{display:flex;gap:64px}
.ring-action{display:flex;flex-direction:column;align-items:center;gap:10px;font-size:13px;color:#fff;cursor:pointer}
.call-hdr-btn{background:var(--input-bg);border:none;border-radius:50%;width:38px;height:38px;cursor:pointer;padding:0;display:flex;align-items:center;justify-content:center;transition:all .2s}
.call-hdr-btn:hover{filter:brightness(.95);transform:scale(1.06)}
.call-hdr-btn:active{transform:scale(.94)}
.call-hdr-btn svg{width:21px;height:21px;fill:var(--accent)}
</style>
<div id="call-incoming">
    <div class="ring-avatar" id="ring-avatar">📞</div>
    <div class="ring-name" id="ring-name">تماس ورودی</div>
    <div class="ring-sub" id="ring-sub">تماس صوتی</div>
    <div class="ring-actions">
        <div class="ring-action" onclick="declineIncoming()">
            <button class="call-btn hangup"><svg viewBox="0 0 24 24"><path d="M12 9c-1.6 0-3.15.25-4.6.72v3.1c0 .39-.23.74-.56.9-.98.49-1.87 1.12-2.66 1.85-.18.18-.43.28-.7.28-.28 0-.53-.11-.71-.29L.29 13.08c-.18-.17-.29-.42-.29-.7 0-.28.11-.53.29-.71C3.34 8.78 7.46 7 12 7s8.66 1.78 11.71 4.67c.18.18.29.43.29.71 0 .28-.11.53-.29.7l-2.48 2.48c-.18.18-.43.29-.71.29-.27 0-.52-.11-.7-.28-.79-.74-1.69-1.36-2.67-1.85-.33-.16-.56-.51-.56-.9v-3.1C15.15 9.25 13.6 9 12 9z"/></svg></button>
            <span>رد تماس</span>
        </div>
        <div class="ring-action" onclick="acceptIncoming()">
            <button class="call-btn accept"><svg viewBox="0 0 24 24"><path d="M6.62 10.79c1.44 2.83 3.76 5.14 6.59 6.59l2.2-2.2c.27-.27.67-.36 1.02-.24 1.12.37 2.33.57 3.57.57.55 0 1 .45 1 1V20c0 .55-.45 1-1 1-9.39 0-17-7.61-17-17 0-.55.45-1 1-1H7.5c.55 0 1 .45 1 1 0 1.25.2 2.45.57 3.57.11.35.03.74-.25 1.02l-2.2 2.2z"/></svg></button>
            <span>پاسخ</span>
        </div>
    </div>
</div>
<div id="call-screen">
    <video id="call-remote-video" autoplay playsinline></video>
    <video id="call-local-video" autoplay playsinline muted></video>
    <audio id="call-remote-audio" autoplay></audio>
    <div id="call-overlay-top">
        <div id="call-avatar">👤</div>
        <div id="call-peer-name">طرف مقابل</div>
        <div id="call-status-text">در حال اتصال…</div>
        <div id="call-quality"><span class="dot"></span><span id="call-quality-text">عالی</span></div>
    </div>
    <div id="call-controls">
        <button class="call-btn" id="call-mic-btn" onclick="toggleMic()" title="میکروفون">
            <svg viewBox="0 0 24 24"><path d="M12 14c1.66 0 3-1.34 3-3V5c0-1.66-1.34-3-3-3S9 3.34 9 5v6c0 1.66 1.34 3 3 3zm5-3c0 2.76-2.24 5-5 5s-5-2.24-5-5H5c0 3.53 2.61 6.43 6 6.92V21h2v-3.08c3.39-.49 6-3.39 6-6.92h-2z"/></svg>
        </button>
        <button class="call-btn" id="call-cam-btn" onclick="toggleCam()" title="دوربین">
            <svg viewBox="0 0 24 24"><path d="M17 10.5V7c0-.55-.45-1-1-1H4c-.55 0-1 .45-1 1v10c0 .55.45 1 1 1h12c.55 0 1-.45 1-1v-3.5l4 4v-11l-4 4z"/></svg>
        </button>
        <button class="call-btn hangup" onclick="hangupCall()" title="پایان تماس">
            <svg viewBox="0 0 24 24"><path d="M12 9c-1.6 0-3.15.25-4.6.72v3.1c0 .39-.23.74-.56.9-.98.49-1.87 1.12-2.66 1.85-.18.18-.43.28-.7.28-.28 0-.53-.11-.71-.29L.29 13.08c-.18-.17-.29-.42-.29-.7 0-.28.11-.53.29-.71C3.34 8.78 7.46 7 12 7s8.66 1.78 11.71 4.67c.18.18.29.43.29.71 0 .28-.11.53-.29.7l-2.48 2.48c-.18.18-.43.29-.71.29-.27 0-.52-.11-.7-.28-.79-.74-1.69-1.36-2.67-1.85-.33-.16-.56-.51-.56-.9v-3.1C15.15 9.25 13.6 9 12 9z"/></svg>
        </button>
    </div>
</div>

<script>
    // تابع تغییر تم
    function toggleTheme() {
        const currentTheme = document.documentElement.getAttribute('data-theme');
        const newTheme = currentTheme === 'dark' ? 'light' : 'dark';
        document.documentElement.setAttribute('data-theme', newTheme);
        localStorage.setItem('theme', newTheme);
        
        // تغییر آیکون دکمه
        const themeBtn = document.querySelector('.theme-toggle');
        if (themeBtn) {
            themeBtn.textContent = newTheme === 'dark' ? '☀️' : '🌙';
        }
        
        // به‌روزرسانی overlay key
        updateKeyOverlayTheme(newTheme);
        // والپیپر را با تم جدید دوباره اعمال کن
        if (typeof loadWallpaper === 'function') loadWallpaper();
    }

    function updateKeyOverlayTheme(theme) {
        const card = document.getElementById('key-overlay-card');
        const title = document.getElementById('key-overlay-title');
        const input = document.getElementById('kInp');
        
        if (card && title && input) {
            const cardBg = getComputedStyle(document.documentElement).getPropertyValue('--card-bg') || (theme === 'dark' ? '#1e1e1e' : 'white');
            const textColor = getComputedStyle(document.documentElement).getPropertyValue('--text-color') || (theme === 'dark' ? '#e0e0e0' : '#263238');
            const inputBorder = getComputedStyle(document.documentElement).getPropertyValue('--input-border') || (theme === 'dark' ? '#424242' : '#cfd8dc');
            const inputBg = getComputedStyle(document.documentElement).getPropertyValue('--input-bg') || (theme === 'dark' ? '#2a3942' : 'white');
            
            card.style.background = cardBg.trim() || (theme === 'dark' ? '#1e1e1e' : 'white');
            card.style.transition = 'background 0.3s';
            title.style.color = textColor.trim() || (theme === 'dark' ? '#e0e0e0' : '#263238');
            title.style.transition = 'color 0.3s';
            input.style.border = `1px solid ${inputBorder.trim() || (theme === 'dark' ? '#424242' : '#cfd8dc')}`;
            input.style.background = inputBg.trim() || (theme === 'dark' ? '#2a3942' : 'white');
            input.style.color = textColor.trim() || (theme === 'dark' ? '#e0e0e0' : '#263238');
            input.style.transition = 'all 0.3s';
        }
    }
    
    // تنظیم آیکون اولیه
    document.addEventListener('DOMContentLoaded', function() {
        const currentTheme = document.documentElement.getAttribute('data-theme') || 'light';
        const themeBtn = document.querySelector('.theme-toggle');
        if (themeBtn) {
            themeBtn.textContent = currentTheme === 'dark' ? '☀️' : '🌙';
        }
        updateKeyOverlayTheme(currentTheme);
        updateFavicon();

        if (!SHOW_MEDIA_BUTTONS) {
            document.getElementById('mic-btn').style.display = 'none';
            document.getElementById('video-note-btn').style.display = 'none';
        }

        // جلوگیری از بسته شدن کیبورد در موبایل هنگام کلیک/تاچ روی صفحه
        const msgInput = document.getElementById('msgInput');
        if (msgInput) {
            // mousedown: جلوگیری از blur هنگام کلیک (دسکتاپ و اندروید)
            document.addEventListener('mousedown', function(e) {
                if (window.innerWidth > 768) return;
                if (document.activeElement !== msgInput) return;
                const t = e.target;
                if (t === msgInput || t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT') return;
                e.preventDefault();
            });
            // touchstart روی chat-box: از preventDefault استفاده نمی‌کنیم تا اسکرول نشکنه
            // به جایش بعد از touchend فوکوس رو برمی‌گردونیم (iOS Safari)
            let inputHadFocus = false;
            msgInput.addEventListener('focus', function() { inputHadFocus = true; });
            msgInput.addEventListener('blur', function() { inputHadFocus = false; });
            msgInput.addEventListener('input', handleComposerInput);
            msgInput.addEventListener('keyup', saveComposerSelection);
            msgInput.addEventListener('mouseup', saveComposerSelection);
            msgInput.addEventListener('contextmenu', function(e) {
                if (!hasMeaningfulSelection()) {
                    hideComposerContextMenu();
                    return;
                }
                e.preventDefault();
                saveComposerSelection();
                showComposerContextMenu(e.clientX, e.clientY);
            });
            document.addEventListener('selectionchange', function() {
                const selection = window.getSelection();
                if (!selection || selection.rangeCount === 0) {
                    hideComposerContextMenu();
                    return;
                }
                const range = selection.getRangeAt(0);
                if (range.collapsed) {
                    hideComposerContextMenu();
                    return;
                }
                if (msgInput.contains(range.commonAncestorContainer)) {
                    composerSelectionRange = range.cloneRange();
                } else {
                    hideComposerContextMenu();
                }
            });
            document.getElementById('chat-box').addEventListener('touchend', function(e) {
                if (!inputHadFocus) return;
                const t = e.target;
                if (t === msgInput || t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT') return;
                if (t.closest('.msg-actions') || t.closest('.reaction-menu') || t.tagName === 'BUTTON' || t.tagName === 'A') return;
                // بازگرداندن فوکوس بدون اسکرول
                setTimeout(function() { msgInput.focus({ preventScroll: true }); }, 50);
            }, { passive: true });
            autoGrow(msgInput);
        }
    });

    let myId = "ME";
    let CHAT_KEY = "";
    let lastTime = 0;
    let lastUpdated = 0;
    let replyingTo = null;
    let editingTo = null;
    let autoScroll = true;
    let unreadCount = 0;
    let hasFetchedOnce = false;
    const APP_TITLE = "این‌چت";
    let mobileKeyboardWasOpen = false;
    let pendingUploadCounter = 0;
    let composerSelectionRange = null;
    const textMessagePayloads = new Map();
    let composerMenuCloseHandler = null;

    // ── تنظیم نمایش دکمه‌های ویس و ویدیومسیج ──────────────────────────
    const SHOW_MEDIA_BUTTONS = true;  // false = مخفی | true = نمایش

    function roundRectPath(ctx, x, y, w, h, r) {
        if (ctx.roundRect) {
            ctx.beginPath();
            ctx.roundRect(x, y, w, h, r);
            return;
        }
        const radius = Math.min(r, w / 2, h / 2);
        ctx.beginPath();
        ctx.moveTo(x + radius, y);
        ctx.lineTo(x + w - radius, y);
        ctx.quadraticCurveTo(x + w, y, x + w, y + radius);
        ctx.lineTo(x + w, y + h - radius);
        ctx.quadraticCurveTo(x + w, y + h, x + w - radius, y + h);
        ctx.lineTo(x + radius, y + h);
        ctx.quadraticCurveTo(x, y + h, x, y + h - radius);
        ctx.lineTo(x, y + radius);
        ctx.quadraticCurveTo(x, y, x + radius, y);
        ctx.closePath();
    }

    function buildFavicon(showUnreadDot = false) {
        const canvas = document.createElement('canvas');
        canvas.width = 64;
        canvas.height = 64;
        const ctx = canvas.getContext('2d');
        if (!ctx) return "";

        const grad = ctx.createLinearGradient(0, 0, 64, 64);
        grad.addColorStop(0, '#00a884');
        grad.addColorStop(1, '#005c4b');
        ctx.fillStyle = grad;
        roundRectPath(ctx, 4, 4, 56, 56, 18);
        ctx.fill();

        ctx.fillStyle = '#ffffff';
        roundRectPath(ctx, 13, 18, 38, 27, 9);
        ctx.fill();

        ctx.beginPath();
        ctx.moveTo(25, 45);
        ctx.lineTo(19, 53);
        ctx.lineTo(20, 44);
        ctx.closePath();
        ctx.fill();

        ctx.fillStyle = '#00a884';
        [22, 32, 42].forEach((x) => {
            ctx.beginPath();
            ctx.arc(x, 31, 2.8, 0, Math.PI * 2);
            ctx.fill();
        });

        if (showUnreadDot) {
            ctx.fillStyle = '#f44336';
            ctx.beginPath();
            ctx.arc(51, 13, 10, 0, Math.PI * 2);
            ctx.fill();
            ctx.strokeStyle = '#ffffff';
            ctx.lineWidth = 3;
            ctx.stroke();
        }

        return canvas.toDataURL('image/png');
    }

    function getFaviconElement() {
        let favicon = document.getElementById('app-favicon');
        if (!favicon) {
            favicon = document.querySelector("link[rel*='icon']");
        }
        if (!favicon) {
            favicon = document.createElement('link');
            favicon.rel = 'icon';
            document.head.appendChild(favicon);
        }
        favicon.id = 'app-favicon';
        favicon.type = 'image/png';
        return favicon;
    }

    function updateFavicon() {
        const favicon = getFaviconElement();
        favicon.href = buildFavicon(unreadCount > 0);
        const badgeText = unreadCount > 99 ? '99+' : String(unreadCount);
        document.title = unreadCount > 0 ? `(${badgeText}) ${APP_TITLE}` : APP_TITLE;
    }

    function isWindowInactive() {
        return document.hidden || !document.hasFocus();
    }

    function clearUnread() {
        if (unreadCount === 0) return;
        unreadCount = 0;
        updateFavicon();
    }

    function onWindowActivityChanged() {
        if (!isWindowInactive() && autoScroll) {
            clearUnread();
        }
    }

    function isEditableElement(el) {
        return !!el && (
            el.tagName === 'INPUT' ||
            el.tagName === 'TEXTAREA' ||
            el.isContentEditable
        );
    }

    function shouldHandleMobileKeyboard() {
        return window.matchMedia && window.matchMedia('(pointer: coarse)').matches;
    }

    function updateAppHeight(){
        const vv = window.visualViewport;
        const h = vv ? vv.height : window.innerHeight;
        document.documentElement.style.setProperty('--app-height', h + 'px');
        const inputH = document.getElementById('input-container')?.offsetHeight || 0;
        const keyboardH = vv ? Math.max(0, window.innerHeight - vv.height - (vv.offsetTop || 0)) : 0;
        const bottom = keyboardH + inputH + 12;
        document.documentElement.style.setProperty('--bubble-bottom', bottom + 'px');

        const keyboardOpen = keyboardH > 120;
        if (shouldHandleMobileKeyboard() && mobileKeyboardWasOpen && !keyboardOpen && isEditableElement(document.activeElement)) {
            document.activeElement.blur();
        }
        mobileKeyboardWasOpen = keyboardOpen;
    }

    updateAppHeight();

    window.addEventListener('resize', updateAppHeight);
    if (window.visualViewport) {
        window.visualViewport.addEventListener('resize', updateAppHeight);
        window.visualViewport.addEventListener('scroll', updateAppHeight);
    }

    let pollTimer = null;
    function schedulePoll(){
        if (pollTimer) clearInterval(pollTimer);
        const interval = document.hidden ? 30000 : 2000;
        pollTimer = setInterval(fetchMessages, interval);
    }

    function handleVisibilityChange() {
        schedulePoll();
        onWindowActivityChanged();
    }

    function startChat() {
        let v = document.getElementById('kInp').value;
        if(!v) return;
        CHAT_KEY = v;
        document.getElementById('key-overlay').style.display = 'none';
        updateFavicon();
        loadWallpaper();
        schedulePoll();
        document.addEventListener('visibilitychange', handleVisibilityChange);
        window.addEventListener('focus', onWindowActivityChanged);
        window.addEventListener('blur', onWindowActivityChanged);
        setTimeout(() => handleScroll(), 500);
    }

    // --- صدای بیپ ---
    function playDing() {
        try {
            const ctx = new (window.AudioContext || window.webkitAudioContext)();
            const osc = ctx.createOscillator();
            const gain = ctx.createGain();
            osc.connect(gain); gain.connect(ctx.destination);
            osc.type = 'sine';
            osc.frequency.setValueAtTime(580, ctx.currentTime);
            gain.gain.setValueAtTime(0, ctx.currentTime);
            gain.gain.linearRampToValueAtTime(0.1, ctx.currentTime + 0.01);
            gain.gain.exponentialRampToValueAtTime(0.01, ctx.currentTime + 0.4);
            osc.start(); osc.stop(ctx.currentTime + 0.5);
        } catch(e) {}
    }

    let copyBubbleTimer = null;
    function showCopyBubble(){
        const b = document.getElementById('copy-bubble');
        b.style.display = 'block';
        b.style.opacity = '1';
        if (copyBubbleTimer) clearTimeout(copyBubbleTimer);
        copyBubbleTimer = setTimeout(() => {
            b.style.display = 'none';
        }, 1200);
    }

    // --- رمزنگاری بهبود یافته با PBKDF2 + AES-like ---
    async function deriveKey(password) {
        const encoder = new TextEncoder();
        const keyMaterial = await crypto.subtle.importKey(
            'raw',
            encoder.encode(password),
            'PBKDF2',
            false,
            ['deriveBits', 'deriveKey']
        );
        return await crypto.subtle.deriveKey(
            {
                name: 'PBKDF2',
                salt: encoder.encode('chat_secure_salt_2024'),
                iterations: 100000,
                hash: 'SHA-256'
            },
            keyMaterial,
            { name: 'AES-GCM', length: 256 },
            false,
            ['encrypt', 'decrypt']
        );
    }

    let cryptoKey = null;
    
    async function initCrypto() {
        if (CHAT_KEY && !cryptoKey) {
            try {
                cryptoKey = await deriveKey(CHAT_KEY);
            } catch(e) {
                console.warn('Web Crypto not available, falling back to RC4');
            }
        }
    }

    // RC4 fallback برای مرورگرهای قدیمی
    function rc4(key, str) {
        var s = [], j = 0, x, res = '';
        for (var i = 0; i < 256; i++) s[i] = i;
        for (i = 0; i < 256; i++) {
            j = (j + s[i] + key.charCodeAt(i % key.length)) % 256;
            x = s[i]; s[i] = s[j]; s[j] = x;
        }
        i = 0; j = 0;
        for (var y = 0; y < str.length; y++) {
            i = (i + 1) % 256; j = (j + s[i]) % 256;
            x = s[i]; s[i] = s[j]; s[j] = x;
            res += String.fromCharCode(str.charCodeAt(y) ^ s[(s[i] + s[j]) % 256]);
        }
        return res;
    }

    async function enc(t) {
        await initCrypto();
        if (cryptoKey && window.crypto && window.crypto.subtle) {
            try {
                const encoder = new TextEncoder();
                const iv = crypto.getRandomValues(new Uint8Array(12));
                const encrypted = await crypto.subtle.encrypt(
                    { name: 'AES-GCM', iv: iv },
                    cryptoKey,
                    encoder.encode(t)
                );
                const combined = new Uint8Array(iv.length + encrypted.byteLength);
                combined.set(iv);
                combined.set(new Uint8Array(encrypted), iv.length);
                return 'AES:' + btoa(String.fromCharCode(...combined));
            } catch(e) {
                console.warn('AES encryption failed, using RC4');
            }
        }
        return btoa(rc4(CHAT_KEY, unescape(encodeURIComponent(t))));
    }

    async function dec(t) {
        if(!t) return "";
        await initCrypto();
        try {
            if (t.startsWith('AES:') && cryptoKey && window.crypto && window.crypto.subtle) {
                const data = Uint8Array.from(atob(t.slice(4)), c => c.charCodeAt(0));
                const iv = data.slice(0, 12);
                const encrypted = data.slice(12);
                const decrypted = await crypto.subtle.decrypt(
                    { name: 'AES-GCM', iv: iv },
                    cryptoKey,
                    encrypted
                );
                return new TextDecoder().decode(decrypted);
            }
            return decodeURIComponent(escape(rc4(CHAT_KEY, atob(t))));
        } catch(e) {
            return "❌";
        }
    }

    async function encryptBinary(arrayBuffer) {
        await initCrypto();
        if (!(cryptoKey && window.crypto && window.crypto.subtle)) {
            throw new Error('Secure crypto unavailable');
        }
        const iv = crypto.getRandomValues(new Uint8Array(12));
        const encrypted = await crypto.subtle.encrypt(
            { name: 'AES-GCM', iv: iv },
            cryptoKey,
            arrayBuffer
        );
        const combined = new Uint8Array(iv.length + encrypted.byteLength);
        combined.set(iv);
        combined.set(new Uint8Array(encrypted), iv.length);
        return combined;
    }

    async function decryptBinary(bytes) {
        await initCrypto();
        if (!(cryptoKey && window.crypto && window.crypto.subtle)) {
            throw new Error('Secure crypto unavailable');
        }
        const data = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
        const iv = data.slice(0, 12);
        const encrypted = data.slice(12);
        const decrypted = await crypto.subtle.decrypt(
            { name: 'AES-GCM', iv: iv },
            cryptoKey,
            encrypted
        );
        return decrypted;
    }

    function autoGrow(el) {
        if (!el) return;
        if (el.isContentEditable) {
            if (el.textContent.replace(/\u200B/g, '').trim() === '' && el.innerHTML !== '') {
                el.innerHTML = '';
            }
            el.style.height = '34px';
            el.style.height = Math.min(el.scrollHeight, 120) + 'px';
            return;
        }
        el.style.height = '34px';
        el.style.height = (el.scrollHeight) + 'px';
    }

    function getComposer() {
        return document.getElementById('msgInput');
    }

    function focusComposer() {
        const composer = getComposer();
        if (composer) composer.focus({ preventScroll: true });
    }

    function getComposerContextMenu() {
        return document.getElementById('composer-context-menu');
    }

    function clearComposer() {
        const composer = getComposer();
        if (!composer) return;
        composer.innerHTML = '';
        composer.style.height = '34px';
    }

    function getComposerPlainText() {
        const composer = getComposer();
        if (!composer) return '';
        return composer.innerText.replace(/\u00A0/g, ' ').replace(/\r/g, '').replace(/\n{3,}/g, '\n\n');
    }

    function escapeHtml(text) {
        return String(text ?? '')
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;');
    }

    function escapeAttr(text) {
        return escapeHtml(text).replace(/'/g, '&#39;');
    }

    function normalizeUrl(url) {
        const trimmed = String(url || '').trim();
        if (!trimmed) return '';
        if (/^https?:\/\//i.test(trimmed)) return trimmed;
        return 'https://' + trimmed;
    }

    function hasMeaningfulSelection() {
        const selection = window.getSelection();
        if (!selection || selection.rangeCount === 0) return false;
        const range = selection.getRangeAt(0);
        return !range.collapsed && getComposer()?.contains(range.commonAncestorContainer);
    }

    function saveComposerSelection() {
        const composer = getComposer();
        const selection = window.getSelection();
        if (!composer || !selection || selection.rangeCount === 0) return;
        const range = selection.getRangeAt(0);
        if (composer.contains(range.commonAncestorContainer)) {
            composerSelectionRange = range.cloneRange();
        }
    }

    function hideComposerContextMenu() {
        const menu = getComposerContextMenu();
        if (!menu) return;
        menu.classList.remove('show');
        menu.style.display = 'none';
        if (composerMenuCloseHandler) {
            document.removeEventListener('mousedown', composerMenuCloseHandler);
            document.removeEventListener('scroll', composerMenuCloseHandler, true);
            window.removeEventListener('resize', composerMenuCloseHandler);
            composerMenuCloseHandler = null;
        }
    }

    function restoreComposerSelection() {
        const composer = getComposer();
        if (!composer) return false;
        composer.focus({ preventScroll: true });
        const selection = window.getSelection();
        if (!selection) return false;
        selection.removeAllRanges();
        if (composerSelectionRange) {
            selection.addRange(composerSelectionRange);
            return true;
        }
        const range = document.createRange();
        range.selectNodeContents(composer);
        range.collapse(false);
        selection.addRange(range);
        composerSelectionRange = range.cloneRange();
        return true;
    }

    function syncComposerSelectionSoon() {
        requestAnimationFrame(() => {
            saveComposerSelection();
        });
    }

    function insertComposerLineBreak() {
        restoreComposerSelection();
        if (document.execCommand) {
            document.execCommand('insertLineBreak');
        } else {
            const selection = window.getSelection();
            if (!selection || selection.rangeCount === 0) return;
            const range = selection.getRangeAt(0);
            range.deleteContents();
            range.insertNode(document.createElement('br'));
            range.collapse(false);
            selection.removeAllRanges();
            selection.addRange(range);
        }
        handleComposerInput();
    }

    function applyComposerCommand(command, value = null) {
        restoreComposerSelection();
        if (document.execCommand) {
            document.execCommand(command, false, value);
        }
        handleComposerInput();
        focusComposer();
        syncComposerSelectionSoon();
        hideComposerContextMenu();
    }

    function unwrapComposerSpoilersInRange() {
        const composer = getComposer();
        const selection = window.getSelection();
        if (!composer || !selection || selection.rangeCount === 0) return;
        const range = selection.getRangeAt(0);
        const spoilers = Array.from(composer.querySelectorAll('[data-spoiler]'));
        spoilers.forEach((node) => {
            if (!range.intersectsNode(node)) return;
            const parent = node.parentNode;
            if (!parent) return;
            while (node.firstChild) {
                parent.insertBefore(node.firstChild, node);
            }
            parent.removeChild(node);
        });
    }

    function clearComposerFormatting() {
        if (!restoreComposerSelection() || !hasMeaningfulSelection()) return;
        if (document.execCommand) {
            document.execCommand('removeFormat', false, null);
            document.execCommand('unlink', false, null);
        }
        unwrapComposerSpoilersInRange();
        handleComposerInput();
        focusComposer();
        syncComposerSelectionSoon();
        hideComposerContextMenu();
    }

    function applyComposerLink() {
        if (!restoreComposerSelection() || !hasMeaningfulSelection()) return;
        const currentSelection = window.getSelection().toString().trim();
        const linkUrl = prompt('لینک را وارد کنید', currentSelection && /^https?:\/\//i.test(currentSelection) ? currentSelection : 'https://');
        const normalized = normalizeUrl(linkUrl);
        if (!normalized) return;
        applyComposerCommand('createLink', normalized);
    }

    function applySpoilerFormat() {
        if (!restoreComposerSelection() || !hasMeaningfulSelection()) return;
        const selection = window.getSelection();
        if (!selection || selection.rangeCount === 0) return;
        const range = selection.getRangeAt(0);
        const spoiler = document.createElement('span');
        spoiler.className = 'composer-spoiler';
        spoiler.setAttribute('data-spoiler', 'true');
        spoiler.appendChild(range.extractContents());
        range.insertNode(spoiler);
        range.selectNodeContents(spoiler);
        selection.removeAllRanges();
        selection.addRange(range);
        handleComposerInput();
        focusComposer();
        syncComposerSelectionSoon();
        hideComposerContextMenu();
    }

    function showComposerContextMenu(clientX, clientY) {
        const menu = getComposerContextMenu();
        if (!menu) return;

        menu.style.visibility = 'hidden';
        menu.style.display = 'flex';
        menu.classList.add('show');

        const menuRect = menu.getBoundingClientRect();
        const menuWidth = menuRect.width || 200;
        const menuHeight = menuRect.height || 40;
        const padding = 10;

        let left = clientX;
        
        // تغییر مهم اینجاست: قرار دادن منو در بالای مختصات Y با در نظر گرفتن یک فاصله (مثلا 15 پیکسل)
        let top = clientY - menuHeight - 15; 

        if (left + menuWidth + padding > window.innerWidth) {
            left = window.innerWidth - menuWidth - padding;
        }
        if (left < padding) left = padding;

        // اگر محاسبه باعث شد منو از بالای صفحه خارج شود (top منفی شود)، آن را به پایین نقطه لمس منتقل کن
        if (top < padding) {
            top = clientY + 15; 
        }

        menu.style.left = left + 'px';
        menu.style.top = top + 'px';
        menu.style.visibility = 'visible';
    }

    function runComposerMenuAction(action) {
        if (action === 'regular') return clearComposerFormatting();
        if (action === 'bold') return applyComposerCommand('bold');
        if (action === 'italic') return applyComposerCommand('italic');
        if (action === 'spoiler') return applySpoilerFormat();
        if (action === 'link') return applyComposerLink();
    }

    function markSignature(mark) {
        return [!!mark.bold, !!mark.italic, !!mark.spoiler, mark.href || ''].join('|');
    }

    function pushSegment(segments, segment) {
        if (!segment || typeof segment.text !== 'string' || segment.text.length === 0) return;
        const normalized = {
            text: segment.text.replace(/\u00A0/g, ' '),
            bold: !!segment.bold,
            italic: !!segment.italic,
            spoiler: !!segment.spoiler,
            href: segment.href ? normalizeUrl(segment.href) : null
        };
        if (!normalized.text) return;
        const prev = segments[segments.length - 1];
        if (prev && markSignature(prev) === markSignature(normalized)) {
            prev.text += normalized.text;
            return;
        }
        segments.push(normalized);
    }

    function extractSegmentsFromNode(node, activeMarks, segments) {
        if (!node) return;
        if (node.nodeType === Node.TEXT_NODE) {
            pushSegment(segments, { ...activeMarks, text: node.textContent || '' });
            return;
        }
        if (node.nodeType !== Node.ELEMENT_NODE) return;
        const tag = node.tagName.toLowerCase();
        if (tag === 'br') {
            pushSegment(segments, { ...activeMarks, text: '\n' });
            return;
        }
        const nextMarks = { ...activeMarks };
        if (tag === 'b' || tag === 'strong') nextMarks.bold = true;
        if (tag === 'i' || tag === 'em') nextMarks.italic = true;
        if (tag === 'a') nextMarks.href = node.getAttribute('href') || activeMarks.href || null;
        if (node.hasAttribute('data-spoiler')) nextMarks.spoiler = true;

        const blockLike = tag === 'div' || tag === 'p';
        const childNodes = Array.from(node.childNodes);
        childNodes.forEach((child) => extractSegmentsFromNode(child, nextMarks, segments));

        if (blockLike && node.nextSibling) {
            const last = segments[segments.length - 1];
            if (!last || !last.text.endsWith('\n')) {
                pushSegment(segments, { ...activeMarks, text: '\n' });
            }
        }
    }

    function payloadFromPlainText(text, legacyPlain = false) {
        return {
            kind: 'rich_text',
            legacy_plain: legacyPlain,
            segments: [{ text: String(text || '') }]
        };
    }

    function sanitizePayloadSegments(segments) {
        const out = [];
        (Array.isArray(segments) ? segments : []).forEach((segment) => {
            if (!segment || typeof segment.text !== 'string') return;
            pushSegment(out, {
                text: segment.text,
                bold: !!segment.bold,
                italic: !!segment.italic,
                spoiler: !!segment.spoiler,
                href: segment.href || null
            });
        });
        return out.length ? out : [{ text: '' }];
    }

    function parseMessagePayload(raw) {
        if (typeof raw !== 'string') return payloadFromPlainText('');
        try {
            const parsed = JSON.parse(raw);
            if (parsed && parsed.kind === 'rich_text' && Array.isArray(parsed.segments)) {
                return {
                    kind: 'rich_text',
                    legacy_plain: false,
                    segments: sanitizePayloadSegments(parsed.segments)
                };
            }
        } catch (_) {}
        return payloadFromPlainText(raw, true);
    }

    function serializeComposerPayload() {
        const composer = getComposer();
        if (!composer) return payloadFromPlainText('');
        const segments = [];
        Array.from(composer.childNodes).forEach((node) => extractSegmentsFromNode(node, { bold: false, italic: false, spoiler: false, href: null }, segments));
        return {
            kind: 'rich_text',
            segments: sanitizePayloadSegments(segments)
        };
    }

    function payloadToPlainText(payload) {
        return sanitizePayloadSegments(payload?.segments).map((segment) => segment.text).join('');
    }

    function renderSegmentText(text, legacyPlain = false) {
        if (legacyPlain) {
            return linkify(text);
        }
        return escapeHtml(text).replace(/\n/g, '<br>');
    }

    function payloadToHtml(payload, options = {}) {
        const safePayload = {
            kind: 'rich_text',
            legacy_plain: !!payload?.legacy_plain,
            segments: sanitizePayloadSegments(payload?.segments)
        };
        if (safePayload.legacy_plain && !options.forEditor) {
            return `<div>${renderSegmentText(payloadToPlainText(safePayload), true)}</div>`;
        }
        let html = '';
        safePayload.segments.forEach((segment) => {
            let part = renderSegmentText(segment.text, false);
            if (segment.href) {
                part = `<a href="${escapeAttr(segment.href)}" target="_blank" rel="noopener noreferrer">${part}</a>`;
            }
            if (segment.spoiler) {
                part = `<span class="${options.forEditor ? 'composer-spoiler' : 'spoiler-text'}" data-spoiler="true">${part}</span>`;
            }
            if (segment.italic) {
                part = `<em>${part}</em>`;
            }
            if (segment.bold) {
                part = `<strong>${part}</strong>`;
            }
            html += part;
        });
        return `<div>${html || ''}</div>`;
    }

    function setComposerFromPayload(payload) {
        const composer = getComposer();
        if (!composer) return;
        const safePayload = payload && payload.kind === 'rich_text' ? payload : payloadFromPlainText('');
        composer.innerHTML = payloadToHtml(safePayload, { forEditor: true }).replace(/^<div>|<\/div>$/g, '');
        autoGrow(composer);
        syncComposerSelectionSoon();
    }

    function handleComposerInput() {
        const composer = getComposer();
        if (!composer) return;
        autoGrow(composer);
        saveComposerSelection();
        const now = Date.now();
        if (now - lastTypingSent > 800) {
            lastTypingSent = now;
            fetch('/typing', {method:'POST', body: JSON.stringify({u_id: myId})});
        }
    }

    function addPendingUploadBubble(type, payload = {}) {
        const box = document.getElementById('chat-box');
        if (!box) return null;
        const tempId = 'pending-upload-' + (++pendingUploadCounter);
        const div = document.createElement('div');
        div.id = tempId;
        div.className = 'msg sent pending-upload';

        let body = '';
        if (type === 'image') {
            body = `<img src="${payload.previewUrl}" style="max-width:100%; border-radius:12px;">`;
        } else if (type === 'file') {
            body = createFileAttachment({
                file: 'pending',
                name: payload.name || 'فایل',
                mime: payload.mime || 'application/octet-stream',
                size: payload.size || 0
            }, tempId);
        }

        div.innerHTML = `${body}<div class="pending-upload-status">در حال آپلود...</div>`;
        box.appendChild(div);
        scrollToBottom();
        return tempId;
    }

    function removePendingUploadBubble(tempId) {
        if (!tempId) return;
        const el = document.getElementById(tempId);
        if (el) el.remove();
    }

    async function fetchMessages() {
        try {
            await initCrypto();
            const res = await fetch(`/get_messages?since=${lastTime}&since_updated=${lastUpdated}`);
            if (res.status === 401) { location.href = '/'; return; }
            const d = await res.json();
            myId = d.me;
            if (d.room_name) { const rt = document.getElementById('room-title'); if (rt) rt.textContent = d.room_name; }
            const sb = document.getElementById('status-bar');
            sb.innerHTML = d.other_online === "Online" ? '<b style="color:var(--accent)">● آنلاین</b>' : "آخرین بازدید: " + d.other_online;
            document.getElementById('typing-status').innerText = d.is_typing ? "طرف مقابل در حال نوشتن..." : "";
            
            if(d.messages.length > 0) {
                let hasNew = false;
                let unreadIncoming = 0;
                for (const m of d.messages) {
                    if(m.timestamp > lastTime || m.updated) {
                        if(m.timestamp > lastTime && m.sender_id !== myId) {
                            playDing();
                            document.getElementById('typing-status').innerText = "";
                            if (hasFetchedOnce && (isWindowInactive() || !autoScroll)) {
                                unreadIncoming += 1;
                            }
                        }
                        await render(m);
                        if(m.timestamp > lastTime) { lastTime = m.timestamp; hasNew = true; }
                        if(m.updated && m.updated > lastUpdated) { lastUpdated = m.updated; }
                    }
                }
                if (unreadIncoming > 0) {
                    unreadCount += unreadIncoming;
                    updateFavicon();
                }
                if(hasNew) {
                    if(autoScroll) {
                        scrollToBottom();
                    } else {
                        document.getElementById('new-msg-bubble').style.display = 'block';
                    }
                }
                setTimeout(() => handleScroll(), 100);
            }
            hasFetchedOnce = true;
        } catch(e) {
            console.error('Fetch error:', e);
        }
    }

    function linkify(text){
        const esc = text.replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;").replace(/"/g,"&quot;");
        const withBreaks = esc.replace(/\n/g, '<br>');
        return withBreaks.replace(/(https?:\/\/[^\s<]+|www\.[^\s<]+)/gi, (m) => {
            const href = m.startsWith('http') ? m : 'https://' + m;
            return `<a href="${href}" target="_blank" rel="noopener noreferrer">${m}</a>`;
        });
    }

    async function render(m) {
        const box = document.getElementById('chat-box');
        let old = document.getElementById('msg-' + m.id);
        if(m.deleted) {
            textMessagePayloads.delete(m.id);
            pinnedMsgs.delete(m.id);
            updatePinBar();
            if(old) {
                const cachedAudio = window['audio_' + m.id];
                if (cachedAudio) { try { cachedAudio.pause(); } catch(e){} }
                const vp = old.querySelector('.voice-player');
                if (vp && vp.dataset.blobUrl) URL.revokeObjectURL(vp.dataset.blobUrl);
                const vn = old.querySelector('video[data-blob-url]');
                if (vn && vn.dataset.blobUrl) URL.revokeObjectURL(vn.dataset.blobUrl);
                delete window['audio_' + m.id];
                old.remove();
            }
            return;
        }

        const div = old || document.createElement('div');
        div.id = 'msg-' + m.id;
        div.className = 'msg ' + (m.sender_id === myId ? 'sent' : 'received');

        if (old && (m.type === 'voice' || m.type === 'image' || m.type === 'video_note' || m.type === 'file')) {
            var liteReplyText = m.reply_text ? escapeHtml(await dec(m.reply_text)) : '';
            var liteReply = m.reply_id ? `<div class="reply-area" onclick="scrollToMsg('${m.reply_id}')">${liteReplyText}</div>` : '';
            var liteReact = m.react ? `<div class="reaction">${escapeHtml(m.react)}</div>` : '';
            var liteSeen = (m.sender_id === myId && m.seen) ? '<span class="seen-status">✓✓</span>' : (m.sender_id === myId ? '✓' : '');
            var liteEditedIcon = m.edited ? '<span style="font-size:9px; opacity:0.7; margin-right:4px;">✏️</span>' : '';
            var liteFooter = `<div class="footer-info">${liteEditedIcon}<span>${m.time}</span> ${liteSeen}</div>`;
            var liteReplyLabel = m.type === 'image' ? 'تصویر' : (m.type === 'video_note' ? 'پیام ویدیویی' : (m.type === 'file' ? 'فایل' : 'پیام صوتی'));
            var liteActions = `<div class="msg-actions">
                ${m.sender_id === myId ? `<span onpointerdown="event.preventDefault();" onclick="deleteMsg('${m.id}')">حذف</span>` : ''}
                <span class="pin-btn" onpointerdown="event.preventDefault();">${m.pinned ? 'برداشتن سنجاق' : 'سنجاق'}</span>
                <span onpointerdown="event.preventDefault();" onclick="setReply('${m.id}', '${liteReplyLabel}')">پاسخ</span>
            </div>`;
            var replyEl = old.querySelector('.reply-area');
            if (liteReply) {
                if (replyEl) replyEl.outerHTML = liteReply;
                else {
                    var bodyRef = old.querySelector('.voice-player') || old.querySelector('.video-note') || old.querySelector('.file-card') || old.querySelector('img');
                    if (bodyRef) bodyRef.insertAdjacentHTML('beforebegin', liteReply);
                }
            } else if (replyEl) replyEl.remove();
            var reactEl = old.querySelector('.reaction');
            if (liteReact) {
                if (reactEl) reactEl.outerHTML = liteReact;
                else {
                    var bodyRef2 = old.querySelector('.voice-player') || old.querySelector('.video-note') || old.querySelector('.file-card') || old.querySelector('img');
                    if (bodyRef2) bodyRef2.insertAdjacentHTML('afterend', liteReact);
                }
            } else if (reactEl) reactEl.remove();
            var footerEl = old.querySelector('.footer-info');
            if (footerEl) footerEl.outerHTML = liteFooter;
            var actionsEl = old.querySelector('.msg-actions');
            if (actionsEl) actionsEl.outerHTML = liteActions;
            var liteNewActions = old.querySelector('.msg-actions');
            var litePinBtn = liteNewActions ? liteNewActions.querySelector('.pin-btn') : null;
            if (litePinBtn) litePinBtn.addEventListener('click', () => pinMsg(m.id));
            trackPinned(m, liteReplyLabel);
            return;
        }
        
        let longPressHappened = false;
        if (m.sender_id !== myId) {
            div.onclick = (e) => {
                // جلوگیری از باز شدن منو روی لینک، عکس، اکشن‌ها یا reply-area
                if (e.target.closest('.spoiler-text')) {
                    return;
                }
                if (e.target.tagName === 'A' || e.target.tagName === 'IMG' || e.target.closest('.msg-actions') || e.target.closest('.reply-area') || e.target.closest('.voice-player') || e.target.closest('.video-note') || e.target.closest('.file-card') || e.target.closest('.checklist')) {
                    return;
                }
                if (longPressHappened) {
                    longPressHappened = false;
                    return;
                }
                showReactionMenu(e, m.id);
            };
        }

        let pressTimer = null;
        function clearPress(){
            if (pressTimer) { clearTimeout(pressTimer); pressTimer = null; }
        }

        let decryptedData = "";
        let videoMeta = null;
        let voiceMeta = null;
        let fileMeta = null;
        let textPayload = payloadFromPlainText('');
        if (m.type === 'video_note' || m.type === 'voice' || m.type === 'file') {
            try {
                const parsedMeta = JSON.parse(m.data || '{}');
                if (m.type === 'video_note' && parsedMeta?.kind === 'video_note' && parsedMeta?.file) {
                    videoMeta = parsedMeta;
                } else if (m.type === 'voice' && parsedMeta?.kind === 'voice' && parsedMeta?.file) {
                    voiceMeta = parsedMeta;
                } else if (m.type === 'file' && parsedMeta?.kind === 'file' && parsedMeta?.file) {
                    fileMeta = parsedMeta;
                }
            } catch (e) {
                videoMeta = null;
                voiceMeta = null;
                fileMeta = null;
            }
        }
        if (m.type === 'voice' && !voiceMeta) {
            decryptedData = await dec(m.data);
        } else if (m.type === 'checklist') {
            decryptedData = await dec(m.data);
        } else if (m.type !== 'video_note' && m.type !== 'voice' && m.type !== 'file') {
            decryptedData = await dec(m.data);
            textPayload = parseMessagePayload(decryptedData);
            textMessagePayloads.set(m.id, textPayload);
        }
        
        // فقط هنگام ساخت المان لیسنرها را اضافه کن تا روی هر رندر مجدد انباشته نشوند
        if (!old) {
            div.addEventListener('touchstart', (e) => {
                if (e.target && (e.target.closest('img'))) return;
                if (m.type === 'image' || m.type === 'voice' || m.type === 'video_note' || m.type === 'file' || m.type === 'checklist') return;
                longPressHappened = false;
                pressTimer = setTimeout(async () => {
                    longPressHappened = true;
                    // مقدار زندهٔ پیام را بخوان تا بعد از ویرایش هم درست کپی شود
                    const livePayload = textMessagePayloads.get(m.id) || textPayload;
                    try {
                        if (navigator.clipboard && window.isSecureContext) {
                            await navigator.clipboard.writeText(payloadToPlainText(livePayload));
                        } else {
                            const ta = document.createElement('textarea');
                            ta.value = payloadToPlainText(livePayload);
                            document.body.appendChild(ta);
                            ta.select();
                            document.execCommand('copy');
                            ta.remove();
                        }
                        showCopyBubble();
                    } catch(_) {}
                }, 1000);
            }, {passive:true});

            div.addEventListener('touchend', (e) => {
                clearPress();
                if (!longPressHappened) {
                    setTimeout(() => { longPressHappened = false; }, 50);
                }
            }, {passive:true});

            div.addEventListener('touchcancel', (e) => {
                clearPress();
                longPressHappened = false;
            }, {passive:true});

            div.addEventListener('touchmove', (e) => {
                clearPress();
                longPressHappened = false;
            }, {passive:true});
        }

        let checklistData = null;
        if (m.type === 'checklist') {
            try { checklistData = JSON.parse(decryptedData); } catch(e) { checklistData = null; }
        }

        let content = m.type === 'text' ? payloadToPlainText(textPayload)
                    : m.type === 'checklist' ? ((checklistData && checklistData.title ? checklistData.title + ' — ' : '') + (checklistData && Array.isArray(checklistData.items) ? checklistData.items.map(i => i.text).join('، ') : ''))
                    : decryptedData;
        let replyText = m.reply_text ? escapeHtml(await dec(m.reply_text)) : '';
        let reply = m.reply_id ? `<div class="reply-area" onclick="scrollToMsg('${m.reply_id}')">${replyText}</div>` : '';
        let react = m.react ? `<div class="reaction">${escapeHtml(m.react)}</div>` : '';
        let seen = (m.sender_id === myId && m.seen) ? '<span class="seen-status">✓✓</span>' : (m.sender_id === myId ? '✓' : '');

        // برچسب پاسخ به‌صورت متن خام نگه‌داشته می‌شود و از طریق JS (نه اتریبیوت HTML) به هندلر داده می‌شود تا از XSS جلوگیری شود
        const replyLabel = m.type === 'image' ? 'تصویر' : m.type === 'voice' ? 'پیام صوتی' : m.type === 'video_note' ? 'پیام ویدیویی' : m.type === 'file' ? 'فایل' : m.type === 'checklist' ? ('☑️ ' + ((checklistData && checklistData.title) || 'چک‌لیست')) : content.replace(/\n/g, ' ').replace(/\s+/g, ' ').trim().substring(0, 100);
        const canEdit = (m.sender_id === myId && m.type === 'text');
        const pinLabel = m.pinned ? 'برداشتن سنجاق' : 'سنجاق';
        let actions = `<div class="msg-actions">
            ${m.sender_id === myId ? `<span onpointerdown="event.preventDefault();" onclick="deleteMsg('${m.id}')">حذف</span>` : ''}
            ${canEdit ? `<span onpointerdown="event.preventDefault();" onclick="editMsg('${m.id}', ${m.edited ? 'true' : 'false'})">ویرایش</span>` : ''}
            <span class="pin-btn" onpointerdown="event.preventDefault();">${pinLabel}</span>
            <span class="reply-btn" onpointerdown="event.preventDefault();">پاسخ</span>
        </div>`;

        let body;
        if (m.type === 'image') {
            const safeSrc = /^data:image\//i.test(content) ? content : '';
            body = `<img src="${escapeAttr(safeSrc)}" style="max-width:100%; border-radius:12px;">`;
        } else if (m.type === 'voice') {
            body = createVoicePlayer(voiceMeta || { legacySrc: content }, m.id);
        } else if (m.type === 'video_note') {
            body = createVideoNotePlayer(videoMeta, m.id);
        } else if (m.type === 'file') {
            body = createFileAttachment(fileMeta, m.id);
        } else if (m.type === 'checklist') {
            body = buildChecklistHtml(m.id, checklistData);
        } else {
            body = payloadToHtml(textPayload);
        }

        let editedIcon = m.edited ? '<span style="font-size:9px; opacity:0.7; margin-right:4px;">✏️</span>' : '';
        div.innerHTML = `${reply} ${body} ${react} <div class="footer-info">${editedIcon}<span>${m.time}</span> ${seen}</div> ${actions}`;
        div.dataset.plain = (m.type === 'text' || m.type === 'checklist') ? content : '';
        const replyBtn = div.querySelector('.reply-btn');
        if (replyBtn) replyBtn.addEventListener('click', () => setReply(m.id, replyLabel));
        const pinBtn = div.querySelector('.pin-btn');
        if (pinBtn) pinBtn.addEventListener('click', () => pinMsg(m.id));
        if (m.type === 'checklist') wireChecklist(div, m.id);
        trackPinned(m, replyLabel);
        div.querySelectorAll('.spoiler-text').forEach((el) => {
            el.addEventListener('click', function(event) {
                event.preventDefault();
                event.stopPropagation();
                this.classList.toggle('revealed');
            });
        });
        if(!old) box.appendChild(div);
    }

    function setReply(id, text) {
        cancelEdit();
        replyingTo = {id: id, text: text};
        const rp = document.getElementById('reply-preview');
        rp.style.display = 'flex';
        const singleLineText = text.replace(/\n/g, ' ').replace(/\s+/g, ' ').trim();
        const previewText = singleLineText.length > 50 ? singleLineText.substring(0, 50) + '...' : singleLineText;
        document.getElementById('reply-text').innerText = previewText;
        focusComposer();
    }

    function cancelReply(keepFocus=false) {
        replyingTo = null;
        document.getElementById('reply-preview').style.display = 'none';
        if (keepFocus) focusComposer();
    }

    function cancelEdit(keepFocus=false) {
        if (!editingTo) {
            if (keepFocus) focusComposer();
            return;
        }
        editingTo = null;
        document.getElementById('edit-preview').style.display = 'none';
        const i = document.getElementById('msgInput');
        clearComposer();
        i.dataset.placeholder = 'پیام بنویسید...';
        if (keepFocus) focusComposer();
    }

    async function sendTxt() {
        let i = document.getElementById('msgInput');
        const payload = serializeComposerPayload();
        const plainText = payloadToPlainText(payload);
        if(!plainText.trim()) return;
        
        if (editingTo) {
            const encData = await enc(JSON.stringify(payload));
            postAction('/edit_message', {
                id: editingTo.id,
                data: encData
            });
            clearComposer();
            i.dataset.placeholder = 'پیام بنویسید...';
            cancelEdit();
        } else {
            const encData = await enc(JSON.stringify(payload));
            const encReplyText = replyingTo ? await enc(replyingTo.text) : null;
            postAction('/send_message', {
                type:'text', data: encData,
                reply_id: replyingTo ? replyingTo.id : null,
                reply_text: encReplyText
            });
            clearComposer();
            cancelReply();
            setTimeout(() => scrollToBottom(), 100);
        }
    }

    async function sendImg(input) {
        const file = input.files[0];
        if (!file) return;
        const previewUrl = URL.createObjectURL(file);
        const pendingId = addPendingUploadBubble('image', { previewUrl });

        const img = new Image();
        img.onload = async () => {
            try {
                const maxW = 720;
                const scale = Math.min(1, maxW / img.width);
                const w = Math.round(img.width * scale);
                const h = Math.round(img.height * scale);

                const canvas = document.createElement('canvas');
                canvas.width = w; canvas.height = h;
                const ctx = canvas.getContext('2d');
                ctx.drawImage(img, 0, 0, w, h);

                const quality = 0.5;
                const dataUrl = canvas.toDataURL('image/jpeg', quality);

                const encData = await enc(dataUrl);
                const encReplyText = replyingTo ? await enc(replyingTo.text) : null;
                
                await postAction('/send_message', {
                    type: 'image',
                    data: encData,
                    reply_id: replyingTo ? replyingTo.id : null,
                    reply_text: encReplyText
                });
                removePendingUploadBubble(pendingId);
                input.value = "";
                setTimeout(() => scrollToBottom(), 100);
            } catch (error) {
                removePendingUploadBubble(pendingId);
                console.error('Error sending image:', error);
                alert('ارسال تصویر ناموفق بود');
            } finally {
                URL.revokeObjectURL(previewUrl);
            }
        };
        img.onerror = () => {
            removePendingUploadBubble(pendingId);
            URL.revokeObjectURL(previewUrl);
            alert('خواندن تصویر ناموفق بود');
        };

        img.src = previewUrl;
    }

    function formatFileSize(bytes) {
        if (!bytes || bytes < 1024) return `${bytes || 0} بایت`;
        if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} کیلوبایت`;
        if (bytes < 1024 * 1024 * 1024) return `${(bytes / (1024 * 1024)).toFixed(1)} مگابایت`;
        return `${(bytes / (1024 * 1024 * 1024)).toFixed(1)} گیگابایت`;
    }

    function getFileEmoji(fileName, mimeType) {
        const lowerName = (fileName || '').toLowerCase();
        const mime = mimeType || '';
        if (mime.startsWith('audio/')) return '🎵';
        if (mime.startsWith('video/')) return '🎬';
        if (mime.includes('pdf') || lowerName.endsWith('.pdf')) return '📄';
        if (mime.includes('zip') || mime.includes('rar') || lowerName.endsWith('.zip') || lowerName.endsWith('.rar') || lowerName.endsWith('.7z')) return '🗜️';
        if (mime.includes('word') || lowerName.endsWith('.doc') || lowerName.endsWith('.docx')) return '📝';
        if (mime.includes('excel') || lowerName.endsWith('.xls') || lowerName.endsWith('.xlsx')) return '📊';
        return '📎';
    }

    async function sendAttachment(input) {
        const file = input.files[0];
        if (!file) return;
        let pendingId = null;

        try {
            if (file.type && file.type.startsWith('image/')) {
                await sendImg(input);
                return;
            }

            if (file.size > 20 * 1024 * 1024) {
                alert('حجم فایل بیش از حد مجاز است (حداکثر ۲۰ مگابایت)');
                return;
            }

            pendingId = addPendingUploadBubble('file', {
                name: file.name,
                mime: file.type,
                size: file.size
            });
            const encryptedBytes = await encryptBinary(await file.arrayBuffer());
            const encReplyText = replyingTo ? await enc(replyingTo.text) : '';
            const params = new URLSearchParams({
                mime: file.type || 'application/octet-stream',
                name: file.name || 'file',
                size: String(file.size || 0)
            });

            const response = await fetch(`/upload_file?${params.toString()}`, {
                method: 'POST',
                headers: {
                    'X-Reply-Id': replyingTo ? replyingTo.id : '',
                    'X-Reply-Text': encReplyText
                },
                body: new Blob([encryptedBytes], { type: 'application/octet-stream' })
            });
            if (!response.ok) throw new Error('file upload failed');

            removePendingUploadBubble(pendingId);
            cancelReply();
            fetchMessages();
            setTimeout(() => scrollToBottom(), 100);
        } catch (error) {
            removePendingUploadBubble(pendingId);
            console.error('Error sending file:', error);
            alert('ارسال فایل ناموفق بود');
        } finally {
            input.value = "";
        }
    }

    // --- Voice Recording ---
    let mediaRecorder = null;
    let audioChunks = [];
    let recordingStartTime = 0;
    let recordingTimer = null;
    let recordedBlob = null;
    let videoRecorder = null;
    let videoChunks = [];
    let recordedVideoBlob = null;
    let videoStreamRef = null;
    let audioStream = null;
    let audioStopResolve = null;
    let videoStopResolve = null;

    function stopAudioStream() {
        if (audioStream) {
            audioStream.getTracks().forEach(t => t.stop());
            audioStream = null;
        }
    }

    async function toggleRecording() {
        if (mediaRecorder && mediaRecorder.state === 'recording') {
            mediaRecorder.stop();
        } else {
            try {
                audioStream = await navigator.mediaDevices.getUserMedia({
                    audio: {
                        sampleRate: 16000,
                        channelCount: 1,
                        echoCancellation: true,
                        noiseSuppression: true
                    }
                });
                let options = { mimeType: 'audio/webm;codecs=opus', audioBitsPerSecond: 16000 };
                if (!MediaRecorder.isTypeSupported(options.mimeType)) {
                    options = { mimeType: 'audio/webm', audioBitsPerSecond: 16000 };
                }
                if (!MediaRecorder.isTypeSupported(options.mimeType)) {
                    options = { mimeType: 'audio/mp4', audioBitsPerSecond: 16000 };
                }
                if (!MediaRecorder.isTypeSupported(options.mimeType)) {
                    options = {};
                }
                mediaRecorder = new MediaRecorder(audioStream, options);
                audioChunks = [];
                mediaRecorder.ondataavailable = (e) => {
                    if (e.data.size > 0) audioChunks.push(e.data);
                };
                mediaRecorder.onstop = () => {
                    stopAudioStream();
                    recordedBlob = new Blob(audioChunks, { type: mediaRecorder.mimeType || 'audio/webm' });
                    document.getElementById('mic-btn').classList.remove('recording');
                    if (audioStopResolve) { const r = audioStopResolve; audioStopResolve = null; r(); }
                };
                mediaRecorder.onerror = (ev) => {
                    console.error('Audio recorder error:', ev && ev.error);
                    stopAudioStream();
                    if (recordingTimer) clearTimeout(recordingTimer);
                    document.getElementById('recording-ui').classList.remove('show');
                    document.getElementById('mic-btn').classList.remove('recording');
                    audioChunks = [];
                    recordedBlob = null;
                    if (audioStopResolve) { const r = audioStopResolve; audioStopResolve = null; r(); }
                };
                mediaRecorder.start(1000);
                recordingStartTime = Date.now();
                document.getElementById('mic-btn').classList.add('recording');
                document.getElementById('recording-ui').classList.add('show');
                updateRecordingTime();
            } catch(e) {
                console.error('Microphone access denied:', e);
                stopAudioStream();
                alert('دسترسی به میکروفون داده نشد');
            }
        }
    }

    async function toggleVideoNoteRecording() {
        if (videoRecorder && videoRecorder.state === 'recording') return;
        try {
            const stream = await navigator.mediaDevices.getUserMedia({
                video: { facingMode: 'user', width: { ideal: 360 }, height: { ideal: 360 } },
                audio: true
            });
            videoStreamRef = stream;
            const preview = document.getElementById('video-note-preview');
            preview.srcObject = stream;

            let options = { mimeType: 'video/webm;codecs=vp8,opus', videoBitsPerSecond: 450000 };
            if (!MediaRecorder.isTypeSupported(options.mimeType)) {
                options = { mimeType: 'video/webm', videoBitsPerSecond: 450000 };
            }
            if (!MediaRecorder.isTypeSupported(options.mimeType)) options = {};

            videoRecorder = new MediaRecorder(stream, options);
            videoChunks = [];
            recordedVideoBlob = null;
            videoRecorder.ondataavailable = (event) => {
                if (event.data.size > 0) videoChunks.push(event.data);
            };
            videoRecorder.onstop = () => {
                recordedVideoBlob = new Blob(videoChunks, { type: videoRecorder.mimeType || 'video/webm' });
                stopVideoStream();
                if (videoStopResolve) { const r = videoStopResolve; videoStopResolve = null; r(); }
            };
            videoRecorder.onerror = (ev) => {
                console.error('Video recorder error:', ev && ev.error);
                stopVideoStream();
                document.getElementById('video-note-ui').classList.remove('show');
                videoChunks = [];
                recordedVideoBlob = null;
                if (videoStopResolve) { const r = videoStopResolve; videoStopResolve = null; r(); }
            };
            videoRecorder.start(250);
            document.getElementById('video-note-ui').classList.add('show');
        } catch (error) {
            console.error('Camera access denied:', error);
            stopVideoStream();
            alert('دسترسی به دوربین داده نشد');
        }
    }

    function stopVideoStream() {
        if (videoStreamRef) {
            videoStreamRef.getTracks().forEach(track => track.stop());
            videoStreamRef = null;
        }
        const preview = document.getElementById('video-note-preview');
        if (preview) preview.srcObject = null;
    }

    function cancelVideoNote() {
        videoStopResolve = null;
        if (videoRecorder && videoRecorder.state === 'recording') {
            videoRecorder.stop();
        } else {
            stopVideoStream();
        }
        document.getElementById('video-note-ui').classList.remove('show');
        videoChunks = [];
        recordedVideoBlob = null;
    }

    async function sendVideoNote() {
        if (videoRecorder && videoRecorder.state === 'recording') {
            await new Promise(resolve => { videoStopResolve = resolve; videoRecorder.stop(); });
        }
        document.getElementById('video-note-ui').classList.remove('show');

        if (!recordedVideoBlob || recordedVideoBlob.size === 0) {
            recordedVideoBlob = null;
            videoChunks = [];
            return;
        }
        if (recordedVideoBlob.size > 8 * 1024 * 1024) {
            alert('حجم پیام ویدیویی بیش از حد مجاز است (حداکثر 8 مگابایت)');
            recordedVideoBlob = null;
            videoChunks = [];
            return;
        }

        try {
            const encryptedBytes = await encryptBinary(await recordedVideoBlob.arrayBuffer());
            const encReplyText = replyingTo ? await enc(replyingTo.text) : '';
            await fetch(`/upload_video_note?mime=${encodeURIComponent(recordedVideoBlob.type || 'video/webm')}`, {
                method: 'POST',
                headers: {
                    'X-Reply-Id': replyingTo ? replyingTo.id : '',
                    'X-Reply-Text': encReplyText
                },
                body: new Blob([encryptedBytes], { type: 'application/octet-stream' })
            });
            cancelReply();
            fetchMessages();
            setTimeout(() => scrollToBottom(), 100);
        } catch (error) {
            console.error('Error sending video note:', error);
            alert('ارسال پیام ویدیویی ناموفق بود');
        } finally {
            recordedVideoBlob = null;
            videoChunks = [];
        }
    }

    function updateRecordingTime() {
        if (!mediaRecorder || mediaRecorder.state !== 'recording') return;
        const elapsed = Math.floor((Date.now() - recordingStartTime) / 1000);
        const mins = Math.floor(elapsed / 60);
        const secs = elapsed % 60;
        document.getElementById('recording-time').textContent = `${mins}:${secs.toString().padStart(2, '0')}`;
        recordingTimer = setTimeout(updateRecordingTime, 1000);
    }

    function cancelRecording() {
        audioStopResolve = null;
        if (mediaRecorder && mediaRecorder.state === 'recording') {
            mediaRecorder.stop();
        } else {
            stopAudioStream();
        }
        if (recordingTimer) clearTimeout(recordingTimer);
        document.getElementById('recording-ui').classList.remove('show');
        document.getElementById('mic-btn').classList.remove('recording');
        recordedBlob = null;
        audioChunks = [];
    }

    async function sendRecording() {
        if (mediaRecorder && mediaRecorder.state === 'recording') {
            await new Promise(resolve => { audioStopResolve = resolve; mediaRecorder.stop(); });
        }
        if (recordingTimer) clearTimeout(recordingTimer);
        document.getElementById('recording-ui').classList.remove('show');
        if (!recordedBlob || recordedBlob.size === 0) {
            recordedBlob = null;
            audioChunks = [];
            return;
        }
        if (recordedBlob.size > 1024 * 1024) {
            alert('حجم ویس بیش از حد مجاز است (حداکثر 1 مگابایت)');
            recordedBlob = null;
            audioChunks = [];
            return;
        }
        try {
            const encryptedBytes = await encryptBinary(await recordedBlob.arrayBuffer());
            const encReplyText = replyingTo ? await enc(replyingTo.text) : '';
            await fetch(`/upload_voice?mime=${encodeURIComponent(recordedBlob.type || 'audio/webm')}`, {
                method: 'POST',
                headers: {
                    'X-Reply-Id': replyingTo ? replyingTo.id : '',
                    'X-Reply-Text': encReplyText
                },
                body: new Blob([encryptedBytes], { type: 'application/octet-stream' })
            });
            cancelReply();
            fetchMessages();
            setTimeout(() => scrollToBottom(), 100);
        } catch(e) {
            console.error('Error sending voice:', e);
            alert('خطا در ارسال ویس');
        } finally {
            recordedBlob = null;
            audioChunks = [];
        }
    }

    // --- Voice Player: waveform قابل کلیک، دکمه 1.5x ---
    function createVoicePlayer(meta, msgId) {
        const fileName = meta?.file || '';
        const mime = meta?.mime || 'audio/webm';
        const legacySrc = meta?.legacySrc || '';
        const bars = [];
        for (let i = 0; i < 25; i++) {
            bars.push(Math.random() * 20 + 8);
        }
        const barsHtml = bars.map((h, i) =>
            `<div class="voice-bar" data-idx="${i}" style="height:${h}px"></div>`
        ).join('');
        const html = `
            <div class="voice-player" data-msg="${msgId}" data-file="${fileName}" data-mime="${mime}" data-legacy-src="${legacySrc}">
                <button class="voice-play-btn" onclick="toggleVoicePlay('${msgId}')">
                    <svg class="play-icon" viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg>
                    <svg class="pause-icon" style="display:none" viewBox="0 0 24 24"><path d="M6 19h4V5H6v14zm8-14v14h4V5h-4z"/></svg>
                </button>
                <div class="voice-waveform" onclick="seekVoice(event, '${msgId}')">${barsHtml}</div>
                <div class="voice-info">
                    <span class="voice-time" id="vtime-${msgId}">0:00</span>
                    <span class="voice-speed" onclick="toggleVoiceSpeed('${msgId}')">1x</span>
                </div>
            </div>
        `;
        return html;
    }

    // مدت‌زمان بلاب‌های webm/opus که با MediaRecorder ساخته می‌شوند اغلب Infinity گزارش می‌شود؛
    // این تابع مقدار واقعی را برمی‌گرداند (پس از حل‌شدن با seek).
    function voiceDuration(audio) {
        const d = audio.duration;
        if (isFinite(d) && d > 0) return d;
        return audio._realDuration || 0;
    }

    function setupVoiceAudio(msgId, audio) {
        let durationFixAttempted = false;
        function setTimeLabel(seconds) {
            if (!(seconds > 0) || !isFinite(seconds)) return;
            const durSec = Math.floor(seconds);
            const mins = Math.floor(durSec / 60);
            const secs = durSec % 60;
            const el = document.getElementById('vtime-' + msgId);
            if (el) el.textContent = `${mins}:${secs.toString().padStart(2, '0')}`;
        }
        function resolveDuration() {
            const dur = audio.duration;
            if (isFinite(dur) && dur > 0) {
                audio._realDuration = dur;
                if (audio.paused) setTimeLabel(dur);
                return;
            }
            // ترفند رفع باگ Infinity: یک‌بار به انتهای فایل seek کن تا مرورگر مدت واقعی را محاسبه کند
            if (!durationFixAttempted) {
                durationFixAttempted = true;
                const onForcedSeek = () => {
                    if (isFinite(audio.duration) && audio.duration > 0) {
                        audio._realDuration = audio.duration;
                        audio.removeEventListener('timeupdate', onForcedSeek);
                        audio.currentTime = 0;
                        if (audio.paused) setTimeLabel(audio._realDuration);
                    }
                };
                audio.addEventListener('timeupdate', onForcedSeek);
                try { audio.currentTime = 1e101; } catch (e) {}
            }
        }
        audio.onloadedmetadata = resolveDuration;
        audio.ondurationchange = resolveDuration;
        audio.oncanplaythrough = resolveDuration;
        audio.ontimeupdate = () => updateVoiceProgress(msgId);
        audio.onended = () => {
            const player = document.querySelector(`.voice-player[data-msg="${msgId}"]`);
            if (player) {
                player.querySelector('.play-icon').style.display = 'block';
                player.querySelector('.pause-icon').style.display = 'none';
                player.querySelectorAll('.voice-bar').forEach(b => b.classList.remove('played'));
            }
            audio.currentTime = 0;
            const dur = voiceDuration(audio);
            if (dur && isFinite(dur)) {
                const mins = Math.floor(dur / 60);
                const secs = Math.floor(dur % 60);
                const el = document.getElementById('vtime-' + msgId);
                if (el) el.textContent = `${mins}:${secs.toString().padStart(2, '0')}`;
            }
        };
    }

    async function ensureVoiceAudio(msgId) {
        const existing = window['audio_' + msgId];
        if (existing) return existing;

        const player = document.querySelector(`.voice-player[data-msg="${msgId}"]`);
        if (!player) return null;

        const legacySrc = player.dataset.legacySrc || '';
        let src = legacySrc;
        if (!src) {
            const fileName = player.dataset.file || '';
            const mime = player.dataset.mime || 'audio/webm';
            if (!fileName) return null;
            const response = await fetch('/media/' + encodeURIComponent(fileName));
            if (!response.ok) throw new Error('voice media fetch failed');
            const encryptedBytes = await response.arrayBuffer();
            const decryptedBytes = await decryptBinary(encryptedBytes);
            src = URL.createObjectURL(new Blob([decryptedBytes], { type: mime }));
            player.dataset.blobUrl = src;
        }

        const audio = new Audio(src);
        window['audio_' + msgId] = audio;
        setupVoiceAudio(msgId, audio);
        return audio;
    }

    function createVideoNotePlayer(meta, msgId) {
        if (!meta || !meta.file) {
            return '<div style="font-size:12px; color:#f44336;">پیام ویدیویی در دسترس نیست</div>';
        }
        const mime = meta.mime || 'video/webm';
        const html = `
            <div class="video-note" data-video-note="${msgId}" onclick="toggleVideoNotePlay('${msgId}', '${meta.file}', '${mime}')">
                <video id="vnote-${msgId}" playsinline preload="none"></video>
                <div class="video-note-play">
                    <svg viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg>
                </div>
            </div>
        `;
        return html;
    }

    function createFileAttachment(meta, msgId) {
        if (!meta || !meta.file) {
            return '<div style="font-size:12px; color:#f44336;">فایل در دسترس نیست</div>';
        }
        const rawName = meta.name || 'فایل';
        const name = rawName.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
        const mime = (meta.mime || 'application/octet-stream').replace(/'/g, '&#39;');
        const fileName = (meta.file || '').replace(/'/g, '&#39;');
        const sizeLabel = formatFileSize(Number(meta.size || 0));
        const downloadName = rawName.replace(/\\/g, '_').replace(/\//g, '_').replace(/'/g, "\\'");
        const emoji = getFileEmoji(rawName, mime);
        return `
            <div class="file-card" onclick="downloadAttachment(this, '${msgId}', '${fileName}', '${mime}', '${downloadName}')">
                <div class="file-card-icon">${emoji}</div>
                <div class="file-card-body">
                    <div class="file-card-name">${name}</div>
                    <div class="file-card-meta">${sizeLabel}</div>
                    <div class="file-card-action">دانلود فایل</div>
                </div>
            </div>
        `;
    }

    const spinnerSvg = `
    <svg class="spinner-icon" viewBox="0 0 50 50">
        <circle cx="25" cy="25" r="20" fill="none" stroke="currentColor" stroke-width="5" stroke-dasharray="31.415, 31.415" stroke-linecap="round"></circle>
    </svg>`;

    async function downloadAttachment(cardElement, msgId, fileName, mime, fileDisplayName) {
        const iconElement = cardElement.querySelector('.file-card-icon');
        const originalIcon = iconElement.innerHTML;
        
        // تغییر آیکون به لودینگ 
        iconElement.innerHTML = spinnerSvg; 
        try {
            const response = await fetch('/media/' + encodeURIComponent(fileName));
            if (!response.ok) throw new Error('file fetch failed');
            const encryptedBytes = await response.arrayBuffer();
            const decryptedBytes = await decryptBinary(encryptedBytes);
            const blob = new Blob([decryptedBytes], { type: mime || 'application/octet-stream' });
            const blobUrl = URL.createObjectURL(blob);
            const link = document.createElement('a');
            link.href = blobUrl;
            link.download = fileDisplayName || 'download';
            document.body.appendChild(link);
            link.click();
            link.remove();
            setTimeout(() => URL.revokeObjectURL(blobUrl), 1000);
        } catch (error) {
            console.error('File download failed:', error);
            alert('دانلود فایل ناموفق بود');
        } finally {
            // برگرداندن آیکون به حالت اولیه بعد از اتمام فرآیند دانلود
            if (iconElement) {
                iconElement.innerHTML = originalIcon;
            }
        }
    }

    async function toggleVideoNotePlay(msgId, fileName, mime) {
        const wrapper = document.querySelector(`.video-note[data-video-note="${msgId}"]`);
        const video = document.getElementById('vnote-' + msgId);
        if (!wrapper || !video) return;

        if (!video.src) {
            try {
                const response = await fetch('/media/' + encodeURIComponent(fileName));
                if (!response.ok) throw new Error('media fetch failed');
                const encryptedBytes = await response.arrayBuffer();
                const decryptedBytes = await decryptBinary(encryptedBytes);
                const blobUrl = URL.createObjectURL(new Blob([decryptedBytes], { type: mime || 'video/webm' }));
                video.dataset.blobUrl = blobUrl;
                video.src = blobUrl;

                // ✅ صبر کن تا ویدیو واقعاً آماده پخش بشه (با تایم‌اوت تا برای همیشه معلق نماند)
                await new Promise((resolve, reject) => {
                    let settled = false;
                    const finish = (fn) => {
                        if (settled) return;
                        settled = true;
                        clearTimeout(timer);
                        video.oncanplay = null;
                        video.onloadeddata = null;
                        video.onerror = null;
                        fn();
                    };
                    const timer = setTimeout(() => finish(() => reject(new Error('video load timeout'))), 8000);
                    video.oncanplay = () => finish(resolve);
                    video.onloadeddata = () => finish(resolve);
                    video.onerror = () => finish(() => reject(new Error('video load error')));
                    video.load(); // ← force load
                });

            } catch (error) {
                console.error('Video note decrypt failed:', error);
                if (video.dataset.blobUrl) { URL.revokeObjectURL(video.dataset.blobUrl); delete video.dataset.blobUrl; }
                video.removeAttribute('src');
                alert('بازگشایی پیام ویدیویی ناموفق بود');
                return;
            }
        }

        if (video.paused || video.ended) {
            // توقف بقیه ویدیوها
            document.querySelectorAll('.video-note video').forEach(v => {
                if (!v.paused) {
                    v.pause();
                    v.closest('.video-note')?.classList.remove('playing');
                }
            });

            // ✅ play() رو داخل try/catch بگیر تا AbortError crash نکنه
            try {
                await video.play();
                wrapper.classList.add('playing');
            } catch (err) {
                if (err.name !== 'AbortError') {
                    console.error('Video play failed:', err);
                }
                // AbortError رو نادیده بگیر - مرورگر خودش resolve می‌کنه
            }
        } else {
            video.pause();
            wrapper.classList.remove('playing');
        }

        video.onended = () => wrapper.classList.remove('playing');
    }

    async function toggleVoicePlay(msgId) {
        let audio;
        try {
            audio = await ensureVoiceAudio(msgId);
        } catch (error) {
            console.error('Voice decrypt failed:', error);
            alert('بازگشایی پیام صوتی ناموفق بود');
            return;
        }
        if (!audio) return;
        const player = document.querySelector(`.voice-player[data-msg="${msgId}"]`);
        if (!player) return;
        if (audio.paused) {
            document.querySelectorAll('.voice-player').forEach(p => {
                const id = p.dataset.msg;
                const a = window['audio_' + id];
                if (a && !a.paused && id !== msgId) {
                    a.pause();
                    const pi = p.querySelector('.play-icon');
                    const pai = p.querySelector('.pause-icon');
                    if (pi) pi.style.display = 'block';
                    if (pai) pai.style.display = 'none';
                    const dur = a.duration;
                    if (dur && isFinite(dur)) {
                        const el = document.getElementById('vtime-' + id);
                        if (el) el.textContent = `${Math.floor(dur/60)}:${Math.floor(dur%60).toString().padStart(2,'0')}`;
                    }
                }
            });
            const pi = player.querySelector('.play-icon');
            const pai = player.querySelector('.pause-icon');
            if (pi) pi.style.display = 'none';
            if (pai) pai.style.display = 'block';
            audio.play().catch(err => {
                if (err && err.name !== 'AbortError') {
                    console.error('Voice play failed:', err);
                    if (pi) pi.style.display = 'block';
                    if (pai) pai.style.display = 'none';
                }
            });
        } else {
            audio.pause();
            const pi = player.querySelector('.play-icon');
            const pai = player.querySelector('.pause-icon');
            if (pi) pi.style.display = 'block';
            if (pai) pai.style.display = 'none';
            const dur = audio.duration;
            if (dur && isFinite(dur)) {
                const el = document.getElementById('vtime-' + msgId);
                if (el) el.textContent = `${Math.floor(dur/60)}:${Math.floor(dur%60).toString().padStart(2,'0')}`;
            }
        }
    }

    function toggleVoiceSpeed(msgId) {
        const audio = window['audio_' + msgId];
        if (!audio) return;
        const player = document.querySelector(`.voice-player[data-msg="${msgId}"]`);
        const speedBtn = player?.querySelector('.voice-speed');
        if (!speedBtn) return;
        if (audio.playbackRate === 1) {
            audio.playbackRate = 1.5;
            speedBtn.textContent = '1.5x';
            speedBtn.classList.add('active');
        } else {
            audio.playbackRate = 1;
            speedBtn.textContent = '1x';
            speedBtn.classList.remove('active');
        }
    }

    function updateVoiceProgress(msgId) {
        const audio = window['audio_' + msgId];
        if (!audio) return;
        const player = document.querySelector(`.voice-player[data-msg="${msgId}"]`);
        if (!player) return;
        const duration = voiceDuration(audio);
        const currentTime = audio.currentTime;
        const el = document.getElementById('vtime-' + msgId);
        if (duration && isFinite(duration) && duration > 0) {
            const progress = currentTime / duration;
            const bars = player.querySelectorAll('.voice-bar');
            const playedBars = Math.floor(progress * bars.length);
            bars.forEach((bar, i) => {
                if (i < playedBars) bar.classList.add('played');
                else bar.classList.remove('played');
            });
        }
        if (el) {
            let timeToShow = (!audio.paused && currentTime > 0) ? Math.floor(currentTime) : (duration && isFinite(duration) && duration > 0 ? Math.floor(duration) : 0);
            const mins = Math.floor(timeToShow / 60);
            const secs = timeToShow % 60;
            el.textContent = `${mins}:${secs.toString().padStart(2, '0')}`;
        }
    }

    function seekVoice(event, msgId) {
        const audio = window['audio_' + msgId];
        if (!audio) return;
        const dur = voiceDuration(audio);
        if (!dur || !isFinite(dur)) return;
        const waveform = event.currentTarget;
        const rect = waveform.getBoundingClientRect();
        const x = event.clientX - rect.left;
        const progress = Math.max(0, Math.min(1, x / rect.width));
        audio.currentTime = progress * dur;
    }

    async function postAction(path, p) {
        try {
            await fetch(path, {method:'POST', body: JSON.stringify({...p})});
            fetchMessages();
        } catch(e) {
            console.error('Post error:', e);
        }
    }

    // ========================= فیچرهای جدید =========================

    // --- منوی هدر ---
    function toggleHeaderMenu(e){ e.stopPropagation(); document.getElementById('header-menu').classList.toggle('show'); }
    function closeHeaderMenu(){ document.getElementById('header-menu').classList.remove('show'); }
    document.addEventListener('click', (e)=>{
        const menu=document.getElementById('header-menu');
        if(menu && menu.classList.contains('show') && !e.target.closest('#header-menu') && !e.target.closest('#menu-btn')) menu.classList.remove('show');
    });

    // --- مودال‌ها ---
    function showModal(id){
        document.getElementById('modal-backdrop').classList.add('show');
        document.querySelectorAll('.modal').forEach(m=>m.classList.remove('show'));
        document.getElementById(id).classList.add('show');
    }
    function closeModals(){
        document.getElementById('modal-backdrop').classList.remove('show');
        document.querySelectorAll('.modal').forEach(m=>m.classList.remove('show'));
    }

    // --- فیچر ۱: پیام‌های سنجاق‌شده (چندتایی، با چرخش و لیست) ---
    const pinnedMsgs = new Map(); // id -> {text, ts}
    let pinOrder = [];            // idها به ترتیب زمانی (قدیمی→جدید)
    let pinIdx = 0;               // اندیس سنجاق فعلی روی نوار
    function trackPinned(m, label){
        if(m.pinned) pinnedMsgs.set(m.id, {text: label, ts: m.timestamp});
        else pinnedMsgs.delete(m.id);
        updatePinBar();
    }
    function rebuildPinOrder(){
        pinOrder = [...pinnedMsgs.entries()].sort((a,b)=>a[1].ts-b[1].ts).map(e=>e[0]);
        if(pinIdx >= pinOrder.length) pinIdx = pinOrder.length-1;
        if(pinIdx < 0) pinIdx = 0;
    }
    function updatePinBar(){
        const bar=document.getElementById('pin-bar');
        if(!bar) return;
        rebuildPinOrder();
        if(pinOrder.length===0){ bar.classList.remove('show'); return; }
        const id=pinOrder[pinIdx];
        const info=pinnedMsgs.get(id) || {text:''};
        const counter = pinOrder.length>1 ? ('('+(pinIdx+1)+'/'+pinOrder.length+') ') : '';
        document.getElementById('pin-bar-text').textContent = counter + (info.text || 'پیام سنجاق‌شده');
        document.getElementById('pin-bar-list').style.display = pinOrder.length>1 ? 'flex' : 'none';
        bar.classList.add('show');
    }
    function pinMsg(id){ closeHeaderMenu(); postAction('/pin_message', {id:id}); }
    function pinBarGo(){
        if(!pinOrder.length) return;
        scrollToMsg(pinOrder[pinIdx]);
        // برای تپ بعدی، به سنجاق بعدی برو (چرخشی)
        if(pinOrder.length>1){ pinIdx=(pinIdx+1)%pinOrder.length; updatePinBar(); }
    }
    function pinBarUnpin(e){ e.stopPropagation(); if(!pinOrder.length) return; pinMsg(pinOrder[pinIdx]); }
    function openPinnedList(e){
        if(e) e.stopPropagation();
        const box=document.getElementById('pinned-list'); box.innerHTML='';
        rebuildPinOrder();
        if(!pinOrder.length){ box.innerHTML='<div class="sched-empty">پیامی سنجاق نشده</div>'; }
        else {
            [...pinOrder].reverse().forEach(id=>{
                const info=pinnedMsgs.get(id)||{text:''};
                const div=document.createElement('div'); div.className='sched-item';
                div.innerHTML='<div class="sc-text"></div><button class="sc-cancel" title="برداشتن سنجاق">✕</button>';
                const t=div.querySelector('.sc-text');
                t.textContent=info.text||'پیام'; t.style.cursor='pointer';
                t.onclick=()=>{ closeModals(); scrollToMsg(id); };
                div.querySelector('.sc-cancel').onclick=()=>{ pinMsg(id); setTimeout(()=>openPinnedList(),350); };
                box.appendChild(div);
            });
        }
        showModal('pinned-modal');
    }

    // --- فیچر ۲: جست‌وجوی داخل چت ---
    let searchHits=[], searchIdx=-1;
    function normalizeFa(s){ return (s||'').toLowerCase().replace(/ي/g,'ی').replace(/ك/g,'ک').replace(/[‌ً-ْ]/g,''); }
    function openSearch(){ closeHeaderMenu(); document.getElementById('search-bar').classList.add('show'); const i=document.getElementById('search-input'); i.value=''; i.focus(); }
    function closeSearch(){ document.getElementById('search-bar').classList.remove('show'); clearSearchHL(); document.getElementById('search-input').value=''; document.getElementById('search-count').textContent=''; }
    function clearSearchHL(){ document.querySelectorAll('.search-hit').forEach(e=>e.classList.remove('search-hit')); document.querySelectorAll('.search-current').forEach(e=>e.classList.remove('search-current')); searchHits=[]; searchIdx=-1; }
    function runSearch(){
        clearSearchHL();
        const q=normalizeFa(document.getElementById('search-input').value.trim());
        const cnt=document.getElementById('search-count');
        if(!q){ cnt.textContent=''; return; }
        document.querySelectorAll('#chat-box .msg').forEach(el=>{
            if(normalizeFa(el.dataset.plain||'').includes(q)){ el.classList.add('search-hit'); searchHits.push(el); }
        });
        if(searchHits.length){ searchIdx=0; focusHit(); } else { cnt.textContent='۰'; }
    }
    function focusHit(){
        document.querySelectorAll('.search-current').forEach(e=>e.classList.remove('search-current'));
        const el=searchHits[searchIdx];
        if(el){ el.classList.add('search-current'); el.scrollIntoView({behavior:'smooth',block:'center'}); document.getElementById('search-count').textContent=(searchIdx+1)+'/'+searchHits.length; }
    }
    function searchStep(dir){ if(!searchHits.length) return; searchIdx=(searchIdx+dir+searchHits.length)%searchHits.length; focusHit(); }

    // --- فیچر ۵: والپیپر ---
    const WALLPAPERS=[
        {id:'default', light:'#f5f6f8', dark:'#0d1317'},
        {id:'mint', light:'linear-gradient(160deg,#e9f6f1,#d4ebe3)', dark:'linear-gradient(160deg,#0e1c1a,#11261f)'},
        {id:'sky', light:'linear-gradient(160deg,#eef3fb,#dde8f6)', dark:'linear-gradient(160deg,#0d1622,#101d2e)'},
        {id:'sand', light:'linear-gradient(160deg,#f8f2e9,#efe6d6)', dark:'linear-gradient(160deg,#1a160f,#221c12)'},
        {id:'rose', light:'linear-gradient(160deg,#fbeef1,#f5dce2)', dark:'linear-gradient(160deg,#221016,#2a131b)'},
        {id:'violet', light:'linear-gradient(160deg,#f1eefb,#e3dcf6)', dark:'linear-gradient(160deg,#16111f,#1d1430)'}
    ];
    function isDark(){ return document.documentElement.getAttribute('data-theme')==='dark'; }
    function applyWallpaper(id, save){
        const wp=WALLPAPERS.find(w=>w.id===id)||WALLPAPERS[0];
        document.getElementById('chat-box').style.background = isDark()? wp.dark : wp.light;
        if(save!==false) localStorage.setItem('wallpaper', id);
        document.querySelectorAll('.wp-swatch').forEach(s=>s.classList.toggle('active', s.dataset.wp===id));
    }
    function loadWallpaper(){ applyWallpaper(localStorage.getItem('wallpaper')||'default', false); }
    function openWallpaper(){
        closeHeaderMenu();
        const grid=document.getElementById('wallpaper-grid'); grid.innerHTML='';
        const cur=localStorage.getItem('wallpaper')||'default';
        WALLPAPERS.forEach(w=>{
            const d=document.createElement('div');
            d.className='wp-swatch'+(w.id===cur?' active':''); d.dataset.wp=w.id;
            d.style.background=isDark()? w.dark : w.light;
            d.onclick=()=>applyWallpaper(w.id, true);
            grid.appendChild(d);
        });
        showModal('wallpaper-modal');
    }

    // --- فیچر ۳: ارسال زمان‌بندی‌شده ---
    function pad2(n){ return String(n).padStart(2,'0'); }
    function toLocalInput(d){ return d.getFullYear()+'-'+pad2(d.getMonth()+1)+'-'+pad2(d.getDate())+'T'+pad2(d.getHours())+':'+pad2(d.getMinutes()); }
    function openScheduled(){
        closeHeaderMenu();
        document.getElementById('schedule-time').value = toLocalInput(new Date(Date.now()+3600000));
        refreshScheduledList();
        showModal('scheduled-modal');
    }
    async function scheduleCurrentText(){
        const composer=getComposer();
        const text=(composer? composer.innerText : '').replace(/​/g,'').trim();
        if(!text){ alert('ابتدا متن پیام را در کادر بنویس'); return; }
        const tv=document.getElementById('schedule-time').value;
        if(!tv){ alert('زمان را انتخاب کن'); return; }
        const da=new Date(tv).getTime()/1000;
        if(!da || da*1000 < Date.now()-60000){ alert('زمان نامعتبر یا گذشته است'); return; }
        const payload=JSON.stringify({kind:'rich_text', segments:[{text:text}]});
        const enc_data=await enc(payload);
        await fetch('/schedule_message',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({data:enc_data, deliver_at:da})});
        composer.innerHTML=''; autoGrow(composer);
        refreshScheduledList();
    }
    async function refreshScheduledList(){
        const box=document.getElementById('scheduled-list'); box.innerHTML='';
        try{
            const r=await (await fetch('/scheduled_list')).json();
            if(!r.scheduled || !r.scheduled.length){ box.innerHTML='<div class="sched-empty">موردی در صف نیست</div>'; return; }
            for(const it of r.scheduled){
                let preview='...';
                try{ preview = payloadToPlainText(parseMessagePayload(await dec(it.data))); }catch(e){}
                const when=new Date(it.deliver_at*1000);
                const div=document.createElement('div'); div.className='sched-item';
                div.innerHTML='<div class="sc-text"></div><div class="sc-time"></div><button class="sc-cancel">✕</button>';
                div.querySelector('.sc-text').textContent=preview.slice(0,60)||'(خالی)';
                div.querySelector('.sc-time').textContent=when.toLocaleString('fa-IR',{month:'short',day:'numeric',hour:'2-digit',minute:'2-digit'});
                div.querySelector('.sc-cancel').onclick=async()=>{ await fetch('/cancel_scheduled',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:it.id})}); refreshScheduledList(); };
                box.appendChild(div);
            }
        }catch(e){ box.innerHTML='<div class="sched-empty">خطا در دریافت</div>'; }
    }

    // --- فیچر ۴: چک‌لیست مشترک ---
    const checklistStore=new Map();
    function openChecklist(){ closeHeaderMenu(); document.getElementById('checklist-title').value=''; document.getElementById('checklist-items').value=''; showModal('checklist-modal'); }
    async function sendChecklist(){
        const title=document.getElementById('checklist-title').value.trim().slice(0,80);
        const items=document.getElementById('checklist-items').value.split('\n').map(s=>s.trim()).filter(Boolean).slice(0,40);
        if(!items.length){ alert('حداقل یک آیتم وارد کن'); return; }
        const payload={kind:'checklist', title:title, items:items.map(t=>({text:t.slice(0,120), checked:false}))};
        const enc_data=await enc(JSON.stringify(payload));
        await fetch('/send_message',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({type:'checklist', data:enc_data})});
        closeModals(); fetchMessages(); setTimeout(()=>scrollToBottom(),150);
    }
    function buildChecklistHtml(id, data){
        if(!data || !Array.isArray(data.items)) return '<div style="color:#e5484d;font-size:12px">چک‌لیست نامعتبر</div>';
        checklistStore.set(id, data);
        let html='<div class="checklist">';
        if(data.title) html+='<div class="checklist-title">'+escapeHtml(data.title)+'</div>';
        data.items.forEach((it,idx)=>{
            html+='<label class="checklist-item'+(it.checked?' done':'')+'" data-idx="'+idx+'"><input type="checkbox"'+(it.checked?' checked':'')+'><span>'+escapeHtml(it.text)+'</span></label>';
        });
        html+='</div>';
        return html;
    }
    function wireChecklist(div, id){
        div.querySelectorAll('.checklist-item').forEach(item=>{
            const cb=item.querySelector('input');
            if(!cb) return;
            cb.onclick=async(e)=>{
                e.stopPropagation();
                const idx=parseInt(item.dataset.idx);
                const data=checklistStore.get(id);
                if(!data || !data.items[idx]) return;
                data.items[idx].checked=cb.checked;
                item.classList.toggle('done', cb.checked);
                try{
                    const enc_data=await enc(JSON.stringify(data));
                    await fetch('/update_message_data',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:id, data:enc_data})});
                }catch(err){ console.error('checklist update failed', err); }
            };
        });
    }

    function scrollToBottom() {
        const b = document.getElementById('chat-box');
        b.scrollTop = b.scrollHeight;
        setTimeout(() => handleScroll(), 100);
    }

    function handleScroll() {
        const b = document.getElementById('chat-box');
        autoScroll = (b.scrollHeight - b.scrollTop - b.clientHeight < 100);
        const scrollBtn = document.getElementById('scroll-down-btn');
        if (autoScroll) {
            document.getElementById('new-msg-bubble').style.display = 'none';
            scrollBtn.classList.remove('show');
            if (!isWindowInactive()) {
                clearUnread();
            }
        } else {
            scrollBtn.classList.add('show');
        }
    }

    function deleteMsg(id) { if(confirm("حذف پیام؟")) postAction('/delete_message', {id: id}); }
    
    function editMsg(id, isEdited) {
        const msgEl = document.getElementById('msg-' + id);
        if (!msgEl) return;
        if (msgEl.querySelector('.voice-player') || msgEl.querySelector('.video-note') || msgEl.querySelector('.file-card')) return;
        const payload = textMessagePayloads.get(id) || payloadFromPlainText('');
        const currentText = payloadToPlainText(payload);
        editingTo = {id: id, originalText: currentText, payload: payload};
        
        const ep = document.getElementById('edit-preview');
        ep.style.display = 'flex';
        
        const singleLineText = currentText.replace(/\n/g, ' ').replace(/\s+/g, ' ').trim();
        const previewText = singleLineText.length > 50 ? singleLineText.substring(0, 50) + '...' : singleLineText;
        document.getElementById('edit-text').innerText = previewText;
        
        const i = document.getElementById('msgInput');
        i.dataset.placeholder = 'پیام را ویرایش کنید...';
        setComposerFromPayload(payload);
        
        cancelReply();
        focusComposer();
    }

    function scrollToMsg(id) {
        const el = document.getElementById('msg-' + id);
        if(el) { el.scrollIntoView({ behavior: 'smooth', block: 'center' }); el.classList.add('highlight'); setTimeout(()=>el.classList.remove('highlight'), 1500); }
    }

    let currentReactingMsgId = null;
    let reactionMenuCloseHandler = null;

    function showReactionMenu(e, msgId) {
        const menu = document.getElementById('reaction-menu');
        currentReactingMsgId = msgId;
        
        if (reactionMenuCloseHandler) {
            document.removeEventListener('click', reactionMenuCloseHandler);
            document.removeEventListener('touchstart', reactionMenuCloseHandler);
            reactionMenuCloseHandler = null;
        }
        
        const msgEl = document.getElementById('msg-' + msgId);
        if (!msgEl) return;
        
        const rect = msgEl.getBoundingClientRect();
        
        menu.style.visibility = 'hidden';
        menu.style.display = 'flex';
        menu.classList.add('show');
        
        const menuRect = menu.getBoundingClientRect();
        const menuWidth = menuRect.width || 200;
        const menuHeight = menuRect.height || 50;
        
        let left = rect.left + (rect.width / 2) - (menuWidth / 2);
        let top = rect.top - menuHeight - 10;
        
        const padding = 10;
        if (left < padding) left = padding;
        if (left + menuWidth > window.innerWidth - padding) {
            left = window.innerWidth - menuWidth - padding;
        }
        if (top < padding) {
            top = rect.bottom + 10;
        }
        
        menu.style.left = left + 'px';
        menu.style.top = top + 'px';
        menu.style.visibility = 'visible';
        
        reactionMenuCloseHandler = (event) => {
            if (!menu.contains(event.target) && event.target !== msgEl && !msgEl.contains(event.target)) {
                menu.classList.remove('show');
                menu.style.display = 'none';
                document.removeEventListener('click', reactionMenuCloseHandler);
                document.removeEventListener('touchstart', reactionMenuCloseHandler);
                reactionMenuCloseHandler = null;
            }
        };
        setTimeout(() => {
            document.addEventListener('click', reactionMenuCloseHandler);
            document.addEventListener('touchstart', reactionMenuCloseHandler);
        }, 10);
    }

    function selectReaction(emoji) {
        if (!currentReactingMsgId) return;
        
        const menu = document.getElementById('reaction-menu');
        menu.classList.remove('show');
        menu.style.display = 'none';
        
        if (reactionMenuCloseHandler) {
            document.removeEventListener('click', reactionMenuCloseHandler);
            document.removeEventListener('touchstart', reactionMenuCloseHandler);
            reactionMenuCloseHandler = null;
        }
        
        postAction('/react_message', {
            id: currentReactingMsgId,
            react: emoji
        });
        
        currentReactingMsgId = null;
    }

    let lastTypingSent = 0;

    const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);

    if (isMobile) {
        document.getElementById('msgInput').addEventListener('keydown', function(e) {
            if (e.key === 'Enter') {
                e.preventDefault();
                insertComposerLineBreak();
                return;
            }
        });
    } else {
        document.getElementById('msgInput').addEventListener('keydown', function(e) {
            if (e.key === 'Enter') {
                if (e.shiftKey) {
                    e.preventDefault();
                    insertComposerLineBreak();
                    return;
                } else {
                    e.preventDefault();
                    sendTxt();
                }
            }
        });
    }

    // ============================================================
    // ============  تماس صوتی/تصویری (WebRTC)  ====================
    // ============================================================
    let iceConfig = { enabled:false, iceServers:[] };
    let pc = null;
    let localStream = null;
    let callActive = false;        // تماس برقرار/در حال برقراری
    let incomingActive = false;    // در حال زنگ خوردن (ورودی)
    let callRole = null;           // 'caller' | 'callee'
    let callKind = 'audio';        // 'audio' | 'video'
    let incomingKind = 'audio';
    let pendingOffer = null;       // offer دریافتی تا زمان پاسخ
    let remoteCandQueue = [];       // candidateهای زودرس
    let micOn = true, camOn = true;
    let callPollSeq = 0;
    let callTimerInt = null, callStartTs = 0;
    let qualityInt = null;
    let ringTimer = null, ringCtx = null;

    function callEl(id){ return document.getElementById(id); }

    // --- دریافت پیکربندی STUN/TURN؛ اگر سرور آماده نبود، دوباره تلاش می‌کند ---
    async function loadIceServers(isRetry){
        try{
            const r = await fetch('/ice_servers', {cache:'no-store'});
            const d = await r.json();
            iceConfig = d || {enabled:false, iceServers:[]};
        }catch(e){ iceConfig = {enabled:false, iceServers:[]}; }
        const show = iceConfig.enabled ? '' : 'none';
        const ab = callEl('call-audio-btn'), vb = callEl('call-video-btn');
        if(ab) ab.style.display = show;
        if(vb) vb.style.display = show;
        // اگر هنوز فعال نشده (نصب TURN در جریان است) هر ۱۵ ثانیه دوباره بررسی کن
        if(!iceConfig.enabled) setTimeout(()=>loadIceServers(true), 15000);
        return iceConfig;
    }

    function rtcConfig(){
        return { iceServers: iceConfig.iceServers || [], iceCandidatePoolSize: 4, bundlePolicy:'max-bundle' };
    }

    // --- ارسال سیگنال به طرف مقابل ---
    async function signalSend(obj){
        try{
            await fetch('/call_signal', {method:'POST', headers:{'Content-Type':'application/json'},
                body: JSON.stringify({signal: obj})});
        }catch(e){ console.error('signal send error', e); }
    }

    // --- حلقهٔ همیشه‌فعال long-poll برای دریافت سیگنال‌ها (حتی خارج از تماس، برای تماس ورودی) ---
    async function callPollLoop(){
        for(;;){
            try{
                const r = await fetch('/call_poll?since=' + callPollSeq, {cache:'no-store'});
                if(r.status === 401){ await new Promise(s=>setTimeout(s,3000)); continue; }
                const d = await r.json();
                if(typeof d.seq === 'number') callPollSeq = d.seq;
                if(d.signals && d.signals.length){
                    for(const s of d.signals){ handleSignal(s.from, s.data); }
                }
            }catch(e){
                await new Promise(s=>setTimeout(s, 2000));
            }
        }
    }

    // --- بهینه‌سازی کیفیت صدا (Opus): FEC برای مقاومت به packet loss، بیت‌ریت بالا، DTX خاموش ---
    function tuneSdp(sdp){
        const m = sdp.match(/a=rtpmap:(\d+) opus\/48000/i);
        if(!m) return sdp;
        const pt = m[1];
        const opts = 'stereo=0;sprop-stereo=0;maxaveragebitrate=64000;maxplaybackrate=48000;useinbandfec=1;usedtx=0';
        const fmtpRe = new RegExp('a=fmtp:' + pt + ' ([^\\r\\n]*)');
        if(fmtpRe.test(sdp)){
            sdp = sdp.replace(fmtpRe, function(mm, params){
                const kept = params.split(';').filter(function(x){
                    return !/^(stereo|sprop-stereo|maxaveragebitrate|maxplaybackrate|useinbandfec|usedtx)=/.test(x.trim());
                });
                kept.push(opts);
                return 'a=fmtp:' + pt + ' ' + kept.filter(Boolean).join(';');
            });
        }else{
            sdp = sdp.replace(new RegExp('(a=rtpmap:' + pt + ' opus/48000[^\\r\\n]*\\r\\n)'),
                '$1a=fmtp:' + pt + ' ' + opts + '\r\n');
        }
        return sdp;
    }

    // --- تنظیم بیت‌ریت/فریم‌ریت ویدیو روی sender برای کیفیت بالا و بدون لگ ---
    async function tuneVideoSender(){
        if(!pc) return;
        for(const sender of pc.getSenders()){
            if(sender.track && sender.track.kind === 'video'){
                try{
                    const p = sender.getParameters();
                    if(!p.encodings || !p.encodings.length) p.encodings = [{}];
                    p.encodings[0].maxBitrate = 2000000;     // ۲ مگابیت برای ۷۲۰p
                    p.encodings[0].maxFramerate = 30;
                    p.degradationPreference = 'balanced';
                    await sender.setParameters(p);
                }catch(e){}
            }
        }
    }

    function createPC(){
        pc = new RTCPeerConnection(rtcConfig());
        pc.onicecandidate = function(e){
            if(e.candidate) signalSend({t:'cand', c:e.candidate});
        };
        pc.ontrack = function(e){
            const stream = (e.streams && e.streams[0]) ? e.streams[0] : null;
            if(!stream) return;
            if(e.track.kind === 'video'){
                const v = callEl('call-remote-video');
                if(v.srcObject !== stream){ v.srcObject = stream; }
            }else{
                const a = callEl('call-remote-audio');
                if(a.srcObject !== stream){ a.srcObject = stream; }
            }
        };
        pc.onconnectionstatechange = function(){
            if(!pc) return;
            const st = pc.connectionState;
            if(st === 'connected'){
                onCallConnected();
            }else if(st === 'failed'){
                setCallStatus('اتصال قطع شد، تلاش مجدد…');
                tryIceRestart();
            }else if(st === 'disconnected'){
                setCallStatus('اتصال ضعیف…');
            }
        };
    }

    async function tryIceRestart(){
        // فقط تماس‌گیرنده offer جدید با restartIce می‌سازد تا از حلقه جلوگیری شود
        if(callRole !== 'caller' || !pc) return;
        try{
            const offer = await pc.createOffer({iceRestart:true});
            offer.sdp = tuneSdp(offer.sdp);
            await pc.setLocalDescription(offer);
            signalSend({t:'offer', sdp: pc.localDescription.sdp, kind: callKind});
        }catch(e){}
    }

    async function getLocalMedia(kind){
        const constraints = {
            audio: { echoCancellation:true, noiseSuppression:true, autoGainControl:true },
            video: (kind === 'video') ? {
                width:{ideal:1280}, height:{ideal:720},
                frameRate:{ideal:30, max:30}, facingMode:'user'
            } : false
        };
        localStream = await navigator.mediaDevices.getUserMedia(constraints);
        for(const track of localStream.getTracks()){ pc.addTrack(track, localStream); }
        if(kind === 'video'){
            const lv = callEl('call-local-video');
            lv.srcObject = localStream;
        }
        micOn = true; camOn = (kind === 'video');
        updateCallButtons();
    }

    // ---------------------- شروع تماس (تماس‌گیرنده) ----------------------
    async function startCall(kind){
        if(callActive || incomingActive) return;
        await loadIceServers();   // اعتبارنامهٔ تازهٔ TURN
        if(!iceConfig.enabled){ alert('تماس در حال حاضر در دسترس نیست.'); return; }
        callKind = kind; callRole = 'caller'; callActive = true;
        pendingOffer = null; remoteCandQueue = [];
        try{
            createPC();
            await getLocalMedia(kind);
            await tuneVideoSender();
            showCallScreen(kind);
            setCallStatus('در حال زنگ خوردن…');
            signalSend({t:'invite', kind:kind});
            const offer = await pc.createOffer();
            offer.sdp = tuneSdp(offer.sdp);
            await pc.setLocalDescription(offer);
            signalSend({t:'offer', sdp: pc.localDescription.sdp, kind:kind});
            startRingback();
        }catch(e){
            console.error('startCall error', e);
            alert('دسترسی به دوربین/میکروفون ممکن نشد.');
            endCall();
        }
    }

    // ---------------------- مدیریت سیگنال‌های دریافتی ----------------------
    async function handleSignal(from, d){
        if(!d || !d.t) return;
        if(d.t === 'invite'){
            if(callActive || incomingActive){ signalSend({t:'busy'}); return; }
            incomingActive = true; incomingKind = d.kind || 'audio';
            showIncoming(incomingKind);
            startRingtone();
            return;
        }
        if(d.t === 'offer'){
            if(callActive && pc){
                // مذاکرهٔ مجدد یا restartIce
                try{
                    await pc.setRemoteDescription({type:'offer', sdp:d.sdp});
                    await flushCands();
                    const ans = await pc.createAnswer();
                    ans.sdp = tuneSdp(ans.sdp);
                    await pc.setLocalDescription(ans);
                    signalSend({t:'answer', sdp: pc.localDescription.sdp});
                }catch(e){ console.error(e); }
            }else{
                pendingOffer = d.sdp;   // تا زمان پاسخ نگه دار
            }
            return;
        }
        if(d.t === 'answer'){
            if(pc){
                try{ await pc.setRemoteDescription({type:'answer', sdp:d.sdp}); await flushCands(); }
                catch(e){ console.error(e); }
            }
            return;
        }
        if(d.t === 'cand'){
            await addRemoteCandidate(d.c);
            return;
        }
        if(d.t === 'busy'){ setCallStatus('مخاطب مشغول است'); setTimeout(()=>endCall(), 1500); return; }
        if(d.t === 'decline'){ setCallStatus('تماس رد شد'); setTimeout(()=>endCall(), 1200); return; }
        if(d.t === 'hangup'){ endCall(); return; }
    }

    async function addRemoteCandidate(c){
        if(!c) return;
        if(pc && pc.remoteDescription && pc.remoteDescription.type){
            try{ await pc.addIceCandidate(c); }catch(e){}
        }else{
            remoteCandQueue.push(c);
        }
    }
    async function flushCands(){
        const q = remoteCandQueue; remoteCandQueue = [];
        for(const c of q){ try{ await pc.addIceCandidate(c); }catch(e){} }
    }

    // ---------------------- پاسخ به تماس (گیرنده) ----------------------
    async function acceptIncoming(){
        if(!incomingActive) return;
        incomingActive = false; stopRingtone(); hideIncoming();
        await loadIceServers();
        if(!iceConfig.enabled){ endCall(); return; }
        callKind = incomingKind; callRole = 'callee'; callActive = true;
        remoteCandQueue = [];
        try{
            createPC();
            await getLocalMedia(callKind);
            await tuneVideoSender();
            showCallScreen(callKind);
            setCallStatus('در حال اتصال…');
            // منتظر رسیدن offer (ممکن است کمی دیرتر از invite برسد)
            for(let i=0; i<50 && !pendingOffer; i++){ await new Promise(s=>setTimeout(s,100)); }
            if(!pendingOffer){ endCall(); return; }
            await pc.setRemoteDescription({type:'offer', sdp:pendingOffer});
            pendingOffer = null;
            await flushCands();
            const ans = await pc.createAnswer();
            ans.sdp = tuneSdp(ans.sdp);
            await pc.setLocalDescription(ans);
            signalSend({t:'answer', sdp: pc.localDescription.sdp});
        }catch(e){
            console.error('accept error', e);
            alert('دسترسی به دوربین/میکروفون ممکن نشد.');
            endCall();
        }
    }

    function declineIncoming(){
        if(!incomingActive) return;
        incomingActive = false; stopRingtone(); hideIncoming();
        signalSend({t:'decline'});
    }

    function hangupCall(){
        signalSend({t:'hangup'});
        endCall();
    }

    function onCallConnected(){
        stopRingback();
        if(!callStartTs){
            callStartTs = Date.now();
            if(callTimerInt) clearInterval(callTimerInt);
            callTimerInt = setInterval(updateCallTimer, 1000);
            updateCallTimer();
            if(qualityInt) clearInterval(qualityInt);
            qualityInt = setInterval(monitorQuality, 2000);
        }
    }

    function updateCallTimer(){
        if(!callStartTs) return;
        const s = Math.floor((Date.now() - callStartTs)/1000);
        const mm = String(Math.floor(s/60)).padStart(2,'0');
        const ss = String(s%60).padStart(2,'0');
        setCallStatus(mm + ':' + ss);
    }

    async function monitorQuality(){
        if(!pc) return;
        try{
            const stats = await pc.getStats();
            let rtt = 0, fl = 0, hasFl = false;
            stats.forEach(function(r){
                if(r.type === 'candidate-pair' && r.state === 'succeeded' && r.currentRoundTripTime != null) rtt = r.currentRoundTripTime;
                if(r.type === 'remote-inbound-rtp' && r.fractionLost != null){ fl = r.fractionLost; hasFl = true; }
            });
            let q = 'good';
            if((hasFl && fl > 0.08) || rtt > 0.4) q = 'bad';
            else if((hasFl && fl > 0.03) || rtt > 0.2) q = 'medium';
            setQuality(q);
        }catch(e){}
    }

    function setQuality(q){
        const el = callEl('call-quality');
        if(!el) return;
        el.classList.remove('medium','bad');
        if(q === 'medium') el.classList.add('medium');
        else if(q === 'bad') el.classList.add('bad');
        callEl('call-quality-text').textContent = (q==='good'?'کیفیت عالی':(q==='medium'?'کیفیت متوسط':'کیفیت ضعیف'));
    }

    // ---------------------- کنترل‌ها ----------------------
    function toggleMic(){
        if(!localStream) return;
        micOn = !micOn;
        localStream.getAudioTracks().forEach(t=>t.enabled = micOn);
        updateCallButtons();
    }
    function toggleCam(){
        if(!localStream) return;
        const vts = localStream.getVideoTracks();
        if(!vts.length) return;
        camOn = !camOn;
        vts.forEach(t=>t.enabled = camOn);
        updateCallButtons();
    }
    function updateCallButtons(){
        const mb = callEl('call-mic-btn'), cb = callEl('call-cam-btn');
        if(mb) mb.classList.toggle('off', !micOn);
        if(cb){
            cb.classList.toggle('off', !camOn);
            cb.style.display = (callKind === 'video') ? '' : 'none';
        }
        const lv = callEl('call-local-video');
        if(lv) lv.style.opacity = camOn ? '1' : '0';
    }

    // ---------------------- UI ----------------------
    function showCallScreen(kind){
        const sc = callEl('call-screen');
        sc.classList.toggle('audio-only', kind !== 'video');
        sc.classList.add('show');
        callEl('call-peer-name').textContent = (document.getElementById('room-title')||{}).textContent || 'طرف مقابل';
        setQuality('good');
        updateCallButtons();
    }
    function showIncoming(kind){
        callEl('ring-name').textContent = (document.getElementById('room-title')||{}).textContent || 'تماس ورودی';
        callEl('ring-sub').textContent = (kind === 'video') ? 'تماس تصویری ورودی…' : 'تماس صوتی ورودی…';
        callEl('ring-avatar').textContent = (kind === 'video') ? '🎥' : '📞';
        callEl('call-incoming').classList.add('show');
    }
    function hideIncoming(){ callEl('call-incoming').classList.remove('show'); }

    function endCall(){
        try{ if(pc){ pc.onicecandidate=null; pc.ontrack=null; pc.onconnectionstatechange=null; pc.close(); } }catch(e){}
        pc = null;
        if(localStream){ localStream.getTracks().forEach(t=>{ try{t.stop();}catch(e){} }); localStream = null; }
        callActive = false; incomingActive = false; callRole = null;
        pendingOffer = null; remoteCandQueue = []; callStartTs = 0;
        if(callTimerInt){ clearInterval(callTimerInt); callTimerInt = null; }
        if(qualityInt){ clearInterval(qualityInt); qualityInt = null; }
        stopRingback(); stopRingtone();
        const rv = callEl('call-remote-video'), lv = callEl('call-local-video'), ra = callEl('call-remote-audio');
        if(rv) rv.srcObject = null;
        if(lv) lv.srcObject = null;
        if(ra) ra.srcObject = null;
        callEl('call-screen').classList.remove('show');
        hideIncoming();
    }

    // ---------------------- زنگ (WebAudio، بدون فایل خارجی) ----------------------
    function ensureRingCtx(){
        if(!ringCtx){
            try{ ringCtx = new (window.AudioContext || window.webkitAudioContext)(); }catch(e){ ringCtx = null; }
        }
        if(ringCtx && ringCtx.state === 'suspended'){ try{ ringCtx.resume(); }catch(e){} }
        return ringCtx;
    }
    function beep(freq, dur, vol){
        const ctx = ensureRingCtx(); if(!ctx) return;
        const o = ctx.createOscillator(), g = ctx.createGain();
        o.frequency.value = freq; o.type = 'sine';
        g.gain.value = vol || 0.18;
        o.connect(g); g.connect(ctx.destination);
        o.start();
        g.gain.setValueAtTime(g.gain.value, ctx.currentTime + dur*0.7);
        g.gain.linearRampToValueAtTime(0, ctx.currentTime + dur);
        o.stop(ctx.currentTime + dur);
    }
    function startRingtone(){   // آهنگ تماس ورودی
        stopRingtone();
        const play = ()=>{ beep(880,0.35); setTimeout(()=>beep(660,0.35), 420); };
        play(); ringTimer = setInterval(play, 1600);
    }
    function startRingback(){   // بوق انتظار برای تماس‌گیرنده
        stopRingback();
        const play = ()=>beep(440,0.4,0.12);
        play(); ringTimer = setInterval(play, 2500);
    }
    function stopRingtone(){ if(ringTimer){ clearInterval(ringTimer); ringTimer = null; } }
    function stopRingback(){ if(ringTimer){ clearInterval(ringTimer); ringTimer = null; } }

    function setCallStatus(t){ const el = callEl('call-status-text'); if(el) el.textContent = t; }

    // راه‌اندازی اولیهٔ زیرسیستم تماس
    loadIceServers();
    callPollLoop();
    window.addEventListener('beforeunload', function(){ if(callActive) signalSend({t:'hangup'}); });

</script>
</body>
</html>
"""


# --- Thread های پاک‌سازی ---
def clean_typing():
    """پاک‌سازی وضعیت تایپ کاربران در همهٔ اتاق‌ها"""
    while True:
        time.sleep(2)
        now = time.time()
        with LOCKED:
            for st in ROOMS_STATE.values():
                typing = st['typing']
                to_del = [u for u, t in typing.items() if now - t > 3]
                for u in to_del:
                    del typing[u]


def deliver_scheduled_messages():
    """ارسال پیام‌های زمان‌بندی‌شده‌ای که زمانشان فرارسیده است"""
    while True:
        time.sleep(5)
        try:
            now = time.time()
            conn = get_db_connection()
            cur = conn.cursor()
            rows = cur.execute("SELECT * FROM scheduled WHERE deliver_at <= ? ORDER BY deliver_at", (now,)).fetchall()
            conn.close()
            for r in rows:
                row = dict(r)
                message = {
                    'id': str(time.time()),
                    'sender_id': row['sender_id'],
                    'type': row.get('type') or 'text',
                    'data': row.get('data'),
                    'timestamp': time.time(),
                    'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"),
                    'seen': False,
                    'react': None,
                    'reply_id': row.get('reply_id'),
                    'reply_text': row.get('reply_text'),
                    'deleted': False,
                    'edited': False,
                    'updated': None,
                    'room_id': row['room_id'],
                    'pinned': False
                }
                st = get_room_state(row['room_id'])
                with LOCKED:
                    st['messages'].append(message)
                save_message_to_db(message)
                delete_scheduled(row['id'], row['room_id'])
                logger.info(f"پیام زمان‌بندی‌شده در اتاق {row['room_id']} ارسال شد")
        except Exception as e:
            logger.error(f"خطا در ارسال پیام‌های زمان‌بندی‌شده: {e}")


def cleanup_data():
    """پاک‌سازی دوره‌ای پیام‌های قدیمی و بازسازی حافظهٔ اتاق‌ها"""
    while True:
        time.sleep(300)  # هر 5 دقیقه
        try:
            cleanup_old_messages()
            # حافظهٔ اتاق‌های لودشده را باطل کن تا در دسترسی بعدی دوباره از دیتابیس بخواند
            with LOCKED:
                for st in ROOMS_STATE.values():
                    st['messages'].clear()
                    st['loaded'] = False
        except Exception as e:
            logger.error(f"خطا در پاک‌سازی دوره‌ای: {e}")


# --- Handler درخواست‌ها ---
class ChatHandler(http.server.BaseHTTPRequestHandler):
    
    def log_message(self, format, *args):
        """سفارشی‌سازی لاگ درخواست‌ها"""
        logger.debug(f"{self.address_string()} - {format % args}")

    def send_json_response(self, data, status=200):
        """ارسال پاسخ JSON"""
        self.send_response(status)
        self.send_header('Content-type', 'application/json; charset=utf-8')
        self.end_headers()
        self.wfile.write(json.dumps(data, ensure_ascii=False).encode('utf-8'))

    def send_html_response(self, html, status=200):
        """ارسال پاسخ HTML"""
        self.send_response(status)
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        self.end_headers()
        self.wfile.write(html.encode('utf-8'))

    def get_user_from_cookie(self):
        """دریافت و اعتبارسنجی نشست از کوکی امضاشده؛ (room_id, role) یا None"""
        cookies = parse_cookies(self.headers.get("Cookie", ""))
        return verify_session_token(cookies.get("chat_user"))

    def is_admin(self):
        """آیا کوکی ادمین معتبر است؟"""
        cookies = parse_cookies(self.headers.get("Cookie", ""))
        return verify_admin_token(cookies.get("chat_admin"))

    def do_GET(self):
        try:
            u = urllib.parse.urlparse(self.path)

            if u.path == '/':
                session = self.get_user_from_cookie()
                self.send_html_response(CHAT_PAGE if session else LOGIN_PAGE)
            elif u.path == '/logout':
                self.send_response(303)
                self.send_header("Set-Cookie", "chat_user=; Path=/; Max-Age=0")
                self.send_header("Set-Cookie", "chat_admin=; Path=/; Max-Age=0")
                self.send_header("Location", "/")
                self.end_headers()
            elif u.path == '/admin':
                if self.is_admin():
                    self.send_html_response(render_admin_page())
                else:
                    self.send_response(303)
                    self.send_header("Location", "/")
                    self.end_headers()
            elif u.path == '/get_messages':
                self.handle_get_messages(u.query)
            elif u.path == '/ice_servers':
                self.handle_ice_servers()
            elif u.path == '/call_poll':
                self.handle_call_poll(u.query)
            elif u.path == '/scheduled_list':
                self.handle_scheduled_list()
            elif u.path.startswith('/media/'):
                self.handle_get_media(u.path)
            else:
                self.send_response(404)
                self.end_headers()

        except Exception as e:
            logger.error(f"خطا در GET {self.path}: {e}")
            self.send_response(500)
            self.end_headers()

    def handle_get_media(self, path):
        """ارسال فایل‌های رمزنگاری‌شده رسانه (محدود به اتاق کاربر)"""
        session = self.get_user_from_cookie()
        if not session:
            self.send_response(401)
            self.end_headers()
            return
        room_id, role = session
        file_name = path.replace('/media/', '', 1)
        if not file_name or '/' in file_name or '\\' in file_name:
            self.send_response(400)
            self.end_headers()
            return
        # فایل باید متعلق به اتاق همین کاربر باشد
        if not media_belongs_to_room(file_name, room_id):
            self.send_response(404)
            self.end_headers()
            return
        file_path = os.path.join(MEDIA_DIR, file_name)
        if not os.path.isfile(file_path):
            self.send_response(404)
            self.end_headers()
            return
        try:
            with open(file_path, 'rb') as media_file:
                data = media_file.read()
            self.send_response(200)
            self.send_header('Content-Type', 'application/octet-stream')
            self.send_header('Content-Length', str(len(data)))
            self.send_header('Cache-Control', 'no-store')
            self.end_headers()
            self.wfile.write(data)
        except Exception as e:
            logger.error(f"خطا در ارسال فایل رسانه {file_name}: {e}")
            self.send_response(500)
            self.end_headers()

    def handle_get_messages(self, query):
        """پردازش درخواست دریافت پیام‌ها (محدود به اتاق کاربر)"""
        session = self.get_user_from_cookie()
        if not session:
            self.send_json_response({"error": "unauthorized"}, 401)
            return
        room_id, role = session
        room = get_room(room_id)
        if not room:
            self.send_json_response({"error": "room_gone"}, 401)
            return

        p = urllib.parse.parse_qs(query)

        def _parse_float(raw):
            try:
                v = float(raw)
            except (TypeError, ValueError):
                return 0.0
            if v != v or v == float('inf') or v == float('-inf'):
                return 0.0
            return v

        since = _parse_float(p.get('since', ['0'])[0])
        since_updated = _parse_float(p.get('since_updated', ['0'])[0])

        st = get_room_state(room_id)
        other_role = 'guest' if role == 'admin' else 'admin'
        news = []
        other_online = "Offline"
        seen_updates = []

        with LOCKED:
            st['last_seen'][role] = time.time()
            messages = st['messages']

            for m in messages:
                if m['sender_id'] != role and not m.get('seen'):
                    m['seen'] = True
                    m['updated'] = time.time()
                    seen_updates.append((m['id'], m['updated']))

            for m in messages:
                if m['timestamp'] > since or (m.get('updated') or 0) > since_updated:
                    msg_dict = dict(m)
                    if m['timestamp'] <= since and m.get('type') in ('voice', 'image', 'video_note', 'file'):
                        msg_dict.pop('data', None)
                    news.append(msg_dict)

            if other_role in st['last_seen']:
                diff = time.time() - st['last_seen'][other_role]
                other_online = "Online" if diff < 10 else (datetime.utcnow() - timedelta(seconds=diff) + timedelta(hours=3, minutes=30)).strftime("%H:%M")

            is_typing = other_role in st['typing']

        for mid, upd in seen_updates:
            update_message_in_db(mid, {'seen': 1, 'updated': upd})

        self.send_json_response({
            "me": role,
            "messages": news,
            "is_typing": is_typing,
            "other_online": other_online,
            "room_name": room.get('name') or ''
        })

    def handle_scheduled_list(self):
        """فهرست پیام‌های زمان‌بندی‌شدهٔ خود کاربر در این اتاق"""
        session = self.get_user_from_cookie()
        if not session:
            self.send_json_response({"error": "unauthorized"}, 401)
            return
        room_id, role = session
        items = list_scheduled(room_id, role)
        self.send_json_response({"scheduled": [
            {"id": it['id'], "deliver_at": it['deliver_at'], "data": it['data'], "type": it['type']}
            for it in items
        ]})

    def do_POST(self):
        try:
            try:
                content_length = int(self.headers.get('Content-Length', 0) or 0)
            except (TypeError, ValueError):
                self.send_response(400)
                self.end_headers()
                return
            if content_length < 0 or content_length > MAX_REQUEST_BYTES:
                # رد کردن بدنه‌ی منفی/خیلی بزرگ پیش از خواندن آن (جلوگیری از مصرف حافظه/معلق‌شدن)
                self.send_response(413)
                self.end_headers()
                return
            raw_bytes = self.rfile.read(content_length)
            parsed_url = urllib.parse.urlparse(self.path)

            # --- مسیرهای آپلود رسانه (نیازمند نشست اتاق) ---
            if parsed_url.path in ('/upload_video_note', '/upload_voice', '/upload_file'):
                session = self.get_user_from_cookie()
                if not session:
                    self.send_response(401)
                    self.end_headers()
                    return
                room_id, role = session
                if parsed_url.path == '/upload_video_note':
                    self.handle_upload_video_note(room_id, role, raw_bytes, parsed_url.query)
                elif parsed_url.path == '/upload_voice':
                    self.handle_upload_voice(room_id, role, raw_bytes, parsed_url.query)
                else:
                    self.handle_upload_file(room_id, role, raw_bytes, parsed_url.query)
                return

            raw = raw_bytes.decode('utf-8')

            if parsed_url.path == '/login':
                self.handle_login(raw)
                return
            if parsed_url.path == '/logout':
                self.send_response(303)
                self.send_header("Set-Cookie", "chat_user=; Path=/; Max-Age=0")
                self.send_header("Set-Cookie", "chat_admin=; Path=/; Max-Age=0")
                self.send_header("Location", "/")
                self.end_headers()
                return

            # --- مسیرهای پنل ادمین (نیازمند کوکی ادمین) ---
            if parsed_url.path == '/create_room':
                self.handle_create_room(raw)
                return
            if parsed_url.path == '/delete_room':
                self.handle_delete_room(raw)
                return

            # --- مسیرهای JSON با نشست اتاق ---
            body = parse_json_safely(raw)
            if not body and parsed_url.path != '/typing':
                self.send_response(400)
                self.end_headers()
                return

            session = self.get_user_from_cookie()
            if not session:
                self.send_response(401)
                self.end_headers()
                return
            room_id, role = session

            body['u_id'] = role
            body['sender_id'] = role
            body['room_id'] = room_id

            # اعتبارسنجی فیلدهای ضروری پیش از ارسال پاسخ 200
            if parsed_url.path in ('/delete_message', '/react_message', '/edit_message', '/pin_message', '/update_message_data'):
                if not isinstance(body.get('id'), str):
                    self.send_response(400)
                    self.end_headers()
                    return
            if parsed_url.path in ('/edit_message', '/update_message_data'):
                data_val = body.get('data')
                max_len = 16384 if parsed_url.path == '/update_message_data' else 8192
                if not isinstance(data_val, str) or len(data_val) > max_len:
                    self.send_response(400)
                    self.end_headers()
                    return
            if parsed_url.path == '/schedule_message':
                try:
                    da = float(body.get('deliver_at'))
                except (TypeError, ValueError):
                    da = float('nan')
                if da != da:
                    self.send_response(400)
                    self.end_headers()
                    return

            self.send_response(200)
            self.end_headers()

            if parsed_url.path == '/send_message':
                self.handle_send_message(body)
            elif parsed_url.path == '/delete_message':
                self.handle_delete_message(body)
            elif parsed_url.path == '/react_message':
                self.handle_react_message(body)
            elif parsed_url.path == '/edit_message':
                self.handle_edit_message(body)
            elif parsed_url.path == '/typing':
                self.handle_typing(body)
            elif parsed_url.path == '/pin_message':
                self.handle_pin_message(body)
            elif parsed_url.path == '/update_message_data':
                self.handle_update_message_data(body)
            elif parsed_url.path == '/schedule_message':
                self.handle_schedule_message(body)
            elif parsed_url.path == '/cancel_scheduled':
                self.handle_cancel_scheduled(body)
            elif parsed_url.path == '/call_signal':
                self.handle_call_signal(body)

        except Exception as e:
            logger.error(f"خطا در POST {self.path}: {e}")
            try:
                self.send_response(500)
                self.end_headers()
            except Exception:
                pass

    def handle_login(self, raw):
        """پردازش ورود کاربر (اتاق یا ادمین اصلی)"""
        ip = self.client_address[0] if self.client_address else "?"

        now = time.time()
        with _LOGIN_LOCK:
            entry = _LOGIN_FAILS.get(ip)
            if entry and entry.get("lock_until", 0) > now:
                logger.warning(f"ورود مسدود (rate-limit) از {ip}")
                self.send_response(429)
                self.send_header("Retry-After", str(LOGIN_LOCK_SECONDS))
                self.end_headers()
                return

        parsed = urllib.parse.parse_qs(raw)
        p = parsed.get("p", [""])[0]

        # ادمین اصلی → پنل مدیریت اتاق‌ها
        if p and hmac.compare_digest(p, ADMIN_MASTER_PASSWORD):
            with _LOGIN_LOCK:
                _LOGIN_FAILS.pop(ip, None)
            logger.info("ورود ادمین اصلی")
            self.send_response(303)
            self.send_header("Set-Cookie", f"chat_admin={make_admin_token()}; Path=/; SameSite=Lax; HttpOnly")
            self.send_header("Location", "/admin")
            self.end_headers()
            return

        # رمز اتاق → ورود به همان اتاق
        match = lookup_password(p)
        if match:
            room_id, role = match
            with _LOGIN_LOCK:
                _LOGIN_FAILS.pop(ip, None)
            logger.info(f"ورود موفق به اتاق {room_id} ({role})")
            self.send_response(303)
            self.send_header("Set-Cookie", f"chat_user={make_session_token(room_id, role)}; Path=/; SameSite=Lax; HttpOnly")
            self.send_header("Location", "/")
            self.end_headers()
        else:
            with _LOGIN_LOCK:
                entry = _LOGIN_FAILS.get(ip) or {"count": 0, "lock_until": 0}
                entry["count"] += 1
                if entry["count"] >= LOGIN_MAX_FAILS:
                    entry["lock_until"] = now + LOGIN_LOCK_SECONDS
                    entry["count"] = 0
                _LOGIN_FAILS[ip] = entry
            logger.warning(f"تلاش ورود ناموفق از {ip}")
            time.sleep(0.5)
            self.send_response(303)
            self.send_header("Location", "/")
            self.end_headers()

    def handle_create_room(self, raw):
        """ساخت اتاق جدید (فقط ادمین)"""
        if not self.is_admin():
            self.send_response(303)
            self.send_header("Location", "/")
            self.end_headers()
            return
        parsed = urllib.parse.parse_qs(raw)
        name = (parsed.get("name", [""])[0] or "").strip()[:60]
        admin_pass = (parsed.get("admin_pass", [""])[0] or "").strip()[:64]
        guest_pass = (parsed.get("guest_pass", [""])[0] or "").strip()[:64]
        if name and admin_pass and guest_pass and admin_pass != guest_pass:
            create_room(name, admin_pass, guest_pass)
        self.send_response(303)
        self.send_header("Location", "/admin")
        self.end_headers()

    def handle_delete_room(self, raw):
        """حذف اتاق (فقط ادمین)"""
        if not self.is_admin():
            self.send_response(303)
            self.send_header("Location", "/")
            self.end_headers()
            return
        parsed = urllib.parse.parse_qs(raw)
        room_id = (parsed.get("room_id", [""])[0] or "").strip()
        if room_id:
            delete_room(room_id)
        self.send_response(303)
        self.send_header("Location", "/admin")
        self.end_headers()

    def _save_media_message(self, room_id, role, encrypted_bytes, file_name, mtype, data_obj):
        """نوشتن فایل رسانه و ساخت پیام در اتاق مربوطه"""
        file_path = os.path.join(MEDIA_DIR, file_name)
        try:
            with open(file_path, 'wb') as media_file:
                media_file.write(encrypted_bytes)
        except Exception as e:
            logger.error(f"خطا در ذخیره رسانه: {e}")
            return None
        message = {
            'id': str(time.time()),
            'sender_id': role,
            'type': mtype,
            'data': json.dumps(data_obj, ensure_ascii=False),
            'timestamp': time.time(),
            'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"),
            'seen': False,
            'react': None,
            'reply_id': (self.headers.get('X-Reply-Id') or '')[:64] or None,
            'reply_text': (self.headers.get('X-Reply-Text') or '')[:2048] or None,
            'deleted': False,
            'edited': False,
            'updated': None,
            'room_id': room_id,
            'pinned': False
        }
        st = get_room_state(room_id)
        with LOCKED:
            st['messages'].append(message)
        save_message_to_db(message)
        return message

    def handle_upload_video_note(self, room_id, role, encrypted_bytes, query):
        """ذخیره پیام ویدیویی رمزنگاری‌شده به صورت فایل"""
        if not encrypted_bytes or len(encrypted_bytes) < 20:
            self.send_json_response({"error": "invalid_video_payload"}, 400)
            return
        if len(encrypted_bytes) > 10 * 1024 * 1024:
            self.send_json_response({"error": "video_too_large"}, 400)
            return

        params = urllib.parse.parse_qs(query)
        mime_type = params.get('mime', ['video/webm'])[0]
        if not mime_type.startswith('video/') or not re.match(r'^[a-zA-Z0-9.+-]+/[a-zA-Z0-9.+-]+$', mime_type):
            mime_type = 'video/webm'

        file_id = hashlib.sha256(f"{room_id}:{role}:{time.time()}:{len(encrypted_bytes)}".encode('utf-8')).hexdigest()[:24]
        file_name = f"{file_id}.bin"
        message = self._save_media_message(room_id, role, encrypted_bytes, file_name, 'video_note',
                                           {'kind': 'video_note', 'file': file_name, 'mime': mime_type})
        if not message:
            self.send_json_response({"error": "video_save_failed"}, 500)
            return
        self.send_json_response({"ok": True, "id": message['id']}, 200)

    def handle_upload_voice(self, room_id, role, encrypted_bytes, query):
        """ذخیره پیام صوتی رمزنگاری‌شده به صورت فایل"""
        if not encrypted_bytes or len(encrypted_bytes) < 20:
            self.send_json_response({"error": "invalid_voice_payload"}, 400)
            return
        if len(encrypted_bytes) > 1024 * 1024:
            self.send_json_response({"error": "voice_too_large"}, 400)
            return

        params = urllib.parse.parse_qs(query)
        mime_type = params.get('mime', ['audio/webm'])[0]
        if not mime_type.startswith('audio/') or not re.match(r'^[a-zA-Z0-9.+-]+/[a-zA-Z0-9.+-]+$', mime_type):
            mime_type = 'audio/webm'

        file_id = hashlib.sha256(f"{room_id}:{role}:{time.time()}:{len(encrypted_bytes)}".encode('utf-8')).hexdigest()[:24]
        file_name = f"{file_id}.bin"
        message = self._save_media_message(room_id, role, encrypted_bytes, file_name, 'voice',
                                           {'kind': 'voice', 'file': file_name, 'mime': mime_type})
        if not message:
            self.send_json_response({"error": "voice_save_failed"}, 500)
            return
        self.send_json_response({"ok": True, "id": message['id']}, 200)

    def handle_upload_file(self, room_id, role, encrypted_bytes, query):
        """ذخیره فایل رمزنگاری‌شده به صورت فایل"""
        if not encrypted_bytes or len(encrypted_bytes) < 20:
            self.send_json_response({"error": "invalid_file_payload"}, 400)
            return
        if len(encrypted_bytes) > 20 * 1024 * 1024:
            self.send_json_response({"error": "file_too_large"}, 400)
            return

        params = urllib.parse.parse_qs(query)
        mime_type = params.get('mime', ['application/octet-stream'])[0]
        original_name = params.get('name', ['file'])[0]
        try:
            file_size = int(params.get('size', ['0'])[0])
        except Exception:
            file_size = 0

        if not re.match(r'^[a-zA-Z0-9.+-]+/[a-zA-Z0-9.+-]+$', mime_type or ''):
            mime_type = 'application/octet-stream'

        original_name = os.path.basename(original_name or 'file').strip() or 'file'
        original_name = re.sub(r'[\x00-\x1f\x7f]+', '', original_name)
        if len(original_name) > 180:
            original_name = original_name[:180]
        file_size = max(0, file_size)

        file_id = hashlib.sha256(f"{room_id}:{role}:{time.time()}:{len(encrypted_bytes)}:{original_name}".encode('utf-8')).hexdigest()[:24]
        file_name = f"{file_id}.bin"
        message = self._save_media_message(room_id, role, encrypted_bytes, file_name, 'file', {
            'kind': 'file', 'file': file_name, 'mime': mime_type,
            'name': original_name, 'size': file_size
        })
        if not message:
            self.send_json_response({"error": "file_save_failed"}, 500)
            return
        self.send_json_response({"ok": True, "id": message['id']}, 200)

    def handle_send_message(self, body):
        """پردازش ارسال پیام"""
        room_id = body['room_id']
        mtype = body.get('type', 'text')
        if mtype not in ('text', 'checklist'):
            mtype = 'text'
        message = {
            'id': str(time.time()),
            'sender_id': body['sender_id'],
            'type': mtype,
            'data': body.get('data'),
            'timestamp': time.time(),
            'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"),
            'seen': False,
            'react': None,
            'reply_id': (str(body.get('reply_id') or '')[:64]) or None,
            'reply_text': (str(body.get('reply_text') or '')[:2048]) or None,
            'deleted': False,
            'edited': False,
            'updated': None,
            'room_id': room_id,
            'pinned': False
        }
        st = get_room_state(room_id)
        with LOCKED:
            st['messages'].append(message)
        save_message_to_db(message)

    def handle_delete_message(self, body):
        """پردازش حذف پیام"""
        st = get_room_state(body['room_id'])
        with LOCKED:
            for m in st['messages']:
                if m['id'] == body['id'] and m['sender_id'] == body['u_id']:
                    delete_media_file(m)
                    m['deleted'] = True
                    m['data'] = "-"
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {'deleted': 1, 'data': '-', 'updated': m['updated']})
                    break

    def handle_react_message(self, body):
        """پردازش واکنش به پیام"""
        react_emoji = body.get('react')
        if react_emoji is not None and react_emoji not in ALLOWED_REACTIONS:
            return
        st = get_room_state(body['room_id'])
        with LOCKED:
            for m in st['messages']:
                if m['id'] == body['id']:
                    if m['sender_id'] == body['u_id']:
                        break
                    m['react'] = None if m.get('react') == react_emoji else react_emoji
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {'react': m['react'], 'updated': m['updated']})
                    break

    def handle_edit_message(self, body):
        """پردازش ویرایش پیام"""
        st = get_room_state(body['room_id'])
        with LOCKED:
            for m in st['messages']:
                if m['id'] == body['id'] and m['sender_id'] == body['u_id']:
                    if m.get('type') in ('image', 'voice', 'video_note', 'file'):
                        break
                    m['data'] = body['data']
                    m['edited'] = True
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {'data': m['data'], 'edited': 1, 'updated': m['updated']})
                    break

    def handle_pin_message(self, body):
        """سنجاق/برداشتن سنجاق پیام (هر دو کاربر اتاق می‌توانند)"""
        st = get_room_state(body['room_id'])
        with LOCKED:
            for m in st['messages']:
                if m['id'] == body['id']:
                    new_pinned = not m.get('pinned')
                    m['pinned'] = new_pinned
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {'pinned': 1 if new_pinned else 0, 'updated': m['updated']})
                    break

    def handle_update_message_data(self, body):
        """به‌روزرسانی دادهٔ پیام چک‌لیست (هر دو کاربر اتاق می‌توانند)"""
        st = get_room_state(body['room_id'])
        with LOCKED:
            for m in st['messages']:
                if m['id'] == body['id'] and m.get('type') == 'checklist':
                    m['data'] = body['data']
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {'data': m['data'], 'updated': m['updated']})
                    break

    def handle_schedule_message(self, body):
        """ثبت یک پیام متنی برای ارسال زمان‌بندی‌شده"""
        room_id = body['room_id']
        role = body['sender_id']
        data = body.get('data')
        if not isinstance(data, str) or len(data) > 8192:
            return
        reply_id = (str(body.get('reply_id') or '')[:64]) or None
        reply_text = (str(body.get('reply_text') or '')[:2048]) or None
        try:
            deliver_at = float(body.get('deliver_at'))
        except (TypeError, ValueError):
            return
        now = time.time()
        if deliver_at < now:
            deliver_at = now
        if deliver_at > now + 90 * 24 * 3600:
            return
        add_scheduled(room_id, role, 'text', data, reply_id, reply_text, deliver_at)

    def handle_cancel_scheduled(self, body):
        """لغو یک پیام زمان‌بندی‌شده"""
        sid = body.get('id')
        if isinstance(sid, str):
            delete_scheduled(sid, body['room_id'])

    def handle_typing(self, body):
        """پردازش وضعیت تایپ"""
        st = get_room_state(body['room_id'])
        with LOCKED:
            st['typing'][body['u_id']] = time.time()

    # ---------------------- تماس صوتی/تصویری (WebRTC) ----------------------
    def handle_ice_servers(self):
        """پیکربندی STUN/TURN با اعتبارنامهٔ موقت برای مرورگر."""
        session = self.get_user_from_cookie()
        if not session:
            self.send_json_response({"enabled": False}, 401)
            return
        host = (self.headers.get('Host', '').split(':')[0] or '').strip()
        self.send_json_response(build_ice_servers(host))

    def handle_call_poll(self, query):
        """long-poll دریافت سیگنال‌های تماس برای کاربر فعلی."""
        session = self.get_user_from_cookie()
        if not session:
            self.send_json_response({"error": "unauthorized"}, 401)
            return
        room_id, role = session
        p = urllib.parse.parse_qs(query)
        try:
            since = int(p.get('since', ['0'])[0])
        except (TypeError, ValueError):
            since = 0
        seq, items = fetch_signals(room_id, role, since)
        self.send_json_response({
            "seq": seq,
            "signals": [{"from": it['frm'], "data": it['data']} for it in items],
        })

    def handle_call_signal(self, body):
        """ارسال یک سیگنال تماس به طرف مقابلِ همین اتاق."""
        room_id = body['room_id']
        role = body['sender_id']
        other = 'guest' if role == 'admin' else 'admin'
        data = body.get('signal')
        if data is not None:
            push_signal(room_id, role, other, data)


class ThreadingHTTPServer(socketserver.ThreadingMixIn, socketserver.TCPServer):
    daemon_threads = True
    allow_reuse_address = True


# تزریق @font-face امبدشده به هر دو قالب صفحه
LOGIN_PAGE = LOGIN_PAGE.replace("/*__VAZIR__*/", FONT_FACE_CSS)
CHAT_PAGE = CHAT_PAGE.replace("/*__VAZIR__*/", FONT_FACE_CSS)

if __name__ == "__main__":
    # مقداردهی اولیه دیتابیس
    ensure_media_dir()
    init_database()
    load_messages_to_memory()
    
    # شروع thread های پاک‌سازی و تحویل پیام‌های زمان‌بندی‌شده
    threading.Thread(target=clean_typing, daemon=True).start()
    threading.Thread(target=cleanup_data, daemon=True).start()
    threading.Thread(target=deliver_scheduled_messages, daemon=True).start()

    # راه‌اندازی خودکار TURN در پس‌زمینه (غیرکشنده؛ اگر شکست بخورد فقط تماس غیرفعال می‌شود)
    threading.Thread(target=setup_turn, daemon=True).start()
    
    # شروع سرور
    with ThreadingHTTPServer(("0.0.0.0", PORT), ChatHandler) as httpd:
        scheme = "http"
        if SSL_CERTFILE and SSL_KEYFILE and os.path.isfile(SSL_CERTFILE) and os.path.isfile(SSL_KEYFILE):
            try:
                import ssl
                ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
                ctx.load_cert_chain(certfile=SSL_CERTFILE, keyfile=SSL_KEYFILE)
                httpd.socket = ctx.wrap_socket(httpd.socket, server_side=True)
                scheme = "https"
            except Exception as e:
                logger.error(f"TLS فعال نشد ({e})؛ روی HTTP ادامه می‌دهد")
        logger.info(f"سرور چت روی {scheme}://0.0.0.0:{PORT} شروع به کار کرد...")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            logger.info("سرور متوقف شد")
