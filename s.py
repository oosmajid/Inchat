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
import re
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
PORT = 2026
MAX_MESSAGES_IN_MEMORY = 500  # حداکثر تعداد پیام در حافظه
MESSAGE_EXPIRY_HOURS = 24  # مدت زمان نگهداری پیام‌ها

PASSWORD_TO_USER = {
    "2728": "USER_A",
    "9604": "USER_B",
}

DB_FILE = "chat_history.db"
MEDIA_DIR = "encrypted_media"

# استفاده از deque برای محدود کردن پیام‌ها در حافظه
MESSAGES = deque(maxlen=MAX_MESSAGES_IN_MEMORY)
TYPING_USERS = {}
LAST_SEEN = {}

# استفاده از RLock برای امکان nested locking
LOCKED = threading.RLock()

# --- کلید رمزنگاری AES-like (ساده‌شده برای سازگاری با مرورگر) ---
# نکته: برای امنیت بیشتر باید از Web Crypto API استفاده شود
ENCRYPTION_SALT = "chat_secure_2024"


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


def init_database():
    """ایجاد جداول دیتابیس"""
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
        
        # ایجاد ایندکس برای جستجوی سریع‌تر
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_timestamp ON messages(timestamp)')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_sender ON messages(sender_id)')
        cursor.execute('CREATE INDEX IF NOT EXISTS idx_deleted ON messages(deleted)')
        
        conn.commit()
        conn.close()
        logger.info("دیتابیس با موفقیت آماده شد")
    except Exception as e:
        logger.error(f"خطا در ایجاد دیتابیس: {e}")
        raise


def load_messages_to_memory():
    """بارگذاری پیام‌های اخیر به حافظه"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        
        # فقط پیام‌های غیرحذف‌شده و جدید را بارگذاری کن
        expiry_time = time.time() - (MESSAGE_EXPIRY_HOURS * 3600)
        cursor.execute('''
            SELECT * FROM messages 
            WHERE deleted = 0 AND timestamp > ? 
            ORDER BY timestamp DESC 
            LIMIT ?
        ''', (expiry_time, MAX_MESSAGES_IN_MEMORY))
        
        rows = cursor.fetchall()
        conn.close()
        
        # ترتیب را معکوس کن (قدیمی به جدید)
        for row in reversed(rows):
            MESSAGES.append(dict(row))
        
        logger.info(f"{len(MESSAGES)} پیام به حافظه بارگذاری شد")
    except Exception as e:
        logger.error(f"خطا در بارگذاری پیام‌ها: {e}")


def save_message_to_db(message):
    """ذخیره یک پیام در دیتابیس"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        
        cursor.execute('''
            INSERT OR REPLACE INTO messages 
            (id, sender_id, type, data, timestamp, time, seen, react, reply_id, reply_text, deleted, edited, updated)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
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
            message.get('updated')
        ))
        
        conn.commit()
        conn.close()
    except Exception as e:
        logger.error(f"خطا در ذخیره پیام: {e}")


def update_message_in_db(message_id, updates):
    """به‌روزرسانی یک پیام در دیتابیس"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        
        set_clause = ', '.join([f"{k} = ?" for k in updates.keys()])
        values = list(updates.values()) + [message_id]
        
        cursor.execute(f'''
            UPDATE messages SET {set_clause} WHERE id = ?
        ''', values)
        
        conn.commit()
        conn.close()
    except Exception as e:
        logger.error(f"خطا در به‌روزرسانی پیام: {e}")


def cleanup_old_messages():
    """حذف پیام‌های قدیمی از دیتابیس"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        
        expiry_time = time.time() - (MESSAGE_EXPIRY_HOURS * 3600)
        cursor.execute('SELECT type, data FROM messages WHERE timestamp < ?', (expiry_time,))
        old_rows = cursor.fetchall()
        for row in old_rows:
            if row['type'] in ('voice', 'video_note', 'file'):
                delete_media_file(dict(row))
        cursor.execute('DELETE FROM messages WHERE timestamp < ?', (expiry_time,))
        
        deleted_count = cursor.rowcount
        conn.commit()
        conn.close()
        
        if deleted_count > 0:
            logger.info(f"{deleted_count} پیام قدیمی حذف شد")
    except Exception as e:
        logger.error(f"خطا در حذف پیام‌های قدیمی: {e}")


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
    * { box-sizing: border-box; }

    :root {
        --bg-color: #eceff1;
        --card-bg: white;
        --text-color: #263238;
        --input-border: #cfd8dc;
        --button-bg: #00796b;
        --button-hover: #004d40;
    }

    [data-theme="dark"] {
        --bg-color: #121212;
        --card-bg: #1e1e1e;
        --text-color: #e0e0e0;
        --input-border: #424242;
        --button-bg: #00796b;
        --button-hover: #004d40;
    }

    body { 
        font-family: 'Tahoma', sans-serif; 
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
    }

    .card { 
        background: var(--card-bg); 
        padding: 40px; 
        border-radius: 28px; 
        text-align: center; 
        width: 100%;
        max-width: 340px; 
        box-shadow: 0 10px 25px rgba(0,0,0,0.1); 
        transition: background 0.3s;
    }

    h2 { color: var(--text-color); margin-bottom: 20px; transition: color 0.3s; }

    input { 
        width: 100%; 
        padding: 15px; 
        margin: 15px 0; 
        border-radius: 12px; 
        border: 1px solid var(--input-border); 
        text-align: center; 
        outline: none; 
        font-size: 16px; 
        background: var(--card-bg);
        color: var(--text-color);
        transition: all 0.3s;
    }

    button { 
        width: 100%; 
        background: var(--button-bg); 
        color: white; 
        border: none; 
        padding: 15px; 
        border-radius: 12px; 
        cursor: pointer; 
        font-weight: bold; 
        font-size: 16px; 
        transition: 0.3s; 
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
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
    <title>این‌چت</title>
    <link id="app-favicon" rel="icon" type="image/png">
    <style>
        :root {
            --bg-color: #efe7dd;
            --header-bg: #005c4b;
            --sent-msg-bg: white;
            --received-msg-bg: #d9fdd3;
            --input-bg: #f0f2f5;
            --input-container-bg: #f0f2f5;
            --reply-preview-bg: #f0f2f5;
            --input-border: #d1d7db;
            --text-color: #000;
            --secondary-text: #54656f;
            --msg-actions-color: #00796b;
            --reaction-bg: white;
            --highlight-bg: #fff59d;
            --reply-area-bg: rgba(0,0,0,0.04);
            --reply-border: #00a884;
            --icon-fill: #54656f;
            --send-icon-fill: #00a884;
        }

        [data-theme="dark"] {
            --bg-color: #0b141a;
            --header-bg: #202c33;
            --sent-msg-bg: #005c4b;
            --received-msg-bg: #202c33;
            --input-bg: #2a3942;
            --input-container-bg: #202c33;
            --reply-preview-bg: #202c33;
            --input-border: #2a3942;
            --text-color: #e9edef;
            --secondary-text: #8696a0;
            --msg-actions-color: #00a884;
            --reaction-bg: #2a3942;
            --highlight-bg: #547a7a;
            --reply-area-bg: rgba(255,255,255,0.1);
            --reply-border: #00a884;
            --icon-fill: #8696a0;
            --send-icon-fill: #00a884;
        }

        * { box-sizing: border-box; font-family: 'Segoe UI', Tahoma, sans-serif; }

        body {
            background: var(--bg-color);
            margin: 0;
            height: var(--app-height, 100dvh);
            display: flex;
            flex-direction: column;
            overflow: hidden;
            transition: background 0.3s;
        }

        /* Header Material */
        #header { background: var(--header-bg); color: white; padding: 12px 20px; box-shadow: 0 2px 4px rgba(0,0,0,0.2); z-index: 10; display: flex; flex-direction: column; align-items: center; transition: background 0.3s; position: relative; }
        #header b { font-size: 18px; }
        #status-bar { font-size: 12px; opacity: 0.9; margin-top: 2px; }
        .theme-toggle {
            position: absolute;
            left: 20px;
            top: 50%;
            transform: translateY(-50%);
            background: rgba(255,255,255,0.1);
            border: none;
            border-radius: 50%;
            width: 36px;
            height: 36px;
            cursor: pointer;
            display: flex;
            align-items: center;
            justify-content: center;
            font-size: 18px;
            transition: all 0.3s;
        }
        .theme-toggle:hover {
            background: rgba(255,255,255,0.2);
        }

        /* Chat Area */
        #chat-box { flex: 1; overflow-y: auto; padding: 15px; display: flex; flex-direction: column; gap: 8px; scroll-behavior: smooth; }

        /* Message Bubbles */
        .msg { 
            max-width: 80%; 
            padding: 8px 12px; 
            border-radius: 16px; 
            font-size: 14.5px; 
            position: relative; 
            box-shadow: 0 1px 0.5px rgba(0,0,0,0.15); 
            transition: all 0.2s; 
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

        .sent { background: var(--sent-msg-bg); color: var(--text-color); align-self: flex-start; border-top-left-radius: 4px; transition: background 0.3s, color 0.3s; }
        .received { background: var(--received-msg-bg); color: var(--text-color); align-self: flex-end; border-top-right-radius: 4px; transition: background 0.3s, color 0.3s; }
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

        /* Input Area Material */
        #input-container { background: var(--input-container-bg); padding: 8px 16px; display: flex; align-items: flex-end; gap: 10px; border-top: 1px solid var(--input-border); position: sticky; bottom: 0; z-index: 20; transition: background 0.3s, border-color 0.3s; }

        #msgInput { flex: 1; border: none; padding: 10px 15px; border-radius: 20px; outline: none; font-size: 15px; max-height: 120px; min-height: 40px; resize: none; background: var(--input-bg); color: var(--text-color); line-height: 20px; transition: background 0.3s, color 0.3s; }

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
            padding: 16px 24px;
            border-radius: 20px;
            box-shadow: 0 4px 20px rgba(0,0,0,0.25);
            z-index: 1000;
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
        .recording-send:hover { background: #008069; }
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

        #key-overlay { position: fixed; top:0; left:0; width:100%; height:100%; background:var(--header-bg, #005c4b); z-index:10000; display:flex; justify-content:center; align-items:center; transition: background 0.3s; }

        #new-msg-bubble {
            display: none;
            position: fixed;
            bottom: var(--bubble-bottom, 85px);
            left: 50%;
            transform: translateX(-50%);
            background: #00a884;
            color: white;
            padding: 8px 16px;
            border-radius: 20px;
            font-size: 13px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.3);
            cursor: pointer;
            z-index: 1000;
            font-weight: bold;
            animation: fadeIn 0.3s;
        }
        #scroll-down-btn {
            display: none;
            position: fixed;
            bottom: var(--bubble-bottom, 85px);
            right: 20px;
            background: #00a884;
            color: white;
            border: none;
            border-radius: 50%;
            width: 40px;
            height: 40px;
            cursor: pointer;
            z-index: 1000;
            box-shadow: 0 2px 8px rgba(0,0,0,0.3);
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
            background: #008069;
            transform: scale(1.1);
        }
        a { color: #00a884; }
        @keyframes fadeIn {
            from { opacity: 0; bottom: calc(var(--bubble-bottom, 85px) - 15px); }
            to   { opacity: 1; bottom: var(--bubble-bottom, 85px); }
        }

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
        <input type="password" id="kInp" style="width:100%; padding:15px; margin-bottom:20px; border-radius:12px; text-align:center; font-size:18px;" placeholder="کلید محرمانه">
        <button onclick="startChat()" style="width:100%; background:#00a884; color:white; border:none; padding:15px; border-radius:12px; font-weight:bold; cursor:pointer;">تایید</button>
    </div>
</div>

<div id="header">
    <button class="theme-toggle" onclick="toggleTheme()" title="تغییر تم">🌙</button>
    <b>این‌چت</b>
    <div id="status-bar">درحال اتصال...</div>
</div>

<div id="chat-box" onscroll="handleScroll()"></div>
<div id="typing-status"></div>

<div id="reply-preview">
    <div style="border-right: 4px solid #00a884; padding-right: 10px;">
        <div style="font-size:12px; color:#00a884; font-weight:bold;">پاسخ به:</div>
        <div id="reply-text" style="font-size:13px; color:#54656f;"></div>
    </div>
    <span onpointerdown="event.preventDefault();" onclick="cancelReply(true)" style="cursor:pointer; font-size:20px; color:#54656f;">✕</span>
</div>
<div id="edit-preview">
    <div style="border-right: 4px solid #ff9800; padding-right: 10px;">
        <div style="font-size:12px; color:#ff9800; font-weight:bold;">در حال ویرایش:</div>
        <div id="edit-text" style="font-size:13px; color:#54656f;"></div>
    </div>
    <span onpointerdown="event.preventDefault();" onclick="cancelEdit(true)" style="cursor:pointer; font-size:20px; color:#54656f;">✕</span>
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
    <textarea id="msgInput" placeholder="پیام بنویسید..." rows="1" oninput="autoGrow(this)"></textarea>
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
<div id="reaction-menu" class="reaction-menu">
    <span class="reaction-emoji" onclick="selectReaction('❤️')">❤️</span>
    <span class="reaction-emoji" onclick="selectReaction('👍')">👍</span>
    <span class="reaction-emoji" onclick="selectReaction('😂')">😂</span>
    <span class="reaction-emoji" onclick="selectReaction('😮')">😮</span>
    <span class="reaction-emoji" onclick="selectReaction('😢')">😢</span>
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
            document.getElementById('chat-box').addEventListener('touchend', function(e) {
                if (!inputHadFocus) return;
                const t = e.target;
                if (t === msgInput || t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT') return;
                if (t.closest('.msg-actions') || t.closest('.reaction-menu') || t.tagName === 'BUTTON' || t.tagName === 'A') return;
                // بازگرداندن فوکوس بدون اسکرول
                setTimeout(function() { msgInput.focus({ preventScroll: true }); }, 50);
            }, { passive: true });
        }
    });

    let myId = "ME";
    let CHAT_KEY = "";
    let lastTime = 0;
    let replyingTo = null;
    let editingTo = null;
    let autoScroll = true;
    let unreadCount = 0;
    let hasFetchedOnce = false;
    const APP_TITLE = "این‌چت";
    let mobileKeyboardWasOpen = false;

    // ── تنظیم نمایش دکمه‌های ویس و ویدیومسیج ──────────────────────────
    const SHOW_MEDIA_BUTTONS = false;  // false = مخفی | true = نمایش

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
        el.style.height = '40px';
        el.style.height = (el.scrollHeight) + 'px';
    }

    async function fetchMessages() {
        try {
            await initCrypto();
            const res = await fetch(`/get_messages?since=${lastTime}`);
            const d = await res.json();
            myId = d.me;
            const sb = document.getElementById('status-bar');
            sb.innerHTML = d.other_online === "Online" ? '<b style="color:#1df0bc">● آنلاین</b>' : "آخرین بازدید: " + d.other_online;
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
        if(m.deleted) { if(old) old.remove(); return; }

        const div = old || document.createElement('div');
        div.id = 'msg-' + m.id;
        div.className = 'msg ' + (m.sender_id === myId ? 'sent' : 'received');

        if (old && (m.type === 'voice' || m.type === 'image' || m.type === 'video_note' || m.type === 'file')) {
            var liteReplyText = m.reply_text ? await dec(m.reply_text) : '';
            var liteReply = m.reply_id ? `<div class="reply-area" onclick="scrollToMsg('${m.reply_id}')">${liteReplyText}</div>` : '';
            var liteReact = m.react ? `<div class="reaction">${m.react}</div>` : '';
            var liteSeen = (m.sender_id === myId && m.seen) ? '<span class="seen-status">✓✓</span>' : (m.sender_id === myId ? '✓' : '');
            var liteEditedIcon = m.edited ? '<span style="font-size:9px; opacity:0.7; margin-right:4px;">✏️</span>' : '';
            var liteFooter = `<div class="footer-info">${liteEditedIcon}<span>${m.time}</span> ${liteSeen}</div>`;
            var liteReplyLabel = m.type === 'image' ? 'تصویر' : (m.type === 'video_note' ? 'پیام ویدیویی' : (m.type === 'file' ? 'فایل' : 'پیام صوتی'));
            var liteActions = `<div class="msg-actions">
                ${m.sender_id === myId ? `<span onpointerdown="event.preventDefault();" onclick="deleteMsg('${m.id}')">حذف</span>` : ''}
                ${m.sender_id === myId && m.type !== 'image' && m.type !== 'voice' && m.type !== 'video_note' && m.type !== 'file' ? `<span onpointerdown="event.preventDefault();" onclick="editMsg('${m.id}', ${m.edited ? 'true' : 'false'})">ویرایش</span>` : ''}
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
            return;
        }
        
        let longPressHappened = false;
        if (m.sender_id !== myId) {
            div.onclick = (e) => {
                // جلوگیری از باز شدن منو روی لینک، عکس، اکشن‌ها یا reply-area
                if (e.target.tagName === 'A' || e.target.tagName === 'IMG' || e.target.closest('.msg-actions') || e.target.closest('.reply-area') || e.target.closest('.voice-player') || e.target.closest('.video-note') || e.target.closest('.file-card')) {
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
        } else if (m.type !== 'video_note' && m.type !== 'voice' && m.type !== 'file') {
            decryptedData = await dec(m.data);
        }
        
        div.addEventListener('touchstart', (e) => {
            if (e.target && (e.target.closest('img'))) return;
            if (m.type === 'image' || m.type === 'voice' || m.type === 'video_note' || m.type === 'file') return;
            longPressHappened = false;
            pressTimer = setTimeout(async () => {
                longPressHappened = true;
                try {
                    if (navigator.clipboard && window.isSecureContext) {
                        await navigator.clipboard.writeText(decryptedData);
                    } else {
                        const ta = document.createElement('textarea');
                        ta.value = decryptedData;
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

        let content = decryptedData;
        let replyText = m.reply_text ? await dec(m.reply_text) : '';
        let reply = m.reply_id ? `<div class="reply-area" onclick="scrollToMsg('${m.reply_id}')">${replyText}</div>` : '';
        let react = m.react ? `<div class="reaction">${m.react}</div>` : '';
        let seen = (m.sender_id === myId && m.seen) ? '<span class="seen-status">✓✓</span>' : (m.sender_id === myId ? '✓' : '');
        
        let actions = `<div class="msg-actions">
            ${m.sender_id === myId ? `<span onpointerdown="event.preventDefault();" onclick="deleteMsg('${m.id}')">حذف</span>` : ''}
            ${m.sender_id === myId && m.type !== 'image' && m.type !== 'voice' && m.type !== 'video_note' && m.type !== 'file' ? `<span onpointerdown="event.preventDefault();" onclick="editMsg('${m.id}', ${m.edited ? 'true' : 'false'})">ویرایش</span>` : ''}
            <span onpointerdown="event.preventDefault();" onclick="setReply('${m.id}', '${m.type === 'image' ? 'تصویر' : m.type === 'voice' ? 'پیام صوتی' : m.type === 'video_note' ? 'پیام ویدیویی' : m.type === 'file' ? 'فایل' : content.replace(/'/g, "\\'").replace(/\n/g, ' ').replace(/\s+/g, ' ').trim().substring(0,100)}')">پاسخ</span>
        </div>`;

        let body;
        if (m.type === 'image') {
            body = `<img src="${content}" style="max-width:100%; border-radius:12px;">`;
        } else if (m.type === 'voice') {
            body = createVoicePlayer(voiceMeta || { legacySrc: content }, m.id);
        } else if (m.type === 'video_note') {
            body = createVideoNotePlayer(videoMeta, m.id);
        } else if (m.type === 'file') {
            body = createFileAttachment(fileMeta, m.id);
        } else {
            body = `<div>${linkify(content)}</div>`;
        }

        let editedIcon = m.edited ? '<span style="font-size:9px; opacity:0.7; margin-right:4px;">✏️</span>' : '';
        div.innerHTML = `${reply} ${body} ${react} <div class="footer-info">${editedIcon}<span>${m.time}</span> ${seen}</div> ${actions}`;
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
        document.getElementById('msgInput').focus();
    }

    function cancelReply(keepFocus=false) {
        replyingTo = null;
        document.getElementById('reply-preview').style.display = 'none';
        if (keepFocus) document.getElementById('msgInput').focus({preventScroll:true});
    }

    function cancelEdit(keepFocus=false) {
        if (!editingTo) {
            if (keepFocus) document.getElementById('msgInput').focus({preventScroll:true});
            return;
        }
        editingTo = null;
        document.getElementById('edit-preview').style.display = 'none';
        const i = document.getElementById('msgInput');
        i.value = '';
        i.style.height = '40px';
        i.placeholder = 'پیام بنویسید...';
        if (keepFocus) i.focus({preventScroll:true});
    }

    async function sendTxt() {
        let i = document.getElementById('msgInput');
        if(!i.value.trim()) return;
        
        if (editingTo) {
            const encData = await enc(i.value.trim());
            postAction('/edit_message', {
                id: editingTo.id,
                data: encData
            });
            i.value = '';
            i.style.height = '40px';
            i.placeholder = 'پیام بنویسید...';
            cancelEdit();
        } else {
            const encData = await enc(i.value);
            const encReplyText = replyingTo ? await enc(replyingTo.text) : null;
            postAction('/send_message', {
                type:'text', data: encData,
                reply_id: replyingTo ? replyingTo.id : null,
                reply_text: encReplyText
            });
            i.value = '';
            i.style.height = '40px';
            cancelReply();
            setTimeout(() => scrollToBottom(), 100);
        }
    }

    async function sendImg(input) {
        const file = input.files[0];
        if (!file) return;

        const img = new Image();
        img.onload = async () => {
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

            input.value = "";
            setTimeout(() => scrollToBottom(), 100);
        };

        img.src = URL.createObjectURL(file);
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

        try {
            if (file.type && file.type.startsWith('image/')) {
                await sendImg(input);
                return;
            }

            if (file.size > 100 * 1024 * 1024) {
                alert('حجم فایل بیش از حد مجاز است (حداکثر 100 مگابایت)');
                return;
            }

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

            cancelReply();
            fetchMessages();
            setTimeout(() => scrollToBottom(), 100);
        } catch (error) {
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

    async function toggleRecording() {
        if (mediaRecorder && mediaRecorder.state === 'recording') {
            mediaRecorder.stop();
        } else {
            try {
                const stream = await navigator.mediaDevices.getUserMedia({
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
                mediaRecorder = new MediaRecorder(stream, options);
                audioChunks = [];
                mediaRecorder.ondataavailable = (e) => {
                    if (e.data.size > 0) audioChunks.push(e.data);
                };
                mediaRecorder.onstop = () => {
                    stream.getTracks().forEach(t => t.stop());
                    recordedBlob = new Blob(audioChunks, { type: mediaRecorder.mimeType || 'audio/webm' });
                    document.getElementById('mic-btn').classList.remove('recording');
                };
                mediaRecorder.start(1000);
                recordingStartTime = Date.now();
                document.getElementById('mic-btn').classList.add('recording');
                document.getElementById('recording-ui').classList.add('show');
                updateRecordingTime();
            } catch(e) {
                console.error('Microphone access denied:', e);
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
            };
            videoRecorder.start(250);
            document.getElementById('video-note-ui').classList.add('show');
        } catch (error) {
            console.error('Camera access denied:', error);
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
            videoRecorder.stop();
            await new Promise(resolve => setTimeout(resolve, 350));
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
        if (mediaRecorder && mediaRecorder.state === 'recording') {
            mediaRecorder.stop();
        }
        if (recordingTimer) clearTimeout(recordingTimer);
        document.getElementById('recording-ui').classList.remove('show');
        document.getElementById('mic-btn').classList.remove('recording');
        recordedBlob = null;
        audioChunks = [];
    }

    async function sendRecording() {
        if (mediaRecorder && mediaRecorder.state === 'recording') {
            mediaRecorder.stop();
            await new Promise(r => setTimeout(r, 300));
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

    function setupVoiceAudio(msgId, audio) {
        function updateDuration() {
            const dur = audio.duration;
            if (dur && isFinite(dur) && !isNaN(dur)) {
                const durSec = Math.floor(dur);
                const mins = Math.floor(durSec / 60);
                const secs = durSec % 60;
                const el = document.getElementById('vtime-' + msgId);
                if (el) el.textContent = `${mins}:${secs.toString().padStart(2, '0')}`;
            }
        }
        audio.onloadedmetadata = updateDuration;
        audio.ondurationchange = updateDuration;
        audio.oncanplaythrough = updateDuration;
        audio.ontimeupdate = () => updateVoiceProgress(msgId);
        audio.onended = () => {
            const player = document.querySelector(`.voice-player[data-msg="${msgId}"]`);
            if (player) {
                player.querySelector('.play-icon').style.display = 'block';
                player.querySelector('.pause-icon').style.display = 'none';
                player.querySelectorAll('.voice-bar').forEach(b => b.classList.remove('played'));
            }
            audio.currentTime = 0;
            const dur = audio.duration;
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
            <div class="file-card" onclick="downloadAttachment('${msgId}', '${fileName}', '${mime}', '${downloadName}')">
                <div class="file-card-icon">${emoji}</div>
                <div class="file-card-body">
                    <div class="file-card-name">${name}</div>
                    <div class="file-card-meta">${sizeLabel}</div>
                    <div class="file-card-action">دانلود فایل</div>
                </div>
            </div>
        `;
    }

    async function downloadAttachment(msgId, fileName, mime, fileDisplayName) {
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
                video.src = blobUrl;

                // ✅ صبر کن تا ویدیو واقعاً آماده پخش بشه
                await new Promise((resolve, reject) => {
                    video.oncanplay = resolve;
                    video.onerror = reject;
                    video.load(); // ← force load
                });

            } catch (error) {
                console.error('Video note decrypt failed:', error);
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
            audio.play();
            const pi = player.querySelector('.play-icon');
            const pai = player.querySelector('.pause-icon');
            if (pi) pi.style.display = 'none';
            if (pai) pai.style.display = 'block';
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
        const duration = audio.duration;
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
        if (!audio || !audio.duration) return;
        const waveform = event.currentTarget;
        const rect = waveform.getBoundingClientRect();
        const x = event.clientX - rect.left;
        const progress = Math.max(0, Math.min(1, x / rect.width));
        audio.currentTime = progress * audio.duration;
    }

    async function postAction(path, p) {
        try {
            await fetch(path, {method:'POST', body: JSON.stringify({...p})});
            fetchMessages();
        } catch(e) {
            console.error('Post error:', e);
        }
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
        
        const bodyDiv = msgEl.querySelector('div:not(.reply-area):not(.reaction):not(.footer-info):not(.msg-actions)');
        if (!bodyDiv) return;
        
        if (bodyDiv.tagName === 'IMG') return;
        
        function extractTextWithBreaks(node) {
            let text = '';
            for (let child of node.childNodes) {
                if (child.nodeType === Node.TEXT_NODE) {
                    text += child.textContent;
                } else if (child.nodeType === Node.ELEMENT_NODE) {
                    if (child.tagName === 'BR' || child.tagName === 'br') {
                        text += '\n';
                    } else if (child.tagName === 'A' || child.tagName === 'a') {
                        text += extractTextWithBreaks(child);
                    } else {
                        text += extractTextWithBreaks(child);
                    }
                }
            }
            return text;
        }
        
        let currentText = extractTextWithBreaks(bodyDiv);
        
        editingTo = {id: id, originalText: currentText};
        
        const ep = document.getElementById('edit-preview');
        ep.style.display = 'flex';
        
        const singleLineText = currentText.replace(/\n/g, ' ').replace(/\s+/g, ' ').trim();
        const previewText = singleLineText.length > 50 ? singleLineText.substring(0, 50) + '...' : singleLineText;
        document.getElementById('edit-text').innerText = previewText;
        
        const i = document.getElementById('msgInput');
        i.value = currentText;
        i.placeholder = 'پیام را ویرایش کنید...';
        autoGrow(i);
        
        cancelReply();
        i.focus();
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
    document.getElementById('msgInput').oninput = (e) => {
        autoGrow(e.target);
        const now = Date.now();
        if (now - lastTypingSent > 800) {
            lastTypingSent = now;
            fetch('/typing', {method:'POST', body: JSON.stringify({u_id: myId})});
        }
    };

    const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);

    if (isMobile) {
        document.getElementById('msgInput').addEventListener('keydown', function(e) {
            if (e.key === 'Enter') {
                return;
            }
        });
    } else {
        document.getElementById('msgInput').addEventListener('keydown', function(e) {
            if (e.key === 'Enter') {
                if (e.shiftKey) {
                    return;
                } else {
                    e.preventDefault();
                    sendTxt();
                }
            }
        });
    }

</script>
</body>
</html>
"""


# --- Thread های پاک‌سازی ---
def clean_typing():
    """پاک‌سازی وضعیت تایپ کاربران"""
    while True:
        time.sleep(2)
        now = time.time()
        with LOCKED:
            to_del = [u for u, t in TYPING_USERS.items() if now - t > 3]
            for u in to_del:
                del TYPING_USERS[u]


def cleanup_data():
    """پاک‌سازی دوره‌ای پیام‌های قدیمی"""
    while True:
        time.sleep(300)  # هر 5 دقیقه
        try:
            cleanup_old_messages()
            
            # بازسازی حافظه
            with LOCKED:
                MESSAGES.clear()
            load_messages_to_memory()
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
        """دریافت شناسه کاربر از کوکی"""
        cookies = parse_cookies(self.headers.get("Cookie", ""))
        return cookies.get("chat_user")

    def do_GET(self):
        try:
            u = urllib.parse.urlparse(self.path)
            
            if u.path == '/':
                user_id = self.get_user_from_cookie()
                html = CHAT_PAGE if user_id in ("USER_A", "USER_B") else LOGIN_PAGE
                self.send_html_response(html)

            elif u.path == '/get_messages':
                self.handle_get_messages(u.query)
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
        """ارسال فایل‌های رمزنگاری‌شده رسانه (ویس/ویدیو)"""
        uid = self.get_user_from_cookie()
        if uid not in ("USER_A", "USER_B"):
            self.send_response(401)
            self.end_headers()
            return
        file_name = path.replace('/media/', '', 1)
        if not file_name or '/' in file_name or '\\' in file_name:
            self.send_response(400)
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
        """پردازش درخواست دریافت پیام‌ها"""
        uid = self.get_user_from_cookie()
        
        if uid not in ("USER_A", "USER_B"):
            self.send_json_response({"error": "unauthorized"}, 401)
            return
        
        p = urllib.parse.parse_qs(query)
        since = float(p.get('since', [0])[0])
        
        need_save = False
        news = []
        other_online = "Offline"
        
        with LOCKED:
            LAST_SEEN[uid] = time.time()
            
            # به‌روزرسانی seen برای پیام‌های جدید
            for m in MESSAGES:
                if m['sender_id'] != uid and not m.get('seen'):
                    m['seen'] = True
                    m['updated'] = time.time()
                    need_save = True
                    # به‌روزرسانی در دیتابیس
                    update_message_in_db(m['id'], {'seen': 1, 'updated': m['updated']})
            
            # فیلتر پیام‌های جدید؛ برای به‌روزرسانی‌های سبک (مثلاً seen) دادهٔ حجیم ویس/عکس را نفرست
            news = []
            for m in MESSAGES:
                if m['timestamp'] > since or (m.get('updated') or 0) > since:
                    msg_dict = dict(m)
                    if m['timestamp'] <= since and m.get('type') in ('voice', 'image', 'video_note', 'file'):
                        msg_dict.pop('data', None)
                    news.append(msg_dict)
            
            # وضعیت آنلاین طرف مقابل
            other_uid = next((k for k in LAST_SEEN if k != uid), None)
            if other_uid:
                diff = time.time() - LAST_SEEN[other_uid]
                other_online = "Online" if diff < 10 else (datetime.now() - timedelta(seconds=diff) + timedelta(hours=3, minutes=30)).strftime("%H:%M")
            
            is_typing = any(k != uid for k in TYPING_USERS.keys())
        
        self.send_json_response({
            "me": uid,
            "messages": news,
            "is_typing": is_typing,
            "other_online": other_online
        })

    def do_POST(self):
        try:
            content_length = int(self.headers.get('Content-Length', 0))
            raw_bytes = self.rfile.read(content_length)
            parsed_url = urllib.parse.urlparse(self.path)

            if parsed_url.path == '/upload_video_note':
                uid = self.get_user_from_cookie()
                if uid not in ("USER_A", "USER_B"):
                    self.send_response(401)
                    self.end_headers()
                    return
                self.handle_upload_video_note(uid, raw_bytes, parsed_url.query)
                return
            if parsed_url.path == '/upload_voice':
                uid = self.get_user_from_cookie()
                if uid not in ("USER_A", "USER_B"):
                    self.send_response(401)
                    self.end_headers()
                    return
                self.handle_upload_voice(uid, raw_bytes, parsed_url.query)
                return
            if parsed_url.path == '/upload_file':
                uid = self.get_user_from_cookie()
                if uid not in ("USER_A", "USER_B"):
                    self.send_response(401)
                    self.end_headers()
                    return
                self.handle_upload_file(uid, raw_bytes, parsed_url.query)
                return
            
            raw = raw_bytes.decode('utf-8')
            
            if parsed_url.path == '/login':
                self.handle_login(raw)
                return
            
            body = parse_json_safely(raw)
            if not body and parsed_url.path != '/typing':
                self.send_response(400)
                self.end_headers()
                return
            
            uid = self.get_user_from_cookie()
            if uid not in ("USER_A", "USER_B"):
                self.send_response(401)
                self.end_headers()
                return
            
            body['u_id'] = uid
            body['sender_id'] = uid
            
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
                
        except Exception as e:
            logger.error(f"خطا در POST {self.path}: {e}")
            self.send_response(500)
            self.end_headers()

    def handle_login(self, raw):
        """پردازش ورود کاربر"""
        parsed = urllib.parse.parse_qs(raw)
        p = parsed.get("p", [""])[0]
        
        user_id = PASSWORD_TO_USER.get(p)
        if user_id:
            logger.info(f"ورود موفق: {user_id}")
            self.send_response(303)
            self.send_header("Set-Cookie", f"chat_user={user_id}; Path=/; SameSite=Lax; HttpOnly")
            self.send_header("Location", "/")
            self.end_headers()
        else:
            logger.warning(f"تلاش ورود ناموفق")
            self.send_response(303)
            self.send_header("Location", "/")
            self.end_headers()

    def handle_upload_video_note(self, uid, encrypted_bytes, query):
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

        file_id = hashlib.sha256(f"{uid}:{time.time()}:{len(encrypted_bytes)}".encode('utf-8')).hexdigest()[:24]
        file_name = f"{file_id}.bin"
        file_path = os.path.join(MEDIA_DIR, file_name)

        try:
            with open(file_path, 'wb') as media_file:
                media_file.write(encrypted_bytes)
        except Exception as e:
            logger.error(f"خطا در ذخیره پیام ویدیویی: {e}")
            self.send_json_response({"error": "video_save_failed"}, 500)
            return

        message = {
            'id': str(time.time()),
            'sender_id': uid,
            'type': 'video_note',
            'data': json.dumps({'kind': 'video_note', 'file': file_name, 'mime': mime_type}, ensure_ascii=False),
            'timestamp': time.time(),
            'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"),
            'seen': False,
            'react': None,
            'reply_id': self.headers.get('X-Reply-Id') or None,
            'reply_text': self.headers.get('X-Reply-Text') or None,
            'deleted': False,
            'edited': False,
            'updated': None
        }

        with LOCKED:
            MESSAGES.append(message)
        save_message_to_db(message)

        self.send_json_response({"ok": True, "id": message['id']}, 200)

    def handle_upload_voice(self, uid, encrypted_bytes, query):
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

        file_id = hashlib.sha256(f"{uid}:{time.time()}:{len(encrypted_bytes)}".encode('utf-8')).hexdigest()[:24]
        file_name = f"{file_id}.bin"
        file_path = os.path.join(MEDIA_DIR, file_name)

        try:
            with open(file_path, 'wb') as media_file:
                media_file.write(encrypted_bytes)
        except Exception as e:
            logger.error(f"خطا در ذخیره پیام صوتی: {e}")
            self.send_json_response({"error": "voice_save_failed"}, 500)
            return

        message = {
            'id': str(time.time()),
            'sender_id': uid,
            'type': 'voice',
            'data': json.dumps({'kind': 'voice', 'file': file_name, 'mime': mime_type}, ensure_ascii=False),
            'timestamp': time.time(),
            'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"),
            'seen': False,
            'react': None,
            'reply_id': self.headers.get('X-Reply-Id') or None,
            'reply_text': self.headers.get('X-Reply-Text') or None,
            'deleted': False,
            'edited': False,
            'updated': None
        }

        with LOCKED:
            MESSAGES.append(message)
        save_message_to_db(message)

        self.send_json_response({"ok": True, "id": message['id']}, 200)

    def handle_upload_file(self, uid, encrypted_bytes, query):
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

        file_id = hashlib.sha256(f"{uid}:{time.time()}:{len(encrypted_bytes)}:{original_name}".encode('utf-8')).hexdigest()[:24]
        file_name = f"{file_id}.bin"
        file_path = os.path.join(MEDIA_DIR, file_name)

        try:
            with open(file_path, 'wb') as media_file:
                media_file.write(encrypted_bytes)
        except Exception as e:
            logger.error(f"خطا در ذخیره فایل: {e}")
            self.send_json_response({"error": "file_save_failed"}, 500)
            return

        message = {
            'id': str(time.time()),
            'sender_id': uid,
            'type': 'file',
            'data': json.dumps({
                'kind': 'file',
                'file': file_name,
                'mime': mime_type,
                'name': original_name,
                'size': file_size
            }, ensure_ascii=False),
            'timestamp': time.time(),
            'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"),
            'seen': False,
            'react': None,
            'reply_id': self.headers.get('X-Reply-Id') or None,
            'reply_text': self.headers.get('X-Reply-Text') or None,
            'deleted': False,
            'edited': False,
            'updated': None
        }

        with LOCKED:
            MESSAGES.append(message)
        save_message_to_db(message)

        self.send_json_response({"ok": True, "id": message['id']}, 200)

    def handle_send_message(self, body):
        """پردازش ارسال پیام"""
        message = {
            'id': str(time.time()),
            'sender_id': body['sender_id'],
            'type': body.get('type', 'text'),
            'data': body.get('data'),
            'timestamp': time.time(),
            'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"),
            'seen': False,
            'react': None,
            'reply_id': body.get('reply_id'),
            'reply_text': body.get('reply_text'),
            'deleted': False,
            'edited': False,
            'updated': None
        }
        
        with LOCKED:
            MESSAGES.append(message)
        
        save_message_to_db(message)
        logger.debug(f"پیام جدید از {body['sender_id']}")

    def handle_delete_message(self, body):
        """پردازش حذف پیام"""
        with LOCKED:
            for m in MESSAGES:
                if m['id'] == body['id'] and m['sender_id'] == body['u_id']:
                    delete_media_file(m)
                    m['deleted'] = True
                    m['data'] = "-"
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {
                        'deleted': 1,
                        'data': '-',
                        'updated': m['updated']
                    })
                    logger.debug(f"پیام حذف شد: {body['id']}")
                    break

    def handle_react_message(self, body):
        """پردازش واکنش به پیام"""
        with LOCKED:
            for m in MESSAGES:
                if m['id'] == body['id']:
                    if m['sender_id'] == body['u_id']:
                        break
                    
                    react_emoji = body.get('react')
                    if m.get('react') == react_emoji:
                        m['react'] = None
                    else:
                        m['react'] = react_emoji
                    
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {
                        'react': m['react'],
                        'updated': m['updated']
                    })
                    break

    def handle_edit_message(self, body):
        """پردازش ویرایش پیام"""
        with LOCKED:
            for m in MESSAGES:
                if m['id'] == body['id'] and m['sender_id'] == body['u_id']:
                    if m.get('type') in ('image', 'voice', 'video_note', 'file'):
                        break
                    
                    m['data'] = body['data']
                    m['edited'] = True
                    m['updated'] = time.time()
                    update_message_in_db(m['id'], {
                        'data': m['data'],
                        'edited': 1,
                        'updated': m['updated']
                    })
                    logger.debug(f"پیام ویرایش شد: {body['id']}")
                    break

    def handle_typing(self, body):
        """پردازش وضعیت تایپ"""
        with LOCKED:
            TYPING_USERS[body['u_id']] = time.time()


class ThreadingHTTPServer(socketserver.ThreadingMixIn, socketserver.TCPServer):
    daemon_threads = True
    allow_reuse_address = True


if __name__ == "__main__":
    # مقداردهی اولیه دیتابیس
    ensure_media_dir()
    init_database()
    load_messages_to_memory()
    
    # شروع thread های پاک‌سازی
    threading.Thread(target=clean_typing, daemon=True).start()
    threading.Thread(target=cleanup_data, daemon=True).start()
    
    # شروع سرور
    with ThreadingHTTPServer(("0.0.0.0", PORT), ChatHandler) as httpd:
        logger.info(f"سرور چت در پورت {PORT} شروع به کار کرد...")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            logger.info("سرور متوقف شد")
