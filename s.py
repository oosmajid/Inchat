import http.server

import socketserver

import json

import urllib.parse

import threading

import time

from datetime import datetime, timedelta



# --- تنظیمات ---

PORT = 2026

PASSWORD = "9604"

MESSAGES = [] 

TYPING_USERS = {} # برای ذخیره زمان آخرین تایپ هر کاربر

MAX_MESSAGES = 1000

LOCKED = threading.Lock()

AUTH_IPS = set()



# --- حذف خودکار دیتای مدیا و پاکسازی وضعیت تایپ ---

def cleanup_data():

    while True:

        time.sleep(5)

        now = time.time()

        with LOCKED:

            # پاکسازی مدیا

            for m in MESSAGES:

                if m['type'] in ['image', 'audio'] and (now - m['timestamp'] > 300):

                    m['data'] = None 

            

            # پاکسازی وضعیت تایپ (اگر بیش از 3 ثانیه از آخرین فعالیت گذشت)

            to_remove = [uid for uid, t in TYPING_USERS.items() if now - t > 3]

            for uid in to_remove:

                del TYPING_USERS[uid]



threading.Thread(target=cleanup_data, daemon=True).start()



# --- صفحه لاگین ---

LOGIN_PAGE = """

<!DOCTYPE html>

<html lang="fa" dir="rtl">

<head>

    <meta charset="UTF-8">

    <meta name="viewport" content="width=device-width, initial-scale=1.0">

    <title>ورود ایمن به این‌چت</title>

    <style>

        body { font-family: Tahoma, sans-serif; background: linear-gradient(135deg, #075e54 0%, #128c7e 100%); display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; }

        .login-card { background: white; padding: 40px 30px; border-radius: 30px; box-shadow: 0 15px 35px rgba(0,0,0,0.2); text-align: center; width: 90%; max-width: 380px; }

        h2 { color: #333; margin-bottom: 25px; font-size: 22px; }

        input { width: 100%; padding: 15px; margin-bottom: 20px; border: 1px solid #eee; border-radius: 15px; background: #f9f9f9; text-align: center; outline: none; }

        button { width: 100%; background: #128c7e; color: white; border: none; padding: 15px; border-radius: 15px; font-weight: bold; cursor: pointer; }

    </style>

</head>

<body>

    <div class="login-card">

        <h2>ورود به این‌چت</h2>

        <form method="POST" action="/login">

            <input type="password" name="p" placeholder="رمز عبور را وارد کنید" required>

            <button type="submit">تایید هویت</button>

        </form>

    </div>

</body>

</html>

"""



# --- صفحه اصلی چت ---

CHAT_PAGE = """

<!DOCTYPE html>

<html lang="fa" dir="rtl">

<head>

    <meta charset="UTF-8">

    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">

    <title>این‌چت</title>

    <style>

        * { box-sizing: border-box; }

        body { font-family: Tahoma, sans-serif; background: #e5ddd5; margin: 0; height: 100vh; display: flex; flex-direction: column; }

        #header { background: #075e54; color: white; padding: 15px; text-align: center; font-weight: bold; }

        #chat-box { flex: 1; overflow-y: auto; padding: 15px; display: flex; flex-direction: column; gap: 12px; }

        .msg { max-width: 85%; padding: 10px; border-radius: 15px; font-size: 15px; position: relative; line-height: 1.5; }

        .sent { background: white; align-self: flex-start; border-top-left-radius: 2px; box-shadow: 1px 1px 2px rgba(0,0,0,0.1); }

        .received { background: #dcf8c6; align-self: flex-end; border-top-right-radius: 2px; box-shadow: -1px 1px 2px rgba(0,0,0,0.1); }

        .reply-area { background: rgba(0,0,0,0.06); padding: 5px 8px; border-right: 3px solid #075e54; font-size: 12px; margin-bottom: 8px; border-radius: 5px; color: #555; }

        .media-content { max-width: 100%; border-radius: 10px; margin-top: 5px; cursor: pointer; }

        .footer-msg { display: flex; justify-content: space-between; align-items: center; margin-top: 5px; }

        .time { font-size: 10px; color: #888; }

        .reply-btn { color: #075e54; font-size: 11px; border: none; background: none; cursor: pointer; font-weight: bold; }

        #typing-status { padding: 5px 20px; font-size: 12px; color: #075e54; height: 20px; font-style: italic; }

        #reply-preview { display: none; background: #f7f7f7; padding: 10px 20px; border-top: 1px solid #ddd; justify-content: space-between; align-items: center; }

        #input-area { background: #f0f0f0; padding: 10px; display: flex; gap: 10px; align-items: center; border-top: 1px solid #ddd; }

        #msgInput { flex: 1; border: none; padding: 12px 18px; border-radius: 25px; outline: none; font-size: 16px; background: white; }

        .circle-btn { background: #075e54; color: white; border: none; width: 45px; height: 45px; border-radius: 50%; cursor: pointer; font-size: 20px; display: flex; align-items: center; justify-content: center; flex-shrink: 0; }

    </style>

</head>

<body>

    <div id="header">این‌چت</div>

    <div id="chat-box"></div>

    <div id="typing-status"></div>

    

    <div id="reply-preview">

        <div style="border-right: 3px solid #075e54; padding-right: 10px;">

            <div style="font-size: 11px; color: #075e54; font-weight: bold;">پاسخ به:</div>

            <div id="reply-text" style="font-size: 13px; color: #666;"></div>

        </div>

        <button onclick="cancelReply()" style="border:none; background:none; font-size:20px; color:#888;">✕</button>

    </div>



    <div id="input-area">

        <button class="circle-btn" onclick="document.getElementById('fileInput').click()">📷</button>

        <input type="file" id="fileInput" hidden accept="image/*" onchange="confirmImage(this)">

        <input type="text" id="msgInput" placeholder="پیام شما..." autocomplete="off">

        <button class="circle-btn" onclick="sendText()">🚀</button>

    </div>



<script>

    let myId = localStorage.getItem('u_id') || Math.random().toString(36).substring(7);

    localStorage.setItem('u_id', myId);



    let lastTime = 0;

    let replyingTo = null;



    function playSoftDing() {

        try {

            const ctx = new (window.AudioContext || window.webkitAudioContext)();

            const osc = ctx.createOscillator();

            const gain = ctx.createGain();

            osc.connect(gain); gain.connect(ctx.destination);

            osc.type = 'sine';

            osc.frequency.setValueAtTime(660, ctx.currentTime);

            gain.gain.setValueAtTime(0, ctx.currentTime);

            gain.gain.linearRampToValueAtTime(0.2, ctx.currentTime + 0.05);

            gain.gain.exponentialRampToValueAtTime(0.0001, ctx.currentTime + 0.5);

            osc.start(); osc.stop(ctx.currentTime + 0.6);

        } catch(e) {}

    }



    async function fetchMessages() {

        try {

            const res = await fetch(`/get_messages?since=${lastTime}&u_id=${myId}`);

            const data = await res.json();

            

            // نمایش وضعیت تایپ

            const typingDiv = document.getElementById('typing-status');

            typingDiv.innerText = data.is_typing ? "طرف مقابل در حال تایپ..." : "";



            const news = data.messages;

            if (news.length > 0) {

                if (lastTime !== 0 && news[news.length-1].sender_id !== myId) playSoftDing();

                news.forEach(m => {

                    if (m.timestamp > lastTime) {

                        render(m);

                        lastTime = m.timestamp;

                    }

                });

                const box = document.getElementById('chat-box');

                box.scrollTop = box.scrollHeight;

            }

        } catch(e) {}

    }



    async function render(m) {

        const box = document.getElementById('chat-box');

        const div = document.createElement('div');

        div.className = 'msg ' + (m.sender_id === myId ? 'sent' : 'received');

        

        // رمزگشایی متن یا تصویر

        let decryptedContent = m.data;

        if (m.iv) {

            decryptedContent = decryptData(m.data, m.iv);

        }



        let content = '';

        if (m.type === 'text') content = `<div>${decryptedContent}</div>`;

        else if (m.type === 'image') {

            content = m.data ? `<img src="${decryptedContent}" class="media-content" onclick="window.open(this.src)">` : `<i style="color:#999">🖼️ منقضی شده</i>`;

        }



        div.innerHTML = `

            ${m.reply_to ? `<div class="reply-area">${m.reply_to}</div>` : ''}

            ${content}

            <div class="footer-msg">

                <button class="reply-btn" onclick="setReply('${m.type=='text' ? decryptedContent : 'تصویر'}')">پاسخ</button>

                <div class="time">${m.time}</div>

            </div>

        `;

        box.appendChild(div);

    }




    // ارسال سیگنال تایپ کردن

    const msgInput = document.getElementById('msgInput');

    msgInput.addEventListener('input', () => {

        fetch('/typing', { method: 'POST', body: JSON.stringify({u_id: myId}) });

    });



    function sendText() {

        if(!msgInput.value.trim()) return;

        post({type: 'text', data: msgInput.value});

        msgInput.value = '';

    }



    function confirmImage(input) {

        if(input.files[0]) {

            if(confirm("آیا مایل به ارسال این تصویر هستید؟")) {

                const r = new FileReader();

                r.onload = e => post({type: 'image', data: e.target.result});

                r.readAsDataURL(input.files[0]);

            }

            input.value = '';

        }

    }



    function setReply(text) {

        replyingTo = text.substring(0, 40);

        document.getElementById('reply-preview').style.display = 'flex';

        document.getElementById('reply-text').innerText = replyingTo + "...";

        msgInput.focus();

    }



    function cancelReply() {

        replyingTo = null;

        document.getElementById('reply-preview').style.display = 'none';

    }




    async function post(payload) {

        // رمزنگاری محتوا قبل از ارسال به سرور

        const encrypted = encryptData(payload.data);

        const securePayload = {

            ...payload,

            data: encrypted.cipher,

            iv: encrypted.iv, // IV برای رمزنگاری لازم است

            sender_id: myId,

            reply_to: replyingTo

        };



        await fetch('/send_message', { method: 'POST', body: JSON.stringify(securePayload) });

        cancelReply();

        fetchMessages();

    }




    // کلید رمزنگاری که فقط در مرورگر می‌ماند

    
    
    let CHAT_KEY = "";



    function saveKeyAndStart() {

        const input = document.getElementById('chatKeyInput');

        if (input.value.trim() === "") {

            alert("لطفا کلید را وارد کنید");

            return;

        }

        CHAT_KEY = input.value;

        document.getElementById('key-overlay').style.display = 'none';

        // شروع به گرفتن پیام‌ها بعد از ورود کلید

        setInterval(fetchMessages, 500);

    }



    // الگوریتم RC4 (بدون نیاز به کتابخانه و کاملا آفلاین)

    function rc4(key, str) {

        var s = [], j = 0, x, res = '';

        for (var i = 0; i < 256; i++) s[i] = i;

        for (i = 0; i < 256; i++) {

            j = (j + s[i] + key.charCodeAt(i % key.length)) % 256;

            x = s[i]; s[i] = s[j]; s[j] = x;

        }

        i = 0; j = 0;

        for (var y = 0; y < str.length; y++) {

            i = (i + 1) % 256;

            j = (j + s[i]) % 256;

            x = s[i]; s[i] = s[j]; s[j] = x;

            res += String.fromCharCode(str.charCodeAt(y) ^ s[(s[i] + s[j]) % 256]);

        }

        return res;

    }



    function encodeUTF8(s) { return unescape(encodeURIComponent(s)); }

    function decodeUTF8(s) { return decodeURIComponent(escape(s)); }



    // توابع رمزنگاری ساده و سریع

    function encryptData(text) {

        const cipher = rc4(CHAT_KEY, encodeUTF8(text));

        return { cipher: btoa(cipher), iv: "off" };

    }



    function decryptData(cipher) {

        try {

            const decoded = atob(cipher);

            const decrypted = rc4(CHAT_KEY, decoded);

            return decodeUTF8(decrypted);

        } catch (e) { return "❌ خطا در رمزگشایی"; }

    }




    msgInput.addEventListener('keypress', e => {if(e.key==='Enter') sendText()});

</script>

</body>

<!-- لایه ورود کلید امنیتی -->

<div id="key-overlay" style="position:fixed; top:0; left:0; width:100%; height:100%; background:#075e54; z-index:9999; display:flex; flex-direction:column; justify-content:center; align-items:center; color:white; font-family:Tahoma, sans-serif;">

    <div style="background:white; padding:30px; border-radius:20px; width:85%; max-width:350px; text-align:center; color:#333; box-shadow:0 10px 25px rgba(0,0,0,0.3);">

        <h3 style="margin-top:0;">🔑 ورود به گفت‌وگو</h3>

        <p style="font-size:13px; color:#666;">کلید محرمانه مشترک را وارد کنید:</p>

        <input type="password" id="chatKeyInput" style="width:100%; padding:12px; border:1px solid #ddd; border-radius:10px; margin-bottom:20px; text-align:center; outline:none;" placeholder="کلید محرمانه">

        <button onclick="saveKeyAndStart()" style="width:100%; background:#128c7e; color:white; border:none; padding:12px; border-radius:10px; font-weight:bold; cursor:pointer;">تایید و ورود</button>

    </div>

</div>


</html>

"""



# --- سرور پایتون ---

class ChatHandler(http.server.BaseHTTPRequestHandler):

    def do_GET(self):

        u = urllib.parse.urlparse(self.path)

        if u.path == '/':

            self.send_response(200); self.end_headers()

            if self.client_address[0] in AUTH_IPS:

                self.wfile.write(CHAT_PAGE.encode('utf-8'))

            else:

                self.wfile.write(LOGIN_PAGE.encode('utf-8'))

        elif u.path == '/get_messages':

            p = urllib.parse.parse_qs(u.query)

            since = float(p.get('since', [0])[0])

            current_uid = p.get('u_id', [''])[0]

            

            self.send_response(200); self.send_header('Content-type', 'application/json'); self.end_headers()

            

            with LOCKED:

                news = [m for m in MESSAGES if m['timestamp'] > since]

                # چک کردن اینکه آیا شخص دیگری جز کاربر فعلی در حال تایپ است؟

                is_typing = any(uid != current_uid for uid in TYPING_USERS.keys())

                

                response = {

                    "messages": news,

                    "is_typing": is_typing

                }

                self.wfile.write(json.dumps(response).encode('utf-8'))



    def do_POST(self):

        content_length = int(self.headers['Content-Length'])

        body = self.rfile.read(content_length).decode('utf-8')

        

        if self.path == '/login':

            if f"p={PASSWORD}" in body:

                AUTH_IPS.add(self.client_address[0])

                self.send_response(303); self.send_header('Location', '/'); self.end_headers()

            else:

                self.send_response(200); self.end_headers(); self.wfile.write(b"Password Incorrect")

        

        elif self.path == '/typing':

            d = json.loads(body)

            with LOCKED:

                TYPING_USERS[d['u_id']] = time.time()

            self.send_response(200); self.end_headers()



        elif self.path == '/send_message':

            d = json.loads(body)

            d['timestamp'] = time.time()

            d['time'] = (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M")


            with LOCKED:

                MESSAGES.append(d)

                if len(MESSAGES) > MAX_MESSAGES: MESSAGES.pop(0)

                # وقتی پیام فرستاد، وضعیت تایپش رو حذف کن

                if d['sender_id'] in TYPING_USERS: del TYPING_USERS[d['sender_id']]

            self.send_response(200); self.end_headers()



class ThreadingHTTPServer(socketserver.ThreadingMixIn, socketserver.TCPServer):

    daemon_threads = True

    allow_reuse_address = True



if __name__ == "__main__":

    with ThreadingHTTPServer(("0.0.0.0", PORT), ChatHandler) as httpd:

        print(f"Server started at port {PORT}")

        httpd.serve_forever()

