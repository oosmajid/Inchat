import http.server, socketserver, json, urllib.parse, threading, time, os

from datetime import datetime, timedelta



# --- تنظیمات سرور ---

PORT = 2026


PASSWORD_TO_USER = {

    "9604": "USER_A",

    "2728": "USER_B",

}


DB_FILE = "chat_history.txt"

MESSAGES = [] 

TYPING_USERS = {}

LAST_SEEN = {} 

LOCKED = threading.Lock()



# --- مدیریت فایل ---

if os.path.exists(DB_FILE):

    with open(DB_FILE, "r", encoding="utf-8") as f:

        for line in f:

            try: MESSAGES.append(json.loads(line))

            except: pass



def save_all():

    with open(DB_FILE, "w", encoding="utf-8") as f:

        for m in MESSAGES: f.write(json.dumps(m) + "\n")



# --- صفحه لاگین ---

LOGIN_PAGE = """

<!DOCTYPE html>

<html lang="fa" dir="rtl">

<head><meta charset="UTF-8"><title>ورود</title>

<style>

    body { font-family: 'Tahoma', sans-serif; background: #eceff1; display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; }

    .card { background: white; padding: 40px; border-radius: 28px; text-align: center; width: 340px; box-shadow: 0 10px 25px rgba(0,0,0,0.1); }

    h2 { color: #263238; margin-bottom: 20px; }

    input { width: 100%; padding: 15px; margin: 15px 0; border-radius: 12px; border: 1px solid #cfd8dc; text-align: center; outline: none; font-size: 16px; }

    button { width: 100%; background: #00796b; color: white; border: none; padding: 15px; border-radius: 12px; cursor: pointer; font-weight: bold; font-size: 16px; transition: 0.3s; }

    button:hover { background: #004d40; }

</style>

</head>

<body>

    <div class="card">

        <h2>ورود به این‌چت</h2>

        <form method="POST" action="/login">

            <input type="password" name="p" placeholder="رمز عبور" required>

            <button type="submit">ورود امن</button>

        </form>

    </div>

</body>

</html>

"""



# --- صفحه چت ---

CHAT_PAGE = """

<!DOCTYPE html>

<html lang="fa" dir="rtl">

<head>

    <meta charset="UTF-8">

    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">

    <title>این‌چت</title>

    <style>

        * { box-sizing: border-box; font-family: 'Segoe UI', Tahoma, sans-serif; }

        body { background: #efe7dd; margin: 0; height: 100vh; height: 100dvh; display: flex; flex-direction: column; overflow: hidden; }

        

        /* Header Material */

        #header { background: #005c4b; color: white; padding: 12px 20px; box-shadow: 0 2px 4px rgba(0,0,0,0.2); z-index: 10; display: flex; flex-direction: column; align-items: center; }

        #header b { font-size: 18px; }

        #status-bar { font-size: 12px; opacity: 0.9; margin-top: 2px; }



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

            

            /* کدهای جدید برای جلوگیری از بیرون زدن متن */

            word-wrap: break-word;      /* برای مرورگرهای قدیمی */

            overflow-wrap: break-word;  /* استاندارد جدید */

            word-break: break-word;     /* شکستن کلمات طولانی */

            user-select: text;          /* اجازه انتخاب متن */

            -webkit-user-select: text;  /* برای آیفون */

        }


        .sent { background: white; align-self: flex-start; border-top-left-radius: 4px; }

        .received { background: #d9fdd3; align-self: flex-end; border-top-right-radius: 4px; }

        .highlight { background: #fff59d !important; }



        /* Reactions */

        .reaction { position: absolute; bottom: -10px; left: 10px; background: white; border-radius: 10px; padding: 2px 4px; font-size: 12px; box-shadow: 0 1px 3px rgba(0,0,0,0.2); }



        .reply-area { background: rgba(0,0,0,0.04); padding: 6px; border-right: 4px solid #00a884; font-size: 11.5px; margin-bottom: 6px; border-radius: 6px; cursor: pointer; color: #54656f; }

        

        .footer-info { display: flex; justify-content: space-between; align-items: center; font-size: 10px; color: #667781; margin-top: 4px; }

        .seen-status { color: #53bdeb; font-weight: bold; margin-right: 4px; }



        .msg-actions { font-size: 10px; margin-top: 6px; display: flex; gap: 12px; color: #00796b; border-top: 1px solid rgba(0,0,0,0.05); padding-top: 4px; }

        .msg-actions span { cursor: pointer; font-weight: 500; }



        #typing-status { height: 20px; font-size: 12px; color: #667781; padding: 0 25px; font-style: italic; }

        

        /* Input Area Material */

        #input-container { background: #f0f2f5; padding: 8px 16px; display: flex; align-items: flex-end; gap: 10px; border-top: 1px solid #d1d7db; }

        

        #msgInput { flex: 1; border: none; padding: 10px 15px; border-radius: 20px; outline: none; font-size: 15px; max-height: 120px; min-height: 40px; resize: none; background: white; line-height: 20px; }

        

        .icon-btn { background: transparent; border: none; cursor: pointer; padding: 8px; border-radius: 50%; display: flex; align-items: center; justify-content: center; transition: 0.2s; }

        .icon-btn:hover { background: rgba(0,0,0,0.05); }

        .icon-btn svg { fill: #54656f; width: 24px; height: 24px; }

        .send-btn svg { fill: #00a884; }



        #reply-preview { display: none; background: #f0f2f5; padding: 10px 20px; border-top: 1px solid #d1d7db; justify-content: space-between; align-items: center; }



        #key-overlay { position: fixed; top:0; left:0; width:100%; height:100%; background:#005c4b; z-index:10000; display:flex; justify-content:center; align-items:center; }


        #new-msg-bubble {

            display: none;

            position: fixed;

            bottom: 85px;

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

        @keyframes fadeIn { from { opacity: 0; bottom: 70px; } to { opacity: 1; bottom: 85px; } }


    </style>

</head>

<body>



<div id="key-overlay">

    <div style="background:white; padding:35px; border-radius:28px; width:340px; text-align:center; box-shadow:0 20px 50px rgba(0,0,0,0.3);">

        <h3 style="margin-top:0; color:#263238;">🔐 بازگشایی گفت‌وگو</h3>

        <input type="password" id="kInp" style="width:100%; padding:15px; margin-bottom:20px; border:1px solid #cfd8dc; border-radius:12px; text-align:center; font-size:18px;" placeholder="کلید محرمانه">

        <button onclick="startChat()" style="width:100%; background:#00a884; color:white; border:none; padding:15px; border-radius:12px; font-weight:bold; cursor:pointer;">تایید</button>

    </div>

</div>



<div id="header">

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

    <span onclick="cancelReply()" style="cursor:pointer; font-size:20px; color:#54656f;">✕</span>

</div>

<div id="new-msg-bubble" onclick="scrollToBottom()">پیام جدید 👇</div>

<div id="input-container">

    <button class="icon-btn send-btn" onclick="sendTxt()">

        <svg viewBox="0 0 24 24"><path d="M2.01 21L23 12 2.01 3 2 10l15 2-15 2z"/></svg>

    </button>

    

    <textarea id="msgInput" placeholder="پیام بنویسید..." rows="1" oninput="autoGrow(this)"></textarea>



    <button class="icon-btn" onclick="document.getElementById('fInp').click()">

        <svg viewBox="0 0 24 24"><path d="M19 7v2.99s-1.99.01-2 0V7h-3s.01-1.99 0-2h3V2h2v3h3v2h-3zm-3 4V8h-3V5H5c-1.1 0-2 .9-2 2v12c0 1.1.9 2 2 2h12c1.1 0 2-.9 2-2v-8h-3zM5 19l3-4 2 3 3-4 4 5H5z"/></svg>

    </button>

    <input type="file" id="fInp" hidden accept="image/*" onchange="sendImg(this)">

</div>



<script>

    let myId = "ME"; // فقط برای تشخیص سمت کلاینت؛ سرور با کوکی تصمیم می‌گیرد

    let CHAT_KEY = "";

    let lastTime = 0;

    let replyingTo = null;

    let autoScroll = true;



    function startChat() {

        let v = document.getElementById('kInp').value;

        if(!v) return;

        CHAT_KEY = v;

        document.getElementById('key-overlay').style.display = 'none';

        setInterval(fetchMessages, 2000);

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



    // --- رمزنگاری ---

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

    function enc(t) { return btoa(rc4(CHAT_KEY, unescape(encodeURIComponent(t)))); }

    function dec(t) { 

        if(!t) return "";

        try { return decodeURIComponent(escape(rc4(CHAT_KEY, atob(t)))); } catch(e) { return "❌"; } 

    }



    function autoGrow(el) {

        el.style.height = '40px';

        el.style.height = (el.scrollHeight) + 'px';

    }



    async function fetchMessages() {

        try {

            const res = await fetch(`/get_messages?since=${lastTime}`);


            const d = await res.json();

            myId = d.me;

            const sb = document.getElementById('status-bar');

            sb.innerHTML = d.other_online === "Online" ? '<b style="color:#1df0bc">● آنلاین</b>' : "آخرین بازدید: " + d.other_online;



            document.getElementById('typing-status').innerText = d.is_typing ? "طرف مقابل در حال نوشتن..." : "";

            

            if(d.messages.length > 0) {

                let hasNew = false;

                 d.messages.forEach(m => {

                    if(m.timestamp > lastTime || m.updated) {

                        // اگر پیام جدید از طرف مقابل بود، بلافاصله متن تایپ را پاک کن

                        if(m.timestamp > lastTime && m.sender_id !== myId) {

                            playDing();

                            document.getElementById('typing-status').innerText = ""; 

                        }

                        render(m);

                        if(m.timestamp > lastTime) { lastTime = m.timestamp; hasNew = true; }

                    }

                });



                if(hasNew) {

                    if(autoScroll) {

                        scrollToBottom();

                    } else {

                        // اگر کاربر بالا بود، دکمه "پیام جدید" را نشان بده

                        document.getElementById('new-msg-bubble').style.display = 'block';

                    }

                }

            }

        } catch(e) {}

    }



    function render(m) {

        const box = document.getElementById('chat-box');

        let old = document.getElementById('msg-' + m.id);

        if(m.deleted) { if(old) old.remove(); return; }



        const div = old || document.createElement('div');

        div.id = 'msg-' + m.id;

        div.className = 'msg ' + (m.sender_id === myId ? 'sent' : 'received');

        div.ondblclick = () => postAction('/react_message', {id: m.id});

        

        let content = dec(m.data);

        let reply = m.reply_id ? `<div class="reply-area" onclick="scrollToMsg('${m.reply_id}')">${dec(m.reply_text)}</div>` : '';

        let react = m.react ? `<div class="reaction">❤️</div>` : '';

        let seen = (m.sender_id === myId && m.seen) ? '<span class="seen-status">✓✓</span>' : (m.sender_id === myId ? '✓' : '');

        

        let actions = `<div class="msg-actions">

            ${m.sender_id === myId ? `<span onclick="deleteMsg('${m.id}')">حذف</span>` : ''}

            <span onclick="setReply('${m.id}', '${m.type === 'image' ? 'تصویر' : content.replace(/'/g, "\\'").substring(0,100)}')">پاسخ</span>


        </div>`;



        let body = m.type === 'image' ? `<img src="${content}" style="max-width:100%; border-radius:12px;">` : `<div>${content}</div>`;

        

        div.innerHTML = `${reply} ${body} ${react} <div class="footer-info"><span>${m.time}</span> ${seen}</div> ${actions}`;

        if(!old) box.appendChild(div);

    }



    function setReply(id, text) {

        replyingTo = {id: id, text: text};

        const rp = document.getElementById('reply-preview');

        rp.style.display = 'flex';

        document.getElementById('reply-text').innerText = text.substring(0, 50);

        document.getElementById('msgInput').focus();

    }

    function cancelReply() { replyingTo = null; document.getElementById('reply-preview').style.display = 'none'; }



    function sendTxt() {

        let i = document.getElementById('msgInput');

        if(!i.value.trim()) return;

        postAction('/send_message', {

            type:'text', data: enc(i.value), 

            reply_id: replyingTo ? replyingTo.id : null,

            reply_text: replyingTo ? enc(replyingTo.text) : null

        });

        i.value = ''; i.style.height = '40px'; cancelReply();

    }



    async function sendImg(input) {

        const file = input.files[0];

        if (!file) return;



        // Resize + compress

        const img = new Image();

        img.onload = async () => {

            const maxW = 1024; // حداکثر عرض

            const scale = Math.min(1, maxW / img.width);

            const w = Math.round(img.width * scale);

            const h = Math.round(img.height * scale);



            const canvas = document.createElement('canvas');

            canvas.width = w; canvas.height = h;

            const ctx = canvas.getContext('2d');

            ctx.drawImage(img, 0, 0, w, h);



            // کیفیت jpg

            const quality = 0.7;

            const dataUrl = canvas.toDataURL('image/jpeg', quality);



            await postAction('/send_message', {

            type: 'image',

            data: enc(dataUrl),

            reply_id: replyingTo ? replyingTo.id : null,

            reply_text: replyingTo ? enc(replyingTo.text) : null

            });



            input.value = "";

        };



        img.src = URL.createObjectURL(file);

    }



    async function postAction(path, p) {

        await fetch(path, {method:'POST', body: JSON.stringify({...p})});

        fetchMessages();

    }



    function scrollToBottom() { const b = document.getElementById('chat-box'); b.scrollTop = b.scrollHeight; }


    function handleScroll() {

        const b = document.getElementById('chat-box');

        // تشخیص اینکه کاربر در انتهای صفحه است یا نه

        autoScroll = (b.scrollHeight - b.scrollTop - b.clientHeight < 100);

        

        // اگر کاربر به پایین رسید، دکمه را مخفی کن

        if (autoScroll) {

            document.getElementById('new-msg-bubble').style.display = 'none';

        }

    }

    function deleteMsg(id) { if(confirm("حذف پیام؟")) postAction('/delete_message', {id: id}); }

    function scrollToMsg(id) {

        const el = document.getElementById('msg-' + id);

        if(el) { el.scrollIntoView({ behavior: 'smooth', block: 'center' }); el.classList.add('highlight'); setTimeout(()=>el.classList.remove('highlight'), 1500); }

    }



    document.getElementById('msgInput').oninput = (e) => {

        autoGrow(e.target);

        fetch('/typing', {method:'POST', body: JSON.stringify({u_id: myId})});

    };

     // اضافه کردن قابلیت ارسال با Enter

    document.getElementById('msgInput').addEventListener('keydown', function(e) {

        if (e.key === 'Enter' && !e.shiftKey) { // ارسال با اینتر و خط جدید با شیفت+اینتر

            e.preventDefault(); // جلوگیری از ایجاد خط جدید در تکست‌اریا

            sendTxt();

        }

    });


</script>

</body>

</html>

"""


def clean_typing():

    while True:

        time.sleep(2)

        now = time.time()

        with LOCKED:

            # حذف کاربرانی که بیش از 3 ثانیه از آخرین سیگنال تایپشان گذشته

            to_del = [u for u, t in TYPING_USERS.items() if now - t > 3]

            for u in to_del: del TYPING_USERS[u]


def cleanup_data():

    while True:

        time.sleep(60) # هر یک دقیقه چک کن

        now = time.time()
        need_save = False
        with LOCKED:
            

            # حذف پیام‌های قدیمی‌تر از ۲۴ ساعت (۸۶۴۰۰ ثانیه)

            original_count = len(MESSAGES)

            # فقط پیام‌هایی که کمتر از ۲۴ ساعت سن دارند را نگه دار

            MESSAGES[:] = [m for m in MESSAGES if now - m['timestamp'] < 86400]

            

            # اگر پیامی حذف شد، فایل را بازنویسی کن

            if len(MESSAGES) != original_count:

                need_save = True
        
        if need_save:

            save_all()

def append_one(m):

    with open(DB_FILE, "a", encoding="utf-8") as f:

        f.write(json.dumps(m) + "\n")





threading.Thread(target=clean_typing, daemon=True).start()
threading.Thread(target=cleanup_data, daemon=True).start()


def parse_cookies(cookie_header: str):

    out = {}

    if not cookie_header:

        return out

    parts = cookie_header.split(";")

    for p in parts:

        if "=" in p:

            k, v = p.strip().split("=", 1)

            out[k] = v

    return out



class ChatHandler(http.server.BaseHTTPRequestHandler):

    def do_GET(self):

        u = urllib.parse.urlparse(self.path)

        
        if u.path == '/':

            cookies = parse_cookies(self.headers.get("Cookie", ""))

            user_id = cookies.get("chat_user")



            self.send_response(200)

            self.send_header("Content-Type", "text/html; charset=utf-8")

            self.end_headers()



            self.wfile.write((CHAT_PAGE if user_id in ("USER_A", "USER_B") else LOGIN_PAGE).encode("utf-8"))


        elif u.path == '/get_messages':

            p = urllib.parse.parse_qs(u.query)

            
            since = float(p.get('since', [0])[0])


            cookies = parse_cookies(self.headers.get("Cookie", ""))

            uid = cookies.get("chat_user", "")

            if uid not in ("USER_A", "USER_B"):

                self.send_response(401)

                self.send_header('Content-type', 'application/json')

                self.end_headers()

                self.wfile.write(json.dumps({"error": "unauthorized"}).encode())

                return


            self.send_response(200); self.send_header('Content-type', 'application/json'); self.end_headers()

            need_save = False

            with LOCKED:

                LAST_SEEN[uid] = time.time()

                for m in MESSAGES:

                    if m['sender_id'] != uid and not m.get('seen'): 

                        m['seen'] = True; m['updated'] = time.time(); need_save = True

                

                news = [m for m in MESSAGES if m['timestamp'] > since or m.get('updated', 0) > since]

                other_uid = next((k for k in LAST_SEEN if k != uid), None)

                other_online = "Offline"

                if other_uid:

                    diff = time.time() - LAST_SEEN[other_uid]

                    other_online = "Online" if diff < 10 else (datetime.now() - timedelta(seconds=diff) + timedelta(hours=3, minutes=30)).strftime("%H:%M")

            news = [dict(m) for m in news]

            if need_save: save_all()


            self.wfile.write(json.dumps({

                "me": uid,

                "messages": news,

                "is_typing": any(k != uid for k in TYPING_USERS.keys()),

                "other_online": other_online

            }).encode())



    def do_POST(self):

        l = int(self.headers['Content-Length'])

        raw = self.rfile.read(l).decode()

        
        if self.path == '/login':

            # raw مثل: p=9604

            parsed = urllib.parse.parse_qs(raw)

            p = parsed.get("p", [""])[0]



            user_id = PASSWORD_TO_USER.get(p)

            if user_id:

                self.send_response(303)

                # کوکی لاگین (برای همه مسیرها)

                self.send_header("Set-Cookie", f"chat_user={user_id}; Path=/; SameSite=Lax")

                self.send_header("Location", "/")

                self.end_headers()

            else:

                self.send_response(303)

                self.send_header("Location", "/")

                self.end_headers()

            return





        body = json.loads(raw)


        cookies = parse_cookies(self.headers.get("Cookie", ""))

        uid = cookies.get("chat_user", "")

        if uid not in ("USER_A", "USER_B"):

            self.send_response(401); self.end_headers()

            return



        # کاربر را از کوکی تحمیل کن (حتی اگر کلاینت چیز دیگری فرستاد)

        body['u_id'] = uid

        body['sender_id'] = uid


        self.send_response(200); self.end_headers()

        need_append = False

        need_save = False

        new_msg = None


        with LOCKED:

            if self.path == '/send_message':

                body.update({'id': str(time.time()), 'timestamp': time.time(), 'time': (datetime.utcnow() + timedelta(hours=3, minutes=30)).strftime("%H:%M"), 'seen': False, 'react': False})

                MESSAGES.append(body)

                need_append = True

                new_msg = dict(body)
            



            elif self.path == '/delete_message':

                for m in MESSAGES:

                    if m['id'] == body['id'] and m['sender_id'] == body['u_id']:

                        m['deleted'] = True

                        m['updated'] = time.time()

                        need_save = True

                        break



            elif self.path == '/react_message':

                for m in MESSAGES:

                    if m['id'] == body['id']:

                        m['react'] = not m.get('react')

                        m['updated'] = time.time()

                        need_save = True

                        break



            elif self.path == '/typing':

                TYPING_USERS[body['u_id']] = time.time()



        # بیرون لاک

        if need_append:

            append_one(new_msg)

        if need_save:

            save_all()




class ThreadingHTTPServer(socketserver.ThreadingMixIn, socketserver.TCPServer):

    daemon_threads = True; allow_reuse_address = True



if __name__ == "__main__":

    with ThreadingHTTPServer(("0.0.0.0", PORT), ChatHandler) as httpd:

        print(f"Chat Server Running on Port {PORT}..."); httpd.serve_forever()
