# Inchat | اینچت

A secure, real-time chat application with end-to-end encryption and persistent message history.

یک برنامه چت امن و بی‌درنگ با رمزنگاری سرتاسر و تاریخچه پیام پایدار.

## Features | ویژگی‌ها

### 🚀 Core Features | ویژگی‌های اصلی
- **Real-time Messaging** | پیام‌رسانی بی‌درنگ
- **End-to-End Encryption** | رمزنگاری سرتاسر
- **Persistent Chat History** | تاریخچه چت پایدار
- **Multi-user Support** | پشتیبانی از چند کاربر
- **Media File Sharing** | اشتراک‌گذاری فایل‌های رسانه‌ای
- **SQLite Database** | پایگاه داده SQLite

### 🔒 Security | امنیت
- **Password-based Authentication** | احراز هویت مبتنی بر رمز عبور
- **Encrypted Media Storage** | ذخیره‌سازی رسانه‌های رمزنگاری شده
- **Session Management** | مدیریت جلسه
- **Secure File Handling** | مدیریت امن فایل

### 📱 User Experience | تجربه کاربری
- **Bilingual Interface (English/Farsi)** | رابط کاربری دو زبانه (انگلیسی/فارسی)
- **Responsive Design** | طراحی واکنش‌گرا
- **Message Expiry** | انقضای پیام‌ها
- **Chat History Search** | جستجوی تاریخچه چت

## Installation | نصب

### Prerequisites | پیش‌نیازها
- Python 3.7+
- SQLite3

### Setup | راه‌اندازی

1. **Clone the repository** | مخزن را کلون کنید:
```bash
git clone <repository-url>
cd Inchat
```

2. **Run the server** | سرور را اجرا کنید:
```bash
python s.py
```

3. **Access the application** | به برنامه دسترسی پیدا کنید:
Open your browser and navigate to `http://localhost:2026`

مرورگر خود را باز کرده و به `http://localhost:2026` بروید

## Usage | نحوه استفاده

### Authentication | احراز هویت
- Use one of the predefined passwords | از یکی از رمزهای عبور از پیش تعریف شده استفاده کنید:
  - `9604` for USER_A | برای کاربر A
  - `2728` for USER_B | برای کاربر B

### Sending Messages | ارسال پیام
1. Type your message in the input field | پیام خود را در فیلد ورودی تایپ کنید
2. Press Enter or click Send | Enter را فشار دهید یا روی Send کلیک کنید
3. Your message will be encrypted and stored | پیام شما رمزنگاری و ذخیره می‌شود

### Media Sharing | اشتراک‌گذاری رسانه
- Click the media button to upload files | روی دکمه رسانه کلیک کنید تا فایل‌ها را آپلود کنید
- Supported formats: Images, videos, documents | فرمت‌های پشتیبانی شده: تصاویر، ویدیوها، اسناد
- Files are automatically encrypted | فایل‌ها به صورت خودکار رمزنگاری می‌شوند

## Configuration | پیکربندی

### Server Settings | تنظیمات سرور
```python
PORT = 2026                    # Server port | پورت سرور
MAX_MESSAGES_IN_MEMORY = 500   # Max messages in memory | حداکثر پیام در حافظه
MESSAGE_EXPIRY_HOURS = 24      # Message expiry time | زمان انقضای پیام
```

### User Authentication | احراز هویت کاربران
```python
PASSWORD_TO_USER = {
    "9604": "USER_A",
    "2728": "USER_B",
}
```

### Database | پایگاه داده
- **Database file**: `chat_history.db` | فایل پایگاه داده
- **Media directory**: `encrypted_media/` | دایرکتوری رسانه‌ها
- **Automatic cleanup**: Old messages are automatically removed | پاکسازی خودکار: پیام‌های قدیمی به صورت خودکار حذف می‌شوند

## Security Features | ویژگی‌های امنیتی

### Encryption | رمزنگاری
- **Message encryption**: AES-256 encryption for all messages | رمزنگاری پیام: رمزنگاری AES-256 برای همه پیام‌ها
- **Media encryption**: Files are encrypted before storage | رمزنگاری رسانه: فایل‌ها قبل از ذخیره‌سازی رمزنگاری می‌شوند
- **Secure key management**: Keys are generated per session | مدیریت امن کلید: کلیدها برای هر جلسه تولید می‌شوند

### Privacy | حریم خصوصی
- **No tracking**: No analytics or tracking scripts | بدون ردیابی: بدون اسکریپت‌های تحلیلی یا ردیابی
- **Local storage**: All data stored locally | ذخیره‌سازی محلی: همه داده‌ها به صورت محلی ذخیره می‌شوند
- **Message expiry**: Automatic deletion of old messages | انقضای پیام: حذف خودکار پیام‌های قدیمی

## Development | توسعه

### Project Structure | ساختار پروژه
```
Inchat/
├── s.py              # Main server file | فایل اصلی سرور
├── README.md         # Documentation | مستندات
├── .gitignore        # Git ignore file | فایل gitignore
├── chat_history.db   # SQLite database | پایگاه داده SQLite
└── encrypted_media/  # Encrypted media files | فایل‌های رسانه رمنگاری شده
```

### Technologies Used | فناوری‌های استفاده شده
- **Backend**: Python, http.server, SQLite3 | پشتیبان: پایتون، http.server، SQLite3
- **Frontend**: HTML, CSS, JavaScript | جلویی: HTML، CSS، JavaScript
- **Database**: SQLite3 | پایگاه داده: SQLite3
- **Encryption**: AES-256 | رمزنگاری: AES-256

## Contributing | مشارکت

1. Fork the repository | مخزن را فورک کنید
2. Create a feature branch | یک شاخه ویژگی ایجاد کنید
3. Make your changes | تغییرات خود را ایجاد کنید
4. Test thoroughly | به طور کامل تست کنید
5. Submit a pull request | یک درخواست pull ارسال کنید

## License | مجوز

This project is licensed under the MIT License - see the LICENSE file for details.

این پروژه تحت مجوز MIT مجوز دارد - برای جزئیات به فایل LICENSE مراجعه کنید.

## Support | پشتیبانی

For issues and questions:
برای مسائل و سوالات:
- Create an issue on GitHub | یک issue در GitHub ایجاد کنید
- Check the documentation | مستندات را بررسی کنید

---

**Note**: This is a secure chat application designed for private communication. Always ensure you're using it in a trusted environment.

**توجه**: این یک برنامه چت امن طراحی شده برای ارتباط خصوصی است. همیشه اطمینان حاصل کنید که آن را در یک محیط قابل اعتماد استفاده می‌کنید.
