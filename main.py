import imaplib
import smtplib
import poplib
import email
import os
import threading
import queue
import re
import ssl
import certifi
import socket
socket.setdefaulttimeout(15)
import time
import hashlib
import dns.resolver
import shutil
import logging
from kivymd.uix.selectioncontrol import MDCheckbox
from kivy.storage.jsonstore import JsonStore
from kivymd.uix.list import MDList, ThreeLineListItem # زوّدنا الـ ThreeLineListItem هنا
from kivymd.uix.dialog import MDDialog
from kivymd.uix.button import MDFlatButton
from kivymd.uix.textfield import MDTextField
from kivymd.uix.label import MDLabel
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s"
)

from kivy.app import App
from kivy.uix.spinner import Spinner
from kivy.clock import Clock
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.popup import Popup
from kivy.uix.label import Label
from kivy.uix.button import Button
from kivy.uix.textinput import TextInput
from kivy.uix.scrollview import ScrollView

from kivymd.app import MDApp
from kivymd.uix.screen import MDScreen
from kivymd.uix.list import MDList, OneLineListItem
from kivymd.uix.button import MDRaisedButton
from email.utils import parsedate_to_datetime
from email.header import decode_header
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from bs4 import BeautifulSoup

try:
    from kivy.core.audio import SoundLoader
except:
    SoundLoader = None

ATTACHMENTS_FOLDER = "attachments"
if not os.path.exists(ATTACHMENTS_FOLDER):
    os.makedirs(ATTACHMENTS_FOLDER)

def decode_email_header(header):
    decoded_parts = []
    try:
        if not header: return ""
        for bytes_part, charset in decode_header(header):
            if isinstance(bytes_part, bytes):
                try:
                    if charset and charset != 'unknown-8bit':
                        decoded_parts.append(bytes_part.decode(charset))
                    else:
                        decoded_parts.append(bytes_part.decode('utf-8'))
                except (UnicodeDecodeError, LookupError):
                    decoded_parts.append(bytes_part.decode('latin-1', errors='replace'))
            else:
                decoded_parts.append(str(bytes_part))
    except Exception:
        return str(header)
    return "".join(decoded_parts)

def parse_date_to_timestamp(date_str):
    if not date_str:
        return 0

    try:
        # تنظيف أي علامات غريبة
        cleaned = re.sub(r'["\']', '', str(date_str)).strip()

        dt = parsedate_to_datetime(cleaned)

        # لو التاريخ مفيهوش timezone
        if dt and dt.tzinfo is None:
            dt = dt.replace(tzinfo=None)

        return dt.timestamp()

    except Exception:
        # 🔒 fallback آمن: ما يكسرش البرنامج
        return 0
KNOWN_PROVIDERS = {
    "gmail.com": {"imap": "imap.gmail.com", "pop3": "pop.gmail.com", "smtp": "smtp.gmail.com"},
    "yahoo.com": {"imap": "imap.mail.yahoo.com", "pop3": "pop.mail.yahoo.com", "smtp": "smtp.mail.yahoo.com"},
    "outlook.com": {"imap": "outlook.office365.com", "pop3": "outlook.office365.com", "smtp": "smtp.office365.com"},
    "hotmail.com": {"imap": "outlook.office365.com", "pop3": "outlook.office365.com", "smtp": "smtp.office365.com"},
    "naver.com": {"imap": "imap.naver.com", "pop3": "pop.naver.com", "smtp": "smtp.naver.com"}
}

def get_mail_servers(domain):
    SPECIAL_DOMAINS = {
        "orange.fr": ["imap.orange.fr"], 
        "wanadoo.fr": ["imap.orange.fr"],
        "hotmail.com": ["outlook.office365.com"], 
        "outlook.com": ["outlook.office365.com"],
        "live.com": ["outlook.office365.com"], 
        "msn.com": ["outlook.office365.com"],
        "yahoo.com": ["imap.mail.yahoo.com"], 
        "aol.com": ["imap.aol.com"],
        "charter.net": ["mobile.charter.net", "imap.charter.net"], 
        "comcast.net": ["imap.comcast.net"],
        "att.net": ["imap.mail.att.net", "pop.mail.att.net"],
        "139.com": ["imap.139.com", "pop.139.com"],
        "satx.rr.com": ["mail.twc.com", "imap-server.texas.rr.com"],
        "sina.com": ["imap.sina.com", "imap.vip.sina.com", "imap.sina.cn"],
        "nifty.com": ["imap.nifty.com", "pop.nifty.com"],
        "ntlworld.com": ["imap.virginmedia.com", "imap.ntlworld.com"],
        "suddenlink.net": ["imap.suddenlink.net", "mail.suddenlink.net"],
        "terra.com.br": ["imap.terra.com.br", "imap.sao.terra.com.br"],
        "uol.com.br": ["imap.uol.com.br"],
        "videotron.ca": ["imap.videotron.ca", "mail.videotron.ca", "pop.videotron.ca"],
        "naver.com": ["partnerimap.naver.com", "imap.naver.com", "pop.naver.com"],
        "daum.net": ["imap.daum.net", "pop.daum.net"],
        "hanmail.net": ["imap.daum.net", "pop.daum.net"],
        "kakao.com": ["imap.kakao.com", "pop.kakao.com"],
        "nate.com": ["imap.nate.com", "pop3.nate.com"],
        "qq.com": ["imap.exmail.qq.com", "hwimap.exmail.qq.com", "imap.qq.com"],
        "126.com": ["imap.126.com", "hwimap.126.com", "pop.126.com", "imap.163.com"],
        "163.com": ["imap.163.com", "hwimap.163.com", "pop.163.com", "imap.126.com"]
        
    }
    
    if domain in SPECIAL_DOMAINS:
        return SPECIAL_DOMAINS[domain]
        
    servers = [
        f"imap.{domain}", f"pop.{domain}", f"pop3.{domain}", f"mail.{domain}", domain, f"webmail.{domain}"
    ]
    return servers

class EmailClient:
    def __init__(self):
        
        self.email = None
        self.password = None
        self.check_interval = 60000
        self.displayed_ids = set()
        self.after_id = None
        self.task_queue = queue.Queue()
        self.connection = None
        self.protocol = None  # "imap" or "pop3"
        self.fetch_only_last5 = False
        self.is_fetching = False
        self.connection_mode = "auto"
        # self.setup_ui()
        self.connection_info = ""
        self.cached_emails = {}
        self.folders = {}
        self.current_folder = "INBOX"
        self.page_size = 20
        self.current_offset = 0
        self.loading_more = False
        self.total_fetched = 0
        self.app_active = True
        self.last_seen_uid = None
        self.seen_uids = set()
        self.search_mode = False
        self.imap_lock = threading.Lock()
        self.highest_uid = {}
        self.store = JsonStore("settings.json")
        self.selected_msg_ids = set() # لحفظ الرسائل المحددة للحذف
        self.process_queue()


    def _is_port_open(self, host, port, timeout=3):
        try:
            sock = socket.create_connection((host, port), timeout)
            sock.close()
            return True
        except:
            return False

    def _get_ssl_contexts(self):
        # 1. السياق الحديث (Modern Context)
        ctx_modern = ssl.create_default_context()
        ctx_modern.check_hostname = False
        ctx_modern.verify_mode = ssl.CERT_NONE

        # 2. السياق القديم المتهالك (Legacy Context - مأخوذ من كود الفحص)
        ctx_legacy = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        ctx_legacy.check_hostname = False
        ctx_legacy.verify_mode = ssl.CERT_NONE
        ctx_legacy.minimum_version = ssl.TLSVersion.TLSv1

        if hasattr(ssl, 'OP_NO_TLSv1'):
            ctx_legacy.options &= ~ssl.OP_NO_TLSv1
        if hasattr(ssl, 'OP_NO_TLSv1_1'):
            ctx_legacy.options &= ~ssl.OP_NO_TLSv1_1

        for option in ["OP_LEGACY_SERVER_CONNECT", "OP_UNSAFE_LEGACY_RENEGOTIATION", "OP_NO_TICKET"]:
            if hasattr(ssl, option):
                ctx_legacy.options |= getattr(ssl, option)

        try:
            ctx_legacy.set_ciphers("DEFAULT:@SECLEVEL=0")
        except:
            try:
                ctx_legacy.set_ciphers("ALL:!aNULL:!eNULL:!MD5:@SECLEVEL=0")
            except:
                pass

        return ctx_modern, ctx_legacy

    
    def _try_imap_ssl(self, host, port, email, password, verify=True):
        ctx = self._get_ssl_context(verify)
        conn = imaplib.IMAP4_SSL(host, port, timeout=15, ssl_context=ctx)
        conn.login(email, password)
        return conn, "imap", host, port

    def _try_imap_starttls(self, host, port, email, password, verify=True):
        ctx = self._get_ssl_context(verify)
        conn = imaplib.IMAP4(host, port, timeout=15)
        conn.starttls(ssl_context=ctx)
        conn.login(email, password)
        return conn, "imap", host, port

    def _try_imap_plain(self, host, port, email, password):
        conn = imaplib.IMAP4(host, port, timeout=15)
        conn.login(email, password)
        return conn, "imap", host, port  
      
    def _try_pop3_ssl(self, host, port, email, password, verify=True):
        ctx = self._get_ssl_context(verify)
        conn = poplib.POP3_SSL(host, port, timeout=15, context=ctx)
        conn.user(email)
        conn.pass_(password)
        return conn, "pop3", host, port
    
    def _try_pop3_plain(self, host, port, email, password):
        conn = poplib.POP3(host, port, timeout=15)
        conn.user(email)
        conn.pass_(password)
        return conn, "pop3", host, port

    def _try_smtp_starttls(self, host, port, email, password, verify=True):
        ctx = self._get_ssl_context(verify)
        server = smtplib.SMTP(host, port, timeout=15)
        server.ehlo()
        server.starttls(context=ctx)
        server.login(email, password)
        return server, "smtp", host, port
    
    def _try_smtp_ssl(self, host, port, email, password, verify=True):
        ctx = self._get_ssl_context(verify)
        server = smtplib.SMTP_SSL(host, port, timeout=15, context=ctx)
        server.login(email, password)
        return server, "smtp", host, port
    
    def _try_smtp_plain(self, host, port, email, password):
        server = smtplib.SMTP(host, port, timeout=15)
        server.ehlo()
        server.login(email, password)
        return server, "smtp", host, port

    def _connect_smtp_fast(self, email, password):
        domain = email.split("@")[-1].lower()

        if domain in KNOWN_PROVIDERS:
            hosts = [KNOWN_PROVIDERS[domain]["smtp"]]
        else:
            hosts = get_mail_servers(domain)

        ctx_modern, ctx_legacy = self._get_ssl_contexts()
        last_error = ""

        # هنجرب الحديث الأول، ولو فشل نجرب القديم المتهالك
        for ctx in [ctx_modern, ctx_legacy]:
            for host in hosts:
                for port in [465]:
                    try:
                        server = smtplib.SMTP_SSL(host, port, timeout=7, context=ctx)
                        server.login(email, password)
                        return server, "smtp", host, port
                    except Exception as e:
                        last_error = str(e)

            for host in hosts:
                for port in [587, 2525]:
                    try:
                        server = smtplib.SMTP(host, port, timeout=7)
                        server.ehlo()
                        server.starttls(context=ctx)
                        server.login(email, password)
                        return server, "smtp", host, port
                    except Exception as e:
                        last_error = str(e)

        for host in hosts:
            for port in [25]:
                try:
                    server = smtplib.SMTP(host, port, timeout=7)
                    server.ehlo()
                    server.login(email, password)
                    return server, "smtp", host, port
                except Exception as e:
                    last_error = str(e)

        raise Exception(f"SMTP failed: {last_error}")
    # ================== NETWORK & CONNECTION LOGIC ==================

    

    def _check_auth_error(self, error_str):
        e = error_str.lower()

        # 1. أخطاء الشبكة والاتصال (الكود هيتجاهلها ويكمل تخمين السيرفر اللي بعده)
        network_errors = [
            'getaddrinfo', 'timeout', 'timed out', 'connection refused', 
            '10061', '10060', '10054', 'host not found', 'socket', 'unreachable',
            'no route to host', 'network is unreachable'
        ]
        if any(net_err in e for net_err in network_errors):
            return  # سيب السيرفر ده وكمل للي بعده

        # 2. كلمات قاطعة تدل إن الباسورد أو الإيميل غلط (هنوقف البرنامج فوراً عشان نكسب وقت)
        auth_errors = [
            'authentication failed', 'invalid credentials', 
            'wrong password',  
            'invalid user', 'authentication rejected'
        ]
        if any(auth_err in e for auth_err in auth_errors):
            raise Exception(f"❌ Wrong Email or Password!\nServer Response: {error_str}")

        # 3. كلمات تدل إن الحساب مقفول أو خدمة IMAP/POP3 معطلة من جوه (هنوقف فوراً برضه)
        disabled_errors = [
            'disabled', 'not allowed', 'locked', 'blocked', 'temporarily',
            'error 54', 'service is currently not available', 'suspended'
        ]
        if any(dis_err in e for dis_err in disabled_errors):
            raise Exception(f"🚫 Account Locked OR IMAP/POP3 Disabled!\nServer Response: {error_str}")

        # 4. أي خطأ غريب أو جديد من السيرفر (هنوقف ونعرضلك الرسالة الخام زي ما هي)
        raise Exception(f"⚠️ Server Original Response:\n{error_str}")

    def _connect_and_login(self, email_addr, password):
        mode = self.connection_mode
        domain = email_addr.split("@")[-1].lower()
        last_server_response = {"host": "", "proto": "", "port": "", "error": ""}

        if domain in KNOWN_PROVIDERS:
            hosts_imap = [KNOWN_PROVIDERS[domain]["imap"]]
            hosts_pop = [KNOWN_PROVIDERS[domain]["pop3"]]
        else:
            special = get_mail_servers(domain)
            if len(special) > 5:
                hosts_imap = [f"mail.{domain}", f"imap.{domain}", domain]
                hosts_pop = [f"mail.{domain}", f"pop.{domain}", f"pop3.{domain}", domain]
            else:
                hosts_imap = special
                hosts_pop = special

        result_queue = queue.Queue()
        stop_event = threading.Event()
        fatal_errors = []

        def worker(proto, host, port, use_ssl, use_starttls=False):
            if stop_event.is_set(): return
            
            try:
                sock = socket.create_connection((host, port), timeout=2)
                sock.close()
            except:
                return

            if stop_event.is_set(): return

            ctx_modern, ctx_legacy = self._get_ssl_contexts()
            contexts_to_try = [ctx_modern, ctx_legacy] if (use_ssl or use_starttls) else [None]

            for ctx in contexts_to_try:
                if stop_event.is_set(): return
                try:
                    if proto == "imap":
                        if use_ssl:
                            conn = imaplib.IMAP4_SSL(host, port, timeout=8, ssl_context=ctx)
                        elif use_starttls:
                            conn = imaplib.IMAP4(host, port, timeout=8)
                            conn.starttls(ssl_context=ctx)
                        else:
                            conn = imaplib.IMAP4(host, port, timeout=8)
                            
                        try:
                            conn.login(email_addr, password)
                        except imaplib.IMAP4.error as e:
                            err_str = str(e).lower()
                            # تفعيل الخطة البديلة AUTH PLAIN لو الـ LOGIN مقفول
                            if "command unknown" in err_str or "disabled" in err_str or "not supported" in err_str:
                                def plain_auth_handler(response):
                                    return f"\0{email_addr}\0{password}".encode()
                                conn.authenticate('PLAIN', plain_auth_handler)
                            else:
                                raise e
                                
                        info = f"IMAP {'SSL' if use_ssl else 'STARTTLS' if use_starttls else 'Plain'} {host}:{port}"
                        
                        if not stop_event.is_set():
                            result_queue.put((conn, "imap", info))
                            stop_event.set()
                            return

                    elif proto == "pop3":
                        if use_ssl:
                            conn = poplib.POP3_SSL(host, port, timeout=8, context=ctx)
                        else:
                            conn = poplib.POP3(host, port, timeout=8)
                            
                        conn.user(email_addr)
                        conn.pass_(password)
                        
                        if not stop_event.is_set():
                            result_queue.put((conn, "pop3", f"POP3 {'SSL' if use_ssl else 'Plain'} {host}:{port}"))
                            stop_event.set()
                            return

                except Exception as e:
                    e_str = str(e)
                    
                    # 1. تسجيل الخطأ الحقيقي فوراً قبل اتخاذ أي قرار
                    last_server_response["host"] = host
                    last_server_response["proto"] = proto.upper()
                    last_server_response["port"] = port
                    last_server_response["error"] = e_str

                    # 2. لو الخطأ من الـ SSL، هنكمل اللوب عشان نجرب الـ Legacy Context
                    if "ssl" in e_str.lower() or "tlsv1" in e_str.lower() or "wrong version number" in e_str.lower():
                        continue
                        
                    # 3. لو الخطأ رفض دخول قاطع، نسجله كخطأ قاتل ونوقف محاولات السياق ده
                    auth_errs = ['authentication failed', 'invalid credentials', 'wrong password', 'invalid user', 'rejected', 'logon failure']
                    if any(err in e_str.lower() for err in auth_errs):
                        fatal_errors.append(e_str)
                        break

        # ================== تجهيز المضمار للسباق ==================
        combos = []
        if mode in ["auto", "imap_ssl"]:
            for h in hosts_imap: combos.append(("imap", h, 993, True, False))
        if mode in ["auto", "pop3_ssl"]:
            for h in hosts_pop: combos.append(("pop3", h, 995, True, False))
        if mode in ["auto", "imap_plain"]:
            for h in hosts_imap: combos.append(("imap", h, 143, False, True)) # STARTTLS
            for h in hosts_imap: combos.append(("imap", h, 143, False, False)) # Plain
        if mode in ["auto", "pop3_plain"]:
            for h in hosts_pop: combos.append(("pop3", h, 110, False, False))

        # إطلاق كل المندوبين في نفس اللحظة!
        threads = []
        for c in combos:
            t = threading.Thread(target=worker, args=c, daemon=True)
            threads.append(t)
            t.start()

        # ================== انتظار الفائز ==================
        try:
            # هنستنى بحد أقصى 12 ثانية للإجراء كله! (بدل دقايق)
            conn, proto, info = result_queue.get(timeout=12) 
            self.connection_info = info + (" (Auto)" if mode == "auto" else "")
            # 🔥 التعديل هنا: زيادة وقت الانتظار بعد نجاح الاتصال عشان السيرفرات البطيئة
            try:
                if hasattr(conn, 'sock') and conn.sock:
                    conn.sock.settimeout(45)
            except:
                pass
            
            return conn, proto
            
        except queue.Empty:
            # لو الـ 12 ثانية خلصوا ومحدش كسب
            stop_event.set() # اقتل أي حد لسه بيحاول
            
            if fatal_errors:
                raise Exception(
                    f"❌ Login Failed\n\n"
                    f"Protocol : {last_server_response['proto']}\n"
                    f"Host     : {last_server_response['host']}\n"
                    f"Port     : {last_server_response['port']}\n\n"
                    f"Server Response:\n"
                    f"{last_server_response['error']}"
                )
            else:
                raise Exception(f"Connection failed. Ports blocked or server unresponsive after testing {len(combos)} combinations.")

    def clear_email_list(self):
        if hasattr(self, "email_list"):
            self.email_list.clear_widgets()


    def add_email_item(self, iid, sender, subject, date_text):
        clean_date = str(date_text).replace("+00:00", "").strip()
        
        item = ThreeLineListItem(
            text=f"[b]{sender}[/b]",
            secondary_text=subject,
            tertiary_text=clean_date,
            theme_text_color="Custom",
            text_color=(0.1, 0.1, 0.1, 1)
        )
        item.msg_id = iid
        item.long_press_triggered = False

        def on_item_long_click(instance):
            instance.long_press_triggered = True
            self.toggle_item_selection(instance)

        def touch_down(inst, touch):
            if inst.collide_point(*touch.pos):
                inst.long_press_triggered = False

                inst.long_press_event = Clock.schedule_once(
                    lambda dt: on_item_long_click(inst),
                    0.8
                )
            return False

        def touch_up(inst, touch):
            if hasattr(inst, "long_press_event"):
                inst.long_press_event.cancel()
            return False

        def on_item_click(instance):

            if instance.long_press_triggered:
                instance.long_press_triggered = False
                return

            if self.selected_msg_ids:
                self.toggle_item_selection(instance)
            else:
                self._open_email_from_list(instance.msg_id)

        item.bind(on_release=on_item_click)
        item.bind(on_touch_down=touch_down)
        item.bind(on_touch_up=touch_up)

        self.email_list.add_widget(item)

    def toggle_item_selection(self, item_widget):
        mid = item_widget.msg_id
        if mid in self.selected_msg_ids:
            self.selected_msg_ids.remove(mid)
            item_widget.md_bg_color = (1, 1, 1, 1) # يرجع للابيض الافتراضي
        else:
            self.selected_msg_ids.add(mid)
            item_widget.md_bg_color = (1, 0.8, 0.8, 1) # يتلون بأحمر خفيف للتحديد
            
        # تحديث نص زرار المسح في السيرفر بحسب عدد العناصر
        if self.selected_msg_ids:
            self.btn_delete.text = f"Delete ({len(self.selected_msg_ids)})"
            self.btn_delete.md_bg_color = (1, 0, 0, 1) # يقلب أحمر خطر
        else:
            self.btn_delete.text = "Delete"
            self.btn_delete.md_bg_color = App.get_running_app().theme_cls.primary_color


    def _open_email_from_list(self, msg_id):
        self.start_view_email_thread_manual(msg_id)


    def start_view_email_thread_manual(self, msg_id):

        if not self.email:
            return

        self.is_fetching = True

        self.set_status(f"Loading email {msg_id}...")

        threading.Thread(
            target=self._threaded_view_email,
            args=(msg_id,),
            daemon=True
        ).start()          

    def toggle_theme(self):
        app = App.get_running_app()

        if app.theme_cls.theme_style == "Dark":
            app.theme_cls.theme_style = "Light"
        else:
            app.theme_cls.theme_style = "Dark"

    def ask_save_login(self):

        dialog = MDDialog(
            title="Save Login",
            text="Do you want to save this account for next time?",
            buttons=[
                MDFlatButton(
                    text="NO",
                    on_release=lambda x: (
                        dialog.dismiss()
                    )
                ),
                MDFlatButton(
                    text="YES",
                    on_release=lambda x: (
                        self.store.put(
                            "login",
                            email=self.email,
                            password=self.password
                        ),
                        dialog.dismiss()
                    )
                )
            ]
        )

        dialog.open()


    def build_ui(self):
        screen = MDScreen()

        # الحاوية الرئيسية
        layout = BoxLayout(
            orientation="vertical",
            spacing=12,
            padding=15,
            size_hint=(1, 1)
        )

        # === هيدر التطبيق باسم بنتك Asia ===
        title_label = MDLabel(
            text="[b]✨ Asia Mail Client Pro ✨[/b]",
            halign="center",
            font_style="H5",
            theme_text_color="Primary",
            markup=True,
            size_hint_y=None,
            height=40
        )
        layout.add_widget(title_label)

        # === خانة الإيميل الذكية (تغنيك عن الـ Label العادي) ===
        self.email_field = MDTextField(
            hint_text="Email Address",
            helper_text="e.g., name@domain.com",
            helper_text_mode="on_focus",
            mode="rectangle",
            multiline=False,
            size_hint_y=None,
            height=50
        )
        layout.add_widget(self.email_field)

        # === خانة الباسورد الذكية ===
        self.password_field = MDTextField(
            hint_text="Password",
            password=True,
            mode="rectangle",
            multiline=False,
            size_hint_y=None,
            height=50
        )
        layout.add_widget(self.password_field)
        
        if self.store.exists("login"):
            data = self.store.get("login")
            self.email_field.text = data.get("email", "")
            self.password_field.text = data.get("password", "")

        # زر الاتصال
        connect_btn = MDRaisedButton(
            text="CONNECT",
            size_hint=(None, None),
            size=(200, 45),
            pos_hint={"center_x": 0.5},
            on_release=lambda x: self.connect_and_fetch()
        )
        layout.add_widget(connect_btn)

        # قائمة اختيار وضع الاتصال
        self.mode_spinner = Spinner(
            text='auto',
            values=('auto', 'imap_ssl', 'imap_plain', 'pop3_ssl', 'pop3_plain'),
            size_hint_y=None,
            height=45,
            background_color=(0.2, 0.6, 1, 1)
        )
        layout.add_widget(MDLabel(text="Connection Mode:", size_hint_y=None, height=20, theme_text_color="Hint"))
        layout.add_widget(self.mode_spinner)

        # === شريط زراير التحكم (بتمرير أفقي) ===
        actions_scroll = ScrollView(size_hint=(1, None), height=50, do_scroll_x=True, do_scroll_y=False)
        actions_layout = BoxLayout(orientation="horizontal", spacing=10, size_hint_x=None, padding=[5,0,5,0])
        actions_layout.bind(minimum_width=actions_layout.setter('width'))

        # تعريف الزراير واحدة واحدة عشان نضمن إن self.btn_delete معرف
        self.btn_refresh = MDRaisedButton(text="Refresh", on_release=lambda x: self.refresh_emails())
        self.btn_new = MDRaisedButton(text="New", on_release=lambda x: self.compose_email_window())
        self.btn_search = MDRaisedButton(text="Search", on_release=lambda x: self.search_all_folders())
        self.btn_last5 = MDRaisedButton(text="Last 5", on_release=lambda x: self.fetch_last_5_button())
        
        # ده الزرار المهم اللي إنت بتسأل عليه:
        self.btn_delete = MDRaisedButton(text="Delete", on_release=lambda x: self.start_delete_selected_thread())
        
        self.btn_delete_last = MDRaisedButton(text="Del Last", on_release=lambda x: self.start_delete_last_n_thread())
        self.btn_theme = MDRaisedButton(text="Theme", on_release=lambda x: self.toggle_theme())
        self.btn_exit = MDRaisedButton(text="Exit", on_release=lambda x: self.exit_session())

        # إضافة الزراير للشريط (بنفس الترتيب)
        for btn in [self.btn_refresh, self.btn_new, self.btn_search, self.btn_last5, self.btn_delete, self.btn_delete_last, self.btn_theme, self.btn_exit]:
            actions_layout.add_widget(btn)

        actions_scroll.add_widget(actions_layout)
        layout.add_widget(actions_scroll)

        # شريط الحالة
        self.status_label = MDLabel(text="Ready", size_hint_y=None, height=30, halign="center", theme_text_color="Secondary")
        layout.add_widget(self.status_label)

        # === شريط الفولدرات (Inbox, Sent, Spam) ===
        self.tabs_scroll = ScrollView(size_hint=(1, None), height=50, do_scroll_x=True, do_scroll_y=False)
        self.tabs_layout = BoxLayout(orientation="horizontal", spacing=10, size_hint_x=None, padding=[5, 5, 5, 5])
        self.tabs_layout.bind(minimum_width=self.tabs_layout.setter('width'))
        self.tabs_scroll.add_widget(self.tabs_layout)
        layout.add_widget(self.tabs_scroll)

        # قائمة الإيميلات الاحترافية الـ 3 سطور
        self.email_list = MDList()
        # ربط السكرولر بحدث مراقبة الحركة للسحب لأسفل
        emails_scroll = ScrollView(size_hint=(1, 1))
        
        def check_scroll_y(instance, value):
            # لو المستخدم سحب الشاشة لتحت خالص (أقل من الصفر) والتطبيق مش مشغول حالياً
            if value < -0.05 and not self.is_fetching:
                self.refresh_emails()
                
        emails_scroll.bind(scroll_y=check_scroll_y)
        emails_scroll.add_widget(self.email_list)
        layout.add_widget(emails_scroll)


        screen.add_widget(layout)
        return screen


    def exit_session(self):
        # 1. إيقاف كل العمليات الدورية والشغالة
        self.app_active = False
        self.is_fetching = False

        if self.after_id:
            try:
                Clock.unschedule(self.after_id)
            except:
                pass
            self.after_id = None

        # 2. إغلاق الاتصال بأمان
        try:
            if self.connection:
                if self.protocol == "imap":
                    self.connection.logout()
                elif self.protocol == "pop3":
                    self.connection.quit()
        except:
            pass

        # 3. تصفير الذاكرة بالكامل
        self.connection = None
        self.protocol = None
        self.email = None
        self.password = None

        self.displayed_ids.clear()
        self.cached_emails.clear()
        self.folders.clear()
        self.highest_uid.clear()
        self.seen_uids.clear()

        self.current_folder = "INBOX"
        self.current_offset = 0
        self.loading_more = False
        self.total_fetched = 0

        # 4. حذف الملفات المؤقتة (المرفقات)
        try:
            if os.path.exists(ATTACHMENTS_FOLDER):
                shutil.rmtree(ATTACHMENTS_FOLDER)
                os.makedirs(ATTACHMENTS_FOLDER)
        except Exception as e:
            print(f"Cleanup error: {e}")

        # 5. تنظيف حقول الواجهة والقائمة في Kivy
        def clear_ui_fields(dt):
            self.clear_email_list()
            self.email_field.text = ""
            self.password_field.text = ""
            if hasattr(self, 'tabs_layout'):
                self.tabs_layout.clear_widgets()

        Clock.schedule_once(clear_ui_fields)
        self.set_status("Program reset completely (like fresh start)")


    def set_status(self, text):

        def update_label(dt):
            if hasattr(self, "status_label"):
                self.status_label.text = str(text)

        Clock.schedule_once(update_label)

    def show_dialog(self, title, text):
        def open_dialog(dt):
            dialog = MDDialog(
                title=title,
                text=str(text),
                buttons=[
                    MDFlatButton(
                        text="OK",
                        on_release=lambda x: dialog.dismiss()
                    )
                ],
            )
            dialog.open()
        # لازم نستخدم Clock عشان الواجهة متعملش Crash
        Clock.schedule_once(open_dialog)

    def process_queue(self, *args):
        try:
            while True:
                task = self.task_queue.get_nowait()
                task()
        except queue.Empty:
            pass

        Clock.schedule_once(self.process_queue, 0.05)

    def connect_and_fetch(self):

        self.email = self.email_field.text
        self.password = self.password_field.text

        self.connection_mode = self.mode_spinner.text

        if not self.email or not self.password:
            print("Please enter email and password!")
            return
        self.connection_mode = self.mode_spinner.text
        if not self.email or not self.password:
            print("Please enter email and password!")
            return
            
        # Default fetch normal (Last 50)
        self.current_offset = 0
        self.cached_emails.clear()
        
        # 🔥 ضيف التلات سطور دول عشان تصفر الذاكرة بالكامل كل مرة تعمل اتصال
        self.displayed_ids.clear()
        self.seen_uids.clear()     
        self.highest_uid.clear()   
        
        self.start_fetch_thread(is_first_connect=True)


    def start_periodic_check(self):

        if self.after_id:
            try:
                Clock.unschedule(self.after_id)
            except:
                pass

        def check(dt=None):

            if not self.app_active:
                return

            if not self.is_fetching:
                self.start_fetch_thread(notify=True)

        self.after_id = check

        Clock.schedule_interval(
            check,
            self.check_interval / 1000.0
        )

    def start_fetch_thread(self, notify=False, count_to_display=50, is_first_connect=False):
        if self.is_fetching:
            return
        self.is_fetching = True
        self.set_status("Fetching emails...")
        threading.Thread(
            target=self._threaded_fetch,
            args=(self.email, self.password, count_to_display, notify, is_first_connect),
            daemon=True
        ).start()

    def render_emails_sorted(self):

        self.clear_email_list()

        emails_sorted = sorted(
            self.cached_emails.values(),
            key=lambda x: x.get("dt", 0),
            reverse=True
        )

        for e in emails_sorted:

            sender = str(e["values"][0])
            subject = str(e["values"][1])
            date_text = str(e["values"][2])

            self.add_email_item(
                e["id"],
                sender,
                subject,
                date_text
            )

    def _threaded_fetch(self, email_addr, password, count_to_display, notify, is_first_connect):
        mail = None
        proto = None
        current_ids = set()

        try:
            # 1. إدارة الاتصال
            if self.connection and not is_first_connect:
                self.ensure_connection_alive()
                mail = self.connection
                proto = self.protocol
            else:
                old_proto = self.protocol
                mail, proto = self._connect_and_login(email_addr, password)
               
                # 🔥 التعديل هنا: قفل التخمين وتثبيت البروتوكول الناجح فوراً عشان الريفرش والمسح
                if "imap" in proto.lower():
                    self.connection_mode = "imap_ssl" if "993" in self.connection_info else "imap_plain"
                else:
                    self.connection_mode = "pop3_ssl" if "995" in self.connection_info else "pop3_plain"

                if old_proto and old_proto != proto:
                    self.cached_emails.clear()
                    self.displayed_ids.clear()
                    self.seen_uids.clear()
                    self.current_offset = 0
                    self.highest_uid.clear()
                
                self.connection = mail
                self.protocol = proto

            if is_first_connect:
                if proto == "imap":
                    self.folders = self.detect_folders()
                    self.current_folder = self.folders.get("Inbox", self.folders.get("INBOX", "INBOX"))
                    self.task_queue.put(self.build_folder_tabs)

                self.task_queue.put(self.update_buttons)
                self.task_queue.put(lambda: self.set_status(f"Connected via {self.connection_info} | Fetching..."))
                self.task_queue.put(lambda: self.show_dialog("Success", f"🎉 Logged in successfully via {proto.upper()}!\nFetching your emails now..."))
                if not self.store.exists("login"):
                    self.task_queue.put(self.ask_save_login)
                self.task_queue.put(self.start_periodic_check)

            # 2. معالجة IMAP
            if proto == "imap" and self.current_folder:
                clean_folder = self.current_folder.strip('"\'')
                status, _ = mail.select(f'"{clean_folder}"', readonly=True)
                if status != "OK":
                    status, _ = mail.select("INBOX", readonly=True)
                
                if status == "OK":
                    status, data = mail.uid('search', None, "ALL")
                    if status == "OK" and data and data[0]:
                        all_uids = data[0].split()
                        uids_to_fetch = list(reversed(all_uids))[:self.page_size]
                        
                        for uid in uids_to_fetch:
                            uid_str = uid.decode()
                            if uid_str in self.cached_emails: continue
                            
                            status, fetch_data = mail.uid('fetch', uid, "(BODY.PEEK[HEADER] FLAGS INTERNALDATE)")
                            if status != "OK":
                                status, fetch_data = mail.uid('fetch', uid, "(RFC822.HEADER FLAGS INTERNALDATE)")
                            
                            if status == "OK":
                                msg = email.message_from_bytes(fetch_data[0][1])
                                sender = decode_email_header(msg.get("From", "Unknown"))
                                subject = decode_email_header(msg.get("Subject", "No Subject"))
                                date_str = msg.get("Date", "")
                                
                                self.cached_emails[uid_str] = {
                                    "id": uid_str,
                                    "values": (sender, subject, date_str[:16]),
                                    "tags": () if any(s in str(fetch_data).lower() for s in ["\\seen", "seen"]) else ("Unread.Treeview",),
                                    "dt": parse_date_to_timestamp(date_str)
                                }
                                current_ids.add(uid_str)

            # 3. معالجة POP3
            elif proto == "pop3":
                self.ensure_connection_alive()
                resp, items, _ = mail.uidl()
                for item in reversed(items[-self.page_size:]):
                    parts = item.decode().split()
                    if len(parts) < 2: continue
                    msg_num, uid = int(parts[0]), parts[1]
                    
                    if uid in self.cached_emails: continue
                    
                    try:
                        _, lines, _ = mail.top(msg_num, 20)
                    except:
                        _, lines, _ = mail.retr(msg_num)
                        
                    msg = email.message_from_bytes(b"\r\n".join(lines))
                    sender = decode_email_header(msg.get("From", "Unknown"))
                    subject = decode_email_header(msg.get("Subject", "No Subject"))
                    date_str = msg.get("Date", "")
                    
                    stable_id = hashlib.md5(f"{sender}|{subject}|{date_str}".encode()).hexdigest()
                    self.cached_emails[stable_id] = {
                        "id": stable_id, "values": (sender, subject, date_str[:16]),
                        "tags": (), "dt": parse_date_to_timestamp(date_str)
                    }
                    current_ids.add(stable_id)

            # 4. تحديث الواجهة
            if self.cached_emails:
                self.task_queue.put(self.render_emails_sorted)

        except Exception as e:
            error_msg = str(e)
            # إظهار بوب أب بالرد الحقيقي من السيرفر فوراً
            self.task_queue.put(lambda: self.show_dialog("❌ Connection Failed", error_msg))
            self.task_queue.put(lambda: self.set_status("Connection failed."))
        finally:
            self.loading_more = False
            self.is_fetching = False
            if self.connection:
                self.task_queue.put(lambda: self.set_status(f"Ready | {self.connection_info}"))

    def update_buttons(self):
        pass


    def detect_folders(self):
        folders = {}
        try:
            status, data = self.connection.list()
            if status != "OK":
                return {"Inbox": "INBOX"}

            for raw in data:
                try:
                    if not raw: continue
                    # فك التشفير بأمان
                    if isinstance(raw, tuple):
                        line = raw[0].decode(errors='ignore')
                    else:
                        line = raw.decode(errors='ignore')

                    # فلتر ذكي جداً لاستخراج اسم الفولدر مهما كان شكل السيرفر
                    match = re.search(r'^\s*\((.*?)\)\s+("[^"]+"|\'[^\']+\'|NIL)\s+(.*)$', line)
                    if match:
                        folder_name = match.group(3).strip()
                    else:
                        folder_name = line.split()[-1].strip()

                    # إزالة الأقواس لو موجودة عشان نستخدمها صح بعدين
                    if (folder_name.startswith('"') and folder_name.endswith('"')) or \
                       (folder_name.startswith("'") and folder_name.endswith("'")):
                        folder_name = folder_name[1:-1]

                    lname = folder_name.lower()
                    
                    # تنظيف الاسم للعرض (عشان لو السيرفر باعت INBOX.Sent يخليها Sent بس)
                    display_name = folder_name
                    if lname.startswith("inbox.") or lname.startswith("inbox/"):
                        display_name = folder_name[6:]

                    lname_clean = display_name.lower()

                    # تصنيف الفولدرات بذكاء
                    if "inbox" in lname_clean or lname_clean == "inbox":
                        folders["Inbox"] = folder_name
                    elif "spam" in lname_clean or "junk" in lname_clean:
                        folders["Spam"] = folder_name
                    elif "sent" in lname_clean:
                        folders["Sent"] = folder_name
                    elif "trash" in lname_clean or "deleted" in lname_clean or "bin" in lname_clean:
                        folders["Trash"] = folder_name
                    elif "draft" in lname_clean:
                        folders["Drafts"] = folder_name
                    elif "archive" in lname_clean:
                        folders["Archive"] = folder_name
                    else:
                        folders[display_name] = folder_name

                except Exception as e:
                    logging.warning(f"Error parsing folder line: {e}")
                    continue

        except Exception as e:
            logging.error(f"Error detecting folders: {e}")

        # ضمان وجود الـ Inbox دائماً عشان البرنامج ميكراشش
        if "Inbox" not in folders:
            folders["Inbox"] = "INBOX"

        return folders
           
    def build_folder_tabs(self):
        def update_tabs(dt):
            if hasattr(self, 'tabs_layout'):
                self.tabs_layout.clear_widgets()
                
                if self.protocol == "pop3":
                    return # الـ POP3 مفيهوش فولدرات

                for name, folder_path in self.folders.items():
                    btn = MDRaisedButton(
                        text=name,
                        md_bg_color=(0.8, 0.8, 0.8, 1) if name != "Inbox" else (0.2, 0.6, 1, 1),
                        text_color=(0, 0, 0, 1) if name != "Inbox" else (1, 1, 1, 1)
                    )
                    btn.bind(on_release=lambda instance, f_path=folder_path: self.on_folder_change_kivy(f_path, instance))
                    self.tabs_layout.add_widget(btn)
                    
        Clock.schedule_once(update_tabs)

    def on_folder_change_kivy(self, folder_path, btn_instance):
        # 1. تلوين الزرار النشط وإعادة باقي الفولدرات للرمادي
        for child in self.tabs_layout.children:
            child.md_bg_color = (0.8, 0.8, 0.8, 1)
            child.text_color = (0, 0, 0, 1)
        btn_instance.md_bg_color = (0.2, 0.6, 1, 1)
        btn_instance.text_color = (1, 1, 1, 1)

        # 2. تغيير الفولدر الحالي وتصفير الذاكرة تماماً عشان الرسايل متتدخلش
        self.current_folder = folder_path
        self.highest_uid[self.current_folder] = 0
        self.clear_email_list()
        
        self.cached_emails.clear()
        self.current_offset = 0
        self.displayed_ids.clear()
        self.seen_uids.clear() 
        self.search_mode = False
        
        # 3. إجبار الباك-إند يسحب رسايل الفولدر الجديد فوراً باستخدام نفس الجلسة المفتوحة
        self.set_status(f"Switching to {folder_path}...")
        self.start_fetch_thread(notify=False, is_first_connect=False)
    

    def refresh_emails(self):
        if not self.email or not self.password:
            return

        if self.is_fetching:
            return

        try:
            self.set_status("Refreshing emails...")

            # تصفير الكاش والواجهة في Kivy
            self.cached_emails.clear()
            self.displayed_ids.clear()
            self.seen_uids.clear()
            self.current_offset = 0
            self.highest_uid.clear()
            self.clear_email_list() # استخدام الدالة الصحيحة للموبايل

            # فحص حالة الاتصال
            if self.protocol == "imap" and self.connection:
                try:
                    self.connection.noop()
                except:
                    self.connection = None
            elif self.protocol == "pop3" and self.connection:
                try:
                    self.connection.quit()
                except:
                    pass
                self.connection = None 

            # جلب الرسائل من جديد
            self.start_fetch_thread(
                notify=False,
                count_to_display=self.page_size,
                is_first_connect=False
            )

        except Exception as e:
            self.set_status(f"Refresh Error: {e}")
            self.set_status("Ready")

    def fetch_last_5_button(self):
        if not self.email:
            self.task_queue.put(lambda: self.show_dialog("Error", "Please connect to an account first."))
            return

        if self.protocol != "imap":
            self.show_dialog("Not supported", "Last 5 (All Folders) works only with IMAP.")
            return
        self.fetch_only_last5 = True
        self.current_folder = None   # ✅ مهم جدًا
        self.cached_emails.clear()
        self.displayed_ids.clear()
        self.current_offset = 0
        self.loading_more = False
        self.is_fetching = True

        self.set_status("Fetching last 5 emails from all folders...")
        threading.Thread(
            target=self._threaded_fetch_last_5_all_folders,
            daemon=True
        ).start()

    def search_all_folders(self):
        if not self.email:
            self.show_dialog("Error", "Please connect first.")
            return

        if self.protocol != "imap":
            self.show_dialog("Not supported", "Search works only with IMAP.")
            return

        def open_search_dialog(dt):
            content = BoxLayout(orientation='vertical', spacing=10, padding=10)
            
            # حقل إدخال كلمة البحث
            search_input = TextInput(multiline=False, hint_text="Enter keyword to search...")
            content.add_widget(search_input)
            
            # زراير التحكم
            btn_layout = BoxLayout(orientation='horizontal', size_hint_y=None, height=50, spacing=10)
            search_btn = MDRaisedButton(text="Search", pos_hint={"center_y": 0.5})
            cancel_btn = MDFlatButton(text="Cancel", pos_hint={"center_y": 0.5})
            
            btn_layout.add_widget(cancel_btn)
            btn_layout.add_widget(search_btn)
            content.add_widget(btn_layout)

            popup = Popup(title="Search in all folders", content=content, size_hint=(0.8, 0.4))

            def do_search(instance):
                keyword = search_input.text.strip()
                if keyword:
                    popup.dismiss() # نقفل النافذة
                    
                    # تصفير الذاكرة والبدء في البحث
                    self.search_mode = True
                    self.current_folder = None
                    self.cached_emails.clear()
                    self.displayed_ids.clear()
                    self.current_offset = 0
                    
                    self.set_status(f"Searching for '{keyword}' in all folders...")
                    threading.Thread(
                        target=self._threaded_search_all_folders,
                        args=(keyword,),
                        daemon=True
                    ).start()

            search_btn.bind(on_release=do_search)
            cancel_btn.bind(on_release=popup.dismiss)

            popup.open()

        # استدعاء آمن للواجهة
        Clock.schedule_once(open_search_dialog)




    def _threaded_search_all_folders(self, keyword):
        self.ensure_connection_alive()
        results = {}

        try:
            keyword_upper = keyword.upper()

            for folder_name, folder in self.folders.items():
                try:
                    self.connection.select(folder)
                except:
                    continue

                # نبحث في SUBJECT و FROM
                status, data = self.connection.uid(
                    "search",
                    None,
                    f'(OR SUBJECT "{keyword}" FROM "{keyword}")'
                )

                if status != "OK" or not data or not data[0]:
                    continue

                uids = data[0].split()[-50:]  # حد أقصى 50 نتيجة من كل فولدر

                for uid in uids:
                    try:
                        status, fetch_data = self.connection.uid(
                            "fetch",
                            uid,
                            "(BODY.PEEK[HEADER] INTERNALDATE)"
                        )
                        if status != "OK":
                            continue

                        raw_header = None
                        internaldate = None

                        for item in fetch_data:
                            if isinstance(item, tuple):
                                raw_header = item[1]
                            else:
                                m = re.search(r'INTERNALDATE\s+"(.+?)"', str(item))
                                if m:
                                    internaldate = m.group(1)

                        if not raw_header:
                            continue

                        msg = email.message_from_bytes(raw_header)

                        sender = decode_email_header(msg.get("From", ""))
                        subject = decode_email_header(msg.get("Subject", ""))
                        chosen_date = internaldate or msg.get("Date")
                        ts = parse_date_to_timestamp(chosen_date)

                        uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)

                        email_item = {
                            "id": f"{folder}:{uid_str}",
                            "values": (
                                sender,
                                f"[{folder_name}] {subject}",
                                chosen_date
                            ),
                            "tags": (),
                            "dt": ts
                        }

                        results[email_item["id"]] = email_item

                    except:
                        continue

            # ترتيب النتائج
            sorted_emails = sorted(
                results.values(),
                key=lambda x: x.get("dt", 0),
                reverse=True
            )

            # تحديث الحالة
            self.cached_emails = {e["id"]: e for e in sorted_emails}
            self.displayed_ids = set(self.cached_emails.keys())
            self.current_offset = len(self.displayed_ids)

            self.task_queue.put(self.render_emails_sorted)

        except Exception as e:
            self.task_queue.put(
                lambda err=e: self.show_dialog("Search Error", str(err)))

        finally:
            self.is_fetching = False
            self.loading_more = False
            self.task_queue.put(lambda: self.set_status("Ready"))

    def _threaded_fetch_last_5_all_folders(self):

        self.ensure_connection_alive()
        results = {}

        try:
            # 🔴 fallback لو مفيش فولدرات (سيرفرات بدائية)
            folders = self.folders or {"Inbox": "INBOX"}

            for folder_name, folder in folders.items():
                try:
                    self.connection.select(folder)
                except:
                    continue

                status, data = self.connection.uid('search', None, 'ALL')
                if status != 'OK' or not data or not data[0]:
                    continue

                # 🔥 ناخد آخر 5 UIDs من كل فولدر
                last_uids = data[0].split()[-5:]

                for uid in last_uids:
                    try:
                        status, fetch_data = self.connection.uid(
                            'fetch',
                            uid,
                            '(BODY.PEEK[HEADER] INTERNALDATE)'
                        )
                        if status != 'OK':
                            continue

                        raw_header = b""
                        internaldate = None

                        for item in fetch_data:
                            if isinstance(item, tuple):
                                raw_header = item[1]
                            else:
                                m = re.search(r'INTERNALDATE\s+"(.+?)"', str(item))
                                if m:
                                    internaldate = m.group(1)

                        if not raw_header:
                            continue

                        msg = email.message_from_bytes(raw_header)
                        uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)

                        sender = decode_email_header(msg.get("From", "Unknown"))
                        subject = decode_email_header(msg.get("Subject", "No Subject"))
                        chosen_date = internaldate or msg.get("Date")
                        ts = parse_date_to_timestamp(chosen_date)

                        email_item = {
                            'id': f"{folder}:{uid_str}",
                            'values': (sender, f"[{folder_name}] {subject}", chosen_date),
                            'tags': (),
                            'dt': ts
                        }

                        results[email_item['id']] = email_item

                    except:
                        continue

            # 🔥 نرتب كل النتائج ونجيب أحدث 5 إجمالي
            sorted_emails = sorted(
                results.values(),
                key=lambda x: x.get('dt', 0),
                reverse=True
            )[:5]

            self.cached_emails = {e['id']: e for e in sorted_emails}
            self.displayed_ids = set(self.cached_emails.keys())
            self.current_offset = len(self.displayed_ids)

            self.task_queue.put(self.render_emails_sorted)

        except Exception as e:
            self.task_queue.put(
                lambda err=e: self.show_dialog("Error", str(err)))

        finally:
            # 🧹 تنظيف الحالة (مهم جدًا)
            self.fetch_only_last5 = False
            self.search_mode = False
            self.current_folder = self.folders.get("Inbox", "INBOX")

            self.loading_more = False
            self.is_fetching = False
            self.task_queue.put(lambda: self.set_status("Ready"))



    
    


    def ensure_connection_alive(self):
        try:
            if not self.connection:
                raise Exception("No connection")

            if self.protocol == "imap":
                # نستخدم NOOP للتأكد من استجابة السيرفر في أقل من ثانية
                status, _ = self.connection.noop()
                if status != "OK":
                    raise Exception("IMAP connection lost")
                
                # تأكيد إضافي: التحقق من حالة الفولدر الحالي
                if self.current_folder:
                    self.connection.select(f'"{self.current_folder}"', readonly=True)
            
            elif self.protocol == "pop3":
                self.connection.noop()
                
        except Exception as e:
            logging.info(f"Connection lost ({e}). Reconnecting silently...")
            
            # تنظيف الاتصال القديم الميت
            try:
                if self.connection:
                    if self.protocol == "imap": 
                        self.connection.logout()
                    elif self.protocol == "pop3": 
                        self.connection.quit()
            except:
                pass
                
            self.connection = None
            # إعادة بناء الاتصال أوتوماتيكياً
            self.connection, self.protocol = self._connect_and_login(self.email, self.password)



    def _threaded_view_email(self, msg_id):
        max_retries = 3
        
        for attempt in range(max_retries):
            try:
                if not self.email or not self.password:
                    raise Exception("Missing credentials")

                uid = msg_id.strip()

                email_data = self.cached_emails.get(msg_id)
                if not email_data:
                    raise Exception("Message not found")

                pop3_uid = email_data.get("pop3_uid")
                folder_override = None

                if ":" in uid:
                    folder_override, uid = uid.split(":", 1)

                msg = None

                # إجبار التأكد من الاتصال أو إعادة بنائه
                try:
                    self.ensure_connection_alive()
                except:
                    # لو الاتصال ميت، ابنيه من جديد فوراً
                    self.connection = None
                    self.connection, self.protocol = self._connect_and_login(self.email, self.password)

                mail = self.connection

                # ================= IMAP =================
                if self.protocol == "imap":
                    folder = folder_override or self.current_folder or self.folders.get("Inbox", "INBOX")
                    try:
                        mail.select(f'"{folder}"', readonly=True)
                    except:
                        mail.select(folder, readonly=True)

                    status, msg_data = mail.uid('fetch', uid, "(RFC822)")
                    if status != "OK":
                        raise Exception("Failed to fetch message")

                    for part in msg_data:
                        if isinstance(part, tuple) and part[1]:
                            msg = email.message_from_bytes(part[1])
                            break

                # ================= POP3 =================
                elif self.protocol == "pop3":
                    # في POP3، نطلب الـ UIDL عشان نربط الـ ID برقم الرسالة الحالي
                    resp, items, _ = mail.uidl()
                    
                    msg_number = None
                    for item in items:
                        parts = item.decode().split()
                        if len(parts) >= 2:
                            msg_num = parts[0]
                            uidl = parts[1]
                            if uidl == pop3_uid:
                                msg_number = msg_num
                                break

                    if msg_number is None:
                        try:
                            msg_number = items[-1].decode().split()[0]
                        except:
                            raise Exception("Message not found on server")

                    # تحميل الرسالة بالكامل
                    resp, lines, octets = mail.retr(int(msg_number)) 
                    msg = email.message_from_bytes(b"\r\n".join(lines))

                if not msg:
                    raise Exception("Message content empty")

                sender = decode_email_header(msg.get("From", ""))
                subject = decode_email_header(msg.get("Subject", ""))
                body_content, attachments = self.parse_email_body(msg)

                self.task_frame = self.task_queue.put(
                    lambda: self.display_email_window(
                        sender, subject, body_content, attachments, msg
                    )
                )

                # self.task_queue.put(
                #     lambda mid=msg_id: self.email_listbox.item(mid, tags=())
                # )  <--- السطر ده قفلناه تماماً عشان هو سبب الكراش

                # لو وصلنا هنا بدون أخطاء، نكسر الـ Loop ونخرج بنجاح
                break

            except (ssl.SSLEOFError, EOFError, socket.error, imaplib.IMAP4.abort, poplib.error_proto) as e:
                # لو حصل خطأ انقطاع اتصال (EOF)
                logging.warning(f"Connection dropped on attempt {attempt+1}: {e}")
                
                # تنظيف الاتصال القديم الميت
                try:
                    if self.connection:
                        if self.protocol == "imap": self.connection.logout()
                        elif self.protocol == "pop3": self.connection.quit()
                except:
                    pass
                
                self.connection = None # تصفير الاتصال عشان الـ Loop اللي بعده يبدأ على نظافة
                
                if attempt == max_retries - 1:
                    # دي آخر محاولة وفشلت، نظهر الخطأ للمستخدم
                    self.task_queue.put(
                        lambda err=e: self.show_dialog("Error", f"Could not view email. Server keeps closing connection:\n{err}")
                    ) # <--- القوس اللي كان ناقص
                else:
                    # ننتظر ثانية واحدة قبل إعادة المحاولة
                    time.sleep(1)
            
            except Exception as e:
                # أخطاء أخرى غير متعلقة بالشبكة (زي خطأ في التحليل)
                self.task_queue.put(
                    lambda err=e: self.show_dialog("Error", f"An error occurred:\n{err}")
                ) # <--- القوس اللي كان ناقص
                break # نخرج لأن الإعادة مش هتحل خطأ برمجي

        # ================= FINALLY =================
        self.is_fetching = False
        self.task_queue.put(self.start_periodic_check)
        self.task_queue.put(lambda: self.set_status("Ready"))
            
    def parse_email_body(self, msg):
        body_content = ""
        attachments = []
        try:
            if msg.is_multipart():
                for part in msg.walk():
                    content_type = part.get_content_type()
                    content_disposition = str(part.get("Content-Disposition") or "")
                    if "attachment" in content_disposition.lower() and part.get_filename():
                        attachments.append({"filename": decode_email_header(part.get_filename()), "part": part})
                    elif content_type == "text/plain" and "attachment" not in content_disposition.lower():
                        payload = part.get_payload(decode=True)
                        if payload: body_content += payload.decode(errors='ignore')
                    elif content_type == "text/html" and "attachment" not in content_disposition.lower():
                        payload = part.get_payload(decode=True)
                        if payload:
                            html_content = payload.decode(errors='ignore')
                            soup = BeautifulSoup(html_content, "html.parser")
                            body_content += soup.get_text('\n')
            else:
                payload = msg.get_payload(decode=True)
                if payload: body_content = payload.decode(errors='ignore')
        except Exception:
            body_content = "Error parsing body."
        return body_content, attachments

    def display_email_window(self, sender, subject, body, attachments, original_msg):
        def open_reader(dt):
            # 1. الحاوية الرئيسية للنافذة
            content = BoxLayout(orientation='vertical', spacing=10, padding=10)

            # 2. زراير التحكم (رد - إعادة توجيه - إغلاق)
            action_frame = BoxLayout(orientation='horizontal', size_hint_y=None, height=50, spacing=10)
            
            reply_btn = MDRaisedButton(text="Reply")
            reply_btn.bind(on_release=lambda x: self.compose_email_window(reply_to=original_msg))
            
            forward_btn = MDRaisedButton(text="Forward")
            forward_btn.bind(on_release=lambda x: self.compose_email_window(forward_msg=original_msg))
            
            close_btn = MDFlatButton(text="Close")
            
            action_frame.add_widget(reply_btn)
            action_frame.add_widget(forward_btn)
            action_frame.add_widget(close_btn)
            content.add_widget(action_frame)

            # 3. محتوى الإيميل (نص قابل للتمرير)
            email_text_content = f"From: {sender}\nSubject: {subject}\n{'='*40}\n\n{body}"
            email_text = TextInput(
                text=email_text_content, 
                readonly=True, 
                multiline=True,
                background_color=(0.95, 0.95, 0.95, 1),
                foreground_color=(0, 0, 0, 1)
            )
            content.add_widget(email_text)

            # 4. المرفقات (لو موجودة)
            if attachments:
                att_label = Label(text="Attachments:", size_hint_y=None, height=30)
                content.add_widget(att_label)
                
                # سكرول للمرفقات لو كانوا كتير
                att_scroll = ScrollView(size_hint_y=None, height=60)
                att_layout = BoxLayout(orientation='horizontal', spacing=10, size_hint_x=None)
                att_layout.bind(minimum_width=att_layout.setter('width'))
                
                for att in attachments:
                    btn_text = f"DL: {att['filename'][:15]}.." if len(att['filename']) > 15 else f"DL: {att['filename']}"
                    att_btn = MDRaisedButton(text=btn_text, size_hint_x=None, width=150)
                    att_btn.bind(on_release=lambda x, a=att: self.save_attachment(a))
                    att_layout.add_widget(att_btn)
                    
                att_scroll.add_widget(att_layout)
                content.add_widget(att_scroll)

            # 5. إنشاء وعرض الـ Popup
            display_title = subject[:30] + "..." if len(subject) > 30 else subject
            popup = Popup(title=display_title, content=content, size_hint=(0.95, 0.95))
            
            # ربط زرار الإغلاق
            close_btn.bind(on_release=popup.dismiss)
            
            popup.open()
            self.set_status("Email loaded successfully")

        # استخدام Clock لضمان إن واجهة Kivy متعملش كراش
        Clock.schedule_once(open_reader)

    def compose_email_window(self, reply_to=None, forward_msg=None):
        def open_compose(dt):
            content = BoxLayout(orientation='vertical', spacing=10, padding=10)

            # صف المرسل إليه (To)
            to_layout = BoxLayout(orientation='horizontal', size_hint_y=None, height=45, spacing=5)
            to_layout.add_widget(Label(text="To:", size_hint_x=0.2))
            to_entry = TextInput(size_hint_x=0.8, multiline=False)
            to_layout.add_widget(to_entry)
            content.add_widget(to_layout)

            # صف الموضوع (Subject)
            subj_layout = BoxLayout(orientation='horizontal', size_hint_y=None, height=45, spacing=5)
            subj_layout.add_widget(Label(text="Subject:", size_hint_x=0.2))
            subj_entry = TextInput(size_hint_x=0.8, multiline=False)
            subj_layout.add_widget(subj_entry)
            content.add_widget(subj_layout)

            # صندوق الرسالة (Body)
            body_entry = TextInput(multiline=True)
            content.add_widget(body_entry)

            title_text = "Compose Email"

            # لو كان رد (Reply)
            if reply_to:
                title_text = "Reply"
                to_entry.text = decode_email_header(reply_to.get("From", ""))
                subj = decode_email_header(reply_to.get("Subject", ""))
                subj_entry.text = f"Re: {subj}"
                body, _ = self.parse_email_body(reply_to)
                body_entry.text = f"\n\n--- On {reply_to.get('Date')}, {to_entry.text} wrote: ---\n> " + body.replace('\n', '\n> ')

            # لو كان إعادة توجيه (Forward)
            if forward_msg:
                title_text = "Forward"
                subj = decode_email_header(forward_msg.get("Subject", ""))
                subj_entry.text = f"Fwd: {subj}"
                body, _ = self.parse_email_body(forward_msg)
                forward_from = decode_email_header(forward_msg.get('From', ''))
                body_entry.text = f"\n\n--- Forwarded message ---\nFrom: {forward_from}\nDate: {forward_msg.get('Date')}\nSubject: {subj}\n\n{body}"

            # زراير الإرسال والإلغاء
            btn_layout = BoxLayout(orientation='horizontal', size_hint_y=None, height=50, spacing=10)
            send_btn = MDRaisedButton(text="Send Email", pos_hint={"center_y": 0.5})
            cancel_btn = MDFlatButton(text="Cancel", pos_hint={"center_y": 0.5})
            
            btn_layout.add_widget(cancel_btn)
            btn_layout.add_widget(send_btn)
            content.add_widget(btn_layout)

            popup = Popup(title=title_text, content=content, size_hint=(0.95, 0.95))

            def start_send_thread(instance):
                popup.dismiss() # نقفل النافذة أولاً
                self.set_status("Sending email...")
                threading.Thread(
                    target=self._threaded_send, 
                    args=(to_entry.text, subj_entry.text, body_entry.text), 
                    daemon=True
                ).start()

            send_btn.bind(on_release=start_send_thread)
            cancel_btn.bind(on_release=popup.dismiss)

            popup.open()

        Clock.schedule_once(open_compose)

    def _threaded_send(self, recipient, subject, body):
        # الدالة دي بقت نضيفة بدون أي أوامر Tkinter تقفل البرنامج
        msg = MIMEMultipart()
        msg['From'] = self.email
        msg['To'] = recipient
        msg['Subject'] = subject
        msg.attach(MIMEText(body, 'plain'))
        try:
            server, _, host, port = self._connect_smtp_fast(self.email, self.password)
            server.send_message(msg)
            server.quit()
            self.task_queue.put(lambda: self.show_dialog("Success", "Email sent successfully!"))
            self.task_queue.put(lambda: self.set_status("Ready"))
        except Exception as e:
            self.task_queue.put(lambda err=e: self.show_dialog("Send Error", f"Failed to send email:\n{err}"))
            self.task_queue.put(lambda: self.set_status("Ready"))

    def play_notification_sound_and_show_message(self, message):
        try:
            if SoundLoader:
                # تأكد إن عندك ملف اسمه notification.wav في نفس الفولدر
                sound = SoundLoader.load('notification.wav')
                if sound:
                    sound.play()
            self.show_dialog("رسالة جديدة ياهيما", message)
        except Exception as e:
            self.show_dialog("رسالة جديدة ياهيما", message)

    def save_attachment(self, attachment):
        filename = attachment['filename']

        filename = re.sub(r'[\\/*?:"<>|]', "", filename)

        if not filename:
            filename = "attachment.dat"

        filepath = os.path.join(ATTACHMENTS_FOLDER, filename)

        try:
            with open(filepath, "wb") as f:
                f.write(attachment['part'].get_payload(decode=True))

            self.set_status(f"Saved: {filename}")

        except Exception as e:
            self.set_status("Error", str(e))

    

    def update_after_delete(self, deleted_ids):
        for iid in deleted_ids:
            # دعم search mode (folder:uid)
            if iid in self.cached_emails:
                self.cached_emails.pop(iid, None)
            else:
                # حاول تلاقيه بأي شكل
                for key in list(self.cached_emails.keys()):
                    if key.endswith(str(iid)):
                        self.cached_emails.pop(key, None)

            self.displayed_ids.discard(iid)

        self.render_emails_sorted()


    def start_delete_selected_thread(self):
        if not self.email:
            self.show_dialog("Warning", "Please connect to an account first.")
            return
        if not self.selected_msg_ids:
            self.show_dialog("Warning", "Please long-press on emails to select them first.")
            return
            
        self.set_status(f"Deleting {len(self.selected_msg_ids)} selected emails...")
        # نمرر قايمة الأيديهات المتحددة للـ Thread عشان يمسحها من السيرفر
        threading.Thread(target=self._threaded_delete_selected, args=(list(self.selected_msg_ids),), daemon=True).start()
        self.selected_msg_ids.clear() # تصفير التحديد بعد الإرسال
        self.btn_delete.text = "Delete"

    def start_delete_last_n_thread(self):
        if not self.email:
            self.show_dialog("Warning", "Please connect first.")
            return

        def open_delete_dialog(dt):
            content = BoxLayout(orientation='vertical', spacing=10, padding=10)
            
            # حقل إدخال الأرقام فقط
            num_input = TextInput(multiline=False, input_filter='int', hint_text="How many recent emails to delete?")
            content.add_widget(num_input)
            
            # زراير التحكم
            btn_layout = BoxLayout(orientation='horizontal', size_hint_y=None, height=50, spacing=10)
            # زرار الحذف (ممكن نخليه لونه أحمر لو حابب، بس هنسيبه الافتراضي دلوقتي)
            delete_btn = MDRaisedButton(text="Delete", pos_hint={"center_y": 0.5}) 
            cancel_btn = MDFlatButton(text="Cancel", pos_hint={"center_y": 0.5})
            
            btn_layout.add_widget(cancel_btn)
            btn_layout.add_widget(delete_btn)
            content.add_widget(btn_layout)

            popup = Popup(title="Delete Recent Emails", content=content, size_hint=(0.8, 0.4))

            def do_delete(instance):
                val = num_input.text.strip()
                if val.isdigit():
                    num_to_delete = int(val)
                    if num_to_delete > 0:
                        popup.dismiss() # نقفل النافذة
                        self.set_status(f"Deleting last {num_to_delete} emails...")
                        threading.Thread(
                            target=self._threaded_delete_last_n,
                            args=(num_to_delete,),
                            daemon=True
                        ).start()

            delete_btn.bind(on_release=do_delete)
            cancel_btn.bind(on_release=popup.dismiss)

            popup.open()

        # استدعاء آمن للواجهة
        Clock.schedule_once(open_delete_dialog)

    def _threaded_delete_last_n(self, num_to_delete):
        try:
            old_proto = self.protocol
            try:
                self.ensure_connection_alive()
            except:
                self.connection, self.protocol = self._connect_and_login(self.email, self.password)
                if old_proto and self.protocol != old_proto:
                    raise Exception("Connection protocol changed. Please click 'Refresh' to reload your emails before deleting.")

            mail = self.connection
            actually_deleted = 0

            # ================= IMAP =================
            if self.protocol == "imap":
                folder = self.current_folder or "INBOX"
                try: mail.select(f'"{folder}"', readonly=False)
                except: mail.select(folder, readonly=False)

                status, data = mail.uid('search', None, 'ALL')

                if status == 'OK' and data[0]:
                    all_uids = data[0].split()
                    to_delete = all_uids[-num_to_delete:]

                    chunk_size = 100
                    for i in range(0, len(to_delete), chunk_size):
                        chunk = to_delete[i:i+chunk_size]
                        # 🔥 تصفية إضافية لضمان إن كل العناصر أرقام فقط
                        valid_chunk = [u for u in chunk if str(u.decode() if isinstance(u, bytes) else u).isdigit()]
                        if not valid_chunk: continue
                        
                        chunk_str = ",".join([u.decode() if isinstance(u, bytes) else str(u) for u in valid_chunk])
                        
                        try:
                            status_del, _ = mail.uid('STORE', chunk_str, '+FLAGS', '(\\Deleted)')
                            if status_del == "OK":
                                actually_deleted += len(valid_chunk)
                        except Exception as e:
                            logging.error(f"IMAP mass delete error: {e}")

                    try: mail.expunge()
                    except: pass

            # ================= POP3 =================
            elif self.protocol == "pop3":
                resp, items, octets = mail.list()
                total = len(items)
                start = max(1, total - num_to_delete + 1)

                for i in range(total, start - 1, -1):
                    try:
                        mail.dele(i)
                        actually_deleted += 1
                    except Exception as e:
                        logging.error(f"POP3 mass delete error: {e}")
                        err_str = str(e).upper()
                        # 🔥 الانسحاب لو الاتصال سقط
                        if "EOF" in err_str or "CLOSED" in err_str or "10054" in err_str:
                            self.connection = None
                            break
                
                if self.connection:
                    try: mail.quit()
                    except: pass
                    self.connection = None

            if actually_deleted > 0:
                self.task_queue.put(lambda: self._after_delete_last(actually_deleted))
                self.task_queue.put(lambda: self.set_status(f"Cleaned up {actually_deleted} recent emails."))

        except Exception as e:
            self.task_queue.put(
                lambda err=e: self.show_dialog("Delete Error", f"Mass delete failed:\n{err}")
            )
        finally:
            self.task_queue.put(lambda: self.set_status("Ready"))

    def _after_delete_last(self, count):
        # احذف من الكاش
        keys = list(self.cached_emails.keys())[:count]

        for k in keys:
            self.cached_emails.pop(k, None)
            self.displayed_ids.discard(k)

        self.render_emails_sorted()


    def gui_call(self, func, *args, **kwargs):
        # لو الدالة المطلوبة هي إظهار رسالة (بديل الـ messagebox)
        func_name = str(func)
        if "messagebox" in func_name or "show" in getattr(func, "__name__", ""):
            title = args[0] if len(args) > 0 else "Notification"
            text = args[1] if len(args) > 1 else ""
            self.show_dialog(title, text)
        elif callable(func):
            self.task_queue.put(lambda: func(*args, **kwargs))

    

    

class MailApp(MDApp):

    def build(self):
        self.client = EmailClient()
        return self.client.build_ui()

MailApp().run()
