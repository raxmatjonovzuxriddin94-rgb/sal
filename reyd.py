import asyncio
import logging
import os
import re
import time
import sqlite3
from pathlib import Path
from typing import Dict, Any, Optional, List
from datetime import datetime, timedelta
from collections import defaultdict

from dotenv import load_dotenv
load_dotenv()

API_ID = int(os.getenv('API_ID', 0))
API_HASH = os.getenv('API_HASH', '')
BOT_TOKEN = os.getenv('BOT_TOKEN', '')
# Bir nechta admin ID vergul bilan ajratilgan holda: ADMIN_IDS=123456,789012
_admin_ids_raw = os.getenv('ADMIN_IDS', os.getenv('ADMIN_ID', ''))
ADMIN_IDS = {int(x.strip()) for x in _admin_ids_raw.split(',') if x.strip().isdigit()}

if not API_ID or not API_HASH or not BOT_TOKEN:
    print("❌ .env faylida ma'lumotlar topilmadi!")
    exit(1)

print(f"✅ .env fayli yuklandi!")

from aiogram import Bot, Dispatcher, types, F
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton, ChatPermissions, ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove
from aiogram.utils.keyboard import InlineKeyboardBuilder
from aiogram.filters import Command, CommandStart
from aiogram import Router

from telethon import TelegramClient, events
from telethon.tl.types import (
    MessageMediaPhoto,
    MessageMediaDocument,
    DocumentAttributeVideo,
    DocumentAttributeFilename,
    DocumentAttributeAnimated,
    DocumentAttributeAudio,
    Channel,
    Chat,
    User,
    ChannelParticipantsSearch,
    ChannelParticipantsAdmins,
    ChannelParticipantsKicked,
    ChannelParticipant,
    ChannelParticipantAdmin,
    ChannelParticipantCreator,
    ChatBannedRights,
    UserStatusOffline,
    UserStatusOnline,
    UserStatusRecently,
    UserStatusLastWeek,
    UserStatusLastMonth
)
from telethon.sessions import StringSession, MemorySession
from telethon.errors import (
    SessionPasswordNeededError,
    PasswordHashInvalidError,
    PhoneCodeInvalidError,
    PhoneCodeExpiredError,
    FloodWaitError,
    ChatAdminRequiredError,
    UserAdminInvalidError
)
from telethon.tl.functions.channels import (
    GetFullChannelRequest, 
    GetParticipantsRequest,
    EditBannedRequest,
    EditAdminRequest
)
from telethon.tl.functions.messages import GetFullChatRequest
from telethon.tl.functions.contacts import SearchRequest

# Logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('bot.log', encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Papkalar
SESSIONS_DIR = Path("sessions")
DOWNLOADS_DIR = Path("downloads")
SESSIONS_DIR.mkdir(exist_ok=True)
DOWNLOADS_DIR.mkdir(exist_ok=True)

# Database
conn = sqlite3.connect("users.db", check_same_thread=False)
conn.execute("PRAGMA journal_mode=WAL")
conn.execute("PRAGMA busy_timeout=5000")
cursor = conn.cursor()

cursor.execute('''
    CREATE TABLE IF NOT EXISTS users (
        user_id INTEGER PRIMARY KEY,
        session_string TEXT,
        phone_number TEXT,
        is_active BOOLEAN DEFAULT TRUE,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
''')

cursor.execute('''
    CREATE TABLE IF NOT EXISTS saved_messages (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        message_id INTEGER,
        chat_id INTEGER,
        media_type TEXT,
        file_path TEXT,
        saved_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        UNIQUE(user_id, chat_id, message_id)
    )
''')

cursor.execute('''
    CREATE TABLE IF NOT EXISTS watched_chats (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        chat_id INTEGER,
        chat_name TEXT,
        is_active BOOLEAN DEFAULT TRUE,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        UNIQUE(user_id, chat_id)
    )
''')

cursor.execute('''
    CREATE TABLE IF NOT EXISTS username_history (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        target_user_id INTEGER,
        username TEXT,
        found_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        UNIQUE(user_id, target_user_id, username)
    )
''')

cursor.execute('''
    CREATE TABLE IF NOT EXISTS group_cache (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        chat_id INTEGER,
        chat_name TEXT,
        participants_count INTEGER,
        admin_count INTEGER,
        bot_count INTEGER,
        is_admin BOOLEAN,
        can_ban BOOLEAN,
        cached_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        UNIQUE(user_id, chat_id)
    )
''')

# Anti-reyd / so'kish filtri uchun ogohlantirishlar (guruh bo'yicha, doimiy saqlanadi)
cursor.execute('''
    CREATE TABLE IF NOT EXISTS warns (
        chat_id INTEGER,
        user_id INTEGER,
        count INTEGER DEFAULT 0,
        PRIMARY KEY (chat_id, user_id)
    )
''')

# /ruxsat: guruh admini tomonidan filtrdan ozod qilingan foydalanuvchilar
# (faqat o'sha guruh doirasida amal qiladi, faqat shu guruh adminlari bera oladi)
cursor.execute('''
    CREATE TABLE IF NOT EXISTS permitted_users (
        chat_id INTEGER,
        user_id INTEGER,
        granted_by INTEGER,
        granted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (chat_id, user_id)
    )
''')

# Majburiy obuna: admin /majburiy orqali qo'shgan kanal(lar)
cursor.execute('''
    CREATE TABLE IF NOT EXISTS required_channels (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        chat_id INTEGER UNIQUE,
        username TEXT,
        title TEXT,
        invite_link TEXT,
        added_by INTEGER,
        added_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
''')
conn.commit()

# Bot
bot = Bot(token=BOT_TOKEN)
storage = MemoryStorage()
dp = Dispatcher(storage=storage)
router = Router()
dp.include_router(router)

# FSM
class AccountStates(StatesGroup):
    waiting_phone = State()
    waiting_code = State()
    waiting_password = State()
    waiting_chat = State()
    waiting_group_selection = State()
    waiting_purge_confirmation = State()
    waiting_blackword = State()

# Xotira
temp_clients: Dict[int, Dict[str, Any]] = {}
active_clients: Dict[int, TelegramClient] = {}
group_actions: Dict[int, Dict[str, Any]] = {}
# Guruhlar tahlili keshi - "orqaga" bosilganda qayta tahlil qilmaslik uchun
group_stats_cache: Dict[int, Dict] = {}

# ============ ANTI-REYD + SO'KISH FILTRI (1-BOSQICH) ============
# Bu modul GURUH ICHIDA (odam qo'shgan asosiy Bot orqali) ishlaydi -
# userbot bilan bog'liq emas. Botni guruhga admin qilib qo'shish kerak
# (xabarlarni o'chirish va a'zolarni cheklash huquqi bilan).

# --- So'kish/haqorat so'zlari filtri ---
# ESLATMA: ro'yxatdagi ba'zi so'zlar (masalan "am", "om", "oyin") juda qisqa
# bo'lgani uchun oddiy so'zlarga ham tasodifan mos kelishi (false positive)
# mumkin. Buni keyingi bosqichda /blackwords orqali guruh-guruh sozlash
# imkoniyati bilan yaxshilaymiz.
DEFAULT_BLACKLIST_WORDS = [
    "dinnaxuy", "gey", "sky", "ske", "ski", "s.ke", "s.ki", "s.ky", "sk,i", "sk.e", "sk.y",
    "skaman", "sex", "seks", "bich", "bitch", "bic", "trans", "seksual",
    "am", "om", "ayen", "aden", "daden", "oyin", "momen", "adajonin", "oyjonin", "oyjonn",
    "adajonn", "buvin", "buvn", "chmo", "chimo", "dalbayop", "dlbyp", "dalbayob", "dalban",
    "chushpan", "naxuy", "nxy",
]

def contains_blacklisted_word(text: str) -> Optional[str]:
    """Matnda taqiqlangan so'z bormi tekshiradi. Topilsa, o'sha so'zni qaytaradi."""
    if not text:
        return None
    lowered = text.lower()
    for word in DEFAULT_BLACKLIST_WORDS:
        w = word.lower()
        if re.search(r'[.\-_,]', w):
            # Punktuatsiyali (masalan "s.ke") - to'g'ridan-to'g'ri substring qidiramiz
            if w in lowered:
                return word
        else:
            # Oddiy so'z - so'z chegarasi bilan (false positive'ni kamaytirish uchun)
            pattern = r'(?<![a-zA-Zа-яёʻʼ0-9])' + re.escape(w) + r'(?![a-zA-Zа-яёʻʼ0-9])'
            if re.search(pattern, lowered):
                return word
    return None

# --- Reyd aniqlash: bitta foydalanuvchi bir xil kontentni 1 daqiqada 5+ marta yuborsa ---
RAID_THRESHOLD = 5          # nechta marta takrorlansa reyd deb hisoblanadi
RAID_WINDOW_SECONDS = 60    # necha soniya oralig'ida
RAID_LOCK_SECONDS = 5 * 60  # reyddan keyin o'sha ibora nechta soniya "qulflanib" turadi
WARN_LIMIT = 3              # nechta ogohlantirishdan keyin mute beriladi
REPEAT_MUTE_WINDOW_SECONDS = 5 * 60  # ochilgandan keyin shu vaqt ichida yana mute bo'lsa - alohida ogohlantiriladi

# chat_id -> user_id -> [{'sig':..., 'msg_id':..., 'ts':...}, ...]
recent_group_messages: Dict[int, Dict[int, List[Dict[str, Any]]]] = defaultdict(lambda: defaultdict(list))
# chat_id -> signature -> qulf tugash vaqti (time.time())
raid_locked_signatures: Dict[int, Dict[str, float]] = defaultdict(dict)
# (chat_id, user_id) -> oxirgi marta ovozi ochilgan vaqt (unmute qilingan vaqt)
last_unmute_time: Dict[tuple, float] = {}

# --- Guruhni yo'q qilishga urinishni aniqlash (admin ommaviy ban/kick qilsa) ---
MASS_REMOVE_THRESHOLD = 5          # necha marta kick/ban qilinsa "urinish" deb hisoblanadi
MASS_REMOVE_WINDOW_SECONDS = 30    # necha soniya ichida
# chat_id -> actor_user_id -> [timestamp, ...]
mass_remove_tracker: Dict[int, Dict[int, List[float]]] = defaultdict(lambda: defaultdict(list))
# Botning o'zining "Nakrutkani tozalash" / "Guruhni yopish" funksiyalari orqali
# ATAYIN bajarilayotgan ommaviy chiqarishlarni mass-removal himoyasi noto'g'ri
# "hujum" deb hisoblamasligi uchun - shu guruhlar vaqtincha shu ro'yxatga
# qo'shiladi va tekshiruvdan chetlab o'tiladi.
internal_bulk_action_chats: set = set()

def get_message_signature(message: types.Message) -> Optional[str]:
    """Xabar "nimadan" iboratligini bir xil turdagi xabarlarni solishtirish uchun belgi qilib qaytaradi."""
    if message.sticker:
        return f"sticker:{message.sticker.file_unique_id}"
    if message.animation:
        return f"gif:{message.animation.file_unique_id}"
    if message.photo:
        return f"photo:{message.photo[-1].file_unique_id}"
    if message.text:
        return f"text:{message.text.strip().lower()}"
    return None

def is_permitted_user(chat_id: int, user_id: int) -> bool:
    """Foydalanuvchi shu guruhda admin tomonidan /ruxsat berilganmi (filtrdan ozodmi)."""
    cursor.execute(
        "SELECT 1 FROM permitted_users WHERE chat_id=? AND user_id=?",
        (chat_id, user_id)
    )
    return cursor.fetchone() is not None

def grant_permission(chat_id: int, user_id: int, granted_by: int):
    cursor.execute(
        "INSERT OR REPLACE INTO permitted_users (chat_id, user_id, granted_by) VALUES (?, ?, ?)",
        (chat_id, user_id, granted_by)
    )
    conn.commit()

def revoke_permission(chat_id: int, user_id: int) -> bool:
    cursor.execute(
        "DELETE FROM permitted_users WHERE chat_id=? AND user_id=?",
        (chat_id, user_id)
    )
    conn.commit()
    return cursor.rowcount > 0

async def is_chat_admin(chat_id: int, user_id: int) -> bool:
    try:
        member = await bot.get_chat_member(chat_id, user_id)
        return member.status in ("administrator", "creator")
    except Exception:
        return False

async def is_chat_creator(chat_id: int, user_id: int) -> bool:
    try:
        member = await bot.get_chat_member(chat_id, user_id)
        return member.status == "creator"
    except Exception:
        return False

def _full_mute_permissions() -> ChatPermissions:
    try:
        return ChatPermissions(
            can_send_messages=False,
            can_send_audios=False,
            can_send_documents=False,
            can_send_photos=False,
            can_send_videos=False,
            can_send_video_notes=False,
            can_send_voice_notes=False,
            can_send_polls=False,
            can_send_other_messages=False,
            can_add_web_page_previews=False,
        )
    except TypeError:
        # Eski aiogram/Bot API versiyasi uchun fallback
        return ChatPermissions(can_send_messages=False)

def _full_unmute_permissions() -> ChatPermissions:
    try:
        return ChatPermissions(
            can_send_messages=True,
            can_send_audios=True,
            can_send_documents=True,
            can_send_photos=True,
            can_send_videos=True,
            can_send_video_notes=True,
            can_send_voice_notes=True,
            can_send_polls=True,
            can_send_other_messages=True,
            can_add_web_page_previews=True,
        )
    except TypeError:
        return ChatPermissions(can_send_messages=True)

async def mute_user(chat_id: int, user_id: int, display_name: str = "Foydalanuvchi", notify_repeat: bool = True):
    """Foydalanuvchini ovozsiz qiladi. Agar bu foydalanuvchi so'nggi
    REPEAT_MUTE_WINDOW_SECONDS ichida ochilgan bo'lsa - buni alohida,
    aniq va ravshan tarzda guruhga xabar qiladi."""
    try:
        await bot.restrict_chat_member(chat_id, user_id, permissions=_full_mute_permissions())
    except Exception as e:
        logger.error(f"Mute qilishda xatolik (chat={chat_id}, user={user_id}): {e}")
        return

    if notify_repeat:
        key = (chat_id, user_id)
        prev = last_unmute_time.get(key)
        if prev and (time.time() - prev) <= REPEAT_MUTE_WINDOW_SECONDS:
            minutes_ago = int((time.time() - prev) // 60)
            seconds_ago = int((time.time() - prev) % 60)
            try:
                await bot.send_message(
                    chat_id,
                    f"🔁 <b>TAKRORIY QOIDABUZARLIK!</b>\n\n"
                    f"👤 <b>{display_name}</b> ovozi ochilganidan atigi "
                    f"{minutes_ago} daqiqa {seconds_ago} soniya o'tib yana ovozsiz qilindi.\n"
                    f"⚠️ Bu foydalanuvchiga alohida e'tibor bering.",
                    parse_mode="HTML"
                )
            except Exception:
                pass
            del last_unmute_time[key]

async def unmute_user(chat_id: int, user_id: int):
    try:
        await bot.restrict_chat_member(chat_id, user_id, permissions=_full_unmute_permissions())
        last_unmute_time[(chat_id, user_id)] = time.time()
    except Exception as e:
        logger.error(f"Unmute qilishda xatolik (chat={chat_id}, user={user_id}): {e}")

def get_unmute_keyboard(chat_id: int, user_id: int):
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="🔊 Ovozni ochish", callback_data=f"unmute_{chat_id}_{user_id}"))
    return builder.as_markup()

async def add_warn(chat_id: int, user_id: int, display_name: str):
    """Ogohlantirish qo'shadi (DB'da doimiy saqlanadi). WARN_LIMIT ga yetsa - mute qiladi."""
    cursor.execute(
        "INSERT INTO warns (chat_id, user_id, count) VALUES (?, ?, 1) "
        "ON CONFLICT(chat_id, user_id) DO UPDATE SET count = count + 1",
        (chat_id, user_id)
    )
    conn.commit()
    cursor.execute("SELECT count FROM warns WHERE chat_id=? AND user_id=?", (chat_id, user_id))
    row = cursor.fetchone()
    count = row[0] if row else 1

    if count >= WARN_LIMIT:
        await mute_user(chat_id, user_id, display_name)
        cursor.execute("UPDATE warns SET count=0 WHERE chat_id=? AND user_id=?", (chat_id, user_id))
        conn.commit()
        try:
            await bot.send_message(
                chat_id,
                f"🔇 <b>{display_name}</b> {WARN_LIMIT}-ogohlantirishni oldi (taqiqlangan so'zlar uchun) "
                f"va ovozi o'chirildi.",
                parse_mode="HTML",
                reply_markup=get_unmute_keyboard(chat_id, user_id)
            )
        except Exception:
            pass
    else:
        try:
            await bot.send_message(
                chat_id,
                f"⚠️ <b>{display_name}</b>, xabaringizda taqiqlangan so'z bor edi va o'chirildi.\n"
                f"Ogohlantirish: {count}/{WARN_LIMIT}",
                parse_mode="HTML"
            )
        except Exception:
            pass

async def handle_potential_raid(chat_id: int, user_id: int, display_name: str, matching: List[Dict[str, Any]], sig: str):
    """Reyd aniqlanganda: xabarlarni o'chiradi, mute qiladi, iborani vaqtincha qulflaydi, xabar beradi."""
    now = time.time()
    raid_locked_signatures[chat_id][sig] = now + RAID_LOCK_SECONDS

    for m in matching:
        try:
            await bot.delete_message(chat_id, m['msg_id'])
        except Exception:
            pass

    await mute_user(chat_id, user_id, display_name)

    # Guruh nomini har doim ANIQ ko'rsatish uchun to'g'ridan-to'g'ri Telegram'dan
    # olamiz (kesh yoki bazadagi eski/bo'sh nom emas)
    try:
        chat_obj = await bot.get_chat(chat_id)
        group_title = chat_obj.title or str(chat_id)
    except Exception:
        group_title = str(chat_id)

    try:
        await bot.send_message(
            chat_id,
            f"🚨 <b>REYD ANIQLANDI!</b>\n\n"
            f"🏷 <b>Guruh:</b> {group_title}\n"
            f"👤 <b>{display_name}</b> bir xil xabar/stikerni 1 daqiqa ichida "
            f"{len(matching)} marta yubordi.\n"
            f"🔇 Foydalanuvchi ovozi o'chirildi.\n"
            f"⏱ Keyingi {RAID_LOCK_SECONDS // 60} daqiqa davomida shu iborani/stikerni "
            f"ishlatgan HAR KIM ham avtomatik ovozsiz qilinadi.",
            parse_mode="HTML",
            reply_markup=get_unmute_keyboard(chat_id, user_id)
        )
    except Exception as e:
        logger.error(f"Reyd xabarini yuborishda xatolik: {e}")

    # Ittifoq: agar bu guruh biror nazorat guruhiga ulangan bo'lsa - u yerga ham xabar beramiz
    alliance_row = get_alliance_group_by_chat(chat_id)
    if alliance_row and alliance_row[3]:
        control_chat_id = alliance_row[3]
        try:
            await bot.send_message(
                control_chat_id,
                f"🚨 <b>REYD BOSHLANDI!</b>\n\n"
                f"🏷 Guruh: <b>{group_title}</b> (ID: <code>{alliance_row[0]}</code>)\n"
                f"👤 Foydalanuvchi: {display_name}\n"
                f"📨 {len(matching)} marta bir xil xabar/stiker/gif yubordi.",
                parse_mode="HTML",
                reply_markup=get_unmute_keyboard(chat_id, user_id)
            )
        except Exception as e:
            logger.error(f"Nazorat guruhiga xabar yuborishda xatolik: {e}")

def _not_a_command(message: types.Message) -> bool:
    """Xabar '/' bilan boshlanadigan buyruq bo'lmasa True qaytaradi.
    Bu FILTR darajasida ishlatiladi (handler ICHIDA emas) - aks holda
    aiogram bu handlerni "mos keldi" deb hisoblab, pastda joylashgan
    /change, /ulash, /unlink, /blackwords buyruq handlerlariga
    xabarni UMUMAN yetkazmay qo'yadi (bu aynan /link ishlamasligining
    asl sababi edi)."""
    return not (message.text and message.text.startswith('/'))

@router.message(F.chat.type.in_(["group", "supergroup"]), _not_a_command)
async def handle_group_message(message: types.Message):
    """Guruhdagi HAR BIR (buyruqdan boshqa) xabarni anti-reyd va so'kish filtridan o'tkazadi."""
    if not message.from_user or message.from_user.is_bot:
        return

    chat_id = message.chat.id
    user_id = message.from_user.id
    display_name = message.from_user.full_name or "Foydalanuvchi"

    # Adminlar filtrlanmaydi
    if await is_chat_admin(chat_id, user_id):
        return

    # Admin /ruxsat orqali ozod qilgan foydalanuvchilar ham filtrlanmaydi
    if is_permitted_user(chat_id, user_id):
        return

    alliance_row = get_alliance_group_by_chat(chat_id)

    # Ittifoq: xabar uzunligi chegarasi (faqat "oddiy guruh" sifatida
    # ro'yxatdan o'tgan guruhlarda; adminlar yuqorida allaqachon chiqib ketdi)
    if alliance_row and message.text:
        max_len = alliance_row[4] or 350
        if len(message.text) > max_len:
            try:
                await message.delete()
            except Exception:
                pass
            try:
                warn_msg = await message.answer(
                    f"✂️ {display_name}, xabar juda uzun (max {max_len} belgi). O'chirildi."
                )
                asyncio.create_task(_auto_delete(warn_msg, 8))
            except Exception:
                pass
            return

    now = time.time()
    sig = get_message_signature(message)

    # 1) Reyddan keyin "qulflangan" iboradan foydalansa - darhol o'chirib, mute qilamiz
    if sig:
        locked = raid_locked_signatures.get(chat_id, {})
        expire = locked.get(sig)
        if expire and expire > now:
            try:
                await message.delete()
            except Exception:
                pass
            await mute_user(chat_id, user_id, display_name)
            return
        elif expire:
            del locked[sig]

    # 2) So'kish so'zlari filtri (default ro'yxat + guruhga xos qora ro'yxat)
    if message.text:
        bad_word = contains_any_blacklisted_word(message.text, chat_id)
        if bad_word:
            try:
                await message.delete()
            except Exception:
                pass
            await add_warn(chat_id, user_id, display_name)
            return

    # 3) Reyd tekshiruvi - bir xil kontent 1 daqiqada 5+ marta
    if sig:
        bucket = recent_group_messages[chat_id][user_id]
        bucket.append({'sig': sig, 'msg_id': message.message_id, 'ts': now})
        bucket[:] = [m for m in bucket if now - m['ts'] <= RAID_WINDOW_SECONDS]

        matching = [m for m in bucket if m['sig'] == sig]
        if len(matching) >= RAID_THRESHOLD:
            bucket[:] = [m for m in bucket if m['sig'] != sig]
            await handle_potential_raid(chat_id, user_id, display_name, matching, sig)

@router.callback_query(F.data.startswith("unmute_"))
async def unmute_button_pressed(callback_query: types.CallbackQuery):
    parts = callback_query.data.split("_")
    if len(parts) != 3:
        await callback_query.answer()
        return

    chat_id = int(parts[1])
    target_user_id = int(parts[2])
    presser_id = callback_query.from_user.id

    is_admin_here = await is_chat_admin(chat_id, presser_id)
    is_control_admin = False
    if not is_admin_here:
        # Ittifoq: bu guruh ulangan nazorat guruhi admini ham ovozni ocha oladi
        alliance_row = get_alliance_group_by_chat(chat_id)
        if alliance_row and alliance_row[3]:
            is_control_admin = await is_chat_admin(alliance_row[3], presser_id)

    if not is_admin_here and not is_control_admin:
        await callback_query.answer("❌ Faqat adminlar ovozni ocha oladi!", show_alert=True)
        return

    await unmute_user(chat_id, target_user_id)
    await callback_query.answer("✅ Ovoz ochildi!")
    try:
        await callback_query.message.edit_text(
            (callback_query.message.html_text or callback_query.message.text or "") + "\n\n✅ <i>Ovoz ochildi</i>",
            parse_mode="HTML"
        )
    except Exception:
        pass

async def _auto_delete(message: types.Message, delay: int):
    await asyncio.sleep(delay)
    try:
        await message.delete()
    except Exception:
        pass

# ============ GURUHNI YO'Q QILISHGA URINISHDAN HIMOYA ============
# Agar biror admin (hattoki ko-founder bo'lsa ham) qisqa vaqt ichida
# ko'plab a'zolarni ban/kick qilsa - bu "guruhni yo'q qilishga urinish"
# deb hisoblanadi. Faqat guruh EGASI (creator) barcha a'zolarni ban qila oladi.
@router.chat_member()
async def handle_chat_member_update(update: types.ChatMemberUpdated):
    chat_id = update.chat.id
    new_status = update.new_chat_member.status
    if new_status not in ("kicked", "left", "restricted"):
        return

    if chat_id in internal_bulk_action_chats:
        return  # botning o'zi "tozalash"/"guruhni yopish" orqali ataylab bajarayotgan amal

    actor = update.from_user
    target = update.new_chat_member.user
    if not actor or not target:
        return
    if actor.id == target.id:
        return  # foydalanuvchi o'zi chiqib ketdi - bu urinish emas
    me = await bot.get_me()
    if actor.id == me.id:
        return  # bu bizning botimizning o'z amali (masalan tozalash funksiyasi)

    # Guruh EGASI cheklovsiz - faqat u barchani ban qila oladi
    if await is_chat_creator(chat_id, actor.id):
        return

    now = time.time()
    bucket = mass_remove_tracker[chat_id][actor.id]
    bucket.append(now)
    bucket[:] = [t for t in bucket if now - t <= MASS_REMOVE_WINDOW_SECONDS]

    if len(bucket) >= MASS_REMOVE_THRESHOLD:
        mass_remove_tracker[chat_id][actor.id] = []
        await handle_mass_removal_attempt(chat_id, actor, len(bucket))

async def handle_mass_removal_attempt(chat_id: int, actor: types.User, removed_count: int):
    display = actor.full_name or str(actor.id)

    try:
        chat_obj = await bot.get_chat(chat_id)
        group_title = chat_obj.title or str(chat_id)
    except Exception:
        group_title = str(chat_id)

    # Aybdorning admin huquqini darhol olib tashlaymiz (agar co-founder bo'lsa ham)
    try:
        await bot.promote_chat_member(
            chat_id, actor.id,
            can_manage_chat=False, can_delete_messages=False,
            can_manage_video_chats=False, can_restrict_members=False,
            can_promote_members=False, can_change_info=False,
            can_invite_users=False, can_pin_messages=False,
            is_anonymous=False,
        )
    except Exception as e:
        logger.error(f"Admin huquqini olishda xatolik: {e}")

    try:
        await bot.send_message(
            chat_id,
            f"🚨🚨 <b>GURUHNI YO'Q QILISHGA URINISH ANIQLANDI!</b>\n\n"
            f"🏷 <b>Guruh:</b> {group_title}\n"
            f"👤 <b>{display}</b> qisqa vaqt ichida {removed_count} ta a'zoni "
            f"chiqarib/ban qildi.\n"
            f"🛑 Uning admin huquqi darhol olib tashlandi.\n\n"
            f"⚠️ <b>Faqat guruh EGASI</b> barcha a'zolarni ban qila oladi.",
            parse_mode="HTML"
        )
    except Exception as e:
        logger.error(f"Guruhga xabar yuborishda xatolik: {e}")

    # Guruh egasiga shaxsan ham darhol xabar beramiz
    try:
        admins = await bot.get_chat_administrators(chat_id)
        creator = next((a.user for a in admins if a.status == "creator"), None)
        if creator:
            await bot.send_message(
                creator.id,
                f"🚨 <b>Diqqat!</b> <b>{group_title}</b> guruhingizda "
                f"<b>{display}</b> qisqa vaqt ichida {removed_count} ta a'zoni "
                f"chiqarib/ban qildi - bu guruhni yo'q qilishga urinish bo'lishi "
                f"mumkin. Uning admin huquqi avtomatik olib tashlandi.",
                parse_mode="HTML"
            )
    except Exception as e:
        logger.error(f"Egaga xabar yuborishda xatolik: {e}")

    # Ittifoq: nazorat guruhiga ham xabar beramiz
    alliance_row = get_alliance_group_by_chat(chat_id)
    if alliance_row and alliance_row[3]:
        try:
            await bot.send_message(
                alliance_row[3],
                f"🚨 <b>GURUHNI YO'Q QILISHGA URINISH!</b>\n\n"
                f"🏷 Guruh: <b>{group_title}</b> (ID: <code>{alliance_row[0]}</code>)\n"
                f"👤 {display} {removed_count} ta a'zoni chiqarib yubordi.\n"
                f"🛑 Admin huquqi olib tashlandi.",
                parse_mode="HTML"
            )
        except Exception:
            pass

# ============ ITTIFOQ (ALLIANCE) TIZIMI (2-BOSQICH) ============
# "Oddiy guruh" - anti-reyd/so'kish filtri + xabar uzunligi chegarasi
# yoqilgan, tasodifiy 7 xonali ID bilan ro'yxatdan o'tgan guruh.
# "Nazorat guruhi" - bir nechta oddiy guruhni kuzatib turadigan,
# ulardagi reyd xabarlarini oladigan markaziy guruh.
import random
import string

cursor.execute('''
    CREATE TABLE IF NOT EXISTS alliance_control (
        control_chat_id INTEGER PRIMARY KEY,
        title TEXT,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS alliance_group (
        code TEXT PRIMARY KEY,
        chat_id INTEGER UNIQUE,
        title TEXT,
        control_chat_id INTEGER,
        max_msg_len INTEGER DEFAULT 350,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS alliance_blacklist (
        chat_id INTEGER,
        word TEXT,
        PRIMARY KEY (chat_id, word)
    )
''')

# Qo'shilish so'rovlari: nazorat guruhiga xabar qilinadi, /qabul yoki /rad
# orqali (faqat can_change_info huquqli admin tomonidan) hal qilinadi.
cursor.execute('''
    CREATE TABLE IF NOT EXISTS join_requests (
        user_id INTEGER,
        chat_id INTEGER,
        control_chat_id INTEGER,
        notify_message_id INTEGER,
        status TEXT DEFAULT 'pending',
        requested_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (user_id, chat_id)
    )
''')
conn.commit()

def generate_alliance_code() -> str:
    while True:
        code = ''.join(random.choices(string.digits, k=7))
        cursor.execute("SELECT 1 FROM alliance_group WHERE code=?", (code,))
        if not cursor.fetchone():
            return code

def get_alliance_group_by_chat(chat_id: int):
    """Qaytaradi: (code, chat_id, title, control_chat_id, max_msg_len) yoki None."""
    cursor.execute(
        "SELECT code, chat_id, title, control_chat_id, max_msg_len FROM alliance_group WHERE chat_id=?",
        (chat_id,)
    )
    return cursor.fetchone()

def get_alliance_group_by_code(code: str):
    cursor.execute(
        "SELECT code, chat_id, title, control_chat_id, max_msg_len FROM alliance_group WHERE code=?",
        (code,)
    )
    return cursor.fetchone()

def get_custom_blacklist(chat_id: int) -> List[str]:
    cursor.execute("SELECT word FROM alliance_blacklist WHERE chat_id=?", (chat_id,))
    return [r[0] for r in cursor.fetchall()]

def contains_any_blacklisted_word(text: str, chat_id: int) -> Optional[str]:
    """DEFAULT ro'yxat + shu guruhga xos qo'shilgan qora ro'yxat so'zlarini tekshiradi."""
    found = contains_blacklisted_word(text)
    if found:
        return found
    if not text:
        return None
    lowered = text.lower()
    for word in get_custom_blacklist(chat_id):
        w = word.lower()
        if not w:
            continue
        if re.search(r'[.\-_,]', w):
            if w in lowered:
                return word
        else:
            pattern = r'(?<![a-zA-Zа-яёʻʼ0-9])' + re.escape(w) + r'(?![a-zA-Zа-яёʻʼ0-9])'
            if re.search(pattern, lowered):
                return word
    return None

async def get_editable_alliance_groups(user_id: int):
    """Foydalanuvchi guruh ma'lumotlarini o'zgartira oladigan (creator yoki
    can_change_info huquqli admin) barcha ittifoq guruhlarini qaytaradi."""
    result = []
    cursor.execute("SELECT code, chat_id, title FROM alliance_group")
    for code, chat_id, title in cursor.fetchall():
        try:
            member = await bot.get_chat_member(chat_id, user_id)
        except Exception:
            continue
        allowed = member.status == "creator" or (
            member.status == "administrator" and getattr(member, "can_change_info", False)
        )
        if allowed:
            result.append((code, chat_id, title))
    return result

async def has_change_info_right(chat_id: int, user_id: int) -> bool:
    """Foydalanuvchi shu chatda guruh ma'lumotini o'zgartira oladigan
    (creator yoki can_change_info huquqli admin) ekanini tekshiradi."""
    try:
        member = await bot.get_chat_member(chat_id, user_id)
    except Exception:
        return False
    if member.status == "creator":
        return True
    if member.status == "administrator":
        return bool(getattr(member, "can_change_info", False))
    return False

def get_open_notify_message(control_chat_id: int, user_id: int) -> Optional[int]:
    """Shu foydalanuvchi uchun nazorat guruhida hali hal qilinmagan
    (pending) bildirishnoma xabari bor-yo'qligini tekshiradi."""
    cursor.execute(
        "SELECT notify_message_id FROM join_requests "
        "WHERE control_chat_id=? AND user_id=? AND status='pending' AND notify_message_id IS NOT NULL "
        "LIMIT 1",
        (control_chat_id, user_id)
    )
    row = cursor.fetchone()
    return row[0] if row else None

def get_pending_group_titles(control_chat_id: int, user_id: int) -> List[str]:
    """Shu foydalanuvchi ushbu ittifoq doirasida so'rov yuborgan,
    hali hal qilinmagan guruhlar nomlarini qaytaradi."""
    cursor.execute(
        "SELECT jr.chat_id, ag.title FROM join_requests jr "
        "LEFT JOIN alliance_group ag ON ag.chat_id = jr.chat_id "
        "WHERE jr.control_chat_id=? AND jr.user_id=? AND jr.status='pending'",
        (control_chat_id, user_id)
    )
    return [title or str(cid) for cid, title in cursor.fetchall()]

# --- Klaviaturalar ---
def get_alliance_menu_keyboard():
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="📋 Ittifoq guruhlari", callback_data="alliance_list"))
    builder.row(InlineKeyboardButton(text="➕ Yangi ittifoq", callback_data="alliance_new"))
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
    return builder.as_markup()

def get_alliance_new_keyboard(bot_username: str):
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(
        text="➕ Botni guruhga qo'shish",
        url=f"https://t.me/{bot_username}?startgroup=alliance"
    ))
    builder.row(InlineKeyboardButton(text="❌ Bekor qilish", callback_data="alliance_menu"))
    return builder.as_markup()

def get_group_role_keyboard(chat_id: int):
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="🛡 Oddiy guruh", callback_data=f"alliance_role_oddiy_{chat_id}"))
    builder.row(InlineKeyboardButton(text="🧭 Nazorat guruhi", callback_data=f"alliance_role_nazorat_{chat_id}"))
    return builder.as_markup()

def get_blackwords_group_list_keyboard(groups):
    builder = InlineKeyboardBuilder()
    for code, chat_id, title in groups:
        builder.row(InlineKeyboardButton(text=title or str(chat_id), callback_data=f"bw_group_{chat_id}"))
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
    return builder.as_markup()

def get_blackwords_edit_keyboard(chat_id: int, words: List[str]):
    builder = InlineKeyboardBuilder()
    for w in words:
        builder.row(InlineKeyboardButton(text=f"❌ {w}", callback_data=f"bw_del_{chat_id}_{w}"))
    builder.row(InlineKeyboardButton(text="➕ So'z qo'shish", callback_data=f"bw_add_{chat_id}"))
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="blackwords_menu"))
    return builder.as_markup()

def render_blackwords_text(words: List[str]) -> str:
    text = "🚫 <b>Qora ro'yxat so'zlari</b>\n\n"
    text += ("\n".join(f"• {w}" for w in words) if words else "Hali maxsus so'z qo'shilmagan.")
    return text

ALLIANCE_EXPLAIN_TEXT = (
    "🤝 <b>Ittifoq tizimi qanday ishlaydi:</b>\n\n"
    "1️⃣ Botni istalgan guruhga qo'shasiz va uni <b>admin</b> qilasiz "
    "(xabar o'chirish va a'zolarni cheklash huquqi bilan).\n"
    "2️⃣ Bot admin bo'lgach, guruhda ikkita rol taklif qiladi:\n"
    "   🛡 <b>Oddiy guruh</b> — reyddan himoya, so'kish so'zlari filtri va "
    "350 belgigacha xabar chegarasi yoqiladi (adminlarga tegishli emas). "
    "Guruhga tasodifiy 7 xonali ID beriladi.\n"
    "   🧭 <b>Nazorat guruhi</b> — bir nechta oddiy guruhni kuzatib turadi "
    "va ularda reyd boshlanganda shu yerga xabar keladi.\n"
    "3️⃣ Nazorat guruhida <code>/ulash ID</code> deb yozib, oddiy guruhni "
    "shu nazorat guruhiga ulaysiz.\n"
    "4️⃣ Ittifoqdan chiqish uchun oddiy guruhda <code>/unlink</code>, "
    "nazorat guruhida esa <code>/unlink ID</code> deb yozing.\n"
    "5️⃣ Guruh rolini keyinchalik o'zgartirish uchun o'sha guruhda "
    "<code>/change</code> deb yozing.\n"
    "6️⃣ Guruh ma'lumotlarini o'zgartira oladigan admin guruhda "
    "<code>/blackwords</code> deb yozib, o'sha guruh uchun qo'shimcha "
    "qora ro'yxat so'zlarini boshqarishi mumkin.\n\n"
    "Boshlash uchun botni guruhga qo'shing 👇"
)

# --- Bot guruhga qo'shilganda / admin qilinganda ---
@router.my_chat_member()
async def bot_membership_changed(update: types.ChatMemberUpdated):
    chat = update.chat
    new_status = update.new_chat_member.status
    old_status = update.old_chat_member.status

    if new_status == "member" and old_status in ("left", "kicked"):
        try:
            await bot.send_message(
                chat.id,
                "👋 Salom! Ittifoq tizimidan foydalanish uchun meni <b>admin</b> qiling "
                "(xabar o'chirish va a'zolarni cheklash huquqi bilan) — shundan so'ng "
                "guruh rolini tanlash tugmalari chiqadi.",
                parse_mode="HTML"
            )
        except Exception:
            pass
    elif new_status == "administrator" and old_status != "administrator":
        try:
            await bot.send_message(
                chat.id,
                "✅ <b>Admin huquqi berildi!</b>\n\nUshbu guruh qanday ishlatiladi? "
                "(Faqat adminlar tanlay oladi)",
                parse_mode="HTML",
                reply_markup=get_group_role_keyboard(chat.id)
            )
        except Exception:
            pass

# --- Asosiy menyu: Ittifoq bo'limi ---
@router.callback_query(F.data == "alliance_menu")
async def alliance_menu(callback_query: types.CallbackQuery):
    await callback_query.message.edit_text(
        "🤝 <b>Ittifoq</b>\n\nGuruhlaringizni reyd va spamdan himoya qiling.",
        parse_mode="HTML",
        reply_markup=get_alliance_menu_keyboard()
    )
    await callback_query.answer()

@router.callback_query(F.data == "alliance_new")
async def alliance_new(callback_query: types.CallbackQuery):
    me = await bot.get_me()
    await callback_query.message.edit_text(
        ALLIANCE_EXPLAIN_TEXT,
        parse_mode="HTML",
        reply_markup=get_alliance_new_keyboard(me.username)
    )
    await callback_query.answer()

@router.callback_query(F.data == "alliance_list")
async def alliance_list(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    await callback_query.answer("⏳ Qidirilmoqda...")

    rows_g = []
    cursor.execute("SELECT code, chat_id, title, control_chat_id FROM alliance_group")
    for code, chat_id, title, control_chat_id in cursor.fetchall():
        if await is_chat_admin(chat_id, user_id):
            rows_g.append((code, chat_id, title, control_chat_id))

    rows_c = []
    cursor.execute("SELECT control_chat_id, title FROM alliance_control")
    for control_chat_id, title in cursor.fetchall():
        if await is_chat_admin(control_chat_id, user_id):
            rows_c.append((control_chat_id, title))

    if not rows_g and not rows_c:
        await callback_query.message.edit_text(
            "📋 Sizda hali ittifoqqa ulangan guruh yo'q.",
            reply_markup=get_alliance_menu_keyboard()
        )
        return

    text = "📋 <b>Ittifoq guruhlaringiz:</b>\n\n"
    if rows_g:
        text += "🛡 <b>Oddiy guruhlar:</b>\n"
        for code, chat_id, title, control_chat_id in rows_g:
            link_status = "🔗 ulangan" if control_chat_id else "⛔️ nazoratsiz"
            text += f"• {title or chat_id} — ID: <code>{code}</code> ({link_status})\n"
        text += "\n"
    if rows_c:
        text += "🧭 <b>Nazorat guruhlari:</b>\n"
        for control_chat_id, title in rows_c:
            cursor.execute("SELECT COUNT(*) FROM alliance_group WHERE control_chat_id=?", (control_chat_id,))
            cnt = cursor.fetchone()[0]
            text += f"• {title or control_chat_id} — {cnt} ta guruhni kuzatmoqda\n"

    await callback_query.message.edit_text(text, parse_mode="HTML", reply_markup=get_alliance_menu_keyboard())

# --- Rol tanlash (faqat adminlar) ---
async def _activate_oddiy_role(chat_id: int) -> str:
    """Guruhni 'oddiy guruh' rejimiga o'tkazadi (yangi bo'lsa yaratadi,
    mavjud bo'lsa kod o'zgarmaydi) va kodni qaytaradi."""
    existing = get_alliance_group_by_chat(chat_id)
    if existing:
        return existing[0]
    code = generate_alliance_code()
    try:
        chat = await bot.get_chat(chat_id)
        title = chat.title
    except Exception:
        title = None
    cursor.execute(
        "INSERT INTO alliance_group (code, chat_id, title, max_msg_len) VALUES (?, ?, ?, 350)",
        (code, chat_id, title)
    )
    conn.commit()
    return code

@router.callback_query(F.data.startswith("alliance_role_oddiy_"))
async def alliance_role_oddiy(callback_query: types.CallbackQuery):
    chat_id = int(callback_query.data.rsplit("_", 1)[-1])
    if not await is_chat_admin(chat_id, callback_query.from_user.id):
        await callback_query.answer("❌ Faqat guruh adminlari tanlay oladi!", show_alert=True)
        return

    # Agar bu guruh avval "nazorat guruhi" bo'lgan bo'lsa - o'sha rolni olib tashlaymiz
    cursor.execute("DELETE FROM alliance_control WHERE control_chat_id=?", (chat_id,))
    conn.commit()

    code = await _activate_oddiy_role(chat_id)

    await callback_query.message.edit_text(
        f"🛡 <b>Oddiy guruh rejimi yoqildi!</b>\n\n"
        f"🆔 Guruh ID: <code>{code}</code>\n\n"
        f"• Reyddan himoya faol\n"
        f"• So'kish so'zlari filtri faol\n"
        f"• Xabar uzunligi chegarasi: 350 belgi (adminlarga tegishli emas)\n\n"
        f"Bu guruhni nazorat guruhiga ulash uchun, nazorat guruhida:\n"
        f"<code>/ulash {code}</code>\n\n"
        f"Ittifoqdan chiqish uchun shu yerga <code>/unlink</code> deb yozing.\n"
        f"Rolni keyinchalik o'zgartirish uchun <code>/change</code> deb yozing.",
        parse_mode="HTML"
    )
    await callback_query.answer("✅ Oddiy guruh sifatida faollashtirildi!")

@router.callback_query(F.data.startswith("alliance_role_nazorat_"))
async def alliance_role_nazorat(callback_query: types.CallbackQuery):
    chat_id = int(callback_query.data.rsplit("_", 1)[-1])
    if not await is_chat_admin(chat_id, callback_query.from_user.id):
        await callback_query.answer("❌ Faqat guruh adminlari tanlay oladi!", show_alert=True)
        return

    # Agar bu guruh avval "oddiy guruh" bo'lgan bo'lsa - o'sha rolni olib tashlaymiz
    cursor.execute("DELETE FROM alliance_group WHERE chat_id=?", (chat_id,))
    cursor.execute("DELETE FROM alliance_blacklist WHERE chat_id=?", (chat_id,))
    conn.commit()

    try:
        chat = await bot.get_chat(chat_id)
        title = chat.title
    except Exception:
        title = None

    cursor.execute(
        "INSERT OR REPLACE INTO alliance_control (control_chat_id, title) VALUES (?, ?)",
        (chat_id, title)
    )
    conn.commit()

    await callback_query.message.edit_text(
        f"🧭 <b>Nazorat guruhi rejimi yoqildi!</b>\n\n"
        f"Oddiy guruhlarni ulash uchun shu yerga:\n"
        f"<code>/ulash GURUH_ID</code>\n\n"
        f"Ulangan guruhni uzish uchun:\n"
        f"<code>/unlink GURUH_ID</code>\n\n"
        f"Rolni keyinchalik o'zgartirish uchun <code>/change</code> deb yozing.",
        parse_mode="HTML"
    )
    await callback_query.answer("✅ Nazorat guruhi sifatida faollashtirildi!")

# --- /change: guruh rolini keyinchalik o'zgartirish ---
@router.message(Command("change"), F.chat.type.in_(["group", "supergroup"]))
async def change_command(message: types.Message):
    chat_id = message.chat.id
    if not await is_chat_admin(chat_id, message.from_user.id):
        await message.reply("❌ Bu buyruq faqat guruh adminlari uchun.")
        return

    await message.reply(
        "🔄 <b>Guruh rolini o'zgartirish</b>\n\nUshbu guruh endi qanday ishlatilsin?",
        parse_mode="HTML",
        reply_markup=get_group_role_keyboard(chat_id)
    )

# --- /ulash (avvalgi nomi /link), /unlink, /blackwords ---
@router.message(Command("ulash", "link"), F.chat.type.in_(["group", "supergroup"]))
async def link_command(message: types.Message):
    chat_id = message.chat.id
    if not await is_chat_admin(chat_id, message.from_user.id):
        return

    cursor.execute("SELECT 1 FROM alliance_control WHERE control_chat_id=?", (chat_id,))
    if not cursor.fetchone():
        await message.reply("❌ Bu guruh nazorat guruhi sifatida sozlanmagan. Avval /change orqali 'Nazorat guruhi' rolini tanlang.")
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        await message.reply("ℹ️ Foydalanish: <code>/ulash GURUH_ID</code>", parse_mode="HTML")
        return
    code = parts[1].strip()

    group = get_alliance_group_by_code(code)
    if not group:
        await message.reply("❌ Bunday ID'li oddiy guruh topilmadi. ID guruhda /change → 🛡 Oddiy guruh tanlanganda beriladi.")
        return

    cursor.execute("UPDATE alliance_group SET control_chat_id=? WHERE code=?", (chat_id, code))
    conn.commit()
    await message.reply(f"✅ <b>{group[2] or group[1]}</b> guruhi shu nazorat guruhiga ulandi.", parse_mode="HTML")

@router.message(Command("unlink"), F.chat.type.in_(["group", "supergroup"]))
async def unlink_command(message: types.Message):
    chat_id = message.chat.id
    if not await is_chat_admin(chat_id, message.from_user.id):
        return

    parts = message.text.split(maxsplit=1)
    is_control = cursor.execute(
        "SELECT 1 FROM alliance_control WHERE control_chat_id=?", (chat_id,)
    ).fetchone()

    if is_control:
        if len(parts) < 2:
            await message.reply("ℹ️ Foydalanish: <code>/unlink GURUH_ID</code>", parse_mode="HTML")
            return
        code = parts[1].strip()
        cursor.execute(
            "UPDATE alliance_group SET control_chat_id=NULL WHERE code=? AND control_chat_id=?",
            (code, chat_id)
        )
        conn.commit()
        await message.reply("✅ Guruh nazoratdan chiqarildi.")
        return

    group = get_alliance_group_by_chat(chat_id)
    if not group:
        await message.reply("❌ Bu guruh ittifoqqa ulanmagan.")
        return
    cursor.execute("DELETE FROM alliance_group WHERE chat_id=?", (chat_id,))
    cursor.execute("DELETE FROM alliance_blacklist WHERE chat_id=?", (chat_id,))
    conn.commit()
    await message.reply("✅ Guruh ittifoqdan chiqarildi. Maxsus reyd himoyasi va uzunlik chegarasi o'chirildi.")

@router.message(Command("ruxsat"), F.chat.type.in_(["group", "supergroup"]))
async def ruxsat_command(message: types.Message):
    """Guruh admini boshqa foydalanuvchining xabariga reply qilib, uni
    shu guruhdagi anti-reyd/so'kish/uzunlik filtridan ozod qiladi."""
    chat_id = message.chat.id
    actor_id = message.from_user.id

    if not await is_chat_admin(chat_id, actor_id):
        await message.reply("⛔ Bu buyruqni faqat guruh adminlari ishlata oladi.")
        return

    if not message.reply_to_message or not message.reply_to_message.from_user:
        await message.reply("ℹ️ /ruxsat buyrug'ini ozod qilmoqchi bo'lgan foydalanuvchining xabariga reply qilib yuboring.")
        return

    target = message.reply_to_message.from_user
    if target.is_bot:
        await message.reply("⛔ Botlarga ruxsat berib bo'lmaydi.")
        return

    grant_permission(chat_id, target.id, actor_id)
    name = target.full_name or target.username or str(target.id)
    await message.reply(f"✅ {name} shu guruhda filtrdan ozod qilindi.\nBekor qilish uchun: /ruxsatbekor (unga reply qilib)")

@router.message(Command("ruxsatbekor"), F.chat.type.in_(["group", "supergroup"]))
async def ruxsatbekor_command(message: types.Message):
    """Avval /ruxsat orqali berilgan ozodlikni bekor qiladi."""
    chat_id = message.chat.id
    actor_id = message.from_user.id

    if not await is_chat_admin(chat_id, actor_id):
        await message.reply("⛔ Bu buyruqni faqat guruh adminlari ishlata oladi.")
        return

    if not message.reply_to_message or not message.reply_to_message.from_user:
        await message.reply("ℹ️ /ruxsatbekor buyrug'ini ruxsati bekor qilinadigan foydalanuvchining xabariga reply qilib yuboring.")
        return

    target = message.reply_to_message.from_user
    removed = revoke_permission(chat_id, target.id)
    name = target.full_name or target.username or str(target.id)
    if removed:
        await message.reply(f"✅ {name} uchun ruxsat bekor qilindi. Endi filtrlar unga ham qo'llanadi.")
    else:
        await message.reply(f"ℹ️ {name} uchun avval /ruxsat berilmagan edi.")

# ============ QO'SHILISH SO'ROVLARI (JOIN REQUESTS) ============
# Guruh "faqat admin tasdiqlasa qo'shiladi" rejimida bo'lsa, Telegram bunday
# so'rovlarni chat_join_request event orqali yuboradi. Agar shu guruh biror
# nazorat guruhiga ulangan bo'lsa, so'rov o'sha yerga xabar qilinadi va
# faqat can_change_info huquqli admin /qabul yoki /rad orqali hal qiladi.
@router.chat_join_request()
async def handle_join_request(update: types.ChatJoinRequest):
    chat_id = update.chat.id
    user = update.from_user

    alliance_row = get_alliance_group_by_chat(chat_id)
    if not alliance_row or not alliance_row[3]:
        return  # guruh nazorat guruhiga ulanmagan - so'rovni admin Telegramning o'zida ko'radi
    control_chat_id = alliance_row[3]

    existing_msg_id = get_open_notify_message(control_chat_id, user.id)

    cursor.execute(
        "INSERT OR REPLACE INTO join_requests "
        "(user_id, chat_id, control_chat_id, notify_message_id, status, requested_at) "
        "VALUES (?, ?, ?, ?, 'pending', CURRENT_TIMESTAMP)",
        (user.id, chat_id, control_chat_id, existing_msg_id)
    )
    conn.commit()

    name = user.full_name or (f"@{user.username}" if user.username else str(user.id))
    pending_groups = get_pending_group_titles(control_chat_id, user.id)
    text = (
        f"📥 <b>Qo'shilish so'rovi</b>\n\n"
        f"👤 {name} (ID: <code>{user.id}</code>)\n"
        f"🏷 So'rov yuborilgan guruh(lar):\n" +
        "\n".join(f"  • {t}" for t in pending_groups) +
        f"\n\n✅ Qabul qilish uchun shu xabarga <code>/qabul</code>,\n"
        f"❌ rad etish uchun <code>/rad</code> deb reply qiling.\n"
        f"<i>(faqat guruh ma'lumotini o'zgartira oladigan admin ishlata oladi)</i>"
    )

    try:
        if existing_msg_id:
            await bot.edit_message_text(chat_id=control_chat_id, message_id=existing_msg_id, text=text, parse_mode="HTML")
        else:
            sent = await bot.send_message(control_chat_id, text, parse_mode="HTML")
            cursor.execute(
                "UPDATE join_requests SET notify_message_id=? "
                "WHERE user_id=? AND control_chat_id=? AND status='pending'",
                (sent.message_id, user.id, control_chat_id)
            )
            conn.commit()
    except Exception as e:
        logger.error(f"Nazorat guruhiga qo'shilish so'rovi xabarini yuborishda xatolik: {e}")

async def _process_join_decision(message: types.Message, approve: bool):
    chat_id = message.chat.id
    actor_id = message.from_user.id

    if not await has_change_info_right(chat_id, actor_id):
        await message.reply("⛔ Bu buyruqni faqat guruh ma'lumotini o'zgartira oladigan admin ishlata oladi.")
        return

    if not message.reply_to_message:
        await message.reply("ℹ️ Ushbu buyruqni tegishli qo'shilish so'rovi xabariga reply qilib yuboring.")
        return

    notify_msg_id = message.reply_to_message.message_id
    cursor.execute(
        "SELECT user_id, chat_id FROM join_requests "
        "WHERE control_chat_id=? AND notify_message_id=? AND status='pending'",
        (chat_id, notify_msg_id)
    )
    rows = cursor.fetchall()
    if not rows:
        await message.reply("ℹ️ Bu xabarga tegishli faol qo'shilish so'rovi topilmadi.")
        return

    user_id = rows[0][0]
    ok, fail = 0, 0
    for _, group_chat_id in rows:
        try:
            if approve:
                await bot.approve_chat_join_request(group_chat_id, user_id)
            else:
                await bot.decline_chat_join_request(group_chat_id, user_id)
            ok += 1
        except Exception as e:
            logger.error(f"Join request {'qabul' if approve else 'rad'} qilishda xatolik: {e}")
            fail += 1

    cursor.execute(
        "UPDATE join_requests SET status=? WHERE control_chat_id=? AND notify_message_id=?",
        ("approved" if approve else "declined", chat_id, notify_msg_id)
    )
    conn.commit()

    verb = "qabul qilindi ✅" if approve else "rad etildi ❌"
    result_text = f"{ok} ta guruhda so'rov {verb}."
    if fail:
        result_text += f" ({fail} tasida xatolik yuz berdi)"

    try:
        old_text = message.reply_to_message.html_text or message.reply_to_message.text or ""
        await message.reply_to_message.edit_text(old_text + f"\n\n{result_text}", parse_mode="HTML")
    except Exception:
        pass
    await message.reply(result_text)

@router.message(Command("qabul"), F.chat.type.in_(["group", "supergroup"]))
async def qabul_command(message: types.Message):
    await _process_join_decision(message, approve=True)

@router.message(Command("rad"), F.chat.type.in_(["group", "supergroup"]))
async def rad_command(message: types.Message):
    await _process_join_decision(message, approve=False)

@router.message(Command("blackwords"), F.chat.type.in_(["group", "supergroup"]))
async def blackwords_command(message: types.Message):
    chat_id = message.chat.id
    user_id = message.from_user.id
    try:
        member = await bot.get_chat_member(chat_id, user_id)
    except Exception:
        return
    allowed = member.status == "creator" or (
        member.status == "administrator" and getattr(member, "can_change_info", False)
    )
    if not allowed:
        await message.reply("❌ Bu buyruq faqat guruh ma'lumotlarini o'zgartira oladigan adminlar uchun.")
        return

    me = await bot.get_me()
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="🔓 Botga o'tish", url=f"https://t.me/{me.username}?start=blackwords"))
    await message.reply(
        "🚫 Qora ro'yxatni boshqarish uchun bot bilan shaxsiy chatga o'ting:",
        reply_markup=builder.as_markup()
    )

# --- Shaxsiy chatda: Qora ro'yxat menyusi ---
@router.callback_query(F.data == "blackwords_menu")
async def blackwords_menu(callback_query: types.CallbackQuery, state: FSMContext):
    await state.clear()
    groups = await get_editable_alliance_groups(callback_query.from_user.id)
    if not groups:
        await callback_query.message.edit_text(
            "🚫 Siz guruh ma'lumotlarini o'zgartira oladigan ittifoq guruhi topilmadi.",
            reply_markup=main_kb(callback_query.from_user.id)
        )
        await callback_query.answer()
        return
    await callback_query.message.edit_text(
        "🚫 <b>Qora ro'yxat</b>\n\nQaysi guruh uchun so'zlarni boshqarmoqchisiz?",
        parse_mode="HTML",
        reply_markup=get_blackwords_group_list_keyboard(groups)
    )
    await callback_query.answer()

@router.callback_query(F.data.startswith("bw_group_"))
async def blackwords_group_selected(callback_query: types.CallbackQuery):
    chat_id = int(callback_query.data.rsplit("_", 1)[-1])
    words = get_custom_blacklist(chat_id)
    await callback_query.message.edit_text(
        render_blackwords_text(words), parse_mode="HTML",
        reply_markup=get_blackwords_edit_keyboard(chat_id, words)
    )
    await callback_query.answer()

@router.callback_query(F.data.startswith("bw_del_"))
async def blackwords_delete_word(callback_query: types.CallbackQuery):
    _, _, chat_id_str, word = callback_query.data.split("_", 3)
    chat_id = int(chat_id_str)
    cursor.execute("DELETE FROM alliance_blacklist WHERE chat_id=? AND word=?", (chat_id, word))
    conn.commit()
    words = get_custom_blacklist(chat_id)
    await callback_query.message.edit_text(
        render_blackwords_text(words), parse_mode="HTML",
        reply_markup=get_blackwords_edit_keyboard(chat_id, words)
    )
    await callback_query.answer("✅ So'z o'chirildi!")

@router.callback_query(F.data.startswith("bw_add_"))
async def blackwords_add_prompt(callback_query: types.CallbackQuery, state: FSMContext):
    chat_id = int(callback_query.data.rsplit("_", 1)[-1])
    await state.update_data(bw_chat_id=chat_id)
    await state.set_state(AccountStates.waiting_blackword)
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data=f"bw_group_{chat_id}"))
    await callback_query.message.edit_text(
        "✍️ Qo'shmoqchi bo'lgan so'zni yozing:",
        reply_markup=builder.as_markup()
    )
    await callback_query.answer()

@router.message(AccountStates.waiting_blackword)
async def blackwords_add_word(message: types.Message, state: FSMContext):
    data = await state.get_data()
    chat_id = data.get("bw_chat_id")
    await state.clear()
    if not chat_id:
        return
    word = (message.text or "").strip().lower()
    if word:
        cursor.execute("INSERT OR IGNORE INTO alliance_blacklist (chat_id, word) VALUES (?, ?)", (chat_id, word))
        conn.commit()
    words = get_custom_blacklist(chat_id)
    await message.answer(
        "✅ So'z qo'shildi!\n\n" + render_blackwords_text(words),
        parse_mode="HTML",
        reply_markup=get_blackwords_edit_keyboard(chat_id, words)
    )

# ============ INLINE KEYBOARDLAR ============
def get_main_keyboard(is_connected: bool = False):
    """Akkaunt ULANMAGUNCHA faqat 'Akkauntni ulash' tugmasi ko'rinadi.
    Akkaunt ulangandan keyin barcha bo'limlar ochiladi."""
    builder = InlineKeyboardBuilder()
    if not is_connected:
        builder.row(InlineKeyboardButton(text="🔗 Akkauntni ulash", callback_data="connect_account"))
        return builder.as_markup()

    builder.add(
        InlineKeyboardButton(text="👤 FunStat", callback_data="funstat_menu"),
        InlineKeyboardButton(text="👁 View Once", callback_data="view_once_menu"),
        InlineKeyboardButton(text="👥 Guruhlar", callback_data="group_management"),
        InlineKeyboardButton(text="🔨 A'zolar", callback_data="member_management"),
        InlineKeyboardButton(text="🤝 Ittifoq", callback_data="alliance_menu"),
        InlineKeyboardButton(text="🚫 Qora ro'yxat", callback_data="blackwords_menu"),
        InlineKeyboardButton(text="⚙️ Sozlamalar", callback_data="settings_menu"),
    )
    builder.adjust(2)
    return builder.as_markup()

def main_kb(user_id: int):
    """get_main_keyboard uchun qulay yordamchi - foydalanuvchining
    userbot ulanganligini aniqlaydi. Avval xotiradagi active_clients
    tekshiriladi (tezkor), agar u yerda bo'lmasa - ma'lumotlar bazasidagi
    saqlangan sessiyaga qaraladi (masalan, bot qayta ishga tushgandan keyin,
    userbot hali qayta ulanmagan bo'lsa ham, tugmalar noto'g'ri "ulanmagan"
    holatni ko'rsatib qolmasligi uchun)."""
    if user_id in active_clients:
        return get_main_keyboard(True)
    cursor.execute("SELECT is_active FROM users WHERE user_id=?", (user_id,))
    row = cursor.fetchone()
    is_connected = bool(row and row[0])
    return get_main_keyboard(is_connected)

# ============ MAJBURIY OBUNA ============
def get_required_channels() -> List[tuple]:
    """Qaytaradi: [(chat_id, username, title, invite_link), ...]"""
    cursor.execute("SELECT chat_id, username, title, invite_link FROM required_channels")
    return cursor.fetchall()

async def get_unsubscribed_channels(user_id: int) -> List[tuple]:
    """Foydalanuvchi hali obuna bo'lmagan majburiy kanallarni qaytaradi."""
    unsubscribed = []
    for chat_id, username, title, invite_link in get_required_channels():
        try:
            member = await bot.get_chat_member(chat_id, user_id)
            if member.status in ("left", "kicked"):
                unsubscribed.append((chat_id, username, title, invite_link))
        except Exception as e:
            # Bot kanalda admin bo'lmasa yoki boshqa xatolik - tekshirib bo'lmaydi,
            # foydalanuvchini bloklamaslik uchun o'tkazib yuboramiz, lekin logga yozamiz
            logger.error(f"Majburiy obuna tekshirishda xatolik (chat={chat_id}): {e}")
    return unsubscribed

def get_force_sub_keyboard(unsubscribed: List[tuple]):
    builder = InlineKeyboardBuilder()
    for chat_id, username, title, invite_link in unsubscribed:
        url = invite_link or (f"https://t.me/{username}" if username else None)
        if url:
            builder.row(InlineKeyboardButton(text=f"📢 {title or username or chat_id}", url=url))
    builder.row(InlineKeyboardButton(text="✅ Obuna bo'ldim", callback_data="check_force_sub"))
    return builder.as_markup()

async def enforce_force_sub(message_or_callback) -> bool:
    """True qaytarsa - foydalanuvchi hammasiga obuna (davom etsa bo'ladi).
    False qaytarsa - obuna bo'lmagan kanallar ro'yxati allaqachon yuborildi,
    handler shu yerda to'xtashi kerak."""
    if isinstance(message_or_callback, types.CallbackQuery):
        user_id = message_or_callback.from_user.id
        target = message_or_callback.message
    else:
        user_id = message_or_callback.from_user.id
        target = message_or_callback

    if not get_required_channels():
        return True

    unsubscribed = await get_unsubscribed_channels(user_id)
    if not unsubscribed:
        return True

    text = (
        "🔒 <b>Botdan foydalanish uchun quyidagi kanal(lar)ga obuna bo'ling:</b>\n\n"
        "Obuna bo'lgach, <b>✅ Obuna bo'ldim</b> tugmasini bosing."
    )
    try:
        await bot.send_message(user_id, text, parse_mode="HTML", reply_markup=get_force_sub_keyboard(unsubscribed))
    except Exception as e:
        logger.error(f"Majburiy obuna xabarini yuborishda xatolik: {e}")
    return False

@router.callback_query(F.data == "check_force_sub")
async def check_force_sub(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    unsubscribed = await get_unsubscribed_channels(user_id)
    if unsubscribed:
        await callback_query.answer("❌ Hali barcha kanallarga obuna bo'lmadingiz!", show_alert=True)
        try:
            await callback_query.message.edit_reply_markup(reply_markup=get_force_sub_keyboard(unsubscribed))
        except Exception:
            pass
        return
    await callback_query.answer("✅ Rahmat!")
    await callback_query.message.edit_text(
        "✅ <b>Obuna tasdiqlandi!</b>\n\nEndi botdan to'liq foydalanishingiz mumkin. /start bosing.",
        parse_mode="HTML"
    )

@router.message(Command("majburiy"), F.chat.type == "private")
async def majburiy_command(message: types.Message):
    """Faqat admin. Foydalanish:
    /majburiy @kanal_username  - kanalni qo'shish (bot kanalda admin bo'lishi shart)
    /majburiy https://t.me/+xxxxx Kanal nomi - shaxsiy kanal uchun invite link bilan
    /majburiy off @kanal_username - kanalni olib tashlash
    /majburiy list - ro'yxatni ko'rish"""
    user_id = message.from_user.id
    if user_id not in ADMIN_IDS:
        return

    parts = (message.text or "").split(maxsplit=2)
    if len(parts) < 2:
        await message.reply(
            "ℹ️ <b>Foydalanish:</b>\n"
            "<code>/majburiy @kanal_username</code> — ochiq kanal qo'shish\n"
            "<code>/majburiy https://t.me/+xxxx Kanal nomi</code> — yopiq kanal (invite link bilan)\n"
            "<code>/majburiy off @kanal_username</code> — olib tashlash\n"
            "<code>/majburiy list</code> — ro'yxat",
            parse_mode="HTML"
        )
        return

    sub = parts[1].strip()

    if sub == "list":
        channels = get_required_channels()
        if not channels:
            await message.reply("📋 Majburiy obuna kanallari hali qo'shilmagan.")
            return
        text = "📋 <b>Majburiy obuna kanallari:</b>\n\n"
        for chat_id, username, title, invite_link in channels:
            ident = f"@{username}" if username else (invite_link or str(chat_id))
            text += f"• {title or ident} — {ident}\n"
        await message.reply(text, parse_mode="HTML")
        return

    if sub == "off":
        if len(parts) < 3:
            await message.reply("ℹ️ Foydalanish: <code>/majburiy off @kanal_username</code>", parse_mode="HTML")
            return
        target = parts[2].strip().lstrip('@')
        cursor.execute("DELETE FROM required_channels WHERE username=?", (target,))
        conn.commit()
        await message.reply(f"✅ @{target} majburiy obunadan olib tashlandi (agar mavjud bo'lsa).")
        return

    # Qo'shish
    invite_link = None
    title = None
    username = None

    if sub.startswith("https://t.me/+") or sub.startswith("http://t.me/+") or sub.startswith("t.me/+"):
        # Yopiq kanal - faqat invite link orqali, chat_id'ni bilish uchun botni shu linkka
        # taklif qilib qo'shish kerak bo'lishi mumkin; shuning uchun admin nomni ham yozadi
        invite_link = sub if sub.startswith("http") else f"https://{sub}"
        title = parts[2].strip() if len(parts) > 2 else invite_link
        # Yopiq kanal uchun chat_id avtomatik aniqlanmaydi - admin botni shu kanalga
        # admin qilib qo'shgach, bot birinchi update orqali chat_id'ni bilib oladi.
        # Hozircha faqat link asosida ro'yxatga qo'shamiz (tekshiruv chat_id kerak, shuning
        # uchun bunday kanal uchun a'zolikni AVTOMATIK tekshira olmaymiz - ogohlantiramiz).
        await message.reply(
            "⚠️ Yopiq kanal uchun avtomatik a'zolik tekshiruvi ishlamaydi (Telegram username'siz "
            "kanal a'zoligini bot orqali tekshirishga imkon bermaydi). Kanal faqat tugma sifatida "
            "ko'rsatiladi, lekin 'obuna bo'lganmi' deb avtomatik bloklanmaydi.\n\n"
            "Iltimos, iloji bo'lsa ochiq (@username) kanal qo'shing - to'liq ishlaydi.",
        )
        return
    else:
        username = sub.lstrip('@')
        try:
            chat = await bot.get_chat(f"@{username}")
        except Exception as e:
            await message.reply(f"❌ Kanal topilmadi yoki bot u yerda admin emas: {e}")
            return
        try:
            bot_member = await bot.get_chat_member(chat.id, (await bot.get_me()).id)
            if bot_member.status not in ("administrator", "creator"):
                await message.reply("❌ Bot bu kanalda admin emas! Avval botni kanalga admin qilib qo'shing.")
                return
        except Exception as e:
            await message.reply(f"❌ Tekshirishda xatolik: {e}")
            return
        title = chat.title
        chat_id_val = chat.id

        cursor.execute(
            "INSERT OR REPLACE INTO required_channels (chat_id, username, title, invite_link, added_by) VALUES (?, ?, ?, ?, ?)",
            (chat_id_val, username, title, None, user_id)
        )
        conn.commit()
        await message.reply(f"✅ <b>{title}</b> (@{username}) majburiy obunaga qo'shildi.", parse_mode="HTML")


    builder = InlineKeyboardBuilder()
    builder.add(
        InlineKeyboardButton(text="📊 Ultra statistika", callback_data="get_stats"),
        InlineKeyboardButton(text="👁 Kuzatish", callback_data="start_watching"),
    )
    builder.adjust(2)
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
    return builder.as_markup()

def get_view_once_keyboard():
    builder = InlineKeyboardBuilder()
    builder.add(
        InlineKeyboardButton(text="📊 Ma'lumotlarim", callback_data="my_info"),
        InlineKeyboardButton(text="📥 Eskilarni yuklash", callback_data="load_old_messages"),
        InlineKeyboardButton(text="🔄 Qayta ulash", callback_data="reconnect"),
        InlineKeyboardButton(text="❌ O'chirish", callback_data="delete_account"),
    )
    builder.adjust(2)
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
    return builder.as_markup()

def get_settings_keyboard():
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="ℹ️ Yordam", callback_data="help"))
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
    return builder.as_markup()

def get_cancel_keyboard():
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="❌ Bekor qilish", callback_data="cancel_action"))
    return builder.as_markup()

def get_phone_request_keyboard():
    """Telefon raqamini kontakt sifatida ulashish uchun pastki klaviatura."""
    builder = ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📱 Raqamni ulashish", request_contact=True)]],
        resize_keyboard=True,
        one_time_keyboard=True
    )
    return builder

# ============ KOD KIRITISH - INLINE RAQAMLI KLAVIATURA ============
CODE_MAX_LENGTH = 5  # Telegram login kodi odatda 5 xonali

def get_code_keyboard(current_code: str):
    builder = InlineKeyboardBuilder()
    for d in ["1", "2", "3", "4", "5", "6", "7", "8", "9"]:
        builder.add(InlineKeyboardButton(text=d, callback_data=f"code_digit_{d}"))
    builder.adjust(3)
    builder.row(
        InlineKeyboardButton(text="⌫", callback_data="code_backspace"),
        InlineKeyboardButton(text="0", callback_data="code_digit_0"),
        InlineKeyboardButton(text="✅ Tasdiqlash", callback_data="code_confirm"),
    )
    builder.row(InlineKeyboardButton(text="❌ Bekor qilish", callback_data="cancel_action"))
    return builder.as_markup()

def render_code_text(current_code: str, error: Optional[str] = None) -> str:
    masked = " ".join(current_code) if current_code else "—"
    text = (
        "🔐 <b>Telegram'dan kelgan kodni kiriting</b>\n\n"
        f"Kiritilgan: <code>{masked}</code> ({len(current_code)}/{CODE_MAX_LENGTH})\n\n"
        "Pastdagi raqamli tugmalar orqali kiriting 👇"
    )
    if error:
        text = f"❌ <b>{error}</b>\nQaytadan kiriting.\n\n" + text
    return text

# ============ VIEW ONCE ANIQLASH ============
def is_view_once_media(media) -> bool:
    if isinstance(media, MessageMediaPhoto):
        return bool(getattr(media, 'ttl_seconds', None))

    if isinstance(media, MessageMediaDocument):
        return bool(getattr(media, 'ttl_seconds', None))

    return False

def get_media_type(media) -> Optional[str]:
    if isinstance(media, MessageMediaPhoto):
        return "photo"
    elif isinstance(media, MessageMediaDocument):
        if hasattr(media.document, 'attributes'):
            for attr in media.document.attributes:
                if isinstance(attr, DocumentAttributeVideo):
                    return "video"
                elif isinstance(attr, DocumentAttributeAnimated):
                    return "gif"
                elif isinstance(attr, DocumentAttributeAudio):
                    return "audio"
                elif isinstance(attr, DocumentAttributeFilename):
                    return "document"
    return None

def get_display_name(entity):
    if entity is None:
        return "Noma'lum", None, None

    entity_id = getattr(entity, 'id', None)
    username = getattr(entity, 'username', None)

    if getattr(entity, 'first_name', None) is not None or hasattr(entity, 'first_name'):
        first = getattr(entity, 'first_name', '') or ''
        last = getattr(entity, 'last_name', '') or ''
        name = f"{first} {last}".strip() or "Noma'lum"
    elif getattr(entity, 'title', None):
        name = entity.title
    else:
        name = "Noma'lum"

    if username:
        name += f" (@{username})"

    return name, entity_id, username

def get_media_emoji(media_type: str) -> str:
    emojis = {"photo": "📷", "video": "🎬", "gif": "🎪", "audio": "🎵", "document": "📄"}
    return emojis.get(media_type, "📁")

def get_media_name(media_type: str) -> str:
    names = {"photo": "Rasm", "video": "Video", "gif": "GIF", "audio": "Audio", "document": "Hujjat"}
    return names.get(media_type, "Fayl")

# ============ FAOLLIK TEKSHIRISH (LAST SEEN) ============
INACTIVE_DAYS_THRESHOLD = 10

def is_inactive_account(participant) -> bool:
    if getattr(participant, 'deleted', False):
        return True

    status = getattr(participant, 'status', None)
    if status is None:
        return False

    if isinstance(status, UserStatusOffline):
        last_seen = status.was_online
        if last_seen:
            now = datetime.now(last_seen.tzinfo) if last_seen.tzinfo else datetime.now()
            if now - last_seen > timedelta(days=INACTIVE_DAYS_THRESHOLD):
                return True
        return False

    if isinstance(status, UserStatusLastMonth):
        return True

    return False

# ============ TO'LIQ FUNSTAT - KENGAYTIRILGAN ============
async def get_ultra_user_stats(client: TelegramClient, entity) -> str:
    """ENG TO'LIQ foydalanuvchi statistikasi"""
    try:
        stats_text = ""
        
        if isinstance(entity, User):
            name = f"{entity.first_name} {entity.last_name if entity.last_name else ''}"
            username = f"@{entity.username}" if entity.username else "Yo'q"
            user_id = entity.id
            
            stats_text += "📊 <b>ULTRA FUNSTAT STATISTIKASI</b>\n\n"
            stats_text += "━━━━━━━━━━━━━━━━━━━━\n"
            stats_text += "👤 <b>ASOSIY MA'LUMOTLAR</b>\n"
            stats_text += "━━━━━━━━━━━━━━━━━━━━\n"
            stats_text += f"📛 <b>Ism:</b> {name}\n"
            stats_text += f"🔖 <b>Joriy Username:</b> {username}\n"
            stats_text += f"🆔 <b>ID:</b> <code>{user_id}</code>\n"
            
            if entity.phone:
                stats_text += f"📱 <b>Telefon:</b> <code>{entity.phone}</code>\n"
            
            stats_text += "\n━━━━━━━━━━━━━━━━━━━━\n"
            stats_text += "📈 <b>STATUS</b>\n"
            stats_text += "━━━━━━━━━━━━━━━━━━━━\n"
            
            is_bot = "Ha" if entity.bot else "Yo'q"
            is_verified = "Ha" if entity.verified else "Yo'q"
            is_premium = "Ha" if entity.premium else "Yo'q"
            is_scam = "Ha" if entity.scam else "Yo'q"
            is_fake = "Ha" if entity.fake else "Yo'q"
            
            stats_text += f"🤖 <b>Bot:</b> {is_bot}\n"
            stats_text += f"✅ <b>Tasdiqlangan:</b> {is_verified}\n"
            stats_text += f"⭐ <b>Premium:</b> {is_premium}\n"
            stats_text += f"⚠️ <b>Scam:</b> {is_scam}\n"
            stats_text += f"⚠️ <b>Fake:</b> {is_fake}\n"
            
            if entity.status:
                if hasattr(entity.status, 'was_online'):
                    last_seen = entity.status.was_online
                    stats_text += f"🕐 <b>Oxirgi faollik:</b> {last_seen.strftime('%Y-%m-%d %H:%M:%S')}\n"
                elif hasattr(entity.status, 'expires'):
                    stats_text += f"⭐ <b>Premium tugashi:</b> {entity.status.expires.strftime('%Y-%m-%d')}\n"
            
            stats_text += "\n━━━━━━━━━━━━━━━━━━━━\n"
            stats_text += "🌐 <b>BARCHA GURUHLAR VA KANALLAR</b>\n"
            stats_text += "━━━━━━━━━━━━━━━━━━━━\n"
            
            dialogs = await client.get_dialogs(limit=500)
            
            common_groups = []
            common_channels = []
            
            for dialog in dialogs:
                try:
                    if dialog.is_group:
                        try:
                            participants = await client.get_participants(dialog.entity, limit=200)
                            found = False
                            for p in participants:
                                if p.id == user_id:
                                    found = True
                                    break
                            
                            if found:
                                group_info = {
                                    'name': dialog.name,
                                    'members': dialog.entity.participants_count if hasattr(dialog.entity, 'participants_count') else 0,
                                    'username': dialog.entity.username if hasattr(dialog.entity, 'username') else '',
                                    'private': not bool(getattr(dialog.entity, 'username', None))
                                }
                                common_groups.append(group_info)
                        except:
                            pass
                    
                    elif dialog.is_channel:
                        try:
                            participants = await client.get_participants(dialog.entity, limit=200)
                            found = False
                            for p in participants:
                                if p.id == user_id:
                                    found = True
                                    break
                            
                            if found:
                                channel_info = {
                                    'name': dialog.name,
                                    'subscribers': dialog.entity.participants_count if hasattr(dialog.entity, 'participants_count') else 0,
                                    'username': dialog.entity.username if hasattr(dialog.entity, 'username') else '',
                                    'private': not bool(getattr(dialog.entity, 'username', None))
                                }
                                common_channels.append(channel_info)
                        except:
                            pass
                            
                except:
                    continue
            
            if common_groups:
                stats_text += f"\n👥 <b>Guruhlar ({len(common_groups)} ta):</b>\n"
                for i, group in enumerate(common_groups[:15], 1):
                    username_str = f" @{group['username']}" if group['username'] else ""
                    stats_text += f"{i}. {group['name']}{username_str} - {group['members']} a'zo\n"
            else:
                stats_text += "\n👥 <b>Guruhlar:</b> Topilmadi\n"
            
            if common_channels:
                stats_text += f"\n📢 <b>Kanallar ({len(common_channels)} ta):</b>\n"
                for i, channel in enumerate(common_channels[:15], 1):
                    username_str = f" @{channel['username']}" if channel['username'] else ""
                    stats_text += f"{i}. {channel['name']}{username_str} - {channel['subscribers']} obunachi\n"
            else:
                stats_text += "\n📢 <b>Kanallar:</b> Topilmadi\n"
            
            stats_text += "\n━━━━━━━━━━━━━━━━━━━━\n"
            stats_text += "📊 <b>FAOLLIK TAHLILI</b>\n"
            stats_text += "━━━━━━━━━━━━━━━━━━━━\n"
            
            try:
                messages = await client.get_messages(entity, limit=100)
                if messages:
                    text_count = sum(1 for m in messages if not m.media)
                    photo_count = sum(1 for m in messages if m.photo)
                    video_count = sum(1 for m in messages if m.video)
                    
                    stats_text += "📝 <b>Oxirgi 100 xabar:</b>\n"
                    stats_text += f"   💬 Matnli: {text_count}\n"
                    stats_text += f"   📷 Rasmlar: {photo_count}\n"
                    stats_text += f"   🎬 Videolar: {video_count}\n"
            except:
                pass
            
            stats_text += "\n━━━━━━━━━━━━━━━━━━━━\n"
            stats_text += "📜 <b>USERNAME TARIXI</b>\n"
            stats_text += "━━━━━━━━━━━━━━━━━━━━\n"
            
            cursor.execute(
                "SELECT username, found_at FROM username_history WHERE target_user_id=? ORDER BY found_at DESC LIMIT 10",
                (user_id,)
            )
            history = cursor.fetchall()
            
            if history:
                stats_text += "📝 <b>Avvalgi usernamelar:</b>\n"
                for old_username, found_at in history:
                    stats_text += f"   • @{old_username} (topilgan: {found_at})\n"
            else:
                stats_text += "📝 Avvalgi usernamelar topilmadi\n"
            
            if entity.username:
                cursor.execute(
                    "INSERT OR IGNORE INTO username_history (user_id, target_user_id, username) VALUES (?, ?, ?)",
                    (0, user_id, entity.username)
                )
                conn.commit()
            
        elif isinstance(entity, (Channel, Chat)):
            try:
                if isinstance(entity, Channel):
                    full = await client(GetFullChannelRequest(entity))
                    title = entity.title
                    participants_count = full.full_chat.participants_count or 0
                else:
                    full = await client(GetFullChatRequest(entity.id))
                    title = entity.title
                    participants_count = full.full_chat.participants_count or 0
                
                stats_text += "📊 <b>GURUH/KANAL STATISTIKASI</b>\n\n"
                stats_text += "━━━━━━━━━━━━━━━━━━━━\n"
                stats_text += f"📛 <b>Nomi:</b> {title}\n"
                
                if hasattr(entity, 'username') and entity.username:
                    stats_text += f"🔖 <b>Username:</b> @{entity.username}\n"
                else:
                    stats_text += "🔒 <b>Yashirin:</b> Ha\n"
                
                stats_text += f"🆔 <b>ID:</b> <code>{entity.id}</code>\n"
                stats_text += f"👥 <b>A'zolar:</b> {participants_count}\n"
                
            except Exception as e:
                stats_text += f"\n❌ Xatolik: {str(e)}"
        
        return stats_text
        
    except Exception as e:
        logger.error(f"Statistika olishda xatolik: {e}")
        return f"❌ Statistika olishda xatolik: {str(e)}"

# ============ MEDIA YUBORISH ============
def get_profile_keyboard(sender_id: Optional[int], sender_username: Optional[str]):
    if not sender_id:
        return None
    
    builder = InlineKeyboardBuilder()
    if sender_username:
        url = f"https://t.me/{sender_username}"
    else:
        url = f"tg://user?id={sender_id}"
    
    builder.row(InlineKeyboardButton(text="👤 Profilga o'tish", url=url))
    return builder.as_markup()

async def send_media_with_caption(user_id, file_path, media_type, sender_name, chat_name, date_str,
                                    sender_id: Optional[int] = None, sender_username: Optional[str] = None):
    try:
        id_line = f"🆔 <b>Yuboruvchi ID:</b> <code>{sender_id}</code>\n" if sender_id else ""
        caption = (
            f"{get_media_emoji(media_type)} <b>View Once {get_media_name(media_type)}</b>\n"
            f"👤 <b>Kimdan:</b> {sender_name}\n"
            f"{id_line}"
            f"💬 <b>Chat:</b> {chat_name}\n"
            f"📅 <b>Qachon:</b> {date_str}"
        )
        
        reply_markup = get_profile_keyboard(sender_id, sender_username)
        file_size = os.path.getsize(file_path)
        
        if media_type == 'photo':
            await bot.send_photo(user_id, types.FSInputFile(file_path), caption=caption, parse_mode="HTML", reply_markup=reply_markup)
        elif media_type == 'video':
            if file_size > 50 * 1024 * 1024:
                await bot.send_message(user_id, caption, parse_mode="HTML", reply_markup=reply_markup)
                await bot.send_document(user_id, types.FSInputFile(file_path))
            else:
                await bot.send_video(user_id, types.FSInputFile(file_path), caption=caption, parse_mode="HTML", reply_markup=reply_markup)
        elif media_type == 'gif':
            await bot.send_animation(user_id, types.FSInputFile(file_path), caption=caption, parse_mode="HTML", reply_markup=reply_markup)
        elif media_type == 'audio':
            await bot.send_audio(user_id, types.FSInputFile(file_path), caption=caption, parse_mode="HTML", reply_markup=reply_markup)
        else:
            await bot.send_document(user_id, types.FSInputFile(file_path), caption=caption, parse_mode="HTML", reply_markup=reply_markup)
        
        return True
        
    except Exception as e:
        logger.error(f"Yuborishda xatolik: {e}")
        await bot.send_message(user_id, f"❌ Xatolik: {str(e)}")
        return False

async def download_and_send_media(event, user_id, chat, sender, media_type):
    try:
        user_download_dir = DOWNLOADS_DIR / str(user_id)
        user_download_dir.mkdir(exist_ok=True)
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        file_path = await event.message.download_media(
            file=str(user_download_dir / f"view_once_{timestamp}")
        )
        
        if not file_path:
            await bot.send_message(user_id, "❌ Faylni yuklab bo'lmadi!")
            return
        
        chat_name, _, _ = get_display_name(chat)
        if chat_name == "Noma'lum":
            chat_name = "Shaxsiy chat"
        
        sender_name, sender_id, sender_username = get_display_name(sender)
        
        date_str = event.message.date.strftime('%Y-%m-%d %H:%M:%S')
        
        success = await send_media_with_caption(
            user_id, file_path, media_type, sender_name, chat_name, date_str,
            sender_id=sender_id, sender_username=sender_username
        )
        
        if success:
            cursor.execute(
                """INSERT OR IGNORE INTO saved_messages 
                   (user_id, message_id, chat_id, media_type, file_path) 
                   VALUES (?, ?, ?, ?, ?)""",
                (user_id, event.message.id, getattr(chat, 'id', 0), media_type, file_path)
            )
            conn.commit()
            
            if os.path.exists(file_path):
                os.remove(file_path)
                
    except Exception as e:
        logger.error(f"Yuklashda xatolik: {e}")
        try:
            await bot.send_message(user_id, f"❌ Xatolik: {str(e)}")
        except Exception:
            pass

# ============ USERBOT ============
async def start_userbot(client: TelegramClient, user_id: int):
    @client.on(events.NewMessage(incoming=True))
    async def handle_new_message(event):
        try:
            if event.message.out or not event.message.media:
                return
            
            if not is_view_once_media(event.message.media):
                return
            
            media_type = get_media_type(event.message.media)
            if not media_type:
                return
            
            chat_id = None
            if event.message.peer_id:
                if hasattr(event.message.peer_id, 'user_id'):
                    chat_id = event.message.peer_id.user_id
                elif hasattr(event.message.peer_id, 'chat_id'):
                    chat_id = event.message.peer_id.chat_id
                elif hasattr(event.message.peer_id, 'channel_id'):
                    chat_id = event.message.peer_id.channel_id
            
            if chat_id:
                cursor.execute(
                    "SELECT id FROM watched_chats WHERE user_id=? AND chat_id=? AND is_active=TRUE",
                    (user_id, chat_id)
                )
                if cursor.fetchone():
                    chat = await event.get_chat()
                    sender = await event.get_sender()
                    await download_and_send_media(event, user_id, chat, sender, media_type)
                    return
            
            cursor.execute(
                "SELECT id FROM watched_chats WHERE user_id=? AND is_active=TRUE",
                (user_id,)
            )
            if not cursor.fetchone():
                chat = await event.get_chat()
                sender = await event.get_sender()
                await download_and_send_media(event, user_id, chat, sender, media_type)
                        
        except Exception as e:
            logger.error(f"Xabarni qayta ishlashda xatolik: {e}")

    active_clients[user_id] = client
    
    try:
        await client.run_until_disconnected()
    except Exception as e:
        logger.error(f"Userbot xatolik: {e}")
    finally:
        if user_id in active_clients:
            del active_clients[user_id]

# ============ ESKI XABARLARNI SKANERLASH ============
async def scan_old_messages(client: TelegramClient, user_id: int, limit: int = 100):
    try:
        await bot.send_message(user_id, "🔍 Skanerlash boshlandi...")
        
        dialogs = await client.get_dialogs(limit=50)
        total_saved = 0
        
        for dialog in dialogs:
            try:
                messages = await client.get_messages(dialog.entity, limit=limit)
                
                for message in messages:
                    if not message.media:
                        continue
                    
                    if not is_view_once_media(message.media):
                        continue
                    
                    media_type = get_media_type(message.media)
                    if not media_type:
                        continue
                    
                    cursor.execute(
                        "SELECT id FROM saved_messages WHERE user_id=? AND chat_id=? AND message_id=?",
                        (user_id, dialog.id, message.id)
                    )
                    
                    if cursor.fetchone():
                        continue
                    
                    file_path = await message.download_media(
                        file=str(DOWNLOADS_DIR / str(user_id))
                    )
                    
                    if file_path and os.path.exists(file_path):
                        sender_name, sender_id, sender_username = get_display_name(message.sender)
                        
                        chat_name = dialog.name or "Shaxsiy chat"
                        date_str = message.date.strftime('%Y-%m-%d %H:%M:%S')
                        
                        success = await send_media_with_caption(
                            user_id, file_path, media_type, sender_name, chat_name, date_str,
                            sender_id=sender_id, sender_username=sender_username
                        )
                        
                        if success:
                            cursor.execute(
                                """INSERT OR IGNORE INTO saved_messages 
                                   (user_id, message_id, chat_id, media_type, file_path) 
                                   VALUES (?, ?, ?, ?, ?)""",
                                (user_id, message.id, dialog.id, media_type, file_path)
                            )
                            conn.commit()
                            
                            os.remove(file_path)
                            total_saved += 1
                            
                            await asyncio.sleep(0.5)
                        
            except Exception as e:
                logger.error(f"Chat {dialog.name} xatolik: {e}")
                continue
        
        await bot.send_message(
            user_id,
            f"✅ Skanerlash yakunlandi!\n📥 Jami {total_saved} ta xabar saqlandi."
        )
        
    except Exception as e:
        logger.error(f"Skanerlashda xatolik: {e}")
        await bot.send_message(user_id, f"❌ Xatolik: {str(e)}")

# ============ GURUH BOSHQARUVI ============
async def get_user_groups_stats(client: TelegramClient, user_id: int) -> Dict:
    """Foydalanuvchining guruhlardagi statistikasi"""
    try:
        dialogs = await client.get_dialogs(limit=500)
        
        admin_groups = []
        member_groups = []
        all_groups = []
        
        for dialog in dialogs:
            if not dialog.is_group and not (dialog.is_channel and not dialog.entity.broadcast):
                continue
            
            try:
                me = await client.get_me()
                
                try:
                    participants = await client.get_participants(dialog.entity, filter=ChannelParticipantsAdmins())
                    is_admin = any(p.id == me.id for p in participants)
                except:
                    is_admin = False
                
                can_ban = False
                if is_admin:
                    try:
                        admins = await client.get_participants(dialog.entity, filter=ChannelParticipantsAdmins())
                        for admin in admins:
                            if admin.id == me.id:
                                if hasattr(admin.participant, 'admin_rights'):
                                    can_ban = admin.participant.admin_rights.ban_users
                                break
                    except:
                        pass
                
                group_info = {
                    'id': dialog.id,
                    'name': dialog.name,
                    'members': dialog.entity.participants_count if hasattr(dialog.entity, 'participants_count') else 0,
                    'is_admin': is_admin,
                    'can_ban': can_ban
                }
                
                all_groups.append(group_info)
                
                if is_admin:
                    admin_groups.append(group_info)
                else:
                    member_groups.append(group_info)
                    
            except Exception as e:
                logger.error(f"Guruh {dialog.name} tekshirishda xatolik: {e}")
                continue
        
        return {
            'total': len(all_groups),
            'admin': len(admin_groups),
            'member': len(member_groups),
            'admin_groups': admin_groups,
            'member_groups': member_groups,
            'all_groups': all_groups
        }
        
    except Exception as e:
        logger.error(f"Guruhlar statistikasida xatolik: {e}")
        return {
            'total': 0,
            'admin': 0,
            'member': 0,
            'admin_groups': [],
            'member_groups': [],
            'all_groups': []
        }

async def get_groups_with_ban_rights(client: TelegramClient, user_id: int) -> List[Dict]:
    """Ban huquqi bor guruhlar"""
    try:
        stats = await get_user_groups_stats(client, user_id)
        return [g for g in stats['admin_groups'] if g['can_ban']]
    except:
        return []

async def _ban_participants_in_parallel(client: TelegramClient, chat_id: int, participants: List, concurrency: int = 15):
    banned_count = 0
    failed_count = 0
    lock = asyncio.Lock()
    semaphore = asyncio.Semaphore(concurrency)

    async def ban_one(participant):
        nonlocal banned_count, failed_count
        async with semaphore:
            try:
                await client(EditBannedRequest(
                    chat_id,
                    participant.id,
                    ChatBannedRights(until_date=None, view_messages=True)
                ))
                async with lock:
                    banned_count += 1
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds)
                try:
                    await client(EditBannedRequest(
                        chat_id,
                        participant.id,
                        ChatBannedRights(until_date=None, view_messages=True)
                    ))
                    async with lock:
                        banned_count += 1
                except Exception:
                    async with lock:
                        failed_count += 1
            except Exception:
                async with lock:
                    failed_count += 1

    await asyncio.gather(*[ban_one(p) for p in participants])
    return banned_count, failed_count


async def purge_deleted_accounts(client: TelegramClient, chat_id: int, user_id: int, progress_callback=None) -> Dict[str, int]:
    async def notify(text):
        if progress_callback:
            try:
                await progress_callback(text)
            except Exception:
                pass

    try:
        chat = await client.get_entity(chat_id)

        await notify("🔍 <b>1-bosqich:</b> Guruhdagi barcha a'zolar yig'ilmoqda...")
        participants = await client.get_participants(chat, limit=5000)

        await notify(f"📋 <b>2-bosqich:</b> {len(participants)} ta a'zo tekshirilib, notinchlari belgilanmoqda...")
        to_ban = [p for p in participants if is_inactive_account(p)]

        if not to_ban:
            return {'banned': 0, 'failed': 0, 'total_found': 0, 'total_checked': len(participants)}

        await notify(
            f"✅ {len(to_ban)} ta notinch akkaunt aniqlandi.\n"
            f"🧹 <b>3-bosqich:</b> Barchasi bittada ban qilinmoqda..."
        )
        banned_count, failed_count = await _ban_participants_in_parallel(client, chat_id, to_ban)

        return {
            'banned': banned_count,
            'failed': failed_count,
            'total_found': len(to_ban),
            'total_checked': len(participants)
        }

    except Exception as e:
        logger.error(f"Tozalashda xatolik: {e}")
        return {'banned': 0, 'failed': 0, 'total_found': 0, 'total_checked': 0}

async def close_group(client: TelegramClient, chat_id: int, user_id: int, progress_callback=None) -> Dict[str, int]:
    async def notify(text):
        if progress_callback:
            try:
                await progress_callback(text)
            except Exception:
                pass

    try:
        chat = await client.get_entity(chat_id)

        await notify("🔍 <b>1-bosqich:</b> Adminlar va barcha a'zolar yig'ilmoqda...")
        admins = await client.get_participants(chat, filter=ChannelParticipantsAdmins())
        admin_ids = {admin.id for admin in admins}
        participants = await client.get_participants(chat, limit=5000)

        await notify(f"📋 <b>2-bosqich:</b> {len(participants)} ta a'zodan chiqariladiganlar belgilanmoqda...")
        to_remove = [p for p in participants if p.id not in admin_ids]

        if not to_remove:
            return {'removed': 0, 'failed': 0, 'total_found': 0}

        await notify(
            f"✅ {len(to_remove)} ta a'zo belgilandi.\n"
            f"🔒 <b>3-bosqich:</b> Barchasi bittada chiqarilmoqda..."
        )
        removed_count, failed_count = await _ban_participants_in_parallel(client, chat_id, to_remove)

        return {'removed': removed_count, 'failed': failed_count, 'total_found': len(to_remove)}

    except Exception as e:
        logger.error(f"Guruhni yopishda xatolik: {e}")
        return {'removed': 0, 'failed': 0, 'total_found': 0}

# ============ BOT HANDLERLAR ============
@router.message(CommandStart())
async def start_command(message: types.Message):
    user_id = message.from_user.id

    if not await enforce_force_sub(message):
        return

    payload_parts = (message.text or "").split(maxsplit=1)
    payload = payload_parts[1].strip() if len(payload_parts) > 1 else ""

    if payload == "blackwords":
        groups = await get_editable_alliance_groups(user_id)
        if not groups:
            await message.answer(
                "🚫 Siz guruh ma'lumotlarini o'zgartira oladigan ittifoq guruhi topilmadi.",
                reply_markup=main_kb(user_id)
            )
            return
        await message.answer(
            "🚫 <b>Qora ro'yxat</b>\n\nQaysi guruh uchun so'zlarni boshqarmoqchisiz?",
            parse_mode="HTML",
            reply_markup=get_blackwords_group_list_keyboard(groups)
        )
        return

    cursor.execute("SELECT is_active FROM users WHERE user_id=?", (user_id,))
    user = cursor.fetchone()
    
    if user and user[0]:
        welcome_text = (
            f"👋 <b>Xush kelibsiz, {message.from_user.first_name}!</b>\n\n"
            f"✅ Akkauntingiz ulangan.\n\n"
            f"📌 <b>Bo'limlardan birini tanlang:</b>"
        )
    else:
        welcome_text = (
            f"👋 <b>Xush kelibsiz, {message.from_user.first_name}!</b>\n\n"
            f"🤖 Ko'p funksiyali bot.\n\n"
            f"📱 Boshlash uchun avval akkauntingizni ulang:"
        )
    
    await message.answer(welcome_text, parse_mode="HTML", reply_markup=main_kb(user_id))

@router.message(Command("stop"))
async def stop_command(message: types.Message):
    user_id = message.from_user.id
    
    if user_id in active_clients:
        try:
            await active_clients[user_id].disconnect()
            del active_clients[user_id]
            
            cursor.execute("UPDATE users SET is_active = FALSE WHERE user_id=?", (user_id,))
            conn.commit()
            
            await message.answer("⏹ <b>Profil tekshirish to'xtatildi!</b>", parse_mode="HTML", reply_markup=main_kb(user_id))
        except Exception as e:
            await message.answer(f"❌ Xatolik: {str(e)}")
    else:
        await message.answer("❌ Sizda faol profil yo'q!", reply_markup=main_kb(user_id))

# ============ ADMIN: /stats va /groups ============
@router.message(Command("stats"), F.chat.type == "private")
async def admin_stats_command(message: types.Message):
    if message.from_user.id not in ADMIN_IDS:
        return

    cursor.execute("SELECT COUNT(*) FROM users")
    total_users = cursor.fetchone()[0]
    cursor.execute("SELECT COUNT(*) FROM users WHERE is_active=TRUE")
    active_users = cursor.fetchone()[0]
    currently_connected = len(active_clients)
    cursor.execute("SELECT COUNT(*) FROM alliance_group")
    total_alliance_groups = cursor.fetchone()[0]
    cursor.execute("SELECT COUNT(*) FROM alliance_control")
    total_control_groups = cursor.fetchone()[0]
    cursor.execute("SELECT COUNT(*) FROM saved_messages")
    total_saved = cursor.fetchone()[0]
    cursor.execute("SELECT COUNT(*) FROM required_channels")
    total_required_channels = cursor.fetchone()[0]

    text = (
        "📊 <b>Bot statistikasi</b>\n\n"
        f"👤 Jami ro'yxatdan o'tgan: {total_users} ta\n"
        f"✅ Faol (is_active): {active_users} ta\n"
        f"🟢 Hozir ulangan (userbot): {currently_connected} ta\n"
        f"🛡 Ittifoq — oddiy guruhlar: {total_alliance_groups} ta\n"
        f"🧭 Ittifoq — nazorat guruhlari: {total_control_groups} ta\n"
        f"📥 Saqlangan view-once: {total_saved} ta\n"
        f"📢 Majburiy obuna kanallari: {total_required_channels} ta"
    )
    await message.reply(text, parse_mode="HTML")

@router.message(Command("groups"), F.chat.type == "private")
async def admin_groups_command(message: types.Message):
    if message.from_user.id not in ADMIN_IDS:
        return

    processing = await message.reply("⏳ Guruhlar ro'yxati tayyorlanmoqda...")

    cursor.execute("SELECT code, chat_id, title, control_chat_id FROM alliance_group")
    groups = cursor.fetchall()

    if not groups:
        await processing.edit_text("📋 Hali ittifoqqa ulangan guruh yo'q.")
        return

    lines = ["📋 <b>Ittifoq — oddiy guruhlar:</b>\n"]
    for code, chat_id, title, control_chat_id in groups:
        link = None
        try:
            chat_obj = await bot.get_chat(chat_id)
            if getattr(chat_obj, "username", None):
                link = f"https://t.me/{chat_obj.username}"
            else:
                # Bot guruhda admin bo'lsa, invite link yarata/ola oladi
                invite = await bot.export_chat_invite_link(chat_id)
                link = invite
        except Exception as e:
            link = f"(havola olinmadi: {e})"

        status = "🔗 nazoratda" if control_chat_id else "⛔️ nazoratsiz"
        lines.append(f"• <b>{title or chat_id}</b> — ID: <code>{code}</code> ({status})\n  {link}")

    text = "\n\n".join(lines)
    if len(text) > 4000:
        parts = [text[i:i+4000] for i in range(0, len(text), 4000)]
        await processing.edit_text(parts[0], parse_mode="HTML", disable_web_page_preview=True)
        for part in parts[1:]:
            await bot.send_message(message.from_user.id, part, parse_mode="HTML", disable_web_page_preview=True)
    else:
        await processing.edit_text(text, parse_mode="HTML", disable_web_page_preview=True)

# ============ CALLBACK HANDLERLAR ============
@router.callback_query(F.data == "funstat_menu")
async def funstat_menu(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    if user_id not in active_clients:
        await callback_query.message.edit_text("❌ Avval akkauntni ulang! (View Once bo'limidan)", reply_markup=main_kb(user_id))
        await callback_query.answer()
        return
    
    await callback_query.message.edit_text(
        "👤 <b>FunStat Tekshirish</b>\n\n"
        "Nima qilmoqchisiz?",
        parse_mode="HTML",
        reply_markup=get_funstat_keyboard()
    )
    await callback_query.answer()

@router.callback_query(F.data == "view_once_menu")
async def view_once_menu(callback_query: types.CallbackQuery):
    await callback_query.message.edit_text(
        "👁 <b>View Once saqlash</b>\n\n"
        "View Once xabarlarni avtomatik saqlash uchun akkaunt ulang.",
        parse_mode="HTML",
        reply_markup=get_view_once_keyboard()
    )
    await callback_query.answer()

@router.callback_query(F.data == "settings_menu")
async def settings_menu(callback_query: types.CallbackQuery):
    await callback_query.message.edit_text(
        "⚙️ <b>Sozlamalar</b>",
        parse_mode="HTML",
        reply_markup=get_settings_keyboard()
    )
    await callback_query.answer()

@router.callback_query(F.data == "back_to_main")
async def back_to_main(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    await callback_query.message.edit_text(
        "📋 <b>Asosiy menyu</b>\n\nBo'limlardan birini tanlang:",
        parse_mode="HTML",
        reply_markup=main_kb(user_id)
    )
    await callback_query.answer()

# ============ GURUH BOSHQARUVI HANDLERLARI ============
async def render_group_management(callback_query: types.CallbackQuery, force_refresh: bool = False):
    user_id = callback_query.from_user.id
    
    if user_id not in active_clients:
        await callback_query.message.edit_text("❌ Avval akkauntni ulang!", reply_markup=main_kb(user_id))
        return
    
    try:
        if force_refresh or user_id not in group_stats_cache:
            await callback_query.message.edit_text("📊 Guruhlar tahlil qilinmoqda...")
            client = active_clients[user_id]
            stats = await get_user_groups_stats(client, user_id)
            group_stats_cache[user_id] = stats
        else:
            stats = group_stats_cache[user_id]
        
        text = (
            f"👥 <b>GURUH BOSHQARUVI</b>\n\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"📊 <b>Umumiy statistika:</b>\n"
            f"• Jami guruhlar: {stats['total']} ta\n"
            f"• Admin guruhlar: {stats['admin']} ta\n"
            f"• A'zo guruhlar: {stats['member']} ta\n"
            f"━━━━━━━━━━━━━━━━━━━━\n\n"
            f"Qaysi guruhlarni ko'rmoqchisiz?"
        )
        
        builder = InlineKeyboardBuilder()
        builder.row(InlineKeyboardButton(text=f"👑 Admin guruhlar ({stats['admin']})", callback_data="show_admin_groups"))
        builder.row(InlineKeyboardButton(text=f"👤 A'zo guruhlar ({stats['member']})", callback_data="show_member_groups"))
        builder.row(InlineKeyboardButton(text=f"📋 Barchasi ({stats['total']})", callback_data="show_all_groups"))
        builder.row(InlineKeyboardButton(text="🔄 Yangilash", callback_data="refresh_group_stats"))
        builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
        
        await callback_query.message.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())
    except Exception as e:
        await callback_query.message.edit_text(f"❌ Xatolik: {str(e)}", reply_markup=main_kb(user_id))

@router.callback_query(F.data == "group_management")
async def group_management(callback_query: types.CallbackQuery):
    await render_group_management(callback_query, force_refresh=False)
    await callback_query.answer()

@router.callback_query(F.data == "refresh_group_stats")
async def refresh_group_stats(callback_query: types.CallbackQuery):
    await render_group_management(callback_query, force_refresh=True)
    await callback_query.answer("🔄 Yangilandi!")

@router.callback_query(F.data == "show_admin_groups")
async def show_admin_groups(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    stats = group_stats_cache.get(user_id)
    if stats is None:
        client = active_clients[user_id]
        stats = await get_user_groups_stats(client, user_id)
        group_stats_cache[user_id] = stats
    
    groups = stats['admin_groups']
    
    if not groups:
        await callback_query.message.edit_text("❌ Admin guruhlar topilmadi!", reply_markup=main_kb(user_id))
        await callback_query.answer()
        return
    
    text = "👑 <b>ADMIN GURUHLAR</b>\n\n"
    for i, group in enumerate(groups[:50], 1):
        ban_status = "🔨 Ban huquqi bor" if group['can_ban'] else "⚪ Ban huquqi yo'q"
        text += f"{i}. {group['name']}\n   👥 {group['members']} a'zo | {ban_status}\n\n"
    
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="group_management"))
    
    if len(text) > 4000:
        parts = [text[i:i+4000] for i in range(0, len(text), 4000)]
        await callback_query.message.edit_text(parts[0], parse_mode="HTML", reply_markup=builder.as_markup())
        for part in parts[1:]:
            await bot.send_message(user_id, part, parse_mode="HTML")
    else:
        await callback_query.message.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())
    
    await callback_query.answer()

@router.callback_query(F.data == "show_member_groups")
async def show_member_groups(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    stats = group_stats_cache.get(user_id)
    if stats is None:
        client = active_clients[user_id]
        stats = await get_user_groups_stats(client, user_id)
        group_stats_cache[user_id] = stats
    
    groups = stats['member_groups']
    
    if not groups:
        await callback_query.message.edit_text("❌ A'zo guruhlar topilmadi!", reply_markup=main_kb(user_id))
        await callback_query.answer()
        return
    
    text = "👤 <b>A'ZO GURUHLAR</b>\n\n"
    for i, group in enumerate(groups[:50], 1):
        text += f"{i}. {group['name']}\n   👥 {group['members']} a'zo\n\n"
    
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="group_management"))
    
    if len(text) > 4000:
        parts = [text[i:i+4000] for i in range(0, len(text), 4000)]
        await callback_query.message.edit_text(parts[0], parse_mode="HTML", reply_markup=builder.as_markup())
        for part in parts[1:]:
            await bot.send_message(user_id, part, parse_mode="HTML")
    else:
        await callback_query.message.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())
    
    await callback_query.answer()

@router.callback_query(F.data == "show_all_groups")
async def show_all_groups(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    stats = group_stats_cache.get(user_id)
    if stats is None:
        client = active_clients[user_id]
        stats = await get_user_groups_stats(client, user_id)
        group_stats_cache[user_id] = stats
    
    groups = stats['all_groups']
    
    if not groups:
        await callback_query.message.edit_text("❌ Guruhlar topilmadi!", reply_markup=main_kb(user_id))
        await callback_query.answer()
        return
    
    text = "📋 <b>BARCHA GURUHLAR</b>\n\n"
    for i, group in enumerate(groups[:50], 1):
        status = "👑 Admin" if group['is_admin'] else "👤 A'zo"
        text += f"{i}. {group['name']}\n   👥 {group['members']} a'zo | {status}\n\n"
    
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="group_management"))
    
    if len(text) > 4000:
        parts = [text[i:i+4000] for i in range(0, len(text), 4000)]
        await callback_query.message.edit_text(parts[0], parse_mode="HTML", reply_markup=builder.as_markup())
        for part in parts[1:]:
            await bot.send_message(user_id, part, parse_mode="HTML")
    else:
        await callback_query.message.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())
    
    await callback_query.answer()

# ============ A'ZOLAR BOSHQARUVI HANDLERLARI ============
@router.callback_query(F.data == "member_management")
async def member_management(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    if user_id not in active_clients:
        await callback_query.message.edit_text("❌ Avval akkauntni ulang!", reply_markup=main_kb(user_id))
        await callback_query.answer()
        return
    
    processing_msg = await callback_query.message.edit_text("📊 Ban huquqi bor guruhlar qidirilmoqda...")
    
    try:
        client = active_clients[user_id]
        ban_groups = await get_groups_with_ban_rights(client, user_id)
        
        if not ban_groups:
            await processing_msg.edit_text(
                "❌ Ban huquqi bor guruhlar topilmadi!",
                reply_markup=main_kb(user_id)
            )
            await callback_query.answer()
            return
        
        text = (
            f"🔨 <b>A'ZOLAR BOSHQARUVI</b>\n\n"
            f"Ban huquqi bor guruhlar: {len(ban_groups)} ta\n\n"
            f"Guruhni tanlang:"
        )
        
        builder = InlineKeyboardBuilder()
        for group in ban_groups[:30]:
            builder.row(InlineKeyboardButton(
                text=f"{group['name']} ({group['members']} a'zo)",
                callback_data=f"manage_group_{group['id']}"
            ))
        builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
        
        await processing_msg.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())
    except Exception as e:
        await processing_msg.edit_text(f"❌ Xatolik: {str(e)}", reply_markup=main_kb(user_id))
    
    await callback_query.answer()

@router.callback_query(F.data.startswith('manage_group_'))
async def manage_group(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    chat_id = int(callback_query.data.split('_')[2])
    
    group_actions[user_id] = {'chat_id': chat_id}
    
    builder = InlineKeyboardBuilder()
    builder.row(InlineKeyboardButton(text="📋 A'zolarni eksport qilish", callback_data="export_members"))
    builder.row(InlineKeyboardButton(text="🧹 Nakrutkani tozalash", callback_data="purge_deleted"))
    builder.row(InlineKeyboardButton(text="🔒 Guruhni yopish", callback_data="close_group_action"))
    builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="member_management"))
    
    await callback_query.message.edit_text(
        "🔨 <b>Guruh boshqaruvi</b>\n\n"
        "Nima qilmoqchisiz?",
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )
    await callback_query.answer()

@router.callback_query(F.data == "export_members")
async def export_members(callback_query: types.CallbackQuery):
    await callback_query.answer()
    user_id = callback_query.from_user.id
    
    if user_id not in group_actions:
        await callback_query.message.edit_text("❌ Xatolik yuz berdi!", reply_markup=main_kb(user_id))
        return
    
    chat_id = group_actions[user_id]['chat_id']
    client = active_clients[user_id]
    
    processing_msg = await callback_query.message.edit_text("📋 A'zolar ro'yxati tayyorlanmoqda...")
    
    try:
        chat = await client.get_entity(chat_id)
        chat_title = getattr(chat, 'title', str(chat_id))
        
        admins = await client.get_participants(chat, filter=ChannelParticipantsAdmins())
        admin_ids = {a.id for a in admins}
        
        await processing_msg.edit_text("📋 Barcha a'zolar yig'ilmoqda (guruh kattaligiga qarab bir necha soniya davom etishi mumkin)...")
        all_participants = await client.get_participants(chat, limit=10000)
        
        admin_lines = []
        for a in admins:
            uname = f"@{a.username}" if getattr(a, 'username', None) else "username yo'q"
            admin_lines.append(f"{a.id} — {uname}")
        
        member_lines = []
        for p in all_participants:
            if p.id in admin_ids:
                continue
            if getattr(p, 'bot', False):
                continue
            uname = f"@{p.username}" if getattr(p, 'username', None) else "username yo'q"
            member_lines.append(uname)
        
        export_dir = DOWNLOADS_DIR / str(user_id)
        export_dir.mkdir(exist_ok=True)
        file_path = export_dir / f"azolar_{chat_id}.txt"
        
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(f"📌 GURUH: {chat_title}\n")
            f.write(f"📅 Sana: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            f.write(f"👑 ADMINLAR ({len(admin_lines)} ta)\n")
            f.write("=" * 30 + "\n")
            for line in admin_lines:
                f.write(line + "\n")
            f.write("\n\n")
            f.write(f"👤 ODDIY A'ZOLAR - USERNAMELARI ({len(member_lines)} ta)\n")
            f.write("=" * 30 + "\n")
            for line in member_lines:
                f.write(line + "\n")
        
        await processing_msg.edit_text(
            f"✅ <b>Tayyor!</b>\n\n"
            f"👑 Adminlar: {len(admin_lines)} ta\n"
            f"👤 Oddiy a'zolar: {len(member_lines)} ta\n"
            f"🤖 Botlar chetlab o'tildi",
            parse_mode="HTML",
            reply_markup=main_kb(user_id)
        )
        await bot.send_document(user_id, types.FSInputFile(str(file_path)))
        
        if os.path.exists(file_path):
            os.remove(file_path)
            
    except Exception as e:
        logger.error(f"A'zolarni eksport qilishda xatolik: {e}")
        await processing_msg.edit_text(f"❌ Xatolik: {str(e)}", reply_markup=main_kb(user_id))


@router.callback_query(F.data == "purge_deleted")
async def purge_deleted(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    if user_id not in group_actions:
        await callback_query.message.edit_text("❌ Xatolik yuz berdi!", reply_markup=main_kb(user_id))
        await callback_query.answer()
        return
    
    builder = InlineKeyboardBuilder()
    builder.row(
        InlineKeyboardButton(text="✅ Ha, tozalash", callback_data="confirm_purge"),
        InlineKeyboardButton(text="❌ Yo'q", callback_data="cancel_purge")
    )
    
    await callback_query.message.edit_text(
        "⚠️ <b>Nakrutkani tozalash</b>\n\n"
        "Bu amal guruhdagi:\n"
        "• o'chirilgan (deleted) akkauntlarni,\n"
        f"• oxirgi marta {INACTIVE_DAYS_THRESHOLD} kundan ortiq oldin kirgan (last seen) akkauntlarni\n\n"
        "chiqarib tashlaydi. Jarayon 3 bosqichda ketadi: avval BARCHA a'zolar "
        "yig'ib chiqiladi, keyin notinchlari belgilanadi, so'ng barchasi BITTADA "
        "(parallel) ban qilinadi.\n\n"
        "Rostdan ham davom etmoqchimisiz?",
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )
    await callback_query.answer()

@router.callback_query(F.data == "confirm_purge")
async def confirm_purge(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    await callback_query.answer()
    
    if user_id not in group_actions:
        await callback_query.message.edit_text("❌ Xatolik yuz berdi!", reply_markup=main_kb(user_id))
        return
    
    chat_id = group_actions[user_id]['chat_id']
    client = active_clients[user_id]
    
    processing_msg = await callback_query.message.edit_text("🧹 Tozalash boshlanmoqda...")
    
    async def update_progress(text):
        await processing_msg.edit_text(text, parse_mode="HTML")
    
    internal_bulk_action_chats.add(chat_id)
    try:
        result = await purge_deleted_accounts(client, chat_id, user_id, progress_callback=update_progress)
        
        await processing_msg.edit_text(
            f"✅ <b>Tozalash yakunlandi!</b>\n\n"
            f"👥 <b>Tekshirildi:</b> {result.get('total_checked', 0)} ta a'zo\n"
            f"🔎 <b>Notinch topildi:</b> {result['total_found']} ta\n"
            f"🧹 <b>Ban qilindi:</b> {result['banned']} ta\n"
            f"❌ <b>Xatolik:</b> {result['failed']} ta\n\n"
            f"<i>Barchasi avval to'liq yig'ib chiqilib, belgilanib, so'ng bittada (parallel) ban qilindi.</i>",
            parse_mode="HTML",
            reply_markup=main_kb(user_id)
        )
    except Exception as e:
        await processing_msg.edit_text(f"❌ Xatolik: {str(e)}", reply_markup=main_kb(user_id))
    finally:
        internal_bulk_action_chats.discard(chat_id)
    
    del group_actions[user_id]

@router.callback_query(F.data == "cancel_purge")
async def cancel_purge(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    if user_id in group_actions:
        del group_actions[user_id]
    
    await callback_query.message.edit_text("❌ Bekor qilindi.", reply_markup=main_kb(user_id))
    await callback_query.answer()

@router.callback_query(F.data == "close_group_action")
async def close_group_action(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    if user_id not in group_actions:
        await callback_query.message.edit_text("❌ Xatolik yuz berdi!", reply_markup=main_kb(user_id))
        await callback_query.answer()
        return

    chat_id = group_actions[user_id]['chat_id']
    client = active_clients.get(user_id)
    if client:
        try:
            perms = await client.get_permissions(chat_id, 'me')
            if not getattr(perms, 'is_creator', False):
                await callback_query.message.edit_text(
                    "⛔ <b>Ruxsat yo'q!</b>\n\n"
                    "Guruhni to'liq yopish (barcha a'zolarni ban qilish) faqat "
                    "guruh <b>EGASI</b> (creator) uchun mumkin - hattoki co-founder "
                    "darajasidagi adminlar ham bu amalni bajara olmaydi.",
                    parse_mode="HTML",
                    reply_markup=main_kb(user_id)
                )
                await callback_query.answer()
                return
        except Exception:
            pass
    
    builder = InlineKeyboardBuilder()
    builder.row(
        InlineKeyboardButton(text="✅ Ha, yopish", callback_data="confirm_close_group"),
        InlineKeyboardButton(text="❌ Yo'q", callback_data="cancel_close_group")
    )
    
    await callback_query.message.edit_text(
        "⚠️ <b>Guruhni yopish</b>\n\n"
        "Bu amal guruhdagi barcha a'zolarni chiqarib tashlaydi (adminlardan tashqari).\n\n"
        "Rostdan ham davom etmoqchimisiz?",
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )
    await callback_query.answer()

@router.callback_query(F.data == "confirm_close_group")
async def confirm_close_group(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    await callback_query.answer()
    
    if user_id not in group_actions:
        await callback_query.message.edit_text("❌ Xatolik yuz berdi!", reply_markup=main_kb(user_id))
        return
    
    chat_id = group_actions[user_id]['chat_id']
    client = active_clients[user_id]
    
    processing_msg = await callback_query.message.edit_text("🔒 Guruh yopilmoqda...")
    
    async def update_progress(text):
        await processing_msg.edit_text(text, parse_mode="HTML")
    
    internal_bulk_action_chats.add(chat_id)
    try:
        result = await close_group(client, chat_id, user_id, progress_callback=update_progress)
        
        await processing_msg.edit_text(
            f"✅ <b>Guruh yopildi!</b>\n\n"
            f"🔎 <b>Belgilandi:</b> {result['total_found']} ta a'zo (adminlardan tashqari)\n"
            f"🔒 <b>Chiqarildi:</b> {result['removed']} ta\n"
            f"❌ <b>Xatolik:</b> {result['failed']} ta\n\n"
            f"<i>Barchasi bittada (parallel) chiqarib tashlandi.</i>",
            parse_mode="HTML",
            reply_markup=main_kb(user_id)
        )
    except Exception as e:
        await processing_msg.edit_text(f"❌ Xatolik: {str(e)}", reply_markup=main_kb(user_id))
    finally:
        internal_bulk_action_chats.discard(chat_id)
    
    del group_actions[user_id]

@router.callback_query(F.data == "cancel_close_group")
async def cancel_close_group(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    if user_id in group_actions:
        del group_actions[user_id]
    
    await callback_query.message.edit_text("❌ Bekor qilindi.", reply_markup=main_kb(user_id))
    await callback_query.answer()

# ============ FUNSTAT HANDLERLARI ============
@router.callback_query(F.data == "get_stats")
async def get_stats(callback_query: types.CallbackQuery, state: FSMContext):
    await callback_query.message.edit_text(
        "📊 <b>Ultra statistika olish</b>\n\n"
        "Username, telefon raqam yoki ID yuboring:\n"
        "Masalan:\n"
        "• @username\n"
        "• +998901234567\n"
        "• 123456789 (ID raqam)",
        parse_mode="HTML",
        reply_markup=get_cancel_keyboard()
    )
    await state.set_state(AccountStates.waiting_chat)
    await state.update_data(action="stats")
    await callback_query.answer()

@router.callback_query(F.data == "start_watching")
async def start_watching(callback_query: types.CallbackQuery, state: FSMContext):
    await callback_query.message.edit_text(
        "👁 <b>Kuzatishni boshlash</b>\n\n"
        "Username, telefon raqam yoki ID yuboring:",
        parse_mode="HTML",
        reply_markup=get_cancel_keyboard()
    )
    await state.set_state(AccountStates.waiting_chat)
    await state.update_data(action="watch")
    await callback_query.answer()

@router.message(AccountStates.waiting_chat)
async def process_chat(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    chat_input = message.text.strip()
    
    data = await state.get_data()
    action = data.get("action", "watch")
    
    if user_id not in active_clients:
        await message.answer("❌ Akkaunt ulanmagan!")
        await state.clear()
        return
    
    processing_msg = await message.answer("🔍 Qidirilmoqda...")
    
    try:
        client = active_clients[user_id]
        
        entity = None
        errors = []
        
        if chat_input.startswith('@'):
            try:
                entity = await client.get_entity(chat_input)
            except Exception as e:
                errors.append(f"Username: {str(e)}")
        elif chat_input.startswith('+'):
            try:
                entity = await client.get_entity(chat_input)
            except Exception as e:
                errors.append(f"Telefon: {str(e)}")
        elif chat_input.isdigit():
            try:
                entity = await client.get_entity(int(chat_input))
            except Exception as e:
                errors.append(f"ID: {str(e)}")
        else:
            try:
                result = await client(SearchRequest(q=chat_input, limit=10))
                if result.users:
                    entity = result.users[0]
            except Exception as e:
                errors.append(f"Ism: {str(e)}")
        
        if not entity:
            await processing_msg.edit_text(
                f"❌ Foydalanuvchi topilmadi!\n\n"
                f"Xatolar:\n" + "\n".join(errors[:3]),
                reply_markup=main_kb(user_id)
            )
            await state.clear()
            return
        
        if action == "stats":
            await processing_msg.edit_text("📊 Ultra statistika yig'ilmoqda... Bu biroz vaqt olishi mumkin...")
            
            stats_text = await get_ultra_user_stats(client, entity)
            
            if len(stats_text) > 4000:
                parts = [stats_text[i:i+4000] for i in range(0, len(stats_text), 4000)]
                await processing_msg.edit_text(parts[0], parse_mode="HTML")
                for part in parts[1:]:
                    await bot.send_message(user_id, part, parse_mode="HTML")
            else:
                await processing_msg.edit_text(stats_text, parse_mode="HTML")
            
            builder = InlineKeyboardBuilder()
            builder.row(InlineKeyboardButton(text="👁 Kuzatishni boshlash", callback_data=f"watch_entity_{entity.id}"))
            builder.row(InlineKeyboardButton(text="🔙 Orqaga", callback_data="back_to_main"))
            
            await bot.send_message(user_id, "Nima qilmoqchisiz?", reply_markup=builder.as_markup())
        else:
            chat_id = entity.id
            
            chat_name = "Noma'lum"
            if hasattr(entity, 'title') and entity.title:
                chat_name = entity.title
            elif hasattr(entity, 'first_name'):
                chat_name = f"{entity.first_name} {entity.last_name if entity.last_name else ''}"
            
            cursor.execute(
                "INSERT OR REPLACE INTO watched_chats (user_id, chat_id, chat_name, is_active) VALUES (?, ?, ?, TRUE)",
                (user_id, chat_id, chat_name)
            )
            conn.commit()
            
            await processing_msg.edit_text(
                f"✅ <b>{chat_name}</b> endi kuzatilmoqda!",
                parse_mode="HTML",
                reply_markup=main_kb(user_id)
            )
        
        await state.clear()
        
    except Exception as e:
        logger.error(f"Xatolik: {e}")
        await processing_msg.edit_text(f"❌ Xatolik: {str(e)}")
        await state.clear()

@router.callback_query(F.data.startswith('watch_entity_'))
async def watch_entity(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    entity_id = int(callback_query.data.split('_')[2])
    
    try:
        client = active_clients[user_id]
        entity = await client.get_entity(entity_id)
        
        chat_name = "Noma'lum"
        if hasattr(entity, 'title') and entity.title:
            chat_name = entity.title
        elif hasattr(entity, 'first_name'):
            chat_name = f"{entity.first_name} {entity.last_name if entity.last_name else ''}"
        
        cursor.execute(
            "INSERT OR REPLACE INTO watched_chats (user_id, chat_id, chat_name, is_active) VALUES (?, ?, ?, TRUE)",
            (user_id, entity_id, chat_name)
        )
        conn.commit()
        
        await callback_query.message.edit_text(
            f"✅ <b>{chat_name}</b> endi kuzatilmoqda!",
            parse_mode="HTML",
            reply_markup=main_kb(user_id)
        )
    except Exception as e:
        await callback_query.message.edit_text(f"❌ Xatolik: {str(e)}", reply_markup=main_kb(user_id))
    
    await callback_query.answer()

# ============ VIEW ONCE HANDLERLARI ============
@router.callback_query(F.data == "connect_account")
async def connect_account(callback_query: types.CallbackQuery, state: FSMContext):
    user_id = callback_query.from_user.id
    
    if user_id in active_clients:
        await callback_query.message.edit_text("⚠️ Akkaunt allaqachon ulangan!", reply_markup=get_view_once_keyboard())
        await callback_query.answer()
        return
    
    await callback_query.message.edit_text(
        "📱 <b>Telefon raqamingizni yuboring</b>\n\n"
        "Pastdagi <b>📱 Raqamni ulashish</b> tugmasini bosing yoki raqamingizni "
        "qo'lda yozing.\nMasalan: +998901234567",
        parse_mode="HTML"
    )
    await bot.send_message(
        user_id,
        "👇 Tugmani bosing yoki raqamni qo'lda yozing:",
        reply_markup=get_phone_request_keyboard()
    )
    await state.set_state(AccountStates.waiting_phone)
    await callback_query.answer()

@router.callback_query(F.data == "my_info")
async def show_info(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    cursor.execute("SELECT phone_number, is_active, created_at FROM users WHERE user_id=?", (user_id,))
    user = cursor.fetchone()
    
    if user:
        phone, is_active, created_at = user
        status = "✅ Faol" if is_active else "❌ Nofaol"
        client_status = "🟢 Ishlamoqda" if user_id in active_clients else "🔴 To'xtatilgan"
        
        cursor.execute("SELECT COUNT(*) FROM saved_messages WHERE user_id=?", (user_id,))
        saved_count = cursor.fetchone()[0]
        
        cursor.execute("SELECT COUNT(*) FROM watched_chats WHERE user_id=? AND is_active=TRUE", (user_id,))
        watched_count = cursor.fetchone()[0]
        
        info_text = (
            f"📊 <b>Akkaunt ma'lumotlari</b>\n\n"
            f"📱 Telefon: {phone}\n"
            f"🔄 Holat: {status}\n"
            f"💻 Userbot: {client_status}\n"
            f"📥 Saqlangan: {saved_count} ta\n"
            f"👤 Kuzatilayotgan: {watched_count} ta\n"
            f"📅 Yaratilgan: {created_at}"
        )
    else:
        info_text = "❌ Akkaunt ulanmagan!"
    
    await callback_query.message.edit_text(info_text, parse_mode="HTML", reply_markup=get_view_once_keyboard())
    await callback_query.answer()

@router.callback_query(F.data == "load_old_messages")
async def load_old_messages(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    
    if user_id not in active_clients:
        await callback_query.message.edit_text("❌ Avval akkauntni ulang!", reply_markup=get_view_once_keyboard())
        await callback_query.answer()
        return
    
    await callback_query.message.edit_text("🔍 Skanerlash boshlandi...")
    await callback_query.answer()
    
    asyncio.create_task(scan_old_messages(active_clients[user_id], user_id, limit=100))

@router.callback_query(F.data == "reconnect")
async def reconnect_account(callback_query: types.CallbackQuery, state: FSMContext):
    user_id = callback_query.from_user.id
    await delete_user_data(user_id)
    
    await callback_query.message.edit_text("🔄 Eski akkaunt o'chirildi.")
    await bot.send_message(
        user_id,
        "📱 Yangi telefon raqamingizni yuboring:\n👇 Tugmani bosing yoki qo'lda yozing:",
        reply_markup=get_phone_request_keyboard()
    )
    await state.set_state(AccountStates.waiting_phone)
    await callback_query.answer()

@router.callback_query(F.data == "delete_account")
async def delete_account(callback_query: types.CallbackQuery):
    builder = InlineKeyboardBuilder()
    builder.row(
        InlineKeyboardButton(text="✅ Ha, o'chirish", callback_data="confirm_delete"),
        InlineKeyboardButton(text="❌ Yo'q", callback_data="cancel_delete")
    )
    
    await callback_query.message.edit_text(
        "⚠️ <b>Rostdan ham o'chirmoqchimisiz?</b>",
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )
    await callback_query.answer()

@router.callback_query(F.data == "confirm_delete")
async def confirm_delete(callback_query: types.CallbackQuery):
    user_id = callback_query.from_user.id
    await delete_user_data(user_id)
    
    await callback_query.message.edit_text("✅ Akkaunt o'chirildi!", reply_markup=main_kb(user_id))
    await callback_query.answer("✅ O'chirildi!")

@router.callback_query(F.data == "cancel_delete")
async def cancel_delete(callback_query: types.CallbackQuery):
    await callback_query.message.edit_text("❌ O'chirish bekor qilindi.", reply_markup=get_view_once_keyboard())
    await callback_query.answer()

@router.callback_query(F.data == "cancel_action")
async def cancel_action(callback_query: types.CallbackQuery, state: FSMContext):
    user_id = callback_query.from_user.id
    await state.clear()
    if user_id in temp_clients:
        try:
            await temp_clients[user_id]['client'].disconnect()
        except Exception:
            pass
        del temp_clients[user_id]
    await callback_query.message.edit_text("❌ Bekor qilindi.", reply_markup=main_kb(user_id))
    await callback_query.answer()

@router.callback_query(F.data == "help")
async def help_command(callback_query: types.CallbackQuery):
    help_text = (
        "ℹ️ <b>Yordam</b>\n\n"
        "📌 <b>Bo'limlar:</b>\n"
        "• 👤 FunStat tekshirish - foydalanuvchi statistikasi\n"
        "• 👁 View Once saqlash - view once xabarlarni saqlash\n"
        "• 👥 Guruh boshqaruvi - guruhlar statistikasi\n"
        "• 🔨 A'zolar boshqaruvi - guruh a'zolarini boshqarish\n\n"
        "📌 <b>Shaxsiy buyruqlar:</b>\n"
        "/start - Botni boshlash\n"
        "/stop - Profilni to'xtatish\n\n"
        "📌 <b>Guruh buyruqlari (faqat adminlar):</b>\n"
        "/change - Guruh rolini o'zgartirish (Oddiy/Nazorat)\n"
        "/ulash GURUH_ID - Oddiy guruhni nazorat guruhiga ulash\n"
        "/unlink - Ittifoqdan chiqish\n"
        "/blackwords - Guruhga xos qora ro'yxatni boshqarish"
    )
    await callback_query.message.edit_text(help_text, parse_mode="HTML", reply_markup=get_settings_keyboard())
    await callback_query.answer()

# ============ TELEFON RAQAM ============
async def _send_code_request_and_move_to_code_state(user_id: int, phone: str, message_target, state: FSMContext):
    """Telegram'ga kod yuborishni so'raydi va foydalanuvchini kod kiritish
    bosqichiga o'tkazadi. Ham matn, ham kontakt orqali kiritilgan raqam
    uchun umumiy funksiya."""
    try:
        client = TelegramClient(MemorySession(), API_ID, API_HASH)
        await client.connect()
        sent_code = await client.send_code_request(phone)

        temp_clients[user_id] = {
            'client': client,
            'phone_code_hash': sent_code.phone_code_hash,
            'phone': phone
        }

        await state.update_data(code_digits="")
        await bot.send_message(
            user_id,
            render_code_text(""),
            parse_mode="HTML",
            reply_markup=get_code_keyboard("")
        )
        await state.set_state(AccountStates.waiting_code)
    except Exception as e:
        await bot.send_message(user_id, f"❌ Xatolik: {str(e)}", reply_markup=main_kb(user_id))
        await state.clear()

@router.message(AccountStates.waiting_phone, F.contact)
async def process_phone_contact(message: types.Message, state: FSMContext):
    """Foydalanuvchi '📱 Raqamni ulashish' tugmasini bosganda keladi."""
    user_id = message.from_user.id
    phone = message.contact.phone_number
    if not phone.startswith('+'):
        phone = f"+{phone}"

    await message.answer("⏳ Kod yuborilmoqda...", reply_markup=ReplyKeyboardRemove())
    await _send_code_request_and_move_to_code_state(user_id, phone, message, state)

@router.message(AccountStates.waiting_phone)
async def process_phone(message: types.Message, state: FSMContext):
    phone = (message.text or "").strip()
    user_id = message.from_user.id
    
    if not phone.startswith('+'):
        await message.answer("❌ Telefon raqami '+' bilan boshlanishi kerak! Yoki pastdagi tugma orqali ulashing.")
        return
    
    processing_msg = await message.answer("⏳ Kod yuborilmoqda...", reply_markup=ReplyKeyboardRemove())
    await _send_code_request_and_move_to_code_state(user_id, phone, processing_msg, state)

# --- Kodni inline raqamli klaviatura orqali kiritish ---
@router.callback_query(F.data.startswith("code_digit_"), AccountStates.waiting_code)
async def code_digit_pressed(callback_query: types.CallbackQuery, state: FSMContext):
    data = await state.get_data()
    code = data.get("code_digits", "")

    if len(code) >= CODE_MAX_LENGTH:
        await callback_query.answer("⚠️ Kod to'liq kiritildi, ✅ Tasdiqlashni bosing!", show_alert=False)
        return

    digit = callback_query.data.rsplit("_", 1)[-1]
    code += digit
    await state.update_data(code_digits=code)
    await callback_query.answer()
    try:
        await callback_query.message.edit_text(render_code_text(code), parse_mode="HTML", reply_markup=get_code_keyboard(code))
    except Exception:
        pass

@router.callback_query(F.data == "code_backspace", AccountStates.waiting_code)
async def code_backspace_pressed(callback_query: types.CallbackQuery, state: FSMContext):
    await callback_query.answer()
    
    data = await state.get_data()
    code = data.get("code_digits", "")[:-1]
    await state.update_data(code_digits=code)
    try:
        await callback_query.message.edit_text(render_code_text(code), parse_mode="HTML", reply_markup=get_code_keyboard(code))
    except Exception:
        pass

@router.callback_query(F.data == "code_confirm", AccountStates.waiting_code)
async def code_confirm_pressed(callback_query: types.CallbackQuery, state: FSMContext):
    user_id = callback_query.from_user.id
    data = await state.get_data()
    code = data.get("code_digits", "")
    
    if not code:
        await callback_query.answer("❌ Avval kodni kiriting!", show_alert=True)
        return
    
    await callback_query.answer()
    
    if user_id not in temp_clients:
        await callback_query.message.edit_text("❌ Sessiya topilmadi. /start bosib qaytadan urinib ko'ring.")
        await state.clear()
        return
    
    processing_msg = callback_query.message
    await processing_msg.edit_text("⏳ Tekshirilmoqda...")
    
    try:
        client = temp_clients[user_id]['client']
        phone = temp_clients[user_id]['phone']
        phone_code_hash = temp_clients[user_id]['phone_code_hash']
        
        try:
            await client.sign_in(phone=phone, code=code, phone_code_hash=phone_code_hash)
        except SessionPasswordNeededError:
            await processing_msg.edit_text("🔐 2FA parolni kiriting (matn sifatida yozing):")
            await state.set_state(AccountStates.waiting_password)
            return
        except (PhoneCodeInvalidError, PhoneCodeExpiredError):
            await state.update_data(code_digits="")
            await processing_msg.edit_text(
                render_code_text("", error="Kod noto'g'ri yoki eskirgan!"),
                parse_mode="HTML",
                reply_markup=get_code_keyboard("")
            )
            return
        
        await finish_connection(client, user_id, phone, processing_msg, state)
        
    except Exception as e:
        logger.error(f"Kod xatolik: {e}")
        await state.update_data(code_digits="")
        await processing_msg.edit_text(
            render_code_text("", error=f"Xatolik: {str(e)}"),
            parse_mode="HTML",
            reply_markup=get_code_keyboard("")
        )

# ============ 2FA PAROLNI QABUL QILISH ============
# MUHIM TUZATISH: avvalgi versiyada AccountStates.waiting_password holatini
# ushlaydigan HECH QANDAY handler yo'q edi. code_confirm_pressed ichida
# SessionPasswordNeededError chiqqanda foydalanuvchi shu holatga
# o'tkazilardi va undan matn sifatida parol so'ralardi, lekin xabarni
# tutib oladigan funksiya mavjud emasligi sababli parol HECH QACHON
# o'qilmasdi - shuning uchun 2FA'li akkauntlarni ulash imkonsiz edi.
@router.message(AccountStates.waiting_password)
async def process_password(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    password = (message.text or "").strip()

    # Parolni chatdan darhol o'chirib tashlaymiz (xavfsizlik uchun)
    try:
        await message.delete()
    except Exception:
        pass

    if user_id not in temp_clients:
        await bot.send_message(user_id, "❌ Sessiya topilmadi. /start bosib qaytadan urinib ko'ring.")
        await state.clear()
        return

    processing_msg = await bot.send_message(user_id, "⏳ Parol tekshirilmoqda...")

    try:
        client = temp_clients[user_id]['client']
        phone = temp_clients[user_id]['phone']

        await client.sign_in(password=password)
        await finish_connection(client, user_id, phone, processing_msg, state)

    except PasswordHashInvalidError:
        await processing_msg.edit_text("❌ Parol noto'g'ri! Qaytadan kiriting:")
        # state o'zgarmaydi - foydalanuvchi yana parol yozishi mumkin
    except Exception as e:
        logger.error(f"Parol tekshirishda xatolik: {e}")
        await processing_msg.edit_text(f"❌ Xatolik: {str(e)}")
        await state.clear()

async def finish_connection(client, user_id, phone, processing_msg, state):
    try:
        session_string = client.session.save()
        
        cursor.execute(
            "INSERT OR REPLACE INTO users (user_id, session_string, phone_number, is_active) VALUES (?, ?, ?, TRUE)",
            (user_id, session_string, phone)
        )
        conn.commit()

        # DIQQAT: active_clients ga DARHOL (task ishga tushishini kutmasdan) yozamiz -
        # aks holda pastda chaqiriladigan main_kb(user_id) hali "ulanmagan" deb
        # hisoblab, "Akkauntni ulash" tugmasini noto'g'ri qayta ko'rsatib yuboradi
        # (start_userbot task sifatida ishga tushadi, lekin bu yerga hali yetib
        # kelmagan bo'ladi).
        active_clients[user_id] = client

        asyncio.create_task(start_userbot(client, user_id))
        
        await processing_msg.edit_text(
            "✅ <b>Akkaunt muvaffaqiyatli ulandi!</b>\n\n"
            "🎉 Barcha funksiyalar endi ishlaydi.",
            parse_mode="HTML",
            reply_markup=main_kb(user_id)
        )
        
        if user_id in temp_clients:
            del temp_clients[user_id]
        await state.clear()
        
    except Exception as e:
        logger.error(f"Yakunlash xatolik: {e}")
        await processing_msg.edit_text(f"❌ Xatolik: {str(e)}")
        await state.clear()

async def delete_user_data(user_id: int):
    cursor.execute("DELETE FROM users WHERE user_id=?", (user_id,))
    cursor.execute("DELETE FROM saved_messages WHERE user_id=?", (user_id,))
    cursor.execute("DELETE FROM watched_chats WHERE user_id=?", (user_id,))
    conn.commit()
    
    group_stats_cache.pop(user_id, None)
    
    if user_id in active_clients:
        try:
            await active_clients[user_id].disconnect()
        except:
            pass
        del active_clients[user_id]

async def main():
    print("=" * 60)
    print("🚀 Bot ishga tushmoqda...")
    print("📌 View Once xabarlar saqlanadi")
    print("📊 Ultra FunStat funksiyasi mavjud")
    print("👥 Guruh boshqaruvi mavjud")
    print("🔨 A'zolar boshqaruvi mavjud")
    print("=" * 60)
    
    cursor.execute("SELECT user_id, session_string FROM users WHERE is_active = TRUE")
    users = cursor.fetchall()
    
    for user_id, session_string in users:
        try:
            client = TelegramClient(StringSession(session_string), API_ID, API_HASH)
            await client.connect()
            
            if await client.is_user_authorized():
                asyncio.create_task(start_userbot(client, user_id))
                logger.info(f"User {user_id} uchun userbot qayta ishga tushirildi")
            else:
                logger.warning(f"User {user_id} sessiyasi yaroqsiz")
                cursor.execute("UPDATE users SET is_active = FALSE WHERE user_id=?", (user_id,))
                conn.commit()
        except Exception as e:
            logger.error(f"User {user_id} xatolik: {e}")
    
    try:
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        for user_id, client in active_clients.items():
            try:
                await client.disconnect()
            except:
                pass
        conn.close()

if __name__ == '__main__':
    asyncio.run(main())
