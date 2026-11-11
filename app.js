const pages = ['home', 'quran', 'reader', 'listen', 'prayer', 'favorites', 'settings'];

// ── إعدادات تحميل الصفحات عند الحاجة (كل صفحة في ملف HTML مستقل) ──
const PAGE_VERSION = '41';
const PAGE_FILES = Object.fromEntries(pages.map(page => [page, `pages/${page}.html?v=${PAGE_VERSION}`]));
const $ = id => document.getElementById(id);
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
function setTextById(id, text) { const el = document.getElementById(id); if (el) el.textContent = text; }
let currentPage = null;      // اسم الصفحة المركَّب محتواها حاليًا في الـDOM (الباقي فارغ تمامًا)
let listenSurahNumber = 1;   // السورة المختارة في صفحة الاستماع؛ تبقى في الذاكرة حتى بعد إزالة الصفحة من الـDOM
const QURAN_API = 'https://api.alquran.cloud/v1';
let surahs = []; // populated from Al Quran Cloud API
let currentSurahNumber = null;
let playingSurahNumber = null;
let listTab = 'surahs';
const ayahCache = new Map();
const juzCache = new Map();
const tafsirCache = new Map();

// ── مساعدات تحميل الآيات: مهلة زمنية، حماية من استجابات الطلبات القديمة، ومعالجة البسملة ──
const REQUEST_TIMEOUT_MS = 12000;

async function fetchJson(url, timeoutMs = REQUEST_TIMEOUT_MS) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    const res = await fetch(url, { signal: controller.signal });
    if (!res.ok) throw new Error(`http-${res.status}`);
    return await res.json();
  } catch (err) {
    if (err.name === 'AbortError') throw new Error('timeout');
    throw err;
  } finally {
    clearTimeout(timer);
  }
}

// نصّ "بِسْمِ اللَّهِ الرَّحْمَٰنِ الرَّحِيمِ" يأتي من Al Quran Cloud مدمَجًا داخل نص الآية الأولى نفسها
// لكل سورة (عدا التوبة) — بما فيها الفاتحة حيث الآية الأولى هي البسملة ذاتها. لذلك نعرض عنوان
// البسملة المستقل مرة واحدة فقط للسور العادية، ونحذف النسخة المدمجة من نص الآية الأولى لتفادي تكرارها،
// بينما لا نعرض العنوان المستقل إطلاقًا في الفاتحة (لأن آيتها الأولى هي البسملة بعينها) ولا في التوبة (لا بسملة فيها).
const BISMILLAH_TEXT = 'بِسْمِ اللَّهِ الرَّحْمَٰنِ الرَّحِيمِ';
// "بسم"، "الله"، "الرحمن"، "الرحيم" بعد تجريدها من التشكيل وتوحيد أشكال الألف — تُستخدم للمطابقة فقط
const BISMILLAH_WORDS_NORMALIZED = ['بسم', 'الله', 'الرحمن', 'الرحيم'];

// نُجرّد النص من التشكيل (الحركات) ونوحّد أشكال الألف (ٱ/أ/إ/آ ← ا) للمقارنة فقط؛ لا نستخدم الناتج للعرض
function normalizeArabicForMatch(s) {
  return s
    .replace(/[ً-ْٰۖ-ۭ﻿]/g, '') // إزالة التشكيل وعلامة BOM
    .replace(/[إأآٱ]/g, 'ا')
    .trim();
}

// نطابق البسملة على مستوى الكلمات (بعد التجريد) بدل المطابقة الحرفية للنص الكامل، لأن نص الآية الأولى
// من Al Quran Cloud يستخدم أحيانًا الألف الوصلية "ٱ" أو تشكيلًا مختلفًا قليلًا عن الشكل المعروض في العنوان المستقل،
// فتفشل المطابقة الحرفية الصامتة رغم تطابق الكلمات فعليًا. نُعيد الكلمات الأصلية غير المُجرَّدة بعد الحذف كي يبقى العرض سليمًا.
function stripLeadingBismillah(text) {
  const cleaned = text.replace(/^﻿/, '');
  const words = cleaned.split(/\s+/);
  if (words.length <= 4) return cleaned; // النص كله أربع كلمات أو أقل، على الأرجح البسملة نفسها فقط (حالة الفاتحة، لا تُستدعى هنا أصلًا)
  const matches = BISMILLAH_WORDS_NORMALIZED.every((word, i) => normalizeArabicForMatch(words[i]) === word);
  return matches ? words.slice(4).join(' ').trim() : cleaned;
}

function shouldShowBismillahHeader(surahNumber) {
  return surahNumber !== 1 && surahNumber !== 9; // لا عنوان مستقل في الفاتحة (آيتها الأولى هي البسملة) ولا في التوبة (بلا بسملة)
}

let surahRequestId = 0; // يزداد مع كل طلب فتح سورة؛ يُستخدم لتجاهل استجابة طلب سابق وصلت متأخرة
let juzRequestId = 0;   // نفس الفكرة لطلبات فتح الأجزاء
const juzOrdinals = ['الأول', 'الثاني', 'الثالث', 'الرابع', 'الخامس', 'السادس', 'السابع', 'الثامن', 'التاسع', 'العاشر', 'الحادي عشر', 'الثاني عشر', 'الثالث عشر', 'الرابع عشر', 'الخامس عشر', 'السادس عشر', 'السابع عشر', 'الثامن عشر', 'التاسع عشر', 'العشرون', 'الحادي والعشرون', 'الثاني والعشرون', 'الثالث والعشرون', 'الرابع والعشرون', 'الخامس والعشرون', 'السادس والعشرون', 'السابع والعشرون', 'الثامن والعشرون', 'التاسع والعشرون', 'الثلاثون'];
// edition/bitrate تطابق طبعات Al Quran Cloud الفعلية المتاحة على cdn.islamic.network
// country: مفتاح ترجمة (country_xx) بدل نص عربي ثابت، لتُترجم اسم البلد حسب لغة الواجهة
const reciters = [
  { name: 'مشاري راشد العفاسي', latinName: 'Mishary Rashid Alafasy', country: 'kw', initials: 'مع', latinInitials: 'MA', image: 'icons/images/Mishari.jpg', edition: 'ar.alafasy', bitrate: 128, chapterServer: 'https://server8.mp3quran.net/afs/' },
  { name: 'عبد الباسط عبد الصمد', latinName: 'Abdul Basit Abdus Samad', country: 'eg', initials: 'عب', latinInitials: 'AB', image: 'icons/images/Abdul%20Basit.jpg', edition: 'ar.abdulbasitmurattal', bitrate: 64, chapterServer: 'https://server7.mp3quran.net/basit/' },
  { name: 'عبد الرحمن السديس', latinName: 'Abdur Rahman As-Sudais', country: 'sa', initials: 'عس', latinInitials: 'AS', image: 'icons/images/Al-Sudais.jpg', edition: 'ar.abdurrahmaansudais', bitrate: 64, chapterServer: 'https://server11.mp3quran.net/sds/' },
  { name: 'ماهر المعيقلي', latinName: 'Maher Al Muaiqly', country: 'sa', initials: 'مم', latinInitials: 'MM', image: 'icons/images/Al-Muaiqly.jpg', edition: 'ar.mahermuaiqly', bitrate: 64, chapterServer: 'https://server12.mp3quran.net/maher/' },
  { name: 'سعود الشريم', latinName: 'Saud Al-Shuraim', country: 'sa', initials: 'سش', latinInitials: 'SS', image: 'icons/images/Al-Shuraim.jpg', edition: 'ar.saoodshuraym', bitrate: 64, chapterServer: 'https://server7.mp3quran.net/shur/' },
  { name: 'محمود خليل الحصري', latinName: 'Mahmoud Khalil Al-Husary', country: 'eg', initials: 'مح', latinInitials: 'MH', image: 'icons/images/alhasriu.jpg', edition: 'ar.husary', bitrate: 64, chapterServer: 'https://server13.mp3quran.net/husr/' },
  { name: 'محمد أيوب', latinName: 'Muhammad Ayyub', country: 'sa', initials: 'مأ', latinInitials: 'MA', image: 'icons/images/Ayoub.jpg', edition: 'ar.muhammadayyoub', bitrate: 128, chapterServer: 'https://server8.mp3quran.net/ayyub/' },
  { name: 'علي الحذيفي', latinName: 'Ali Al-Hudhaify', country: 'sa', initials: 'عح', latinInitials: 'AH', image: 'icons/images/Al-Hudhaifi.jpg', edition: 'ar.hudhaify', bitrate: 64, chapterServer: 'https://server9.mp3quran.net/hthfi/' },
  { name: 'محمد صديق المنشاوي', latinName: 'Muhammad Siddiq Al-Minshawi', country: 'eg', initials: 'مص', latinInitials: 'MM', image: 'icons/images/Al-Minshawi.jpg', edition: 'ar.minshawi', bitrate: 128, chapterServer: 'https://server10.mp3quran.net/minsh/' },
  { name: 'هاني الرفاعي', latinName: 'Hani Ar-Rifai', country: 'sa', initials: 'هر', latinInitials: 'HR', image: 'icons/images/Hani%20Al-Rifai.jpg', edition: 'ar.hanirifai', bitrate: 64, chapterServer: 'https://server8.mp3quran.net/hani/' },
  { name: 'أحمد بن علي العجمي', latinName: 'Ahmad Al-Ajmy', country: 'sa', initials: 'أع', latinInitials: 'AA', image: 'icons/images/Ahmed-Al-Ajmy.png', edition: 'mp3quran.5', chapterOnly: true, chapterServer: 'https://server10.mp3quran.net/ajm/' },
  { name: 'إدريس أبكر', latinName: 'Idrees Abkar', country: 'so', countryLabel: { ar: 'الصومال', en: 'Somalia' }, initials: 'إأ', latinInitials: 'IA', image: 'icons/images/Idrees-Abkar.png', edition: 'mp3quran.12', chapterOnly: true, chapterServer: 'https://server6.mp3quran.net/abkr/' },
  { name: 'ياسر الدوسري', latinName: 'Yasser Al-Dosari', country: 'sa', initials: 'يد', latinInitials: 'YD', image: 'icons/images/Yasser-Al-Dosari.png', edition: 'mp3quran.92', chapterOnly: true, chapterServer: 'https://server11.mp3quran.net/yasser/' },
  { name: 'ناصر القطامي', latinName: 'Nasser Al-Qatami', country: 'sa', initials: 'نق', latinInitials: 'NQ', image: 'icons/images/Nasser-Al-Qatami.png', edition: 'mp3quran.86', chapterOnly: true, chapterServer: 'https://server6.mp3quran.net/qtm/' },
  { name: 'أبو بكر الشاطري', latinName: 'Abu Bakr Al-Shatri', country: 'sa', initials: 'أش', latinInitials: 'AS', image: 'icons/images/Abu-Bakr-Al-Shatri.png', edition: 'mp3quran.4', chapterOnly: true, chapterServer: 'https://server11.mp3quran.net/shatri/' },
  { name: 'سعد الغامدي', latinName: 'Saad Al-Ghamdi', country: 'sa', initials: 'سغ', latinInitials: 'SG', image: 'icons/images/Saad-Al-Ghamdi.png', edition: 'mp3quran.30', chapterOnly: true, chapterServer: 'https://server7.mp3quran.net/s_gmd/' },
  { name: 'صلاح البدير', latinName: 'Salah Al-Budair', country: 'sa', initials: 'صب', latinInitials: 'SB', image: 'icons/images/Salah-Al-Budair.png', edition: 'mp3quran.43', chapterOnly: true, chapterServer: 'https://server6.mp3quran.net/s_bud/' },
  { name: 'بندر بليلة', latinName: 'Bandar Balilah', country: 'sa', initials: 'بب', latinInitials: 'BB', image: 'icons/images/Bandar-Balilah.jpg', edition: 'mp3quran.217', chapterOnly: true, chapterServer: 'https://server6.mp3quran.net/balilah/' },
  { name: 'عبدالله عواد الجهني', latinName: 'Abdullah Al-Juhany', country: 'sa', initials: 'عج', latinInitials: 'AJ', image: 'icons/images/Abdullah-Al-Juhany.png', edition: 'mp3quran.62', chapterOnly: true, chapterServer: 'https://server13.mp3quran.net/jhn/' },
  { name: 'عبدالمحسن القاسم', latinName: 'Abdulmohsen Al-Qasim', country: 'sa', initials: 'عق', latinInitials: 'AQ', image: 'icons/images/Abdulmohsen-Al-Qasim.png', edition: 'mp3quran.67', chapterOnly: true, chapterServer: 'https://server8.mp3quran.net/qasm/' },
  { name: 'علي جابر', latinName: 'Ali Jaber', country: 'sa', initials: 'عج', latinInitials: 'AJ', image: 'icons/images/Ali-Jaber.png', edition: 'mp3quran.76', chapterOnly: true, chapterServer: 'https://server11.mp3quran.net/a_jbr/' },
  { name: 'إبراهيم الأخضر', latinName: 'Ibrahim Al-Akdar', country: 'sa', initials: 'إخ', latinInitials: 'IA', image: 'icons/images/Ibrahim-Al-Akdar.png', edition: 'mp3quran.1', chapterOnly: true, chapterServer: 'https://server6.mp3quran.net/akdr/' },
  { name: 'أحمد عامر', latinName: 'Ahmed Amer', country: 'eg', initials: 'أع', latinInitials: 'AA', image: 'icons/images/Ahmed-Amer.png', edition: 'mp3quran.203', chapterOnly: true, chapterServer: 'https://server10.mp3quran.net/Aamer/' },
  { name: 'محمود علي البنا', latinName: 'Mahmoud Ali Al-Banna', country: 'eg', initials: 'مب', latinInitials: 'MB', image: 'icons/images/Mahmoud-Ali-Al-Banna.png', edition: 'mp3quran.122', chapterOnly: true, chapterServer: 'https://server8.mp3quran.net/bna/Almusshaf-Al-Mojawwad/' },
  { name: 'مصطفى إسماعيل', latinName: 'Mustafa Ismail', country: 'eg', initials: 'مإ', latinInitials: 'MI', image: 'icons/images/Mustafa-Ismail.png', edition: 'mp3quran.288', chapterOnly: true, chapterServer: 'https://server8.mp3quran.net/mustafa/Almusshaf-Al-Mojawwad/' },
  { name: 'محمد محمود الطبلاوي', latinName: 'Mohammad Al-Tablawi', country: 'eg', initials: 'مط', latinInitials: 'MT', image: 'icons/images/Mohammad-Al-Tablawi.png', edition: 'mp3quran.10912', chapterOnly: true, chapterServer: 'https://server12.mp3quran.net/tblawi/Al-Mojawwad/' },
  { name: 'أحمد نعينع', latinName: 'Ahmad Nuaina', country: 'eg', initials: 'أن', latinInitials: 'AN', image: 'icons/images/Ahmad-Nuaina.png', edition: 'mp3quran.9', chapterOnly: true, chapterServer: 'https://server11.mp3quran.net/ahmad_nu/' },
  { name: 'عبدالعزيز الأحمد', latinName: 'Abdul Aziz Al-Ahmad', country: 'sa', initials: 'عأ', latinInitials: 'AA', image: 'icons/images/Abdul-Aziz-Al-Ahmad.png', edition: 'mp3quran.55', chapterOnly: true, chapterServer: 'https://server11.mp3quran.net/a_ahmed/' },
  { name: 'عبدالله المطرود', latinName: 'Abdullah Al-Matrood', country: 'sa', initials: 'عم', latinInitials: 'AM', image: 'icons/images/Abdullah-Al-Matrood.png', edition: 'mp3quran.59', chapterOnly: true, chapterServer: 'https://server8.mp3quran.net/mtrod/' },
  { name: 'عبدالله بصفر', latinName: 'Abdullah Basfar', country: 'sa', initials: 'عب', latinInitials: 'AB', image: 'icons/images/Abdullah-Basfar.png', edition: 'mp3quran.60', chapterOnly: true, chapterServer: 'https://server6.mp3quran.net/bsfr/' }
];
let currentReciter = reciters[0];
let playQueue = []; // أرقام الآيات العالمية (across the whole Quran) للسورة الجارية
let queueIndex = 0;
// أرقام شرقية (١٢٣) تُعرض فقط عند اختيار العربية لغةً وتفعيل مفتاح "الأرقام العربية"؛ غير ذلك أرقام غربية عادية
const requestedLanguage = new URLSearchParams(location.search).get('lang');
let currentLang = (requestedLanguage && i18n[requestedLanguage] ? requestedLanguage : storage_get_early()) || 'ar';
let easternNumeralsOn = true;
function storage_get_early() {
  try { const raw = localStorage.getItem('qaraen:language'); return raw ? JSON.parse(raw) : null; } catch (err) { return null; }
}
const eastern = value => (currentLang === 'ar' && easternNumeralsOn) ? String(value).replace(/\d/g, digit => '٠١٢٣٤٥٦٧٨٩'[digit]) : String(value);
const toastBox = document.getElementById('toast');

function toast(message) {
  toastBox.textContent = message;
  toastBox.className = 'toast show';
  clearTimeout(toastBox.timer);
  toastBox.timer = setTimeout(() => toastBox.classList.remove('show'), 2400);
}

// ── تخزين محلي (localStorage) ───────────────────────────────
const STORAGE_PREFIX = 'qaraen:';
const storage = {
  get(key, fallback = null) {
    try {
      const raw = localStorage.getItem(STORAGE_PREFIX + key);
      return raw === null ? fallback : JSON.parse(raw);
    } catch (err) { return fallback; } // وضع التصفح الخاص أو تعطيل التخزين قد يرمي استثناء
  },
  set(key, value) {
    try { localStorage.setItem(STORAGE_PREFIX + key, JSON.stringify(value)); } catch (err) { /* تجاهل: تخزين ممتلئ أو معطّل */ }
  },
  clearAll() {
    try {
      Object.keys(localStorage).filter(k => k.startsWith(STORAGE_PREFIX)).forEach(k => localStorage.removeItem(k));
    } catch (err) { /* تجاهل */ }
  }
};

// نصوص الوظائف الجديدة؛ العربية للواجهات العربية، والإنجليزية لبقية اللغات حتى لا يظهر مفتاح تقني للمستخدم.
const extraStrings = {
  ar: {
    audio_loading: 'جاري تحميل ملف التلاوة…', audio_ready: 'جاهز للتشغيل', audio_playing: 'قيد التشغيل',
    audio_paused: 'متوقف مؤقتًا', audio_blocked: 'منع المتصفح التشغيل التلقائي؛ اضغط زر التشغيل للمتابعة.',
    audio_fallback: 'تعذّر ملف السورة الكامل؛ جارٍ استخدام تشغيل الآيات الاحتياطي…',
    audio_ended: 'انتهت التلاوة', font_saved: 'تم حفظ حجم خط القرآن', shared: 'تمت المشاركة', link_copied: 'تم نسخ رابط السورة',
    share_failed: 'تعذرت المشاركة أو نسخ الرابط', saved_ayahs: 'الآيات المفضلة', saved_positions: 'مواضع القراءة المحفوظة',
    saved_surahs_label: 'السور المفضلة', open_item: 'فتح', remove_item: 'حذف', save_ayah: 'حفظ الآية', remove_ayah: 'إزالة الآية', share_ayah: 'مشاركة الآية',
    ayah_saved: 'أُضيفت الآية إلى المفضلة', ayah_removed: 'أُزيلت الآية من المفضلة', position_removed: 'حُذف موضع القراءة',
    full_recitations_via: '· تلاوات السور الكاملة عبر', automatic_on: 'تم تفعيل الانتقال التلقائي بين السور',
    automatic_off: 'تم إيقاف الانتقال التلقائي', automatic_enable: 'تفعيل الانتقال التلقائي بين السور',
    automatic_disable: 'إيقاف الانتقال التلقائي بين السور', quran_recitation_ended: 'اكتملت تلاوة القرآن الكريم',
    select_search: 'ابحث في الخيارات…', select_close: 'إغلاق القائمة', select_empty: 'لا توجد خيارات مطابقة'
  },
  en: {
    audio_loading: 'Loading recitation audio…', audio_ready: 'Ready to play', audio_playing: 'Playing',
    audio_paused: 'Paused', audio_blocked: 'Autoplay was blocked; press Play to continue.', audio_ended: 'Recitation finished',
    audio_fallback: 'The full-surah file failed; switching to verse playback…',
    font_saved: 'Quran font size saved', shared: 'Shared', link_copied: 'Surah link copied', share_failed: 'Could not share or copy the link',
    saved_ayahs: 'Favorite verses', saved_positions: 'Saved reading positions', saved_surahs_label: 'Favorite surahs',
    open_item: 'Open', remove_item: 'Delete', save_ayah: 'Save verse', remove_ayah: 'Remove verse', share_ayah: 'Share verse', ayah_saved: 'Verse added to favorites',
    ayah_removed: 'Verse removed from favorites', position_removed: 'Reading position deleted', full_recitations_via: '· Full-surah recitations via',
    automatic_on: 'Automatic surah advance enabled', automatic_off: 'Automatic surah advance disabled',
    automatic_enable: 'Enable automatic surah advance', automatic_disable: 'Disable automatic surah advance', quran_recitation_ended: 'Quran recitation complete',
    select_search: 'Search options…', select_close: 'Close list', select_empty: 'No matching options'
  }
};
function tx(key, vars) {
  let str = (usesArabicScript() ? extraStrings.ar : extraStrings.en)[key] || key;
  if (vars) Object.keys(vars).forEach(k => { str = str.replace(`{${k}}`, vars[k]); });
  return str;
}
Object.assign(extraStrings.ar, {
  listen_ayah: 'إستماع للآية', download_surah: 'تنزيل السورة', download_preparing: 'جاري تجهيز ملف السورة…',
  download_done: 'تم تنزيل السورة كملف HTML', download_failed: 'تعذّر تنزيل السورة',
  explanation_loading: 'جاري تحميل التفسير…', explanation_error: 'تعذّر تحميل التفسير.',
  position_saved_ayah: 'تم حفظ الآية كآخر موقع قراءة', wird_today: 'وردك اليوم: {n} آية',
  automatic_unavailable: 'الانتقال التلقائي غير متاح أثناء الاستماع من صفحة القراءة',
  ayah_reciter_notice: 'تلاوة الآية الواحدة متاحة بصوت مشاري العفاسي', page_load_error: 'تعذّر تحميل الصفحة.',
  ayah_word: 'الآية'
});
Object.assign(extraStrings.en, {
  listen_ayah: 'Listen to verse', download_surah: 'Download surah', download_preparing: 'Preparing the surah file…',
  download_done: 'Surah downloaded as an HTML file', download_failed: 'Could not download the surah',
  explanation_loading: 'Loading explanation…', explanation_error: 'Could not load the explanation.',
  position_saved_ayah: 'Verse saved as your last reading position', wird_today: "Today's wird: {n} verses",
  automatic_unavailable: 'Automatic advance is unavailable while listening from the reader',
  ayah_reciter_notice: 'Single-verse audio plays in Mishary Alafasy’s voice', page_load_error: 'Could not load the page.',
  ayah_word: 'Verse'
});

const savedReciterEdition = storage.get('audioReciter', null);
currentReciter = reciters.find(r => r.edition === savedReciterEdition) || currentReciter;

// ── تطبيق لغة الواجهة (i18n) ──────────────────────────────────
// ملاحظة صادقة حول النطاق: نص القرآن الكريم وأسماء السور والقرّاء تبقى بالعربية دائمًا
// (كالمعتاد في تطبيقات القرآن)؛ الترجمة هنا لواجهة التطبيق (الأزرار والعناوين والرسائل) فقط.
const RTL_LANGS = ['ar', 'ur', 'fa'];
const FORWARD_I18N_KEYS = new Set(['view_all_times', 'open_mushaf', 'all_reciters']);
const usesArabicScript = () => RTL_LANGS.includes(currentLang);

const ICON_PATHS = {
  home: '<path d="M3 11.5 12 4l9 7.5"/><path d="M5.5 10.5V20h13v-9.5"/><path d="M9.5 20v-6h5v6"/>',
  book: '<path d="M4 5.5A3.5 3.5 0 0 1 7.5 2H12v18H7.5A3.5 3.5 0 0 0 4 23z"/><path d="M20 5.5A3.5 3.5 0 0 0 16.5 2H12v18h4.5A3.5 3.5 0 0 1 20 23z"/>',
  headphones: '<path d="M4 14v-2a8 8 0 0 1 16 0v2"/><path d="M4 14h3v6H5a1 1 0 0 1-1-1zM20 14h-3v6h2a1 1 0 0 0 1-1z"/>',
  clock: '<circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/>',
  heart: '<path d="M20.8 4.6a5.5 5.5 0 0 0-7.8 0L12 5.7l-1.1-1.1a5.5 5.5 0 0 0-7.8 7.8L12 21l8.8-8.6a5.5 5.5 0 0 0 0-7.8z"/>',
  settings: '<circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.7 1.7 0 0 0 .3 1.9l.1.1-2.8 2.8-.1-.1a1.7 1.7 0 0 0-1.9-.3 1.7 1.7 0 0 0-1 1.6v.2h-4V21a1.7 1.7 0 0 0-1-1.6 1.7 1.7 0 0 0-1.9.3l-.1.1L4.2 17l.1-.1a1.7 1.7 0 0 0 .3-1.9A1.7 1.7 0 0 0 3 14H2.8v-4H3a1.7 1.7 0 0 0 1.6-1 1.7 1.7 0 0 0-.3-1.9L4.2 7 7 4.2l.1.1a1.7 1.7 0 0 0 1.9.3A1.7 1.7 0 0 0 10 3V2.8h4V3a1.7 1.7 0 0 0 1 1.6 1.7 1.7 0 0 0 1.9-.3l.1-.1L19.8 7l-.1.1a1.7 1.7 0 0 0-.3 1.9 1.7 1.7 0 0 0 1.6 1h.2v4H21a1.7 1.7 0 0 0-1.6 1z"/>',
  sparkle: '<path d="m12 3 1.4 4.1L17.5 8.5l-4.1 1.4L12 14l-1.4-4.1-4.1-1.4 4.1-1.4zM18.5 15l.8 2.2 2.2.8-2.2.8-.8 2.2-.8-2.2-2.2-.8 2.2-.8z"/>',
  moon: '<path d="M20.5 14.5A8.5 8.5 0 0 1 9.5 3.5a8.5 8.5 0 1 0 11 11z"/>',
  sun: '<circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/>',
  pin: '<path d="M20 10c0 5-8 12-8 12S4 15 4 10a8 8 0 1 1 16 0z"/><circle cx="12" cy="10" r="2.5"/>',
  search: '<circle cx="11" cy="11" r="7"/><path d="m20 20-4-4"/>',
  menu: '<path d="M4 7h16M4 12h16M4 17h16"/>',
  play: '<path d="m9 7 8 5-8 5z"/>', pause: '<path d="M9 7v10M15 7v10"/>',
  arrowLeft: '<path d="M19 12H5M11 18l-6-6 6-6"/>', arrowRight: '<path d="M5 12h14M13 6l6 6-6 6"/>',
  chevronLeft: '<path d="m15 18-6-6 6-6"/>', chevronRight: '<path d="m9 18 6-6-6-6"/>',
  skipBack: '<path d="M19 20 9 12l10-8zM5 19V5"/>', skipForward: '<path d="m5 4 10 8-10 8zM19 5v14"/>',
  autoplay: '<path d="M20 7V3l-1.7 1.7A9 9 0 1 0 21 12"/><path d="M16 3h4v4"/><path d="m10 8 6 4-6 4z"/>',
  check: '<path d="m5 12 4 4L19 6"/>', chevronDown: '<path d="m6 9 6 6 6-6"/>',
  close: '<path d="M6 6l12 12M18 6 6 18"/>',
  bookmark: '<path d="M6 3h12v18l-6-4-6 4z"/>',
  share: '<circle cx="18" cy="5" r="2"/><circle cx="6" cy="12" r="2"/><circle cx="18" cy="19" r="2"/><path d="m8 11 8-5M8 13l8 5"/>',
  volume: '<path d="M5 10H2v4h3l4 4V6zM13 9a4 4 0 0 1 0 6M16 6a8 8 0 0 1 0 12"/>',
  textSize: '<path d="M4 7V4h12v3M10 4v16M7 20h6M15 11h6M18 11v9M16 20h4"/>',
  palette: '<path d="M12 3a9 9 0 0 0 0 18h1.5a2 2 0 0 0 0-4H12a2 2 0 0 1 0-4h5a4 4 0 0 0 4-4c0-3.3-4-6-9-6z"/><circle cx="7.5" cy="9" r=".8"/><circle cx="10" cy="6.5" r=".8"/><circle cx="14" cy="6.5" r=".8"/>',
  bell: '<path d="M18 8a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9M10 21h4"/>',
  trash: '<path d="M4 7h16M9 7V4h6v3M7 7l1 14h8l1-14M10 11v6M14 11v6"/>',
  info: '<circle cx="12" cy="12" r="9"/><path d="M12 11v6M12 7h.01"/>',
  navigation: '<path d="m12 3 7 18-7-4-7 4z"/>',
  sunrise: '<path d="M4 18h16M6 14a6 6 0 0 1 12 0M12 3v4M4.9 6.9l2.1 2M19.1 6.9l-2.1 2"/>',
  sunset: '<path d="M4 18h16M6 14a6 6 0 0 1 12 0M12 7V3M9 5l3-3 3 3"/>',
  download: '<path d="M12 3v12M7 10l5 5 5-5M4 21h16"/>',
  language: '<circle cx="12" cy="12" r="9"/><path d="M3 12h18M12 3a14 14 0 0 1 0 18M12 3a14 14 0 0 0 0 18"/>'
};

function icon(name, className = '') {
  return `<svg class="ui-icon${className ? ` ${className}` : ''}" viewBox="0 0 24 24" aria-hidden="true" focusable="false">${ICON_PATHS[name] || ICON_PATHS.info}</svg>`;
}
function cleanIconText(value) { return String(value || '').replace(/[⌂☷◉◷♡♥⚙☾☀⌖⌕←→↷↶×✦♜◐◒◓▶↗]/g, '').trim(); }
function setIconLabel(element, iconName, label = '') {
  if (!element) return;
  element.classList.add('has-icon');
  element.innerHTML = `${icon(iconName)}${label ? `<span>${label}</span>` : ''}`;
}
function hydrateStaticIcons(root = document) {
  root.querySelectorAll('[data-icon]').forEach(element => { element.innerHTML = icon(element.dataset.icon); });
}

// ── قوائم اختيار مخصصة مع إبقاء <select> الأصلي مصدرًا للقيمة والأحداث ──
const customSelectInstances = new Map();
let activeCustomSelect = null;
let customSelectLayer = null;
let customSelectDrag = null;
function isTouchUiMode() { return matchMedia('(pointer: coarse)').matches || matchMedia('(max-width: 760px)').matches; }
// لا نضيف أي إدخال في تاريخ المتصفح للقوائم والنوافذ؛ أسهم المتصفح مخصّصة للتنقّل بين الصفحات فقط
function pushTouchUiHistory() {}
function ensureCustomSelectLayer() {
  if (customSelectLayer) return customSelectLayer;
  customSelectLayer = document.createElement('div');
  customSelectLayer.id = 'customSelectLayer';
  customSelectLayer.className = 'custom-select-layer';
  customSelectLayer.hidden = true;
  customSelectLayer.innerHTML = `<section class="custom-select-panel" role="dialog" aria-modal="false" aria-labelledby="customSelectTitle"><header><strong id="customSelectTitle"></strong><button type="button" class="custom-select-close" aria-label="${tx('select_close')}">${icon('close')}</button></header><label class="custom-select-search"><span>${icon('search')}</span><input type="search" autocomplete="off" placeholder="${tx('select_search')}"></label><div class="custom-select-options" id="customSelectOptions" role="listbox"></div></section>`;
  document.body.appendChild(customSelectLayer);
  customSelectLayer.querySelector('.custom-select-close').onclick = () => closeCustomSelect();
  customSelectLayer.addEventListener('click', event => { if (event.target === customSelectLayer) closeCustomSelect(); });
  customSelectLayer.querySelector('input').addEventListener('input', event => renderCustomSelectOptions(event.target.value));
  customSelectLayer.addEventListener('keydown', handleCustomSelectKeyboard);
  const dragHeader = customSelectLayer.querySelector('.custom-select-panel > header');
  dragHeader.addEventListener('pointerdown', startCustomSelectDrag);
  dragHeader.addEventListener('pointermove', moveCustomSelectDrag);
  dragHeader.addEventListener('pointerup', finishCustomSelectDrag);
  dragHeader.addEventListener('pointercancel', finishCustomSelectDrag);
  return customSelectLayer;
}
function customSelectTitle(select) {
  return select.closest('label')?.querySelector(':scope > span')?.textContent?.trim() || select.getAttribute('aria-label') || '';
}
function refreshCustomSelect(select) {
  const instance = customSelectInstances.get(select);
  if (!instance) return;
  instance.trigger.querySelector('.custom-select-value').textContent = select.selectedOptions[0]?.textContent?.trim() || '';
  instance.trigger.disabled = select.disabled;
  if (activeCustomSelect?.select === select) renderCustomSelectOptions(customSelectLayer.querySelector('input').value);
}
function refreshAllCustomSelects() { customSelectInstances.forEach((_, select) => refreshCustomSelect(select)); }
function renderCustomSelectOptions(query = '') {
  if (!activeCustomSelect || !customSelectLayer) return;
  const { select } = activeCustomSelect;
  const box = customSelectLayer.querySelector('.custom-select-options');
  const normalizedQuery = query.trim().toLocaleLowerCase(currentLang);
  const options = Array.from(select.options).filter(option => !option.hidden && option.textContent.trim().toLocaleLowerCase(currentLang).includes(normalizedQuery));
  box.innerHTML = '';
  if (!options.length) {
    const empty = document.createElement('p'); empty.className = 'custom-select-empty'; empty.textContent = tx('select_empty'); box.appendChild(empty); return;
  }
  options.forEach(option => {
    const button = document.createElement('button');
    button.type = 'button'; button.className = 'custom-select-option'; button.disabled = option.disabled;
    button.setAttribute('role', 'option'); button.setAttribute('aria-selected', String(option.selected));
    const label = document.createElement('span'); label.textContent = option.textContent.trim();
    const mark = document.createElement('span'); mark.className = 'custom-select-check'; if (option.selected) mark.innerHTML = icon('check');
    button.append(label, mark);
    button.onclick = () => { select.value = option.value; select.dispatchEvent(new Event('change', { bubbles: true })); refreshCustomSelect(select); closeCustomSelect(); };
    box.appendChild(button);
  });
  setTimeout(() => box.querySelector('[aria-selected="true"]')?.scrollIntoView({ block: 'center', behavior: 'auto' }), 0);
}
function visibleCustomSelectOptions() {
  if (!customSelectLayer) return [];
  return Array.from(customSelectLayer.querySelectorAll('.custom-select-option:not(:disabled)'));
}
function focusCustomSelectOption(direction, fromElement) {
  const options = visibleCustomSelectOptions();
  if (!options.length) return;
  const currentIndex = options.indexOf(fromElement);
  let nextIndex;
  if (direction === 'first') nextIndex = 0;
  else if (direction === 'last') nextIndex = options.length - 1;
  else if (currentIndex < 0) {
    const selectedIndex = options.findIndex(option => option.getAttribute('aria-selected') === 'true');
    nextIndex = selectedIndex >= 0 ? selectedIndex : (direction > 0 ? 0 : options.length - 1);
  } else nextIndex = (currentIndex + direction + options.length) % options.length;
  const next = options[nextIndex];
  next.focus({ preventScroll: true });
  // scroll-margin وscroll-padding في CSS يتركان 6px مرئية أعلى العنصر وأسفله.
  next.scrollIntoView({ block: 'nearest', behavior: 'auto' });
}
function handleCustomSelectKeyboard(event) {
  if (!activeCustomSelect) return;
  const option = event.target.closest?.('.custom-select-option');
  if (event.key === 'ArrowDown' || event.key === 'ArrowUp') {
    event.preventDefault();
    focusCustomSelectOption(event.key === 'ArrowDown' ? 1 : -1, option);
  } else if (option && (event.key === 'Home' || event.key === 'End')) {
    event.preventDefault();
    focusCustomSelectOption(event.key === 'Home' ? 'first' : 'last', option);
  }
}
function resetCustomSelectDragStyles() {
  if (!customSelectLayer) return;
  const panel = customSelectLayer.querySelector('.custom-select-panel');
  panel.classList.remove('dragging', 'settling', 'dismissing');
  customSelectLayer.classList.remove('drag-finishing');
  panel.style.removeProperty('transform');
  panel.style.removeProperty('opacity');
  customSelectLayer.style.removeProperty('background-color');
  customSelectDrag = null;
}
function startCustomSelectDrag(event) {
  if (!isTouchUiMode() || event.button !== 0 || event.target.closest('button')) return;
  customSelectLayer.classList.remove('drag-finishing');
  customSelectDrag = { pointerId: event.pointerId, startY: event.clientY, lastY: event.clientY, lastAt: performance.now(), velocity: 0, distance: 0, started: false };
  event.currentTarget.setPointerCapture?.(event.pointerId);
  event.preventDefault();
}
function moveCustomSelectDrag(event) {
  if (!customSelectDrag || event.pointerId !== customSelectDrag.pointerId) return;
  const now = performance.now();
  const elapsed = Math.max(1, now - customSelectDrag.lastAt);
  const distance = Math.max(0, event.clientY - customSelectDrag.startY);
  customSelectDrag.velocity = (event.clientY - customSelectDrag.lastY) / elapsed;
  customSelectDrag.lastY = event.clientY;
  customSelectDrag.lastAt = now;
  customSelectDrag.distance = distance;
  const panel = customSelectLayer.querySelector('.custom-select-panel');
  // السحب للأعلى ليس إيماءة إغلاق: لا نوقف حركة الفتح ولا نحرك النافذة بسببه.
  if (event.clientY <= customSelectDrag.startY) {
    if (customSelectDrag.started) {
      panel.style.transform = 'translateY(0)';
      panel.style.opacity = '1';
      customSelectLayer.style.removeProperty('background-color');
    }
    event.preventDefault();
    return;
  }
  if (!customSelectDrag.started) {
    customSelectDrag.started = true;
    panel.classList.add('dragging');
  }
  const progress = Math.min(1, distance / Math.max(180, panel.offsetHeight * .55));
  panel.style.transform = `translateY(${distance}px)`;
  panel.style.opacity = String(1 - progress * .35);
  customSelectLayer.style.backgroundColor = `rgba(15,30,25,${.5 * (1 - progress)})`;
  event.preventDefault();
}
function finishCustomSelectDrag(event) {
  if (!customSelectDrag || event.pointerId !== customSelectDrag.pointerId) return;
  const panel = customSelectLayer.querySelector('.custom-select-panel');
  if (!customSelectDrag.started) {
    event.currentTarget.releasePointerCapture?.(event.pointerId);
    resetCustomSelectDragStyles();
    return;
  }
  const dismiss = customSelectDrag.distance > Math.min(160, panel.offsetHeight * .28) || (customSelectDrag.distance > 38 && customSelectDrag.velocity > .65);
  event.currentTarget.releasePointerCapture?.(event.pointerId);
  panel.classList.remove('dragging');
  if (dismiss) {
    customSelectLayer.classList.add('drag-finishing');
    panel.classList.add('dismissing');
    panel.style.transform = `translateY(${panel.offsetHeight + 32}px)`;
    panel.style.opacity = '0';
    customSelectLayer.style.backgroundColor = 'rgba(15,30,25,0)';
    customSelectDrag = null;
    setTimeout(() => closeCustomSelect({ restoreFocus: false }), 190);
  } else {
    customSelectLayer.classList.add('drag-finishing');
    panel.classList.add('settling');
    panel.style.transform = 'translateY(0)';
    panel.style.opacity = '1';
    customSelectLayer.style.removeProperty('background-color');
    customSelectDrag = null;
    setTimeout(resetCustomSelectDragStyles, 190);
  }
}
function positionCustomSelect() {
  if (!activeCustomSelect || !customSelectLayer || customSelectLayer.hidden) return;
  const panel = customSelectLayer.querySelector('.custom-select-panel');
  const touch = isTouchUiMode();
  customSelectLayer.classList.toggle('touch', touch); customSelectLayer.classList.toggle('desktop', !touch);
  panel.style.cssText = ''; panel.setAttribute('aria-modal', String(touch));
  if (touch) return;
  const rect = activeCustomSelect.trigger.getBoundingClientRect();
  const margin = 12; const width = Math.min(Math.max(rect.width, 250), innerWidth - margin * 2);
  const gap = 7;
  const spaceBelow = innerHeight - rect.bottom - margin - gap;
  const spaceAbove = rect.top - margin - gap;
  const placeAbove = spaceBelow < 220 && spaceAbove > spaceBelow;
  const maxHeight = Math.max(120, Math.min(420, placeAbove ? spaceAbove : spaceBelow));
  const left = Math.min(Math.max(margin, rect.left), innerWidth - width - margin);
  // عند الظهور للأعلى نثبّت القائمة من الأسفل لتلتصق بالمشغّل بدل ترك فراغ بحسب الارتفاع الأقصى
  const vertical = placeAbove ? { bottom: `${innerHeight - rect.top + gap}px` } : { top: `${rect.bottom + gap}px` };
  Object.assign(panel.style, { width: `${width}px`, maxHeight: `${maxHeight}px`, left: `${left}px`, ...vertical });
}
function openCustomSelect(select) {
  const instance = customSelectInstances.get(select); if (!instance || select.disabled) return;
  // النقر المتكرر على المشغّل نفسه يغلق القائمة، والانتقال لقائمة أخرى يعيد حالة المشغّل السابق فورًا.
  if (activeCustomSelect?.select === select) { closeCustomSelect(); return; }
  if (activeCustomSelect) closeCustomSelect({ restoreFocus: false });
  closeFontMenu(); ensureCustomSelectLayer(); activeCustomSelect = { select, trigger: instance.trigger };
  customSelectLayer.querySelector('#customSelectTitle').textContent = customSelectTitle(select);
  const search = customSelectLayer.querySelector('.custom-select-search'); const input = search.querySelector('input');
  input.placeholder = tx('select_search'); customSelectLayer.querySelector('.custom-select-close').setAttribute('aria-label', tx('select_close'));
  input.value = ''; search.hidden = select.options.length <= 20; customSelectLayer.hidden = false;
  instance.trigger.setAttribute('aria-expanded', 'true'); renderCustomSelectOptions(); positionCustomSelect(); pushTouchUiHistory('custom-select');
  setTimeout(() => (search.hidden ? customSelectLayer.querySelector('[aria-selected="true"]') : input)?.focus(), 0);
}
function closeCustomSelect({ restoreFocus = true } = {}) {
  if (!activeCustomSelect || !customSelectLayer) return;
  const trigger = activeCustomSelect.trigger; trigger.setAttribute('aria-expanded', 'false'); customSelectLayer.hidden = true; activeCustomSelect = null; resetCustomSelectDragStyles();
  if (restoreFocus) trigger.focus();
}
function initCustomSelects(root = document) {
  root.querySelectorAll('select').forEach(select => {
    if (customSelectInstances.has(select)) return;
    select.classList.add('custom-select-native');
    const trigger = document.createElement('button'); trigger.type = 'button'; trigger.className = 'custom-select-trigger';
    trigger.setAttribute('role', 'combobox'); trigger.setAttribute('aria-haspopup', 'listbox'); trigger.setAttribute('aria-expanded', 'false');
    trigger.setAttribute('aria-controls', 'customSelectOptions');
    trigger.innerHTML = `<span class="custom-select-value"></span><span class="custom-select-chevron">${icon('chevronDown')}</span>`;
    select.insertAdjacentElement('afterend', trigger); const observer = new MutationObserver(() => refreshCustomSelect(select));
    customSelectInstances.set(select, { trigger, observer });
    trigger.onclick = event => { event.preventDefault(); openCustomSelect(select); };
    trigger.onkeydown = event => {
      if (event.key !== 'ArrowDown' && event.key !== 'ArrowUp') return;
      event.preventDefault();
      if (!activeCustomSelect || activeCustomSelect.select !== select) openCustomSelect(select);
      setTimeout(() => focusCustomSelectOption(event.key === 'ArrowDown' ? 1 : -1, null), 0);
    };
    select.addEventListener('change', () => refreshCustomSelect(select));
    observer.observe(select, { childList: true, subtree: true, characterData: true });
    refreshCustomSelect(select);
  });
}
// عند إزالة صفحة من الـDOM نحرّر قوائمها المخصصة ومراقِباتها
function destroyCustomSelects(root) {
  root.querySelectorAll('select').forEach(select => {
    const instance = customSelectInstances.get(select);
    if (!instance) return;
    if (activeCustomSelect?.select === select) closeCustomSelect({ restoreFocus: false });
    instance.observer?.disconnect();
    customSelectInstances.delete(select);
  });
}
window.addEventListener('resize', () => { if (activeCustomSelect) positionCustomSelect(); });
if ('ResizeObserver' in window) new ResizeObserver(() => { if (activeCustomSelect) positionCustomSelect(); }).observe(document.body);
document.addEventListener('pointerdown', event => {
  if (!activeCustomSelect || isTouchUiMode()) return;
  if (!event.target.closest('.custom-select-panel') && !event.target.closest('.custom-select-trigger')) closeCustomSelect({ restoreFocus: false });
});

function decorateLocalizedControls(root = document) {
  const controls = [
    ['saveReading', 'download', tx('download_surah')], ['listenCurrentSurah', 'headphones', t('listen_to_surah')],
    ['shareCurrentSurah', 'share', t('share_action')], ['ListenToAverse', 'headphones', tx('listen_ayah')]
  ];
  controls.forEach(([id, name, label]) => setIconLabel(document.getElementById(id), name, cleanIconText(label)));
  root.querySelectorAll('[data-i18n="use_my_location"]').forEach(element => setIconLabel(element, 'pin', cleanIconText(t('use_my_location'))));
  const themeQuick = document.getElementById('themeQuick');
  if (themeQuick) themeQuick.innerHTML = icon(document.body.classList.contains('dark') ? 'sun' : 'moon');
}

function localizeDirectionalIcons(root = document) {
  const rtl = usesArabicScript();
  root.querySelectorAll('[data-i18n]').forEach(el => {
    const key = el.dataset.i18n;
    if (FORWARD_I18N_KEYS.has(key)) setIconLabel(el, rtl ? 'arrowLeft' : 'arrowRight', cleanIconText(t(key)));
    if (key === 'back_to_surahs') setIconLabel(el, rtl ? 'arrowRight' : 'arrowLeft', cleanIconText(t(key)));
  });
  root.querySelectorAll('.directional-arrow').forEach(el => { el.innerHTML = icon(rtl ? 'arrowLeft' : 'arrowRight'); });
  root.querySelectorAll('.setting-chevron').forEach(el => { el.innerHTML = icon(rtl ? 'chevronLeft' : 'chevronRight'); });
  const previous = root.querySelector('[data-direction-icon="previous"]');
  const next = root.querySelector('[data-direction-icon="next"]');
  if (previous) previous.innerHTML = icon(rtl ? 'chevronRight' : 'chevronLeft');
  if (next) next.innerHTML = icon(rtl ? 'chevronLeft' : 'chevronRight');
}

// يطبّق الترجمة والأيقونات على جذر معيّن: الصفحة كلها (الهيكل الثابت) أو قسم صفحة حُمِّل لتوّه
function localizeRoot(root = document) {
  root.querySelectorAll('[data-i18n]').forEach(el => { el.textContent = t(el.dataset.i18n); });
  root.querySelectorAll('[data-i18n-aria]').forEach(el => el.setAttribute('aria-label', t(el.dataset.i18nAria)));
  root.querySelectorAll('[data-i18n-placeholder]').forEach(el => { el.placeholder = t(el.dataset.i18nPlaceholder); });
  hydrateStaticIcons(root);
  localizeDirectionalIcons(root);
  decorateLocalizedControls(root);
}

function applyLanguage(code) {
  if (!i18n[code]) code = 'ar';
  currentLang = code;
  storage.set('language', code);
  document.documentElement.lang = code;
  document.documentElement.dir = RTL_LANGS.includes(code) ? 'rtl' : 'ltr';
  document.documentElement.dataset.script = usesArabicScript() ? 'arabic' : 'international';
  document.getElementById('brandName').textContent = usesArabicScript() ? 'نور القرآن' : 'Nur al quran';
  document.getElementById('brandMark').innerHTML = usesArabicScript() ? '<img src="icons/logo.png" alt="">' : '<img src="icons/logo.png" alt="">';
  document.querySelector('meta[name="apple-mobile-web-app-title"]')?.setAttribute('content', 'نور القرآن');
  document.title = 'نور القرآن';
  document.querySelector('meta[name="description"]')?.setAttribute('content', t('meta_description'));
  localizeRoot(document); // الهيكل الثابت + الصفحة المركَّبة حاليًا فقط (بقية الصفحات غير موجودة في الـDOM)
  document.querySelector('.brand')?.setAttribute('aria-label', currentLang === 'ar' ? 'نور القرآن - الرئيسية' : 'Nur al Quran - Home');
  const fullRecitationsCredit = document.getElementById('fullRecitationsCredit');
  if (fullRecitationsCredit) fullRecitationsCredit.textContent = tx('full_recitations_via');
  syncAutomaticButton();
  renderLocalDateFallback();
  // إعادة رسم الأجزاء الديناميكية للصفحة المركَّبة حاليًا حتى تنعكس اللغة الجديدة على النصوص المولَّدة من JS
  pageModules[currentPage]?.render?.();
  if (!document.getElementById('player').hidden) {
    const activeSurah = surahs.find(s => s.number === playingSurahNumber);
    if (activeSurah && !singleAyahMode) {
      document.getElementById('trackTitle').textContent = surahDisplayName(activeSurah);
      updatePlayerReciterPhoto(currentReciter);
    }
    document.getElementById('trackReciter').textContent = reciterDisplayName(singleAyahReciter || currentReciter);
  }
  if (todayTimings) updateTopbarDate(todayTimings.date);
  // اسم الموقع الافتراضي (الرياض) يُعاد حسابه فورًا بلغته الجديدة؛ الاسم الحقيقي المرصود (تلقائي أو يدوي) يُعاد جلبه
  // من خدمة تحديد الموقع بلغته الجديدة (طلب شبكة غير حاجب) مع الحفاظ على مصدر الموقع الحالي كما هو
  if (!userCoords) userLocationLabel = defaultLocationLabel();
  updateLocationUI();
  if (userCoords) {
    if (locationIsFallback) {
      userLocationLabel = defaultLocationLabel();
      updateLocationUI();
    } else if (locationSource !== 'manual') {
      // لا نعيد الجلب العكسي لموقع اختير يدويًا: اسمه معروف بالفعل من نتيجة البحث ولا يعتمد على لغة الواجهة بنفس الدقة
      reverseGeocode(userCoords, locationSource).then(() => {
        const label = document.getElementById('prayerLocationLabel');
        if (label && !label.textContent.includes('...')) label.textContent = `${userLocationLabel} · ${locationSourceLabel()} · ${methodLabel()}`;
      });
    }
    const label = document.getElementById('prayerLocationLabel');
    if (label && !label.textContent.includes('...')) label.textContent = `${userLocationLabel} · ${locationSourceLabel()} · ${methodLabel()}`;
  }
  refreshAllCustomSelects();
}

// ── تسجيل Service Worker (تصفح دون اتصال + تثبيت PWA) ────────
if ('serviceWorker' in navigator) {
  window.addEventListener('load', () => {
    navigator.serviceWorker.register('sw.js').catch(() => {
      // فشل التسجيل (مثلًا فتح الموقع عبر file:// أو دون HTTPS) لا يجب أن يعطّل بقية التطبيق
    });
  });
}

// ── مدير الصفحات: كل صفحة في ملف HTML مستقل داخل pages/ ──────────────────
// لا يُجلب محتوى أي صفحة إلا عند الانتقال إليها، وعند مغادرتها يُفرَّغ قسمها من الـDOM بالكامل؛
// يبقى في index.html الحاويات الفارغة (#homePage … #settingsPage) فقط.
const pageHtmlCache = new Map(); // نص HTML فقط (ليس عناصر DOM) لتفادي إعادة الجلب عند العودة لصفحة زُرتها
const pageReady = new Map();     // اسم الصفحة ← وعد يتحقق (true) عند اكتمال تركيبها في الـDOM
let routeToken = 0;

function pageSection(name) { return document.getElementById(`${name}Page`); }

async function loadPageHtml(name) {
  if (pageHtmlCache.has(name)) return pageHtmlCache.get(name);
  const res = await fetch(PAGE_FILES[name]);
  if (!res.ok) throw new Error(`page-${res.status}`);
  const html = await res.text();
  pageHtmlCache.set(name, html);
  return html;
}

async function mountPage(name) {
  const section = pageSection(name);
  section.setAttribute('aria-busy', 'true');
  try {
    const html = await loadPageHtml(name);
    if (currentPage !== name) return false; // انتقل المستخدم لصفحة أخرى أثناء الجلب
    section.innerHTML = html;
    section.removeAttribute('aria-busy');
    localizeRoot(section);
    pageModules[name]?.mount?.(section);
    initCustomSelects(section);
    return true;
  } catch (err) {
    console.error(`[pages] تعذّر تركيب صفحة ${name} (${PAGE_FILES[name]}):`, err);
    if (currentPage === name) {
      section.removeAttribute('aria-busy');
      section.innerHTML = `<div class="empty-inline">${tx('page_load_error')} <small dir="ltr">${escapeHtml(PAGE_FILES[name])} — ${escapeHtml(err && err.message || err)}</small> <button type="button" class="text-button" id="retryPageLoad">${t('retry')}</button></div>`;
      $('retryPageLoad').onclick = () => { unmountPage(name); route(name, { fromHistory: true }); };
    }
    return false;
  }
}

function unmountPage(name) {
  const section = pageSection(name);
  if (!section) return;
  pageModules[name]?.unmount?.(section);
  destroyCustomSelects(section);
  section.replaceChildren(); // إزالة محتوى الصفحة من الـDOM
  section.classList.remove('active');
  section.removeAttribute('aria-busy');
  pageReady.delete(name);
  if (currentPage === name) currentPage = null;
}

async function route(name, { fromHistory = false, restore = true, shareParams = false } = {}) {
  if (!pages.includes(name)) name = 'home';
  const token = ++routeToken;
  const previous = currentPage;
  // مشغّل التلاوة عام للتطبيق؛ يبقى الصوت مستمرًا عند التنقّل بين الصفحات ولا يتوقف إلا بأمر المستخدم
  // أو عند إغلاق المشغّل. عنصر <audio> نفسه خارج أقسام الصفحات، لذلك لا يتأثر بإزالة محتوى الصفحات.
  // نحفظ موضع القراءة تلقائيًا عند مغادرة صفحة القارئ فعليًا إلى صفحة أخرى — ويتم ذلك قبل إفراغ الـDOM لأن الحفظ يقرأ الآيات الظاهرة منه
  if (previous === 'reader' && name !== 'reader') autoCommitReadingPosition();
  if (!document.getElementById('ayahActionsModal')?.hidden) closeAyahActions();
  document.querySelectorAll('.nav-item').forEach(button => button.classList.toggle('active', button.dataset.route === name));
  setMenuOpen(false);
  // ندفع إدخالًا جديدًا في تاريخ المتصفح (بدل استبداله) ليعمل زرّا التنقّل للخلف/للأمام بين الصفحات؛
  // عند الوصول عبر popstate (ضغط المستخدم زر الرجوع) لا نُعيد الدفع تفاديًا لحلقة تكرار
  if (!fromHistory && location.hash.slice(1) !== name) history.pushState({ route: name }, '', `#${name}`);
  // فوري لا سلس: تمرير سلس هنا كان يتعارض مع استعادة موضع آية دقيق في صفحة القارئ
  window.scrollTo({ top: 0, behavior: 'auto' });
  if (previous && previous !== name) unmountPage(previous);
  if (currentPage === name) {            // الصفحة مركَّبة (أو قيد التركيب) بالفعل؛ ننتظر اكتمالها فقط
    return Boolean(await pageReady.get(name));
  }
  currentPage = name;
  pages.forEach(page => pageSection(page)?.classList.toggle('active', page === name));
  const ready = mountPage(name);
  pageReady.set(name, ready);
  const ok = await ready;
  if (!ok || token !== routeToken || currentPage !== name) return false;
  if (name === 'reader' && restore) await restoreReader({ useShareParams: shareParams });
  return true;
}

// عند فتح صفحة القارئ دون اختيار سورة/جزء صريح (الرجوع بزر المتصفح، أو فتح الرابط مباشرة) نعيد تحميل آخر ما كان مفتوحًا،
// فتعود القراءة إلى آخر آية محفوظة كما كانت قبل إزالة الصفحة من الـDOM
async function restoreReader({ useShareParams = false } = {}) {
  const savedReaderState = storage.get('readerState', null);
  const lastReading = storage.get('lastReading', null);
  const params = new URLSearchParams(location.search);
  const sharedSurahNumber = useShareParams ? +params.get('surah') : 0;
  const sharedAyahNumber = useShareParams ? +params.get('ayah') : 0;
  const savedNumber = +savedReaderState?.number;
  if (Number.isInteger(sharedSurahNumber) && sharedSurahNumber >= 1 && sharedSurahNumber <= 114) {
    return openSurah(sharedSurahNumber, { focusAyahNumber: Number.isInteger(sharedAyahNumber) && sharedAyahNumber > 0 ? sharedAyahNumber : null });
  }
  if (savedReaderState?.type === 'surah' && Number.isInteger(savedNumber) && savedNumber >= 1 && savedNumber <= 114) return openSurah(savedNumber);
  if (savedReaderState?.type === 'juz' && Number.isInteger(savedNumber) && savedNumber >= 1 && savedNumber <= 30) return openJuz(savedNumber);
  if (lastReading?.number) return openSurah(+lastReading.number);
  return route('quran', { fromHistory: true });
}

function closeAllTransientUi() {
  if (activeCustomSelect) closeCustomSelect({ restoreFocus: false });
  closeFontMenu();
  if (!document.getElementById('ayahActionsModal')?.hidden) closeAyahActions();
  if (!document.getElementById('aboutModal')?.hidden) closeAboutModal();
  if (!document.getElementById('locationModal')?.hidden) closeLocationModal();
  setMenuOpen(false);
}
window.addEventListener('popstate', () => {
  // أسهم المتصفح (رجوع/تقدّم) تنتقل بين الصفحات فقط ولا تُستخدم لإغلاق القوائم؛ أي قائمة مفتوحة تُغلق تلقائيًا عند الانتقال
  closeAllTransientUi();
  route((location.hash || '#home').slice(1), { fromHistory: true });
});

const sidebarEl = document.getElementById('appSidebar');
const backdropEl = document.getElementById('backdrop');
const menuButtonEl = document.getElementById('menuButton');
function setMenuOpen(open) {
  const shouldOpen = Boolean(open && matchMedia('(max-width: 760px)').matches);
  const wasOpen = sidebarEl.classList.contains('open');
  sidebarEl.classList.toggle('open', shouldOpen);
  backdropEl.classList.toggle('show', shouldOpen);
  menuButtonEl.setAttribute('aria-expanded', String(shouldOpen));
  document.body.classList.toggle('menu-open', shouldOpen);
  if (shouldOpen && !wasOpen) pushTouchUiHistory('sidebar');
}
document.addEventListener('click', event => {
  const button = event.target.closest('[data-route]');
  if (!button) return;
  setMenuOpen(false);
  route(button.dataset.route);
});
menuButtonEl.addEventListener('click', () => setMenuOpen(!sidebarEl.classList.contains('open')));
backdropEl.addEventListener('click', () => setMenuOpen(false));
document.addEventListener('keydown', event => {
  if (event.key !== 'Escape') return;
  if (activeCustomSelect) closeCustomSelect({ restoreFocus: false });
  setMenuOpen(false);
  closeFontMenu();
  if (!document.getElementById('ayahActionsModal')?.hidden) closeAyahActions();
  if (!document.getElementById('aboutModal')?.hidden) closeAboutModal();
  if (!document.getElementById('locationModal')?.hidden) closeLocationModal();
});
// إغلاق القوائم المنبثقة عند التمرير بعجلة الفأرة أو بالسحب خارج القائمة نفسها
function closeFloatingMenusOnScroll(event) {
  const target = event.target;
  if (target instanceof Element && target.closest('.custom-select-panel, .font-menu, .sidebar')) return;
  closeFontMenu();
  if (activeCustomSelect && customSelectLayer?.classList.contains('desktop')) closeCustomSelect({ restoreFocus: false });
  if (sidebarEl.classList.contains('open')) setMenuOpen(false);
}
window.addEventListener('wheel', closeFloatingMenusOnScroll, { passive: true });
document.addEventListener('scroll', closeFloatingMenusOnScroll, { capture: true, passive: true });
const desktopQuery = matchMedia('(min-width: 761px)');
const closeMenuOnDesktop = event => { if (event.matches) setMenuOpen(false); };
desktopQuery.addEventListener?.('change', closeMenuOnDesktop);

// رسم عناصر قائمة على دفعات: دفعة تلو الأخرى مع انتظار قصير بينها؛ تتوقف فورًا إن أصبح الرسم قديمًا (isStale)
async function renderInBatches(container, items, buildHtml, batchSize, delayMs, isStale) {
  container.replaceChildren();
  for (let i = 0; i < items.length; i += batchSize) {
    if (isStale()) return false;
    container.insertAdjacentHTML('beforeend', items.slice(i, i + batchSize).map(buildHtml).join(''));
    if (i + batchSize < items.length) await sleep(delayMs);
  }
  return !isStale();
}

let surahsPromise = null;
let surahsLoadFailed = false;
let surahListRenderId = 0;

function showSurahListError() {
  const list = $('surahList');
  if (list) list.innerHTML = `<div class="empty-inline">${t('surahs_error')} <button id="retrySurahList" type="button" class="text-button">${t('retry')}</button></div>`;
}

// قائمة السور بياناتٌ عامة يحتاجها أكثر من صفحة (المحفوظات، الاستماع، المشغّل)، لذا تُجلب مرة واحدة؛ أما رسمها فيخص صفحة القرآن فقط
function loadSurahList() {
  const list = $('surahList');
  if (list) list.innerHTML = `<div class="empty-inline">${t('loading_surahs')}</div>`;
  surahsLoadFailed = false;
  surahsPromise = (async () => {
    try {
      const res = await fetch(`${QURAN_API}/surah`);
      if (!res.ok) throw new Error('network');
      const json = await res.json();
      surahs = json.data;
      pageModules[currentPage]?.render?.();
      return true;
    } catch (err) {
      surahsLoadFailed = true;
      showSurahListError();
      return false;
    }
  })();
  return surahsPromise;
}

function revelationLabel(type) { return t(type === 'Meccan' ? 'meccan' : 'medinan'); }
function surahDisplayName(surah) { return usesArabicScript() ? surah.name : surah.englishName; }
function reciterDisplayName(reciter) { return usesArabicScript() ? reciter.name : reciter.latinName; }
function reciterDisplayInitials(reciter) { return usesArabicScript() ? reciter.initials : reciter.latinInitials; }
function updatePlayerReciterPhoto(reciter = currentReciter) {
  const holder = document.querySelector('.player-surah');
  if (!holder || !reciter) return;
  const image = document.createElement('img');
  image.src = reciter.image;
  image.alt = usesArabicScript() ? `صورة القارئ ${reciterDisplayName(reciter)}` : `Photo of reciter ${reciterDisplayName(reciter)}`;
  image.decoding = 'async';
  holder.replaceChildren(image);
}

// أسماء السور تُرسم 10 أسماء ثم 10 بعدها بفاصل 1 مللي ثانية
async function renderSurahs(filter = '') {
  const list = $('surahList');
  if (!list || !surahs.length) return;
  const token = ++surahListRenderId;
  const query = filter.trim();
  const items = surahs.filter(s => s.name.includes(query) || s.englishName.toLowerCase().includes(query.toLowerCase()) || String(s.number).includes(query));
  const favs = getFavorites();
  if (!items.length) { list.innerHTML = `<div class="empty-inline">${t('no_surah_match')}</div>`; return; }
  const build = s => `<button class="surah-item" data-surah-number="${s.number}"><span class="surah-number">${eastern(s.number)}</span><div><b>${surahDisplayName(s)}</b><small>${revelationLabel(s.revelationType)} · ${eastern(s.numberOfAyahs)} ${t('ayah_suffix')}</small></div><span class="fav-toggle${favs.includes(s.number) ? ' active' : ''}" data-fav-number="${s.number}" role="button" tabindex="0" aria-label="${t('fav_toggle_aria')}">${icon('heart')}</span><span class="surah-arabic" lang="ar" dir="rtl">${s.name}</span></button>`;
  await renderInBatches(list, items, build, 10, 1, () => token !== surahListRenderId || $('surahList') !== list);
}

// أجزاء القرآن: نفس أسلوب التحميل التدريجي (10 ثم 10 بفاصل 1 مللي ثانية) داخل نفس #surahList
async function renderJuzList(filter = '') {
  const list = $('surahList');
  if (!list) return;
  const token = ++surahListRenderId;
  const query = filter.trim();
  const items = juzOrdinals
    .map((ordinal, index) => ({ number: index + 1, ordinal }))
    .filter(j => juzOrdinals[j.number - 1].includes(query) || String(j.number).includes(query));
  if (!items.length) { list.innerHTML = `<div class="empty-inline">${t('no_juz_match')}</div>`; return; }
  const build = j => `<button class="surah-item" data-juz-number="${j.number}"><span class="surah-number">${eastern(j.number)}</span><div><b>${juzTitle(j.number)}</b><small>${t('juz_of_30', { n: eastern(j.number) })}</small></div><span class="surah-arabic">${eastern(j.number)}</span></button>`;
  await renderInBatches(list, items, build, 10, 1, () => token !== surahListRenderId || $('surahList') !== list);
}

function renderCurrentSurahList() {
  const search = $('surahSearch');
  const value = search ? search.value : '';
  if (listTab === 'surahs') renderSurahs(value); else renderJuzList(value);
}

function onSurahListClick(event) {
  if (event.target.closest('#retrySurahList')) { loadSurahList(); return; }
  const fav = event.target.closest('[data-fav-number]');
  if (fav) { event.stopPropagation(); toggleFavorite(+fav.dataset.favNumber); return; }
  const surahButton = event.target.closest('[data-surah-number]');
  if (surahButton) { openSurah(+surahButton.dataset.surahNumber); return; }
  const juzButton = event.target.closest('[data-juz-number]');
  if (juzButton) openJuz(+juzButton.dataset.juzNumber);
}

function syncListTabsUI() {
  $('tabSurahs')?.classList.toggle('active', listTab === 'surahs');
  $('tabJuz')?.classList.toggle('active', listTab === 'juz');
  const search = $('surahSearch');
  if (search) search.placeholder = t(listTab === 'surahs' ? 'search_surah_ph' : 'search_juz_ph');
}

function switchListTab(tab) {
  listTab = tab;
  const searchInput = $('surahSearch');
  if (searchInput) searchInput.value = '';
  syncListTabsUI();
  renderCurrentSurahList();
}

function mountQuran() {
  $('tabSurahs').onclick = () => switchListTab('surahs');
  $('tabJuz').onclick = () => switchListTab('juz');
  $('surahSearch').oninput = event => {
    if (listTab === 'surahs') renderSurahs(event.target.value); else renderJuzList(event.target.value);
  };
  const list = $('surahList');
  list.onclick = onSurahListClick;
  list.onkeydown = event => {
    const fav = event.target.closest?.('[data-fav-number]');
    if (fav && (event.key === 'Enter' || event.key === ' ')) { event.preventDefault(); toggleFavorite(+fav.dataset.favNumber); }
  };
  renderQuranPage();
}

function renderQuranPage() {
  if (!$('surahList')) return;
  syncListTabsUI();
  renderKhatmaCard();
  if (listTab === 'juz') { renderJuzList($('surahSearch').value); return; }
  if (surahs.length) { renderSurahs($('surahSearch').value); return; }
  if (surahsLoadFailed) showSurahListError();
  else $('surahList').innerHTML = `<div class="empty-inline">${t('loading_surahs')}</div>`;
}

// ── المفضّلة وآخر قراءة (localStorage) ───────────────────────
function getFavorites() { return storage.get('favorites', []); }
function isFavorite(number) { return getFavorites().includes(number); }

function toggleFavorite(number) {
  const favs = getFavorites();
  const idx = favs.indexOf(number);
  if (idx === -1) { favs.push(number); toast(t('toast_fav_added')); }
  else { favs.splice(idx, 1); toast(t('toast_fav_removed')); }
  storage.set('favorites', favs);
  // نحدّث القلب في مكانه دون إعادة رسم القائمة (لتفادي القفز ومعاودة التحميل التدريجي)
  document.querySelectorAll(`#surahList [data-fav-number="${number}"]`).forEach(el => el.classList.toggle('active', favs.includes(number)));
  renderFavoritesPage();
}

function getFavoriteAyahs() { return storage.get('favoriteAyahs', []); }
function ayahKey(surahNumber, ayahNumber) { return `${surahNumber}:${ayahNumber}`; }
function isFavoriteAyah(surahNumber, ayahNumber) {
  return getFavoriteAyahs().some(item => ayahKey(item.surahNumber, item.ayahNumber) === ayahKey(surahNumber, ayahNumber));
}
function toggleFavoriteAyah(item) {
  const items = getFavoriteAyahs();
  const key = ayahKey(item.surahNumber, item.ayahNumber);
  const index = items.findIndex(saved => ayahKey(saved.surahNumber, saved.ayahNumber) === key);
  if (index >= 0) { items.splice(index, 1); toast(tx('ayah_removed')); }
  else { items.unshift({ ...item, savedAt: Date.now() }); toast(tx('ayah_saved')); }
  storage.set('favoriteAyahs', items);
  renderFavoritesPage();
  updateAyahActionState();
}

function getSavedPositions() {
  const positions = storage.get('savedPositions', []);
  const latestSeven = Array.isArray(positions) ? positions.slice(0, 7) : [];
  if (Array.isArray(positions) && positions.length > 7) storage.set('savedPositions', latestSeven);
  return latestSeven;
}
function saveReadingPositionEntry(number, ayahInfo) {
  const meta = surahs.find(s => s.number === number) || ayahCache.get(number);
  if (!meta) return;
  const ayahNumber = ayahInfo?.numberInSurah || 1;
  const positions = getSavedPositions().filter(item => !(item.number === number && item.ayahNumberInSurah === ayahNumber));
  positions.unshift({
    number, name: meta.name, englishName: meta.englishName, revelationType: meta.revelationType,
    numberOfAyahs: meta.numberOfAyahs, ayahNumberInSurah: ayahNumber,
    globalAyahNumber: ayahInfo?.globalNumber || null, juz: ayahInfo?.juz || null, savedAt: Date.now()
  });
  storage.set('savedPositions', positions.slice(0, 7));
  renderFavoritesPage();
}

// ── موضع القراءة (منفصل تمامًا عن قائمة "favorites" المفضّلة؛ مفتاح تخزين مستقل ولا تُنشئ إحداهما الأخرى أو تعدّلها) ──
// ayahInfo (اختياري): {numberInSurah, globalNumber, juz} — الآية الدقيقة المطلوب حفظها.
// إن لم تُمرَّر وكانت السورة نفسها محفوظة مسبقًا، نُبقي على موضع الآية المحفوظ سابقًا بدل إعادته للآية الأولى؛
// أما عند فتح سورة مختلفة عن المحفوظة فنبدأ من الآية الأولى حتى تُحفظ آية أدق أثناء القراءة.
function saveLastReading(number, ayahInfo = null) {
  const meta = surahs.find(s => s.number === number) || ayahCache.get(number);
  if (!meta) return;
  const existing = storage.get('lastReading', null);
  const position = ayahInfo
    ? { ayahNumberInSurah: ayahInfo.numberInSurah, globalAyahNumber: ayahInfo.globalNumber, juz: ayahInfo.juz }
    : (existing?.number === number
      ? { ayahNumberInSurah: existing.ayahNumberInSurah || 1, globalAyahNumber: existing.globalAyahNumber || null, juz: existing.juz || null }
      : { ayahNumberInSurah: 1, globalAyahNumber: null, juz: null });
  const record = {
    number: meta.number,
    name: meta.name,
    englishName: meta.englishName,
    numberOfAyahs: meta.numberOfAyahs,
    revelationType: meta.revelationType,
    ...position,
    savedAt: Date.now()
  };
  updateDailyWird(existing?.globalAyahNumber, record.globalAyahNumber);
  storage.set('lastReading', record);
  ensureKhatmaStarted();
  const progressPercent = khatmaPercentFrom(record.globalAyahNumber, record.juz);
  storage.set('khatmaProgress', {
    surahNumber: record.number,
    ayahNumberInSurah: record.ayahNumberInSurah || 1,
    globalAyahNumber: record.globalAyahNumber || null,
    juz: record.juz || null,
    percent: progressPercent,
    updatedAt: record.savedAt
  });
  renderContinueCard();
  renderKhatmaCard();
  highlightSavedAyah();
}

// ── الختمة الحالية: تُحسب من موضع آخر قراءة فعلي (lastReading)، وليست بيانات عرض ثابتة ──
// نقطة البداية: أول مرة يُحفظ فيها موضع قراءة تُسجَّل كبداية الختمة الحالية في localStorage
function ensureKhatmaStarted() {
  let khatma = storage.get('khatma', null);
  if (!khatma) {
    khatma = { startedAt: Date.now() };
    storage.set('khatma', khatma);
  }
  return khatma;
}

// لا نعرض ٠٪ بعد بدء القراءة: الآيات الأولى أقل من نصف بالمئة فتُقرب رياضيًا إلى صفر،
// وهو ما يوحي خطأً بأن الحفظ لم يعمل. نعرض حدًا أدنى ١٪ مع إبقاء الحساب الدقيق لبقية الختمة.
function khatmaPercentFrom(globalAyahNumber, juz) {
  const globalNumber = Number(globalAyahNumber);
  const juzNumber = Number(juz);
  if (globalNumber > 0) return Math.max(1, Math.min(100, Math.round((globalNumber / 6236) * 100)));
  if (juzNumber > 0) return Math.max(1, Math.min(100, Math.round((juzNumber / 30) * 100)));
  return 1;
}

function paintKhatmaProgress(percent, juz) {
  const safePercent = Math.max(0, Math.min(100, Number(percent) || 0));
  const safeJuz = Math.max(0, Math.min(30, Number(juz) || 0));
  const percentText = `${eastern(safePercent)}%`;
  const gradient = `conic-gradient(var(--gold) ${safePercent}%, var(--surface-2) 0)`;
  const percentEl = document.getElementById('khatmaPercent');
  const completionEl = document.querySelector('.completion b');
  const ringStrongEl = document.querySelector('.ring strong');
  const ringEl = document.querySelector('.ring');
  const completionRingEl = document.querySelector('.completion');
  if (percentEl) percentEl.textContent = percentText;
  if (completionEl) completionEl.textContent = percentText;
  if (ringStrongEl) ringStrongEl.textContent = eastern(safeJuz);
  if (ringEl) ringEl.style.background = gradient;
  if (completionRingEl) completionRingEl.style.background = gradient;
  paintDailyWird();
}

// ── الورد اليومي: يُحسب من موضع القراءة المحفوظ؛ بداية اليوم = آخر موضع محفوظ قبل أول حفظ في هذا اليوم ──
function updateDailyWird(previousGlobal, newGlobal) {
  if (!(Number(newGlobal) > 0)) return;
  const today = new Date().toDateString();
  let wird = storage.get('dailyWird', null);
  if (!wird || wird.date !== today) wird = { date: today, startGlobal: Number(previousGlobal) > 0 ? Number(previousGlobal) : Number(newGlobal) };
  wird.currentGlobal = Number(newGlobal);
  storage.set('dailyWird', wird);
}
function dailyWirdCount() {
  const wird = storage.get('dailyWird', null);
  if (!wird || wird.date !== new Date().toDateString()) return 0;
  return Math.max(0, (Number(wird.currentGlobal) || 0) - (Number(wird.startGlobal) || 0));
}
function paintDailyWird() {
  const tip = document.querySelector('.khatma-card p');
  if (!tip) return;
  const count = dailyWirdCount();
  tip.textContent = count > 0 ? tx('wird_today', { n: eastern(count) }) : t('khatma_tip');
}

// نعتمد جزء الآية الفعلية المحفوظة في موضع القراءة (وليس أول آية في السورة) كلما توفّر ذلك،
// فتعكس نسبة الختمة تقدّم القراءة الحقيقي داخل السورة لا مجرد كونها مفتوحة
async function currentJuzFromLastReading(last = storage.get('lastReading', null)) {
  if (!last) return null;
  if (last.juz) return last.juz; // محفوظ مسبقًا من موضع قراءة دقيق (آية فعلية تمّ تمرير الآيات إليها أو حفظها يدويًا)
  // توافقًا مع سجلات محفوظة قبل إضافة تتبّع الآية الدقيق، أو حين لا تتوفر آية محددة بعد: نستخدم أول آية في السورة كتقريب
  let data = ayahCache.get(last.number);
  if (!data) {
    try {
      const json = await fetchJson(`${QURAN_API}/surah/${last.number}/quran-uthmani`);
      data = json.data;
      ayahCache.set(last.number, data);
    } catch (err) { /* تعذّر الجلب؛ سيُعاد المحاولة عند أول تصيير لاحق */ }
  }
  return data?.ayahs?.[0]?.juz ?? null;
}

let khatmaRenderId = 0;
async function renderKhatmaCard() {
  const renderId = ++khatmaRenderId;
  const last = storage.get('lastReading', null);
  if (!last) {
    paintKhatmaProgress(0, 0);
    return;
  }
  ensureKhatmaStarted();
  const persistedProgress = storage.get('khatmaProgress', null);
  if (persistedProgress?.surahNumber === last.number) {
    const savedPct = Number(persistedProgress.percent) > 0
      ? Number(persistedProgress.percent)
      : khatmaPercentFrom(persistedProgress.globalAyahNumber || last.globalAyahNumber, persistedProgress.juz || last.juz);
    const savedJuz = Math.max(1, Math.min(30, Number(persistedProgress.juz) || 1));
    paintKhatmaProgress(savedPct, savedJuz);
  } else {
    paintKhatmaProgress(khatmaPercentFrom(last.globalAyahNumber, last.juz), last.juz || 1);
  }
  const juz = (await currentJuzFromLastReading(last)) || 1;
  const latestReading = storage.get('lastReading', null);
  if (renderId !== khatmaRenderId || latestReading?.number !== last.number || latestReading?.savedAt !== last.savedAt) return;
  const pct = khatmaPercentFrom(last.globalAyahNumber, juz);
  paintKhatmaProgress(pct, juz);
  storage.set('khatmaProgress', { surahNumber: last.number, ayahNumberInSurah: last.ayahNumberInSurah || 1, globalAyahNumber: last.globalAyahNumber || null, juz, percent: pct, updatedAt: last.savedAt || Date.now() });
}

// ── تتبّع الآية الظاهرة أثناء التمرير + تمييز آخر آية محفوظة بصريًا ──────────────
let currentVisibleAyah = null; // {numberInSurah, globalNumber, juz} لأحدث آية رُصدت في منتصف منطقة القراءة أثناء التمرير
let ayahScrollHandler = null; // مستمع "scroll" الحالي على window؛ يُزال ويُستبدل عند كل فتح سورة جديدة
// صحيح أثناء نقل القارئ تلقائيًا إلى موضعه المحفوظ عقب فتح سورة (scrollToSavedAyah): نمنع الحفظ التلقائي
// (إغلاق التبويب/تصفّح بعيدًا) خلال هذه النافذة الزمنية القصيرة، لأن القراءة اللحظية لموضع التمرير قبل استقرار
// القفزة قد تكون مضلِّلة (مثلًا أعلى الصفحة قبل أن ينفّذ المتصفح القفزة إلى الآية المحفوظة)
let isRestoringPosition = false;
// صحيح فقط بعد أن يُمرِّر المستخدم فعليًا (حدث scroll حقيقي) خلال جلسة القراءة الحالية؛ القراءة الأولية
// التي تُحسب فور فتح السورة (قبل أي تمرير فعلي) لا تُعتبر تتبّعًا موثوقًا ولا يُسمح لها بالحفظ التلقائي،
// حتى لا تُستبدل قراءة سابقة صحيحة بموضع عرضي غير مقصود (مثل بداية السورة) عند إغلاق التبويب مبكرًا
let hasUserScrolledThisSession = false;

// نعتمد على حدث scroll مع getBoundingClientRect بدل IntersectionObserver: نحسب يدويًا أي آية أقرب
// لمنتصف الشاشة رأسيًا (منطقة نظر القارئ المعتادة)، وهو أسلوب مباشر ويعمل بشكل متسق عبر المتصفحات
function updateVisibleAyahFromScroll(units) {
  const viewportCenter = window.innerHeight / 2;
  let best = null, bestDist = Infinity;
  for (const u of units) {
    const rect = u.getBoundingClientRect();
    if (rect.bottom < 0 || rect.top > window.innerHeight) continue; // تجاهل ما هو خارج الشاشة تمامًا لتسريع الحساب
    const center = (rect.top + rect.bottom) / 2;
    const dist = Math.abs(center - viewportCenter);
    if (dist < bestDist) { bestDist = dist; best = u; }
  }
  if (best) {
    currentVisibleAyah = {
      numberInSurah: +best.dataset.ayahNumber,
      globalNumber: +best.dataset.globalAyah,
      juz: +best.dataset.juz
    };
  }
}

function setupAyahScrollTracking() {
  if (ayahScrollHandler) { window.removeEventListener('scroll', ayahScrollHandler); ayahScrollHandler = null; }
  currentVisibleAyah = null;
  hasUserScrolledThisSession = false;
  const units = Array.from(document.querySelectorAll('#ayahText .ayah-unit'));
  if (!units.length) return;
  // نستخدم setTimeout بدل requestAnimationFrame للتهدئة (debounce): rAF يتوقف عن العمل في التبويبات
  // غير المرئية/الخلفية في بعض المتصفحات، بينما setTimeout يستمر بالعمل بشكل موثوق في كل الحالات
  let debounceTimer = null;
  ayahScrollHandler = () => {
    hasUserScrolledThisSession = true; // حدث تمرير حقيقي من المستخدم، بخلاف القراءة الأولية أدناه
    clearTimeout(debounceTimer);
    debounceTimer = setTimeout(() => updateVisibleAyahFromScroll(units), 80);
  };
  window.addEventListener('scroll', ayahScrollHandler, { passive: true });
  updateVisibleAyahFromScroll(units); // نحسب الآية الظاهرة فور فتح السورة للعرض الفوري فقط، دون اعتبارها تمريرًا فعليًا
}

function highlightSavedAyah() {
  document.querySelectorAll('#ayahText .ayah-unit.saved-position').forEach(el => el.classList.remove('saved-position'));
  const last = storage.get('lastReading', null);
  if (!last || last.number !== currentSurahNumber || !last.ayahNumberInSurah) return;
  const el = document.querySelector(`#ayahText .ayah-unit[data-ayah-number="${last.ayahNumberInSurah}"]`);
  if (el) el.classList.add('saved-position');
}

// يُستدعى بعد رسم آيات سورة تطابق سورة موضع القراءة المحفوظ، لإعادة القارئ إلى آيته الدقيقة بدل بداية السورة
function scrollToSavedAyah() {
  const last = storage.get('lastReading', null);
  if (!last || last.number !== currentSurahNumber || !last.ayahNumberInSurah || last.ayahNumberInSurah <= 1) return;
  isRestoringPosition = true;
  // نستخدم setTimeout بدل requestAnimationFrame: rAF قد لا يُنفَّذ في تبويب غير مرئي/خلفي عند الاستعادة التلقائية بعد التحميل
  setTimeout(() => {
    const el = document.querySelector(`#ayahText .ayah-unit[data-ayah-number="${last.ayahNumberInSurah}"]`);
    el?.scrollIntoView({ behavior: 'auto', block: 'center' });
    // مهلة إضافية قصيرة حتى يهدأ أي حدث scroll ناتج عن القفزة (ومُهلة التهدئة 80ms الخاصة به) قبل السماح مجددًا بالحفظ التلقائي
    setTimeout(() => { isRestoringPosition = false; }, 250);
  }, 0);
}

// نحفظ الموضع تلقائيًا عند مغادرة صفحة القارئ (تصفّح لصفحة أخرى) اعتمادًا على آخر آية رُصدت أثناء التمرير،
// حتى لو لم يضغط المستخدم زر الحفظ اليدوي صراحةً
function autoCommitReadingPosition() {
  if (isRestoringPosition) return; // تفادي حفظ موضع غير مستقر أثناء نقل القارئ تلقائيًا إلى موضعه المحفوظ عقب فتح السورة
  if (!hasUserScrolledThisSession) return; // لم يُمرِّر المستخدم فعليًا بعد؛ لا نستبدل موضعًا محفوظًا بقراءة أولية غير موثوقة
  const units = Array.from(document.querySelectorAll('#ayahText .ayah-unit'));
  if (units.length) updateVisibleAyahFromScroll(units); // قراءة متزامنة أخيرة قبل الإغلاق حتى لا يسبق pagehide مؤقّت التهدئة
  if (currentSurahNumber && currentVisibleAyah) {
    saveLastReading(currentSurahNumber, currentVisibleAyah);
  }
}
// نحفظ الموضع أيضًا عند إغلاق التبويب أو تحديث الصفحة أو تصغيرها، لا فقط عند التنقّل داخل التطبيق،
// حتى لا يُفقد تتبّع الآية أثناء التمرير إن أعاد المستخدم تحميل الصفحة مباشرة دون تنقّل صريح
window.addEventListener('pagehide', autoCommitReadingPosition);
window.addEventListener('beforeunload', autoCommitReadingPosition);
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden') autoCommitReadingPosition(); });

function renderContinueCard() {
  const card = document.querySelector('.continue-card');
  if (!card) return;
  const last = storage.get('lastReading', null);
  const medallion = card.querySelector('.surah-medallion');
  const title = card.querySelector('h3');
  const meta = card.querySelector('p');
  const progress = card.querySelector('.progress');
  const button = card.querySelector('.round-play');
  if (last) {
    medallion.textContent = last.name.replace('سورة ', '').slice(0, 2);
    title.textContent = usesArabicScript() ? last.name : (last.englishName || last.name);
    meta.textContent = `${revelationLabel(last.revelationType)} · ${eastern(last.numberOfAyahs)} ${t('ayah_suffix')}`;
    if (progress) progress.hidden = true;
    button.onclick = () => openSurah(last.number);
  } else {
    medallion.innerHTML = icon('play');
    title.textContent = t('not_started_title');
    meta.textContent = t('not_started_desc');
    if (progress) progress.hidden = true;
    button.onclick = () => route('quran');
  }
}

function renderFavoritesPage() {
  const container = document.getElementById('favoritesContent');
  if (!container) return; // صفحة المحفوظات غير مركَّبة الآن
  const favs = getFavorites();
  const favoriteAyahs = getFavoriteAyahs();
  const positions = getSavedPositions();
  if (!favs.length && !favoriteAyahs.length && !positions.length) {
    container.innerHTML = `<div class="empty-state"><div>${icon('heart')}</div><h2>${t('fav_empty_title')}</h2><p>${t('fav_empty_desc')}</p><button class="primary-button" data-route="quran">${t('browse_quran')}</button></div>`;
    return;
  }
  let html = '';
  if (favs.length) {
    const items = favs.map(n => surahs.find(s => s.number === n)).filter(Boolean);
    html += `<section class="saved-section"><div class="section-head wide"><div><span class="eyebrow">${t('saved_surahs')}</span><h2>${tx('saved_surahs_label')}</h2></div></div>
      <div class="favorites-list">${items.map(s => `<article><span class="favorite-number">${eastern(s.number)}</span><div><h3>${surahDisplayName(s)}</h3><small>${revelationLabel(s.revelationType)} · ${eastern(s.numberOfAyahs)} ${t('ayah_suffix')}</small></div><div class="saved-actions"><button class="has-icon" data-open-surah="${s.number}">${icon('book')}<span>${tx('open_item')}</span></button><button class="remove" data-remove-surah="${s.number}" aria-label="${tx('remove_item')}">${icon('trash')}</button></div></article>`).join('')}</div></section>`;
  }
  if (favoriteAyahs.length) html += `<section class="saved-section"><div class="section-head wide"><div><h2>${tx('saved_ayahs')}</h2></div></div><div class="favorites-list">${favoriteAyahs.map((item, index) => {
    const name = usesArabicScript() ? item.surahName : (item.englishName || item.surahName);
    return `<article><span class="favorite-number">${eastern(item.ayahNumber)}</span><div><h3>${name || ''} · ${eastern(item.ayahNumber)}</h3><small lang="ar" dir="rtl">${item.text || ''}</small></div><div class="saved-actions"><button class="has-icon" data-open-ayah="${index}">${icon('book')}<span>${tx('open_item')}</span></button><button class="remove" data-remove-ayah="${index}" aria-label="${tx('remove_item')}">${icon('trash')}</button></div></article>`;
  }).join('')}</div></section>`;
  if (positions.length) html += `<section class="saved-section"><div class="section-head wide"><div><h2>${tx('saved_positions')}</h2></div></div><div class="favorites-list">${positions.map((item, index) => {
    const name = usesArabicScript() ? item.name : (item.englishName || item.name);
    return `<article><span class="favorite-number">${eastern(item.ayahNumberInSurah)}</span><div><h3>${name}</h3><small>${t('ayah_suffix')} ${eastern(item.ayahNumberInSurah)}</small></div><div class="saved-actions"><button class="has-icon" data-open-position="${index}">${icon('book')}<span>${tx('open_item')}</span></button><button class="remove" data-remove-position="${index}" aria-label="${tx('remove_item')}">${icon('trash')}</button></div></article>`;
  }).join('')}</div></section>`;
  container.innerHTML = html;
  container.querySelectorAll('[data-open-surah]').forEach(button => button.onclick = () => openSurah(+button.dataset.openSurah));
  container.querySelectorAll('[data-remove-surah]').forEach(button => button.onclick = () => toggleFavorite(+button.dataset.removeSurah));
  container.querySelectorAll('[data-open-ayah]').forEach(button => button.onclick = () => {
    const item = favoriteAyahs[+button.dataset.openAyah];
    storage.set('lastReading', { number: item.surahNumber, name: item.surahName, englishName: item.englishName, numberOfAyahs: item.numberOfAyahs, revelationType: item.revelationType, ayahNumberInSurah: item.ayahNumber, globalAyahNumber: item.globalNumber, juz: item.juz, savedAt: Date.now() });
    openSurah(item.surahNumber);
  });
  container.querySelectorAll('[data-remove-ayah]').forEach(button => button.onclick = () => {
    const items = getFavoriteAyahs(); items.splice(+button.dataset.removeAyah, 1); storage.set('favoriteAyahs', items); toast(tx('ayah_removed')); renderFavoritesPage();
  });
  container.querySelectorAll('[data-open-position]').forEach(button => button.onclick = () => {
    const item = positions[+button.dataset.openPosition]; storage.set('lastReading', item); openSurah(item.number);
  });
  container.querySelectorAll('[data-remove-position]').forEach(button => button.onclick = () => {
    const items = getSavedPositions(); items.splice(+button.dataset.removePosition, 1); storage.set('savedPositions', items); toast(tx('position_removed')); renderFavoritesPage();
  });
}

const AYAH_BATCH_SIZE = 30;     // عدد الآيات في كل دفعة عند رسم السورة/الجزء/ملف التنزيل
const AYAH_BATCH_DELAY_MS = 3;  // الانتظار بين دفعات الرسم في صفحة القراءة
let readerAyahMap = new Map();  // رقم الآية العالمي ← بياناتها (لنافذة إجراءات الآية)

function ayahUnitHtml(a, text) {
  return `<span class="ayah-unit" tabindex="0" data-ayah-number="${a.numberInSurah}" data-global-ayah="${a.number}" data-juz="${a.juz}">${text} <span class="ayah-badge"><a></a>${eastern(a.numberInSurah)}</span></span>`;
}

function resetReaderTracking() {
  if (ayahScrollHandler) { window.removeEventListener('scroll', ayahScrollHandler); ayahScrollHandler = null; }
  currentVisibleAyah = null;
  hasUserScrolledThisSession = false;
}

function onAyahContextEvent(event) {
  const unit = event.target.closest?.('.ayah-unit');
  if (!unit) return;
  if (event.type === 'keydown' && !(event.key === 'ContextMenu' || (event.shiftKey && event.key === 'F10'))) return;
  event.preventDefault();
  const item = readerAyahMap.get(+unit.dataset.globalAyah);
  if (item) openAyahActions(item, unit);
}

function mountReader() {
  const fontButton = $('fontButton');
  const fontMenu = $('fontMenu');
  fontButton.onclick = event => { event.stopPropagation(); toggleFontMenu(); };
  fontMenu.querySelectorAll('[data-font-size]').forEach(button => button.onclick = event => {
    event.stopPropagation(); applyReaderFontSize(+button.dataset.fontSize, { announce: true }); closeFontMenu();
  });
  applyReaderFontSize(storage.get('readerFontSize', 31));
  $('saveReading').onclick = downloadCurrentSurah;
  $('listenCurrentSurah').onclick = () => {
    if (currentSurahNumber) playSurahWithReciter(currentSurahNumber, currentReciter, { source: 'reader' });
    else toast(t('toast_open_surah_first'));
  };
  $('shareCurrentSurah').onclick = shareCurrentSurah;
  const ayahText = $('ayahText');
  ayahText.addEventListener('contextmenu', onAyahContextEvent);
  ayahText.addEventListener('keydown', onAyahContextEvent);
}

function unmountReader() {
  resetReaderTracking();
  surahRequestId++; juzRequestId++; // يلغي أي رسم دفعات ما زال جاريًا
  closeFontMenu();
  readerAyahMap = new Map();
}

// الآيات تُرسم 30 آية ثم 30 بعدها بفاصل 3 مللي ثانية، ولا ننتقل إلى موضع آخر آية محفوظة إلا بعد اكتمال الرسم كله
async function openSurah(number, { focusAyahNumber = null } = {}) {
  const requestId = ++surahRequestId; // يميّز هذا الطلب عن أي طلب فتح سورة سابق لم يصل بعد
  juzRequestId++;
  // إن كنا نقرأ سورة أخرى، نحفظ موضعنا فيها أولًا قبل الانتقال (route() لا يلتقط هذه الحالة لأننا نبقى داخل صفحة القارئ نفسها)
  if (currentSurahNumber && currentSurahNumber !== number) autoCommitReadingPosition();
  resetReaderTracking();
  const mounted = await route('reader', { restore: false });
  if (!mounted || requestId !== surahRequestId || currentPage !== 'reader') return;
  currentSurahNumber = number;
  storage.set('readerState', { type: 'surah', number });
  saveLastReading(number);
  const savedReading = storage.get('lastReading', null);
  const meta = surahs.find(s => s.number === number)
    || (savedReading?.number === number ? savedReading : null);
  const ayahText = $('ayahText');
  const bismillah = document.querySelector('.bismillah');
  // نفرغ محتوى السورة السابقة فورًا حتى لا يظهر نص سورة أخرى أثناء تحميل هذه السورة
  $('readerTitle').textContent = meta ? surahDisplayName(meta) : '…';
  $('readerMeta').textContent = meta ? `${revelationLabel(meta.revelationType)} · ${eastern(meta.numberOfAyahs)} ${t('ayah_suffix')}` : '';
  bismillah.hidden = !shouldShowBismillahHeader(number);
  ayahText.innerHTML = `<p class="empty-inline">${t('loading_ayahs')}</p>`;
  const isStale = () => requestId !== surahRequestId || $('ayahText') !== ayahText;
  try {
    let data = ayahCache.get(number);
    if (!data) {
      const json = await fetchJson(`${QURAN_API}/surah/${number}/quran-uthmani`);
      data = json.data;
      ayahCache.set(number, data);
    }
    if (isStale()) return; // فتح المستخدم سورة أخرى (أو غادر الصفحة) قبل وصول هذه الاستجابة
    if (!meta) {
      $('readerTitle').textContent = usesArabicScript() ? data.name : (data.englishName || data.name);
      $('readerMeta').textContent = `${revelationLabel(data.revelationType)} · ${eastern(data.numberOfAyahs)} ${t('ayah_suffix')}`;
    }
    const showHeader = shouldShowBismillahHeader(number);
    bismillah.hidden = !showHeader;
    readerAyahMap = new Map();
    ayahText.setAttribute('aria-busy', 'true');
    ayahText.innerHTML = '<p lang="ar" dir="rtl"></p>';
    const paragraph = ayahText.firstElementChild;
    const total = data.ayahs.length;
    for (let i = 0; i < total; i += AYAH_BATCH_SIZE) {
      if (isStale()) return;
      const html = data.ayahs.slice(i, i + AYAH_BATCH_SIZE).map((a, k) => {
        // نحذف نسخة البسملة المدمجة في نص الآية الأولى عندما نعرض عنوان البسملة المستقل، لتفادي ظهورها مرتين؛
        // في الفاتحة نُبقي آيتها الأولى كما هي لأنها البسملة ذاتها ولا عنوان مستقل يرافقها
        const text = (i + k === 0 && showHeader) ? stripLeadingBismillah(a.text) : a.text;
        readerAyahMap.set(a.number, { surahNumber: number, surahName: data.name, englishName: data.englishName, numberOfAyahs: data.numberOfAyahs, revelationType: data.revelationType, ayahNumber: a.numberInSurah, globalNumber: a.number, juz: a.juz, text: a.text });
        return ayahUnitHtml(a, text);
      }).join(' ');
      const hasMore = i + AYAH_BATCH_SIZE < total;
      paragraph.insertAdjacentHTML('beforeend', hasMore ? `${html} ` : html);
      if (hasMore) await sleep(AYAH_BATCH_DELAY_MS);
    }
    if (isStale()) return;
    ayahText.removeAttribute('aria-busy');
    // اكتمل التحميل: الآن فقط نفعّل تتبّع التمرير ونمرّر إلى آخر آية محفوظة
    setupAyahScrollTracking();
    highlightSavedAyah();
    if (focusAyahNumber) {
      setTimeout(() => document.querySelector(`#ayahText .ayah-unit[data-ayah-number="${focusAyahNumber}"]`)?.scrollIntoView({ behavior: 'auto', block: 'center' }), 0);
    } else scrollToSavedAyah(); // يفتح موضع القراءة الدقيق المحفوظ بدل بداية السورة، إن كان محفوظًا لهذه السورة تحديدًا
  } catch (err) {
    if (isStale()) return;
    ayahText.removeAttribute('aria-busy');
    const timedOut = err.message === 'timeout';
    ayahText.innerHTML = `<p class="empty-inline">${timedOut ? t('request_timeout') : t('ayahs_error')} <button id="retryAyahText" type="button" class="text-button">${t('retry')}</button></p>`;
    $('retryAyahText')?.addEventListener('click', () => openSurah(number));
  }
}

// بالعربية نستخدم اسم الجزء التقليدي (الأول، الثاني...)؛ في باقي اللغات نستخدم رقمًا (Juz 5) تفاديًا لترجمة 30 اسمًا ترتيبيًا إضافيًا لكل لغة
function juzTitle(number) {
  return currentLang === 'ar' ? `الجزء ${juzOrdinals[number - 1]}` : `${t('juz_word')} ${eastern(number)}`;
}

async function openJuz(number) {
  const requestId = ++juzRequestId; // يميّز هذا الطلب عن أي طلب فتح جزء سابق لم يصل بعد
  surahRequestId++;
  // إن كنا نقرأ سورة قبل الانتقال لعرض الجزء، نحفظ موضعنا فيها أولًا
  if (currentSurahNumber) autoCommitReadingPosition();
  resetReaderTracking(); // تتبّع الآية أثناء التمرير مخصّص لعرض السورة المفردة فقط
  const mounted = await route('reader', { restore: false });
  if (!mounted || requestId !== juzRequestId || currentPage !== 'reader') return;
  currentSurahNumber = null;
  storage.set('readerState', { type: 'juz', number });
  $('readerTitle').textContent = juzTitle(number);
  $('readerMeta').textContent = t('juz_of_30', { n: eastern(number) });
  const ayahText = $('ayahText');
  const bismillah = document.querySelector('.bismillah'); // العنوان المستقل غير مستخدم في عرض الجزء (العناوين هنا مضمّنة لكل سورة داخل الجزء)
  bismillah.hidden = true;
  ayahText.innerHTML = `<p class="empty-inline">${t('loading_juz_ayahs')}</p>`;
  const isStale = () => requestId !== juzRequestId || $('ayahText') !== ayahText;
  try {
    let data = juzCache.get(number);
    if (!data) {
      const json = await fetchJson(`${QURAN_API}/juz/${number}/quran-uthmani`);
      data = json.data;
      juzCache.set(number, data);
    }
    if (isStale()) return;
    readerAyahMap = new Map();
    ayahText.setAttribute('aria-busy', 'true');
    ayahText.innerHTML = '';
    let lastSurah = null;
    let ayahIndexInSurah = 0;
    let paragraph = null;
    const total = data.ayahs.length;
    for (let i = 0; i < total; i += AYAH_BATCH_SIZE) {
      if (isStale()) return;
      data.ayahs.slice(i, i + AYAH_BATCH_SIZE).forEach(a => {
        if (a.surah.number !== lastSurah) {
          ayahText.insertAdjacentHTML('beforeend', `<h2 class="juz-surah-heading" lang="ar" dir="rtl">${a.surah.name}</h2>`);
          if (a.numberInSurah === 1 && shouldShowBismillahHeader(a.surah.number)) {
            ayahText.insertAdjacentHTML('beforeend', `<div class="bismillah" lang="ar" dir="rtl">${BISMILLAH_TEXT}</div>`);
          }
          paragraph = document.createElement('p');
          paragraph.lang = 'ar'; paragraph.dir = 'rtl';
          ayahText.appendChild(paragraph);
          lastSurah = a.surah.number;
          ayahIndexInSurah = 0;
        }
        // نحذف نسخة البسملة المدمجة في نص الآية الأولى من كل سورة يظهر لها عنوان بسملة مستقل هنا، لتفادي تكرارها
        const text = (ayahIndexInSurah === 0 && shouldShowBismillahHeader(a.surah.number)) ? stripLeadingBismillah(a.text) : a.text;
        readerAyahMap.set(a.number, { surahNumber: a.surah.number, surahName: a.surah.name, englishName: a.surah.englishName, numberOfAyahs: a.surah.numberOfAyahs, revelationType: a.surah.revelationType, ayahNumber: a.numberInSurah, globalNumber: a.number, juz: a.juz || number, text: a.text });
        // نفس شكل ترقيم الآية المستخدم في صفحة قراءة السورة (ayah-badge)
        paragraph.insertAdjacentHTML('beforeend', ayahUnitHtml(a, text) + ' ');
        ayahIndexInSurah++;
      });
      if (i + AYAH_BATCH_SIZE < total) await sleep(AYAH_BATCH_DELAY_MS);
    }
    if (!isStale()) ayahText.removeAttribute('aria-busy');
  } catch (err) {
    if (isStale()) return;
    ayahText.removeAttribute('aria-busy');
    const timedOut = err.message === 'timeout';
    ayahText.innerHTML = `<p class="empty-inline">${timedOut ? t('request_timeout') : t('juz_ayahs_error')} <button id="retryJuzText" type="button" class="text-button">${t('retry')}</button></p>`;
    $('retryJuzText')?.addEventListener('click', () => openJuz(number));
  }
}

// ── تنزيل السورة كملف HTML (زر #saveReading) ─────────────────
let downloadingSurah = false;
let badgeImageDataUri; // undefined: لم تُجرَّب بعد، null: تعذّر التحميل

function escapeHtml(value) {
  return String(value).replace(/[&<>"']/g, ch => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[ch]));
}

// نضمّن صورة شارة الآية داخل الملف المنزَّل (data URI) حتى يظهر الترقيم بنفس الشكل دون الاعتماد على مجلد icons
async function loadBadgeImageDataUri() {
  if (badgeImageDataUri !== undefined) return badgeImageDataUri;
  try {
    const res = await fetch('icons/Qr.png');
    if (!res.ok) throw new Error('badge-image');
    const blob = await res.blob();
    badgeImageDataUri = await new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onload = () => resolve(reader.result);
      reader.onerror = reject;
      reader.readAsDataURL(blob);
    });
  } catch (err) { badgeImageDataUri = null; }
  return badgeImageDataUri;
}

function buildSurahDocument(data, bodyHtml, badgeImage, showHeader) {
  const meta = `${revelationLabel(data.revelationType)} · ${eastern(data.numberOfAyahs)} ${t('ayah_suffix')}`;
  const badgeBackground = badgeImage ? `background-image:url(${badgeImage});` : '';
  return `<!doctype html>
<html lang="ar" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${escapeHtml(data.name)} — نور القرآن</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Naskh+Arabic:wght@500;600;700&display=swap" rel="stylesheet">
<style>
:root{--bg:#f7f4ed;--surface:#fffdf8;--ink:#19382f;--muted:#73827c;--line:#e3e2d9;--green:#1e5a47;--gold:#c79b4d;--font-quran:"Noto Naskh Arabic","Amiri",serif}
@media (prefers-color-scheme:dark){:root{--bg:#0f1a16;--surface:#15251f;--ink:#e8efe9;--muted:#9bb0a6;--line:#27382f;--green:#7ec9aa;--gold:#d7ae63}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font-family:system-ui,sans-serif}
main{max-width:860px;margin:0 auto;padding:32px 18px 64px}
header{text-align:center;margin-bottom:26px}
header h1{margin:0 0 6px;font:700 34px var(--font-quran)}
header p{margin:0;color:var(--muted)}
article{background:var(--surface);border:1px solid var(--line);border-radius:22px;padding:28px 22px}
.bismillah{text-align:center;font:700 30px var(--font-quran);margin-bottom:22px}
.ayah-text{font:600 31px/2.2 var(--font-quran);color:var(--ink)}
.ayah-text p{margin:0}
.ayah-unit{position:relative;display:inline;border-radius:8px}
.ayah-badge{display:inline-flex;justify-content:center;line-height:0;align-items:center;font-family:system-ui;width:32px;height:32px;font-size:14px;color:var(--green);border:1px solid var(--gold);border-radius:50%;vertical-align:middle;user-select:none;background:var(--surface)}
.ayah-badge a{${badgeBackground}background-size:cover;position:absolute;padding:20px}
footer{text-align:center;color:var(--muted);font-size:12px;margin-top:20px}
</style>
</head>
<body>
<main>
<header><h1>${escapeHtml(data.name)}</h1><p>${escapeHtml(meta)}</p></header>
<article>
${showHeader ? `<div class="bismillah">${BISMILLAH_TEXT}</div>` : ''}
<div class="ayah-text"><p>${bodyHtml}</p></div>
</article>
<footer>نور القرآن · النص عبر Al Quran Cloud</footer>
</main>
</body>
</html>`;
}

function triggerDownload(content, filename, type = 'text/html;charset=utf-8') {
  const url = URL.createObjectURL(new Blob([content], { type }));
  const link = document.createElement('a');
  link.href = url; link.download = filename; link.rel = 'noopener';
  document.body.appendChild(link); link.click(); link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 10000);
}

// تحميل آيات السورة للملف 30 آية ثم 30 بعدها بفاصل 1 مللي ثانية
async function downloadCurrentSurah() {
  if (!currentSurahNumber) { toast(t('toast_open_surah_first')); return; }
  if (downloadingSurah) return;
  downloadingSurah = true;
  const number = currentSurahNumber;
  const button = $('saveReading');
  if (button) { button.disabled = true; button.classList.add('is-loading'); button.setAttribute('aria-busy', 'true'); }
  try {
    toast(tx('download_preparing'));
    let data = ayahCache.get(number);
    if (!data) {
      const json = await fetchJson(`${QURAN_API}/surah/${number}/quran-uthmani`);
      data = json.data;
      ayahCache.set(number, data);
    }
    const badgeImage = await loadBadgeImageDataUri();
    const showHeader = shouldShowBismillahHeader(number);
    const chunks = [];
    for (let i = 0; i < data.ayahs.length; i += AYAH_BATCH_SIZE) {
      chunks.push(data.ayahs.slice(i, i + AYAH_BATCH_SIZE).map((a, k) => {
        const text = (i + k === 0 && showHeader) ? stripLeadingBismillah(a.text) : a.text;
        return `<span class="ayah-unit" id="ayah-${a.numberInSurah}">${escapeHtml(text)} <span class="ayah-badge"><a></a>${eastern(a.numberInSurah)}</span></span>`;
      }).join(' '));
      if (i + AYAH_BATCH_SIZE < data.ayahs.length) await sleep(1);
    }
    const html = buildSurahDocument(data, chunks.join(' '), badgeImage, showHeader);
    const slug = String(data.englishName || 'surah').replace(/[^A-Za-z0-9]+/g, '-').replace(/^-|-$/g, '');
    triggerDownload(html, `${String(number).padStart(3, '0')}-${slug || 'surah'}.html`);
    toast(tx('download_done'));
  } catch (err) {
    toast(tx('download_failed'));
  } finally {
    downloadingSurah = false;
    const current = $('saveReading');
    if (current) { current.disabled = false; current.classList.remove('is-loading'); current.removeAttribute('aria-busy'); }
  }
}

// ── القرّاء وصفحة الاستماع ───────────────────────────────────
function reciterCard(reciter, index, mini = false) {
  const country = reciter.countryLabel ? reciter.countryLabel[currentLang === 'ar' ? 'ar' : 'en'] : t(`country_${reciter.country}`);
  const name = reciterDisplayName(reciter);
  const photoLabel = usesArabicScript() ? `صورة ${name}` : `Photo of ${name}`;
  const avatar = `<div class="avatar"><img src="${reciter.image}" alt="${photoLabel}" loading="lazy" decoding="async"></div>`;
  return mini
    ? `<article class="mini-reciter" tabindex="0" data-reciter-index="${index}">${avatar}<b>${name}</b><small>${country}</small></article>`
    : `<article class="reciter-card">${avatar}<h3>${name}</h3><p>${country}</p><button class="has-icon" data-reciter-index="${index}">${icon('play')}<span>${cleanIconText(t('listen_now'))}</span></button></article>`;
}

function bindReciterCards(scopeSelector) {
  const container = document.querySelector(scopeSelector);
  if (!container) return;
  container.onclick = event => {
    const el = event.target.closest('[data-reciter-index]');
    if (!el || !container.contains(el)) return;
    playSurahWithReciter(listenSurahNumber || 1, reciters[+el.dataset.reciterIndex]);
  };
}

function renderHomeReciters() {
  const strip = $('homeReciters');
  if (!strip) return;
  strip.innerHTML = reciters.slice(0, 5).map((reciter, index) => reciterCard(reciter, index, true)).join('');
  bindReciterCards('#homeReciters');
}

// القرّاء يُحمَّلون اثنين ثم اثنين بفاصل 1 مللي ثانية داخل #recitersGrid
let reciterGridRenderId = 0;
async function renderReciterGrid(filter = '') {
  const grid = $('recitersGrid');
  if (!grid) return;
  const token = ++reciterGridRenderId;
  const value = filter.trim();
  const normalizedFilter = value.toLocaleLowerCase(currentLang);
  const filtered = reciters.map((reciter, index) => ({ reciter, index })).filter(({ reciter }) =>
    reciter.name.includes(value) || reciter.latinName.toLocaleLowerCase().includes(normalizedFilter));
  bindReciterCards('#recitersGrid');
  if (!filtered.length) { grid.innerHTML = `<div class="empty-inline">${t('no_reciter_match')}</div>`; return; }
  await renderInBatches(grid, filtered, ({ reciter, index }) => reciterCard(reciter, index), 2, 1, () => token !== reciterGridRenderId || $('recitersGrid') !== grid);
}

function populateListenSurahSelect() {
  const select = $('listenSurah');
  if (!select) return;
  select.innerHTML = surahs.map(s => `<option value="${s.number}">${eastern(s.number)} · ${surahDisplayName(s)}${usesArabicScript() ? '' : ` — ${s.name}`}</option>`).join('');
  select.value = String(listenSurahNumber);
  refreshCustomSelect(select);
}

function setListenSurahNumber(number) {
  listenSurahNumber = number;
  const select = $('listenSurah');
  if (select) { select.value = String(number); refreshCustomSelect(select); }
}

function mountListen() {
  $('listenSurah').onchange = () => {
    listenSurahNumber = +$('listenSurah').value || 1;
    if (!player.hidden) playSurahWithReciter(listenSurahNumber, currentReciter);
  };
  $('reciterSearch').oninput = event => renderReciterGrid(event.target.value);
  renderListenPage();
}

function renderListenPage() {
  if (!$('recitersGrid')) return;
  populateListenSurahSelect();
  renderReciterGrid($('reciterSearch').value);
}

// ── الصفحة الرئيسية ──────────────────────────────────────────
function renderHome() {
  renderHomeReciters();
  renderContinueCard();
  renderKhatmaCard();
  if (todayTimings) renderHomePrayerList(todayTimings.timings);
  updateLocationUI();
  tickCountdown();
}

// ── تحميل الصوت على دفعات زمنية (3 ثوانٍ) أثناء الاستماع ─────────────
// بدل تحميل ملف السورة كاملًا: نطلب أول 3 ثوانٍ فقط عبر HTTP Range ونضيفها إلى MediaSource،
// وحين يتبقى ثانية واحدة أو أقل من المخزَّن أمام موضع التشغيل نطلب الـ3 ثوانٍ التالية، وهكذا.
// شريط #seek يبقى ممثِّلًا لمدة السورة كاملةً (تُقدَّر من ترويسة MP3)، والتشغيل متصل دون انقطاع.
// إن لم يدعم المتصفح/الخادم ذلك (MediaSource أو Range أو CORS) نعود تلقائيًا للتشغيل المباشر المعتاد.
const MP3_BITRATES_V1 = [0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 0];
const MP3_BITRATES_V2 = [0, 8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 144, 160, 0];

class ChunkedAudio {
  static supported() {
    return typeof window.MediaSource === 'function' && MediaSource.isTypeSupported('audio/mpeg');
  }

  // يقرأ أول إطار MP3 (بعد وسم ID3) لاستخراج معدل البت/المدة؛ يستخدم ترويسة Xing/Info إن وُجدت (VBR)
  static parseMp3(bytes, total) {
    let pos = 0;
    if (bytes.length > 10 && bytes[0] === 0x49 && bytes[1] === 0x44 && bytes[2] === 0x33) {
      const size = ((bytes[6] & 0x7f) << 21) | ((bytes[7] & 0x7f) << 14) | ((bytes[8] & 0x7f) << 7) | (bytes[9] & 0x7f);
      pos = 10 + size + ((bytes[5] & 0x10) ? 10 : 0);
    }
    for (let i = pos; i < bytes.length - 12; i++) {
      if (bytes[i] !== 0xFF || (bytes[i + 1] & 0xE0) !== 0xE0) continue;
      const versionBits = (bytes[i + 1] >> 3) & 3;
      const layerBits = (bytes[i + 1] >> 1) & 3;
      if (versionBits === 1 || layerBits !== 1) continue; // إصدار محجوز أو ليس Layer III
      const bitrateIndex = bytes[i + 2] >> 4;
      const sampleRateIndex = (bytes[i + 2] >> 2) & 3;
      if (bitrateIndex === 0 || bitrateIndex === 15 || sampleRateIndex === 3) continue;
      const mpeg1 = versionBits === 3;
      const bitrate = (mpeg1 ? MP3_BITRATES_V1 : MP3_BITRATES_V2)[bitrateIndex] * 1000;
      const sampleRate = (mpeg1 ? [44100, 48000, 32000] : versionBits === 2 ? [22050, 24000, 16000] : [11025, 12000, 8000])[sampleRateIndex];
      const samplesPerFrame = mpeg1 ? 1152 : 576;
      const mono = (bytes[i + 3] >> 6) === 3;
      let bytesPerSecond = bitrate / 8;
      let duration = (total - i) / bytesPerSecond;
      const sideInfo = mpeg1 ? (mono ? 17 : 32) : (mono ? 9 : 17);
      const tagAt = i + 4 + sideInfo + ((bytes[i + 1] & 1) === 0 ? 2 : 0);
      if (tagAt + 12 <= bytes.length) {
        const tag = String.fromCharCode(bytes[tagAt], bytes[tagAt + 1], bytes[tagAt + 2], bytes[tagAt + 3]);
        if ((tag === 'Xing' || tag === 'Info') && (bytes[tagAt + 7] & 1)) {
          const frames = ((bytes[tagAt + 8] << 24) | (bytes[tagAt + 9] << 16) | (bytes[tagAt + 10] << 8) | bytes[tagAt + 11]) >>> 0;
          if (frames > 0) { duration = frames * samplesPerFrame / sampleRate; bytesPerSecond = (total - i) / duration; }
        }
      }
      if (!(bytesPerSecond > 0) || !isFinite(duration)) return null;
      return { dataStart: i, bytesPerSecond, duration };
    }
    return null;
  }

  constructor(audio, url, { chunkSeconds = 3, leadSeconds = 1, onFatal = () => {} } = {}) {
    this.audio = audio;
    this.url = url;
    this.chunkSeconds = chunkSeconds;
    this.leadSeconds = leadSeconds;
    this.onFatal = onFatal;
    this.abort = new AbortController();
    this.destroyed = false;
    this.pumping = false;
    this.total = 0;
    this.dataStart = 0;
    this.bytesPerSecond = 0;
    this.loadByte = 0;      // البايت التالي المطلوب جلبه
    this.loadTime = 0;      // الزمن المقابل له (يُستخدم عند القفز لموضع جديد)
    this.needReposition = false;
    this.endReached = false;
    this.onTick = () => this.tick();
  }

  async start() {
    const ms = this.ms = new MediaSource();
    this.objectUrl = URL.createObjectURL(ms);
    const opened = new Promise((resolve, reject) => {
      ms.addEventListener('sourceopen', resolve, { once: true });
      this.openTimer = setTimeout(() => reject(new Error('sourceopen-timeout')), 8000);
    });
    this.audio.src = this.objectUrl;
    await opened;
    clearTimeout(this.openTimer);
    if (this.destroyed) throw new Error('destroyed');
    const [headLength, probe] = await Promise.all([this.headLength(), this.fetchRange(0, 16383)]);
    if (this.destroyed) throw new Error('destroyed');
    const total = headLength || probe.total;
    if (!total) throw new Error('unknown-size');
    const info = ChunkedAudio.parseMp3(probe.bytes, total);
    if (!info) throw new Error('not-mp3');
    this.total = total;
    this.dataStart = info.dataStart;
    this.bytesPerSecond = info.bytesPerSecond;
    this.sb = ms.addSourceBuffer('audio/mpeg');
    try { this.sb.mode = 'sequence'; } catch (err) { /* الافتراضي كافٍ */ }
    try { ms.duration = info.duration; } catch (err) { /* تُستنتج المدة من البيانات */ }
    // أول 3 ثوانٍ: نكمل ما قرأناه للترويسة حتى نبلغ 3 ثوانٍ
    let first = probe.bytes;
    const wanted = Math.min(this.total, Math.ceil(this.chunkSeconds * this.bytesPerSecond));
    if (wanted > first.length) {
      const more = await this.fetchRange(first.length, wanted - 1);
      if (this.destroyed) throw new Error('destroyed');
      const merged = new Uint8Array(first.length + more.bytes.length);
      merged.set(first, 0); merged.set(more.bytes, first.length);
      first = merged;
    }
    await this.append(first);
    this.loadByte = first.length;
    if (this.loadByte >= this.total) this.finish();
    ['timeupdate', 'seeking', 'waiting', 'playing'].forEach(name => this.audio.addEventListener(name, this.onTick));
  }

  async headLength() {
    try {
      const res = await fetch(this.url, { method: 'HEAD', signal: this.abort.signal });
      if (!res.ok) return 0;
      return Number(res.headers.get('Content-Length')) || 0;
    } catch (err) { if (err.name === 'AbortError') throw err; return 0; }
  }

  async fetchRange(start, end) {
    const res = await fetch(this.url, { headers: { Range: `bytes=${start}-${end}` }, signal: this.abort.signal });
    if (res.status !== 206) { try { res.body?.cancel(); } catch (err) { /* تجاهل */ } throw new Error(`range-${res.status}`); }
    const bytes = new Uint8Array(await res.arrayBuffer());
    const match = /\/(\d+)\s*$/.exec(res.headers.get('Content-Range') || '');
    return { bytes, total: match ? Number(match[1]) : 0 };
  }

  waitIdle() {
    const sb = this.sb;
    if (!sb.updating) return Promise.resolve();
    return new Promise(resolve => sb.addEventListener('updateend', resolve, { once: true }));
  }

  async append(bytes) {
    await this.waitIdle();
    const sb = this.sb;
    await new Promise((resolve, reject) => {
      const cleanup = () => { sb.removeEventListener('updateend', done); sb.removeEventListener('error', fail); };
      const done = () => { cleanup(); resolve(); };
      const fail = () => { cleanup(); reject(new Error('append-error')); };
      sb.addEventListener('updateend', done);
      sb.addEventListener('error', fail);
      try { sb.appendBuffer(bytes); } catch (err) { cleanup(); reject(err); }
    });
  }

  // كم ثانية مخزَّنة أمام الموضع t؟ (-1 إن لم يكن t داخل أي مدى مخزَّن)
  bufferedAhead(t) {
    const ranges = this.sb.buffered;
    for (let i = 0; i < ranges.length; i++) {
      if (t >= ranges.start(i) - 0.15 && t <= ranges.end(i) + 0.05) return Math.max(0, ranges.end(i) - t);
    }
    return -1;
  }

  shouldLoad() {
    if (this.destroyed || !this.sb || this.loadByte >= this.total) return false;
    if (this.needReposition) return true;
    return this.bufferedAhead(this.audio.currentTime) <= this.leadSeconds; // بقيت ثانية (أو أقل) من المخزَّن → حمّل 3 ثوانٍ أخرى
  }

  reposition(time) {
    this.abort.abort();                  // نلغي الطلب الجاري (إن وُجد) لأن المستخدم انتقل إلى موضع آخر
    this.abort = new AbortController();
    const byte = Math.floor(this.dataStart + Math.max(0, time - 0.4) * this.bytesPerSecond);
    this.loadByte = Math.min(Math.max(this.dataStart, byte), this.total - 1);
    this.loadTime = (this.loadByte - this.dataStart) / this.bytesPerSecond;
    this.needReposition = true;
    this.endReached = false;
  }

  tick() {
    if (this.destroyed || !this.sb) return;
    try {
      const t = this.audio.currentTime;
      if (this.bufferedAhead(t) < 0) {
        const cursorTime = (this.loadByte - this.dataStart) / this.bytesPerSecond;
        if (this.needReposition ? Math.abs(this.loadTime - t) > 1 : Math.abs(cursorTime - t) > 0.75) this.reposition(t);
      }
    } catch (err) { return; } // الـSourceBuffer أُزيل أثناء تبديل المصدر
    this.pump();
  }

  async pump() {
    if (this.pumping || this.destroyed) return;
    this.pumping = true;
    try {
      while (this.shouldLoad()) {
        try { await this.loadChunk(); }
        catch (err) {
          if (this.destroyed) return;
          if (err.name === 'AbortError') continue; // انتقال المستخدم لموضع آخر ألغى الطلب؛ نعيد التقييم
          if (err.name === 'QuotaExceededError' && this.evict(true)) continue;
          throw err;
        }
      }
    } catch (err) {
      if (!this.destroyed) this.onFatal(err);
    } finally {
      this.pumping = false;
    }
  }

  async loadChunk() {
    await this.waitIdle();
    if (this.destroyed) return;
    const sb = this.sb;
    if (this.needReposition) {
      this.needReposition = false;
      try { sb.abort(); } catch (err) { /* تجاهل */ }
      sb.timestampOffset = this.loadTime;
    }
    const start = this.loadByte;
    const end = Math.min(this.total, start + Math.ceil(this.chunkSeconds * this.bytesPerSecond)) - 1;
    const { bytes } = await this.fetchRange(start, end);
    if (this.destroyed || start !== this.loadByte || this.needReposition) return; // وصلت متأخرة بعد قفزة جديدة؛ تُهمَل
    await this.append(bytes);
    if (this.destroyed || this.needReposition) return;
    this.loadByte = start + bytes.length;
    if (this.loadByte >= this.total) this.finish();
    this.evict();
  }

  finish() {
    this.endReached = true;
    try { if (this.ms.readyState === 'open' && !this.sb.updating) this.ms.endOfStream(); } catch (err) { /* تجاهل */ }
  }

  // نحرّر الذاكرة بإزالة ما مضى من التشغيل بمسافة كبيرة؛ العودة إليه لاحقًا تُعيد تحميله عند الحاجة
  evict(force = false) {
    const sb = this.sb;
    if (!sb || sb.updating || this.ms.readyState === 'closed' || !sb.buffered.length) return false;
    const t = this.audio.currentTime;
    const start = sb.buffered.start(0);
    if (t - start <= (force ? 12 : 90)) return false;
    try { sb.remove(start, t - (force ? 8 : 40)); return true; } catch (err) { return false; }
  }

  destroy() {
    if (this.destroyed) return;
    this.destroyed = true;
    clearTimeout(this.openTimer);
    this.abort.abort();
    ['timeupdate', 'seeking', 'waiting', 'playing'].forEach(name => this.audio.removeEventListener(name, this.onTick));
    try { URL.revokeObjectURL(this.objectUrl); } catch (err) { /* تجاهل */ }
  }
}

let chunkedAudio = null;
function destroyChunkedAudio() {
  if (!chunkedAudio) return;
  chunkedAudio.destroy();
  chunkedAudio = null;
}

// فشل تحميل الدفعات (شبكة/خادم لا يدعم Range…): نكمل من نفس الموضع بتشغيل الملف مباشرةً
function handleChunkedFatal(loader, requestId) {
  if (chunkedAudio !== loader || requestId !== audioRequestId || audioMode !== 'chapter') return;
  const time = audioEl.currentTime || 0;
  const wasPlaying = !audioEl.paused;
  const url = loader.url;
  chunkedAudio = null;
  loader.destroy();
  pendingChapterResume = time > 1 ? { requestId, surahNumber: playingSurahNumber, currentTime: time } : null;
  audioEl.src = url;
  audioEl.load();
  if (wasPlaying) audioEl.play().catch(() => {});
}

async function attachChapterSource(url, requestId) {
  destroyChunkedAudio();
  if (ChunkedAudio.supported()) {
    const loader = new ChunkedAudio(audioEl, url, { chunkSeconds: 3, leadSeconds: 1, onFatal: () => handleChunkedFatal(loader, requestId) });
    chunkedAudio = loader;
    try {
      await loader.start();
      return;
    } catch (err) {
      if (chunkedAudio === loader) chunkedAudio = null;
      loader.destroy();
      if (requestId !== audioRequestId) return; // أُلغي الطلب أثناء التحضير
    }
  }
  audioEl.src = url;
  audioEl.load();
}

// ── مشغّل الصوت ──────────────────────────────────────────────
const audioEl = document.getElementById('audio');
const player = document.getElementById('player');
const playPauseBtn = document.getElementById('playPause');
const seekInput = document.getElementById('seek');
const currentTimeEl = document.getElementById('currentTime');
const durationEl = document.getElementById('duration');
const trackTitleEl = document.getElementById('trackTitle');
const trackReciterEl = document.getElementById('trackReciter');
const playerStatusEl = document.getElementById('playerStatus');
const volumeInput = document.getElementById('volume');
const prevTrackBtn = document.getElementById('prevTrack');
const nextTrackBtn = document.getElementById('nextTrack');
const automaticBtn = document.getElementById('automatic');
let audioRequestController = null;
let audioRequestId = 0;
let audioMode = 'idle'; // chapter: ملف سورة كامل، ayah: المسار الاحتياطي آيةً آية
let chapterFallbackStarted = false;
let pendingChapterResume = null;
let lastAudioProgressSave = 0;
let autoAdvanceEnabled = Boolean(storage.get('audioAutoAdvance', false));
// مصدر التشغيل: 'listen' (صفحة الاستماع) | 'reader' (زر استمع للسورة) | 'reader-ayah' (زر إستماع للآية).
// الانتقال التلقائي بين السور يعمل مع 'listen' فقط.
let playbackSource = 'listen';
let singleAyahMode = false;
let singleAyahReciter = null;

function syncAutomaticButton() {
  if (!automaticBtn) return;
  const blocked = playbackSource !== 'listen';
  automaticBtn.innerHTML = icon('autoplay');
  automaticBtn.disabled = blocked;
  automaticBtn.classList.toggle('active', autoAdvanceEnabled && !blocked);
  automaticBtn.setAttribute('aria-pressed', String(autoAdvanceEnabled && !blocked));
  const label = blocked ? tx('automatic_unavailable') : tx(autoAdvanceEnabled ? 'automatic_disable' : 'automatic_enable');
  automaticBtn.setAttribute('aria-label', label);
  automaticBtn.title = label;
}

function advanceToNextSurahAutomatically() {
  if (playbackSource !== 'listen' || !autoAdvanceEnabled || !playingSurahNumber || playingSurahNumber >= 114) return false;
  const nextSurah = playingSurahNumber + 1;
  setListenSurahNumber(nextSurah);
  playSurahWithReciter(nextSurah, currentReciter);
  return true;
}

function setPlayerLoading(loading, message = '') {
  player.classList.toggle('is-loading', loading);
  player.setAttribute('aria-busy', String(loading));
  playPauseBtn.disabled = loading && !playQueue.length;
  if (message) playerStatusEl.textContent = message;
}

function syncPlaybackUI() {
  const isPlaying = !audioEl.paused && !audioEl.ended;
  playPauseBtn.innerHTML = icon(isPlaying ? 'pause' : 'play');
  playPauseBtn.setAttribute('aria-label', isPlaying ? (usesArabicScript() ? 'إيقاف مؤقت' : 'Pause') : (usesArabicScript() ? 'تشغيل' : 'Play'));
  playPauseBtn.setAttribute('aria-pressed', String(isPlaying));
}

function syncTrackNavigationLabels() {
  const chapterMode = audioMode === 'chapter';
  prevTrackBtn.setAttribute('aria-label', chapterMode ? (usesArabicScript() ? 'السورة السابقة' : 'Previous surah') : (usesArabicScript() ? 'الآية السابقة' : 'Previous verse'));
  nextTrackBtn.setAttribute('aria-label', chapterMode ? (usesArabicScript() ? 'السورة التالية' : 'Next surah') : (usesArabicScript() ? 'الآية التالية' : 'Next verse'));
}

function cancelPendingAudio({ clearSource = false } = {}) {
  audioRequestController?.abort();
  audioRequestController = null;
  audioRequestId++;
  persistAudioProgress(true);
  audioEl.pause();
  destroyChunkedAudio();
  singleAyahMode = false;
  singleAyahReciter = null;
  audioMode = 'idle';
  chapterFallbackStarted = false;
  pendingChapterResume = null;
  if (clearSource) {
    audioEl.removeAttribute('src');
    audioEl.load();
  }
  setPlayerLoading(false);
}

function audioUrl(ayahGlobalNumber) {
  const reciter = singleAyahReciter || currentReciter;
  return `https://cdn.islamic.network/quran/audio/${reciter.bitrate}/${reciter.edition}/${ayahGlobalNumber}.mp3`;
}

function chapterAudioUrl(surahNumber, reciter = currentReciter) {
  return `${reciter.chapterServer}${String(surahNumber).padStart(3, '0')}.mp3`;
}

function persistAudioProgress(force = false) {
  if (audioMode !== 'chapter' || !playingSurahNumber || !audioEl.currentSrc) return;
  const now = Date.now();
  if (!force && now - lastAudioProgressSave < 1000) return;
  lastAudioProgressSave = now;
  storage.set('lastAudio', {
    mode: 'chapter', surahNumber: playingSurahNumber, currentTime: audioEl.currentTime || 0,
    reciterEdition: currentReciter.edition, savedAt: now
  });
}

function formatTime(seconds) {
  if (!isFinite(seconds) || seconds < 0) return eastern('0:00');
  const m = Math.floor(seconds / 60);
  const s = Math.floor(seconds % 60);
  return eastern(`${m}:${String(s).padStart(2, '0')}`);
}

async function playSurahWithReciter(surahNumber, reciter, { source = 'listen' } = {}) {
  cancelPendingAudio({ clearSource: true });
  playbackSource = source;
  if (source === 'listen') setListenSurahNumber(surahNumber);
  syncAutomaticButton();
  const requestId = audioRequestId;
  const controller = new AbortController();
  audioRequestController = controller;
  let requestTimedOut = false;
  const requestTimer = setTimeout(() => { requestTimedOut = true; controller.abort(); }, REQUEST_TIMEOUT_MS);
  currentReciter = reciter;
  updatePlayerReciterPhoto(reciter);
  playingSurahNumber = surahNumber;
  storage.set('audioReciter', reciter.edition);
  player.hidden = false;
  playQueue = [];
  queueIndex = 0;
  const knownSurah = surahs.find(s => s.number === surahNumber);
  if (knownSurah) {
    const name = surahDisplayName(knownSurah);
    trackTitleEl.textContent = name;
  }
  trackReciterEl.textContent = reciterDisplayName(reciter);
  setPlayerLoading(true, tx('audio_loading'));
  toast(t('toast_loading_recitation', { name: reciterDisplayName(reciter) }));
  try {
    let data = ayahCache.get(surahNumber);
    if (!data) {
      const res = await fetch(`${QURAN_API}/surah/${surahNumber}/quran-uthmani`, { signal: controller.signal });
      if (!res.ok) throw new Error('network');
      const json = await res.json();
      data = json.data;
      ayahCache.set(surahNumber, data);
    }
    if (requestId !== audioRequestId || controller.signal.aborted) return;
    playQueue = data.ayahs.map(a => a.number);
    const lastAudio = storage.get('lastAudio', null);
    queueIndex = lastAudio?.mode === 'ayah' && lastAudio.surahNumber === surahNumber && lastAudio.reciterEdition === reciter.edition
      ? Math.max(0, Math.min(playQueue.length - 1, +lastAudio.queueIndex || 0)) : 0;
    trackTitleEl.textContent = usesArabicScript() ? data.name : (data.englishName || data.name);
    trackReciterEl.textContent = reciterDisplayName(reciter);
    audioRequestController = null;
    await playCurrentSurah({ requestId });
  } catch (err) {
    if ((err.name === 'AbortError' && !requestTimedOut) || requestId !== audioRequestId) return;
    setPlayerLoading(false, t('toast_audio_load_error'));
    syncPlaybackUI();
    toast(t('toast_audio_load_error'));
  } finally {
    clearTimeout(requestTimer);
    if (audioRequestController === controller) audioRequestController = null;
  }
}

async function startAyahFallback(requestId = audioRequestId) {
  if (chapterFallbackStarted || requestId !== audioRequestId || !playQueue.length) return;
  chapterFallbackStarted = true;
  if (currentReciter.chapterOnly) {
    audioMode = 'idle';
    pendingChapterResume = null;
    setPlayerLoading(false, t('toast_audio_load_error'));
    syncPlaybackUI();
    toast(t('toast_audio_load_error'));
    return;
  }
  audioMode = 'ayah';
  pendingChapterResume = null;
  setPlayerLoading(true, tx('audio_fallback'));
  toast(tx('audio_fallback'));
  await playCurrentAyah({ requestId });
}

async function playCurrentSurah({ requestId = audioRequestId } = {}) {
  if (!playingSurahNumber || !currentReciter.chapterServer) return startAyahFallback(requestId);
  const expectedSurah = playingSurahNumber;
  audioMode = 'chapter';
  syncTrackNavigationLabels();
  chapterFallbackStarted = false;
  setPlayerLoading(true, tx('audio_loading'));
  const lastAudio = storage.get('lastAudio', null);
  pendingChapterResume = lastAudio?.mode === 'chapter'
    && lastAudio.surahNumber === expectedSurah
    && lastAudio.reciterEdition === currentReciter.edition
    ? { requestId, surahNumber: expectedSurah, currentTime: Math.max(0, Number(lastAudio.currentTime) || 0) }
    : null;
  // الملف يُحمَّل على دفعات (3 ثوانٍ ثم 3 ثوانٍ…) مع بقاء التشغيل متصلًا للسورة كاملة
  await attachChapterSource(chapterAudioUrl(expectedSurah), requestId);
  if (requestId !== audioRequestId || expectedSurah !== playingSurahNumber || audioMode !== 'chapter') return;
  persistAudioProgress(true);
  try {
    await audioEl.play();
    if (requestId !== audioRequestId || expectedSurah !== playingSurahNumber || audioMode !== 'chapter') return;
    setPlayerLoading(false, tx('audio_playing'));
    syncPlaybackUI();
  } catch (err) {
    if (requestId !== audioRequestId || expectedSurah !== playingSurahNumber || err.name === 'AbortError') return;
    if (err.name === 'NotAllowedError') {
      setPlayerLoading(false, tx('audio_blocked'));
      syncPlaybackUI();
      toast(tx('audio_blocked'));
      return;
    }
    await startAyahFallback(requestId);
  }
}

async function playCurrentAyah({ requestId = audioRequestId, userInitiated = true } = {}) {
  if (!playQueue.length) return;
  audioMode = 'ayah';
  syncTrackNavigationLabels();
  const expectedAyah = playQueue[queueIndex];
  setPlayerLoading(true, tx('audio_loading'));
  audioEl.src = audioUrl(playQueue[queueIndex]);
  audioEl.load();
  if (!singleAyahMode) storage.set('lastAudio', { mode: 'ayah', surahNumber: playingSurahNumber, queueIndex, globalAyahNumber: expectedAyah, reciterEdition: currentReciter.edition, savedAt: Date.now() });
  try {
    await audioEl.play();
    if (requestId !== audioRequestId || expectedAyah !== playQueue[queueIndex]) return;
    setPlayerLoading(false, tx('audio_playing'));
    syncPlaybackUI();
  } catch (err) {
    if (requestId !== audioRequestId || expectedAyah !== playQueue[queueIndex] || err.name === 'AbortError') return;
    const blocked = err.name === 'NotAllowedError';
    setPlayerLoading(false, blocked ? tx('audio_blocked') : t('toast_audio_play_error'));
    syncPlaybackUI();
    toast(blocked ? tx('audio_blocked') : t('toast_audio_play_error'));
  }
}

audioEl.addEventListener('loadstart', () => setPlayerLoading(true, tx('audio_loading')));
audioEl.addEventListener('waiting', () => setPlayerLoading(true, tx('audio_loading')));
audioEl.addEventListener('canplay', () => {
  if (audioEl.paused) setPlayerLoading(false, tx('audio_ready'));
});
audioEl.addEventListener('loadedmetadata', () => {
  const resume = pendingChapterResume;
  if (!resume || resume.requestId !== audioRequestId || resume.surahNumber !== playingSurahNumber || audioMode !== 'chapter') return;
  pendingChapterResume = null;
  if (resume.currentTime > 0 && resume.currentTime < audioEl.duration - 3) audioEl.currentTime = resume.currentTime;
});
audioEl.addEventListener('playing', () => { setPlayerLoading(false, tx('audio_playing')); syncPlaybackUI(); });
audioEl.addEventListener('play', syncPlaybackUI);
audioEl.addEventListener('pause', () => {
  persistAudioProgress(true);
  syncPlaybackUI();
  if (!audioEl.ended && audioEl.currentSrc) playerStatusEl.textContent = tx('audio_paused');
});
audioEl.addEventListener('timeupdate', () => {
  if (audioEl.duration) {
    seekInput.value = (audioEl.currentTime / audioEl.duration) * 100;
    currentTimeEl.textContent = formatTime(audioEl.currentTime);
    durationEl.textContent = formatTime(audioEl.duration);
    persistAudioProgress();
  }
});
audioEl.addEventListener('ended', () => {
  if (audioMode === 'chapter') {
    persistAudioProgress(true);
    if (advanceToNextSurahAutomatically()) return;
    playerStatusEl.textContent = tx(autoAdvanceEnabled && playingSurahNumber === 114 ? 'quran_recitation_ended' : 'audio_ended');
    seekInput.value = 100;
    syncPlaybackUI();
    return;
  }
  if (queueIndex < playQueue.length - 1) {
    queueIndex++;
    playCurrentAyah({ userInitiated: false });
  } else if (advanceToNextSurahAutomatically()) {
    return;
  } else {
    playerStatusEl.textContent = tx(autoAdvanceEnabled && playingSurahNumber === 114 ? 'quran_recitation_ended' : 'audio_ended');
    seekInput.value = 100;
    syncPlaybackUI();
  }
});
audioEl.addEventListener('error', () => {
  if (!audioEl.currentSrc) return;
  if (chunkedAudio) { handleChunkedFatal(chunkedAudio, audioRequestId); return; }
  if (audioMode === 'chapter' && !chapterFallbackStarted) {
    startAyahFallback(audioRequestId);
    return;
  }
  setPlayerLoading(false, t('toast_audio_load_error'));
  syncPlaybackUI();
  toast(t('toast_audio_load_error'));
});
seekInput.oninput = () => {
  if (audioEl.duration) audioEl.currentTime = (seekInput.value / 100) * audioEl.duration;
};
playPauseBtn.onclick = async () => {
  if (!playQueue.length) return;
  if (audioEl.paused) {
    try { await audioEl.play(); }
    catch (err) {
      const blocked = err.name === 'NotAllowedError';
      setPlayerLoading(false, blocked ? tx('audio_blocked') : t('toast_audio_play_error'));
      toast(blocked ? tx('audio_blocked') : t('toast_audio_play_error'));
      syncPlaybackUI();
    }
  } else audioEl.pause();
};
function playAdjacentSurah(delta) {
  const target = playingSurahNumber + delta;
  if (target < 1 || target > 114) return;
  playSurahWithReciter(target, currentReciter, { source: playbackSource });
}
prevTrackBtn.onclick = () => {
  if (audioMode === 'chapter') playAdjacentSurah(-1);
  else if (queueIndex > 0) { queueIndex--; playCurrentAyah(); }
};
nextTrackBtn.onclick = () => {
  if (audioMode === 'chapter') playAdjacentSurah(1);
  else if (queueIndex < playQueue.length - 1) { queueIndex++; playCurrentAyah(); }
};
automaticBtn.onclick = () => {
  if (playbackSource !== 'listen') { toast(tx('automatic_unavailable')); return; }
  autoAdvanceEnabled = !autoAdvanceEnabled;
  storage.set('audioAutoAdvance', autoAdvanceEnabled);
  syncAutomaticButton();
  toast(tx(autoAdvanceEnabled ? 'automatic_on' : 'automatic_off'));
};
document.getElementById('closePlayer').onclick = () => {
  cancelPendingAudio({ clearSource: true });
  playQueue = [];
  player.hidden = true;
  playbackSource = 'listen';
  syncAutomaticButton();
};
audioEl.volume = Math.max(0, Math.min(1, Number(storage.get('audioVolume', 1))));
volumeInput.value = String(audioEl.volume);
volumeInput.oninput = () => { audioEl.volume = Number(volumeInput.value); storage.set('audioVolume', audioEl.volume); };
syncAutomaticButton();
syncPlaybackUI();

// ── مواقيت الصلاة (AlAdhan API) ──────────────────────────────
const ALADHAN_API = 'https://api.aladhan.com/v1';
const KAABA = { lat: 21.4225, lon: 39.8262 };
const RIYADH = { lat: 24.7136, lon: 46.6753 };
const prayerOrder = ['Fajr', 'Sunrise', 'Dhuhr', 'Asr', 'Maghrib', 'Isha'];
const heroPrayerOrder = ['Fajr', 'Dhuhr', 'Asr', 'Maghrib', 'Isha'];
const prayerIcons = { Fajr: 'sunrise', Sunrise: 'sunrise', Dhuhr: 'sun', Asr: 'clock', Maghrib: 'sunset', Isha: 'moon' };
function prayerName(key) { return key === 'Sunrise' ? t('sunrise_word') : t('p_' + key.toLowerCase()); }
function monthName(n) { return t('m' + n); } // n: 1-12
// وحدات عدّاد الصلاة التنازلي: بالعربية كلمات كاملة (ساعة/دقيقة/ثانية)، وبباقي اللغات اختصارات عالمية شائعة (h/m/s) تفاديًا لإضافة 24 ترجمة أخرى لثلاث كلمات فقط
function countdownUnit(unit) {
  if (currentLang === 'ar') return { h: 'ساعة', m: 'دقيقة', s: 'ثانية' }[unit];
  return unit;
}

let userCoords = null;
let userLocationLabel = 'الرياض، السعودية';
let locationIsFallback = false; // true عندما تكون userLocationLabel هي القيمة الافتراضية (الرياض) لا موقعًا حقيقيًا تم رصده
// مصدر الموقع الحالي: 'auto' (GPS) | 'manual' (اختيار المستخدم يدويًا) | 'default' (تقديري، لم يُرصد بعد)
let locationSource = 'default';
// يمنع استجابة موقع قديمة (GPS بطيء، أو نتيجة بحث سابقة) من الكتابة فوق اختيار أحدث اختاره المستخدم
let locationRequestId = 0;
let calcMethod = storage.get('calcMethod', '4');
let todayTimings = null; // مواقيت اليوم الفعلي دائمًا (يقود العدّاد التنازلي)
let tomorrowFajrTime = null;
let prayerViewDate = startOfDay(new Date()); // اليوم المتصفَّح في صفحة "أوقات الصلاة"
let todayDateKey = null; // مفتاح اليوم الذي جُلبت له آخر مواقيت؛ يُستخدم لرصد دخول يوم جديد تلقائيًا
let timingsRequestId = 0; // حماية loadTodayTimings من استجابة قديمة (تبدّل الموقع/الطريقة/اليوم)
let pageTimingsRequestId = 0; // حماية loadPageTimings من استجابة قديمة (تصفّح أيام متعددة بسرعة)

function startOfDay(d) { const x = new Date(d); x.setHours(0, 0, 0, 0); return x; }
function isSameDay(a, b) { return a.getFullYear() === b.getFullYear() && a.getMonth() === b.getMonth() && a.getDate() === b.getDate(); }
function pad2(n) { return String(n).padStart(2, '0'); }
function formatDateParam(date) { return `${pad2(date.getDate())}-${pad2(date.getMonth() + 1)}-${date.getFullYear()}`; }

function parseHHMM(str, baseDate) {
  const [h, m] = str.split(':').map(Number);
  const d = new Date(baseDate);
  d.setHours(h, m, 0, 0);
  return d;
}

function formatArabicTime(str) {
  let [h, m] = str.split(':').map(Number);
  const isPM = h >= 12;
  h = h % 12; if (h === 0) h = 12;
  const period = currentLang === 'ar' ? (isPM ? 'م' : 'ص') : (isPM ? 'PM' : 'AM');
  return `${eastern(h)}:${eastern(pad2(m))} ${period}`;
}

function computeQibla({ lat, lon }) {
  const φ1 = lat * Math.PI / 180, φ2 = KAABA.lat * Math.PI / 180;
  const Δλ = (KAABA.lon - lon) * Math.PI / 180;
  const y = Math.sin(Δλ) * Math.cos(φ2);
  const x = Math.cos(φ1) * Math.sin(φ2) - Math.sin(φ1) * Math.cos(φ2) * Math.cos(Δλ);
  return (Math.atan2(y, x) * 180 / Math.PI + 360) % 360;
}

// تحقّق سريع من الاتصال قبل محاولة الجلب، بدل انتظار انتهاء المهلة الزمنية كاملة عند انقطاع واضح للإنترنت
function assertOnline() {
  if (navigator.onLine === false) throw new Error('offline');
}

async function fetchTimings(date, lat, lon, method) {
  assertOnline();
  // calendarMethod=UAQ يثبّت التقويم الهجري على تقويم أم القرى الرسمي بدل الاعتماد على افتراضي غير معلن
  const json = await fetchJson(`${ALADHAN_API}/timings/${formatDateParam(date)}?latitude=${lat}&longitude=${lon}&method=${method}&calendarMethod=UAQ`);
  return json.data;
}

async function reverseGeocodeLookup(coords) {
  assertOnline();
  // BigDataCloud لا يدعم بالضرورة كل لغات الواجهة الـ24؛ العربية تُطلب بدقة، وباقي اللغات تُطلب بالإنجليزية كافتراضٍ عالمي معقول
  const geoLang = currentLang === 'ar' ? 'ar' : 'en';
  const j = await fetchJson(`https://api.bigdatacloud.net/data/reverse-geocode-client?latitude=${coords.lat}&longitude=${coords.lon}&localityLanguage=${geoLang}`, 8000);
  const city = j.city || j.locality || j.principalSubdivision || '';
  const country = j.countryName || '';
  const label = [city, country].filter(Boolean).join(usesArabicScript() ? '، ' : ', ') || t('your_location');
  return { city, country, label };
}

// يحفظ الموقع المختار كاملًا في localStorage: خط العرض، خط الطول، المدينة، الدولة، وقت آخر تحديث، ومصدر التحديد
function saveLocation(coords, meta = {}) {
  const record = {
    lat: coords.lat,
    lon: coords.lon,
    city: meta.city || '',
    country: meta.country || '',
    label: meta.label || userLocationLabel,
    source: meta.source || locationSource,
    updatedAt: Date.now()
  };
  storage.set('location', record);
  return record;
}

// يجلب اسم المدينة/الدولة من الإحداثيات، يحدّث الحالة والواجهة، ويحفظ النتيجة في localStorage دائمًا —
// حتى عند فشل الجلب العكسي نحفظ الإحداثيات نفسها بتسمية عامة، فلا تُفقد دقة الموقع بسبب تعذّر تحديد اسم المدينة فقط
async function reverseGeocode(coords, source = 'auto') {
  try {
    const { city, country, label } = await reverseGeocodeLookup(coords);
    locationIsFallback = false;
    userLocationLabel = label;
    saveLocation(coords, { city, country, label, source });
  } catch (err) {
    userLocationLabel = t('your_location');
    saveLocation(coords, { label: userLocationLabel, source });
  }
  locationSource = source;
  updateLocationUI();
}

function geolocationErrorMessage(err) {
  switch (err && err.code) {
    case 1: return t('geo_err_denied');
    case 2: return t('geo_err_unavailable');
    case 3: return t('geo_err_timeout');
    default: return t('geo_err_default');
  }
}

function defaultLocationLabel() {
  // لا نُلحق "(تقديري)" بالاسم نفسه: شارة مصدر الموقع (location-source-badge) تُبلّغ هذا المعنى بوضوح بدل تكراره هنا
  locationIsFallback = true;
  if (currentLang === 'ar') return 'الرياض، السعودية';
  return usesArabicScript() ? `الرياض، ${t('country_sa')}` : `Riyadh, ${t('country_sa')}`;
}

// مصدر الحقيقة الوحيد لتحديد إحداثيات بدء التطبيق:
// 1) موقع محفوظ سابقًا في localStorage — يُستخدم فورًا دون أي طلب إذن موقع جديد.
// 2) لا يوجد موقع محفوظ — نحاول GPS مرة واحدة، ثم نحفظ الناتج أيًّا كان (نجاحًا حقيقيًا أو تقديرًا احتياطيًا)
//    كي لا نُعيد طلب إذن الموقع في كل زيارة لاحقة.
function resolveCoords() {
  const saved = storage.get('location', null);
  if (saved && typeof saved.lat === 'number' && typeof saved.lon === 'number') {
    locationSource = saved.source || 'auto';
    locationIsFallback = saved.source === 'default';
    userLocationLabel = saved.label || defaultLocationLabel();
    // نضبط userCoords هنا مباشرةً (لا ننتظر استقرار الـPromise) لأن هذا الفرع متزامن فعليًا:
    // applyLanguage() يُستدعى بعد initPrayerTimes() مباشرة في الكود دون انتظاره، وتحقّقه من "!userCoords"
    // قد يسبق تسوية هذا الـPromise فيُعيد الكتابة فوق الموقع المحفوظ بالتسمية الافتراضية خطأً لولا هذا الضبط الفوري
    const coords = { lat: saved.lat, lon: saved.lon };
    userCoords = coords;
    return Promise.resolve(coords);
  }
  return new Promise(resolve => {
    if (!window.isSecureContext || !navigator.geolocation) {
      locationSource = 'default';
      userLocationLabel = defaultLocationLabel();
      saveLocation(RIYADH, { label: userLocationLabel, source: 'default' });
      resolve(RIYADH);
      return;
    }
    navigator.geolocation.getCurrentPosition(
      async pos => {
        const coords = { lat: pos.coords.latitude, lon: pos.coords.longitude };
        await reverseGeocode(coords, 'auto');
        resolve(coords);
      },
      () => {
        locationSource = 'default';
        userLocationLabel = defaultLocationLabel();
        saveLocation(RIYADH, { label: userLocationLabel, source: 'default' });
        resolve(RIYADH);
      },
      { timeout: 8000 }
    );
  });
}

function locationSourceLabel() {
  return {
    auto: t('location_source_auto'),
    manual: t('location_source_manual'),
    default: t('location_source_default')
  }[locationSource] || '';
}

// يحدّث كل عناصر الواجهة التي تعرض تسمية الموقع الحالي ومصدره (تلقائي GPS / محفوظ يدويًا / تقديري)
function updateLocationUI() {
  document.querySelector('.location-pill b').textContent = userLocationLabel;
  setTextById('settingsLocationText', userLocationLabel);
  setTextById('homeTodayIn', t('today_in', { city: userLocationLabel }));
  const badgeText = locationSourceLabel();
  const pillBadge = document.getElementById('locationSourceBadge');
  const settingsBadge = document.getElementById('settingsLocationSourceBadge');
  if (pillBadge) pillBadge.textContent = badgeText;
  if (settingsBadge) settingsBadge.textContent = badgeText;
}

function updateTopbarDate(dateInfo) {
  const h = dateInfo.hijri;
  const gregorianDate = new Date(dateInfo.gregorian.year, dateInfo.gregorian.month.number - 1, dateInfo.gregorian.day);
  let hijriMonth = currentLang === 'ar' ? h.month.ar : h.month.en;
  try {
    hijriMonth = new Intl.DateTimeFormat(currentLang, { calendar: 'islamic-umalqura', month: 'long' }).format(gregorianDate);
  } catch (err) { /* نستخدم اسم الشهر الذي أعادته الخدمة إذا لم يدعم المتصفح التقويم */ }
  document.getElementById('hijriDate').textContent = `${eastern(h.day)} ${hijriMonth} ${eastern(h.year)}`;
  const g = dateInfo.gregorian;
  // gregorian.weekday من AlAdhan لا يحتوي على "ar"؛ نستخدم weekday.ar من hijri لأنه نفس اليوم (لغير العربية نستخدم Intl لاسم اليوم بلغة الواجهة)
  const weekdayName = currentLang === 'ar' ? h.weekday.ar : new Date(g.year, g.month.number - 1, g.day).toLocaleDateString(currentLang, { weekday: 'long' });
  const separator = currentLang === 'ar' ? '، ' : ', ';
  document.getElementById('gregorianDate').textContent = `${weekdayName}${separator}${eastern(g.day)} ${monthName(+g.month.number)} ${eastern(g.year)}`;
}

function renderLocalDateFallback() {
  const now = new Date();
  try {
    document.getElementById('hijriDate').textContent = new Intl.DateTimeFormat(currentLang, {
      calendar: 'islamic-umalqura', day: 'numeric', month: 'long', year: 'numeric'
    }).format(now);
    document.getElementById('gregorianDate').textContent = new Intl.DateTimeFormat(currentLang, {
      weekday: 'long', day: 'numeric', month: 'long', year: 'numeric'
    }).format(now);
  } catch (err) { /* تبقى القيمة الحالية في المتصفحات القديمة */ }
}

function renderHomePrayerList(timings) {
  const homeList = document.getElementById('homePrayerList');
  if (!homeList) return;
  homeList.innerHTML = prayerOrder.map(key =>
    `<div class="prayer-row" data-prayer="${key}"><div><span class="prayer-icon">${icon(prayerIcons[key])}</span><b>${prayerName(key)}</b><small class="next-badge" hidden>${t('next_badge')}</small></div><time>${formatArabicTime(timings[key])}</time></div>`
  ).join('');
}

function renderPrayerTiles(timings) {
  const tiles = document.getElementById('prayerTiles');
  if (!tiles) return;
  tiles.innerHTML = prayerOrder.map(key =>
    `<article data-prayer="${key}"><span>${icon(prayerIcons[key])}</span><b>${prayerName(key)}</b><time>${formatArabicTime(timings[key])}</time></article>`
  ).join('');
}

function renderInfoGrid(timings) {
  if (!document.getElementById('sunriseInfo')) return;
  document.getElementById('sunriseInfo').textContent = formatArabicTime(timings.Sunrise);
  document.getElementById('midnightInfo').textContent = formatArabicTime(timings.Midnight);
  const bearing = computeQibla(userCoords || RIYADH);
  document.getElementById('qiblaInfo').textContent = `${eastern(Math.round(bearing))}°`;
  const arrow = document.getElementById('qiblaArrow');
  arrow.style.display = 'flex';
  arrow.style.transform = `rotate(${bearing}deg)`;
}

function dayLabel(date) {
  const diffDays = Math.round((date - startOfDay(new Date())) / 86400000);
  if (diffDays === 0) return t('today');
  if (diffDays === 1) return t('tomorrow');
  if (diffDays === -1) return t('yesterday');
  const weekday = date.toLocaleDateString(currentLang, { weekday: 'long' });
  const separator = currentLang === 'ar' ? '، ' : ', ';
  return `${weekday}${separator}${eastern(date.getDate())} ${monthName(date.getMonth() + 1)}`;
}

const CALC_METHOD_KEYS = { 4: 'cm_umm_qura', 3: 'cm_mwl', 5: 'cm_egypt', 2: 'cm_isna', 8: 'cm_gulf', 10: 'cm_qatar', 13: 'cm_turkey' };
function methodLabel() { return t(CALC_METHOD_KEYS[calcMethod] || 'cm_umm_qura'); }

function highlightCurrentPrayer(name) {
  document.querySelectorAll('#homePrayerList [data-prayer]').forEach(row => {
    const isNext = row.dataset.prayer === name;
    row.classList.toggle('current', isNext);
    row.querySelector('.next-badge')?.toggleAttribute('hidden', !isNext);
  });
  document.querySelectorAll('#prayerTiles [data-prayer]').forEach(tile => tile.classList.toggle('active', tile.dataset.prayer === name));
}

function tickCountdown() {
  if (!todayTimings) return;
  if (currentPage !== 'home' && currentPage !== 'prayer') return; // لا عناصر عدّاد في الـDOM
  const now = new Date();
  let nextName = null, nextTime = null, crossedToTomorrow = false;
  for (const key of heroPrayerOrder) {
    const t = parseHHMM(todayTimings.timings[key], now);
    if (t > now) { nextName = key; nextTime = t; break; }
  }
  if (!nextName) {
    nextName = 'Fajr';
    crossedToTomorrow = true;
    if (tomorrowFajrTime) {
      const tmr = new Date(now); tmr.setDate(tmr.getDate() + 1);
      nextTime = parseHHMM(tomorrowFajrTime, tmr);
    }
  }
  if (!nextTime) return; // بانتظار جلب فجر الغد عند العبور بعد العشاء
  const diffMs = nextTime - now;
  const hh = eastern(pad2(Math.floor(diffMs / 3600000)));
  const mm = eastern(pad2(Math.floor((diffMs % 3600000) / 60000)));
  const ss = eastern(pad2(Math.floor((diffMs % 60000) / 1000)));

  const countdownEl = document.getElementById('countdown');
  if (countdownEl) countdownEl.innerHTML = `<span>${hh}<small>${countdownUnit('h')}</small></span><i>:</i><span>${mm}<small>${countdownUnit('m')}</small></span><i>:</i><span>${ss}<small>${countdownUnit('s')}</small></span>`;
  const heroLine = document.querySelector('.hero-copy p');
  if (heroLine) heroLine.textContent = `${t('remaining_prefix')} ${prayerName(nextName)}`;

  setTextById('nextPrayerName', prayerName(nextName));
  setTextById('prayerCountdown', `${hh}:${mm}:${ss}`);
  const rawTime = crossedToTomorrow ? tomorrowFajrTime : todayTimings.timings[nextName];
  const [timePart, period] = formatArabicTime(rawTime).split(' ');
  setTextById('nextPrayerTime', timePart);
  setTextById('nextPrayerPeriod', period);

  highlightCurrentPrayer(crossedToTomorrow ? null : nextName);
}

function timingsErrorMessage(err) {
  if (err.message === 'offline') return t('offline_error');
  if (err.message === 'timeout') return t('request_timeout');
  return t('toast_prayer_times_error');
}

async function loadTodayTimings() {
  const requestId = ++timingsRequestId; // كل نداء يُلغي أي نداء سابق لم تصل نتيجته بعد (تبدّل موقع/طريقة حساب/يوم)
  try {
    const data = await fetchTimings(new Date(), userCoords.lat, userCoords.lon, calcMethod);
    if (requestId !== timingsRequestId) return; // وصلت متأخرة بعد تغيّر لاحق؛ تُهمَل
    todayTimings = data;
    todayDateKey = new Date().toDateString();
    updateTopbarDate(data.date);
    renderHomePrayerList(data.timings);
    const tomorrow = new Date(); tomorrow.setDate(tomorrow.getDate() + 1);
    fetchTimings(tomorrow, userCoords.lat, userCoords.lon, calcMethod).then(d => {
      if (requestId !== timingsRequestId) return;
      tomorrowFajrTime = d.timings.Fajr; tickCountdown();
    }).catch(() => {});
    tickCountdown();
    scheduleTodayNotifications();
    scheduleDailyReminder();
  } catch (err) {
    if (requestId !== timingsRequestId) return;
    const homeList = document.getElementById('homePrayerList');
    if (homeList) homeList.innerHTML = `<div class="empty-inline">${timingsErrorMessage(err)}</div>`;
  }
}

async function loadPageTimings() {
  const label = document.getElementById('prayerLocationLabel');
  if (!label || !userCoords) return; // صفحة المواقيت غير مركَّبة الآن (أو لم يُحدَّد الموقع بعد)
  const requestId = ++pageTimingsRequestId;
  label.textContent = `${t('loading_location')} (${userLocationLabel})`;
  try {
    const data = isSameDay(prayerViewDate, new Date()) && todayTimings
      ? todayTimings
      : await fetchTimings(prayerViewDate, userCoords.lat, userCoords.lon, calcMethod);
    if (requestId !== pageTimingsRequestId || !label.isConnected) return;
    label.textContent = `${userLocationLabel} · ${locationSourceLabel()} · ${methodLabel()}`;
    renderPrayerTiles(data.timings);
    renderInfoGrid(data.timings);
    setTextById('prayerDateLabel', dayLabel(prayerViewDate));
    tickCountdown();
  } catch (err) {
    if (requestId !== pageTimingsRequestId || !label.isConnected) return;
    const msg = timingsErrorMessage(err);
    label.textContent = msg;
    toast(msg);
  }
}

// يُستدعى عند أي تغيّر في الموقع (تلقائي أو يدوي): يعيد ضبط بيانات اليوم الحالي ويعيد جلب المواقيت،
// ما يعيد جدولة التنبيهات تلقائيًا أيضًا (scheduleTodayNotifications/scheduleDailyReminder داخل loadTodayTimings)
async function refreshTimingsForNewLocation() {
  todayTimings = null;
  tomorrowFajrTime = null;
  prayerViewDate = startOfDay(new Date());
  await loadTodayTimings();
  await loadPageTimings();
}

async function initPrayerTimes() {
  userCoords = await resolveCoords();
  updateLocationUI();
  await loadTodayTimings();
  await loadPageTimings();
  setInterval(tickCountdown, 1000);
  // نتحقق كل دقيقة من دخول يوم جديد (بلا حاجة لإعادة تحميل الصفحة) لإعادة جلب المواقيت وإعادة جدولة التنبيهات تلقائيًا
  setInterval(() => {
    const nowKey = new Date().toDateString();
    if (todayDateKey && nowKey !== todayDateKey) {
      if (isSameDay(prayerViewDate, new Date(todayDateKey))) prayerViewDate = startOfDay(new Date());
      refreshTimingsForNewLocation();
    }
  }, 60000);
}

async function requestFreshLocation() {
  const buttons = [document.getElementById('useLocation'), document.getElementById('settingsLocation'), document.getElementById('modalUseCurrentLocation')].filter(Boolean);
  if (!window.isSecureContext) {
    toast(t('toast_https_required'));
    return;
  }
  if (!navigator.geolocation) {
    toast(t('toast_geo_unsupported'));
    return;
  }
  if (!navigator.onLine) {
    toast(t('offline_error'));
    return;
  }
  // إن كانت واجهة الأذونات متاحة نتحقق أولًا حتى لا نظهر رسالة عامة لموقع مرفوض مسبقًا
  if (navigator.permissions?.query) {
    try {
      const status = await navigator.permissions.query({ name: 'geolocation' });
      if (status.state === 'denied') {
        toast(geolocationErrorMessage({ code: 1 }));
        return;
      }
    } catch (err) { /* بعض المتصفحات لا تدعم استعلام إذن الموقع؛ نتابع بالطلب المباشر */ }
  }
  // نعطّل الأزرار أثناء الطلب دون المساس ببنيتها الداخلية: useLocation يحوي span[data-i18n] يعتمد عليه applyLanguage،
  // وsettingsLocation يحوي عنصر #settingsLocationText الذي تعتمد عليه دوال أخرى — لذا نستهدف الـspan الداخلي فقط لا الزر نفسه
  const useLocationLabel = document.querySelector('#useLocation [data-i18n]') || document.getElementById('useLocation');
  const originalUseLocationText = useLocationLabel?.textContent;
  buttons.forEach(b => { b.disabled = true; b.classList.add('is-loading'); });
  if (useLocationLabel) setIconLabel(useLocationLabel, 'pin', t('toast_locating'));
  toast(t('toast_locating'));
  const restoreButtons = () => {
    buttons.forEach(b => { b.disabled = false; b.classList.remove('is-loading'); });
    if (useLocationLabel) setIconLabel(useLocationLabel, 'pin', cleanIconText(originalUseLocationText));
  };
  const myRequestId = ++locationRequestId; // يُلغي أي طلب GPS/بحث يدوي سابق لم يصل بعد
  navigator.geolocation.getCurrentPosition(async pos => {
    if (myRequestId !== locationRequestId) { restoreButtons(); return; } // المستخدم اختار موقعًا آخر أثناء الانتظار
    const coords = { lat: pos.coords.latitude, lon: pos.coords.longitude };
    userCoords = coords;
    await reverseGeocode(coords, 'auto');
    if (myRequestId !== locationRequestId) { restoreButtons(); return; }
    closeLocationModal();
    await refreshTimingsForNewLocation();
    toast(t('toast_location_updated', { location: userLocationLabel }));
    restoreButtons();
  }, err => {
    if (myRequestId === locationRequestId) toast(geolocationErrorMessage(err));
    restoreButtons();
  }, { timeout: 8000, enableHighAccuracy: true });
}

// ── اختيار الموقع يدويًا: بحث عن مدينة/دولة عبر Nominatim (OpenStreetMap) ──
// ملاحظة صادقة: هذه خدمة بحث جغرافي مجانية بلا مفتاح API، مناسبة للاستخدام الحالي لكنها تخضع لسياسة استخدام عادل
// (معدّل طلبات محدود)؛ لموقع بحركة زوّار كبيرة يُفضَّل الانتقال لخدمة جغرافية مدفوعة تضمن معدّل استجابة أعلى.
async function searchCities(query) {
  assertOnline();
  const url = `https://nominatim.openstreetmap.org/search?q=${encodeURIComponent(query)}&format=json&addressdetails=1&limit=6&accept-language=${currentLang}`;
  const results = await fetchJson(url, 8000);
  return results.map(r => ({
    label: r.display_name,
    city: r.address?.city || r.address?.town || r.address?.village || r.address?.county || r.name || query,
    country: r.address?.country || '',
    lat: parseFloat(r.lat),
    lon: parseFloat(r.lon)
  }));
}

let citySearchDebounceTimer = null;
let citySearchToken = 0;

function renderCitySearchResults(items) {
  const box = document.getElementById('citySearchResults');
  if (!items.length) { box.innerHTML = `<div class="empty-inline">${t('no_city_match')}</div>`; return; }
  box.innerHTML = items.map((item, i) =>
    `<button type="button" class="city-result-item" data-index="${i}">${[item.city, item.country].filter(Boolean).join(usesArabicScript() ? '، ' : ', ') || item.label}</button>`
  ).join('');
  box.querySelectorAll('.city-result-item').forEach(btn => {
    btn.onclick = () => selectManualLocation(items[+btn.dataset.index]);
  });
}

async function selectManualLocation(item) {
  const coords = { lat: item.lat, lon: item.lon };
  const label = [item.city, item.country].filter(Boolean).join(usesArabicScript() ? '، ' : ', ') || item.label;
  locationRequestId++; // يُلغي أي طلب GPS كان معلّقًا؛ الاختيار اليدوي الحالي هو الأحدث الآن
  userCoords = coords;
  userLocationLabel = label;
  locationSource = 'manual';
  locationIsFallback = false;
  saveLocation(coords, { city: item.city, country: item.country, label, source: 'manual' });
  updateLocationUI();
  closeLocationModal();
  await refreshTimingsForNewLocation();
  toast(t('toast_location_updated', { location: label }));
}

function openLocationModal() {
  document.getElementById('locationModal').hidden = false;
  document.getElementById('citySearchInput').value = '';
  document.getElementById('citySearchResults').innerHTML = '';
  document.getElementById('citySearchInput').focus();
  pushTouchUiHistory('location-modal');
}
function closeLocationModal() {
  document.getElementById('locationModal').hidden = true;
}
document.getElementById('closeLocationModal').onclick = closeLocationModal;
document.getElementById('locationModal').addEventListener('click', event => {
  if (event.target.id === 'locationModal') closeLocationModal();
});
document.getElementById('modalUseCurrentLocation').onclick = requestFreshLocation;
document.getElementById('locationPill').onclick = openLocationModal;
document.getElementById('locationPill').addEventListener('keydown', event => {
  if (event.key === 'Enter' || event.key === ' ') { event.preventDefault(); openLocationModal(); }
});
document.getElementById('citySearchInput').addEventListener('input', event => {
  const query = event.target.value.trim();
  clearTimeout(citySearchDebounceTimer);
  const box = document.getElementById('citySearchResults');
  if (query.length < 2) { box.innerHTML = ''; return; }
  // تأخير نصف ثانية بعد توقف الكتابة احترامًا لسياسة الاستخدام العادل لخدمة Nominatim المجانية، وتفاديًا لطلبات زائدة
  citySearchDebounceTimer = setTimeout(async () => {
    const myToken = ++citySearchToken;
    box.innerHTML = `<div class="empty-inline">${t('toast_locating')}</div>`;
    try {
      const items = await searchCities(query);
      if (myToken !== citySearchToken) return; // نتيجة بحث سابقة متأخرة؛ المستخدم كتب استعلامًا أحدث
      renderCitySearchResults(items);
    } catch (err) {
      if (myToken !== citySearchToken) return;
      box.innerHTML = `<div class="empty-inline">${err.message === 'offline' ? t('offline_error') : t('city_search_error')}</div>`;
    }
  }, 500);
});

function applyTheme(value) {
  const dark = value === 'dark' || (value === 'system' && matchMedia('(prefers-color-scheme: dark)').matches);
  document.body.classList.toggle('dark', dark);
  document.querySelectorAll('[data-theme-value]').forEach(button => button.classList.toggle('selected', button.dataset.themeValue === value));
  document.getElementById('themeQuick').innerHTML = icon(dark ? 'sun' : 'moon');
  storage.set('theme', value);
}

applyTheme(storage.get('theme', 'system'));
document.getElementById('themeQuick').onclick = () => applyTheme(document.body.classList.contains('dark') ? 'light' : 'dark');

// إعدادات التبديل (checkbox) البسيطة: نحفظ حالتها فعليًا في localStorage
// ── إشعارات الويب (Web Notifications API) ────────────────────
// ملاحظة صادقة: هذه إشعارات تعمل عبر مؤقّتات (setTimeout) طالما التبويب مفتوحًا في المتصفح؛
// وليست إشعارات دفع (push) تصل والمتصفح مغلق، لأن ذلك يتطلب خادم إشعارات فعليًا.
let scheduledPrayerTimers = [];
let scheduledDailyReminderTimer = null;

function clearScheduledTimers(arr) { arr.forEach(id => clearTimeout(id)); arr.length = 0; }

async function ensureNotificationPermission() {
  if (!('Notification' in window)) { toast(t('toast_notif_unsupported')); return false; }
  if (Notification.permission === 'granted') return true;
  if (Notification.permission === 'denied') {
    toast(t('toast_notif_blocked'));
    return false;
  }
  const result = await Notification.requestPermission();
  if (result !== 'granted') { toast(t('toast_notif_permission_denied')); return false; }
  return true;
}

function showAppNotification(title, body) {
  // لا يوجد ملف أيقونة فعلي بعد في المشروع (سيُضاف ضمن استكمال PWA)؛ نتجنب تمرير مسار أيقونة غير موجود
  try { new Notification(title, { body }); }
  catch (err) { /* بعض المتصفحات (مثل iOS Safari) لا تدعم new Notification إطلاقًا */ }
}

function scheduleTodayNotifications() {
  clearScheduledTimers(scheduledPrayerTimers);
  if (!todayTimings || window.Notification?.permission !== 'granted') return;
  const now = new Date();
  if (settingOn('prayerNotifications')) {
    heroPrayerOrder.forEach(key => {
      const prayerTime = parseHHMM(todayTimings.timings[key], now);
      const delay = prayerTime - now;
      if (delay > 0) {
        // نعيد استخدام تسميات الإعدادات الموجودة كعنوان/نص للإشعار بدل إضافة مفاتيح ترجمة جديدة
        scheduledPrayerTimers.push(setTimeout(() => {
          showAppNotification(t('prayer_notif_toggle'), `${prayerName(key)} — ${t('adhan_time')}`);
        }, delay));
      }
    });
  }
  if (settingOn('sunriseNotification')) {
    const sunrise = parseHHMM(todayTimings.timings.Sunrise, now);
    const delay = sunrise.getTime() - 10 * 60 * 1000 - now.getTime();
    if (delay > 0) {
      scheduledPrayerTimers.push(setTimeout(() => {
        showAppNotification(t('sunrise_notif_toggle'), t('sunrise_notif_desc'));
      }, delay));
    }
  }
}

function scheduleDailyReminder() {
  if (scheduledDailyReminderTimer) clearTimeout(scheduledDailyReminderTimer);
  if (!settingOn('dailyReminder') || window.Notification?.permission !== 'granted') return;
  const now = new Date();
  const target = new Date(now);
  target.setHours(20, 0, 0, 0); // ٨ مساءً، وقت افتراضي ثابت لتذكير الورد اليومي
  if (target <= now) target.setDate(target.getDate() + 1);
  scheduledDailyReminderTimer = setTimeout(() => {
    showAppNotification(t('daily_reminder_toggle'), t('daily_wird'));
    scheduleDailyReminder(); // إعادة الجدولة لليوم التالي تلقائيًا
  }, target - now);
}

const persistedToggleIds = ['prayerNotifications', 'dailyReminder', 'sunriseNotification', 'easternNumeralsToggle'];
// حالة المفاتيح تُقرأ من التخزين لا من الـDOM لأن صفحة الإعدادات ليست دائمًا موجودة في الصفحة
function settingOn(id) {
  const saved = storage.get(`setting:${id}`, null);
  return saved === null ? id === 'easternNumeralsToggle' : Boolean(saved);
}
easternNumeralsOn = settingOn('easternNumeralsToggle');
// عند تحميل الصفحة: إن كانت التفضيلات محفوظة سابقًا والإذن ممنوح بالفعل نُجدول الإشعارات فورًا بلا حاجة لتفاعل جديد
if (window.Notification?.permission === 'granted') scheduleDailyReminder();

function syncSettingsControls() {
  const languageSelect = $('languageSelect');
  if (!languageSelect) return;
  languageSelect.value = currentLang;
  persistedToggleIds.forEach(id => { const el = $(id); if (el) el.checked = settingOn(id); });
  const method = $('calculationMethod');
  if (method) method.value = calcMethod;
  applyTheme(storage.get('theme', 'system'));
  updateLocationUI();
  refreshAllCustomSelects();
}

function mountSettings(section) {
  const languageSelect = $('languageSelect');
  languageSelect.innerHTML = LANGS.map(l => `<option value="${l.code}">${l.name}</option>`).join('');
  languageSelect.onchange = () => {
    applyLanguage(languageSelect.value);
    toast(t('toast_lang_saved'));
  };
  section.querySelectorAll('[data-theme-value]').forEach(button => button.onclick = () => applyTheme(button.dataset.themeValue));
  ['prayerNotifications', 'sunriseNotification'].forEach(id => {
    const el = $(id);
    el.onchange = async () => {
      if (el.checked) {
        const granted = await ensureNotificationPermission();
        if (!granted) { el.checked = false; storage.set(`setting:${id}`, false); return; }
      }
      storage.set(`setting:${id}`, el.checked);
      scheduleTodayNotifications();
      toast(t(el.checked ? 'toast_notif_on' : 'toast_notif_off'));
    };
  });
  $('dailyReminder').onchange = async () => {
    const el = $('dailyReminder');
    if (el.checked) {
      const granted = await ensureNotificationPermission();
      if (!granted) { el.checked = false; storage.set('setting:dailyReminder', false); return; }
    }
    storage.set('setting:dailyReminder', el.checked);
    scheduleDailyReminder();
    toast(t(el.checked ? 'toast_daily_reminder_on' : 'toast_daily_reminder_off'));
  };
  $('easternNumeralsToggle').onchange = () => {
    easternNumeralsOn = $('easternNumeralsToggle').checked;
    storage.set('setting:easternNumeralsToggle', easternNumeralsOn);
    toast(t('toast_setting_saved'));
    if (todayTimings) updateTopbarDate(todayTimings.date);
    pageModules[currentPage]?.render?.();
  };
  $('calculationMethod').onchange = async event => {
    calcMethod = event.target.value;
    storage.set('calcMethod', calcMethod);
    todayTimings = null;
    tomorrowFajrTime = null;
    await loadTodayTimings();
    await loadPageTimings();
    toast(t('toast_calc_method_updated'));
  };
  // زر "الموقع" في الإعدادات يفتح نافذة الاختيار (استخدام موقعي الحالي أو بحث يدوي) بدل تحديد GPS مباشرةً
  $('settingsLocation').onclick = openLocationModal;
  $('clearLocalData').onclick = clearLocalDataFlow;
  $('openAbout').onclick = openAboutModal;
  syncSettingsControls();
}

async function clearLocalDataFlow() {
  // نعيد استخدام تسميات الإعدادات الموجودة لبناء رسالة تأكيد مترجمة بدل إضافة مفتاح ترجمة جديد
  if (!confirm(`${t('clear_data')}? ${t('clear_data_desc')}`)) return;
  storage.clearAll();
  cancelPendingAudio({ clearSource: true });
  playQueue = [];
  player.hidden = true;
  playbackSource = 'listen';
  syncAutomaticButton();
  toast(t('toast_data_cleared'));
  listTab = 'surahs';
  listenSurahNumber = 1;
  easternNumeralsOn = true;
  applyTheme('system');
  applyReaderFontSize(31);
  audioEl.volume = 1;
  volumeInput.value = '1';
  clearScheduledTimers(scheduledPrayerTimers);
  if (scheduledDailyReminderTimer) { clearTimeout(scheduledDailyReminderTimer); scheduledDailyReminderTimer = null; }
  calcMethod = '4';
  todayTimings = null;
  tomorrowFajrTime = null;
  // مسح الموقع المحفوظ يعيدنا لسلوك أول زيارة: محاولة GPS جديدة (أو التقدير الاحتياطي) بدل الإبقاء على موقع قديم في الذاكرة
  userCoords = null;
  locationSource = 'default';
  locationIsFallback = false;
  locationRequestId++;
  applyLanguage('ar'); // يعيد رسم صفحة الإعدادات بالقيم الافتراضية وكل الواجهة
  userCoords = await resolveCoords();
  updateLocationUI();
  await loadTodayTimings();
  await loadPageTimings();
}

function renderPrayerPage() {
  if ($('prayerTiles') && userCoords) loadPageTimings();
}
function mountPrayer() {
  $('useLocation').onclick = requestFreshLocation;
  $('pickLocationManually').onclick = openLocationModal;
  $('previousDay').onclick = () => { prayerViewDate.setDate(prayerViewDate.getDate() - 1); loadPageTimings(); };
  $('nextDay').onclick = () => { prayerViewDate.setDate(prayerViewDate.getDate() + 1); loadPageTimings(); };
  renderPrayerPage();
}

const READER_FONT_SIZES = [26, 31, 38];
function applyReaderFontSize(size, { announce = false } = {}) {
  const normalized = READER_FONT_SIZES.includes(+size) ? +size : 31;
  document.documentElement.style.setProperty('--reader-size', `${normalized}px`);
  storage.set('readerFontSize', normalized);
  document.querySelectorAll('#fontMenu [data-font-size]').forEach(button => button.classList.toggle('active', +button.dataset.fontSize === normalized));
  if (announce) toast(tx('font_saved'));
}
function closeFontMenu() {
  const menu = $('fontMenu');
  if (menu) menu.hidden = true;
  $('fontButton')?.setAttribute('aria-expanded', 'false');
}
function toggleFontMenu() {
  const menu = $('fontMenu');
  if (!menu) return;
  menu.hidden = !menu.hidden;
  $('fontButton')?.setAttribute('aria-expanded', String(!menu.hidden));
  if (!menu.hidden) pushTouchUiHistory('font-menu');
}
document.addEventListener('click', event => { if (!event.target.closest('.font-control')) closeFontMenu(); });

// وحدات كل صفحة: mount عند تركيب HTML الصفحة، render لإعادة رسم أجزائها الديناميكية (تغيّر اللغة/وصول البيانات)، unmount قبل إفراغها
const pageModules = {
  home: { mount: renderHome, render: renderHome },
  quran: { mount: mountQuran, render: renderQuranPage },
  reader: { mount: mountReader, unmount: unmountReader },
  listen: { mount: mountListen, render: renderListenPage },
  prayer: { mount: mountPrayer, render: renderPrayerPage },
  favorites: { mount: renderFavoritesPage, render: renderFavoritesPage },
  settings: { mount: mountSettings, render: syncSettingsControls }
};

async function copyText(text) {
  if (navigator.clipboard?.writeText && window.isSecureContext) { await navigator.clipboard.writeText(text); return; }
  const input = document.createElement('textarea');
  input.value = text; input.setAttribute('readonly', ''); input.style.position = 'fixed'; input.style.opacity = '0';
  document.body.appendChild(input); input.select();
  const copied = document.execCommand('copy'); input.remove();
  if (!copied) throw new Error('copy-failed');
}

const ayahActionsModal = document.getElementById('ayahActionsModal');
const ayahActionsTitle = document.getElementById('ayahActionsTitle');
const saveAyahAction = document.getElementById('saveAyahAction');
const shareAyahAction = document.getElementById('shareAyahAction');
const listenAyahAction = document.getElementById('ListenToAverse');
let selectedAyahForActions = null;
let selectedAyahElement = null;

function ayahTitleSnippet(text) {
  const normalized = String(text || '').replace(/\s+/g, ' ').trim();
  return normalized.length > 52 ? `${normalized.slice(0, 52)}…` : normalized;
}
function updateAyahActionState() {
  if (!selectedAyahForActions) return;
  // "محفوظة" = هذه الآية هي موضع القراءة المحفوظ الحالي
  const last = storage.get('lastReading', null);
  const saved = last?.number === selectedAyahForActions.surahNumber && last?.ayahNumberInSurah === selectedAyahForActions.ayahNumber;
  saveAyahAction.classList.toggle('saved', saved);
  saveAyahAction.setAttribute('aria-pressed', String(saved));
  setIconLabel(saveAyahAction, 'bookmark', tx('save_ayah'));
  setIconLabel(shareAyahAction, 'share', tx('share_ayah'));
  setIconLabel(listenAyahAction, 'headphones', tx('listen_ayah'));
}

// تفسير الآية (التفسير الميسّر) داخل #explanation
let explanationToken = 0;
async function loadExplanation(item) {
  const box = document.getElementById('explanation');
  if (!box) return;
  const token = ++explanationToken;
  const key = item.globalNumber;
  if (tafsirCache.has(key)) { box.textContent = tafsirCache.get(key); return; }
  box.textContent = tx('explanation_loading');
  try {
    const json = await fetchJson(`${QURAN_API}/ayah/${key}/ar.muyassar`);
    const text = json?.data?.text;
    if (!text) throw new Error('empty');
    tafsirCache.set(key, text);
    if (token === explanationToken) box.textContent = text;
  } catch (err) {
    if (token !== explanationToken) return;
    box.innerHTML = `${tx('explanation_error')} <button type="button" class="text-button" id="retryExplanation">${t('retry')}</button>`;
    document.getElementById('retryExplanation').onclick = () => loadExplanation(item);
  }
}

// حفظ الآية كآخر موقع قراءة؛ والورد اليومي/نسبة الختمة تُحسب من هذا الموضع (داخل saveLastReading)
function saveAyahAsReadingPosition(item) {
  const info = { numberInSurah: item.ayahNumber, globalNumber: item.globalNumber, juz: item.juz };
  saveLastReading(item.surahNumber, info);
  saveReadingPositionEntry(item.surahNumber, info);
  hasUserScrolledThisSession = false; // لا يطغى الحفظ التلقائي لموضع التمرير على الآية المحفوظة صراحةً
  updateAyahActionState();
  toast(tx('position_saved_ayah'));
}

// إستماع لآية واحدة فقط (بصوت القارئ الحالي، أو العفاسي إن كان قارئه متاحًا بملفات السور فقط)
async function playSingleAyah(item) {
  cancelPendingAudio({ clearSource: true });
  const requestId = audioRequestId;
  const reciter = currentReciter.chapterOnly ? (reciters.find(r => !r.chapterOnly) || reciters[0]) : currentReciter;
  playbackSource = 'reader-ayah';
  singleAyahMode = true;
  singleAyahReciter = reciter;
  playingSurahNumber = item.surahNumber;
  playQueue = [item.globalNumber];
  queueIndex = 0;
  updatePlayerReciterPhoto(reciter);
  player.hidden = false;
  const surahName = usesArabicScript() ? item.surahName : (item.englishName || item.surahName);
  trackTitleEl.textContent = `${surahName} · ${eastern(item.ayahNumber)}`;
  trackReciterEl.textContent = reciterDisplayName(reciter);
  syncAutomaticButton();
  syncTrackNavigationLabels();
  if (reciter !== currentReciter) toast(tx('ayah_reciter_notice'));
  await playCurrentAyah({ requestId });
}

function openAyahActions(item, sourceElement) {
  selectedAyahForActions = item;
  selectedAyahElement?.classList.remove('context-active');
  selectedAyahElement = sourceElement;
  selectedAyahElement?.classList.add('context-active');
  ayahActionsTitle.textContent = ayahTitleSnippet(item.text);
  updateAyahActionState();
  loadExplanation(item);
  ayahActionsModal.hidden = false;
  document.getElementById('closeAyahActions').focus();
  pushTouchUiHistory('ayah-actions');
}
function closeAyahActions() {
  explanationToken++;
  ayahActionsModal.hidden = true;
  selectedAyahElement?.classList.remove('context-active');
  const focusTarget = selectedAyahElement;
  selectedAyahElement = null;
  selectedAyahForActions = null;
  focusTarget?.focus();
}
async function shareSelectedAyah() {
  const item = selectedAyahForActions;
  if (!item) return;
  const url = new URL(location.href);
  url.hash = 'reader';
  url.searchParams.set('surah', String(item.surahNumber));
  url.searchParams.set('ayah', String(item.ayahNumber));
  const surahName = usesArabicScript() ? item.surahName : (item.englishName || item.surahName);
  const shareData = { title: `${surahName} · ${eastern(item.ayahNumber)}`, text: `${item.text}\n— ${surahName}، ${t('ayah_suffix')} ${eastern(item.ayahNumber)}`, url: url.toString() };
  try {
    if (navigator.share) { await navigator.share(shareData); toast(tx('shared')); }
    else { await copyText(`${shareData.text}\n${shareData.url}`); toast(tx('link_copied')); }
    closeAyahActions();
  } catch (err) {
    if (err.name !== 'AbortError') {
      try { await copyText(`${shareData.text}\n${shareData.url}`); toast(tx('link_copied')); closeAyahActions(); }
      catch (copyError) { toast(tx('share_failed')); }
    }
  }
}
document.getElementById('closeAyahActions').onclick = closeAyahActions;
ayahActionsModal.addEventListener('click', event => { if (event.target === ayahActionsModal) closeAyahActions(); });
saveAyahAction.onclick = () => { if (selectedAyahForActions) saveAyahAsReadingPosition(selectedAyahForActions); };
if (listenAyahAction) listenAyahAction.onclick = () => { const item = selectedAyahForActions; if (!item) return; closeAyahActions(); playSingleAyah(item); };
shareAyahAction.onclick = shareSelectedAyah;

async function shareCurrentSurah() {
  if (!currentSurahNumber) { toast(t('toast_open_surah_first')); return; }
  const meta = surahs.find(s => s.number === currentSurahNumber) || ayahCache.get(currentSurahNumber);
  const url = new URL(location.href);
  url.hash = 'reader';
  url.searchParams.set('surah', String(currentSurahNumber));
  const shareData = { title: meta ? surahDisplayName(meta) : document.title, text: meta ? `${t('quran_title')} — ${surahDisplayName(meta)}` : t('quran_title'), url: url.toString() };
  try {
    if (navigator.share) { await navigator.share(shareData); toast(tx('shared')); }
    else { await copyText(shareData.url); toast(tx('link_copied')); }
  } catch (err) {
    if (err.name !== 'AbortError') {
      try { await copyText(shareData.url); toast(tx('link_copied')); }
      catch (copyError) { toast(tx('share_failed')); }
    }
  }
}

const aboutModal = document.getElementById('aboutModal');
function openAboutModal() {
  aboutModal.hidden = false;
  document.getElementById('closeAbout').focus();
  pushTouchUiHistory('about-modal');
}
function closeAboutModal() { aboutModal.hidden = true; }
document.getElementById('closeAbout').onclick = closeAboutModal;
aboutModal.addEventListener('click', event => { if (event.target === aboutModal) closeAboutModal(); });

// ── التشغيل ──────────────────────────────────────────────────
applyReaderFontSize(storage.get('readerFontSize', 31));
applyLanguage(currentLang);
initPrayerTimes();
loadSurahList();
const initialRoute = (location.hash || '#home').slice(1);
route(initialRoute, { fromHistory: true, shareParams: true });
