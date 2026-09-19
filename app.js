const express = require('express');
const bcrypt = require('bcryptjs');
const session = require('express-session');
const multer = require('multer');
const fs = require('fs');
const http = require('http');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
    cors: {
        origin: "*",
        methods: ["GET", "POST"]
    }
});

// Create sounds directory if not exists
if (!fs.existsSync('./public')) {
    fs.mkdirSync('./public');
}
if (!fs.existsSync('./public/sounds')) {
    fs.mkdirSync('./public/sounds');
}

const soundFileName = 'message-notification.wav';
const soundPath = `./public/sounds/${soundFileName}`;

function generateNotificationWav() {
    const sampleRate = 22050;
    const durationSeconds = 0.55;
    const totalSamples = Math.floor(sampleRate * durationSeconds);
    const buffer = Buffer.alloc(44 + totalSamples * 2);

    // RIFF header
    buffer.write('RIFF', 0, 'ascii');
    buffer.writeUInt32LE(36 + totalSamples * 2, 4);
    buffer.write('WAVE', 8, 'ascii');
    buffer.write('fmt ', 12, 'ascii');
    buffer.writeUInt32LE(16, 16);
    buffer.writeUInt16LE(1, 20);
    buffer.writeUInt16LE(1, 22);
    buffer.writeUInt32LE(sampleRate, 24);
    buffer.writeUInt32LE(sampleRate * 2, 28);
    buffer.writeUInt16LE(2, 32);
    buffer.writeUInt16LE(16, 34);
    buffer.write('data', 36, 'ascii');
    buffer.writeUInt32LE(totalSamples * 2, 40);

    for (let i = 0; i < totalSamples; i++) {
        const t = i / sampleRate;
        const tone = Math.sin(2 * Math.PI * 880 * t) * 0.55 + Math.sin(2 * Math.PI * 660 * t) * 0.25;
        const envelope = Math.min(1, t * 4) * Math.max(0, 1 - (t / durationSeconds));
        const sample = Math.max(-1, Math.min(1, tone * envelope));
        const intSample = Math.round(sample * 32767);
        buffer.writeInt16LE(intSample, 44 + i * 2);
    }

    return buffer;
}

if (!fs.existsSync(soundPath)) {
    fs.writeFileSync(soundPath, generateNotificationWav());
    console.log(`✅ Created notification sound: ${soundPath}`);
}

// Store connected sockets
const connectedUsers = new Map(); // userId -> socket.id
const typingUsers = new Map(); // userId -> { partnerId, timeout }

const PORT = process.env.PORT || 8080;

// ==========================================
// CONFIGURATION
// ==========================================
const CONFIG = {
    TRIAL_DAYS: 7,
    COINS_PER_MESSAGE: 1,
    GIFT_CARD_MINIMUM: 50,
    COINS_PER_PURCHASE: 500,
    COIN_PRICE: 0.10,
    MAX_PROFILE_PHOTOS: 5,
    MALE_FREE_PHOTOS_PER_DAY: 2,
    MALE_PHOTO_SEND_COST: 10,
    MALE_FREE_PROFILE_VIEWS_PER_DAY: 5,
    MALE_PROFILE_VIEW_COST: 20,
    MALE_FREE_MESSAGES_PER_DAY: 10
};

const COIN_PRICE = 0.10;
const MIN_PURCHASE_USD = 50;
const MIN_COINS = Math.ceil(MIN_PURCHASE_USD / COIN_PRICE);

// ==========================================
// PHONE NUMBER DETECTION & CENSORSHIP
// ==========================================
function detectContactInfo(text) {
    const patterns = [
        /\+\d{1,4}[\s\-]?\d{1,4}[\s\-]?\d{1,4}[\s\-]?\d{1,4}[\s\-]?\d{0,4}/g,
        /\(?\d{3}\)?[\s\-\.]?\d{3}[\s\-\.]?\d{4}/g,
        /whatsapp[:\s]?\+?\d{7,15}/gi,
        /wa\.me\/\d+/gi,
        /t\.me\/\w+/gi,
        /telegram[:\s]?\w+/gi,
        /[\w\.-]+@[\w\.-]+\.\w+/g,
        /@[\w\.]+/g,
        /(?:call|phone|contact|reach|text|whatsapp|telegram)[\s:]*\+?\d[\d\s\-\(\)]{7,}/gi,
        /\b\d{7,}\b/g
    ];
    
    let detected = [];
    let censoredText = text;
    
    patterns.forEach(pattern => {
        const matches = text.match(pattern);
        if (matches) {
            matches.forEach(match => {
                if (!detected.find(d => d.original === match)) {
                    detected.push({
                        original: match,
                        type: getContactType(match)
                    });
                    censoredText = censoredText.replace(match, '*'.repeat(match.length));
                }
            });
        }
    });
    
    return {
        hasContact: detected.length > 0,
        detected: detected,
        censoredText: censoredText,
        originalText: text
    };
}

function getContactType(text) {
    text = text.toLowerCase();
    if (text.includes('whatsapp') || text.includes('wa.me')) return 'WhatsApp';
    if (text.includes('telegram') || text.includes('t.me')) return 'Telegram';
    if (text.includes('@') && text.includes('.')) return 'Email';
    if (text.startsWith('@')) return 'Social Media';
    if (text.includes('+')) return 'International Phone';
    return 'Phone Number';
}

// ==========================================
// DATABASE
// ==========================================
const users = [];
const transactions = [];
const messages = [];
const favorites = [];
const reports = [];
const notifications = [];
const censorshipLogs = [];
const photoSendLogs = [];
const profileViewLogs = [];
const messageSendLogs = [];
const adminAssignments = []; // Admin assigns males to females
const albums = []; // Admin-managed album photos for female users
const chatAlbums = []; // Chat album photos female can send in chat
const userSessions = new Map(); // Track active sessions
let userIdCounter = 1;
let notificationIdCounter = 1;

function createChatAlbumEntry(femaleId, photoFile, uploadedBy) {
    return {
        id: chatAlbums.length + 1,
        femaleId: femaleId,
        photoFile: photoFile,
        uploadedBy: uploadedBy,
        uploadedAt: new Date()
    };
}

// Generate unique 6-digit ID based on gender
function generateUserId(gender) {
    const prefix = gender === 'female' ? '1' : '2'; // 1xxxxx for females, 2xxxxx for males
    let id;
    do {
        const random = Math.floor(Math.random() * 99999).toString().padStart(5, '0');
        id = parseInt(prefix + random);
    } while (users.find(u => u.id === id));
    return id;
}

function createUser(data) {
    const gender = data.gender || 'male';
    const userId = data.id || generateUserId(gender);
    
    return {
        id: userId,
        displayId: userId.toString(), // 6-digit display ID
        email: '',
        password: '',
        showPassword: '',
        name: '',
        age: 18,
        gender: '',
        role: 'user',
        coins: 0,
        trialDays: CONFIG.TRIAL_DAYS,
        trialStart: null,
        isTrialActive: false,
        isBlocked: false,
        isVerified: false,
        isOnline: false,
        lastActive: new Date(),
        bio: '',
        photo: null,
        photos: [],
        location: '',
        country: '',
        interests: '',
        lookingFor: 'Dating',
        occupation: '',
        createdAt: new Date(),
        profileViews: 0,
        totalMessagesReceived: 0,
        ...data
    };
}

// Create Admin with 6-digit ID
users.push(createUser({
    id: 100001, // Admin gets 100001
    email: 'admin@site.com',
    password: bcrypt.hashSync('admin123', 10),
    showPassword: 'admin123',
    name: 'Administrator',
    age: 30,
    gender: 'male',
    role: 'admin',
    coins: 999999,
    isVerified: true,
    bio: 'Site Administrator',
    location: 'Global HQ',
    occupation: 'Site Admin',
    photos: []
}));

// Sample Females (IDs starting with 1)
const sampleFemales = [
    { id: 100002, name: 'Sarah Johnson', age: 24, email: 'sarah@site.com', password: 'password123', location: 'New York', country: 'USA', bio: 'Adventure seeker and coffee lover!', interests: 'Travel, Photography, Yoga', lookingFor: 'Serious Relationship', occupation: 'Marketing Manager' },
    { id: 100003, name: 'Maria Garcia', age: 27, email: 'maria@site.com', password: 'password123', location: 'Los Angeles', country: 'USA', bio: 'Professional dancer and artist.', interests: 'Dance, Art, Beach', lookingFor: 'Dating', occupation: 'Dance Instructor' },
    { id: 100004, name: 'Emma Wilson', age: 22, email: 'emma@site.com', password: 'password123', location: 'London', country: 'UK', bio: 'Book lover and tea enthusiast.', interests: 'Reading, Writing, Hiking', lookingFor: 'Long-term Relationship', occupation: 'Journalist' },
    { id: 100005, name: 'Linda Chen', age: 25, email: 'linda@site.com', password: 'password123', location: 'Toronto', country: 'Canada', bio: 'Tech professional who loves outdoors.', interests: 'Hiking, Photography, Tech', lookingFor: 'Dating', occupation: 'Software Engineer' },
    { id: 100006, name: 'Sophie Martin', age: 26, email: 'sophie@site.com', password: 'password123', location: 'Sydney', country: 'Australia', bio: 'Beach lover and surfer.', interests: 'Surfing, Beach, Cooking', lookingFor: 'Serious Relationship', occupation: 'Marine Biologist' },
    { id: 100007, name: 'Aisha Patel', age: 23, email: 'aisha@site.com', password: 'password123', location: 'Mumbai', country: 'India', bio: 'Family-oriented and ambitious.', interests: 'Cooking, Bollywood, Travel', lookingFor: 'Marriage', occupation: 'Doctor' }
];

sampleFemales.forEach(f => {
    users.push(createUser({
        ...f,
        gender: 'female',
        password: bcrypt.hashSync(f.password, 10),
        showPassword: f.password,
        isOnline: Math.random() > 0.5,
        lastActive: new Date(Date.now() - Math.random() * 86400000),
        photos: []
    }));
});

const sampleSarah = users.find(u => u.id === 100002);
if (sampleSarah) {
    sampleSarah.photos = ['sample-photo-1.jpg'];
}

// Sample Males (IDs starting with 2)
const sampleMales = [
    { id: 200001, name: 'John Smith', age: 28, email: 'john@site.com', password: 'password123', location: 'San Francisco', country: 'USA', bio: 'Software developer looking for connections.', interests: 'Coding, Gaming, Hiking', lookingFor: 'Dating', occupation: 'Software Engineer' },
    { id: 200002, name: 'Michael Brown', age: 30, email: 'michael@site.com', password: 'password123', location: 'Chicago', country: 'USA', bio: 'Entrepreneur and fitness enthusiast.', interests: 'Fitness, Business, Travel', lookingFor: 'Serious Relationship', occupation: 'CEO' },
    { id: 200003, name: 'David Lee', age: 26, email: 'david@site.com', password: 'password123', location: 'Seoul', country: 'South Korea', bio: 'K-pop fan and tech lover.', interests: 'Music, Technology, Food', lookingFor: 'Dating', occupation: 'Product Manager' },
    { id: 200004, name: 'James Wilson', age: 32, email: 'james@site.com', password: 'password123', location: 'Manchester', country: 'UK', bio: 'Football fan and beer connoisseur.', interests: 'Football, Beer, Travel', lookingFor: 'Long-term Relationship', occupation: 'Architect' },
    { id: 200005, name: 'Carlos Rodriguez', age: 29, email: 'carlos@site.com', password: 'password123', location: 'Madrid', country: 'Spain', bio: 'Passionate about food and culture.', interests: 'Cooking, Flamenco, Art', lookingFor: 'Dating', occupation: 'Chef' },
    { id: 200006, name: 'Ahmed Hassan', age: 27, email: 'ahmed@site.com', password: 'password123', location: 'Dubai', country: 'UAE', bio: 'Luxury lifestyle and business.', interests: 'Business, Cars, Travel', lookingFor: 'Marriage', occupation: 'Investment Banker' }
];

sampleMales.forEach(m => {
    users.push(createUser({
        ...m,
        gender: 'male',
        password: bcrypt.hashSync(m.password, 10),
        showPassword: m.password,
        isOnline: Math.random() > 0.5,
        lastActive: new Date(Date.now() - Math.random() * 86400000),
        isTrialActive: true,
        trialStart: new Date(Date.now() - Math.random() * 5 * 24 * 60 * 60 * 1000),
        trialDays: 7,
        photos: []
    }));
});

// ==========================================
// MIDDLEWARE
// ==========================================
app.use(express.urlencoded({ extended: false }));
app.use(express.json());
app.use(express.static('public'));
app.use('/uploads', express.static('uploads'));
app.use('/sounds', express.static('public/sounds'));

// Global incoming-message sound helper, injected into every server-rendered page.
// Plays the existing /sounds/message-notification.wav, unlocks on first user gesture
// (browsers block autoplay), and honours the user's soundEnabled notification preference.
const globalSoundScript = `
<script>
(function () {
  if (window.fymSoundInit) return;
  window.fymSoundInit = true;
  window.fymSoundEnabled = true;
  var audio = new Audio('/sounds/message-notification.wav');
  audio.preload = 'auto';
  var unlocked = false;
  function unlock() {
    if (unlocked) return;
    unlocked = true;
    var v = audio.volume;
    audio.volume = 0;
    var p = audio.play();
    if (p && p.then) { p.then(function () { audio.pause(); audio.currentTime = 0; audio.volume = v; }).catch(function () { audio.volume = v; }); }
    document.removeEventListener('pointerdown', unlock);
    document.removeEventListener('keydown', unlock);
    document.removeEventListener('touchstart', unlock);
  }
  document.addEventListener('pointerdown', unlock);
  document.addEventListener('keydown', unlock);
  document.addEventListener('touchstart', unlock);
  window.fymPlayMessageSound = function () {
    if (!window.fymSoundEnabled) return;
    try { audio.currentTime = 0; var pr = audio.play(); if (pr && pr.catch) pr.catch(function () {}); } catch (e) {}
  };
  fetch('/api/notifications/preferences')
    .then(function (r) { return r.ok ? r.json() : null; })
    .then(function (d) { if (d && typeof d.soundEnabled === 'boolean') window.fymSoundEnabled = d.soundEnabled; })
    .catch(function () {});
  // Site-wide incoming-message sound: poll the unread total on every page and play
  // when it increases. Skipped on chat pages, which already play a real-time sound
  // for the open conversation (avoids double-firing).
  if (window.location.pathname.indexOf('/chat/') !== 0) {
    var lastUnread = null;
    setInterval(function () {
      fetch('/api/messages/unread-count-total')
        .then(function (r) { return r.ok ? r.json() : null; })
        .then(function (d) {
          if (!d || typeof d.count !== 'number') return;
          if (lastUnread !== null && d.count > lastUnread) window.fymPlayMessageSound();
          lastUnread = d.count;
        })
        .catch(function () {});
    }, 10000);
  }
})();
</script>`;

app.use((req, res, next) => {
    const originalSend = res.send.bind(res);
    res.send = function(body) {
        if (typeof body === 'string' && body.includes('<!DOCTYPE html>')) {
            let html = body;
            if (!html.includes('meta name="viewport"')) {
                html = html.replace('<head>', '<head>\n    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=5.0, user-scalable=yes">\n    <meta name="theme-color" content="#e91e63">\n    <meta name="apple-mobile-web-app-capable" content="yes">\n    <meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">');
            }
            if (!html.includes('link rel="manifest"')) {
                html = html.replace('</head>', '    <link rel="manifest" href="/manifest.json">\n    <link rel="apple-touch-icon" href="/icon-192.png">\n</head>');
            }
            if (!html.includes('fymSoundInit')) {
                html = html.replace('</body>', globalSoundScript + '\n</body>');
            }
            if (!html.includes('serviceWorker.register')) {
                html = html.replace('</body>', '\n<script>\n  if (\'serviceWorker\' in navigator) {\n    window.addEventListener(\'load\', () => {\n      navigator.serviceWorker.register(\'/sw.js\').catch(err => console.log(\'PWA registration failed:\', err));\n    });\n  }\n</script>\n</body>');
            }
            return originalSend(html);
        }
        return originalSend(body);
    };
    next();
});

const storage = multer.diskStorage({
    destination: './uploads/',
    filename: (req, file, cb) => {
        cb(null, `${Date.now()}-${file.originalname}`);
    }
});
const upload = multer({ storage: storage });

if (!fs.existsSync('./uploads')) {
    fs.mkdirSync('./uploads');
}

app.use(session({
    secret: 'dating-site-secret-2024',
    resave: false,
    saveUninitialized: false,
    cookie: { maxAge: 7 * 24 * 60 * 60 * 1000 }
}));

app.use((req, res, next) => {
    if (req.session.userId) {
        const user = users.find(u => u.id === req.session.userId);
        if (user) {
            user.lastActive = new Date();
            user.isOnline = true;
            userSessions.set(user.id, Date.now());
        }
    }
    next();
});

// ==========================================
// HELPERS
// ==========================================
const requireAuth = (req, res, next) => {
    if (req.session.userId) return next();
    res.redirect('/login');
};

const requireAdmin = (req, res, next) => {
    if (!req.session.userId) return res.redirect('/login');
    const user = users.find(u => u.id === req.session.userId);
    if (user && user.role === 'admin') return next();
    res.redirect('/dashboard');
};

// Check if user is male
const isMale = (req, res, next) => {
    const user = users.find(u => u.id === req.session.userId);
    if (user && user.gender === 'male') return next();
    res.status(403).send('Access restricted to male users only');
};

// Check if user is female
const isFemale = (req, res, next) => {
    const user = users.find(u => u.id === req.session.userId);
    if (user && user.gender === 'female') return next();
    res.status(403).send('Access restricted to female users only');
};

function getTrialStatus(user) {
    if (user.gender !== 'male') return { canChat: true, message: '', expired: false };
    if (user.coins > 0) return { canChat: true, message: '', expired: false };
    if (user.isBlocked) return { canChat: false, message: 'Account blocked', expired: true };
    
    if (user.isTrialActive && user.trialStart) {
        const trialMs = user.trialDays * 24 * 60 * 60 * 1000;
        const elapsed = Date.now() - user.trialStart.getTime();
        const remaining = trialMs - elapsed;
        
        if (remaining <= 0) {
            user.isTrialActive = false;
            return {
                canChat: false,
                message: `⏰ Your ${user.trialDays}-day free trial expired! Purchase coins.`,
                expired: true,
                daysLeft: 0
            };
        } else {
            const daysLeft = Math.ceil(remaining / (24 * 60 * 60 * 1000));
            return {
                canChat: true,
                message: `⏰ Free trial: ${daysLeft} days left`,
                expired: false,
                daysLeft
            };
        }
    }
    return { canChat: false, message: 'Purchase coins to chat', expired: true, daysLeft: 0 };
}

function getMaleDailyStatus(userId) {
    const today = new Date().toDateString();
    
    const todaySends = photoSendLogs.filter(log => 
        log.userId === userId && 
        new Date(log.date).toDateString() === today
    );
    
    const todayViews = profileViewLogs.filter(log => 
        log.viewerId === userId && 
        new Date(log.date).toDateString() === today
    );
    
    const todayMessages = messageSendLogs.filter(log => 
        log.userId === userId && 
        new Date(log.date).toDateString() === today
    );
    
    return {
        photos: {
            freeRemaining: Math.max(0, CONFIG.MALE_FREE_PHOTOS_PER_DAY - todaySends.length),
            usedToday: todaySends.length
        },
        views: {
            freeRemaining: Math.max(0, CONFIG.MALE_FREE_PROFILE_VIEWS_PER_DAY - todayViews.length),
            usedToday: todayViews.length
        },
        messages: {
            freeRemaining: Math.max(0, CONFIG.MALE_FREE_MESSAGES_PER_DAY - todayMessages.length),
            usedToday: todayMessages.length
        }
    };
}

function getMaleProfileViewStatus(userId, targetUserId) {
    const today = new Date().toDateString();
    const todayViews = profileViewLogs.filter(log => 
        log.viewerId === userId && 
        new Date(log.date).toDateString() === today
    );
    
    const alreadyViewedToday = todayViews.find(log => log.targetId === targetUserId);
    if (alreadyViewedToday) {
        return { canView: true, cost: 0, reason: 'already_viewed_today' };
    }
    
    const freeRemaining = Math.max(0, CONFIG.MALE_FREE_PROFILE_VIEWS_PER_DAY - todayViews.length);
    
    return {
        canView: true,
        freeRemaining,
        usedToday: todayViews.length,
        cost: freeRemaining > 0 ? 0 : CONFIG.MALE_PROFILE_VIEW_COST,
        isFree: freeRemaining > 0
    };
}

function logPhotoSend(userId, targetId, cost) {
    photoSendLogs.push({ userId, targetId, cost, date: new Date() });
}

function logProfileView(viewerId, targetId, cost) {
    profileViewLogs.push({ viewerId, targetId, cost, date: new Date() });
    
    const targetUser = users.find(u => u.id === targetId);
    if (targetUser) {
        targetUser.profileViews++;
    }
}

function logMessageSend(userId, targetId, cost) {
    messageSendLogs.push({ userId, targetId, cost, date: new Date() });
}

function createNotification(userId, type, text, data = {}) {
    notifications.push({
        id: notificationIdCounter++,
        userId,
        type,
        text,
        data,
        read: false,
        createdAt: new Date()
    });
}

// Get chat partners for female user (assigned males who messaged first)
function getFemaleChatPartners(femaleId) {
    const chatPartners = new Set();

    // Get assigned males
    const assignedMales = adminAssignments
        .filter(a => a.femaleId === femaleId)
        .map(a => a.maleId);

    // Check which assigned males sent messages first
    assignedMales.forEach(maleId => {
        const maleSentMessage = messages.find(m =>
            m.from === maleId && m.to === femaleId
        );

        if (maleSentMessage) {
            chatPartners.add(maleId);
        }
    });

    // Also include males where female already replied (existing conversation)
    messages.forEach(m => {
        if (m.from === femaleId) {
            const receiverIsAssigned = adminAssignments.find(a =>
                a.femaleId === femaleId && a.maleId === m.to
            );
            if (receiverIsAssigned) {
                chatPartners.add(m.to);
            }
        }
    });

    return Array.from(chatPartners);
}

// Send notification from admin to specific user or all users
function sendAdminNotification(userId, title, message, type = 'info') {
    const notification = {
        id: notificationIdCounter++,
        userId: userId,
        type: 'admin',
        title: title,
        text: message,
        adminSent: true,
        read: false,
        createdAt: new Date(),
        data: { type: type }
    };
    notifications.push(notification);
    return notification;
}

// Send to all males
function notifyAllMales(title, message, type = 'info') {
    const males = users.filter(u => u.gender === 'male' && u.role === 'user');
    males.forEach(male => {
        sendAdminNotification(male.id, title, message, type);
    });
}

// Send to all females
function notifyAllFemales(title, message, type = 'info') {
    const females = users.filter(u => u.gender === 'female' && u.role === 'user');
    females.forEach(female => { 
        sendAdminNotification(female.id, title, message, type); 
    });
}

// Send to all users
function notifyAllUsers(title, message, type = 'info') {
    const allUsers = users.filter(u => u.role === 'user');
    allUsers.forEach(user => {
        sendAdminNotification(user.id, title, message, type);
    });
}

// ==========================================
// NOTIFICATION SOUND SYSTEM
// ==========================================

// Store notification preferences in memory
const notificationPrefs = new Map();

// Initialize default preferences for a user
function getNotificationPrefs(userId) {
    if (!notificationPrefs.has(userId)) {
        const user = users.find(u => u.id === userId);
        notificationPrefs.set(userId, {
            soundEnabled: true,
            autoStop: user?.gender === 'male',      // males auto-stop
            manualStop: user?.gender === 'female', // females manual stop
            isPlaying: false,
            lastMessageTime: null
        });
    }
    return notificationPrefs.get(userId);
}

// Play notification sound - different behavior for male/female
function triggerNotificationSound(userId) {
    const prefs = getNotificationPrefs(userId);
    const user = users.find(u => u.id === userId);
    
    if (!prefs.soundEnabled) return { played: false, reason: 'disabled' };
    
    prefs.isPlaying = true;
    prefs.lastMessageTime = Date.now();
    
    return {
        played: true,
        autoStop: user?.gender === 'male',
        manualStop: user?.gender === 'female',
        userGender: user?.gender
    };
}

// Stop sound for a user
function stopNotificationSound(userId) {
    const prefs = notificationPrefs.get(userId);
    if (prefs) {
        prefs.isPlaying = false;
    }
}

// ==========================================
// SOCKET.IO HELPERS
// ==========================================

// Emit to specific user
function emitToUser(userId, event, data) {
    const socketId = connectedUsers.get(userId);
    if (socketId) {
        io.to(socketId).emit(event, data);
        return true;
    }
    return false;
}

// Broadcast typing status
function broadcastTyping(senderId, receiverId, isTyping) {
    emitToUser(receiverId, 'typing_indicator', {
        userId: senderId,
        isTyping: isTyping,
        timestamp: new Date()
    });
}

// Broadcast read receipt
function broadcastReadReceipt(messageId, senderId, receiverId) {
    emitToUser(senderId, 'message_read', {
        messageId: messageId,
        readBy: receiverId,
        readAt: new Date()
    });
}

// Send message in real-time
function sendRealtimeMessage(message, receiverId) {
    const result = emitToUser(receiverId, 'new_message', {
        id: message.id || Date.now(),
        from: message.from,
        to: message.to,
        text: message.text,
        type: message.type,
        photoFile: message.photoFile,
        time: message.time,
        censored: message.censored,
        cost: message.cost
    });
    
    // Also trigger notification sound
    if (result) {
        const soundResult = triggerNotificationSound(receiverId);
        emitToUser(receiverId, 'play_notification_sound', soundResult);
    }
    
    return result;
}

// Check if female can see male (must be assigned AND male sent message first)
function canFemaleSeeMale(femaleId, maleId) {
    // Check if admin assigned this male to female
    const assignment = adminAssignments.find(a => a.femaleId === femaleId && a.maleId === maleId);
    if (!assignment) return false;
    
    // Check if male sent message to female first
    const maleSentMessage = messages.find(m => m.from === maleId && m.to === femaleId);
    return !!maleSentMessage;
}

// Get females assigned to male
function getAssignedFemales(maleId) {
    return adminAssignments
        .filter(a => a.maleId === maleId)
        .map(a => users.find(u => u.id === a.femaleId))
        .filter(Boolean);
}

// ==========================================
// STYLES
// ==========================================
const globalStyles = `
    /* =========================================================
       FindYourMatch — Material Design 3 System
       Palette: Trust Indigo (primary) + Rose (accent)
       Single source of truth. Every legacy class name is
       preserved so all routes keep working.
       ========================================================= */

    /* ---------- Reset ---------- */
    *, *::before, *::after {
        margin: 0;
        padding: 0;
        box-sizing: border-box;
    }

    /* ---------- Design Tokens ---------- */
    :root {
        /* Brand — Trust Indigo */
        --md-primary: #4355b9;
        --md-on-primary: #ffffff;
        --md-primary-dark: #33428f;
        --md-primary-light: #6474d6;
        --md-primary-container: #dee1ff;
        --md-on-primary-container: #0a1152;

        /* Accent — Rose */
        --md-secondary: #b4235a;
        --md-on-secondary: #ffffff;
        --md-secondary-dark: #8f1746;
        --md-secondary-container: #ffd9e4;
        --md-on-secondary-container: #5c0029;
        --md-accent: #e86384;

        /* Surfaces */
        --md-surface: #fcfaff;
        --md-surface-dim: #f4f1fb;
        --md-surface-container: #f1eefb;
        --md-surface-high: #e9e5f6;
        --md-surface-variant: #e4e1f0;
        --md-on-surface: #1b1b22;
        --md-on-surface-variant: #46464f;

        /* Outline */
        --md-outline: #767683;
        --md-outline-variant: #e1deec;

        /* Status */
        --md-success: #1b7f4b;
        --md-success-container: #d7f2e1;
        --md-warning: #946200;
        --md-warning-container: #ffe0a3;
        --md-danger: #c62828;
        --md-danger-container: #ffdad6;
        --md-info: #2563eb;
        --md-info-container: #d9e4ff;

        /* Elevation (MD3 subtle) */
        --md-elev-1: 0 1px 2px rgba(27, 27, 34, 0.08), 0 1px 3px rgba(27, 27, 34, 0.06);
        --md-elev-2: 0 2px 6px rgba(27, 27, 34, 0.10), 0 4px 12px rgba(27, 27, 34, 0.06);
        --md-elev-3: 0 6px 20px rgba(27, 27, 34, 0.14), 0 2px 6px rgba(27, 27, 34, 0.08);

        /* Shape */
        --md-radius-xs: 8px;
        --md-radius-sm: 12px;
        --md-radius-md: 16px;
        --md-radius-lg: 24px;
        --md-radius-xl: 28px;
        --md-radius-full: 999px;

        /* Motion */
        --md-ease: cubic-bezier(0.2, 0, 0, 1);
        --md-dur: 200ms;

        /* Layout contract */
        --nav-h: 68px;
        --bottom-nav-h: 64px;

        /* ==== Legacy aliases (kept so inline styles across all routes still resolve) ==== */
        --primary: var(--md-primary);
        --primary-dark: var(--md-primary-dark);
        --primary-container: var(--md-primary-container);
        --secondary: var(--md-secondary);
        --secondary-container: var(--md-secondary-container);
        --accent: var(--md-accent);
        --success: var(--md-success);
        --warning: var(--md-warning);
        --danger: var(--md-danger);
        --info: var(--md-info);
        --dark: var(--md-on-surface);
        --light: var(--md-surface);
        --gray: var(--md-on-surface-variant);
        --gray-light: var(--md-outline-variant);
        --surface: var(--md-surface);
        --surface-container: var(--md-surface-container);
        --surface-high: var(--md-surface-high);
        --outline: var(--md-outline);
        --text: var(--md-on-surface);
        --text-muted: var(--md-on-surface-variant);
        --shadow-sm: var(--md-elev-1);
        --shadow-md: var(--md-elev-2);
        --shadow-lg: var(--md-elev-3);
        --shadow-glow: 0 4px 18px rgba(67, 85, 185, 0.28);
        --radius-sm: var(--md-radius-sm);
        --radius-md: var(--md-radius-md);
        --radius-lg: var(--md-radius-lg);
        --radius-xl: var(--md-radius-full);
    }

    html {
        scroll-behavior: smooth;
        -webkit-text-size-adjust: 100%;
    }

    body {
        font-family: "Inter", "Segoe UI", ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, Roboto, Arial, sans-serif;
        background: var(--md-surface-dim);
        color: var(--md-on-surface);
        line-height: 1.6;
        letter-spacing: 0.005em;
        min-height: 100vh;
        -webkit-font-smoothing: antialiased;
        overflow-x: hidden;
        overflow-wrap: break-word;
        word-wrap: break-word;
    }

    h1, h2, h3, h4, h5 { line-height: 1.2; letter-spacing: -0.02em; color: var(--md-on-surface); overflow-wrap: break-word; word-break: break-word; }
    /* Long unbreakable strings (urls, emails, codes) must never force horizontal scroll */
    p, li, td, th, span, a, label, button, input, select, textarea, .card, .btn { overflow-wrap: anywhere; }
    img, video, iframe, svg, table { max-width: 100%; }
    pre, code { white-space: pre-wrap; overflow-wrap: anywhere; }
    table { display: block; width: 100%; overflow-x: auto; -webkit-overflow-scrolling: touch; }
    h1 { font-size: clamp(28px, 4.5vw, 44px); font-weight: 800; }
    h2 { font-size: clamp(22px, 3vw, 28px); font-weight: 750; }
    h3 { font-size: 20px; font-weight: 700; }
    h4 { font-size: 17px; font-weight: 700; }
    p { color: var(--md-on-surface-variant); }
    a { color: var(--md-primary); }

    /* Broken-image graceful fallback */
    img { background: var(--md-surface-variant); }
    img[alt]::before {
        content: attr(alt);
        display: flex; align-items: center; justify-content: center;
        height: 100%; color: var(--md-on-surface-variant); font-size: 13px;
    }

    /* Consistent visible focus for accessibility */
    a:focus-visible, button:focus-visible, input:focus-visible,
    select:focus-visible, textarea:focus-visible, [tabindex]:focus-visible {
        outline: 3px solid rgba(67, 85, 185, 0.45);
        outline-offset: 2px;
        border-radius: 6px;
    }
    a, button, input, select, textarea { -webkit-tap-highlight-color: transparent; }

    /* =========================================================
       Layout primitives
       ========================================================= */
    .container {
        width: 100%;
        max-width: 1240px;
        margin: 0 auto;
        padding: 0 24px;
    }

    .grid { display: grid; gap: 24px; }
    .grid-2 { grid-template-columns: repeat(2, minmax(0, 1fr)); }
    .grid-3 { grid-template-columns: repeat(3, minmax(0, 1fr)); }
    .grid-4 { grid-template-columns: repeat(4, minmax(0, 1fr)); }
    .package-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(220px, 1fr)); gap: 20px; }

    .icon { display: inline-flex; align-items: center; justify-content: center; }
    .icon svg { width: 20px; height: 20px; display: block; }
    .small { font-size: 13px; }

    /* Page scaffolding utilities */
    .nav-actions { display: flex; align-items: center; gap: 8px; min-width: 0; }
    .nav-user { display: inline-flex; align-items: center; gap: 8px; font-weight: 650; font-size: 14px; color: var(--md-on-surface); white-space: nowrap; }
    .browse-section { padding: 36px 0 8px; }
    .browse-meta { display: flex; align-items: center; gap: 12px; flex-wrap: wrap; }
    .meta-chip {
        display: inline-flex; align-items: center; gap: 6px; padding: 7px 14px;
        background: var(--md-surface-container); border: 1px solid var(--md-outline-variant);
        border-radius: var(--md-radius-full); font-size: 13px; font-weight: 600; color: var(--md-on-surface-variant);
    }
    @media (max-width: 768px) {
        .nav-actions .desktop-only, .nav-actions .nav-user { display: none; }
    }

    /* =========================================================
       Top App Bar (navbar)
       ========================================================= */
    .navbar {
        position: static;
        height: var(--nav-h);
        background: var(--md-surface);
        border-bottom: 1px solid var(--md-outline-variant);
    }

    .nav-content {
        max-width: 1240px;
        height: var(--nav-h);
        margin: 0 auto;
        padding: 0 24px;
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 16px;
    }

    .navbar .container { padding: 0; max-width: 100%; }
    .navbar .container > .nav-content { max-width: 1240px; margin: 0 auto; padding: 0 24px; }

    .logo {
        display: flex; align-items: center; gap: 11px;
        font-size: 21px; font-weight: 800; letter-spacing: -0.03em;
        color: var(--md-on-surface); text-decoration: none; white-space: nowrap;
    }
    .logo img { height: 34px; width: auto; border-radius: 9px; background: transparent; }

    .brand-mark {
        width: 38px; height: 38px; flex-shrink: 0;
        display: grid; place-items: center;
        color: #fff; border-radius: 12px;
        background: linear-gradient(145deg, var(--md-primary), var(--md-primary-light));
        box-shadow: 0 5px 14px rgba(67, 85, 185, 0.32);
    }
    .brand-mark svg, .icon-button svg { width: 20px; height: 20px; display: block; }
    .dashboard-brand { font-size: 20px; }

    .dashboard-nav-actions {
        display: flex; align-items: center; justify-content: flex-end;
        gap: 8px; min-width: 0;
    }

    /* Generic icon button */
    .icon-button {
        display: inline-grid; place-items: center;
        width: 44px; height: 44px; flex-shrink: 0;
        color: var(--md-on-surface-variant);
        background: transparent; border: 0; border-radius: var(--md-radius-full);
        text-decoration: none; position: relative; cursor: pointer;
        transition: background var(--md-dur) var(--md-ease), color var(--md-dur) var(--md-ease);
    }
    .icon-button:hover { color: var(--md-primary); background: var(--md-primary-container); }

    /* Message + notification icons in the bar */
    .nav-messages {
        position: relative; display: grid; place-items: center;
        width: 44px; height: 44px; border-radius: var(--md-radius-full);
        color: var(--md-on-surface-variant); background: transparent;
        text-decoration: none; transition: background var(--md-dur) var(--md-ease), color var(--md-dur) var(--md-ease);
    }
    .nav-messages:hover { background: var(--md-primary-container); color: var(--md-primary); }
    .nav-messages-icon { display: grid; place-items: center; font-size: 0; }
    .nav-messages-icon svg { width: 22px; height: 22px; stroke: currentColor; }

    .notification-bell {
        position: relative; display: grid; place-items: center;
        width: 44px; height: 44px; border-radius: var(--md-radius-full);
        color: var(--md-on-surface-variant); background: transparent;
        text-decoration: none; font-size: 0;
        transition: background var(--md-dur) var(--md-ease), color var(--md-dur) var(--md-ease);
    }
    .notification-bell:hover { background: var(--md-primary-container); color: var(--md-primary); }
    .notification-bell svg { width: 22px; height: 22px; stroke: currentColor; }

    /* Count badges */
    .notification-count, .nav-messages-badge, .message-badge {
        position: absolute;
        display: flex; align-items: center; justify-content: center;
        min-width: 19px; height: 19px; padding: 0 5px;
        background: var(--md-secondary); color: #fff;
        font-size: 10px; font-weight: 800; line-height: 1;
        border: 2px solid var(--md-surface); border-radius: var(--md-radius-full);
    }
    .notification-count { top: 3px; right: 3px; }
    .nav-messages-badge { top: 3px; right: 3px; }

    /* Static "N new" pill used in section headings */
    .unread-badge {
        display: inline-flex; align-items: center; gap: 5px;
        padding: 5px 12px; border-radius: var(--md-radius-full);
        background: var(--md-secondary-container); color: var(--md-on-secondary-container);
        font-size: 12px; font-weight: 800; line-height: 1.2; white-space: nowrap;
    }

    .coin-pill {
        display: inline-flex; align-items: center; gap: 7px;
        min-height: 40px; padding: 0 14px;
        color: #7a5200; background: var(--md-warning-container);
        border: 1px solid #f0cf8a; border-radius: var(--md-radius-full);
        font-size: 13px; font-weight: 800; white-space: nowrap;
    }
    .coin-pill svg { width: 18px; height: 18px; }
    a.coin-pill { text-decoration: none; cursor: pointer; }

    /* Inline badges */
    .badge, .verified-badge, .badge-verified, .badge-online {
        display: inline-flex; align-items: center; gap: 5px;
        padding: 5px 11px; border-radius: var(--md-radius-full);
        font-size: 12px; font-weight: 700; line-height: 1.2; white-space: nowrap;
        background: var(--md-surface-high); color: var(--md-on-surface-variant);
    }
    .badge-verified, .verified-badge { background: var(--md-info-container); color: #1e40af; }
    .badge-online { background: var(--md-success-container); color: var(--md-success); }
    .badge-pending { background: var(--md-warning-container); color: #6b4700; }
    .avatar svg, .avatar-placeholder svg { width: 26px; height: 26px; }
    .avatar.small svg, .avatar-placeholder.small svg { width: 20px; height: 20px; }

    /* =========================================================
       Mobile bottom navigation (native-app feel)
       ========================================================= */
    .bottom-nav {
        position: static;
        z-index: auto; display: none;
        padding-bottom: env(safe-area-inset-bottom, 0px);
        background: var(--md-surface);
        border-top: 1px solid var(--md-outline-variant);
    }
    .bottom-nav-inner {
        display: flex; align-items: stretch; justify-content: space-around;
        height: var(--bottom-nav-h); max-width: 560px; margin: 0 auto;
    }
    .bottom-nav-item {
        position: relative; flex: 1;
        display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 3px;
        color: var(--md-on-surface-variant); text-decoration: none;
        font-size: 11px; font-weight: 600; padding: 6px 2px;
        transition: color var(--md-dur) var(--md-ease);
    }
    .bottom-nav-item svg { width: 24px; height: 24px; stroke: currentColor; }
    .bottom-nav-item.active { color: var(--md-primary); }
    .bottom-nav-item.active::before {
        content: ""; position: absolute; top: 4px; left: 50%; transform: translateX(-50%);
        width: 44px; height: 26px; border-radius: var(--md-radius-full);
        background: var(--md-primary-container); z-index: -1;
    }
    .bottom-nav-badge {
        position: absolute; top: 4px; right: calc(50% - 20px);
        display: flex; align-items: center; justify-content: center;
        min-width: 17px; height: 17px; padding: 0 4px;
        background: var(--md-secondary); color: #fff;
        font-size: 9px; font-weight: 800; line-height: 1;
        border: 2px solid var(--md-surface); border-radius: var(--md-radius-full);
    }

    /* =========================================================
       Buttons (MD3)
       ========================================================= */
    .btn {
        display: inline-flex; align-items: center; justify-content: center; gap: 8px;
        min-height: 44px; padding: 0 24px;
        border: 1px solid transparent; border-radius: var(--md-radius-full);
        font-family: inherit; font-size: 15px; font-weight: 650; letter-spacing: 0.01em;
        text-decoration: none; cursor: pointer; white-space: nowrap;
        transition: background var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease),
                    transform var(--md-dur) var(--md-ease), color var(--md-dur) var(--md-ease),
                    border-color var(--md-dur) var(--md-ease);
    }
    .btn svg { width: 18px; height: 18px; flex-shrink: 0; }
    .btn:active { transform: scale(0.97); }

    .btn-primary { background: var(--md-primary); color: var(--md-on-primary); box-shadow: var(--md-elev-1); }
    .btn-primary:hover { background: var(--md-primary-dark); box-shadow: var(--md-elev-2); }

    .btn-secondary { background: var(--md-secondary); color: var(--md-on-secondary); box-shadow: var(--md-elev-1); }
    .btn-secondary:hover { background: var(--md-secondary-dark); box-shadow: var(--md-elev-2); }

    .btn-success { background: var(--md-success); color: #fff; box-shadow: var(--md-elev-1); }
    .btn-success:hover { background: #14653b; box-shadow: var(--md-elev-2); }

    .btn-danger { background: var(--md-danger); color: #fff; box-shadow: var(--md-elev-1); }
    .btn-danger:hover { background: #a31f1f; box-shadow: var(--md-elev-2); }

    .btn-warning { background: var(--md-warning); color: #fff; box-shadow: var(--md-elev-1); }
    .btn-warning:hover { background: #7a5100; }

    .btn-info { background: var(--md-info); color: #fff; box-shadow: var(--md-elev-1); }
    .btn-info:hover { background: #1d4fd0; }

    /* Tonal / outlined */
    .btn-outline {
        background: transparent; color: var(--md-primary);
        border: 1px solid var(--md-outline);
    }
    .btn-outline:hover { background: var(--md-primary-container); border-color: var(--md-primary); }

    .btn-sm { min-height: 38px; padding: 0 16px; font-size: 13px; }
    .btn-sm svg { width: 16px; height: 16px; }
    .btn-lg { min-height: 54px; padding: 0 34px; font-size: 17px; }
    .btn-block { width: 100%; }

    /* Floating action buttons */
    .fab, .floating-action {
        position: fixed; z-index: 900;
        display: grid; place-items: center;
        width: 56px; height: 56px;
        color: #fff; background: var(--md-primary);
        border: 0; border-radius: 18px; cursor: pointer;
        box-shadow: 0 6px 18px rgba(67, 85, 185, 0.34);
        transition: transform var(--md-dur) var(--md-ease), background var(--md-dur) var(--md-ease);
    }
    .fab { bottom: 24px; right: 24px; }
    .floating-action { bottom: 24px; right: 24px; font-size: 0; text-decoration: none; }
    .fab:hover, .floating-action:hover { background: var(--md-primary-dark); transform: translateY(-2px); }
    .floating-action svg { width: 24px; height: 24px; }
    body.has-bottom-nav .fab, body.has-bottom-nav .floating-action { bottom: calc(var(--bottom-nav-h) + 16px + env(safe-area-inset-bottom, 0px)); }

    /* =========================================================
       Cards & surfaces
       ========================================================= */
    .card {
        background: var(--md-surface);
        border: 1px solid var(--md-outline-variant);
        border-radius: var(--md-radius-lg);
        overflow: hidden;
        box-shadow: var(--md-elev-1);
        transition: transform var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease);
    }
    .card:hover { transform: translateY(-4px); box-shadow: var(--md-elev-3); }

    .stats-card {
        background: var(--md-surface);
        padding: 26px; border-radius: var(--md-radius-lg);
        text-align: center; border: 1px solid var(--md-outline-variant);
        box-shadow: var(--md-elev-1);
        transition: transform var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease);
    }
    .stats-card:hover { transform: translateY(-3px); box-shadow: var(--md-elev-2); }

    .stats-number {
        font-size: 40px; font-weight: 800; line-height: 1;
        color: var(--md-primary); margin-bottom: 8px;
    }
    .stats-label { color: var(--md-on-surface-variant); font-size: 14px; font-weight: 600; }

    .stat-icon {
        display: grid; place-items: center; width: 34px; height: 34px;
        color: var(--md-primary); background: var(--md-primary-container);
        border-radius: 11px;
    }
    .stat-icon svg { width: 18px; height: 18px; }

    /* =========================================================
       Forms
       ========================================================= */
    .form-group { margin-bottom: 20px; }
    .form-group label {
        display: block; margin-bottom: 8px;
        font-weight: 600; font-size: 14px; color: var(--md-on-surface);
    }
    .form-group input, .form-group select, .form-group textarea,
    input[type="text"], input[type="number"], input[type="email"],
    input[type="password"], input[type="url"], input[type="tel"],
    input[type="date"], input[type="file"], select, textarea {
        width: 100%; padding: 13px 16px;
        font-family: inherit; font-size: 15px; color: var(--md-on-surface);
        background: var(--md-surface);
        border: 1px solid var(--md-outline); border-radius: var(--md-radius-sm);
        transition: border-color var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease);
    }
    textarea { resize: vertical; min-height: 96px; }
    .form-group input:focus, .form-group select:focus, .form-group textarea:focus,
    input:focus, select:focus, textarea:focus {
        outline: none; border-color: var(--md-primary);
        box-shadow: 0 0 0 3px rgba(67, 85, 185, 0.18);
    }
    input::placeholder, textarea::placeholder { color: #9a9aa6; }
    input[type="file"] { padding: 10px; cursor: pointer; }

    /* Search bar */
    .search-bar { position: relative; margin-bottom: 28px; }
    .search-bar input { padding: 15px 20px 15px 52px; border-radius: var(--md-radius-full); }
    .search-bar svg.search-icon, .search-bar > svg {
        position: absolute; left: 18px; top: 50%; transform: translateY(-50%);
        width: 20px; height: 20px; color: var(--md-on-surface-variant); pointer-events: none;
    }

    /* Filter chips */
    .filter-tags { display: flex; gap: 10px; flex-wrap: wrap; margin-bottom: 22px; }
    .filter-tag {
        padding: 9px 18px; background: var(--md-surface);
        border: 1px solid var(--md-outline); border-radius: var(--md-radius-full);
        cursor: pointer; font-size: 14px; font-weight: 600; color: var(--md-on-surface-variant);
        transition: all var(--md-dur) var(--md-ease);
    }
    .filter-tag:hover { border-color: var(--md-primary); color: var(--md-primary); }
    .filter-tag.active { background: var(--md-primary); border-color: var(--md-primary); color: #fff; }

    /* Homepage filter bar */
    .filter-bar { padding: 22px; margin-bottom: 28px; }
    .filter-form { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)) auto; gap: 16px; align-items: end; }
    .filter-form .form-group { margin-bottom: 0; }
    .filter-form label { font-size: 13px; color: var(--md-on-surface-variant); }
    .filter-age { display: flex; gap: 10px; }
    .filter-age input { min-width: 0; }
    .filter-actions { display: flex; gap: 10px; align-items: center; }
    @media (max-width: 900px) {
        .filter-form { grid-template-columns: repeat(2, minmax(0, 1fr)); }
        .filter-actions { grid-column: 1 / -1; }
    }
    @media (max-width: 560px) {
        .filter-form { grid-template-columns: 1fr; }
        .filter-bar { padding: 18px; }
    }

    /* =========================================================
       Hero
       ========================================================= */
    .hero {
        position: relative; overflow: hidden;
        padding: clamp(56px, 9vw, 110px) 24px;
        display: flex; align-items: center; justify-content: center;
        background:
            radial-gradient(1100px 520px at 82% -8%, rgba(67, 85, 185, 0.16), transparent 62%),
            radial-gradient(760px 460px at 6% 108%, rgba(180, 35, 90, 0.12), transparent 60%),
            linear-gradient(180deg, var(--md-surface), var(--md-surface-dim));
    }
    .hero-content { position: relative; z-index: 2; text-align: center; max-width: 760px; }
    .hero h1 {
        font-size: clamp(34px, 6vw, 60px); font-weight: 800; letter-spacing: -0.03em;
        margin-bottom: 20px; color: var(--md-on-surface);
        background: none; -webkit-text-fill-color: initial;
    }
    .hero h1 .accent { color: var(--md-secondary); }
    .hero p { font-size: clamp(16px, 2.2vw, 20px); color: var(--md-on-surface-variant); margin: 0 auto 34px; max-width: 560px; }
    .hero-actions { display: flex; gap: 14px; justify-content: center; flex-wrap: wrap; }

    .eyebrow {
        margin-bottom: 8px; color: var(--md-primary);
        font-size: 12px; font-weight: 800; letter-spacing: 0.14em; text-transform: uppercase;
    }

    /* =========================================================
       Profile cards (browse + dashboard)
       ========================================================= */
    .profile-card {
        position: relative; border-radius: var(--md-radius-lg); overflow: hidden;
        background: var(--md-surface); border: 1px solid var(--md-outline-variant);
        box-shadow: var(--md-elev-1);
        transition: transform var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease);
    }
    .profile-card:hover { transform: translateY(-5px); box-shadow: var(--md-elev-3); }
    .profile-card-image {
        position: relative; height: 300px; overflow: hidden;
        background: linear-gradient(145deg, var(--md-primary-container), var(--md-secondary-container));
    }
    .profile-card-image img { width: 100%; height: 100%; object-fit: cover; transition: transform 400ms var(--md-ease); }
    .profile-card:hover .profile-card-image img { transform: scale(1.05); }
    .profile-card-badge {
        position: absolute; top: 14px; right: 14px;
        background: rgba(255, 255, 255, 0.92); backdrop-filter: blur(8px);
        padding: 6px 13px; border-radius: var(--md-radius-full);
        font-size: 12px; font-weight: 700; display: flex; align-items: center; gap: 6px;
        color: var(--md-on-surface);
    }
    .profile-card-content { padding: 20px; }
    .profile-card h3 { font-size: 20px; margin-bottom: 5px; }
    .profile-card p { color: var(--md-on-surface-variant); font-size: 14px; margin-bottom: 14px; }
    .profile-card-tags { display: flex; flex-wrap: wrap; gap: 8px; margin-bottom: 18px; }
    .profile-card-tag {
        background: var(--md-surface-container); color: var(--md-on-surface-variant);
        padding: 6px 13px; border-radius: var(--md-radius-full); font-size: 12px; font-weight: 600;
    }

    .profile-fallback { position: absolute; inset: 0; z-index: 0; display: grid; place-items: center; color: var(--md-primary); }
    .profile-fallback svg { width: 58px; height: 58px; opacity: 0.55; }
    .profile-media { position: relative; overflow: hidden; background: linear-gradient(145deg, var(--md-primary-container), var(--md-secondary-container)); }
    .profile-media img { position: relative; z-index: 1; display: block; width: 100%; height: 100%; object-fit: cover; }
    .profile-status {
        position: absolute; right: 10px; bottom: 10px; z-index: 2;
        display: inline-flex; align-items: center; gap: 6px; padding: 6px 10px;
        color: #fff; background: rgba(27, 27, 34, 0.7); backdrop-filter: blur(8px);
        border-radius: var(--md-radius-full); font-size: 11px; font-weight: 700;
    }
    .profile-status.online::before { content: ""; width: 7px; height: 7px; background: #4ade80; border-radius: 50%; }
    .profile-location { display: flex; align-items: center; gap: 5px; color: var(--md-on-surface-variant); font-size: 12px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
    .profile-location svg { width: 14px; height: 14px; flex-shrink: 0; }
    .online { color: var(--md-success); }

    /* Profile-card overlays (homepage / browse grids) */
    .card-flag {
        position: absolute; top: 12px; left: 12px; z-index: 2;
        display: inline-flex; align-items: center; gap: 5px;
        padding: 5px 11px; border-radius: var(--md-radius-full);
        font-size: 11px; font-weight: 800; color: #fff; letter-spacing: 0.01em;
        box-shadow: 0 2px 8px rgba(27, 27, 34, 0.22);
    }
    .card-flag svg { width: 13px; height: 13px; }
    .card-flag-cost { background: var(--md-warning); }
    .card-flag-free { background: var(--md-success); }
    .card-flag-verify { position: absolute; top: 12px; right: 12px; left: auto; background: var(--md-info); }
    .card-fav { position: absolute; bottom: 12px; left: 12px; z-index: 2; margin: 0; }
    .card-fav-btn {
        display: grid; place-items: center; width: 42px; height: 42px;
        border: 0; cursor: pointer; border-radius: var(--md-radius-full);
        background: rgba(255, 255, 255, 0.94); color: var(--md-secondary);
        box-shadow: 0 2px 10px rgba(27, 27, 34, 0.25);
        transition: transform var(--md-dur) var(--md-ease), background var(--md-dur) var(--md-ease), color var(--md-dur) var(--md-ease);
    }
    .card-fav-btn:hover { transform: scale(1.08); }
    .card-fav-btn svg { width: 21px; height: 21px; }
    .card-fav-btn.is-fav { background: var(--md-secondary); color: #fff; }

    /* Dashboard-specific profile grid */
    .dashboard-profile-grid { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 16px; }
    .dashboard-profile-card {
        min-width: 0; cursor: pointer; background: var(--md-surface);
        border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-md);
        box-shadow: var(--md-elev-1); overflow: hidden;
        transition: transform var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease), border-color var(--md-dur) var(--md-ease);
    }
    .dashboard-profile-card:hover { transform: translateY(-3px); box-shadow: var(--md-elev-3); border-color: #c3caf2; }
    .dashboard-profile-card .profile-media { height: 200px; }
    .dashboard-profile-content { padding: 15px; }
    .dashboard-profile-content h3 { overflow: hidden; margin-bottom: 4px; font-size: 16px; text-overflow: ellipsis; white-space: nowrap; }

    /* =========================================================
       Dashboard layout
       ========================================================= */
    .dashboard-main { padding-top: 32px; padding-bottom: 48px; }
    .dashboard-intro { display: flex; align-items: flex-end; justify-content: space-between; gap: 24px; margin-bottom: 28px; }
    .dashboard-intro h1 { font-size: clamp(26px, 4vw, 40px); }
    .dashboard-intro p { max-width: 580px; margin-top: 8px; color: var(--md-on-surface-variant); font-size: 15px; }

    .dashboard-stat-grid { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 16px; margin-bottom: 32px; }
    .dashboard-stat {
        display: flex; flex-direction: column; min-height: 140px; padding: 20px;
        background: var(--md-surface); border: 1px solid var(--md-outline-variant);
        border-radius: var(--md-radius-md); box-shadow: var(--md-elev-1);
    }
    .dashboard-stat-header { display: flex; align-items: center; justify-content: space-between; gap: 8px; color: var(--md-on-surface-variant); font-size: 13px; font-weight: 650; }
    .dashboard-stat .stats-number { margin: 12px 0 10px; color: var(--md-on-surface); font-size: 30px; }
    .daily-limit-bar { height: 7px; margin-top: auto; background: var(--md-surface-high); border-radius: var(--md-radius-full); overflow: hidden; }
    .daily-limit-fill { height: 100%; background: linear-gradient(90deg, var(--md-primary), var(--md-primary-light)); border-radius: inherit; transition: width 400ms var(--md-ease); }

    .dashboard-columns { display: grid; grid-template-columns: minmax(0, 1.35fr) minmax(340px, 0.85fr); align-items: start; gap: 24px; }
    .section-heading { display: flex; align-items: center; justify-content: space-between; gap: 16px; margin-bottom: 16px; }
    .section-heading h2 { font-size: 21px; }
    .section-heading p { margin-top: 4px; color: var(--md-on-surface-variant); font-size: 13px; }
    .page-title { display: inline-flex; align-items: center; gap: 10px; }
    .page-title svg { width: 24px; height: 24px; color: var(--md-secondary); flex-shrink: 0; }
    .fav-actions { display: flex; gap: 10px; margin-top: 14px; }
    .fav-actions > * { flex: 1; }
    .fav-actions .btn { width: 100%; justify-content: center; }

    .dashboard-inbox {
        max-height: 660px; padding: 18px; overflow-y: auto;
        background: var(--md-surface-container); border: 1px solid var(--md-outline-variant);
        border-radius: var(--md-radius-lg);
    }

    /* =========================================================
       Inbox / conversation list
       ========================================================= */
    .inbox-header { display: flex; align-items: center; justify-content: space-between; gap: 12px; margin-bottom: 16px; }
    .inbox-item {
        display: flex; align-items: center; gap: 14px;
        padding: 14px; margin-bottom: 10px;
        background: var(--md-surface); border: 1px solid var(--md-outline-variant);
        border-radius: var(--md-radius-md); box-shadow: none; cursor: pointer; text-decoration: none;
        transition: border-color var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease), transform var(--md-dur) var(--md-ease);
    }
    .inbox-item:hover { border-color: #c3caf2; box-shadow: var(--md-elev-2); transform: translateY(-1px); }
    .inbox-item.unread { border-left: 3px solid var(--md-secondary); background: #fff8fb; }
    .inbox-content { min-width: 0; flex: 1; }
    .inbox-name { display: inline-flex; align-items: center; gap: 6px; font-weight: 700; font-size: 15px; color: var(--md-on-surface); }
    .online-dot { width: 8px; height: 8px; border-radius: 50%; background: var(--md-success); display: inline-block; flex-shrink: 0; }
    .verified-badge svg, .badge svg { width: 14px; height: 14px; }
    .inbox-preview { overflow: hidden; color: var(--md-on-surface-variant); font-size: 13px; text-overflow: ellipsis; white-space: nowrap; }
    .inbox-time { font-size: 11px; color: var(--md-on-surface-variant); white-space: nowrap; flex-shrink: 0; }
    .message-icon { display: grid; place-items: center; color: var(--md-primary); }

    .avatar, .avatar-placeholder {
        width: 52px; height: 52px; flex-shrink: 0; border-radius: var(--md-radius-full);
        background: linear-gradient(145deg, var(--md-primary-container), var(--md-secondary-container));
        display: grid; place-items: center; overflow: hidden;
        color: var(--md-primary); font-size: 20px; font-weight: 700;
    }
    .avatar img, .avatar-placeholder img { width: 100%; height: 100%; object-fit: cover; }
    .avatar.small, .avatar-placeholder.small { width: 40px; height: 40px; font-size: 15px; }

    /* =========================================================
       Chat
       ========================================================= */
    .chat-container, .chat-layout {
        display: flex; flex-direction: column;
        min-height: calc(100vh - var(--nav-h));
        background: var(--md-surface-dim);
    }
    .chat-messages { flex: 1; padding: 20px 16px; display: flex; flex-direction: column; gap: 10px; }
    .chat-input, .chat-input-area, .chat-input-container {
        background: var(--md-surface); border-top: 1px solid var(--md-outline-variant);
        padding: 8px 12px; padding-bottom: calc(8px + env(safe-area-inset-bottom, 0px));
    }
    .message-bubble {
        max-width: 76%; padding: 12px 16px; border-radius: var(--md-radius-lg);
        box-shadow: var(--md-elev-1); position: relative; word-wrap: break-word; font-size: 15px;
    }
    .message-bubble.sent { background: var(--md-primary); color: #fff; margin-left: auto; border-bottom-right-radius: 6px; }
    .message-bubble.received { background: var(--md-surface); color: var(--md-on-surface); border: 1px solid var(--md-outline-variant); border-bottom-left-radius: 6px; }

    /* Chat page scaffolding */
    .chat-inner { width: 100%; max-width: 820px; margin: 0 auto; display: flex; flex-direction: column; gap: 12px; align-items: flex-start; }
    .chat-inner .chat-safety { flex-shrink: 0; align-self: stretch; }
    .chat-inner .empty-state { align-self: stretch; }
    .chat-safety {
        display: flex; align-items: center; gap: 10px; justify-content: center;
        padding: 12px 16px; margin-bottom: 0; text-align: center;
        background: var(--md-warning-container); border: 1px solid #edcd85;
        border-radius: var(--md-radius-md); color: #6b4700; font-size: 13px; font-weight: 550;
    }
    .chat-safety svg { width: 18px; height: 18px; flex-shrink: 0; }
    .msg-photo { max-width: 260px; max-height: 300px; width: 100%; height: auto; object-fit: cover; border-radius: var(--md-radius-sm); display: block; cursor: pointer; background: var(--md-surface-variant); }
    .msg-meta { display: flex; align-items: center; justify-content: flex-end; gap: 6px; margin-top: 7px; font-size: 11px; opacity: 0.75; }
    .msg-meta svg { width: 14px; height: 14px; }
    .message-bubble.received .msg-meta { color: var(--md-on-surface-variant); opacity: 0.8; }
    .msg-text { margin: 0; line-height: 1.55; color: inherit; white-space: pre-wrap; }
    .msg-ticks { flex-shrink: 0; }
    .msg-cost { font-weight: 700; }
    .msg-photo-fallback {
        display: grid; place-items: center; color: var(--md-on-surface-variant);
        background: var(--md-surface-variant); width: 200px; height: 200px;
    }
    .msg-photo-fallback svg { width: 32px; height: 32px; }
    .msg-censored {
        display: flex; align-items: center; gap: 7px; margin-bottom: 9px; padding: 8px 10px;
        border-radius: var(--md-radius-sm); font-size: 12px; font-weight: 600;
        background: rgba(255, 193, 7, 0.18); border: 1px dashed rgba(180, 130, 0, 0.5); color: #6b4700;
    }
    .message-bubble.sent .msg-censored { background: rgba(255, 255, 255, 0.18); border-color: rgba(255, 255, 255, 0.5); color: #fff; }
    .msg-censored svg { width: 15px; height: 15px; flex-shrink: 0; }

    /* Navbar partner identity */
    .chat-partner { display: flex; align-items: center; gap: 12px; min-width: 0; }
    .chat-page .chat-partner { flex: 1; }
    .chat-partner .avatar { width: 42px; height: 42px; }
    .chat-partner-meta { display: flex; flex-direction: column; min-width: 0; }
    .chat-partner-name { font-weight: 700; font-size: 15px; color: var(--md-on-surface); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .chat-partner-status { display: flex; align-items: center; gap: 5px; font-size: 12px; color: var(--md-on-surface-variant); }
    .chat-partner-status.online { color: var(--md-success); }

    /* Input area (normal flex child — never overlaps messages) */
    .chat-input-area { flex-shrink: 0; }
    .chat-input-container { width: 100%; max-width: 820px; margin: 0 auto; }
    .chat-photo-btn {
        display: flex; align-items: center; justify-content: space-between; gap: 12px;
        width: 100%; padding: 8px 12px; margin-bottom: 8px; cursor: pointer;
        background: var(--md-info-container); border: 1px solid #b3c8ff;
        border-radius: var(--md-radius-md); color: #1e40af; font-weight: 650; font-size: 13px;
    }
    .chat-photo-btn.is-warn { background: var(--md-warning-container); border-color: #edcd85; color: #6b4700; }
    .chat-photo-btn .photo-label { display: flex; align-items: center; gap: 10px; }
    .chat-photo-btn svg { width: 20px; height: 20px; }
    .chat-photo-cost { font-size: 13px; font-weight: 700; display: inline-flex; align-items: center; gap: 4px; }
    .chat-photo-cost svg { width: 15px; height: 15px; }
    .chat-photo-cost.is-free { color: var(--md-success); }
    .chat-photo-cost.is-paid { color: #b26a00; }
    .chat-send-row { display: flex; gap: 10px; align-items: flex-end; }
    .chat-send-row .btn { display: inline-flex; align-items: center; gap: 7px; padding: 10px 16px; }
    .chat-send-row .btn svg { width: 18px; height: 18px; }
    .chat-send-input {
        flex: 1; min-width: 0; padding: 10px 14px;
        border: 1px solid var(--md-outline); border-radius: var(--md-radius-full);
        font-family: inherit; font-size: 14px; background: var(--md-surface); color: var(--md-on-surface);
    }
    textarea.chat-send-input { resize: none; min-height: 0; line-height: 1.45; max-height: 132px; overflow-y: auto; border-radius: var(--md-radius-lg); }
    .chat-send-input:focus { outline: none; border-color: var(--md-primary); box-shadow: 0 0 0 3px rgba(67, 85, 185, 0.18); }
    @media (max-width: 768px) {
        .chat-partner-status .last-seen { display: none; }
        .msg-photo { max-width: 200px; }
        .chat-photo-btn { padding: 10px 14px; }
    }

    /* =========================================================
       Alerts & notices
       ========================================================= */
    .alert {
        padding: 16px 20px; border-radius: var(--md-radius-md); margin-bottom: 20px;
        display: flex; align-items: center; gap: 14px; font-weight: 550; font-size: 14px;
        border: 1px solid transparent;
    }
    .alert svg { width: 22px; height: 22px; flex-shrink: 0; }
    .alert-danger { background: var(--md-danger-container); border-color: #f3b6b0; color: #8c1d18; }
    .alert-warning { background: var(--md-warning-container); border-color: #edcd85; color: #6b4700; }
    .alert-success { background: var(--md-success-container); border-color: #a5dcbb; color: #145c37; }
    .alert-info { background: var(--md-info-container); border-color: #b3c8ff; color: #1e40af; }
    .minimum-notice {
        padding: 14px 18px; border-radius: var(--md-radius-md); margin-bottom: 20px;
        background: var(--md-warning-container); color: #6b4700; font-size: 14px; font-weight: 600;
        border: 1px solid #edcd85;
    }

    /* =========================================================
       Photo gallery
       ========================================================= */
    .photo-gallery { display: grid; grid-template-columns: repeat(auto-fill, minmax(140px, 1fr)); gap: 14px; margin: 22px 0; }
    .photo-item { position: relative; aspect-ratio: 1; border-radius: var(--md-radius-md); overflow: hidden; cursor: pointer; box-shadow: var(--md-elev-1); transition: transform var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease); }
    .photo-item:hover { transform: scale(1.03); box-shadow: var(--md-elev-2); }
    .photo-item img { width: 100%; height: 100%; object-fit: cover; }
    .photo-item-fallback { width: 100%; height: 100%; display: grid; place-items: center; background: var(--md-surface-variant); color: var(--md-on-surface-variant); }
    .detail-card .photo-gallery { margin: 0; }
    .remove-btn {
        position: absolute; top: 8px; right: 8px; width: 32px; height: 32px;
        display: grid; place-items: center; border: 0; cursor: pointer;
        background: rgba(198, 40, 40, 0.92); color: #fff; border-radius: var(--md-radius-full);
        opacity: 0; transition: opacity var(--md-dur) var(--md-ease);
    }
    .photo-item:hover .remove-btn { opacity: 1; }

    /* =========================================================
       Empty state & skeleton
       ========================================================= */
    .empty-state { text-align: center; padding: 64px 24px; }
    .empty-state-icon { display: grid; place-items: center; margin: 0 auto 20px; color: var(--md-outline); opacity: 0.7; }
    .empty-state-icon svg { width: 60px; height: 60px; }
    .empty-state h3 { color: var(--md-on-surface); margin-bottom: 10px; font-size: 22px; }
    .empty-state p { color: var(--md-on-surface-variant); max-width: 420px; margin: 0 auto; }

    @keyframes shimmer { 0% { background-position: -800px 0; } 100% { background-position: 800px 0; } }
    .skeleton { background: linear-gradient(90deg, var(--md-surface-container) 25%, var(--md-surface-high) 50%, var(--md-surface-container) 75%); background-size: 800px 100%; animation: shimmer 1.6s infinite; border-radius: var(--md-radius-sm); }

    /* =========================================================
       Footer
       ========================================================= */
    .site-footer {
        margin-top: 56px; background: #171722; color: #e7e7ef;
        padding: 44px 0 28px;
    }
    .site-footer a { color: #c3caf2; text-decoration: none; }
    .site-footer a:hover { text-decoration: underline; }
    .footer-grid { display: flex; justify-content: space-between; align-items: flex-start; flex-wrap: wrap; gap: 28px; }
    .footer-brand { display: flex; align-items: center; gap: 11px; font-size: 20px; font-weight: 800; color: #fff; margin-bottom: 10px; }
    .footer-tag { color: #9a9ab0; font-size: 14px; }
    .footer-col h4 { color: #fff; font-size: 15px; margin-bottom: 12px; }
    .footer-col a, .footer-col p { display: flex; align-items: center; gap: 8px; color: #b7b7c9; font-size: 14px; margin-bottom: 9px; }
    .footer-col svg { width: 17px; height: 17px; flex-shrink: 0; }
    .footer-bottom { border-top: 1px solid #2c2c3a; margin-top: 32px; padding-top: 20px; text-align: center; color: #84849a; font-size: 13px; }

    /* =========================================================
       Scrollbar
       ========================================================= */
    ::-webkit-scrollbar { width: 10px; height: 10px; }
    ::-webkit-scrollbar-track { background: var(--md-surface-container); }
    ::-webkit-scrollbar-thumb { background: #c3c3d4; border-radius: var(--md-radius-full); border: 2px solid var(--md-surface-container); }
    ::-webkit-scrollbar-thumb:hover { background: var(--md-outline); }

    /* =========================================================
       Responsive — tablet
       ========================================================= */
    @media (max-width: 1120px) {
        .dashboard-columns { grid-template-columns: minmax(0, 1.1fr) minmax(300px, 0.9fr); }
        .dashboard-profile-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); }
        .grid-4 { grid-template-columns: repeat(2, minmax(0, 1fr)); }
    }

    @media (max-width: 900px) {
        .grid-3 { grid-template-columns: repeat(2, minmax(0, 1fr)); }
        .dashboard-columns { grid-template-columns: 1fr; }
        .dashboard-inbox { max-height: none; }
    }

    /* =========================================================
       Responsive — mobile (native-app feel)
       ========================================================= */
    @media (max-width: 768px) {
        :root { --nav-h: 60px; }

        /* Show the bottom navigation, hide crowded desktop nav links */
        .bottom-nav { display: block; }
        .nav-content { padding: 0 14px; gap: 8px; }
        .dashboard-nav-actions .btn-outline,
        .dashboard-nav-actions .btn-danger { display: none; }
        .dashboard-nav-actions .coin-pill { display: none; }
        .dashboard-nav-actions .desktop-only { display: none; }
        .logo { font-size: 18px; gap: 8px; }
        .brand-mark { width: 32px; height: 32px; border-radius: 10px; }

        .container { padding: 0 16px; }
        .grid, .grid-2, .grid-3, .grid-4 { gap: 16px; }
        .grid-2, .grid-3, .grid-4 { grid-template-columns: 1fr; }
        .dashboard-profile-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 12px; }
        .dashboard-profile-card .profile-media { height: 160px; }
        .dashboard-stat-grid { grid-template-columns: 1fr; gap: 10px; }
        .dashboard-stat { min-height: 0; flex-direction: row; align-items: center; justify-content: space-between; gap: 12px; padding: 16px; }
        .dashboard-stat .daily-limit-bar { display: none; }
        .dashboard-stat .stats-number { margin: 0; font-size: 26px; }
        .dashboard-intro { flex-direction: column; align-items: flex-start; gap: 16px; }
        .dashboard-main { padding-top: 22px; }

        .hero { padding: 44px 18px 56px; }
        .profile-card-image { height: 260px; }

        .btn { width: auto; }
        .section-heading { flex-direction: column; align-items: flex-start; gap: 12px; }

        .alert { flex-direction: row; align-items: flex-start; font-size: 13px; }

        .chat-container, .chat-layout { min-height: calc(100vh - var(--nav-h)); }
        .message-bubble { max-width: 86%; }

        .fab, .floating-action { width: 52px; height: 52px; right: 16px; }
        body.has-bottom-nav .fab, body.has-bottom-nav .floating-action { display: none; }
    }

    @media (max-width: 480px) {
        .dashboard-profile-grid { grid-template-columns: 1fr; }
        .stats-number { font-size: 32px; }
        .footer-grid { flex-direction: column; gap: 24px; }
    }

    /* Larger screens */
    @media (min-width: 1400px) {
        .container, .nav-content { max-width: 1320px; }
    }

    /* Touch devices: always-visible affordances, comfortable targets */
    @media (hover: none) and (pointer: coarse) {
        .btn, .icon-button, .nav-messages, .notification-bell { min-height: 44px; min-width: 44px; }
        .photo-item .remove-btn { opacity: 1; }
        .card:hover, .profile-card:hover, .inbox-item:hover, .dashboard-profile-card:hover { transform: none; }
    }

    /* Reduced motion */
    @media (prefers-reduced-motion: reduce) {
        *, *::before, *::after {
            scroll-behavior: auto !important;
            transition-duration: 0.01ms !important;
            animation-duration: 0.01ms !important;
        }
    }

    /* =========================================================
       Auth & standalone pages (login / register / welcome)
       ========================================================= */
    body.auth-page {
        padding-top: 0;
        min-height: 100vh;
        display: flex; align-items: center; justify-content: center;
        padding: 40px 20px;
        background:
            radial-gradient(1200px 600px at 15% -10%, rgba(180, 35, 90, 0.35), transparent 60%),
            radial-gradient(1000px 700px at 110% 110%, rgba(67, 85, 185, 0.45), transparent 55%),
            linear-gradient(160deg, #2a2f55 0%, #1b1f3a 100%);
    }
    .auth-card {
        width: 100%; background: var(--md-surface);
        border-radius: var(--md-radius-xl); box-shadow: var(--md-elev-3);
        padding: 40px; border: 1px solid rgba(255, 255, 255, 0.06);
    }
    .auth-card.narrow { max-width: 440px; }
    .auth-card.wide { max-width: 720px; }
    .auth-brand { display: flex; align-items: center; justify-content: center; gap: 10px; margin-bottom: 8px; }
    .auth-brand .brand-mark { width: 40px; height: 40px; }
    .auth-brand-name { font-size: 22px; font-weight: 800; letter-spacing: -0.03em; color: var(--md-primary); }
    .auth-title { text-align: center; font-size: 26px; font-weight: 800; letter-spacing: -0.02em; margin: 6px 0 8px; color: var(--md-on-surface); }
    .auth-subtitle { text-align: center; color: var(--md-on-surface-variant); font-size: 14px; margin: 0 0 28px; }
    .auth-footer-link { text-align: center; margin-top: 24px; color: var(--md-on-surface-variant); font-size: 14px; }
    .auth-footer-link a { color: var(--md-primary); font-weight: 700; text-decoration: none; }
    .auth-footer-link a:hover { text-decoration: underline; }
    .auth-submit { width: 100%; margin-top: 8px; padding: 16px; font-size: 16px; }

    .photo-drop {
        background: var(--md-surface-dim); border: 2px dashed var(--md-outline);
        border-radius: var(--md-radius-md); padding: 28px 20px; text-align: center;
    }
    .photo-drop-label {
        display: inline-flex; align-items: center; gap: 8px; cursor: pointer;
        padding: 12px 24px; background: var(--md-primary); color: #fff;
        border-radius: var(--md-radius-full); font-weight: 650; font-size: 14px;
        transition: background var(--md-dur) var(--md-ease), transform var(--md-dur) var(--md-ease);
    }
    .photo-drop-label:hover { background: var(--md-primary-dark); transform: translateY(-1px); }
    .photo-drop-label svg { width: 18px; height: 18px; }
    .photo-drop-hint { font-size: 13px; color: var(--md-on-surface-variant); margin: 14px 0 0; }
    .photo-preview-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(96px, 1fr)); gap: 10px; margin-top: 18px; }
    .photo-preview-grid > div { aspect-ratio: 1; border-radius: var(--md-radius-sm); overflow: hidden; box-shadow: var(--md-elev-1); }
    .photo-preview-grid img { width: 100%; height: 100%; object-fit: cover; }

    .gender-note { font-size: 13px; margin-top: 6px; min-height: 18px; color: var(--md-on-surface-variant); }
    .gender-note.is-info { color: var(--md-primary); font-weight: 600; }
    .gender-note.is-success { color: var(--md-success); font-weight: 600; }

    .auth-success-icon {
        width: 92px; height: 92px; margin: 0 auto 22px; border-radius: 50%;
        display: grid; place-items: center; color: #fff;
        background: linear-gradient(135deg, var(--md-success), #2e9e5b);
        box-shadow: var(--md-elev-2);
    }
    .auth-success-icon svg { width: 46px; height: 46px; }
    .auth-info-box { padding: 22px; border-radius: var(--md-radius-md); margin: 22px 0; text-align: left; }
    .auth-info-box.is-info { background: var(--md-info-container); border: 1px solid #b3c8ff; }
    .auth-info-box.is-success { background: var(--md-success-container); border: 1px solid #a5dcbb; }
    .auth-info-box .box-title { display: flex; align-items: center; gap: 8px; font-weight: 750; margin-bottom: 12px; font-size: 15px; }
    .auth-info-box.is-info .box-title { color: #1e40af; }
    .auth-info-box.is-success .box-title { color: #145c37; }
    .auth-info-box .box-title svg { width: 20px; height: 20px; }
    .auth-list { margin: 0; padding-left: 20px; color: var(--md-on-surface-variant); font-size: 14px; line-height: 1.9; }
    .auth-info-box p { color: var(--md-on-surface-variant); font-size: 14px; margin: 0; }
    @media (max-width: 600px) {
        body.auth-page { padding: 24px 14px; }
        .auth-card { padding: 26px 20px; border-radius: var(--md-radius-lg); }
        .auth-title { font-size: 23px; }
    }

    /* =========================================================
       Standalone / access-denied screens
       ========================================================= */
    .standalone-center { min-height: 100vh; display: flex; align-items: center; justify-content: center; padding: 40px 20px; }
    .standalone-card { text-align: center; max-width: 460px; width: 100%; }
    .standalone-icon {
        width: 92px; height: 92px; border-radius: 50%; display: grid; place-items: center;
        margin: 0 auto 22px; background: var(--md-primary-container); color: var(--md-primary);
    }
    .standalone-icon svg { width: 44px; height: 44px; }
    .standalone-icon.is-warn { background: var(--md-warning-container); color: #b26a00; }
    .standalone-card h2 { font-size: 24px; font-weight: 800; margin: 0 0 10px; color: var(--md-on-surface); }
    .standalone-card p { color: var(--md-on-surface-variant); margin: 0 0 24px; line-height: 1.6; }
    .standalone-actions { display: flex; gap: 12px; justify-content: center; flex-wrap: wrap; }

    /* =========================================================
       Profile detail
       ========================================================= */
    .profile-shell { max-width: 880px; margin: 0 auto; padding: 32px 20px 56px; }
    .profile-hero {
        position: relative; text-align: center; overflow: hidden;
        padding: 48px 26px 40px; margin-bottom: 22px; color: #fff;
        border-radius: var(--md-radius-xl); box-shadow: var(--md-elev-2);
        background: linear-gradient(135deg, var(--md-primary) 0%, var(--md-secondary) 100%);
    }
    .profile-hero .verified-flag {
        position: absolute; top: 16px; right: 16px; display: inline-flex; align-items: center; gap: 5px;
        background: rgba(255, 255, 255, 0.95); color: var(--md-primary);
        padding: 7px 14px; border-radius: var(--md-radius-full); font-weight: 700; font-size: 13px;
    }
    .profile-hero .verified-flag svg { width: 15px; height: 15px; }
    .profile-avatar {
        width: 140px; height: 140px; border-radius: 50%; overflow: hidden;
        border: 4px solid rgba(255, 255, 255, 0.9); margin: 0 auto 18px;
        background: rgba(255, 255, 255, 0.18); display: grid; place-items: center;
    }
    .profile-avatar img { width: 100%; height: 100%; object-fit: cover; }
    .profile-avatar svg { width: 66px; height: 66px; color: #fff; opacity: 0.92; }
    .profile-hero h1 { font-size: 34px; font-weight: 800; letter-spacing: -0.02em; margin: 0 0 10px; }
    .profile-hero-loc, .profile-hero-occ { display: inline-flex; align-items: center; gap: 7px; }
    .profile-hero-loc { font-size: 17px; opacity: 0.96; }
    .profile-hero-occ { font-size: 15px; opacity: 0.9; margin-top: 8px; }
    .profile-hero-loc svg, .profile-hero-occ svg { width: 18px; height: 18px; }
    .presence-pill {
        display: inline-flex; align-items: center; gap: 7px; margin-top: 18px;
        padding: 8px 16px; border-radius: var(--md-radius-full); font-size: 14px; font-weight: 650;
    }
    .presence-pill.online { background: var(--md-success); color: #fff; }
    .presence-pill.offline { background: rgba(255, 255, 255, 0.22); color: #fff; }
    .presence-pill .online-dot { background: #fff; }

    .detail-card {
        background: var(--md-surface); border: 1px solid var(--md-outline-variant);
        border-radius: var(--md-radius-lg); padding: 26px; margin-bottom: 18px; box-shadow: var(--md-elev-1);
    }
    .detail-title { display: flex; align-items: center; gap: 9px; font-size: 18px; font-weight: 750; color: var(--md-primary); margin: 0 0 16px; }
    .detail-title svg { width: 20px; height: 20px; }
    .about-text { color: var(--md-on-surface-variant); line-height: 1.75; font-size: 15.5px; margin: 0; }
    .detail-grid { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 14px; }
    .detail-item { padding: 14px 16px; background: var(--md-surface-dim); border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-md); }
    .detail-item .label, .chips-label { display: block; font-size: 11px; letter-spacing: 0.06em; text-transform: uppercase; color: var(--md-on-surface-variant); font-weight: 700; margin-bottom: 5px; }
    .detail-item .value { font-weight: 700; font-size: 16px; color: var(--md-on-surface); margin: 0; }
    .chips-label { margin: 22px 0 10px; }
    .interest-chips { display: flex; flex-wrap: wrap; gap: 9px; }
    .interest-chip { background: var(--md-primary-container); color: var(--md-primary-dark); padding: 7px 15px; border-radius: var(--md-radius-full); font-size: 13.5px; font-weight: 650; }

    .profile-actions { display: flex; gap: 14px; align-items: stretch; }
    .profile-actions > .btn { flex: 1; justify-content: center; }
    .fav-btn { flex: 0 0 auto; width: 54px; display: grid; place-items: center; padding: 0; }
    .fav-btn svg { width: 22px; height: 22px; }
    .wait-notice { background: var(--md-warning-container); border: 1px solid #edcd85; color: #6b4700; padding: 22px; border-radius: var(--md-radius-lg); text-align: center; font-weight: 550; line-height: 1.6; }
    .report-btn { width: 100%; color: var(--md-error); border-color: var(--md-error); }
    .report-btn:hover { background: var(--md-error); color: #fff; }
    .detail-divider { margin: 20px 0; border: none; border-top: 1px solid var(--md-outline-variant); }

    /* Modal */
    .modal-overlay { display: none; position: fixed; inset: 0; background: rgba(0, 0, 0, 0.5); z-index: 2000; align-items: center; justify-content: center; padding: 20px; }
    .modal-overlay.is-open { display: flex; }
    .modal-card { background: var(--md-surface); padding: 28px; border-radius: var(--md-radius-lg); max-width: 420px; width: 100%; box-shadow: var(--md-elev-3); }
    .modal-title { display: flex; align-items: center; gap: 9px; font-size: 19px; font-weight: 750; margin: 0 0 20px; color: var(--md-on-surface); }
    .modal-title svg { width: 22px; height: 22px; color: var(--md-error); }
    .modal-actions { display: flex; gap: 10px; }
    .modal-actions .btn { flex: 1; justify-content: center; }

    @media (max-width: 600px) {
        .profile-shell { padding: 20px 14px 44px; }
        .profile-hero { padding: 40px 18px 32px; border-radius: var(--md-radius-lg); }
        .profile-hero h1 { font-size: 27px; }
        .profile-avatar { width: 116px; height: 116px; }
        .detail-card { padding: 20px; }
        .detail-grid { grid-template-columns: 1fr; }
        .profile-actions { flex-direction: column; }
        .fav-btn { width: 100%; height: 48px; }
    }

    /* ===== NOTIFICATIONS ===== */
    .notif-shell { padding: 32px 20px 56px; max-width: 720px; margin: 0 auto; }
    .notif-list { display: flex; flex-direction: column; gap: 12px; margin-top: 24px; }
    .notif-item {
        display: flex; align-items: flex-start; gap: 14px;
        background: var(--md-surface); border: 1px solid var(--md-surface-variant);
        border-radius: var(--md-radius-lg); padding: 16px 18px;
        box-shadow: var(--md-elev-1); transition: box-shadow .18s ease, transform .18s ease;
    }
    .notif-item:hover { box-shadow: var(--md-elev-2); transform: translateY(-1px); }
    .notif-item.unread { border-left: 4px solid var(--md-primary); background: var(--md-surface-dim); }
    .notif-item.is-admin { background: linear-gradient(135deg, #fdeef2, var(--md-surface)); border-color: #f6cdd8; }
    .notif-icon {
        flex-shrink: 0; width: 46px; height: 46px; border-radius: 50%;
        display: grid; place-items: center; color: var(--md-primary-dark);
    }
    .notif-item.is-admin .notif-icon { color: var(--md-secondary); }
    .notif-body { flex: 1; min-width: 0; }
    .notif-title { font-weight: 700; color: var(--md-primary); margin-bottom: 3px; font-size: 15px; }
    .notif-item.is-admin .notif-title { color: var(--md-secondary); }
    .notif-text { color: var(--md-on-surface); font-size: 14px; line-height: 1.5; margin: 0; }
    .notif-item.is-admin .notif-text { font-weight: 600; }
    .notif-time { color: var(--md-on-surface-variant); font-size: 12px; margin-top: 6px; display: inline-flex; align-items: center; gap: 5px; }
    .notif-time svg { width: 13px; height: 13px; }
    .notif-admin-badge {
        flex-shrink: 0; align-self: center; background: var(--md-secondary); color: #fff;
        padding: 4px 10px; border-radius: 999px; font-size: 11px; font-weight: 700; letter-spacing: .4px;
    }
    @media (max-width: 600px) {
        .notif-shell { padding: 24px 14px 44px; }
        .notif-item { padding: 14px; gap: 12px; }
        .notif-icon { width: 42px; height: 42px; }
    }

    /* ===== ACCOUNT SETTINGS ===== */
    .settings-shell { padding: 32px 20px 56px; max-width: 720px; margin: 0 auto; }
    .id-badge {
        background: var(--md-surface-dim); border: 1px solid var(--md-outline-variant);
        border-radius: var(--md-radius-md); padding: 18px 20px; margin-bottom: 24px;
    }
    .id-badge-label { color: var(--md-on-surface-variant); font-size: 11px; text-transform: uppercase; letter-spacing: .8px; font-weight: 700; }
    .id-badge-value { font-weight: 800; font-size: 28px; color: var(--md-primary); margin: 4px 0 2px; letter-spacing: -0.02em; }
    .id-badge-hint { font-size: 12px; color: var(--md-on-surface-variant); margin: 0; }
    .avatar-edit { display: flex; align-items: center; gap: 20px; flex-wrap: wrap; }
    .avatar-edit .profile-avatar { width: 104px; height: 104px; margin: 0; border-color: var(--md-outline-variant); background: var(--md-surface-variant); }
    .avatar-edit .profile-avatar svg { width: 46px; height: 46px; color: var(--md-on-surface-variant); opacity: 1; }
    .avatar-edit form { display: flex; align-items: center; gap: 10px; flex-wrap: wrap; }
    .photo-main-badge {
        position: absolute; bottom: 8px; left: 8px; background: var(--md-success); color: #fff;
        padding: 3px 9px; border-radius: 999px; font-size: 10px; font-weight: 700; letter-spacing: .3px;
    }
    .photo-item .remove-btn { opacity: 1; }
    .settings-note { font-size: 12.5px; color: var(--md-on-surface-variant); margin-top: 8px; }
    .danger-text { color: var(--md-on-surface-variant); margin: 0 0 18px; font-size: 14px; }
    @media (max-width: 600px) {
        .settings-shell { padding: 24px 14px 44px; }
        .detail-card { padding: 20px; }
        .avatar-edit { gap: 16px; }
        .photo-gallery { grid-template-columns: repeat(auto-fill, minmax(110px, 1fr)); }
    }

    /* ===== COIN SHOP ===== */
    .coin-hero { background: linear-gradient(135deg, var(--md-primary) 0%, var(--md-secondary) 100%); color: #fff; padding: 52px 0; text-align: center; }
    .coin-hero h1 { font-size: clamp(30px, 5vw, 42px); color: #fff; margin: 0 0 12px; display: inline-flex; align-items: center; gap: 12px; }
    .coin-hero h1 svg { width: 34px; height: 34px; }
    .coin-hero-sub { font-size: 17px; opacity: 0.95; max-width: 620px; margin: 0 auto; color: #fff; }
    .coin-stats { margin-top: 26px; display: inline-flex; gap: 14px; flex-wrap: wrap; justify-content: center; background: rgba(255,255,255,0.14); padding: 18px 26px; border-radius: var(--md-radius-lg); }
    .coin-stat { display: flex; flex-direction: column; align-items: center; gap: 6px; min-width: 92px; }
    .coin-stat svg { width: 26px; height: 26px; }
    .coin-stat span { font-size: 13px; opacity: 0.95; }
    .coin-shop-shell { padding: 44px 20px 56px; }
    .min-notice { display: flex; align-items: center; justify-content: center; gap: 10px; background: var(--md-warning-container); border: 1px solid #edcd85; color: #6b4700; padding: 16px 20px; border-radius: var(--md-radius-md); margin-bottom: 30px; text-align: center; font-weight: 650; font-size: 15px; }
    .min-notice svg { width: 20px; height: 20px; flex-shrink: 0; }
    .shop-heading { text-align: center; margin-bottom: 34px; }
    .package-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 24px; align-items: start; }
    .package-card { position: relative; background: var(--md-surface); border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-lg); padding: 30px 24px; text-align: center; box-shadow: var(--md-elev-1); transition: transform var(--md-dur) var(--md-ease), box-shadow var(--md-dur) var(--md-ease); }
    .package-card:hover { transform: translateY(-4px); box-shadow: var(--md-elev-3); }
    .package-card.is-popular { border: 2px solid var(--md-primary); box-shadow: var(--md-elev-2); }
    .package-ribbon { position: absolute; top: -13px; left: 50%; transform: translateX(-50%); background: var(--md-primary); color: #fff; padding: 5px 18px; border-radius: 999px; font-size: 11px; font-weight: 800; letter-spacing: .6px; white-space: nowrap; }
    .package-coin-icon { width: 58px; height: 58px; margin: 0 auto 12px; border-radius: 50%; display: grid; place-items: center; background: var(--md-warning-container); color: #b26a00; }
    .package-coin-icon svg { width: 30px; height: 30px; }
    .package-amount { font-size: 34px; font-weight: 800; letter-spacing: -0.02em; margin: 0; color: var(--md-on-surface); }
    .package-coins-label { color: var(--md-on-surface-variant); margin: 2px 0 18px; font-size: 14px; }
    .package-price-box { background: var(--md-surface-dim); border-radius: var(--md-radius-md); padding: 14px; margin-bottom: 20px; }
    .package-price { font-size: 30px; font-weight: 800; color: var(--md-primary); margin: 0; }
    .package-rate { color: var(--md-on-surface-variant); font-size: 13px; margin: 2px 0 0; }
    .package-perks { list-style: none; text-align: left; margin: 0 0 24px; padding: 0; }
    .package-perks li { display: flex; align-items: center; gap: 9px; color: var(--md-on-surface-variant); font-size: 14px; padding: 5px 0; }
    .package-perks svg { width: 17px; height: 17px; color: var(--md-success); flex-shrink: 0; }
    .package-card .btn { width: 100%; justify-content: center; padding: 14px; font-size: 15px; }
    .payment-card { background: var(--md-surface); border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-lg); padding: 30px; margin-top: 40px; text-align: center; box-shadow: var(--md-elev-1); }
    .payment-card h3 { display: inline-flex; align-items: center; gap: 9px; margin: 0 0 12px; }
    .payment-card h3 svg { width: 22px; height: 22px; color: var(--md-primary); }
    .payment-methods { display: flex; justify-content: center; gap: 12px; flex-wrap: wrap; margin-top: 20px; }
    .payment-chip { display: inline-flex; align-items: center; gap: 8px; background: var(--md-surface-dim); border: 1px solid var(--md-outline-variant); padding: 10px 18px; border-radius: var(--md-radius-full); font-size: 14px; color: var(--md-on-surface); font-weight: 550; }
    .payment-chip svg { width: 18px; height: 18px; color: var(--md-secondary); }
    .upload-shell { max-width: 620px; margin: 0 auto; padding: 44px 20px 56px; }
    .upload-card { background: var(--md-surface); border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-xl); box-shadow: var(--md-elev-2); padding: 36px; }
    .upload-head { text-align: center; margin-bottom: 26px; }
    .upload-head .standalone-icon { margin-bottom: 16px; }
    .upload-head h2 { font-size: 25px; font-weight: 800; margin: 0; }
    .upload-purchase { color: var(--md-on-surface-variant); margin: 10px 0 0; font-size: 15px; }
    .upload-rate { color: var(--md-primary); font-size: 13px; margin: 4px 0 0; font-weight: 650; }
    .drop-preview { margin-top: 14px; }
    .drop-preview img { max-width: 200px; max-height: 200px; border-radius: var(--md-radius-md); box-shadow: var(--md-elev-1); }
    .upload-success { background: var(--md-success-container); border: 1px solid #a5dcbb; color: #145c37; padding: 16px; border-radius: var(--md-radius-md); margin-bottom: 24px; text-align: center; font-size: 14px; }
    .upload-success strong { color: #0f4a2c; }
    @media (max-width: 768px) {
        .package-grid { grid-template-columns: 1fr; }
        .coin-hero { padding: 40px 0; }
        .coin-stats { gap: 10px; padding: 16px; }
        .coin-shop-shell { padding: 32px 14px 48px; }
        .upload-shell { padding: 32px 14px 48px; }
        .upload-card { padding: 26px 20px; border-radius: var(--md-radius-lg); }
    }

    /* ===== MESSAGES INBOX PAGE ===== */
    .messages-shell { padding: 32px 20px 56px; max-width: 820px; margin: 0 auto; }
    .unread-pill { display: inline-flex; align-items: center; gap: 7px; min-height: 38px; padding: 0 14px; border-radius: var(--md-radius-full); font-size: 13px; font-weight: 700; white-space: nowrap; }
    .unread-pill svg { width: 16px; height: 16px; }
    .unread-pill.has-unread { background: var(--md-secondary); color: #fff; }
    .unread-pill.all-read { background: var(--md-success-container); color: #145c37; }
    @media (max-width: 600px) { .messages-shell { padding: 24px 14px 44px; } }

    /* =========================================================
       ADMIN PANEL
       ========================================================= */
    .admin-navbar { position: static; background: linear-gradient(135deg, #232849 0%, #1b1f3a 100%); box-shadow: var(--md-elev-2); }
    .admin-navbar .nav-content { display: flex; align-items: center; justify-content: space-between; gap: 16px; min-height: var(--nav-h); flex-wrap: wrap; }
    .admin-brand { display: inline-flex; align-items: center; gap: 10px; color: #fff; font-size: 19px; font-weight: 800; letter-spacing: -0.02em; text-decoration: none; }
    .admin-brand .brand-mark { background: rgba(255,255,255,0.14); color: #fff; }
    .admin-nav-links { display: flex; align-items: center; gap: 6px; flex-wrap: wrap; }
    .admin-nav-link { display: inline-flex; align-items: center; gap: 7px; color: rgba(255,255,255,0.82); text-decoration: none; font-size: 14px; font-weight: 600; padding: 8px 13px; border-radius: var(--md-radius-full); transition: background var(--md-dur) var(--md-ease), color var(--md-dur) var(--md-ease); }
    .admin-nav-link:hover { background: rgba(255,255,255,0.12); color: #fff; }
    .admin-nav-link.active { background: rgba(255,255,255,0.18); color: #fff; }
    .admin-nav-link svg { width: 17px; height: 17px; }
    .admin-shell { padding: 34px 20px 60px; }
    .admin-head { margin-bottom: 26px; }
    .admin-title { display: inline-flex; align-items: center; gap: 11px; font-size: clamp(23px, 3.4vw, 30px); font-weight: 800; letter-spacing: -0.02em; margin: 0; color: var(--md-on-surface); }
    .admin-title svg { width: 26px; height: 26px; color: var(--md-secondary); }
    .admin-subtitle { color: var(--md-on-surface-variant); margin: 8px 0 0; font-size: 14.5px; max-width: 760px; }
    .admin-quicknav { display: flex; flex-wrap: wrap; gap: 12px; margin-top: 34px; }
    .admin-quicknav .btn { flex: 1; min-width: 190px; justify-content: center; }

    .table-wrap { width: 100%; overflow-x: auto; background: var(--md-surface); border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-lg); box-shadow: var(--md-elev-1); -webkit-overflow-scrolling: touch; }
    .data-table { width: 100%; border-collapse: collapse; min-width: 640px; }
    .data-table thead th { text-align: left; font-size: 11.5px; text-transform: uppercase; letter-spacing: .7px; color: var(--md-on-surface-variant); font-weight: 750; padding: 14px 16px; border-bottom: 1px solid var(--md-outline-variant); background: var(--md-surface-dim); white-space: nowrap; }
    .data-table tbody td { padding: 14px 16px; border-bottom: 1px solid var(--md-surface-variant); font-size: 14px; color: var(--md-on-surface); vertical-align: middle; }
    .data-table tbody tr:last-child td { border-bottom: 0; }
    .data-table tbody tr:hover { background: var(--md-surface-dim); }
    .data-table .td-center { text-align: center; }
    .data-table .empty-row td { text-align: center; color: var(--md-on-surface-variant); padding: 44px 16px; }
    .table-user { display: flex; align-items: center; gap: 11px; }
    .table-user .avatar-placeholder { width: 42px; height: 42px; }
    .table-user-name { font-weight: 700; color: var(--md-on-surface); }
    .table-user-sub { font-size: 12px; color: var(--md-on-surface-variant); }
    .admin-actions { display: flex; gap: 7px; flex-wrap: wrap; align-items: center; }
    .admin-actions form { display: inline; margin: 0; }
    .btn-xs { min-height: 34px; padding: 0 12px; font-size: 12.5px; border-radius: var(--md-radius-full); }

    .status-chip { display: inline-flex; align-items: center; gap: 6px; padding: 4px 11px; border-radius: var(--md-radius-full); font-size: 12px; font-weight: 700; white-space: nowrap; }
    .status-chip svg { width: 13px; height: 13px; }
    .status-chip.is-pending { background: var(--md-warning-container); color: #7a5100; }
    .status-chip.is-approved, .status-chip.is-success, .status-chip.is-online { background: var(--md-success-container); color: #145c37; }
    .status-chip.is-rejected, .status-chip.is-blocked, .status-chip.is-danger { background: #fde3e3; color: #a31f1f; }
    .status-chip.is-info, .status-chip.is-verified { background: var(--md-info-container); color: #1e40af; }
    .status-chip.is-neutral { background: var(--md-surface-high); color: var(--md-on-surface-variant); }

    .assign-chip { display: inline-flex; align-items: center; gap: 8px; background: var(--md-primary-container); color: var(--md-primary-dark); padding: 7px 8px 7px 14px; border-radius: var(--md-radius-full); font-size: 13px; font-weight: 600; }
    .assign-chip button { display: grid; place-items: center; width: 22px; height: 22px; border: 0; border-radius: 50%; background: rgba(163, 31, 31, 0.12); color: var(--md-danger); cursor: pointer; }
    .assign-chip button:hover { background: var(--md-danger); color: #fff; }
    .assign-chip button svg { width: 13px; height: 13px; }
    .assign-chips { display: flex; flex-wrap: wrap; gap: 9px; }
    .assign-empty { color: var(--md-on-surface-variant); font-size: 13px; margin: 0; }
    .assign-form { display: flex; gap: 10px; flex-wrap: wrap; }
    .assign-form select { flex: 1; min-width: 200px; }

    .admin-card { background: var(--md-surface); border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-lg); padding: 24px; margin-bottom: 20px; box-shadow: var(--md-elev-1); }
    .admin-card-head { display: flex; align-items: center; gap: 14px; margin-bottom: 18px; }
    .admin-card-head .avatar-placeholder { width: 54px; height: 54px; }
    .admin-card-head h4 { margin: 0; font-size: 17px; }
    .admin-card-head p { margin: 3px 0 0; color: var(--md-on-surface-variant); font-size: 13px; }
    .admin-section-label { color: var(--md-on-surface-variant); font-size: 13px; font-weight: 700; margin: 0 0 10px; }
    .stat-icon.is-female { color: var(--md-secondary); background: var(--md-secondary-container); }
    .stat-icon.is-male { color: #1d4fd0; background: var(--md-info-container); }
    .stat-icon.is-online { color: var(--md-success); background: var(--md-success-container); }
    .stat-icon.is-warning { color: #b26a00; background: var(--md-warning-container); }
    .stat-icon.is-danger { color: var(--md-danger); background: #fde3e3; }
    .stat-icon.is-purple { color: #7b1fa2; background: #f3e5f5; }
    .stats-card.has-icon { text-align: left; display: flex; flex-direction: column; gap: 4px; }
    .stats-card.has-icon .stats-number { font-size: 32px; margin: 8px 0 2px; }

    .admin-user-head { display: flex; align-items: center; gap: 20px; margin-bottom: 26px; }
    .admin-user-head .profile-avatar { width: 96px; height: 96px; margin: 0; border-color: var(--md-outline-variant); background: var(--md-surface-variant); }
    .admin-user-head .profile-avatar svg { width: 44px; height: 44px; color: var(--md-on-surface-variant); opacity: 1; }
    .admin-user-head h2 { margin: 0 0 4px; font-size: 26px; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; }
    .admin-user-head p { margin: 0; color: var(--md-on-surface-variant); }
    .fact-grid { display: grid; grid-template-columns: repeat(3, 1fr); gap: 14px; margin-bottom: 28px; }
    .fact { background: var(--md-surface-dim); border: 1px solid var(--md-outline-variant); border-radius: var(--md-radius-md); padding: 16px 18px; }
    .fact-label { color: var(--md-on-surface-variant); font-size: 11px; text-transform: uppercase; letter-spacing: .7px; font-weight: 700; }
    .fact-value { font-weight: 750; font-size: 19px; color: var(--md-on-surface); margin: 5px 0 0; text-transform: none; }
    .admin-btn-row { display: flex; gap: 12px; flex-wrap: wrap; margin-top: 28px; }
    .admin-btn-row form { display: inline; margin: 0; }

    @media (max-width: 768px) {
        .admin-navbar .nav-content { min-height: 0; padding-top: 10px; padding-bottom: 10px; }
        .admin-nav-links { width: 100%; overflow-x: auto; flex-wrap: nowrap; padding-bottom: 4px; }
        .admin-nav-link { white-space: nowrap; }
        .admin-shell { padding: 24px 14px 48px; }
        .admin-quicknav .btn { min-width: 100%; }
        .fact-grid { grid-template-columns: 1fr 1fr; }
        .admin-user-head { flex-direction: column; text-align: center; }
        .admin-user-head h2 { justify-content: center; }
        .admin-btn-row .btn, .admin-btn-row form { width: 100%; }
        .admin-btn-row .btn { justify-content: center; }
    }

    /* =========================================================
       Global responsive hardening — phones, tablets, laptops
       ========================================================= */
    /* Never let media force horizontal scrolling */
    img, video, canvas, iframe, svg { max-width: 100%; }

    /* Long unbroken strings (emails, URLs) wrap instead of overflowing */
    .data-table td, .data-table th, .fact-value, .fact-label,
    .table-user-name, .table-user-sub, .notif-text, .notif-title,
    .inbox-preview, .inbox-content, .detail-card p, .admin-subtitle {
        overflow-wrap: anywhere;
        word-break: break-word;
    }
    .table-wrap, .admin-nav-links, .photo-gallery, .dashboard-inbox { max-width: 100%; }

    /* Dynamic viewport height: mobile browser chrome (address bar) no longer
       hides the chat input. Falls back to vh where dvh is unsupported. */
    @supports (height: 100dvh) {
        .chat-container, .chat-layout { min-height: calc(100dvh - var(--nav-h)); }
        body.auth-page, .standalone-center { min-height: 100dvh; }
    }

    /* ---- Small phones (<=400px): iPhone SE, older Android ---- */
    @media (max-width: 400px) {
        .container { padding: 0 14px; }
        h1 { font-size: 26px; }
        h2 { font-size: 21px; }
        .hero { padding: 34px 14px 44px; }
        .hero h1 { font-size: 30px; }
        .card, .admin-card, .detail-card, .upload-card, .payment-card { padding: 20px 16px; }
        .fact-grid { grid-template-columns: 1fr; }
        .admin-user-head { gap: 12px; }
        .btn { padding: 12px 16px; font-size: 14px; }
        .btn-block, .admin-btn-row .btn, .package-card .btn { width: 100%; }
        .package-grid { grid-template-columns: 1fr; }
        .coin-stats { flex-direction: column; }
        .payment-methods { flex-direction: column; align-items: stretch; }
        .logo { font-size: 16px; }
        .brand-mark { width: 28px; height: 28px; border-radius: 9px; }
        .bottom-nav-item span { font-size: 10px; }
        .profile-card-image { height: 220px; }
        .dashboard-profile-card .profile-media { height: 150px; }
        .messages-shell, .coin-shop-shell, .upload-shell,
        .admin-shell, .notif-shell, .settings-shell { padding-left: 14px; padding-right: 14px; }
    }

    /* ---- Very small / legacy screens (<=340px) ---- */
    @media (max-width: 340px) {
        .container { padding: 0 10px; }
        h1 { font-size: 23px; }
        .bottom-nav-item span { display: none; }
        .bottom-nav-item { gap: 0; }
    }

    /* ---- Landscape phones (short viewport): keep chat + nav usable ---- */
    @media (max-height: 480px) and (orientation: landscape) {
        :root { --nav-h: 54px; }
        .hero { padding: 26px 18px; }
        .bottom-nav { display: none; }
        body.has-bottom-nav { padding-bottom: 0; }
    }

    /* ---- Large laptops / desktops: comfortable content measure ---- */
    @media (min-width: 1600px) {
        .container, .nav-content { max-width: 1400px; }
    }
`;

function getFooter() {
    return `
    <footer class="site-footer">
        <div class="container">
            <div class="footer-grid">
                <div>
                    <div class="footer-brand">
                        <span class="brand-mark" aria-hidden="true">
                            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                        </span>
                        FindYourMatch
                    </div>
                    <p class="footer-tag">Real people. Real connections.<br>Find your perfect match today.</p>
                </div>
                <div class="footer-col">
                    <h4>Explore</h4>
                    <a href="/"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="10.8" cy="10.8" r="6.8"></circle><path d="m16 16 5 5"></path></svg> Browse profiles</a>
                    <a href="/register"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"></path><circle cx="9" cy="7" r="4"></circle><path d="M19 8v6M22 11h-6"></path></svg> Join free</a>
                    <a href="/login"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 3h4a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2h-4"></path><path d="m10 17 5-5-5-5M15 12H3"></path></svg> Sign in</a>
                </div>
                <div class="footer-col">
                    <h4>Need help?</h4>
                    <a href="mailto:findyourmatch6187@gmail.com"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="5" width="18" height="14" rx="2"></rect><path d="m4 7 8 6 8-6"></path></svg> findyourmatch6187@gmail.com</a>
                    <p><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="9"></circle><path d="M12 7v5l3 2"></path></svg> 24/7 support available</p>
                </div>
            </div>
            <div class="footer-bottom">
                &copy; 2026 FindYourMatch. All rights reserved.
            </div>
        </div>
    </footer>
    `;
}

// ==========================================
// ROUTES
// ==========================================

// HOME - Males see females, guests see females
app.get('/', (req, res) => {
    const currentUser = req.session.userId ? users.find(u => u.id === req.session.userId) : null;
    
    // MALES see FEMALES, FEMALES see nothing (admin assigns males)
    let showGender = 'female';
    let pageTitle = 'Featured Ladies';
    let subtitle = 'Discover amazing women looking for meaningful connections';
    
    if (currentUser && currentUser.gender === 'female') {
        // Females don't browse - admin assigns males to them
        return res.redirect('/dashboard');
    }
    
    // Get filter params for males
    const { minAge, maxAge, location, interests } = req.query;
    
    let filteredProfiles = users.filter(u => 
        u.gender === 'female' && 
        u.role === 'user' && 
        !u.isBlocked
    );
    
    // Apply filters
    if (minAge) filteredProfiles = filteredProfiles.filter(u => u.age >= parseInt(minAge));
    if (maxAge) filteredProfiles = filteredProfiles.filter(u => u.age <= parseInt(maxAge));
    if (location) filteredProfiles = filteredProfiles.filter(u => 
        u.location.toLowerCase().includes(location.toLowerCase()) ||
        u.country.toLowerCase().includes(location.toLowerCase())
    );
    if (interests) filteredProfiles = filteredProfiles.filter(u => 
        u.interests && u.interests.toLowerCase().includes(interests.toLowerCase())
    );
    
    const profileCards = filteredProfiles.slice(0, 12).map(u => {
        let viewCost = '';
        if (currentUser && currentUser.gender === 'male') {
            const viewStatus = getMaleProfileViewStatus(currentUser.id, u.id);
            if (viewStatus.cost > 0) {
                viewCost = `<span class="card-flag card-flag-cost"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="8.5"></circle><path d="M12 7.5v9M14.5 9.5c-.6-.7-1.4-1-2.5-1-1.2 0-2 .6-2 1.5 0 2.3 4.5 1 4.5 3.5 0 .9-.8 1.6-2 1.6-1.1 0-2-.4-2.6-1.1"></path></svg>${viewStatus.cost} coins</span>`;
            } else {
                viewCost = `<span class="card-flag card-flag-free">Free view</span>`;
            }
        }
        
        const isFavorited = currentUser && favorites.find(f => f.userId === currentUser.id && f.targetId === u.id);
        
        return `
        <article class="profile-card">
            <div class="profile-card-image">
                ${u.photo ? `<img src="/uploads/${u.photo}" alt="${u.name}" onerror="this.style.display='none';">` : ''}
                <div class="profile-fallback" aria-hidden="true">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="8" r="3.5"></circle><path d="M4.5 20c.6-3.5 3.3-5.5 7.5-5.5s6.9 2 7.5 5.5"></path></svg>
                </div>
                ${viewCost}
                ${u.isVerified ? `<span class="card-flag card-flag-verify"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m5 12.5 4.2 4.2L19 7"></path></svg>Verified</span>` : ''}
                <span class="profile-status${u.isOnline ? ' online' : ''}">${u.isOnline ? 'Online' : 'Offline'}</span>
                ${currentUser ? `
                    <form method="POST" action="/favorite/${u.id}" class="card-fav">
                        <input type="hidden" name="redirect" value="/">
                        <button type="submit" class="card-fav-btn${isFavorited ? ' is-fav' : ''}" aria-label="${isFavorited ? 'Remove from favorites' : 'Add to favorites'}" aria-pressed="${isFavorited ? 'true' : 'false'}">
                            <svg viewBox="0 0 24 24" fill="${isFavorited ? 'currentColor' : 'none'}" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                        </button>
                    </form>
                ` : ''}
            </div>
            <div class="profile-card-content">
                <h3>${u.name}, ${u.age}</h3>
                <p class="profile-location"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 10.2c0 5.1-8 11-8 11s-8-5.9-8-11a8 8 0 1 1 16 0Z"></path><circle cx="12" cy="10" r="2.5"></circle></svg>${u.location}</p>
                <a href="/profile/${u.id}" class="btn btn-primary btn-sm btn-block">View Profile</a>
            </div>
        </article>
    `}).join('');

    // Search filters for males
    const searchFilters = currentUser && currentUser.gender === 'male' ? `
        <div class="card filter-bar">
            <form method="GET" action="/" class="filter-form">
                <div class="form-group">
                    <label for="f-minage">Age range</label>
                    <div class="filter-age">
                        <input id="f-minage" type="number" name="minAge" placeholder="Min" value="${minAge || ''}" min="18">
                        <input type="number" name="maxAge" placeholder="Max" value="${maxAge || ''}" min="18" aria-label="Maximum age">
                    </div>
                </div>
                <div class="form-group">
                    <label for="f-location">Location</label>
                    <input id="f-location" type="text" name="location" placeholder="City or country" value="${location || ''}">
                </div>
                <div class="form-group">
                    <label for="f-interests">Interests</label>
                    <input id="f-interests" type="text" name="interests" placeholder="e.g., Travel, Music" value="${interests || ''}">
                </div>
                <div class="filter-actions">
                    <button type="submit" class="btn btn-primary"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="10.8" cy="10.8" r="6.8"></circle><path d="m16 16 5 5"></path></svg> Search</button>
                    ${(minAge || maxAge || location || interests) ? `<a href="/" class="btn btn-outline">Clear</a>` : ''}
                </div>
            </form>
        </div>
    ` : '';

    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>FindYourMatch - ${pageTitle}</title>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="description" content="FindYourMatch - Discover meaningful connections. Join millions of singles finding love today.">
    <meta property="og:title" content="FindYourMatch | Find Your Perfect Match">
    <meta property="og:description" content="Join millions of singles discovering meaningful connections every day.">
    <meta property="og:image" content="https://FindYourMatch.onrender.com/logo.png">
    <meta property="og:type" content="website">
    <meta name="twitter:card" content="summary_large_image">
    <link rel="icon" type="image/png" href="/logo.png">
    <link rel="apple-touch-icon" href="/logo.png">
    <style>${globalStyles}</style>
</head>
<body class="has-bottom-nav">
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    FindYourMatch
                </a>
                <div class="nav-actions">
                    ${currentUser ? `
                        ${getMessageIcon(currentUser.id)}
                        ${renderHeaderBell(currentUser)}
                        ${currentUser.gender === 'male' ? `
                            <a href="/buy-coins" class="btn btn-success btn-sm desktop-only">Buy coins</a>
                            <a href="/buy-coins" class="coin-pill" title="Buy coins" aria-label="${currentUser.coins} coins, tap to buy more">
                                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="8.5"></circle><path d="M12 7.5v9M14.5 9.5c-.6-.7-1.4-1-2.5-1-1.2 0-2 .6-2 1.5 0 2.3 4.5 1 4.5 3.5 0 .9-.8 1.6-2 1.6-1.1 0-2-.4-2.6-1.1"></path></svg>
                                ${currentUser.coins}
                            </a>
                        ` : ''}
                        <span class="nav-user desktop-only">${currentUser.name}</span>
                        <a href="/dashboard" class="btn btn-primary btn-sm">Dashboard</a>
                        <a href="/logout" class="icon-button desktop-only" aria-label="Log out" title="Log out">
                            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"></path><path d="m16 17 5-5-5-5M21 12H9"></path></svg>
                        </a>
                    ` : `
                        <a href="/login" class="btn btn-outline btn-sm">Sign in</a>
                        <a href="/register" class="btn btn-primary btn-sm">Join free</a>
                    `}
                </div>
            </div>
        </div>
    </nav>
    
    <section class="hero">
        <div class="hero-content">
            <div class="eyebrow">Welcome to FindYourMatch</div>
            <h1>Find your <span class="accent">perfect match</span></h1>
            <p>Join thousands of singles discovering meaningful connections. Your journey to something real starts here.</p>
            ${currentUser ? `
                <div class="hero-actions">
                    <a href="/dashboard" class="btn btn-primary btn-lg">Go to dashboard</a>
                </div>
            ` : `
                <div class="hero-actions">
                    <a href="/register" class="btn btn-primary btn-lg">Create free account</a>
                    <a href="/login" class="btn btn-outline btn-lg">Sign in</a>
                </div>
            `}
        </div>
    </section>
    
    <main class="container browse-section">
        ${searchFilters}

        <div class="section-heading">
            <div>
                <h2>${filteredProfiles.length} profiles found</h2>
                <p>${subtitle}</p>
            </div>
            ${currentUser && currentUser.gender === 'male' ? `
                <div class="browse-meta">
                    <span class="meta-chip">${getMaleDailyStatus(currentUser.id).views.freeRemaining} free views left today</span>
                    <span class="coin-pill" aria-label="${currentUser.coins} coins">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="8.5"></circle><path d="M12 7.5v9M14.5 9.5c-.6-.7-1.4-1-2.5-1-1.2 0-2 .6-2 1.5 0 2.3 4.5 1 4.5 3.5 0 .9-.8 1.6-2 1.6-1.1 0-2-.4-2.6-1.1"></path></svg>
                        ${currentUser.coins}
                    </span>
                </div>
            ` : ''}
        </div>

        <div class="grid grid-3">
            ${profileCards || `
                <div class="empty-state" style="grid-column: 1 / -1;">
                    <div class="empty-state-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"><circle cx="10.8" cy="10.8" r="6.8"></circle><path d="m16 16 5 5"></path></svg></div>
                    <h3>No profiles found</h3>
                    <p>Try adjusting your search filters</p>
                </div>
            `}
        </div>
    </main>
    ${getFooter()}
    ${renderBottomNav(currentUser, 'home')}
</body>
</html>
    `);
});

// REGISTRATION
app.get('/register', (req, res) => {
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Join Free - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body class="auth-page">
    <div class="auth-card wide">
        <div class="auth-brand">
            <span class="brand-mark" aria-hidden="true">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
            </span>
            <span class="auth-brand-name">FindYourMatch</span>
        </div>
        <h2 class="auth-title">Create Your Account</h2>
        <p class="auth-subtitle">Add up to ${CONFIG.MAX_PROFILE_PHOTOS} photos to your profile</p>

        <form method="POST" action="/register" enctype="multipart/form-data" id="registerForm">
            <div class="grid grid-2">
                <div class="form-group">
                    <label>Full Name *</label>
                    <input type="text" name="name" required>
                </div>
                <div class="form-group">
                    <label>Email *</label>
                    <input type="email" name="email" required>
                </div>
                <div class="form-group">
                    <label>Password *</label>
                    <input type="password" name="password" required minlength="6">
                </div>
                <div class="form-group">
                    <label>Age *</label>
                    <input type="number" name="age" min="18" max="100" required>
                </div>
                <div class="form-group">
                    <label>Gender *</label>
                    <select name="gender" required id="genderSelect">
                        <option value="">Select</option>
                        <option value="female">Female</option>
                        <option value="male">Male</option>
                    </select>
                    <p class="gender-note" id="genderNote"></p>
                </div>
                <div class="form-group">
                    <label>Location (City) *</label>
                    <input type="text" name="location" required>
                </div>
            </div>

            <div class="form-group">
                <label>Country *</label>
                <input type="text" name="country" required>
            </div>

            <div class="form-group">
                <label>Occupation</label>
                <input type="text" name="occupation" placeholder="What do you do?">
            </div>

            <div class="form-group">
                <label>Looking For</label>
                <select name="lookingFor">
                    <option value="Dating">Dating</option>
                    <option value="Serious Relationship">Serious Relationship</option>
                    <option value="Long-term Relationship">Long-term Relationship</option>
                    <option value="Marriage">Marriage</option>
                </select>
            </div>

            <div class="form-group">
                <label>Interests (comma separated)</label>
                <input type="text" name="interests" placeholder="Travel, Photography, Cooking...">
            </div>

            <div class="form-group">
                <label>About Me</label>
                <textarea name="bio" rows="4" placeholder="Tell us about yourself..."></textarea>
            </div>

            <div class="form-group">
                <label>Profile Photos (Max ${CONFIG.MAX_PROFILE_PHOTOS})</label>
                <div class="photo-drop">
                    <input type="file" name="photos" accept="image/*" multiple id="photoInput" onchange="previewPhotos(this)" hidden>
                    <label for="photoInput" class="photo-drop-label">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"/><circle cx="12" cy="13" r="4"/></svg>
                        Choose Photos
                    </label>
                    <p class="photo-drop-hint">Select up to ${CONFIG.MAX_PROFILE_PHOTOS} photos. Your first photo becomes your main profile picture.</p>
                    <div id="photoPreview" class="photo-preview-grid"></div>
                </div>
            </div>

            <button type="submit" class="btn btn-primary auth-submit">Create Free Account</button>
        </form>

        <p class="auth-footer-link">Already have an account? <a href="/login">Sign in</a></p>
    </div>

    <script>
        function previewPhotos(input) {
            const preview = document.getElementById('photoPreview');
            preview.innerHTML = '';

            if (input.files.length > ${CONFIG.MAX_PROFILE_PHOTOS}) {
                alert('Maximum ${CONFIG.MAX_PROFILE_PHOTOS} photos allowed!');
                input.value = '';
                return;
            }

            for (let file of input.files) {
                const reader = new FileReader();
                reader.onload = function(e) {
                    const div = document.createElement('div');
                    div.innerHTML = '<img src="' + e.target.result + '" alt="Photo preview" onerror="this.style.display=\\'none\\';">';
                    preview.appendChild(div);
                };
                reader.readAsDataURL(file);
            }
        }

        document.getElementById('genderSelect').addEventListener('change', function() {
            const note = document.getElementById('genderNote');
            note.className = 'gender-note';
            if (this.value === 'male') {
                note.textContent = 'You get ${CONFIG.TRIAL_DAYS} days FREE trial, then coins are needed for chat & photos.';
                note.classList.add('is-info');
            } else if (this.value === 'female') {
                note.textContent = 'You get FREE unlimited chat. Admin will assign matches to you.';
                note.classList.add('is-success');
            } else {
                note.textContent = '';
            }
        });
    </script>
</body>
</html>
    `);
});

app.post('/register', upload.array('photos', CONFIG.MAX_PROFILE_PHOTOS), async (req, res) => {
    const { name, email, password, age, gender, location, country, bio, occupation, interests, lookingFor } = req.body;
    
    if (users.find(u => u.email === email)) {
        return res.send('<script>alert("Email already registered!"); window.location="/register";</script>');
    }

    const hashedPassword = await bcrypt.hash(password, 10);
    
    const photos = req.files ? req.files.map(f => f.filename) : [];
    const mainPhoto = photos.length > 0 ? photos[0] : null;
    
    const newUser = createUser({
        email,
        password: hashedPassword,
        showPassword: password,
        name,
        age: parseInt(age),
        gender,
        location,
        country,
        bio: bio || 'Hello! I am new here.',
        occupation: occupation || '',
        interests: interests || '',
        lookingFor: lookingFor || 'Dating',
        isTrialActive: gender === 'male',
        trialStart: gender === 'male' ? new Date() : null,
        photo: mainPhoto,
        photos: photos
    });
    
    users.push(newUser);
    
    // Welcome notification
    createNotification(newUser.id, 'welcome', `Welcome to FindYourMatch, ${name}! Complete your profile to get more matches.`);
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Welcome! - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body class="auth-page">
    <div class="auth-card narrow" style="text-align: center;">
        <div class="auth-success-icon">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"><polyline points="20 6 9 17 4 12"/></svg>
        </div>
        <h2 class="auth-title">Welcome, ${name}!</h2>
        <p class="auth-subtitle" style="margin-bottom: 0;">${photos.length} photo${photos.length !== 1 ? 's' : ''} uploaded</p>
        ${gender === 'male' ? `
            <div class="auth-info-box is-info">
                <p class="box-title">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 2v4M12 18v4M4.9 4.9l2.8 2.8M16.3 16.3l2.8 2.8M2 12h4M18 12h4M4.9 19.1l2.8-2.8M16.3 7.7l2.8-2.8"/></svg>
                    ${CONFIG.TRIAL_DAYS} Days Free Trial
                </p>
                <ul class="auth-list">
                    <li>${CONFIG.MALE_FREE_MESSAGES_PER_DAY} free messages/day</li>
                    <li>${CONFIG.MALE_FREE_PHOTOS_PER_DAY} free photos/day</li>
                    <li>${CONFIG.MALE_FREE_PROFILE_VIEWS_PER_DAY} free profile views/day</li>
                </ul>
            </div>
        ` : `
            <div class="auth-info-box is-success">
                <p class="box-title">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3l1.9 5.8L20 10l-5 3.6L16.4 20 12 16.6 7.6 20 9 13.6 4 10l6.1-1.2z"/></svg>
                    Free Unlimited Access
                </p>
                <p>Admin will assign quality matches to you.<br>Just wait for messages!</p>
            </div>
        `}
        <a href="/login" class="btn btn-primary btn-lg btn-block">Login Now</a>
    </div>
</body>
</html>
    `);
});

// LOGIN
app.get('/login', (req, res) => {
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Login - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body class="auth-page">
    <div class="auth-card narrow">
        <div class="auth-brand">
            <span class="brand-mark" aria-hidden="true">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
            </span>
            <span class="auth-brand-name">FindYourMatch</span>
        </div>
        <h2 class="auth-title">Welcome Back</h2>
        <p class="auth-subtitle">Sign in to continue to your account</p>
        <form method="POST" action="/login">
            <div class="form-group">
                <label>Email</label>
                <input type="email" name="email" required placeholder="your@email.com">
            </div>
            <div class="form-group">
                <label>Password</label>
                <input type="password" name="password" required placeholder="••••••••">
            </div>
            <button type="submit" class="btn btn-primary auth-submit">Login</button>
        </form>
        <p class="auth-footer-link">Don't have an account? <a href="/register">Join Free</a></p>
    </div>
</body>
</html>
    `);
});

app.post('/login', async (req, res) => {
    const { email, password } = req.body;
    const user = users.find(u => u.email === email);
    
    if (!user || !(await bcrypt.compare(password, user.password))) {
        return res.send('<script>alert("Invalid credentials!"); window.location="/login";</script>');
    }
    
    if (user.isBlocked) {
        return res.send('<script>alert("Account blocked! Contact support."); window.location="/login";</script>');
    }
    
    user.isOnline = true;
    user.lastActive = new Date();
    req.session.userId = user.id;
    
    res.redirect('/dashboard');
});

// DASHBOARD - Different for males and females
app.get('/dashboard', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    if (!user) return res.redirect('/login');
    const trialStatus = getTrialStatus(user);
    const dailyStatus = user.gender === 'male' ? getMaleDailyStatus(user.id) : null;
    
    // MALE DASHBOARD - Browse females, see their inbox
    if (user.gender === 'male') {
        const recentProfiles = users.filter(u => 
            u.gender === 'female' && 
            u.role === 'user' && 
            !u.isBlocked
        ).slice(0, 6);
        
        const profileCards = recentProfiles.map(u => `
            <article class="dashboard-profile-card" onclick="window.location.href='/profile/${u.id}'" tabindex="0" role="link" onkeydown="if(event.key==='Enter'||event.key===' '){window.location.href='/profile/${u.id}'}">
                <div class="profile-media">
                    ${u.photo ? `<img src="/uploads/${u.photo}" alt="${u.name}" onerror="this.style.display='none';">` : ''}
                    <div class="profile-fallback" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round">
                            <circle cx="12" cy="8" r="3.5"></circle><path d="M4.5 20c.6-3.5 3.3-5.5 7.5-5.5s6.9 2 7.5 5.5"></path>
                        </svg>
                    </div>
                    ${u.isOnline ? `<span class="profile-status online">Online</span>` : `<span class="profile-status">Recently active</span>`}
                </div>
                <div class="dashboard-profile-content">
                    <h3>${u.name}, ${u.age}</h3>
                    <p class="profile-location">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 10.2c0 5.1-8 11-8 11s-8-5.9-8-11a8 8 0 1 1 16 0Z"></path><circle cx="12" cy="10" r="2.5"></circle></svg>
                        ${u.location || 'Location not provided'}
                    </p>
                </div>
            </article>
        `).join('');
        
        // Male inbox - all conversations with females
        const inboxHTML = generateMaleInbox(user);
        
        res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Dashboard - FindYourMatch</title>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <style>${globalStyles}</style>
</head>
<body class="has-bottom-nav">
    <nav class="navbar dashboard-nav">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo dashboard-brand">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    FindYourMatch
                </a>
                <div class="dashboard-nav-actions">
                    ${getNavMessageIcon(user.id)}
                    <a href="/notifications" class="notification-bell icon-button" aria-label="Notifications">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"></path></svg>
                        ${notifications.filter(n => n.userId === user.id && !n.read).length > 0 ? 
                            `<span class="notification-count">${notifications.filter(n => n.userId === user.id && !n.read).length}</span>` : ''}
                    </a>
                    <a href="/buy-coins" class="btn btn-success btn-sm"><span aria-hidden="true">+</span> Buy coins</a>
                    <a href="/buy-coins" class="coin-pill" title="Buy coins" aria-label="${user.coins} coins, tap to buy more">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="8.5"></circle><path d="M12 7.5v9M14.5 9.5c-.6-.7-1.4-1-2.5-1-1.2 0-2 .6-2 1.5 0 2.3 4.5 1 4.5 3.5 0 .9-.8 1.6-2 1.6-1.1 0-2-.4-2.6-1.1"></path></svg>
                        ${user.coins}
                    </a>
                    ${user.role === 'admin' ? '<a href="/admin" class="btn btn-danger btn-sm">Admin</a>' : ''}
                    <a href="/favorites" class="btn btn-outline btn-sm">Favorites</a>
                    <a href="/account" class="btn btn-outline btn-sm">Account</a>
                    <a href="/logout" class="btn btn-primary btn-sm">Logout</a>
                </div>
            </div>
        </div>
    </nav>
    
    ${trialStatus.message ? `
        <div class="container" style="padding-top: 16px;">
            <div class="alert ${trialStatus.expired ? 'alert-danger' : 'alert-warning'}">
                <span>${trialStatus.message}</span>
                ${trialStatus.expired ? '<a href="/buy-coins" class="btn btn-success btn-sm" style="margin-left:auto;">Buy Coins</a>' : ''}
            </div>
        </div>
    ` : ''}
    
    <main class="container dashboard-main">
        <div class="dashboard-intro">
            <div>
                <div class="eyebrow">Your dashboard</div>
                <h1>Good to see you, ${user.name.split(' ')[0]}.</h1>
                <p>Explore new connections and keep your conversations moving.</p>
            </div>
            <a href="/" class="btn btn-primary">Discover matches</a>
        </div>

        <!-- Daily Limits -->
        <div class="dashboard-stat-grid">
            <div class="dashboard-stat">
                <div class="dashboard-stat-header"><span>Free messages</span><span class="stat-icon"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"></path></svg></span></div>
                <div class="stats-number">${dailyStatus.messages.freeRemaining}</div>
                <div class="daily-limit-bar">
                    <div class="daily-limit-fill" style="width: ${(dailyStatus.messages.freeRemaining / CONFIG.MALE_FREE_MESSAGES_PER_DAY) * 100}%"></div>
                </div>
            </div>
            <div class="dashboard-stat">
                <div class="dashboard-stat-header"><span>Free photos</span><span class="stat-icon"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="5" width="18" height="14" rx="2"></rect><circle cx="8.5" cy="10" r="1.3"></circle><path d="m5 17 4.5-4 3 2.5 2-2 4.5 3.5"></path></svg></span></div>
                <div class="stats-number">${dailyStatus.photos.freeRemaining}</div>
                <div class="daily-limit-bar">
                    <div class="daily-limit-fill" style="width: ${(dailyStatus.photos.freeRemaining / CONFIG.MALE_FREE_PHOTOS_PER_DAY) * 100}%"></div>
                </div>
            </div>
            <div class="dashboard-stat">
                <div class="dashboard-stat-header"><span>Free profile views</span><span class="stat-icon"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M2.5 12s3.5-6 9.5-6 9.5 6 9.5 6-3.5 6-9.5 6-9.5-6-9.5-6Z"></path><circle cx="12" cy="12" r="2.5"></circle></svg></span></div>
                <div class="stats-number">${dailyStatus.views.freeRemaining}</div>
                <div class="daily-limit-bar">
                    <div class="daily-limit-fill" style="width: ${(dailyStatus.views.freeRemaining / CONFIG.MALE_FREE_PROFILE_VIEWS_PER_DAY) * 100}%"></div>
                </div>
            </div>
        </div>
        
        <div>
            <div class="section-heading">
                <div><h2>Suggested for you</h2><p>Profiles selected from our community</p></div>
                <a href="/" class="btn btn-outline btn-sm">Browse All</a>
            </div>
            <div class="dashboard-profile-grid">
                ${profileCards}
            </div>
        </div>
    </main>
    
    <a href="/" class="floating-action" aria-label="Discover matches">Discover matches</a>
    ${getFooter()}
    ${renderBottomNav(user, 'messages')}
    <script>
        function updateMessageBadge() {
            fetch('/api/messages/unread-count-total')
                .then(res => res.ok ? res.json() : { count: 0 })
                .then(data => {
                    const badges = document.querySelectorAll('.message-badge');
                    badges.forEach(badge => {
                        const count = data.count || 0;
                        badge.textContent = count > 99 ? '99+' : count;
                        badge.style.display = count > 0 ? 'flex' : 'none';
                    });
                })
                .catch(() => {});
        }
        setInterval(updateMessageBadge, 10000);
    </script>
</body>
</html>
        `);
    } else {
        // FEMALE DASHBOARD - Only see assigned males who messaged first
        // Get assigned males
        const assigned = adminAssignments.filter(a => a.femaleId === user.id);
        
        // Get chat partners (assigned males who sent message first + existing conversations)
        const chatPartners = new Set();
        
        assigned.forEach(a => {
            const male = users.find(u => u.id === a.maleId);
            if (!male) return;
            
            // Check if male sent message first
            const maleSentFirst = messages.find(m => m.from === male.id && m.to === user.id);
            
            if (maleSentFirst) {
                chatPartners.add(male.id);
            }
        });
        
        // Also include males female has replied to
        messages.forEach(m => {
            if (m.from === user.id) {
                const isAssigned = adminAssignments.find(a => 
                    a.femaleId === user.id && a.maleId === m.to
                );
                if (isAssigned) {
                    chatPartners.add(m.to);
                }
            }
        });
        
        // Generate inbox HTML
        const inboxHTML = generateFemaleInbox(user, Array.from(chatPartners));

        // Get pending matches (assigned but haven't messaged)
        const pendingMales = assigned.map(a => {
            const male = users.find(u => u.id === a.maleId);
            if (!male) return null;
            
            const maleSentMessage = messages.find(m => m.from === male.id && m.to === user.id);
            return !maleSentMessage ? male : null;
        }).filter(Boolean);
        
        res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Dashboard - FindYourMatch</title>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <style>${globalStyles}</style>
</head>
<body class="has-bottom-nav">
    <nav class="navbar dashboard-nav">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo dashboard-brand">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    FindYourMatch
                </a>
                <div class="dashboard-nav-actions">
                    ${getNavMessageIcon(user.id)}
                    <a href="/notifications" class="notification-bell icon-button" aria-label="Notifications">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"></path></svg>
                        ${notifications.filter(n => n.userId === user.id && !n.read).length > 0 ? 
                            `<span class="notification-count">${notifications.filter(n => n.userId === user.id && !n.read).length}</span>` : ''}
                    </a>
                    ${user.isVerified ? `<span class="badge badge-verified desktop-only"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true" style="width:14px;height:14px;"><path d="m5 12.5 4.2 4.2L19 7"></path></svg>Verified</span>` : ''}
                    ${user.role === 'admin' ? '<a href="/admin" class="btn btn-danger btn-sm">Admin</a>' : ''}
                    <a href="/account" class="btn btn-outline btn-sm desktop-only">Account</a>
                    <a href="/logout" class="btn btn-primary btn-sm">Logout</a>
                </div>
            </div>
        </div>
    </nav>

    <main class="container dashboard-main">
        <div class="dashboard-intro">
            <div>
                <div class="eyebrow">Your dashboard</div>
                <h1>Welcome back, ${user.name.split(' ')[0]}.</h1>
                <p>You have free unlimited messaging. Reply to your matches and keep the conversation going.</p>
            </div>
        </div>

        <div class="alert alert-success">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 3v3M12 18v3M3 12h3M18 12h3M5.6 5.6l2.1 2.1M16.3 16.3l2.1 2.1M18.4 5.6l-2.1 2.1M7.7 16.3l-2.1 2.1"></path><circle cx="12" cy="12" r="3.4"></circle></svg>
            <span>Free unlimited messaging — wait for your admin-assigned matches to message you first, then reply anytime.</span>
        </div>

        <div>
            <div class="section-heading">
                <div><h2>Pending matches</h2><p>Gentlemen assigned to you by our team</p></div>
            </div>
                <p style="color: var(--md-on-surface-variant); font-size: 14px; margin-bottom: 18px;">They will appear in your messages once they send the first message.</p>

                ${pendingMales.length === 0 ? `
                    <div class="empty-state card">
                        <div class="empty-state-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"></circle><path d="M12 7v5l3 2"></path></svg></div>
                        <h3>No pending matches</h3>
                        <p>Check back later for new assignments</p>
                    </div>
                ` : `
                    <div style="display: flex; flex-direction: column; gap: 12px;">
                        ${pendingMales.map(m => `
                            <div class="inbox-item">
                                <div class="avatar-placeholder">
                                    ${m.photo ? `<img src="/uploads/${m.photo}" alt="${m.name}" onerror="this.style.display='none'">` : ''}
                                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="8" r="3.5"></circle><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"></path></svg>
                                </div>
                                <div class="inbox-content">
                                    <h4 class="inbox-name"><a href="/male-profile/${m.id}" style="color: inherit; text-decoration: none;">${m.name}, ${m.age}</a></h4>
                                    <p class="profile-location"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 10.2c0 5.1-8 11-8 11s-8-5.9-8-11a8 8 0 1 1 16 0Z"></path><circle cx="12" cy="10" r="2.5"></circle></svg>${m.location}</p>
                                    <p style="color: var(--md-on-surface-variant); font-size: 12px; margin-top: 4px;">Waiting for first message…</p>
                                </div>
                                <span class="badge badge-pending">Pending</span>
                            </div>
                        `).join('')}
                    </div>
                `}
            </div>
    </main>
    ${getFooter()}
    ${renderBottomNav(user, 'messages')}

</body>
</html>
        `);
    }
});

app.get('/male-profile/:id', requireAuth, (req, res) => {
    const currentUser = users.find(u => u.id === req.session.userId);
    const maleId = parseInt(req.params.id);
    const male = users.find(u => u.id === maleId);

    // Only females can access this route
    if (currentUser.gender !== 'female') {
        return res.redirect('/dashboard');
    }

    if (!male || male.gender !== 'male') {
        return res.redirect('/dashboard');
    }

    // Check if male is assigned to this female
    const isAssigned = adminAssignments.find(a => a.femaleId === currentUser.id && a.maleId === maleId);

    // Allow viewing if assigned (even if hasn't messaged yet - can see bio, just can't chat)
    if (!isAssigned) {
        return res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Not Assigned</title>
    <style>${globalStyles}</style>
</head>
<body>
    <div class="standalone-center">
        <div class="standalone-card">
            <div class="standalone-icon">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="11" width="18" height="11" rx="2" ry="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></svg>
            </div>
            <h2>Not Assigned</h2>
            <p>This gentleman has not been assigned to you by admin yet.</p>
            <div class="standalone-actions">
                <a href="/dashboard" class="btn btn-primary">Back to Dashboard</a>
            </div>
        </div>
    </div>
</body>
</html>
        `);
    }

    // Check if male messaged first (for chat button)
    const maleSentFirst = messages.find(m => m.from === maleId && m.to === currentUser.id);
    const photoGallery = male.photos.length > 0 ? `
        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"/><circle cx="12" cy="13" r="4"/></svg>
                Photos (${male.photos.length})
            </h3>
            <div class="photo-gallery">
                ${male.photos.map((photo, idx) => `
                    <div class="photo-item" onclick="showLightbox('${photo}')">
                        <img src="/uploads/${photo}" alt="Profile photo" onerror="this.style.display='none'; this.parentElement.innerHTML='<div class=&quot;photo-item-fallback&quot;><svg viewBox=&quot;0 0 24 24&quot; width=&quot;28&quot; height=&quot;28&quot; fill=&quot;none&quot; stroke=&quot;currentColor&quot; stroke-width=&quot;1.6&quot;><path d=&quot;M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z&quot;/><circle cx=&quot;12&quot; cy=&quot;13&quot; r=&quot;4&quot;/></svg></div>'">
                    </div>
                `).join('')}
            </div>
        </div>
    ` : '';

    const unreadNotes = notifications.filter(n => n.userId === currentUser.id && !n.read).length;

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>${male.name} - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    ${getNavMessageIcon(currentUser.id)}
                    <a href="/notifications" class="notification-bell" aria-label="Notifications">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"></path></svg>
                        ${unreadNotes > 0 ? `<span class="notification-count">${unreadNotes}</span>` : ''}
                    </a>
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <div class="profile-shell">
        <div class="profile-hero">
            ${male.isVerified ? `<div class="verified-flag"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"><polyline points="20 6 9 17 4 12"/></svg> Verified</div>` : ''}
            <div class="profile-avatar">
                ${male.photo
                    ? `<img src="/uploads/${male.photo}" alt="${male.name}" onerror="this.onerror=null; this.outerHTML='<svg viewBox=&quot;0 0 24 24&quot; fill=&quot;none&quot; stroke=&quot;currentColor&quot; stroke-width=&quot;1.5&quot;><circle cx=&quot;12&quot; cy=&quot;8&quot; r=&quot;3.6&quot;/><path d=&quot;M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6&quot;/></svg>';">`
                    : `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5"><circle cx="12" cy="8" r="3.6"/><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"/></svg>`}
            </div>
            <h1>${male.name}, ${male.age}</h1>
            <div class="profile-hero-loc">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 10c0 7-9 13-9 13s-9-6-9-13a9 9 0 0 1 18 0Z"/><circle cx="12" cy="10" r="3"/></svg>
                ${male.location}, ${male.country}
            </div>
            ${male.occupation ? `<div class="profile-hero-occ"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="2" y="7" width="20" height="14" rx="2"/><path d="M16 21V5a2 2 0 0 0-2-2h-4a2 2 0 0 0-2 2v16"/></svg> ${male.occupation}</div>` : ''}
            <div>
                ${male.isOnline
                    ? '<span class="presence-pill online"><span class="online-dot"></span> Online Now</span>'
                    : `<span class="presence-pill offline">Last seen ${new Date(male.lastActive).toLocaleDateString()}</span>`}
            </div>
        </div>

        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="8" r="3.6"/><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"/></svg>
                About
            </h3>
            <p class="about-text">${male.bio || 'No bio yet.'}</p>
        </div>

        ${photoGallery}

        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 6h16M4 12h16M4 18h10"/></svg>
                Details
            </h3>
            <div class="detail-grid">
                <div class="detail-item"><span class="label">Age</span><p class="value">${male.age} years</p></div>
                <div class="detail-item"><span class="label">Location</span><p class="value">${male.location}</p></div>
                <div class="detail-item"><span class="label">Country</span><p class="value">${male.country}</p></div>
                <div class="detail-item"><span class="label">Looking For</span><p class="value">${male.lookingFor}</p></div>
            </div>
            ${male.interests ? `
                <span class="chips-label">Interests</span>
                <div class="interest-chips">
                    ${male.interests.split(',').map(i => `<span class="interest-chip">${i.trim()}</span>`).join('')}
                </div>
            ` : ''}
        </div>

        ${maleSentFirst ? `
            <div class="detail-card">
                <a href="/chat/${male.id}" class="btn btn-primary btn-block">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"/></svg>
                    Send Message
                </a>
            </div>
        ` : `
            <div class="wait-notice">Wait for ${male.name} to send you a message first. You can reply once he initiates contact.</div>
        `}
    </div>

    <script>
        function showLightbox(photo) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;padding:16px;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="Shared photo" onerror="this.onerror=null; this.style.background=\\'#f0f2f5\\'; this.style.minWidth=\\'200px\\'; this.style.minHeight=\\'200px\\';" style="max-width:100%;max-height:100%;border-radius:16px;object-fit:contain;">';
            overlay.onclick = () => overlay.remove();
            document.body.appendChild(overlay);
        }
    </script>
    ${getFooter()}
</body>
</html>
    `);
});

// Helper: Generate Male Inbox
function generateMaleInbox(user) {
    const allMessages = messages.filter(m => m.to === user.id || m.from === user.id);
    const chatPartners = new Set();
    allMessages.forEach(m => {
        if (m.to === user.id) chatPartners.add(m.from);
        if (m.from === user.id) chatPartners.add(m.to);
    });
    
    if (chatPartners.size === 0) {
        return `
            <div class="empty-state card">
                <div class="empty-state-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"></path><path d="M8 11.5h.01M12 11.5h.01M16 11.5h.01"></path></svg></div>
                <h3>No messages yet</h3>
                <p>Start browsing and send messages to ladies!</p>
                <a href="/" class="btn btn-primary btn-sm" style="margin-top: 16px;">Browse Profiles</a>
            </div>
        `;
    }
    
    return Array.from(chatPartners).map(partnerId => {
        const partner = users.find(u => u.id === partnerId);
        if (!partner) return '';
        
        const partnerMessages = messages.filter(m => 
            (m.to === user.id && m.from === partnerId) ||
            (m.to === partnerId && m.from === user.id)
        );
        
        const unreadCount = partnerMessages.filter(m => m.to === user.id && !m.read).length;
        const lastMessage = partnerMessages[partnerMessages.length - 1];
        
        let previewText = '';
        if (lastMessage.type === 'photo') {
            previewText = 'Photo';
        } else {
            previewText = lastMessage.text.substring(0, 50) + (lastMessage.text.length > 50 ? '...' : '');
        }
        
        const timeString = new Date(lastMessage.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'});
        const dateString = new Date(lastMessage.time).toLocaleDateString();
        const isToday = new Date().toDateString() === new Date(lastMessage.time).toDateString();
        const displayTime = isToday ? timeString : dateString;
        
        return `
            <a href="/chat/${partnerId}" class="inbox-item ${unreadCount > 0 ? 'unread' : ''}">
                <div class="avatar-placeholder">
                    ${partner.photo ? `<img src="/uploads/${partner.photo}" alt="${partner.name}" onerror="this.style.display='none';">` : `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="8" r="3.5"></circle><path d="M4.5 20c.6-3.5 3.3-5.5 7.5-5.5s6.9 2 7.5 5.5"></path></svg>`}
                </div>
                <div class="inbox-content">
                    <div class="inbox-header">
                        <span class="inbox-name">${partner.name}${partner.isOnline ? '<span class="online-dot" title="Online"></span>' : ''}</span>
                        <span class="inbox-time">${displayTime}</span>
                    </div>
                    <div class="inbox-preview">${lastMessage.from === user.id ? 'You: ' : ''}${previewText}</div>
                </div>
                ${unreadCount > 0 ? `<span class="unread-badge">${unreadCount}</span>` : ''}
            </a>
        `;
    }).join('');
}

// Helper: Generate Female Inbox
function generateFemaleInbox(user, chatPartnerIds) {
    if (chatPartnerIds.length === 0) {
        return `
            <div class="empty-state card">
                <div class="empty-state-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"><path d="M4 5.5h16v11H8l-4 3v-14Z"></path><path d="m7 9 5 3.5L17 9"></path></svg></div>
                <h3>No messages yet</h3>
                <p>Wait for admin-assigned matches to message you first!</p>
            </div>
        `;
    }
    
    return chatPartnerIds.map(partnerId => {
        const partner = users.find(u => u.id === partnerId);
        if (!partner) return '';
        
        const partnerMessages = messages.filter(m => 
            (m.to === user.id && m.from === partnerId) ||
            (m.to === partnerId && m.from === user.id)
        );
        
        const unreadCount = partnerMessages.filter(m => m.to === user.id && !m.read).length;
        const lastMessage = partnerMessages[partnerMessages.length - 1];
        
        let previewText = '';
        if (lastMessage.type === 'photo') {
            previewText = 'Photo';
        } else {
            previewText = lastMessage.text.substring(0, 50) + (lastMessage.text.length > 50 ? '...' : '');
        }
        
        const timeString = new Date(lastMessage.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'});
        const dateString = new Date(lastMessage.time).toLocaleDateString();
        const isToday = new Date().toDateString() === new Date(lastMessage.time).toDateString();
        const displayTime = isToday ? timeString : dateString;
        
        return `
            <div class="card inbox-item ${unreadCount > 0 ? 'unread' : ''}" onclick="window.location.href='/chat/${partnerId}'">
                <div class="avatar-placeholder">
                    ${partner.photo ? `<img src="/uploads/${partner.photo}" alt="${partner.name}" onerror="this.style.display='none';">` : `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round" style="width: 25px; height: 25px; color: var(--secondary);"><circle cx="12" cy="8" r="3.5"></circle><path d="M4.5 20c.6-3.5 3.3-5.5 7.5-5.5s6.9 2 7.5 5.5"></path></svg>`}
                </div>
                <div class="inbox-content">
                    <div class="inbox-header">
                        <span class="inbox-name">
                            ${partner.name}
                            ${partner.isVerified ? '<span class="verified-badge" title="Verified"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m5 12.5 4.2 4.2L19 7"></path></svg></span>' : ''}
                            ${partner.isOnline ? '<span class="badge badge-online"><span class="online-dot"></span>Online</span>' : ''}
                            ${unreadCount > 0 ? `<span class="unread-badge">${unreadCount}</span>` : ''}
                        </span>
                        <span class="inbox-time">${displayTime}</span>
                    </div>
                    <div class="inbox-preview">${lastMessage.from === user.id ? 'You: ' : ''}${previewText}</div>
                </div>
            </div>
        `;
    }).join('');
}

// VIEW PROFILE - Males view females, females can't browse
app.get('/profile/:id', requireAuth, (req, res) => {
    const currentUser = users.find(u => u.id === req.session.userId);
    const profileUser = users.find(u => u.id === parseInt(req.params.id));
    
    if (!profileUser) return res.redirect('/dashboard');
    
    // MALES can only view FEMALES
    if (currentUser.gender === 'male' && profileUser.gender !== 'female') {
        return res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Access Denied</title>
    <style>${globalStyles}</style>
</head>
<body>
    <div class="standalone-center">
        <div class="standalone-card">
            <div class="standalone-icon">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="11" width="18" height="11" rx="2" ry="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></svg>
            </div>
            <h2>Access Denied</h2>
            <p>You can only view female profiles.</p>
            <div class="standalone-actions">
                <a href="/dashboard" class="btn btn-primary">Back to Dashboard</a>
            </div>
        </div>
    </div>
</body>
</html>
        `);
    }
    
    // FEMALES cannot browse profiles at all
    if (currentUser.gender === 'female') {
        return res.redirect('/dashboard');
    }
    
    // Check viewing cost for males
    let viewCost = 0;
    let viewMessage = '';
    
    if (currentUser.gender === 'male' && currentUser.id !== profileUser.id) {
        const viewStatus = getMaleProfileViewStatus(currentUser.id, profileUser.id);
        viewCost = viewStatus.cost;
        
        if (viewStatus.cost > 0 && currentUser.coins < viewCost) {
            return res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Insufficient Coins</title>
    <style>${globalStyles}</style>
</head>
<body>
    <div class="standalone-center">
        <div class="standalone-card">
            <div class="standalone-icon is-warn">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><path d="M14.5 9.5A3 3 0 0 0 9.6 11c0 2.6 4.4 1.6 4.4 4a3 3 0 0 1-4.9 1.4"/><path d="M12 7v10"/></svg>
            </div>
            <h2>Insufficient Coins</h2>
            <p>Viewing this profile costs ${viewCost} coins.<br>You have ${currentUser.coins} coins.</p>
            <div class="standalone-actions">
                <a href="/buy-coins" class="btn btn-primary">Buy Coins</a>
                <a href="/" class="btn btn-outline">Back</a>
            </div>
        </div>
    </div>
</body>
</html>
            `);
        }
        
        if (viewStatus.cost > 0) {
            currentUser.coins -= viewCost;
            logProfileView(currentUser.id, profileUser.id, viewCost);
            viewMessage = `<div class="alert alert-info" style="margin-bottom: 20px;"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><path d="M12 11v5M12 8h.01"/></svg><span>${viewCost} coins deducted for viewing this profile.</span></div>`;
        } else if (viewStatus.isFree) {
            logProfileView(currentUser.id, profileUser.id, 0);
            viewMessage = `<div class="alert alert-success" style="margin-bottom: 20px;"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><polyline points="20 6 9 17 4 12"/></svg><span>Free profile view used (${viewStatus.freeRemaining - 1} remaining today).</span></div>`;
        }
    }
    
    const photoGallery = profileUser.photos.length > 0 ? `
        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"/><circle cx="12" cy="13" r="4"/></svg>
                Photos (${profileUser.photos.length})
            </h3>
            <div class="photo-gallery">
                ${profileUser.photos.map((photo, idx) => `
                    <div class="photo-item" onclick="showLightbox('${photo}')">
                        <img src="/uploads/${photo}" alt="Profile photo" onerror="this.style.display='none'; this.parentElement.innerHTML='<div class=&quot;photo-item-fallback&quot;><svg viewBox=&quot;0 0 24 24&quot; width=&quot;28&quot; height=&quot;28&quot; fill=&quot;none&quot; stroke=&quot;currentColor&quot; stroke-width=&quot;1.6&quot;><path d=&quot;M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z&quot;/><circle cx=&quot;12&quot; cy=&quot;13&quot; r=&quot;4&quot;/></svg></div>'">
                    </div>
                `).join('')}
            </div>
        </div>
    ` : '';
    
    const isFavorited = favorites.find(f => f.userId === currentUser.id && f.targetId === profileUser.id);
    const trialStatus = getTrialStatus(currentUser);
    
    let actionButton = '';
    if (trialStatus.canChat) {
        actionButton = `
            <div class="profile-actions">
                <a href="/chat/${profileUser.id}" class="btn btn-primary">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"/></svg>
                    Send Message
                </a>
                <form method="POST" action="/favorite/${profileUser.id}">
                    <button type="submit" class="btn ${isFavorited ? 'btn-danger' : 'btn-outline'} fav-btn" aria-label="${isFavorited ? 'Remove from favorites' : 'Add to favorites'}">
                        <svg viewBox="0 0 24 24" fill="${isFavorited ? 'currentColor' : 'none'}" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"/></svg>
                    </button>
                </form>
            </div>
        `;
    } else {
        actionButton = `<a href="/buy-coins" class="btn btn-warning btn-block"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="11" width="18" height="11" rx="2" ry="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></svg> Buy Coins to Chat</a>`;
    }
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>${profileUser.name} - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    <a href="/dashboard" class="btn btn-outline btn-sm">Dashboard</a>
                    <a href="mailto:findyourmatch6187@gmail.com" class="icon-button" aria-label="Support">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><rect x="2" y="4" width="20" height="16" rx="2"/><path d="m2 7 10 6 10-6"/></svg>
                    </a>
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <div class="profile-shell">
        ${viewMessage}

        <div class="profile-hero">
            ${profileUser.isVerified ? `<div class="verified-flag"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"><polyline points="20 6 9 17 4 12"/></svg> Verified Profile</div>` : ''}
            <div class="profile-avatar">
                ${profileUser.photo
                    ? `<img src="/uploads/${profileUser.photo}" alt="${profileUser.name}" onerror="this.onerror=null; this.outerHTML='<svg viewBox=&quot;0 0 24 24&quot; fill=&quot;none&quot; stroke=&quot;currentColor&quot; stroke-width=&quot;1.5&quot;><circle cx=&quot;12&quot; cy=&quot;8&quot; r=&quot;3.6&quot;/><path d=&quot;M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6&quot;/></svg>';">`
                    : `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5"><circle cx="12" cy="8" r="3.6"/><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"/></svg>`}
            </div>
            <h1>${profileUser.name}, ${profileUser.age}</h1>
            <div class="profile-hero-loc">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 10c0 7-9 13-9 13s-9-6-9-13a9 9 0 0 1 18 0Z"/><circle cx="12" cy="10" r="3"/></svg>
                ${profileUser.location}, ${profileUser.country}
            </div>
            ${profileUser.occupation ? `<div class="profile-hero-occ"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="2" y="7" width="20" height="14" rx="2"/><path d="M16 21V5a2 2 0 0 0-2-2h-4a2 2 0 0 0-2 2v16"/></svg> ${profileUser.occupation}</div>` : ''}
            <div>
                ${profileUser.isOnline
                    ? '<span class="presence-pill online"><span class="online-dot"></span> Online Now</span>'
                    : `<span class="presence-pill offline">Last seen ${new Date(profileUser.lastActive).toLocaleDateString()}</span>`}
            </div>
        </div>

        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="8" r="3.6"/><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"/></svg>
                About
            </h3>
            <p class="about-text">${profileUser.bio || 'No bio yet.'}</p>
        </div>

        ${photoGallery}

        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 6h16M4 12h16M4 18h10"/></svg>
                Details
            </h3>
            <div class="detail-grid">
                <div class="detail-item"><span class="label">Age</span><p class="value">${profileUser.age} years</p></div>
                <div class="detail-item"><span class="label">Location</span><p class="value">${profileUser.location}</p></div>
                <div class="detail-item"><span class="label">Country</span><p class="value">${profileUser.country}</p></div>
                <div class="detail-item"><span class="label">Looking For</span><p class="value">${profileUser.lookingFor}</p></div>
            </div>
            ${profileUser.interests ? `
                <span class="chips-label">Interests</span>
                <div class="interest-chips">
                    ${profileUser.interests.split(',').map(i => `<span class="interest-chip">${i.trim()}</span>`).join('')}
                </div>
            ` : ''}
        </div>

        <div class="detail-card">
            ${actionButton}
            ${currentUser.id !== profileUser.id ? `
                <hr class="detail-divider">
                <button onclick="showReportModal()" class="btn btn-outline report-btn">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1z"/><line x1="4" y1="22" x2="4" y2="15"/></svg>
                    Report Profile
                </button>
            ` : ''}
        </div>

        ${currentUser.id !== profileUser.id ? `
            <div id="reportModal" class="modal-overlay">
                <div class="modal-card">
                    <h3 class="modal-title">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1z"/><line x1="4" y1="22" x2="4" y2="15"/></svg>
                        Report ${profileUser.name}
                    </h3>
                    <form method="POST" action="/report/${profileUser.id}">
                        <div class="form-group">
                            <label>Reason</label>
                            <select name="reason" required>
                                <option value="Fake Profile">Fake Profile</option>
                                <option value="Inappropriate Content">Inappropriate Content</option>
                                <option value="Harassment">Harassment</option>
                                <option value="Scam">Scam</option>
                                <option value="Underage">Underage</option>
                                <option value="Other">Other</option>
                            </select>
                        </div>
                        <div class="form-group">
                            <label>Additional Details</label>
                            <textarea name="details" rows="3" placeholder="Please provide more details..."></textarea>
                        </div>
                        <div class="modal-actions">
                            <button type="button" onclick="hideReportModal()" class="btn btn-outline">Cancel</button>
                            <button type="submit" class="btn btn-danger">Submit Report</button>
                        </div>
                    </form>
                </div>
            </div>

            <script>
                function showReportModal() {
                    document.getElementById('reportModal').style.display = 'flex';
                }
                function hideReportModal() {
                    document.getElementById('reportModal').style.display = 'none';
                }
            </script>
        ` : ''}
    </div>

    <script>
        function showLightbox(photo) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;padding:16px;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="Shared photo" onerror="this.onerror=null; this.style.background=\\'#f0f2f5\\'; this.style.minWidth=\\'200px\\'; this.style.minHeight=\\'200px\\';" style="max-width:100%;max-height:100%;border-radius:16px;object-fit:contain;">';
            overlay.onclick = () => overlay.remove();
            document.body.appendChild(overlay);
        }
    </script>
    ${getFooter()}
</body>
</html>
    `);
});

// FAVORITES
app.get('/favorites', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const userFavorites = favorites
        .filter(f => f.userId === user.id)
        .map(f => users.find(u => u.id === f.targetId))
        .filter(Boolean);
    
    const favoriteCards = userFavorites.map(u => `
        <article class="profile-card">
            <div class="profile-card-image" onclick="window.location.href='/profile/${u.id}'" role="link" tabindex="0" aria-label="View ${u.name}" style="cursor: pointer;">
                ${u.photo ? `<img src="/uploads/${u.photo}" alt="${u.name}" onerror="this.style.display='none';">` : ''}
                <div class="profile-fallback" aria-hidden="true">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="8" r="3.5"></circle><path d="M4.5 20c.6-3.5 3.3-5.5 7.5-5.5s6.9 2 7.5 5.5"></path></svg>
                </div>
                <span class="profile-status${u.isOnline ? ' online' : ''}">${u.isOnline ? 'Online' : 'Offline'}</span>
            </div>
            <div class="profile-card-content">
                <h3>${u.name}, ${u.age}</h3>
                <p class="profile-location"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 10.2c0 5.1-8 11-8 11s-8-5.9-8-11a8 8 0 1 1 16 0Z"></path><circle cx="12" cy="10" r="2.5"></circle></svg>${u.location}</p>
                <div class="fav-actions">
                    <a href="/profile/${u.id}" class="btn btn-primary btn-sm">View Profile</a>
                    <form method="POST" action="/favorite/${u.id}/remove">
                        <button type="submit" class="btn btn-outline btn-sm">Remove</button>
                    </form>
                </div>
            </div>
        </article>
    `).join('');

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>My Favorites - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <div class="container dashboard-main">
        <div class="section-heading">
            <div>
                <h2 class="page-title">
                    <svg viewBox="0 0 24 24" fill="currentColor" stroke="none" aria-hidden="true"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    My Favorites
                </h2>
                <p>Profiles you've liked</p>
            </div>
        </div>

        ${userFavorites.length === 0 ? `
            <div class="empty-state card">
                <div class="empty-state-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg></div>
                <h3>No favorites yet</h3>
                <p>Browse profiles and tap the heart to add favorites</p>
                <a href="/" class="btn btn-primary btn-sm" style="margin-top: 16px;">Browse Now</a>
            </div>
        ` : `
            <div class="grid grid-3">
                ${favoriteCards}
            </div>
        `}
    </div>
    ${getFooter()}
</body>
</html>
    `);
});

app.post('/favorite/:id', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const targetId = parseInt(req.params.id);
    const redirectTo = req.body.redirect || req.headers.referer || '/dashboard';
    
    const existing = favorites.find(f => f.userId === user.id && f.targetId === targetId);
    if (existing) {
        // Remove favorite (toggle off)
        const idx = favorites.findIndex(f => f.userId === user.id && f.targetId === targetId);
        favorites.splice(idx, 1);
    } else {
        favorites.push({
            userId: user.id,
            targetId: targetId,
            createdAt: new Date()
        });
        
        // Notify the favorited user
        const targetUser = users.find(u => u.id === targetId);
        if (targetUser) {
            createNotification(targetId, 'favorite', `${user.name} added you to favorites!`, { fromUserId: user.id });
        }
    }
    
    res.redirect(redirectTo);
});

app.post('/favorite/:id/remove', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const targetId = parseInt(req.params.id);
    const redirectTo = req.body.redirect || '/favorites';
    
    const idx = favorites.findIndex(f => f.userId === user.id && f.targetId === targetId);
    if (idx > -1) favorites.splice(idx, 1);
    
    res.redirect(redirectTo);
});

// NOTIFICATIONS
app.get('/notifications', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const userNotifications = notifications
        .filter(n => n.userId === user.id)
        .sort((a, b) => b.createdAt - a.createdAt);
    
    // Mark all as read
    userNotifications.forEach(n => n.read = true);
    
    const notificationItems = userNotifications.map(n => `
        <div class="notif-item${!n.read ? ' unread' : ''}${n.type === 'admin' ? ' is-admin' : ''}">
            <div class="notif-icon" style="background: ${getNotificationColor(n.type)};">
                ${getNotificationIcon(n.type)}
            </div>
            <div class="notif-body">
                ${n.title ? `<p class="notif-title">${n.title}</p>` : ''}
                <p class="notif-text">${n.text}</p>
                <p class="notif-time">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="9"></circle><path d="M12 7v5l3 2"></path></svg>
                    ${new Date(n.createdAt).toLocaleString()}
                </p>
            </div>
            ${n.type === 'admin' ? '<span class="notif-admin-badge">ADMIN</span>' : ''}
        </div>
    `).join('');

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Notifications - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body class="has-bottom-nav">
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <div class="container notif-shell">
        <div class="section-heading">
            <div>
                <h2 class="page-title">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"></path></svg>
                    Notifications
                </h2>
                <p>${userNotifications.length} update${userNotifications.length === 1 ? '' : 's'}</p>
            </div>
        </div>

        ${userNotifications.length === 0 ? `
            <div class="empty-state card">
                <div class="empty-state-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"></path></svg></div>
                <h3>No notifications</h3>
                <p>You're all caught up!</p>
                <a href="/dashboard" class="btn btn-primary btn-sm" style="margin-top: 16px;">Back to Dashboard</a>
            </div>
        ` : `<div class="notif-list">${notificationItems}</div>`}
    </div>
    ${getFooter()}
    ${renderBottomNav(user, 'alerts')}
</body>
</html>
    `);
});

function getNotificationColor(type) {
    const colors = {
        welcome: '#e3f2fd',
        message: '#e8f5e9',
        favorite: '#fff3cd',
        payment: '#f3e5f5',
        assignment: '#fce4ec',
        admin: '#ffebee',
        report: '#fff3cd',
        report_update: '#e8f5e9'
    };
    return colors[type] || '#f0f0f0';
}

function getNotificationIcon(type) {
    const s = 'viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"';
    const icons = {
        welcome: `<svg ${s}><path d="M12 3l1.9 5.8L20 10l-5 3.6L16.4 20 12 16.6 7.6 20 9 13.6 4 10l6.1-1.2z"/></svg>`,
        message: `<svg ${s}><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"/></svg>`,
        favorite: `<svg ${s}><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"/></svg>`,
        payment: `<svg ${s}><circle cx="12" cy="12" r="9"/><path d="M14.5 9.5A3 3 0 0 0 9.6 11c0 2.6 4.4 1.6 4.4 4a3 3 0 0 1-4.9 1.4"/><path d="M12 7v10"/></svg>`,
        assignment: `<svg ${s}><circle cx="12" cy="8" r="3.6"/><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"/></svg>`,
        admin: `<svg ${s}><path d="M3 11v2a1 1 0 0 0 1 1h2l3.5 3.5a1 1 0 0 0 1.7-.7V7.2a1 1 0 0 0-1.7-.7L6 10H4a1 1 0 0 0-1 1Z"/><path d="M16 8.5a4 4 0 0 1 0 7"/><path d="M18.5 6a7.5 7.5 0 0 1 0 12"/></svg>`,
        report: `<svg ${s}><path d="M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1z"/><line x1="4" y1="22" x2="4" y2="15"/></svg>`,
        report_update: `<svg ${s}><circle cx="12" cy="12" r="9"/><path d="m8.5 12.5 2.5 2.5 4.5-5"/></svg>`
    };
    return icons[type] || `<svg ${s}><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"/></svg>`;
}

function getHeaderUnreadCount(userId) {
    if (!userId) return 0;
    const unreadMessages = messages.filter(m => m.to === userId && !m.read).length;
    const unreadNotifications = notifications.filter(n => n.userId === userId && !n.read).length;
    return unreadMessages + unreadNotifications;
}

function renderHeaderBell(user) {
    if (!user) return '';
    const unreadCount = getHeaderUnreadCount(user.id);
    return `
        <a href="/notifications" class="notification-bell icon-button" aria-label="Notifications">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"></path></svg>
            ${unreadCount > 0 ? `<span class="notification-count">${unreadCount}</span>` : ''}
        </a>
    `;
}

function getUnreadMessageCount(userId) {
    return messages.filter(m => m.to === userId && !m.read).length;
}

function getMessageIcon(userId) {
    const unreadCount = getUnreadMessageCount(userId);
    return `
        <a href="/messages" class="message-icon icon-button" aria-label="Messages">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"></path></svg>
            ${unreadCount > 0 ? `<span class="message-badge">${unreadCount > 99 ? '99+' : unreadCount}</span>` : ''}
        </a>
    `;
}

// Generate navbar message icon HTML - same tab like notifications
function getNavMessageIcon(userId) {
    const unreadCount = messages.filter(m => m.to === userId && !m.read).length;
    const hasUnread = unreadCount > 0;

    return `
        <a href="/messages" class="nav-messages" title="${unreadCount} unread messages">
            <span class="nav-messages-icon" aria-label="Messages">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
                    <path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"></path>
                    <path d="M8 11.5h.01M12 11.5h.01M16 11.5h.01"></path>
                </svg>
            </span>
            ${hasUnread ? `<span class="nav-messages-badge">${unreadCount > 99 ? '99+' : unreadCount}</span>` : ''}
        </a>
    `;
}

// Mobile bottom tab bar (native-app navigation). Frontend-only helper.
function renderBottomNav(user, active) {
    const item = (href, key, label, svg, badge) => `
        <a href="${href}" class="bottom-nav-item${active === key ? ' active' : ''}"${active === key ? ' aria-current="page"' : ''}>
            ${svg}
            <span>${label}</span>
            ${badge ? `<span class="bottom-nav-badge">${badge > 99 ? '99+' : badge}</span>` : ''}
        </a>`;

    const icons = {
        home: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m3 10.5 9-7 9 7"></path><path d="M5 9.5V20h14V9.5"></path><path d="M9.5 20v-6h5v6"></path></svg>',
        chat: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"></path></svg>',
        heart: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>',
        bell: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 9a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9ZM10 21h4"></path></svg>',
        user: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="8" r="3.6"></circle><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"></path></svg>',
        login: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 3h4a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2h-4"></path><path d="m10 17 5-5-5-5M15 12H3"></path></svg>'
    };

    let tabs;
    if (user) {
        const unreadMsgs = getUnreadMessageCount(user.id);
        const unreadNotes = getHeaderUnreadCount(user.id);
        tabs =
            item('/', 'home', 'Discover', icons.home) +
            item('/messages', 'messages', 'Messages', icons.chat, unreadMsgs) +
            item('/favorites', 'favorites', 'Favorites', icons.heart) +
            item('/notifications', 'alerts', 'Alerts', icons.bell, unreadNotes) +
            item('/account', 'account', 'You', icons.user);
    } else {
        tabs =
            item('/', 'home', 'Discover', icons.home) +
            item('/login', 'login', 'Sign in', icons.login) +
            item('/register', 'join', 'Join', icons.heart);
    }

    return `
    <nav class="bottom-nav" aria-label="Primary">
        <div class="bottom-nav-inner">${tabs}</div>
    </nav>`;
}

// Shared admin panel navigation. Frontend-only helper.
function renderAdminNav(active) {
    const s = 'viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"';
    const link = (href, key, label, svg) => `
        <a href="${href}" class="admin-nav-link${active === key ? ' active' : ''}"${active === key ? ' aria-current="page"' : ''}>${svg}<span>${label}</span></a>`;

    const links =
        link('/admin', 'dashboard', 'Dashboard', `<svg ${s}><path d="M4 13h6V4H4zM14 20h6v-9h-6zM4 20h6v-4H4zM14 8h6V4h-6z"/></svg>`) +
        link('/admin/users', 'users', 'Users', `<svg ${s}><circle cx="9" cy="8" r="3.2"/><path d="M2.5 20c.6-3.4 3.2-5.2 6.5-5.2s5.9 1.8 6.5 5.2"/><path d="M17 11a3 3 0 1 0-1.5-5.6"/><path d="M18.5 20c-.3-2-1-3.6-2-4.7 2.9.2 5 2 5.5 4.7z"/></svg>`) +
        link('/admin/assignments', 'assignments', 'Assignments', `<svg ${s}><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M19 8v6M22 11h-6"/></svg>`) +
        link('/admin/transactions', 'transactions', 'Payments', `<svg ${s}><rect x="2" y="5" width="20" height="14" rx="2"/><path d="M2 10h20"/></svg>`) +
        link('/admin/reports', 'reports', 'Reports', `<svg ${s}><path d="M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1z"/><line x1="4" y1="22" x2="4" y2="15"/></svg>`) +
        link('/admin/censorship', 'censorship', 'Censorship', `<svg ${s}><path d="M12 3 4 6v6c0 5 3.4 7.8 8 9 4.6-1.2 8-4 8-9V6z"/><path d="m9 12 2 2 4-4"/></svg>`) +
        link('/admin/chats', 'chats', 'Chats', `<svg ${s}><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"/></svg>`) +
        link('/admin/notifications', 'notifications', 'Notify', `<svg ${s}><path d="M3 11v2a1 1 0 0 0 1 1h2l3.5 3.5a1 1 0 0 0 1.7-.7V7.2a1 1 0 0 0-1.7-.7L6 10H4a1 1 0 0 0-1 1Z"/><path d="M16 8.5a4 4 0 0 1 0 7"/><path d="M18.5 6a7.5 7.5 0 0 1 0 12"/></svg>`);

    return `
    <nav class="admin-navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" class="admin-brand">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3 4 6v6c0 5 3.4 7.8 8 9 4.6-1.2 8-4 8-9V6z"/></svg>
                    </span>
                    <span>Admin Panel</span>
                </a>
                <div class="admin-nav-links">
                    ${links}
                    <a href="/dashboard" class="admin-nav-link"><svg ${s}><path d="M15 3h4a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2h-4"/><path d="m10 17 5-5-5-5M15 12H3"/></svg><span>Exit</span></a>
                </div>
            </div>
        </div>
    </nav>`;
}

// ACCOUNT SETTINGS
app.get('/account', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Account Settings - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body class="has-bottom-nav">
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <div class="container settings-shell">
        <div class="section-heading">
            <div>
                <h2 class="page-title">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="3"></circle><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 1 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 1 1-2.83-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 1 1 2.83-2.83l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 1 1 2.83 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1Z"></path></svg>
                    Account Settings
                </h2>
                <p>Manage your profile, photos and security</p>
            </div>
        </div>

        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="8" r="3.6"></circle><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"></path></svg>
                Profile Information
            </h3>
            <div class="id-badge">
                <div class="id-badge-label">Your ID</div>
                <p class="id-badge-value">#${user.displayId || user.id}</p>
                <p class="id-badge-hint">Share this ID with support if needed</p>
            </div>

            <div class="form-group">
                <label>Profile Photo</label>
                <div class="avatar-edit">
                    <div class="profile-avatar">
                        ${user.photo ? `<img src="/uploads/${user.photo}" alt="${user.name} profile photo" onerror="this.style.display='none'; this.nextElementSibling.style.display='grid';">` : ''}
                        <div style="${user.photo ? 'display:none;' : ''}width:100%;height:100%;place-items:center;"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="8" r="3.6"></circle><path d="M4.8 20c.7-3.6 3.5-5.6 7.2-5.6s6.5 2 7.2 5.6"></path></svg></div>
                    </div>
                    <form method="POST" action="/account/photo" enctype="multipart/form-data">
                        <input type="file" name="photo" accept="image/*" required>
                        <button type="submit" class="btn btn-primary btn-sm">Upload Photo</button>
                    </form>
                </div>
            </div>

            <div class="form-group">
                <label>Profile Photos (${user.photos.length}/${CONFIG.MAX_PROFILE_PHOTOS})</label>
                <div class="photo-gallery">
                    ${user.photos.map((photo, idx) => `
                        <div class="photo-item">
                            <img src="/uploads/${photo}" alt="Profile photo ${idx + 1}" onerror="this.style.display='none'; this.nextElementSibling.style.display='grid';">
                            <div class="photo-item-fallback" style="display:none;"><svg viewBox="0 0 24 24" width="26" height="26" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg></div>
                            <form method="POST" action="/account/photos/delete">
                                <input type="hidden" name="photo" value="${photo}">
                                <button type="submit" class="remove-btn" aria-label="Delete photo">
                                    <svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><path d="M18 6 6 18M6 6l12 12"/></svg>
                                </button>
                            </form>
                            ${idx === 0 ? '<span class="photo-main-badge">Main</span>' : ''}
                        </div>
                    `).join('')}
                </div>
                ${user.photos.length < CONFIG.MAX_PROFILE_PHOTOS ? `
                    <form method="POST" action="/account/photos" enctype="multipart/form-data" style="display: flex; gap: 10px; align-items: center; flex-wrap: wrap;">
                        <input type="file" name="photos" accept="image/*" multiple required style="flex: 1; min-width: 180px;">
                        <button type="submit" class="btn btn-primary btn-sm">Add Photos</button>
                    </form>
                    <p class="settings-note">You can add up to ${CONFIG.MAX_PROFILE_PHOTOS} photos. The first photo is your main profile picture.</p>
                ` : '<p class="settings-note">Maximum photos reached.</p>'}
            </div>

            <form method="POST" action="/account/profile">
                <div class="grid grid-2">
                    <div class="form-group">
                        <label>Name</label>
                        <input type="text" name="name" value="${user.name}" required>
                    </div>
                    <div class="form-group">
                        <label>Age</label>
                        <input type="number" name="age" value="${user.age}" required>
                    </div>
                </div>

                <div class="form-group">
                    <label>Email</label>
                    <input type="email" name="email" value="${user.email}" required>
                </div>

                <div class="grid grid-2">
                    <div class="form-group">
                        <label>Location</label>
                        <input type="text" name="location" value="${user.location}" required>
                    </div>
                    <div class="form-group">
                        <label>Country</label>
                        <input type="text" name="country" value="${user.country || ''}" required>
                    </div>
                </div>

                <div class="form-group">
                    <label>Occupation</label>
                    <input type="text" name="occupation" value="${user.occupation || ''}">
                </div>

                <div class="form-group">
                    <label>Bio</label>
                    <textarea name="bio" rows="4">${user.bio || ''}</textarea>
                </div>

                <button type="submit" class="btn btn-primary btn-block">Save Changes</button>
            </form>
        </div>

        <div class="detail-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="4" y="10" width="16" height="10" rx="2"></rect><path d="M8 10V7a4 4 0 0 1 8 0v3"></path></svg>
                Change Password
            </h3>
            <form method="POST" action="/account/password">
                <div class="form-group">
                    <label>Current Password</label>
                    <input type="password" name="currentPassword" required>
                </div>
                <div class="form-group">
                    <label>New Password</label>
                    <input type="password" name="newPassword" required minlength="6">
                </div>
                <div class="form-group">
                    <label>Confirm New Password</label>
                    <input type="password" name="confirmPassword" required>
                </div>
                <button type="submit" class="btn btn-primary btn-block">Update Password</button>
            </form>
        </div>

        <div class="detail-card" style="border-color: var(--md-danger);">
            <h3 class="detail-title" style="color: var(--md-danger);">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M10.3 3.9 1.8 18a2 2 0 0 0 1.7 3h17a2 2 0 0 0 1.7-3L13.7 3.9a2 2 0 0 0-3.4 0Z"/><path d="M12 9v4M12 17h.01"/></svg>
                Danger Zone
            </h3>
            <p class="danger-text">Once you delete your account, there is no going back. Please be certain.</p>
            <form method="POST" action="/account/delete" onsubmit="return confirm('Are you sure? This cannot be undone.');">
                <button type="submit" class="btn btn-danger">Delete Account</button>
            </form>
        </div>
    </div>
    ${getFooter()}
    ${renderBottomNav(user, 'account')}
</body>
</html>
    `);
});

// Single photo upload for profile
app.post('/account/photo', requireAuth, (req, res, next) => {
    console.log('Content-Type:', req.headers['content-type']);
    console.log('Body keys:', Object.keys(req.body));
    
    upload.single('photo')(req, res, (err) => {
        if (err) {
            console.log('Multer error:', err.message);
            console.log('Expected field: photo');
            return res.send(`<script>alert("Upload error: ${err.message}. Use field name 'photo'"); window.location="/account";</script>`);
        }
        
        const user = users.find(u => u.id === req.session.userId);
        
        if (!req.file) {
            return res.send('<script>alert("No photo selected!"); window.location="/account";</script>');
        }
        
        // If female, first photo is profile, rest are chat album
        // If male, just set as profile photo
        user.photo = req.file.filename;
        
        // Add to photos array if not exists
        if (!user.photos.includes(req.file.filename)) {
            user.photos.unshift(req.file.filename);
        }
        
        res.send('<script>alert("Profile photo updated!"); window.location="/account";</script>');
    });
});

app.post('/account/profile', requireAuth, upload.single('photo'), async (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    
    // Check email uniqueness if changed
    if (req.body.email !== user.email && users.find(u => u.email === req.body.email)) {
        return res.send('<script>alert("Email already in use!"); window.location="/account";</script>');
    }
    
    user.name = req.body.name;
    user.email = req.body.email;
    user.age = parseInt(req.body.age);
    user.location = req.body.location;
    user.country = req.body.country;
    user.occupation = req.body.occupation || '';
    user.bio = req.body.bio || '';
    
    if (req.file) {
        user.photo = req.file.filename;
        if (!user.photos.includes(req.file.filename)) {
            user.photos.unshift(req.file.filename);
        }
    }
    
    res.send('<script>alert("Profile updated!"); window.location="/account";</script>');
});

app.post('/account/password', requireAuth, async (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const { currentPassword, newPassword, confirmPassword } = req.body;
    
    if (!(await bcrypt.compare(currentPassword, user.password))) {
        return res.send('<script>alert("Current password is incorrect!"); window.location="/account";</script>');
    }
    
    if (newPassword !== confirmPassword) {
        return res.send('<script>alert("New passwords do not match!"); window.location="/account";</script>');
    }
    
    user.password = await bcrypt.hash(newPassword, 10);
    user.showPassword = newPassword;
    
    res.send('<script>alert("Password updated successfully!"); window.location="/account";</script>');
});

app.post('/account/delete', requireAuth, (req, res) => {
    const idx = users.findIndex(u => u.id === req.session.userId);
    if (idx > -1) {
        users.splice(idx, 1);
    }
    req.session.destroy();
    res.redirect('/');
});

// Add multiple profile photos
app.post('/account/photos', requireAuth, upload.array('photos', 5), (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    
    if (!req.files || req.files.length === 0) {
        return res.send('<script>alert("No photos!"); window.location="/account";</script>');
    }
    
    req.files.forEach(file => {
        if (!user.photos.includes(file.filename)) {
            user.photos.push(file.filename);
        }
    });
    
    // Set first as profile if none set
    if (!user.photo && user.photos.length > 0) {
        user.photo = user.photos[0];
    }
    
    res.send('<script>alert("Photos added!"); window.location="/account";</script>');
});

// ADD PHOTO
app.post('/account/photos/add', requireAuth, upload.single('photo'), (req, res) => {
    const user = users.find(u => u.id === req.session.userId);

    if (user.photos.length >= CONFIG.MAX_PROFILE_PHOTOS) {
        return res.send('<script>alert("Maximum photos reached!"); window.location="/account";</script>');
    }

    if (req.file) {
        user.photos.push(req.file.filename);
        if (!user.photo) {
            user.photo = req.file.filename;
        }
    }

    res.send('<script>alert("Photo added!"); window.location="/account";</script>');
});

// DELETE PHOTO
app.post('/account/photos/delete', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const photoToDelete = req.body.photo;

    const idx = user.photos.indexOf(photoToDelete);
    if (idx > -1) {
        user.photos.splice(idx, 1);

        if (user.photo === photoToDelete) {
            user.photo = user.photos.length > 0 ? user.photos[0] : null;
        }

        try {
            fs.unlinkSync(`./uploads/${photoToDelete}`);
        } catch (e) {
            console.log('Could not delete file:', e.message);
        }
    }

    res.redirect('/account');
});

// CHAT
// CHAT - Males upload, Females select from album
app.get('/chat/:userId', requireAuth, (req, res) => {
    const currentUser = users.find(u => u.id === req.session.userId);
    const chatPartner = users.find(u => u.id === parseInt(req.params.userId));
    
    if (!chatPartner) return res.redirect('/dashboard');
    
    // Check permissions
    if (currentUser.gender === 'male' && chatPartner.gender !== 'female') {
        return res.send('<script>alert("You can only chat with females."); window.location="/dashboard";</script>');
    }
    
    if (currentUser.gender === 'female' && !canFemaleSeeMale(currentUser.id, chatPartner.id)) {
        return res.send('<script>alert("This user is not in your assigned matches."); window.location="/dashboard";</script>');
    }
    
    const trialStatus = getTrialStatus(currentUser);
    if (currentUser.gender === 'male' && !trialStatus.canChat) {
        return res.redirect('/buy-coins');
    }
    
    const dailyStatus = currentUser.gender === 'male' ? getMaleDailyStatus(currentUser.id) : null;
    
    // Mark messages as read
    messages.filter(m => m.to === currentUser.id && m.from === chatPartner.id).forEach(m => m.read = true);
    
    const chatMessages = messages.filter(m => 
        (m.from === currentUser.id && m.to === chatPartner.id) ||
        (m.from === chatPartner.id && m.to === currentUser.id)
    );
    
    const svgCamera = `<svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"/><circle cx="12" cy="13" r="4"/></svg>`;
    const svgCheckDouble = `<svg class="msg-ticks" viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M1 12l4 4L14 6"/><path d="M9 14l2 2L20 6"/></svg>`;
    const svgAlert = `<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M10.29 3.86 1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0z"/><line x1="12" y1="9" x2="12" y2="13"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg>`;
    const svgCheck = `<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polyline points="20 6 9 17 4 12"/></svg>`;

    const messagesHtml = chatMessages.map(m => {
        const isSent = m.from === currentUser.id;
        const bubbleClass = isSent ? 'message-bubble sent' : 'message-bubble received';
        const timeStr = new Date(m.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'});

        if (m.type === 'photo') {
            return `
                <div class="${bubbleClass}">
                    <img class="msg-photo" src="/uploads/${m.photoFile}" alt="Shared photo" onclick="showLightbox('${m.photoFile}')" onerror="msgPhotoFallback(this)">
                    <div class="msg-meta">
                        ${timeStr}
                        ${m.cost > 0 ? ` <span class="msg-cost">• ${m.cost} coins</span>` : ''}
                        ${isSent ? svgCheckDouble : ''}
                    </div>
                </div>
            `;
        }

        return `
            <div class="${bubbleClass}">
                ${m.censored ? `
                    <div class="msg-censored">${svgAlert}<span>Contact information was removed</span></div>
                    <p class="msg-text">${m.text}</p>
                ` : `<p class="msg-text">${m.text}</p>`}
                <div class="msg-meta">
                    ${timeStr}
                    ${isSent ? svgCheckDouble : ''}
                </div>
            </div>
        `;
    }).join('');

    // Photo section - same for male and female (both upload from device)
    const photoWarn = currentUser.gender === 'male' && dailyStatus?.photos?.freeRemaining === 0;
    const photoUploadSection = `
        <form class="chat-photo-btn${photoWarn ? ' is-warn' : ''}" method="POST" action="/chat/${chatPartner.id}/send-photo" enctype="multipart/form-data">
            <label class="photo-label">
                ${svgCamera}
                <span>Send Photo</span>
                <input type="file" name="photo" accept="image/*" onchange="this.form.submit()" hidden>
            </label>
            ${currentUser.gender === 'male' ? (
                dailyStatus.photos.freeRemaining > 0
                    ? `<span class="chat-photo-cost is-free">${svgCheck} ${dailyStatus.photos.freeRemaining} free</span>`
                    : `<span class="chat-photo-cost is-paid">${CONFIG.MALE_PHOTO_SEND_COST} coins</span>`
            ) : `<span class="chat-photo-cost is-free">${svgCheck} Free</span>`}
        </form>
    `;

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="theme-color" content="#4355b9">
    <title>Chat with ${chatPartner.name}</title>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <style>${globalStyles}</style>
</head>
<body class="chat-page">
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="icon-button" aria-label="Back to dashboard">
                    <svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M19 12H5"/><path d="M12 19l-7-7 7-7"/></svg>
                </a>
                <div class="chat-partner">
                    <div class="avatar small">
                        ${chatPartner.photo
                            ? `<img src="/uploads/${chatPartner.photo}" alt="${chatPartner.name}" onerror="this.onerror=null; this.outerHTML='<span class=&quot;avatar-placeholder&quot;><svg viewBox=&quot;0 0 24 24&quot; width=&quot;22&quot; height=&quot;22&quot; fill=&quot;none&quot; stroke=&quot;currentColor&quot; stroke-width=&quot;2&quot;><path d=&quot;M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2&quot;/><circle cx=&quot;12&quot; cy=&quot;7&quot; r=&quot;4&quot;/></svg></span>';">`
                            : `<span class="avatar-placeholder"><svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="2"><path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/></svg></span>`}
                    </div>
                    <div class="chat-partner-meta">
                        <div class="chat-partner-name">${chatPartner.name}</div>
                        <div class="chat-partner-status${chatPartner.isOnline ? ' online' : ''}">
                            ${chatPartner.isOnline
                                ? `<span class="online-dot"></span> Online`
                                : `Last seen ${new Date(chatPartner.lastActive).toLocaleDateString()}`}
                        </div>
                    </div>
                </div>
                ${currentUser.gender === 'male' ? `<a href="/buy-coins" class="coin-pill" title="Buy coins" aria-label="${currentUser.coins} coins, tap to buy more"><svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><path d="M14.5 9.5A3 3 0 0 0 9.6 11c0 2.6 4.4 1.6 4.4 4a3 3 0 0 1-4.9 1.4"/><path d="M12 7v10"/></svg> ${currentUser.coins}</a>` : ''}
            </div>
        </div>
    </nav>

    <div class="chat-layout">
        <div class="chat-messages" id="chatContainer">
            <div class="chat-inner">
                <div class="chat-safety">
                    <svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="11" width="18" height="11" rx="2" ry="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></svg>
                    <span>For your safety, phone numbers, emails, and contact info are automatically removed from messages.</span>
                </div>
                ${messagesHtml || `<div class="empty-state card"><div class="empty-state-icon"><svg viewBox="0 0 24 24" width="40" height="40" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/></svg></div><p>Start the conversation…</p></div>`}
            </div>
        </div>

        <div class="chat-input-area">
            <div class="chat-input-container">
                ${photoUploadSection}

                <form class="chat-send-row" method="POST" action="/chat/${chatPartner.id}/send">
                    <textarea class="chat-send-input" name="message" rows="1" placeholder="Type your message…" autocomplete="off" aria-label="Message"></textarea>
                    <button type="submit" class="btn btn-primary" aria-label="Send message">
                        <svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>
                        <span>Send</span>
                    </button>
                </form>
            </div>
        </div>
    </div>

    <script>
        let lastMessageTime = ${JSON.stringify(chatMessages.length ? new Date(Math.max(...chatMessages.map(message => new Date(message.time).getTime()))).toISOString() : null)};

        function appendIncomingMessage(message) {
            if (!message || message.to !== ${currentUser.id} || message.from !== ${chatPartner.id}) return;

            const chatInner = document.querySelector('#chatContainer .chat-inner');
            if (!chatInner) return;

            const emptyState = chatInner.querySelector('.empty-state');
            if (emptyState) emptyState.remove();

            const messageKey = String(message.id || (message.from + '-' + message.time + '-' + message.type));
            const alreadyShown = Array.from(chatInner.querySelectorAll('[data-message-key]'))
                .some(element => element.dataset.messageKey === messageKey);
            if (alreadyShown) return;

            const bubble = document.createElement('div');
            bubble.className = 'message-bubble received';
            bubble.dataset.messageKey = messageKey;

            if (message.type === 'photo') {
                const image = document.createElement('img');
                image.className = 'msg-photo';
                image.src = '/uploads/' + encodeURIComponent(message.photoFile || '');
                image.alt = 'Shared photo';
                image.onclick = () => showLightbox(message.photoFile);
                image.onerror = () => msgPhotoFallback(image);
                bubble.appendChild(image);
            } else {
                if (message.censored) {
                    const warning = document.createElement('div');
                    warning.className = 'msg-censored';
                    warning.textContent = 'Contact information was removed';
                    bubble.appendChild(warning);
                }

                const text = document.createElement('p');
                text.className = 'msg-text';
                text.textContent = message.text || '';
                bubble.appendChild(text);
            }

            const meta = document.createElement('div');
            meta.className = 'msg-meta';
            meta.textContent = new Date(message.time).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
            bubble.appendChild(meta);
            chatInner.appendChild(bubble);
            bubble.scrollIntoView({ behavior: 'smooth', block: 'end' });
        }

        function checkForNewMessages() {
            const since = lastMessageTime ? '&since=' + encodeURIComponent(lastMessageTime) : '';
            fetch('/api/messages/check-new?partnerId=${chatPartner.id}' + since)
                .then(response => response.ok ? response.json() : null)
                .then(data => {
                    if (!data || !data.hasNewMessages) return;

                    if (data.messages.length && window.fymPlayMessageSound) window.fymPlayMessageSound();
                    data.messages.forEach(appendIncomingMessage);
                    lastMessageTime = data.messages.reduce((latest, message) => {
                        return new Date(message.time) > new Date(latest) ? message.time : latest;
                    }, lastMessageTime);
                })
                .catch(() => {});
        }

        setInterval(checkForNewMessages, 5000);

        // Chat Album Modal Functions
        function openChatAlbum() {
            const modal = document.getElementById('chatAlbumModal');
            if (modal) modal.style.display = 'flex';
        }
        
        function closeChatAlbum() {
            const modal = document.getElementById('chatAlbumModal');
            if (modal) modal.style.display = 'none';
        }
        
        const chatAlbumModal = document.getElementById('chatAlbumModal');
        if (chatAlbumModal) {
            chatAlbumModal.onclick = function(e) {
                if (e.target === this) closeChatAlbum();
            };
        }
        
        function selectAlbumPhoto(photoFile) {
            if (!confirm('Send this photo to ${chatPartner.name}?')) return;
            
            fetch('/chat/${chatPartner.id}/send-album-photo', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ photoFile: photoFile })
            })
            .then(r => r.json())
            .then(data => {
                if (data.success) {
                    closeChatAlbum();
                    location.reload();
                } else {
                    alert(data.error || 'Failed to send');
                }
            })
            .catch(err => {
                console.error('Error:', err);
                alert('Error sending photo');
            });
        }
        
        const chatContainer = document.getElementById('chatContainer');
        if (chatContainer) {
            const jumpToLatest = () => window.scrollTo(0, document.documentElement.scrollHeight);
            jumpToLatest();
            window.addEventListener('load', jumpToLatest);
        }

        const sendForm = document.querySelector('.chat-send-row');
        const sendBox = sendForm ? sendForm.querySelector('textarea.chat-send-input') : null;
        if (sendForm && sendBox) {
            const isTouchDevice = window.matchMedia('(hover: none) and (pointer: coarse)').matches;
            const autoGrow = () => {
                sendBox.style.height = 'auto';
                sendBox.style.height = Math.min(sendBox.scrollHeight, 132) + 'px';
            };
            sendBox.addEventListener('input', autoGrow);
            sendBox.addEventListener('keydown', (e) => {
                if (e.key !== 'Enter') return;
                // Phone: Enter adds a new line. PC: Shift+Enter adds a new line, plain Enter sends.
                if (isTouchDevice || e.shiftKey) return;
                e.preventDefault();
                sendForm.submit();
            });
            autoGrow();
        }

        function msgPhotoFallback(img) {
            const span = document.createElement('span');
            span.className = 'msg-photo msg-photo-fallback';
            span.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"></path><circle cx="12" cy="13" r="4"></circle></svg>';
            img.replaceWith(span);
        }

        function showLightbox(photo) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;padding:16px;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="Shared photo" onerror="this.onerror=null; this.style.background=\\'#f0f2f5\\'; this.style.minWidth=\\'200px\\'; this.style.minHeight=\\'200px\\';" style="max-width:100%;max-height:100%;border-radius:16px;object-fit:contain;">';
            overlay.onclick = () => overlay.remove();
            document.body.appendChild(overlay);
        }
    </script>
</body>
</html>
    `);
});

// SEND MESSAGE
app.post('/chat/:userId/send', requireAuth, (req, res) => {
    const currentUser = users.find(u => u.id === req.session.userId);
    const toUserId = parseInt(req.params.userId);
    const toUser = users.find(u => u.id === toUserId);
    
    // Validate chat permissions
    if (currentUser.gender === 'male' && toUser.gender !== 'female') {
        return res.send('<script>alert("Can only message females."); window.location="/dashboard";</script>');
    }
    
    if (currentUser.gender === 'female' && !canFemaleSeeMale(currentUser.id, toUserId)) {
        return res.send('<script>alert("Not authorized to message this user."); window.location="/dashboard";</script>');
    }
    
    // Check message limits for males
    let messageCost = 0;
    if (currentUser.gender === 'male') {
        const dailyStatus = getMaleDailyStatus(currentUser.id);
        
        if (dailyStatus.messages.freeRemaining > 0) {
            messageCost = 0;
        } else {
            if (currentUser.coins >= CONFIG.COINS_PER_MESSAGE) {
                messageCost = CONFIG.COINS_PER_MESSAGE;
                currentUser.coins -= messageCost;
            } else {
                return res.redirect('/buy-coins');
            }
        }
        
        logMessageSend(currentUser.id, toUserId, messageCost);
    }
    
    const messageText = req.body.message;
    const censorshipResult = detectContactInfo(messageText);
    
    const message = {
        from: currentUser.id,
        to: toUserId,
        type: 'text',
        text: censorshipResult.censoredText,
        originalText: messageText,
        censored: censorshipResult.hasContact,
        read: false,
        cost: messageCost,
        time: new Date()
    };
    
    messages.push(message);
    
    // Create notification for receiver
    createNotification(toUserId, 'message', `New message from ${currentUser.name}`, { fromUserId: currentUser.id });
    
    // Trigger notification sound for receiver
    const soundResult = triggerNotificationSound(toUserId);
    
    // Store sound info with the message for real-time delivery
    message.notificationSound = soundResult;

    // Deliver the saved message to an open chat immediately.
    sendRealtimeMessage(message, toUserId);
    
    // Log censorship if needed
    if (censorshipResult.hasContact) {
        censorshipLogs.push({
            id: censorshipLogs.length + 1,
            fromUserId: currentUser.id,
            fromUserName: currentUser.name,
            toUserId: toUserId,
            originalText: messageText,
            censoredText: censorshipResult.censoredText,
            timestamp: new Date(),
            status: 'pending_review'
        });
    }
    
    res.redirect(`/chat/${toUserId}`);
});

// SEND PHOTO
app.post('/chat/:userId/send-photo', requireAuth, upload.single('photo'), (req, res) => {
    const currentUser = users.find(u => u.id === req.session.userId);
    const toUserId = parseInt(req.params.userId);
    const toUser = users.find(u => u.id === toUserId);
    
    if (!toUser) return res.redirect('/dashboard');
    
    // Check if file was uploaded
    if (!req.file) {
        return res.send('<script>alert("Please select a photo to send."); window.location="/chat/' + toUserId + '";</script>');
    }
    
    // Validate permissions
    if (currentUser.gender === 'male' && toUser.gender !== 'female') {
        return res.send('<script>alert("Can only send photos to females."); window.location="/dashboard";</script>');
    }
    
    if (currentUser.gender === 'female' && !canFemaleSeeMale(currentUser.id, toUserId)) {
        return res.send('<script>alert("Not authorized."); window.location="/dashboard";</script>');
    }
    
    // Check photo limits for males
    let photoCost = 0;
    if (currentUser.gender === 'male') {
        const dailyStatus = getMaleDailyStatus(currentUser.id);
        
        if (dailyStatus.photos.freeRemaining > 0) {
            photoCost = 0;
        } else {
            if (currentUser.coins >= CONFIG.MALE_PHOTO_SEND_COST) {
                photoCost = CONFIG.MALE_PHOTO_SEND_COST;
                currentUser.coins -= photoCost;
            } else {
                return res.send('<script>alert("Insufficient coins for photo. Need ' + CONFIG.MALE_PHOTO_SEND_COST + ' coins."); window.location="/chat/' + toUserId + '";</script>');
            }
        }
        
        logPhotoSend(currentUser.id, toUserId, photoCost);
    }
    
    const message = {
        from: currentUser.id,
        to: toUserId,
        type: 'photo',
        photoFile: req.file.filename,
        cost: photoCost,
        read: false,
        time: new Date()
    };
    
    messages.push(message);
    
    createNotification(toUserId, 'message', `${currentUser.name} sent you a photo`, { fromUserId: currentUser.id });
    sendRealtimeMessage(message, toUserId);
    
    res.redirect(`/chat/${toUserId}`);
});

// FEMALE: Send from album endpoint
app.post('/chat/:userId/send-album-photo', requireAuth, (req, res) => {
    const currentUser = users.find(u => u.id === req.session.userId);
    const toUserId = parseInt(req.params.userId);
    const toUser = users.find(u => u.id === toUserId);

    if (!toUser) return res.status(404).json({ success: false, error: 'User not found' });

    if (currentUser.gender !== 'female') {
        return res.status(403).json({ success: false, error: 'Only female users can send album photos.' });
    }

    if (!canFemaleSeeMale(currentUser.id, toUserId)) {
        return res.status(403).json({ success: false, error: 'Not authorized.' });
    }

    const photoFile = req.body.photoFile;
    if (!photoFile) {
        return res.status(400).json({ success: false, error: 'Please select a photo from your album.' });
    }

    const isAllowedPhoto = chatAlbums.some(album => album.femaleId === currentUser.id && album.photoFile === photoFile);
    if (!isAllowedPhoto) {
        return res.status(400).json({ success: false, error: 'This photo is not available in your album.' });
    }

    const message = {
        from: currentUser.id,
        to: toUserId,
        type: 'photo',
        photoFile,
        read: false,
        time: new Date()
    };

    messages.push(message);
    createNotification(toUserId, 'message', `${currentUser.name} sent you a photo`, { fromUserId: currentUser.id });
    sendRealtimeMessage(message, toUserId);

    return res.json({ success: true });
});

// ==========================================
// COIN PURCHASE SYSTEM
// ==========================================

// COIN PURCHASE PAGE - Main packages
app.get('/buy-coins', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    if (user.gender === 'female') return res.redirect('/dashboard');
    
    const coinPackages = [
        { coins: 500, price: 50, popular: true, label: 'Minimum Purchase' },
        { coins: 750, price: 75, popular: false, label: 'Starter Plus' },
        { coins: 1000, price: 100, popular: false, label: 'Popular' },
        { coins: 1500, price: 150, popular: false, label: 'Value Pack' },
        { coins: 2500, price: 250, popular: false, label: 'Best Value' },
        { coins: 5000, price: 500, popular: false, label: 'VIP Package' }
    ];
    
    const svgCoin = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="8.5"></circle><path d="M12 7.5v9M14.5 9.5c-.6-.7-1.4-1-2.5-1-1.2 0-2 .6-2 1.5 0 2.3 4.5 1 4.5 3.5 0 .9-.8 1.6-2 1.6-1.1 0-2-.4-2.6-1.1"></path></svg>';
    const svgCheck = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m5 13 4 4L19 7"/></svg>';

    const packagesHtml = coinPackages.map(pkg => `
        <div class="package-card${pkg.popular ? ' is-popular' : ''}">
            ${pkg.popular ? '<div class="package-ribbon">RECOMMENDED</div>' : ''}
            <div class="package-coin-icon">${svgCoin}</div>
            <p class="package-amount">${pkg.coins.toLocaleString()}</p>
            <p class="package-coins-label">Coins</p>
            <div class="package-price-box">
                <p class="package-price">$${pkg.price}</p>
                <p class="package-rate">$0.10 per coin</p>
            </div>
            <ul class="package-perks">
                <li>${svgCheck} Send ${pkg.coins} messages</li>
                <li>${svgCheck} View ${Math.floor(pkg.coins / 20)} profiles</li>
                <li>${svgCheck} Send ${Math.floor(pkg.coins / 10)} photos</li>
                <li>${svgCheck} No expiration</li>
            </ul>
            <form method="POST" action="/buy-coins/select">
                <input type="hidden" name="coins" value="${pkg.coins}">
                <input type="hidden" name="price" value="${pkg.price}">
                <button type="submit" class="btn ${pkg.popular ? 'btn-primary' : 'btn-outline'}">
                    ${pkg.popular ? 'Select Package' : 'Choose'}
                </button>
            </form>
        </div>
    `).join('');

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Buy Coins - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    <span class="coin-pill" aria-label="${user.coins} coins">${svgCoin} ${user.coins}</span>
                    <a href="/dashboard" class="btn btn-primary btn-sm desktop-only">Dashboard</a>
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <section class="coin-hero">
        <div class="container">
            <h1>${svgCoin} Buy Coins</h1>
            <p class="coin-hero-sub">Only <strong>$0.10 per coin</strong>. Minimum purchase: <strong>$50 (500 coins)</strong></p>
            <div class="coin-stats">
                <div class="coin-stat">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"/></svg>
                    <span>1 coin/message</span>
                </div>
                <div class="coin-stat">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M2 12s3.5-7 10-7 10 7 10 7-3.5 7-10 7-10-7-10-7Z"/><circle cx="12" cy="12" r="3"/></svg>
                    <span>20 coins/view</span>
                </div>
                <div class="coin-stat">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg>
                    <span>10 coins/photo</span>
                </div>
            </div>
        </div>
    </section>

    <section class="coin-shop-shell">
        <div class="container">
            <div class="min-notice">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="9"/><path d="M12 8v5M12 16h.01"/></svg>
                Minimum Purchase: $50 USD (500 coins) @ $0.10 per coin
            </div>

            <h2 class="shop-heading">Choose Your Package</h2>
            <div class="package-grid">
                ${packagesHtml}
            </div>

            <div class="payment-card">
                <h3>
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="2" y="5" width="20" height="14" rx="2"/><path d="M2 10h20"/></svg>
                    Payment Method
                </h3>
                <p>We accept gift cards as payment. Minimum value: <strong>$50 USD</strong></p>
                <div class="payment-methods">
                    <span class="payment-chip"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 12v8H4v-8"/><path d="M2 7h20v5H2z"/><path d="M12 22V7"/><path d="M12 7H7.5a2.5 2.5 0 0 1 0-5C11 2 12 7 12 7z"/><path d="M12 7h4.5a2.5 2.5 0 0 0 0-5C13 2 12 7 12 7z"/></svg> Apple Gift Card ($50+)</span>
                    <span class="payment-chip"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 12v8H4v-8"/><path d="M2 7h20v5H2z"/><path d="M12 22V7"/><path d="M12 7H7.5a2.5 2.5 0 0 1 0-5C11 2 12 7 12 7z"/><path d="M12 7h4.5a2.5 2.5 0 0 0 0-5C13 2 12 7 12 7z"/></svg> Google Play ($50+)</span>
                    <span class="payment-chip"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 12v8H4v-8"/><path d="M2 7h20v5H2z"/><path d="M12 22V7"/><path d="M12 7H7.5a2.5 2.5 0 0 1 0-5C11 2 12 7 12 7z"/><path d="M12 7h4.5a2.5 2.5 0 0 0 0-5C13 2 12 7 12 7z"/></svg> Amazon ($50+)</span>
                    <span class="payment-chip"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="2" y="5" width="20" height="14" rx="2"/><path d="M2 10h20"/></svg> Visa/Mastercard ($50+)</span>
                </div>
            </div>
        </div>
    </section>
    ${getFooter()}
</body>
</html>
    `);
});

// Select package and proceed to upload
app.post('/buy-coins/select', requireAuth, (req, res) => {
    const { coins, price } = req.body;
    req.session.pendingPurchase = { coins: parseInt(coins), price: parseInt(price) };
    res.redirect('/buy-coins/upload');
});

// Upload gift card page
app.get('/buy-coins/upload', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const purchase = req.session.pendingPurchase;
    
    if (!purchase) return res.redirect('/buy-coins');
    
    // Validate minimum purchase
    if (purchase.coins < MIN_COINS) {
        delete req.session.pendingPurchase;
        return res.send(`<script>alert("Minimum purchase is ${MIN_COINS} coins ($${MIN_PURCHASE_USD}). Please select a valid package."); window.location="/buy-coins";</script>`);
    }
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Upload Gift Card - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/buy-coins" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <div class="container upload-shell">
        <div class="upload-card">
            <div class="upload-head">
                <div class="standalone-icon" aria-hidden="true">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><path d="M20 12v8H4v-8"/><path d="M2 7h20v5H2z"/><path d="M12 22V7"/><path d="M12 7H7.5a2.5 2.5 0 0 1 0-5C11 2 12 7 12 7z"/><path d="M12 7h4.5a2.5 2.5 0 0 0 0-5C13 2 12 7 12 7z"/></svg>
                </div>
                <h2>Upload Gift Card</h2>
                <p class="upload-purchase">Purchasing <strong>${purchase.coins.toLocaleString()} coins</strong> for <strong>$${purchase.price}</strong></p>
                <p class="upload-rate">$0.10 per coin &middot; Minimum $50</p>
            </div>

            <div class="auth-info-box is-info">
                <div class="box-title">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 5h6a1 1 0 0 1 1 1v13a1 1 0 0 1-1 1H8a1 1 0 0 1-1-1V6"/><path d="M9 3h6v3H9z"/><path d="M11 11h4M11 15h4"/></svg>
                    Requirements
                </div>
                <ul class="auth-list">
                    <li>Gift card must be worth <strong>$${purchase.price} or more</strong></li>
                    <li>Take clear photos of the <strong>front and back</strong></li>
                    <li>Make sure the code is clearly visible</li>
                    <li>Admin will verify within 24 hours</li>
                </ul>
            </div>

            <form method="POST" action="/buy-coins/upload" enctype="multipart/form-data">
                <div class="form-group">
                    <label>Gift Card Type *</label>
                    <select name="cardType" required>
                        <option value="">Select card type...</option>
                        <option value="Apple Gift Card">Apple Gift Card ($50+)</option>
                        <option value="Google Play">Google Play ($50+)</option>
                        <option value="Amazon">Amazon ($50+)</option>
                        <option value="Visa">Visa Gift Card ($50+)</option>
                        <option value="Mastercard">Mastercard Gift Card ($50+)</option>
                        <option value="Other">Other ($50+)</option>
                    </select>
                </div>

                <div class="form-group">
                    <label>Front of Card (showing value) *</label>
                    <div class="photo-drop">
                        <input type="file" name="front" accept="image/*" required id="frontInput" onchange="previewImage(this, 'frontPreview')" style="display: none;">
                        <label for="frontInput" class="photo-drop-label">
                            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg>
                            Upload Front
                        </label>
                        <div class="drop-preview" id="frontPreview"></div>
                    </div>
                </div>

                <div class="form-group">
                    <label>Back of Card (showing code) *</label>
                    <div class="photo-drop">
                        <input type="file" name="back" accept="image/*" required id="backInput" onchange="previewImage(this, 'backPreview')" style="display: none;">
                        <label for="backInput" class="photo-drop-label">
                            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg>
                            Upload Back
                        </label>
                        <div class="drop-preview" id="backPreview"></div>
                    </div>
                </div>

                <div class="upload-success">
                    You will receive <strong>${purchase.coins.toLocaleString()} coins</strong> after verification ($0.10 per coin)
                </div>

                <button type="submit" class="btn btn-primary btn-block auth-submit">Submit for Verification</button>
            </form>
        </div>
    </div>
    ${getFooter()}

    <script>
        function previewImage(input, previewId) {
            const preview = document.getElementById(previewId);
            if (input.files && input.files[0]) {
                const reader = new FileReader();
                reader.onload = function(e) {
                    preview.innerHTML = '<img src="' + e.target.result + '" alt="Card preview">';
                };
                reader.readAsDataURL(input.files[0]);
            }
        }
    </script>
</body>
</html>
    `);
});

// Process gift card upload
app.post('/buy-coins/upload', requireAuth, upload.fields([{ name: 'front' }, { name: 'back' }]), (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    const purchase = req.session.pendingPurchase;
    
    if (!purchase) {
        return res.redirect('/buy-coins');
    }
    
    // Validate minimum purchase
    if (purchase.coins < MIN_COINS || purchase.price < MIN_PURCHASE_USD) {
        delete req.session.pendingPurchase;
        return res.send(`<script>alert("Minimum purchase is $${MIN_PURCHASE_USD} (${MIN_COINS} coins). Please select a valid package."); window.location="/buy-coins";</script>`);
    }
    
    if (!req.files.front || !req.files.back) {
        return res.send('<script>alert("Both front and back images are required!"); window.location="/buy-coins/upload";</script>');
    }
    
    transactions.push({
        id: transactions.length + 1,
        userId: user.id,
        userEmail: user.email,
        cardType: req.body.cardType,
        frontImage: req.files.front[0].filename,
        backImage: req.files.back[0].filename,
        status: 'pending',
        coinsRequested: purchase.coins,
        price: purchase.price,
        coinRate: COIN_PRICE,
        createdAt: new Date()
    });
    
    delete req.session.pendingPurchase;
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Submitted - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body class="auth-page">
    <div class="auth-card narrow standalone-card">
        <div class="auth-success-icon" aria-hidden="true">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><path d="m5 13 4 4L19 7"/></svg>
        </div>
        <h2>Submitted Successfully!</h2>
        <p>
            Your gift card is being verified by our team.<br>
            <strong>${purchase.coins.toLocaleString()} coins</strong> will be added to your account within 24 hours ($0.10 per coin).
        </p>
        <a href="/dashboard" class="btn btn-primary btn-block">Back to Dashboard</a>
    </div>
</body>
</html>
    `);
});

// OLD UPLOAD PROOF - Redirect to new system
app.get('/upload-proof', requireAuth, (req, res) => {
    res.redirect('/buy-coins');
});

// LOGOUT
app.get('/logout', (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    if (user) {
        user.isOnline = false;
        user.lastActive = new Date();
        userSessions.delete(user.id);
    }
    req.session.destroy();
    res.redirect('/');
});

// ==========================================
// ADMIN ROUTES
// ==========================================

app.get('/admin', requireAdmin, (req, res) => {
    const stats = {
        total: users.filter(u => u.role === 'user').length,
        males: users.filter(u => u.gender === 'male' && u.role === 'user').length,
        females: users.filter(u => u.gender === 'female' && u.role === 'user').length,
        online: users.filter(u => u.isOnline && u.role === 'user').length,
        pending: transactions.filter(t => t.status === 'pending').length,
        reports: reports.filter(r => r.status === 'pending').length,
        censorshipAlerts: censorshipLogs.filter(c => c.status === 'pending_review').length
    };
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#1b1f3a">
    <title>Admin Dashboard - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('dashboard')}

    <div class="container admin-shell">
        <div class="admin-head">
            <h2 class="admin-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 13h6V4H4zM14 20h6v-9h-6zM4 20h6v-4H4zM14 8h6V4h-6z"/></svg>
                Dashboard Overview
            </h2>
            <p class="admin-subtitle">Monitor users, payments, reports and moderation across the platform.</p>
        </div>

        <div class="grid grid-4" style="margin-bottom: 24px;">
            <div class="stats-card has-icon">
                <div class="stat-icon"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="9" cy="8" r="3.2"/><path d="M2.5 20c.6-3.4 3.2-5.2 6.5-5.2s5.9 1.8 6.5 5.2"/><path d="M17 11a3 3 0 1 0-1.5-5.6"/><path d="M18.5 20c-.3-2-1-3.6-2-4.7 2.9.2 5 2 5.5 4.7z"/></svg></div>
                <div class="stats-number">${stats.total}</div>
                <div class="stats-label">Total Users</div>
            </div>
            <div class="stats-card has-icon">
                <div class="stat-icon is-female"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="9" r="5"/><path d="M12 14v8M9 19h6"/></svg></div>
                <div class="stats-number" style="color: var(--md-secondary);">${stats.females}</div>
                <div class="stats-label">Female Users</div>
            </div>
            <div class="stats-card has-icon">
                <div class="stat-icon is-male"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="10" cy="14" r="5"/><path d="M14 10 20 4M15 4h5v5"/></svg></div>
                <div class="stats-number" style="color: #1d4fd0;">${stats.males}</div>
                <div class="stats-label">Male Users</div>
            </div>
            <div class="stats-card has-icon">
                <div class="stat-icon is-online"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2v3M12 19v3M2 12h3M19 12h3M5 5l2 2M17 17l2 2M19 5l-2 2M7 17l-2 2"/></svg></div>
                <div class="stats-number" style="color: var(--md-success);">${stats.online}</div>
                <div class="stats-label">Online Now</div>
            </div>
        </div>

        <div class="grid grid-3">
            <div class="stats-card has-icon">
                <div class="stat-icon is-warning"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="2" y="5" width="20" height="14" rx="2"/><path d="M2 10h20"/></svg></div>
                <div class="stats-number" style="color: #b26a00;">${stats.pending}</div>
                <div class="stats-label" style="margin-bottom: 15px;">Pending Payments</div>
                <a href="/admin/transactions" class="btn btn-warning btn-sm">Review Payments</a>
            </div>
            <div class="stats-card has-icon">
                <div class="stat-icon is-danger"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1z"/><line x1="4" y1="22" x2="4" y2="15"/></svg></div>
                <div class="stats-number" style="color: var(--md-danger);">${stats.reports}</div>
                <div class="stats-label" style="margin-bottom: 15px;">Pending Reports</div>
                <a href="/admin/reports" class="btn btn-danger btn-sm">Review Reports</a>
            </div>
            <div class="stats-card has-icon">
                <div class="stat-icon is-purple"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 3 4 6v6c0 5 3.4 7.8 8 9 4.6-1.2 8-4 8-9V6z"/><path d="m9 12 2 2 4-4"/></svg></div>
                <div class="stats-number" style="color: #7b1fa2;">${stats.censorshipAlerts}</div>
                <div class="stats-label" style="margin-bottom: 15px;">Censorship Alerts</div>
                <a href="/admin/censorship" class="btn btn-primary btn-sm">View Alerts</a>
            </div>
        </div>

        <div class="admin-quicknav">
            <a href="/admin/users" class="btn btn-primary btn-lg">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="9" cy="8" r="3.2"/><path d="M2.5 20c.6-3.4 3.2-5.2 6.5-5.2s5.9 1.8 6.5 5.2"/></svg>
                Manage All Users
            </a>
            <a href="/admin/assignments" class="btn btn-success btn-lg">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M19 8v6M22 11h-6"/></svg>
                Manage Assignments
            </a>
            <a href="/admin/chats" class="btn btn-warning btn-lg">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"/></svg>
                Chat Monitor
            </a>
            <a href="/admin/notifications" class="btn btn-info btn-lg">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M3 11v2a1 1 0 0 0 1 1h2l3.5 3.5a1 1 0 0 0 1.7-.7V7.2a1 1 0 0 0-1.7-.7L6 10H4a1 1 0 0 0-1 1Z"/><path d="M16 8.5a4 4 0 0 1 0 7"/><path d="M18.5 6a7.5 7.5 0 0 1 0 12"/></svg>
                Notifications
            </a>
        </div>
    </div>
</body>
</html>
    `);
});

// ADMIN: ASSIGNMENTS - Assign males to females
app.get('/admin/assignments', requireAdmin, (req, res) => {
    const females = users.filter(u => u.gender === 'female' && u.role === 'user');
    const males = users.filter(u => u.gender === 'male' && u.role === 'user');
    
    const femaleList = females.map(f => {
        const assignedMales = adminAssignments
            .filter(a => a.femaleId === f.id)
            .map(a => users.find(u => u.id === a.maleId))
            .filter(Boolean);
        
        return `
            <div class="admin-card">
                <div class="admin-card-head">
                    <div class="avatar-placeholder">
                        ${f.photo ? `<img src="/uploads/${f.photo}" alt="${f.name}" onerror="this.style.display='none';">` : `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="8" r="3.5"></circle><path d="M4.5 20c.6-3.5 3.3-5.5 7.5-5.5s6.9 2 7.5 5.5"></path></svg>`}
                    </div>
                    <div>
                        <h4>${f.name}, ${f.age}</h4>
                        <p>${f.email} &bull; ${f.location}</p>
                    </div>
                </div>

                <div style="margin-bottom: 18px;">
                    <p class="admin-section-label">Assigned Gentlemen (${assignedMales.length})</p>
                    ${assignedMales.length === 0 ? '<p class="assign-empty">No assignments yet</p>' : `
                        <div class="assign-chips">
                            ${assignedMales.map(m => `
                                <span class="assign-chip">
                                    ${m.name}
                                    <form method="POST" action="/admin/assignments/remove">
                                        <input type="hidden" name="femaleId" value="${f.id}">
                                        <input type="hidden" name="maleId" value="${m.id}">
                                        <button type="submit" aria-label="Remove ${m.name}">
                                            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" aria-hidden="true"><path d="M18 6 6 18M6 6l12 12"/></svg>
                                        </button>
                                    </form>
                                </span>
                            `).join('')}
                        </div>
                    `}
                </div>

                <form method="POST" action="/admin/assignments/add" class="assign-form">
                    <input type="hidden" name="femaleId" value="${f.id}">
                    <select name="maleId" required>
                        <option value="">Select gentleman to assign...</option>
                        ${males.filter(m => !assignedMales.find(am => am.id === m.id)).map(m => 
                            `<option value="${m.id}">${m.name}, ${m.age} - ${m.location}</option>`
                        ).join('')}
                    </select>
                    <button type="submit" class="btn btn-success btn-sm">Assign</button>
                </form>
            </div>
        `;
    }).join('');
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#1b1f3a">
    <title>Manage Assignments - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('assignments')}

    <div class="container admin-shell" style="max-width: 900px;">
        <div class="admin-head">
            <h2 class="admin-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M19 8v6M22 11h-6"/></svg>
                Manage Assignments
            </h2>
            <p class="admin-subtitle">Assign male users to female users. Females will only see assigned males who message them first.</p>
        </div>

        ${females.length === 0 ? '<div class="admin-card"><p class="assign-empty">No female users found.</p></div>' : femaleList}
    </div>
</body>
</html>
    `);
});

app.post('/admin/assignments/add', requireAdmin, (req, res) => {
    const { femaleId, maleId } = req.body;
    
    // Check if already assigned
    const existing = adminAssignments.find(a => a.femaleId === parseInt(femaleId) && a.maleId === parseInt(maleId));
    if (!existing) {
        adminAssignments.push({
            femaleId: parseInt(femaleId),
            maleId: parseInt(maleId),
            assignedAt: new Date(),
            assignedBy: req.session.userId
        });
        
        // Notify female
        const male = users.find(u => u.id === parseInt(maleId));
        createNotification(parseInt(femaleId), 'assignment', `A new match has been assigned to you: ${male.name}! Wait for his message.`, { maleId: parseInt(maleId) });
    }
    
    res.redirect('/admin/assignments');
});

app.post('/admin/assignments/remove', requireAdmin, (req, res) => {
    const { femaleId, maleId } = req.body;
    const idx = adminAssignments.findIndex(a => a.femaleId === parseInt(femaleId) && a.maleId === parseInt(maleId));
    if (idx > -1) adminAssignments.splice(idx, 1);
    res.redirect('/admin/assignments');
});

// Admin: View female album
app.get('/admin/album/:femaleId', requireAdmin, (req, res) => {
    const femaleId = parseInt(req.params.femaleId);
    const female = users.find(u => u.id === femaleId);

    if (!female || female.gender !== 'female') {
        return res.redirect('/admin/users');
    }

    const albumPhotos = albums.filter(a => a.femaleId === femaleId);

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#1b1f3a">
    <title>Manage Album - ${female.name}</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('users')}

    <div class="container admin-shell" style="max-width: 900px;">
        <div class="admin-head">
            <h2 class="admin-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg>
                Manage Album: ${female.name} (${female.displayId})
            </h2>
            <p class="admin-subtitle">These photos will be available for ${female.name} to send in chat.</p>
        </div>

        <div class="admin-card">
            <h3 class="detail-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 5v14M5 12h14"/></svg>
                Upload Photos
            </h3>
            <form method="POST" action="/admin/album/${femaleId}/upload" enctype="multipart/form-data">
                <div class="photo-drop">
                    <input type="file" name="photos" accept="image/*" multiple id="albumInput" style="display: none;">
                    <label for="albumInput" class="photo-drop-label">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg>
                        Select Photos
                    </label>
                    <p class="photo-drop-hint">Select multiple photos</p>
                    <div class="photo-preview-grid" id="preview"></div>
                </div>
                <button type="submit" class="btn btn-primary btn-block auth-submit">Upload to Album</button>
            </form>
        </div>

        <h3 class="detail-title" style="margin-top: 8px;">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="3" width="18" height="18" rx="2"/><circle cx="8.5" cy="8.5" r="1.5"/><path d="m21 15-5-5L5 21"/></svg>
            Current Album (${albumPhotos.length} photos)
        </h3>
        ${albumPhotos.length === 0 ? '<p class="assign-empty">No photos yet.</p>' : `
            <div class="photo-gallery">
                ${albumPhotos.map(photo => `
                    <div class="photo-item">
                        <img src="/uploads/${photo.photoFile}" alt="Album photo" onerror="this.style.display='none'; this.nextElementSibling.style.display='grid';">
                        <div class="photo-item-fallback" style="display:none;"><svg viewBox="0 0 24 24" width="26" height="26" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg></div>
                        <form method="POST" action="/admin/album/${photo.id}/delete">
                            <button type="submit" class="remove-btn" aria-label="Delete photo">
                                <svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><path d="M18 6 6 18M6 6l12 12"/></svg>
                            </button>
                        </form>
                    </div>
                `).join('')}
            </div>
        `}
    </div>

    <script>
        document.getElementById('albumInput').onchange = function() {
            const preview = document.getElementById('preview');
            preview.innerHTML = '';
            for (let file of this.files) {
                const reader = new FileReader();
                reader.onload = function(e) {
                    const wrap = document.createElement('div');
                    const img = document.createElement('img');
                    img.src = e.target.result;
                    img.alt = 'Preview';
                    wrap.appendChild(img);
                    preview.appendChild(wrap);
                };
                reader.readAsDataURL(file);
            }
        };
    </script>
</body>
</html>
    `);
});

// Admin: Upload to female's photos array
app.post('/admin/album/:femaleId/upload', requireAdmin, upload.array('photos', 20), (req, res) => {
    const femaleId = parseInt(req.params.femaleId);
    const female = users.find(u => u.id === femaleId);
    
    if (!female || female.gender !== 'female') {
        return res.redirect('/admin/users');
    }
    
    if (!req.files || req.files.length === 0) {
        return res.send('<script>alert("No photos selected!"); window.location="/admin/album/' + femaleId + '";</script>');
    }
    
    req.files.forEach(file => {
        if (!female.photos) female.photos = [];
        female.photos.push(file.filename);
    });
    
    res.send(`<script>alert("${req.files.length} photos added to ${female.name}'s album!"); window.location="/admin/album/${femaleId}";</script>`);
});

// Admin: Delete album photo
app.post('/admin/album/:albumId/delete', requireAdmin, (req, res) => {
    const albumId = parseInt(req.params.albumId);
    const albumItem = albums.find(a => a.id === albumId);
    
    if (albumItem) {
        const female = users.find(u => u.id === albumItem.femaleId);
        if (female && female.photos) {
            female.photos = female.photos.filter(file => file !== albumItem.photoFile);
        }
        const albumIndex = albums.findIndex(a => a.id === albumId);
        if (albumIndex > -1) albums.splice(albumIndex, 1);
        return res.redirect('/admin/album/' + albumItem.femaleId);
    }

    res.redirect('/admin/users');
});

// ADMIN: USERS
app.get('/admin/users', requireAdmin, (req, res) => {
    const { gender, verified, search } = req.query;
    
    let filteredUsers = users.filter(u => u.role === 'user');
    
    if (gender) filteredUsers = filteredUsers.filter(u => u.gender === gender);
    if (verified === 'true') filteredUsers = filteredUsers.filter(u => u.isVerified);
    if (verified === 'false') filteredUsers = filteredUsers.filter(u => !u.isVerified);
    if (search) {
        const term = search.toLowerCase();
        filteredUsers = filteredUsers.filter(u => 
            u.name.toLowerCase().includes(term) ||
            u.email.toLowerCase().includes(term) ||
            u.location.toLowerCase().includes(term)
        );
    }
    
    const userRows = filteredUsers.map(u => {
        const trialStatus = getTrialStatus(u);
        const assignedCount = adminAssignments.filter(a => 
            u.gender === 'female' ? a.femaleId === u.id : a.maleId === u.id
        ).length;
        
        return `
            <tr>
                <td>
                    <div class="table-user">
                        <div class="avatar-placeholder">
                            ${u.photo ? `<img src="/uploads/${u.photo}" alt="${u.name}" onerror="this.style.display='none';">` : `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="8" r="3.5"></circle><path d="M4.5 20c.6-3.5 3.3-5.5 7.5-5.5s6.9 2 7.5 5.5"></path></svg>`}
                        </div>
                        <div>
                            <div class="table-user-name">${u.name} ${u.isVerified ? '<span class="status-chip is-verified" style="margin-left:4px;"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m5 12.5 4.2 4.2L19 7"/></svg></span>' : ''}</div>
                            <div class="table-user-sub">${u.email}</div>
                        </div>
                    </div>
                </td>
                <td>
                    <span class="status-chip ${u.gender === 'female' ? 'is-info' : 'is-neutral'}" style="${u.gender === 'female' ? 'background: var(--md-secondary-container); color: var(--md-secondary);' : ''}text-transform: uppercase;">${u.gender}</span>
                </td>
                <td>${u.age}</td>
                <td>${u.location}</td>
                <td>
                    ${u.gender === 'male' ? `
                        <div>
                            <div style="font-weight: 700; color: ${u.coins > 0 ? 'var(--md-success)' : 'var(--md-danger)'};">${u.coins} coins</div>
                            <div class="table-user-sub">${u.isTrialActive ? 'Trial active' : (trialStatus.canChat ? 'Active' : 'Expired')}</div>
                        </div>
                    ` : `<div class="table-user-sub">${assignedCount} assigned</div>`}
                </td>
                <td>
                    <span class="status-chip ${u.isBlocked ? 'is-blocked' : 'is-approved'}">
                        ${u.isBlocked ? 'Blocked' : 'Active'}
                    </span>
                </td>
                <td>
                    <div class="admin-actions">
                        <a href="/admin/users/${u.id}/view" class="btn btn-xs btn-outline">View</a>
                        <a href="/admin/users/${u.id}/edit" class="btn btn-xs btn-primary">Edit</a>
                        ${u.gender === 'female' ? `
                            <a href="/admin/album/${u.id}" class="btn btn-xs btn-info">
                                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M14.5 4h-5L7 7H4a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2V9a2 2 0 0 0-2-2h-3l-2.5-3z"/><circle cx="12" cy="13" r="3"/></svg>
                                Album
                            </a>
                        ` : ''}
                        <form action="/admin/users/${u.id}/toggle-block" method="POST">
                            <button type="submit" class="btn btn-xs ${u.isBlocked ? 'btn-success' : 'btn-danger'}">
                                ${u.isBlocked ? 'Unblock' : 'Block'}
                            </button>
                        </form>
                    </div>
                </td>
            </tr>
        `;
    }).join('');
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#1b1f3a">
    <title>Manage Users - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('users')}

    <div class="container admin-shell">
        <div class="admin-head">
            <h2 class="admin-title">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="9" cy="8" r="3.2"/><path d="M2.5 20c.6-3.4 3.2-5.2 6.5-5.2s5.9 1.8 6.5 5.2"/><path d="M17 11a3 3 0 1 0-1.5-5.6"/><path d="M18.5 20c-.3-2-1-3.6-2-4.7 2.9.2 5 2 5.5 4.7z"/></svg>
                All Users
            </h2>
            <p class="admin-subtitle">${filteredUsers.length} user${filteredUsers.length === 1 ? '' : 's'} matching your filters.</p>
        </div>

        <div class="admin-card">
            <form method="GET" action="/admin/users" class="filter-form" style="display: flex; gap: 14px; flex-wrap: wrap; align-items: flex-end;">
                <div class="form-group" style="margin:0;">
                    <label>Gender</label>
                    <select name="gender">
                        <option value="">All</option>
                        <option value="female" ${gender === 'female' ? 'selected' : ''}>Female</option>
                        <option value="male" ${gender === 'male' ? 'selected' : ''}>Male</option>
                    </select>
                </div>
                <div class="form-group" style="margin:0;">
                    <label>Verified</label>
                    <select name="verified">
                        <option value="">All</option>
                        <option value="true" ${verified === 'true' ? 'selected' : ''}>Verified</option>
                        <option value="false" ${verified === 'false' ? 'selected' : ''}>Unverified</option>
                    </select>
                </div>
                <div class="form-group" style="margin:0; flex:1; min-width:200px;">
                    <label>Search</label>
                    <input type="text" name="search" placeholder="Name, email, location..." value="${search || ''}">
                </div>
                <button type="submit" class="btn btn-primary btn-sm">Filter</button>
                <a href="/admin/users" class="btn btn-outline btn-sm">Clear</a>
            </form>
        </div>

        <div class="table-wrap">
            <table class="data-table">
                <thead>
                    <tr>
                        <th>User</th>
                        <th>Gender</th>
                        <th>Age</th>
                        <th>Location</th>
                        <th>Status</th>
                        <th>Account</th>
                        <th>Actions</th>
                    </tr>
                </thead>
                <tbody>
                    ${userRows || '<tr class="empty-row"><td colspan="7">No users found</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
</body>
</html>
    `);
});

// ADMIN: VIEW USER
app.get('/admin/users/:id/view', requireAdmin, (req, res) => {
    const user = users.find(u => u.id === parseInt(req.params.id));
    if (!user) return res.redirect('/admin/users');
    
    const userMessages = messages.filter(m => m.from === user.id || m.to === user.id);
    const chatPartners = new Set();
    userMessages.forEach(m => {
        if (m.from === user.id) chatPartners.add(m.to);
        if (m.to === user.id) chatPartners.add(m.from);
    });
    
    const svgLock = '<svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></svg>';
    const svgVerified = '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6 9 17l-5-5"/></svg>';
    const svgUser = '<svg viewBox="0 0 24 24" width="44" height="44" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/></svg>';
    const svgImage = '<svg viewBox="0 0 24 24" width="28" height="28" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="3" width="18" height="18" rx="2"/><circle cx="8.5" cy="8.5" r="1.5"/><path d="m21 15-5-5L5 21"/></svg>';

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>${user.name} - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('users')}

    <div class="container admin-shell">
        <div class="admin-card">
            <div class="admin-user-head">
                <div class="profile-avatar">
                    ${user.photo ? `<img src="/uploads/${user.photo}" alt="${user.name}">${svgUser}` : svgUser}
                </div>
                <div>
                    <h2 class="admin-title" style="margin-bottom:6px;">${user.name} ${user.isVerified ? `<span class="status-chip is-verified">${svgVerified} Verified</span>` : ''}</h2>
                    <p class="admin-subtitle">${user.email}</p>
                </div>
            </div>

            <div class="auth-info-box is-info" style="margin-bottom:24px;">
                <span class="standalone-icon">${svgLock}</span>
                <div>
                    <h4 class="detail-title" style="margin-bottom:8px;">Login Credentials</h4>
                    <p style="margin-bottom:4px;"><strong>Email:</strong> ${user.email}</p>
                    <p><strong>Password:</strong> ${user.showPassword || '(encrypted)'}</p>
                </div>
            </div>

            <div class="fact-grid" style="margin-bottom:24px;">
                <div class="fact">
                    <span class="fact-label">User ID</span>
                    <span class="fact-value" style="color:var(--md-primary);">#${user.displayId || user.id}</span>
                </div>
                <div class="fact">
                    <span class="fact-label">Gender</span>
                    <span class="fact-value" style="text-transform:capitalize;">${user.gender}</span>
                </div>
                <div class="fact">
                    <span class="fact-label">Age</span>
                    <span class="fact-value">${user.age}</span>
                </div>
                <div class="fact">
                    <span class="fact-label">Location</span>
                    <span class="fact-value">${user.location}</span>
                </div>
                <div class="fact">
                    <span class="fact-label">Coins</span>
                    <span class="fact-value" style="color:${user.coins > 0 ? 'var(--md-success)' : 'var(--md-danger)'};">${user.coins}</span>
                </div>
                <div class="fact">
                    <span class="fact-label">Messages</span>
                    <span class="fact-value">${userMessages.length}</span>
                </div>
            </div>

            ${user.photos.length > 0 ? `
                <div style="margin-bottom:24px;">
                    <h4 class="admin-section-label">Photos (${user.photos.length})</h4>
                    <div class="photo-gallery">
                        ${user.photos.map(photo => `
                            <div class="photo-item">
                                <img src="/uploads/${photo}" alt="Photo" onerror="this.style.display='none'; this.nextElementSibling.style.display='flex';">
                                <div class="photo-item-fallback" style="display:none;">${svgImage}</div>
                            </div>
                        `).join('')}
                    </div>
                </div>
            ` : ''}

            <div class="admin-btn-row">
                <a href="/admin/users/${user.id}/edit" class="btn btn-primary">Edit Profile</a>
                <form action="/admin/users/${user.id}/toggle-verify" method="POST">
                    <button type="submit" class="btn ${user.isVerified ? 'btn-warning' : 'btn-success'}">
                        ${user.isVerified ? 'Remove Verification' : 'Verify User'}
                    </button>
                </form>
                <form action="/admin/users/${user.id}/delete" method="POST" onsubmit="return confirm('DELETE this user permanently?');">
                    <button type="submit" class="btn btn-danger">Delete Account</button>
                </form>
            </div>
        </div>
    </div>
</body>
</html>
    `);
});

// ADMIN: EDIT USER
app.get('/admin/users/:id/edit', requireAdmin, (req, res) => {
    const user = users.find(u => u.id === parseInt(req.params.id));
    if (!user) return res.redirect('/admin/users');
    
    const svgPencil = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 20h9"/><path d="M16.5 3.5a2.121 2.121 0 0 1 3 3L7 19l-4 1 1-4Z"/></svg>';

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Edit ${user.name} - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('users')}

    <div class="container admin-shell">
        <div class="admin-card">
            <div class="admin-head">
                <h2 class="admin-title">${svgPencil} Edit ${user.name}</h2>
                <p class="admin-subtitle">Update this member's profile and account details.</p>
            </div>

            <form method="POST" action="/admin/users/${user.id}/edit">
                <div class="grid grid-2">
                    <div class="form-group">
                        <label>Name</label>
                        <input type="text" name="name" value="${user.name}" required>
                    </div>
                    <div class="form-group">
                        <label>Email</label>
                        <input type="email" name="email" value="${user.email}" required>
                    </div>
                    <div class="form-group">
                        <label>Password (leave empty to keep)</label>
                        <input type="text" name="password" placeholder="New password">
                    </div>
                    <div class="form-group">
                        <label>Age</label>
                        <input type="number" name="age" value="${user.age}" required>
                    </div>
                    <div class="form-group">
                        <label>Coins</label>
                        <input type="number" name="coins" value="${user.coins}" required>
                    </div>
                    <div class="form-group">
                        <label>Trial Days</label>
                        <input type="number" name="trialDays" value="${user.trialDays}" required>
                    </div>
                </div>

                <div class="form-group">
                    <label>Location</label>
                    <input type="text" name="location" value="${user.location}" required>
                </div>

                <div class="form-group">
                    <label>Country</label>
                    <input type="text" name="country" value="${user.country || ''}" required>
                </div>

                <div class="form-group">
                    <label>Bio</label>
                    <textarea name="bio" rows="4">${user.bio || ''}</textarea>
                </div>

                <div class="admin-btn-row" style="margin-top:20px;">
                    <button type="submit" class="btn btn-primary">Save Changes</button>
                    <a href="/admin/users" class="btn btn-outline">Cancel</a>
                </div>
            </form>
        </div>
    </div>
</body>
</html>
    `);
});

app.post('/admin/users/:id/edit', requireAdmin, async (req, res) => {
    const user = users.find(u => u.id === parseInt(req.params.id));
    if (!user) return res.redirect('/admin/users');
    
    user.name = req.body.name;
    user.email = req.body.email;
    user.age = parseInt(req.body.age);
    user.coins = parseInt(req.body.coins);
    user.trialDays = parseInt(req.body.trialDays);
    user.location = req.body.location;
    user.country = req.body.country;
    user.bio = req.body.bio;
    
    if (req.body.password) {
        user.password = await bcrypt.hash(req.body.password, 10);
        user.showPassword = req.body.password;
    }
    
    res.redirect('/admin/users');
});

app.post('/admin/users/:id/toggle-block', requireAdmin, (req, res) => {
    const user = users.find(u => u.id === parseInt(req.params.id));
    if (user) user.isBlocked = !user.isBlocked;
    res.redirect('/admin/users');
});

app.post('/admin/users/:id/toggle-verify', requireAdmin, (req, res) => {
    const user = users.find(u => u.id === parseInt(req.params.id));
    if (user) user.isVerified = !user.isVerified;
    res.redirect('/admin/users');
});

app.post('/admin/users/:id/delete', requireAdmin, (req, res) => {
    const index = users.findIndex(u => u.id === parseInt(req.params.id));
    if (index > -1) users.splice(index, 1);
    res.redirect('/admin/users');
});

// ADMIN: TRANSACTIONS
app.get('/admin/transactions', requireAdmin, (req, res) => {
    const pending = transactions.filter(t => t.status === 'pending');
    
    const svgCheckCircle = '<svg viewBox="0 0 24 24" width="56" height="56" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><path d="M22 4 12 14.01l-3-3"/></svg>';
    const svgCheck = '<svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6 9 17l-5-5"/></svg>';
    const svgX = '<svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M18 6 6 18M6 6l12 12"/></svg>';
    const svgCard = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="2" y="5" width="20" height="14" rx="2"/><path d="M2 10h20"/></svg>';

    if (pending.length === 0) {
        return res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Transactions - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('transactions')}
    <div class="container admin-shell">
        <div class="admin-card">
            <div class="empty-state">
                <span class="auth-success-icon">${svgCheckCircle}</span>
                <h2>No Pending Transactions</h2>
                <p>All caught up! Every gift card verification has been processed.</p>
            </div>
        </div>
    </div>
</body>
</html>
        `);
    }
    
    const txRows = pending.map(t => `
        <tr>
            <td>
                <div class="table-user">
                    <span class="table-user-name">${t.userEmail}</span>
                    <span class="table-user-sub">User ID: ${t.userId}</span>
                </div>
            </td>
            <td>${t.cardType}</td>
            <td>$50+</td>
            <td>
                <a href="/uploads/${t.frontImage}" target="_blank" style="color:var(--md-primary);margin-right:10px;font-weight:600;">Front</a>
                <a href="/uploads/${t.backImage}" target="_blank" style="color:var(--md-primary);font-weight:600;">Back</a>
            </td>
            <td>${new Date(t.createdAt).toLocaleDateString()}</td>
            <td>
                <div class="admin-actions">
                    <form action="/admin/transactions/${t.id}/approve" method="POST">
                        <button type="submit" class="btn btn-xs btn-success">${svgCheck} Approve</button>
                    </form>
                    <form action="/admin/transactions/${t.id}/reject" method="POST">
                        <button type="submit" class="btn btn-xs btn-danger">${svgX} Reject</button>
                    </form>
                </div>
            </td>
        </tr>
    `).join('');
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Pending Payments - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('transactions')}

    <div class="container admin-shell">
        <div class="admin-head">
            <h2 class="admin-title">${svgCard} Pending Gift Card Verifications</h2>
            <p class="admin-subtitle">${pending.length} payment${pending.length !== 1 ? 's' : ''} awaiting review.</p>
        </div>
        <div class="admin-card">
            <div class="table-wrap">
                <table class="data-table">
                    <thead>
                        <tr>
                            <th>User</th>
                            <th>Card Type</th>
                            <th>Amount</th>
                            <th>Images</th>
                            <th>Date</th>
                            <th>Actions</th>
                        </tr>
                    </thead>
                    <tbody>${txRows}</tbody>
                </table>
            </div>
        </div>
    </div>
</body>
</html>
    `);
});

app.post('/admin/transactions/:id/approve', requireAdmin, (req, res) => {
    const tx = transactions.find(t => t.id === parseInt(req.params.id));
    if (tx && tx.status === 'pending') {
        tx.status = 'approved';
        const user = users.find(u => u.id === tx.userId);
        if (user) {
            const addedCoins = tx.coinsRequested || tx.amount || 0;
            user.coins += addedCoins;
            user.isTrialActive = false;
            createNotification(user.id, 'payment', `Your payment was approved! ${addedCoins.toLocaleString()} coins have been added to your account.`);
        }
    }
    res.redirect('/admin/transactions');
});

app.post('/admin/transactions/:id/reject', requireAdmin, (req, res) => {
    const tx = transactions.find(t => t.id === parseInt(req.params.id));
    if (tx) {
        tx.status = 'rejected';
        const user = users.find(u => u.id === tx.userId);
        if (user) {
            createNotification(user.id, 'payment', 'Your payment was rejected. Please contact support for assistance.');
        }
    }
    res.redirect('/admin/transactions');
});

// ADMIN: CENSORSHIP ALERTS
app.get('/admin/censorship', requireAdmin, (req, res) => {
    const pendingAlerts = censorshipLogs.filter(c => c.status === 'pending_review');
    
    const svgAlert = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="m21.73 18-8-14a2 2 0 0 0-3.48 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.73-3Z"/><path d="M12 9v4"/><path d="M12 17h.01"/></svg>';
    const svgCheck = '<svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6 9 17l-5-5"/></svg>';
    const svgShield = '<svg viewBox="0 0 24 24" width="56" height="56" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10Z"/><path d="m9 12 2 2 4-4"/></svg>';
    const svgArrow = '<svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" style="vertical-align:-2px;margin:0 6px;"><path d="M5 12h14"/><path d="m12 5 7 7-7 7"/></svg>';

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Censorship Alerts - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('censorship')}

    <div class="container admin-shell">
        <div class="admin-head">
            <h2 class="admin-title">${svgAlert} Censorship Alerts</h2>
            <p class="admin-subtitle">${pendingAlerts.length} message${pendingAlerts.length !== 1 ? 's' : ''} flagged for review.</p>
        </div>

        ${pendingAlerts.length === 0 ? `
        <div class="admin-card">
            <div class="empty-state">
                <span class="auth-success-icon">${svgShield}</span>
                <h2>No Pending Alerts</h2>
                <p>Nothing has been flagged by the content filter.</p>
            </div>
        </div>` : `
            <div style="display:flex;flex-direction:column;gap:18px;">
                ${pendingAlerts.map(alert => `
                    <div class="admin-card" style="border-left:4px solid var(--md-secondary);">
                        <div style="display:flex;justify-content:space-between;align-items:flex-start;gap:16px;flex-wrap:wrap;margin-bottom:16px;">
                            <div>
                                <h4 class="detail-title" style="margin-bottom:4px;">${alert.fromUserName}${svgArrow}${alert.toUserName || 'Unknown'}</h4>
                                <p class="admin-subtitle" style="margin:0;">${new Date(alert.timestamp).toLocaleString()}</p>
                            </div>
                            <form action="/admin/censorship/${alert.id}/resolve" method="POST">
                                <button type="submit" class="btn btn-xs btn-success">${svgCheck} Mark Reviewed</button>
                            </form>
                        </div>

                        <div class="fact" style="margin-bottom:12px;">
                            <span class="fact-label">Original</span>
                            <p style="font-family:monospace;background:var(--md-warning-container);padding:12px;border-radius:var(--md-radius-md);word-break:break-all;margin:0;">${alert.originalText}</p>
                        </div>

                        <div class="fact">
                            <span class="fact-label">Censored</span>
                            <p style="font-family:monospace;background:var(--md-success-container);padding:12px;border-radius:var(--md-radius-md);word-break:break-all;margin:0;">${alert.censoredText}</p>
                        </div>
                    </div>
                `).join('')}
            </div>
        `}
    </div>
</body>
</html>
    `);
});

app.post('/admin/censorship/:id/resolve', requireAdmin, (req, res) => {
    const alert = censorshipLogs.find(c => c.id === parseInt(req.params.id));
    if (alert) alert.status = 'reviewed';
    res.redirect('/admin/censorship');
});

// ==========================================
// REPORT SYSTEM
// ==========================================

// Submit report
app.post('/report/:userId', requireAuth, (req, res) => {
    const reporter = users.find(u => u.id === req.session.userId);
    const reportedId = parseInt(req.params.userId);
    const reported = users.find(u => u.id === reportedId);
    const { reason, details } = req.body;
    
    if (!reported) {
        return res.send('<script>alert("User not found!"); window.location="/dashboard";</script>');
    }
    
    const report = {
        id: reports.length + 1,
        reporterId: reporter.id,
        reporterName: reporter.name,
        reporterEmail: reporter.email,
        reportedId: reportedId,
        reportedName: reported.name,
        reportedEmail: reported.email,
        reason: reason,
        details: details || '',
        status: 'pending',
        createdAt: new Date(),
        reviewedBy: null,
        reviewedAt: null,
        action: null
    };
    
    reports.push(report);
    
    // Notify admin
    createNotification(1, 'report', `New report: ${reporter.name} reported ${reported.name}`, { reportId: report.id });
    
    res.send('<script>alert("Report submitted. Thank you for helping keep our community safe."); window.location="/dashboard";</script>');
});

// Admin view reports
app.get('/admin/reports', requireAdmin, (req, res) => {
    const { status } = req.query;
    
    let filteredReports = reports;
    if (status) {
        filteredReports = reports.filter(r => r.status === status);
    }
    
    const svgFlag = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1z"/><line x1="4" y1="22" x2="4" y2="15"/></svg>';

    const statusChip = (s) => s === 'pending' ? 'is-pending' : s === 'resolved' ? 'is-success' : 'is-danger';

    const reportRows = filteredReports.sort((a, b) => b.createdAt - a.createdAt).map(r => `
        <tr>
            <td>
                <div class="table-user">
                    <span class="table-user-name">#${r.id}</span>
                    <span class="table-user-sub">${new Date(r.createdAt).toLocaleDateString()}</span>
                </div>
            </td>
            <td>
                <div class="table-user">
                    <span class="table-user-name">${r.reporterName}</span>
                    <span class="table-user-sub">${r.reporterEmail}</span>
                </div>
            </td>
            <td>
                <div class="table-user">
                    <span class="table-user-name">${r.reportedName}</span>
                    <span class="table-user-sub">${r.reportedEmail}</span>
                </div>
            </td>
            <td>
                <span class="status-chip" style="background:${getReportReasonColor(r.reason)};color:#fff;">${r.reason}</span>
            </td>
            <td><span class="status-chip ${statusChip(r.status)}" style="text-transform:capitalize;">${r.status}</span></td>
            <td>
                <a href="/admin/reports/${r.id}" class="btn btn-xs btn-primary">View</a>
            </td>
        </tr>
    `).join('');
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Reports - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('reports')}

    <div class="container admin-shell">
        <div class="admin-head">
            <h2 class="admin-title">${svgFlag} User Reports</h2>
            <p class="admin-subtitle">Review and action member-submitted reports.</p>
        </div>

        <div class="admin-quicknav" style="margin-bottom:20px;">
            <a href="/admin/reports" class="btn btn-xs ${!status ? 'btn-primary' : 'btn-outline'}">All</a>
            <a href="/admin/reports?status=pending" class="btn btn-xs ${status === 'pending' ? 'btn-primary' : 'btn-outline'}">Pending</a>
            <a href="/admin/reports?status=resolved" class="btn btn-xs ${status === 'resolved' ? 'btn-primary' : 'btn-outline'}">Resolved</a>
            <a href="/admin/reports?status=dismissed" class="btn btn-xs ${status === 'dismissed' ? 'btn-primary' : 'btn-outline'}">Dismissed</a>
        </div>

        <div class="admin-card">
            <div class="table-wrap">
                <table class="data-table">
                    <thead>
                        <tr>
                            <th>ID</th>
                            <th>Reporter</th>
                            <th>Reported User</th>
                            <th>Reason</th>
                            <th>Status</th>
                            <th>Actions</th>
                        </tr>
                    </thead>
                    <tbody>
                        ${reportRows || '<tr><td colspan="6" class="empty-row">No reports found</td></tr>'}
                    </tbody>
                </table>
            </div>
        </div>
    </div>
</body>
</html>
    `);
});

function getReportReasonColor(reason) {
    const colors = {
        'Fake Profile': '#f44336',
        'Inappropriate Content': '#ff9800',
        'Harassment': '#9c27b0',
        'Scam': '#d32f2f',
        'Underage': '#e91e63',
        'Other': '#607d8b'
    };
    return colors[reason] || '#607d8b';
}

// View single report
app.get('/admin/reports/:id', requireAdmin, (req, res) => {
    const report = reports.find(r => r.id === parseInt(req.params.id));
    if (!report) return res.redirect('/admin/reports');
    
    const reported = users.find(u => u.id === report.reportedId);
    const reporter = users.find(u => u.id === report.reporterId);
    
    const svgWarn = '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="m21.73 18-8-14a2 2 0 0 0-3.48 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.73-3Z"/><path d="M12 9v4"/><path d="M12 17h.01"/></svg>';
    const svgBlock = '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="m4.9 4.9 14.2 14.2"/></svg>';
    const svgCheck = '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6 9 17l-5-5"/></svg>';
    const statusChipClass = report.status === 'pending' ? 'is-pending' : report.status === 'resolved' ? 'is-success' : 'is-danger';

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Report #${report.id} - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('reports')}

    <div class="container admin-shell">
        <div class="admin-card">
            <div style="display:flex;justify-content:space-between;align-items:center;gap:16px;flex-wrap:wrap;margin-bottom:24px;">
                <h2 class="admin-title" style="margin:0;">Report #${report.id}</h2>
                <span class="status-chip ${statusChipClass}">${report.status.toUpperCase()}</span>
            </div>

            <div class="fact-grid" style="margin-bottom:20px;">
                <div class="fact">
                    <span class="fact-label">Reporter</span>
                    <span class="fact-value">${report.reporterName}</span>
                    <span class="table-user-sub">${report.reporterEmail}</span>
                    <a href="/admin/users/${report.reporterId}/view" class="btn btn-xs btn-outline" style="margin-top:10px;align-self:flex-start;">View Profile</a>
                </div>
                <div class="fact">
                    <span class="fact-label">Reported User</span>
                    <span class="fact-value">${report.reportedName}</span>
                    <span class="table-user-sub">${report.reportedEmail}</span>
                    <a href="/admin/users/${report.reportedId}/view" class="btn btn-xs btn-outline" style="margin-top:10px;align-self:flex-start;">View Profile</a>
                </div>
            </div>

            <div class="fact" style="margin-bottom:16px;">
                <span class="fact-label">Reason</span>
                <span class="fact-value" style="color:${getReportReasonColor(report.reason)};">${report.reason}</span>
            </div>

            <div class="fact" style="margin-bottom:24px;">
                <span class="fact-label">Details</span>
                <p style="background:var(--md-surface-dim);padding:15px;border-radius:var(--md-radius-md);margin:8px 0 0;line-height:1.6;">${report.details || 'No additional details provided.'}</p>
            </div>

            ${report.status === 'pending' ? `
                <div class="admin-btn-row">
                    <form method="POST" action="/admin/reports/${report.id}/resolve">
                        <button type="submit" name="action" value="warn" class="btn btn-warning">${svgWarn} Warn User</button>
                    </form>
                    <form method="POST" action="/admin/reports/${report.id}/resolve">
                        <button type="submit" name="action" value="block" class="btn btn-danger">${svgBlock} Block User</button>
                    </form>
                    <form method="POST" action="/admin/reports/${report.id}/dismiss">
                        <button type="submit" class="btn btn-outline">${svgCheck} Dismiss</button>
                    </form>
                </div>
            ` : `
                <div class="auth-info-box" style="background:var(--md-success-container);">
                    <div>
                        <p style="color:var(--md-success);margin-bottom:4px;"><strong>Action Taken:</strong> ${report.action || 'None'}</p>
                        <p class="table-user-sub" style="margin:0;">Reviewed on ${new Date(report.reviewedAt).toLocaleString()}</p>
                    </div>
                </div>
            `}
        </div>
    </div>
</body>
</html>
    `);
});

// Resolve report
app.post('/admin/reports/:id/resolve', requireAdmin, (req, res) => {
    const report = reports.find(r => r.id === parseInt(req.params.id));
    if (!report) return res.redirect('/admin/reports');
    
    const action = req.body.action;
    const reported = users.find(u => u.id === report.reportedId);
    
    report.status = 'resolved';
    report.action = action === 'block' ? 'User Blocked' : 'User Warned';
    report.reviewedBy = req.session.userId;
    report.reviewedAt = new Date();
    
    if (action === 'block' && reported) {
        reported.isBlocked = true;
    }
    
    // Notify reporter
    createNotification(report.reporterId, 'report_update', `Your report against ${report.reportedName} has been resolved. Action: ${report.action}`);
    
    res.redirect('/admin/reports');
});

// Dismiss report
app.post('/admin/reports/:id/dismiss', requireAdmin, (req, res) => {
    const report = reports.find(r => r.id === parseInt(req.params.id));
    if (!report) return res.redirect('/admin/reports');
    
    report.status = 'dismissed';
    report.action = 'No action taken';
    report.reviewedBy = req.session.userId;
    report.reviewedAt = new Date();
    
    res.redirect('/admin/reports');
});

// ==========================================
// API ROUTES FOR NOTIFICATIONS & PREFERENCES
// ==========================================

// Get notification preferences
app.get('/api/notifications/preferences', requireAuth, (req, res) => {
    const prefs = getNotificationPrefs(req.session.userId);
    const user = users.find(u => u.id === req.session.userId);
    
    res.json({
        soundEnabled: prefs.soundEnabled,
        autoStop: user.gender === 'male',
        manualStop: user.gender === 'female',
        isPlaying: prefs.isPlaying
    });
});

// Update notification preferences
app.put('/api/notifications/preferences', requireAuth, (req, res) => {
    const { soundEnabled } = req.body;
    const prefs = getNotificationPrefs(req.session.userId);
    
    if (soundEnabled !== undefined) prefs.soundEnabled = soundEnabled;
    
    res.json({ success: true, soundEnabled: prefs.soundEnabled });
});

// Female manually stops sound
app.post('/api/notifications/stop-sound', requireAuth, isFemale, (req, res) => {
    stopNotificationSound(req.session.userId);
    res.json({ success: true, message: 'Sound stopped' });
});

// Trigger sound for testing (internal use)
app.post('/api/notifications/trigger', requireAuth, (req, res) => {
    const result = triggerNotificationSound(req.session.userId);
    res.json(result);
});

// Typing indicator REST endpoints (fallback for non-socket clients)
app.post('/api/typing/start', requireAuth, (req, res) => {
    const { receiverId } = req.body;
    const senderId = req.session.userId;
    
    broadcastTyping(senderId, receiverId, true);
    
    // Auto-clear after 3 seconds
    setTimeout(() => {
        broadcastTyping(senderId, receiverId, false);
    }, 3000);
    
    res.json({ success: true });
});

app.post('/api/typing/stop', requireAuth, (req, res) => {
    const { receiverId } = req.body;
    const senderId = req.session.userId;
    
    broadcastTyping(senderId, receiverId, false);
    res.json({ success: true });
});

// Mark message as read via API
app.post('/api/messages/:id/read', requireAuth, (req, res) => {
    const messageId = parseInt(req.params.id);
    const readerId = req.session.userId;
    
    const message = messages.find(m => m.id === messageId || m.time.getTime() === messageId);
    
    if (!message) {
        return res.status(404).json({ error: 'Message not found' });
    }
    
    if (message.to !== readerId) {
        return res.status(403).json({ error: 'Not authorized' });
    }
    
    message.read = true;
    
    // Broadcast read receipt
    broadcastReadReceipt(messageId, message.from, readerId);
    
    res.json({ success: true, read: true });
});

// ==========================================
// API ROUTES FOR GENDER-BASED FEATURES
// ==========================================

// Male: Get profiles with filters
app.get('/api/profiles', requireAuth, isMale, (req, res) => {
    const { minAge, maxAge, location, interests } = req.query;
    
    let filtered = users.filter(u => 
        u.gender === 'female' && 
        u.role === 'user' && 
        !u.isBlocked
    );
    
    if (minAge) filtered = filtered.filter(u => u.age >= parseInt(minAge));
    if (maxAge) filtered = filtered.filter(u => u.age <= parseInt(maxAge));
    if (location) filtered = filtered.filter(u => 
        u.location.toLowerCase().includes(location.toLowerCase())
    );
    if (interests) filtered = filtered.filter(u => 
        u.interests && u.interests.toLowerCase().includes(interests.toLowerCase())
    );
    
    res.json(filtered.map(u => ({
        id: u.id,
        name: u.name,
        age: u.age,
        location: u.location,
        country: u.country,
        photo: u.photo,
        isOnline: u.isOnline,
        interests: u.interests,
        occupation: u.occupation,
        bio: u.bio
    })));
});

// Female: Get assigned males (only those who messaged first)
app.get('/api/female/contacts', requireAuth, isFemale, (req, res) => {
    const femaleId = req.session.userId;
    
    // Get assigned males
    const assigned = adminAssignments.filter(a => a.femaleId === femaleId);
    
    // Filter to only those who sent message first
    const availableMales = assigned.map(a => {
        const male = users.find(u => u.id === a.maleId);
        if (!male) return null;
        
        // Check if male sent message first
        const maleSentFirst = messages.find(m => m.from === male.id && m.to === femaleId);
        
        // Get unread count
        const unreadCount = messages.filter(m => 
            m.from === male.id && 
            m.to === femaleId && 
            !m.read
        ).length;
        
        // Get last message
        const lastMessage = messages
            .filter(m => (m.from === male.id && m.to === femaleId) || (m.from === femaleId && m.to === male.id))
            .sort((a, b) => b.time - a.time)[0];
        
        return {
            ...male,
            canChat: !!maleSentFirst,
            maleMessagedFirst: !!maleSentFirst,
            unreadCount,
            lastMessage: lastMessage ? {
                text: lastMessage.text,
                time: lastMessage.time,
                isFromMe: lastMessage.from === femaleId
            } : null
        };
    }).filter(Boolean);
    
    res.json(availableMales);
});

// Get unread message count for polling
app.get('/api/messages/unread-count', requireAuth, (req, res) => {
    const partnerId = parseInt(req.query.partnerId);
    const userId = req.session.userId;
    
    const unreadCount = messages.filter(m => 
        m.to === userId && 
        m.from === partnerId && 
        !m.read
    ).length;
    
    res.json({ 
        newMessages: unreadCount,  
        totalUnread: messages.filter(m => m.to === userId && !m.read).length  
    });
});

// Get total unread message count for header badge refresh
app.get('/api/messages/unread-count-total', requireAuth, (req, res) => {
    const count = messages.filter(m => m.to === req.session.userId && !m.read).length;
    res.json({ count });
});

// Poll for messages received in an open conversation.
app.get('/api/messages/check-new', requireAuth, (req, res) => {
    const userId = req.session.userId;
    const partnerId = parseInt(req.query.partnerId, 10);
    const sinceTime = req.query.since ? new Date(req.query.since).getTime() : 0;

    if (!Number.isInteger(partnerId) || Number.isNaN(sinceTime)) {
        return res.status(400).json({ hasNewMessages: false, messages: [] });
    }

    const newMessages = messages.filter(message =>
        message.to === userId &&
        message.from === partnerId &&
        new Date(message.time).getTime() > sinceTime
    );

    newMessages.forEach(message => {
        message.read = true;
    });

    res.json({
        hasNewMessages: newMessages.length > 0,
        messages: newMessages.map(message => ({
            id: message.id || `${message.from}-${new Date(message.time).getTime()}-${message.type}`,
            from: message.from,
            to: message.to,
            text: message.text,
            type: message.type,
            photoFile: message.photoFile,
            time: message.time,
            censored: message.censored,
            cost: message.cost
        }))
    });
});

// Get online status of a user
app.get('/api/users/:id/online-status', requireAuth, (req, res) => {
    const user = users.find(u => u.id === parseInt(req.params.id));
    if (!user) return res.status(404).json({ error: 'User not found' });
    
    res.json({
        isOnline: user.isOnline,
        lastSeen: user.lastActive
    });
});

// ==========================================
// SOCKET.IO CONNECTION HANDLER
// ==========================================

io.on('connection', (socket) => {
    console.log('Socket connected:', socket.id);
    
    // Authenticate user
    socket.on('authenticate', (userId) => {
        connectedUsers.set(userId, socket.id);
        socket.userId = userId;
        
        // Update online status
        const user = users.find(u => u.id === userId);
        if (user) {
            user.isOnline = true;
            user.lastActive = new Date();
        }
        
        // Broadcast online status to chat partners
        const chatPartners = new Set();
        messages.forEach(m => {
            if (m.from === userId) chatPartners.add(m.to);
            if (m.to === userId) chatPartners.add(m.from);
        });
        
        chatPartners.forEach(partnerId => {
            emitToUser(partnerId, 'user_online', { userId: userId, isOnline: true });
        });
        
        console.log(`User ${userId} authenticated on socket ${socket.id}`);
    });
    
    // Handle typing indicator
    socket.on('typing', (data) => {
        const { receiverId, isTyping } = data;
        const senderId = socket.userId;
        
        if (!senderId) return;
        
        // Clear existing timeout
        if (typingUsers.has(senderId)) {
            clearTimeout(typingUsers.get(senderId).timeout);
        }
        
        if (isTyping) {
            // Broadcast typing start
            broadcastTyping(senderId, receiverId, true);
            
            // Auto-stop typing after 3 seconds of inactivity
            const timeout = setTimeout(() => {
                broadcastTyping(senderId, receiverId, false);
                typingUsers.delete(senderId);
            }, 3000);
            
            typingUsers.set(senderId, { partnerId: receiverId, timeout });
        } else {
            // Broadcast typing stop
            broadcastTyping(senderId, receiverId, false);
            typingUsers.delete(senderId);
        }
    });
    
    // Handle message read receipt
    socket.on('message_read', (data) => {
        const { messageId, senderId } = data;
        const readerId = socket.userId;
        
        // Mark message as read in database
        const message = messages.find(m => m.id === messageId || (m.time && m.time.getTime() === new Date(data.messageTime).getTime()));
        if (message && message.to === readerId) {
            message.read = true;
            
            // Broadcast to original sender
            broadcastReadReceipt(messageId, senderId, readerId);
        }
    });
    
    // Handle manual sound stop (for females)
    socket.on('stop_sound', () => {
        stopNotificationSound(socket.userId);
    });
    
    // Handle disconnect
    socket.on('disconnect', () => {
        const userId = socket.userId;
        
        if (userId) {
            connectedUsers.delete(userId);
            
            // Clear typing status
            if (typingUsers.has(userId)) {
                clearTimeout(typingUsers.get(userId).timeout);
                const partnerId = typingUsers.get(userId).partnerId;
                broadcastTyping(userId, partnerId, false);
                typingUsers.delete(userId);
            }
            
            // Update offline status
            const user = users.find(u => u.id === userId);
            if (user) {
                user.isOnline = false;
                user.lastActive = new Date();
            }
            
            // Broadcast offline status
            const chatPartners = new Set();
            messages.forEach(m => {
                if (m.from === userId) chatPartners.add(m.to);
                if (m.to === userId) chatPartners.add(m.from);
            });
            
            chatPartners.forEach(partnerId => {
                emitToUser(partnerId, 'user_online', { userId: userId, isOnline: false, lastSeen: new Date() });
            });
        }
        
        console.log('Socket disconnected:', socket.id);
    });
});

// ==========================================
// ADMIN CHAT MONITORING
// ==========================================

// View all chats list
app.get('/admin/chats', requireAdmin, (req, res) => {
    const chatPairs = new Map();

    messages.forEach(m => {
        const pairKey = [Math.min(m.from, m.to), Math.max(m.from, m.to)].join('-');
        if (!chatPairs.has(pairKey)) {
            chatPairs.set(pairKey, {
                user1: users.find(u => u.id === Math.min(m.from, m.to)),
                user2: users.find(u => u.id === Math.max(m.from, m.to)),
                lastMessage: m,
                messageCount: 0
            });
        }

        const pair = chatPairs.get(pairKey);
        pair.messageCount++;
        if (m.time > pair.lastMessage.time) {
            pair.lastMessage = m;
        }
    });

    const sortedChats = Array.from(chatPairs.values())
        .filter(chat => chat.user1 && chat.user2)
        .sort((a, b) => b.lastMessage.time - a.lastMessage.time);

    const svgChat = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/></svg>';
    const svgPersonSm = '<svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/></svg>';
    const avatarCell = (u, grad) => `
        <div style="display:flex;align-items:center;gap:10px;">
            <div style="width:40px;height:40px;border-radius:50%;background:${grad};display:flex;align-items:center;justify-content:center;color:#fff;overflow:hidden;flex-shrink:0;">
                ${u.photo ? `<img src="/uploads/${u.photo}" alt="${u.name}" style="width:100%;height:100%;object-fit:cover;border-radius:50%;" onerror="this.style.display='none';this.nextElementSibling.style.display='flex';">` : ''}<span style="display:${u.photo ? 'none' : 'flex'};align-items:center;justify-content:center;">${svgPersonSm}</span>
            </div>
            <div class="table-user">
                <span class="table-user-name">${u.name}</span>
                <span class="table-user-sub" style="text-transform:capitalize;">${u.gender}</span>
            </div>
        </div>`;

    const chatRows = sortedChats.map(chat => `
        <tr>
            <td>${avatarCell(chat.user1, 'linear-gradient(135deg, var(--md-secondary), #764ba2)')}</td>
            <td>${avatarCell(chat.user2, 'linear-gradient(135deg, var(--md-primary), var(--md-primary-dark))')}</td>
            <td class="td-center"><span class="status-chip is-info">${chat.messageCount}</span></td>
            <td class="table-user-sub">${new Date(chat.lastMessage.time).toLocaleString()}</td>
            <td><a href="/admin/chats/${chat.user1.id}/${chat.user2.id}" class="btn btn-xs btn-primary">View Chat</a></td>
        </tr>
    `).join('');

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Chat Monitor - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('chats')}

    <div class="container admin-shell">
        <div class="admin-head">
            <h2 class="admin-title">${svgChat} Chat Monitor</h2>
            <p class="admin-subtitle">${sortedChats.length} active conversation${sortedChats.length !== 1 ? 's' : ''}.</p>
        </div>

        <div class="admin-card">
            <div class="table-wrap">
                <table class="data-table">
                    <thead>
                        <tr>
                            <th>User 1</th>
                            <th>User 2</th>
                            <th class="td-center">Messages</th>
                            <th>Last Activity</th>
                            <th>Actions</th>
                        </tr>
                    </thead>
                    <tbody>
                        ${chatRows || '<tr><td colspan="5" class="empty-row">No chats yet</td></tr>'}
                    </tbody>
                </table>
            </div>
        </div>
    </div>
</body>
</html>
    `);
});

// View specific chat
app.get('/admin/chats/:user1/:user2', requireAdmin, (req, res) => {
    const user1Id = parseInt(req.params.user1);
    const user2Id = parseInt(req.params.user2);

    const user1 = users.find(u => u.id === user1Id);
    const user2 = users.find(u => u.id === user2Id);

    if (!user1 || !user2) return res.redirect('/admin/chats');

    const chatMessages = messages.filter(m =>
        (m.from === user1Id && m.to === user2Id) ||
        (m.from === user2Id && m.to === user1Id)
    ).sort((a, b) => a.time - b.time);

    const svgPersonSm = '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/></svg>';
    const svgChat = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/></svg>';
    const svgArrowSm = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" style="vertical-align:-3px;margin:0 8px;opacity:.6;"><path d="M8 3 4 7l4 4"/><path d="M4 7h16"/><path d="m16 21 4-4-4-4"/><path d="M20 17H4"/></svg>';
    const svgDoubleCheck = '<svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" style="vertical-align:-2px;"><path d="M18 6 7 17l-5-5"/><path d="m22 10-7.5 7.5L13 16"/></svg>';
    const svgWarnSm = '<svg viewBox="0 0 24 24" width="12" height="12" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" style="vertical-align:-1px;margin-right:3px;"><path d="m21.73 18-8-14a2 2 0 0 0-3.48 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.73-3Z"/><path d="M12 9v4"/><path d="M12 17h.01"/></svg>';

    const messagesHtml = chatMessages.map(m => {
        const isFromUser1 = m.from === user1Id;
        const sender = isFromUser1 ? user1 : user2;

        return `
            <div style="margin-bottom:20px;display:flex;${isFromUser1 ? 'justify-content:flex-start' : 'justify-content:flex-end'};">
                <div style="max-width:70%;">
                    <div style="display:flex;align-items:center;gap:8px;margin-bottom:5px;${isFromUser1 ? '' : 'flex-direction:row-reverse;'}">
                        <div style="width:30px;height:30px;border-radius:50%;overflow:hidden;display:flex;align-items:center;justify-content:center;color:#fff;background:linear-gradient(135deg, ${isFromUser1 ? 'var(--md-secondary), #764ba2' : 'var(--md-primary), var(--md-primary-dark)'});">
                            ${sender.photo ? `<img src="/uploads/${sender.photo}" alt="${sender.name}" style="width:100%;height:100%;object-fit:cover;" onerror="this.style.display='none';this.nextElementSibling.style.display='flex';">` : ''}<span style="display:${sender.photo ? 'none' : 'flex'};">${svgPersonSm}</span>
                        </div>
                        <span style="font-size:12px;color:var(--md-on-surface-variant);">${sender.name}</span>
                    </div>
                    <div style="padding:14px 18px;border-radius:var(--md-radius-lg);background:${isFromUser1 ? 'var(--md-surface)' : 'linear-gradient(135deg, var(--md-primary), var(--md-secondary))'};color:${isFromUser1 ? 'var(--md-on-surface)' : '#fff'};box-shadow:var(--md-elev-1);${m.censored ? 'border:2px solid var(--md-warning);' : ''}">
                        ${m.censored ? `<div style="font-size:11px;color:var(--md-warning);margin-bottom:5px;font-weight:600;">${svgWarnSm}CENSORED</div>` : ''}
                        ${m.type === 'photo' ?
                            `<img src="/uploads/${m.photoFile}" alt="Shared photo" style="max-width:200px;border-radius:var(--md-radius-md);cursor:pointer;display:block;" onclick="showLightbox('${m.photoFile}')" onerror="this.onerror=null;this.style.background='var(--md-surface-variant)';this.style.minWidth='120px';this.style.minHeight='120px';this.removeAttribute('src');">` :
                            `<p style="line-height:1.6;margin:0;">${m.text}</p>`
                        }
                        <div style="font-size:11px;opacity:${isFromUser1 ? '0.55' : '0.8'};margin-top:8px;text-align:right;">
                            ${new Date(m.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'})}
                            ${m.read ? ` ${svgDoubleCheck} Read` : ` ${svgDoubleCheck}`}
                            ${m.cost > 0 ? ` &bull; ${m.cost} coins` : ''}
                        </div>
                    </div>
                </div>
            </div>
        `;
    }).join('');

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Chat: ${user1.name} & ${user2.name} - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('chats')}

    <div class="container admin-shell">
        <div class="admin-head" style="display:flex;justify-content:space-between;align-items:center;gap:16px;flex-wrap:wrap;">
            <h2 class="admin-title">${svgChat} ${user1.name}${svgArrowSm}${user2.name}</h2>
            <span class="status-chip is-info">${chatMessages.length} messages</span>
        </div>

        <div class="admin-card" style="background:var(--md-surface-dim);min-height:400px;">
            ${messagesHtml || '<p class="empty-row" style="text-align:center;">No messages in this conversation</p>'}
        </div>

        <div class="admin-btn-row" style="margin-top:24px;">
            <a href="/admin/users/${user1.id}/view" class="btn btn-outline">View ${user1.name}</a>
            <a href="/admin/users/${user2.id}/view" class="btn btn-outline">View ${user2.name}</a>
        </div>
    </div>

    <script>
        function showLightbox(photo) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;padding:16px;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="Shared photo" onerror="this.onerror=null; this.style.background=\\'#f0f2f5\\'; this.style.minWidth=\\'200px\\'; this.style.minHeight=\\'200px\\';" style="max-width:100%;max-height:100%;border-radius:16px;object-fit:contain;">';
            overlay.onclick = () => overlay.remove();
            document.body.appendChild(overlay);
        }
    </script>
</body>
</html>
    `);
});

// ==========================================
// ADMIN NOTIFICATION MANAGEMENT
// ==========================================

// Admin send notification page
app.get('/admin/notifications', requireAdmin, (req, res) => {
    const { filter } = req.query;
    
    let adminNotifications = notifications.filter(n => n.adminSent || n.type === 'admin');
    
    if (filter === 'unread') {
        adminNotifications = adminNotifications.filter(n => !n.read);
    }
    
    const svgPersonSm = '<svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/></svg>';
    const svgMegaphone = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="m3 11 18-5v12L3 14v-3z"/><path d="M11.6 16.8a3 3 0 1 1-5.8-1.6"/></svg>';
    const svgInbox = '<svg viewBox="0 0 24 24" width="24" height="24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M22 12h-6l-2 3h-4l-2-3H2"/><path d="M5.45 5.11 2 12v6a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2v-6l-3.45-6.89A2 2 0 0 0 16.76 4H7.24a2 2 0 0 0-1.79 1.11z"/></svg>';

    const notificationRows = adminNotifications.map(n => {
        const user = users.find(u => u.id === n.userId);
        return `
            <tr>
                <td>
                    <div style="display:flex;align-items:center;gap:10px;">
                        <div style="width:40px;height:40px;border-radius:50%;background:linear-gradient(135deg, var(--md-secondary), #764ba2);display:flex;align-items:center;justify-content:center;color:#fff;overflow:hidden;flex-shrink:0;">
                            ${user?.photo ? `<img src="/uploads/${user.photo}" alt="${user.name}" style="width:100%;height:100%;border-radius:50%;object-fit:cover;" onerror="this.style.display='none';this.nextElementSibling.style.display='flex';">` : ''}<span style="display:${user?.photo ? 'none' : 'flex'};">${svgPersonSm}</span>
                        </div>
                        <div class="table-user">
                            <span class="table-user-name">${user?.name || 'Unknown'}</span>
                            <span class="table-user-sub">${user?.email || ''}</span>
                        </div>
                    </div>
                </td>
                <td>
                    <div class="table-user-name">${n.title || 'Notification'}</div>
                    <div class="table-user-sub" style="max-width:300px;overflow:hidden;text-overflow:ellipsis;">${n.text}</div>
                </td>
                <td><span class="status-chip ${n.read ? 'is-success' : 'is-pending'}">${n.read ? 'Read' : 'Unread'}</span></td>
                <td class="table-user-sub">${new Date(n.createdAt).toLocaleString()}</td>
            </tr>
        `;
    }).join('');
    
    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#232849">
    <title>Send Notifications - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    ${renderAdminNav('notifications')}

    <div class="container admin-shell">
        <div class="grid grid-2">
            <div class="admin-card">
                <div class="admin-head">
                    <h2 class="admin-title">${svgMegaphone} Send Notification</h2>
                </div>

                <form method="POST" action="/admin/notifications/send">
                    <div class="form-group">
                        <label>Send To</label>
                        <select name="recipient" required>
                            <option value="all">All Users</option>
                            <option value="all_males">All Male Users</option>
                            <option value="all_females">All Female Users</option>
                            ${users.filter(u => u.role === 'user').map(u =>
                                `<option value="${u.id}">${u.name} (${u.gender})</option>`
                            ).join('')}
                        </select>
                    </div>

                    <div class="form-group">
                        <label>Title</label>
                        <input type="text" name="title" placeholder="Notification title" required>
                    </div>

                    <div class="form-group">
                        <label>Message</label>
                        <textarea name="message" rows="4" placeholder="Your message..." required></textarea>
                    </div>

                    <div class="form-group">
                        <label>Type</label>
                        <select name="type">
                            <option value="info">Info</option>
                            <option value="success">Success</option>
                            <option value="warning">Warning</option>
                            <option value="promo">Promotion</option>
                        </select>
                    </div>

                    <button type="submit" class="btn btn-primary btn-block">Send Notification</button>
                </form>
            </div>

            <div class="admin-card">
                <div class="admin-head">
                    <h2 class="admin-title">${svgInbox} Sent Notifications</h2>
                </div>

                <div class="admin-quicknav" style="margin-bottom:16px;">
                    <a href="/admin/notifications" class="btn btn-xs ${!filter ? 'btn-primary' : 'btn-outline'}">All</a>
                    <a href="/admin/notifications?filter=unread" class="btn btn-xs ${filter === 'unread' ? 'btn-primary' : 'btn-outline'}">Unread</a>
                </div>

                <div class="table-wrap" style="max-height:440px;overflow-y:auto;">
                    <table class="data-table">
                        <tbody>
                            ${notificationRows || '<tr><td class="empty-row">No notifications sent yet</td></tr>'}
                        </tbody>
                    </table>
                </div>
            </div>
        </div>
    </div>
</body>
</html>
    `);
});

// Send notification
app.post('/admin/notifications/send', requireAdmin, (req, res) => {
    const { recipient, title, message, type } = req.body;
    
    if (recipient === 'all') {
        notifyAllUsers(title, message, type);
    } else if (recipient === 'all_males') {
        notifyAllMales(title, message, type);
    } else if (recipient === 'all_females') {
        notifyAllFemales(title, message, type);
    } else {
        const userId = parseInt(recipient);
        sendAdminNotification(userId, title, message, type);
    }
    
    res.send('<script>alert("Notification sent!"); window.location="/admin/notifications";</script>');
});

// DEDICATED MESSAGES PAGE
app.get('/messages', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    if (!user) return res.redirect('/login');

    let inboxHTML;
    if (user.gender === 'male') {
        inboxHTML = generateMaleInbox(user);
    } else {
        const chatPartnerIds = getFemaleChatPartners(user.id);
        inboxHTML = generateFemaleInbox(user, chatPartnerIds);
    }

    const unreadCount = messages.filter(m => m.to === user.id && !m.read).length;

    res.send(`
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="theme-color" content="#4355b9">
    <title>Messages - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body class="has-bottom-nav">
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">
                    <span class="brand-mark" aria-hidden="true">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M20.8 8.8c0 5.2-8.8 10.3-8.8 10.3S3.2 14 3.2 8.8A4.7 4.7 0 0 1 12 6.1a4.7 4.7 0 0 1 8.8 2.7Z"></path></svg>
                    </span>
                    <span>FindYourMatch</span>
                </a>
                <div class="nav-actions">
                    <span class="unread-pill ${unreadCount > 0 ? 'has-unread' : 'all-read'}">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"/></svg>
                        ${unreadCount} unread
                    </span>
                    <a href="/logout" class="icon-button" aria-label="Logout">
                        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/></svg>
                    </a>
                </div>
            </div>
        </div>
    </nav>

    <div class="container messages-shell">
        <div class="section-heading">
            <div>
                <h2 class="page-title">
                    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 11.5a7.5 7.5 0 0 1-7.5 7.5H7l-4 3v-6.2A7.5 7.5 0 1 1 20 11.5Z"></path></svg>
                    Your Messages
                </h2>
                <p>Tap a conversation to continue chatting</p>
            </div>
        </div>
        ${inboxHTML}
    </div>
    ${getFooter()}
    ${renderBottomNav(user, 'messages')}
</body>
</html>
    `);
});

// START SERVER
if (require.main === module) {
    server.listen(PORT, () => {
        console.log('╔════════════════════════════════════════╗');
        console.log('║     💕 FINDYOURMATCH IS LIVE! 💕       ║');
        console.log('╠════════════════════════════════════════╣');
        console.log(`║  🌐 http://localhost:${PORT}              ║`);
        console.log('║                                        ║');
        console.log('║  📋 DEFAULT ACCOUNTS:                  ║');
        console.log('║  Admin: admin@site.com / admin123      ║');
        console.log('║  Female: sarah@site.com / password123  ║');
        console.log('║  Male: john@site.com / password123     ║');
        console.log('╚════════════════════════════════════════╝');
    });
}

module.exports = app;