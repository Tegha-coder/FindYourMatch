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
    return { canChat: false, message: '🔒 Purchase coins to chat', expired: true, daysLeft: 0 };
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
    /* Modern Font & Smooth Reset */
    * {
        margin: 0;
        padding: 0;
        box-sizing: border-box;
    }
    
    :root {
        --primary: #ff416c;
        --primary-dark: #ff4b2b;
        --secondary: #667eea;
        --accent: #764ba2;
        --success: #4caf50;
        --warning: #ff9800;
        --danger: #f44336;
        --info: #2196f3;
        --dark: #2c3e50;
        --light: #fcf8f9;
        --gray: #6b7280;
        --gray-light: #f3f4f6;
        --shadow-sm: 0 2px 4px rgba(0,0,0,0.05);
        --shadow-md: 0 4px 12px rgba(0,0,0,0.1);
        --shadow-lg: 0 10px 40px rgba(0,0,0,0.15);
        --shadow-glow: 0 4px 20px rgba(255, 65, 108, 0.3);
        --radius-sm: 8px;
        --radius-md: 16px;
        --radius-lg: 24px;
        --radius-xl: 50px;
    }
    
    html {
        scroll-behavior: smooth;
    }
    
    body {
        font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
        background: linear-gradient(135deg, #fcf8f9 0%, #f8f4f5 100%);
        color: var(--dark);
        line-height: 1.6;
        min-height: 100vh;
        padding-top: 80px; /* Space for fixed navbar */
    }

    /* Broken image fallback */
    img {
        background: linear-gradient(135deg, #f0f2f5, #e4e6e9);
        min-height: 100px;
    }

    img[alt]:before {
        content: attr(alt);
        display: flex;
        align-items: center;
        justify-content: center;
        height: 100%;
        color: #888;
        font-size: 14px;
    }

    @media (max-width: 768px) {
        body {
            padding-top: 70px;
        }
    }
    
    /* Glassmorphic Navbar */
    .navbar {
        position: fixed;
        top: 0;
        left: 0;
        right: 0;
        z-index: 1000;
        background: rgba(255, 255, 255, 0.85);
        backdrop-filter: blur(20px);
        -webkit-backdrop-filter: blur(20px);
        border-bottom: 1px solid rgba(255, 255, 255, 0.3);
        box-shadow: var(--shadow-sm);
    }
    
    .nav-content {
        max-width: 1400px;
        margin: 0 auto;
        padding: 16px 24px;
        display: flex;
        justify-content: space-between;
        align-items: center;
    }
    
    @media (max-width: 768px) {
        .nav-content {
            padding: 12px 16px;
            flex-wrap: wrap;
            gap: 12px;
        }

        .nav-content > div {
            display: flex;
            align-items: center;
            gap: 8px;
            flex-wrap: wrap;
            justify-content: flex-end;
        }

        .btn {
            padding: 10px 16px;
            font-size: 14px;
        }

        .btn-sm {
            padding: 8px 12px;
            font-size: 12px;
        }

        .card {
            margin: 0;
        }

        .grid {
            gap: 16px;
        }

        .hero {
            padding: 100px 16px 60px;
        }

        .hero h1 {
            font-size: 32px;
        }

        .profile-card-image {
            height: 180px;
        }

        .inbox-item {
            padding: 12px;
        }

        .avatar {
            width: 48px;
            height: 48px;
        }

        .chat-messages {
            padding-bottom: 180px;
        }

        .chat-input-area {
            padding: 12px 16px 16px;
        }

        .stats-card {
            padding: 20px;
        }

        .stats-number {
            font-size: 28px;
        }
    }

    /* Tablet */
    @media (min-width: 769px) and (max-width: 1024px) {
        .container {
            padding: 0 20px;
        }

        .grid-3 {
            grid-template-columns: repeat(2, 1fr);
        }
    }

    /* Large screens */
    @media (min-width: 1400px) {
        .container {
            max-width: 1400px;
        }
    }
    
    .logo {
        font-size: 28px;
        font-weight: 800;
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        text-decoration: none;
        letter-spacing: -0.5px;
        display: flex;
        align-items: center;
        gap: 12px;
    }
    
    .logo img {
        height: 40px;
        width: auto;
        border-radius: 8px;
    }
    
    @media (max-width: 768px) {
        .logo {
            font-size: 20px;
            gap: 8px;
        }
        .logo img {
            height: 32px;
        }
    }
    
    /* Modern Buttons */
    .btn {
        display: inline-flex;
        align-items: center;
        justify-content: center;
        gap: 8px;
        padding: 12px 28px;
        border-radius: var(--radius-xl);
        font-weight: 600;
        font-size: 15px;
        text-decoration: none;
        border: none;
        cursor: pointer;
        transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1);
        position: relative;
        overflow: hidden;
    }
    
    .btn::before {
        content: '';
        position: absolute;
        top: 0;
        left: -100%;
        width: 100%;
        height: 100%;
        background: linear-gradient(90deg, transparent, rgba(255,255,255,0.3), transparent);
        transition: left 0.5s;
    }
    
    .btn:hover::before {
        left: 100%;
    }
    
    .btn-primary {
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        color: white;
        box-shadow: var(--shadow-glow);
    }
    
    .btn-primary:hover {
        transform: translateY(-2px);
        box-shadow: 0 8px 30px rgba(255, 65, 108, 0.5);
    }
    
    .btn-secondary {
        background: transparent;
        color: var(--primary);
        border: 2px solid var(--primary);
    }
    
    .btn-secondary:hover {
        background: var(--primary);
        color: white;
        transform: translateY(-2px);
    }
    
    .btn-success {
        background: linear-gradient(45deg, #45a049, var(--success));
        color: white;
    }
    
    .btn-danger {
        background: linear-gradient(45deg, #d32f2f, var(--danger));
        color: white;
    }
    
    .btn-warning {
        background: linear-gradient(45deg, #f57c00, var(--warning));
        color: white;
    }
    
    .btn-outline {
        background: transparent;
        color: var(--gray);
        border: 2px solid var(--gray-light);
    }
    
    .btn-outline:hover {
        border-color: var(--primary);
        color: var(--primary);
    }
    
    .btn-sm {
        padding: 8px 20px;
        font-size: 13px;
    }
    
    .btn-lg {
        padding: 18px 40px;
        font-size: 17px;
    }
    
    /* Modern Cards with Glass Effect */
    .card {
        background: rgba(255, 255, 255, 0.95);
        backdrop-filter: blur(10px);
        border-radius: var(--radius-lg);
        overflow: hidden;
        box-shadow: var(--shadow-md);
        transition: all 0.3s ease;
        border: 1px solid rgba(255, 255, 255, 0.5);
    }
    
    .card:hover {
        transform: translateY(-8px);
        box-shadow: var(--shadow-lg);
    }
    
    /* Forms */
    .form-group {
        margin-bottom: 24px;
    }
    
    .form-group label {
        display: block;
        margin-bottom: 8px;
        font-weight: 500;
        color: var(--dark);
        font-size: 14px;
    }
    
    .form-group input,
    .form-group select,
    .form-group textarea {
        width: 100%;
        padding: 14px 18px;
        border: 2px solid var(--gray-light);
        border-radius: var(--radius-md);
        font-size: 15px;
        transition: all 0.3s;
        background: white;
    }
    
    .form-group input:focus,
    .form-group select:focus,
    .form-group textarea:focus {
        outline: none;
        border-color: var(--primary);
        box-shadow: 0 0 0 4px rgba(255, 65, 108, 0.1);
    }
    
    /* Grid System */
    .grid {
        display: grid;
        gap: 24px;
    }
    
    .grid-2 {
        grid-template-columns: repeat(2, 1fr);
    }
    
    .grid-3 {
        grid-template-columns: repeat(3, 1fr);
    }
    
    .grid-4 {
        grid-template-columns: repeat(4, 1fr);
    }
    
    @media (max-width: 1024px) {
        .grid-4 {
            grid-template-columns: repeat(2, 1fr);
        }
    }
    
    @media (max-width: 768px) {
        .grid-2, .grid-3, .grid-4 {
            grid-template-columns: 1fr;
        }
    }
    
    /* Container */
    .container {
        max-width: 1400px;
        margin: 0 auto;
        padding: 0 24px;
    }
    
    @media (max-width: 768px) {
        .container {
            padding: 0 16px;
        }
    }
    
    /* Hero Section */
    .hero {
        position: relative;
        min-height: 100vh;
        display: flex;
        align-items: center;
        justify-content: center;
        padding: 40px 24px 80px;
        background: linear-gradient(135deg, rgba(102, 126, 234, 0.1) 0%, rgba(118, 75, 162, 0.1) 100%);
        overflow: hidden;
    }
    
    .hero::before {
        content: '';
        position: absolute;
        top: -50%;
        right: -20%;
        width: 800px;
        height: 800px;
        background: radial-gradient(circle, rgba(255, 65, 108, 0.15) 0%, transparent 70%);
        border-radius: 50%;
    }
    
    .hero::after {
        content: '';
        position: absolute;
        bottom: -30%;
        left: -10%;
        width: 600px;
        height: 600px;
        background: radial-gradient(circle, rgba(102, 126, 234, 0.1) 0%, transparent 70%);
        border-radius: 50%;
    }
    
    .hero-content {
        position: relative;
        z-index: 2;
        text-align: center;
        max-width: 700px;
    }
    
    .hero h1 {
        font-size: 56px;
        font-weight: 800;
        margin-bottom: 24px;
        line-height: 1.1;
        letter-spacing: -1px;
        background: linear-gradient(45deg, var(--dark), var(--accent));
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
    }
    
    @media (max-width: 768px) {
        .hero h1 {
            font-size: 36px;
        }
    }
    
    .hero p {
        font-size: 20px;
        color: var(--gray);
        margin-bottom: 40px;
        max-width: 500px;
        margin-left: auto;
        margin-right: auto;
    }
    
    @media (max-width: 768px) {
        .hero p {
            font-size: 17px;
        }
    }
    
    /* Profile Cards */
    .profile-card {
        position: relative;
        border-radius: var(--radius-lg);
        overflow: hidden;
        background: white;
        box-shadow: var(--shadow-md);
        transition: all 0.3s ease;
    }
    
    .profile-card:hover {
        transform: translateY(-8px) scale(1.02);
        box-shadow: var(--shadow-lg);
    }
    
    .profile-card-image {
        position: relative;
        height: 320px;
        background: linear-gradient(135deg, var(--secondary), var(--accent));
        overflow: hidden;
    }
    
    @media (max-width: 768px) {
        .profile-card-image {
            height: 280px;
        }
    }
    
    .profile-card-image img {
        width: 100%;
        height: 100%;
        object-fit: cover;
        transition: transform 0.5s ease;
    }
    
    .profile-card:hover .profile-card-image img {
        transform: scale(1.1);
    }
    
    .profile-card-badge {
        position: absolute;
        top: 16px;
        right: 16px;
        background: rgba(255, 255, 255, 0.95);
        backdrop-filter: blur(10px);
        padding: 6px 14px;
        border-radius: var(--radius-xl);
        font-size: 12px;
        font-weight: 600;
        display: flex;
        align-items: center;
        gap: 6px;
    }
    
    .profile-card-content {
        padding: 24px;
    }
    
    .profile-card h3 {
        font-size: 22px;
        font-weight: 700;
        margin-bottom: 6px;
    }
    
    .profile-card p {
        color: var(--gray);
        font-size: 14px;
        margin-bottom: 16px;
    }
    
    .profile-card-tags {
        display: flex;
        flex-wrap: wrap;
        gap: 8px;
        margin-bottom: 20px;
    }
    
    .profile-card-tag {
        background: var(--gray-light);
        padding: 6px 14px;
        border-radius: var(--radius-xl);
        font-size: 12px;
        font-weight: 500;
        color: var(--gray);
    }
    
    /* Message Icon */
    .nav-messages {
        position: relative;
        display: flex;
        align-items: center;
        justify-content: center;
        width: 44px;
        height: 44px;
        border-radius: 50%;
        background: var(--gray-light);
        text-decoration: none;
        transition: all 0.3s;
    }
    
    .nav-messages:hover {
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        transform: scale(1.1);
    }
    
    .nav-messages:hover .nav-messages-icon {
        filter: brightness(0) invert(1);
    }
    
    .nav-messages-icon {
        font-size: 20px;
        transition: all 0.3s;
    }
    
    .nav-messages-badge {
        position: absolute;
        top: -4px;
        right: -4px;
        background: var(--danger);
        color: white;
        font-size: 11px;
        font-weight: 700;
        min-width: 22px;
        height: 22px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        padding: 0 6px;
        box-shadow: 0 2px 8px rgba(244, 67, 54, 0.4);
        animation: pulse-badge 2s infinite;
    }
    
    @keyframes pulse-badge {
        0%, 100% { transform: scale(1); }
        50% { transform: scale(1.15); }
    }
    
    /* Notification Bell */
    .notification-bell {
        position: relative;
        font-size: 20px;
        padding: 10px;
        border-radius: 50%;
        transition: all 0.3s;
    }
    
    .notification-bell:hover {
        background: var(--gray-light);
    }
    
    .notification-count {
        position: absolute;
        top: 2px;
        right: 2px;
        background: var(--danger);
        color: white;
        font-size: 10px;
        font-weight: 700;
        min-width: 18px;
        height: 18px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
    }
    
    /* Inbox Items */
    .inbox-item {
        display: flex;
        align-items: center;
        padding: 20px;
        border-radius: var(--radius-md);
        background: white;
        margin-bottom: 12px;
        box-shadow: var(--shadow-sm);
        transition: all 0.3s;
        cursor: pointer;
        border: 2px solid transparent;
    }
    
    .inbox-item:hover {
        transform: translateX(8px);
        box-shadow: var(--shadow-md);
        border-color: var(--primary);
    }
    
    .inbox-item.unread {
        background: linear-gradient(135deg, rgba(255, 65, 108, 0.05) 0%, rgba(255, 75, 43, 0.05) 100%);
        border-left: 4px solid var(--primary);
    }
    
    /* Avatar */
    .avatar {
        width: 56px;
        height: 56px;
        border-radius: 50%;
        background: linear-gradient(135deg, var(--secondary), var(--accent));
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 24px;
        color: white;
        flex-shrink: 0;
        overflow: hidden;
        box-shadow: var(--shadow-sm);
    }
    
    .avatar img {
        width: 100%;
        height: 100%;
        object-fit: cover;
    }
    
    .avatar.small {
        width: 40px;
        height: 40px;
        font-size: 16px;
    }
    
    /* Stats Cards */
    .stats-card {
        background: white;
        padding: 28px;
        border-radius: var(--radius-lg);
        text-align: center;
        box-shadow: var(--shadow-sm);
        transition: all 0.3s;
        border: 1px solid var(--gray-light);
    }
    
    .stats-card:hover {
        transform: translateY(-4px);
        box-shadow: var(--shadow-md);
    }
    
    .stats-number {
        font-size: 42px;
        font-weight: 800;
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 8px;
    }
    
    .stats-label {
        color: var(--gray);
        font-size: 14px;
        font-weight: 500;
    }
    
    /* Alerts */
    .alert {
        padding: 20px 24px;
        border-radius: var(--radius-md);
        margin-bottom: 24px;
        display: flex;
        align-items: center;
        gap: 16px;
        font-weight: 500;
    }
    
    .alert-danger {
        background: linear-gradient(135deg, #fee 0%, #ffebee 100%);
        border-left: 4px solid var(--danger);
        color: #c33;
    }
    
    .alert-warning {
        background: linear-gradient(135deg, #fff8e1 0%, #fff3cd 100%);
        border-left: 4px solid var(--warning);
        color: #856404;
    }
    
    .alert-success {
        background: linear-gradient(135deg, #e8f5e9 0%, #f1f8e9 100%);
        border-left: 4px solid var(--success);
        color: #2e7d32;
    }
    
    .alert-info {
        background: linear-gradient(135deg, #e3f2fd 0%, #e8f5e9 100%);
        border-left: 4px solid var(--info);
        color: #0d47a1;
    }
    
    /* Photo Gallery */
    .photo-gallery {
        display: grid;
        grid-template-columns: repeat(auto-fill, minmax(140px, 1fr));
        gap: 16px;
        margin: 24px 0;
    }
    
    .photo-item {
        position: relative;
        aspect-ratio: 1;
        border-radius: var(--radius-md);
        overflow: hidden;
        cursor: pointer;
        box-shadow: var(--shadow-sm);
        transition: all 0.3s;
    }
    
    .photo-item:hover {
        transform: scale(1.05);
        box-shadow: var(--shadow-md);
    }
    
    .photo-item img {
        width: 100%;
        height: 100%;
        object-fit: cover;
        transition: transform 0.5s;
    }
    
    .photo-item:hover img {
        transform: scale(1.1);
    }
    
    /* Search Bar */
    .search-bar {
        position: relative;
        margin-bottom: 32px;
    }
    
    .search-bar input {
        width: 100%;
        padding: 18px 24px 18px 56px;
        border: 2px solid var(--gray-light);
        border-radius: var(--radius-xl);
        font-size: 16px;
        transition: all 0.3s;
        background: white;
    }
    
    .search-bar input:focus {
        outline: none;
        border-color: var(--primary);
        box-shadow: 0 0 0 4px rgba(255, 65, 108, 0.1);
    }
    
    .search-bar::before {
        content: '🔍';
        position: absolute;
        left: 22px;
        top: 50%;
        transform: translateY(-50%);
        font-size: 18px;
        opacity: 0.5;
    }
    
    /* Filter Tags */
    .filter-tags {
        display: flex;
        gap: 12px;
        flex-wrap: wrap;
        margin-bottom: 24px;
    }
    
    .filter-tag {
        padding: 10px 20px;
        background: white;
        border: 2px solid var(--gray-light);
        border-radius: var(--radius-xl);
        cursor: pointer;
        transition: all 0.3s;
        font-size: 14px;
        font-weight: 500;
    }
    
    .filter-tag:hover,
    .filter-tag.active {
        border-color: var(--primary);
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        color: white;
    }
    
    /* Floating Action Button */
    .fab {
        position: fixed;
        bottom: 30px;
        right: 30px;
        width: 64px;
        height: 64px;
        border-radius: 50%;
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        color: white;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 28px;
        box-shadow: var(--shadow-glow);
        cursor: pointer;
        transition: all 0.3s;
        z-index: 100;
        border: none;
    }
    
    .fab:hover {
        transform: scale(1.1) rotate(90deg);
    }
    
    @media (max-width: 768px) {
        .fab {
            width: 56px;
            height: 56px;
            font-size: 24px;
            bottom: 20px;
            right: 20px;
        }
    }
    
    /* Chat Page */
    .chat-container {
        height: calc(100vh - 80px);
        display: flex;
        flex-direction: column;
        background: linear-gradient(135deg, #f8f4f5 0%, #fcf8f9 100%);
    }
    
    .chat-messages {
        flex: 1;
        overflow-y: auto;
        padding: 24px;
    }
    
    .chat-input {
        background: white;
        padding: 20px 24px;
        border-top: 1px solid var(--gray-light);
    }
    
    .message-bubble {
        max-width: 70%;
        padding: 16px 20px;
        border-radius: var(--radius-lg);
        margin-bottom: 16px;
        box-shadow: var(--shadow-sm);
        position: relative;
    }
    
    .message-bubble.sent {
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        color: white;
        margin-left: auto;
        border-bottom-right-radius: 4px;
    }
    
    .message-bubble.received {
        background: white;
        color: var(--dark);
        border-bottom-left-radius: 4px;
    }
    
    /* Empty State */
    .empty-state {
        text-align: center;
        padding: 80px 24px;
    }
    
    .empty-state-icon {
        font-size: 80px;
        margin-bottom: 24px;
        opacity: 0.3;
    }
    
    .empty-state h3 {
        color: var(--dark);
        margin-bottom: 12px;
        font-size: 24px;
    }
    
    .empty-state p {
        color: var(--gray);
        max-width: 400px;
        margin: 0 auto;
    }
    
    /* Loading Animation */
    @keyframes shimmer {
        0% { background-position: -1000px 0; }
        100% { background-position: 1000px 0; }
    }
    
    .skeleton {
        background: linear-gradient(90deg, #f0f0f0 25%, #e0e0e0 50%, #f0f0f0 75%);
        background-size: 1000px 100%;
        animation: shimmer 2s infinite;
    }
    
    /* Mobile Optimizations */
    @media (max-width: 768px) {
        .btn {
            padding: 14px 24px;
            font-size: 16px; /* Prevents zoom on iOS */
        }
        
        .card {
            margin: 0 8px;
        }
        
        .profile-card-content {
            padding: 20px;
        }
        
        .inbox-item {
            padding: 16px;
        }
        
        .avatar {
            width: 48px;
            height: 48px;
        }
        
        .stats-number {
            font-size: 32px;
        }
        
        .alert {
            flex-direction: column;
            text-align: center;
            gap: 12px;
        }
    }
    
    /* Touch improvements */
    @media (hover: none) and (pointer: coarse) {
        .btn, a, button {
            min-height: 44px;
            min-width: 44px;
        }
        
        .photo-item .remove-btn {
            opacity: 1;
        }
    }
    
    /* Safe area for notched phones */
    @supports (padding-top: env(safe-area-inset-top)) {
        .navbar {
            padding-top: env(safe-area-inset-top);
        }
        
        body {
            padding-bottom: env(safe-area-inset-bottom);
        }
    }
    
    /* Scrollbar styling */
    ::-webkit-scrollbar {
        width: 8px;
        height: 8px;
    }
    
    ::-webkit-scrollbar-track {
        background: var(--gray-light);
        border-radius: 4px;
    }
    
    ::-webkit-scrollbar-thumb {
        background: linear-gradient(45deg, var(--primary-dark), var(--primary));
        border-radius: 4px;
    }
    
    ::-webkit-scrollbar-thumb:hover {
        background: var(--primary);
    }
`;

function getFooter() {
    return `
    <footer style="background: #333; color: white; padding: 40px 0; margin-top: 60px;">
        <div class="container">
            <div style="display: flex; justify-content: space-between; align-items: center; flex-wrap: wrap; gap: 20px;">
                <div>
                    <h4 style="margin-bottom: 10px;">FindYourMatch</h4>
                    <p style="color: #888; font-size: 14px;">Find your perfect match today</p>
                </div>
                <div style="text-align: right;">
                    <p style="margin-bottom: 8px;"><strong>Need Help?</strong></p>
                    <a href="mailto:findyourmatch6187@gmail.com" style="color: var(--primary); text-decoration: none; font-size: 16px;">
                        📧 findyourmatch6187@gmail.com
                    </a>
                    <p style="color: #888; font-size: 12px; margin-top: 5px;">24/7 Support Available</p>
                </div>
            </div>
            <div style="border-top: 1px solid #444; margin-top: 30px; padding-top: 20px; text-align: center; color: #666; font-size: 13px;">
                © 2024 FindYourMatch. All rights reserved.
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
                viewCost = `<div style="position: absolute; top: 10px; left: 10px; background: var(--warning); color: white; padding: 5px 12px; border-radius: 15px; font-size: 11px; font-weight: 600; z-index: 2;">🔒 ${viewStatus.cost} coins</div>`;
            } else {
                viewCost = `<div style="position: absolute; top: 10px; left: 10px; background: var(--success); color: white; padding: 5px 12px; border-radius: 15px; font-size: 11px; font-weight: 600; z-index: 2;">✓ Free</div>`;
            }
        }
        
        const isFavorited = currentUser && favorites.find(f => f.userId === currentUser.id && f.targetId === u.id);
        
        return `
        <div class="card" style="position: relative; overflow: hidden;">
            <div style="height: 200px; background: linear-gradient(135deg, var(--secondary), var(--accent)); position: relative; overflow: hidden;">
                ${u.photo ? `<img src="/uploads/${u.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover; object-position: center; display: block;">` : `<div style="display: flex; align-items: center; justify-content: center; height: 100%; color: white; font-size: 60px;">👩</div>`}
                ${viewCost}
                ${u.isVerified ? `<div style="position: absolute; top: 10px; right: 10px; background: var(--info); color: white; padding: 5px 10px; border-radius: 15px; font-size: 11px; z-index: 2;">✓ Verified</div>` : ''}
                <span style="position: absolute; bottom: 10px; right: 10px; background: ${u.isOnline ? '#4caf50' : '#999'}; color: white; padding: 5px 12px; border-radius: 20px; font-size: 11px; font-weight: 600; z-index: 2;">
                    ${u.isOnline ? '● Online' : '○ Offline'}
                </span>
                ${currentUser ? `
                    <form method="POST" action="/favorite/${u.id}" style="position: absolute; bottom: 10px; left: 10px; z-index: 2;">
                        <input type="hidden" name="redirect" value="/">
                        <button type="submit" style="background: ${isFavorited ? 'var(--danger)' : 'white'}; color: ${isFavorited ? 'white' : 'var(--danger)'}; border: none; padding: 8px 14px; border-radius: 20px; cursor: pointer; font-size: 18px; box-shadow: 0 2px 10px rgba(0,0,0,0.2);">
                            ${isFavorited ? '♥' : '♡'}
                        </button>
                    </form>
                ` : ''}
            </div>
            <div style="padding: 16px;">
                <h4 style="font-size: 16px; margin-bottom: 4px;">${u.name}, ${u.age}</h4>
                <p style="color: #888; font-size: 13px; margin-bottom: 12px;">📍 ${u.location}</p>
                <a href="/profile/${u.id}" class="btn btn-primary btn-sm" style="width: 100%;">View Profile</a>
            </div>
        </div>
    `}).join('');

    // Search filters for males
    const searchFilters = currentUser && currentUser.gender === 'male' ? `
        <div style="background: white; padding: 25px; border-radius: 16px; margin-bottom: 30px; box-shadow: 0 5px 20px rgba(0,0,0,0.08);">
            <form method="GET" action="/" style="display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 15px; align-items: end;">
                <div class="form-group" style="margin-bottom: 0;">
                    <label style="font-size: 13px; color: #888;">Age Range</label>
                    <div style="display: flex; gap: 10px;">
                        <input type="number" name="minAge" placeholder="Min" value="${minAge || ''}" style="flex: 1;">
                        <input type="number" name="maxAge" placeholder="Max" value="${maxAge || ''}" style="flex: 1;">
                    </div>
                </div>
                <div class="form-group" style="margin-bottom: 0;">
                    <label style="font-size: 13px; color: #888;">Location</label>
                    <input type="text" name="location" placeholder="City or Country" value="${location || ''}">
                </div>
                <div class="form-group" style="margin-bottom: 0;">
                    <label style="font-size: 13px; color: #888;">Interests</label>
                    <input type="text" name="interests" placeholder="e.g., Travel, Music" value="${interests || ''}">
                </div>
                <button type="submit" class="btn btn-primary" style="height: fit-content;">🔍 Search</button>
                ${(minAge || maxAge || location || interests) ? `<a href="/" class="btn btn-outline" style="height: fit-content; text-align: center;">Clear</a>` : ''}
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
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">FindYourMatch</a>
                <div style="display: flex; align-items: center; gap: 20px;">
                    ${currentUser ? `
                        ${getMessageIcon(currentUser.id)}
                        ${renderHeaderBell(currentUser)}
                        ${currentUser.gender === 'male' ? `
                            <a href="/buy-coins" class="btn btn-success btn-sm">+ Buy Coins</a>
                            <span style="background: linear-gradient(135deg, #ffd700, #ff9800); color: white; padding: 8px 16px; border-radius: 20px; font-weight: 600;">🪙 ${currentUser.coins}</span>
                        ` : ''}
                        <span>👤 ${currentUser.name}</span>
                        <a href="/dashboard">Dashboard</a>
                        <a href="mailto:findyourmatch6187@gmail.com" style="color: var(--primary); font-size: 14px; margin-left: 15px;">📧 Support</a>
                        <a href="/logout" style="margin-left: 10px;">Logout</a>
                    ` : `
                        <a href="/login">Login</a>
                        <a href="mailto:findyourmatch6187@gmail.com" style="color: var(--primary); font-size: 14px; margin-right: 10px;">📧 Support</a>
                        <a href="/register" class="btn btn-primary" style="margin-left: 15px;">Join Free</a>
                    `}
                </div>
            </div>
        </div>
    </nav>
    
    <section class="hero">
        <div class="hero-content">
            <h1>Find Your Perfect Match</h1>
            <p>Join millions of singles discovering meaningful connections. Your journey to love starts here.</p>
            ${currentUser ? `
                <a href="/dashboard" class="btn btn-primary btn-lg">Go to Dashboard →</a>
            ` : `
                <div style="display: flex; gap: 16px; justify-content: center; flex-wrap: wrap;">
                    <a href="/register" class="btn btn-primary btn-lg">Create Free Account</a>
                    <a href="/login" class="btn btn-secondary btn-lg">Sign In</a>
                </div>
            `}
        </div>
    </section>
    
    <section style="padding: 40px 0;">
        <div class="container">
            ${searchFilters}
            
            <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 25px;">
                <h2 style="font-size: 24px;">${filteredProfiles.length} Profiles Found</h2>
                ${currentUser && currentUser.gender === 'male' ? `
                    <div style="display: flex; gap: 15px; align-items: center;">
                        <span style="color: #888; font-size: 14px;">Daily Views: ${getMaleDailyStatus(currentUser.id).views.freeRemaining} free left</span>
                        <span style="background: linear-gradient(135deg, #ffd700, #ff9800); color: white; padding: 8px 16px; border-radius: 20px; font-weight: 600;">🪙 ${currentUser.coins}</span>
                    </div>
                ` : ''}
            </div>
            
            <div class="grid grid-3">
                ${profileCards || `
                    <div class="empty-state" style="grid-column: 1 / -1;">
                        <div class="empty-state-icon">🔍</div>
                        <h3>No profiles found</h3>
                        <p>Try adjusting your search filters</p>
                    </div>
                `}
            </div>
        </div>
    </section>
    ${getFooter()}
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
    <title>Join Free - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body style="background: linear-gradient(135deg, var(--secondary) 0%, #764ba2 100%); min-height: 100vh; padding: 40px 20px;">
    <div class="container" style="max-width: 700px;">
        <div style="background: white; padding: 40px; border-radius: 20px;">
            <h2 style="text-align: center; margin-bottom: 10px;">📝 Create Your Account</h2>
            <p style="text-align: center; color: #888; margin-bottom: 30px;">Add up to ${CONFIG.MAX_PROFILE_PHOTOS} photos to your profile</p>
            
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
                        <p style="font-size: 13px; color: #888; margin-top: 5px;" id="genderNote"></p>
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
                    <div style="background: #f8f9fa; padding: 25px; border-radius: 12px; border: 2px dashed #ddd; text-align: center;">
                        <input type="file" name="photos" accept="image/*" multiple id="photoInput" onchange="previewPhotos(this)" style="display: none;">
                        <label for="photoInput" style="cursor: pointer; display: inline-block; padding: 15px 30px; background: var(--primary); color: white; border-radius: 25px; font-weight: 600;">
                            📷 Choose Photos
                        </label>
                        <p style="font-size: 13px; color: #888; margin-top: 15px;">Select up to ${CONFIG.MAX_PROFILE_PHOTOS} photos. First photo will be your main profile picture.</p>
                        <div id="photoPreview" style="display: grid; grid-template-columns: repeat(auto-fill, minmax(100px, 1fr)); gap: 10px; margin-top: 20px;"></div>
                    </div>
                </div>
                
                <button type="submit" class="btn btn-primary" style="width: 100%; margin-top: 20px; padding: 18px;">Create Free Account</button>
            </form>
        </div>
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
                    div.style.cssText = 'aspect-ratio: 1; border-radius: 12px; overflow: hidden; box-shadow: 0 5px 15px rgba(0,0,0,0.1);';
                    div.innerHTML = '<img src="' + e.target.result + '" alt="📷" onerror="this.style.display=\'none\'; this.parentElement.innerHTML=\'<div style=\\\'display:flex;align-items:center;justify-content:center;height:100%;background:#f0f2f5;color:#888;font-size:24px;\\\'>📷</div>\';" style="width: 100%; height: 100%; object-fit: cover;">';
                    preview.appendChild(div);
                };
                reader.readAsDataURL(file);
            }
        }
        
        document.getElementById('genderSelect').addEventListener('change', function() {
            const note = document.getElementById('genderNote');
            if (this.value === 'male') {
                note.innerHTML = '💡 You get ${CONFIG.TRIAL_DAYS} days FREE trial, then need coins for chat & photos';
                note.style.color = '#2196f3';
            } else if (this.value === 'female') {
                note.innerHTML = '✨ You get FREE unlimited chat! Admin will assign matches to you.';
                note.style.color = '#4caf50';
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
    <title>Welcome! - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body style="background: linear-gradient(135deg, var(--secondary) 0%, #764ba2 100%); min-height: 100vh; display: flex; align-items: center; justify-content: center;">
    <div style="background: white; padding: 60px; border-radius: 20px; text-align: center; max-width: 500px;">
        <div style="width: 100px; height: 100px; background: linear-gradient(135deg, #4caf50, #45a049); border-radius: 50%; margin: 0 auto 25px; display: flex; align-items: center; justify-content: center; color: white; font-size: 50px;">✓</div>
        <h2>Welcome, ${name}!</h2>
        <p style="color: #888; margin: 15px 0;">${photos.length} photo${photos.length !== 1 ? 's' : ''} uploaded</p>
        ${gender === 'male' ? `
            <div style="background: #e3f2fd; padding: 25px; border-radius: 12px; margin: 25px 0; text-align: left;">
                <p style="color: #1976d2; font-weight: 600; margin-bottom: 15px;">🎉 ${CONFIG.TRIAL_DAYS} DAYS FREE TRIAL!</p>
                <ul style="color: #555; font-size: 14px; line-height: 2; padding-left: 20px;">
                    <li>${CONFIG.MALE_FREE_MESSAGES_PER_DAY} free messages/day</li>
                    <li>${CONFIG.MALE_FREE_PHOTOS_PER_DAY} free photos/day</li>
                    <li>${CONFIG.MALE_FREE_PROFILE_VIEWS_PER_DAY} free profile views/day</li>
                </ul>
            </div>
        ` : `
            <div style="background: #e8f5e9; padding: 25px; border-radius: 12px; margin: 25px 0;">
                <p style="color: #2e7d32; font-weight: 600; margin-bottom: 10px;">✨ FREE Unlimited Access!</p>
                <p style="color: #555; font-size: 14px;">Admin will assign quality matches to you.<br>Just wait for messages!</p>
            </div>
        `}
        <a href="/login" class="btn btn-primary btn-lg">Login Now</a>
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
    <title>Login - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body style="background: linear-gradient(135deg, var(--secondary) 0%, #764ba2 100%); min-height: 100vh; display: flex; align-items: center; justify-content: center;">
    <div style="background: white; padding: 50px; border-radius: 20px; width: 100%; max-width: 420px; box-shadow: 0 20px 60px rgba(0,0,0,0.3);">
        <h2 style="text-align: center; margin-bottom: 30px;">🔐 Welcome Back</h2>
        <form method="POST" action="/login">
            <div class="form-group">
                <label>Email</label>
                <input type="email" name="email" required placeholder="your@email.com">
            </div>
            <div class="form-group">
                <label>Password</label>
                <input type="password" name="password" required placeholder="••••••••">
            </div>
            <button type="submit" class="btn btn-primary" style="width: 100%; padding: 16px;">Login</button>
        </form>
        <p style="text-align: center; margin-top: 25px; color: #888;">
            Don't have an account? <a href="/register" style="color: var(--primary); font-weight: 600;">Join Free</a>
        </p>
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
            <div class="card" style="cursor: pointer;" onclick="window.location.href='/profile/${u.id}'">
                <div style="height: 200px; background: linear-gradient(135deg, var(--secondary), #764ba2); position: relative;">
                    ${u.photo ? `<img src="/uploads/${u.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : `<div style="display: flex; align-items: center; justify-content: center; height: 100%; color: white; font-size: 60px;">👩</div>`}
                    ${u.isOnline ? `<span style="position: absolute; bottom: 10px; right: 10px; background: #4caf50; color: white; padding: 5px 12px; border-radius: 15px; font-size: 11px;">● Online</span>` : ''}
                </div>
                <div style="padding: 20px;">
                    <h4>${u.name}, ${u.age}</h4>
                    <p style="color: #888; font-size: 13px;">📍 ${u.location}</p>
                </div>
            </div>
        `).join('');
        
        // Male inbox - all conversations with females
        const inboxHTML = generateMaleInbox(user);
        
        res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Dashboard - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">FindYourMatch</a>
                <div style="display: flex; align-items: center; gap: 15px;">
                    ${getNavMessageIcon(user.id)}
                    <a href="/notifications" class="notification-bell" style="position: relative; font-size: 20px; margin-right: 5px;">
                        🔔
                        ${notifications.filter(n => n.userId === user.id && !n.read).length > 0 ? 
                            `<span class="notification-count">${notifications.filter(n => n.userId === user.id && !n.read).length}</span>` : ''}
                    </a>
                    <a href="/buy-coins" class="btn btn-success btn-sm">+ Buy Coins</a>
                    <span style="background: linear-gradient(135deg, #ffd700, #ff9800); color: white; padding: 8px 16px; border-radius: 20px; font-weight: 600;">🪙 ${user.coins}</span>
                    ${user.role === 'admin' ? '<a href="/admin" class="btn btn-danger btn-sm">Admin</a>' : ''}
                    <a href="/favorites" class="btn btn-outline btn-sm">♥ Favorites</a>
                    <a href="/account" class="btn btn-outline btn-sm">⚙️ Account</a>
                    <a href="/logout" class="btn btn-primary btn-sm">Logout</a>
                </div>
            </div>
        </div>
    </nav>
    
    ${trialStatus.message ? `
        <div style="background: ${trialStatus.expired ? '#fee' : '#fff3cd'}; padding: 15px 0; border-bottom: 3px solid ${trialStatus.expired ? 'var(--danger)' : 'var(--warning)'};">
            <div class="container" style="display: flex; justify-content: space-between; align-items: center;">
                <span>${trialStatus.message}</span>
                ${trialStatus.expired ? '<a href="/buy-coins" class="btn btn-success btn-sm">Buy Coins</a>' : ''}
            </div>
        </div>
    ` : ''}
    
    <div class="container" style="padding: 30px 20px;">
        <!-- Daily Limits -->
        <div class="grid grid-3" style="margin-bottom: 30px;">
            <div class="stats-card">
                <div class="stats-number">${dailyStatus.messages.freeRemaining}</div>
                <div class="stats-label">Free Messages Left</div>
                <div class="daily-limit-bar">
                    <div class="daily-limit-fill" style="width: ${(dailyStatus.messages.freeRemaining / CONFIG.MALE_FREE_MESSAGES_PER_DAY) * 100}%"></div>
                </div>
            </div>
            <div class="stats-card">
                <div class="stats-number">${dailyStatus.photos.freeRemaining}</div>
                <div class="stats-label">Free Photos Left</div>
                <div class="daily-limit-bar">
                    <div class="daily-limit-fill" style="width: ${(dailyStatus.photos.freeRemaining / CONFIG.MALE_FREE_PHOTOS_PER_DAY) * 100}%"></div>
                </div>
            </div>
            <div class="stats-card">
                <div class="stats-number">${dailyStatus.views.freeRemaining}</div>
                <div class="stats-label">Free Views Left</div>
                <div class="daily-limit-bar">
                    <div class="daily-limit-fill" style="width: ${(dailyStatus.views.freeRemaining / CONFIG.MALE_FREE_PROFILE_VIEWS_PER_DAY) * 100}%"></div>
                </div>
            </div>
        </div>
        
        <div class="grid grid-2" style="grid-template-columns: 1fr 1fr; gap: 24px; align-items: start;">
            <!-- Browse Section -->
            <div>
                <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 20px;">
                    <h2 style="font-size: 24px;">🔥 New Ladies</h2>
                    <a href="/" class="btn btn-outline btn-sm">Browse All</a>
                </div>
                <div style="display: grid; grid-template-columns: repeat(2, 1fr); gap: 16px;">
                    ${profileCards}
                </div>
            </div>
            
            <!-- Inbox Section -->
            <div id="messages" style="background: white; border-radius: 16px; padding: 24px; box-shadow: 0 4px 12px rgba(0,0,0,0.1); max-height: 600px; overflow-y: auto;">
                <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 20px;">
                    <h2 style="font-size: 24px;">💬 Messages</h2>
                    ${messages.filter(m => m.to === user.id && !m.read).length > 0 ? 
                        `<span class="unread-badge">${messages.filter(m => m.to === user.id && !m.read).length} new</span>` : ''}
                </div>
                ${inboxHTML}
            </div>
        </div>
    </div>
    
    <a href="/" class="floating-action">🔍</a>
    ${getFooter()}
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
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">FindYourMatch</a>
                <div style="display: flex; align-items: center; gap: 15px;">
                    ${getNavMessageIcon(user.id)}
                    <a href="/notifications" class="notification-bell" style="position: relative; font-size: 20px; margin-right: 5px;">
                        🔔
                        ${notifications.filter(n => n.userId === user.id && !n.read).length > 0 ? 
                            `<span class="notification-count">${notifications.filter(n => n.userId === user.id && !n.read).length}</span>` : ''}
                    </a>
                    <span class="badge badge-verified">✓ Verified</span>
                    ${user.role === 'admin' ? '<a href="/admin" class="btn btn-danger btn-sm">Admin</a>' : ''}
                    <a href="/account" class="btn btn-outline btn-sm">⚙️ Account</a>
                    <a href="/logout" class="btn btn-primary btn-sm">Logout</a>
                </div>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 30px 20px;">
        <div class="alert alert-success" style="margin-bottom: 30px;">
            <span>✨ You have FREE unlimited messaging! Wait for admin-assigned matches to message you first.</span>
        </div>
        
        <div class="grid grid-2">
            <!-- Messages Section -->
            <div id="messages" style="scroll-margin-top: 80px;">
                <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 20px;">
                    <h2 style="font-size: 24px;">💬 Your Messages</h2>
                    ${messages.filter(m => m.to === user.id && !m.read).length > 0 ? 
                        `<span class="unread-badge">${messages.filter(m => m.to === user.id && !m.read).length} new</span>` : ''}
                </div>
                ${inboxHTML}
            </div>
            
            <!-- Pending Matches Section -->
            <div>
                <h2 style="font-size: 24px; margin-bottom: 20px;">⏳ Pending Matches</h2>
                <p style="color: #888; margin-bottom: 20px;">These gentlemen have been assigned to you. They will appear here once they send you a message.</p>
                
                ${pendingMales.length === 0 ? `
                    <div class="empty-state" style="background: white; border-radius: 16px; padding: 40px;">
                        <div class="empty-state-icon">⏳</div>
                        <h3>No pending matches</h3>
                        <p>Check back later for new assignments</p>
                    </div>
                ` : `
                    <div style="display: flex; flex-direction: column; gap: 15px;">
                        ${pendingMales.map(m => `
                            <div class="card" style="padding: 20px; display: flex; align-items: center; gap: 15px;">
                                <div class="avatar-placeholder">
                                    ${m.photo ? `<img src="/uploads/${m.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';">` : '👨'}
                                </div>
                                <div style="flex: 1;">
                                    <h4><a href="/male-profile/${m.id}" style="color: inherit; text-decoration: none;">${m.name}, ${m.age}</a></h4>
                                    <p style="color: #888; font-size: 13px;">📍 ${m.location}</p>
                                    <p style="color: #999; font-size: 12px; margin-top: 5px;">Waiting for first message...</p>
                                </div>
                                <span style="background: #fff3cd; color: #856404; padding: 5px 12px; border-radius: 15px; font-size: 12px;">⏳ Pending</span>
                            </div>
                        `).join('')}
                    </div>
                `}
            </div>
        </div>
    </div>
    ${getFooter()}
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
<html>
<head>
    <title>Access Denied</title>
    <style>${globalStyles}</style>
</head>
<body style="display: flex; align-items: center; justify-content: center; min-height: 100vh;">
    <div style="text-align: center; padding: 60px;">
        <div style="font-size: 80px; margin-bottom: 20px;">🔒</div>
        <h2>Not Assigned</h2>
        <p style="color: #888; margin: 20px 0;">This gentleman has not been assigned to you by admin yet.</p>
        <a href="/dashboard" class="btn btn-primary">Back to Dashboard</a>
    </div>
</body>
</html>
        `);
    }

    // Check if male messaged first (for chat button)
    const maleSentFirst = messages.find(m => m.from === maleId && m.to === currentUser.id);
    const photoGallery = male.photos.length > 0 ? `
        <div style="margin: 30px 0;">
            <h3 style="margin-bottom: 20px; color: var(--primary);">Photos (${male.photos.length})</h3>
            <div class="photo-gallery">
                ${male.photos.map((photo, idx) => `
                    <div class="photo-item" onclick="showLightbox('${photo}')">
                        <img src="/uploads/${photo}" alt="📷" onerror="this.style.display='none'; this.parentElement.innerHTML='<div style=\'display:flex;align-items:center;justify-content:center;height:100%;background:#f0f2f5;color:#888;font-size:24px;\'>📷</div>'">
                    </div>
                `).join('')}
            </div>
        </div>
    ` : '';

    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>${male.name} - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">← Back</a>
                <div style="display: flex; align-items: center; gap: 15px;">
                    ${getNavMessageIcon(currentUser.id)}
                    <a href="/notifications" class="notification-bell" style="position: relative; font-size: 20px; margin-right: 5px;">
                        🔔
                        ${notifications.filter(n => n.userId === currentUser.id && !n.read).length > 0 ? 
                            `<span class="notification-count">${notifications.filter(n => n.userId === currentUser.id && !n.read).length}</span>` : ''}
                    </a>
                    ${currentUser.gender === 'male' ? `
                        <a href="/buy-coins" class="btn btn-success btn-sm">+ Buy Coins</a>
                        <span style="background: linear-gradient(135deg, #ffd700, #ff9800); color: white; padding: 8px 16px; border-radius: 20px; font-weight: 600;">🪙 ${currentUser.coins}</span>
                    ` : ''}
                    <a href="/logout">Logout</a>
                </div>
            </div>
        </div>
    </nav>

    <div class="container" style="padding: 40px 20px;">
        <div style="background: linear-gradient(135deg, #2196f3, #1976d2); color: white; padding: 60px; border-radius: 20px; text-align: center; margin-bottom: 30px; position: relative;">
            ${male.isVerified ? `<div style="position: absolute; top: 20px; right: 20px; background: white; color: var(--info); padding: 8px 16px; border-radius: 20px; font-weight: 600;">✓ Verified</div>` : ''}
            <div style="width: 150px; height: 150px; border-radius: 50%; border: 5px solid white; margin: 0 auto 20px; overflow: hidden; background: rgba(255,255,255,0.2);">
                ${male.photo ? `<img src="/uploads/${male.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : '<div style="display: flex; align-items: center; justify-content: center; height: 100%; font-size: 60px;">👨</div>'}
            </div>
            <h1 style="font-size: 42px; margin-bottom: 10px;">${male.name}, ${male.age}</h1>
            <p style="font-size: 20px; opacity: 0.95;">📍 ${male.location}, ${male.country}</p>
            ${male.occupation ? `<p style="font-size: 16px; margin-top: 10px;">💼 ${male.occupation}</p>` : ''}
            <div style="margin-top: 20px;">
                ${male.isOnline ? 
                    '<span style="background: #4caf50; color: white; padding: 8px 16px; border-radius: 20px; font-size: 14px;">● Online Now</span>' : 
                    `<span style="background: rgba(255,255,255,0.2); padding: 8px 16px; border-radius: 20px; font-size: 14px;">Last seen ${new Date(male.lastActive).toLocaleDateString()}</span>`
                }
            </div>
        </div>

        <div style="max-width: 800px; margin: 0 auto;">
            <div style="background: white; padding: 30px; border-radius: 16px; margin-bottom: 20px;">
                <h3 style="color: var(--primary); margin-bottom: 15px;">About</h3>
                <p style="color: #555; line-height: 1.8; font-size: 16px;">${male.bio || 'No bio yet.'}</p>
            </div>

            ${photoGallery}

            <div style="background: white; padding: 30px; border-radius: 16px; margin-bottom: 20px;">
                <h3 style="color: var(--primary); margin-bottom: 20px;">Details</h3>
                <div class="grid grid-2">
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Age</label>
                        <p style="font-weight: 600; font-size: 18px;">${male.age} years</p>
                    </div>
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Location</label>
                        <p style="font-weight: 600; font-size: 18px;">${male.location}</p>
                    </div>
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Country</label>
                        <p style="font-weight: 600; font-size: 18px;">${male.country}</p>
                    </div>
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Looking For</label>
                        <p style="font-weight: 600; font-size: 18px;">${male.lookingFor}</p>
                    </div>
                </div>

                ${male.interests ? `
                    <div style="margin-top: 20px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase; margin-bottom: 10px; display: block;">Interests</label>
                        <div style="display: flex; gap: 10px; flex-wrap: wrap;">
                            ${male.interests.split(',').map(i => 
                                `<span style="background: linear-gradient(135deg, #2196f3, #1976d2); color: white; padding: 8px 16px; border-radius: 20px; font-size: 14px;">${i.trim()}</span>`
                            ).join('')}
                        </div>
                    </div>
                ` : ''}
            </div>

            ${maleSentFirst ? `
                <div style="background: white; padding: 30px; border-radius: 16px;">
                    <a href="/chat/${male.id}" class="btn btn-primary" style="width: 100%; justify-content: center;">💬 Send Message</a>
                </div>
            ` : `
                <div style="background: #fff3cd; padding: 25px; border-radius: 16px; text-align: center;">
                    <p style="color: #856404;">⏳ Wait for ${male.name} to send you a message first. You can reply once he initiates contact.</p>
                </div>
            `}
        </div>
    </div>

    <script>
        function showLightbox(photo) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="📷" onerror="this.onerror=null; this.src=\'\'; this.style.background=\'#f0f2f5\'; this.style.display=\'flex\'; this.style.alignItems=\'center\'; this.style.justifyContent=\'center\'; this.innerHTML=\'📷\';" style="max-width:90%;max-height:90%;border-radius:10px;">';
            overlay.onclick = () => overlay.remove();
            document.body.appendChild(overlay);
        }
    </script>
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
            <div class="empty-state" style="background: white; border-radius: 16px; padding: 40px;">
                <div class="empty-state-icon">💬</div>
                <h3>No messages yet</h3>
                <p>Start browsing and send messages to ladies!</p>
                <a href="/" class="btn btn-primary btn-sm" style="margin-top: 15px;">Browse Profiles</a>
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
            previewText = '📸 Photo';
        } else {
            previewText = lastMessage.text.substring(0, 50) + (lastMessage.text.length > 50 ? '...' : '');
        }
        
        const timeString = new Date(lastMessage.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'});
        const dateString = new Date(lastMessage.time).toLocaleDateString();
        const isToday = new Date().toDateString() === new Date(lastMessage.time).toDateString();
        const displayTime = isToday ? timeString : dateString;
        
        return `
            <div class="card inbox-item ${unreadCount > 0 ? 'unread' : ''}" onclick="window.location.href='/chat/${partnerId}'" style="display: flex; align-items: center; gap: 14px; padding: 16px; margin-bottom: 12px; border-radius: 14px; cursor: pointer; transition: transform 0.2s ease, box-shadow 0.2s ease;">
                <div class="avatar-placeholder" style="width: 56px; height: 56px; min-width: 56px; border-radius: 50%; overflow: hidden; flex-shrink: 0;">
                    ${partner.photo ? `<img src="/uploads/${partner.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : '👩'}
                </div>
                <div style="flex: 1; min-width: 0;">
                    <div style="display: flex; justify-content: space-between; align-items: center; gap: 10px; margin-bottom: 6px;">
                        <div style="display: flex; align-items: center; gap: 8px; min-width: 0; flex: 1;">
                            <span style="font-weight: 700; font-size: 15px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;">${partner.name}</span>
                            ${partner.isOnline ? '<span style="width: 8px; height: 8px; background: #4caf50; border-radius: 50%; display: inline-block; flex-shrink: 0;"></span>' : ''}
                        </div>
                        <div style="display: flex; align-items: center; gap: 8px; flex-shrink: 0;">
                            ${unreadCount > 0 ? `<span style="background: var(--primary); color: white; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 700;">${unreadCount}</span>` : ''}
                            <span style="font-size: 12px; color: #888;">${displayTime}</span>
                        </div>
                    </div>
                    <div style="font-size: 14px; color: #666; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;">
                        ${lastMessage.from === user.id ? 'You: ' : ''}${previewText}
                    </div>
                </div>
            </div>
        `;
    }).join('');
}

// Helper: Generate Female Inbox
function generateFemaleInbox(user, chatPartnerIds) {
    if (chatPartnerIds.length === 0) {
        return `
            <div class="empty-state" style="background: white; border-radius: 16px; padding: 40px;">
                <div class="empty-state-icon">💌</div>
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
            previewText = '📸 Photo';
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
                    ${partner.photo ? `<img src="/uploads/${partner.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';">` : '👨'}
                </div>
                <div class="inbox-content">
                    <div class="inbox-header">
                        <span class="inbox-name">
                            ${partner.name}
                            ${partner.isVerified ? '<span class="verified-badge">✓</span>' : ''}
                            ${partner.isOnline ? '<span class="badge badge-online" style="margin-left: 8px;">● Online</span>' : ''}
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
<html>
<head>
    <title>Access Denied</title>
    <style>${globalStyles}</style>
</head>
<body style="display: flex; align-items: center; justify-content: center; min-height: 100vh;">
    <div style="text-align: center; padding: 60px;">
        <div style="font-size: 80px; margin-bottom: 20px;">🔒</div>
        <h2>Access Denied</h2>
        <p style="color: #888; margin: 20px 0;">You can only view female profiles.</p>
        <a href="/dashboard" class="btn btn-primary">Back to Dashboard</a>
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
<html>
<head>
    <title>Insufficient Coins</title>
    <style>${globalStyles}</style>
</head>
<body style="display: flex; align-items: center; justify-content: center; min-height: 100vh;">
    <div style="text-align: center; padding: 60px; max-width: 400px;">
        <div style="font-size: 80px; margin-bottom: 20px;">🪙</div>
        <h2>Insufficient Coins</h2>
        <p style="color: #888; margin: 20px 0;">
            Viewing this profile costs ${viewCost} coins.<br>
            You have ${currentUser.coins} coins.
        </p>
        <a href="/buy-coins" class="btn btn-primary">Buy Coins</a>
        <br><br>
        <a href="/" class="btn btn-outline">Back</a>
    </div>
</body>
</html>
            `);
        }
        
        if (viewStatus.cost > 0) {
            currentUser.coins -= viewCost;
            logProfileView(currentUser.id, profileUser.id, viewCost);
            viewMessage = `<div class="alert alert-info" style="margin-bottom: 20px;">${viewCost} coins deducted for viewing this profile.</div>`;
        } else if (viewStatus.isFree) {
            logProfileView(currentUser.id, profileUser.id, 0);
            viewMessage = `<div class="alert alert-success" style="margin-bottom: 20px;">✓ Free profile view used (${viewStatus.freeRemaining - 1} remaining today).</div>`;
        }
    }
    
    const photoGallery = profileUser.photos.length > 0 ? `
        <div style="margin: 30px 0;">
            <h3 style="margin-bottom: 20px; color: var(--primary);">Photos (${profileUser.photos.length})</h3>
            <div class="photo-gallery">
                ${profileUser.photos.map((photo, idx) => `
                    <div class="photo-item" onclick="showLightbox('${photo}')">
                        <img src="/uploads/${photo}" alt="📷" onerror="this.style.display='none'; this.parentElement.innerHTML='<div style=\'display:flex;align-items:center;justify-content:center;height:100%;background:#f0f2f5;color:#888;font-size:24px;\'>📷</div>'">
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
            <div style="display: flex; gap: 15px;">
                <a href="/chat/${profileUser.id}" class="btn btn-primary" style="flex: 1; justify-content: center;">💬 Send Message</a>
                <form method="POST" action="/favorite/${profileUser.id}" style="flex: 0;">
                    <button type="submit" class="btn ${isFavorited ? 'btn-danger' : 'btn-outline'}" style="font-size: 20px;">
                        ${isFavorited ? '♥' : '♡'}
                    </button>
                </form>
            </div>
        `;
    } else {
        actionButton = `<a href="/buy-coins" class="btn btn-warning" style="width: 100%; justify-content: center;">🔒 Buy Coins to Chat</a>`;
    }
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>${profileUser.name} - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">
                    <img src="/logo.png" alt="FindYourMatch" onerror="this.style.display='none'">
                    <span>FindYourMatch</span>
                </a>
                <div>
                    <a href="/dashboard">Dashboard</a>
                    <a href="mailto:findyourmatch6187@gmail.com" style="color: var(--primary); font-size: 14px; margin-left: 15px;">📧 Support</a>
                    <a href="/logout" style="margin-left: 20px;">Logout</a>
                </div>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        ${viewMessage}
        
        <div style="background: linear-gradient(135deg, var(--secondary), #764ba2); color: white; padding: 60px; border-radius: 20px; text-align: center; margin-bottom: 30px; position: relative;">
            ${profileUser.isVerified ? `<div style="position: absolute; top: 20px; right: 20px; background: white; color: var(--info); padding: 8px 16px; border-radius: 20px; font-weight: 600;">✓ Verified Profile</div>` : ''}
            <div style="width: 150px; height: 150px; border-radius: 50%; border: 5px solid white; margin: 0 auto 20px; overflow: hidden; background: rgba(255,255,255,0.2);">
                ${profileUser.photo ? `<img src="/uploads/${profileUser.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : '<div style="display: flex; align-items: center; justify-content: center; height: 100%; font-size: 60px;">👩</div>'}
            </div>
            <h1 style="font-size: 42px; margin-bottom: 10px;">${profileUser.name}, ${profileUser.age}</h1>
            <p style="font-size: 20px; opacity: 0.95;">📍 ${profileUser.location}, ${profileUser.country}</p>
            ${profileUser.occupation ? `<p style="font-size: 16px; margin-top: 10px;">💼 ${profileUser.occupation}</p>` : ''}
            <div style="margin-top: 20px;">
                ${profileUser.isOnline ? 
                    '<span style="background: #4caf50; color: white; padding: 8px 16px; border-radius: 20px; font-size: 14px;">● Online Now</span>' : 
                    `<span style="background: rgba(255,255,255,0.2); padding: 8px 16px; border-radius: 20px; font-size: 14px;">Last seen ${new Date(profileUser.lastActive).toLocaleDateString()}</span>`
                }
            </div>
        </div>
        
        <div style="max-width: 800px; margin: 0 auto;">
            <div style="background: white; padding: 30px; border-radius: 16px; margin-bottom: 20px;">
                <h3 style="color: var(--primary); margin-bottom: 15px;">About</h3>
                <p style="color: #555; line-height: 1.8; font-size: 16px;">${profileUser.bio || 'No bio yet.'}</p>
            </div>
            
            ${photoGallery}
            
            <div style="background: white; padding: 30px; border-radius: 16px; margin-bottom: 20px;">
                <h3 style="color: var(--primary); margin-bottom: 20px;">Details</h3>
                <div class="grid grid-2">
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Age</label>
                        <p style="font-weight: 600; font-size: 18px;">${profileUser.age} years</p>
                    </div>
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Location</label>
                        <p style="font-weight: 600; font-size: 18px;">${profileUser.location}</p>
                    </div>
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Country</label>
                        <p style="font-weight: 600; font-size: 18px;">${profileUser.country}</p>
                    </div>
                    <div style="padding: 15px; background: #f8f9fa; border-radius: 12px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Looking For</label>
                        <p style="font-weight: 600; font-size: 18px;">${profileUser.lookingFor}</p>
                    </div>
                </div>
                
                ${profileUser.interests ? `
                    <div style="margin-top: 20px;">
                        <label style="color: #888; font-size: 12px; text-transform: uppercase; margin-bottom: 10px; display: block;">Interests</label>
                        <div style="display: flex; gap: 10px; flex-wrap: wrap;">
                            ${profileUser.interests.split(',').map(i => 
                                `<span style="background: linear-gradient(135deg, var(--primary), #c2185b); color: white; padding: 8px 16px; border-radius: 20px; font-size: 14px;">${i.trim()}</span>`
                            ).join('')}
                        </div>
                    </div>
                ` : ''}
            </div>
            
            <div style="background: white; padding: 30px; border-radius: 16px;">
                ${actionButton}
                
                ${currentUser.id !== profileUser.id ? `
                    <hr style="margin: 20px 0; border: none; border-top: 1px solid #e0e0e0;">
                    <button onclick="showReportModal()" class="btn btn-outline" style="width: 100%; color: #f44336; border-color: #f44336;">
                        🚩 Report Profile
                    </button>
                ` : ''}
            </div>
            
            ${currentUser.id !== profileUser.id ? `
                <!-- Report Modal -->
                <div id="reportModal" style="display: none; position: fixed; top: 0; left: 0; right: 0; bottom: 0; background: rgba(0,0,0,0.5); z-index: 2000; align-items: center; justify-content: center;">
                    <div style="background: white; padding: 30px; border-radius: 20px; max-width: 400px; width: 90%;">
                        <h3 style="margin-bottom: 20px;">🚩 Report ${profileUser.name}</h3>
                        <form method="POST" action="/report/${profileUser.id}">
                            <div class="form-group">
                                <label>Reason</label>
                                <select name="reason" required style="width: 100%; padding: 12px; border: 2px solid #e0e0e0; border-radius: 10px;">
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
                                <textarea name="details" rows="3" placeholder="Please provide more details..." style="width: 100%; padding: 12px; border: 2px solid #e0e0e0; border-radius: 10px;"></textarea>
                            </div>
                            <div style="display: flex; gap: 10px;">
                                <button type="button" onclick="hideReportModal()" class="btn btn-outline" style="flex: 1;">Cancel</button>
                                <button type="submit" class="btn btn-danger" style="flex: 1;">Submit Report</button>
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
    </div>
    
    <script>
        function showLightbox(photo) {
            // Simple lightbox implementation
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="📷" onerror="this.onerror=null; this.src=\'\'; this.style.background=\'#f0f2f5\'; this.style.display=\'flex\'; this.style.alignItems=\'center\'; this.style.justifyContent=\'center\'; this.innerHTML=\'📷\';" style="max-width:90%;max-height:90%;border-radius:10px;">';
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
        <div class="card">
            <div style="height: 250px; background: linear-gradient(135deg, var(--secondary), #764ba2); position: relative; cursor: pointer;" onclick="window.location.href='/profile/${u.id}'">
                ${u.photo ? `<img src="/uploads/${u.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : `<div style="display: flex; align-items: center; justify-content: center; height: 100%; color: white; font-size: 60px;">👩</div>`}
                ${u.isOnline ? `<span style="position: absolute; bottom: 10px; right: 10px; background: #4caf50; color: white; padding: 5px 12px; border-radius: 15px; font-size: 11px;">● Online</span>` : ''}
            </div>
            <div style="padding: 20px;">
                <h4>${u.name}, ${u.age}</h4>
                <p style="color: #888; font-size: 13px;">📍 ${u.location}</p>
                <form method="POST" action="/favorite/${u.id}/remove" style="margin-top: 15px;">
                    <button type="submit" class="btn btn-outline btn-sm" style="width: 100%;">Remove from Favorites</button>
                </form>
            </div>
        </div>
    `).join('');
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>My Favorites - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">← Back</a>
                <a href="/logout">Logout</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        <h2 style="margin-bottom: 30px;">♥ My Favorites</h2>
        
        ${userFavorites.length === 0 ? `
            <div class="empty-state" style="background: white; border-radius: 16px; padding: 60px;">
                <div class="empty-state-icon">♡</div>
                <h3>No favorites yet</h3>
                <p>Browse profiles and click the heart to add favorites</p>
                <a href="/" class="btn btn-primary btn-sm" style="margin-top: 20px;">Browse Now</a>
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
        <div class="card" style="padding: 20px; margin-bottom: 15px; display: flex; align-items: center; gap: 15px; ${!n.read ? 'border-left: 4px solid var(--primary);' : ''} ${n.type === 'admin' ? 'background: linear-gradient(135deg, #ffebee, #fff);' : ''}">
            <div style="width: 50px; height: 50px; border-radius: 50%; background: ${getNotificationColor(n.type)}; display: flex; align-items: center; justify-content: center; font-size: 24px;">
                ${getNotificationIcon(n.type)}
            </div>
            <div style="flex: 1;">
                ${n.title ? `<p style="font-weight: 700; color: var(--primary); margin-bottom: 5px;">${n.title}</p>` : ''}
                <p style="font-weight: ${n.type === 'admin' ? '600' : '500'};">${n.text}</p>
                <p style="color: #888; font-size: 12px; margin-top: 5px;">${new Date(n.createdAt).toLocaleString()}</p>
            </div>
            ${n.type === 'admin' ? '<span style="background: var(--danger); color: white; padding: 3px 10px; border-radius: 10px; font-size: 11px;">ADMIN</span>' : ''}
        </div>
    `).join('');
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Notifications - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">← Back</a>
                <a href="/logout">Logout</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px; max-width: 700px;">
        <h2 style="margin-bottom: 30px;">🔔 Notifications</h2>
        
        ${userNotifications.length === 0 ? `
            <div class="empty-state" style="background: white; border-radius: 16px; padding: 60px;">
                <div class="empty-state-icon">🔔</div>
                <h3>No notifications</h3>
                <p>You're all caught up!</p>
            </div>
        ` : notificationItems}
    </div>
    ${getFooter()}
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
    const icons = {
        welcome: '👋',
        message: '💬',
        favorite: '♥',
        payment: '🪙',
        assignment: '👤',
        admin: '📢',
        report: '🚩',
        report_update: '✓'
    };
    return icons[type] || '🔔';
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
        <a href="/notifications" class="notification-bell">
            🔔
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
        <a href="/dashboard#messages" class="message-icon" style="margin-right: 15px; font-size: 20px; position: relative;">
            💬
            ${unreadCount > 0 ? `<span class="message-badge">${unreadCount > 99 ? '99+' : unreadCount}</span>` : ''}
        </a>
    `;
}

// Generate navbar message icon HTML - same tab like notifications
function getNavMessageIcon(userId) {
    const unreadCount = messages.filter(m => m.to === userId && !m.read).length;
    const hasUnread = unreadCount > 0;

    return `
        <a href="/dashboard#messages" class="nav-messages" title="${unreadCount} unread messages">
            <span class="nav-messages-icon">💬</span>
            ${hasUnread ? `<span class="nav-messages-badge">${unreadCount > 99 ? '99+' : unreadCount}</span>` : ''}
        </a>
    `;
}

// ACCOUNT SETTINGS
app.get('/account', requireAuth, (req, res) => {
    const user = users.find(u => u.id === req.session.userId);
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Account Settings - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">← Back</a>
                <a href="/logout">Logout</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px; max-width: 700px;">
        <h2 style="margin-bottom: 30px;">⚙️ Account Settings</h2>
        
        <div class="card" style="padding: 30px; margin-bottom: 25px;">
            <h3 style="margin-bottom: 25px; color: var(--primary);">Profile Information</h3>
            <div style="background: #f8f9fa; padding: 20px; border-radius: 12px; margin-bottom: 20px;">
                <label style="color: #888; font-size: 12px; text-transform: uppercase;">Your ID</label>
                <p style="font-weight: 600; font-size: 24px; color: var(--primary);">#${user.displayId || user.id}</p>
                <p style="font-size: 12px; color: #888; margin-top: 5px;">Share this ID with support if needed</p>
            </div>
                <div class="form-group">
                    <label>Profile Photo</label>
                    <div style="display: flex; align-items: center; gap: 20px; margin-bottom: 15px;">
                        <div style="width: 100px; height: 100px; border-radius: 50%; overflow: hidden; background: linear-gradient(135deg, var(--secondary), #764ba2);">
                            ${user.photo ? `<img src="/uploads/${user.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : '<div style="display: flex; align-items: center; justify-content: center; height: 100%; color: white; font-size: 40px;">👤</div>'}
                        </div>
                        <form method="POST" action="/account/photo" enctype="multipart/form-data" style="display: flex; align-items: center; gap: 10px;">
                            <input type="file" name="photo" accept="image/*" required>
                            <button type="submit" class="btn btn-primary btn-sm">Upload Photo</button>
                        </form>
                    </div>
                </div>

                <div class="form-group">
                    <label>Profile Photos (${user.photos.length}/${CONFIG.MAX_PROFILE_PHOTOS})</label>
                    <div class="photo-gallery" style="margin-bottom: 15px;">
                        ${user.photos.map((photo, idx) => `
                            <div class="photo-item" style="position: relative;">
                                <img src="/uploads/${photo}" alt="📷" onerror="this.style.display='none'; this.parentElement.innerHTML='<div style=\'display:flex;align-items:center;justify-content:center;height:100%;background:#f0f2f5;color:#888;font-size:24px;\'>📷</div>'">
                                <form method="POST" action="/account/photos/delete" style="position: absolute; top: 5px; right: 5px;">
                                    <input type="hidden" name="photo" value="${photo}">
                                    <button type="submit" style="background: var(--danger); color: white; border: none; border-radius: 50%; width: 30px; height: 30px; cursor: pointer; font-size: 14px;">×</button>
                                </form>
                                ${idx === 0 ? '<span style="position: absolute; bottom: 5px; left: 5px; background: var(--success); color: white; padding: 2px 8px; border-radius: 10px; font-size: 10px;">Main</span>' : ''}
                            </div>
                        `).join('')}
                    </div>
                    ${user.photos.length < CONFIG.MAX_PROFILE_PHOTOS ? `
                        <form method="POST" action="/account/photos" enctype="multipart/form-data" style="display: flex; gap: 10px; align-items: center;">
                            <input type="file" name="photos" accept="image/*" multiple required style="flex: 1;">
                            <button type="submit" class="btn btn-primary btn-sm">Add Photos</button>
                        </form>
                        <p style="font-size: 12px; color: #888; margin-top: 5px;">You can add up to ${CONFIG.MAX_PROFILE_PHOTOS} photos. First photo is your main profile picture.</p>
                    ` : '<p style="color: #888; font-size: 13px;">Maximum photos reached.</p>'}
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
                
                <button type="submit" class="btn btn-primary">Save Changes</button>
            </form>
        </div>
        
        <div class="card" style="padding: 30px; margin-bottom: 25px;">
            <h3 style="margin-bottom: 25px; color: var(--primary);">Change Password</h3>
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
                <button type="submit" class="btn btn-primary">Update Password</button>
            </form>
        </div>
        
        <div class="card" style="padding: 30px;">
            <h3 style="margin-bottom: 20px; color: var(--danger);">Danger Zone</h3>
            <p style="color: #888; margin-bottom: 20px;">Once you delete your account, there is no going back.</p>
            <form method="POST" action="/account/delete" onsubmit="return confirm('Are you sure? This cannot be undone.');">
                <button type="submit" class="btn btn-danger">Delete Account</button>
            </form>
        </div>
    </div>
    ${getFooter()}
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
    
    const messagesHtml = chatMessages.map(m => {
        const isSent = m.from === currentUser.id;
        
        if (m.type === 'photo') {
            return `
                <div style="margin-bottom: 20px; display: flex; ${isSent ? 'justify-content: flex-end' : ''};">
                    <div style="max-width: 70%;">
                        <div style="background: ${isSent ? 'linear-gradient(135deg, var(--primary-dark), var(--primary))' : 'white'}; padding: 15px; border-radius: 20px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); ${isSent ? 'color: white;' : ''}">
                            <img src="/uploads/${m.photoFile}" alt="Photo" onerror="this.onerror=null; this.src=''; this.style.background='#f0f2f5'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.innerHTML='📷';" style="max-width: 280px; max-height: 280px; border-radius: 12px; display: block; cursor: pointer;" onclick="showLightbox('${m.photoFile}')">
                            <div style="font-size: 11px; ${isSent ? 'color: rgba(255,255,255,0.7);' : 'color: #888;'} margin-top: 10px; text-align: right;">
                                ${new Date(m.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'})}
                                ${m.cost > 0 ? ` • ${m.cost} coins` : ''}
                                ${isSent ? ' ✓✓' : ''}
                            </div>
                        </div>
                    </div>
                </div>
            `;
        }
        
        return `
            <div style="margin-bottom: 20px; display: flex; ${isSent ? 'justify-content: flex-end' : ''};">
                <div style="max-width: 70%;">
                    <div style="padding: 15px 20px; border-radius: 20px; background: ${isSent ? 'linear-gradient(135deg, var(--primary-dark), var(--primary))' : 'white'}; color: ${isSent ? 'white' : '#333'}; box-shadow: 0 2px 10px rgba(0,0,0,0.1);">
                        ${m.censored ? `
                            <div style="background: rgba(255,193,7,0.2); border: 1px dashed #ffc107; padding: 10px; border-radius: 8px; margin-bottom: 10px; font-size: 12px; ${isSent ? 'color: rgba(255,255,255,0.9);' : 'color: #856404;'}">
                                ⚠️ Contact information was removed
                            </div>
                            <p style="${isSent ? 'opacity: 0.9;' : ''}">${m.text}</p>
                        ` : `<p style="line-height: 1.6;">${m.text}</p>`}
                        <div style="font-size: 11px; ${isSent ? 'opacity: 0.7;' : 'opacity: 0.5;'} margin-top: 8px; text-align: right;">
                            ${new Date(m.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'})}
                            ${isSent ? ' ✓✓' : ''}
                        </div>
                    </div>
                </div>
            </div>
        `;
    }).join('');

    // Photo section - same for male and female (both upload from device)
    const photoUploadSection = `
    <div style="background: ${currentUser.gender === 'male' && dailyStatus?.photos?.freeRemaining === 0 ? '#fff3cd' : '#e3f2fd'}; padding: 15px 20px; border-radius: 12px; margin-bottom: 15px;">
        <form method="POST" action="/chat/${chatPartner.id}/send-photo" enctype="multipart/form-data" style="display: flex; justify-content: space-between; align-items: center;">
            <label style="display: flex; align-items: center; gap: 12px; cursor: pointer; flex: 1;">
                <span style="font-size: 24px;">📷</span>
                <span style="font-weight: 500;">Send Photo</span>
                <input type="file" name="photo" accept="image/*" onchange="this.form.submit()" style="display: none;">
            </label>
            ${currentUser.gender === 'male' ? `
                <span style="font-size: 14px; font-weight: 600; color: ${dailyStatus.photos.freeRemaining > 0 ? '#4caf50' : '#ff9800'};">
                    ${dailyStatus.photos.freeRemaining > 0 ? `✓ ${dailyStatus.photos.freeRemaining} FREE` : `⚠️ ${CONFIG.MALE_PHOTO_SEND_COST} coins`}
                </span>
            ` : `
                <span style="font-size: 14px; font-weight: 600; color: #4caf50;">✓ FREE</span>
            `}
        </form>
    </div>
    `;

    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Chat with ${chatPartner.name}</title>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <style>${globalStyles}</style>
    <style>
        .chat-layout {
            height: calc(100vh - 70px);
            display: flex;
            flex-direction: column;
            background: #f0f2f5;
        }
        .chat-messages {
            flex: 1;
            overflow-y: auto;
            padding: 20px;
            padding-bottom: 250px;
        }
        .chat-input-area {
            position: fixed;
            bottom: 0;
            left: 0;
            right: 0;
            background: white;
            padding: 20px;
            border-top: 1px solid #e0e0e0;
            box-shadow: 0 -4px 20px rgba(0,0,0,0.1);
            z-index: 100;
        }
        .chat-input-container {
            max-width: 800px;
            margin: 0 auto;
        }
        @media (max-width: 768px) {
            .chat-messages {
                padding-bottom: 280px;
            }
            .chat-input-area {
                padding: 15px;
            }
        }
    </style>
</head>
<body>
    <nav class="navbar" style="position: fixed; top: 0; left: 0; right: 0; z-index: 1000;">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">← Back</a>
                <div style="display: flex; align-items: center; gap: 15px;">
                    <div class="avatar small">
                        ${chatPartner.photo ? `<img src="/uploads/${chatPartner.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';">` : (chatPartner.gender === 'female' ? '👩' : '👨')}
                    </div>
                    <div>
                        <div style="font-weight: 600;">${chatPartner.name}</div>
                        <div style="font-size: 12px; color: ${chatPartner.isOnline ? '#4caf50' : '#999'};">
                            ${chatPartner.isOnline ? '● Online' : 'Last seen ' + new Date(chatPartner.lastActive).toLocaleDateString()}
                        </div>
                    </div>
                </div>
                ${currentUser.gender === 'male' ? `<span style="background: linear-gradient(135deg, #ffd700, #ff9800); color: white; padding: 8px 16px; border-radius: 20px; font-weight: 600; font-size: 14px;">🪙 ${currentUser.coins}</span>` : ''}
            </div>
        </div>
    </nav>
    
    <div class="chat-layout" style="margin-top: 70px;">
        <div class="chat-messages" id="chatContainer">
            <div class="container" style="max-width: 800px;">
                <div style="background: #fff3cd; border: 2px dashed #ffc107; padding: 15px; border-radius: 10px; margin-bottom: 25px; text-align: center; color: #856404; font-size: 14px;">
                    🔒 For your safety, phone numbers, emails, and contact info are automatically removed from messages.
                </div>
                ${messagesHtml || '<div class="empty-state" style="padding: 40px;"><div class="empty-state-icon">💬</div><p style="color: #888;">Start the conversation...</p></div>'}
            </div>
        </div>
    </div>
    
    <div class="chat-input-area">
        <div class="chat-input-container">
            ${photoUploadSection}
            
            <form method="POST" action="/chat/${chatPartner.id}/send" style="display: flex; gap: 12px;">
                <input type="text" name="message" placeholder="Type your message..." autocomplete="off" style="flex: 1; padding: 14px 20px; border: 2px solid #e0e0e0; border-radius: 30px; font-size: 15px;">
                <button type="submit" class="btn btn-primary" style="padding: 14px 28px;">Send</button>
            </form>
        </div>
    </div>
    
    <script>
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
            chatContainer.scrollTop = chatContainer.scrollHeight;
        }
        
        function showLightbox(photo) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="📷" onerror="this.onerror=null; this.src=\'\'; this.style.background=\'#f0f2f5\'; this.style.display=\'flex\'; this.style.alignItems=\'center\'; this.style.justifyContent=\'center\'; this.innerHTML=\'📷\';" style="max-width:90%;max-height:90%;border-radius:10px;">';
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
    
    const packagesHtml = coinPackages.map(pkg => `
        <div class="card" style="padding: 30px; text-align: center; position: relative; ${pkg.popular ? 'border: 3px solid var(--primary); transform: scale(1.05);' : ''}">
            ${pkg.popular ? '<div style="position: absolute; top: -12px; left: 50%; transform: translateX(-50%); background: var(--primary); color: white; padding: 5px 20px; border-radius: 20px; font-size: 12px; font-weight: 600;">RECOMMENDED</div>' : ''}
            <div style="font-size: 48px; margin-bottom: 10px;">🪙</div>
            <h3 style="font-size: 36px; margin-bottom: 5px;">${pkg.coins.toLocaleString()}</h3>
            <p style="color: #888; margin-bottom: 20px;">Coins</p>
            <div style="background: #f8f9fa; padding: 15px; border-radius: 12px; margin-bottom: 20px;">
                <p style="font-size: 32px; font-weight: 700; color: var(--primary);">$${pkg.price}</p>
                <p style="color: #888; font-size: 14px;">$0.10 per coin</p>
            </div>
            <ul style="text-align: left; margin-bottom: 25px; padding-left: 20px; color: #666; font-size: 14px; line-height: 2;">
                <li>✓ Send ${pkg.coins} messages</li>
                <li>✓ View ${Math.floor(pkg.coins / 20)} profiles</li>
                <li>✓ Send ${Math.floor(pkg.coins / 10)} photos</li>
                <li>✓ No expiration</li>
            </ul>
            <form method="POST" action="/buy-coins/select">
                <input type="hidden" name="coins" value="${pkg.coins}">
                <input type="hidden" name="price" value="${pkg.price}">
                <button type="submit" class="btn ${pkg.popular ? 'btn-primary' : 'btn-outline'}" style="width: 100%; padding: 15px; font-size: 16px;">
                    ${pkg.popular ? 'Select Package' : 'Choose'}
                </button>
            </form>
        </div>
    `).join('');
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Buy Coins - FindYourMatch</title>
    <style>${globalStyles}</style>
    <style>
        .package-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 25px; align-items: start; }
        @media (max-width: 768px) { .package-grid { grid-template-columns: 1fr; } }
        .minimum-notice { background: linear-gradient(135deg, #fff3cd, #ffe0b2); border: 2px solid #ff9800; padding: 20px; border-radius: 12px; margin-bottom: 30px; text-align: center; }
    </style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/" class="logo">FindYourMatch</a>
                <div style="display: flex; align-items: center; gap: 20px;">
                    <span style="background: linear-gradient(135deg, #ffd700, #ff9800); color: white; padding: 8px 16px; border-radius: 20px; font-weight: 600;">🪙 ${user.coins}</span>
                    <a href="/dashboard">Dashboard</a>
                    <a href="/logout">Logout</a>
                </div>
            </div>
        </div>
    </nav>
    
    <section style="background: linear-gradient(135deg, var(--secondary) 0%, #764ba2 100%); color: white; padding: 60px 0; text-align: center;">
        <div class="container">
            <h1 style="font-size: 42px; margin-bottom: 15px;">🪙 Buy Coins</h1>
            <p style="font-size: 18px; opacity: 0.95; max-width: 600px; margin: 0 auto;">
                Only <strong>$0.10 per coin</strong>. Minimum purchase: <strong>$50 (500 coins)</strong>
            </p>
            <div style="margin-top: 25px; display: inline-flex; gap: 30px; background: rgba(255,255,255,0.1); padding: 20px 40px; border-radius: 16px;">
                <div style="text-align: center;">
                    <div style="font-size: 28px; font-weight: 700;">💬</div>
                    <div style="font-size: 14px; margin-top: 5px;">1 coin/message</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 28px; font-weight: 700;">👁️</div>
                    <div style="font-size: 14px; margin-top: 5px;">20 coins/view</div>
                </div>
                <div style="text-align: center;">
                    <div style="font-size: 28px; font-weight: 700;">📸</div>
                    <div style="font-size: 14px; margin-top: 5px;">10 coins/photo</div>
                </div>
            </div>
        </div>
    </section>
    
    <section style="padding: 60px 0; background: #f8f9fa;">
        <div class="container">
            <div class="minimum-notice">
                <p style="color: #856404; font-size: 16px; font-weight: 600;">
                    💰 Minimum Purchase: $50 USD (500 coins) @ $0.10 per coin
                </p>
            </div>
            
            <h2 style="text-align: center; margin-bottom: 40px;">Choose Your Package</h2>
            <div class="package-grid">
                ${packagesHtml}
            </div>
            
            <div style="background: white; padding: 30px; border-radius: 16px; margin-top: 40px; text-align: center;">
                <h3 style="margin-bottom: 15px;">💳 Payment Method</h3>
                <p style="color: #888; margin-bottom: 20px;">We accept gift cards as payment. Minimum value: <strong>$50 USD</strong></p>
                <div style="display: flex; justify-content: center; gap: 15px; flex-wrap: wrap;">
                    <span style="background: #f8f9fa; padding: 10px 20px; border-radius: 10px; font-size: 14px;">🎁 Apple Gift Card ($50+)</span>
                    <span style="background: #f8f9fa; padding: 10px 20px; border-radius: 10px; font-size: 14px;">🎁 Google Play ($50+)</span>
                    <span style="background: #f8f9fa; padding: 10px 20px; border-radius: 10px; font-size: 14px;">🎁 Amazon ($50+)</span>
                    <span style="background: #f8f9fa; padding: 10px 20px; border-radius: 10px; font-size: 14px;">💳 Visa/Mastercard ($50+)</span>
                </div>
            </div>
        </div>
    </section>
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
<html>
<head>
    <title>Upload Gift Card - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/buy-coins" class="logo">
                    <img src="/logo.png" alt="FindYourMatch" onerror="this.style.display='none'">
                    <span>FindYourMatch</span>
                </a>
                <div>
                    <a href="/logout">Logout</a>
                </div>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 60px 20px; max-width: 600px;">
        <div style="background: white; padding: 40px; border-radius: 20px; box-shadow: 0 10px 40px rgba(0,0,0,0.1);">
            <div style="text-align: center; margin-bottom: 30px;">
                <div style="font-size: 56px; margin-bottom: 15px;">🎁</div>
                <h2>Upload Gift Card</h2>
                <p style="color: #888; margin-top: 10px;">
                    Purchasing <strong>${purchase.coins.toLocaleString()} coins</strong> for <strong>$${purchase.price}</strong>
                </p>
                <p style="color: var(--primary); font-size: 14px; margin-top: 5px;">
                    ($0.10 per coin | Minimum $50)
                </p>
            </div>
            
            <div style="background: #fff3cd; border-left: 4px solid #ffc107; padding: 20px; border-radius: 10px; margin-bottom: 25px;">
                <h4 style="color: #856404; margin-bottom: 10px;">📋 Requirements:</h4>
                <ul style="color: #856404; padding-left: 20px; line-height: 2; font-size: 14px;">
                    <li>Gift card must be worth <strong>$${purchase.price} or more</strong></li>
                    <li>Take clear photos of the <strong>front and back</strong></li>
                    <li>Make sure the code is clearly visible</li>
                    <li>Admin will verify within 24 hours</li>
                </ul>
            </div>
            
            <form method="POST" action="/buy-coins/upload" enctype="multipart/form-data">
                <div class="form-group">
                    <label>Gift Card Type *</label>
                    <select name="cardType" required style="width: 100%; padding: 14px; border: 2px solid #e0e0e0; border-radius: 12px;">
                        <option value="">Select card type...</option>
                        <option value="Apple Gift Card">🍎 Apple Gift Card ($50+)</option>
                        <option value="Google Play">🤖 Google Play ($50+)</option>
                        <option value="Amazon">📦 Amazon ($50+)</option>
                        <option value="Visa">💳 Visa Gift Card ($50+)</option>
                        <option value="Mastercard">💳 Mastercard Gift Card ($50+)</option>
                        <option value="Other">🎁 Other ($50+)</option>
                    </select>
                </div>
                
                <div class="form-group">
                    <label>Front of Card (showing value) *</label>
                    <div style="background: #f8f9fa; padding: 25px; border-radius: 12px; border: 2px dashed #ddd; text-align: center;">
                        <input type="file" name="front" accept="image/*" required id="frontInput" onchange="previewImage(this, 'frontPreview')" style="display: none;">
                        <label for="frontInput" style="cursor: pointer; display: inline-block; padding: 12px 25px; background: var(--primary); color: white; border-radius: 25px; font-weight: 600;">
                            📷 Upload Front
                        </label>
                        <div id="frontPreview" style="margin-top: 15px;"></div>
                    </div>
                </div>
                
                <div class="form-group">
                    <label>Back of Card (showing code) *</label>
                    <div style="background: #f8f9fa; padding: 25px; border-radius: 12px; border: 2px dashed #ddd; text-align: center;">
                        <input type="file" name="back" accept="image/*" required id="backInput" onchange="previewImage(this, 'backPreview')" style="display: none;">
                        <label for="backInput" style="cursor: pointer; display: inline-block; padding: 12px 25px; background: var(--primary); color: white; border-radius: 25px; font-weight: 600;">
                            📷 Upload Back
                        </label>
                        <div id="backPreview" style="margin-top: 15px;"></div>
                    </div>
                </div>
                
                <div style="background: #e8f5e9; padding: 15px; border-radius: 10px; margin-bottom: 25px;">
                    <p style="color: #2e7d32; font-size: 14px; text-align: center;">
                        ✓ You will receive <strong>${purchase.coins.toLocaleString()} coins</strong> after verification<br>
                        <span style="font-size: 12px;">($0.10 per coin)</span>
                    </p>
                </div>
                
                <button type="submit" class="btn btn-primary" style="width: 100%; padding: 18px; font-size: 16px;">
                    Submit for Verification
                </button>
            </form>
        </div>
    </div>
    
    <script>
        function previewImage(input, previewId) {
            const preview = document.getElementById(previewId);
            if (input.files && input.files[0]) {
                const reader = new FileReader();
                reader.onload = function(e) {
                    preview.innerHTML = '<img src="' + e.target.result + '" alt="📷" onerror="this.style.display=\'none\'; this.parentElement.innerHTML=\'<div style=\\\'display:flex;align-items:center;justify-content:center;height:100px;background:#f0f2f5;color:#888;font-size:24px;\\\'>📷</div>\';" style="max-width: 200px; max-height: 200px; border-radius: 10px; box-shadow: 0 5px 15px rgba(0,0,0,0.1);">';
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
<html>
<head>
    <title>Submitted - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body style="background: linear-gradient(135deg, var(--secondary) 0%, #764ba2 100%); min-height: 100vh; display: flex; align-items: center; justify-content: center; padding: 20px;">
    <div style="background: white; padding: 60px; border-radius: 20px; text-align: center; max-width: 450px;">
        <div style="width: 100px; height: 100px; background: linear-gradient(135deg, #4caf50, #45a049); border-radius: 50%; margin: 0 auto 25px; display: flex; align-items: center; justify-content: center; color: white; font-size: 50px;">✓</div>
        <h2 style="margin-bottom: 15px;">Submitted Successfully!</h2>
        <p style="color: #888; margin-bottom: 25px;">
            Your gift card is being verified by our team.<br>
            <strong>${purchase.coins.toLocaleString()} coins</strong> will be added to your account within 24 hours.<br>
            <span style="font-size: 13px;">($0.10 per coin)</span>
        </p>
        <a href="/dashboard" class="btn btn-primary">Back to Dashboard</a>
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
<html>
<head>
    <title>Admin Dashboard - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <div style="color: white; font-size: 22px; font-weight: 700;">🔐 Admin Panel</div>
                <div>
                    <a href="/dashboard" style="color: white; margin-right: 20px;">Exit Admin</a>
                    <a href="mailto:findyourmatch6187@gmail.com" style="color: var(--primary); font-size: 14px; margin-right: 15px;">📧 Support</a>
                    <a href="/logout" style="color: white;">Logout</a>
                </div>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        <h2 style="margin-bottom: 30px;">Dashboard Overview</h2>
        
        <div class="grid grid-4" style="margin-bottom: 40px;">
            <div class="stats-card">
                <div class="stats-number">${stats.total}</div>
                <div class="stats-label">Total Users</div>
            </div>
            <div class="stats-card">
                <div class="stats-number" style="color: #e91e63;">${stats.females}</div>
                <div class="stats-label">Female Users</div>
            </div>
            <div class="stats-card">
                <div class="stats-number" style="color: #2196f3;">${stats.males}</div>
                <div class="stats-label">Male Users</div>
            </div>
            <div class="stats-card">
                <div class="stats-number" style="color: #4caf50;">${stats.online}</div>
                <div class="stats-label">Online Now</div>
            </div>
        </div>
        
        <div class="grid grid-3">
            <div class="stats-card">
                <div class="stats-number" style="color: #ff9800;">${stats.pending}</div>
                <div class="stats-label" style="margin-bottom: 15px;">Pending Payments</div>
                <a href="/admin/transactions" class="btn btn-warning btn-sm">Review Payments</a>
            </div>
            <div class="stats-card">
                <div class="stats-number" style="color: var(--danger);">${stats.reports}</div>
                <div class="stats-label" style="margin-bottom: 15px;">Pending Reports</div>
                <a href="/admin/reports" class="btn btn-danger btn-sm">Review Reports</a>
            </div>
            <div class="stats-card">
                <div class="stats-number" style="color: #9c27b0;">${stats.censorshipAlerts}</div>
                <div class="stats-label" style="margin-bottom: 15px;">Censorship Alerts</div>
                <a href="/admin/censorship" class="btn btn-primary btn-sm">View Alerts</a>
            </div>
        </div>
        
        <div style="margin-top: 40px; text-align: center;">
            <a href="/admin/users" class="btn btn-primary btn-lg">Manage All Users</a>
            <a href="/admin/assignments" class="btn btn-success btn-lg" style="margin-left: 15px;">Manage Assignments</a>
            <a href="/admin/chats" class="btn btn-warning btn-lg" style="margin-left: 15px;">💬 Chat Monitor</a>
            <a href="/admin/notifications" class="btn btn-info btn-lg" style="margin-left: 15px;">📢 Notifications</a>
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
            <div class="card" style="padding: 25px; margin-bottom: 20px;">
                <div style="display: flex; align-items: center; gap: 15px; margin-bottom: 20px;">
                    <div class="avatar-placeholder">
                        ${f.photo ? `<img src="/uploads/${f.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';">` : '👩'}
                    </div>
                    <div>
                        <h4>${f.name}, ${f.age}</h4>
                        <p style="color: #888; font-size: 14px;">${f.email} • ${f.location}</p>
                    </div>
                </div>
                
                <div style="margin-bottom: 15px;">
                    <p style="color: #666; font-size: 14px; margin-bottom: 10px;">
                        <strong>Assigned Gentlemen (${assignedMales.length}):</strong>
                    </p>
                    ${assignedMales.length === 0 ? '<p style="color: #999; font-size: 13px;">No assignments yet</p>' : `
                        <div style="display: flex; flex-wrap: wrap; gap: 10px;">
                            ${assignedMales.map(m => `
                                <div style="background: #e3f2fd; padding: 8px 15px; border-radius: 20px; font-size: 13px; display: flex; align-items: center; gap: 8px;">
                                    ${m.name}
                                    <form method="POST" action="/admin/assignments/remove" style="display: inline;">
                                        <input type="hidden" name="femaleId" value="${f.id}">
                                        <input type="hidden" name="maleId" value="${m.id}">
                                        <button type="submit" style="background: none; border: none; color: var(--danger); cursor: pointer; font-size: 16px;">×</button>
                                    </form>
                                </div>
                            `).join('')}
                        </div>
                    `}
                </div>
                
                <form method="POST" action="/admin/assignments/add" style="display: flex; gap: 10px;">
                    <input type="hidden" name="femaleId" value="${f.id}">
                    <select name="maleId" required style="flex: 1; padding: 10px 15px; border: 2px solid #e0e0e0; border-radius: 10px;">
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
<html>
<head>
    <title>Manage Assignments - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none; font-size: 20px;">← Back to Admin</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px; max-width: 900px;">
        <h2 style="margin-bottom: 10px;">👥 Manage Assignments</h2>
        <p style="color: #888; margin-bottom: 30px;">Assign male users to female users. Females will only see assigned males who message them first.</p>
        
        ${femaleList}
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
<html>
<head>
    <title>Manage Album - ${female.name}</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin/users" style="color: white; text-decoration: none;">← Back to Users</a>
                <span style="color: white;">Manage Album: ${female.name} (${female.displayId})</span>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px; max-width: 900px;">
        <div class="card" style="padding: 30px; margin-bottom: 30px;">
            <h2>📸 Upload Photos to ${female.name}'s Album</h2>
            <p style="color: #888; margin: 10px 0 20px;">These photos will be available for ${female.name} to send in chat.</p>
            
            <form method="POST" action="/admin/album/${femaleId}/upload" enctype="multipart/form-data">
                <div style="background: #f8f9fa; padding: 40px; border-radius: 16px; border: 2px dashed #ddd; text-align: center;">
                    <input type="file" name="photos" accept="image/*" multiple id="albumInput" style="display: none;">
                    <label for="albumInput" style="cursor: pointer; display: inline-block; padding: 16px 32px; background: var(--primary); color: white; border-radius: 30px; font-weight: 600; font-size: 16px;">
                        📷 Select Photos
                    </label>
                    <p style="color: #888; margin-top: 15px;">Select multiple photos</p>
                    <div id="preview" style="margin-top: 20px;"></div>
                </div>
                <button type="submit" class="btn btn-primary" style="width: 100%; margin-top: 20px; padding: 16px;">Upload to Album</button>
            </form>
        </div>
        
        <h3 style="margin-bottom: 20px;">Current Album (${albumPhotos.length} photos)</h3>
        ${albumPhotos.length === 0 ? '<p style="color: #888;">No photos yet.</p>' : `
            <div class="photo-gallery">
                ${albumPhotos.map(photo => `
                    <div class="photo-item" style="position: relative;">
                        <img src="/uploads/${photo.photoFile}" alt="Photo" onerror="this.onerror=null; this.src=''; this.style.background='#f0f2f5'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.innerHTML='📷';">
                        <form method="POST" action="/admin/album/${photo.id}/delete" style="position: absolute; top: 8px; right: 8px;">
                            <button type="submit" style="background: var(--danger); color: white; border: none; border-radius: 50%; width: 32px; height: 32px; cursor: pointer;">×</button>
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
                    const img = document.createElement('img');
                    img.src = e.target.result;
                    img.style.cssText = 'width: 100px; height: 100px; object-fit: cover; border-radius: 10px; margin: 5px;';
                    preview.appendChild(img);
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
                <td style="padding: 15px;">
                    <div style="display: flex; align-items: center; gap: 12px;">
                        <div style="width: 45px; height: 45px; border-radius: 50%; background: ${u.photo ? `url(/uploads/${u.photo})` : '#ddd'}; background-size: cover; display: flex; align-items: center; justify-content: center; font-size: 20px;">
                            ${u.photo ? '' : (u.gender === 'female' ? '👩' : '👨')}
                        </div>
                        <div>
                            <div style="font-weight: 600;">${u.name} ${u.isVerified ? '<span style="color: var(--info);">✓</span>' : ''}</div>
                            <div style="font-size: 12px; color: #888;">${u.email}</div>
                        </div>
                    </div>
                </td>
                <td style="padding: 15px;">
                    <span style="text-transform: uppercase; font-size: 12px; font-weight: 600; color: ${u.gender === 'female' ? '#e91e63' : '#2196f3'};">${u.gender}</span>
                </td>
                <td style="padding: 15px;">${u.age}</td>
                <td style="padding: 15px;">${u.location}</td>
                <td style="padding: 15px;">
                    ${u.gender === 'male' ? `
                        <div>
                            <div style="font-weight: 600; color: ${u.coins > 0 ? '#4caf50' : '#f44336'};">${u.coins} coins</div>
                            <div style="font-size: 12px; color: #888;">${u.isTrialActive ? 'Trial active' : (trialStatus.canChat ? 'Active' : 'Expired')}</div>
                        </div>
                    ` : `<div style="font-size: 12px; color: #888;">${assignedCount} assigned</div>`}
                </td>
                <td style="padding: 15px;">
                    <span style="padding: 5px 12px; border-radius: 15px; font-size: 12px; font-weight: 600; background: ${u.isBlocked ? '#fee' : '#e8f5e9'}; color: ${u.isBlocked ? '#c33' : '#2e7d32'};">
                        ${u.isBlocked ? 'Blocked' : 'Active'}
                    </span>
                </td>
                <td style="padding: 15px;">
                    <a href="/admin/users/${u.id}/view" class="btn btn-sm btn-secondary">View</a>
                    <a href="/admin/users/${u.id}/edit" class="btn btn-sm btn-primary">Edit</a>
                    ${u.gender === 'female' ? `
                        <a href="/admin/album/${u.id}" class="btn btn-sm btn-info">📸 Profile Album</a>
                    ` : ''}
                    <form action="/admin/users/${u.id}/toggle-block" method="POST" style="display: inline;">
                        <button type="submit" class="btn btn-sm ${u.isBlocked ? 'btn-success' : 'btn-danger'}">
                            ${u.isBlocked ? 'Unblock' : 'Block'}
                        </button>
                    </form>
                </td>
            </tr>
        `;
    }).join('');
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Manage Users - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none; font-size: 20px;">← Back to Admin</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        <h2 style="margin-bottom: 20px;">All Users</h2>
        
        <!-- Filters -->
        <div style="background: white; padding: 20px; border-radius: 12px; margin-bottom: 25px;">
            <form method="GET" action="/admin/users" style="display: flex; gap: 15px; flex-wrap: wrap; align-items: end;">
                <div>
                    <label style="font-size: 12px; color: #888; display: block; margin-bottom: 5px;">Gender</label>
                    <select name="gender" style="padding: 10px 15px; border: 2px solid #e0e0e0; border-radius: 10px;">
                        <option value="">All</option>
                        <option value="female" ${gender === 'female' ? 'selected' : ''}>Female</option>
                        <option value="male" ${gender === 'male' ? 'selected' : ''}>Male</option>
                    </select>
                </div>
                <div>
                    <label style="font-size: 12px; color: #888; display: block; margin-bottom: 5px;">Verified</label>
                    <select name="verified" style="padding: 10px 15px; border: 2px solid #e0e0e0; border-radius: 10px;">
                        <option value="">All</option>
                        <option value="true" ${verified === 'true' ? 'selected' : ''}>Verified</option>
                        <option value="false" ${verified === 'false' ? 'selected' : ''}>Unverified</option>
                    </select>
                </div>
                <div>
                    <label style="font-size: 12px; color: #888; display: block; margin-bottom: 5px;">Search</label>
                    <input type="text" name="search" placeholder="Name, email, location..." value="${search || ''}" style="padding: 10px 15px; border: 2px solid #e0e0e0; border-radius: 10px; min-width: 200px;">
                </div>
                <button type="submit" class="btn btn-primary btn-sm">Filter</button>
                <a href="/admin/users" class="btn btn-outline btn-sm">Clear</a>
            </form>
        </div>
        
        <div style="overflow-x: auto; background: white; border-radius: 12px; box-shadow: 0 2px 10px rgba(0,0,0,0.1);">
            <table style="width: 100%;">
                <thead>
                    <tr style="background: var(--secondary); color: white;">
                        <th style="padding: 15px; text-align: left;">User</th>
                        <th style="padding: 15px;">Gender</th>
                        <th style="padding: 15px;">Age</th>
                        <th style="padding: 15px;">Location</th>
                        <th style="padding: 15px;">Status</th>
                        <th style="padding: 15px;">Account</th>
                        <th style="padding: 15px;">Actions</th>
                    </tr>
                </thead>
                <tbody>
                    ${userRows || '<tr><td colspan="7" style="padding: 40px; text-align: center; color: #888;">No users found</td></tr>'}
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
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>View User - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin/users" style="color: white; text-decoration: none;">← Back to Users</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px; max-width: 800px;">
        <div class="card" style="padding: 40px;">
            <div style="display: flex; align-items: center; gap: 20px; margin-bottom: 30px;">
                <div style="width: 100px; height: 100px; border-radius: 50%; overflow: hidden; background: linear-gradient(135deg, var(--secondary), #764ba2);">
                    ${user.photo ? `<img src="/uploads/${user.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='40px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : '<div style="display: flex; align-items: center; justify-content: center; height: 100%; color: white; font-size: 50px;">👤</div>'}
                </div>
                <div>
                    <h2 style="margin-bottom: 5px;">${user.name} ${user.isVerified ? '<span style="color: var(--info);">✓</span>' : ''}</h2>
                    <p style="color: #888;">${user.email}</p>
                </div>
            </div>
            
            <div style="background: #fff3cd; padding: 20px; border-radius: 12px; margin-bottom: 30px; border-left: 4px solid #ffc107;">
                <h4 style="color: #856404; margin-bottom: 15px;">🔐 Login Credentials</h4>
                <p><strong>Email:</strong> ${user.email}</p>
                <p><strong>Password:</strong> ${user.showPassword || '(encrypted)'}</p>
            </div>
            
            <div class="grid grid-3" style="margin-bottom: 30px;">
                <div style="background: #f8f9fa; padding: 20px; border-radius: 12px;">
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">User ID</label>
                    <p style="font-weight: 600; font-size: 18px; color: var(--primary);">#${user.displayId || user.id}</p>
                </div>
                <div style="background: #f8f9fa; padding: 20px; border-radius: 12px;">
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">Gender</label>
                    <p style="font-weight: 600; font-size: 18px; text-transform: capitalize;">${user.gender}</p>
                </div>
                <div style="background: #f8f9fa; padding: 20px; border-radius: 12px;">
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">Age</label>
                    <p style="font-weight: 600; font-size: 18px;">${user.age}</p>
                </div>
                <div style="background: #f8f9fa; padding: 20px; border-radius: 12px;">
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">Location</label>
                    <p style="font-weight: 600; font-size: 18px;">${user.location}</p>
                </div>
                <div style="background: #f8f9fa; padding: 20px; border-radius: 12px;">
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">Coins</label>
                    <p style="font-weight: 600; font-size: 18px; color: ${user.coins > 0 ? '#4caf50' : '#f44336'};">${user.coins}</p>
                </div>
                <div style="background: #f8f9fa; padding: 20px; border-radius: 12px;">
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">Messages</label>
                    <p style="font-weight: 600; font-size: 18px;">${userMessages.length}</p>
                </div>
            </div>
            
            ${user.photos.length > 0 ? `
                <div style="margin: 30px 0;">
                    <h4 style="margin-bottom: 15px;">Photos (${user.photos.length})</h4>
                    <div class="photo-gallery">
                        ${user.photos.map(photo => `
                            <div class="photo-item">
                                <img src="/uploads/${photo}" alt="📷" onerror="this.style.display='none'; this.parentElement.innerHTML='<div style=\'display:flex;align-items:center;justify-content:center;height:100%;background:#f0f2f5;color:#888;font-size:24px;\'>📷</div>'">
                            </div>
                        `).join('')}
                    </div>
                </div>
            ` : ''}
            
            <div style="margin-top: 30px; display: flex; gap: 15px;">
                <a href="/admin/users/${user.id}/edit" class="btn btn-primary">Edit Profile</a>
                <form action="/admin/users/${user.id}/toggle-verify" method="POST" style="display: inline;">
                    <button type="submit" class="btn ${user.isVerified ? 'btn-warning' : 'btn-success'}">
                        ${user.isVerified ? 'Remove Verification' : 'Verify User'}
                    </button>
                </form>
                <form action="/admin/users/${user.id}/delete" method="POST" style="display: inline;" onsubmit="return confirm('DELETE this user permanently?');">
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
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Edit User - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin/users" style="color: white; text-decoration: none;">← Back to Users</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px; max-width: 700px;">
        <div class="card" style="padding: 40px;">
            <h2 style="margin-bottom: 30px;">✏️ Edit ${user.name}</h2>
            
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
                
                <div style="display: flex; gap: 15px; margin-top: 20px;">
                    <button type="submit" class="btn btn-primary" style="flex: 1;">Save Changes</button>
                    <a href="/admin/users" class="btn btn-outline" style="flex: 1; text-align: center;">Cancel</a>
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
    
    if (pending.length === 0) {
        return res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Transactions - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none;">← Back to Admin</a>
            </div>
        </div>
    </nav>
    <div class="container" style="padding: 100px 20px; text-align: center;">
        <div class="card" style="padding: 60px; max-width: 400px; margin: 0 auto;">
            <div style="font-size: 60px; margin-bottom: 20px;">✅</div>
            <h2>No Pending Transactions</h2>
            <p style="color: #888; margin-top: 10px;">All caught up!</p>
        </div>
    </div>
</body>
</html>
        `);
    }
    
    const txRows = pending.map(t => `
        <tr>
            <td style="padding: 20px;">
                <div style="font-weight: 600;">${t.userEmail}</div>
                <div style="font-size: 12px; color: #888;">User ID: ${t.userId}</div>
            </td>
            <td style="padding: 20px;">${t.cardType}</td>
            <td style="padding: 20px;">$50+</td>
            <td style="padding: 20px;">
                <a href="/uploads/${t.frontImage}" target="_blank" style="color: var(--primary); margin-right: 10px;">Front</a>
                <a href="/uploads/${t.backImage}" target="_blank" style="color: var(--primary);">Back</a>
            </td>
            <td style="padding: 20px;">${new Date(t.createdAt).toLocaleDateString()}</td>
            <td style="padding: 20px;">
                <form action="/admin/transactions/${t.id}/approve" method="POST" style="display: inline; margin-right: 10px;">
                    <button type="submit" class="btn btn-sm btn-success">✓ Approve</button>
                </form>
                <form action="/admin/transactions/${t.id}/reject" method="POST" style="display: inline;">
                    <button type="submit" class="btn btn-sm btn-danger">✗ Reject</button>
                </form>
            </td>
        </tr>
    `).join('');
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Pending Payments - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none;">← Back to Admin</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        <h2 style="margin-bottom: 30px;">Pending Gift Card Verifications</h2>
        <div style="background: white; border-radius: 12px; overflow: hidden; box-shadow: 0 2px 10px rgba(0,0,0,0.1);">
            <table style="width: 100%;">
                <thead>
                    <tr style="background: var(--secondary); color: white;">
                        <th style="padding: 20px; text-align: left;">User</th>
                        <th style="padding: 20px;">Card Type</th>
                        <th style="padding: 20px;">Amount</th>
                        <th style="padding: 20px;">Images</th>
                        <th style="padding: 20px;">Date</th>
                        <th style="padding: 20px;">Actions</th>
                    </tr>
                </thead>
                <tbody>${txRows}</tbody>
            </table>
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
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Censorship Alerts - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none;">← Back to Admin</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        <h2 style="margin-bottom: 30px;">🚨 Censorship Alerts (${pendingAlerts.length})</h2>
        
        ${pendingAlerts.length === 0 ? '<div class="card" style="padding: 60px; text-align: center; color: #888;">No pending alerts</div>' : `
            <div style="display: flex; flex-direction: column; gap: 20px;">
                ${pendingAlerts.map(alert => `
                    <div class="card" style="padding: 25px; border-left: 4px solid #9c27b0;">
                        <div style="display: flex; justify-content: space-between; align-items: start; margin-bottom: 15px;">
                            <div>
                                <h4 style="margin-bottom: 5px;">${alert.fromUserName} → ${alert.toUserName || 'Unknown'}</h4>
                                <p style="color: #888; font-size: 14px;">${new Date(alert.timestamp).toLocaleString()}</p>
                            </div>
                            <form action="/admin/censorship/${alert.id}/resolve" method="POST">
                                <button type="submit" class="btn btn-sm btn-success">Mark Reviewed</button>
                            </form>
                        </div>
                        
                        <div style="background: #f8f9fa; padding: 15px; border-radius: 10px; margin-bottom: 15px;">
                            <p style="color: #888; font-size: 12px; margin-bottom: 5px;">ORIGINAL:</p>
                            <p style="font-family: monospace; background: #fff3cd; padding: 12px; border-radius: 8px; word-break: break-all;">${alert.originalText}</p>
                        </div>
                        
                        <div style="background: #f8f9fa; padding: 15px; border-radius: 10px;">
                            <p style="color: #888; font-size: 12px; margin-bottom: 5px;">CENSORED:</p>
                            <p style="font-family: monospace; background: #e8f5e9; padding: 12px; border-radius: 8px;">${alert.censoredText}</p>
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
    
    const reportRows = filteredReports.sort((a, b) => b.createdAt - a.createdAt).map(r => `
        <tr style="${r.status === 'pending' ? 'background: #fff3cd;' : ''}">
            <td style="padding: 15px;">
                <div style="font-weight: 600;">${r.id}</div>
                <div style="font-size: 12px; color: #888;">${new Date(r.createdAt).toLocaleDateString()}</div>
            </td>
            <td style="padding: 15px;">
                <div style="font-weight: 600;">${r.reporterName}</div>
                <div style="font-size: 12px; color: #888;">${r.reporterEmail}</div>
            </td>
            <td style="padding: 15px;">
                <div style="font-weight: 600;">${r.reportedName}</div>
                <div style="font-size: 12px; color: #888;">${r.reportedEmail}</div>
            </td>
            <td style="padding: 15px;">
                <span style="background: ${getReportReasonColor(r.reason)}; color: white; padding: 5px 12px; border-radius: 15px; font-size: 12px;">${r.reason}</span>
            </td>
            <td style="padding: 15px;">
                <span style="padding: 5px 12px; border-radius: 15px; font-size: 12px; font-weight: 600; background: ${r.status === 'pending' ? '#fff3cd' : r.status === 'resolved' ? '#e8f5e9' : '#fee'}; color: ${r.status === 'pending' ? '#856404' : r.status === 'resolved' ? '#2e7d32' : '#c33'};">
                    ${r.status}
                </span>
            </td>
            <td style="padding: 15px;">
                <a href="/admin/reports/${r.id}" class="btn btn-primary btn-sm">View</a>
            </td>
        </tr>
    `).join('');
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Reports - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none; font-size: 20px;">← Back to Admin</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        <h2 style="margin-bottom: 25px;">🚨 User Reports</h2>
        
        <div style="display: flex; gap: 10px; margin-bottom: 25px;">
            <a href="/admin/reports" class="btn btn-sm ${!status ? 'btn-primary' : 'btn-outline'}">All</a>
            <a href="/admin/reports?status=pending" class="btn btn-sm ${status === 'pending' ? 'btn-primary' : 'btn-outline'}">Pending</a>
            <a href="/admin/reports?status=resolved" class="btn btn-sm ${status === 'resolved' ? 'btn-primary' : 'btn-outline'}">Resolved</a>
            <a href="/admin/reports?status=dismissed" class="btn btn-sm ${status === 'dismissed' ? 'btn-primary' : 'btn-outline'}">Dismissed</a>
        </div>
        
        <div style="background: white; border-radius: 12px; overflow: hidden; box-shadow: 0 2px 10px rgba(0,0,0,0.1);">
            <table style="width: 100%;">
                <thead>
                    <tr style="background: var(--secondary); color: white;">
                        <th style="padding: 15px;">ID</th>
                        <th style="padding: 15px;">Reporter</th>
                        <th style="padding: 15px;">Reported User</th>
                        <th style="padding: 15px;">Reason</th>
                        <th style="padding: 15px;">Status</th>
                        <th style="padding: 15px;">Actions</th>
                    </tr>
                </thead>
                <tbody>
                    ${reportRows || '<tr><td colspan="6" style="padding: 40px; text-align: center; color: #888;">No reports found</td></tr>'}
                </tbody>
            </table>
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
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Report #${report.id} - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin/reports" style="color: white; text-decoration: none; font-size: 20px;">← Back to Reports</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px; max-width: 800px;">
        <div class="card" style="padding: 30px;">
            <div style="display: flex; justify-content: space-between; align-items: start; margin-bottom: 25px;">
                <h2>Report #${report.id}</h2>
                <span style="padding: 8px 16px; border-radius: 20px; font-size: 14px; font-weight: 600; background: ${report.status === 'pending' ? '#fff3cd' : report.status === 'resolved' ? '#e8f5e9' : '#fee'}; color: ${report.status === 'pending' ? '#856404' : report.status === 'resolved' ? '#2e7d32' : '#c33'};">
                    ${report.status.toUpperCase()}
                </span>
            </div>
            
            <div style="background: #f8f9fa; padding: 20px; border-radius: 12px; margin-bottom: 25px;">
                <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 20px; margin-bottom: 20px;">
                    <div>
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Reporter</label>
                        <p style="font-weight: 600; font-size: 16px;">${report.reporterName}</p>
                        <p style="font-size: 13px; color: #666;">${report.reporterEmail}</p>
                        <a href="/admin/users/${report.reporterId}/view" class="btn btn-sm btn-outline" style="margin-top: 10px;">View Profile</a>
                    </div>
                    <div>
                        <label style="color: #888; font-size: 12px; text-transform: uppercase;">Reported User</label>
                        <p style="font-weight: 600; font-size: 16px;">${report.reportedName}</p>
                        <p style="font-size: 13px; color: #666;">${report.reportedEmail}</p>
                        <a href="/admin/users/${report.reportedId}/view" class="btn btn-sm btn-outline" style="margin-top: 10px;">View Profile</a>
                    </div>
                </div>
                
                <div style="margin-bottom: 15px;">
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">Reason</label>
                    <p style="font-weight: 600; font-size: 16px; color: ${getReportReasonColor(report.reason)};">${report.reason}</p>
                </div>
                
                <div>
                    <label style="color: #888; font-size: 12px; text-transform: uppercase;">Details</label>
                    <p style="background: white; padding: 15px; border-radius: 8px; margin-top: 8px; line-height: 1.6;">${report.details || 'No additional details provided.'}</p>
                </div>
            </div>
            
            ${report.status === 'pending' ? `
                <div style="display: flex; gap: 15px;">
                    <form method="POST" action="/admin/reports/${report.id}/resolve" style="flex: 1;">
                        <button type="submit" name="action" value="warn" class="btn btn-warning" style="width: 100%;">⚠️ Warn User</button>
                    </form>
                    <form method="POST" action="/admin/reports/${report.id}/resolve" style="flex: 1;">
                        <button type="submit" name="action" value="block" class="btn btn-danger" style="width: 100%;">🚫 Block User</button>
                    </form>
                    <form method="POST" action="/admin/reports/${report.id}/dismiss" style="flex: 1;">
                        <button type="submit" class="btn btn-outline" style="width: 100%;">✓ Dismiss</button>
                    </form>
                </div>
            ` : `
                <div style="background: #e8f5e9; padding: 20px; border-radius: 12px;">
                    <p style="color: #2e7d32;"><strong>Action Taken:</strong> ${report.action || 'None'}</p>
                    <p style="font-size: 13px; color: #666; margin-top: 5px;">Reviewed on ${new Date(report.reviewedAt).toLocaleString()}</p>
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

    const chatRows = sortedChats.map(chat => `
        <tr>
            <td style="padding: 15px;">
                <div style="display: flex; align-items: center; gap: 10px;">
                    <div style="width: 40px; height: 40px; border-radius: 50%; background: linear-gradient(135deg, var(--secondary), #764ba2); display: flex; align-items: center; justify-content: center; color: white; overflow: hidden;">
                        ${chat.user1.photo ? `<img src="/uploads/${chat.user1.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='30px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover; border-radius: 50%;">` : (chat.user1.gender === 'female' ? '👩' : '👨')}
                    </div>
                    <div>
                        <div style="font-weight: 600;">${chat.user1.name}</div>
                        <div style="font-size: 12px; color: #888;">${chat.user1.gender}</div>
                    </div>
                </div>
            </td>
            <td style="padding: 15px;">
                <div style="display: flex; align-items: center; gap: 10px;">
                    <div style="width: 40px; height: 40px; border-radius: 50%; background: linear-gradient(135deg, #2196f3, #1976d2); display: flex; align-items: center; justify-content: center; color: white; overflow: hidden;">
                        ${chat.user2.photo ? `<img src="/uploads/${chat.user2.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='30px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover; border-radius: 50%;">` : (chat.user2.gender === 'female' ? '👩' : '👨')}
                    </div>
                    <div>
                        <div style="font-weight: 600;">${chat.user2.name}</div>
                        <div style="font-size: 12px; color: #888;">${chat.user2.gender}</div>
                    </div>
                </div>
            </td>
            <td style="padding: 15px; text-align: center;">
                <span style="background: #e3f2fd; padding: 5px 12px; border-radius: 15px; font-size: 13px;">${chat.messageCount}</span>
            </td>
            <td style="padding: 15px; color: #888; font-size: 13px;">
                ${new Date(chat.lastMessage.time).toLocaleString()}
            </td>
            <td style="padding: 15px;">
                <a href="/admin/chats/${chat.user1.id}/${chat.user2.id}" class="btn btn-primary btn-sm">View Chat</a>
            </td>
        </tr>
    `).join('');

    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Chat Monitor - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none; font-size: 20px;">← Back to Admin</a>
            </div>
        </div>
    </nav>

    <div class="container" style="padding: 40px 20px;">
        <h2 style="margin-bottom: 30px;">💬 Chat Monitor</h2>

        <div style="background: white; border-radius: 12px; overflow: hidden; box-shadow: 0 2px 10px rgba(0,0,0,0.1);">
            <table style="width: 100%;">
                <thead>
                    <tr style="background: var(--secondary); color: white;">
                        <th style="padding: 15px; text-align: left;">User 1</th>
                        <th style="padding: 15px; text-align: left;">User 2</th>
                        <th style="padding: 15px; text-align: center;">Messages</th>
                        <th style="padding: 15px;">Last Activity</th>
                        <th style="padding: 15px;">Actions</th>
                    </tr>
                </thead>
                <tbody>
                    ${chatRows || '<tr><td colspan="5" style="padding: 40px; text-align: center; color: #888;">No chats yet</td></tr>'}
                </tbody>
            </table>
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

    const messagesHtml = chatMessages.map(m => {
        const isFromUser1 = m.from === user1Id;
        const sender = isFromUser1 ? user1 : user2;

        return `
            <div style="margin-bottom: 20px; display: flex; ${isFromUser1 ? 'justify-content: flex-start' : 'justify-content: flex-end'};">
                <div style="max-width: 70%;">
                    <div style="display: flex; align-items: center; gap: 10px; margin-bottom: 5px; ${isFromUser1 ? '' : 'flex-direction: row-reverse;'}">
                        <div style="width: 30px; height: 30px; border-radius: 50%; overflow: hidden; background: linear-gradient(135deg, ${isFromUser1 ? 'var(--secondary), #764ba2' : '#2196f3, #1976d2'});">
                            ${sender.photo ? `<img src="/uploads/${sender.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='30px'; this.innerHTML='👤';" style="width: 100%; height: 100%; object-fit: cover;">` : '<div style="display: flex; align-items: center; justify-content: center; height: 100%; color: white; font-size: 14px;">' + (sender.gender === 'female' ? '👩' : '👨') + '</div>'}
                        </div>
                        <span style="font-size: 12px; color: #888;">${sender.name}</span>
                    </div>
                    <div style="padding: 15px 20px; border-radius: 20px; background: ${isFromUser1 ? 'white' : 'linear-gradient(135deg, var(--primary), #c2185b)'}; color: ${isFromUser1 ? '#333' : 'white'}; box-shadow: 0 2px 10px rgba(0,0,0,0.1); ${m.censored ? 'border: 2px solid #ffc107;' : ''}">
                        ${m.censored ? '<div style="font-size: 11px; color: #ffc107; margin-bottom: 5px;">⚠️ CENSORED</div>' : ''}
                        ${m.type === 'photo' ? 
                            `<img src="/uploads/${m.photoFile}" alt="Photo" onerror="this.onerror=null; this.src=''; this.style.background='#f0f2f5'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.innerHTML='📷';" style="max-width: 200px; border-radius: 10px; cursor: pointer;" onclick="showLightbox('${m.photoFile}')">` :
                            `<p style="line-height: 1.6;">${m.text}</p>`
                        }
                        <div style="font-size: 11px; opacity: ${isFromUser1 ? '0.5' : '0.7'}; margin-top: 8px; text-align: right;">
                            ${new Date(m.time).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'})}
                            ${m.read ? ' ✓✓ Read' : ' ✓✓'}
                            ${m.cost > 0 ? ` • ${m.cost} coins` : ''}
                        </div>
                    </div>
                </div>
            </div>
        `;
    }).join('');

    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Chat: ${user1.name} & ${user2.name} - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin/chats" style="color: white; text-decoration: none; font-size: 20px;">← Back to Chats</a>
            </div>
        </div>
    </nav>

    <div class="container" style="padding: 40px 20px; max-width: 900px;">
        <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 30px;">
            <h2>💬 ${user1.name} ↔ ${user2.name}</h2>
            <span style="background: #e3f2fd; padding: 8px 16px; border-radius: 20px; font-size: 14px;">${chatMessages.length} messages</span>
        </div>

        <div style="background: #f8f9fa; padding: 30px; border-radius: 16px; min-height: 400px;">
            ${messagesHtml || '<p style="text-align: center; color: #888;">No messages in this conversation</p>'}
        </div>

        <div style="margin-top: 30px; display: flex; gap: 15px;">
            <a href="/admin/users/${user1.id}/view" class="btn btn-outline">View ${user1.name}</a>
            <a href="/admin/users/${user2.id}/view" class="btn btn-outline">View ${user2.name}</a>
        </div>
    </div>

    <script>
        function showLightbox(photo) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.9);display:flex;align-items:center;justify-content:center;z-index:3000;cursor:pointer;';
            overlay.innerHTML = '<img src="/uploads/' + photo + '" alt="📷" onerror="this.onerror=null; this.src=\'\'; this.style.background=\'#f0f2f5\'; this.style.display=\'flex\'; this.style.alignItems=\'center\'; this.style.justifyContent=\'center\'; this.innerHTML=\'📷\';" style="max-width:90%;max-height:90%;border-radius:10px;">';
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
    
    const notificationRows = adminNotifications.map(n => {
        const user = users.find(u => u.id === n.userId);
        return `
            <tr>
                <td style="padding: 15px;">
                    <div style="display: flex; align-items: center; gap: 10px;">
                        <div style="width: 40px; height: 40px; border-radius: 50%; background: linear-gradient(135deg, var(--secondary), #764ba2); display: flex; align-items: center; justify-content: center; color: white; overflow: hidden;">
                            ${user?.photo ? `<img src="/uploads/${user.photo}" alt="👤" onerror="this.src=''; this.alt='👤'; this.style.display='flex'; this.style.alignItems='center'; this.style.justifyContent='center'; this.style.fontSize='30px'; this.innerHTML='👤';" style="width: 100%; height: 100%; border-radius: 50%; object-fit: cover;">` : (user?.gender === 'female' ? '👩' : '👨')}
                        </div>
                        <div>
                            <div style="font-weight: 600;">${user?.name || 'Unknown'}</div>
                            <div style="font-size: 12px; color: #888;">${user?.email || ''}</div>
                        </div>
                    </div>
                </td>
                <td style="padding: 15px;">
                    <div style="font-weight: 600;">${n.title || 'Notification'}</div>
                    <div style="font-size: 13px; color: #666; max-width: 300px; overflow: hidden; text-overflow: ellipsis;">${n.text}</div>
                </td>
                <td style="padding: 15px;">
                    <span style="padding: 5px 12px; border-radius: 15px; font-size: 12px; font-weight: 600; background: ${n.read ? '#e8f5e9' : '#fff3cd'}; color: ${n.read ? '#2e7d32' : '#856404'};">
                        ${n.read ? '✓ Read' : '⏳ Unread'}
                    </span>
                </td>
                <td style="padding: 15px; color: #888; font-size: 13px;">
                    ${new Date(n.createdAt).toLocaleString()}
                </td>
            </tr>
        `;
    }).join('');
    
    res.send(`
<!DOCTYPE html>
<html>
<head>
    <title>Send Notifications - Admin</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar" style="background: #333;">
        <div class="container">
            <div class="nav-content">
                <a href="/admin" style="color: white; text-decoration: none; font-size: 20px;">← Back to Admin</a>
            </div>
        </div>
    </nav>
    
    <div class="container" style="padding: 40px 20px;">
        <div class="grid grid-2">
            <div class="card" style="padding: 30px;">
                <h2 style="margin-bottom: 25px;">📢 Send Notification</h2>
                
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
                            <option value="info">ℹ️ Info</option>
                            <option value="success">✅ Success</option>
                            <option value="warning">⚠️ Warning</option>
                            <option value="promo">🎁 Promotion</option>
                        </select>
                    </div>
                    
                    <button type="submit" class="btn btn-primary" style="width: 100%;">Send Notification</button>
                </form>
            </div>
            
            <div class="card" style="padding: 30px;">
                <h2 style="margin-bottom: 25px;">📨 Sent Notifications</h2>
                
                <div style="display: flex; gap: 10px; margin-bottom: 20px;">
                    <a href="/admin/notifications" class="btn btn-sm ${!filter ? 'btn-primary' : 'btn-outline'}">All</a>
                    <a href="/admin/notifications?filter=unread" class="btn btn-sm ${filter === 'unread' ? 'btn-primary' : 'btn-outline'}">Unread</a>
                </div>
                
                <div style="max-height: 400px; overflow-y: auto;">
                    <table style="width: 100%;">
                        <tbody>
                            ${notificationRows || '<tr><td style="padding: 20px; text-align: center; color: #888;">No notifications sent yet</td></tr>'}
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
<html>
<head>
    <title>Messages - FindYourMatch</title>
    <style>${globalStyles}</style>
</head>
<body>
    <nav class="navbar">
        <div class="container">
            <div class="nav-content">
                <a href="/dashboard" class="logo">
                    <img src="/logo.png" alt="FindYourMatch" onerror="this.style.display='none'">
                    <span>FindYourMatch</span>
                </a>
                <div style="display: flex; align-items: center; gap: 15px;">
                    <span style="background: ${unreadCount > 0 ? '#ff4444' : '#4caf50'}; color: white; padding: 8px 16px; border-radius: 20px; font-weight: 600;">
                        ${unreadCount} unread
                    </span>
                    <a href="/logout">Logout</a>
                </div>
            </div>
        </div>
    </nav>

    <div class="container" style="padding: 40px 20px; max-width: 800px;">
        <h2 style="margin-bottom: 30px;">💬 Your Messages</h2>
        ${inboxHTML}
    </div>
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