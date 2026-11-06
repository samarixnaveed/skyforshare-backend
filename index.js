/**
 * SkyForShare Server
 * Express + Socket.IO backend for real-time text & file sharing.
 * Supports isolated groups (rooms) with optional PIN. No upload size limits.
 */
const express = require("express");
const http = require("http");
const path = require("path");
const fs = require("fs");
const cors = require("cors");
const multer = require("multer");
const { Server } = require("socket.io");
const crypto = require("crypto");

const PORT = process.env.PORT || 5050;
const UPLOAD_DIR = path.join(__dirname, "uploads");
const DATA_FILE = path.join(__dirname, "data.json");
const PUBLIC_ROOM = "public";
const MAX_GROUPS = 30; // max concurrent temporary groups
const TTL_OPTIONS = [15, 30, 45]; // auto-delete timers (minutes)
const DEFAULT_TTL = 30;

if (!fs.existsSync(UPLOAD_DIR)) fs.mkdirSync(UPLOAD_DIR, { recursive: true });

const sha256 = (s) => crypto.createHash("sha256").update(String(s)).digest("hex");

// ---------- Persistent store (rooms) ----------
const emptyRoom = () => ({
  text: "",
  textUpdatedAt: null,
  files: [],
  tokens: [],
  displayName: "",
  expiresAt: null, // null = never (public room only)
  createdAt: new Date().toISOString(),
  lastActivity: new Date().toISOString(),
});

let store = { rooms: { [PUBLIC_ROOM]: emptyRoom() } };
try {
  if (fs.existsSync(DATA_FILE)) {
    const raw = JSON.parse(fs.readFileSync(DATA_FILE, "utf8"));
    if (raw.rooms) {
      store = raw;
    } else {
      // Migrate old single-room format
      store.rooms = {
        [PUBLIC_ROOM]: {
          ...emptyRoom(),
          text: raw.text || "",
          textUpdatedAt: raw.textUpdatedAt || null,
          files: raw.files || [],
        },
      };
    }
    if (!store.rooms[PUBLIC_ROOM]) store.rooms[PUBLIC_ROOM] = emptyRoom();
    for (const [name, room] of Object.entries(store.rooms)) {
      room.files = (room.files || []).filter(
        (f) =>
          f &&
          typeof f.storedName === "string" &&
          !f.storedName.includes("/") &&
          !f.storedName.includes("..") &&
          fs.existsSync(path.join(UPLOAD_DIR, f.storedName))
      );
      room.tokens = Array.isArray(room.tokens) ? room.tokens : [];
      room.lastActivity = room.lastActivity || room.createdAt || new Date().toISOString();
      // Drop the legacy PIN system — invitation codes are the secret now
      delete room.pin;
      delete room.pinHash;
      room.displayName = room.displayName || name;
      // Legacy groups without an expiry get 45 minutes from this boot
      if (name !== PUBLIC_ROOM && !room.expiresAt)
        room.expiresAt = new Date(Date.now() + 45 * 60000).toISOString();
    }
  }
} catch (e) {
  console.error("⚠ data.json unreadable, starting fresh:", e.message);
}

// Remove orphan files on disk that no room references (from pruned rooms etc.)
try {
  const referenced = new Set();
  for (const room of Object.values(store.rooms))
    for (const f of room.files) referenced.add(f.storedName);
  for (const entry of fs.readdirSync(UPLOAD_DIR)) {
    if (!referenced.has(entry)) {
      fs.unlink(path.join(UPLOAD_DIR, entry), () => {});
    }
  }
} catch (_) {}

// Atomic, debounced persistence (tmp file + rename, so data.json can't corrupt)
let saveTimer = null;
let bootMigrated = true; // persist migrations (e.g. PIN hashing) right after boot
function writeStoreSync() {
  try {
    const tmp = DATA_FILE + ".tmp";
    fs.writeFileSync(tmp, JSON.stringify(store, null, 2));
    fs.renameSync(tmp, DATA_FILE);
  } catch (e) {
    console.error("⚠ persist failed:", e.message);
  }
}
function persist() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(writeStoreSync, 150);
}

// Flush pending writes on shutdown so the last change is never lost
for (const sig of ["SIGINT", "SIGTERM"]) {
  process.on(sig, () => {
    clearTimeout(saveTimer);
    writeStoreSync();
    process.exit(0);
  });
}
process.on("uncaughtException", (e) => {
  console.error("Uncaught:", e);
  writeStoreSync();
});
process.on("unhandledRejection", (e) => console.error("Unhandled:", e));

// ---------- Room helpers ----------
function normalizeRoomName(name) {
  if (typeof name !== "string") return null;
  const slug = name
    .trim()
    .toLowerCase()
    .replace(/\s+/g, "-")
    .replace(/[^a-z0-9\-_]/g, "")
    .slice(0, 40);
  return /^[a-z0-9\-_]{2,40}$/.test(slug) ? slug : null;
}

function getRoom(name) {
  return store.rooms[name] || null;
}

function touch(room) {
  room.lastActivity = new Date().toISOString();
}

function isExpired(room) {
  return !!(room.expiresAt && Date.parse(room.expiresAt) <= Date.now());
}

// A request is authorized for a room if it's the public room,
// or it carries a token that was issued for that room.
function isAuthorized(roomName, token) {
  if (roomName === PUBLIC_ROOM) return true;
  const room = getRoom(roomName);
  if (!room || isExpired(room)) return false;
  return !!(typeof token === "string" && token && room.tokens.includes(token));
}

function roomAuth(req, res, next) {
  const roomName =
    normalizeRoomName(req.query.room || PUBLIC_ROOM) || PUBLIC_ROOM;
  const token = String(req.query.token || req.headers["x-room-token"] || "");
  const room = getRoom(roomName);
  if (!room || (roomName !== PUBLIC_ROOM && isExpired(room)))
    return res.status(404).json({ error: "Group not found or expired" });
  if (!isAuthorized(roomName, token))
    return res.status(403).json({ error: "Not a member of this group" });
  req.roomName = roomName;
  req.room = room;
  next();
}

// ---------- Invitation codes & generated names ----------
// Unambiguous characters only (no 0/o, 1/l/i)
const CODE_CHARS = "abcdefghjkmnpqrstuvwxyz23456789";
function genCode() {
  let code;
  do {
    code = Array.from(crypto.randomBytes(6))
      .map((b) => CODE_CHARS[b % CODE_CHARS.length])
      .join("");
  } while (store.rooms[code]);
  return code;
}

const NAME_ADJ = ["swift", "golden", "silent", "bright", "royal", "cosmic", "rapid", "lucky", "bold", "amber", "silver", "crimson"];
const NAME_NOUN = ["falcon", "tiger", "comet", "wave", "orbit", "pearl", "summit", "ember", "breeze", "lion", "harbor", "peak"];
function genDisplayName() {
  const pick = (arr) => arr[crypto.randomInt(arr.length)];
  return `${pick(NAME_ADJ)}-${pick(NAME_NOUN)}-${crypto.randomInt(10, 100)}`;
}

// Extract a 6-char invite code from raw input (bare code or a pasted invite URL)
function parseInviteCode(input) {
  if (typeof input !== "string") return null;
  const m = input.toLowerCase().match(/join=([a-z0-9]{6})/);
  const code = (m ? m[1] : input.toLowerCase().replace(/[^a-z0-9]/g, "")).slice(0, 6);
  return code.length === 6 ? code : null;
}

function activeGroupCount() {
  return Object.entries(store.rooms).filter(
    ([name, room]) => name !== PUBLIC_ROOM && !isExpired(room)
  ).length;
}

function deleteRoom(name, room) {
  for (const f of room.files)
    fs.unlink(path.join(UPLOAD_DIR, f.storedName), () => {});
  delete store.rooms[name];
  io.to(`room:${name}`).emit("room:expired", { room: name });
  io.in(`room:${name}`).socketsLeave(`room:${name}`);
}

// Auto-delete expired groups (checked every 30s; files removed from disk too)
setInterval(() => {
  let changed = false;
  for (const [name, room] of Object.entries(store.rooms)) {
    if (name === PUBLIC_ROOM) continue;
    if (isExpired(room)) {
      deleteRoom(name, room);
      changed = true;
    }
  }
  if (changed) persist();
}, 30 * 1000).unref();

// ---------- Network restriction (LAN-only) ----------
// Only devices on the private/local network may connect. Optionally set
// ALLOWED_IPS="192.168.100.119,192.168.100.50" to lock it to specific devices.
// PUBLIC_MODE=true disables the LAN-only restriction for internet hosting
// (Render/VPS). Optionally set MAX_UPLOAD_MB to cap upload size in public.
const PUBLIC_MODE = process.env.PUBLIC_MODE === "true";
const MAX_UPLOAD_MB = Number(process.env.MAX_UPLOAD_MB || 0); // 0 = unlimited

const ALLOWED_IPS = (process.env.ALLOWED_IPS || "")
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);

function normalizeIp(ip) {
  if (!ip) return "";
  return ip.replace(/^::ffff:/, ""); // IPv4-mapped IPv6
}

function isPrivateIp(raw) {
  const ip = normalizeIp(raw);
  return (
    ip === "::1" ||
    ip === "localhost" ||
    ip.startsWith("127.") ||
    ip.startsWith("10.") ||
    ip.startsWith("192.168.") ||
    /^172\.(1[6-9]|2\d|3[01])\./.test(ip) ||
    ip.toLowerCase().startsWith("fe80:") // IPv6 link-local
  );
}

function isAllowedIp(raw) {
  const ip = normalizeIp(raw);
  if (!isPrivateIp(ip)) return false; // never allow public internet
  if (ALLOWED_IPS.length === 0) return true; // whole LAN allowed
  return ip === "::1" || ip.startsWith("127.") || ALLOWED_IPS.includes(ip);
}

function isAllowedOrigin(origin) {
  if (PUBLIC_MODE) return true;
  if (!origin) return true; // same-origin / curl
  try {
    return isPrivateIp(new URL(origin).hostname);
  } catch (_) {
    return false;
  }
}

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: {
    origin: (origin, cb) =>
      isAllowedOrigin(origin) ? cb(null, true) : cb(new Error("Origin blocked")),
    methods: ["GET", "POST", "DELETE"],
  },
  maxHttpBufferSize: 1e9,
});

if (!PUBLIC_MODE) {
  app.use((req, res, next) => {
    if (!isAllowedIp(req.socket.remoteAddress)) {
      console.warn(`⛔ Blocked request from ${req.socket.remoteAddress}`);
      return res
        .status(403)
        .json({ error: "Access restricted to local network" });
    }
    next();
  });

  io.use((socket, next) => {
    if (!isAllowedIp(socket.handshake.address)) {
      console.warn(`⛔ Blocked socket from ${socket.handshake.address}`);
      return next(new Error("Access restricted to local network"));
    }
    next();
  });
} else {
  // Behind Render/other proxies the real client IP is in X-Forwarded-For
  app.set("trust proxy", 1);

  // Light per-IP rate limit so one visitor can't hammer a free instance
  const hits = new Map();
  app.use("/api", (req, res, next) => {
    const ip = req.ip || "unknown";
    const now = Date.now();
    let h = hits.get(ip);
    if (!h || now > h.reset) {
      h = { n: 0, reset: now + 60000 };
      hits.set(ip, h);
    }
    if (++h.n > 300)
      return res.status(429).json({ error: "Too many requests — slow down" });
    next();
  });
  setInterval(() => {
    const now = Date.now();
    for (const [k, v] of hits) if (now > v.reset) hits.delete(k);
  }, 5 * 60000).unref();
}

app.use(
  cors({
    origin: (origin, cb) =>
      isAllowedOrigin(origin) ? cb(null, true) : cb(new Error("Origin blocked")),
  })
);
app.use(express.json({ limit: "1024mb" }));

// Multer storage — original name preserved, unique stored name, NO size limit
const storage = multer.diskStorage({
  destination: (_req, _file, cb) => cb(null, UPLOAD_DIR),
  filename: (_req, file, cb) => {
    const id = crypto.randomBytes(8).toString("hex");
    // keep only safe characters in the extension
    const safeExt = path
      .extname(file.originalname || "")
      .replace(/[^a-zA-Z0-9.]/g, "")
      .slice(0, 20);
    cb(null, `${Date.now()}-${id}${safeExt}`);
  },
});
// Unlimited by default; MAX_UPLOAD_MB caps per-file size (for free hosting)
const upload = multer({
  storage,
  limits: MAX_UPLOAD_MB > 0 ? { fileSize: MAX_UPLOAD_MB * 1024 * 1024 } : {},
});

const fixName = (name) => {
  try {
    const fixed = Buffer.from(name, "latin1").toString("utf8");
    return fixed && fixed !== "�" ? fixed : name;
  } catch (_) {
    return name || "file";
  }
};

const newToken = () => crypto.randomBytes(16).toString("hex");

function roomPresence(roomName) {
  return io.sockets.adapter.rooms.get(`room:${roomName}`)?.size || 0;
}

function emitPresence(roomName) {
  io.to(`room:${roomName}`).emit("presence", {
    room: roomName,
    online: roomPresence(roomName),
  });
}

// ---------- Routes ----------
app.get("/api/health", (_req, res) =>
  res.json({ ok: true, uptime: process.uptime() })
);

// --- Groups ---
const groupInfo = (code, room, token) => ({
  ok: true,
  room: code,
  code,
  token,
  displayName: room.displayName,
  expiresAt: room.expiresAt,
});

// Create: no name needed — the server generates an invitation code and a
// friendly (editable) name. Caller picks the auto-delete timer: 15/30/45 min.
app.post("/api/groups", (req, res) => {
  const body = req.body || {};
  if (activeGroupCount() >= MAX_GROUPS)
    return res.status(429).json({
      error: `Server is full — max ${MAX_GROUPS} active groups. Try again when one expires.`,
    });

  const ttl = TTL_OPTIONS.includes(Number(body.ttl))
    ? Number(body.ttl)
    : DEFAULT_TTL;
  const code = genCode();
  const token = newToken();
  store.rooms[code] = {
    ...emptyRoom(),
    displayName: genDisplayName(),
    expiresAt: new Date(Date.now() + ttl * 60000).toISOString(),
    tokens: [token],
  };
  persist();
  res.json({ ...groupInfo(code, store.rooms[code], token), ttl });
});

// Join with just the invitation code (bare code or a pasted invite link)
app.post("/api/groups/join", (req, res) => {
  const body = req.body || {};
  const code = parseInviteCode(body.code || body.name);
  if (!code)
    return res.status(400).json({ error: "Invalid invitation code" });
  const room = getRoom(code);
  if (!room || code === PUBLIC_ROOM || isExpired(room))
    return res
      .status(404)
      .json({ error: "Group not found or expired — check the code" });

  const token = newToken();
  room.tokens.push(token);
  if (room.tokens.length > 200) room.tokens = room.tokens.slice(-200);
  touch(room);
  persist();
  res.json(groupInfo(code, room, token));
});

// Rename: any member can edit the generated name
app.post("/api/groups/rename", roomAuth, (req, res) => {
  if (req.roomName === PUBLIC_ROOM)
    return res.status(400).json({ error: "Public space cannot be renamed" });
  const name = String((req.body || {}).name || "").trim().slice(0, 40);
  if (!name) return res.status(400).json({ error: "Name cannot be empty" });
  req.room.displayName = name;
  touch(req.room);
  persist();
  io.to(`room:${req.roomName}`).emit("room:meta", {
    room: req.roomName,
    displayName: name,
    expiresAt: req.room.expiresAt,
  });
  res.json({ ok: true, displayName: name });
});

// --- Text (per room) ---
app.get("/api/text", roomAuth, (req, res) =>
  res.json({ text: req.room.text, updatedAt: req.room.textUpdatedAt })
);

app.post("/api/text", roomAuth, (req, res) => {
  const body = req.body || {};
  req.room.text = typeof body.text === "string" ? body.text : "";
  req.room.textUpdatedAt = new Date().toISOString();
  touch(req.room);
  persist();
  io.to(`room:${req.roomName}`).emit("text:update", {
    room: req.roomName,
    text: req.room.text,
    updatedAt: req.room.textUpdatedAt,
  });
  res.json({ ok: true, updatedAt: req.room.textUpdatedAt });
});

// --- Files (per room) ---
app.get("/api/files", roomAuth, (req, res) =>
  res.json({ files: req.room.files })
);

app.post("/api/upload", roomAuth, upload.array("files"), (req, res) => {
  const added = (req.files || []).map((f) => ({
    id: crypto.randomBytes(8).toString("hex"),
    name: fixName(f.originalname) || "file",
    storedName: f.filename,
    size: f.size,
    type: f.mimetype || "application/octet-stream",
    room: req.roomName,
    uploadedAt: new Date().toISOString(),
  }));
  if (!added.length)
    return res.status(400).json({ error: "No files received" });
  req.room.files.unshift(...added);
  touch(req.room);
  persist();
  io.to(`room:${req.roomName}`).emit("files:update", {
    room: req.roomName,
    files: req.room.files,
  });
  res.json({ ok: true, files: added });
});

// Find a file anywhere + the room it belongs to
function findFile(id) {
  for (const [roomName, room] of Object.entries(store.rooms)) {
    const file = room.files.find((f) => f.id === id);
    if (file) return { file, roomName, room };
  }
  return null;
}

function fileAuth(req, res) {
  const hit = findFile(req.params.id);
  if (!hit) {
    res.status(404).json({ error: "Not found" });
    return null;
  }
  const token = String(req.query.token || req.headers["x-room-token"] || "");
  if (!isAuthorized(hit.roomName, token)) {
    res.status(403).json({ error: "Not a member of this group" });
    return null;
  }
  return hit;
}

// If a file record exists but the bytes vanished from disk, drop the record
function dropMissingFile(hit) {
  hit.room.files = hit.room.files.filter((f) => f.id !== hit.file.id);
  persist();
  io.to(`room:${hit.roomName}`).emit("files:update", {
    room: hit.roomName,
    files: hit.room.files,
  });
}

app.get("/api/files/:id/raw", (req, res) => {
  const hit = fileAuth(req, res);
  if (!hit) return;
  res.setHeader("Content-Type", hit.file.type || "application/octet-stream");
  res.sendFile(path.join(UPLOAD_DIR, hit.file.storedName), (err) => {
    if (err && !res.headersSent) {
      dropMissingFile(hit);
      res.status(410).json({ error: "File no longer exists" });
    }
  });
});

app.get("/api/files/:id/download", (req, res) => {
  const hit = fileAuth(req, res);
  if (!hit) return;
  res.download(
    path.join(UPLOAD_DIR, hit.file.storedName),
    hit.file.name,
    (err) => {
      if (err && !res.headersSent) {
        dropMissingFile(hit);
        res.status(410).json({ error: "File no longer exists" });
      }
    }
  );
});

app.delete("/api/files/:id", (req, res) => {
  const hit = fileAuth(req, res);
  if (!hit) return;
  fs.unlink(path.join(UPLOAD_DIR, hit.file.storedName), () => {});
  hit.room.files = hit.room.files.filter((f) => f.id !== req.params.id);
  touch(hit.room);
  persist();
  io.to(`room:${hit.roomName}`).emit("files:update", {
    room: hit.roomName,
    files: hit.room.files,
  });
  res.json({ ok: true });
});

app.delete("/api/files", roomAuth, (req, res) => {
  for (const f of req.room.files)
    fs.unlink(path.join(UPLOAD_DIR, f.storedName), () => {});
  req.room.files = [];
  touch(req.room);
  persist();
  io.to(`room:${req.roomName}`).emit("files:update", {
    room: req.roomName,
    files: [],
  });
  res.json({ ok: true });
});

// JSON 404 for unknown API routes (instead of HTML)
app.use("/api", (_req, res) => res.status(404).json({ error: "Not found" }));

// Central error handler: malformed JSON, multer failures, blocked origins —
// always answer JSON, never crash, never leak a stack trace.
app.use((err, _req, res, _next) => {
  if (res.headersSent) return;
  if (err.message === "Origin blocked")
    return res.status(403).json({ error: "Origin not allowed" });
  if (err.type === "entity.parse.failed" || err.type === "entity.too.large")
    return res.status(400).json({ error: "Invalid request body" });
  if (err instanceof multer.MulterError)
    return res.status(400).json({ error: `Upload error: ${err.code}` });
  console.error("Request error:", err.message);
  res.status(500).json({ error: "Server error" });
});

// ---------- Sockets ----------
io.on("connection", (socket) => {
  let current = null; // room this socket has joined

  socket.on("room:join", (payload) => {
    const { room, token } = payload || {};
    const roomName = normalizeRoomName(room || PUBLIC_ROOM) || PUBLIC_ROOM;
    if (!getRoom(roomName) || !isAuthorized(roomName, token || "")) {
      socket.emit("room:error", { error: "Cannot join group" });
      return;
    }
    if (current === roomName) return; // already there — avoid presence churn
    if (current) {
      socket.leave(`room:${current}`);
      emitPresence(current);
    }
    current = roomName;
    socket.join(`room:${roomName}`);
    const r = getRoom(roomName);
    touch(r);
    socket.emit("room:joined", {
      room: roomName,
      displayName: r.displayName,
      expiresAt: r.expiresAt,
    });
    socket.emit("text:update", {
      room: roomName,
      text: r.text,
      updatedAt: r.textUpdatedAt,
    });
    socket.emit("files:update", { room: roomName, files: r.files });
    emitPresence(roomName);
  });

  // Live typing relay, scoped to the sender's room
  socket.on("text:typing", (payload) => {
    const { room, token, text } = payload || {};
    const roomName = normalizeRoomName(room || PUBLIC_ROOM) || PUBLIC_ROOM;
    const r = getRoom(roomName);
    if (!r || !isAuthorized(roomName, token || "")) return;
    if (typeof text !== "string") return;
    r.text = text;
    r.textUpdatedAt = new Date().toISOString();
    touch(r);
    persist();
    socket.to(`room:${roomName}`).emit("text:update", {
      room: roomName,
      text: r.text,
      updatedAt: r.textUpdatedAt,
    });
  });

  socket.on("disconnect", () => {
    if (current) emitPresence(current);
  });
});

server.listen(PORT, () => {
  if (bootMigrated) writeStoreSync(); // flush load-time migrations to disk
  console.log(`⚡ SkyForShare server running on http://localhost:${PORT}`);
});
