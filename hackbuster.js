// =========================================================
//  HACKBUSTER — UNIFIED GAME LOGIC
//  Screens: title → breach (arena) → run-end → compiler
// =========================================================

// =========================================================
// SHARED SAVE SYSTEM
// =========================================================
const HB_SAVE_KEY  = 'hb_save';
const HB_SAVE_VER  = 2;

function hbLoadRaw() {
    try {
        const raw = localStorage.getItem(HB_SAVE_KEY);
        if (!raw) return null;
        const p = JSON.parse(raw);
        if (p.version !== HB_SAVE_VER) return null;
        return p;
    } catch (_) { return null; }
}

function hbSaveRaw(payload) {
    try {
        localStorage.setItem(HB_SAVE_KEY, JSON.stringify({ ...payload, version: HB_SAVE_VER, savedAt: Date.now() }));
    } catch (e) { console.warn('Save failed:', e); }
}

// =========================================================
// SCREEN MANAGER
// =========================================================
function showScreen(id) {
    document.querySelectorAll('.screen').forEach(s => s.classList.remove('active'));
    document.getElementById('screen-' + id).classList.add('active');
}

// =========================================================
// ─── BREACH ARENA ────────────────────────────────────────
// =========================================================

// DOM refs (populated in initBreach)
let nb_canvas, nb_ctx, fragDisplay, levelDisplay, damageFlash, progressFill, levelupToast;

// Session state
let nb_gameState     = 'idle';
let playerHealth     = 0;
let playerShield     = 0;   // absorbs damage before HP
let sessionFragments = 0;
let pipelineStats    = null; // set at breach start via computePipelineStats()
let sessionNodes     = 0;
let sessionXp        = 0;
let sessionTime      = 0;
let bossProgress     = 0;
let spawnAccumulator = 0;
let lastTime         = 0;
let prevLevel        = 1;

// Persistent breach state (banked between runs)
let savedFragments = 0;
let savedData      = 0;
let savedXp        = 0;

// Script loot drops collected this run: { defId: { lineIdx: count } }
let sessionScriptFrags = {};

let nb_nodes = [];
let nb_frags = [];
let nb_loopRunning = false;

const nb_mouse = { x: 200, y: 200, radius: 35 };
let nb_prevW = 0, nb_prevH = 0;
let nb_levelupTimer = null;

// ── Constants ──────────────────────────────────────────────
const MAX_HEALTH       = 34.0;
const XP_TO_LEVEL      = 500;
const BOSS_THRESHOLD   = 100;
const HACK_TIME_MS     = 1500;
const HACK_DAMAGE      = 35;
const IDLE_DEGEN_BASE  = 0.05;
const IDLE_DEGEN_SCALE = 0.001;

const NB_NODE_TYPES = {
    basic:  { size: 30,  hp: 70,  frags: 1,  thorns: 0.5, prog: 5  },
    medium: { size: 45,  hp: 140, frags: 3,  thorns: 1.5, prog: 15 },
    boss:   { size: 180, hp: 800, frags: 15, thorns: 4.5, prog: 0  },
    moon:   { size: 18,  hp: 35,  frags: 1,  thorns: 0.2, prog: 2  },
};
const NB_NODE_COLORS = {
    basic: '#ff007f', medium: '#00e5ff', boss: '#d500f9', moon: '#ff007f',
};

// ── Script loot drop table (built from NODE_DEFS after it's defined) ──
// Populated at bottom of file after NODE_DEFS is declared.
let SCRIPT_DROP_TABLE = [];
const SCRIPT_DROP_CHANCE = 0.18; // 18% per non-moon kill

function nb_formatTime(s) {
    const m = Math.floor(s / 60), ss = Math.floor(s % 60);
    return `${String(m).padStart(2,'0')}:${String(ss).padStart(2,'0')}`;
}
function getLevel(xp) { return Math.floor(xp / XP_TO_LEVEL) + 1; }

function nb_triggerDamageFlash() {
    if (!damageFlash) return;
    damageFlash.style.opacity = '1';
    setTimeout(() => { damageFlash.style.opacity = '0'; }, 100);
}
function nb_triggerLevelUp() {
    if (!levelupToast) return;
    levelupToast.style.opacity = '1';
    clearTimeout(nb_levelupTimer);
    nb_levelupTimer = setTimeout(() => { levelupToast.style.opacity = '0'; }, 1200);
}

// ── Node class ─────────────────────────────────────────────
class NbNode {
    constructor(typeOverride = null, isMoon = false) {
        if (typeOverride)   this.type = typeOverride;
        else if (isMoon)    this.type = 'moon';
        else                this.type = Math.random() > 0.65 ? 'medium' : 'basic';

        const cfg = NB_NODE_TYPES[this.type];
        this.size       = cfg.size;
        this.health     = cfg.hp;
        this.maxHealth  = cfg.hp;
        this.color      = NB_NODE_COLORS[this.type];
        this.dropAmount = cfg.frags;
        this.baseThorns = cfg.thorns;
        this.progValue  = cfg.prog;
        this.angle      = Math.random() * Math.PI * 2;
        this.rotSpeed   = (Math.random() - 0.5) * 0.02;
        this.parent     = null;
        this.orbitRadius = 0;
        this.orbitSpeed  = 0;
        this.orbitAngle  = 0;
        this.hackTimer   = 0;
        this.flash       = 0;

        if (isMoon) {
            this.x = -1000; this.y = -1000;
        } else {
            const margin = this.size + 20;
            const edge   = Math.floor(Math.random() * 4);
            const cw = nb_canvas.width, ch = nb_canvas.height;
            if (edge === 0)      { this.x = Math.random() * cw;  this.y = -margin; }
            else if (edge === 1) { this.x = cw + margin;          this.y = Math.random() * ch; }
            else if (edge === 2) { this.x = Math.random() * cw;  this.y = ch + margin; }
            else                 { this.x = -margin;              this.y = Math.random() * ch; }
        }

        const tx = nb_canvas.width  / 2 + (Math.random() - 0.5) * nb_canvas.width  * 0.6;
        const ty = nb_canvas.height / 2 + (Math.random() - 0.5) * nb_canvas.height * 0.6;
        const dir = Math.atan2(ty - this.y, tx - this.x);
        const sm  = this.type === 'boss' ? 0.2 : 1;
        const spd = (40 + Math.random() * 40) * sm;
        this.vx = Math.cos(dir) * spd;
        this.vy = Math.sin(dir) * spd;
    }

    update(dt) {
        if (this.parent !== null) {
            this.orbitAngle += this.orbitSpeed * dt;
            this.x = this.parent.x + Math.cos(this.orbitAngle) * this.orbitRadius;
            this.y = this.parent.y + Math.sin(this.orbitAngle) * this.orbitRadius;
            this.vx = this.parent.vx;
            this.vy = this.parent.vy;
        } else {
            this.x += this.vx * dt;
            this.y += this.vy * dt;
            const bound = 300;
            if (this.x < -bound || this.x > nb_canvas.width  + bound) this.vx *= -1;
            if (this.y < -bound || this.y > nb_canvas.height + bound) this.vy *= -1;
        }
        this.angle += this.rotSpeed;
        if (this.parent === null) this.orbitAngle += dt * 2;
        if (this.flash > 0) this.flash -= dt * 60;
    }

    draw(isHovered) {
        const ctx = nb_ctx;
        const flashing = this.flash > 0;
        ctx.save();
        ctx.translate(this.x, this.y);
        ctx.rotate(this.angle);

        ctx.shadowBlur  = isHovered ? (this.type === 'boss' ? 50 : 30) : 15;
        ctx.shadowColor = this.color;
        ctx.fillStyle   = flashing ? '#ffffff' : this.color;
        ctx.globalAlpha = 0.3 + (this.health / this.maxHealth) * 0.5;
        ctx.beginPath();
        for (let i = 0; i < 6; i++) {
            const a = (Math.PI / 3) * i;
            ctx.lineTo((this.size / 2) * Math.cos(a), (this.size / 2) * Math.sin(a));
        }
        ctx.closePath(); ctx.fill();

        ctx.strokeStyle = flashing ? '#ffffff' : '#fff';
        ctx.lineWidth   = this.type === 'boss' ? 3 : 1.5;
        ctx.globalAlpha = 0.8;
        ctx.stroke();

        ctx.beginPath();
        ctx.moveTo(0,               this.size / 4);
        ctx.lineTo(-this.size / 4.5, -this.size / 5);
        ctx.lineTo( this.size / 4.5, -this.size / 5);
        ctx.closePath(); ctx.stroke();

        if (this.parent === null && this.type !== 'moon') {
            ctx.globalAlpha = 1.0;
            const orbCount = this.type === 'boss' ? 8 : 3;
            const orbDist  = this.size * 0.7;
            for (let i = 0; i < orbCount; i++) {
                const a = (Math.PI * 2 / orbCount) * i + this.orbitAngle;
                ctx.beginPath();
                ctx.arc(orbDist * Math.cos(a), orbDist * Math.sin(a), this.type === 'boss' ? 6 : 3, 0, Math.PI * 2);
                ctx.fill();
            }
        }

        if (isHovered) {
            ctx.shadowBlur  = 0;
            ctx.strokeStyle = '#00e5ff';
            ctx.lineWidth   = this.type === 'boss' ? 4 : 2;
            const off = this.size * 0.85, len = this.type === 'boss' ? 30 : 8;
            ctx.beginPath();
            ctx.moveTo(-off, -off + len); ctx.lineTo(-off, -off); ctx.lineTo(-off + len, -off);
            ctx.moveTo( off - len, -off); ctx.lineTo( off, -off); ctx.lineTo( off, -off + len);
            ctx.moveTo( off,  off - len); ctx.lineTo( off,  off); ctx.lineTo( off - len,  off);
            ctx.moveTo(-off + len,  off); ctx.lineTo(-off,  off); ctx.lineTo(-off,  off - len);
            ctx.stroke();
        }
        ctx.restore();

        if (this.health < this.maxHealth || isHovered) {
            const barW = this.size * 0.8, barH = this.type === 'boss' ? 8 : 4;
            const yOff = -this.size / 1.5 - (this.type === 'boss' ? 25 : 12);
            const pct  = Math.max(0, this.health / this.maxHealth);
            ctx.save();
            ctx.translate(this.x, this.y);
            ctx.shadowBlur = 0;
            ctx.fillStyle  = 'rgba(255,0,127,0.2)';
            ctx.fillRect(-barW / 2, yOff, barW, barH);
            ctx.fillStyle = this.color;
            ctx.fillRect(-barW / 2, yOff, barW * pct, barH);
            ctx.restore();
        }
    }
}

// ── Fragment pickup class ──────────────────────────────────
class NbFragment {
    constructor(x, y) {
        this.x = x; this.y = y;
        this.vx = (Math.random() - 0.5) * 600;
        this.vy = (Math.random() - 0.5) * 600;
        this.size = Math.random() * 4 + 6;
        this.life = 0; this.rot = Math.random() * Math.PI;
        this.homing = false;
        const rect = fragDisplay.getBoundingClientRect();
        this.targetX = rect.left + rect.width  / 2;
        this.targetY = rect.top  + rect.height / 2;
    }
    update(dt) {
        this.life += dt; this.rot += dt * 2;
        if (!this.homing) {
            this.x += this.vx * dt; this.y += this.vy * dt;
            this.vx *= 0.88; this.vy *= 0.88;
            if (this.life > 0.4) this.homing = true;
        } else {
            const dx = this.targetX - this.x, dy = this.targetY - this.y;
            const d  = Math.hypot(dx, dy);
            if (d < 15) return true;
            const spd = 1200 * dt;
            this.x += (dx / d) * spd; this.y += (dy / d) * spd;
        }
        return false;
    }
    draw() {
        const ctx = nb_ctx;
        ctx.save();
        ctx.translate(this.x, this.y); ctx.rotate(this.rot);
        ctx.fillStyle = '#00e5ff'; ctx.shadowBlur = 10; ctx.shadowColor = '#00e5ff';
        ctx.beginPath();
        for (let i = 0; i < 6; i++) {
            const a = (Math.PI / 3) * i;
            ctx.lineTo((this.size / 2) * Math.cos(a), (this.size / 2) * Math.sin(a));
        }
        ctx.closePath(); ctx.fill();
        ctx.restore();
    }
}

// ── Script loot drops (DOM overlay) ───────────────────────
let activeLootDrops = []; // { el, x, y, defId, lineIdx, canvas }

function spawnScriptLootDrop(x, y) {
    if (SCRIPT_DROP_TABLE.length === 0) return;

    // Weighted random pick
    const totalW = SCRIPT_DROP_TABLE.reduce((s, e) => s + e.weight, 0);
    let r = Math.random() * totalW;
    let entry = SCRIPT_DROP_TABLE[SCRIPT_DROP_TABLE.length - 1];
    for (const e of SCRIPT_DROP_TABLE) { r -= e.weight; if (r <= 0) { entry = e; break; } }

    const def   = NODE_DEFS[entry.defId];
    const label = `${def.icon} ${def.title.replace('()', '')} L${entry.lineIdx + 1}`;

    // Drift upward from kill position
    const driftX = x + (Math.random() - 0.5) * 60;
    const driftY = y - 30 - Math.random() * 40;

    const breachEl = document.getElementById('screen-breach');
    const el = document.createElement('div');
    el.className = 'script-loot-drop';
    el.style.left = driftX + 'px';
    el.style.top  = driftY + 'px';

    // Build DOM children without innerHTML stomping
    const ring = document.createElement('div');
    ring.className = 'loot-collect-ring';

    // Gold hexagon dot (small — pickup target is the CSS dot, not the ring)
    const dot = document.createElement('div');
    dot.className = 'loot-hex-dot';

    const lbl = document.createElement('div');
    lbl.className = 'loot-label';
    lbl.textContent = label;

    el.appendChild(ring);
    el.appendChild(dot);
    el.appendChild(lbl);

    breachEl.appendChild(el);

    // Auto-expire after 8s if not collected — bank the frag so player never loses it
    const expireTimer = setTimeout(() => {
        el.classList.add('loot-expiring');
        setTimeout(() => {
            el.remove();
            const idx = activeLootDrops.findIndex(d => d.el === el);
            if (idx > -1) {
                const drop = activeLootDrops[idx];
                // Bank silently — player earned it even if they didn't touch it
                if (!sessionScriptFrags[drop.defId]) sessionScriptFrags[drop.defId] = {};
                sessionScriptFrags[drop.defId][drop.lineIdx] = (sessionScriptFrags[drop.defId][drop.lineIdx] || 0) + 1;
                activeLootDrops.splice(idx, 1);
            }
        }, 600);
    }, 8000);

    activeLootDrops.push({ el, x: driftX, y: driftY, defId: entry.defId, lineIdx: entry.lineIdx, expireTimer });
}

function checkLootCollection() {
    const mx = nb_mouse.x, my = nb_mouse.y;
    for (let i = activeLootDrops.length - 1; i >= 0; i--) {
        const drop = activeLootDrops[i];
        const dist = Math.hypot(drop.x - mx, drop.y - my);
        if (dist < 12) {
            // Flash collect animation then remove
            clearTimeout(drop.expireTimer);
            drop.el.classList.add('loot-collected');
            const elRef = drop.el;
            setTimeout(() => elRef.remove(), 350);
            // Bank the fragment
            if (!sessionScriptFrags[drop.defId]) sessionScriptFrags[drop.defId] = {};
            sessionScriptFrags[drop.defId][drop.lineIdx] = (sessionScriptFrags[drop.defId][drop.lineIdx] || 0) + 1;
            activeLootDrops.splice(i, 1);
        }
    }
}

function clearAllLootDrops() {
    // Bank any uncollected drops into sessionScriptFrags before removing them
    activeLootDrops.forEach(d => {
        clearTimeout(d.expireTimer);
        d.el.remove();
        if (!sessionScriptFrags[d.defId]) sessionScriptFrags[d.defId] = {};
        sessionScriptFrags[d.defId][d.lineIdx] = (sessionScriptFrags[d.defId][d.lineIdx] || 0) + 1;
    });
    activeLootDrops = [];
}

// ── Spawn helpers ──────────────────────────────────────────
function nb_spawnNodeWithMoons(typeOverride = null) {
    const n = new NbNode(typeOverride);
    nb_nodes.push(n);
    if (n.type === 'medium' || n.type === 'boss') {
        const mc = n.type === 'boss'
            ? Math.floor(Math.random() * 4) + 3
            : Math.floor(Math.random() * 3) + 1;
        for (let i = 0; i < mc; i++) {
            const moon = new NbNode(null, true);
            moon.parent      = n;
            moon.orbitRadius = n.size / 2 + moon.size / 2 + 12 + Math.random() * 20;
            moon.orbitSpeed  = (Math.random() > 0.5 ? 1 : -1) * (0.3 + Math.random() * 0.4);
            moon.orbitAngle  = (Math.PI * 2 / mc) * i;
            moon.x = n.x + Math.cos(moon.orbitAngle) * moon.orbitRadius;
            moon.y = n.y + Math.sin(moon.orbitAngle) * moon.orbitRadius;
            nb_nodes.push(moon);
        }
    }
}

// ── Breach round management ────────────────────────────────
function nb_endRound() {
    if (nb_gameState === 'modal') return;
    nb_gameState = 'modal';
    clearAllLootDrops();

    // Bank resources
    savedFragments += sessionFragments;
    const newData   = Math.floor(savedFragments / 3);
    savedData      += newData;
    savedFragments  = savedFragments % 3;
    savedXp        += sessionXp;

    // Persist breach save state (include invFragments so nothing is lost between runs)
    const raw = hbLoadRaw() || {};
    hbSaveRaw({ ...raw, savedFragments, savedData, savedXp, invFragments, breachInProgress: false });

    showRunEndOverlay();
}

function nb_startNewRound() {
    // Compute effective stats from the current compiler pipeline
    pipelineStats    = computePipelineStats();
    nb_applyRadius(); // immediately update cursor radius before first frame
    playerHealth     = MAX_HEALTH;
    playerShield     = pipelineStats.shield;
    sessionFragments = 0;
    sessionNodes     = 0;
    sessionXp        = 0;
    sessionTime      = 0;
    bossProgress     = 0;
    spawnAccumulator = 0;
    sessionScriptFrags  = {};
    nb_eventDamageBoost = 0;
    nb_eventHackBoost   = 0;
    nb_eventFragBoost   = 1;
    nb_eventRadiusBoost = 0;
    nb_prevLevelForEvent = getLevel(savedXp);
    prevLevel        = getLevel(savedXp);
    nb_nodes = []; nb_frags = [];
    clearAllLootDrops();
    progressFill.style.width = '0%';
    for (let i = 0; i < 3; i++) nb_spawnNodeWithMoons();
    nb_gameState = 'playing';
    lastTime = performance.now();

    // Mark breach in progress; persist invFragments so accumulated frags survive
    const raw = hbLoadRaw() || {};
    hbSaveRaw({ ...raw, savedFragments, savedData, savedXp, invFragments, breachInProgress: true });
}

// ── Canvas resize ──────────────────────────────────────────
// Apply the correct cursor radius from pipelineStats (or base if no pipeline yet).
// Called from both nb_resize and nb_startNewRound so they always match.
function nb_applyRadius() {
    const base = pipelineStats ? pipelineStats.radius : PLAYER_STATS.radius;
    nb_mouse.radius = Math.max(28, base + nb_eventRadiusBoost);
}

function nb_resize() {
    const w = window.innerWidth, h = window.innerHeight;
    if (nb_prevW && nb_prevH && (nb_prevW !== w || nb_prevH !== h)) {
        const sx = w / nb_prevW, sy = h / nb_prevH;
        for (const n of nb_nodes) { n.x *= sx; n.y *= sy; }
        for (const f of nb_frags) { f.x *= sx; f.y *= sy; }
        nb_mouse.x *= sx; nb_mouse.y *= sy;
    }
    nb_canvas.width = w; nb_canvas.height = h;
    nb_applyRadius();
    nb_prevW = w; nb_prevH = h;
}

// ── Pipeline event trigger helper ─────────────────────────
// Fires all action effects wired downstream of a given event node type.
function nb_fireEvent(eventId) {
    if (!pipelineStats || !pipelineStats.eventTriggers) return;
    const triggers = pipelineStats.eventTriggers[eventId];
    if (!triggers) return;
    for (const t of triggers) {
        switch (t.statName) {
            case 'radius':
                // Temporary radius burst — tracked separately from pipeline base
                nb_eventRadiusBoost += t.mod;
                nb_mouse.radius = Math.max(28, (pipelineStats ? pipelineStats.radius : PLAYER_STATS.radius) + nb_eventRadiusBoost);
                setTimeout(() => {
                    nb_eventRadiusBoost -= t.mod;
                    nb_mouse.radius = Math.max(28, (pipelineStats ? pipelineStats.radius : PLAYER_STATS.radius) + nb_eventRadiusBoost);
                }, 3000);
                break;
            case 'damage':
                // Temporary damage boost tracked separately
                nb_eventDamageBoost += t.mod;
                setTimeout(() => { nb_eventDamageBoost -= t.mod; }, 3000);
                break;
            case 'heal':
                playerHealth = Math.min(MAX_HEALTH, playerHealth + t.mod);
                break;
            case 'shield':
                playerShield += t.mod;
                break;
            case 'hackspeed':
                nb_eventHackBoost += t.mod;
                setTimeout(() => { nb_eventHackBoost -= t.mod; }, 3000);
                break;
            case 'regen':
                // Burst regen
                playerHealth = Math.min(MAX_HEALTH, playerHealth + t.mod * 3);
                break;
            case 'magnet':
                // Burst magnet pull — collect all frags within range immediately
                for (const f of nb_frags) {
                    if (!f.homing) f.homing = true;
                }
                break;
            case 'databonus':
                nb_eventFragBoost = Math.max(nb_eventFragBoost, t.mod);
                setTimeout(() => { nb_eventFragBoost = 1; }, 5000);
                break;
            case 'aoe_dmg':
                // Damage all current nodes
                for (const n of nb_nodes) {
                    n.health -= t.mod;
                    n.flash   = 8;
                }
                break;
        }
    }
}

// Event boost accumulators (reset each round)
let nb_eventDamageBoost = 0;
let nb_eventHackBoost   = 0;
let nb_eventFragBoost   = 1;
let nb_eventRadiusBoost = 0;
let nb_prevLevelForEvent = 1;

// ── Main loop ──────────────────────────────────────────────
function nb_loop(now) {
    if (nb_gameState !== 'playing') { nb_loopRunning = false; return; }
    nb_loopRunning = true;

    const dt = Math.min((now - lastTime) / 1000, 0.1);
    lastTime = now;

    nb_ctx.clearRect(0, 0, nb_canvas.width, nb_canvas.height);

    sessionTime += dt;
    document.getElementById('time-display').textContent = nb_formatTime(sessionTime);

    const idleDegen = IDLE_DEGEN_BASE + sessionTime * IDLE_DEGEN_SCALE;
    playerHealth -= idleDegen * dt;

    // Pipeline event: On_Tick fires every ~1s
    if (pipelineStats) {
        nb_loop._tickAccum = (nb_loop._tickAccum || 0) + dt;
        if (nb_loop._tickAccum >= 1.0) {
            nb_loop._tickAccum -= 1.0;
            nb_fireEvent('event_tick');
        }
    }

    // Pipeline: passive regen
    if (pipelineStats && pipelineStats.regen > 0) {
        playerHealth = Math.min(MAX_HEALTH, playerHealth + pipelineStats.regen * dt);
    }

    // Pipeline: auto-magnet — pull nearby data frags toward cursor
    if (pipelineStats && pipelineStats.magnetR > 0) {
        for (const f of nb_frags) {
            if (!f.homing) {
                const dx = nb_mouse.x - f.x, dy = nb_mouse.y - f.y;
                const d  = Math.hypot(dx, dy);
                if (d < pipelineStats.magnetR && d > 1) {
                    const pull = 300 * dt;
                    f.x += (dx / d) * pull;
                    f.y += (dy / d) * pull;
                }
            }
        }
    }

    const primaryCount    = nb_nodes.filter(n => n.parent === null && n.type !== 'moon').length;
    const maxPrimary      = 8 + Math.floor(sessionTime * 1.2);
    const spawnsPerSecond = 1.0 + sessionTime * 0.1;
    spawnAccumulator += spawnsPerSecond * dt;
    while (spawnAccumulator >= 1.0) {
        if (primaryCount < maxPrimary) nb_spawnNodeWithMoons();
        spawnAccumulator -= 1.0;
    }

    const timeMult = 1 + sessionTime * 0.015;
    let highestHackProg = 0, tookBurstDamage = false;

    for (let i = nb_nodes.length - 1; i >= 0; i--) {
        const n    = nb_nodes[i];
        n.update(dt);
        const dist    = Math.hypot(n.x - nb_mouse.x, n.y - nb_mouse.y);
        const inRange = dist <= nb_mouse.radius + n.size / 2;

        if (inRange) {
            let proxDmg = 0.4 * timeMult * dt;
            if (playerShield > 0) {
                const absorbed = Math.min(playerShield, proxDmg);
                playerShield -= absorbed;
                proxDmg      -= absorbed;
            }
            playerHealth -= proxDmg;
            const hackSpeedMult = pipelineStats ? (1 + pipelineStats.hackspeed + nb_eventHackBoost) : 1;
            n.hackTimer += dt * 1000 * hackSpeedMult;
            if (n.hackTimer >= HACK_TIME_MS) {
                const effectiveDamage = (pipelineStats ? pipelineStats.damage : PLAYER_STATS.damage) + nb_eventDamageBoost;
                n.health    -= effectiveDamage;
                n.flash      = 5;
                n.hackTimer  = 0;
                let thornDmg = n.baseThorns * timeMult;
                if (playerShield > 0) {
                    const absorbed = Math.min(playerShield, thornDmg);
                    playerShield -= absorbed;
                    thornDmg     -= absorbed;
                }
                playerHealth -= thornDmg;
                tookBurstDamage = true;
                nb_fireEvent('event_hit');

                if (n.health <= 0) {
                    sessionNodes++;
                    bossProgress += n.progValue;
                    const wasBoss = n.type === 'boss';
                    if (bossProgress >= BOSS_THRESHOLD) {
                        bossProgress = 0;
                        nb_spawnNodeWithMoons('boss');
                        nb_fireEvent('event_boss');
                    }
                    progressFill.style.width = Math.min((bossProgress / BOSS_THRESHOLD) * 100, 100) + '%';

                    // Fire on_breach event
                    nb_fireEvent('event_hack');

                    // Data frags (pipeline fragMult + event boost scale the yield)
                    const fragYield = Math.round(n.dropAmount * (pipelineStats ? pipelineStats.fragMult : 1) * nb_eventFragBoost);
                    for (let f = 0; f < fragYield; f++) nb_frags.push(new NbFragment(n.x, n.y));

                    // Script loot drop chance (non-moon kills only)
                    if (n.type !== 'moon' && Math.random() < SCRIPT_DROP_CHANCE) {
                        spawnScriptLootDrop(n.x, n.y);
                    }

                    for (const other of nb_nodes) { if (other.parent === n) other.parent = null; }
                    nb_nodes.splice(i, 1);
                    continue;
                }
            }
            highestHackProg = Math.max(highestHackProg, n.hackTimer);
        }
        n.draw(inRange);
    }

    if (tookBurstDamage) nb_triggerDamageFlash();

    for (let i = nb_frags.length - 1; i >= 0; i--) {
        if (nb_frags[i].update(dt)) {
            sessionFragments++; sessionXp += 2;
            nb_frags.splice(i, 1);
        } else {
            nb_frags[i].draw();
        }
    }

    checkLootCollection();

    if (playerHealth <= 0) {
        playerHealth = 0;
        nb_updateHUD();
        nb_endRound();
        return;
    }

    nb_updateHUD();
    nb_drawCursor(now, highestHackProg);
    requestAnimationFrame(nb_loop);
}

function nb_updateHUD() {
    const hPct = (playerHealth / MAX_HEALTH) * 100;
    document.getElementById('health-fill').style.width = hPct + '%';
    const shieldTxt = playerShield > 0 ? ` [🛡${playerShield.toFixed(0)}]` : '';
    document.getElementById('health-text').textContent = `${playerHealth.toFixed(1)}/${MAX_HEALTH.toFixed(1)}${shieldTxt}`;
    fragDisplay.textContent = `DATA_FRAGS: ${sessionFragments}`;
    const totalXp   = savedXp + sessionXp;
    const level     = getLevel(totalXp);
    const xpInLevel = totalXp % XP_TO_LEVEL;
    const xpPct     = Math.min((xpInLevel / XP_TO_LEVEL) * 100, 100).toFixed(0);
    document.getElementById('xp-fill').style.width = xpPct + '%';
    document.getElementById('xp-text').textContent = xpPct + '%';
    levelDisplay.textContent = `LVL ${level}`;
    if (level > prevLevel) {
        prevLevel = level;
        nb_triggerLevelUp();
        nb_fireEvent('event_levelup');
    }
}

function nb_drawCursor(now, hackProgress) {
    const ctx = nb_ctx;
    ctx.save();
    const pulse = 0.4 + 0.4 * Math.sin(now / 150);
    ctx.beginPath();
    ctx.arc(nb_mouse.x, nb_mouse.y, nb_mouse.radius, 0, Math.PI * 2);
    ctx.strokeStyle = `rgba(0,229,255,${pulse})`; ctx.lineWidth = 2; ctx.stroke();

    if (hackProgress > 0) {
        const start = -Math.PI / 2;
        const end   = start + (hackProgress / HACK_TIME_MS) * Math.PI * 2;
        ctx.beginPath();
        ctx.arc(nb_mouse.x, nb_mouse.y, nb_mouse.radius + 6, 0, Math.PI * 2);
        ctx.strokeStyle = 'rgba(0,229,255,0.15)'; ctx.lineWidth = 4; ctx.stroke();
        ctx.beginPath();
        ctx.arc(nb_mouse.x, nb_mouse.y, nb_mouse.radius + 6, start, end);
        ctx.strokeStyle = '#00e5ff'; ctx.lineCap = 'round'; ctx.lineWidth = 4; ctx.stroke();
    }

    ctx.fillStyle = '#00e5ff';
    ctx.fillRect(nb_mouse.x - 2, nb_mouse.y - 2, 4, 4);
    ctx.restore();
}

// ── Init breach screen ─────────────────────────────────────
function initBreach() {
    nb_canvas    = document.getElementById('gameCanvas');
    nb_ctx       = nb_canvas.getContext('2d');
    fragDisplay  = document.getElementById('fragment-counter');
    levelDisplay = document.getElementById('level-display');
    damageFlash  = document.getElementById('damage-flash');
    progressFill = document.getElementById('progress-fill');
    levelupToast = document.getElementById('levelup-toast');

    // Only attach listeners once
    if (!nb_canvas._listenersAttached) {
        nb_canvas._listenersAttached = true;
        function updateMousePos(e) {
            const src = e.touches ? e.touches[0] : e;
            nb_mouse.x = src.clientX; nb_mouse.y = src.clientY;
        }
        window.addEventListener('mousemove', updateMousePos);
        window.addEventListener('touchstart', updateMousePos, { passive: true });
        window.addEventListener('touchmove', e => { e.preventDefault(); updateMousePos(e); }, { passive: false });
        window.addEventListener('resize', nb_resize);
    }
    nb_resize();
}

// =========================================================
// ─── RUN END OVERLAY ─────────────────────────────────────
// =========================================================
function showRunEndOverlay() {
    document.getElementById('re-stat-time').textContent      = nb_formatTime(sessionTime);
    document.getElementById('re-stat-nodes').textContent     = sessionNodes;
    document.getElementById('re-stat-frags').textContent     = `+${sessionFragments}`;
    document.getElementById('re-stat-banked').textContent    = savedData;
    document.getElementById('re-stat-xp').textContent        = savedXp;

    // Script frags
    const list = document.getElementById('re-frag-list');
    list.innerHTML = '';
    let hasFrags = false;
    for (const defId in sessionScriptFrags) {
        const def = NODE_DEFS[defId];
        if (!def) continue;
        for (const lineIdx in sessionScriptFrags[defId]) {
            const count = sessionScriptFrags[defId][lineIdx];
            if (count <= 0) continue;
            hasFrags = true;
            const pill = document.createElement('div');
            pill.className = 're-frag-pill';
            pill.textContent = `${def.icon} ${def.title.replace('()', '')} L${parseInt(lineIdx)+1} ×${count}`;
            list.appendChild(pill);
        }
    }
    if (!hasFrags) {
        list.innerHTML = '<span class="re-frag-empty">No script fragments found this run.</span>';
    }

    document.getElementById('run-end-overlay').classList.add('visible');
}

function hideRunEndOverlay() {
    document.getElementById('run-end-overlay').classList.remove('visible');
}

function reBreachAgain() {
    hideRunEndOverlay();
    // Bank this run's script frags into inventory BEFORE nb_startNewRound clears sessionScriptFrags
    flushRunScriptFrags();
    nb_loopRunning = false;  // cancel any pending loop frame
    nb_startNewRound();
    lastTime = performance.now();
    requestAnimationFrame(nb_loop);
}

function reGoToCompiler() {
    hideRunEndOverlay();
    flushRunScriptFrags();
    initCompiler();
    showScreen('compiler');
}

function reGoToTitle() {
    hideRunEndOverlay();
    flushRunScriptFrags();   // bank this run's script frags before leaving
    nb_gameState = 'idle';
    showScreen('title');
    updateTitleSaveInfo();
}

function flushRunScriptFrags() {
    for (const defId in sessionScriptFrags) {
        if (!invFragments[defId]) invFragments[defId] = {};
        for (const lineIdx in sessionScriptFrags[defId]) {
            invFragments[defId][lineIdx] = (invFragments[defId][lineIdx] || 0) + sessionScriptFrags[defId][lineIdx];
        }
    }
    sessionScriptFrags = {};
    // Persist inventory update
    const raw = hbLoadRaw() || {};
    hbSaveRaw({ ...raw, invFragments });
}

// =========================================================
// ─── TITLE SCREEN ────────────────────────────────────────
// =========================================================
function updateTitleSaveInfo() {
    const raw = hbLoadRaw();
    const el  = document.getElementById('title-save-info');
    if (!raw) {
        el.textContent = 'No save found — new game.';
        document.getElementById('title-btn-continue').style.display = 'none';
        return;
    }
    const d = new Date(raw.savedAt);
    const t = d.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    el.innerHTML = `XP: <span style="color:var(--neon-purple)">${raw.savedXp || 0}</span> &nbsp;|&nbsp; Data: <span style="color:var(--neon-blue)">${raw.savedData || 0}</span> &nbsp;|&nbsp; Saved: ${t}`;
    document.getElementById('title-btn-continue').style.display = raw.breachInProgress ? '' : 'none';
}

function titleStartNewBreach() {
    // Load breach persistent values
    const raw = hbLoadRaw();
    savedFragments = raw?.savedFragments || 0;
    savedData      = raw?.savedData      || 0;
    savedXp        = raw?.savedXp        || 0;

    initBreach();
    showScreen('breach');
    nb_startNewRound();
    requestAnimationFrame(nb_loop);
}

function titleContinueBreach() {
    const raw = hbLoadRaw();
    savedFragments = raw?.savedFragments || 0;
    savedData      = raw?.savedData      || 0;
    savedXp        = raw?.savedXp        || 0;

    initBreach();
    showScreen('breach');
    nb_startNewRound(); // still starts fresh round (no mid-run save yet)
    requestAnimationFrame(nb_loop);
}

function titleGoToSettings() {
    openSettings();
}

function titleGoToCompiler() {
    flushRunScriptFrags(); // in case any lingered
    const raw = hbLoadRaw();
    if (raw) {
        invFragments    = raw.invFragments    || {};
        stashNodes      = raw.stashNodes      || [{ id: 'sn1', defId: 'action_radius', tier: 0 }, { id: 'sn2', defId: 'event_hack', tier: 0 }];
        blueprintDrafts = raw.blueprintDrafts || {};
    }
    initCompiler();
    showScreen('compiler');
}

function breachBackToTitle() {
    nb_gameState = 'idle';
    clearAllLootDrops();
    showScreen('title');
    updateTitleSaveInfo();
}

// =========================================================
// ─── COMPILER ────────────────────────────────────────────
// =========================================================

// =========================================================
// PLAYER BASE STATS
// =========================================================
const PLAYER_STATS = { radius: 35.0, damage: 35.0, integrity: 100.0 };

// =========================================================
// PIPELINE STAT COMPUTATION
// Walks ws_connections from sys_in → sys_out, finds all
// reachable action nodes, and computes effective breach stats.
// Called at breach start. Returns a flat object of overrides.
// =========================================================
function computePipelineStats() {
    const result = {
        radius:     PLAYER_STATS.radius,
        damage:     PLAYER_STATS.damage,
        integrity:  PLAYER_STATS.integrity,
        hackspeed:  0,      // reduction to HACK_TIME_MS (fraction)
        regen:      0,      // hp/sec passive regen
        fragMult:   1.0,    // data frag drop multiplier
        magnetR:    0,      // auto-magnet radius
        shield:     0,      // starting shield hp
    };

    // BFS forward from sys_in
    const sysIn = ws_nodes.find(n => n.id === 'sys_in');
    if (!sysIn || ws_connections.length === 0) return result;

    const fwdReachable = new Set();
    const fwdQueue = [sysIn.id];
    while (fwdQueue.length) {
        const cur = fwdQueue.shift();
        if (fwdReachable.has(cur)) continue;
        fwdReachable.add(cur);
        ws_connections.filter(c => c.fromNode === cur).forEach(c => fwdQueue.push(c.toNode));
    }

    // Only proceed if sys_out is reachable at all
    if (!fwdReachable.has('sys_out')) return result;

    // BFS backward from sys_out — finds every node that has a path LEADING TO sys_out.
    // A node only counts if it's on a complete path: sys_in → ... → node → ... → sys_out.
    const bwdReachable = new Set();
    const bwdQueue = ['sys_out'];
    while (bwdQueue.length) {
        const cur = bwdQueue.shift();
        if (bwdReachable.has(cur)) continue;
        bwdReachable.add(cur);
        ws_connections.filter(c => c.toNode === cur).forEach(c => bwdQueue.push(c.fromNode));
    }

    // A node is "live" only if it appears in BOTH traversals:
    // reachable forward from sys_in AND backward from sys_out.
    const live = new Set([...fwdReachable].filter(id => bwdReachable.has(id)));

    result.eventTriggers = {};

    for (const nodeId of live) {
        const node = ws_nodes.find(n => n.id === nodeId);
        if (!node || node.isSystem) continue;
        const def = NODE_DEFS[node.defId];
        if (!def) continue;

        const mod = def.baseMod ? def.baseMod * (1 + node.tier * 0.5) : 0;

        if (def.statName) {
            // Action node directly on a live path — passive stat always applies
            switch (def.statName) {
                case 'radius':     result.radius    += mod; break;
                case 'damage':     result.damage    += mod; break;
                case 'heal':       /* handled per-hit in breach */ break;
                case 'aoe_dmg':    result.damage    += mod * 0.5; break;
                case 'shield':     result.shield    += mod; break;
                case 'hackspeed':  result.hackspeed += mod; break;
                case 'magnet':     result.magnetR    = Math.max(result.magnetR, mod); break;
                case 'regen':      result.regen     += mod; break;
                case 'databonus':  result.fragMult  *= mod; break;
            }
        } else if (def.id && def.id.startsWith('event_')) {
            // Event node is live — find downstream action nodes that are ALSO live.
            // This ensures only actions wired all the way to sys_out actually trigger.
            const evTriggers = [];
            const evQueue = [nodeId];
            const evSeen  = new Set([nodeId]);
            while (evQueue.length) {
                const cur = evQueue.shift();
                ws_connections.filter(c => c.fromNode === cur).forEach(c => {
                    if (evSeen.has(c.toNode)) return;
                    evSeen.add(c.toNode);
                    evQueue.push(c.toNode);
                    if (!live.has(c.toNode)) return; // action not on a live path — skip
                    const dn   = ws_nodes.find(n => n.id === c.toNode);
                    const ddef = dn ? NODE_DEFS[dn.defId] : null;
                    if (ddef && ddef.statName) {
                        evTriggers.push({
                            statName: ddef.statName,
                            mod: ddef.baseMod * (1 + dn.tier * 0.5)
                        });
                    }
                });
            }
            if (evTriggers.length) result.eventTriggers[def.id] = evTriggers;
        }
    }

    return result;
}

// =========================================================
// NODE DEFINITIONS
// =========================================================
const NODE_DEFS = {
    'sys_in': {
        id: 'sys_in', title: 'System', typeClass: 'type-system', color: 'var(--neon-green)', icon: '🌐',
        inputs: [], outputs: [{ id: 'out_flow', label: 'Sys.Out', type: 'flow' }],
        isSystem: true, desc: '// Root entry point from hacking OS'
    },
    'sys_out': {
        id: 'sys_out', title: 'WAN_Out', typeClass: 'type-system', color: 'var(--neon-green)', icon: '📡',
        inputs: [{ id: 'in_flow', label: 'Net.Out', type: 'flow' }], outputs: [],
        isSystem: true, desc: '// Final execution to Wide Area Network'
    },

    // ── Flow nodes ──
    'flow_seq': {
        id: 'flow_seq', title: 'Sequence()', typeClass: 'type-flow', color: 'var(--neon-gold)', icon: '🔀',
        inputs: [{ id: 'in_0', label: 'Then 0', type: 'flow' }, { id: 'in_1', label: 'Then 1', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Merges multiple execution paths sequentially.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">Sequence</span>() {`,
            `    <span class="c-fn">await</span>(0); <span class="c-fn">await</span>(1);`,
            `}`
        ]
    },
    'flow_branch': {
        id: 'flow_branch', title: 'Branch()', typeClass: 'type-flow', color: 'var(--neon-gold)', icon: '🌿',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_true', label: 'True', type: 'flow' }, { id: 'out_false', label: 'False', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Conditionally routes execution down true or false path.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">Branch</span>(<span class="c-vr">cond</span>) {`,
            `    <span class="c-kw">if</span> (cond) <span class="c-fn">exec_true</span>();`,
            `    <span class="c-kw">else</span>     <span class="c-fn">exec_false</span>();`,
            `}`
        ]
    },
    'flow_loop': {
        id: 'flow_loop', title: 'ForLoop()', typeClass: 'type-flow', color: 'var(--neon-gold)', icon: '🔁',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_body', label: 'Body', type: 'flow' }, { id: 'out_done', label: 'Done', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Repeats body execution N times, then fires Done.',
        codeLines: [
            `<span class="c-kw">for</span> (<span class="c-vr">i</span> = 0; i < <span class="c-nm">N</span>; i++) {`,
            `    <span class="c-fn">exec_body</span>();`,
            `}`,
            `<span class="c-fn">exec_done</span>();`
        ]
    },

    // ── Event nodes ──
    'event_tick': {
        id: 'event_tick', title: 'On_Tick()', typeClass: 'type-event', color: 'var(--neon-pink)', icon: '⏱️',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Triggers every system clock cycle.',
        codeLines: [
            `<span class="c-kw">event</span> <span class="c-fn">On_Tick</span>() {`,
            `    <span class="c-fn">execute</span>(<span class="c-vr">EXEC</span>);`,
            `}`
        ]
    },
    'event_hit': {
        id: 'event_hit', title: 'On_Dmg_Taken()', typeClass: 'type-event', color: 'var(--neon-pink)', icon: '💥',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Triggers when player loses integrity.',
        codeLines: [
            `<span class="c-kw">event</span> <span class="c-fn">On_Damage_Taken</span>() {`,
            `    <span class="c-fn">execute</span>(<span class="c-vr">EXEC</span>);`,
            `}`
        ]
    },
    'event_hack': {
        id: 'event_hack', title: 'On_Breach()', typeClass: 'type-event', color: 'var(--neon-pink)', icon: '⚡',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Triggers when an enemy node is destroyed.',
        codeLines: [
            `<span class="c-kw">event</span> <span class="c-fn">On_Breach</span>() {`,
            `    <span class="c-fn">execute</span>(<span class="c-vr">EXEC</span>);`,
            `}`
        ]
    },
    'event_levelup': {
        id: 'event_levelup', title: 'On_LevelUp()', typeClass: 'type-event', color: 'var(--neon-pink)', icon: '🆙',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Fires once when player XP crosses a level threshold.',
        codeLines: [
            `<span class="c-kw">event</span> <span class="c-fn">On_LevelUp</span>() {`,
            `    <span class="c-fn">execute</span>(<span class="c-vr">EXEC</span>);`,
            `}`
        ]
    },
    'event_boss': {
        id: 'event_boss', title: 'On_BossSpawn()', typeClass: 'type-event', color: 'var(--neon-pink)', icon: '👾',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: null, baseMod: null, isSystem: false,
        desc: 'Triggers when a boss-class node enters the arena.',
        codeLines: [
            `<span class="c-kw">event</span> <span class="c-fn">On_BossSpawn</span>() {`,
            `    <span class="c-fn">execute</span>(<span class="c-vr">EXEC</span>);`,
            `}`
        ]
    },

    // ── Action nodes ──
    'action_radius': {
        id: 'action_radius', title: 'Expand_Radius()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '⭕',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'radius', statBase: 'radius', baseMod: 15.0, isSystem: false,
        desc: 'Increases targeting area by a flat radius value.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">Expand_Radius</span>() {`,
            `    <span class="c-vr">sys.radius</span> = <span class="c-nb">{BASE}</span> + <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
    'action_dmg': {
        id: 'action_dmg', title: 'Overclock_Dmg()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '⚔️',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'damage', statBase: 'damage', baseMod: 10.0, isSystem: false,
        desc: 'Overclocks base node damage output.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">Overclock_Dmg</span>() {`,
            `    <span class="c-vr">sys.attack</span> = <span class="c-nb">{BASE}</span> + <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
    'action_heal': {
        id: 'action_heal', title: 'Restore_Integrity()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '❤️',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'heal', statBase: 'integrity', baseMod: 5.0, isSystem: false,
        desc: 'Restores player integrity on execution.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">Restore_Integrity</span>() {`,
            `    <span class="c-vr">sys.hp</span> += <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
    'action_emp': {
        id: 'action_emp', title: 'Pulse_EMP()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '💢',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'aoe_dmg', statBase: 'damage', baseMod: 50.0, isSystem: false,
        desc: 'Massive AOE burst to all connected enemy nodes.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">Pulse_EMP</span>() {`,
            `    <span class="c-fn">deal_aoe</span>(<span class="c-nm">{MOD}</span>);`,
            `}`
        ]
    },
    'action_shield': {
        id: 'action_shield', title: 'Deploy_Shield()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '🛡️',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'shield', statBase: 'integrity', baseMod: 20.0, isSystem: false,
        desc: 'Absorbs incoming damage up to shield value before HP drains.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">Deploy_Shield</span>() {`,
            `    <span class="c-vr">sys.shield</span> += <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
    'action_hack_boost': {
        id: 'action_hack_boost', title: 'HackSpeed_Up()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '⚙️',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'hackspeed', statBase: 'damage', baseMod: 0.25, isSystem: false,
        desc: 'Reduces hack tick interval — more hits per second.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">HackSpeed_Up</span>() {`,
            `    <span class="c-vr">sys.tickRate</span> -= <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
    'action_frag_magnet': {
        id: 'action_frag_magnet', title: 'FragMagnet()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '🧲',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'magnet', statBase: 'radius', baseMod: 60.0, isSystem: false,
        desc: 'Pulls nearby data fragments toward the cursor automatically.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">FragMagnet</span>() {`,
            `    <span class="c-vr">sys.magnetR</span> = <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
    'action_regen': {
        id: 'action_regen', title: 'AutoRegen()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '💊',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'regen', statBase: 'integrity', baseMod: 0.5, isSystem: false,
        desc: 'Passively regenerates integrity HP per second while active.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">AutoRegen</span>() {`,
            `    <span class="c-vr">sys.regen</span> += <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
    'action_databank': {
        id: 'action_databank', title: 'DataBank_Boost()', typeClass: 'type-action', color: 'var(--neon-blue)', icon: '💾',
        inputs: [{ id: 'in_flow', label: 'Exec', type: 'flow' }],
        outputs: [{ id: 'out_flow', label: 'Exec', type: 'flow' }],
        statName: 'databonus', statBase: 'damage', baseMod: 2.0, isSystem: false,
        desc: 'Multiplies data fragment yield per node kill.',
        codeLines: [
            `<span class="c-kw">function</span> <span class="c-fn">DataBank_Boost</span>() {`,
            `    <span class="c-vr">sys.fragMult</span> *= <span class="c-nm">{MOD}</span>;`,
            `}`
        ]
    },
};

// Build SCRIPT_DROP_TABLE from NODE_DEFS (weights by category)
(function buildDropTable() {
    for (const defId in NODE_DEFS) {
        const def = NODE_DEFS[defId];
        if (def.isSystem) continue;
        const typeWeight = defId.startsWith('event') ? 3 : defId.startsWith('action') ? 2 : 1;
        for (let lineIdx = 0; lineIdx < (def.codeLines || []).length; lineIdx++) {
            SCRIPT_DROP_TABLE.push({ defId, lineIdx, weight: typeWeight });
        }
    }
})();

// =========================================================
// MACROS
// =========================================================
const MACROS = [
    {
        id: 'm1', title: 'Panic Heal',
        desc: 'Automatically restores integrity when damage is taken.',
        reqs: ['event_hit', 'action_heal'],
        exec(sx, sy) {
            const n1 = deployNodeToCanvas('event_hit',   popStashNode('event_hit').tier,   sx - 120, sy);
            const n2 = deployNodeToCanvas('action_heal', popStashNode('action_heal').tier, sx + 120, sy);
            pushConn(n1.id, 'out_flow', n2.id, 'in_flow');
        }
    },
    {
        id: 'm2', title: 'Ordered Breach',
        desc: 'On breach, pulses EMP then buffs damage.',
        reqs: ['event_hack', 'flow_seq', 'action_emp', 'action_dmg'],
        exec(sx, sy) {
            const ev  = deployNodeToCanvas('event_hack', popStashNode('event_hack').tier, sx - 220, sy);
            const seq = deployNodeToCanvas('flow_seq',   popStashNode('flow_seq').tier,   sx,       sy);
            const emp = deployNodeToCanvas('action_emp', popStashNode('action_emp').tier, sx + 220, sy - 70);
            const dmg = deployNodeToCanvas('action_dmg', popStashNode('action_dmg').tier, sx + 220, sy + 70);
            pushConn(ev.id,  'out_flow', seq.id, 'in_0');
            pushConn(seq.id, 'out_flow', emp.id, 'in_flow');
            pushConn(seq.id, 'out_flow', dmg.id, 'in_flow');
        }
    },
    {
        id: 'm3', title: 'Level Surge',
        desc: 'On level-up, overclock damage and raise shields.',
        reqs: ['event_levelup', 'action_dmg', 'action_shield'],
        exec(sx, sy) {
            const ev  = deployNodeToCanvas('event_levelup', popStashNode('event_levelup').tier, sx - 220, sy);
            const dmg = deployNodeToCanvas('action_dmg',    popStashNode('action_dmg').tier,    sx,       sy - 60);
            const sh  = deployNodeToCanvas('action_shield', popStashNode('action_shield').tier, sx,       sy + 60);
            pushConn(ev.id, 'out_flow', dmg.id, 'in_flow');
            pushConn(ev.id, 'out_flow', sh.id,  'in_flow');
        }
    },
    {
        id: 'm4', title: 'Magnet Farm',
        desc: 'Every tick, pull frags while slowly regenerating.',
        reqs: ['event_tick', 'action_frag_magnet', 'action_regen'],
        exec(sx, sy) {
            const ev  = deployNodeToCanvas('event_tick',       popStashNode('event_tick').tier,       sx - 220, sy);
            const mag = deployNodeToCanvas('action_frag_magnet', popStashNode('action_frag_magnet').tier, sx,   sy - 60);
            const reg = deployNodeToCanvas('action_regen',     popStashNode('action_regen').tier,     sx,       sy + 60);
            pushConn(ev.id, 'out_flow', mag.id, 'in_flow');
            pushConn(ev.id, 'out_flow', reg.id, 'in_flow');
        }
    },
];

function pushConn(fromNode, fromPort, toNode, toPort, type = 'flow') {
    ws_connections.push({
        id: 'c_' + Math.random().toString(36).substr(2, 6),
        fromNode, fromPort, toNode, toPort, type
    });
}

// =========================================================
// COMPILER APP STATE
// =========================================================
let invFragments    = {};
let stashNodes      = [
    { id: 'sn1', defId: 'action_radius', tier: 0 },
    { id: 'sn2', defId: 'event_hack',    tier: 0 }
];
let activeBlueprint = null;
let blueprintDrafts = {};
let isCompiling     = false;

let ws_nodes       = [];
let ws_connections = [];
let selectedNode   = null, draggedNode = null, dragOffset = { x: 0, y: 0 };
let drawingWire    = false, wireStartPort = null, wireStartNode = null;
let camX = 0, camY = 0, camScale = 1;
let isPanning = false, panStartX = 0, panStartY = 0;
let panelCollapsed = { left: false, right: false };

let ws_area = null, canvasInner = null, nLayer = null, wLayer = null;

// =========================================================
// COMPILER INIT
// =========================================================
function initCompiler() {
    ws_area      = document.getElementById('workspace-canvas-area');
    canvasInner  = document.getElementById('canvas-inner');
    nLayer       = document.getElementById('node-layer');
    wLayer       = document.getElementById('wire-layer');

    // Init draft arrays
    for (const key in NODE_DEFS) {
        if (!NODE_DEFS[key].isSystem && !blueprintDrafts[key]) {
            blueprintDrafts[key] = new Array(NODE_DEFS[key].codeLines.length).fill(false);
        }
    }

    renderBlueprintList();
    renderInventory();
    renderStash();
    renderMacros();

    // Spawn system nodes if this is first init or canvas was cleared
    const hasSysIn = ws_nodes.some(n => n.id === 'sys_in');
    if (!hasSysIn) {
        const cx = window.innerWidth  / 2;
        const cy = window.innerHeight / 2 - 22;
        deployNodeToCanvas('sys_in',  0, cx - 220, cy, true, 'sys_in');
        deployNodeToCanvas('sys_out', 0, cx + 80,  cy, true, 'sys_out');
    }

    // Attach canvas events only once
    if (!ws_area._listenersAttached) {
        ws_area._listenersAttached = true;
        ws_area.addEventListener('mousedown',  onCanvasPointerDown);
        ws_area.addEventListener('touchstart', onCanvasPointerDown, { passive: false });
        window.addEventListener('mousemove',  onGlobalPointerMove);
        window.addEventListener('touchmove',  onGlobalPointerMove, { passive: false });
        window.addEventListener('mouseup',    onGlobalPointerUp);
        window.addEventListener('touchend',   onGlobalPointerUp);
        ws_area.addEventListener('wheel', onCanvasWheel, { passive: false });
        window.addEventListener('resize', () => {
            const wsRect     = ws_area.getBoundingClientRect();
            const oldCentreX = (wsRect.width  / 2 - camX) / camScale;
            const oldCentreY = (wsRect.height / 2 - camY) / camScale;
            requestAnimationFrame(() => {
                const newRect = ws_area.getBoundingClientRect();
                camX = newRect.width  / 2 - oldCentreX * camScale;
                camY = newRect.height / 2 - oldCentreY * camScale;
                updateCanvasTransform();
                updateWires();
            });
        });
    }

    // Load save if available
    const raw = hbLoadRaw();
    if (raw) {
        invFragments    = raw.invFragments    || {};
        stashNodes      = raw.stashNodes      || stashNodes;
        blueprintDrafts = raw.blueprintDrafts || blueprintDrafts;
        // Ensure all drafts are initialised
        for (const key in NODE_DEFS) {
            if (!NODE_DEFS[key].isSystem && !blueprintDrafts[key]) {
                blueprintDrafts[key] = new Array(NODE_DEFS[key].codeLines.length).fill(false);
            }
        }
        // Re-apply system node positions
        if (raw.systemNodePos) {
            ws_nodes.filter(n => n.isSystem).forEach(n => {
                const pos = raw.systemNodePos[n.id];
                if (pos) { n.x = pos.x; n.y = pos.y; n.element.style.left = pos.x+'px'; n.element.style.top = pos.y+'px'; }
            });
        }
        // Strip existing non-system canvas nodes before re-deploying from save
        ws_nodes.filter(n => !n.isSystem).forEach(n => n.element.remove());
        ws_nodes = ws_nodes.filter(n => n.isSystem);
        ws_connections = [];

        // Re-deploy non-system nodes
        const idMap = {};
        ws_nodes.forEach(n => { idMap[n.id] = n.id; });
        (raw.wsNodes || []).forEach(nd => {
            const fresh = deployNodeToCanvas(nd.defId, nd.tier, nd.x, nd.y, false);
            idMap[nd.id] = fresh.id;
        });
        ws_connections = [];
        (raw.wsConnections || []).forEach(c => {
            const from = idMap[c.fromNode] ?? c.fromNode;
            const to   = idMap[c.toNode]   ?? c.toNode;
            if (ws_nodes.find(n => n.id === from) && ws_nodes.find(n => n.id === to)) {
                ws_connections.push({ ...c, id: 'conn_' + Math.random().toString(36).substr(2,6), fromNode: from, toNode: to });
            }
        });
        camX = raw.camX ?? 0; camY = raw.camY ?? 0; camScale = raw.camScale ?? 1;
        updateCanvasTransform();
        updateSettingsTimestamp(raw.savedAt);
    }

    renderInventory();
    renderStash();
    renderMacros();
    renderBlueprintList();
    switchView('workspace');

    // Defer wire redraw until browser has finished laying out the newly deployed nodes.
    // offsetLeft/offsetTop aren't reliable until after a layout pass.
    requestAnimationFrame(() => requestAnimationFrame(() => updateWires()));
}

// =========================================================
// NAVIGATION
// =========================================================
function switchView(view) {
    document.getElementById('nav-ide').classList.toggle('active', view === 'ide');
    document.getElementById('nav-workspace').classList.toggle('active', view === 'workspace');

    // Update bottom nav: only IDE and Pipeline tabs track view; Stash/Inspector/Title are separate
    ['mob-nav-ide', 'mob-nav-workspace'].forEach(id => {
        const el = document.getElementById(id);
        if (el) {
            el.classList.toggle('active', id === 'mob-nav-' + view);
            el.classList.remove('panel-open');
        }
    });

    document.querySelectorAll('#screen-compiler .view-container').forEach(v => v.classList.remove('active'));
    document.getElementById('view-' + view)?.classList.add('active');

    // Close panels when switching views (they may be irrelevant to new view)
    document.getElementById('left-panel').classList.remove('open');
    document.getElementById('right-panel').classList.remove('open');
    document.getElementById('mob-nav-stash')?.classList.remove('active', 'panel-open');
    document.getElementById('mob-nav-inspector')?.classList.remove('active', 'panel-open');

    const fragBtn   = document.getElementById('tab-btn-fragments');
    const macrosBtn = document.getElementById('tab-btn-macros');
    if (view === 'ide') {
        fragBtn.style.display   = '';
        macrosBtn.style.display = 'none';
        switchStashTab('fragments');
    } else {
        fragBtn.style.display   = 'none';
        macrosBtn.style.display = '';
        switchStashTab('nodes');
    }
}

// Mobile-only toggle functions for Stash and Inspector bottom-nav tabs
function mobToggleStash() {
    const panel    = document.getElementById('left-panel');
    const btn      = document.getElementById('mob-nav-stash');
    const isOpen   = panel.classList.contains('open');

    // Close inspector if open
    document.getElementById('right-panel').classList.remove('open');
    document.getElementById('mob-nav-inspector')?.classList.remove('active', 'panel-open');

    panel.classList.toggle('open', !isOpen);
    btn?.classList.toggle('panel-open', !isOpen);
    btn?.classList.toggle('active',     !isOpen);
}

function mobToggleInspector() {
    const panel    = document.getElementById('right-panel');
    const btn      = document.getElementById('mob-nav-inspector');
    const isOpen   = panel.classList.contains('open');

    // Close stash if open
    document.getElementById('left-panel').classList.remove('open');
    document.getElementById('mob-nav-stash')?.classList.remove('active', 'panel-open');

    panel.classList.toggle('open', !isOpen);
    btn?.classList.toggle('panel-open', !isOpen);
    btn?.classList.toggle('active',     !isOpen);
}

function switchStashTab(tab) {
    document.querySelectorAll('#left-panel .tab').forEach(t => t.classList.remove('active'));
    const btn = document.getElementById('tab-btn-' + tab);
    if (btn) btn.classList.add('active');
    document.getElementById('tab-fragments').style.display = tab === 'fragments' ? 'flex' : 'none';
    document.getElementById('tab-nodes').style.display     = tab === 'nodes'     ? 'flex' : 'none';
    document.getElementById('tab-macros').style.display    = tab === 'macros'    ? 'flex' : 'none';
}

function openMobileDrawer(tab) {
    document.getElementById('left-panel').classList.add('open');
    switchStashTab(tab);
    document.getElementById('mob-nav-stash')?.classList.add('panel-open');
}
function closeMobileDrawer() {
    document.getElementById('left-panel').classList.remove('open');
    document.getElementById('mob-nav-stash')?.classList.remove('active', 'panel-open');
}

function togglePanel(side) {
    const panel = document.getElementById(`${side}-panel`);
    const btn   = document.getElementById(`toggle-${side}`);
    panelCollapsed[side] = !panelCollapsed[side];
    panel.classList.toggle('collapsed', panelCollapsed[side]);
    if (side === 'left') {
        btn.textContent = panelCollapsed[side] ? '▶' : '◀';
        btn.title       = panelCollapsed[side] ? 'Expand stash' : 'Collapse stash';
    } else {
        btn.textContent = panelCollapsed[side] ? '◀' : '▶';
        btn.title       = panelCollapsed[side] ? 'Expand inspector' : 'Collapse inspector';
    }
    setTimeout(updateWires, 280);
}

function compilerBackToTitle() {
    // Auto-save before leaving
    compilerAutoSave();
    showScreen('title');
    updateTitleSaveInfo();
}

function compilerGoToBreach() {
    compilerAutoSave();
    const raw = hbLoadRaw() || {};
    savedFragments = raw.savedFragments || 0;
    savedData      = raw.savedData      || 0;
    savedXp        = raw.savedXp        || 0;
    initBreach();
    showScreen('breach');
    nb_startNewRound();
    requestAnimationFrame(nb_loop);
}

// =========================================================
// TOAST
// =========================================================
function showToast(msg) {
    const t = document.getElementById('toast-container');
    t.textContent = msg; t.style.opacity = '1';
    clearTimeout(t._tid);
    t._tid = setTimeout(() => { t.style.opacity = '0'; }, 2500);
}

// =========================================================
// RENDER — INVENTORY
// =========================================================
function renderInventory() {
    const dGrid = document.getElementById('desktop-frag-grid');
    if (!dGrid) return;
    dGrid.innerHTML = '';
    let hasAny = false;
    for (const defId in invFragments) {
        const def = NODE_DEFS[defId];
        if (!def || def.isSystem) continue;
        for (const partIdx in invFragments[defId]) {
            if ((invFragments[defId][partIdx] || 0) <= 0) continue;
            hasAny = true;
            const el = document.createElement('div');
            el.className = `grid-item ${def.typeClass}-border`;
            el.innerHTML = `
                <div class="item-count">${invFragments[defId][partIdx]}</div>
                <div class="item-icon" style="color:${def.color}">${def.icon}</div>
                <div class="item-title">${def.title.replace('()', '')}</div>
                <div class="item-line-lbl">Line ${parseInt(partIdx) + 1}</div>
            `;
            el.onclick = () => injectFragmentToIDE(defId, parseInt(partIdx));
            dGrid.appendChild(el);
        }
    }
    if (!hasAny) {
        dGrid.innerHTML = '<div style="color:var(--text-dim);font-size:10px;font-style:italic;padding:8px 4px;">No fragments in inventory.<br>Earn them by breaching nodes.</div>';
    }
}

// =========================================================
// RENDER — STASH
// =========================================================
function renderStash() {
    const grid = document.getElementById('stash-grid');
    if (!grid) return;
    grid.innerHTML = '';
    stashNodes.forEach((node, idx) => {
        const def = NODE_DEFS[node.defId];
        const el  = document.createElement('div');
        el.className = `grid-item ${def.typeClass}-border`;
        el.innerHTML = `
            <div class="item-tier">T${node.tier}</div>
            <div class="item-icon" style="color:${def.color}">${def.icon}</div>
            <div class="item-title">${def.title.replace('()', '')}</div>
        `;
        el.onclick = () => {
            const tx = (-camX + window.innerWidth  / 2) / camScale - 90;
            const ty = (-camY + window.innerHeight / 2) / camScale - 50;
            deployNodeToCanvas(node.defId, node.tier, tx, ty);
            stashNodes.splice(idx, 1);
            renderStash(); closeMobileDrawer();
        };
        el.addEventListener('contextmenu', e => {
            e.preventDefault();
            const mIdx = stashNodes.findIndex((n, i) => i !== idx && n.defId === node.defId && n.tier === node.tier);
            if (mIdx > -1) {
                stashNodes[idx].tier++;
                stashNodes.splice(mIdx, 1);
                renderStash();
                logConsole(`> Upgraded ${def.title} → Tier ${stashNodes[idx]?.tier}`);
            }
        });
        grid.appendChild(el);
    });
}

// =========================================================
// RENDER — MACROS
// =========================================================
function renderMacros() {
    const list = document.getElementById('macro-list');
    if (!list) return;
    list.innerHTML = '';
    MACROS.forEach(m => {
        const canAfford = canAffordMacro(m.reqs);
        const el = document.createElement('div');
        el.className = `macro-item ${canAfford ? '' : 'disabled'}`;
        let reqHtml = '<div class="macro-reqs">';
        m.reqs.forEach(r => {
            const d    = NODE_DEFS[r];
            const have = stashNodes.some(n => n.defId === r);
            reqHtml += `<span style="color:${have ? 'var(--neon-green)' : '#555'}">${have ? '[✓]' : '[x]'} ${d.title}</span><br>`;
        });
        reqHtml += '</div>';
        el.innerHTML = `<div class="macro-title">${m.title}</div><div class="macro-desc">${m.desc}</div>${reqHtml}`;
        el.onclick = canAfford
            ? () => {
                const sx = (-camX + window.innerWidth  / 2) / camScale;
                const sy = (-camY + window.innerHeight / 2) / camScale;
                m.exec(sx, sy);
                updateWires(); renderStash(); renderMacros(); closeMobileDrawer();
              }
            : () => showToast('MISSING REQUIRED NODES');
        list.appendChild(el);
    });
}

function canAffordMacro(reqs) {
    const sc = {}, rc = {};
    stashNodes.forEach(n => { sc[n.defId] = (sc[n.defId] || 0) + 1; });
    reqs.forEach(r       => { rc[r]        = (rc[r]        || 0) + 1; });
    for (const req in rc) { if ((sc[req] || 0) < rc[req]) return false; }
    return true;
}

function popStashNode(defId) {
    let bestIdx = -1, bestTier = -1;
    stashNodes.forEach((n, i) => { if (n.defId === defId && n.tier > bestTier) { bestTier = n.tier; bestIdx = i; } });
    return bestIdx > -1 ? stashNodes.splice(bestIdx, 1)[0] : null;
}

// =========================================================
// IDE — BLUEPRINT LIST
// =========================================================
function renderBlueprintList() {
    const list = document.getElementById('blueprint-list');
    if (!list) return;

    // Preserve active selection across re-renders
    const activeDef = document.querySelector('.blueprint-item.active')?.dataset?.def || null;
    list.innerHTML = '';

    for (const key in NODE_DEFS) {
        const def = NODE_DEFS[key];
        if (def.isSystem) continue;

        const totalLines  = def.codeLines?.length || 0;
        const draft       = blueprintDrafts[key] || [];
        const filledLines = draft.filter(Boolean).length;
        // Count inventory frags available for unfilled lines
        const fragMap     = invFragments[key] || {};
        const fragCount   = Object.values(fragMap).reduce((s, v) => s + (v || 0), 0);
        const pct         = totalLines > 0 ? (filledLines / totalLines) * 100 : 0;
        const inProgress  = filledLines > 0 && filledLines < totalLines;
        const complete    = filledLines === totalLines && totalLines > 0;
        const hasFrags    = fragCount > 0 && !complete;

        const el = document.createElement('div');
        el.className = 'blueprint-item';
        if (key === activeDef) el.classList.add('active');
        el.dataset.def = key;

        // Progress bar background fills behind the text
        let progressStyle = '';
        if (complete) {
            progressStyle = 'background: linear-gradient(90deg, rgba(57,255,20,0.12) 100%, transparent 100%);';
        } else if (inProgress) {
            progressStyle = `background: linear-gradient(90deg, rgba(237,197,49,0.14) ${pct}%, transparent ${pct}%);`;
        }

        // Status badge
        let badge = '';
        if (complete) {
            badge = `<span class="bp-badge bp-complete">✓</span>`;
        } else if (inProgress) {
            badge = `<span class="bp-badge bp-progress">${filledLines}/${totalLines}</span>`;
        } else if (hasFrags) {
            badge = `<span class="bp-badge bp-hasfrags">${fragCount}🔷</span>`;
        }

        el.style.cssText += progressStyle;
        // Split icon and name into separate spans so CSS can stack them on mobile
        el.innerHTML = `<span class="bp-icon-title"><span class="icon-part">${def.icon}</span><span class="name-part">${def.title}</span></span>${badge}`;
        el.onclick = () => openBlueprint(key, el);
        list.appendChild(el);
    }
}

function openBlueprint(defId, el) {
    if (isCompiling) return;
    document.querySelectorAll('.blueprint-item').forEach(i => i.classList.remove('active'));
    if (el) el.classList.add('active');
    activeBlueprint = defId;
    const def = NODE_DEFS[defId];
    document.getElementById('ide-title').textContent  = def.title;
    document.getElementById('ide-title').style.color  = def.color;
    document.getElementById('ide-status').textContent = 'AWAITING FRAGMENTS...';
    renderIDECode();
    logConsole(`> Loaded blueprint: ${def.title}.`);
    const fragMap = invFragments[defId] || {};
    const missing = def.codeLines.some((_, i) => !blueprintDrafts[defId]?.[i] && !(fragMap[i] > 0));
    if (missing) logConsole('> WARNING: Insufficient fragments detected.');

    // Populate the right-panel inspector with this blueprint's info
    document.getElementById('inspector-default').style.display = 'none';
    document.getElementById('inspector-content').style.display = 'flex';
    document.getElementById('insp-title').textContent  = def.title;
    document.getElementById('insp-title').style.color  = def.color;
    document.getElementById('insp-tier').textContent   = 'BLUEPRINT';
    document.getElementById('insp-desc').textContent   = def.desc || '';

    if (def.statName) {
        // Show what this node will do when compiled and connected
        const base  = PLAYER_STATS[def.statBase] || 0;
        const mod   = def.baseMod;
        document.getElementById('insp-stat-name').textContent = def.statName.toUpperCase();
        document.getElementById('insp-base').textContent      = base.toFixed(1);
        document.getElementById('insp-mod').textContent       = '+' + mod.toFixed(1);
        document.getElementById('insp-total').textContent     = (base + mod).toFixed(1);
        document.getElementById('insp-stats').style.display   = 'block';
    } else {
        document.getElementById('insp-stats').style.display   = 'none';
    }

    const lines   = Array.isArray(def.codeLines) ? def.codeLines : [];
    document.getElementById('insp-code').innerHTML = lines.join('\n');
}

function renderIDECode() {
    if (!activeBlueprint) return;
    const def    = NODE_DEFS[activeBlueprint];
    const draft  = blueprintDrafts[activeBlueprint] || [];
    const editor = document.getElementById('ide-editor');
    editor.innerHTML = '';
    def.codeLines.forEach((lineHtml, i) => {
        const container = document.createElement('div');
        container.className = 'ide-line-container';
        const lineNum = document.createElement('div');
        lineNum.className = 'ide-line-num';
        lineNum.textContent = i + 1;
        const lineEl = document.createElement('div');
        lineEl.id        = `ide-line-${i}`;
        lineEl.className = `ide-line ${draft[i] ? 'filled' : 'ghost'}`;
        lineEl.innerHTML = def.statName
            ? lineHtml.replace('{BASE}', PLAYER_STATS[def.statBase].toFixed(1)).replace('{MOD}', def.baseMod.toFixed(1))
            : lineHtml;
        container.appendChild(lineNum);
        container.appendChild(lineEl);
        editor.appendChild(container);
    });
}

function injectFragmentToIDE(defId, partIdx, skipCompileCheck = false) {
    if (isCompiling) return;
    if (activeBlueprint !== defId) {
        openBlueprint(defId, document.querySelector(`.blueprint-item[data-def="${defId}"]`));
    }
    if (blueprintDrafts[defId]?.[partIdx]) { showToast(`Line ${partIdx + 1} already compiled.`); return; }
    if (!invFragments[defId]?.[partIdx]) { showToast('NO FRAGMENT FOR THIS LINE'); return; }

    invFragments[defId][partIdx]--;
    renderInventory();
    renderBlueprintList(); // update progress badges
    if (!blueprintDrafts[defId]) blueprintDrafts[defId] = new Array(NODE_DEFS[defId].codeLines.length).fill(false);
    blueprintDrafts[defId][partIdx] = true;

    const lineEl = document.getElementById(`ide-line-${partIdx}`);
    if (lineEl) {
        lineEl.classList.remove('ghost', 'typing', 'filled');
        void lineEl.offsetWidth;
        lineEl.classList.add('typing');
        lineEl.addEventListener('animationend', () => {
            lineEl.classList.remove('typing'); lineEl.classList.add('filled');
        }, { once: true });
    }
    logConsole(`> Injected fragment → Line ${partIdx + 1}.`);
    compilerAutoSave();

    if (!skipCompileCheck && blueprintDrafts[defId].every(v => v === true)) {
        isCompiling = true;
        document.getElementById('ide-status').textContent = 'COMPILING...';
        setTimeout(() => runCompileSequence(defId), 800);
    }
}

function autoFillIDE() {
    if (!activeBlueprint || isCompiling) return;
    const defId   = activeBlueprint;
    const fragMap = invFragments[defId] || {};
    const anyAvailable = NODE_DEFS[defId].codeLines.some((_, i) => !blueprintDrafts[defId]?.[i] && (fragMap[i] || 0) > 0);
    if (!anyAvailable) { logConsole('> ERROR: No fragments for this blueprint.'); showToast('NO FRAGMENTS AVAILABLE'); return; }
    let missing = false;
    for (let i = 0; i < NODE_DEFS[defId].codeLines.length; i++) {
        if (!blueprintDrafts[defId]?.[i]) {
            if ((fragMap[i] || 0) > 0) injectFragmentToIDE(defId, i, true);
            else missing = true;
        }
    }
    if (missing) { logConsole('> WARNING: Some fragments still missing.'); showToast('INCOMPLETE FRAGMENTS'); }
    if (blueprintDrafts[defId].every(v => v === true)) {
        isCompiling = true;
        document.getElementById('ide-status').textContent = 'COMPILING...';
        setTimeout(() => runCompileSequence(defId), 800);
    }
}

function runCompileSequence(defId) {
    logConsole('> Initiating compile sequence...');
    setTimeout(() => logConsole('> Syntax check: OK.'),  300);
    setTimeout(() => logConsole('> Link pass: OK.'),      600);
    setTimeout(() => {
        document.getElementById('ide-status').textContent = 'SUCCESS';
        stashNodes.push({ id: 'sn_' + Math.random().toString(36).substr(2, 6), defId, tier: 0 });
        renderStash(); renderMacros();
        blueprintDrafts[defId].fill(false);
        isCompiling = false;
        compilerAutoSave();
        document.getElementById('comp-modal-title').textContent = `${NODE_DEFS[defId].title} COMPILED`;
        document.getElementById('compile-modal-overlay').style.display = 'flex';
    }, 1000);
}

function logConsole(msg) {
    const cons = document.getElementById('ide-console');
    if (!cons) return;
    const div = document.createElement('div');
    div.textContent = msg;
    cons.appendChild(div);
    cons.scrollTop = cons.scrollHeight;
}

function closeCompileModal() {
    document.getElementById('compile-modal-overlay').style.display = 'none';
    renderIDECode();
}

// =========================================================
// CANVAS — DEPLOY NODE
// =========================================================
function deployNodeToCanvas(defId, tier, x, y, isSystem = false, forceId = null) {
    const def  = NODE_DEFS[defId];
    const node = {
        id: forceId || ('n_' + Math.random().toString(36).substr(2, 6)),
        defId, tier, x, y, element: null, isSystem
    };

    const el = document.createElement('div');
    el.className = `ws-node ${def.typeClass}`;
    el.style.left   = node.x + 'px';
    el.style.top    = node.y + 'px';
    el.style.zIndex = ws_nodes.length + 10;

    const inHTML  = def.inputs.map(p =>
        `<div class="port-row">
            <div class="port ${p.type}" data-node="${node.id}" data-port="${p.id}" data-io="in" data-type="${p.type}"></div>
            <span>${p.label}</span>
        </div>`
    ).join('');
    const outHTML = def.outputs.map(p =>
        `<div class="port-row">
            <span>${p.label}</span>
            <div class="port ${p.type}" data-node="${node.id}" data-port="${p.id}" data-io="out" data-type="${p.type}"></div>
        </div>`
    ).join('');

    el.innerHTML = `
        <div class="node-header">
            <span>${def.icon} ${def.title}</span>
            <div style="display:flex;align-items:center;gap:4px;">
                ${isSystem ? '' : `<span style="color:#445;font-size:9px;letter-spacing:1px;">T${tier}</span>`}
                ${isSystem ? '' : `<span class="node-close" onclick="deleteNodeFromCanvas('${node.id}')">×</span>`}
            </div>
        </div>
        <div class="node-body">
            <div class="port-group">${inHTML}</div>
            <div class="port-group port-out-group">${outHTML}</div>
        </div>
    `;

    node.element = el;
    if (nLayer) nLayer.appendChild(el);
    ws_nodes.push(node);

    let _downX = 0, _downY = 0, _didDrag = false;
    const onNodeDown = e => {
        if (e.target.classList.contains('node-close')) return;
        const c = getPointerCoords(e);
        _downX = c.x; _downY = c.y; _didDrag = false;
        if (e.target.closest('.node-header')) {
            e.stopPropagation();
            draggedNode  = node;
            const r      = el.getBoundingClientRect();
            dragOffset.x = (c.x - r.left) / camScale;
            dragOffset.y = (c.y - r.top)  / camScale;
        }
    };
    const onNodeMove = e => {
        if (!_didDrag) {
            const c = getPointerCoords(e);
            if (Math.hypot(c.x - _downX, c.y - _downY) > 6) _didDrag = true;
        }
    };
    const onNodeUp = e => {
        if (drawingWire) return;
        if (!_didDrag && !e.target.classList.contains('node-close')) selectNodeCanvas(node);
    };
    el.addEventListener('mousedown',  onNodeDown);
    el.addEventListener('touchstart', onNodeDown,  { passive: true });
    el.addEventListener('mousemove',  onNodeMove);
    el.addEventListener('touchmove',  onNodeMove,  { passive: true });
    el.addEventListener('mouseup',    onNodeUp);
    el.addEventListener('touchend',   onNodeUp,    { passive: true });
    el.querySelectorAll('.port').forEach(p => {
        const onPortDown = e => { e.stopPropagation(); startWireDrag(p); };
        p.addEventListener('mousedown',  onPortDown);
        p.addEventListener('touchstart', onPortDown, { passive: false });
    });

    if (!isSystem) compilerAutoSave();
    return node;
}

function deleteNodeFromCanvas(nodeId) {
    const idx = ws_nodes.findIndex(n => n.id === nodeId);
    if (idx > -1 && !ws_nodes[idx].isSystem) {
        stashNodes.push({ id: 'sn_' + Math.random().toString(36).substr(2, 6), defId: ws_nodes[idx].defId, tier: ws_nodes[idx].tier });
        renderStash(); renderMacros();
        ws_connections = ws_connections.filter(c => c.fromNode !== nodeId && c.toNode !== nodeId);
        ws_nodes[idx].element.remove();
        ws_nodes.splice(idx, 1);
        updateWires(); selectNodeCanvas(null);
        compilerAutoSave();
    }
}

function selectNodeCanvas(node) {
    selectedNode = node;
    document.querySelectorAll('.ws-node').forEach(n => n.classList.remove('selected'));
    if (!node) {
        document.getElementById('right-panel').classList.remove('open');
        document.getElementById('inspector-default').style.display  = 'block';
        document.getElementById('inspector-content').style.display  = 'none';
        return;
    }
    node.element.classList.add('selected');
    document.getElementById('right-panel').classList.add('open');
    document.getElementById('inspector-default').style.display = 'none';
    document.getElementById('inspector-content').style.display = 'flex';

    const def = NODE_DEFS[node.defId];
    document.getElementById('insp-title').textContent  = def.title;
    document.getElementById('insp-title').style.color  = def.color;
    document.getElementById('insp-tier').textContent   = node.isSystem ? 'SYS' : 'T' + node.tier;
    document.getElementById('insp-desc').textContent   = def.desc || '';
    const lines   = Array.isArray(def.codeLines) ? def.codeLines : [];
    const rawCode = lines.join('\n');
    if (def.statName && !node.isSystem) {
        const base  = PLAYER_STATS[def.statBase] || 0;
        const mod   = def.baseMod * (1 + node.tier * 0.5);
        const total = base + mod;
        document.getElementById('insp-stat-name').textContent = def.statName.toUpperCase();
        document.getElementById('insp-base').textContent      = base.toFixed(1);
        document.getElementById('insp-mod').textContent       = '+' + mod.toFixed(1);
        document.getElementById('insp-total').textContent     = total.toFixed(1);
        document.getElementById('insp-stats').style.display   = 'block';
        document.getElementById('insp-code').innerHTML = rawCode.replace('{BASE}', base.toFixed(1)).replace('{MOD}', mod.toFixed(1));
    } else {
        document.getElementById('insp-stats').style.display = 'none';
        document.getElementById('insp-code').innerHTML      = rawCode;
    }
}

// =========================================================
// CANVAS POINTER EVENTS
// =========================================================
function getPointerCoords(e) {
    return (e.touches && e.touches.length > 0)
        ? { x: e.touches[0].clientX, y: e.touches[0].clientY }
        : { x: e.clientX, y: e.clientY };
}

// ── Pinch-to-zoom state ────────────────────────────────────
let _pinchActive   = false;
let _pinchDist0    = 0;
let _pinchScale0   = 1;
let _pinchMidX     = 0;
let _pinchMidY     = 0;

function _touchDist(e) {
    const dx = e.touches[0].clientX - e.touches[1].clientX;
    const dy = e.touches[0].clientY - e.touches[1].clientY;
    return Math.hypot(dx, dy);
}
function _touchMid(e) {
    return {
        x: (e.touches[0].clientX + e.touches[1].clientX) / 2,
        y: (e.touches[0].clientY + e.touches[1].clientY) / 2,
    };
}

function onCanvasPointerDown(e) {
    // Two-finger touch → pinch zoom, never sever/pan
    if (e.touches && e.touches.length === 2) {
        e.preventDefault();
        _cancelSeverCheck();
        _pinchActive = true;
        isPanning    = false;
        _pinchDist0  = _touchDist(e);
        _pinchScale0 = camScale;
        const mid    = _touchMid(e);
        _pinchMidX   = mid.x;
        _pinchMidY   = mid.y;
        return;
    }

    const isBackground = e.target === ws_area
        || e.target.id === 'canvas-inner'
        || e.target.id === 'wire-layer'
        || (e.target.tagName === 'path' && e.target.closest('#wire-layer'));
    if (isBackground) {
        const c = getPointerCoords(e);
        // Sever only on mouse; on touch use longer hold (250ms) to avoid false triggers
        const severDelay = e.touches ? 250 : 120;
        _startSeverCheck(c.x, c.y, severDelay);
        isPanning = true; selectNodeCanvas(null);
        panStartX = c.x - camX; panStartY = c.y - camY;
    }
}

function onGlobalPointerMove(e) {
    if (!document.getElementById('screen-compiler')?.classList.contains('active')) return;

    // Pinch zoom takes priority
    if (_pinchActive && e.touches && e.touches.length === 2) {
        e.preventDefault();
        const newDist  = _touchDist(e);
        const newMid   = _touchMid(e);
        const z        = newDist / _pinchDist0;
        const newScale = Math.max(0.2, Math.min(_pinchScale0 * z, 4.0));

        // Zoom around the midpoint between fingers
        const r  = ws_area.getBoundingClientRect();
        const tx = (_pinchMidX - r.left - camX) / camScale;
        const ty = (_pinchMidY - r.top  - camY) / camScale;
        camScale = newScale;
        camX = (_pinchMidX - r.left) - tx * camScale;
        camY = (_pinchMidY - r.top)  - ty * camScale;

        // Also pan with finger midpoint drift
        const dx = newMid.x - _pinchMidX;
        const dy = newMid.y - _pinchMidY;
        camX += dx; camY += dy;
        _pinchMidX = newMid.x; _pinchMidY = newMid.y;

        updateCanvasTransform();
        return;
    }

    const c = getPointerCoords(e);
    if (_severActive) { e.preventDefault(); _addSeverPoint(c.x, c.y); return; }
    if (isPanning) {
        e.preventDefault(); _cancelSeverCheck();
        camX = c.x - panStartX; camY = c.y - panStartY;
        updateCanvasTransform();
    } else if (draggedNode) {
        e.preventDefault(); _cancelSeverCheck();
        const r = ws_area.getBoundingClientRect();
        draggedNode.x = (c.x - r.left - camX) / camScale - dragOffset.x;
        draggedNode.y = (c.y - r.top  - camY) / camScale - dragOffset.y;
        draggedNode.element.style.left = draggedNode.x + 'px';
        draggedNode.element.style.top  = draggedNode.y + 'px';
        updateWires();
    } else if (drawingWire) {
        e.preventDefault(); _cancelSeverCheck();
        const r  = ws_area.getBoundingClientRect();
        const tx = (c.x - r.left - camX) / camScale;
        const ty = (c.y - r.top  - camY) / camScale;
        wLayer.innerHTML = ''; redrawExistingWires();
        const s = getPortPos(wireStartNode.id, wireStartPort.dataset.port);
        if (s) drawBez(s.x, s.y, tx, ty, wireStartPort.dataset.type, 'temp', true);
    }
}

function onGlobalPointerUp(e) {
    // End pinch
    if (_pinchActive && (!e.touches || e.touches.length < 2)) {
        _pinchActive = false;
        updateWires();
        return;
    }

    _cancelSeverCheck();
    if (_severActive) { _commitSever(); isPanning = false; return; }
    const wasDraggingNode = !!draggedNode;
    isPanning = false; draggedNode = null;
    if (wasDraggingNode) compilerAutoSave();
    if (!drawingWire) return;

    const clientX = e.changedTouches ? e.changedTouches[0].clientX : e.clientX;
    const clientY = e.changedTouches ? e.changedTouches[0].clientY : e.clientY;
    if (!ws_area) return;
    const wsRect  = ws_area.getBoundingClientRect();
    const canvasX = (clientX - wsRect.left - camX) / camScale;
    const canvasY = (clientY - wsRect.top  - camY) / camScale;

    let bestPort = null, bestDist = Infinity;
    const exactEl = document.elementFromPoint(clientX, clientY);
    if (exactEl?.classList.contains('port') && exactEl.dataset.io === 'in') bestPort = exactEl;
    if (!bestPort) {
        const SNAP_R = 80;
        for (const node of ws_nodes) {
            if (wireStartNode && node.id === wireStartNode.id) continue;
            const def = NODE_DEFS[node.defId];
            if (!def.inputs?.length) continue;
            for (const portDef of def.inputs) {
                const portEl = node.element.querySelector(`[data-port="${portDef.id}"][data-io="in"]`);
                if (!portEl) continue;
                const pos  = getPortCanvasPos(portEl);
                const dist = Math.hypot(canvasX - pos.x, canvasY - pos.y);
                if (dist < SNAP_R && dist < bestDist) { bestDist = dist; bestPort = portEl; }
            }
        }
    }
    if (bestPort) finishWireDrag(bestPort);
    else { drawingWire = false; wireStartPort = null; wireStartNode = null; updateWires(); }
}

function onCanvasWheel(e) {
    e.preventDefault();
    const z = e.deltaY > 0 ? 0.9 : 1.1;
    const r = ws_area.getBoundingClientRect();
    const tx = (e.clientX - r.left - camX) / camScale;
    const ty = (e.clientY - r.top  - camY) / camScale;
    camScale = Math.max(0.2, Math.min(camScale * z, 4.0));
    camX = (e.clientX - r.left) - tx * camScale;
    camY = (e.clientY - r.top)  - ty * camScale;
    updateCanvasTransform(); updateWires();
}

function updateCanvasTransform() {
    if (canvasInner) canvasInner.style.transform = `translate(${camX}px, ${camY}px) scale(${camScale})`;
}

// ── Swipe-to-sever ─────────────────────────────────────────
let _severActive = false, _severPath = [], _severEl = null, _severHoldTimer = null;

function _startSeverCheck(clientX, clientY, delay = 120) {
    _severHoldTimer = setTimeout(() => {
        _severActive = true; _severPath = [];
        const wsRect = ws_area?.getBoundingClientRect();
        if (!wsRect) return;
        _severPath.push({
            x: (clientX - wsRect.left - camX) / camScale,
            y: (clientY - wsRect.top  - camY) / camScale
        });
        if (ws_area) ws_area.style.cursor = 'crosshair';
    }, delay);
}
function _cancelSeverCheck() { clearTimeout(_severHoldTimer); _severHoldTimer = null; }
function _addSeverPoint(clientX, clientY) {
    if (!_severActive || !ws_area) return;
    const wsRect = ws_area.getBoundingClientRect();
    _severPath.push({ x: (clientX - wsRect.left - camX) / camScale, y: (clientY - wsRect.top - camY) / camScale });
    _drawSeverLine();
}
function _drawSeverLine() {
    if (_severEl) _severEl.remove();
    if (_severPath.length < 2) return;
    const pts  = _severPath.map(p => `${p.x},${p.y}`).join(' ');
    const poly = document.createElementNS('http://www.w3.org/2000/svg', 'polyline');
    poly.setAttribute('points', pts);
    poly.setAttribute('stroke', 'rgba(255,0,127,0.7)');
    poly.setAttribute('stroke-width', '2');
    poly.setAttribute('stroke-dasharray', '6 3');
    poly.setAttribute('fill', 'none');
    poly.setAttribute('pointer-events', 'none');
    if (wLayer) wLayer.appendChild(poly);
    _severEl = poly;
}
function _commitSever() {
    if (!_severActive) return;
    _severActive = false;
    if (ws_area) ws_area.style.cursor = '';
    if (_severEl) { _severEl.remove(); _severEl = null; }
    if (_severPath.length < 2) { _severPath = []; return; }
    const severed = new Set();
    for (let si = 0; si < _severPath.length - 1; si++) {
        const s1 = _severPath[si], s2 = _severPath[si + 1];
        for (const conn of ws_connections) {
            if (severed.has(conn.id)) continue;
            const src = getPortPos(conn.fromNode, conn.fromPort);
            const dst = getPortPos(conn.toNode,   conn.toPort);
            if (!src || !dst) continue;
            const N = 40, off = Math.max(Math.abs(dst.x - src.x) * 0.5, 50);
            let prev = null;
            for (let t = 0; t <= N; t++) {
                const u = t / N, u1 = 1 - u;
                const bx = u1**3*src.x + 3*u1**2*u*(src.x+off) + 3*u1*u**2*(dst.x-off) + u**3*dst.x;
                const by = u1**3*src.y + 3*u1**2*u*src.y       + 3*u1*u**2*dst.y       + u**3*dst.y;
                const cur = { x: bx, y: by };
                if (prev && _segmentsIntersect(s1, s2, prev, cur)) { severed.add(conn.id); break; }
                prev = cur;
            }
        }
    }
    if (severed.size > 0) {
        ws_connections = ws_connections.filter(c => !severed.has(c.id));
        updateWires(); compilerAutoSave();
        showToast(severed.size === 1 ? 'WIRE SEVERED' : `${severed.size} WIRES SEVERED`);
    }
    _severPath = [];
}
function _segmentsIntersect(a1, a2, b1, b2) {
    const d1x = a2.x-a1.x, d1y = a2.y-a1.y, d2x = b2.x-b1.x, d2y = b2.y-b1.y;
    const cross = d1x*d2y - d1y*d2x;
    if (Math.abs(cross) < 1e-10) return false;
    const dx = b1.x-a1.x, dy = b1.y-a1.y;
    const t = (dx*d2y - dy*d2x)/cross, u = (dx*d1y - dy*d1x)/cross;
    return t >= 0 && t <= 1 && u >= 0 && u <= 1;
}

// ── Wiring ──────────────────────────────────────────────────
function startWireDrag(portEl) {
    if (portEl.dataset.io !== 'out') return;
    drawingWire = true;
    wireStartPort = portEl;
    wireStartNode = ws_nodes.find(n => n.id === portEl.dataset.node);
    updateWires();
}
function drawBez(x1, y1, x2, y2, cls, id, isTemp = false) {
    const off      = Math.max(Math.abs(x2 - x1) * 0.5, 50);
    const pathData = `M ${x1} ${y1} C ${x1+off} ${y1}, ${x2-off} ${y2}, ${x2} ${y2}`;
    const path     = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', pathData);
    path.setAttribute('class', `wire ${cls}${isTemp ? ' temp' : ''}`);
    if (!isTemp) {
        path.addEventListener('contextmenu', e => {
            e.preventDefault();
            ws_connections = ws_connections.filter(c => c.id !== id);
            updateWires(); compilerAutoSave();
        });
    }
    if (wLayer) wLayer.appendChild(path);
}
// Semantic compatibility check — returns null if valid, error string if not.
function getWireCompatError(fromDefId, toDefId) {
    const fromCat = fromDefId.split('_')[0]; // sys, event, flow, action
    const toCat   = toDefId.split('_')[0];

    // Terminal: nothing connects OUT of sys_out
    if (fromDefId === 'sys_out')
        return 'WAN_Out is a terminal — nothing connects from it.';

    // sys_in can connect to anything except another sys_in
    if (fromDefId === 'sys_in' && toDefId === 'sys_in')
        return 'Cannot connect System to itself.';

    // Events must connect TO actions or flow — not to other events or sys_out
    if (fromCat === 'event' && toCat === 'event')
        return 'Events cannot chain. Connect to an action or flow node.';
    if (fromCat === 'event' && toDefId === 'sys_out')
        return 'Event nodes cannot wire directly to WAN_Out. Connect to an action first.';

    // Actions cannot connect TO events (wrong direction)
    if (fromCat === 'action' && toCat === 'event')
        return 'Actions cannot trigger events. Events are inputs, not outputs.';

    // Flow nodes must connect to actions, not directly to sys_out or events
    if (fromCat === 'flow' && toDefId === 'sys_out')
        return 'Flow nodes route to actions — connect to an action node, not WAN_Out.';
    if (fromCat === 'flow' && toCat === 'event')
        return 'Flow nodes cannot wire into events.';

    // sys_in should not connect directly to sys_out (pointless passthrough)
    if (fromDefId === 'sys_in' && toDefId === 'sys_out')
        return 'Direct System→WAN_Out does nothing. Add action nodes between them.';

    return null; // valid
}

function finishWireDrag(targetPortEl) {
    if (!drawingWire) return;
    drawingWire = false;
    if (!targetPortEl) { updateWires(); return; }
    const fromType = wireStartPort.dataset.type;
    const toType   = targetPortEl.dataset.type;
    const isInput  = targetPortEl.dataset.io === 'in';
    let wireAdded  = false;
    if (isInput && fromType === toType && wireStartNode.id !== targetPortEl.dataset.node) {
        const targetNode = ws_nodes.find(n => n.id === targetPortEl.dataset.node);

        // Semantic validation
        const compatError = getWireCompatError(wireStartNode.defId, targetNode?.defId || '');
        if (compatError) {
            showToast(compatError);
            wireStartPort = null; wireStartNode = null;
            updateWires();
            return;
        }

        if (targetNode?.defId !== 'sys_out') {
            ws_connections = ws_connections.filter(c =>
                !(c.toNode === targetPortEl.dataset.node && c.toPort === targetPortEl.dataset.port)
            );
        }
        ws_connections.push({
            id: 'conn_' + Math.random().toString(36).substr(2, 6),
            fromNode: wireStartNode.id, fromPort: wireStartPort.dataset.port,
            toNode: targetPortEl.dataset.node, toPort: targetPortEl.dataset.port,
            type: fromType
        });
        wireAdded = true;
    }
    wireStartPort = null; wireStartNode = null;
    updateWires();
    if (wireAdded) compilerAutoSave();
}
function getPortPos(nId, pId) {
    const n = ws_nodes.find(nd => nd.id === nId);
    if (!n) return null;
    const pEl = n.element.querySelector(`[data-port="${pId}"]`);
    if (!pEl) return null;
    // Walk up offsetParent chain to get offset relative to the node root element
    let ox = pEl.offsetWidth / 2, oy = pEl.offsetHeight / 2;
    let el = pEl;
    while (el && el !== n.element) {
        ox += el.offsetLeft;
        oy += el.offsetTop;
        el = el.offsetParent;
    }
    return { x: n.x + ox, y: n.y + oy };
}
function getPortCanvasPos(portEl) {
    const r = portEl.getBoundingClientRect();
    const wsRect = ws_area.getBoundingClientRect();
    return {
        x: (r.left + r.width/2  - wsRect.left - camX) / camScale,
        y: (r.top  + r.height/2 - wsRect.top  - camY) / camScale
    };
}
function redrawExistingWires() {
    ws_connections.forEach(conn => {
        const s = getPortPos(conn.fromNode, conn.fromPort);
        const e = getPortPos(conn.toNode,   conn.toPort);
        if (s && e) drawBez(s.x, s.y, e.x, e.y, conn.type, conn.id);
        document.querySelector(`[data-node="${conn.fromNode}"][data-port="${conn.fromPort}"]`)?.classList.add('connected');
        document.querySelector(`[data-node="${conn.toNode}"][data-port="${conn.toPort}"]`)?.classList.add('connected');
    });
}
function updateWires() {
    if (!wLayer) return;
    wLayer.innerHTML = ''; redrawExistingWires();
    document.querySelectorAll('.port').forEach(p => {
        const wired = ws_connections.some(c =>
            (c.fromNode === p.dataset.node && c.fromPort === p.dataset.port) ||
            (c.toNode   === p.dataset.node && c.toPort   === p.dataset.port)
        );
        if (!wired) p.classList.remove('connected');
    });
}

// =========================================================
// SAVE / LOAD
// =========================================================
const SAVE_VERSION = HB_SAVE_VER;
let _suppressAutoSave = false, _autoSaveTimer = null;

function compilerAutoSave() {
    if (_suppressAutoSave) return;
    clearTimeout(_autoSaveTimer);
    _autoSaveTimer = setTimeout(() => {
        try {
            const raw = hbLoadRaw() || {};
            hbSaveRaw({ ...raw, ...buildCompilerPayload() });
            updateSettingsTimestamp();
        } catch (err) { console.warn('Auto-save failed:', err); }
    }, 400);
}

function buildCompilerPayload() {
    const systemNodePos = {};
    ws_nodes.filter(n => n.isSystem).forEach(n => { systemNodePos[n.id] = { x: n.x, y: n.y }; });
    return {
        invFragments:    JSON.parse(JSON.stringify(invFragments)),
        stashNodes:      JSON.parse(JSON.stringify(stashNodes)),
        blueprintDrafts: JSON.parse(JSON.stringify(blueprintDrafts)),
        systemNodePos,
        wsNodes: ws_nodes.filter(n => !n.isSystem).map(n => ({ id: n.id, defId: n.defId, tier: n.tier, x: n.x, y: n.y })),
        wsConnections: JSON.parse(JSON.stringify(ws_connections)),
        camX, camY, camScale
    };
}

function saveState() {
    clearTimeout(_autoSaveTimer);
    try {
        const raw = hbLoadRaw() || {};
        const compPayload = ws_area ? buildCompilerPayload() : {};
        hbSaveRaw({ ...raw, ...compPayload });
    } catch (err) { showToast('SAVE FAILED — STORAGE FULL?'); return; }
    updateSettingsTimestamp();
    const btn = document.getElementById('btn-save');
    if (btn) { btn.classList.add('save-flash'); btn.addEventListener('animationend', () => btn.classList.remove('save-flash'), { once: true }); }
    if (ws_area) logConsole('> Build saved to local storage.');
    showToast('BUILD SAVED');
}

function loadState() {
    const raw = hbLoadRaw();
    if (!raw) { showToast('NO SAVE FOUND'); return; }

    // If compiler canvas not initialized, just restore flat state
    if (!ws_area) {
        invFragments   = raw.invFragments   || {};
        stashNodes     = raw.stashNodes     || stashNodes;
        blueprintDrafts = raw.blueprintDrafts || {};
        savedFragments = raw.savedFragments || 0;
        savedData      = raw.savedData      || 0;
        savedXp        = raw.savedXp        || 0;
        updateSettingsTimestamp(raw.savedAt);
        closeSettings(); showToast('BUILD LOADED');
        updateTitleSaveInfo(); return;
    }

    try {
        invFragments    = raw.invFragments    || {};
        stashNodes      = raw.stashNodes      || [];
        blueprintDrafts = raw.blueprintDrafts || {};
        for (const key in NODE_DEFS) {
            if (!NODE_DEFS[key].isSystem && !blueprintDrafts[key]) {
                blueprintDrafts[key] = new Array(NODE_DEFS[key].codeLines.length).fill(false);
            }
        }
        // Re-apply system positions
        const savedSysPos = raw.systemNodePos || {};
        ws_nodes.filter(n => n.isSystem).forEach(n => {
            const pos = savedSysPos[n.id];
            if (pos) { n.x = pos.x; n.y = pos.y; n.element.style.left = pos.x+'px'; n.element.style.top = pos.y+'px'; }
        });
        ws_nodes.filter(n => !n.isSystem).forEach(n => n.element.remove());
        ws_nodes = ws_nodes.filter(n => n.isSystem);
        ws_connections = [];
        const idMap = {};
        ws_nodes.forEach(n => { idMap[n.id] = n.id; });
        (raw.wsNodes || []).forEach(nd => {
            const fresh = deployNodeToCanvas(nd.defId, nd.tier, nd.x, nd.y, false);
            idMap[nd.id] = fresh.id;
        });
        (raw.wsConnections || []).forEach(c => {
            const from = idMap[c.fromNode] ?? c.fromNode;
            const to   = idMap[c.toNode]   ?? c.toNode;
            if (ws_nodes.find(n => n.id === from) && ws_nodes.find(n => n.id === to)) {
                ws_connections.push({ ...c, id: 'conn_' + Math.random().toString(36).substr(2,6), fromNode: from, toNode: to });
            }
        });
        camX = raw.camX ?? 0; camY = raw.camY ?? 0; camScale = raw.camScale ?? 1;
        updateCanvasTransform(); updateWires();
        renderInventory(); renderStash(); renderMacros(); renderBlueprintList();
        if (activeBlueprint && blueprintDrafts[activeBlueprint]) renderIDECode();
        updateSettingsTimestamp(raw.savedAt);
        closeSettings(); showToast('BUILD LOADED'); logConsole('> Build loaded.');
    } catch (err) { showToast('LOAD FAILED — CORRUPT DATA'); console.error(err); }
}

function clearSave() {
    if (!confirm('Clear all save data and reset to defaults?')) return;
    localStorage.removeItem(HB_SAVE_KEY);
    location.reload();
}

function updateSettingsTimestamp(ts) {
    const el = document.getElementById('settings-save-time');
    if (!el) return;
    const d = ts ? new Date(ts) : new Date();
    el.textContent = d.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
}

function openSettings() {
    document.getElementById('settings-overlay').classList.add('open');
    updateSettingsTimestamp((hbLoadRaw() || {}).savedAt);
}
function closeSettings() { document.getElementById('settings-overlay').classList.remove('open'); }
function onSettingsBackdrop(e) { if (e.target === document.getElementById('settings-overlay')) closeSettings(); }

// =========================================================
// BOOT
// =========================================================
window.addEventListener('DOMContentLoaded', () => {
    showScreen('title');
    updateTitleSaveInfo();
});
