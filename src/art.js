'use strict';
// ============ ARTE PROCEDURAL (estilo vectorial con brillo) ============
const PAL = {
  bg0: '#050814', bg1: '#0b1330', hull: '#d4dcea', hullDark: '#5a6680', hullMid: '#98a6bf',
  accent: '#3de8ff', cockpit: '#a8f6ff', flame0: '#fff2c0', flame1: '#ffb347', flame2: '#ff4d2a',
  enemy: '#ff4d6d', enemyDark: '#5a1a2a', enemyMid: '#b83450', military: '#9bbf6a', militaryDark: '#34462a',
};

// ---------- Fondo de estrellas ----------
function makeStars(n, w, h, seed) {
  let s = seed || 1;
  const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
  const out = [];
  for (let i = 0; i < n; i++) out.push({ x: r() * w, y: r() * h, z: 0.2 + r() * 0.8, t: r() * TAU, c: r() });
  return out;
}
const STARS = makeStars(420, 2000, 2000, 7);

function drawSpaceBg(ctx, W, H, camX, camY, t, tint) {
  const g = ctx.createRadialGradient(W * 0.5, H * 0.45, 0, W * 0.5, H * 0.5, Math.max(W, H) * 0.8);
  g.addColorStop(0, tint || PAL.bg1);
  g.addColorStop(1, PAL.bg0);
  ctx.fillStyle = g;
  ctx.fillRect(0, 0, W, H);
  // nebulosas suaves
  ctx.globalCompositeOperation = 'lighter';
  const neb = [[0.2, 0.3, '#3a1f6b'], [0.8, 0.7, '#0f3f5e'], [0.65, 0.15, '#4a1540']];
  for (const [nx, ny, c] of neb) {
    const x = ((nx * W - camX * 0.03) % (W * 1.4) + W * 1.4) % (W * 1.4) - W * 0.2;
    const y = ((ny * H - camY * 0.03) % (H * 1.4) + H * 1.4) % (H * 1.4) - H * 0.2;
    const rg = ctx.createRadialGradient(x, y, 0, x, y, Math.max(W, H) * 0.45);
    rg.addColorStop(0, c + '55');
    rg.addColorStop(1, c + '00');
    ctx.fillStyle = rg;
    ctx.fillRect(0, 0, W, H);
  }
  ctx.globalCompositeOperation = 'source-over';
  for (const s of STARS) {
    const px = ((s.x - camX * s.z * 0.25) % 2000 + 2000) % 2000;
    const py = ((s.y - camY * s.z * 0.25) % 2000 + 2000) % 2000;
    for (let ox = 0; ox < W; ox += 2000) for (let oy = 0; oy < H; oy += 2000) {
      const x = px + ox, y = py + oy;
      if (x > W || y > H) continue;
      const tw = 0.55 + 0.45 * Math.sin(t * 1.5 + s.t);
      ctx.globalAlpha = s.z * tw;
      ctx.fillStyle = s.c > 0.85 ? '#ffd9a8' : s.c > 0.7 ? '#a8d4ff' : '#ffffff';
      const sz = s.z > 0.85 ? 2 : 1.2;
      ctx.fillRect(x, y, sz, sz);
    }
  }
  ctx.globalAlpha = 1;
}

function glow(ctx, x, y, r, color, a) {
  const g = ctx.createRadialGradient(x, y, 0, x, y, r);
  g.addColorStop(0, color);
  g.addColorStop(1, 'rgba(0,0,0,0)');
  ctx.globalAlpha = a == null ? 1 : a;
  ctx.globalCompositeOperation = 'lighter';
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill();
  ctx.globalCompositeOperation = 'source-over';
  ctx.globalAlpha = 1;
}

// ---------- Planetas ----------
function drawPlanet(ctx, x, y, r, loc, lightAng, t) {
  const [c0, c1] = loc.col;
  // atmósfera
  glow(ctx, x, y, r * 1.9, c0 + '66', 0.7);
  if (loc.ring) drawRing(ctx, x, y, r, c0, true);
  const lx = x + Math.cos(lightAng) * r * 0.5, ly = y + Math.sin(lightAng) * r * 0.5;
  const g = ctx.createRadialGradient(lx, ly, r * 0.1, x, y, r);
  g.addColorStop(0, c0);
  g.addColorStop(1, c1);
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill();
  if (loc.bands) {
    ctx.save();
    ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.clip();
    for (let i = -3; i <= 3; i++) {
      ctx.fillStyle = i % 2 ? c1 + '55' : '#ffffff18';
      ctx.fillRect(x - r, y + i * r * 0.26 - r * 0.07, r * 2, r * 0.13);
    }
    if (loc.id === 'jupiter') {
      ctx.fillStyle = '#c4553388';
      ctx.beginPath(); ctx.ellipse(x + r * 0.3, y + r * 0.35, r * 0.2, r * 0.11, 0, 0, TAU); ctx.fill();
    }
    ctx.restore();
  }
  if (loc.id === 'tierra') {
    ctx.save();
    ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.clip();
    ctx.fillStyle = '#4fbf6a';
    const rot = (t || 0) * 0.05;
    for (let i = 0; i < 4; i++) {
      const a = rot + i * 1.7;
      const cx = x + Math.cos(a) * r * 0.55, cy = y + Math.sin(i * 2.1) * r * 0.45;
      ctx.beginPath(); ctx.ellipse(cx, cy, r * 0.32, r * 0.2, i, 0, TAU); ctx.fill();
    }
    ctx.fillStyle = '#ffffff55';
    ctx.beginPath(); ctx.ellipse(x - r * 0.2, y - r * 0.3, r * 0.5, r * 0.08, 0.3, 0, TAU); ctx.fill();
    ctx.restore();
  }
  // lado nocturno
  const dx = x - Math.cos(lightAng) * r * 0.9, dy = y - Math.sin(lightAng) * r * 0.9;
  const sh = ctx.createRadialGradient(dx, dy, 0, dx, dy, r * 1.5);
  sh.addColorStop(0, 'rgba(0,0,10,0.75)');
  sh.addColorStop(0.6, 'rgba(0,0,10,0.25)');
  sh.addColorStop(1, 'rgba(0,0,10,0)');
  ctx.fillStyle = sh;
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill();
  // borde iluminado
  ctx.strokeStyle = c0 + 'aa'; ctx.lineWidth = Math.max(1, r * 0.06);
  ctx.beginPath(); ctx.arc(x, y, r, lightAng - 1.2, lightAng + 1.2); ctx.stroke();
  if (loc.ring) drawRing(ctx, x, y, r, c0, false);
}
function drawRing(ctx, x, y, r, c, back) {
  ctx.save();
  ctx.translate(x, y); ctx.rotate(-0.35);
  ctx.beginPath();
  if (back) ctx.rect(-r * 3, -r * 3, r * 6, r * 3);
  else ctx.rect(-r * 3, 0, r * 6, r * 3);
  ctx.clip();
  for (let i = 0; i < 3; i++) {
    ctx.strokeStyle = i === 1 ? c + '99' : c + '55';
    ctx.lineWidth = r * (i === 1 ? 0.22 : 0.12);
    ctx.beginPath(); ctx.ellipse(0, 0, r * (1.55 + i * 0.3), r * (0.42 + i * 0.08), 0, 0, TAU); ctx.stroke();
  }
  ctx.restore();
}

function drawSun(ctx, x, y, r, t) {
  glow(ctx, x, y, r * 7, '#ff8a2a55', 0.6);
  glow(ctx, x, y, r * 3.2, '#ffc56a', 0.55);
  const g = ctx.createRadialGradient(x, y, 0, x, y, r);
  g.addColorStop(0, '#fffbe6'); g.addColorStop(0.6, '#ffe07a'); g.addColorStop(1, '#ff9d2a');
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill();
  ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < 12; i++) {
    const a = i / 12 * TAU + t * 0.05;
    const l = r * (1.5 + 0.3 * Math.sin(t * 2 + i));
    ctx.strokeStyle = 'rgba(255,200,100,0.12)'; ctx.lineWidth = r * 0.25;
    ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * r, y + Math.sin(a) * r); ctx.lineTo(x + Math.cos(a) * l, y + Math.sin(a) * l); ctx.stroke();
  }
  ctx.globalCompositeOperation = 'source-over';
}

// ---------- Nave del jugador (procedural según mejoras) ----------
// Apunta hacia +x. s = escala (1 ≈ 30px de largo en nivel 1)
function drawPlayerShip(ctx, lv, x, y, ang, s, thrust, t) {
  const H = lv.hull, E = lv.engine, W = lv.weapons, L = lv.laser;
  ctx.save();
  ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s, s);
  const len = 16 + H * 5;          // media longitud
  const wid = 8 + H * 2.2;
  const nEng = 1 + Math.floor((E - 1) / 2) + (H >= 4 ? 1 : 0);
  // llamas
  if (thrust > 0) {
    ctx.globalCompositeOperation = 'lighter';
    for (let i = 0; i < nEng; i++) {
      const oy = (i - (nEng - 1) / 2) * (wid * 0.55);
      const fl = (10 + E * 4) * thrust * (0.85 + 0.3 * Math.sin(t * 40 + i * 2));
      const g = ctx.createLinearGradient(-len, 0, -len - fl, 0);
      g.addColorStop(0, PAL.flame0); g.addColorStop(0.3, PAL.flame1); g.addColorStop(1, 'rgba(255,77,42,0)');
      ctx.fillStyle = g;
      ctx.beginPath();
      ctx.moveTo(-len + 2, oy - 3.2); ctx.quadraticCurveTo(-len - fl * 0.6, oy, -len - fl, oy);
      ctx.quadraticCurveTo(-len - fl * 0.6, oy, -len + 2, oy + 3.2); ctx.fill();
    }
    ctx.globalCompositeOperation = 'source-over';
  }
  // alas / radiadores
  ctx.fillStyle = PAL.hullDark;
  ctx.beginPath();
  ctx.moveTo(len * 0.1, 0);
  ctx.lineTo(-len * 0.55, -wid * (1.1 + H * 0.08));
  ctx.lineTo(-len * 0.85, -wid * (1.1 + H * 0.08));
  ctx.lineTo(-len * 0.7, 0);
  ctx.lineTo(-len * 0.85, wid * (1.1 + H * 0.08));
  ctx.lineTo(-len * 0.55, wid * (1.1 + H * 0.08));
  ctx.closePath(); ctx.fill();
  ctx.fillStyle = PAL.accent;
  ctx.fillRect(-len * 0.8, -wid * (1.1 + H * 0.08) - 1, len * 0.22, 2);
  ctx.fillRect(-len * 0.8, wid * (1.1 + H * 0.08) - 1, len * 0.22, 2);
  // módulos de carga
  const pods = H - 1;
  for (let i = 0; i < pods; i++) {
    const px = -len * 0.45 + i * (len * 0.8 / Math.max(1, pods)) * 0.9;
    for (const sgn of [-1, 1]) {
      ctx.fillStyle = PAL.hullMid;
      roundRect(ctx, px - 5, sgn * wid * 0.62 - 4.5, 10, 9, 2); ctx.fill();
      ctx.fillStyle = PAL.hullDark;
      ctx.fillRect(px - 5, sgn * wid * 0.62 - 0.6, 10, 1.2);
    }
  }
  // motores
  for (let i = 0; i < nEng; i++) {
    const oy = (i - (nEng - 1) / 2) * (wid * 0.55);
    ctx.fillStyle = PAL.hullDark;
    roundRect(ctx, -len - 2, oy - 4, 9, 8, 2); ctx.fill();
    ctx.fillStyle = thrust > 0 ? PAL.flame1 : '#334';
    ctx.fillRect(-len - 2.5, oy - 2.5, 2, 5);
  }
  // casco principal
  const g = ctx.createLinearGradient(0, -wid, 0, wid);
  g.addColorStop(0, '#f2f6ff'); g.addColorStop(0.5, PAL.hull); g.addColorStop(1, PAL.hullMid);
  ctx.fillStyle = g;
  ctx.beginPath();
  ctx.moveTo(len, 0);
  ctx.quadraticCurveTo(len * 0.6, -wid * 0.55, 0, -wid * 0.6);
  ctx.lineTo(-len, -wid * 0.45);
  ctx.lineTo(-len, wid * 0.45);
  ctx.lineTo(0, wid * 0.6);
  ctx.quadraticCurveTo(len * 0.6, wid * 0.55, len, 0);
  ctx.fill();
  ctx.strokeStyle = PAL.hullDark; ctx.lineWidth = 1; ctx.stroke();
  // franja de acento
  ctx.fillStyle = PAL.accent;
  ctx.beginPath();
  ctx.moveTo(len * 0.55, -1.2); ctx.lineTo(-len * 0.9, -1.2); ctx.lineTo(-len * 0.9, 1.2); ctx.lineTo(len * 0.55, 1.2);
  ctx.fill();
  // cabina
  ctx.fillStyle = PAL.cockpit;
  ctx.beginPath(); ctx.ellipse(len * 0.45, 0, len * 0.18, wid * 0.22, 0, 0, TAU); ctx.fill();
  ctx.fillStyle = '#ffffff';
  ctx.beginPath(); ctx.ellipse(len * 0.5, -wid * 0.08, len * 0.06, wid * 0.07, 0, 0, TAU); ctx.fill();
  // torretas
  const tur = W - 1;
  for (let i = 0; i < tur; i++) {
    const tx = len * 0.1 - i * len * 0.35, ty = (i % 2 ? 1 : -1) * wid * 0.35;
    ctx.fillStyle = '#ff934a';
    ctx.beginPath(); ctx.arc(tx, ty, 2.6, 0, TAU); ctx.fill();
    ctx.fillStyle = PAL.hullDark; ctx.fillRect(tx, ty - 0.8, 6, 1.6);
  }
  // emisor láser
  ctx.fillStyle = laserColor(L);
  ctx.beginPath(); ctx.arc(len - 1, 0, 1.8 + L * 0.3, 0, TAU); ctx.fill();
  ctx.restore();
}
function laserColor(L) { return ['#3de8ff', '#5dffb0', '#ffe14d', '#ff7a3d', '#ff4dff'][L - 1] || '#3de8ff'; }
function shipLen(lv) { return 16 + lv.hull * 5; }

function roundRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y); ctx.lineTo(x + w - r, y); ctx.quadraticCurveTo(x + w, y, x + w, y + r);
  ctx.lineTo(x + w, y + h - r); ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
  ctx.lineTo(x + r, y + h); ctx.quadraticCurveTo(x, y + h, x, y + h - r);
  ctx.lineTo(x, y + r); ctx.quadraticCurveTo(x, y, x + r, y);
}

// ---------- Naves enemigas ----------
function drawEnemyShip(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type];
  const mil = e.military;
  const main = mil ? PAL.military : PAL.enemyMid, dark = mil ? PAL.militaryDark : PAL.enemyDark, lit = mil ? '#d8f0a8' : PAL.enemy;
  ctx.save();
  ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s * e.size, s * e.size);
  // llama
  ctx.globalCompositeOperation = 'lighter';
  const fl = 10 + 3 * Math.sin(t * 30);
  ctx.fillStyle = mil ? '#9fe0ff' : '#ff6a3a';
  ctx.beginPath(); ctx.moveTo(-14, -3); ctx.lineTo(-14 - fl, 0); ctx.lineTo(-14, 3); ctx.fill();
  ctx.globalCompositeOperation = 'source-over';
  ctx.fillStyle = dark;
  ctx.beginPath();
  ctx.moveTo(6, 0); ctx.lineTo(-10, -16); ctx.lineTo(-16, -16); ctx.lineTo(-8, 0); ctx.lineTo(-16, 16); ctx.lineTo(-10, 16);
  ctx.closePath(); ctx.fill();
  ctx.fillStyle = main;
  ctx.beginPath();
  ctx.moveTo(20, 0); ctx.lineTo(-4, -7); ctx.lineTo(-15, -5); ctx.lineTo(-15, 5); ctx.lineTo(-4, 7);
  ctx.closePath(); ctx.fill();
  ctx.strokeStyle = dark; ctx.lineWidth = 1; ctx.stroke();
  ctx.fillStyle = lit;
  ctx.beginPath(); ctx.moveTo(14, 0); ctx.lineTo(4, -2.5); ctx.lineTo(4, 2.5); ctx.fill();
  if (type === 'frigate' || type === 'carrier') {
    ctx.fillStyle = dark;
    ctx.fillRect(-12, -11, 12, 4); ctx.fillRect(-12, 7, 12, 4);
    ctx.fillStyle = lit;
    ctx.fillRect(-2, -10, 3, 2); ctx.fillRect(-2, 8, 3, 2);
  }
  if (type === 'carrier') {
    ctx.fillStyle = main;
    roundRect(ctx, -10, -4, 16, 8, 2); ctx.fill();
    ctx.fillStyle = '#ffd24a'; ctx.fillRect(-6, -1, 8, 2);
  }
  ctx.restore();
}

// ---------- Asteroides ----------
function makeRockShape(n, jag) {
  const pts = [];
  for (let i = 0; i < n; i++) {
    const a = i / n * TAU;
    pts.push([Math.cos(a), Math.sin(a), 1 - jag + Math.random() * jag * 2]);
  }
  return pts;
}
function drawRock(ctx, a, t, scanLv) {
  const ore = ITEMS[a.ore];
  ctx.save();
  ctx.translate(a.x, a.y); ctx.rotate(a.rot);
  if (a.rich) glow(ctx, 0, 0, a.r * 2.2, ore.c + '66', 0.5 + 0.25 * Math.sin(t * 3 + a.x));
  const g = ctx.createRadialGradient(-a.r * 0.3, -a.r * 0.3, a.r * 0.1, 0, 0, a.r * 1.1);
  g.addColorStop(0, a.cold ? '#8d9bb8' : '#8a7e72');
  g.addColorStop(1, a.cold ? '#2a3348' : '#2e2924');
  ctx.fillStyle = g;
  ctx.beginPath();
  a.shape.forEach((p, i) => {
    const px = p[0] * a.r * p[2], py = p[1] * a.r * p[2];
    i ? ctx.lineTo(px, py) : ctx.moveTo(px, py);
  });
  ctx.closePath(); ctx.fill();
  if (a.hit > 0) { ctx.fillStyle = 'rgba(255,240,220,0.22)'; ctx.fill(); }
  ctx.strokeStyle = 'rgba(255,255,255,0.12)'; ctx.lineWidth = 1.5; ctx.stroke();
  // vetas de mineral
  ctx.fillStyle = ore.c;
  for (const v of a.veins) {
    ctx.globalAlpha = 0.85;
    ctx.beginPath(); ctx.arc(v[0] * a.r, v[1] * a.r, v[2] * a.r, 0, TAU); ctx.fill();
  }
  ctx.globalAlpha = 1;
  // cráteres
  ctx.fillStyle = 'rgba(0,0,0,0.25)';
  for (const c of a.craters) { ctx.beginPath(); ctx.arc(c[0] * a.r, c[1] * a.r, c[2] * a.r, 0, TAU); ctx.fill(); }
  ctx.restore();
  if (scanLv >= 2 && a.rich) {
    ctx.strokeStyle = ore.c; ctx.globalAlpha = 0.5 + 0.3 * Math.sin(t * 4);
    ctx.setLineDash([4, 4]); ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.arc(a.x, a.y, a.r + 8, 0, TAU); ctx.stroke();
    ctx.setLineDash([]); ctx.globalAlpha = 1;
  }
}

function drawOreChunk(ctx, c, t) {
  const col = ITEMS[c.ore].c;
  glow(ctx, c.x, c.y, 18, col + 'aa', 0.7);
  ctx.save(); ctx.translate(c.x, c.y); ctx.rotate(c.rot + t); ctx.scale(1.45, 1.45);
  ctx.fillStyle = col;
  ctx.beginPath(); ctx.moveTo(0, -5); ctx.lineTo(4, 0); ctx.lineTo(0, 5); ctx.lineTo(-4, 0); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#fff'; ctx.globalAlpha = 0.7;
  ctx.beginPath(); ctx.moveTo(0, -5); ctx.lineTo(1.5, -1); ctx.lineTo(-1.5, -1); ctx.fill();
  ctx.restore(); ctx.globalAlpha = 1;
}

// ---------- Estación espacial (icono en mapa) ----------
function drawStationIcon(ctx, x, y, s, col, t) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(t * 0.4);
  ctx.strokeStyle = col; ctx.lineWidth = 1.5;
  ctx.beginPath(); ctx.arc(0, 0, s, 0, TAU); ctx.stroke();
  for (let i = 0; i < 4; i++) {
    const a = i * TAU / 4;
    ctx.beginPath(); ctx.moveTo(Math.cos(a) * s * 0.3, Math.sin(a) * s * 0.3); ctx.lineTo(Math.cos(a) * s, Math.sin(a) * s); ctx.stroke();
  }
  ctx.fillStyle = col;
  ctx.beginPath(); ctx.arc(0, 0, s * 0.3, 0, TAU); ctx.fill();
  ctx.restore();
}

// ---------- Partículas ----------
class Particles {
  constructor() { this.list = []; }
  add(x, y, vx, vy, life, col, size, glowy) { this.list.push({ x, y, vx, vy, life, max: life, col, size, glowy }); }
  burst(x, y, n, col, spd, life, size) {
    for (let i = 0; i < n; i++) {
      const a = Math.random() * TAU, v = spd * (0.3 + Math.random() * 0.7);
      this.add(x, y, Math.cos(a) * v, Math.sin(a) * v, life * (0.5 + Math.random() * 0.5), col, size * (0.5 + Math.random()), true);
    }
  }
  update(dt) {
    for (const p of this.list) { p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= 0.98; p.vy *= 0.98; p.life -= dt; }
    this.list = this.list.filter(p => p.life > 0);
    if (this.list.length > 900) this.list.splice(0, this.list.length - 900);
  }
  draw(ctx) {
    ctx.globalCompositeOperation = 'lighter';
    for (const p of this.list) {
      const k = p.life / p.max;
      ctx.globalAlpha = k;
      ctx.fillStyle = p.col;
      ctx.beginPath(); ctx.arc(p.x, p.y, p.size * (0.4 + k * 0.6), 0, TAU); ctx.fill();
    }
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = 'source-over';
  }
}
