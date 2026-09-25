'use strict';
// ============ PROCEDURAL ART (glowing vector style) ============
const PAL = {
  bg0: '#03050f', bg1: '#0a1230',
  enemy: '#ff4d6d', enemyDark: '#4a1422', enemyMid: '#b83450', military: '#9bbf6a', militaryDark: '#34462a',
};

// ---------- noise ----------
function hash2(x, y, s) {
  let h = (x * 374761393 + y * 668265263 + s * 1442695041) | 0;
  h = Math.imul(h ^ (h >>> 13), 1274126177);
  return ((h ^ (h >>> 16)) >>> 0) / 4294967295;
}
function vnoise(x, y, s, P) {
  const xi = Math.floor(x), yi = Math.floor(y), xf = x - xi, yf = y - yi;
  const u = xf * xf * (3 - 2 * xf), v = yf * yf * (3 - 2 * yf);
  const m = k => ((k % P) + P) % P;
  const a = hash2(m(xi), yi, s), b = hash2(m(xi + 1), yi, s), c = hash2(m(xi), yi + 1, s), d = hash2(m(xi + 1), yi + 1, s);
  return a + (b - a) * u + (c - a) * v + (a - b - c + d) * u * v;
}
// tileable horizontally with period P (in noise units at base frequency)
function fbm(x, y, s, P, oct) {
  let v = 0, amp = 0.5, f = 1, norm = 0;
  for (let i = 0; i < (oct || 4); i++) { v += amp * vnoise(x * f, y * f, s + i * 31, P * f); norm += amp; f *= 2; amp *= 0.5; }
  return v / norm;
}
function hexRgb(h) { const n = parseInt(h.slice(1), 16); return [(n >> 16) & 255, (n >> 8) & 255, n & 255]; }
function mixc(a, b, t) { return [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t]; }
function ramp(stops, t) {
  t = clamp(t, 0, 1);
  for (let i = 1; i < stops.length; i++) if (t <= stops[i][0]) {
    const [t0, c0] = stops[i - 1], [t1, c1] = stops[i];
    return mixc(c0, c1, (t - t0) / (t1 - t0 || 1));
  }
  return stops[stops.length - 1][1];
}

// ---------- backdrop (pre-rendered, tileable nebula) ----------
const BD = 512;
let backdrop = null;
function makeBackdrop() {
  const c = document.createElement('canvas'); c.width = BD; c.height = BD;
  const x = c.getContext('2d');
  const img = x.createImageData(BD, BD);
  const P = 4;
  for (let j = 0; j < BD; j++) for (let i = 0; i < BD; i++) {
    const u = i / BD * P, v = j / BD * P;
    const n1 = fbm(u, v, 11, P, 5), n2 = fbm(u + 3.1, v + 1.7, 29, P, 4), n3 = fbm(u * 2, v * 2, 47, P * 2, 3);
    let col = [5, 8, 22];
    const purple = Math.pow(clamp((n1 - 0.45) * 2.6, 0, 1), 1.6);
    const teal = Math.pow(clamp((n2 - 0.5) * 2.8, 0, 1), 1.7);
    const pink = Math.pow(clamp((n3 - 0.58) * 3, 0, 1), 2);
    col = mixc(col, [58, 28, 110], purple * 0.85);
    col = mixc(col, [16, 78, 110], teal * 0.7);
    col = mixc(col, [120, 30, 90], pink * 0.5);
    const k = (j * BD + i) * 4;
    img.data[k] = col[0]; img.data[k + 1] = col[1]; img.data[k + 2] = col[2]; img.data[k + 3] = 255;
  }
  x.putImageData(img, 0, 0);
  // faint dust stars baked in
  let s = 5; const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
  for (let i = 0; i < 900; i++) {
    x.globalAlpha = 0.15 + r() * 0.45;
    x.fillStyle = r() > 0.8 ? '#ffe6c8' : r() > 0.6 ? '#bcd8ff' : '#ffffff';
    x.fillRect(r() * BD, r() * BD, 1, 1);
  }
  x.globalAlpha = 1;
  backdrop = c;
}
function makeStars(n, w, h, seed) {
  let s = seed || 1;
  const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
  const out = [];
  for (let i = 0; i < n; i++) out.push({ x: r() * w, y: r() * h, z: 0.25 + r() * 0.75, t: r() * TAU, c: r() });
  return out;
}
const STARS = makeStars(260, 2000, 2000, 7);

function drawSpaceBg(ctx, W, H, camX, camY, t, tint) {
  if (!backdrop) makeBackdrop();
  const sc = 2.2, tw = BD * sc;
  const ox = -(((camX * 0.06) % tw) + tw) % tw, oy = -(((camY * 0.06) % tw) + tw) % tw;
  ctx.imageSmoothingEnabled = true;
  for (let x = ox; x < W; x += tw) for (let y = oy; y < H; y += tw) ctx.drawImage(backdrop, x, y, tw, tw);
  if (tint) { ctx.globalAlpha = 0.35; ctx.fillStyle = tint; ctx.fillRect(0, 0, W, H); ctx.globalAlpha = 1; }
  // vignette
  const g = ctx.createRadialGradient(W / 2, H / 2, Math.min(W, H) * 0.3, W / 2, H / 2, Math.max(W, H) * 0.75);
  g.addColorStop(0, 'rgba(0,0,0,0)'); g.addColorStop(1, 'rgba(0,0,6,0.55)');
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
  for (const s of STARS) {
    const px = ((s.x - camX * s.z * 0.25) % 2000 + 2000) % 2000;
    const py = ((s.y - camY * s.z * 0.25) % 2000 + 2000) % 2000;
    for (let ox2 = 0; ox2 < W; ox2 += 2000) for (let oy2 = 0; oy2 < H; oy2 += 2000) {
      const x = px + ox2, y = py + oy2;
      if (x > W || y > H) continue;
      const twk = 0.55 + 0.45 * Math.sin(t * 1.5 + s.t);
      ctx.globalAlpha = s.z * twk;
      ctx.fillStyle = s.c > 0.85 ? '#ffd9a8' : s.c > 0.7 ? '#a8d4ff' : '#ffffff';
      if (s.z > 0.9) {
        ctx.fillRect(x - 0.5, y - 2, 1, 4); ctx.fillRect(x - 2, y - 0.5, 4, 1);
      } else ctx.fillRect(x, y, s.z > 0.6 ? 1.6 : 1, s.z > 0.6 ? 1.6 : 1);
    }
  }
  ctx.globalAlpha = 1;
}

function glow(ctx, x, y, r, color, a) {
  if (!(r > 0)) return;
  const g = ctx.createRadialGradient(x, y, 0, x, y, r);
  g.addColorStop(0, color);
  g.addColorStop(1, 'rgba(0,0,0,0)');
  const pa = ctx.globalAlpha;
  ctx.globalAlpha = pa * (a == null ? 1 : a);
  ctx.globalCompositeOperation = 'lighter';
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill();
  ctx.globalCompositeOperation = 'source-over';
  ctx.globalAlpha = pa;
}

// ---------- planet textures ----------
const TEX = {};
const TW = 256, TH = 128;
function planetTex(loc) {
  if (!loc.tex) return null;
  if (TEX[loc.id]) return TEX[loc.id];
  if (loc.id === 'marte' && typeof built === 'function' && built('terraform')) loc = { ...loc, tex: 'marsgreen' };
  const c = document.createElement('canvas'); c.width = TW; c.height = TH;
  const x = c.getContext('2d');
  const img = x.createImageData(TW, TH);
  const seed = loc.id.length * 13 + loc.id.charCodeAt(0);
  const L = hexRgb(loc.col[0]), D = hexRgb(loc.col[1]);
  const P = 6;
  let clouds = null;
  for (let j = 0; j < TH; j++) for (let i = 0; i < TW; i++) {
    const u = i / TW * P, v = j / TH * P / 2;
    const lat = Math.abs(j / TH - 0.5) * 2; // 0 equator .. 1 pole
    const n = fbm(u, v, seed, P, 5);
    let col;
    switch (loc.tex) {
      case 'earth': {
        const land = fbm(u * 4 / 6, v * 4 / 6, seed + 5, 4, 5);
        if (land > 0.575) col = ramp([[0, [78, 150, 70]], [0.5, [120, 150, 70]], [1, [170, 140, 95]]], (land - 0.575) * 4 + (n - 0.5));
        else col = ramp([[0, [10, 40, 110]], [1, [40, 120, 200]]], land * 1.8);
        if (lat > 0.82 + n * 0.1) col = [235, 242, 250];
        break;
      }
      case 'moon': {
        const maria = fbm(u * 4 / 6, v * 4 / 6, seed + 9, 4, 4);
        col = ramp([[0, [70, 70, 78]], [1, [215, 215, 220]]], n * 0.9 + 0.15);
        if (maria < 0.42) col = mixc(col, [70, 72, 82], 0.6);
        break;
      }
      case 'rock': col = mixc(D, L, clamp((n - 0.3) * 1.6, 0, 1)); break;
      case 'marsgreen': {
        const land = fbm(u * 4 / 6, v * 4 / 6, seed + 5, 4, 5);
        if (land > 0.5) col = ramp([[0, [90, 140, 70]], [0.6, [170, 110, 70]], [1, [200, 120, 80]]], (land - 0.5) * 3 + (n - 0.5));
        else col = ramp([[0, [20, 60, 130]], [1, [60, 140, 200]]], land * 1.8);
        if (lat > 0.85) col = [240, 245, 250];
        break;
      }
      case 'mars': {
        const dark = fbm(u * 4 / 6, v * 4 / 6, seed + 3, 4, 4);
        col = ramp([[0, [120, 40, 20]], [0.5, [205, 95, 55]], [1, [240, 150, 100]]], n);
        if (dark < 0.4) col = mixc(col, [90, 35, 25], 0.55);
        if (lat > 0.88) col = [245, 235, 230];
        break;
      }
      case 'venus': {
        const sw = Math.sin(v * 5 + fbm(u, v, seed + 2, P, 4) * 7);
        col = ramp([[0, [168, 121, 59]], [0.5, [230, 200, 140]], [1, [250, 235, 200]]], 0.5 + sw * 0.25 + (n - 0.5) * 0.5);
        break;
      }
      case 'jupiter': case 'saturn': {
        const turb = fbm(u * 1.5, v * 3, seed + 7, P * 1.5, 4);
        const band = Math.sin((j / TH) * (loc.tex === 'jupiter' ? 22 : 16) + turb * 3.2);
        const stops = loc.tex === 'jupiter'
          ? [[0, [140, 80, 50]], [0.35, [205, 150, 100]], [0.6, [240, 220, 190]], [1, [250, 240, 225]]]
          : [[0, [170, 140, 80]], [0.5, [230, 205, 150]], [1, [250, 240, 205]]];
        col = ramp(stops, 0.5 + band * 0.4 + (n - 0.5) * 0.3);
        break;
      }
      case 'europa': {
        const ridge = Math.abs(fbm(u * 8 / 6, v * 8 / 6, seed + 4, 8, 5) - 0.5);
        col = ramp([[0, [200, 185, 160]], [1, [250, 245, 235]]], n);
        if (ridge < 0.025) col = [150, 95, 60];
        break;
      }
      case 'titan': col = ramp([[0, [170, 95, 30]], [1, [245, 180, 90]]], 0.35 + Math.sin(j / TH * 8 + n * 3) * 0.12 + n * 0.4); break;
      case 'pluto': {
        const heart = fbm(u * 4 / 6, v * 4 / 6, seed + 8, 4, 4);
        col = ramp([[0, [110, 70, 55]], [1, [220, 195, 170]]], n);
        if (heart > 0.58) col = mixc(col, [250, 240, 230], 0.75);
        break;
      }
      default: col = mixc(D, L, n);
    }
    const k = (j * TW + i) * 4;
    img.data[k] = col[0]; img.data[k + 1] = col[1]; img.data[k + 2] = col[2]; img.data[k + 3] = 255;
  }
  x.putImageData(img, 0, 0);
  if (loc.tex === 'rock' || loc.tex === 'moon') {
    let s = seed; const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
    for (let i = 0; i < 26; i++) {
      const cx = r() * TW, cy = 10 + r() * (TH - 20), cr = 2 + r() * r() * 12;
      x.fillStyle = 'rgba(0,0,0,0.28)'; x.beginPath(); x.ellipse(cx, cy, cr, cr * 0.9, 0, 0, TAU); x.fill();
      x.strokeStyle = 'rgba(255,255,255,0.18)'; x.lineWidth = 1; x.beginPath(); x.arc(cx - 0.6, cy - 0.6, cr, Math.PI * 0.9, Math.PI * 1.9); x.stroke();
    }
  }
  if (loc.tex === 'jupiter') {
    x.fillStyle = 'rgba(190,80,50,0.85)'; x.beginPath(); x.ellipse(TW * 0.3, TH * 0.64, 13, 7, 0, 0, TAU); x.fill();
    x.strokeStyle = 'rgba(240,190,150,0.6)'; x.lineWidth = 2; x.stroke();
  }
  if (loc.tex === 'earth' || loc.tex === 'marsgreen') {
    clouds = document.createElement('canvas'); clouds.width = TW; clouds.height = TH;
    const cx = clouds.getContext('2d'); const ci = cx.createImageData(TW, TH);
    for (let j = 0; j < TH; j++) for (let i = 0; i < TW; i++) {
      const n = fbm(i / TW * 8, j / TH * P * 0.9, seed + 77, 8, 5);
      const a = clamp((n - 0.52) * 4, 0, 1);
      const k = (j * TW + i) * 4;
      ci.data[k] = ci.data[k + 1] = ci.data[k + 2] = 255; ci.data[k + 3] = a * 220;
    }
    cx.putImageData(ci, 0, 0);
  }
  TEX[loc.id] = { c, clouds };
  return TEX[loc.id];
}
const ATMO = { tierra: '#6fb8ff', venus: '#ffd59a', titan: '#ffb35c', marte: '#ff9a70', jupiter: '#ffd9b0', saturno: '#fff0c0', europa: '#dff4ff' };

function drawPlanet(ctx, x, y, r, loc, lightAng, t) {
  const [c0, c1] = loc.col;
  const atmo = ATMO[loc.id];
  glow(ctx, x, y, r * 1.7, (atmo || c0) + '55', 0.8);
  if (loc.ring) drawRing(ctx, x, y, r, c0, true);
  const tex = planetTex(loc);
  ctx.save();
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.clip();
  if (tex && r > 2.5) {
    const spin = ((t || 0) * 0.012 * (loc.bands || loc.tex === 'jupiter' || loc.tex === 'saturn' ? 1.6 : 1)) % 1;
    const w = r * 4, h = r * 2;
    let ox = x - r * 2 - spin * w;
    ctx.drawImage(tex.c, ox, y - r, w, h); ctx.drawImage(tex.c, ox + w, y - r, w, h);
    if (tex.clouds) {
      const cs = ((t || 0) * 0.018) % 1; ox = x - r * 2 - cs * w;
      ctx.globalAlpha = 0.85; ctx.drawImage(tex.clouds, ox, y - r, w, h); ctx.drawImage(tex.clouds, ox + w, y - r, w, h); ctx.globalAlpha = 1;
    }
  } else {
    const g = ctx.createRadialGradient(x, y, 0, x, y, r); g.addColorStop(0, c0); g.addColorStop(1, c1);
    ctx.fillStyle = g; ctx.fillRect(x - r, y - r, r * 2, r * 2);
  }
  // spherical shading
  const lx = Math.cos(lightAng), ly = Math.sin(lightAng);
  const sh = ctx.createRadialGradient(x + lx * r * 0.45, y + ly * r * 0.45, r * 0.15, x + lx * r * 0.2, y + ly * r * 0.2, r * 1.35);
  sh.addColorStop(0, 'rgba(255,255,255,0.10)');
  sh.addColorStop(0.45, 'rgba(0,0,10,0)');
  sh.addColorStop(0.8, 'rgba(0,0,12,0.72)');
  sh.addColorStop(1, 'rgba(0,0,12,0.92)');
  ctx.fillStyle = sh; ctx.fillRect(x - r, y - r, r * 2, r * 2);
  ctx.restore();
  // atmosphere rim on the lit side
  if (r > 3) {
    ctx.strokeStyle = (atmo || c0) + 'aa'; ctx.lineWidth = clamp(r * 0.06, 1, 5);
    ctx.globalCompositeOperation = 'lighter';
    ctx.beginPath(); ctx.arc(x, y, r - ctx.lineWidth / 2, lightAng - 1.1, lightAng + 1.1); ctx.stroke();
    ctx.globalCompositeOperation = 'source-over';
  }
  if (loc.ring) drawRing(ctx, x, y, r, c0, false);
}
function drawRing(ctx, x, y, r, c, back) {
  ctx.save();
  ctx.translate(x, y); ctx.rotate(-0.35);
  ctx.beginPath();
  if (back) ctx.rect(-r * 3, -r * 3, r * 6, r * 3); else ctx.rect(-r * 3, 0, r * 6, r * 3);
  ctx.clip();
  const rings = [[1.45, 0.1, 0.35], [1.62, 0.16, 0.7], [1.85, 0.2, 0.55], [2.05, 0.08, 0.3], [2.18, 0.06, 0.45]];
  for (const [rr, w, a] of rings) {
    ctx.strokeStyle = c; ctx.globalAlpha = a * (back ? 0.7 : 1); ctx.lineWidth = r * w;
    ctx.beginPath(); ctx.ellipse(0, 0, r * rr, r * rr * 0.28, 0, 0, TAU); ctx.stroke();
  }
  ctx.globalAlpha = 1;
  ctx.restore();
}

function drawSun(ctx, x, y, r, t) {
  glow(ctx, x, y, r * 9, '#ff7a1a33', 0.7);
  glow(ctx, x, y, r * 4, '#ffb04a88', 0.7);
  ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < 16; i++) {
    const a = i / 16 * TAU + t * 0.04 + Math.sin(t * 0.7 + i) * 0.05;
    const l = r * (1.7 + 0.5 * Math.sin(t * 1.3 + i * 2.1));
    const g = ctx.createLinearGradient(x, y, x + Math.cos(a) * l, y + Math.sin(a) * l);
    g.addColorStop(0, 'rgba(255,210,120,0.35)'); g.addColorStop(1, 'rgba(255,150,60,0)');
    ctx.strokeStyle = g; ctx.lineWidth = r * (0.18 + 0.08 * Math.sin(i));
    ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + Math.cos(a) * l, y + Math.sin(a) * l); ctx.stroke();
  }
  ctx.globalCompositeOperation = 'source-over';
  const g = ctx.createRadialGradient(x, y, 0, x, y, r);
  g.addColorStop(0, '#ffffff'); g.addColorStop(0.35, '#fff4c2'); g.addColorStop(0.75, '#ffd060'); g.addColorStop(1, '#ff9a2a');
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill();
  // lens flare
  glow(ctx, x, y, r * 1.5, '#ffffffaa', 0.6);
  ctx.globalCompositeOperation = 'lighter';
  const fl = ctx.createLinearGradient(x - r * 6, y, x + r * 6, y);
  fl.addColorStop(0, 'rgba(255,220,160,0)'); fl.addColorStop(0.5, 'rgba(255,240,200,0.45)'); fl.addColorStop(1, 'rgba(255,220,160,0)');
  ctx.fillStyle = fl; ctx.fillRect(x - r * 6, y - 1, r * 12, 2);
  ctx.globalCompositeOperation = 'source-over';
}

// ---------- player ship: 5 hull designs, details from upgrades ----------
const HULLS = [
  { hull: [[26, 0], [18, -4], [6, -7], [-12, -7], [-18, -4]], wing: [[4, -6], [-8, -17], [-15, -17], [-13, -6]], pods: [], ck: [14, 7, 3.2], tail: -18, tw: 4 },
  { hull: [[30, 0], [22, -5], [8, -9], [-18, -9], [-23, -5]], wing: [[0, -8], [-12, -21], [-20, -21], [-18, -8]], pods: [[-5, -12, 14, 6]], ck: [18, 7.5, 3.6], tail: -23, tw: 5 },
  { hull: [[38, 0], [28, -5.5], [12, -9.5], [-22, -10], [-28, -6]], wing: [[-2, -9], [-16, -28], [-25, -28], [-22, -9]], canard: [[24, -5], [16, -12], [12, -12], [14, -5]], pods: [[3, -13, 14, 6], [-13, -13, 12, 6]], ck: [25, 8, 3.8], tail: -28, tw: 6 },
  { hull: [[46, 0], [36, -7], [16, -12], [-30, -12], [-36, -7]], wing: [[6, -12], [-14, -32], [-28, -32], [-26, -12]], canard: [[30, -7], [20, -16], [14, -16], [18, -7]], pods: [[5, -16, 16, 7], [-12, -16, 14, 7], [-27, -16, 10, 7]], ck: [31, 9, 4.2], tail: -36, tw: 8 },
  { hull: [[58, 0], [46, -8], [24, -16], [-36, -16], [-44, -9]], wing: [[12, -16], [-10, -39], [-34, -39], [-30, -16]], canard: [[38, -8], [26, -20], [18, -20], [22, -8]], pods: [[12, -20, 16, 8], [-4, -20, 14, 8], [-19, -20, 14, 8], [-32, -20, 10, 8]], ck: [42, 10, 4.6], tail: -44, tw: 10, bridge: 1 },
];
const ENGINE_COL = ['#ffb347', '#5fd0ff', '#b58bff', '#9ff3ff', '#ff6bd6'];
function laserColor(L) { return ['#3de8ff', '#5dffb0', '#ffe14d', '#ff7a3d', '#ff4dff'][L - 1] || '#3de8ff'; }
function shipLen(lv) { return HULLS[clamp(lv.hull, 1, 5) - 1].hull[0][0]; }
function mirrorPath(ctx, pts) {
  ctx.beginPath();
  pts.forEach((p, i) => i ? ctx.lineTo(p[0], p[1]) : ctx.moveTo(p[0], p[1]));
  for (let i = pts.length - 1; i >= 0; i--) if (pts[i][1] !== 0 || i === pts.length - 1) ctx.lineTo(pts[i][0], -pts[i][1]);
  ctx.closePath();
}
function polyPath(ctx, pts, sy) {
  ctx.beginPath(); pts.forEach((p, i) => i ? ctx.lineTo(p[0], p[1] * sy) : ctx.moveTo(p[0], p[1] * sy)); ctx.closePath();
}

function drawPlayerShip(ctx, lv, x, y, ang, s, thrust, t) {
  const Hd = HULLS[clamp(lv.hull, 1, 5) - 1];
  const E = lv.engine || 1, W = lv.weapons || 1, Lz = lv.laser || 1;
  const ecol = ENGINE_COL[E - 1];
  ctx.save();
  ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s, s);
  const nEng = E >= 4 ? 3 : E >= 2 ? 2 : 1;
  const engY = i => (i - (nEng - 1) / 2) * (Hd.tw * 1.25);
  // flames
  if (thrust > 0) {
    ctx.globalCompositeOperation = 'lighter';
    for (let i = 0; i < nEng; i++) {
      const oy = engY(i);
      const fl = (12 + E * 4 + lv.hull * 2) * thrust * (0.85 + 0.25 * Math.sin(t * 45 + i * 2));
      const g = ctx.createLinearGradient(Hd.tail, 0, Hd.tail - fl, 0);
      g.addColorStop(0, '#ffffff'); g.addColorStop(0.25, ecol); g.addColorStop(1, 'rgba(0,0,0,0)');
      ctx.fillStyle = g;
      const fw = 2.6 + lv.hull * 0.4;
      ctx.beginPath();
      ctx.moveTo(Hd.tail + 1, oy - fw); ctx.quadraticCurveTo(Hd.tail - fl * 0.5, oy - fw * 0.8, Hd.tail - fl, oy);
      ctx.quadraticCurveTo(Hd.tail - fl * 0.5, oy + fw * 0.8, Hd.tail + 1, oy + fw); ctx.fill();
      glow(ctx, Hd.tail - 2, oy, fw * 4, ecol, 0.7 * thrust);
    }
    ctx.globalCompositeOperation = 'source-over';
  }
  ctx.lineJoin = 'round';
  // wings (both sides)
  for (const sy of [-1, 1]) {
    polyPath(ctx, Hd.wing, -sy);
    const wg = ctx.createLinearGradient(0, 0, 0, Hd.wing[1][1] * -sy);
    wg.addColorStop(0, '#95a2bd'); wg.addColorStop(1, '#4c5770');
    ctx.fillStyle = wg; ctx.fill();
    ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 1; ctx.stroke();
    // leading edge accent
    ctx.strokeStyle = '#3de8ff'; ctx.lineWidth = 1.2;
    ctx.beginPath(); ctx.moveTo(Hd.wing[0][0], Hd.wing[0][1] * -sy); ctx.lineTo(Hd.wing[1][0], Hd.wing[1][1] * -sy); ctx.stroke();
    // panel line on wing
    ctx.strokeStyle = 'rgba(20,28,48,0.5)'; ctx.lineWidth = 0.8;
    const mx = (Hd.wing[0][0] + Hd.wing[3][0]) / 2, my = (Hd.wing[0][1] + Hd.wing[3][1]) / 2;
    ctx.beginPath(); ctx.moveTo(mx, my * -sy); ctx.lineTo((Hd.wing[1][0] + Hd.wing[2][0]) / 2, Hd.wing[1][1] * -sy * 0.92); ctx.stroke();
    // nav lights
    const blink = (Math.sin(t * 5 + (sy > 0 ? 0 : 1.6)) > 0.2);
    const tip = [(Hd.wing[1][0] + Hd.wing[2][0]) / 2, Hd.wing[1][1] * -sy];
    ctx.fillStyle = sy < 0 ? '#ff4d6d' : '#6dff9e';
    ctx.beginPath(); ctx.arc(tip[0], tip[1], 1.3, 0, TAU); ctx.fill();
    if (blink) glow(ctx, tip[0], tip[1], 6, sy < 0 ? '#ff4d6d' : '#6dff9e', 0.9);
    if (Hd.canard) {
      polyPath(ctx, Hd.canard, -sy);
      ctx.fillStyle = '#7d8aa6'; ctx.fill(); ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 1; ctx.stroke();
    }
    // cargo pods
    for (const [px, py, pw, ph] of Hd.pods) {
      const yy = py * -sy;
      const pg = ctx.createLinearGradient(0, yy - ph / 2, 0, yy + ph / 2);
      pg.addColorStop(0, '#d7deeb'); pg.addColorStop(1, '#7d8aa3');
      ctx.fillStyle = pg;
      roundRect(ctx, px - pw / 2, yy - ph / 2, pw, ph, 2); ctx.fill();
      ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 0.8; ctx.stroke();
      ctx.fillStyle = '#ffb347'; ctx.fillRect(px - pw / 2 + 2, yy - 0.7, pw - 4, 1.4);
    }
  }
  // engine nozzles
  for (let i = 0; i < nEng; i++) {
    const oy = engY(i), nh = Hd.tw * 0.95;
    ctx.fillStyle = '#39425a';
    roundRect(ctx, Hd.tail - 3, oy - nh / 2, 8, nh, 2); ctx.fill();
    ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 0.8; ctx.stroke();
    ctx.fillStyle = thrust > 0 ? ecol : '#222a3d';
    ctx.fillRect(Hd.tail - 3.5, oy - nh / 2 + 1.2, 1.8, nh - 2.4);
  }
  // main hull
  const top = Hd.hull.reduce((m, p) => Math.min(m, p[1]), 0);
  mirrorPath(ctx, Hd.hull);
  const hg = ctx.createLinearGradient(0, top, 0, -top);
  hg.addColorStop(0, '#f7f9ff'); hg.addColorStop(0.45, '#cfd8e8'); hg.addColorStop(1, '#6f7c97');
  ctx.fillStyle = hg; ctx.fill();
  ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 1.2; ctx.stroke();
  // panel lines (clipped)
  ctx.save(); mirrorPath(ctx, Hd.hull); ctx.clip();
  ctx.strokeStyle = 'rgba(30,40,70,0.35)'; ctx.lineWidth = 0.7;
  const step = 7 + lv.hull;
  for (let px = Hd.tail + step; px < Hd.hull[0][0] - 6; px += step) { ctx.beginPath(); ctx.moveTo(px, top); ctx.lineTo(px, -top); ctx.stroke(); }
  ctx.beginPath(); ctx.moveTo(Hd.tail, top * 0.5); ctx.lineTo(Hd.hull[0][0], 0); ctx.moveTo(Hd.tail, -top * 0.5); ctx.lineTo(Hd.hull[0][0], 0); ctx.stroke();
  // underside shadow
  const us = ctx.createLinearGradient(0, 0, 0, -top);
  us.addColorStop(0, 'rgba(0,0,20,0)'); us.addColorStop(1, 'rgba(0,0,20,0.25)');
  ctx.fillStyle = us; ctx.fillRect(Hd.tail, 0, Hd.hull[0][0] - Hd.tail, -top);
  ctx.restore();
  // spine accent stripe
  ctx.globalCompositeOperation = 'lighter';
  const sg = ctx.createLinearGradient(Hd.tail, 0, Hd.ck[0], 0);
  sg.addColorStop(0, 'rgba(61,232,255,0.2)'); sg.addColorStop(1, 'rgba(61,232,255,0.95)');
  ctx.fillStyle = sg; ctx.fillRect(Hd.tail + 3, -1.1, Hd.ck[0] - Hd.ck[1] - Hd.tail - 3, 2.2);
  ctx.globalCompositeOperation = 'source-over';
  // bridge tower (capital ship)
  if (Hd.bridge) {
    ctx.fillStyle = '#aeb9cf'; roundRect(ctx, -14, -7, 22, 14, 3); ctx.fill();
    ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 1; ctx.stroke();
    ctx.fillStyle = '#9ff3ff';
    for (let i = 0; i < 4; i++) ctx.fillRect(-11 + i * 5, -2, 3, 4);
  }
  // cockpit
  const [cx, crx, cry] = Hd.ck;
  const cg = ctx.createLinearGradient(cx, -cry, cx, cry);
  cg.addColorStop(0, '#e9fdff'); cg.addColorStop(0.45, '#46dcf5'); cg.addColorStop(1, '#0b4d6a');
  ctx.fillStyle = cg;
  ctx.beginPath(); ctx.ellipse(cx, 0, crx, cry, 0, 0, TAU); ctx.fill();
  ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 1; ctx.stroke();
  ctx.fillStyle = 'rgba(255,255,255,0.85)';
  ctx.beginPath(); ctx.ellipse(cx + crx * 0.25, -cry * 0.4, crx * 0.35, cry * 0.22, -0.15, 0, TAU); ctx.fill();
  // turrets
  const tur = W - 1;
  for (let i = 0; i < tur; i++) {
    const tx = Hd.ck[0] - Hd.ck[1] - 6 - i * ((Hd.ck[0] - Hd.tail) / 5.5), ty = (i % 2 ? 1 : -1) * Math.abs(top) * 0.45;
    ctx.fillStyle = '#4a546c'; ctx.beginPath(); ctx.arc(tx, ty, 3, 0, TAU); ctx.fill();
    ctx.fillStyle = '#ff934a'; ctx.beginPath(); ctx.arc(tx, ty, 1.6, 0, TAU); ctx.fill();
    ctx.fillStyle = '#2b3246'; ctx.fillRect(tx, ty - 0.8, 7, 1.6);
  }
  // laser emitter
  const lc = laserColor(Lz);
  ctx.fillStyle = '#39425a'; ctx.fillRect(Hd.hull[0][0] - 5, -1.8 - Lz * 0.2, 5, 3.6 + Lz * 0.4);
  ctx.fillStyle = lc; ctx.beginPath(); ctx.arc(Hd.hull[0][0] + 0.5, 0, 1.6 + Lz * 0.35, 0, TAU); ctx.fill();
  glow(ctx, Hd.hull[0][0] + 0.5, 0, 6 + Lz * 1.5, lc, 0.8);
  ctx.restore();
}

function roundRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y); ctx.lineTo(x + w - r, y); ctx.quadraticCurveTo(x + w, y, x + w, y + r);
  ctx.lineTo(x + w, y + h - r); ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
  ctx.lineTo(x + r, y + h); ctx.quadraticCurveTo(x, y + h, x, y + h - r);
  ctx.lineTo(x, y + r); ctx.quadraticCurveTo(x, y, x + r, y);
}

// ---------- enemy ships ----------
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

// ---------- asteroids ----------
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

// ---------- station icon ----------
function drawStationIcon(ctx, x, y, s, col, t) {
  glow(ctx, x, y, s * 3.5, col + '88', 0.6);
  ctx.save(); ctx.translate(x, y); ctx.rotate(t * 0.3);
  ctx.fillStyle = '#5a6a8a';
  ctx.fillRect(-s * 2.2, -s * 0.35, s * 4.4, s * 0.7);
  ctx.fillStyle = '#3d7fd6';
  ctx.fillRect(-s * 2.4, -s * 0.9, s * 1.1, s * 1.8); ctx.fillRect(s * 1.3, -s * 0.9, s * 1.1, s * 1.8);
  ctx.fillStyle = '#e6edf8';
  ctx.beginPath(); ctx.arc(0, 0, s * 0.75, 0, TAU); ctx.fill();
  ctx.fillStyle = col;
  ctx.beginPath(); ctx.arc(0, 0, s * 0.35, 0, TAU); ctx.fill();
  ctx.restore();
}

// ---------- particles ----------
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
