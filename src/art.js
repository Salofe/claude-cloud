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
// every star system has its own sky: [base, nebula 1, nebula 2, highlights]
const NEB = {
  sol:        [[5, 8, 22], [58, 28, 110], [16, 78, 110], [120, 30, 90]],
  centauri:   [[6, 10, 20], [20, 70, 100], [110, 80, 40], [150, 120, 70]],
  barnard:    [[12, 5, 8], [90, 20, 26], [60, 22, 50], [150, 50, 30]],
  sirius:     [[4, 9, 22], [30, 70, 140], [20, 110, 130], [150, 190, 255]],
  tauceti:    [[6, 10, 12], [30, 80, 50], [100, 90, 30], [70, 140, 90]],
  eridani:    [[12, 8, 6], [100, 50, 20], [70, 30, 50], [170, 90, 40]],
  vega:       [[5, 6, 24], [50, 50, 150], [90, 30, 140], [140, 170, 255]],
  altair:     [[8, 5, 18], [110, 30, 120], [20, 100, 120], [200, 80, 160]],
  kepler:     [[3, 10, 16], [10, 80, 90], [20, 100, 70], [90, 200, 200]],
  rigel:      [[3, 6, 24], [20, 60, 170], [40, 120, 200], [180, 220, 255]],
  betelgeuse: [[14, 4, 4], [130, 30, 20], [110, 60, 20], [220, 90, 40]],
  orion:      [[8, 4, 16], [140, 40, 120], [30, 110, 140], [230, 120, 180]],
  pulsar:     [[4, 4, 10], [60, 60, 110], [30, 30, 60], [200, 200, 255]],
  rim:        [[10, 8, 4], [120, 90, 30], [90, 50, 20], [240, 190, 90]],
  sgra:       [[2, 1, 6], [70, 20, 90], [120, 50, 20], [255, 150, 60]],
};
const BACKDROPS = {};
function skyKey() { try { return S && typeof sysId === 'function' ? sysId() : 'sol'; } catch (e) { return 'sol'; } }
function makeBackdrop(key) {
  const N = NEB[key] || NEB.sol;
  const c = document.createElement('canvas'); c.width = BD; c.height = BD;
  const x = c.getContext('2d');
  const img = x.createImageData(BD, BD);
  const P = 4, seed = key === 'sol' ? 0 : key.length * 7 + key.charCodeAt(0);
  for (let j = 0; j < BD; j++) for (let i = 0; i < BD; i++) {
    const u = i / BD * P, v = j / BD * P;
    const n1 = fbm(u, v, 11 + seed, P, 5), n2 = fbm(u + 3.1, v + 1.7, 29 + seed, P, 4), n3 = fbm(u * 2, v * 2, 47 + seed, P * 2, 3);
    let col = N[0];
    const a = Math.pow(clamp((n1 - 0.45) * 2.6, 0, 1), 1.6);
    const b = Math.pow(clamp((n2 - 0.5) * 2.8, 0, 1), 1.7);
    const h = Math.pow(clamp((n3 - 0.58) * 3, 0, 1), 2);
    col = mixc(col, N[1], a * 0.85);
    col = mixc(col, N[2], b * 0.7);
    col = mixc(col, N[3], h * 0.5);
    // dark dust lanes cut through the glow
    const lane = clamp((fbm(u * 1.5 + 9, v * 1.5, 71 + seed, P * 1.5, 3) - 0.62) * 4, 0, 1);
    col = mixc(col, [col[0] * 0.35, col[1] * 0.35, col[2] * 0.4], lane * (a + b) * 0.8);
    const k = (j * BD + i) * 4;
    img.data[k] = col[0]; img.data[k + 1] = col[1]; img.data[k + 2] = col[2]; img.data[k + 3] = 255;
  }
  x.putImageData(img, 0, 0);
  // faint dust stars baked in, plus a few bright ones with a halo
  let sd = 5 + seed; const r = () => (sd = (sd * 16807) % 2147483647) / 2147483647;
  for (let i = 0; i < 900; i++) {
    x.globalAlpha = 0.15 + r() * 0.45;
    x.fillStyle = r() > 0.8 ? '#ffe6c8' : r() > 0.6 ? '#bcd8ff' : '#ffffff';
    x.fillRect(r() * BD, r() * BD, 1, 1);
  }
  for (let i = 0; i < 14; i++) {
    const px = r() * BD, py = r() * BD, rr = 1.5 + r() * 2.5;
    const g = x.createRadialGradient(px, py, 0, px, py, rr);
    g.addColorStop(0, 'rgba(255,255,255,0.35)'); g.addColorStop(1, 'rgba(255,255,255,0)');
    x.globalAlpha = 1; x.fillStyle = g; x.fillRect(px - rr, py - rr, rr * 2, rr * 2);
    x.fillStyle = '#ffffff'; x.fillRect(px - 0.5, py - 0.5, 1.2, 1.2);
  }
  x.globalAlpha = 1;
  return c;
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
  const key = skyKey(), backdrop = BACKDROPS[key] || (BACKDROPS[key] = makeBackdrop(key));
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
  // now and then a shooting star streaks across the sky
  const per = 9, n = Math.floor(t / per), f = (t / per) % 1;
  if (f < 0.09) {
    const k = f / 0.09, ang = 0.35 + hash2(n, 3, 5) * 0.5, L = 120 + hash2(n, 4, 5) * 140;
    const x0 = hash2(n, 1, 5) * W * 0.8, y0 = hash2(n, 2, 5) * H * 0.5;
    const hx = x0 + Math.cos(ang) * L * 2.2 * k, hy = y0 + Math.sin(ang) * L * 2.2 * k;
    const g = ctx.createLinearGradient(hx, hy, hx - Math.cos(ang) * L, hy - Math.sin(ang) * L);
    g.addColorStop(0, 'rgba(255,255,255,0.9)'); g.addColorStop(1, 'rgba(160,200,255,0)');
    ctx.globalAlpha = Math.sin(k * Math.PI); ctx.strokeStyle = g; ctx.lineWidth = 1.6;
    ctx.beginPath(); ctx.moveTo(hx, hy); ctx.lineTo(hx - Math.cos(ang) * L, hy - Math.sin(ang) * L); ctx.stroke();
  }
  ctx.globalAlpha = 1;
}
// foreground dust: drifts past faster than the camera, so you feel your speed
const DUST = makeStars(70, 1600, 1600, 23);
function drawDust(ctx, W, H, camX, camY, vx, vy, col) {
  const sp = Math.hypot(vx, vy), L = clamp(sp * 0.035, 0, 26), ux = sp ? vx / sp : 0, uy = sp ? vy / sp : 0;
  ctx.strokeStyle = col || '#cfe6ff'; ctx.fillStyle = col || '#cfe6ff'; ctx.lineCap = 'round';
  for (const d of DUST) {
    const par = 1.15 + d.z * 0.9;
    const x = ((d.x - camX * par) % 1600 + 1600) % 1600, y = ((d.y - camY * par) % 1600 + 1600) % 1600;
    for (let ox = 0; ox < W; ox += 1600) for (let oy = 0; oy < H; oy += 1600) {
      const px = x + ox, py = y + oy; if (px > W || py > H) continue;
      ctx.globalAlpha = 0.12 + d.z * 0.22;
      if (L > 2) { ctx.lineWidth = 0.8 + d.z; ctx.beginPath(); ctx.moveTo(px, py); ctx.lineTo(px - ux * L * par, py - uy * L * par); ctx.stroke(); }
      else ctx.fillRect(px, py, 1 + d.z, 1 + d.z);
    }
  }
  ctx.globalAlpha = 1; ctx.lineCap = 'butt';
}
// soft light from the system's star washing over the scene, tinted to its color
function starWash(ctx, W, H, pal, t) {
  const P = STAR_PAL[pal] || STAR_PAL.sol;
  glow(ctx, -W * 0.05, -H * 0.1, Math.max(W, H) * 0.95, P.g2, 0.22 + 0.03 * Math.sin(t * 0.3));
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
      // generic worlds coloured by loc.col (used by other star systems)
      case 'ocean': {
        const land = fbm(u * 4 / 6, v * 4 / 6, seed + 5, 4, 5);
        col = land > 0.6 ? mixc(L, [235, 225, 190], clamp((land - 0.6) * 3 + (n - 0.5) * 0.6, 0, 1)) : mixc(D, mixc(D, L, 0.5), land * 1.4);
        if (lat > 0.84 + n * 0.08) col = [235, 245, 250];
        break;
      }
      case 'gas': {
        const turb = fbm(u * 1.5, v * 3, seed + 7, P * 1.5, 4);
        const band = Math.sin((j / TH) * 18 + turb * 3.4);
        col = mixc(D, L, clamp(0.5 + band * 0.42 + (n - 0.5) * 0.3, 0, 1));
        break;
      }
      case 'ice': {
        const ridge = Math.abs(fbm(u * 8 / 6, v * 8 / 6, seed + 4, 8, 5) - 0.5);
        col = mixc(D, L, clamp(0.4 + n * 0.8, 0, 1));
        if (ridge < 0.03) col = mixc(D, [40, 60, 110], 0.5);
        break;
      }
      case 'lava': {
        const crack = Math.abs(fbm(u * 6 / 6, v * 6 / 6, seed + 6, 6, 5) - 0.5);
        col = mixc([30, 22, 20], D, n);
        if (crack < 0.04) col = mixc(L, [255, 240, 180], 1 - crack / 0.04);
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

// star palettes: Sol is yellow; other systems bring white, orange, red and blue stars
const STAR_PAL = {
  sol:    { g1: '#ff7a1a33', g2: '#ffb04a88', r0: 'rgba(255,210,120,0.35)', r1: 'rgba(255,150,60,0)', core: ['#ffffff', '#fff4c2', '#ffd060', '#ff9a2a'], f0: 'rgba(255,220,160,0)', f1: 'rgba(255,240,200,0.45)' },
  white:  { g1: '#9fd0ff33', g2: '#e8f4ff88', r0: 'rgba(230,240,255,0.35)', r1: 'rgba(160,200,255,0)', core: ['#ffffff', '#f4f8ff', '#d6e8ff', '#9cc4ff'], f0: 'rgba(210,230,255,0)', f1: 'rgba(235,245,255,0.45)' },
  orange: { g1: '#ff5a1a33', g2: '#ff8a3a88', r0: 'rgba(255,170,90,0.35)', r1: 'rgba(255,110,40,0)', core: ['#ffffff', '#ffe0b0', '#ffa050', '#ff6a1a'], f0: 'rgba(255,190,140,0)', f1: 'rgba(255,215,170,0.45)' },
  red:    { g1: '#ff2a1a33', g2: '#ff5a3a88', r0: 'rgba(255,120,90,0.35)', r1: 'rgba(255,60,40,0)', core: ['#ffe6e0', '#ffb09a', '#ff5a3a', '#c41a10'], f0: 'rgba(255,140,120,0)', f1: 'rgba(255,170,150,0.4)' },
  blue:   { g1: '#3a7aff33', g2: '#7ab0ff88', r0: 'rgba(160,200,255,0.4)', r1: 'rgba(90,140,255,0)', core: ['#ffffff', '#dff0ff', '#9cc8ff', '#4a7aff'], f0: 'rgba(160,200,255,0)', f1: 'rgba(200,225,255,0.5)' },
};
function drawSun(ctx, x, y, r, t, pal) {
  const P = STAR_PAL[pal] || STAR_PAL.sol;
  glow(ctx, x, y, r * 9, P.g1, 0.7);
  glow(ctx, x, y, r * 4, P.g2, 0.7);
  ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < 16; i++) {
    const a = i / 16 * TAU + t * 0.04 + Math.sin(t * 0.7 + i) * 0.05;
    const l = r * (1.7 + 0.5 * Math.sin(t * 1.3 + i * 2.1));
    const g = ctx.createLinearGradient(x, y, x + Math.cos(a) * l, y + Math.sin(a) * l);
    g.addColorStop(0, P.r0); g.addColorStop(1, P.r1);
    ctx.strokeStyle = g; ctx.lineWidth = r * (0.18 + 0.08 * Math.sin(i));
    ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + Math.cos(a) * l, y + Math.sin(a) * l); ctx.stroke();
  }
  ctx.globalCompositeOperation = 'source-over';
  const g = ctx.createRadialGradient(x, y, 0, x, y, r);
  g.addColorStop(0, P.core[0]); g.addColorStop(0.35, P.core[1]); g.addColorStop(0.75, P.core[2]); g.addColorStop(1, P.core[3]);
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill();
  // lens flare
  glow(ctx, x, y, r * 1.5, '#ffffffaa', 0.6);
  ctx.globalCompositeOperation = 'lighter';
  const fl = ctx.createLinearGradient(x - r * 6, y, x + r * 6, y);
  fl.addColorStop(0, P.f0); fl.addColorStop(0.5, P.f1); fl.addColorStop(1, P.f0);
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
// alien machines: crystal hulls, rotating rings, a glowing core
function drawAlienShip(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type];
  ctx.save(); ctx.translate(x, y); ctx.scale(s * e.size, s * e.size);
  glow(ctx, 0, 0, 30, '#7fdfff55', 0.8);
  const big = type === 'sentinel';
  if (big) for (let k = 0; k < 2; k++) {
    ctx.save(); ctx.rotate(t * (k ? -0.6 : 0.9));
    ctx.strokeStyle = k ? 'rgba(217,179,255,0.8)' : 'rgba(127,223,255,0.9)'; ctx.lineWidth = 1.4;
    ctx.beginPath(); ctx.arc(0, 0, 20 + k * 5, 0, TAU); ctx.stroke();
    for (let i = 0; i < 6; i++) { const a = i * TAU / 6; ctx.fillStyle = k ? '#d9b3ff' : '#9ffcff'; ctx.fillRect(Math.cos(a) * (20 + k * 5) - 1.5, Math.sin(a) * (20 + k * 5) - 1.5, 3, 3); }
    ctx.restore();
  }
  ctx.rotate(ang + (big ? t * 0.3 : 0));
  const n = big ? 8 : 4, R = big ? 15 : 12;
  const g = ctx.createLinearGradient(-R, -R, R, R); g.addColorStop(0, '#2a3f7a'); g.addColorStop(0.5, '#4fb6d8'); g.addColorStop(1, '#1a2450');
  ctx.fillStyle = g; ctx.strokeStyle = '#bff6ff'; ctx.lineWidth = 1;
  ctx.beginPath();
  for (let i = 0; i < n; i++) { const a = i * TAU / n, r = i % 2 ? R * 0.62 : R; ctx[i ? 'lineTo' : 'moveTo'](Math.cos(a) * r, Math.sin(a) * r); }
  ctx.closePath(); ctx.fill(); ctx.stroke();
  const pulse = 0.6 + 0.4 * Math.sin(t * 5);
  ctx.globalCompositeOperation = 'lighter';
  glow(ctx, 0, 0, big ? 9 : 5, '#ffffff', pulse);
  ctx.fillStyle = '#e8fdff'; ctx.beginPath(); ctx.arc(0, 0, big ? 3.5 : 2, 0, TAU); ctx.fill();
  ctx.restore();
}
function drawHiveShip(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type], big = type === 'queen';
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s * e.size, s * e.size);
  glow(ctx, 0, 0, big ? 30 : 16, '#7aff6a33', 0.8);
  const flap = Math.sin(t * (big ? 6 : 18)) * 0.35;
  ctx.fillStyle = 'rgba(176,255,154,0.25)'; ctx.strokeStyle = 'rgba(176,255,154,0.6)'; ctx.lineWidth = 0.8;
  for (const side of [-1, 1]) {
    ctx.save(); ctx.rotate(side * (0.9 + flap));
    ctx.beginPath(); ctx.ellipse(-4, side * 0, 14, 5, side * 0.3, 0, TAU); ctx.fill(); ctx.stroke();
    ctx.restore();
  }
  const g = ctx.createLinearGradient(-14, 0, 14, 0); g.addColorStop(0, '#2a1a3a'); g.addColorStop(0.6, '#5a2a6a'); g.addColorStop(1, '#8a4a9a');
  ctx.fillStyle = g; ctx.strokeStyle = '#c08ad0'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.ellipse(-2, 0, big ? 16 : 11, big ? 8 : 5, 0, 0, TAU); ctx.fill(); ctx.stroke();
  ctx.beginPath(); ctx.ellipse(big ? 14 : 10, 0, big ? 6 : 4, big ? 5 : 3.5, 0, 0, TAU); ctx.fill(); ctx.stroke();
  ctx.globalCompositeOperation = 'lighter';
  const pulse = 0.5 + 0.5 * Math.sin(t * 4 + x);
  ctx.fillStyle = `rgba(176,255,154,${0.5 + pulse * 0.4})`;
  for (let i = 0; i < (big ? 4 : 2); i++) { ctx.beginPath(); ctx.arc(-10 + i * 5, (i % 2 ? 2 : -2) * (big ? 1.5 : 1), big ? 2.4 : 1.4, 0, TAU); ctx.fill(); }
  ctx.fillStyle = '#ff6a6a'; ctx.beginPath(); ctx.arc(big ? 17 : 12, -1.5, 1.2, 0, TAU); ctx.arc(big ? 17 : 12, 1.5, 1.2, 0, TAU); ctx.fill();
  ctx.restore();
}
// Mining Colossus: a hulking excavator with hazard stripes and spinning drill arms
function drawMechShip(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type];
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s * e.size, s * e.size);
  glow(ctx, 0, 0, 26, '#ffb03033', 0.8);
  for (const side of [-1, 1]) {           // drill arms
    ctx.fillStyle = '#4a4a52'; ctx.fillRect(-2, side * 9 - 2, 14, 4);
    ctx.save(); ctx.translate(14, side * 9); ctx.rotate(t * 8 * side);
    ctx.fillStyle = '#c8c8d0'; ctx.beginPath(); ctx.moveTo(8, 0); ctx.lineTo(0, -3.5); ctx.lineTo(0, 3.5); ctx.closePath(); ctx.fill();
    ctx.restore();
  }
  ctx.fillStyle = '#2a2a30'; ctx.fillRect(-15, -10, 22, 20);
  ctx.save(); ctx.beginPath(); ctx.rect(-15, -10, 22, 20); ctx.clip();
  ctx.fillStyle = '#ffc830';
  for (let i = -6; i < 6; i++) { ctx.beginPath(); ctx.moveTo(-15 + i * 6, -10); ctx.lineTo(-12 + i * 6, -10); ctx.lineTo(-3 + i * 6, 10); ctx.lineTo(-6 + i * 6, 10); ctx.closePath(); ctx.fill(); }
  ctx.restore();
  ctx.fillStyle = '#3a3a42'; ctx.fillRect(-11, -6, 14, 12);
  ctx.strokeStyle = '#ffc830'; ctx.lineWidth = 1; ctx.strokeRect(-15, -10, 22, 20);
  const pulse = 0.6 + 0.4 * Math.sin(t * 6);
  ctx.fillStyle = `rgba(255,60,40,${pulse})`; ctx.fillRect(1, -3, 5, 6);
  glow(ctx, 3, 0, 6, '#ff3a2a', pulse);
  ctx.fillStyle = '#ff7a30'; ctx.fillRect(-18, -6, 3, 4); ctx.fillRect(-18, 2, 3, 4);
  ctx.restore();
}
// Solar Serpent: a burning head (the body is drawn from its trail)
function drawSerpentHead(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type];
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s * e.size, s * e.size);
  glow(ctx, 0, 0, 22, '#ffb03055', 0.9);
  const g = ctx.createRadialGradient(2, 0, 1, 0, 0, 10); g.addColorStop(0, '#fff6c0'); g.addColorStop(0.5, '#ffa030'); g.addColorStop(1, '#c03010');
  ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(13, 0); ctx.quadraticCurveTo(4, -9, -7, -6); ctx.lineTo(-7, 6); ctx.quadraticCurveTo(4, 9, 13, 0); ctx.fill();
  ctx.fillStyle = '#ffffff'; ctx.beginPath(); ctx.arc(5, -3, 1.4, 0, TAU); ctx.arc(5, 3, 1.4, 0, TAU); ctx.fill();
  ctx.strokeStyle = '#ffe080'; ctx.lineWidth = 1.2;
  for (const side of [-1, 1]) { ctx.beginPath(); ctx.moveTo(-3, side * 5); ctx.quadraticCurveTo(-10, side * 13, -15, side * 9 + Math.sin(t * 6) * 2); ctx.stroke(); }
  ctx.restore();
}
function drawSerpentBody(ctx, e, t) {
  const n = e.trail.length, sz = ENEMIES[e.k].size * 1.3;
  ctx.globalCompositeOperation = 'lighter';
  for (let i = n - 1; i >= 0; i--) {
    const p = e.trail[i], k = 1 - i / n, r = (4 + 6 * k) * sz;
    glow(ctx, p.x, p.y, r * 1.8, i % 2 ? '#ff7a2a' : '#ffb040', 0.35 * k + 0.1);
    ctx.fillStyle = i % 2 ? `rgba(255,140,50,${0.5 + 0.4 * k})` : `rgba(255,200,90,${0.5 + 0.4 * k})`;
    ctx.beginPath(); ctx.arc(p.x, p.y, r, 0, TAU); ctx.fill();
  }
  ctx.globalCompositeOperation = 'source-over';
}
// Dust Citadel: a pirate fortress hidden in the dust, with a spinning turret ring
function drawFortShip(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type];
  ctx.save(); ctx.translate(x, y); ctx.scale(s * e.size, s * e.size);
  glow(ctx, 0, 0, 26, '#ffa86033', 0.8);
  ctx.save(); ctx.rotate(t * 0.9);
  for (let i = 0; i < 4; i++) { ctx.rotate(TAU / 4); ctx.fillStyle = '#5a4a3a'; ctx.fillRect(9, -2.5, 9, 5); ctx.fillStyle = '#ffa860'; ctx.fillRect(16, -1.2, 4, 2.4); }
  ctx.restore();
  ctx.fillStyle = '#3a3228'; ctx.strokeStyle = '#ffa860'; ctx.lineWidth = 1;
  ctx.beginPath(); for (let i = 0; i < 6; i++) { const a = i * TAU / 6; ctx[i ? 'lineTo' : 'moveTo'](Math.cos(a) * 12, Math.sin(a) * 12); } ctx.closePath(); ctx.fill(); ctx.stroke();
  ctx.fillStyle = '#6a5440'; ctx.beginPath(); for (let i = 0; i < 6; i++) { const a = i * TAU / 6 + TAU / 12; ctx[i ? 'lineTo' : 'moveTo'](Math.cos(a) * 7, Math.sin(a) * 7); } ctx.closePath(); ctx.fill();
  const pulse = 0.6 + 0.4 * Math.sin(t * 5);
  glow(ctx, 0, 0, 6, '#ff6a2a', pulse); ctx.fillStyle = `rgba(255,120,60,${pulse})`; ctx.beginPath(); ctx.arc(0, 0, 2.6, 0, TAU); ctx.fill();
  ctx.restore();
}
// Ice Leviathan: a whale of living ice
function drawWhaleShip(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type];
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s * e.size, s * e.size);
  glow(ctx, 0, 0, 24, '#bfefff33', 0.8);
  const tail = Math.sin(t * 4) * 4;
  const g = ctx.createLinearGradient(0, -8, 0, 8); g.addColorStop(0, '#e8faff'); g.addColorStop(0.5, '#7fc8e8'); g.addColorStop(1, '#2a5a7a');
  ctx.fillStyle = g; ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 0.8;
  ctx.beginPath(); ctx.moveTo(16, 0); ctx.quadraticCurveTo(12, -8, 0, -8); ctx.quadraticCurveTo(-10, -7, -15, tail * 0.3); ctx.quadraticCurveTo(-10, 7, 0, 7); ctx.quadraticCurveTo(12, 8, 16, 0); ctx.fill(); ctx.stroke();
  ctx.beginPath(); ctx.moveTo(-14, tail * 0.3); ctx.lineTo(-21, -6 + tail); ctx.lineTo(-19, tail * 0.3); ctx.lineTo(-21, 6 + tail); ctx.closePath(); ctx.fill(); ctx.stroke();
  ctx.fillStyle = 'rgba(255,255,255,0.7)'; for (let i = 0; i < 4; i++) { ctx.beginPath(); ctx.moveTo(-6 + i * 4, -7.5); ctx.lineTo(-5 + i * 4, -11); ctx.lineTo(-4 + i * 4, -7.5); ctx.fill(); }
  ctx.fillStyle = '#0a2a4a'; ctx.beginPath(); ctx.arc(10, -2.5, 1.4, 0, TAU); ctx.fill();
  ctx.restore();
}
// Space Kraken (Kepler): a glowing mantle with eight tentacles trailing behind
function drawKraken(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type];
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s * e.size, s * e.size);
  glow(ctx, -4, 0, 30, '#c080ff33', 0.8);
  ctx.lineCap = 'round';
  for (let i = 0; i < 8; i++) {
    const side = i < 4 ? -1 : 1, k = (i % 4) / 3, y0 = side * (2 + k * 5);
    ctx.strokeStyle = i % 2 ? '#7a3a9a' : '#9a4ab8'; ctx.lineWidth = 3.2 - k * 0.8;
    ctx.beginPath(); ctx.moveTo(-6, y0);
    let px = -6, py = y0;
    for (let j = 1; j <= 6; j++) { px -= 4; py = y0 * (1 + j * 0.25) + Math.sin(t * 3 + i * 1.3 + j * 0.8) * j * 0.9; ctx.lineTo(px, py); }
    ctx.stroke();
    ctx.fillStyle = '#7fffe0'; ctx.globalAlpha = 0.6 + 0.4 * Math.sin(t * 4 + i); ctx.beginPath(); ctx.arc(px, py, 0.9, 0, TAU); ctx.fill(); ctx.globalAlpha = 1;
  }
  ctx.lineCap = 'butt';
  const pulse = 1 + Math.sin(t * 2.5) * 0.05;
  const g = ctx.createRadialGradient(6, -3, 1, 2, 0, 15);
  g.addColorStop(0, '#e0a0ff'); g.addColorStop(0.6, '#8a3ab0'); g.addColorStop(1, '#3a1050');
  ctx.fillStyle = g; ctx.strokeStyle = '#e8c0ff'; ctx.lineWidth = 0.8;
  ctx.beginPath(); ctx.ellipse(4, 0, 13 * pulse, 9 / pulse, 0, 0, TAU); ctx.fill(); ctx.stroke();
  ctx.fillStyle = '#7fffe0';
  for (const [sx, sy] of [[8, -5], [2, -6], [-3, -4], [8, 5], [2, 6], [-3, 4], [12, 0]]) { ctx.globalAlpha = 0.5 + 0.5 * Math.sin(t * 3 + sx + sy); ctx.beginPath(); ctx.arc(sx, sy, 0.9, 0, TAU); ctx.fill(); }
  ctx.globalAlpha = 1;
  for (const sy of [-3.5, 3.5]) {
    ctx.fillStyle = '#fff4a0'; ctx.beginPath(); ctx.ellipse(-4, sy, 2.4, 1.8, 0, 0, TAU); ctx.fill();
    ctx.fillStyle = '#1a0a20'; ctx.beginPath(); ctx.ellipse(-3.6, sy, 0.8, 1.5, 0, 0, TAU); ctx.fill();
  }
  ctx.restore();
}
// Radiant Titan (Rigel): a floating crystal giant ringed by shards and halos
function drawRadiant(ctx, type, x, y, ang, s, t) {
  const e = ENEMIES[type], k = s * e.size;
  ctx.save(); ctx.translate(x, y); ctx.scale(k, k);
  glow(ctx, 0, 0, 34, '#a0d8ff55', 0.9);
  ctx.strokeStyle = 'rgba(200,235,255,0.5)'; ctx.lineWidth = 0.7;
  for (let i = 0; i < 2; i++) { ctx.beginPath(); ctx.ellipse(0, 0, 20 + i * 4, 6 + i * 2, t * (0.4 - i * 0.7), 0, TAU); ctx.stroke(); }
  for (let i = 0; i < 6; i++) {
    const a = t * 0.8 + i * TAU / 6, r = 17 + Math.sin(t * 2 + i) * 1.5, sx = Math.cos(a) * r, sy = Math.sin(a) * r * 0.75;
    ctx.save(); ctx.translate(sx, sy); ctx.rotate(a + t);
    ctx.fillStyle = 'rgba(190,230,255,0.85)'; ctx.beginPath(); ctx.moveTo(0, -3.5); ctx.lineTo(1.6, 0); ctx.lineTo(0, 3.5); ctx.lineTo(-1.6, 0); ctx.closePath(); ctx.fill();
    ctx.restore();
  }
  ctx.rotate(Math.sin(t * 0.6) * 0.2);
  const g = ctx.createLinearGradient(-10, -12, 10, 12);
  g.addColorStop(0, '#ffffff'); g.addColorStop(0.5, '#8ac8ff'); g.addColorStop(1, '#2a4a9a');
  ctx.fillStyle = g; ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 0.9;
  ctx.beginPath(); ctx.moveTo(0, -14); ctx.lineTo(9, -3); ctx.lineTo(6, 10); ctx.lineTo(0, 14); ctx.lineTo(-6, 10); ctx.lineTo(-9, -3); ctx.closePath(); ctx.fill(); ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,0.45)'; ctx.beginPath(); ctx.moveTo(0, -14); ctx.lineTo(0, 14); ctx.moveTo(-9, -3); ctx.lineTo(9, -3); ctx.moveTo(-6, 10); ctx.lineTo(0, 2); ctx.lineTo(6, 10); ctx.stroke();
  // the eye looks at you
  const ea = ang - Math.sin(t * 0.6) * 0.2;
  glow(ctx, Math.cos(ea) * 2.5, Math.sin(ea) * 2.5 - 1, 7, '#ffffff', 0.9);
  ctx.fillStyle = '#ffffff'; ctx.beginPath(); ctx.arc(Math.cos(ea) * 2.5, Math.sin(ea) * 2.5 - 1, 2, 0, TAU); ctx.fill();
  ctx.restore();
}
// Stellar Phoenix (Betelgeuse): a bird of fire with beating wings; reborn in blue flame
function drawPhoenix(ctx, type, x, y, ang, s, t, ent) {
  const e = ENEMIES[type], blue = ent && ent.reborn;
  const c0 = blue ? '#e0f4ff' : '#fff2a0', c1 = blue ? '#60b0ff' : '#ffa030', c2 = blue ? '#2050c0' : '#d02010';
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(s * e.size, s * e.size);
  glow(ctx, -4, 0, 34, c1 + '66', 0.9);
  ctx.globalCompositeOperation = 'lighter';
  // tail of fire
  for (let i = 0; i < 5; i++) {
    const w = Math.sin(t * 6 + i) * 3, L = 20 + i * 3;
    const g = ctx.createLinearGradient(-6, 0, -6 - L, w); g.addColorStop(0, c1); g.addColorStop(1, 'rgba(0,0,0,0)');
    ctx.strokeStyle = g; ctx.lineWidth = 2.4 - i * 0.3;
    ctx.beginPath(); ctx.moveTo(-6, 0); ctx.quadraticCurveTo(-6 - L * 0.5, (i - 2) * 2.5 + w, -6 - L, (i - 2) * 5 + w); ctx.stroke();
  }
  // wings
  const flap = Math.sin(t * 5);
  for (const sd of [-1, 1]) {
    const tipY = sd * (20 + flap * 6), tipX = -6 + flap * 2;
    const g = ctx.createLinearGradient(0, 0, tipX, tipY); g.addColorStop(0, c0); g.addColorStop(0.5, c1); g.addColorStop(1, c2);
    ctx.fillStyle = g; ctx.globalAlpha = 0.9;
    ctx.beginPath(); ctx.moveTo(4, sd * 2); ctx.quadraticCurveTo(2, sd * 14, tipX, tipY); ctx.quadraticCurveTo(-4, sd * 10, -8, sd * 6); ctx.quadraticCurveTo(-6, sd * 8, -10, sd * 3); ctx.lineTo(-4, sd * 1.5); ctx.closePath(); ctx.fill();
  }
  ctx.globalAlpha = 1;
  // body & head
  const bg = ctx.createRadialGradient(6, 0, 1, 0, 0, 12); bg.addColorStop(0, '#ffffff'); bg.addColorStop(0.4, c0); bg.addColorStop(1, c1);
  ctx.fillStyle = bg; ctx.beginPath(); ctx.ellipse(1, 0, 10, 4.5, 0, 0, TAU); ctx.fill();
  ctx.beginPath(); ctx.moveTo(10, -2.5); ctx.lineTo(16, 0); ctx.lineTo(10, 2.5); ctx.closePath(); ctx.fill();
  ctx.globalCompositeOperation = 'source-over';
  ctx.fillStyle = '#3a0a00'; ctx.beginPath(); ctx.arc(8, -1.4, 0.9, 0, TAU); ctx.fill();
  ctx.restore();
}
function drawEnemyShip(ctx, type, x, y, ang, s, t, ent) {
  const e = ENEMIES[type];
  if (e.kraken) return drawKraken(ctx, type, x, y, ang, s, t);
  if (e.radiant) return drawRadiant(ctx, type, x, y, ang, s, t);
  if (e.phoenix) return drawPhoenix(ctx, type, x, y, ang, s, t, ent);
  if (e.alien) return drawAlienShip(ctx, type, x, y, ang, s, t);
  if (e.fort) return drawFortShip(ctx, type, x, y, ang, s, t);
  if (e.whale) return drawWhaleShip(ctx, type, x, y, ang, s, t);
  if (e.hive) return drawHiveShip(ctx, type, x, y, ang, s, t);
  if (e.mech) return drawMechShip(ctx, type, x, y, ang, s, t);
  if (e.serpent) return drawSerpentHead(ctx, type, x, y, ang, s, t);
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
  if (type === 'warlord' || type === 'pirateking') {
    ctx.fillStyle = dark;
    ctx.beginPath(); ctx.moveTo(2, -6); ctx.lineTo(-14, -22); ctx.lineTo(-20, -20); ctx.lineTo(-10, -5); ctx.closePath(); ctx.fill();
    ctx.beginPath(); ctx.moveTo(2, 6); ctx.lineTo(-14, 22); ctx.lineTo(-20, 20); ctx.lineTo(-10, 5); ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#ffd24a'; ctx.fillRect(-18, -21, 5, 2); ctx.fillRect(-18, 19, 5, 2);
  }
  if (type === 'frigate' || type === 'carrier' || type === 'warlord' || type === 'dreadnought' || type === 'pirateking') {
    ctx.fillStyle = dark;
    ctx.fillRect(-12, -11, 12, 4); ctx.fillRect(-12, 7, 12, 4);
    ctx.fillStyle = lit;
    ctx.fillRect(-2, -10, 3, 2); ctx.fillRect(-2, 8, 3, 2);
  }
  if (type === 'warlord') {
    ctx.save(); ctx.rotate(Math.PI / 2); drawIcon(ctx, 'skull', 0, 2, 9, '#ffd24a'); ctx.restore();
  }
  if (type === 'pirateking') {
    ctx.save(); ctx.rotate(Math.PI / 2); drawIcon(ctx, 'crown', 0, 2, 11, '#ffd24a'); ctx.restore();
  }
  if (type === 'dreadnought') {
    ctx.fillStyle = dark; ctx.fillRect(-16, -14, 26, 5); ctx.fillRect(-16, 9, 26, 5);
    for (const [tx, ty] of [[-10, -11.5], [2, -11.5], [-10, 11.5], [2, 11.5]]) {
      ctx.fillStyle = '#ffd24a'; ctx.beginPath(); ctx.arc(tx, ty, 2.2, 0, TAU); ctx.fill();
      ctx.strokeStyle = '#ffd24a'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(tx, ty); ctx.lineTo(tx + 4, ty); ctx.stroke();
    }
    ctx.strokeStyle = '#ffd24a'; ctx.lineWidth = 0.8; ctx.beginPath(); ctx.moveTo(18, 0); ctx.lineTo(-4, -6); ctx.lineTo(-15, -4); ctx.moveTo(18, 0); ctx.lineTo(-4, 6); ctx.lineTo(-15, 4); ctx.stroke();
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
// crystal asteroids (other star systems): faceted, translucent, glowing with their ore
function drawCrystalRock(ctx, a, t) {
  const ore = ITEMS[a.ore], n = a.tier === 1 ? 5 : a.tier === 2 ? 6 : 7;
  ctx.save(); ctx.translate(a.x, a.y); ctx.rotate(a.rot);
  glow(ctx, 0, 0, a.r * 1.8, ore.c + '55', 0.6 + 0.2 * Math.sin(t * 3 + a.x));
  const pts = Array.from({ length: n }, (_, i) => { const ang = i / n * TAU, k = i % 2 ? 0.72 : 1.05; return [Math.cos(ang) * a.r * k, Math.sin(ang) * a.r * k]; });
  const g = ctx.createLinearGradient(-a.r, -a.r, a.r, a.r);
  g.addColorStop(0, 'rgba(240,235,255,0.85)'); g.addColorStop(0.5, ore.c + 'aa'); g.addColorStop(1, 'rgba(60,40,110,0.85)');
  ctx.fillStyle = g; ctx.beginPath(); pts.forEach((p, i) => i ? ctx.lineTo(p[0], p[1]) : ctx.moveTo(p[0], p[1])); ctx.closePath(); ctx.fill();
  if (a.hit > 0) { ctx.fillStyle = 'rgba(255,255,255,0.35)'; ctx.fill(); }
  ctx.strokeStyle = 'rgba(255,255,255,0.75)'; ctx.lineWidth = 1.2; ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,0.35)'; ctx.lineWidth = 1;
  ctx.beginPath(); for (const p of pts) { ctx.moveTo(0, 0); ctx.lineTo(p[0], p[1]); } ctx.stroke();
  ctx.globalCompositeOperation = 'lighter';
  ctx.fillStyle = 'rgba(255,255,255,0.8)'; const gl = (t * 0.7 + a.x * 0.01) % 1;
  ctx.beginPath(); ctx.arc(pts[0][0] * gl, pts[0][1] * gl, 1.8, 0, TAU); ctx.fill();
  ctx.restore();
}
// armored asteroids (Sirius): a heat-forged metal shell with rivets; ore glows through the seams
function drawArmoredRock(ctx, a, t) {
  const ore = ITEMS[a.ore];
  ctx.save(); ctx.translate(a.x, a.y); ctx.rotate(a.rot);
  const g = ctx.createLinearGradient(-a.r, -a.r, a.r, a.r);
  g.addColorStop(0, '#c8d0dc'); g.addColorStop(0.45, '#6a7484'); g.addColorStop(1, '#2a3038');
  ctx.fillStyle = g; ctx.beginPath();
  a.shape.forEach((p, i) => { const px = p[0] * a.r * (0.85 + p[2] * 0.15), py = p[1] * a.r * (0.85 + p[2] * 0.15); i ? ctx.lineTo(px, py) : ctx.moveTo(px, py); });
  ctx.closePath(); ctx.fill();
  if (a.hit > 0) { ctx.fillStyle = 'rgba(255,255,255,0.18)'; ctx.fill(); }
  ctx.strokeStyle = '#1a1e24'; ctx.lineWidth = 2; ctx.stroke();
  ctx.save(); ctx.clip();
  ctx.strokeStyle = ore.c; ctx.globalAlpha = 0.75 + 0.2 * Math.sin(t * 3 + a.x); ctx.lineWidth = 1.6;
  ctx.beginPath(); ctx.moveTo(-a.r, -a.r * 0.15); ctx.lineTo(a.r, a.r * 0.1); ctx.moveTo(-a.r * 0.2, -a.r); ctx.lineTo(a.r * 0.1, a.r); ctx.stroke();
  ctx.restore();
  ctx.globalAlpha = 1; ctx.fillStyle = '#e8ecf2';
  for (let i = 0; i < 6; i++) { const an = i / 6 * TAU + 0.3; ctx.beginPath(); ctx.arc(Math.cos(an) * a.r * 0.62, Math.sin(an) * a.r * 0.62, 1.3 + a.tier * 0.3, 0, TAU); ctx.fill(); }
  shadeRock(ctx, a, () => { ctx.beginPath(); a.shape.forEach((p, i) => { const px = p[0] * a.r * (0.85 + p[2] * 0.15), py = p[1] * a.r * (0.85 + p[2] * 0.15); i ? ctx.lineTo(px, py) : ctx.moveTo(px, py); }); ctx.closePath(); });
  ctx.restore();
}
// world-fixed light from the upper left: darken the far side, rim-light the near edge
const LIGHT_A = -2.3;
function shadeRock(ctx, a, path) {
  const la = LIGHT_A - a.rot, lx = Math.cos(la) * a.r, ly = Math.sin(la) * a.r;
  const g = ctx.createLinearGradient(lx, ly, -lx, -ly);
  g.addColorStop(0, 'rgba(255,236,210,0.16)'); g.addColorStop(0.45, 'rgba(0,0,0,0)'); g.addColorStop(1, 'rgba(0,0,12,0.6)');
  path(); ctx.fillStyle = g; ctx.fill();
  const rg = ctx.createLinearGradient(lx, ly, 0, 0);
  rg.addColorStop(0, 'rgba(255,240,215,0.55)'); rg.addColorStop(1, 'rgba(255,240,215,0)');
  ctx.strokeStyle = rg; ctx.lineWidth = 1.8; ctx.stroke();
}
function drawRock(ctx, a, t, scanLv) {
  if (a.volatile) {
    // a normal rock with glowing magma cracks that pulse faster as it is damaged
    const k = 1 - a.hp / a.maxhp, pulse = 0.5 + 0.5 * Math.sin(t * (4 + k * 14) + a.x);
    glow(ctx, a.x, a.y, a.r * 1.9, '#ff5a2a', 0.25 + pulse * 0.3);
  }
  if (a.crystal) return drawCrystalRock(ctx, a, t);
  if (a.armored) { drawArmoredRock(ctx, a, t); return drawRockFx(ctx, a, t); }
  if (a.living) drawLivingFins(ctx, a, t);
  const ore = ITEMS[a.ore];
  ctx.save();
  ctx.translate(a.x, a.y); ctx.rotate(a.rot);
  if (a.rich) glow(ctx, 0, 0, a.r * 2.2, ore.c + '66', 0.5 + 0.25 * Math.sin(t * 3 + a.x));
  const hl = LIGHT_A - a.rot;
  const g = ctx.createRadialGradient(Math.cos(hl) * a.r * 0.4, Math.sin(hl) * a.r * 0.4, a.r * 0.1, 0, 0, a.r * 1.1);
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
  if (a.volatile) {
    ctx.strokeStyle = `rgba(255,${150 + Math.round(80 * Math.sin(t * 6 + a.x))},60,0.95)`; ctx.lineWidth = 1.6 + a.tier * 0.4;
    ctx.beginPath(); ctx.moveTo(-a.r * 0.7, -a.r * 0.2); ctx.lineTo(-a.r * 0.1, a.r * 0.1); ctx.lineTo(a.r * 0.5, -a.r * 0.4); ctx.moveTo(-a.r * 0.1, a.r * 0.1); ctx.lineTo(a.r * 0.2, a.r * 0.6); ctx.stroke();
  }
  // cráteres (with a lit lip on the side facing the light)
  const cla = LIGHT_A - a.rot, clx = Math.cos(cla), cly = Math.sin(cla);
  for (const c of a.craters) {
    const cx = c[0] * a.r, cy = c[1] * a.r, cr = c[2] * a.r;
    ctx.fillStyle = 'rgba(0,0,0,0.28)'; ctx.beginPath(); ctx.arc(cx, cy, cr, 0, TAU); ctx.fill();
    ctx.strokeStyle = 'rgba(255,240,220,0.14)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.arc(cx, cy, cr, cla + Math.PI - 1.1, cla + Math.PI + 1.1); ctx.stroke();
  }
  shadeRock(ctx, a, () => { ctx.beginPath(); a.shape.forEach((p, i) => { const px = p[0] * a.r * p[2], py = p[1] * a.r * p[2]; i ? ctx.lineTo(px, py) : ctx.moveTo(px, py); }); ctx.closePath(); });
  ctx.restore();
  drawRockFx(ctx, a, t);
  if ((scanLv >= 2 || a.seen > 0) && a.rich) {
    ctx.strokeStyle = ore.c; ctx.globalAlpha = 0.5 + 0.3 * Math.sin(t * 4);
    ctx.setLineDash([4, 4]); ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.arc(a.x, a.y, a.r + 8, 0, TAU); ctx.stroke();
    ctx.setLineDash([]); ctx.globalAlpha = 1;
  }
}

// living rocks (Kepler): little fins that beat as they swim, and glowing spots
function drawLivingFins(ctx, a, t) {
  const sp = Math.hypot(a.vx, a.vy), dir = sp > 3 ? Math.atan2(a.vy, a.vx) : a.rot, w = Math.sin(a.swim || 0);
  ctx.save(); ctx.translate(a.x, a.y); ctx.rotate(dir);
  glow(ctx, 0, 0, a.r * 1.7, a.flee > 0 ? '#ff9a7a55' : '#7fffd055', 0.6 + 0.2 * Math.sin(t * 2 + a.x));
  ctx.fillStyle = '#4a8a7a'; ctx.strokeStyle = '#9fffe0'; ctx.lineWidth = 1;
  for (const sd of [-1, 1]) { ctx.beginPath(); ctx.moveTo(-a.r * 0.1, sd * a.r * 0.75); ctx.quadraticCurveTo(-a.r * 0.5, sd * a.r * (1.35 + w * 0.15 * sd), -a.r * 0.8, sd * a.r * 0.7); ctx.closePath(); ctx.fill(); ctx.stroke(); }
  ctx.beginPath(); ctx.moveTo(-a.r * 0.85, 0); ctx.lineTo(-a.r * 1.45, -a.r * (0.4 + w * 0.2)); ctx.lineTo(-a.r * 1.3, 0); ctx.lineTo(-a.r * 1.45, a.r * (0.4 - w * 0.2)); ctx.closePath(); ctx.fill(); ctx.stroke();
  ctx.restore();
}
// overlays shared by every rock: living glow spots, molten heat (Betelgeuse pulses), revealed geodes (Deep Scan)
function drawRockFx(ctx, a, t) {
  if (a.living) {
    const sp = Math.hypot(a.vx, a.vy), dir = sp > 3 ? Math.atan2(a.vy, a.vx) : a.rot;
    ctx.fillStyle = a.flee > 0 ? '#ffb090' : '#9fffe0';
    for (let i = 0; i < 5; i++) { const an = i * 2.4 + a.r, d = a.r * (0.25 + (i % 3) * 0.2); ctx.globalAlpha = 0.5 + 0.5 * Math.sin(t * 3 + i * 1.7); ctx.beginPath(); ctx.arc(a.x + Math.cos(an) * d, a.y + Math.sin(an) * d, 1.5 + a.tier * 0.5, 0, TAU); ctx.fill(); }
    ctx.globalAlpha = 1;
    const ex = a.x + Math.cos(dir) * a.r * 0.55, ey = a.y + Math.sin(dir) * a.r * 0.55;
    for (const sd of [-1, 1]) { const px = ex - Math.sin(dir) * sd * a.r * 0.22, py = ey + Math.cos(dir) * sd * a.r * 0.22; ctx.fillStyle = '#fffbe0'; ctx.beginPath(); ctx.arc(px, py, 1.6 + a.tier * 0.7, 0, TAU); ctx.fill(); ctx.fillStyle = '#0a1a1a'; ctx.beginPath(); ctx.arc(px + Math.cos(dir) * 0.8, py + Math.sin(dir) * 0.8, 0.8 + a.tier * 0.35, 0, TAU); ctx.fill(); }
  }
  if (MineScene.moltenT > 0 && !a.comet) {
    const k = Math.min(1, MineScene.moltenT / 2);
    glow(ctx, a.x, a.y, a.r * 1.5, '#ff5a1a', 0.45 * k);
    ctx.strokeStyle = `rgba(255,${170 + Math.round(60 * Math.sin(t * 8 + a.x))},80,${0.8 * k})`; ctx.lineWidth = 1.2 + a.tier * 0.4;
    ctx.save(); ctx.translate(a.x, a.y); ctx.rotate(a.rot);
    ctx.beginPath(); ctx.moveTo(-a.r * 0.6, a.r * 0.3); ctx.lineTo(0, -a.r * 0.1); ctx.lineTo(a.r * 0.55, a.r * 0.35); ctx.moveTo(0, -a.r * 0.1); ctx.lineTo(-a.r * 0.15, -a.r * 0.6); ctx.stroke();
    ctx.restore();
  }
  if (a.geode && a.seen > 0 && !(a.seenD > 0)) {
    const col = ITEMS[a.geode].c, k = Math.min(1, a.seen / 1.5), pr = a.r + 10 + Math.sin(t * 5) * 3;
    ctx.globalAlpha = k;
    glow(ctx, a.x, a.y, a.r * 1.4, col + '88', 0.8);
    ctx.strokeStyle = col; ctx.lineWidth = 2.2;
    ctx.beginPath(); for (let i = 0; i <= 6; i++) { const an = i / 6 * TAU + t * 0.5; i ? ctx.lineTo(a.x + Math.cos(an) * pr, a.y + Math.sin(an) * pr) : ctx.moveTo(a.x + Math.cos(an) * pr, a.y + Math.sin(an) * pr); } ctx.stroke();
    ctx.fillStyle = col; ctx.font = '700 12px Rajdhani, sans-serif'; ctx.textAlign = 'center';
    ctx.fillText(`GEODE · ${ITEMS[a.geode].n}`, a.x, a.y - pr - 6);
    ctx.globalAlpha = 1;
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
  const tw = Math.sin(t * 4 + c.rot * 9);
  if (tw > 0.85) { const k = (tw - 0.85) / 0.15 * 7; ctx.fillStyle = '#ffffff'; ctx.globalAlpha = 0.8; ctx.fillRect(c.x - k, c.y - 0.6, k * 2, 1.2); ctx.fillRect(c.x - 0.6, c.y - k, 1.2, k * 2); ctx.globalAlpha = 1; }
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
