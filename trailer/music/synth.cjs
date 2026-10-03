// Trailer score for Solar Prospector — synthesized from code. 120 BPM, A minor, 40 bars (80 s).
// Writes public/music.wav plus SFX (whoosh/impact/riser) for cuts.
const fs = require('fs'), path = require('path');
const SR = 44100, BPM = 120, BEAT = 60 / BPM, BAR = BEAT * 4, BARS = 41;
const LEN = Math.ceil(BARS * BAR * SR);
const L = new Float32Array(LEN), R = new Float32Array(LEN);
const revL = new Float32Array(LEN), revR = new Float32Array(LEN);   // reverb send
const dlyL = new Float32Array(LEN), dlyR = new Float32Array(LEN);   // tempo delay send
const duck = new Float32Array(LEN).fill(1);                         // sidechain from kick
const TAU = Math.PI * 2;
let seed = 7; const rnd = () => ((seed = (seed * 16807) % 2147483647) / 2147483647) * 2 - 1;
const mtof = m => 440 * Math.pow(2, (m - 69) / 12);
const t2i = t => Math.floor(t * SR);
const bt = (bar, beat = 0) => (bar - 1) * BAR + beat * BEAT;   // bars are 1-based

function biquad(type, f, q) {
  const w = TAU * f / SR, c = Math.cos(w), s = Math.sin(w), a = s / (2 * q);
  let b0, b1, b2, a0 = 1 + a, a1 = -2 * c, a2 = 1 - a;
  if (type === 'lp') { b0 = (1 - c) / 2; b1 = 1 - c; b2 = (1 - c) / 2; }
  else if (type === 'hp') { b0 = (1 + c) / 2; b1 = -(1 + c); b2 = (1 + c) / 2; }
  else { b0 = a; b1 = 0; b2 = -a; }
  return { b0: b0 / a0, b1: b1 / a0, b2: b2 / a0, a1: a1 / a0, a2: a2 / a0, x1: 0, x2: 0, y1: 0, y2: 0 };
}
function filt(st, x) { const y = st.b0 * x + st.b1 * st.x1 + st.b2 * st.x2 - st.a1 * st.y1 - st.a2 * st.y2; st.x2 = st.x1; st.x1 = x; st.y2 = st.y1; st.y1 = y; return y; }
function retune(st, type, f, q) { const n = biquad(type, Math.min(f, SR * 0.45), q); st.b0 = n.b0; st.b1 = n.b1; st.b2 = n.b2; st.a1 = n.a1; st.a2 = n.a2; }
function add(t0, n, fn, pan = 0, gain = 1, rev = 0, dly = 0, ducked = false) {
  const i0 = t2i(t0), gl = gain * Math.cos((pan + 1) * Math.PI / 4) * 1.41, gr = gain * Math.sin((pan + 1) * Math.PI / 4) * 1.41;
  for (let k = 0; k < n; k++) {
    const i = i0 + k; if (i < 0 || i >= LEN) continue;
    let v = fn(k / SR, k); if (ducked) v *= duck[i];
    L[i] += v * gl; R[i] += v * gr; if (rev) { revL[i] += v * gl * rev; revR[i] += v * gr * rev; } if (dly) { dlyL[i] += v * gl * dly; dlyR[i] += v * gr * dly; }
  }
}
const env = (t, a, d) => t < a ? t / a : Math.exp(-(t - a) / d);
// ---------------- instruments ----------------
function kick(t, g = 1) {
  add(t, t2i(0.5), (x) => { const f = 45 + 110 * Math.exp(-x * 28); return Math.sin(TAU * (45 * x + 110 * (1 - Math.exp(-x * 28)) / 28)) * Math.exp(-x * 7) * 0.95 + (x < 0.004 ? rnd() * 0.5 : 0); }, 0, g);
  const i0 = t2i(t); for (let k = 0; k < t2i(0.32); k++) if (i0 + k < LEN) duck[i0 + k] = Math.min(duck[i0 + k], 0.35 + 0.65 * Math.min(1, k / t2i(0.3)));
}
function clap(t, g = 1) { const bp = biquad('bp', 1500, 0.9); add(t, t2i(0.4), (x) => { const e = x < 0.03 ? (Math.floor(x * 300) % 3 === 0 ? 1 : 0.6) : Math.exp(-(x - 0.03) * 14); return filt(bp, rnd()) * e * 1.6 + Math.sin(TAU * 190 * x) * Math.exp(-x * 30) * 0.3; }, 0, g * 0.55, 0.35); }
function hat(t, g = 1, open = false) { const hp = biquad('hp', 8000, 0.7); add(t, t2i(open ? 0.3 : 0.06), (x) => filt(hp, rnd()) * Math.exp(-x * (open ? 12 : 60)), (rnd() * 0.3), g * 0.22); }
function crash(t, g = 1) { const hp = biquad('hp', 4500, 0.5); add(t, t2i(2.6), (x) => filt(hp, rnd()) * Math.exp(-x * 1.6), 0.15, g * 0.3, 0.4); }
function tom(t, m, g = 1) { add(t, t2i(0.6), (x) => Math.sin(TAU * mtof(m) * x * (1 + 0.5 * Math.exp(-x * 20))) * Math.exp(-x * 6), 0, g * 0.6, 0.3); }
function impact(t, g = 1) {
  const lp = biquad('lp', 900, 0.7);
  add(t, t2i(3.5), (x) => Math.sin(TAU * (32 * x + 60 * (1 - Math.exp(-x * 6)) / 6)) * Math.exp(-x * 1.3) * 1.1 + filt(lp, rnd()) * Math.exp(-x * 3) * 0.6, 0, g, 0.5);
  crash(t, g * 0.9);
}
function riser(t, dur, g = 1) {
  const bp = biquad('bp', 300, 2); let ph = 0;
  add(t, t2i(dur), (x, k) => { const p = x / dur; if (k % 64 === 0) retune(bp, 'bp', 300 + 7000 * p * p, 2); ph += TAU * (200 + 900 * p * p) / SR; return (filt(bp, rnd()) * 1.2 + Math.sin(ph) * 0.18) * p * p; }, 0, g * 0.6, 0.4);
}
function whoosh(t, dur = 0.7, g = 1) {
  const bp = biquad('bp', 400, 1.2);
  add(t, t2i(dur), (x, k) => { const p = x / dur; if (k % 64 === 0) retune(bp, 'bp', 300 + 3500 * Math.sin(Math.PI * p), 1.2); return filt(bp, rnd()) * Math.sin(Math.PI * p) * 1.6; }, 0, g * 0.5, 0.3);
}
function saw(ph) { return 2 * (ph - Math.floor(ph + 0.5)); }
function bass(t, m, dur, g = 1) {
  const lp = biquad('lp', 400, 1.1); const f = mtof(m); let p1 = 0, p2 = 0.3;
  add(t, t2i(dur), (x, k) => { if (k % 32 === 0) retune(lp, 'lp', 180 + 1400 * Math.exp(-x * 10), 1.4); p1 += f / SR; p2 += f * 1.005 / SR; return filt(lp, saw(p1) + saw(p2) * 0.6 + Math.sin(TAU * f * 0.5 * x) * 0.8) * Math.min(1, x / 0.005) * Math.min(1, (dur - x) / 0.02); }, 0, g * 0.38, 0, 0, true);
}
function pad(t, notes, dur, g = 1, bright = 1) {
  for (const m of notes) for (let v = 0; v < 4; v++) {
    const f = mtof(m) * (1 + (v - 1.5) * 0.0035); const lp = biquad('lp', 1200 * bright, 0.7); let ph = Math.random();
    add(t, t2i(dur + 1.5), (x) => { ph += f / SR; const e = Math.min(1, x / 0.6) * (x > dur ? Math.exp(-(x - dur) * 2.5) : 1); return filt(lp, saw(ph)) * e; }, (v - 1.5) * 0.45, g * 0.05, 0.6, 0, true);
  }
}
function pluck(t, m, g = 1, pan = 0) {
  const f = mtof(m); const lp = biquad('lp', 3000, 0.8); let ph = 0;
  add(t, t2i(0.45), (x, k) => { if (k % 32 === 0) retune(lp, 'lp', 600 + 5000 * Math.exp(-x * 18), 1); ph += f / SR; return filt(lp, (ph % 1 < 0.5 ? 1 : -1) * 0.7 + saw(ph * 2) * 0.3) * Math.exp(-x * 9); }, pan, g * 0.13, 0.25, 0.35, true);
}
function lead(t, m, dur, g = 1) {
  const f = mtof(m); const lp = biquad('lp', 2600, 0.9); let p1 = 0, p2 = 0;
  add(t, t2i(dur + 0.4), (x) => { const vib = 1 + 0.004 * Math.sin(TAU * 5.5 * x) * Math.min(1, x / 0.3); p1 += f * vib / SR; p2 += f * 1.007 * vib / SR; const e = Math.min(1, x / 0.02) * (x > dur ? Math.exp(-(x - dur) * 8) : 1); return filt(lp, saw(p1) + saw(p2) * 0.7) * e; }, 0.05, g * 0.11, 0.45, 0.3);
}
function choir(t, notes, dur, g = 1) {
  for (const m of notes) for (let v = 0; v < 3; v++) {
    const f = mtof(m) * (1 + (v - 1) * 0.004); const bp1 = biquad('bp', 700, 3), bp2 = biquad('bp', 1150, 4); let ph = Math.random();
    add(t, t2i(dur + 2), (x) => { ph += f * (1 + 0.003 * Math.sin(TAU * 5 * x + v)) / SR; const s = saw(ph); const e = Math.min(1, x / 1.2) * (x > dur ? Math.exp(-(x - dur) * 1.6) : 1); return (filt(bp1, s) + filt(bp2, s) * 0.7) * e; }, (v - 1) * 0.6, g * 0.09, 0.8);
  }
}
// ---------------- score ----------------
// A minor: Am F C G  (i VI III VII)
const PROG = [[57, 60, 64], [53, 57, 60], [48, 52, 55], [55, 59, 62]];
const ROOT = [45, 41, 48, 43];
const chordAt = bar => (bar - 1) % 4;
const ARP = (c) => [c[0] + 12, c[1] + 12, c[2] + 12, c[1] + 12, c[0] + 24, c[2] + 12, c[1] + 12, c[2] + 12];
// game-like theme motif (8 notes over 2 bars), A minor pentatonic
const THEME = [[0, 76, 1], [1, 74, 0.5], [1.5, 72, 0.5], [2, 69, 1.5], [4, 72, 1], [5, 74, 0.5], [5.5, 76, 0.5], [6, 79, 2]];
const THEME2 = [[0, 81, 1], [1, 79, 0.5], [1.5, 76, 0.5], [2, 74, 1.5], [4, 76, 1], [5, 74, 0.5], [5.5, 72, 0.5], [6, 69, 2]];

function groove(bar, o) {
  const c = PROG[chordAt(bar)], r = ROOT[chordAt(bar)];
  for (let b = 0; b < 4; b++) {
    if (o.kick === 'four' || (o.kick === 'half' && b % 2 === 0)) kick(bt(bar, b), o.kg || 1);
    if (o.clap && b % 2 === 1) clap(bt(bar, b), o.cg || 1);
    if (o.hats) { hat(bt(bar, b + 0.5), 1, o.open); if (o.hats > 1) { hat(bt(bar, b + 0.25), 0.5); hat(bt(bar, b + 0.75), 0.5); } }
  }
  if (o.bass) for (let e = 0; e < 8; e++) bass(bt(bar, e * 0.5), r + (e % 2 ? 12 : 0), BEAT * 0.45, o.bg || 1);
  if (o.arp) ARP(c).forEach((m, k) => { pluck(bt(bar, k * 0.5), m, o.ag || 1, k % 2 ? 0.4 : -0.4); if (o.arp > 1) pluck(bt(bar, k * 0.5 + 0.25), m + 12, (o.ag || 1) * 0.5, k % 2 ? -0.4 : 0.4); });
  if (o.pad) pad(bt(bar), c, BAR * 0.98, o.pg || 1, o.bright || 1);
}
function theme(bar, notes, g = 1, oct = 0) { for (const [b, m, d] of notes) lead(bt(bar, b), m + oct, d * BEAT * 0.95, g); }

// 1-2  cold open: drone + impact, pad swell
impact(bt(1), 0.9); pad(bt(1), [45, 52, 57, 60], BAR * 2, 1.3, 0.6); choir(bt(1, 2), [69, 72], BAR * 1.4, 0.7);
for (let k = 0; k < 8; k++) pluck(bt(2, k * 0.5), [69, 72, 76, 72, 81, 76, 72, 76][k], 0.6);
// 3-6  early game: light beat, MINA/VENDE/MEJORA hits on bars 4,5,6
for (let bar = 3; bar <= 6; bar++) groove(bar, { kick: bar === 3 ? 'half' : 'four', hats: 1, bass: bar >= 4, bg: 0.6, kg: 0.75, arp: 1, pad: 1, pg: 0.8, bright: 0.8, ag: 0.8 });
for (const bar of [4, 5, 6]) { tom(bt(bar), 45, 0.6); }
// 7  breakdown + riser into the "after 15 min" drop
pad(bt(7), [45, 52, 57, 64], BAR, 1.2, 0.5); riser(bt(7), BAR - 0.05, 1.2); for (let k = 0; k < 8; k++) clap(bt(7, 2 + k * 0.25), 0.25 + k * 0.08);
// 8-19 main groove with theme
for (let bar = 8; bar <= 19; bar++) {
  groove(bar, { kick: 'four', kg: 0.8, clap: 1, cg: 0.8, hats: bar >= 12 ? 2 : 1, bass: 1, bg: 0.75, arp: 1, ag: 0.8, pad: 1, pg: 0.8, bright: 1 });
  if ((bar - 8) % 4 === 0) crash(bt(bar), 0.7);
}
impact(bt(8), 1);
theme(10, THEME, 1); theme(14, THEME2, 1);
for (let k = 0; k < 4; k++) tom(bt(17, 3 + k * 0.25), 50 - k * 2, 0.6);
// 18-19 build to the jump
riser(bt(18), BAR * 2 - 0.05, 1.3);
for (let k = 0; k < 16; k++) clap(bt(19, k * 0.25), 0.2 + k * 0.05);
// 20-21 galaxy reveal: half time, choir, big
impact(bt(20), 1.2);
for (const bar of [20, 21]) { groove(bar, { kick: 'half', pad: 1, bright: 1.4, pg: 1.4 }); }
choir(bt(20), [69, 72, 76], BAR * 2, 1);
lead(bt(20), 81, BAR * 0.9, 0.8); lead(bt(21), 84, BAR * 0.45, 0.8); lead(bt(21, 2), 83, BAR * 0.45, 0.8);
riser(bt(21, 2), BAR / 2 - 0.05, 1);
// 22-31 the drop: full energy, theme up an octave
for (let bar = 22; bar <= 31; bar++) {
  groove(bar, { kick: 'four', clap: 1, cg: 1.1, hats: 2, open: bar % 2 === 0, bass: 1, bg: 1.1, arp: 2, pad: 1, bright: 1.5 });
  if (bar % 2 === 0) crash(bt(bar), 0.6);
}
impact(bt(22), 1.1);
theme(22, THEME, 1.1, 12); theme(24, THEME2, 1.1, 12); theme(26, THEME, 1.1, 12); theme(28, THEME2, 1.1, 12);
choir(bt(26), [69, 72, 76], BAR * 4, 0.6);
// 30-31 two-bar tom fill into the finale
for (let k = 0; k < 8; k++) tom(bt(31, k * 0.5), 52 - k, 0.7);
// 32-35 finale: epic build
for (let bar = 32; bar <= 35; bar++) { groove(bar, { kick: 'four', clap: 1, hats: 2, bass: 1, arp: 2, pad: 1, bright: 1.7, pg: 1.3 }); tom(bt(bar, 0), 45, 0.8); tom(bt(bar, 2.5), 48, 0.6); }
impact(bt(32), 1); choir(bt(32), [69, 72, 76, 81], BAR * 4, 1);
theme(32, THEME, 1.2, 12); theme(34, [[0, 84, 1], [1, 83, 1], [2, 81, 1], [3, 79, 1], [4, 81, 4]], 1.2, 0);
riser(bt(35), BAR - 0.05, 1.4);
// 36-40 title card: final hit and ring-out
impact(bt(36), 1.4); pad(bt(36), [45, 52, 57, 60, 64], BAR * 3, 1.6, 0.9); choir(bt(36), [69, 72, 76], BAR * 3, 1.1);
for (let k = 0; k < 8; k++) pluck(bt(37, k * 0.5), [81, 76, 72, 69, 72, 76, 81, 88][k], 0.5);
pluck(bt(39), 81, 0.7);

// whooshes into section changes and slams
for (const b of [4, 5, 6, 12, 14, 16, 23, 25, 27, 28, 30, 31]) whoosh(bt(b) - 0.45, 0.5, 0.8);
whoosh(bt(18) - 0.6, 0.8, 1);

// ---------------- fx busses & master ----------------
// tempo delay (dotted 8th), ping-pong
{ const d = t2i(BEAT * 0.75); for (let i = d; i < LEN; i++) { dlyL[i] += dlyR[i - d] * 0.45; dlyR[i] += dlyL[i - d] * 0.45; } for (let i = 0; i < LEN; i++) { L[i] += dlyR[i] * 0.5; R[i] += dlyL[i] * 0.5; revL[i] += dlyL[i] * 0.2; revR[i] += dlyR[i] * 0.2; } }
// Schroeder reverb
function reverb(inp, combs, aps) {
  const out = new Float32Array(LEN);
  for (const [dl, fb] of combs) { const buf = new Float32Array(dl); let p = 0, lp = 0; for (let i = 0; i < LEN; i++) { const y = buf[p]; lp = y * 0.6 + lp * 0.4; buf[p] = inp[i] + lp * fb; p = (p + 1) % dl; out[i] += y; } }
  for (const [dl, g] of aps) { const buf = new Float32Array(dl); let p = 0; for (let i = 0; i < LEN; i++) { const bv = buf[p]; const y = -out[i] * g + bv; buf[p] = out[i] + bv * g; p = (p + 1) % dl; out[i] = y; } }
  return out;
}
const rl = reverb(revL, [[1557, 0.86], [1617, 0.86], [1491, 0.86], [1422, 0.86], [1277, 0.86], [1356, 0.86]], [[225, 0.5], [556, 0.5], [441, 0.5]]);
const rr = reverb(revR, [[1580, 0.86], [1640, 0.86], [1514, 0.86], [1445, 0.86], [1300, 0.86], [1379, 0.86]], [[248, 0.5], [579, 0.5], [464, 0.5]]);
for (let i = 0; i < LEN; i++) { L[i] += rl[i] * 0.22; R[i] += rr[i] * 0.22; }
// master: soft clip + normalize, fade the tail
let peak = 0; for (let i = 0; i < LEN; i++) { L[i] = Math.tanh(L[i] * 0.9); R[i] = Math.tanh(R[i] * 0.9); peak = Math.max(peak, Math.abs(L[i]), Math.abs(R[i])); }
const fadeFrom = t2i(bt(39, 2)), endI = t2i(bt(41));
for (let i = 0; i < LEN; i++) { let g = 0.92 / peak; if (i > fadeFrom) g *= Math.max(0, 1 - (i - fadeFrom) / (endI - fadeFrom)); L[i] *= g; R[i] *= g; }
function wav(file, l, r, n = l.length) {
  const b = Buffer.alloc(44 + n * 4); b.write('RIFF', 0); b.writeUInt32LE(36 + n * 4, 4); b.write('WAVE', 8); b.write('fmt ', 12); b.writeUInt32LE(16, 16); b.writeUInt16LE(1, 20); b.writeUInt16LE(2, 22); b.writeUInt32LE(SR, 24); b.writeUInt32LE(SR * 4, 28); b.writeUInt16LE(4, 32); b.writeUInt16LE(16, 34); b.write('data', 36); b.writeUInt32LE(n * 4, 40);
  for (let i = 0; i < n; i++) { b.writeInt16LE(Math.round(Math.max(-1, Math.min(1, l[i])) * 32767), 44 + i * 4); b.writeInt16LE(Math.round(Math.max(-1, Math.min(1, r[i])) * 32767), 46 + i * 4); }
  fs.writeFileSync(file, b);
}
const PUB = path.join(__dirname, '..', 'public');
wav(path.join(PUB, 'music.wav'), L, R, endI);
console.log('music.wav', (endI / SR).toFixed(1), 's, peak', peak.toFixed(2));
