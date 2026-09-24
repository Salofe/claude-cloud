'use strict';
// ============ AUDIO SINTETIZADO ============
let AC = null, master = null, muted = false;
try { muted = localStorage.getItem('sp_muted') === '1'; } catch (e) {}
function audioInit() {
  if (AC) { if (AC.state === 'suspended') AC.resume(); return; }
  try {
    AC = new (window.AudioContext || window.webkitAudioContext)();
    master = AC.createGain(); master.gain.value = muted ? 0 : 0.45; master.connect(AC.destination);
    startAmbient();
  } catch (e) { AC = null; }
}
function setMuted(m) {
  muted = m; try { localStorage.setItem('sp_muted', m ? '1' : '0'); } catch (e) {}
  if (master) master.gain.value = m ? 0 : 0.45;
}
function tone(freq, dur, type, vol, slide, delay) {
  if (!AC) return;
  const t = AC.currentTime + (delay || 0);
  const o = AC.createOscillator(), g = AC.createGain();
  o.type = type || 'sine'; o.frequency.setValueAtTime(freq, t);
  if (slide) o.frequency.exponentialRampToValueAtTime(Math.max(20, slide), t + dur);
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(vol || 0.2, t + 0.01);
  g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  o.connect(g); g.connect(master); o.start(t); o.stop(t + dur + 0.05);
}
function noise(dur, vol, filt, delay) {
  if (!AC) return;
  const t = AC.currentTime + (delay || 0);
  const buf = AC.createBuffer(1, Math.floor(AC.sampleRate * dur), AC.sampleRate);
  const d = buf.getChannelData(0);
  for (let i = 0; i < d.length; i++) d[i] = (Math.random() * 2 - 1) * (1 - i / d.length);
  const s = AC.createBufferSource(); s.buffer = buf;
  const f = AC.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = filt || 1200;
  const g = AC.createGain(); g.gain.value = vol || 0.3;
  s.connect(f); f.connect(g); g.connect(master); s.start(t);
}
function sfx(name) {
  if (!AC) return;
  switch (name) {
    case 'click': tone(880, 0.06, 'square', 0.05); break;
    case 'pickup': tone(1200 + Math.random() * 300, 0.08, 'sine', 0.08, 1800); break;
    case 'break': noise(0.25, 0.25, 900); tone(140, 0.2, 'triangle', 0.12, 60); break;
    case 'boom': noise(0.7, 0.5, 600); tone(90, 0.6, 'sawtooth', 0.15, 30); break;
    case 'hit': noise(0.08, 0.15, 3000); break;
    case 'shoot': tone(700, 0.08, 'square', 0.04, 300); break;
    case 'eshoot': tone(420, 0.1, 'sawtooth', 0.035, 180); break;
    case 'shield': tone(300, 0.15, 'sine', 0.08, 600); break;
    case 'cash': tone(1318, 0.08, 'square', 0.06); tone(1760, 0.18, 'square', 0.06, null, 0.08); break;
    case 'upgrade': [523, 659, 784, 1046].forEach((f, i) => tone(f, 0.18, 'triangle', 0.1, null, i * 0.07)); break;
    case 'alarm': tone(660, 0.18, 'square', 0.07); tone(440, 0.18, 'square', 0.07, null, 0.2); tone(660, 0.18, 'square', 0.07, null, 0.4); break;
    case 'warp': tone(120, 0.9, 'sawtooth', 0.06, 900); noise(0.9, 0.08, 2000); break;
    case 'event': tone(392, 0.2, 'triangle', 0.08); tone(523, 0.3, 'triangle', 0.08, null, 0.18); break;
    case 'win': [523, 659, 784, 1046, 1318].forEach((f, i) => tone(f, 0.3, 'triangle', 0.1, null, i * 0.1)); break;
    case 'lose': [392, 330, 262, 196].forEach((f, i) => tone(f, 0.35, 'sawtooth', 0.06, null, i * 0.15)); break;
    case 'bump': tone(80, 0.15, 'sine', 0.2, 40); break;
    case 'full': tone(300, 0.12, 'square', 0.05); tone(220, 0.15, 'square', 0.05, null, 0.12); break;
  }
}
// Láser continuo
let laserNode = null;
function laserSound(on, lv) {
  if (!AC) return;
  if (on && !laserNode) {
    const o = AC.createOscillator(), o2 = AC.createOscillator(), g = AC.createGain(), f = AC.createBiquadFilter();
    o.type = 'sawtooth'; o.frequency.value = 110 + lv * 20; o2.type = 'sine'; o2.frequency.value = 220 + lv * 40;
    f.type = 'lowpass'; f.frequency.value = 900;
    g.gain.value = 0.0001; g.gain.exponentialRampToValueAtTime(0.05, AC.currentTime + 0.05);
    o.connect(f); o2.connect(f); f.connect(g); g.connect(master); o.start(); o2.start();
    laserNode = { o, o2, g };
  } else if (!on && laserNode) {
    const n = laserNode; laserNode = null;
    n.g.gain.exponentialRampToValueAtTime(0.0001, AC.currentTime + 0.08);
    n.o.stop(AC.currentTime + 0.1); n.o2.stop(AC.currentTime + 0.1);
  }
}
// Ambiente: drone espacial suave
function startAmbient() {
  if (!AC) return;
  const g = AC.createGain(); g.gain.value = 0.05; g.connect(master);
  const f = AC.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = 500; f.connect(g);
  [55, 82.4, 110.2, 164.8].forEach((fr, i) => {
    const o = AC.createOscillator(); o.type = i % 2 ? 'triangle' : 'sine'; o.frequency.value = fr;
    const lfo = AC.createOscillator(), lg = AC.createGain();
    lfo.frequency.value = 0.05 + i * 0.03; lg.gain.value = 0.4;
    const og = AC.createGain(); og.gain.value = 0.5;
    lfo.connect(lg); lg.connect(og.gain);
    o.connect(og); og.connect(f); o.start(); lfo.start();
  });
}
