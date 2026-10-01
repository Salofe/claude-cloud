'use strict';
// ============ MUSIC: calm generative pieces that drift in now and then ============
// Like the soundtrack of a sandbox game: long silences, then a quiet piece fades in.
// Each piece has a fixed character (key, tempo, chords, instruments, form) but its
// melody is re-composed every time it plays, so it never sounds exactly the same.
// Everything is synthesized with WebAudio: electric piano, soft pads, bells, sub bass,
// all through a generated reverb.

const NOTE = m => 440 * Math.pow(2, (m - 69) / 12);
const MUSIC_VOL = 1.4;
// song form: intro, theme, variation, theme, variation, outro (~2 minutes)
const FORM = (a = 8, b = 8) => ['i', 'i', ...Array(a).fill('A'), ...Array(b).fill('B'), ...Array(a).fill('A'), ...Array(b / 2).fill('B'), 'o', 'o'];
const MUSIC = {
  bus: null, rev: null, on: true, playing: null, nextAt: 0, timer: null, rng: Math.random,
  init() {
    if (!AC || this.bus) return;
    try { this.on = localStorage.getItem('sp_music') !== '0'; } catch (e) {}
    this.bus = AC.createGain(); this.bus.gain.value = this.on ? MUSIC_VOL : 0; this.bus.connect(master);
    // reverb: 3.5 s of decaying stereo noise
    const len = AC.sampleRate * 3.5, buf = AC.createBuffer(2, len, AC.sampleRate);
    for (let c = 0; c < 2; c++) { const d = buf.getChannelData(c); for (let i = 0; i < len; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / len, 2.6); }
    this.rev = AC.createConvolver(); this.rev.buffer = buf;
    const wet = AC.createGain(); wet.gain.value = 0.55; this.rev.connect(wet); wet.connect(this.bus);
    this.dry = AC.createGain(); this.dry.gain.value = 0.6; this.dry.connect(this.bus); this.dry.connect(this.rev);
    this.nextAt = AC.currentTime + 25 + Math.random() * 20;   // first piece soon after you start
    this.ambAt = AC.currentTime + 12 + Math.random() * 15;
    this.timer = setInterval(() => this.tick(), 200);
  },
  setOn(v) { this.on = v; try { localStorage.setItem('sp_music', v ? '1' : '0'); } catch (e) {} if (this.bus) this.bus.gain.setTargetAtTime(v ? MUSIC_VOL : 0, AC.currentTime, 0.4); },
  // ---- instruments ----
  out(t, vol) { const g = AC.createGain(); g.gain.value = vol; g.connect(this.dry); return g; },
  epiano(m, t, dur, vol) {
    const o = this.out(t, 1), f = NOTE(m);
    for (const [mul, v, dec] of [[1, 1, 2.2], [2, 0.25, 0.9], [4, 0.08, 0.25]]) {
      const osc = AC.createOscillator(), g = AC.createGain();
      osc.type = 'sine'; osc.frequency.value = f * mul; osc.detune.value = (Math.random() - 0.5) * 6;
      g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol * v, t + 0.006);
      g.gain.exponentialRampToValueAtTime(vol * v * 0.3, t + Math.min(dur, dec) * 0.6);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur + 0.8);
      osc.connect(g); g.connect(o); osc.start(t); osc.stop(t + dur + 1);
    }
  },
  bell(m, t, vol) {
    const o = this.out(t, 1), f = NOTE(m);
    for (const [mul, v, dec] of [[1, 1, 2.5], [2.76, 0.35, 0.8], [5.4, 0.12, 0.3]]) {
      const osc = AC.createOscillator(), g = AC.createGain();
      osc.type = 'sine'; osc.frequency.value = f * mul;
      g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol * v, t + 0.004);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dec);
      osc.connect(g); g.connect(o); osc.start(t); osc.stop(t + dec + 0.1);
    }
  },
  pad(notes, t, dur, vol, bright) {
    const f = AC.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = bright || 900; f.Q.value = 0.4;
    const g = AC.createGain(); g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + Math.min(2.5, dur * 0.4));
    g.gain.setValueAtTime(vol, t + dur * 0.7); g.gain.exponentialRampToValueAtTime(0.0001, t + dur + 2.5);
    f.connect(g); g.connect(this.dry);
    for (const m of notes) for (const det of [-7, 7]) {
      const osc = AC.createOscillator(); osc.type = 'triangle'; osc.frequency.value = NOTE(m); osc.detune.value = det;
      osc.connect(f); osc.start(t); osc.stop(t + dur + 2.6);
    }
  },
  bass(m, t, dur, vol) {
    const osc = AC.createOscillator(), g = AC.createGain(); osc.type = 'sine'; osc.frequency.value = NOTE(m);
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol, t + 0.05); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    osc.connect(g); g.connect(this.dry); osc.start(t); osc.stop(t + dur + 0.1);
  },
  pulse(m, t, vol) {   // short plucked synth for the guardian theme
    const osc = AC.createOscillator(), f = AC.createBiquadFilter(), g = AC.createGain();
    osc.type = 'sawtooth'; osc.frequency.value = NOTE(m); f.type = 'lowpass'; f.frequency.setValueAtTime(2400, t); f.frequency.exponentialRampToValueAtTime(300, t + 0.25);
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol, t + 0.005); g.gain.exponentialRampToValueAtTime(0.0001, t + 0.3);
    osc.connect(f); f.connect(g); g.connect(this.dry); osc.start(t); osc.stop(t + 0.35);
  },
  // ---- playback ----
  play(id) {
    const P = PIECES[id]; if (!P || !AC) return;
    const beat = 60 / P.bpm, bar = beat * 4, bars = P.form.length;
    this.playing = { id, P, beat, bar, start: AC.currentTime + 0.3, nextBar: 0, bars, motif: this.motif(P) };
  },
  stop(fade) { if (this.playing) { this.playing.stopAt = this.playing.nextBar + (fade ? 1 : 0); } },
  // a 2-bar melodic idea built from the piece's scale; sections vary it
  motif(P) {
    const r = this.rng, notes = [];
    const rhythm = pick(P.rhythms);
    let deg = Math.floor(r() * 3) + 2;
    for (const at of rhythm) { deg = clamp(deg + pick([-2, -1, -1, 1, 1, 2, 0, 3, -3]), 0, P.scale.length - 1); notes.push({ at, deg }); }
    return notes;
  },
  // ---- ambience: rare distant sounds between pieces (radio chatter, solar wind, space whales…) ----
  pan(v) { const p = AC.createStereoPanner ? AC.createStereoPanner() : AC.createGain(); if (p.pan) p.pan.value = v; p.connect(this.dry); return p; },
  ambient(kind) {
    const t = AC.currentTime + 0.1, P = this.pan((Math.random() * 2 - 1) * 0.8);
    const osc = (type, f, t0, dur, vol, dest, f2) => {
      const o = AC.createOscillator(), g = AC.createGain(); o.type = type; o.frequency.setValueAtTime(f, t0);
      if (f2) o.frequency.exponentialRampToValueAtTime(f2, t0 + dur);
      g.gain.setValueAtTime(0.0001, t0); g.gain.exponentialRampToValueAtTime(vol, t0 + Math.min(0.02, dur / 3) + (dur > 1 ? dur * 0.3 : 0));
      g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur); o.connect(g); g.connect(dest || P); o.start(t0); o.stop(t0 + dur + 0.05); return o;
    };
    const hiss = (dur, vol, type, f0, f1, q) => {
      const buf = AC.createBuffer(1, Math.floor(AC.sampleRate * dur), AC.sampleRate), d = buf.getChannelData(0);
      for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
      const s = AC.createBufferSource(), f = AC.createBiquadFilter(), g = AC.createGain(); s.buffer = buf;
      f.type = type; f.Q.value = q || 1; f.frequency.setValueAtTime(f0, t); f.frequency.exponentialRampToValueAtTime(f1, t + dur);
      g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol, t + dur * 0.4); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      s.connect(f); f.connect(g); g.connect(P); s.start(t);
    };
    if (kind === 'radio') {   // a far-off transmission: crackle and a few beeps
      hiss(1.6, 0.025, 'bandpass', 2400, 1800, 4);
      const base = 900 + Math.random() * 700, n = 3 + Math.floor(Math.random() * 4);
      for (let i = 0; i < n; i++) osc('sine', base * pick([1, 1, 1.25, 1.5]), t + 0.2 + i * 0.16, 0.09, 0.02);
    } else if (kind === 'whale') {   // something huge singing in the dark
      const f = 140 + Math.random() * 80, o = osc('sine', f, t, 4.5, 0.05, null, f * pick([1.5, 0.66, 1.33]));
      const v = AC.createOscillator(), vg = AC.createGain(); v.frequency.value = 5; vg.gain.value = 6; v.connect(vg); vg.connect(o.frequency); v.start(t); v.stop(t + 4.6);
      osc('sine', f * 2.01, t + 0.4, 3.5, 0.012);
    } else if (kind === 'wind') {   // solar wind brushing the hull
      hiss(5, 0.03, 'bandpass', 300 + Math.random() * 300, 1400 + Math.random() * 800, 2.5);
    } else if (kind === 'creak') {   // the hull settling
      osc('sawtooth', 70 + Math.random() * 30, t, 0.9, 0.012, null, 50);
      osc('triangle', 210, t + 0.5, 0.6, 0.008, null, 160);
    } else {   // distant chimes from a station
      const sc = [72, 74, 76, 79, 81, 84], a = pick(sc);
      this.bell(a, t, 0.03); this.bell(pick(sc), t + 0.45, 0.022);
    }
  },
  tick() {
    if (!AC || !this.bus) return;
    const now = AC.currentTime;
    const pl = this.playing;
    if (!pl && this.on && now >= this.ambAt && scene !== TitleScene && !(scene === MineScene && MineScene.inCombat)) {
      this.ambAt = now + 35 + Math.random() * 45;
      this.ambient(pick(['radio', 'radio', 'whale', 'wind', 'wind', 'creak', 'chime']));
    }
    if (!pl) {
      if (scene === TitleScene) return;
      const boss = typeof MineScene !== 'undefined' && scene === MineScene && MineScene.enemies.some(e => ENEMIES[e.k].final);
      if (boss) { this.play('guardian'); return; }
      if (now >= this.nextAt && this.on) {
        const calm = Object.keys(PIECES).filter(k => !PIECES[k].combat && k !== this.last);
        this.last = pick(calm); this.play(this.last);
      }
      return;
    }
    // a guardian shows up: let the calm piece end at the bar line, the guardian theme takes over
    const bossNow = scene === MineScene && MineScene.enemies.some(e => ENEMIES[e.k].final);
    if (!pl.P.combat && bossNow && pl.stopAt == null) pl.stopAt = pl.nextBar;
    // the guardian theme stops when the boss is gone
    if (pl.P.combat && !(scene === MineScene && MineScene.enemies.some(e => ENEMIES[e.k].final)) && pl.stopAt == null) pl.stopAt = pl.nextBar + 1;
    while (pl.start + pl.nextBar * pl.bar < now + 1.2) {
      const i = pl.nextBar;
      if (i >= pl.bars || (pl.stopAt != null && i >= pl.stopAt)) {
        this.playing = null;
        this.nextAt = now + pl.bar * 2 + 150 + Math.random() * 180;   // 2.5–5.5 min of silence before the next piece
        return;
      }
      this.renderBar(pl, i, pl.start + i * pl.bar);
      pl.nextBar++;
    }
  },
  renderBar(pl, i, t) {
    const P = pl.P, b = pl.beat, sec = P.form[i], ch = P.chords[i % P.chords.length];
    const fadeIn = i < 2 ? (i + 1) / 3 : 1, fadeOut = i >= pl.bars - 2 ? (pl.bars - i) / 3 : 1, v = Math.min(fadeIn, fadeOut);
    if (P.pad) this.pad(ch.map(n => n + 12), t, pl.bar * 1.02, 0.035 * v, P.bright);
    if (P.bassOn && sec !== 'i') this.bass(ch[0] - 12, t, pl.bar * 0.95, 0.09 * v);
    if (P.combat) {   // driving pulses + arpeggio
      for (let s = 0; s < 8; s++) this.pulse(ch[0] - (s % 2 ? 0 : 12), t + s * b / 2, 0.05 * v);
      if (sec !== 'i') for (let s = 0; s < 8; s++) this.bell(ch[(s * 2) % ch.length] + 24, t + s * b / 2 + b / 4, 0.03 * v);
    }
    if (P.arp && sec !== 'i') for (let s = 0; s < 8; s++) {
      if (this.rng() < 0.18) continue;
      const m = ch[s % ch.length] + 12 * (1 + (s >> 2));
      P.arp === 'bell' ? this.bell(m, t + s * b / 2, 0.035 * v) : this.epiano(m, t + s * b / 2, b * 0.5, 0.03 * v);
    }
    if (P.comp && sec !== 'i' && sec !== 'o') { for (const n of ch.slice(1)) this.epiano(n, t, b * 3, 0.03 * v); if (this.rng() < 0.5) for (const n of ch.slice(1)) this.epiano(n, t + b * 2.5, b * 1.5, 0.022 * v); }
    // melody: sections A play the motif, B a varied/inverted version, i/o are quiet
    if (sec === 'A' || sec === 'B') {
      const half = i % 2, shift = sec === 'B' ? pick([2, -1, 3]) : 0;
      for (const n of pl.motif) {
        const bt = n.at - half * 4; if (bt < 0 || bt >= 4) continue;
        let deg = clamp(n.deg + shift, 0, P.scale.length - 1);
        if (sec === 'B' && this.rng() < 0.25) deg = clamp(P.scale.length - 1 - deg, 0, P.scale.length - 1);
        const m = P.scale[deg] + (P.lead === 'bell' ? 12 : 0);
        if (P.lead === 'bell') this.bell(m, t + bt * b, 0.07 * v); else this.epiano(m, t + bt * b, b * 1.6, 0.075 * v);
      }
    }
  },
};
// helper: chord voicings in MIDI numbers
const PIECES = {
  drift: { name: 'Drift', bpm: 64, pad: 1, bassOn: 1, lead: 'piano', bright: 800,
    scale: [62, 64, 65, 67, 69, 72, 74, 76, 77, 79],
    chords: [[38, 53, 57, 60, 64], [34, 50, 53, 57, 62], [41, 53, 57, 60, 64], [36, 52, 55, 60, 62]],
    rhythms: [[0, 1.5, 3, 4.5, 6], [0, 2, 3, 5, 7], [0, 1, 2.5, 4, 6.5]], form: FORM() },
  orbit: { name: 'Orbit', bpm: 78, pad: 1, arp: 'bell', lead: 'piano', bright: 1100,
    scale: [60, 62, 64, 66, 67, 69, 71, 72, 74, 76],
    chords: [[36, 52, 55, 59, 66], [38, 54, 57, 60, 64], [40, 55, 59, 62, 67], [33, 52, 55, 60, 64]],
    rhythms: [[0, 1, 2, 4, 5, 6], [0, 0.5, 1.5, 4, 4.5, 5.5]], form: FORM() },
  oldmoon: { name: 'Old Moon', bpm: 58, pad: 1, comp: 1, bassOn: 1, lead: 'piano', bright: 700,
    scale: [57, 59, 60, 62, 64, 65, 67, 69, 71, 72],
    chords: [[33, 52, 57, 60, 64], [29, 53, 57, 60, 65], [36, 52, 55, 60, 64], [31, 50, 55, 59, 62]],
    rhythms: [[0, 2, 3, 4, 6], [0, 1.5, 2, 4, 5.5, 6]], form: FORM() },
  starlight: { name: 'Starlight', bpm: 92, pad: 1, arp: 'piano', lead: 'bell', bright: 1400,
    scale: [64, 66, 68, 71, 73, 76, 78, 80, 83, 85],
    chords: [[40, 56, 59, 64, 68], [37, 56, 61, 64, 68], [33, 57, 61, 64, 69], [35, 54, 59, 63, 66]],
    rhythms: [[0, 1, 1.5, 3, 4, 5, 6.5], [0, 0.5, 1, 2, 4, 4.5, 5, 6]], form: FORM() },
  deepfield: { name: 'Deep Field', bpm: 50, pad: 1, bassOn: 1, lead: 'bell', bright: 500,
    scale: [60, 62, 63, 67, 68, 72, 74, 75, 79, 80],
    chords: [[36, 51, 55, 62, 67], [32, 51, 56, 60, 63], [29, 51, 56, 60, 65], [31, 50, 55, 59, 62]],
    rhythms: [[0, 3, 5], [0, 2.5, 6], [1, 4, 6.5]], form: FORM() },
  homeward: { name: 'Homeward', bpm: 72, pad: 1, comp: 1, bassOn: 1, lead: 'piano', bright: 900,
    scale: [65, 67, 69, 70, 72, 74, 76, 77, 79, 81],
    chords: [[41, 57, 60, 64, 69], [45, 55, 60, 64, 67], [46, 57, 62, 65, 69], [48, 55, 60, 64, 70]],
    rhythms: [[0, 1, 2, 3, 4.5, 6], [0, 1.5, 2, 3.5, 4, 6]], form: FORM() },
  guardian: { name: 'Guardian', bpm: 118, combat: 1, pad: 1, bassOn: 1, lead: 'bell', bright: 1200,
    scale: [62, 65, 67, 69, 72, 74, 77, 79, 81, 84],
    chords: [[38, 50, 53, 57, 62], [34, 50, 53, 58, 62], [36, 52, 55, 60, 64], [33, 49, 52, 57, 61]],
    rhythms: [[0, 1, 2, 3, 4, 5, 6, 7], [0, 1.5, 2, 3, 4, 5.5, 6, 7]], form: Array(64).fill('A').map((s, i) => i < 2 ? 'i' : i % 8 >= 4 ? 'B' : 'A') },
};
