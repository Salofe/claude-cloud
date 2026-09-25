'use strict';
// ============ SCENE: SOLAR SYSTEM MAP ============
const BELT = []; const KUIPER = [];
(function () {
  let s = 3; const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
  const cols = ['#c9b8a0', '#a89a88', '#d9c6a8', '#8f8577', '#b7a58c'];
  for (let i = 0; i < 900; i++) BELT.push({ a: r() * TAU, r: 238 + (r() + r() + r() - 1.5) * 34, s: 0.6 + r() * 1.6, sp: 0.9 + r() * 0.2, c: cols[Math.floor(r() * cols.length)] });
  for (let i = 0; i < 600; i++) KUIPER.push({ a: r() * TAU, r: 585 + (r() + r() - 1) * 60, s: 0.6 + r() * 1.5, sp: 0.95 + r() * 0.1, c: r() > 0.5 ? '#a9c2ff' : '#d0dcff' });
})();

const MapScene = {
  cam: { x: 0, y: 0, z: 1 }, camT: null, sel: null, travel: null, t: 0, hover: null, drag: null, trail: new Particles(),
  enter() {
    if (this.travel) { $('travelBanner').classList.remove('hidden'); return; }
    this.focus(S.loc, true);
    showMapUI(true);
    selectLoc(this.sel || S.loc);
  },
  exit() { showMapUI(false); },
  focus(id, instant) {
    const p = locPos(id, S.day);
    const z = clamp(Math.min(W, H) / 2 / (Math.hypot(p.x, p.y) * 0.5 + 120), 0.45, 2.4);
    const t = { x: p.x * 0.6, y: p.y * 0.6, z };
    if (instant) Object.assign(this.cam, t); else this.camT = t;
  },
  zoomAll() {
    let m = 0; for (const l of NODES) if (locOpen(l.id)) { const p = locPos(l.id, S.day); m = Math.max(m, Math.hypot(p.x, p.y)); }
    this.camT = { x: 0, y: 0, z: Math.min(W, H) / 2 / (m + 70) };
  },
  w2s(x, y) { return { x: (x - this.cam.x) * this.cam.z + W / 2, y: (y - this.cam.y) * this.cam.z + H / 2 }; },
  s2w(x, y) { return { x: (x - W / 2) / this.cam.z + this.cam.x, y: (y - H / 2) / this.cam.z + this.cam.y }; },
  pr(loc) { return loc.size * clamp(this.cam.z * 1.5, 1, 3.4); },
  spos(loc, day) {
    if (typeof loc === 'string') loc = LOC[loc];
    if (day == null) day = S.day + (this.travel ? this.travel.frac : 0);
    if (loc.parent) {
      const par = LOC[loc.parent];
      const pp = this.spos(par, day);
      const a = loc.a0 + day / loc.period * TAU;
      const d = Math.max(loc.r * this.cam.z, this.pr(par) + this.pr(loc) + 14);
      return { x: pp.x + Math.cos(a) * d, y: pp.y + Math.sin(a) * d };
    }
    const p = locPos(loc, day);
    return this.w2s(p.x, p.y);
  },
  routeCurve(a, b) {
    const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
    const sun = this.w2s(0, 0);
    let nx = -(b.y - a.y), ny = b.x - a.x; const nl = Math.hypot(nx, ny) || 1; nx /= nl; ny /= nl;
    if ((mx - sun.x) * nx + (my - sun.y) * ny < 0) { nx = -nx; ny = -ny; }
    const bend = Math.min(90, nl * 0.22);
    return { a, b, c: { x: mx + nx * bend, y: my + ny * bend } };
  },
  bez(q, t) { const u = 1 - t; return { x: u * u * q.a.x + 2 * u * t * q.c.x + t * t * q.b.x, y: u * u * q.a.y + 2 * u * t * q.c.y + t * t * q.b.y }; },
  update(dt) {
    this.t += dt;
    this.trail.update(dt);
    const tr = this.travel;
    if (tr && !tr.paused) {
      tr.el += dt;
      const p = clamp(tr.el / tr.dur, 0, 1);
      const dayNow = Math.floor(p * tr.days);
      while (tr.dayDone < dayNow) { tr.dayDone++; tickDay(); }
      tr.frac = p * tr.days - dayNow;
      if (tr.enc && !tr.encDone && p >= tr.enc.at) { tr.encDone = true; tr.paused = true; runEncounter(tr.enc, () => { tr.paused = false; }); }
      if (p >= 1 && !tr.paused) return this.arrive();
      // camera follows the ship
      if (tr.shipPos) {
        const w = this.s2w(tr.shipPos.x, tr.shipPos.y);
        const k = 1 - Math.pow(0.15, dt);
        this.cam.x = lerp(this.cam.x, w.x, k * 0.6); this.cam.y = lerp(this.cam.y, w.y, k * 0.6);
      }
    } else if (this.camT) {
      const k = 1 - Math.pow(0.02, dt);
      this.cam.x = lerp(this.cam.x, this.camT.x, k); this.cam.y = lerp(this.cam.y, this.camT.y, k); this.cam.z = lerp(this.cam.z, this.camT.z, k);
      if (Math.abs(this.cam.z - this.camT.z) < 0.001 && Math.abs(this.cam.x - this.camT.x) < 0.5) this.camT = null;
    }
  },
  startTravel(to) {
    const info = travelInfo(to);
    if (info.fuel > S.fuel) { toast('Not enough fuel', 'bad'); sfx('full'); return; }
    if (S.loc === to) return;
    S.fuel -= info.fuel;
    const dur = built('gates') ? 1.1 : clamp(1.2 + info.days * 0.3, 1.6, 6);
    let enc = null;
    if (Math.random() < info.danger) enc = { kind: 'hostile', at: rand(0.3, 0.7), danger: info.danger };
    else if (Math.random() < 0.22 + info.days * 0.01) enc = { kind: 'random', at: rand(0.25, 0.75), danger: info.danger };
    const war = S.events.find(e => e.war && (e.locs.includes(to) || e.locs.includes(S.loc)));
    if (war && !enc && Math.random() < 0.45) enc = { kind: 'patrol', at: rand(0.3, 0.7), war };
    const storm = S.events.find(e => e.storm && (e.storm.includes(to) || e.storm.includes(S.loc)));
    this.travel = { from: S.loc, to, days: info.days, dur, el: 0, dayDone: 0, frac: 0, enc, encDone: false, storm };
    S.stats.dist += info.d;
    sfx('warp');
    showMapUI(false); hideLocPanel();
    const tb = $('travelBanner');
    tb.classList.remove('hidden');
    tb.innerHTML = `Flying to <b>${LOC[to].n}</b> · ${info.days} day${info.days > 1 ? 's' : ''}`;
    const p = locPos(S.loc, S.day), q = locPos(to, S.day);
    const span = Math.max(Math.abs(p.x - q.x), Math.abs(p.y - q.y)) / 2 + 110;
    this.camT = null;
    this.zoomTarget = clamp(Math.min(W, H) / 2 / span, 0.45, 2.2);
    this.cam.z = lerp(this.cam.z, this.zoomTarget, 0.5);
  },
  arrive() {
    const tr = this.travel; this.travel = null;
    S.loc = tr.to;
    $('travelBanner').classList.add('hidden');
    if (tr.storm) {
      const dmg = Math.max(0, randi(8, 20) - ship.shieldMax * 0.15);
      S.hull = Math.max(1, S.hull - dmg);
      if (dmg) toast(`The solar storm damaged your hull (−${Math.round(dmg)})`, 'bad');
    }
    save();
    this.focus(S.loc);
    updateHUD();
    openDock();
  },
  draw(ctx) {
    const t = this.t;
    const tr = this.travel;
    if (tr && this.zoomTarget) this.cam.z = lerp(this.cam.z, this.zoomTarget, 0.03);
    drawSpaceBg(ctx, W, H, this.cam.x * this.cam.z, this.cam.y * this.cam.z, t);
    const z = this.cam.z;
    const sun = this.w2s(0, 0);
    const day = S.day + (tr ? tr.frac : 0);
    // orbits with bright trailing arc
    for (const l of LOCS) {
      if (l.parent || l.follow) continue;
      const R = l.r * z, open = locOpen(l.id);
      ctx.strokeStyle = open ? 'rgba(120,170,255,0.16)' : 'rgba(120,170,255,0.06)'; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.arc(sun.x, sun.y, R, 0, TAU); ctx.stroke();
      if (open && l.id !== 'kuiper') {
        const a = l.a0 + day / l.period * TAU;
        for (let i = 0; i < 12; i++) {
          ctx.strokeStyle = `rgba(120,200,255,${0.32 * (1 - i / 12)})`; ctx.lineWidth = 2;
          ctx.beginPath(); ctx.arc(sun.x, sun.y, R, a - (i + 1) * 0.05, a - i * 0.05); ctx.stroke();
        }
      }
    }
    // belts
    const beltOpen = has(U.BELT), kOpen = has(U.FRONTIER);
    for (const b of BELT) { const a = b.a + day / 560 * TAU * b.sp; ctx.globalAlpha = beltOpen ? 0.75 : 0.3; ctx.fillStyle = b.c; ctx.fillRect(sun.x + Math.cos(a) * b.r * z, sun.y + Math.sin(a) * b.r * z, b.s, b.s); }
    for (const b of KUIPER) { const a = b.a + day / 3300 * TAU * b.sp; ctx.globalAlpha = kOpen ? 0.6 : 0.2; ctx.fillStyle = b.c; ctx.fillRect(sun.x + Math.cos(a) * b.r * z, sun.y + Math.sin(a) * b.r * z, b.s, b.s); }
    ctx.globalAlpha = 1;
    const tp = this.spos('troyanos', day);
    ctx.fillStyle = locOpen('troyanos') ? 'rgba(210,190,160,0.75)' : 'rgba(210,190,160,0.25)';
    for (let i = 0; i < 50; i++) { const a = i * 2.4 + t * 0.02, rr = (i % 9) * 2.6 * clamp(z, 0.8, 2.2); ctx.fillRect(tp.x + Math.cos(a) * rr, tp.y + Math.sin(a) * rr * 0.8, 1.6, 1.6); }
    drawSun(ctx, sun.x, sun.y, clamp(15 * z, 10, 36), t);
    if (built('dyson')) {
      const R = clamp(15 * z, 10, 36) * 2.6;
      ctx.strokeStyle = 'rgba(255,210,74,0.35)'; ctx.lineWidth = 1;
      for (let k = 0; k < 3; k++) { ctx.beginPath(); ctx.ellipse(sun.x, sun.y, R * (1 + k * 0.15), R * (0.35 + k * 0.1), k * 1.1 + t * 0.05, 0, TAU); ctx.stroke(); }
      ctx.fillStyle = '#ffe9a0';
      for (let i = 0; i < 140; i++) { const a = i * 2.39996 + t * (0.2 + (i % 5) * 0.05), rr = R * (0.8 + (i % 7) * 0.08); ctx.fillRect(sun.x + Math.cos(a) * rr, sun.y + Math.sin(a) * rr * (0.5 + (i % 3) * 0.2), 1.6, 1.6); }
    }
    if (built('beacons')) {
      for (const id of ['mercurio', 'venus', 'tierra', 'marte', 'ceres']) {
        const R = LOC[id].r * z;
        for (let i = 0; i < 8; i++) { const a = i * TAU / 8 + id.length; const on = Math.sin(t * 3 + i + id.length) > 0.3; ctx.fillStyle = on ? '#3de8ff' : 'rgba(61,232,255,0.3)'; ctx.fillRect(sun.x + Math.cos(a) * R - 1.5, sun.y + Math.sin(a) * R - 1.5, 3, 3); }
      }
    }
    // route preview
    const selId = this.sel;
    if (!tr && selId && selId !== S.loc && locOpen(selId)) {
      const q = this.routeCurve(this.spos(S.loc), this.spos(selId));
      const ok = travelInfo(selId).fuel <= S.fuel;
      ctx.setLineDash([7, 7]); ctx.lineDashOffset = -t * 24;
      ctx.strokeStyle = ok ? 'rgba(61,232,255,0.9)' : 'rgba(255,90,110,0.85)'; ctx.lineWidth = 2.2;
      ctx.beginPath(); ctx.moveTo(q.a.x, q.a.y); ctx.quadraticCurveTo(q.c.x, q.c.y, q.b.x, q.b.y); ctx.stroke();
      ctx.setLineDash([]);
    }
    // bodies
    for (const l of LOCS) {
      if (l.id === 'troyanos') continue;
      const p = this.spos(l, day);
      const r = this.pr(l);
      const open = l.body ? locOpen(l.id) : locOpen(l.id);
      ctx.globalAlpha = open ? 1 : 0.35;
      const la = Math.atan2(sun.y - p.y, sun.x - p.x);
      if (l.id === 'kuiper') {
        glow(ctx, p.x, p.y, r * 2.5, '#9fb6ff66', 0.7);
        ctx.fillStyle = '#c9d6ff';
        for (let i = 0; i < 11; i++) { const a = i * 0.7 + t * 0.1; ctx.beginPath(); ctx.arc(p.x + Math.cos(a) * r * (0.4 + (i % 3) * 0.45), p.y + Math.sin(a * 1.3) * r * 0.8, 1.7, 0, TAU); ctx.fill(); }
      } else drawPlanet(ctx, p.x, p.y, r, l, la, t);
      ctx.globalAlpha = 1;
    }
    this.drawProjects(ctx, t, day);
    // node markers & labels
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    for (const l of NODES) {
      const p = this.spos(l, day);
      const open = locOpen(l.id);
      const r = this.pr(l) + (l.id === 'troyanos' ? 10 : 0);
      const isSel = l.id === selId, isHere = l.id === S.loc && !tr, isHov = l.id === this.hover;
      if (open && l.station) {
        const a = t * 0.6 + (l.r || 3);
        const sx = p.x + Math.cos(a) * (r + 8), sy = p.y + Math.sin(a) * (r + 8) * 0.6;
        drawStationIcon(ctx, sx, sy, 2.6, l.faction ? FACTIONS[l.faction].c : '#6dffb0', t);
      }
      if (isHere) {
        const pr = r + 10 + (t * 16 % 16);
        ctx.strokeStyle = `rgba(61,232,255,${0.7 * (1 - (t * 16 % 16) / 16)})`; ctx.lineWidth = 2;
        ctx.beginPath(); ctx.arc(p.x, p.y, pr, 0, TAU); ctx.stroke();
      }
      if (isSel || isHov) {
        ctx.strokeStyle = isSel ? '#3de8ff' : 'rgba(61,232,255,0.5)'; ctx.lineWidth = 2;
        const rr = r + 8 + Math.sin(t * 4) * 1.5;
        for (let i = 0; i < 4; i++) { const a0 = i * TAU / 4 + t * 0.8; ctx.beginPath(); ctx.arc(p.x, p.y, rr, a0, a0 + 0.9); ctx.stroke(); }
      }
      // label pill
      const label = open ? l.n.toUpperCase() : '🔒 ' + l.n.toUpperCase();
      ctx.font = `700 ${isSel ? 12 : 11}px Rajdhani, sans-serif`;
      const tw = ctx.measureText(label).width + 14, ly = p.y + r + 14;
      ctx.globalAlpha = open ? 1 : 0.55;
      ctx.fillStyle = isSel ? 'rgba(61,232,255,0.22)' : 'rgba(6,12,30,0.72)';
      roundRect(ctx, p.x - tw / 2, ly - 8, tw, 16, 8); ctx.fill();
      ctx.strokeStyle = isSel ? '#3de8ff' : 'rgba(120,170,255,0.25)'; ctx.lineWidth = 1; ctx.stroke();
      ctx.fillStyle = isSel ? '#ffffff' : '#cfe0ff';
      ctx.fillText(label, p.x, ly + 0.5);
      ctx.globalAlpha = 1;
      if (open) {
        let icons = '';
        if (l.field) icons += '⛏';
        const evs = S.events.filter(e => e.locs && e.locs.includes(l.id));
        for (const e of evs) icons += e.icon;
        const dg = locDanger(l.id);
        if (dg >= 0.2) icons += dg > 0.45 ? '☠☠' : '☠';
        if (S.active.some(c => c.type === 'deliver' && c.to === l.id)) icons += '📜';
        if (icons) { ctx.font = '12px sans-serif'; ctx.fillText(icons, p.x, p.y - r - 10); }
      }
    }
    ctx.textBaseline = 'alphabetic';
    // player ship
    if (tr) {
      const q = this.routeCurve(this.spos(tr.from), this.spos(tr.to));
      const p = clamp(tr.el / tr.dur, 0, 1), e = p < 0.5 ? 2 * p * p : 1 - Math.pow(-2 * p + 2, 2) / 2;
      const sp = this.bez(q, e), sp2 = this.bez(q, Math.min(1, e + 0.01));
      const ang = Math.atan2(sp2.y - sp.y, sp2.x - sp.x);
      tr.shipPos = sp;
      ctx.strokeStyle = 'rgba(61,232,255,0.25)'; ctx.lineWidth = 1.5; ctx.setLineDash([3, 6]);
      ctx.beginPath(); ctx.moveTo(q.a.x, q.a.y); ctx.quadraticCurveTo(q.c.x, q.c.y, q.b.x, q.b.y); ctx.stroke(); ctx.setLineDash([]);
      const ec = ENGINE_COL[shipLv().engine - 1];
      if (!tr.paused) for (let i = 0; i < 2; i++) this.trail.add(sp.x - Math.cos(ang) * 10 + rand(-2, 2), sp.y - Math.sin(ang) * 10 + rand(-2, 2), -Math.cos(ang) * 20 + rand(-8, 8), -Math.sin(ang) * 20 + rand(-8, 8), 0.8, ec, 2.2);
      this.trail.draw(ctx);
      drawPlayerShip(ctx, shipLv(), sp.x, sp.y, ang, 0.55, 1, t);
      if (built('fleet')) for (const o of [-1, 1]) drawPlayerShip(ctx, { hull: 1, engine: 3, weapons: 3, laser: 1 }, sp.x - Math.cos(ang) * 14 - Math.sin(ang) * o * 12, sp.y - Math.sin(ang) * 14 + Math.cos(ang) * o * 12, ang, 0.3, 1, t);
    } else {
      this.trail.draw(ctx);
      const p = this.spos(S.loc);
      const r = this.pr(LOC[S.loc]) + 16;
      const a = t * 0.7;
      drawPlayerShip(ctx, shipLv(), p.x + Math.cos(a) * r, p.y + Math.sin(a) * r, a + Math.PI / 2, 0.42, 0.5, t);
    }
  },
  drawProjects(ctx, t, day) {
    if (built('driver')) {
      const a = this.spos('luna', day), b = this.spos('tierra', day);
      ctx.strokeStyle = 'rgba(255,210,74,0.35)'; ctx.lineWidth = 1.5; ctx.setLineDash([2, 4]);
      ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke(); ctx.setLineDash([]);
      for (let i = 0; i < 3; i++) { const k = (t * 0.8 + i / 3) % 1; glow(ctx, lerp(a.x, b.x, k), lerp(a.y, b.y, k), 5, '#ffd24a', 0.9); }
    }
    if (built('elevator')) {
      const e = this.spos('tierra', day), sun = this.w2s(0, 0), r = this.pr(LOC.tierra);
      const a = Math.atan2(e.y - sun.y, e.x - sun.x) + 2.2, L = r * 2.4;
      ctx.strokeStyle = 'rgba(220,235,255,0.8)'; ctx.lineWidth = 1.2;
      ctx.beginPath(); ctx.moveTo(e.x + Math.cos(a) * r, e.y + Math.sin(a) * r); ctx.lineTo(e.x + Math.cos(a) * L, e.y + Math.sin(a) * L); ctx.stroke();
      drawStationIcon(ctx, e.x + Math.cos(a) * L, e.y + Math.sin(a) * L, 2.4, '#ffd24a', t);
    }
    if (built('ringstation')) {
      const p = this.spos('saturno', day), r = this.pr(LOC.saturno);
      const a = t * 0.3;
      glow(ctx, p.x + Math.cos(a) * r * 1.9, p.y + Math.sin(a) * r * 0.55, 10, '#ffd24a', 0.9);
      drawStationIcon(ctx, p.x + Math.cos(a) * r * 1.9, p.y + Math.sin(a) * r * 0.55, 3, '#ffd24a', t);
    }
    if (built('gates')) {
      for (const l of NODES) if (l.station && locOpen(l.id)) {
        const p = this.spos(l, day), r = this.pr(l) + 20;
        ctx.strokeStyle = `rgba(180,120,255,${0.5 + 0.3 * Math.sin(t * 4 + (l.r || 3))})`; ctx.lineWidth = 2;
        ctx.beginPath(); ctx.ellipse(p.x - r, p.y, 3, 7, 0, 0, TAU); ctx.stroke();
        glow(ctx, p.x - r, p.y, 8, '#a07cff', 0.6);
      }
    }
  },
  pick(x, y) {
    let best = null, bd = 1e9;
    for (const l of NODES) {
      const p = this.spos(l);
      const d = Math.hypot(p.x - x, p.y - y);
      const hit = Math.max(22, this.pr(l) + 14);
      if (d < hit && d < bd) { bd = d; best = l.id; }
    }
    return best;
  },
  onDown(x, y) { this.drag = { x, y, cx: this.cam.x, cy: this.cam.y, moved: false }; },
  onMove(x, y, down) {
    if (down && this.drag) {
      const dx = x - this.drag.x, dy = y - this.drag.y;
      if (Math.hypot(dx, dy) > 6) this.drag.moved = true;
      if (this.drag.moved && !this.travel) { this.camT = null; this.cam.x = this.drag.cx - dx / this.cam.z; this.cam.y = this.drag.cy - dy / this.cam.z; }
    } else this.hover = this.travel ? null : this.pick(x, y);
    canvas.style.cursor = this.hover ? 'pointer' : 'default';
  },
  onUp(x, y) {
    if (this.drag && !this.drag.moved && !this.travel) {
      const id = this.pick(x, y);
      if (id) { selectLoc(id); sfx('click'); }
    }
    this.drag = null;
  },
  onWheel(dy, x, y) {
    if (this.travel) return;
    const before = this.s2w(x, y);
    this.camT = null;
    this.cam.z = clamp(this.cam.z * Math.pow(1.0015, -dy), 0.35, 3.5);
    const after = this.s2w(x, y);
    this.cam.x += before.x - after.x; this.cam.y += before.y - after.y;
  },
  onPinch(scale, x, y) { this.onWheel(-Math.log(scale) / Math.log(1.0015), x, y); },
};

// ============ TRAVEL ENCOUNTERS ============
function runEncounter(enc, done) {
  if (enc.kind === 'hostile') return pirateEncounter(enc.danger, done);
  if (enc.kind === 'patrol') return patrolEncounter(enc.war, done);
  const opts = ['derelict', 'comet', 'meteor', 'derelict', 'comet'];
  if (has(U.BELT)) opts.push('distress', 'distress');
  if (has(U.TRADE)) opts.push('trader');
  const k = pick(opts);
  const trap = has(U.BELT);
  if (k === 'derelict') {
    showModal({ icon: '🛰️', title: 'Drifting wreck', html: 'Your sensors spot an abandoned freighter. It might have cargo on board…' + (trap ? ' or it might be bait.' : ''),
      buttons: [
        { label: 'Salvage it', cls: 'primary', fn: () => {
          if (trap && Math.random() < 0.22 - ship.avoid * 0.3) { toast('It was a trap!', 'bad'); sfx('alarm'); return pirateEncounter(enc.danger + 0.1, done); }
          const pool = has(U.TRADE) ? ITEM_KEYS : ORES.slice(0, 5);
          const it = pick(pool); const n = Math.min(cargoFree(), randi(3, 6 + S.lv.hull * 3));
          if (n > 0) { addCargo(it, n); toast(`+${n} ${ITEMS[it].n}`, 'good'); sfx('pickup'); } else toast('Cargo hold full — nothing to take', 'bad');
          done();
        } },
        { label: 'Ignore', fn: done },
      ] });
  } else if (k === 'distress') {
    const fac = pick(['tierra', 'marte', 'cinturon', 'exterior']);
    showModal({ icon: '🆘', title: 'Distress signal', html: `A <b style="color:${FACTIONS[fac].c}">${FACTIONS[fac].n}</b> ship's life support is failing. Helping costs 5 fuel.`,
      buttons: [
        { label: 'Help (−5 ⛽)', cls: 'primary', disabled: S.fuel < 5, fn: () => {
          S.fuel -= 5;
          if (Math.random() < 0.18) { toast('Pirate ambush!', 'bad'); sfx('alarm'); return pirateEncounter(enc.danger + 0.15, done); }
          const cr = randi(150, 400) + S.day * 4; repChange(fac, 6); earn(cr);
          toast(`They pay you ${fmt(cr)} cr for the rescue`, 'good'); sfx('cash'); done();
        } },
        { label: 'Ignore', fn: () => { repChange(fac, -1, true); done(); } },
      ] });
  } else if (k === 'trader') {
    const items = Object.keys(S.cargo);
    if (!items.length) return done();
    const it = pick(items); const n = S.cargo[it]; const price = Math.round(ITEMS[it].b * rand(1.15, 1.45));
    showModal({ icon: '🧑‍🚀', title: 'Wandering trader', html: `An independent trader offers to buy your <b>${n} ${ITEMS[it].n}</b> for <b>${price} cr</b> each.`,
      buttons: [
        { label: `Sell (${fmt(n * price)} cr)`, cls: 'primary', fn: () => { addCargo(it, -n); earn(n * price); sfx('cash'); done(); } },
        { label: 'No thanks', fn: done },
      ] });
  } else if (k === 'meteor') {
    const dmg = Math.max(0, randi(4, 12) - ship.shieldMax * 0.2);
    S.hull = Math.max(1, S.hull - dmg);
    showModal({ icon: '☄️', title: 'Micrometeor shower', html: dmg > 0 ? `You fly through a dust cloud. Your hull takes <b>${Math.round(dmg)}</b> damage.` : 'Your shields deflect every impact. Not a scratch!',
      buttons: [{ label: 'Continue', cls: 'primary', fn: done }] });
    sfx('hit');
  } else {
    const n = Math.min(cargoFree(), randi(6, 14));
    showModal({ icon: '☄️', title: 'Comet on your path', html: `A small comet crosses your route. You can harvest <b>${n} Ice</b> for free.`,
      buttons: [
        { label: 'Harvest ice', cls: 'primary', disabled: n <= 0, fn: () => { addCargo('ice', n); toast(`+${n} Ice`, 'good'); sfx('pickup'); done(); } },
        { label: 'Keep flying', fn: done },
      ] });
  }
}

function travelZone() {
  const tr = MapScene.travel;
  const a = tr ? tr.from : S.loc, b = tr ? tr.to : S.loc;
  return clamp(Math.max(locZone(a), locZone(b)), 2, 5);
}
function startBattle(fleet, enemyFirst, done) {
  setScene(MineScene, { fleet, z: travelZone(), done });
  if (enemyFirst) MineScene.p.shield = 0;
}
function pirateEncounter(danger, done) {
  const fleet = buildFleet(danger);
  const z = travelZone();
  const bribe = Math.round(Math.max(50, fleet.reduce((a, k) => a + ENEMIES[k].loot, 0) * Z_LOOT[z] * 0.8 + S.credits * 0.03));
  const friendly = S.rep.piratas >= 35;
  const flee = clamp(0.25 + S.lv.engine * 0.03 - fleet.length * 0.04, 0.1, 0.85);
  const threat = fleetThreat(fleet, z);
  const tl = threat < 0.6 ? ['Low', '#6dffb0', 'Easy pickings — and nice loot.'] : threat < 1.2 ? ['Medium', '#ffc857', 'A fair fight. Keep moving!'] : threat < 2 ? ['High', '#ff934a', 'Dangerous. Upgrade guns & shields.'] : ['Extreme', '#ff4d6d', 'Run or pay!'];
  sfx('alarm');
  const btns = [];
  if (friendly) btns.push({ label: 'Hail the Syndicate', cls: 'primary', fn: () => { toast('They recognize you and let you pass', 'good'); done(); } });
  btns.push({ label: '⚔ Fight!', cls: friendly ? '' : 'danger', fn: () => startBattle(fleet, false, done) });
  btns.push({ label: `Run (${Math.round(flee * 100)}%)`, fn: () => {
    if (Math.random() < flee) { toast('You escaped!', 'good'); sfx('warp'); done(); }
    else { toast('Escape failed — they caught you!', 'bad'); startBattle(fleet, true, done); }
  } });
  btns.push({ label: `Pay them off (${fmt(bribe)} cr)`, disabled: S.credits < bribe, fn: () => { S.credits -= bribe; repChange('piratas', 2, true); toast('The pirates take your money', 'good'); done(); } });
  showModal({ icon: '☠️', title: 'Pirate ambush!', danger: true,
    html: `<div class="fleet">${fleet.map(k => `<span class="chip bad">${ENEMIES[k].n}</span>`).join('')}</div>
    <div class="threat">Threat: <b style="color:${tl[1]}">${tl[0]}</b> — ${tl[2]}</div>
    <small>You fly and shoot: <b>hold the mouse</b> (or FIRE) to fire your guns. Destroyed ships drop credits.</small>`,
    buttons: btns });
}

function patrolEncounter(war, done) {
  const fac = war.war.find(f => FACTIONS[f].locs.includes(MapScene.travel ? MapScene.travel.to : S.loc)) || war.war[0];
  const arms = S.cargo.arms || 0;
  sfx('alarm');
  if (!arms || S.rep[fac] >= 25) {
    showModal({ icon: '🛡️', title: 'Military patrol', html: `A <b style="color:${FACTIONS[fac].c}">${FACTIONS[fac].n}</b> patrol scans your ship and waves you through.`, buttons: [{ label: 'Continue', cls: 'primary', fn: done }] });
    return;
  }
  showModal({ icon: '🛡️', title: 'Military patrol', danger: true, html: `The <b style="color:${FACTIONS[fac].c}">${FACTIONS[fac].n}</b> finds <b>${arms} Weapons</b> in your hold and demands you hand them over.`,
    buttons: [
      { label: 'Hand them over', cls: 'primary', fn: () => { addCargo('arms', -arms); toast('Weapons confiscated', 'bad'); done(); } },
      { label: '⚔ Resist', cls: 'danger', fn: () => { repChange(fac, -12); startBattle(['patrol', 'patrol'], false, done); } },
    ] });
}
