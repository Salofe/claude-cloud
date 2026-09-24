'use strict';
// ============ ESCENA: MAPA DEL SISTEMA SOLAR ============
const BELT = []; const KUIPER = [];
(function () {
  let s = 3; const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
  for (let i = 0; i < 700; i++) BELT.push({ a: r() * TAU, r: 238 + (r() + r() + r() - 1.5) * 34, s: 0.5 + r() * 1.3, sp: 0.9 + r() * 0.2 });
  for (let i = 0; i < 500; i++) KUIPER.push({ a: r() * TAU, r: 585 + (r() + r() - 1) * 60, s: 0.5 + r() * 1.4, sp: 0.95 + r() * 0.1 });
})();

const MapScene = {
  cam: { x: 0, y: 0, z: 1 }, camT: null, sel: null, travel: null, t: 0, hover: null, drag: null,
  enter() {
    this.focus(S.loc, true);
    showMapUI(true);
    if (this.sel) selectLoc(this.sel);
    else selectLoc(S.loc);
  },
  exit() { showMapUI(false); },
  focus(id, instant) {
    const p = locPos(id, S.day);
    const z = clamp(Math.min(W, H) / 2 / (Math.hypot(p.x, p.y) + 110), 0.45, 2.2);
    const t = { x: p.x * 0.55, y: p.y * 0.55, z };
    if (instant) Object.assign(this.cam, t); else this.camT = t;
  },
  zoomAll() { this.camT = { x: 0, y: 0, z: Math.min(W, H) / 2 / 660 }; },
  w2s(x, y) { return { x: (x - this.cam.x) * this.cam.z + W / 2, y: (y - this.cam.y) * this.cam.z + H / 2 }; },
  s2w(x, y) { return { x: (x - W / 2) / this.cam.z + this.cam.x, y: (y - H / 2) / this.cam.z + this.cam.y }; },
  pr(loc) { return loc.size * clamp(this.cam.z * 1.25, 0.85, 2.6); },
  spos(loc, day) {
    if (typeof loc === 'string') loc = LOC[loc];
    if (day == null) day = S.day + (this.travel ? this.travel.frac : 0);
    if (loc.parent) {
      const par = LOC[loc.parent];
      const pp = this.spos(par, day);
      const a = loc.a0 + day / loc.period * TAU;
      const d = Math.max(loc.r * this.cam.z, this.pr(par) + this.pr(loc) + 16);
      return { x: pp.x + Math.cos(a) * d, y: pp.y + Math.sin(a) * d };
    }
    const p = locPos(loc, day);
    return this.w2s(p.x, p.y);
  },
  update(dt) {
    this.t += dt;
    if (this.camT) {
      const k = 1 - Math.pow(0.02, dt);
      this.cam.x = lerp(this.cam.x, this.camT.x, k); this.cam.y = lerp(this.cam.y, this.camT.y, k); this.cam.z = lerp(this.cam.z, this.camT.z, k);
      if (Math.abs(this.cam.z - this.camT.z) < 0.001 && Math.abs(this.cam.x - this.camT.x) < 0.5) this.camT = null;
    }
    const tr = this.travel;
    if (tr && !tr.paused) {
      tr.el += dt;
      const p = clamp(tr.el / tr.dur, 0, 1);
      const dayNow = Math.floor(p * tr.days);
      while (tr.dayDone < dayNow) { tr.dayDone++; tickDay(); updateHUD(); }
      tr.frac = p * tr.days - dayNow;
      if (tr.frac < 0) tr.frac = 0;
      if (tr.enc && !tr.encDone && p >= tr.enc.at) { tr.encDone = true; tr.paused = true; laserSound(false); runEncounter(tr.enc, () => { tr.paused = false; }); }
      if (p >= 1 && !tr.paused) this.arrive();
    }
  },
  startTravel(to) {
    const info = travelInfo(to);
    if (info.fuel > S.fuel) { toast('Combustible insuficiente', 'bad'); sfx('full'); return; }
    if (S.loc === to) return;
    S.fuel -= info.fuel;
    const dur = clamp(0.9 + info.days * 0.28, 1.4, 6);
    let enc = null;
    if (Math.random() < info.danger) enc = { kind: 'hostile', at: rand(0.3, 0.7), danger: info.danger, from: S.loc, to };
    else if (Math.random() < 0.28 + info.days * 0.01) enc = { kind: 'random', at: rand(0.25, 0.75), danger: info.danger, from: S.loc, to };
    // patrulla de guerra
    const war = S.events.find(e => e.war && (e.locs.includes(to) || e.locs.includes(S.loc)));
    if (war && !enc && Math.random() < 0.45) enc = { kind: 'patrol', at: rand(0.3, 0.7), war, from: S.loc, to };
    const storm = S.events.find(e => e.storm && (e.storm.includes(to) || e.storm.includes(S.loc)));
    this.travel = { from: S.loc, to, days: info.days, dur, el: 0, dayDone: 0, frac: 0, enc, encDone: false, storm, fuel: info.fuel, dist: info.d };
    S.stats.dist += info.d;
    sfx('warp');
    showMapUI(false); hideLocPanel();
    document.getElementById('travelBanner').classList.remove('hidden');
    document.getElementById('travelBanner').innerHTML = `Rumbo a <b>${LOC[to].n}</b> · ${info.days} día${info.days > 1 ? 's' : ''}`;
    this.zoomFor(S.loc, to);
  },
  zoomFor(a, b) {
    const p = locPos(a, S.day), q = locPos(b, S.day);
    const cx = (p.x + q.x) / 2, cy = (p.y + q.y) / 2;
    const span = Math.max(Math.abs(p.x - q.x), Math.abs(p.y - q.y)) / 2 + 90;
    this.camT = { x: cx, y: cy, z: clamp(Math.min(W, H) / 2 / span, 0.45, 2.2) };
  },
  arrive() {
    const tr = this.travel; this.travel = null;
    S.loc = tr.to;
    document.getElementById('travelBanner').classList.add('hidden');
    if (tr.storm) {
      const dmg = Math.max(0, randi(8, 20) - ship.shieldMax * 0.15);
      S.hull = Math.max(1, S.hull - dmg);
      toast(`La tormenta solar dañó el casco (−${Math.round(dmg)})`, 'bad');
    }
    save();
    showMapUI(true);
    selectLoc(S.loc);
    this.focus(S.loc);
    checkTut();
    updateHUD();
    if (LOC[S.loc].station) toast(`Llegaste a ${LOC[S.loc].station}`, 'good');
    else toast(`Llegaste a ${LOC[S.loc].field.n}`, 'good');
  },
  draw(ctx) {
    const t = this.t;
    drawSpaceBg(ctx, W, H, this.cam.x * this.cam.z, this.cam.y * this.cam.z, t);
    const z = this.cam.z;
    const sun = this.w2s(0, 0);
    // órbitas
    ctx.lineWidth = 1;
    for (const l of LOCS) {
      if (l.parent || l.follow) continue;
      ctx.strokeStyle = 'rgba(120,160,255,0.13)';
      ctx.beginPath(); ctx.arc(sun.x, sun.y, l.r * z, 0, TAU); ctx.stroke();
    }
    // cinturón + kuiper
    const day = S.day + (this.travel ? this.travel.frac : 0);
    ctx.fillStyle = 'rgba(200,185,160,0.55)';
    for (const b of BELT) { const a = b.a + day / 560 * TAU * b.sp; ctx.fillRect(sun.x + Math.cos(a) * b.r * z, sun.y + Math.sin(a) * b.r * z, b.s, b.s); }
    ctx.fillStyle = 'rgba(150,180,255,0.45)';
    for (const b of KUIPER) { const a = b.a + day / 3300 * TAU * b.sp; ctx.fillRect(sun.x + Math.cos(a) * b.r * z, sun.y + Math.sin(a) * b.r * z, b.s, b.s); }
    // troyanos: nube
    const tp = this.spos('troyanos', day);
    ctx.fillStyle = 'rgba(200,185,160,0.5)';
    for (let i = 0; i < 40; i++) { const a = i * 2.4, rr = (i % 7) * 3.2 * clamp(z, 0.7, 2); ctx.fillRect(tp.x + Math.cos(a) * rr, tp.y + Math.sin(a) * rr, 1.4, 1.4); }
    drawSun(ctx, sun.x, sun.y, clamp(16 * z, 10, 34), t);
    // ruta
    const tr = this.travel;
    const selId = this.sel;
    if (!tr && selId && selId !== S.loc) {
      const a = this.spos(S.loc), b = this.spos(selId);
      const info = travelInfo(selId);
      ctx.setLineDash([6, 6]); ctx.lineDashOffset = -t * 20;
      ctx.strokeStyle = info.fuel > S.fuel ? 'rgba(255,90,110,0.8)' : 'rgba(61,232,255,0.8)'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
      ctx.setLineDash([]);
    }
    // cuerpos
    for (const l of LOCS) {
      if (l.id === 'troyanos') continue;
      const p = this.spos(l, day);
      const r = this.pr(l);
      const la = Math.atan2(sun.y - p.y, sun.x - p.x);
      if (l.id === 'kuiper') {
        glow(ctx, p.x, p.y, r * 2.5, '#9fb6ff55', 0.6);
        ctx.fillStyle = '#b9c9ff';
        for (let i = 0; i < 9; i++) { const a = i * 0.7 + t * 0.1; ctx.beginPath(); ctx.arc(p.x + Math.cos(a) * r * (0.4 + (i % 3) * 0.4), p.y + Math.sin(a * 1.3) * r * 0.8, 1.6, 0, TAU); ctx.fill(); }
      } else drawPlanet(ctx, p.x, p.y, r, l, la, t);
    }
    // nodos (marcadores)
    ctx.textAlign = 'center';
    for (const l of NODES) {
      const p = this.spos(l, day);
      const r = this.pr(l) + (l.id === 'troyanos' ? 8 : 0);
      const isSel = l.id === selId, isHere = l.id === S.loc && !tr, isHov = l.id === this.hover;
      if (l.station) drawStationIcon(ctx, p.x + r + 7, p.y - r - 4, 4, l.faction ? FACTIONS[l.faction].c : '#fff', t);
      if (l.field) { ctx.fillStyle = '#ffd24a'; ctx.font = '10px sans-serif'; ctx.fillText('⛏', p.x - r - 8, p.y - r); }
      if (isSel || isHov) {
        ctx.strokeStyle = isSel ? '#3de8ff' : 'rgba(61,232,255,0.5)'; ctx.lineWidth = 1.5;
        const rr = r + 7 + Math.sin(t * 4) * 1.5;
        ctx.beginPath();
        for (let i = 0; i < 4; i++) { const a0 = i * TAU / 4 + t * 0.6; ctx.arc(p.x, p.y, rr, a0, a0 + 0.9); ctx.moveTo(p.x + Math.cos(a0 + TAU / 4) * rr, p.y + Math.sin(a0 + TAU / 4) * rr); }
        ctx.stroke();
      }
      // eventos
      const evs = S.events.filter(e => e.locs && e.locs.includes(l.id));
      evs.forEach((e, i) => { ctx.font = '13px sans-serif'; ctx.fillText(e.icon, p.x - r - 6 - i * 15, p.y + r + 4); });
      ctx.font = `600 ${isSel ? 12 : 11}px Rajdhani, sans-serif`;
      ctx.fillStyle = isSel ? '#ffffff' : 'rgba(210,225,255,0.8)';
      ctx.fillText(l.n.toUpperCase(), p.x, p.y + r + 15);
      const dg = locDanger(l.id);
      if (dg >= 0.2) { ctx.fillStyle = dg > 0.45 ? '#ff4d6d' : '#ffb347'; ctx.fillText('☠'.repeat(dg > 0.45 ? 2 : 1), p.x, p.y + r + 27); }
    }
    // nave del jugador
    let sp, ang;
    if (tr) {
      const a = this.spos(tr.from), b = this.spos(tr.to);
      const p = clamp(tr.el / tr.dur, 0, 1), e = p < 0.5 ? 2 * p * p : 1 - Math.pow(-2 * p + 2, 2) / 2;
      const nx = -(b.y - a.y), ny = b.x - a.x, nl = Math.hypot(nx, ny) || 1;
      const arc = Math.sin(e * Math.PI) * 0.08 * nl;
      sp = { x: lerp(a.x, b.x, e) + nx / nl * arc, y: lerp(a.y, b.y, e) + ny / nl * arc };
      ang = Math.atan2(b.y - a.y, b.x - a.x);
      // estela
      ctx.strokeStyle = 'rgba(255,179,71,0.5)'; ctx.lineWidth = 2; ctx.setLineDash([2, 5]);
      ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(sp.x, sp.y); ctx.stroke(); ctx.setLineDash([]);
      drawPlayerShip(ctx, S.lv, sp.x, sp.y, ang, 0.5, 1, t);
    } else {
      const p = this.spos(S.loc);
      const r = this.pr(LOC[S.loc]) + 14;
      const a = t * 0.8;
      sp = { x: p.x + Math.cos(a) * r, y: p.y + Math.sin(a) * r };
      drawPlayerShip(ctx, S.lv, sp.x, sp.y, a + Math.PI / 2, 0.4, 0.4, t);
    }
  },
  pick(x, y) {
    let best = null, bd = 1e9;
    for (const l of NODES) {
      const p = this.spos(l);
      const d = Math.hypot(p.x - x, p.y - y);
      const hit = Math.max(20, this.pr(l) + 12);
      if (d < hit && d < bd) { bd = d; best = l.id; }
    }
    return best;
  },
  onDown(x, y) { this.drag = { x, y, cx: this.cam.x, cy: this.cam.y, moved: false }; },
  onMove(x, y, down) {
    if (down && this.drag) {
      const dx = x - this.drag.x, dy = y - this.drag.y;
      if (Math.hypot(dx, dy) > 6) this.drag.moved = true;
      if (this.drag.moved) { this.camT = null; this.cam.x = this.drag.cx - dx / this.cam.z; this.cam.y = this.drag.cy - dy / this.cam.z; }
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
    const before = this.s2w(x, y);
    this.camT = null;
    this.cam.z = clamp(this.cam.z * Math.pow(1.0015, -dy), 0.35, 3.5);
    const after = this.s2w(x, y);
    this.cam.x += before.x - after.x; this.cam.y += before.y - after.y;
  },
  onPinch(scale, x, y) { this.onWheel(-Math.log(scale) / Math.log(1.0015), x, y); },
};

// ============ ENCUENTROS DE VIAJE ============
function buildFleet(danger, bias) {
  let budget = 0.5 + danger * 3.5 + S.day / 120 + ship.power * 0.45 + (bias || 0);
  budget *= rand(0.75, 1.2);
  const fleet = [];
  const order = ['carrier', 'frigate', 'corsair', 'raider'];
  while (budget > 0.6 && fleet.length < 5) {
    const opts = order.filter(k => ENEMIES[k].pow <= budget);
    if (!opts.length) break;
    const k = Math.random() < 0.6 ? opts[0] : pick(opts);
    fleet.push(k); budget -= ENEMIES[k].pow;
  }
  if (!fleet.length) fleet.push('raider');
  return fleet;
}
function fleetPower(f) { return f.reduce((a, k) => a + ENEMIES[k].pow, 0) * (1 + S.day / 400); }

function runEncounter(enc, done) {
  if (enc.kind === 'hostile') return pirateEncounter(enc.danger, done);
  if (enc.kind === 'patrol') return patrolEncounter(enc.war, done);
  const opts = ['derelict', 'distress', 'trader', 'meteor', 'comet', 'derelict', 'distress'];
  const k = pick(opts);
  if (k === 'derelict') {
    showModal({ icon: '🛰️', title: 'Restos a la deriva', html: 'Tu escáner detecta un carguero abandonado. Podría tener carga útil… o ser un señuelo.',
      buttons: [
        { label: 'Rescatar carga', cls: 'primary', fn: () => {
          if (Math.random() < 0.22 - ship.avoid * 0.3) { toast('¡Era una trampa!', 'bad'); sfx('alarm'); return pirateEncounter(enc.danger + 0.1, done, true); }
          const it = pick(ITEM_KEYS); const n = Math.min(cargoFree(), randi(3, 6 + S.lv.hull * 3));
          if (n > 0) { addCargo(it, n); toast(`+${n} ${ITEMS[it].n}`, 'good'); sfx('pickup'); } else toast('Bodega llena: no pudiste llevarte nada', 'bad');
          done();
        } },
        { label: 'Ignorar', fn: done },
      ] });
  } else if (k === 'distress') {
    const fac = pick(['tierra', 'marte', 'cinturon', 'exterior']);
    showModal({ icon: '🆘', title: 'Señal de auxilio', html: `Una nave de la <b style="color:${FACTIONS[fac].c}">${FACTIONS[fac].n}</b> pide ayuda: soporte vital fallando. Ayudar cuesta 5 de combustible.`,
      buttons: [
        { label: 'Ayudar (−5 ⛽)', cls: 'primary', disabled: S.fuel < 5, fn: () => {
          S.fuel -= 5;
          if (Math.random() < 0.18) { toast('¡Emboscada pirata!', 'bad'); sfx('alarm'); return pirateEncounter(enc.danger + 0.15, done, true); }
          const cr = randi(150, 400) + S.day * 4; S.credits += cr; repChange(fac, 6);
          toast(`Te pagan ${fmt(cr)} ₵ por el rescate`, 'good'); sfx('cash'); done();
        } },
        { label: 'Ignorar', fn: () => { repChange(fac, -1, true); done(); } },
      ] });
  } else if (k === 'trader') {
    const items = Object.keys(S.cargo);
    if (!items.length) {
      const cost = Math.round(fuelPrice('tierra') * 1.8 * 10) / 10;
      const n = Math.min(20, ship.fuelMax - Math.floor(S.fuel));
      showModal({ icon: '🧑‍🚀', title: 'Comerciante errante', html: `Una nave mercante ofrece combustible a ${cost} ₵ por unidad.`,
        buttons: [
          { label: `Comprar ${n} ⛽ (${fmt(n * cost)} ₵)`, cls: 'primary', disabled: n <= 0 || S.credits < n * cost, fn: () => { S.fuel += n; S.credits -= Math.round(n * cost); sfx('cash'); done(); } },
          { label: 'Seguir', fn: done },
        ] });
    } else {
      const it = pick(items); const n = S.cargo[it]; const price = Math.round(ITEMS[it].b * rand(1.15, 1.45));
      showModal({ icon: '🧑‍🚀', title: 'Comerciante errante', html: `Un mercader independiente ofrece comprar tus <b>${n} ${ITEMS[it].n}</b> a <b>${price} ₵</b> c/u.`,
        buttons: [
          { label: `Vender (${fmt(n * price)} ₵)`, cls: 'primary', fn: () => { addCargo(it, -n); S.credits += n * price; S.stats.earned += n * price; sfx('cash'); done(); } },
          { label: 'No, gracias', fn: done },
        ] });
    }
  } else if (k === 'meteor') {
    const dmg = Math.max(0, randi(6, 16) - ship.shieldMax * 0.2);
    S.hull = Math.max(1, S.hull - dmg);
    showModal({ icon: '☄️', title: 'Lluvia de micrometeoritos', html: dmg > 0 ? `Atraviesas un enjambre de polvo. El casco recibe <b>${Math.round(dmg)}</b> de daño.` : 'Tus escudos desvían todos los impactos. ¡Ni un rasguño!',
      buttons: [{ label: 'Continuar', cls: 'primary', fn: done }] });
    sfx('hit');
  } else {
    const n = Math.min(cargoFree(), randi(6, 14));
    showModal({ icon: '☄️', title: 'Cometa en ruta', html: `Un pequeño cometa cruza tu trayectoria. Puedes extraer <b>${n} Hielo</b> gratis.`,
      buttons: [
        { label: 'Extraer hielo', cls: 'primary', disabled: n <= 0, fn: () => { addCargo('ice', n); toast(`+${n} Hielo`, 'good'); sfx('pickup'); done(); } },
        { label: 'Seguir', fn: done },
      ] });
  }
}

function pirateEncounter(danger, done, forced) {
  const fleet = buildFleet(danger);
  const fp = fleetPower(fleet);
  const bribe = Math.round((120 * fp + S.credits * 0.06) / 10) * 10;
  const friendly = S.rep.piratas >= 35;
  const flee = clamp(ship.flee - fp * 0.02, 0.1, 0.85);
  const list = fleet.map(k => ENEMIES[k].n).join(', ');
  const threat = fp / Math.max(0.5, ship.power);
  const tl = threat < 0.6 ? ['Baja', '#6dffb0'] : threat < 1.2 ? ['Media', '#ffc857'] : threat < 2 ? ['Alta', '#ff934a'] : ['Extrema', '#ff4d6d'];
  sfx('alarm');
  const btns = [];
  if (friendly) btns.push({ label: 'Saludar al Sindicato', cls: 'primary', fn: () => { toast('Te reconocen y te dejan pasar', 'good'); done(); } });
  btns.push({ label: '⚔ Pelear', cls: friendly ? '' : 'danger', fn: () => startBattle(fleet, false, done) });
  btns.push({ label: `Huir (${Math.round(flee * 100)}%)`, fn: () => {
    if (Math.random() < flee) { toast('¡Escapaste!', 'good'); sfx('warp'); done(); }
    else { toast('No lograste escapar', 'bad'); startBattle(fleet, true, done); }
  } });
  btns.push({ label: `Sobornar (${fmt(bribe)} ₵)`, disabled: S.credits < bribe, fn: () => { S.credits -= bribe; repChange('piratas', 2, true); toast('Los piratas aceptan tu dinero', 'good'); done(); } });
  showModal({ icon: '☠️', title: 'Emboscada pirata', danger: true,
    html: `<div class="fleet">${fleet.map(k => `<span class="chip bad">${ENEMIES[k].n}</span>`).join('')}</div>
    Amenaza: <b style="color:${tl[1]}">${tl[0]}</b> · Tu poder de combate: <b>${ship.power.toFixed(1)}</b> vs <b>${fp.toFixed(1)}</b><br><small>El combate es automático y depende de tu casco, escudos, armas y drones.</small>`,
    buttons: btns });
}

function patrolEncounter(war, done) {
  const fac = war.war.find(f => FACTIONS[f].locs.includes(MapScene.travel ? MapScene.travel.to : S.loc)) || war.war[0];
  const arms = S.cargo.arms || 0;
  sfx('alarm');
  if (!arms || S.rep[fac] >= 25) {
    showModal({ icon: '🛡️', title: 'Patrulla militar', html: `Una patrulla de la <b style="color:${FACTIONS[fac].c}">${FACTIONS[fac].n}</b> escanea tu nave y te deja pasar.`, buttons: [{ label: 'Continuar', cls: 'primary', fn: done }] });
    return;
  }
  showModal({ icon: '🛡️', title: 'Patrulla militar', danger: true, html: `La <b style="color:${FACTIONS[fac].c}">${FACTIONS[fac].n}</b> detecta <b>${arms} Armamento</b> en tu bodega y exige confiscarlo.`,
    buttons: [
      { label: 'Entregar armas', cls: 'primary', fn: () => { addCargo('arms', -arms); toast('Armas confiscadas', 'bad'); done(); } },
      { label: '⚔ Resistir', cls: 'danger', fn: () => { repChange(fac, -12); startBattle(['patrol', ...(S.day > 60 ? ['patrol'] : [])], false, done); } },
    ] });
}
