'use strict';
// ============ ESTADO, ECONOMÍA Y MUNDO ============
const SAVE_KEY = 'solar_prospector_v1';
let S = null;

function newGame() {
  S = {
    v: 1, day: 0, credits: 600, loc: 'tierra', fuel: 60, hull: 60, shipName: 'Pionera',
    lv: { hull: 1, laser: 1, engine: 1, tank: 1, shield: 1, weapons: 1, drones: 1, scanner: 1 },
    cargo: {},
    rep: { tierra: 5, marte: 0, cinturon: 0, exterior: 0, piratas: -10 },
    invest: {}, sat: {}, drift: {}, depl: {},
    events: [], news: [], contracts: {}, active: [],
    stats: { mined: 0, earned: 0, won: 0, lost: 0, dist: 0, contracts: 0, traded: 0 },
    tut: 0, won: false, nextEvent: 6, nextContracts: {},
  };
  for (const l of NODES) if (l.market) { S.sat[l.id] = {}; S.drift[l.id] = {}; for (const k in l.market) { S.sat[l.id][k] = 1; S.drift[l.id][k] = rand(-0.08, 0.08); } }
  for (const l of NODES) if (l.market) genContracts(l.id);
  addNews('📡', 'Tu vieja nave minera está atracada en la Tierra. El Sistema Solar espera.', '#3de8ff');
  return S;
}
function save() { try { localStorage.setItem(SAVE_KEY, JSON.stringify(S)); } catch (e) {} }
function loadSave() {
  try { const s = localStorage.getItem(SAVE_KEY); if (!s) return null; const d = JSON.parse(s); return d && d.v === 1 ? d : null; } catch (e) { return null; }
}
function hasSave() { return !!loadSave(); }

// ---------- stats derivadas ----------
const ship = {
  get cargoMax() { return UPG.hull.cargo[S.lv.hull - 1]; },
  get hpMax() { return UPG.hull.hp[S.lv.hull - 1]; },
  get mass() { return UPG.hull.mass[S.lv.hull - 1]; },
  get fuelMax() { return UPG.tank.fuel[S.lv.tank - 1]; },
  get laserDps() { return UPG.laser.dps[S.lv.laser - 1]; },
  get laserRange() { return UPG.laser.range[S.lv.laser - 1]; },
  get thrust() { return UPG.engine.thrust[S.lv.engine - 1]; },
  get speed() { return UPG.engine.speed[S.lv.engine - 1]; },
  get eff() { return UPG.engine.eff[S.lv.engine - 1]; },
  get flee() { return UPG.engine.flee[S.lv.engine - 1]; },
  get shieldMax() { return UPG.shield.sp[S.lv.shield - 1]; },
  get weaponDps() { return UPG.weapons.dps[S.lv.weapons - 1] + UPG.drones.count[S.lv.drones - 1] * 2.5; },
  get magnet() { return UPG.drones.magnet[S.lv.drones - 1]; },
  get drones() { return UPG.drones.count[S.lv.drones - 1]; },
  get avoid() { return UPG.scanner.avoid[S.lv.scanner - 1]; },
  get power() { return Math.sqrt(Math.max(1, S.hull + this.shieldMax * 1.5) * this.weaponDps) / 12.7; },
};
function cargoUsed() { let n = 0; for (const k in S.cargo) n += S.cargo[k]; return n; }
function cargoFree() { return ship.cargoMax - cargoUsed(); }
function addCargo(k, n) { S.cargo[k] = (S.cargo[k] || 0) + n; if (S.cargo[k] <= 0) delete S.cargo[k]; }
function cargoValueEstimate() { let v = 0; for (const k in S.cargo) v += S.cargo[k] * ITEMS[k].b; return v; }

// ---------- posiciones orbitales ----------
function locPos(loc, day) {
  if (typeof loc === 'string') loc = LOC[loc];
  if (loc.follow) {
    const f = LOC[loc.follow];
    const a = f.a0 + day / f.period * TAU + loc.offset;
    return { x: Math.cos(a) * f.r, y: Math.sin(a) * f.r };
  }
  const a = loc.a0 + day / loc.period * TAU;
  if (loc.parent) {
    const p = locPos(LOC[loc.parent], day);
    return { x: p.x + Math.cos(a) * loc.r, y: p.y + Math.sin(a) * loc.r };
  }
  return { x: Math.cos(a) * loc.r, y: Math.sin(a) * loc.r };
}
function locDist(a, b, day) {
  const p = locPos(a, day), q = locPos(b, day);
  return Math.hypot(p.x - q.x, p.y - q.y);
}
function travelInfo(to) {
  const d = Math.max(8, locDist(S.loc, to, S.day));
  const fuel = Math.ceil(d * 0.1 * ship.mass / ship.eff * fuelEventMult());
  const days = Math.max(1, Math.round(d / (22 * ship.speed)));
  const danger = routeDanger(S.loc, to);
  return { d, fuel, days, danger };
}
function fuelEventMult() { let m = 1; for (const e of S.events) if (e.fuelCost) m *= e.fuelCost; return m; }

function locDanger(id) {
  let d = LOC[id].danger || 0;
  for (const e of S.events) if (e.danger) for (const x of e.danger) if (x.loc === id) d += x.add;
  return clamp(d, 0, 0.95);
}
function routeDanger(a, b) {
  const base = Math.max(locDanger(a), locDanger(b)) * 0.8 + (locDanger(a) + locDanger(b)) * 0.1;
  return clamp(base * (1 - ship.avoid), 0, 0.9);
}

// ---------- mercado ----------
function eventPriceMult(locId, item) {
  let m = 1;
  for (const e of S.events) if (e.price) for (const p of e.price) if ((p.loc === locId || p.loc === '*') && p.item === item) m *= p.m;
  return m;
}
function basePrice(locId, item) {
  const l = LOC[locId];
  const mult = l.market[item];
  if (mult == null) return null;
  return ITEMS[item].b * mult * (1 + (S.drift[locId][item] || 0)) * (S.sat[locId][item] || 1) * eventPriceMult(locId, item);
}
function sellPrice(locId, item) { const p = basePrice(locId, item); return p == null ? null : Math.max(1, Math.round(p * 0.93)); }
function buyPrice(locId, item) {
  const l = LOC[locId]; const mult = l.market[item];
  if (mult == null || mult > 1.0) return null;
  return Math.max(2, Math.round(basePrice(locId, item) * 1.07));
}
function fuelPrice(locId) {
  let p = LOC[locId].fuel; for (const e of S.events) if (e.fuelPrice) p *= e.fuelPrice; return Math.max(1, Math.round(p * 10) / 10);
}
function marketClosed(locId) { return S.events.some(e => e.closed && e.closed.includes(locId)); }

function doSell(locId, item, n) {
  n = Math.min(n, S.cargo[item] || 0);
  let total = 0;
  for (let i = 0; i < n; i++) {
    total += sellPrice(locId, item);
    S.sat[locId][item] = Math.max(0.35, S.sat[locId][item] * (ITEMS[item].ore ? 0.988 : 0.982));
  }
  addCargo(item, -n);
  S.credits += total; S.stats.earned += total; S.stats.traded += n;
  // efectos de reputación
  const l = LOC[locId];
  if (n > 0) {
    if (l.faction) {
      let gain = total / 4000;
      for (const e of S.events) if (e.relief && e.relief.loc === locId && e.relief.item === item) { gain += n * 0.35; }
      if (item === 'arms') for (const e of S.events) if (e.war) {
        if (e.war.includes(l.faction)) { const other = e.war.find(f => f !== l.faction); repChange(other, -n * 0.15, true); gain += n * 0.2; }
      }
      repChange(l.faction, gain, true);
    }
    if (l.black) for (const f in FACTIONS) if (f !== 'piratas') repChange(f, -n * 0.02, true);
  }
  return total;
}
function doBuy(locId, item, n) {
  n = Math.min(n, cargoFree());
  let total = 0, bought = 0;
  for (let i = 0; i < n; i++) {
    const p = buyPrice(locId, item);
    if (p == null || S.credits - total < p) break;
    total += p; bought++;
    S.sat[locId][item] = Math.min(1.6, S.sat[locId][item] * 1.012);
  }
  S.credits -= total; addCargo(item, bought);
  return bought;
}
function repChange(f, d, silent) {
  const before = S.rep[f];
  S.rep[f] = clamp(S.rep[f] + d, -100, 100);
  if (!silent && Math.abs(d) >= 1) toast(`${FACTIONS[f].n}: ${d > 0 ? '+' : ''}${Math.round(d)} reputación`, d > 0 ? 'good' : 'bad');
  return S.rep[f] - before;
}

// ---------- influencia ----------
function influence() {
  let v = 0;
  for (const id in S.invest) for (let i = 0; i < S.invest[id]; i++) v += INVEST.infl[i];
  for (const f in S.rep) if (f !== 'piratas') v += Math.max(0, S.rep[f]) / 8;
  v += Math.max(0, S.rep.piratas) / 16;
  v += Math.min(10, S.stats.won * 0.25);
  return Math.floor(v);
}
function rankName(inf) { let r = RANKS[0][1]; for (const [n, t] of RANKS) if (inf >= n) r = t; return r; }
function dailyIncome() { let v = 0; for (const id in S.invest) for (let i = 0; i < S.invest[id]; i++) v += INVEST.income[i]; return v; }
function investCost(locId) { const lv = S.invest[locId] || 0; const f = LOC[locId].black ? 1.3 : 1; return lv >= 3 ? null : Math.round(INVEST.cost[lv] * f); }

// ---------- contratos ----------
function genContracts(locId) {
  const l = LOC[locId];
  const list = [];
  const n = 3;
  for (let i = 0; i < n; i++) {
    const r = Math.random();
    if (r < 0.62) {
      // entrega: trae X a esta estación
      const wanted = Object.keys(l.market).filter(k => l.market[k] >= 1.05);
      const item = pick(wanted.length ? wanted : Object.keys(l.market));
      const scale = clamp(1 + S.day / 60, 1, 8) * (0.6 + 0.4 * S.lv.hull);
      const qty = Math.max(4, Math.round(rand(6, 14) * scale * (ITEMS[item].b > 100 ? 0.4 : 1)));
      const reward = Math.round(qty * ITEMS[item].b * rand(1.7, 2.3) / 10) * 10;
      list.push({ type: 'deliver', id: Math.random().toString(36).slice(2, 8), from: locId, to: locId, item, qty, reward, rep: 4 + Math.round(qty / 8), days: randi(18, 35), faction: l.faction });
    } else if (r < 0.82) {
      // transporte a otra estación
      const dests = NODES.filter(x => x.market && x.id !== locId && x.market);
      const dest = pick(dests);
      const buyables = Object.keys(l.market).filter(k => l.market[k] <= 1.0);
      const item = buyables.length ? pick(buyables) : 'food';
      const qty = Math.max(4, Math.round(rand(5, 12) * clamp(1 + S.day / 80, 1, 6)));
      const dist = LOC[dest.id].r ? Math.abs((LOC[dest.id].parent ? LOC[LOC[dest.id].parent].r : LOC[dest.id].r) - (l.parent ? LOC[l.parent].r : l.r)) : 100;
      const reward = Math.round((qty * ITEMS[item].b * 1.4 + dist * 6) / 10) * 10;
      list.push({ type: 'deliver', id: Math.random().toString(36).slice(2, 8), from: locId, to: dest.id, item, qty, reward, rep: 5 + Math.round(qty / 6), days: randi(25, 45), faction: dest.faction || l.faction });
    } else {
      const kills = randi(1, 3);
      const reward = Math.round(kills * (300 + S.day * 8) / 10) * 10;
      list.push({ type: 'bounty', id: Math.random().toString(36).slice(2, 8), from: locId, kills, reward, rep: 6 * kills, days: randi(25, 50), faction: l.faction === 'piratas' ? 'piratas' : l.faction });
    }
  }
  S.contracts[locId] = list;
  S.nextContracts[locId] = S.day + randi(8, 14);
}
function contractText(c) {
  if (c.type === 'deliver') return `Entregar <b>${c.qty} ${ITEMS[c.item].n}</b> en <b>${LOC[c.to].station}</b> (${LOC[c.to].n})`;
  return `Destruir <b>${c.kills}</b> flota${c.kills > 1 ? 's' : ''} pirata${c.kills > 1 ? 's' : ''}` + (c.progress != null ? ` (${c.progress}/${c.kills})` : '');
}
function acceptContract(locId, cid) {
  const list = S.contracts[locId]; const i = list.findIndex(c => c.id === cid);
  if (i < 0) return;
  if (S.active.length >= 5) { toast('Máximo 5 contratos activos', 'bad'); return; }
  const c = list.splice(i, 1)[0];
  c.deadline = S.day + c.days;
  if (c.type === 'bounty') c.progress = 0;
  S.active.push(c);
  sfx('click');
  toast('Contrato aceptado', 'good');
  if (S.tut === 4) advanceTut();
}
function canDeliver(c) { return c.type === 'deliver' && S.loc === c.to && (S.cargo[c.item] || 0) >= c.qty; }
function completeContract(c) {
  if (c.type === 'deliver') addCargo(c.item, -c.qty);
  S.credits += c.reward; S.stats.earned += c.reward; S.stats.contracts++;
  if (c.faction) repChange(c.faction, c.rep);
  S.active = S.active.filter(x => x !== c);
  addNews('✅', `Contrato completado: +${fmt(c.reward)} ₵`, '#6dffb0');
  sfx('cash');
}

// ---------- eventos del sistema ----------
const WAR_PAIRS = [['tierra', 'marte'], ['marte', 'cinturon'], ['tierra', 'exterior'], ['cinturon', 'exterior'], ['marte', 'exterior']];
const EVENT_GEN = [
  { w: 1.1, make() {
      if (S.events.some(e => e.war)) return null;
      const [a, b] = pick(WAR_PAIRS);
      const locs = [...FACTIONS[a].locs, ...FACTIONS[b].locs];
      return { icon: '⚔️', title: `Guerra: ${FACTIONS[a].n} vs ${FACTIONS[b].n}`,
        text: `Estalla el conflicto. Armamento y combustible se disparan en sus mercados; las rutas se vuelven peligrosas. Vender armas a un bando enfurece al otro.`,
        dur: randi(28, 50), war: [a, b], locs,
        price: locs.flatMap(l => [{ loc: l, item: 'arms', m: 2.3 }, { loc: l, item: 'meds', m: 1.5 }, { loc: l, item: 'machinery', m: 1.3 }]),
        danger: locs.map(l => ({ loc: l, add: 0.22 })), fuelPrice: 1.3, military: 1 };
  } },
  { w: 1, make() {
      const l = pick(NODES.filter(x => x.market && !x.black));
      return { icon: '☣️', title: `Pandemia en ${l.n}`, text: `Un brote de fiebre marciana azota ${l.station}. Pagan una fortuna por medicinas; entregarlas da gran reputación.`,
        dur: randi(18, 32), locs: [l.id], price: [{ loc: l.id, item: 'meds', m: 3 }, { loc: l.id, item: 'food', m: 1.3 }], relief: { loc: l.id, item: 'meds' } };
  } },
  { w: 1, make() {
      const l = pick(NODES.filter(x => x.market && ['europa', 'titan', 'ceres', 'marte', 'pluton', 'luna'].includes(x.id)));
      return { icon: '🌾', title: `Hambruna en ${l.n}`, text: `Las granjas hidropónicas de ${l.station} fallaron. La comida vale oro.`,
        dur: randi(15, 28), locs: [l.id], price: [{ loc: l.id, item: 'food', m: 2.6 }], relief: { loc: l.id, item: 'food' } };
  } },
  { w: 1, make() {
      const l = pick(NODES.filter(x => x.market));
      return { icon: '🏗️', title: `Boom de construcción en ${l.n}`, text: `${l.station} se expande. Metales y maquinaria con demanda altísima.`,
        dur: randi(20, 35), locs: [l.id], price: ['iron', 'nickel', 'titanium', 'machinery'].map(i => ({ loc: l.id, item: i, m: 1.85 })) };
  } },
  { w: 0.9, make() {
      const l = pick(NODES.filter(x => x.field));
      return { icon: '💎', title: `Descubrimiento en ${l.field.n}`, text: `Sondas detectan vetas ricas en ${l.n}. ¡Hora de minar!`,
        dur: randi(15, 25), locs: [l.id], rich: l.id };
  } },
  { w: 0.9, make() {
      const l = pick(NODES.filter(x => x.id !== 'pluton'));
      return { icon: '☠️', title: `Ola pirata cerca de ${l.n}`, text: `El Sindicato Negro concentra flotas cerca de ${l.n}. Cazarlos paga bien.`,
        dur: randi(15, 30), locs: [l.id], danger: [{ loc: l.id, add: 0.35 }] };
  } },
  { w: 0.7, make() {
      return { icon: '⛽', title: 'Crisis de combustible', text: 'Sabotaje en las refinerías de Titán. El combustible cuesta el doble en todo el sistema… excepto que lo vendas tú.',
        dur: randi(12, 22), locs: ['titan'], fuelPrice: 2, price: [{ loc: '*', item: 'ice', m: 1.4 }, { loc: '*', item: 'he3', m: 1.3 }] };
  } },
  { w: 0.7, make() {
      return { icon: '⚛️', title: 'Fiebre del Helio-3', text: 'Nuevos reactores de fusión en la Tierra y Marte. El Helio-3 se cotiza al alza.',
        dur: randi(18, 30), locs: ['tierra', 'marte'], price: [{ loc: '*', item: 'he3', m: 1.9 }] };
  } },
  { w: 0.6, make() {
      const l = pick(NODES.filter(x => x.market && !['tierra'].includes(x.id)));
      return { icon: '✊', title: `Huelga en ${l.station}`, text: `Los estibadores de ${l.n} paran. Mercado cerrado; solo combustible y reparaciones.`,
        dur: randi(6, 12), locs: [l.id], closed: [l.id] };
  } },
  { w: 0.6, make() {
      return { icon: '☀️', title: 'Tormenta solar', text: 'Una eyección de masa coronal barre el sistema interior. Viajar cerca del Sol daña el casco.',
        dur: randi(6, 12), locs: ['mercurio', 'venus', 'tierra', 'luna'], storm: ['mercurio', 'venus', 'tierra', 'luna'] };
  } },
  { w: 0.6, make() {
      const l = pick(NODES.filter(x => x.market));
      return { icon: '🎉', title: `Festival en ${l.n}`, text: `Celebran el aniversario de ${l.station}. Lujos y comida vuelan de los estantes.`,
        dur: randi(8, 14), locs: [l.id], price: [{ loc: l.id, item: 'luxury', m: 1.9 }, { loc: l.id, item: 'food', m: 1.4 }] };
  } },
];
function spawnEvent() {
  const total = EVENT_GEN.reduce((a, e) => a + e.w, 0);
  let r = Math.random() * total, gen = EVENT_GEN[0];
  for (const e of EVENT_GEN) { r -= e.w; if (r <= 0) { gen = e; break; } }
  const ev = gen.make();
  if (!ev) return;
  ev.start = S.day; ev.end = S.day + ev.dur; ev.uid = Math.random().toString(36).slice(2, 8);
  S.events.push(ev);
  addNews(ev.icon, `<b>${ev.title}</b> — ${ev.text}`, '#ffc857');
  showEventBanner(ev);
  // contrato de ayuda humanitaria
  if (ev.relief) {
    const l = LOC[ev.relief.loc];
    const qty = randi(8, 16) * Math.min(4, S.lv.hull);
    (S.contracts[l.id] = S.contracts[l.id] || []).unshift({ type: 'deliver', id: Math.random().toString(36).slice(2, 8), from: l.id, to: l.id, item: ev.relief.item, qty,
      reward: Math.round(qty * ITEMS[ev.relief.item].b * 3.2 / 10) * 10, rep: 15, days: ev.dur, faction: l.faction, urgent: 1 });
  }
}

// ---------- paso de un día ----------
function tickDay() {
  S.day++;
  for (const id in S.sat) for (const k in S.sat[id]) {
    S.sat[id][k] += (1 - S.sat[id][k]) * 0.07;
    S.drift[id][k] = clamp(S.drift[id][k] * 0.96 + rand(-0.035, 0.035), -0.25, 0.25);
  }
  for (const id in S.depl) S.depl[id] = Math.max(0, S.depl[id] - 0.06);
  const inc = dailyIncome();
  if (inc) { S.credits += inc; S.stats.earned += inc; }
  // eventos
  const ended = S.events.filter(e => e.end <= S.day);
  for (const e of ended) addNews('🕊️', `Termina: ${e.title}`, '#8fa3c7');
  S.events = S.events.filter(e => e.end > S.day);
  if (S.day >= S.nextEvent) {
    if (S.events.length < 3) spawnEvent();
    S.nextEvent = S.day + randi(9, 17);
  }
  // contratos
  for (const id in S.nextContracts) if (S.day >= S.nextContracts[id]) genContracts(id);
  for (const c of [...S.active]) if (S.day > c.deadline) {
    S.active = S.active.filter(x => x !== c);
    if (c.faction) repChange(c.faction, -4, true);
    addNews('❌', `Contrato vencido (${c.type === 'deliver' ? ITEMS[c.item].n : 'recompensa'}). Reputación −4`, '#ff6b7d');
    toast('Un contrato ha vencido', 'bad');
  }
  if (S.day % 3 === 0) save();
}

function addNews(icon, html, col) {
  S.news.unshift({ day: S.day, icon, html, col });
  if (S.news.length > 60) S.news.length = 60;
  if (typeof updateTicker === 'function') updateTicker();
}
