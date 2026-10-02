'use strict';
// ============ STATE, ECONOMY & WORLD ============
const SAVE_KEY = 'solar_prospector_v3';
let S = null;
// ---------- player-facing text (English + Spanish) ----------
Object.assign(TXT, {
  st_ship_name: { en: 'Pioneer', es: 'Pionera' },
  st_news_start: { en: 'Your old mining ship is ready at {st}. Time to get rich.', es: 'Tu vieja nave minera te espera en {st}. Hora de hacerte rico.' },
  st_dem_hungry: { en: 'Hungry', es: 'Ávido' },
  st_dem_steady: { en: 'Steady', es: 'Estable' },
  st_dem_low: { en: 'Low', es: 'Bajo' },
  st_dem_saturated: { en: 'Saturated', es: 'Saturado' },
  st_black_toast: { en: 'Black market sale: −{n} reputation with every faction', es: 'Venta en el mercado negro: −{n} de reputación con todas las facciones' },
  st_rep_toast: { en: '{f}: {d} reputation', es: '{f}: {d} de reputación' },
  st_outpost_news: { en: 'Drone outpost built at {field}', es: 'Puesto minero de drones construido en {field}' },
  st_outpost_lv_news: { en: '{field} outpost upgraded to level {lv} (×2 output)', es: 'Puesto minero de {field} mejorado a nivel {lv} (producción ×2)' },
  st_project_news: { en: '<b>{n}</b> completed. {fx}.', es: '<b>{n}</b> completado. {fx}.' },
  st_c_deliver: { en: 'Deliver <b>{q} {item}</b> to <b>{st}</b> ({n})', es: 'Entrega <b>{q} {item}</b> en <b>{st}</b> ({n})' },
  st_c_bounty_1: { en: 'Destroy <b>1</b> pirate fleet', es: 'Destruye <b>1</b> flota pirata' },
  st_c_bounty_n: { en: 'Destroy <b>{k}</b> pirate fleets', es: 'Destruye <b>{k}</b> flotas piratas' },
  st_c_bounty_at: { en: ' at <b>{at}</b> (the warlord\'s field or routes through it)', es: ' en <b>{at}</b> (el campo del caudillo o las rutas que lo cruzan)' },
  st_max_contracts: { en: 'Max 5 active contracts', es: 'Máximo 5 contratos activos' },
  st_contract_accepted: { en: 'Contract accepted', es: 'Contrato aceptado' },
  st_contract_done: { en: 'Contract complete: +{n} cr', es: 'Contrato cumplido: +{n} cr' },
  st_event_over: { en: 'Over: {t}', es: 'Terminó: {t}' },
  st_contract_expired_news: { en: 'Contract expired. Reputation −4', es: 'Contrato vencido. Reputación −4' },
  st_contract_expired_toast: { en: 'A contract expired', es: 'Un contrato venció' },
});


function newGame() {
  S = {
    v: 3, day: 0, credits: 0, loc: 'luna', fuel: 60, hull: 60, shipName: tx('st_ship_name'),
    lv: { hull: 1, laser: 1, magnet: 1, cargo: 1, extractor: 1, refinery: 1, engine: 1, tank: 1, shield: 1, weapons: 1, scanner: 1 },
    cargo: {},
    rep: { tierra: 5, marte: 0, cinturon: 0, exterior: 0, piratas: -10 },
    invest: {}, outposts: {}, projects: {}, stock: {}, freighters: [], cd: {}, nuked: [], loans: [], peace: 0, sat: {}, demand: {}, allies: {}, spoils: {}, drift: {}, depl: {}, bal: 3,
    events: [], news: [], contracts: {}, active: [],
    stats: { mined: 0, earned: 0, won: 0, lost: 0, dist: 0, contracts: 0, traded: 0, docks: 0, jackpots: 0, kills: 0, droneEarned: 0 },
    unlock: 0, seenUpg: {}, hints: {}, won: false, nextEvent: 0, nextContracts: {}, lastSeen: Date.now(),
  };
  for (const l of NODES) if (l.market) { S.sat[l.id] = {}; S.drift[l.id] = {}; for (const k in l.market) { S.sat[l.id][k] = 1; S.drift[l.id][k] = rand(-0.06, 0.06); } }
  if (typeof resetLocs === 'function') resetLocs();
  addNews('📡', tx('st_news_start', { st: LOC.luna.station }), '#3de8ff');
  return S;
}
// ---------- Clawcade leaderboard: the most credits you've ever held ----------
function trackPeak() { if (S && S.credits > (S.stats.peak || 0)) S.stats.peak = Math.floor(S.credits); }
let postedPeak = 0;
function postPeak() {
  if (!S || !S.stats.peak || S.stats.peak <= postedPeak) return;
  postedPeak = S.stats.peak;
  try { if (window.parent && window.parent !== window) window.parent.postMessage({ clawcade: 'score', score: S.stats.peak }, '*'); } catch (e) {}
}
function save() { if (!S) return; trackPeak(); S.lastSeen = Date.now(); try { localStorage.setItem(SAVE_KEY, JSON.stringify(S)); } catch (e) {} }
function loadSave() {
  try {
    const s = localStorage.getItem(SAVE_KEY); if (!s) return null; const d = JSON.parse(s);
    if (!d || d.v !== 3) return null;
    d.projects = d.projects || {};
    d.lv.extractor = d.lv.extractor || 1;
    d.stock = d.stock || {}; d.freighters = d.freighters || []; d.cd = d.cd || {}; d.nuked = d.nuked || []; d.loans = d.loans || []; d.peace = d.peace || 0;
    for (const e of d.events || []) if (/^(Pirate warlord at|Caudillo pirata en)/.test(e.title || '') && !e.warlord && e.locs) { e.kind = 'warlord'; e.warlord = e.locs[0]; } d.demand = d.demand || {}; d.allies = d.allies || {}; d.spoils = d.spoils || {};
    if (d.won && !d.signal) d.signal = 1;   // saves that already won get the Oort signal
    if (!d.bal) { for (const id in d.outposts) d.outposts[id].n = Math.min(d.outposts[id].n, outpostCap(d.outposts[id].lv)); d.bal = 2; }
    // bal 3: black-market sales used to wipe reputation (−0.02 per unit); undo that once, unless a planet was nuked
    if (d.bal < 3) { if (!(d.nuked || []).length) for (const f in d.rep) if (f !== 'piratas' && d.rep[f] < -10) d.rep[f] = -10; d.bal = 3; }
    return d;
  } catch (e) { return null; }
}
function hasSave() { return !!loadSave(); }
// earlier formats were incompatible prototypes; free their space
try { localStorage.removeItem('solar_prospector_v1'); localStorage.removeItem('solar_prospector_v2'); } catch (e) {}
const has = stage => S && S.unlock >= stage;
const locOpen = id => has(LOC[id].tier || 0) && (!LOC[id].secret || !!S.signal);
// the hidden final field shows up (locked, as an unknown signal) once the frontier opens
const locVisible = id => !LOC[id].secret || has(U.FRONTIER);
const upgOpen = k => has(UPG[k].stage);
const locZone = id => LOC[id].field ? LOC[id].field.z : (LOC[id].parent && LOC[LOC[id].parent].field ? LOC[LOC[id].parent].field.z : clamp((LOC[id].tier || 0) - 2, 0, 5));
const econScale = () => S.unlock < 5 ? 1 : 5 * Math.pow(2, S.unlock - 5);
const itemBase = k => ITEMS[k].ore ? ITEMS[k].b : ITEMS[k].b * econScale();

// ---------- derived stats ----------
const ship = {
  get cargoMax() { return Math.floor(UPG.hull.cargo[S.lv.hull - 1] * (1 + 0.25 * (S.lv.cargo - 1))); },
  get hpMax() { return UPG.hull.hp[S.lv.hull - 1]; },
  get mass() { return UPG.hull.mass[S.lv.hull - 1]; },
  get fuelMax() { return Math.round(60 * Math.pow(1.22, S.lv.tank - 1)); },
  get laserDps() { return 12 * Math.pow(1.17, S.lv.laser - 1); },
  get yieldMult() { return (1 + 0.15 * (S.lv.extractor - 1)) * (1 + 0.1 * spoilCount('rights')); },
  get laserRange() { return 190 + Math.min(190, (S.lv.laser - 1) * 6); },
  get thrust() { return Math.min(2.2, 1 + 0.06 * (S.lv.engine - 1)); },
  get speed() { return 1 + 0.12 * (S.lv.engine - 1); },
  get eff() { return 1 + 0.07 * (S.lv.engine - 1); },
  get warpTime() { return Math.max(1.5, 5 - 0.2 * (S.lv.engine - 1)); },
  get shieldMax() { return S.lv.shield > 1 ? Math.round(30 * Math.pow(1.24, S.lv.shield - 2)) : 0; },
  get weaponDps() { return 15 * Math.pow(1.19, S.lv.weapons - 1); },
  get magnet() { return 130 + Math.min(370, (S.lv.magnet - 1) * 16); },
  get drones() { return Math.min(6, Math.floor((S.lv.magnet - 1) / 3)); },
  get avoid() { return [0, 0.12, 0.22, 0.32, 0.42][S.lv.scanner - 1]; },
  get refinery() { return Math.pow(1.07, S.lv.refinery - 1); },
};
function incomeMult() {
  let inv = 0; for (const id in S.invest) inv += S.invest[id];
  return ship.refinery * (1 + INVEST.bonus * inv) * (built('dyson') ? 5 : 1) * sysDef().value * (1 + 0.1 * legacyLv('ore'));
}
function cargoUsed() { let n = 0; for (const k in S.cargo) n += S.cargo[k]; return n; }
function cargoFree() { return ship.cargoMax - cargoUsed(); }
function addCargo(k, n) { S.cargo[k] = (S.cargo[k] || 0) + n; if (S.cargo[k] <= 0) delete S.cargo[k]; }
function oreValueAt(locId) { let v = 0; for (const k of ORES) if (S.cargo[k]) v += oreSaleValue(locId, k, S.cargo[k]); return v; }
// what n units of ore fetch, following the same price slide doSell applies
function oreSaleValue(locId, k, n) {
  const sp = sellPrice(locId, k); if (!sp) return 0;
  const s0 = S.sat[locId][k] || 1, q = 1 - 0.25 / Math.max(100, ship.cargoMax), fl = 0.4;
  const m = s0 <= fl ? 0 : Math.min(n, Math.ceil(Math.log(fl / s0) / Math.log(q)));
  return sp * (1 - Math.pow(q, m)) / (1 - q) + (n - m) * sp * Math.min(1, fl / s0);
}
// what n units would fetch, accounting for the demand they use up
function goodsValue(locId, k, n) {
  const sp = sellPrice(locId, k); if (!sp) return 0;
  const d = demandOf(locId, k), D = demandCap(), u = Math.min(n, d * D);
  return sp / demandFactor(locId, k) * (u * (0.15 + 0.85 * (d - u / D / 2)) + (n - u) * 0.15);
}
// what your whole hold is worth here: ore, plus goods this station actually wants (never dumps goods at their source)
const wantsGood = (locId, k) => { const m = LOC[locId].market; return m && m[k] != null && m[k] > 1; };
function cargoValueAt(locId) { let v = oreValueAt(locId); for (const k of GOODS) if (S.cargo[k] && wantsGood(locId, k)) v += goodsValue(locId, k, S.cargo[k]); return v; }
function oreValueBase(k) { return ITEMS[k].b * incomeMult(); }
// what one unit of ore is worth right now (base price: depots pay ~0.6×, cities 2–3.5×)
const oreUnit = k => ITEMS[k].b * incomeMult();
// 1–5 value tier for quick reading (iron 1 … void shard 5)
const oreTier = k => clamp(Math.ceil(Math.log10(ITEMS[k].b) * 1.2), 1, 5);
const oreStars = k => '◆'.repeat(oreTier(k)) + '<i class="off">' + '◆'.repeat(5 - oreTier(k)) + '</i>';

// ---------- orbital positions ----------
// orbits can be elliptical (ecc squashes them) and tilted (tilt rotates them) — every star system has its own layout
function orbitXY(o, a, r) {
  r = r == null ? o.r : r;
  const e = o.ecc || 0, tl = o.tilt || 0, x0 = Math.cos(a) * r, y0 = Math.sin(a) * r * (1 - e);
  return { x: x0 * Math.cos(tl) - y0 * Math.sin(tl), y: x0 * Math.sin(tl) + y0 * Math.cos(tl) };
}
function locPos(loc, day) {
  if (typeof loc === 'string') loc = LOC[loc];
  if (loc.follow) {
    const f = LOC[loc.follow];
    const p = orbitXY(f, f.a0 + day / f.period * TAU + loc.offset);
    if (f.parent) { const q = locPos(LOC[f.parent], day); p.x += q.x; p.y += q.y; }
    return p;
  }
  const a = loc.a0 + day / loc.period * TAU;
  if (loc.parent) {
    const p = locPos(LOC[loc.parent], day);
    return { x: p.x + Math.cos(a) * loc.r, y: p.y + Math.sin(a) * loc.r };
  }
  return orbitXY(loc, a);
}
function locDist(a, b, day) { const p = locPos(a, day), q = locPos(b, day); return Math.hypot(p.x - q.x, p.y - q.y); }
// a full hold is heavy: empty ships burn 60% of the fuel, full ones 140%
function travelInfo(to, from, load) {
  from = from || S.loc;
  if (load == null) load = Math.min(1, cargoUsed() / ship.cargoMax);
  const d = Math.max(8, locDist(from, to, S.day));
  let fuel = Math.ceil(d * 0.1 * ship.mass / ship.eff * (0.6 + 0.8 * load) * fuelEventMult() * (built('beacons') ? 0.7 : 1));
  let days = Math.max(1, Math.round(d / (22 * ship.speed * (built('beacons') ? 1.5 : 1))));
  if (built('gates')) { fuel = 0; days = 1; }
  const danger = routeDanger(from, to);
  return { d, fuel, days, danger };
}
function fuelEventMult() { let m = 1; for (const e of S.events) if (e.fuelCost) m = Math.max(m, e.fuelCost); return m; }
function locDanger(id) {
  if (!has(U.BELT)) return 0;
  let d = LOC[id].danger || 0;
  for (const e of S.events) if (e.danger) for (const x of e.danger) if (x.loc === id) d += x.add;
  if (built('fleet')) d *= 0.5;
  return clamp(d, 0, 0.95);
}
function routeDanger(a, b) {
  const base = Math.max(locDanger(a), locDanger(b)) * 0.8 + (locDanger(a) + locDanger(b)) * 0.1;
  return clamp(base * (1 - ship.avoid), 0, 0.9);
}

// ---------- market ----------
// Several events can touch the same price. They never stack: the strongest boost
// and the strongest drop apply, so repeating an action can't multiply prices.
function eventPriceMult(locId, item) {
  let up = 1, down = 1;
  for (const e of S.events) if (e.price) for (const p of e.price) if ((p.loc === locId || p.loc === '*') && p.item === item) {
    if (p.m > 1) up = Math.max(up, p.m); else down = Math.min(down, p.m);
  }
  return clamp(up * down, 0.25, 3.5);
}
function basePrice(locId, item) {
  const l = LOC[locId];
  const mult = l.market && l.market[item];
  if (mult == null) return null;
  const b = ITEMS[item].ore ? ITEMS[item].b * incomeMult() * (built('elevator') ? 1.25 : 1) : itemBase(item);
  const pm = (locId === 'marte' && built('terraform') ? 2 : 1) * (ITEMS[item].ore ? allyMult(locId) : 1);
  return b * mult * pm * (1 + (S.drift[locId][item] || 0)) * (S.sat[locId][item] || 1) * eventPriceMult(locId, item) * demandFactor(locId, item);
}
// ---------- demand: each station only wants so many goods ----------
// Deliveries use up a station's appetite for a good; it comes back slowly
// (~3%/day), so one route pays well once or twice, then you move on.
const demandCap = () => Math.round(stockMax() * 1.5);
function demandOf(locId, item) { if (ITEMS[item].ore) return 1; const d = (S.demand[locId] || {})[item]; return d == null ? 1 : d; }
function demandFactor(locId, item) { return ITEMS[item].ore ? 1 : 0.15 + 0.85 * demandOf(locId, item); }
function useDemand(locId, item, units) {
  S.demand[locId] = S.demand[locId] || {};
  S.demand[locId][item] = Math.max(0, demandOf(locId, item) - units / demandCap());
}
const DEMAND_REGEN = 0.03;
function demandDays(locId, item) { return Math.ceil((1 - demandOf(locId, item)) / DEMAND_REGEN); }
function demandLabel(d) { return d >= 0.75 ? [tx('st_dem_hungry'), 'good'] : d >= 0.45 ? [tx('st_dem_steady'), 'mid'] : d >= 0.2 ? [tx('st_dem_low'), 'low'] : [tx('st_dem_saturated'), 'bad']; }
// permanent war alliances: +15% for ore at an ally's stations per star (max 3)
function allyMult(locId) { const f = LOC[locId].faction; return 1 + 0.15 * ((S.allies || {})[f] || 0); }
function spoilCount(kind) { let n = 0; for (const f in S.spoils || {}) if (S.spoils[f].includes(kind)) n++; return n; }
function priceRatio(locId, item) {
  const l = LOC[locId]; const m = l.market && l.market[item]; if (m == null) return 0;
  return m * (1 + (S.drift[locId][item] || 0)) * (S.sat[locId][item] || 1) * eventPriceMult(locId, item) * demandFactor(locId, item) * (locId === 'marte' && built('terraform') ? 2 : 1) * (ITEMS[item].ore ? allyMult(locId) : 1);
}
function sellPrice(locId, item) { const p = basePrice(locId, item); return p == null ? null : Math.max(1, Math.round(p * 0.95)); }
function buyPrice(locId, item) {
  const l = LOC[locId]; const mult = l.market && l.market[item];
  if (mult == null || mult > 1.0 || ITEMS[item].ore) return null;
  return Math.max(2, Math.round(basePrice(locId, item) * 1.07));
}
// Fuel follows the economy: a round trip costs roughly a tenth of what a typical haul earns.
// (eased in over the first stages so the Star Map doesn't bite new players)
const fuelBase = () => Math.max(1, 0.09 * Math.pow(S.stats.earned, 0.72) * clamp(0.5 + 0.125 * (S.unlock - 2), 0.5, 1));
function fuelPrice(locId) {
  let m = 1; for (const e of S.events) if (e.fuelPrice) m = Math.max(m, e.fuelPrice);
  return Math.max(1, Math.round((LOC[locId].fuel || 6) / 5 * fuelBase() * m * Math.pow(0.85, spoilCount('fuel')) * Math.pow(0.92, legacyLv('fuel'))));
}
function marketClosed(locId) { return S.events.some(e => e.closed && e.closed.includes(locId)); }

function earn(n) {
  S.credits += n; S.stats.earned += n;
  checkUnlocks();
}
function doSell(locId, item, n) {
  n = Math.min(n, S.cargo[item] || 0);
  let total = 0;
  for (let i = 0; i < n; i++) {
    total += sellPrice(locId, item);
    // ore: market depth scales with your hold (a full hold moves prices ~22%); goods: use up demand
    if (ITEMS[item].ore) S.sat[locId][item] = Math.max(0.4, S.sat[locId][item] * (1 - 0.25 / Math.max(100, ship.cargoMax)));
    else useDemand(locId, item, 1);
  }
  addCargo(item, -n);
  S.stats.traded += n;
  const l = LOC[locId];
  if (n > 0 && l.faction) {
    // reputation moves per sale, scaled by how much of a hold it is (never by raw units:
    // late-game holds carry thousands, which used to wipe reputation out in one sale)
    const frac = Math.min(1, n / Math.max(100, ship.cargoMax));
    let gain = Math.min(3, n / 60);
    for (const e of S.events) if (e.relief && e.relief.loc === locId && e.relief.item === item) gain += 3 + 12 * frac;
    if (item === 'arms') for (const e of S.events) if (e.war && e.war.includes(l.faction)) {
      const other = e.war.find(f => f !== l.faction); repChange(other, -(2 + 8 * frac)); gain += 2 + 8 * frac;
    }
    repChange(l.faction, gain, true);
    if (l.black) { const loss = blackMarketLoss(n); for (const f in FACTIONS) if (f !== 'piratas') repChange(f, -loss, true); if (loss >= 1) toast(tx('st_black_toast', { n: Math.round(loss) }), 'bad'); }
  }
  earn(total);
  if (n > 0 && typeof warSalePush === 'function') warSalePush(locId, item, total);
  return total;
}
// Producers hold limited stock (grows each stage), which refills ~10% per day.
const stockMax = () => Math.round(150 * Math.pow(1.8, Math.max(0, S.unlock - 5)));
function stockLeft(locId, item) { const f = (S.stock[locId] || {})[item]; return Math.floor(stockMax() * (f == null ? 1 : f)); }
function doBuy(locId, item, n) {
  n = Math.min(n, cargoFree(), stockLeft(locId, item));
  let total = 0, bought = 0;
  for (let i = 0; i < n; i++) {
    const p = buyPrice(locId, item);
    if (p == null || S.credits - total < p) break;
    total += p; bought++;
    S.sat[locId][item] = Math.min(2.5, S.sat[locId][item] * (1 + 0.5 / Math.max(100, ship.cargoMax)));
  }
  S.credits -= total; addCargo(item, bought);
  S.stock[locId] = S.stock[locId] || {};
  S.stock[locId][item] = Math.max(0, (S.stock[locId][item] == null ? 1 : S.stock[locId][item]) - bought / stockMax());
  return bought;
}
const blackMarketLoss = n => 1 + 5 * Math.min(1, n / Math.max(100, ship.cargoMax));
function repChange(f, d, silent) {
  const before = S.rep[f];
  S.rep[f] = clamp(S.rep[f] + d, -100, 100);
  if (!silent && Math.abs(d) >= 1) toast(tx('st_rep_toast', { f: FACTIONS[f].n, d: (d > 0 ? '+' : '') + Math.round(d) }), d > 0 ? 'good' : 'bad');
  return S.rep[f] - before;
}

function sellAllOre(id, r) {
  r = r || { sold: [], total: 0 };
  if (marketClosed(id)) return r;
  for (const k of ORES) if (S.cargo[k]) {
    const n = S.cargo[k]; const got = doSell(id, k, n);
    r.sold.push([k, n, got]); r.total += got;
  }
  return r;
}
// Where else would this cargo sell for more? (open stations, best first)
function betterMarkets(id) {
  const here = cargoValueAt(id);
  return NODES.filter(l => l.market && l.id !== id && locOpen(l.id) && !marketClosed(l.id))
    .map(l => ({ id: l.id, v: cargoValueAt(l.id), fuel: travelInfo(l.id).fuel }))
    .filter(x => x.v > here * 1.05).sort((a, b) => b.v - a.v).slice(0, 3);
}
// Docking: refuel & repair. Ore is only auto-sold before the Star Map exists.
function dockAtStation() {
  const id = S.loc, l = LOC[id];
  const r = { sold: [], total: 0, fuel: 0, fuelCost: 0, repair: 0, repairCost: 0 };
  if (!has(U.MAP)) sellAllOre(id, r);
  if (has(U.MAP)) {
    const fp = fuelPrice(id);
    const need = Math.floor(ship.fuelMax - S.fuel);
    const can = Math.min(need, Math.floor(S.credits / fp));
    if (can > 0) { S.fuel += can; S.credits -= can * fp; r.fuel = can; r.fuelCost = can * fp; }
  }
  const hneed = Math.ceil(ship.hpMax - S.hull);
  if (hneed > 0) {
    const rp = (l.repair || 3) * (1 + S.unlock);
    const can = Math.min(hneed, Math.floor(S.credits / rp));
    if (can > 0) { S.hull = Math.min(ship.hpMax, S.hull + can); S.credits -= can * rp; r.repair = can; r.repairCost = can * rp; }
  }
  S.stats.docks++;
  if (has(U.TRADE) && l.market && !l.depot && (!S.contracts[id] || !S.nextContracts[id])) genContracts(id);
  save();
  return r;
}

// ---------- drone outposts ----------
function outpostOf(id) { return S.outposts[id]; }
function outpostIncome(id) {
  const o = S.outposts[id]; if (!o) return 0;
  return outpostRate(LOC[id].field.z, o.lv, o.n) * incomeMult() * (id === 'luna' && built('driver') ? 3 : 1) * (built('ringstation') ? 3 : 1);
}
function droneIncome() { let v = 0; for (const id in S.outposts) v += outpostIncome(id); return v; }
function totalIncome() { return droneIncome() + freightIncome(); }
function buildCost(id) { return OUTPOST.build[LOC[id].field.z]; }
function droneCost(id, k) {
  const o = S.outposts[id]; const n = o ? o.n : 0; const z = LOC[id].field.z;
  let c = 0; for (let i = 0; i < (k || 1); i++) c += OUTPOST.drone[z] * Math.pow(OUTPOST.growth, n + i);
  return Math.ceil(c * Math.pow(0.88, spoilCount('drones')) * Math.pow(0.92, legacyLv('drones')));
}
function outpostLvCost(id) { const o = S.outposts[id]; if (!o || o.lv >= OUTPOST.maxLv) return null; return OUTPOST.build[LOC[id].field.z] * OUTPOST.lvCost[o.lv - 1]; }
function buildOutpost(id) {
  const c = buildCost(id); if (S.credits < c || S.outposts[id]) return false;
  S.credits -= c; S.outposts[id] = { lv: 1, n: 1 };
  addNews('🤖', tx('st_outpost_news', { field: LOC[id].field.n }), '#6dffb0');
  return true;
}
function maxAffordableDrones(id) {
  const o = S.outposts[id]; if (!o) return 0;
  let n = 0, c = 0; const z = LOC[id].field.z;
  while (n < outpostCap(o.lv) - o.n) { const nc = OUTPOST.drone[z] * Math.pow(OUTPOST.growth, o.n + n) * Math.pow(0.88, spoilCount('drones')) * Math.pow(0.92, legacyLv('drones')); if (c + nc > S.credits) break; c += nc; n++; }
  return n;
}
function buyDrones(id, k) {
  const o = S.outposts[id]; if (!o) return 0;
  if (k === 'max') k = maxAffordableDrones(id);
  k = Math.min(k, outpostCap(o.lv) - o.n);
  if (k <= 0) return 0;
  const c = droneCost(id, k); if (S.credits < c) return 0;
  S.credits -= c; o.n += k; return k;
}
function upgradeOutpost(id) {
  const c = outpostLvCost(id); if (c == null || S.credits < c) return false;
  S.credits -= c; S.outposts[id].lv++;
  addNews('🏭', tx('st_outpost_lv_news', { field: LOC[id].field.n, lv: S.outposts[id].lv }), '#6dffb0');
  return true;
}
// real-time drone income
let incomeAcc = 0;
function incomeTick(dt) {
  const inc = totalIncome();
  if (!inc) return;
  const g = inc * dt;
  S.credits += g; S.stats.earned += g; S.stats.droneEarned += g;
  incomeAcc += dt;
  if (incomeAcc > 0.5) { incomeAcc = 0; checkUnlocks(); }
}
// ---------- time ----------
// One day passes every DAY_SEC seconds of play (and while away, up to the offline cap).
const DAY_SEC = 50, OFFLINE_CAP = 8 * 3600, OFFLINE_RATE = 0.6;
let OFFLINE = false;   // true while simulating days you were away: no popups, your contracts and backed war wait for you
function offlineGains() {
  const now = Date.now();
  const real = Math.max(0, (now - (S.lastSeen || now)) / 1000);
  const secs = Math.min(real, OFFLINE_CAP);
  S.lastSeen = now;
  if (secs < 30) return null;
  const g = totalIncome() * secs * OFFLINE_RATE;
  if (g >= 1) { S.credits += g; S.stats.earned += g; S.stats.droneEarned += g; }
  const trib = S.galaxy && conquered() ? tributeRate() * secs / 60 : 0;
  if (trib) S.galaxy.tribute += trib;
  // the system keeps living while you're gone
  let days = 0; const newsBefore = S.news.length && S.news[0];
  if (has(U.MAP)) {
    S.dayT = (S.dayT || 0) + secs;
    OFFLINE = true;
    try { while (S.dayT >= DAY_SEC) { S.dayT -= DAY_SEC; tickDay(); days++; } } finally { OFFLINE = false; }
  }
  checkUnlocks();
  const i = S.news.indexOf(newsBefore), fresh = (i < 0 ? S.news : S.news.slice(0, i)).slice(0, 4);
  if (g < 1 && !days && !trib) return null;
  return { secs, real, capped: real > OFFLINE_CAP, g, days, news: fresh, trib };
}

// ---------- progression ----------
let pendingUnlocks = [];
function checkUnlocks() {
  while (S.unlock < UNLOCKS.length - 1 && S.stats.earned >= UNLOCKS[S.unlock + 1].at) {
    S.unlock++;
    const u = UNLOCKS[S.unlock];
    pendingUnlocks.push(S.unlock);
    addNews(u.icon, `<b>${u.title}</b>`, '#ffd24a');
    if (S.unlock === U.TRADE) { S.nextEvent = S.day + 3; for (const l of NODES) if (l.market && !l.depot && locOpen(l.id)) genContracts(l.id); }
  }
}
function nextUnlock() { return S.unlock < UNLOCKS.length - 1 ? UNLOCKS[S.unlock + 1] : null; }

// ---------- megaprojects & system powers ----------
function built(id) { return S && S.projects && S.projects[id]; }
function projectOpen(p) { return has(p.stage) && (!p.req || built(p.req)) && projHere(p); }
// projects that belong to the current star system (signature ones only exist in their own)
const projHere = p => !p.sys || p.sys === sysId();
const sysProjects = () => PROJECTS.filter(projHere);
function buildProject(id) {
  const p = PROJ[id];
  if (built(id) || !projectOpen(p) || S.credits < p.cost) return false;
  S.credits -= p.cost; S.projects[id] = S.day || 1;
  if (id === 'terraform') { repChange('marte', 50, true); delete TEX.marte; }
  addNews(p.icon, tx('st_project_news', { n: p.n, fx: p.fx }), '#ffd24a');
  save();
  return true;
}
// ---------- influence ----------
function influence() {
  let v = 0;
  for (const id in S.invest) for (let i = 0; i < S.invest[id]; i++) v += INVEST.infl[i];
  for (const id in S.outposts) v += S.outposts[id].lv - 1;
  for (const id in S.projects) if (PROJ[id]) v += PROJ[id].infl;
  v += (S.peace || 0) * 3 + (S.nuked || []).length * 10;
  for (const f in S.rep) if (f !== 'piratas') v += Math.max(0, S.rep[f]) / 8;
  v += Math.max(0, S.rep.piratas) / 16;
  v += Math.min(10, S.stats.kills * 0.05);
  return Math.floor(v);
}
function rankName(inf) { let r = RANKS[0][1]; for (const [n, t] of RANKS) if (inf >= n) r = t; return r; }
function investCost(locId) { const lv = S.invest[locId] || 0; return lv >= 3 ? null : Math.round(INVEST.cost[lv] * (STATION_TIER[locId] || 5)); }

// ---------- contracts ----------
function uid() { return Math.random().toString(36).slice(2, 8); }
function genContracts(locId) {
  const l = LOC[locId];
  const list = [];
  const openMarkets = NODES.filter(x => x.market && !x.depot && x.id !== locId && locOpen(x.id));
  for (let i = 0; i < 3; i++) {
    const r = Math.random();
    if (r < 0.55 || !openMarkets.length) {
      const wanted = Object.keys(l.market).filter(k => l.market[k] >= 1.1);
      const item = pick(wanted.length ? wanted : ORES.slice(0, 3));
      const scale = ship.cargoMax / 25;
      const qty = Math.max(4, Math.round(rand(6, 14) * scale * (ITEMS[item].ore ? 1 : 1)));
      const reward = Math.round(qty * itemBase(item) * rand(1.8, 2.4) / 10) * 10;
      list.push({ type: 'deliver', id: uid(), from: locId, to: locId, item, qty, reward, rep: 4 + Math.round(qty / 8), days: randi(18, 35), faction: l.faction });
    } else if (r < 0.8 || !has(U.BELT)) {
      const dest = pick(openMarkets);
      const buyables = GOODS.filter(k => l.market[k] != null && l.market[k] <= 1.0);
      const item = buyables.length ? pick(buyables) : 'food';
      const qty = Math.max(4, Math.round(rand(0.3, 0.6) * ship.cargoMax));
      const reward = Math.round((qty * itemBase(item) * 1.5 + locDist(locId, dest.id, S.day) * 6 * econScale()) / 10) * 10;
      list.push({ type: 'deliver', id: uid(), from: locId, to: dest.id, item, qty, reward, rep: 5 + Math.round(qty / 6), days: randi(25, 45), faction: dest.faction || l.faction });
    } else {
      const kills = randi(1, 3);
      const reward = Math.round(kills * 300 * Z_LOOT[locZone(locId)]);
      list.push({ type: 'bounty', id: uid(), from: locId, kills, reward, rep: 6 * kills, days: randi(25, 50), faction: l.faction });
    }
  }
  S.contracts[locId] = list;
  S.nextContracts[locId] = S.day + randi(8, 14);
}
function contractText(c) {
  if (c.type === 'deliver') return tx('st_c_deliver', { q: c.qty, item: ITEMS[c.item].n, st: LOC[c.to].station, n: LOC[c.to].n });
  return (c.kills > 1 ? tx('st_c_bounty_n', { k: c.kills }) : tx('st_c_bounty_1')) + (c.at ? tx('st_c_bounty_at', { at: LOC[c.at].field ? LOC[c.at].field.n : LOC[c.at].n }) : '') + (c.progress != null ? ` (${c.progress}/${c.kills})` : '');
}
function acceptContract(locId, cid) {
  const list = S.contracts[locId]; const i = list.findIndex(c => c.id === cid);
  if (i < 0) return;
  if (S.active.length >= 5) { toast(tx('st_max_contracts'), 'bad'); return; }
  const c = list.splice(i, 1)[0];
  c.deadline = S.day + c.days;
  if (c.type === 'bounty') c.progress = 0;
  S.active.push(c);
  sfx('click');
  toast(tx('st_contract_accepted'), 'good');
}
function canDeliver(c) { return c.type === 'deliver' && S.loc === c.to && (S.cargo[c.item] || 0) >= c.qty; }
function completeContract(c) {
  if (c.type === 'deliver') addCargo(c.item, -c.qty);
  S.stats.contracts++;
  if (c.faction) repChange(c.faction, c.rep);
  S.active = S.active.filter(x => x !== c);
  addNews('✅', tx('st_contract_done', { n: fmt(c.reward) }), '#6dffb0');
  earn(c.reward);
  sfx('cash');
}

// ---------- one day passes ----------
function tickDay() {
  S.day++;
  if (OFFLINE) {
    // you can't act while away: your contracts and the war you back wait for you
    for (const c of S.active) c.deadline++;
    for (const e of S.events) if (e.war && e.backed) e.end++;
  }
  for (const id in S.sat) for (const k in S.sat[id]) {
    S.sat[id][k] += (1 - S.sat[id][k]) * 0.08;
    S.drift[id][k] = clamp(S.drift[id][k] * 0.96 + rand(-0.035, 0.035), -0.25, 0.25);
  }
  for (const id in S.depl) S.depl[id] = Math.max(0, S.depl[id] - 0.06);
  for (const id in S.stock) for (const k in S.stock[id]) S.stock[id][k] = Math.min(1, S.stock[id][k] + 0.1);
  for (const f in S.rep) if (S.rep[f] < 0) S.rep[f] = Math.min(0, S.rep[f] + 1);   // grudges fade slowly
  for (const id in S.demand) for (const k in S.demand[id]) S.demand[id][k] = Math.min(1, S.demand[id][k] + DEMAND_REGEN);
  for (const f of S.freighters || []) if (freighterIncome(f) > 0) useDemand(f.to, f.g, FREIGHT.cap() / routeCycle(f.from, f.to));
  if (has(U.TRADE)) {
    const ended = S.events.filter(e => e.end <= S.day);
    for (const e of ended) { addNews('🕊️', tx('st_event_over', { t: e.title }), '#8fa3c7'); onEventEnd(e); }
    S.events = S.events.filter(e => e.end > S.day);
    if (S.day >= S.nextEvent) {
      if (S.events.filter(e => !e.mine).length < 4) spawnEvent();
      S.nextEvent = S.day + randi(9, 17);
    }
    for (const id in S.nextContracts) if (S.day >= S.nextContracts[id]) genContracts(id);
    for (const c of [...S.active]) if (S.day > c.deadline) {
      S.active = S.active.filter(x => x !== c);
      if (c.faction) repChange(c.faction, -4, true);
      addNews('❌', tx('st_contract_expired_news'), '#ff6b7d');
      toast(tx('st_contract_expired_toast'), 'bad');
    }
  }
  politicsDay();
  if (S.day % 3 === 0 && !OFFLINE) save();
}

function addNews(icon, html, col) {
  S.news.unshift({ day: S.day, icon, html, col });
  if (S.news.length > 60) S.news.length = 60;
  if (typeof updateTicker === 'function') updateTicker();
}
