// Economy simulator: loads the real game data/formulas and plays an "efficient
// active player" who mines, hauls ore to cities, trades goods and buys the
// upgrade with the best payback. Prints when each unlock is reached.
//   node tools/balance-sim.js
const fs = require('fs'), vm = require('vm'), path = require('path');
const ctx = { console, Math, Date, JSON, Object, Array, localStorage: { getItem() { return null; }, setItem() {} } };
vm.createContext(ctx);
const src = f => fs.readFileSync(path.join(__dirname, '..', 'src', f), 'utf8');
vm.runInContext(src('data.js') + '\n' + src('state.js') + '\n' + src('politics.js') + `
function toast() {} function sfx() {} function showEventBanner() {} function updateTicker() {}
var TEX = {};
this.api = { newGame, ship, UPG, UPG_KEYS, upgCost, LOC, NODES, FIELDS, ITEMS, ORES, GOODS, OUTPOST, outpostRate, outpostCap,
  PROJECTS, PROJ, built, INVEST, STATION_TIER, UNLOCKS, U, Z_ENEMY, incomeMult, totalIncome, locOpen, has, travelInfo,
  econScale, influence, checkUnlocks, tradeRoutes, hireFreighter, FREIGHT, freighterIncome, getS: () => S };
`, ctx);
const A = ctx.api;
const S = () => A.getS();
A.newGame();

const Z_HP = [1, 3.5, 6, 11, 16, 38];
const DEPTH = 0.55;
function fieldStats(f) {
  const keys = Object.keys(f.ores).sort((a, b) => A.ITEMS[a].b - A.ITEMS[b].b);
  let wsum = 0, val = 0, hard = 0;
  keys.forEach((k, i) => { const w = f.ores[k] * (1 + DEPTH * 4 * (i / Math.max(1, keys.length - 1))); wsum += w; val += w * A.ITEMS[k].b; hard += w * A.ITEMS[k].h; });
  const mix = {}; keys.forEach((k, i) => mix[k] = f.ores[k] * (1 + DEPTH * 4 * (i / Math.max(1, keys.length - 1))) / wsum);
  return { val: val / wsum, hard: hard / wsum, mix };
}
function marketMult(locId, mix) { const m = A.LOC[locId].market; let v = 0; for (const k in mix) v += mix[k] * (m[k] || 0); return v; }
function projMult(locId) { return (A.built('elevator') ? 1.25 : 1) * (locId === 'marte' && A.built('terraform') ? 2 : 1); }
function legTime(from, to) { const i = A.travelInfo(to, from); const dur = A.built('gates') ? 1.1 : Math.min(6, Math.max(1.6, 1.2 + i.days * 0.3)); return dur + 5 + i.danger * 25; }
function combatOK(z) { if (z < 2) return 1; const need = 15 * A.Z_ENEMY[z] * 2.2; const r = A.ship.weaponDps / need; return r >= 1 ? 1 : Math.max(0.25, r); }

// best active activity: returns { rate (cr/s), kind, where }
function bestActivity() {
  const s = S(); const opts = [];
  const cargo = A.ship.cargoMax, im = A.incomeMult();
  for (const L of A.FIELDS) {
    if (!A.locOpen(L.id)) continue;
    const f = L.field, st = fieldStats(f);
    const tRock = 142.8 * st.hard * Z_HP[f.z] / A.ship.laserDps + 3;
    const ups = 8.86 * A.ship.yieldMult / tRock;
    const fill = cargo / ups;
    const over = 3400 * DEPTH * 2 / (360 * A.ship.thrust) + 4;
    const cOK = combatOK(f.z) * (f.hazard === 'heat' && !A.ship.shieldMax ? 0.6 : 1);
    const here = marketMult(L.id, st.mix) * projMult(L.id);
    opts.push({ kind: 'mine+depot', where: L.id, rate: cargo * st.val * im * here * 0.89 / (fill + over) * cOK });
    if (A.has(A.U.MAP)) for (const C of A.NODES) {
      if (!C.market || C.depot || C.id === L.id || !A.locOpen(C.id)) continue;
      const cm = marketMult(C.id, st.mix) * projMult(C.id);
      const t = fill + over + legTime(L.id, C.id) + legTime(C.id, L.id);
      opts.push({ kind: 'mine+haul', where: L.id + '→' + C.id, rate: cargo * st.val * im * cm * 0.89 / t * cOK });
    }
  }
  if (A.has(A.U.TRADE)) {
    for (const P of A.NODES) for (const C of A.NODES) {
      if (!P.market || !C.market || P.depot || C.depot || P.id === C.id || !A.locOpen(P.id) || !A.locOpen(C.id)) continue;
      for (const g of A.GOODS) {
        const pm = P.market[g], cmk = C.market[g]; if (pm == null || pm > 1 || cmk == null) continue;
        const b = A.ITEMS[g].b * A.econScale();
        const buy = b * pm * 1.07 * 1.25, sell = b * cmk * projMult(C.id) * 0.95 * 0.8;
        // sustained: each market's demand refills ~3%/day of demandCap; a player rotating
        // between ~3 hungry markets sells at ~55% of the fresh price on average
        const t = legTime(P.id, C.id) * 2 + 6, D = 1.5 * 150 * Math.pow(1.8, Math.max(0, s.unlock - 5));
        const units = Math.min(cargo, D / 1.5, s.credits / buy, D * 0.03 * (t / 20) * 3);
        if (units < 5) continue;
        opts.push({ kind: 'trade', where: `${g} ${P.id}→${C.id}`, rate: units * (sell * 0.55 / 0.8 - buy) * 2 / t });
        const fu = Math.min(cargo, D / 1.5, s.credits / buy); opts.push({ kind: "fresh", where: `${g} ${P.id}→${C.id}`, rate: fu * (sell * 0.72 / 0.8 - buy) / t, noPick: 1 });  // ×2: players chain routes (sell here, buy the next good)
      }
    }
  }
  opts.sort((a, b) => b.rate - a.rate);
  bestActivity.last = opts;
  return opts.find(o => !o.noPick);
}
function rateNow() { const a = bestActivity(); return (a ? a.rate : 0) + A.totalIncome(); }

function candidates() {
  const s = S(), out = [];
  const base = rateNow();
  const tryDelta = (apply, undo) => { apply(); const r = rateNow(); undo(); return r - base; };
  for (const k of A.UPG_KEYS) {
    const u = A.UPG[k]; if (!A.has(u.stage) || s.lv[k] >= u.max) continue;
    const cost = A.upgCost(k, s.lv[k]);
    const g = tryDelta(() => s.lv[k]++, () => s.lv[k]--);
    out.push({ name: 'upg ' + k, cost, gain: Math.max(g, k === 'tank' || k === 'engine' ? base * 0.002 : 0), buy: () => { s.lv[k]++; if (k === 'hull') s.hull = A.ship.hpMax; } });
  }
  if (A.has(A.U.OUTPOST)) for (const L of A.FIELDS) {
    if (!A.locOpen(L.id)) continue;
    const o = s.outposts[L.id], z = L.field.z;
    const boost = (L.id === 'luna' && A.built('driver') ? 3 : 1) * (A.built('ringstation') ? 3 : 1) * A.incomeMult();
    if (!o) { out.push({ name: 'build ' + L.id, cost: A.OUTPOST.build[z], gain: A.OUTPOST.rate[z] * boost, buy: () => s.outposts[L.id] = { lv: 1, n: 1 } }); continue; }
    if (o.n < A.outpostCap(o.lv)) out.push({ name: 'drone ' + L.id, cost: A.OUTPOST.drone[z] * Math.pow(A.OUTPOST.growth, o.n), gain: A.OUTPOST.rate[z] * Math.pow(2, o.lv - 1) * boost, buy: () => o.n++ });
    if (o.lv < A.OUTPOST.maxLv) out.push({ name: 'outlv ' + L.id, cost: A.OUTPOST.build[z] * A.OUTPOST.lvCost[o.lv - 1], gain: A.outpostRate(z, o.lv, o.n) * boost, buy: () => o.lv++ });
  }
  if (A.has(A.U.TRADE) && (s.freighters || []).length < A.FREIGHT.max) {
    let best = null;
    for (const L of A.NODES) for (const r of A.tradeRoutes(L.id)) { const f = { from: L.id, to: r.to, g: r.g }; if ((s.freighters || []).filter(x => x.from === f.from && x.to === f.to && x.g === f.g).length >= 3) continue; const inc = A.freighterIncome(f); if (!best || inc > best.inc) best = { f, inc }; }
    if (best) out.push({ name: 'freighter', cost: A.FREIGHT.cost(), gain: best.inc, buy: () => { s.freighters.push(best.f); } });
  }
  for (const p of A.PROJECTS) {
    if (A.built(p.id) || !A.has(p.stage)) continue;
    const g = tryDelta(() => s.projects[p.id] = 1, () => delete s.projects[p.id]);
    out.push({ name: 'proj ' + p.id, cost: p.cost, gain: g + p.infl * 0.0 + 1e-9, buy: () => s.projects[p.id] = 1, infl: p.infl });
  }
  if (A.has(A.U.SATURN)) for (const id in A.STATION_TIER) {
    const lv = s.invest[id] || 0; if (lv >= 3) continue;
    const cost = A.INVEST.cost[lv] * A.STATION_TIER[id];
    const g = tryDelta(() => s.invest[id] = lv + 1, () => { if (lv) s.invest[id] = lv; else delete s.invest[id]; });
    out.push({ name: 'invest ' + id, cost, gain: g, buy: () => s.invest[id] = lv + 1, infl: A.INVEST.infl[lv] });
  }
  return out;
}

const log = [], unlockAt = {};
let t = 0, lastUnlock = 0, trips = 0, actCount = {};
while (t < 5 * 3600) {
  const s = S();
  const a = bestActivity();
  const dt = 20;
  const gain = (a ? a.rate : 0) * dt + A.totalIncome() * dt;
  s.credits += gain; s.stats.earned += gain; t += dt;
  if (a) actCount[a.kind] = (actCount[a.kind] || 0) + dt;
  A.checkUnlocks();
  if (s.unlock > lastUnlock) { for (let u = lastUnlock + 1; u <= s.unlock; u++) unlockAt[u] = t; lastUnlock = s.unlock; const bk = {}; for (const o of bestActivity.last || []) if (!bk[o.kind]) bk[o.kind] = o; const fl = {}; for (const o of bestActivity.last || []) if (o.kind === 'mine+depot') fl[o.where] = Math.round(o.rate); log.push('         best by kind: ' + Object.values(bk).map(o => `${o.kind} ${Math.round(o.rate)} (${o.where})`).join(' | ') + ' || fields ' + JSON.stringify(fl)); log.push(`${(t / 60).toFixed(1).padStart(6)} min  UNLOCK ${s.unlock} ${A.UNLOCKS[s.unlock].title.padEnd(20)} active ${Math.round(a ? a.rate : 0)}/s (${a && a.kind} ${a && a.where})  drones ${Math.round(A.totalIncome())}/s`); }
  // a real player buys guns & shields to handle the best zone they have open
  { const zs = A.FIELDS.filter(L => A.locOpen(L.id)).map(L => L.field.z); const zmax = Math.max(...zs);
    if (zmax >= 2) for (let g = 0; g < 60; g++) { if (combatOK(zmax) >= 1) break; const c = A.upgCost('weapons', s.lv.weapons); if (c > s.credits * 0.5) break; s.credits -= c; s.lv.weapons++; } }
  // shopping
  for (let guard = 0; guard < 200; guard++) {
    const r = Math.max(1, rateNow());
    const cs = candidates().filter(c => c.gain > 0 || c.infl);
    if (!cs.length) break;
    for (const c of cs) { const ta = Math.max(0, (c.cost - s.credits) / r); c.score = ta + c.cost / Math.max(1e-9, c.gain) + (c.infl && A.has(A.U.SATURN) ? -c.cost / r * 0.5 : 0); }
    cs.sort((x, y) => x.score - y.score);
    const b = cs[0];
    if (b.cost > s.credits) break;
    s.credits -= b.cost; b.buy();
  }
  if (!s.won && A.has(A.U.SATURN) && A.influence() >= 100) { s.won = true; log.push(`${(t / 60).toFixed(1).padStart(6)} min  WIN (influence ${A.influence()})`); break; }
}
const s = S();
console.log(log.join('\n'));
console.log('\nfinal', (t / 60).toFixed(0), 'min · lv', JSON.stringify(s.lv));
console.log('outposts', JSON.stringify(s.outposts), 'projects', Object.keys(s.projects).join(','));
console.log('time share', Object.entries(actCount).map(([k, v]) => `${k} ${Math.round(v / t * 100)}%`).join(' · '));
console.log('freighters', (s.freighters || []).length, 'influence', A.influence(), 'passive share of income', Math.round(A.totalIncome() / rateNow() * 100) + '%');
