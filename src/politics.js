'use strict';
// ============ EVENTS, POLITICS, FREIGHTERS & THE NOVA CANNON ============

// ---------- helpers ----------
const WAR_PAIRS = [['tierra', 'marte'], ['marte', 'cinturon'], ['tierra', 'exterior'], ['cinturon', 'exterior'], ['marte', 'exterior']];
const openMarkets = () => NODES.filter(x => x.market && !x.depot && locOpen(x.id));
const cityOpen = id => LOC[id].market && !LOC[id].depot && locOpen(id);
const factionAlive = f => FACTIONS[f].locs.some(id => !LOC[id].nuked);
const kindActive = (kind, loc) => S.events.some(e => e.kind === kind && (!loc || (e.locs || []).includes(loc)));
// costs scale with how rich you've become, so powers stay meaningful all game
const pcost = (f, min) => Math.round(Math.max(min, S.stats.earned * f));
function addEvent(ev) {
  if (ev.mine && ev.kind) S.events = S.events.filter(e => !(e.mine && e.kind === ev.kind && (e.locs || []).some(l => (ev.locs || []).includes(l))));
  ev.start = S.day; ev.end = S.day + ev.dur; ev.uid = uid();
  // a shortage or boom creates fresh appetite for those goods
  for (const p of ev.price || []) if (p.m > 1 && p.loc !== '*' && !ITEMS[p.item].ore && LOC[p.loc] && LOC[p.loc].market) {
    S.demand[p.loc] = S.demand[p.loc] || {}; S.demand[p.loc][p.item] = Math.max(demandOf(p.loc, p.item), 0.85);
  }
  S.events.push(ev);
  return ev;
}

// ---------- natural system events ----------
const EVENT_GEN = [
  { kind: 'war', w: 1.1, make() {
      if (S.events.some(e => e.war)) return null;
      const pairs = WAR_PAIRS.filter(p => p.every(f => factionAlive(f) && FACTIONS[f].locs.some(locOpen)));
      if (!pairs.length) return null;
      return makeWar(...pick(pairs), randi(28, 50));
  } },
  { kind: 'plague', w: 1, make() {
      const c = openMarkets().filter(x => !x.black && x.market.meds > 1);
      if (!c.length) return null; const l = pick(c);
      return { icon: '☣️', title: `Plague on ${l.n}`, text: `An outbreak hits ${l.station}. Medicine sells ×3 there — delivering it earns big reputation.`,
        dur: randi(18, 32), locs: [l.id], price: [{ loc: l.id, item: 'meds', m: 3 }, { loc: l.id, item: 'food', m: 1.3 }], relief: { loc: l.id, item: 'meds' } };
  } },
  { kind: 'famine', w: 1, make() {
      const c = openMarkets().filter(x => x.market.food > 1);
      if (!c.length) return null; const l = pick(c);
      return { icon: '🌾', title: `Famine on ${l.n}`, text: `${l.station}'s farms failed. Food sells ×2.6 there.`,
        dur: randi(15, 28), locs: [l.id], price: [{ loc: l.id, item: 'food', m: 2.6 }], relief: { loc: l.id, item: 'food' } };
  } },
  { kind: 'refugees', w: 0.7, make() {
      const c = openMarkets().filter(x => x.market.food > 1 && x.market.meds > 1);
      if (!c.length) return null; const l = pick(c);
      return { icon: '🛖', title: `Refugee crisis on ${l.n}`, text: `Thousands flee to ${l.station}. Food and medicine sell ×2 there.`,
        dur: randi(15, 25), locs: [l.id], price: [{ loc: l.id, item: 'food', m: 2 }, { loc: l.id, item: 'meds', m: 2 }], relief: { loc: l.id, item: 'food' } };
  } },
  { kind: 'boom', w: 1.1, make() {
      const l = pick(openMarkets());
      return l && { icon: '🏗️', title: `Construction boom on ${l.n}`, text: `${l.station} is expanding. Metals and machinery sell ×1.8 there.`,
        dur: randi(20, 35), locs: [l.id], price: ['iron', 'nickel', 'titanium', 'platinum', 'machinery'].map(i => ({ loc: l.id, item: i, m: 1.8 })) };
  } },
  { kind: 'goldrush', w: 0.6, make() {
      const l = pick(openMarkets());
      return l && { icon: '🤑', title: `Gold rush on ${l.n}`, text: `Speculators flood ${l.station}. EVERY ore sells ×1.6 there.`,
        dur: randi(10, 16), locs: [l.id], price: ORES.map(i => ({ loc: l.id, item: i, m: 1.6 })) };
  } },
  { kind: 'crash', w: 0.6, make() {
      const l = pick(openMarkets());
      return l && { icon: '📉', title: `Market crash on ${l.n}`, text: `A bank collapse at ${l.station}. Ore prices there are halved — sell elsewhere.`,
        dur: randi(8, 14), locs: [l.id], price: ORES.map(i => ({ loc: l.id, item: i, m: 0.5 })) };
  } },
  { kind: 'techboom', w: 0.7, make() {
      const prod = openMarkets().filter(x => x.market.tech <= 1);
      if (!prod.length) return null; const l = pick(prod);
      return { icon: '💡', title: `Tech breakthrough on ${l.n}`, text: `New chip fabs on ${l.n}: Electronics are half price there and sell ×1.4 everywhere else.`,
        dur: randi(12, 20), locs: [l.id], price: [{ loc: l.id, item: 'tech', m: 0.5 }, { loc: '*', item: 'tech', m: 1.4 }] };
  } },
  { kind: 'rich', w: 1, make() {
      const l = pick(NODES.filter(x => x.field && locOpen(x.id)));
      return l && { icon: '💎', title: `Rich strike: ${l.field.n}`, text: `Probes found rich veins at ${l.n}. More ore and more golden rocks!`,
        dur: randi(15, 25), locs: [l.id], rich: l.id };
  } },
  { kind: 'comets', w: 0.6, make() {
      const l = pick(NODES.filter(x => x.field && locOpen(x.id)));
      return l && { icon: '☄️', title: `Comet swarm at ${l.field.n}`, text: `A comet storm seeds ${l.n} with ice and Helium-3 — and every station pays ×1.5 for them.`,
        dur: randi(12, 20), locs: [l.id], rich: l.id, price: [{ loc: '*', item: 'ice', m: 1.5 }, { loc: '*', item: 'he3', m: 1.5 }] };
  } },
  { kind: 'pirates', w: 0.9, make() {
      if (!has(U.BELT)) return null;
      const l = pick(NODES.filter(x => x.id !== 'pluton' && locOpen(x.id)));
      return l && { icon: '☠️', title: `Pirate surge near ${l.n}`, text: `The Black Syndicate gathers fleets near ${l.n}. Hunting them pays well.`,
        dur: randi(15, 30), locs: [l.id], danger: [{ loc: l.id, add: 0.35 }] };
  } },
  { kind: 'warlord', w: 0.4, make() {
      if (!has(U.BELT)) return null;
      const l = pick(NODES.filter(x => x.field && locOpen(x.id) && x.field.z >= 2));
      if (!l) return null;
      const ev = { icon: '🏴‍☠️', title: `Pirate warlord at ${l.n}`, text: `A notorious warlord raids ${l.n}. Huge bounty for anyone who fights there.`,
        dur: randi(20, 30), locs: [l.id], danger: [{ loc: l.id, add: 0.5 }] };
      const c = S.contracts[l.id] || (S.contracts[l.id] = []);
      if (l.market && !l.depot) c.unshift({ type: 'bounty', id: uid(), from: l.id, kills: 3, reward: Math.round(3 * 1500 * Z_LOOT[l.field.z]), rep: 25, days: ev.dur, faction: l.faction, urgent: 1 });
      return ev;
  } },
  { kind: 'fuel', w: 0.6, make() {
      return { icon: '⛽', title: 'Fuel crisis', text: 'Sabotage at the refineries. Fuel costs double; Ice and Helium-3 sell ×1.4.',
        dur: randi(12, 22), locs: [], fuelPrice: 2, price: [{ loc: '*', item: 'ice', m: 1.4 }, { loc: '*', item: 'he3', m: 1.4 }] };
  } },
  { kind: 'he3rush', w: 0.6, make() {
      return { icon: '⚛️', title: 'Helium-3 rush', text: 'New fusion reactors everywhere. Helium-3 sells ×1.9.',
        dur: randi(18, 30), locs: ['tierra', 'marte'].filter(locOpen), price: [{ loc: '*', item: 'he3', m: 1.9 }] };
  } },
  { kind: 'strike', w: 0.5, make() {
      const l = pick(openMarkets().filter(x => x.id !== 'luna' && x.id !== 'tierra'));
      return l && { icon: '✊', title: `Strike at ${l.station}`, text: `Dockworkers on ${l.n} walk out. Market closed; fuel and repairs only.`,
        dur: randi(5, 10), locs: [l.id], closed: [l.id] };
  } },
  { kind: 'storm', w: 0.5, make() {
      return { icon: '☀️', title: 'Solar storm', text: 'A coronal mass ejection sweeps the inner system. Travel near the Sun damages your hull.',
        dur: randi(6, 12), locs: ['mercurio', 'venus', 'tierra', 'luna'].filter(locOpen), storm: ['mercurio', 'venus', 'tierra', 'luna'] };
  } },
  { kind: 'festival', w: 0.6, make() {
      const l = pick(openMarkets());
      return l && { icon: '🎉', title: `Festival on ${l.n}`, text: `${l.station} celebrates. Luxuries sell ×1.9 and food ×1.4 there.`,
        dur: randi(8, 14), locs: [l.id], price: [{ loc: l.id, item: 'luxury', m: 1.9 }, { loc: l.id, item: 'food', m: 1.4 }] };
  } },
  // ----- events that ask YOU to decide -----
  { kind: 'election', w: 0.7, choice: 1, make() {
      const c = openMarkets().filter(x => x.faction && x.faction !== 'piratas' && !kindActive('policy', x.id));
      if (!c.length) return null; const l = pick(c); const cost = pcost(0.004, 150000);
      return { icon: '🗳️', title: `Election on ${l.n}`, text: `Two parties fight for ${l.station}. Your money could decide it.`, choices: [
        { label: `Back the Industrialists · ${fmt(cost)}`, cost, fn: () => { addEvent({ kind: 'policy', mine: 1, icon: '🏭', title: `Industrialists rule ${l.n}`, text: 'Machinery and weapons half price there; metals sell ×1.3.', dur: 30, locs: [l.id],
            price: [{ loc: l.id, item: 'machinery', m: 0.5 }, { loc: l.id, item: 'arms', m: 0.5 }, ...['iron', 'nickel', 'titanium', 'platinum'].map(i => ({ loc: l.id, item: i, m: 1.3 }))] }); repChange(l.faction, 10); } },
        { label: `Back the Greens · ${fmt(cost)}`, cost, fn: () => { addEvent({ kind: 'policy', mine: 1, icon: '🌱', title: `Greens rule ${l.n}`, text: 'Ice, food and Helium-3 sell ×1.8 there.', dur: 30, locs: [l.id],
            price: [{ loc: l.id, item: 'ice', m: 1.8 }, { loc: l.id, item: 'food', m: 1.8 }, { loc: l.id, item: 'he3', m: 1.8 }] }); repChange(l.faction, 10); } },
        { label: 'Stay out of it', cost: 0, fn: () => {} },
      ] };
  } },
  { kind: 'independence', w: 0.5, choice: 1, make() {
      const c = ['ceres', 'europa', 'titan'].filter(id => cityOpen(id) && !kindActive('free', id) && !kindActive('order', id));
      if (!c.length) return null; const l = LOC[pick(c)]; const cost = pcost(0.006, 250000);
      return { icon: '🏴', title: `${l.n} wants independence`, text: `Separatists on ${l.n} are rising against the Earth Union's influence.`, choices: [
        { label: `Fund the separatists · ${fmt(cost)}`, cost, fn: () => { repChange(l.faction, 20); repChange('tierra', -15); addEvent({ kind: 'free', mine: 1, icon: '🎆', title: `Free ${l.n}`, text: 'The new government rewards its friends: ore sells ×1.5 there.', dur: 40, locs: [l.id], price: ORES.map(i => ({ loc: l.id, item: i, m: 1.5 })) }); } },
        { label: `Fund the government · ${fmt(cost)}`, cost, fn: () => { repChange('tierra', 20); repChange(l.faction, -10); addEvent({ kind: 'order', mine: 1, icon: '🛡️', title: `Order on ${l.n}`, text: 'Patrols everywhere: no pirates there for 40 days.', dur: 40, locs: [l.id], danger: [{ loc: l.id, add: -1 }] }); } },
        { label: 'Ignore it', cost: 0, fn: () => {} },
      ] };
  } },
  { kind: 'buyout', w: 0.5, choice: 1, make() {
      const ids = Object.keys(S.outposts).filter(id => outpostLvCost(id) != null);
      if (!ids.length) return null; const id = pick(ids); const cost = Math.round(outpostLvCost(id) * 0.5);
      return { icon: '💼', title: `Rival miner bankrupt at ${LOC[id].field.n}`, text: `Their equipment is for sale at half price: it would upgrade your outpost there one level (×2 output).`, choices: [
        { label: `Buy it · ${fmt(cost)}`, cost, fn: () => { const o = S.outposts[id]; if (!o || o.lv >= OUTPOST.maxLv) { S.credits += cost; return; } o.lv++; addNews('💼', `You bought out a rival at ${LOC[id].field.n}`, '#6dffb0'); } },
        { label: 'Pass', cost: 0, fn: () => {} },
      ] };
  } },
  { kind: 'loan', w: 0.5, choice: 1, make() {
      const c = openMarkets().filter(x => x.faction && x.faction !== 'piratas');
      if (!c.length) return null; const l = pick(c); const amt = pcost(0.01, 300000);
      return { icon: '🏦', title: `${l.station} asks for a bailout`, text: `They need ${fmt(amt)} cr now and promise to repay ×1.6 in 20 days. Colonies usually keep their word…`, choices: [
        { label: `Lend ${fmt(amt)}`, cost: amt, fn: () => { (S.loans = S.loans || []).push({ loc: l.id, due: S.day + 20, amt: Math.round(amt * 1.6) }); repChange(l.faction, 8); } },
        { label: 'Refuse', cost: 0, fn: () => repChange(l.faction, -3) },
      ] };
  } },
];
let pendingChoices = [];
function spawnEvent() {
  for (let tries = 0; tries < 6; tries++) {
    const pool = EVENT_GEN.filter(g => !g.choice || has(U.TRADE));
    const total = pool.reduce((a, e) => a + e.w, 0);
    let r = Math.random() * total, gen = pool[0];
    for (const e of pool) { r -= e.w; if (r <= 0) { gen = e; break; } }
    const ev = gen.make();
    if (!ev) continue;
    ev.kind = gen.kind;
    if (ev.choices) { pendingChoices.push(ev); addNews(ev.icon, `<b>${ev.title}</b> — ${ev.text}`, '#ffc857'); return; }
    if ((ev.locs || []).some(id => kindActive(ev.kind, id)) || (!ev.locs.length && kindActive(ev.kind))) continue;
    addEvent(ev);
    addNews(ev.icon, `<b>${ev.title}</b> — ${ev.text}`, '#ffc857');
    showEventBanner(ev);
    if (ev.relief) {
      const l = LOC[ev.relief.loc];
      const qty = Math.max(6, Math.round(ship.cargoMax * rand(0.3, 0.6)));
      (S.contracts[l.id] = S.contracts[l.id] || []).unshift({ type: 'deliver', id: uid(), from: l.id, to: l.id, item: ev.relief.item, qty,
        reward: Math.round(qty * itemBase(ev.relief.item) * 3.2 / 10) * 10, rep: 15, days: ev.dur, faction: l.faction, urgent: 1 });
    }
    return;
  }
}
function makeWar(a, b, dur) {
  const locs = [...FACTIONS[a].locs, ...FACTIONS[b].locs].filter(id => locOpen(id) && !LOC[id].nuked);
  return { kind: 'war', icon: '⚔️', title: `War: ${FACTIONS[a].n} vs ${FACTIONS[b].n}`,
    text: 'Weapons sell ×2.3, medicine ×1.5 and fuel costs more in their markets. Routes get dangerous. Back a side and sell your ore there to push the front.',
    dur, war: [a, b], locs, front: 0, push: 0,
    price: locs.flatMap(l => [{ loc: l, item: 'arms', m: 2.3 }, { loc: l, item: 'meds', m: 1.5 }, { loc: l, item: 'machinery', m: 1.3 }]),
    danger: locs.map(l => ({ loc: l, add: 0.22 })), fuelPrice: 1.3 };
}
function onEventEnd(e) {
  if (e.war && !e.resolved) {
    const f = e.front || 0;
    endWar(e, Math.abs(f) >= WAR.decisive ? (f > 0 ? e.war[0] : e.war[1]) : null);
  }
}

// ---------- the war front ----------
// e.front runs from −100 (e.war[1] wins) to +100 (e.war[0] wins). It drifts each
// day with each side's strength; you push it by selling ore/supplies to the side
// you back, funding offensives and beating raiders in their space.
const WAR = { decisive: 25, minPush: 15, maxStars: 3, starBonus: 0.15 };
const SPOILS = {
  rights: { icon: '⛏', n: 'Mining rights', d: '+10% ore from every rock, everywhere' },
  drones: { icon: '🤖', n: 'Drone contract', d: 'Drones cost 12% less at every outpost' },
  fuel:   { icon: '⛽', n: 'Fuel treaty', d: 'Fuel is 15% cheaper at every station' },
};
const warSign = (e, f) => e.war[0] === f ? 1 : -1;
const backedWar = () => S.events.find(e => e.war && e.backed && !e.resolved);
function facStrength(f) { return FACTIONS[f].locs.filter(id => !LOC[id].nuked).length; }
// value of "one good haul" right now, so pushes stay meaningful all game
const haulRef = () => 40 * Math.pow(Math.max(1000, S.stats.earned), 0.72);
function warPush(e, amt, why) {
  if (!e || !e.backed || e.resolved || amt <= 0) return 0;
  amt = Math.min(amt, 100 - warSign(e, e.backed) * (e.front || 0)); if (amt <= 0) return 0;
  e.front = clamp((e.front || 0) + warSign(e, e.backed) * amt, -100, 100);
  e.push = (e.push || 0) + amt;
  if (why) toast(`Front +${Math.round(amt)}% for ${FACTIONS[e.backed].n} (${why})`, 'good');
  if (Math.abs(e.front) >= 100) endWar(e, e.backed);
  if (typeof updateWarBar === 'function') updateWarBar();
  return amt;
}
// how far a sale of this value pushes the front (0 if it doesn't count)
function salePushAmt(locId, item, value) {
  const e = backedWar(); if (!e || LOC[locId].faction !== e.backed) return 0;
  const k = ITEMS[item].ore ? 15 : item === 'arms' ? 30 : 20;
  return Math.min(30, value / haulRef() * k);
}
function warSalePush(locId, item, value) {
  const a = salePushAmt(locId, item, value);
  if (a >= 0.5) warPush(backedWar(), a, `${ITEMS[item].n} delivered`);
}
function warDay(e) {
  if (e.resolved) return;
  const [a, b] = e.war;
  e.front = clamp((e.front || 0) + (facStrength(a) - facStrength(b)) * 0.6 + rand(-4, 4), -100, 100);
  if (Math.abs(e.front) >= 100) endWar(e, e.front > 0 ? a : b);
}
function warBarHTML(e, big) {
  const [a, b] = e.war, f = e.front || 0, pct = (100 + f) / 2;
  const you = e.backed ? `<small>You back <b style="color:${FACTIONS[e.backed].c}">${FACTIONS[e.backed].n}</b> · your push +${Math.round(e.push || 0)}%</small>` : '<small>Back a side at one of their stations to take part</small>';
  return `<div class="warbar ${big ? 'big' : ''}"><div class="wb-names"><b style="color:${FACTIONS[a].c}">${FACTIONS[a].n}</b><span>⚔ ${e.resolved ? 'final' : Math.max(0, e.end - S.day) + 'd left'}</span><b style="color:${FACTIONS[b].c}">${FACTIONS[b].n}</b></div>
    <div class="wb-track"><i style="width:${pct}%;background:${FACTIONS[a].c}"></i><i style="width:${100 - pct}%;background:${FACTIONS[b].c}"></i><em style="left:${pct}%"></em><span class="wb-mid"></span></div>${you}</div>`;
}
function endWar(e, winner) {
  if (e.resolved) return;
  e.resolved = 1;
  S.events = S.events.filter(x => x !== e);
  const names = e.war.map(f => FACTIONS[f].n).join(' vs ');
  if (winner) { addNews('🏆', `<b>${FACTIONS[winner].n}</b> won the war (${names})`, FACTIONS[winner].c); repChange(winner, 3, true); }
  else addNews('🕊️', `Stalemate: ${names} sign a truce`, '#8fa3c7');
  if (!e.backed || typeof pendingChoices === 'undefined') return;
  const f = e.backed, bar = warBarHTML(e, true);
  if (winner === f && e.push >= WAR.minPush) {
    S.allies = S.allies || {}; S.spoils = S.spoils || {};
    const stars = S.allies[f] = Math.min(WAR.maxStars, (S.allies[f] || 0) + 1);
    repChange(f, 15, true);
    const owned = S.spoils[f] = S.spoils[f] || [];
    const opts = Object.keys(SPOILS).filter(k => !owned.includes(k));
    const starTxt = `<div class="ally-stars">${'★'.repeat(stars)}${'☆'.repeat(WAR.maxStars - stars)}</div><p><b>${FACTIONS[f].n}</b> is now your ally: <b>ore sells +${Math.round(stars * WAR.starBonus * 100)}%</b> at all their stations, forever.</p>`;
    if (opts.length) pendingChoices.push({ icon: '🏆', title: `${FACTIONS[f].n} wins!`, html: bar + starTxt + '<p>Choose your spoils of war (permanent):</p>',
      choices: opts.map(k => ({ label: `${SPOILS[k].n} — ${SPOILS[k].d}`, cost: 0, fn: () => { owned.push(k); addNews(SPOILS[k].icon, `Spoils of war: ${SPOILS[k].n} from ${FACTIONS[f].n}`, '#ffd24a'); } })) });
    else { const prize = Math.round(haulRef() * 3); earn(prize); pendingChoices.push({ icon: '🏆', title: `${FACTIONS[f].n} wins!`, html: bar + starTxt + `<p>They already gave you everything they have — a war bonus of <b class="cr">${fmt(prize)} cr</b> instead.</p>`, choices: [{ label: 'Collect', cost: 0, fn: () => {} }] }); }
  } else if (winner === f) {
    repChange(f, 8, true);
    pendingChoices.push({ icon: '🏆', title: `${FACTIONS[f].n} wins`, html: bar + `<p>They won, but you barely helped (push +${Math.round(e.push || 0)}%, needed +${WAR.minPush}%). No alliance this time.</p>`, choices: [{ label: 'OK', cost: 0, fn: () => {} }] });
  } else {
    repChange(f, -8, true);
    pendingChoices.push({ icon: winner ? '💥' : '🕊️', title: winner ? `${FACTIONS[f].n} lost the war` : 'The war ended in a stalemate', html: bar + `<p>${winner ? 'Your side was beaten.' : 'Neither side broke through.'} No spoils this time — but your ore buys you another chance in the next war.</p>`, choices: [{ label: 'OK', cost: 0, fn: () => {} }] });
  }
}
function politicsDay() {
  for (const e of [...S.events]) if (e.war) warDay(e);
  if (!S.loans) return;
  for (const ln of [...S.loans]) if (S.day >= ln.due) {
    S.loans = S.loans.filter(x => x !== ln);
    const l = LOC[ln.loc];
    if (l.nuked || Math.random() < 0.1) { addNews('🏦', `${l.n} defaulted on your loan.`, '#ff6b7d'); toast(`${l.n} defaulted on your loan`, 'bad'); }
    else { earn(ln.amt); addNews('🏦', `${l.station} repaid your loan: +${fmt(ln.amt)} cr`, '#6dffb0'); toast(`Loan repaid: +${fmt(ln.amt)} cr`, 'good'); }
  }
}

// ---------- player powers (one per location, with cooldowns) ----------
const POWERS = {
  works:  { icon: '🏛️', n: 'Fund public works', stage: U.TRADE, cd: 15, cost: () => pcost(0.003, 100000), d: '+12 reputation with this planet' },
  boom:   { icon: '🏗️', n: 'Fund a boom', stage: U.TRADE, cd: 45, cost: () => pcost(0.006, 300000), d: 'Every ore sells ×1.9 here for 20 days' },
  purge:  { icon: '🛡️', n: 'Hire mercenaries', stage: U.TRADE, cd: 30, cost: () => pcost(0.005, 250000), d: 'No pirates here for 30 days' },
  end:    { icon: '🕊️', n: 'End this crisis', stage: U.TRADE, cd: 0, cost: () => pcost(0.004, 200000) },
  incite: { icon: '🔥', n: 'Incite a war', stage: U.SATURN, cd: 60, cost: () => pcost(0.02, 5e7), d: 'Start a war against another faction. Wars pay: weapons ×2.3. Risky if discovered.' },
  back:   { icon: '🎖️', n: 'Back this side', stage: U.TRADE, cd: 0, cost: () => pcost(0.004, 150000), d: 'Their stations pay +30% for metals during the war and every sale pushes the front. Win → a permanent ally.' },
  offensive: { icon: '🚀', n: 'Fund an offensive', stage: U.TRADE, cd: 8, cost: () => pcost(0.008, 300000), d: 'Push the front +20% right now' },
  peace:  { icon: '🤝', n: 'Broker peace', stage: U.SATURN, cd: 0, cost: () => pcost(0.015, 4e7), d: 'End the war: +20 rep with both sides, +3 influence.' },
  nuke:   { icon: '💥', n: 'Fire the Nova Cannon', stage: U.FRONTIER, cd: 0, cost: () => pcost(0.05, 1e12), d: 'Destroy this planet.' },
};
const NUKABLE = ['mercurio', 'venus', 'marte', 'ceres', 'europa', 'titan', 'pluton'];
function cdLeft(id, kind) { const d = ((S.cd || {})[id] || {})[kind]; return d ? Math.max(0, d - S.day) : 0; }
function setCd(id, kind, days) { S.cd = S.cd || {}; (S.cd[id] = S.cd[id] || {})[kind] = S.day + days; }
function warOf(f) { return S.events.find(e => e.war && e.war.includes(f)); }
// Which powers can be used at a location right now? -> [{ kind, arg, label, cost, ok, why }]
function powersAt(id) {
  const l = LOC[id], out = [];
  if (!has(U.TRADE) || !locOpen(id) || l.nuked) return out;
  const add = (kind, extra) => {
    const P = POWERS[kind]; if (!has(P.stage)) return;
    const cost = P.cost(), cd = cdLeft(id, kind);
    const o = { kind, arg: id, icon: P.icon, label: P.n, d: P.d, cost, ...extra };
    o.ok = !cd && S.credits >= cost && !o.why;
    if (cd && !o.why) o.why = `ready in ${cd} day${cd > 1 ? 's' : ''}`;
    out.push(o);
  };
  const city = l.market && !l.depot;
  if (city && l.faction && l.faction !== 'piratas') add('works');
  if (city) add('boom', kindActive('boom', id) ? { why: 'a boom is already running' } : {});
  if (has(U.BELT) && (l.danger || 0) >= 0.1) add('purge', S.events.some(e => e.mine && e.kind === 'purge' && e.locs.includes(id)) ? { why: 'already secured' } : {});
  if (city && l.faction && l.faction !== 'piratas' && has(U.TRADE)) {
    const w = warOf(l.faction);
    if (!w && has(U.SATURN)) {
      for (const f of ['tierra', 'marte', 'cinturon', 'exterior']) if (f !== l.faction && factionAlive(f) && FACTIONS[f].locs.some(locOpen))
        add('incite', { arg: id + '|' + f, label: `Incite war vs ${FACTIONS[f].n}`, why: S.events.some(e => e.war) ? 'another war is running' : null });
    } else if (w) {
      const other = backedWar();
      if (!w.backed) add('back', other && other !== w ? { why: 'you already back a side in another war' } : {});
      else if (w.backed === l.faction) add('offensive');
      if (has(U.SATURN)) add('peace');
    }
  }
  if (has(U.FRONTIER) && built('nova') && NUKABLE.includes(id)) add('nuke');
  return out;
}
function usePower(kind, arg) {
  const P = POWERS[kind]; const c = P.cost();
  if (S.credits < c) return false;
  let id = arg;
  if (kind === 'end') {
    const e = S.events.find(x => x.uid === arg); if (!e || e.mine) return false;
    S.credits -= c;
    S.events = S.events.filter(x => x !== e); e.resolved = 1;
    const facs = new Set((e.locs || []).map(l => LOC[l].faction).filter(f => f && f !== 'piratas'));
    for (const f of facs) repChange(f, 10, true);
    addNews('🕊️', `Your money ended it: <b>${e.title}</b>. The system owes you one.`, '#6dffb0');
    save(); return true;
  }
  if (kind === 'incite') {
    const [loc, f2] = arg.split('|'); id = loc;
    if (cdLeft(id, kind) || S.events.some(e => e.war)) return false;
    const f1 = LOC[loc].faction;
    S.credits -= c;
    const w = makeWar(f1, f2, randi(30, 45)); w.kind = 'war'; w.incited = 1; addEvent(w);
    showEventBanner(w);
    if (Math.random() < 0.25) { repChange(f1, -30); repChange(f2, -30); addNews('🕵️', `Leaked: <b>you</b> started the war between ${FACTIONS[f1].n} and ${FACTIONS[f2].n}!`, '#ff6b7d'); toast('Your plot was discovered! −30 reputation with both sides', 'bad'); }
    else addNews('⚔️', `War breaks out between ${FACTIONS[f1].n} and ${FACTIONS[f2].n}. Nobody suspects you.`, '#ffc857');
    setCd(id, kind, P.cd); save(); return true;
  }
  const l = LOC[id];
  if (cdLeft(id, kind)) return false;
  const opt = powersAt(id).find(o => o.kind === kind);
  if (!opt || opt.why && !opt.why.startsWith('ready')) return false;
  S.credits -= c;
  if (kind === 'works') { repChange(l.faction, 12); addNews('🏛️', `You funded public works on ${l.n}`, '#6dffb0'); }
  else if (kind === 'boom') {
    addEvent({ kind: 'boom', mine: 1, icon: '🏗️', title: `Your boom on ${l.n}`, text: `You funded a building frenzy at ${l.station}. Every ore sells ×1.9 there.`,
      dur: 20, locs: [id], price: ORES.map(i => ({ loc: id, item: i, m: 1.9 })) });
    if (l.faction) repChange(l.faction, 6, true);
    addNews('🏗️', `You funded a construction boom on ${l.n}`, '#ffd24a');
  } else if (kind === 'purge') {
    S.events = S.events.filter(e => !(e.kind === 'pirates' || e.kind === 'warlord') || !e.locs.includes(id));
    addEvent({ kind: 'purge', mine: 1, icon: '🛡️', title: `${l.n} secured`, text: `Your mercenaries hunt every pirate near ${l.n}. No ambushes there for 30 days.`,
      dur: 30, locs: [id], danger: [{ loc: id, add: -1 }] });
    repChange('piratas', -5, true);
    addNews('🛡️', `Mercenaries cleared the pirates near ${l.n}`, '#6dffb0');
  } else if (kind === 'back') {
    const w = warOf(l.faction); if (!w || w.backed) { S.credits += c; return false; }
    if (backedWar()) { S.credits += c; return false; }
    w.backed = l.faction; w.push = 0; w.front = w.front || 0;
    const enemy = w.war.find(f => f !== l.faction);
    // their war industry buys metals: +30% at the stations of the side you back
    for (const id of FACTIONS[l.faction].locs) if (!LOC[id].nuked) for (const it of ['iron', 'titanium', 'nickel', 'platinum', 'iridium']) w.price.push({ loc: id, item: it, m: 1.3 });
    repChange(l.faction, 15); repChange(enemy, -15);
    addNews('🎖️', `You back ${FACTIONS[l.faction].n} in the war`, '#ffd24a');
  } else if (kind === 'offensive') {
    const w = warOf(l.faction); if (!w || w.backed !== l.faction) { S.credits += c; return false; }
    warPush(w, 20, 'offensive');
    for (const x of FACTIONS[l.faction].locs) setCd(x, 'offensive', POWERS.offensive.cd);
    addNews('🚀', `You funded an offensive for ${FACTIONS[l.faction].n}`, '#ffd24a');
  } else if (kind === 'peace') {
    const w = warOf(l.faction); if (!w) { S.credits += c; return false; }
    S.events = S.events.filter(e => e !== w); w.resolved = 1;
    for (const f of w.war) repChange(f, 20, true);
    S.peace = Math.min(5, (S.peace || 0) + 1);
    addNews('🤝', `You brokered peace between ${w.war.map(f => FACTIONS[f].n).join(' and ')}. The system celebrates your name.`, '#6dffb0');
  } else if (kind === 'nuke') {
    destroyPlanet(id);
  }
  if (P.cd) setCd(id, kind, P.cd);
  save();
  return true;
}

// ---------- the Nova Cannon: destroying planets ----------
const LOC_BASE = {};
for (const l of LOCS) LOC_BASE[l.id] = { station: l.station, market: l.market, faction: l.faction, field: l.field, depot: l.depot, desc: l.desc, danger: l.danger, black: l.black, tex: l.tex, col: l.col };
function resetLocs() {
  for (const l of LOCS) { Object.assign(l, LOC_BASE[l.id]); delete l.nuked; if (!LOC_BASE[l.id].field) delete l.field; if (!LOC_BASE[l.id].station) delete l.station; }
  FIELDS.splice(0, FIELDS.length, ...NODES.filter(l => l.field));
}
function wreckLoc(id) {
  const l = LOC[id];
  l.nuked = 1;
  l.station = `${l.n} Salvage Depot`; l.depot = 1; l.market = { ...DEPOT };
  delete l.faction; delete l.black;
  l.field = { n: `${l.n} Debris`, z: 5, ores: { exotic: 3, iridium: 3, platinum: 2 }, count: 36 };
  l.desc = `What's left of ${l.n}. A glowing debris field of shattered crust — the richest mining in the system.`;
  l.danger = 0.35; l.col = ['#ff8a4a', '#3a1208'];
  FIELDS.splice(0, FIELDS.length, ...NODES.filter(x => x.field));
}
function applyNukes() { resetLocs(); for (const id of S.nuked || []) wreckLoc(id); }
function destroyPlanet(id) {
  const l = LOC[id], name = l.n, fac = l.faction;
  S.nuked = S.nuked || []; S.nuked.push(id);
  delete S.invest[id]; delete S.contracts[id]; delete S.outposts[id];
  S.active = S.active.filter(c => c.to !== id && c.from !== id);
  S.events = S.events.filter(e => !(e.locs || []).includes(id) || e.war);
  S.freighters = (S.freighters || []).filter(f => f.from !== id && f.to !== id);
  wreckLoc(id);
  if (fac && !factionAlive(fac)) S.events = S.events.filter(e => !(e.war && e.war.includes(fac)));
  if (fac) repChange(fac, factionAlive(fac) ? -60 : -100, true);
  for (const f in FACTIONS) if (f !== fac && f !== 'piratas') repChange(f, -20, true);
  repChange('piratas', 25, true);
  addNews('💥', `<b>${name} has been destroyed.</b> The Solar System trembles before you.`, '#ff4d6d');
  if (typeof MapScene !== 'undefined') MapScene.nukeFx = { id, t: 0 };
  sfx('boom'); setTimeout(() => sfx('boom'), 250); setTimeout(() => sfx('lose'), 600);
}

// ---------- freighters: automated trade routes ----------
const FREIGHT = {
  max: 10, perRoute: 3,
  cap: () => Math.round(8 * Math.pow(1.6, Math.max(0, S.unlock - 5))),
  cost: () => Math.round(1e6 * Math.pow(3, Math.max(0, S.unlock - 5)) * Math.pow(1.35, (S.freighters || []).length)),
};
function routeCycle(from, to) { const days = Math.max(1, Math.round(locDist(from, to, S.day) / 22)); return 2 * (3 + days * 1.2); }
function tradeMult() { let inv = 0; for (const id in S.invest) inv += S.invest[id]; return (1 + INVEST.bonus * inv) * (built('dyson') ? 5 : 1); }
function freighterIncome(f) {
  if (!cityOpen(f.from) || !cityOpen(f.to) || marketClosed(f.from) || marketClosed(f.to)) return 0;
  const bp = buyPrice(f.from, f.g), sp = sellPrice(f.to, f.g);
  if (!bp || !sp) return 0;
  return Math.max(0, sp - bp) * FREIGHT.cap() / routeCycle(f.from, f.to) * tradeMult();
}
function freightIncome() { let v = 0; for (const f of S.freighters || []) v += freighterIncome(f); return v; }
// best trades starting at a station (used by the Trade tab and freighters).
// Only counts what the destination still wants: a saturated market isn't offered.
function tradeRoutes(id, all) {
  const out = [];
  if (!cityOpen(id)) return out;
  const D = demandCap();
  for (const g of GOODS) {
    const bp = buyPrice(id, g); if (!bp) continue;
    let best = null;
    for (const C of NODES) if (cityOpen(C.id) && C.id !== id && C.market[g] != null && !marketClosed(C.id)) {
      const sp = sellPrice(C.id, g); if (!sp) continue;
      const d = demandOf(C.id, g), f0 = demandFactor(C.id, g);
      const units = Math.min(stockLeft(id, g), ship.cargoMax, Math.floor(d * D));
      if (units < 1 || d < 0.2) continue;
      const f1 = 0.15 + 0.85 * (d - units / D), avg = Math.round(sp * (f0 + f1) / 2 / f0);
      const profit = (avg - bp) * units;
      if (avg > bp * 1.15 && (!best || profit > best.profit)) best = { to: C.id, sp, avg, units, profit, d };
    }
    if (best) out.push({ g, from: id, bp, ...best });
  }
  return out.sort((a, b) => b.profit - a.profit);
}
const routeCount = (from, to, g) => (S.freighters || []).filter(f => f.from === from && f.to === to && f.g === g).length;
function hireFreighter(from, to, g) {
  S.freighters = S.freighters || [];
  const c = FREIGHT.cost();
  if (S.freighters.length >= FREIGHT.max || S.credits < c || routeCount(from, to, g) >= FREIGHT.perRoute) return false;
  S.credits -= c; S.freighters.push({ from, to, g, t0: Math.random() });
  addNews('🚚', `Freighter hired: ${ITEMS[g].n} ${LOC[from].n} → ${LOC[to].n}`, '#6dffb0');
  save();
  return true;
}
