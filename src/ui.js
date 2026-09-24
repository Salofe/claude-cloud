'use strict';
// ============ INTERFACE (DOM) ============
const $ = id => document.getElementById(id);
const isBlocking = () => !$('modal').classList.contains('hidden') || !$('sheet').classList.contains('hidden');
let dockTab = 'upg', lastDock = null, shownCredits = 0;

function toast(msg, cls) {
  const el = document.createElement('div');
  el.className = 'toast ' + (cls || '');
  el.innerHTML = msg;
  $('toasts').appendChild(el);
  setTimeout(() => el.classList.add('out'), 2600);
  setTimeout(() => el.remove(), 3100);
}
function coach(msg) {
  const el = $('coach');
  if (!msg) { el.classList.remove('show'); return; }
  if (el._m !== msg) { el.innerHTML = msg; el._m = msg; }
  el.classList.add('show');
}

function showModal(o) {
  const m = $('modal');
  m.innerHTML = `<div class="mbox ${o.danger ? 'danger' : ''} ${o.cls || ''}">
    ${o.icon ? `<div class="micon">${o.icon}</div>` : ''}
    <h2>${o.title}</h2><div class="mbody">${o.html || ''}</div>
    <div class="mbtns"></div></div>`;
  const bx = m.querySelector('.mbtns');
  o.buttons.forEach(b => {
    const el = document.createElement('button');
    el.className = 'btn ' + (b.cls || '');
    el.innerHTML = b.label; el.disabled = !!b.disabled;
    el.onclick = () => { sfx('click'); closeModal(); b.fn && b.fn(); updateHUD(); };
    bx.appendChild(el);
  });
  m.classList.remove('hidden');
  if (o.after) o.after(m);
}
function closeModal() { $('modal').classList.add('hidden'); }

function showEventBanner(ev) {
  const b = $('eventBanner');
  b.innerHTML = `<span class="eicon">${ev.icon}</span><div><small>SYSTEM NEWS · DAY ${S.day}</small><b>${ev.title}</b><p>${ev.text}</p></div>`;
  b.classList.add('show');
  sfx('event');
  clearTimeout(b._t); b._t = setTimeout(() => b.classList.remove('show'), 6500);
}
function updateTicker() {
  const el = $('tickerIn'); if (!el || !S) return;
  el.innerHTML = S.news.slice(0, 8).map(n => `<span><i>DAY ${n.day}</i> ${n.icon} ${n.html.replace(/<[^>]+>/g, '')}</span>`).join('<span class="sep">◆</span>');
}

// ---------- HUD ----------
function hudTick(dt) {
  if (!S) return;
  const d = S.credits - shownCredits;
  if (Math.abs(d) < 1) shownCredits = S.credits;
  else shownCredits += d * Math.min(1, dt * 6) + Math.sign(d) * Math.min(Math.abs(d), dt * 40);
  $('hCr').textContent = fmt(shownCredits);
  $('hCr').parentElement.classList.toggle('up', d > 1);
}
function updateHUD() {
  if (!S) return;
  for (const el of document.querySelectorAll('[data-need]')) el.classList.toggle('locked', S.unlock < +el.dataset.need);
  $('hDay').textContent = S.day;
  $('hFuel').style.width = (S.fuel / ship.fuelMax * 100) + '%';
  $('hFuelT').textContent = `${Math.floor(S.fuel)}/${ship.fuelMax}`;
  $('hHull').style.width = (S.hull / ship.hpMax * 100) + '%';
  $('hHullT').textContent = `${Math.ceil(S.hull)}/${ship.hpMax}`;
  $('hCargo').style.width = (cargoUsed() / ship.cargoMax * 100) + '%';
  $('hCargoT').textContent = `${cargoUsed()}/${ship.cargoMax}`;
  const inf = influence();
  $('hInfl').textContent = inf;
  $('hRank').textContent = rankName(inf);
  $('hFuel').parentElement.classList.toggle('low', S.fuel < ship.fuelMax * 0.2);
  $('hHull').parentElement.classList.toggle('low', S.hull < ship.hpMax * 0.3);
  $('hCargo').parentElement.classList.toggle('full', cargoFree() <= 0);
  const nu = nextUnlock();
  const o = $('objective');
  if (nu) {
    const prev = UNLOCKS[S.unlock].at, pct = clamp((S.stats.earned - prev) / (nu.at - prev), 0, 1);
    o.innerHTML = `<small>NEXT UNLOCK</small><b>${nu.icon} ${nu.title}</b><div class="meter gold"><i style="width:${pct * 100}%"></i></div><span>${fmt(S.stats.earned)} / ${fmt(nu.at)} cr earned</span>`;
  } else if (!S.won) {
    o.innerHTML = `<small>FINAL GOAL</small><b>👑 Reach 100 influence</b><div class="meter gold"><i style="width:${Math.min(100, inf)}%"></i></div><span>Influence ${inf}/100 · invest in stations</span>`;
  } else o.innerHTML = `<small>SOLAR SOVEREIGN</small><b>👑 You rule the system</b><span>Keep growing your empire.</span>`;
  if (!S.won && has(U.SATURN) && inf >= 100 && !isBlocking()) victory();
  if (pendingUnlocks.length && $('modal').classList.contains('hidden') && scene !== BattleScene && !(MapScene.travel)) showUnlock(pendingUnlocks.shift());
}
function showUnlock(i) {
  const u = UNLOCKS[i];
  sfx('win');
  const upg = u.upg.length ? `<div class="unl-upg">${u.upg.map(k => `<span class="chip ore">${UPG[k].icon} ${UPG[k].n}</span>`).join('')}</div><small>New upgrades available at any station.</small>` : '';
  showModal({ icon: u.icon, title: u.title, cls: 'unlock', html: `<div class="unl-tag">NEW!</div><p>${u.text}</p>${upg}`,
    buttons: [{ label: 'Awesome!', cls: 'primary', fn: () => { if (!$('sheet').classList.contains('hidden') && LOC[S.loc].station) renderDock(); updateHUD(); } }] });
  const el = $('objective'); el.classList.remove('flash'); void el.offsetWidth; el.classList.add('flash');
}
function victory() {
  S.won = true; save();
  sfx('win');
  showModal({ icon: '👑', title: 'You rule the Solar System!', html: `In <b>${S.day} days</b> you went from chipping rocks on the Moon to the most powerful force in the system.<br><br>
    Ore mined: <b>${fmt(S.stats.mined)}</b><br>Total earnings: <b>${fmt(S.stats.earned)} cr</b><br>Battles won: <b>${S.stats.won}</b><br>Contracts: <b>${S.stats.contracts}</b><br><br>Keep playing and grow your empire.`,
    buttons: [{ label: 'Keep playing', cls: 'primary', fn: () => {} }] });
}

// ---------- map panel ----------
function selectLoc(id) {
  MapScene.sel = id;
  const l = LOC[id];
  const p = $('locPanel');
  const here = id === S.loc;
  let html = `<div class="lp-head"><div><h3>${l.n}</h3><small>${[l.station, l.field && l.field.n].filter(Boolean).join(' · ')}</small></div><button class="x" onclick="hideLocPanel()">✕</button></div>`;
  if (!locOpen(id)) {
    const u = UNLOCKS[l.tier];
    html += `<div class="locked-box">🔒 Unlocks at <b>${fmt(u.at)} cr</b> lifetime earnings<br><small>${u.title}</small></div><p class="desc">${l.desc}</p>`;
    p.innerHTML = html; p.classList.remove('hidden'); return;
  }
  html += `<p class="desc">${l.desc}</p><div class="chips">`;
  if (l.field) html += '<span class="chip ore">⛏ Mining</span>';
  if (l.station) html += `<span class="chip" style="--c:${l.faction ? FACTIONS[l.faction].c : '#fff'}">🛰 ${l.station}</span>`;
  const dg = locDanger(id);
  if (has(U.BELT)) html += dg < 0.1 ? '<span class="chip good">Safe</span>' : dg < 0.3 ? '<span class="chip warn">Some pirates</span>' : '<span class="chip bad">☠ Dangerous</span>';
  html += '</div>';
  const evs = S.events.filter(e => e.locs && e.locs.includes(id));
  if (evs.length) html += `<div class="evs">${evs.map(e => `<div class="ev">${e.icon} <b>${e.title}</b> <small>(${e.end - S.day}d)</small></div>`).join('')}</div>`;
  if (l.field) {
    const ores = Object.keys(l.field.ores).sort((a, b) => l.field.ores[b] - l.field.ores[a]);
    html += `<div class="ores">${ores.map(o => `<span class="ore" style="--c:${ITEMS[o].c}">${ITEMS[o].n}</span>`).join('')}</div>`;
    if (l.field.hazard === 'heat') html += `<div class="warnline">🔥 Extreme heat — damages your hull unless you have shields.</div>`;
  }
  if (l.market && !here && cargoUsed()) {
    const v = oreValueAt(id);
    if (v) html += `<div class="valline">Your ore sells for <b class="cr">${fmt(v)} cr</b> here${LOC[S.loc].market ? ` <small>(${fmt(oreValueAt(S.loc))} at ${LOC[S.loc].n})</small>` : ''}</div>`;
  }
  if (l.market && has(U.TRADE) && !here) {
    const hot = Object.keys(l.market).map(k => ({ k, m: basePrice(id, k) / ITEMS[k].b })).filter(x => x.m >= 1.45).sort((a, b) => b.m - a.m).slice(0, 4);
    if (hot.length) html += `<div class="sub">Pays well for</div><div class="ores">${hot.map(x => `<span class="ore" style="--c:${ITEMS[x.k].c}">${ITEMS[x.k].n} <b>×${x.m.toFixed(1)}</b></span>`).join('')}</div>`;
  }
  if (here) {
    html += `<div class="lp-actions">`;
    if (l.station) html += `<button class="btn primary big" onclick="openDock()">🛰 Dock at ${l.station}</button>`;
    if (l.field) html += `<button class="btn ore big" onclick="enterMine()">⛏ Mine ${l.field.n}</button>`;
    if (!l.station) {
      const stations = NODES.filter(x => x.station && locOpen(x.id));
      const reachable = stations.some(x => travelInfo(x.id).fuel <= S.fuel);
      if (!reachable) html += `<button class="btn danger big" onclick="towShip('You ran out of fuel.')">🚨 Call a tug</button>`;
    }
    html += `</div>`;
  } else {
    const info = travelInfo(id);
    const ok = info.fuel <= S.fuel;
    html += `<div class="travel">
      <div><small>Fuel</small><b class="${ok ? '' : 'badt'}">${info.fuel} <small>/ ${Math.floor(S.fuel)}</small></b></div>
      <div><small>Time</small><b>${info.days} day${info.days > 1 ? 's' : ''}</b></div>
      ${has(U.BELT) ? `<div><small>Ambush risk</small><b class="${info.danger > 0.3 ? 'badt' : ''}">${Math.round(info.danger * 100)}%</b></div>` : ''}</div>
      <button class="btn primary big" ${ok ? '' : 'disabled'} onclick="MapScene.startTravel('${id}')">${ok ? '🚀 Fly here' : '⛽ Not enough fuel — upgrade your tank or wait for a closer orbit'}</button>`;
  }
  p.innerHTML = html;
  p.classList.remove('hidden');
}
function hideLocPanel() { $('locPanel').classList.add('hidden'); MapScene.sel = null; }
function enterMine() { sfx('click'); closeSheet(true); setScene(MineScene, S.loc); }

function showMapUI(on) {
  $('mapTools').classList.toggle('hidden', !on);
  if (!on) $('locPanel').classList.add('hidden');
}
function showMineUI(on) {
  document.body.classList.toggle('mining', on);
  $('mineUI').classList.toggle('hidden', !on);
  $('touchUI').classList.toggle('hidden', !on || !isTouch);
  if (!on) { coach(''); $('fullPrompt').classList.add('hidden'); }
  if (on) {
    const l = MineScene.loc;
    $('mineName').textContent = l.field.n;
    $('btnDock').classList.toggle('hidden', !l.station);
    $('btnDock').innerHTML = `🛰 Dock${l.station ? ' & sell' : ''}`;
    $('btnMap').classList.toggle('hidden', !has(U.MAP));
  }
}
function updateMineHUD() {
  const now = performance.now();
  if (updateMineHUD.t && now - updateMineHUD.t < 200) return;
  updateMineHUD.t = now;
  const rows = Object.keys(S.cargo).map(k => `<div class="crow"><i style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}<b>${S.cargo[k]}</b></div>`).join('');
  const val = LOC[S.loc].market ? oreValueAt(S.loc) : 0;
  $('mineCargo').innerHTML = (rows || '<div class="crow dim">Cargo hold empty</div>') + (val ? `<div class="crow val">Worth<b class="cr">${fmt(val)} cr</b></div>` : '');
  $('mineInfo').innerHTML = (ship.shieldMax ? `Shield ${Math.round(MineScene.p.shield)}/${ship.shieldMax}` : '') + (MineScene.loc.field.hazard === 'heat' ? ' <span class="badt">🔥 HEAT</span>' : '');
  const full = cargoFree() <= 0;
  const fp = $('fullPrompt');
  if (full && fp.classList.contains('hidden')) {
    const st = LOC[S.loc].station;
    fp.innerHTML = `<b>CARGO FULL!</b><button class="btn primary big" onclick="MineScene.leave()">${st ? `🛰 Dock & sell <span class="cr2">+${fmt(val)} cr</span>` : '🗺 Open map'}</button>`;
  }
  fp.classList.toggle('hidden', !full);
  $('btnDock').style.visibility = full ? 'hidden' : '';
  if (full) coach('');
  updateHUD();
}
function showBattleUI(on) { document.body.classList.toggle('battle', on); $('battleUI').classList.toggle('hidden', !on); if (on) { $('btnSpeed').textContent = 'Speed ×1'; $('btnRetreat').disabled = false; } }

// ---------- sheet (big panel) ----------
function openSheet(title, html, cls) {
  const s = $('sheet');
  s.className = 'sheet ' + (cls || '');
  s.innerHTML = `<div class="sh-head"><h2>${title}</h2><button class="x" onclick="closeSheet()">✕</button></div><div class="sh-body">${html}</div>`;
  s.classList.remove('hidden');
}
function closeSheet(silent) {
  const s = $('sheet');
  const wasDock = s.classList.contains('dock') && !s.classList.contains('hidden');
  s.classList.add('hidden'); save(); updateHUD();
  if (silent) return;
  if (wasDock && !has(U.MAP) && LOC[S.loc].field) { setScene(MineScene, S.loc); return; }
  if (scene === MapScene && !MapScene.travel) { showMapUI(true); selectLoc(S.loc); }
}

// ---------- DOCK (station) ----------
function openDock() {
  sfx('click');
  if (scene !== MapScene) setScene(MapScene);
  showMapUI(false);
  lastDock = dockAtStation();
  dockTab = 'upg';
  renderDock(true);
  if (lastDock.total > 0) sfx('cash');
}
function renderDock(fresh) {
  const l = LOC[S.loc];
  const tabs = [['upg', '🔧 Upgrades']];
  if (has(U.TRADE)) tabs.push(['trade', '📦 Trade'], ['contracts', '📜 Contracts' + (S.active.some(canDeliver) ? ' <i class="dot"></i>' : '')]);
  if (has(U.SATURN)) tabs.push(['invest', '🏛 Invest']);
  let receipt = '';
  const r = lastDock;
  if (fresh && r && (r.sold.length || r.fuel || r.repair)) {
    receipt = `<div class="receipt">
      ${r.sold.length ? `<div class="rc-main"><div><small>SOLD</small><span>${r.sold.map(([k, n]) => `<i class="sw" style="background:${ITEMS[k].c}"></i>${n} ${ITEMS[k].n}`).join(' &nbsp; ')}</span></div><b class="cr" id="rcTotal" data-v="${r.total}">+0 cr</b></div>` : ''}
      ${marketClosed(S.loc) ? '<div class="rc-sub badt">Market closed by a strike — ore not sold.</div>' : ''}
      ${r.fuel || r.repair ? `<div class="rc-sub">${r.fuel ? `⛽ Refueled +${r.fuel} (−${fmt(r.fuelCost)} cr)` : ''} ${r.repair ? `🔧 Repaired +${r.repair} (−${fmt(r.repairCost)} cr)` : ''}</div>` : ''}
    </div>`;
  }
  const body = dockBody(dockTab);
  const foot = [];
  if (l.field) foot.push(`<button class="btn ore big" onclick="enterMine()">⛏ Launch — ${l.field.n}</button>`);
  if (has(U.MAP)) foot.push(`<button class="btn big" onclick="closeSheet()">🗺 Star Map</button>`);
  const keep = $('sheet').querySelector('.tabbody');
  const sc = keep && !fresh ? keep.scrollTop : 0;
  openSheet(`🛰 ${l.station} <small>${l.n}</small>`, `${receipt}
    ${tabs.length > 1 ? `<div class="tabs">${tabs.map(([k, n]) => `<button class="tab ${k === dockTab ? 'on' : ''}" onclick="dockTab='${k}';renderDock()">${n}</button>`).join('')}</div>` : ''}
    <div class="tabbody">${body}</div>
    <div class="dock-foot">${foot.join('')}</div>`, 'dock');
  const nb = $('sheet').querySelector('.tabbody'); if (nb) nb.scrollTop = sc;
  const rt = $('rcTotal');
  if (rt) countUp(rt, +rt.dataset.v);
  for (const k of UPG_KEYS) if (upgOpen(k)) S.seenUpg[k] = 1;
  updateHUD();
}
function countUp(el, v) {
  const t0 = performance.now(), dur = Math.min(1200, 300 + v / 4);
  const step = now => { const k = Math.min(1, (now - t0) / dur); el.textContent = '+' + fmt(v * (1 - Math.pow(1 - k, 3))) + ' cr'; if (k < 1) requestAnimationFrame(step); };
  requestAnimationFrame(step);
}
function dockBody(tab) {
  const id = S.loc, l = LOC[id];
  if (tab === 'upg') {
    let h = '<div class="upgs">';
    for (const k of UPG_KEYS) {
      if (!upgOpen(k)) continue;
      const u = UPG[k], lv = S.lv[k];
      const next = lv < 5 ? lv + 1 : null;
      const cost = next ? u.cost[next - 1] : 0;
      const can = next && S.credits >= cost;
      h += `<div class="upg ${lv >= 5 ? 'maxed' : ''} ${can ? 'can' : ''}">
        ${!S.seenUpg[k] ? '<span class="newb">NEW</span>' : ''}
        <div class="uh"><span class="uicon">${u.icon}</span><b>${u.n}</b><span class="pips">${[1, 2, 3, 4, 5].map(i => `<i class="${i <= lv ? 'on' : ''}"></i>`).join('')}</span></div>
        <div class="ud">${next ? upgDelta(k, lv, next) : `<b>${u.names[lv - 1]}</b> · MAXED`}</div>
        ${next ? `<button class="btn ${can ? 'primary' : ''}" ${can ? '' : 'disabled'} onclick="buyUpg('${k}')">${can ? 'Buy' : 'Need'} · ${fmt(cost)} cr</button>` : ''}
      </div>`;
    }
    h += '</div>';
    const locked = UPG_KEYS.filter(k => !upgOpen(k));
    if (locked.length) h += `<p class="hint center">🔒 ${locked.length} more upgrade${locked.length > 1 ? 's' : ''} unlock as you progress.</p>`;
    return h;
  }
  if (tab === 'trade') {
    if (marketClosed(id)) return `<div class="empty">✊ Market closed by a strike. Come back in a few days.</div>`;
    const keys = ITEM_KEYS.filter(k => (!ITEMS[k].ore && l.market[k] != null) || S.cargo[k]);
    let h = `<p class="hint">Buy goods where they're cheap (▼) and sell them where they're wanted (▲). Selling a lot at once lowers the price.</p>
      <div class="mkt"><div class="mrow mh"><span>Good</span><span>Sell</span><span>Have</span><span></span><span>Buy</span><span></span></div>`;
    for (const k of keys) {
      const sp = sellPrice(id, k), bp = buyPrice(id, k), have = S.cargo[k] || 0;
      const ratio = sp ? sp / ITEMS[k].b : 0;
      const trend = !sp ? '' : ratio > 1.4 ? '<i class="up">▲▲</i>' : ratio > 1.1 ? '<i class="up">▲</i>' : ratio < 0.75 ? '<i class="dn">▼▼</i>' : ratio < 0.95 ? '<i class="dn">▼</i>' : '';
      const ev = eventPriceMult(id, k) !== 1 ? '<i class="evi">⚡</i>' : '';
      h += `<div class="mrow">
        <span class="mname c-n"><i class="sw" style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}${ev}</span>
        <span class="price c-sp">${sp ? fmt(sp) + ' ' + trend : '<small class="dim">—</small>'}</span>
        <span class="have c-h">${have || '<small class="dim">0</small>'}</span>
        <span class="bb c-sb">${sp && have ? `<button onclick="mktSell('${k}',1)">1</button><button onclick="mktSell('${k}',10)">10</button><button class="all" onclick="mktSell('${k}',9999)">All</button>` : ''}</span>
        <span class="price c-bp">${bp ? fmt(bp) : '<small class="dim">—</small>'}</span>
        <span class="bb c-bb">${bp ? `<button onclick="mktBuy('${k}',1)">1</button><button onclick="mktBuy('${k}',10)">10</button><button class="all" onclick="mktBuy('${k}',9999)">Max</button>` : ''}</span></div>`;
    }
    return h + '</div>';
  }
  if (tab === 'contracts') {
    const avail = S.contracts[id] || [];
    let h = '<div class="sub">Your active contracts</div>';
    if (!S.active.length) h += '<div class="empty small">None yet. Accept one below.</div>';
    for (const c of S.active) {
      const dl = c.deadline - S.day;
      h += `<div class="contract ${canDeliver(c) ? 'ready' : ''}"><div>${c.urgent ? '<span class="chip bad">URGENT</span> ' : ''}${contractText(c)}<small>Reward ${fmt(c.reward)} cr · ${dl} day${dl !== 1 ? 's' : ''} left${c.type === 'deliver' ? ` · you have ${S.cargo[c.item] || 0}/${c.qty}` : ''}</small></div>
        ${canDeliver(c) ? `<button class="btn primary" onclick="deliver('${c.id}')">Deliver</button>` : ''}</div>`;
    }
    h += `<div class="sub">Offered at ${l.station}</div>`;
    if (!avail.length) h += '<div class="empty small">No new contracts. Check back in a few days.</div>';
    for (const c of avail) {
      h += `<div class="contract"><div>${c.urgent ? '<span class="chip bad">URGENT</span> ' : ''}${contractText(c)}<small>Reward <b class="cr">${fmt(c.reward)} cr</b> · +${c.rep} rep · ${c.days} days</small></div>
        <button class="btn" onclick="acceptContract('${id}','${c.id}');renderDock()">Accept</button></div>`;
    }
    return h;
  }
  if (tab === 'invest') {
    const lv = S.invest[id] || 0;
    const cost = investCost(id);
    const needRep = lv < 3 ? INVEST.rep[lv] : 0;
    const rep = l.faction ? S.rep[l.faction] : 0;
    const okRep = rep >= needRep;
    let h = `<div class="inv"><p>Invest in <b>${l.station}</b>. Each level pays <b>daily income</b> and adds permanent <b>influence</b>.</p><div class="invlv">`;
    for (let i = 0; i < 3; i++) {
      h += `<div class="ivc ${i < lv ? 'own' : i === lv ? 'next' : ''}"><b>${INVEST.names[i]}</b><small>+${INVEST.income[i]} cr/day</small><small>+${INVEST.infl[i]} influence</small>${INVEST.rep[i] ? `<small>Needs rep ${INVEST.rep[i]}</small>` : ''}<em>${i < lv ? '✔ OWNED' : fmt(Math.round(INVEST.cost[i] * (l.black ? 1.3 : 1))) + ' cr'}</em></div>`;
    }
    h += '</div>';
    if (cost != null) h += `<button class="btn primary big" ${S.credits >= cost && okRep ? '' : 'disabled'} onclick="buyInvest()">${okRep ? `Invest · ${fmt(cost)} cr` : `Needs ${needRep} reputation with ${FACTIONS[l.faction].n} (you have ${Math.round(rep)})`}</button>`;
    else h += '<div class="empty small">You control this station\'s consortium. 👑</div>';
    h += `<p class="hint">Total income: <b>${fmt(dailyIncome())} cr/day</b>. Raise reputation with contracts, crisis relief and fighting pirates.</p></div>`;
    return h;
  }
  return '';
}
function upgDelta(k, a, b) {
  const u = UPG[k], i = a - 1, j = b - 1;
  const ar = (x, y, unit) => `${x}${unit || ''} → <b>${y}${unit || ''}</b>`;
  switch (k) {
    case 'hull': return `New ship: <b>${u.names[j]}</b><br>Cargo ${ar(u.cargo[i], u.cargo[j])} · Armor ${ar(u.hp[i], u.hp[j])}`;
    case 'laser': return `Mining power ${ar(u.dps[i], u.dps[j])} · Range ${ar(u.range[i], u.range[j])}`;
    case 'engine': return `Speed ${ar('×' + u.speed[i], '×' + u.speed[j])} · Fuel use ${ar(Math.round(100 / u.eff[i]) + '%', Math.round(100 / u.eff[j]) + '%')}`;
    case 'tank': return `Fuel ${ar(u.fuel[i], u.fuel[j])}`;
    case 'shield': return `Shield ${ar(u.sp[i], u.sp[j])}`;
    case 'weapons': return `Firepower ${ar(u.dps[i], u.dps[j])}`;
    case 'drones': return `Magnet ${ar(u.magnet[i], u.magnet[j])} · Drones ${ar(u.count[i], u.count[j])}`;
    case 'scanner': return `Ambush avoidance ${ar(Math.round(u.avoid[i] * 100), Math.round(u.avoid[j] * 100), '%')}`;
  }
}
function drawShipPreview(id, lv, t) {
  const c = $(id); if (!c) return;
  const x = c.getContext('2d');
  const w = c.width, h = c.height;
  x.clearRect(0, 0, w, h);
  const g = x.createRadialGradient(w / 2, h / 2, 10, w / 2, h / 2, w / 2);
  g.addColorStop(0, '#16224a'); g.addColorStop(1, '#070b1c');
  x.fillStyle = g; x.fillRect(0, 0, w, h);
  x.strokeStyle = 'rgba(61,232,255,0.1)';
  for (let i = 0; i < w; i += 20) { x.beginPath(); x.moveTo(i, 0); x.lineTo(i, h); x.stroke(); }
  for (let i = 0; i < h; i += 20) { x.beginPath(); x.moveTo(0, i); x.lineTo(w, i); x.stroke(); }
  const Hd = HULLS[lv.hull - 1];
  const ex = Hd.hull[0][0] - Hd.tail + 28, ey = Math.abs(Hd.wing[1][1]) * 2 + 8;
  const sc = Math.min(w * 0.78 / ex, h * 0.8 / ey);
  const cx = (Hd.hull[0][0] + Hd.tail - 22) / 2;
  drawPlayerShip(x, lv, w / 2 - cx * sc, h / 2 + Math.sin(t * 1.5) * 3, 0, sc, 0.7 + 0.3 * Math.sin(t * 3), t);
}
function mktSell(k, n) { if (marketClosed(S.loc)) return; const before = S.credits; doSell(S.loc, k, n); const got = S.credits - before; if (got) { sfx('cash'); toast(`+${fmt(got)} cr`, 'good'); } renderDock(); }
function mktBuy(k, n) { if (marketClosed(S.loc)) return; if (cargoFree() <= 0) { toast('Cargo hold full', 'bad'); return; } const b = doBuy(S.loc, k, n); if (b) sfx('click'); else toast('Not enough credits', 'bad'); renderDock(); }
function buyUpg(k) {
  const lv = S.lv[k]; const cost = UPG[k].cost[lv];
  if (S.credits < cost) return;
  S.credits -= cost; S.lv[k]++;
  if (k === 'hull') S.hull = ship.hpMax;
  if (k === 'tank' && has(U.MAP)) { S.fuel = ship.fuelMax; }
  sfx('upgrade');
  addNews('🔧', `Upgrade installed: ${UPG[k].n} (${UPG[k].names[S.lv[k] - 1]})`, '#3de8ff');
  renderDock();
  if (k === 'hull') {
    showModal({ icon: '', title: `New ship: ${UPG.hull.names[S.lv.hull - 1]}!`, cls: 'unlock', html: `<canvas id="newShip" width="420" height="200"></canvas><p>Cargo <b>${ship.cargoMax}</b> · Armor <b>${ship.hpMax}</b></p>`,
      buttons: [{ label: 'Nice!', cls: 'primary', fn: () => {} }],
      after: () => { const t0 = performance.now(); const anim = () => { if ($('newShip')) { drawShipPreview('newShip', S.lv, (performance.now() - t0) / 1000); requestAnimationFrame(anim); } }; anim(); } });
  } else toast(`${UPG[k].n} → ${UPG[k].names[S.lv[k] - 1]}`, 'good');
}
function deliver(cid) { const c = S.active.find(x => x.id === cid); if (c && canDeliver(c)) completeContract(c); renderDock(); }
function buyInvest() {
  const id = S.loc, cost = investCost(id);
  if (cost == null || S.credits < cost) return;
  S.credits -= cost; S.invest[id] = (S.invest[id] || 0) + 1;
  const l = LOC[id]; if (l.faction) repChange(l.faction, 5);
  sfx('win');
  addNews('🏛️', `You bought a ${INVEST.names[S.invest[id] - 1]} on ${l.station}. Your influence grows.`, '#ffc857');
  toast(`Investment complete: +${INVEST.infl[S.invest[id] - 1]} influence`, 'good');
  renderDock();
}

// ---------- global panels ----------
function openShip() {
  sfx('click');
  const rows = Object.keys(S.cargo).map(k => `<div class="srow"><span><i class="sw" style="background:${ITEMS[k].c}"></i> ${ITEMS[k].n}</span><b>${S.cargo[k]}</b><button class="mini" onclick="jettison('${k}')">Dump</button></div>`).join('');
  let upg = '';
  for (const k of UPG_KEYS) if (upgOpen(k)) upg += `<div class="srow"><span>${UPG[k].icon} ${UPG[k].n}</span><b>${UPG[k].names[S.lv[k] - 1]}</b><span class="pips">${[1, 2, 3, 4, 5].map(i => `<i class="${i <= S.lv[k] ? 'on' : ''}"></i>`).join('')}</span></div>`;
  openSheet(`🚀 ${S.shipName} <small>${UPG.hull.names[S.lv.hull - 1]} class</small>`, `<div class="yard-top"><canvas id="shipView" width="420" height="190"></canvas></div>
    <div class="cols"><div><div class="sub">Systems</div>${upg}</div><div><div class="sub">Cargo hold ${cargoUsed()}/${ship.cargoMax}</div>${rows || '<div class="empty small">Empty</div>'}
    <div class="sub">Stats</div><div class="srow"><span>Ore mined</span><b>${fmt(S.stats.mined)}</b></div><div class="srow"><span>Lifetime earnings</span><b>${fmt(S.stats.earned)} cr</b></div>
    ${has(U.BELT) ? `<div class="srow"><span>Battles won / lost</span><b>${S.stats.won} / ${S.stats.lost}</b></div>` : ''}${has(U.TRADE) ? `<div class="srow"><span>Contracts</span><b>${S.stats.contracts}</b></div>` : ''}</div></div>`);
  const t0 = performance.now();
  const anim = () => { if (!$('sheet').classList.contains('hidden') && $('shipView')) { drawShipPreview('shipView', S.lv, (performance.now() - t0) / 1000); requestAnimationFrame(anim); } };
  anim();
}
function jettison(k) { addCargo(k, -S.cargo[k]); sfx('click'); openShip(); }

function openFactions() {
  sfx('click');
  const inf = influence();
  let h = `<div class="inf-big"><div><small>INFLUENCE</small><b>${inf}</b><span>/ 100</span></div><div class="meter big gold"><i style="width:${Math.min(100, inf)}%"></i></div><div class="rank">${rankName(inf)}</div></div>`;
  h += '<div class="sub">Faction reputation</div>';
  for (const f in FACTIONS) {
    const r = S.rep[f];
    h += `<div class="fac"><span style="color:${FACTIONS[f].c}">${FACTIONS[f].n}</span><div class="repbar"><i style="left:50%;width:${Math.abs(r) / 2}%;${r < 0 ? `left:${50 - Math.abs(r) / 2}%;background:#ff4d6d` : `background:${FACTIONS[f].c}`}"></i><em></em></div><b>${Math.round(r)}</b></div>`;
  }
  h += '<div class="sub">Your investments</div>';
  const inv = Object.keys(S.invest);
  if (!inv.length) h += '<div class="empty small">No investments yet — use the Invest tab when docked.</div>';
  for (const id of inv) h += `<div class="srow"><span>${LOC[id].station}</span><b>${INVEST.names[S.invest[id] - 1]}</b><span class="pips">${[1, 2, 3].map(i => `<i class="${i <= S.invest[id] ? 'on' : ''}"></i>`).join('')}</span></div>`;
  h += `<p class="hint">Passive income: <b>${fmt(dailyIncome())} cr/day</b>. Influence comes from investments, good reputation and battle victories.</p>`;
  h += '<div class="sub">Active events</div>' + (S.events.length ? S.events.map(e => `<div class="ev">${e.icon} <b>${e.title}</b> <small>— ${e.text} (${e.end - S.day}d)</small></div>`).join('') : '<div class="empty small">The system is calm… for now.</div>');
  openSheet('🏛 Factions & Influence', h);
}
function openNews() {
  sfx('click');
  openSheet('📰 System News', S.news.map(n => `<div class="news"><i>DAY ${n.day}</i><span>${n.icon}</span><div>${n.html}</div></div>`).join(''));
}
function openMenu() {
  sfx('click');
  openSheet('☰ Menu', `<div class="menu">
    <button class="btn primary big" onclick="closeSheet()">Resume</button>
    <button class="btn big" onclick="openHelp()">How to play</button>
    <button class="btn big danger" onclick="confirmNew()">New game</button></div>`);
}
function confirmNew() {
  closeSheet(true);
  showModal({ icon: '⚠️', title: 'Start a new game?', html: 'Your current progress will be lost.', buttons: [
    { label: 'Yes, start over', cls: 'danger', fn: () => { pendingUnlocks = []; newGame(); save(); shownCredits = 0; setScene(MineScene, 'luna'); updateHUD(); updateTicker(); } },
    { label: 'Cancel', fn: () => {} }] });
}
function openHelp() {
  openSheet('📖 How to play', `<div class="help">
    <h4>⛏ Mine</h4><p>Fly with <b>WASD</b> or arrows, <b>hold the mouse</b> to fire your laser (or Space). Big rocks break into smaller ones and drop glowing ore. On mobile: drag on the left, hold LASER. Glowing veins give double ore.</p>
    <h4>🛰 Dock</h4><p>Docking sells your ore, refuels and repairs automatically. Spend your credits on upgrades — a new hull is a whole new ship.</p>
    <h4>🔓 Unlock</h4><p>The more you earn, the more of the Solar System opens up: the star map, new planets, pirates, trading, events and finally influence.</p>
    <h4>🗺 Travel</h4><p>Planets orbit the Sun, so distances change every day. Farther places pay more and are more dangerous.</p>
    <h4>👑 Win</h4><p>Invest in stations to earn influence. Reach <b>100 influence</b> to rule the Solar System.</p></div>`);
}
