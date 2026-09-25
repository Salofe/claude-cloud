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
  const inc = totalIncome();
  $('hRate').textContent = inc > 0 ? `+${fmt(inc)}/s` : '';
}
function updateHUD() {
  if (!S) return;
  for (const el of document.querySelectorAll('[data-need]')) el.classList.toggle('locked', S.unlock < +el.dataset.need);
  $('hDay').textContent = S.day;
  $('hFuel').style.width = (S.fuel / ship.fuelMax * 100) + '%';
  $('hFuelT').textContent = `${Math.floor(S.fuel)}/${ship.fuelMax}`;
  $('hHull').style.width = (S.hull / ship.hpMax * 100) + '%';
  $('hHullT').textContent = `${fmt(Math.ceil(S.hull))}/${fmt(ship.hpMax)}`;
  $('hCargo').style.width = (cargoUsed() / ship.cargoMax * 100) + '%';
  $('hCargoT').textContent = `${fmt(cargoUsed())}/${fmt(ship.cargoMax)}`;
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
    o.innerHTML = `<small>FINAL GOAL</small><b>👑 Reach 100 influence</b><div class="meter gold"><i style="width:${Math.min(100, inf)}%"></i></div><span>Influence ${inf}/100 · invest & upgrade outposts</span>`;
  } else o.innerHTML = `<small>SOLAR SOVEREIGN</small><b>👑 You rule the system</b><span>Keep growing your empire.</span>`;
  if (!S.won && has(U.SATURN) && inf >= 100 && !isBlocking()) victory();
  if (pendingUnlocks.length && $('modal').classList.contains('hidden') && !(scene === MineScene && (MineScene.inCombat || MineScene.space)) && !(MapScene.travel)) showUnlock(pendingUnlocks.shift());
  else if (pendingChoices.length && $('modal').classList.contains('hidden') && $('sheet').classList.contains('hidden') && scene !== MineScene && !MapScene.travel) showChoice(pendingChoices.shift());
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
    const hot = Object.keys(l.market).map(k => ({ k, m: priceRatio(id, k) })).filter(x => x.m >= 1.45).sort((a, b) => b.m - a.m).slice(0, 4);
    if (hot.length) html += `<div class="sub">Pays well for</div><div class="ores">${hot.map(x => `<span class="ore" style="--c:${ITEMS[x.k].c}">${ITEMS[x.k].n} <b>×${x.m.toFixed(1)}</b></span>`).join('')}</div>`;
  }
  const pws = powersAt(id);
  if (pws.length) html += `<div class="sub">⚡ Your power</div>${powerButtons(pws)}`;
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
  if (!on) { coach(''); $('battleUI').classList.add('hidden'); document.body.classList.remove('battle'); }
  if (on) $('mineName').textContent = MineScene.space ? '☠ Pirate ambush' : MineScene.loc.field.n;
}

function updateMineHUD() {
  const now = performance.now();
  if (updateMineHUD.t && now - updateMineHUD.t < 150) return;
  updateMineHUD.t = now;
  const sc = MineScene;
  const rows = Object.keys(S.cargo).map(k => `<div class="crow"><i style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}<b>${fmt(S.cargo[k])}</b></div>`).join('');
  const val = LOC[S.loc].market ? oreValueAt(S.loc) : 0;
  $('mineCargo').innerHTML = (rows || '<div class="crow dim">Cargo hold empty</div>') + (val ? `<div class="crow val">Worth<b class="cr">${fmt(val)} cr</b></div>` : '');
  const depth = sc.space ? '' : `<span class="depth">Depth ${Math.round(sc.depthOf(sc.p.y) * 100)}% · richness ×${(1 + sc.depthOf(sc.p.y) * 4).toFixed(1)}</span>`;
  $('mineInfo').innerHTML = depth + (ship.shieldMax ? `<span>Shield ${fmt(sc.p.shield)}/${fmt(ship.shieldMax)}</span>` : '') + (sc.loc.field.hazard === 'heat' ? ' <span class="badt">🔥 HEAT</span>' : '');
  const combat = sc.inCombat || sc.clearT > 0;
  $('fireBtn').textContent = sc.inCombat ? 'FIRE' : 'LASER';
  document.body.classList.toggle('battle', combat);
  $('battleUI').classList.toggle('hidden', !combat);
  if (combat) {
    $('btTitle').innerHTML = sc.inCombat ? `⚔ ${sc.enemies.length} PIRATE${sc.enemies.length > 1 ? 'S' : ''}` : '✔ AREA CLEAR — resuming course';
    $('btnWarp').classList.toggle('hidden', !sc.space || !sc.inCombat);
    $('btnWarp').textContent = sc.warp ? `Warping… ${Math.round(sc.warp.t / ship.warpTime * 100)}%` : `⚡ Warp out (${ship.warpTime.toFixed(1)}s)`;
    $('btnContinue').classList.toggle('hidden', !(sc.space && !sc.inCombat));
  }
  updateHUD();
}

function showBattleUI(on) {}

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
  if (has(U.OUTPOST) && l.field) tabs.push(['outpost', '🤖 Outpost' + (!S.outposts[l.id] && S.credits >= buildCost(l.id) ? ' <i class="dot"></i>' : '')]);
  if (has(U.TRADE) && !l.depot) tabs.push(['trade', '📦 Trade'], ['contracts', '📜 Contracts' + (S.active.some(canDeliver) ? ' <i class="dot"></i>' : '')]);
  if (has(U.TRADE) && !l.depot && (powersAt(l.id).length || (has(U.SATURN) && STATION_TIER[l.id]))) tabs.push(['planet', '🏛 Planet']);
  let receipt = '';
  const r = lastDock;
  if (fresh && r && (r.sold.length || r.fuel || r.repair)) {
    receipt = `<div class="receipt">
      ${r.sold.length ? `<div class="rc-main"><div><small>SOLD</small><span>${r.sold.map(([k, n]) => `<i class="sw" style="background:${ITEMS[k].c}"></i>${n} ${ITEMS[k].n}`).join(' &nbsp; ')}</span></div><b class="cr" id="rcTotal" data-v="${r.total}">+0 cr</b></div>` : ''}
      ${marketClosed(S.loc) ? '<div class="rc-sub badt">Market closed by a strike — ore not sold.</div>' : ''}
      ${r.fuel || r.repair ? `<div class="rc-sub">${r.fuel ? `⛽ Refueled +${r.fuel} (−${fmt(r.fuelCost)} cr)` : ''} ${r.repair ? `🔧 Repaired +${r.repair} (−${fmt(r.repairCost)} cr)` : ''}</div>` : ''}
    </div>`;
  }
  let sellbox = '';
  const oreN = cargoUsed();
  if (oreN && has(U.MAP)) {
    const here = cargoValueAt(S.loc), alts = betterMarkets(S.loc);
    sellbox = `<div class="sellbox">
      <div class="sb-cargo"><small>CARGO</small><span>${ITEM_KEYS.filter(k => S.cargo[k]).map(k => `<i class="sw" style="background:${ITEMS[k].c}"></i>${fmt(S.cargo[k])} ${ITEMS[k].n}`).join(' &nbsp; ')}</span></div>
      <div class="sb-row">
        ${marketClosed(S.loc) ? '<div class="badt">Market closed by a strike.</div>' : here ? `<button class="btn primary" onclick="sellHere()">Sell all here · <b>${fmt(here)} cr</b></button>` : '<small>Nothing in your hold sells well here.</small>'}
        <div class="sb-alts">${alts.length ? alts.map(a => `<span onclick="closeSheet();selectLoc('${a.id}')"><b>${LOC[a.id].n}</b> pays <b class="cr">${fmt(a.v)}</b> <em>+${Math.round((a.v / Math.max(1, here) - 1) * 100)}%</em> <small>· ${a.fuel} ⛽</small></span>`).join('') : '<small>This is the best price you can get right now.</small>'}</div>
      </div></div>`;
  }
  const body = dockBody(dockTab);
  const foot = [];
  if (l.field) foot.push(`<button class="btn ore big" onclick="enterMine()">⛏ Launch — ${l.field.n}</button>`);
  if (has(U.MAP)) foot.push(`<button class="btn big" onclick="closeSheet()">🗺 Star Map</button>`);
  const keep = $('sheet').querySelector('.tabbody');
  const sc = keep && !fresh ? keep.scrollTop : 0;
  openSheet(`🛰 ${l.station} <small>${l.n}</small>`, `${receipt}${sellbox}
    ${tabs.length > 1 ? `<div class="tabs">${tabs.map(([k, n]) => `<button class="tab ${k === dockTab ? 'on' : ''}" onclick="dockTab='${k}';renderDock()">${n}</button>`).join('')}</div>` : ''}
    <div class="tabbody">${body}</div>
    <div class="dock-foot">${foot.join('')}</div>`, 'dock');
  const nb = $('sheet').querySelector('.tabbody'); if (nb) nb.scrollTop = sc;
  const rt = $('rcTotal');
  if (rt) countUp(rt, +rt.dataset.v);
  for (const k of UPG_KEYS) if (upgOpen(k)) S.seenUpg[k] = 1;
  save();   // every purchase/sale re-renders the dock, so this checkpoints them
  updateHUD();
}
function powerButtons(pws) {
  return `<div class="powers">${pws.map(o => `<button class="btn small-btn ${o.kind === 'nuke' ? 'danger' : ''}" ${o.ok ? '' : 'disabled'} onclick="doPower('${o.kind}','${o.arg}')" title="${o.d || ''}">${o.icon} ${o.label} · ${fmt(o.cost)}${o.why ? ` <small>(${o.why})</small>` : o.d ? ` <small>— ${o.d}</small>` : ''}</button>`).join('')}</div>`;
}
function demandChip(loc, g) {
  const d = demandOf(loc, g), [t, c] = demandLabel(d);
  return `<span class="dem ${c}" title="${t}${d < 1 ? ` · full again in ~${demandDays(loc, g)} days` : ''}"><i style="width:${Math.round(d * 100)}%"></i><b>${t}</b></span>`;
}
function tradeRun(g, to) {
  const n = doBuy(S.loc, g, 9999);
  if (!n) { toast('Not enough credits or space', 'bad'); return; }
  sfx('click'); toast(`Bought ${n} ${ITEMS[g].n} — course plotted to ${LOC[to].n}`, 'good');
  save(); closeSheet(); selectLoc(to); MapScene.focus(to);
}
function doFreighter(from, to, g) {
  if (!hireFreighter(from, to, g)) { toast('Not enough credits (or fleet full)', 'bad'); return; }
  sfx('upgrade'); toast(`🚚 Freighter now runs ${ITEMS[g].n} to ${LOC[to].n}`, 'good'); renderDock();
}
function sellHere() {
  const r = sellAllOre(S.loc);
  for (const k of GOODS) if (S.cargo[k] && wantsGood(S.loc, k)) { const n = S.cargo[k]; const got = doSell(S.loc, k, n); r.sold.push([k, n, got]); r.total += got; }
  if (!r.total) return;
  sfx('cash');
  lastDock = { ...r, fuel: 0, repair: 0 };
  renderDock(true);
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
      const maxed = lv >= u.max;
      const cost = maxed ? 0 : upgCost(k, lv);
      const can = !maxed && S.credits >= cost;
      const nMax = maxed ? 0 : affordableLevels(k);
      h += `<div class="upg ${maxed ? 'maxed' : ''} ${can ? 'can' : ''}">
        ${!S.seenUpg[k] ? '<span class="newb">NEW</span>' : ''}
        <div class="uh"><span class="uicon">${u.icon}</span><b>${u.n}</b><span class="lvl">${k === 'hull' ? u.names[lv - 1] : 'Lv ' + lv + `<small>/${u.max}</small>`}</span></div>
        <div class="lvbar"><i style="width:${lv / u.max * 100}%"></i></div>
        <div class="ud">${maxed ? '<b>MAXED</b>' : upgDelta(k, lv, lv + 1)}</div>
        ${maxed ? '' : `<div class="ubtns"><button class="btn ${can ? 'primary' : ''}" ${can ? '' : 'disabled'} onclick="buyUpg('${k}')">${can ? 'Buy' : 'Need'} · ${fmt(cost)}</button>${nMax > 1 && k !== 'hull' ? `<button class="btn primary maxb" onclick="buyUpg('${k}', ${nMax})">×${nMax}</button>` : ''}</div>`}
      </div>`;
    }
    h += '</div>';
    const locked = UPG_KEYS.filter(k => !upgOpen(k));
    if (locked.length) h += `<p class="hint center">🔒 ${locked.length} more upgrade${locked.length > 1 ? 's' : ''} unlock as you progress.</p>`;
    return h;
  }
  if (tab === 'outpost') return outpostBody(id);
  if (tab === 'trade') {
    if (marketClosed(id)) return `<div class="empty">✊ Market closed by a strike. Come back in a few days.</div>`;
    const keys = ITEM_KEYS.filter(k => (!ITEMS[k].ore && l.market[k] != null) || S.cargo[k]);
    const routes = tradeRoutes(id);
    const fc = FREIGHT.cost(), fn = (S.freighters || []).length;
    let h = routes.length ? `<div class="routes"><div class="sub">💡 Best trades from here</div>${routes.slice(0, 3).map(r => `<div class="route">
      <div><i class="sw" style="background:${ITEMS[r.g].c}"></i><b>${ITEMS[r.g].n}</b> buy ${fmt(r.bp)} → <b>${LOC[r.to].n}</b> pays ${fmt(r.sp)} <em>×${(r.avg / r.bp).toFixed(1)}</em> ${demandChip(r.to, r.g)} <small>≈ +${fmt(r.profit * 0.9)} for ${r.units}</small></div>
      <div class="rt-btns"><button class="btn small-btn primary" ${r.units && S.credits >= r.bp ? '' : 'disabled'} onclick="tradeRun('${r.g}','${r.to}')">Buy ${r.units} & fly there</button>
      ${has(U.TRADE) ? `<button class="btn small-btn" ${fn < FREIGHT.max && S.credits >= fc && routeCount(id, r.to, r.g) < FREIGHT.perRoute ? '' : 'disabled'} onclick="doFreighter('${id}','${r.to}','${r.g}')">🚚 Freighter · ${fmt(fc)} <small>(+${fmt(freighterIncome({ from: id, to: r.to, g: r.g }))}/s)</small></button>` : ''}</div></div>`).join('')}</div>` : '<p class="hint">Nothing here is worth hauling right now — the markets that want these goods are saturated. Try another station, or wait for demand to return.</p>';
    h += `<p class="hint">Buy where it's cheap (▼), sell where it's wanted (▲) — or hire a 🚚 freighter to run the route for you forever. Each market only wants so much: deliveries use up its <b>demand</b>, which returns slowly (~3%/day). Shortages and wars create fresh demand.</p>
      <div class="mkt"><div class="mrow mh"><span>Good</span><span>Sell</span><span>Have</span><span></span><span>Buy</span><span></span></div>`;
    for (const k of keys) {
      const sp = sellPrice(id, k), bp = buyPrice(id, k), have = S.cargo[k] || 0;
      const ratio = sp ? priceRatio(id, k) : 0;
      const trend = !sp ? '' : ratio > 1.4 ? '<i class="up">▲▲</i>' : ratio > 1.1 ? '<i class="up">▲</i>' : ratio < 0.75 ? '<i class="dn">▼▼</i>' : ratio < 0.95 ? '<i class="dn">▼</i>' : '';
      const ev = eventPriceMult(id, k) !== 1 ? '<i class="evi">⚡</i>' : '';
      h += `<div class="mrow">
        <span class="mname c-n"><i class="sw" style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}${ev}</span>
        <span class="price c-sp">${sp ? fmt(sp) + ' ' + trend + (wantsGood(id, k) ? demandChip(id, k) : '') : '<small class="dim">—</small>'}</span>
        <span class="have c-h">${have || '<small class="dim">0</small>'}</span>
        <span class="bb c-sb">${sp && have ? `<button onclick="mktSell('${k}',1)">1</button><button onclick="mktSell('${k}',10)">10</button><button class="all" onclick="mktSell('${k}',9999)">All</button>` : ''}</span>
        <span class="price c-bp">${bp ? fmt(bp) + `<small class="stock">${stockLeft(id, k)} left</small>` : '<small class="dim">—</small>'}</span>
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
  if (tab === 'planet') {
    const pws = powersAt(id);
    let h = pws.length ? `<div class="sub">⚡ Your power on ${l.n}</div>${powerButtons(pws)}` : '';
    if (has(U.SATURN) && STATION_TIER[id]) h += dockBody('invest');
    else if (!has(U.SATURN)) h += '<p class="hint center">🔒 Investments and politics (wars, peace deals) unlock with Saturn & Influence.</p>';
    return h;
  }
  if (tab === 'invest') {
    const lv = S.invest[id] || 0;
    const cost = investCost(id);
    const needRep = lv < 3 ? INVEST.rep[lv] : 0;
    const rep = l.faction ? S.rep[l.faction] : 0;
    const okRep = rep >= needRep;
    let h = `<div class="inv"><p>Invest in <b>${l.station}</b>. Every level adds <b>+10% to ALL your income</b> (mining, drones, everything) and permanent <b>influence</b>.</p><div class="invlv">`;
    for (let i = 0; i < 3; i++) {
      h += `<div class="ivc ${i < lv ? 'own' : i === lv ? 'next' : ''}"><b>${INVEST.names[i]}</b><small>+10% income</small><small>+${INVEST.infl[i]} influence</small>${INVEST.rep[i] ? `<small>Needs rep ${INVEST.rep[i]}</small>` : ''}<em>${i < lv ? '✔ OWNED' : fmt(INVEST.cost[i] * (STATION_TIER[id] || 5)) + ' cr'}</em></div>`;
    }
    h += '</div>';
    if (cost != null) h += `<button class="btn primary big" ${S.credits >= cost && okRep ? '' : 'disabled'} onclick="buyInvest()">${okRep ? `Invest · ${fmt(cost)} cr` : `Needs ${needRep} reputation with ${FACTIONS[l.faction].n} (you have ${Math.round(rep)})`}</button>`;
    else h += '<div class="empty small">You control this station\'s consortium. 👑</div>';
    h += `<p class="hint">Income multiplier: <b>×${incomeMult().toFixed(2)}</b>. Raise reputation with contracts, crisis relief and fighting pirates.</p></div>`;
    return h;
  }
  return '';
}
function upgDelta(k, a, b) {
  const ar = (x, y) => `${x} → <b>${y}</b>`;
  const at = (lv, f) => { const o = S.lv[k]; S.lv[k] = lv; const v = f(); S.lv[k] = o; return v; };
  switch (k) {
    case 'hull': return `New ship: <b>${UPG.hull.names[b - 1]}</b><br>Base cargo ${ar(UPG.hull.cargo[a - 1], UPG.hull.cargo[b - 1])} · Armor ${ar(UPG.hull.hp[a - 1], UPG.hull.hp[b - 1])}`;
    case 'laser': return `Mining power ${ar(fmt(at(a, () => ship.laserDps)), fmt(at(b, () => ship.laserDps)))}`;
    case 'magnet': return `Range ${ar(at(a, () => ship.magnet), at(b, () => ship.magnet))}${at(b, () => ship.drones) > at(a, () => ship.drones) ? ' · <b>+1 drone</b>' : ` · drones ${at(a, () => ship.drones)}`}`;
    case 'cargo': return `Cargo ${ar(at(a, () => ship.cargoMax), at(b, () => ship.cargoMax))}`;
    case 'extractor': return `Ore per rock ${ar('×' + at(a, () => ship.yieldMult).toFixed(2), '×' + at(b, () => ship.yieldMult).toFixed(2))}`;
    case 'refinery': return `All ore value ${ar('×' + at(a, () => ship.refinery).toFixed(2), '×' + at(b, () => ship.refinery).toFixed(2))}`;
    case 'engine': return `Speed ${ar('×' + at(a, () => ship.speed).toFixed(2), '×' + at(b, () => ship.speed).toFixed(2))} · Warp ${at(b, () => ship.warpTime).toFixed(1)}s`;
    case 'tank': return `Fuel ${ar(at(a, () => ship.fuelMax), at(b, () => ship.fuelMax))}`;
    case 'shield': return `Shield ${ar(fmt(at(a, () => ship.shieldMax)), fmt(at(b, () => ship.shieldMax)))}`;
    case 'weapons': return `Firepower ${ar(fmt(at(a, () => ship.weaponDps)), fmt(at(b, () => ship.weaponDps)))}`;
    case 'scanner': return `Ambush avoidance ${ar(Math.round(at(a, () => ship.avoid) * 100) + '%', Math.round(at(b, () => ship.avoid) * 100) + '%')}`;
  }
}
function affordableLevels(k) {
  let n = 0, c = 0, lv = S.lv[k];
  while (lv + n < UPG[k].max && n < 100) { const nc = upgCost(k, lv + n); if (c + nc > S.credits) break; c += nc; n++; }
  return n;
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
function buyUpg(k, n) {
  n = n || 1;
  let bought = 0;
  for (let i = 0; i < n; i++) {
    const lv = S.lv[k]; if (lv >= UPG[k].max) break;
    const cost = upgCost(k, lv); if (S.credits < cost) break;
    S.credits -= cost; S.lv[k]++; bought++;
  }
  if (!bought) return;
  if (k === 'hull') S.hull = ship.hpMax;
  if (k === 'tank' && has(U.MAP)) S.fuel = ship.fuelMax;
  sfx('upgrade');
  renderDock();
  if (k === 'hull') {
    addNews('🚀', `New ship: ${UPG.hull.names[S.lv.hull - 1]}`, '#3de8ff');
    showModal({ icon: '', title: `New ship: ${UPG.hull.names[S.lv.hull - 1]}!`, cls: 'unlock', html: `<canvas id="newShip" width="420" height="200"></canvas><p>Cargo <b>${fmt(ship.cargoMax)}</b> · Armor <b>${fmt(ship.hpMax)}</b></p>`,
      buttons: [{ label: 'Nice!', cls: 'primary', fn: () => {} }],
      after: () => { const t0 = performance.now(); const anim = () => { if ($('newShip')) { drawShipPreview('newShip', shipLv(), (performance.now() - t0) / 1000); requestAnimationFrame(anim); } }; anim(); } });
  } else toast(`${UPG[k].n} → Lv ${S.lv[k]}${bought > 1 ? ` (+${bought})` : ''}`, 'good');
}
function outpostBody(id) {
  const l = LOC[id], o = S.outposts[id], z = l.field.z;
  const boost = (id === 'luna' && built('driver') ? 3 : 1) * (built('ringstation') ? 3 : 1);
  if (!o) {
    const c = buildCost(id);
    return `<div class="op-empty"><div class="op-art">🤖</div><h3>Build a Drone Outpost</h3>
      <p>Drones slowly mine <b>${l.field.n}</b> for you — even when you're somewhere else or offline.</p>
      <p>Each drone earns <b class="cr">${fmt(OUTPOST.rate[z] * incomeMult() * boost)} cr/s</b> here. Starts with room for ${OUTPOST.slots} drones.</p>
      <button class="btn primary big" ${S.credits >= c ? '' : 'disabled'} onclick="doBuild('${id}')">Build outpost · ${fmt(c)} cr</button></div>`;
  }
  const cap = outpostCap(o.lv), full = o.n >= cap;
  const inc = outpostIncome(id), per = OUTPOST.rate[z] * Math.pow(2, o.lv - 1) * incomeMult() * boost;
  const d1 = droneCost(id, 1), n10 = Math.min(10, cap - o.n), d10 = droneCost(id, n10), nm = maxAffordableDrones(id);
  const lc = outpostLvCost(id);
  let slots = '';
  for (let i = 0; i < cap; i++) slots += `<i class="${i < o.n ? 'on' : ''}"></i>`;
  return `<div class="op">
    <div class="op-top"><div><small>OUTPOST · LEVEL ${o.lv}</small><b class="cr">+${fmt(inc)} cr/s</b><span>${o.n} drones × ${fmt(per)} cr/s</span></div><div class="op-drones">${slots}</div></div>
    <div class="sub">Drones <span class="dim">${o.n} / ${cap} slots</span></div>
    ${full ? `<div class="empty small">All slots full — upgrade the outpost for <b>+${OUTPOST.slots} slots</b> and <b>×2 output</b>.</div>` : `<div class="op-row">
      <button class="btn ${S.credits >= d1 ? 'primary' : ''}" ${S.credits >= d1 ? '' : 'disabled'} onclick="doDrones('${id}',1)">+1 drone · ${fmt(d1)}</button>
      ${n10 > 1 ? `<button class="btn ${S.credits >= d10 ? 'primary' : ''}" ${S.credits >= d10 ? '' : 'disabled'} onclick="doDrones('${id}',${n10})">+${n10} · ${fmt(d10)}</button>` : ''}
      <button class="btn ${nm ? 'primary' : ''}" ${nm ? '' : 'disabled'} onclick="doDrones('${id}','max')">MAX${nm ? ` (+${nm})` : ''}</button>
    </div>`}
    <div class="sub">Outpost level</div>
    ${lc != null ? `<button class="btn ${S.credits >= lc ? 'primary' : ''} big" ${S.credits >= lc ? '' : 'disabled'} onclick="doOutLv('${id}')">Level ${o.lv + 1}: <b>×2 output</b> & +${OUTPOST.slots} slots · ${fmt(lc)} cr</button>` : '<div class="empty small">Max level reached 👑</div>'}
    <p class="hint">Drones are slow but never stop — they keep earning while you're offline. Each costs 18% more than the last. Refinery upgrades, investments and megaprojects multiply their income.</p>
  </div>`;
}

function doBuild(id) { if (buildOutpost(id)) { sfx('win'); toast('Outpost online! Your drones are mining.', 'good'); renderDock(); } }
function doDrones(id, k) { const n = buyDrones(id, k); if (n) { sfx('upgrade'); toast(`+${n} drone${n > 1 ? 's' : ''}`, 'good'); renderDock(); } }
function doOutLv(id) { if (upgradeOutpost(id)) { sfx('win'); toast('Outpost upgraded: ×2 output!', 'good'); renderDock(); } }

function deliver(cid) { const c = S.active.find(x => x.id === cid); if (c && canDeliver(c)) completeContract(c); renderDock(); }
function buyInvest() {
  const id = S.loc, cost = investCost(id);
  if (cost == null || S.credits < cost) return;
  S.credits -= cost; S.invest[id] = (S.invest[id] || 0) + 1;
  const l = LOC[id]; if (l.faction) repChange(l.faction, 5);
  sfx('win');
  addNews('🏛️', `You bought a ${INVEST.names[S.invest[id] - 1]} on ${l.station}. Your influence grows.`, '#ffc857');
  toast(`Investment complete: +10% all income, +${INVEST.infl[S.invest[id] - 1]} influence`, 'good');
  renderDock();
}

// ---------- global panels ----------
function openShip() {
  sfx('click');
  const rows = Object.keys(S.cargo).map(k => `<div class="srow"><span><i class="sw" style="background:${ITEMS[k].c}"></i> ${ITEMS[k].n}</span><b>${S.cargo[k]}</b><button class="mini" onclick="jettison('${k}')">Dump</button></div>`).join('');
  let upg = '';
  for (const k of UPG_KEYS) if (upgOpen(k)) upg += `<div class="srow"><span>${UPG[k].icon} ${UPG[k].n}</span><b>${k === 'hull' ? UPG.hull.names[S.lv.hull - 1] : 'Lv ' + S.lv[k] + ' / ' + UPG[k].max}</b></div>`;
  openSheet(`🚀 ${S.shipName} <small>${UPG.hull.names[S.lv.hull - 1]} class</small>`, `<div class="yard-top"><canvas id="shipView" width="420" height="190"></canvas></div>
    <div class="cols"><div><div class="sub">Systems</div>${upg}</div><div><div class="sub">Cargo hold ${cargoUsed()}/${ship.cargoMax}</div>${rows || '<div class="empty small">Empty</div>'}
    <div class="sub">Stats</div><div class="srow"><span>Ore mined</span><b>${fmt(S.stats.mined)}</b></div><div class="srow"><span>Lifetime earnings</span><b>${fmt(S.stats.earned)} cr</b></div>
    ${has(U.BELT) ? `<div class="srow"><span>Battles won / lost</span><b>${S.stats.won} / ${S.stats.lost}</b></div>` : ''}${has(U.TRADE) ? `<div class="srow"><span>Contracts</span><b>${S.stats.contracts}</b></div>` : ''}</div></div>`);
  const t0 = performance.now();
  const anim = () => { if (!$('sheet').classList.contains('hidden') && $('shipView')) { drawShipPreview('shipView', shipLv(), (performance.now() - t0) / 1000); requestAnimationFrame(anim); } };
  anim();
}
function jettison(k) { addCargo(k, -S.cargo[k]); sfx('click'); openShip(); }

function openFactions() {
  sfx('click');
  const inf = influence();
  let h = '';
  const tot = totalIncome();
  h += `<div class="inf-big"><div><small>PASSIVE INCOME</small><b class="cr">${fmt(tot)}</b><span>cr/s</span></div><div class="hint center">Drones ${fmt(droneIncome())}/s · Freighters ${fmt(freightIncome())}/s · ore multiplier ×${incomeMult().toFixed(2)}</div></div>`;
  if ((S.freighters || []).length) {
    h += `<div class="sub">Freighters ${S.freighters.length}/${FREIGHT.max}</div>`;
    for (const f of S.freighters) h += `<div class="srow"><span>🚚 ${ITEMS[f.g].n}: ${LOC[f.from].n} → ${LOC[f.to].n}</span><b class="cr">+${fmt(freighterIncome(f))}/s</b></div>`;
  }
  h += '<div class="sub">Outposts</div>';
  for (const l of FIELDS) {
    const o = S.outposts[l.id];
    if (!locOpen(l.id)) { h += `<div class="srow dim"><span>🔒 ${l.field.n}</span><b>locked</b></div>`; continue; }
    h += `<div class="srow"><span>${o ? '🤖' : '⬜'} ${l.field.n}</span>${o ? `<span class="dim">Lv ${o.lv} · ${o.n} drones</span><b class="cr">+${fmt(outpostIncome(l.id))}/s</b>` : `<b class="dim">Build for ${fmt(buildCost(l.id))}</b>`}</div>`;
  }
  if (has(U.SATURN)) {
    h += `<div class="inf-big" style="margin-top:14px"><div><small>INFLUENCE</small><b>${inf}</b><span>/ 100</span></div><div class="meter big gold"><i style="width:${Math.min(100, inf)}%"></i></div><div class="rank">${rankName(inf)}</div></div>`;
    h += `<p class="hint">Influence comes from investments, outpost levels, megaprojects, reputation, pirate kills${S.peace ? `, ${S.peace} peace deal${S.peace > 1 ? 's' : ''}` : ''}${(S.nuked || []).length ? `, and fear (${S.nuked.length} planet${S.nuked.length > 1 ? 's' : ''} destroyed)` : ''}.</p>`;
  }
  if (has(U.TRADE)) {
    h += '<div class="sub">Faction reputation</div>';
    for (const f in FACTIONS) {
      const r = S.rep[f];
      h += `<div class="fac"><span style="color:${FACTIONS[f].c}">${FACTIONS[f].n}</span><div class="repbar"><i style="left:50%;width:${Math.abs(r) / 2}%;${r < 0 ? `left:${50 - Math.abs(r) / 2}%;background:#ff4d6d` : `background:${FACTIONS[f].c}`}"></i><em></em></div><b>${Math.round(r)}</b></div>`;
    }
    const bad = e => e.war || e.relief || e.closed || e.storm || e.fuelPrice || (e.danger && e.danger.some(d => d.add > 0));
    h += '<div class="sub">Active events</div>' + (S.events.length ? S.events.map(e => `<div class="ev">${e.icon} <b>${e.title}</b> <small>— ${e.text} (${e.end - S.day}d)</small>${bad(e) ? `<button class="btn small-btn" ${S.credits >= POWERS.end.cost() ? '' : 'disabled'} onclick="doPower('end','${e.uid}')">🕊️ End it · ${fmt(POWERS.end.cost())}</button>` : ''}</div>`).join('') : '<div class="empty small">The system is calm… for now.</div>');
  }
  openSheet('🤖 Your Empire', h);
}

function openProjects() {
  sfx('click');
  let h = '<p class="hint">Spend your fortune on projects that change the Solar System forever. Each one also adds influence.</p><div class="projs">';
  for (const p of PROJECTS) {
    const done = built(p.id), open = projectOpen(p), can = open && !done && S.credits >= p.cost;
    const pct = Math.min(100, S.credits / p.cost * 100);
    h += `<div class="proj ${done ? 'done' : ''} ${open ? '' : 'locked'} ${can ? 'can' : ''}">
      <div class="pj-icon">${open || done ? p.icon : '🔒'}</div>
      <div class="pj-main"><b>${p.n}</b>${p.loc ? `<small>${LOC[p.loc].n}</small>` : ''}<p>${open ? p.d : has(p.stage) && p.req ? `Requires the ${PROJ[p.req].n}` : `Unlocks with: ${UNLOCKS[p.stage].title}`}</p>
        <div class="pj-fx">⚡ ${p.fx} · +${p.infl} influence</div>
        ${done ? '<div class="pj-done">✔ BUILT</div>' : open ? `<div class="pj-bar"><i style="width:${pct}%"></i></div><button class="btn ${can ? 'primary' : ''}" ${can ? '' : 'disabled'} onclick="doProject('${p.id}')">${can ? 'Build' : 'Need'} · ${fmt(p.cost)} cr</button>` : ''}
      </div></div>`;
  }
  h += '</div>';
  if (has(U.TRADE)) h += `<div class="sub">System powers</div><p class="hint">Select any planet on the Star Map (or open its 🏛 Planet tab) to fund booms, hire mercenaries, and later start wars, back a side or broker peace. End crises from the Empire panel.</p>`;
  openSheet('🌌 Megaprojects', h);
}
function doProject(id) {
  if (!buildProject(id)) return;
  const p = PROJ[id];
  sfx('win');
  closeSheet(true);
  showModal({ icon: p.icon, title: `${p.n} complete!`, cls: 'unlock', html: `<div class="unl-tag">MEGAPROJECT</div><p>${p.d}</p><p><b class="cr">⚡ ${p.fx}</b></p><small>+${p.infl} influence</small>`,
    buttons: [{ label: 'Behold!', cls: 'primary', fn: () => { if (scene === MapScene && !MapScene.travel) { showMapUI(true); if (p.loc) { selectLoc(p.loc); MapScene.focus(p.loc); } else MapScene.zoomAll(); } } }] });
}
function doPower(kind, arg) {
  if (kind === 'nuke') {
    const l = LOC[arg];
    showModal({ icon: '💥', title: `Destroy ${l.n}?`, danger: true, html: `This cannot be undone. ${l.station || l.n} and everyone's business there will be wiped out, and every faction will fear — and hate — you.<br><br>What remains will be <b>the richest debris field in the system</b>.`,
      buttons: [{ label: `🔥 FIRE · ${fmt(POWERS.nuke.cost())} cr`, cls: 'danger', fn: () => { if (usePower('nuke', arg)) { closeSheet(true); setScene(MapScene); MapScene.focus(arg); selectLoc(arg); } } }, { label: 'Stand down', fn: () => {} }] });
    return;
  }
  if (!usePower(kind, arg)) { toast('Not available right now', 'bad'); return; }
  sfx('win'); toast('Done. The system bends to your will.', 'good');
  const sh = $('sheet');
  if (!sh.classList.contains('hidden')) { if (sh.classList.contains('dock')) renderDock(); else openFactions(); }
  else if (MapScene.sel) selectLoc(MapScene.sel);
  updateHUD();
}
function showChoice(ev) {
  sfx('event');
  showModal({ icon: ev.icon, title: ev.title, html: `<p>${ev.text}</p>`, cls: 'unlock',
    buttons: ev.choices.map(c => ({ label: c.label, cls: c.cost ? 'primary' : '', disabled: c.cost > S.credits, fn: () => { if (c.cost > S.credits) return; S.credits -= c.cost; c.fn(); if (c.cost) addNews(ev.icon, `You chose: ${c.label.split(' · ')[0]}`, '#ffd24a'); save(); } })) });
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
    <h4>🛰 Dock</h4><p>The station is at the <b>bottom</b> of every field. Fly back down into the docking zone to sell your ore, refuel and repair. Rocks get richer the <b>higher</b> you fly.</p>
    <h4>🤖 Drones</h4><p>Build an outpost in each field and buy drones. They earn credits every second — even while you're offline.</p>
    <h4>⚔ Pirates</h4><p>In dangerous zones pirates attack. <b>Hold the mouse</b> to fire your guns. Destroyed ships drop credits.</p>
    <h4>🔓 Unlock</h4><p>The more you earn, the more of the Solar System opens up: the star map, new planets, pirates, trading, events and finally influence.</p>
    <h4>🗺 Travel</h4><p>Planets orbit the Sun, so distances change every day. Farther places pay more and are more dangerous.</p>
    <h4>📦 Trade</h4><p>The Trade tab shows the best deals from each station: one tap buys the goods and plots your course. Hire 🚚 freighters to run a route for you forever.</p>
    <h4>🏛 Power</h4><p>Select a planet on the map (or open its Planet tab) to fund public works, start booms, hire mercenaries — and later incite wars, back a side or broker peace. Each action has a cooldown per planet. The Nova Cannon can even destroy a world…</p>
    <h4>👑 Win</h4><p>Invest in stations to earn influence. Reach <b>100 influence</b> to rule the Solar System.</p></div>`);
}
