'use strict';
// ============ INTERFAZ (DOM) ============
const $ = id => document.getElementById(id);
let modalOpen = false;
let stationTab = 'market';

function toast(msg, cls) {
  const el = document.createElement('div');
  el.className = 'toast ' + (cls || '');
  el.innerHTML = msg;
  $('toasts').appendChild(el);
  setTimeout(() => el.classList.add('out'), 2600);
  setTimeout(() => el.remove(), 3100);
}

function showModal(o) {
  modalOpen = true;
  const m = $('modal');
  m.innerHTML = `<div class="mbox ${o.danger ? 'danger' : ''}">
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
}
function closeModal() { modalOpen = false; $('modal').classList.add('hidden'); }

function showEventBanner(ev) {
  const b = $('eventBanner');
  b.innerHTML = `<span class="eicon">${ev.icon}</span><div><small>NOTICIAS DEL SISTEMA · DÍA ${S.day}</small><b>${ev.title}</b><p>${ev.text}</p></div>`;
  b.classList.add('show');
  sfx('event');
  clearTimeout(b._t); b._t = setTimeout(() => b.classList.remove('show'), 6500);
}

function updateTicker() {
  const el = $('tickerIn'); if (!el || !S) return;
  const items = S.news.slice(0, 8).map(n => `<span><i>DÍA ${n.day}</i> ${n.icon} ${n.html.replace(/<[^>]+>/g, '')}</span>`);
  el.innerHTML = items.join('<span class="sep">◆</span>');
}

// ---------- HUD ----------
function updateHUD() {
  if (!S) return;
  $('hCr').textContent = fmt(S.credits) + ' ₵';
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
  const o = TUTORIAL[S.tut];
  $('objective').innerHTML = o && !S.won ? `<small>OBJETIVO ${S.tut + 1}/${TUTORIAL.length}</small><b>${o.t}</b><span>${o.d}</span>${o.r ? `<em>Recompensa: ${fmt(o.r)} ₵</em>` : `<em>Influencia: ${inf}/100</em>`}` : `<small>SOBERANÍA SOLAR</small><b>Influencia ${inf}</b><span>Sigue expandiendo tu imperio.</span>`;
  if (!S.won && inf >= 100) victory();
}
function checkTut() {
  if (!S) return;
  const c = [
    () => S.loc === 'luna',
    () => S.stats.mined >= 10,
    () => S.stats.traded > 0,
    () => Object.values(S.lv).reduce((a, b) => a + b, 0) > 8,
    () => S.active.length > 0 || S.stats.contracts > 0,
    () => S.loc === 'ceres',
    () => Object.keys(S.invest).length > 0,
    () => influence() >= 100,
  ][S.tut];
  if (c && c()) advanceTut();
}
function advanceTut() {
  const o = TUTORIAL[S.tut];
  if (!o) return;
  if (o.r) { S.credits += o.r; toast(`✔ Objetivo cumplido: ${o.t} (+${fmt(o.r)} ₵)`, 'good'); sfx('cash'); }
  S.tut++;
  const el = $('objective'); el.classList.remove('flash'); void el.offsetWidth; el.classList.add('flash');
  updateHUD();
  setTimeout(checkTut, 400);
}
function victory() {
  S.won = true; save();
  sfx('win');
  showModal({ icon: '👑', title: '¡Dominas el Sistema Solar!', html: `En <b>${S.day} días</b> pasaste de minar rocas en la Luna a ser la fuerza económica más influyente del sistema.<br><br>
    Mineral extraído: <b>${fmt(S.stats.mined)}</b><br>Ganancias totales: <b>${fmt(S.stats.earned)} ₵</b><br>Batallas ganadas: <b>${S.stats.won}</b><br>Contratos: <b>${S.stats.contracts}</b><br><br>Puedes seguir jugando y construir tu imperio.`,
    buttons: [{ label: 'Seguir jugando', cls: 'primary', fn: () => {} }] });
}

// ---------- Panel de ubicación (mapa) ----------
function selectLoc(id) {
  MapScene.sel = id;
  const l = LOC[id];
  const here = id === S.loc;
  const p = $('locPanel');
  const fac = l.faction ? `<span class="chip" style="--c:${FACTIONS[l.faction].c}">${FACTIONS[l.faction].n}</span>` : '<span class="chip">Sin gobierno</span>';
  const dg = locDanger(id);
  const dtxt = dg < 0.1 ? ['Seguro', 'good'] : dg < 0.3 ? ['Moderado', 'warn'] : dg < 0.5 ? ['Peligroso', 'bad'] : ['Mortal', 'bad'];
  const evs = S.events.filter(e => e.locs && e.locs.includes(id));
  let html = `<div class="lp-head"><div><h3>${l.n}</h3><small>${[l.station, l.field && l.field.n].filter(Boolean).join(' · ')}</small></div><button class="x" onclick="hideLocPanel()">✕</button></div>
    <div class="chips">${fac}<span class="chip ${dtxt[1]}">Riesgo: ${dtxt[0]}</span>${l.field ? '<span class="chip ore">⛏ Minería</span>' : ''}${l.station ? '<span class="chip">🛰 Estación</span>' : ''}${l.yard ? `<span class="chip">🔧 Astillero Nv.${l.yard}</span>` : ''}</div>
    <p class="desc">${l.desc}</p>`;
  if (evs.length) html += `<div class="evs">${evs.map(e => `<div class="ev">${e.icon} <b>${e.title}</b> <small>(${e.end - S.day} días)</small></div>`).join('')}</div>`;
  if (l.field) {
    const ores = Object.keys(l.field.ores).sort((a, b) => l.field.ores[b] - l.field.ores[a]);
    html += `<div class="sub">Minerales</div><div class="ores">${ores.map(o => `<span class="ore" style="--c:${ITEMS[o].c}">${ITEMS[o].n}</span>`).join('')}</div>`;
    if (l.field.hazard === 'heat') html += `<div class="warnline">🔥 Calor extremo: daña el casco sin escudos.</div>`;
  }
  if (l.market && !here) {
    let val = 0; for (const k in S.cargo) { const sp = sellPrice(id, k); if (sp) val += sp * S.cargo[k]; }
    const hot = Object.keys(l.market).map(k => ({ k, m: basePrice(id, k) / ITEMS[k].b })).filter(x => x.m >= 1.45).sort((a, b) => b.m - a.m).slice(0, 4);
    const cheap = Object.keys(l.market).filter(k => buyPrice(id, k) != null).map(k => ({ k, m: basePrice(id, k) / ITEMS[k].b })).sort((a, b) => a.m - b.m).slice(0, 3);
    if (cargoUsed()) html += `<div class="sub">Tu carga aquí vale ≈ <b class="cr">${fmt(val)} ₵</b></div>`;
    if (hot.length) html += `<div class="sub">Paga bien</div><div class="ores">${hot.map(x => `<span class="ore" style="--c:${ITEMS[x.k].c}">${ITEMS[x.k].n} <b>×${x.m.toFixed(1)}</b></span>`).join('')}</div>`;
    if (cheap.length) html += `<div class="sub">Vende barato</div><div class="ores">${cheap.map(x => `<span class="ore" style="--c:${ITEMS[x.k].c}">${ITEMS[x.k].n} <b>×${x.m.toFixed(1)}</b></span>`).join('')}</div>`;
  }
  const deliv = S.active.filter(c => c.type === 'deliver' && c.to === id);
  if (deliv.length) html += `<div class="sub">Contratos con destino aquí: ${deliv.length}</div>`;
  if (here) {
    html += `<div class="lp-actions">`;
    if (l.station) html += `<button class="btn primary big" onclick="openStation()">🛰 Atracar en ${l.station}</button>`;
    if (l.field) html += `<button class="btn ore big" onclick="enterMine()">⛏ Minar en ${l.field.n}</button>`;
    html += `</div><div class="here">📍 Estás aquí</div>`;
  } else {
    const info = travelInfo(id);
    const ok = info.fuel <= S.fuel;
    html += `<div class="travel">
      <div><small>Distancia</small><b>${(info.d / 100).toFixed(2)} UA</b></div>
      <div><small>Combustible</small><b class="${ok ? '' : 'badt'}">${info.fuel} / ${Math.floor(S.fuel)}</b></div>
      <div><small>Duración</small><b>${info.days} día${info.days > 1 ? 's' : ''}</b></div>
      <div><small>Emboscada</small><b class="${info.danger > 0.3 ? 'badt' : ''}">${Math.round(info.danger * 100)}%</b></div></div>
      <button class="btn primary big" ${ok ? '' : 'disabled'} onclick="MapScene.startTravel('${id}')">${ok ? '🚀 VIAJAR' : '⛽ Combustible insuficiente'}</button>`;
  }
  p.innerHTML = html;
  p.classList.remove('hidden');
}
function hideLocPanel() { $('locPanel').classList.add('hidden'); MapScene.sel = null; }
function enterMine() { sfx('click'); if (S.tut === 0) checkTut(); setScene(MineScene, S.loc); }

function showMapUI(on) {
  $('mapTools').classList.toggle('hidden', !on);
  if (!on) $('locPanel').classList.add('hidden');
}
function showMineUI(on) {
  document.body.classList.toggle('mining', on);
  $('mineUI').classList.toggle('hidden', !on);
  $('touchUI').classList.toggle('hidden', !on || !isTouch);
  if (on) $('mineName').textContent = MineScene.loc.field.n;
}
function updateMineHUD() {
  const now = performance.now();
  if (updateMineHUD.t && now - updateMineHUD.t < 200) return;
  updateMineHUD.t = now;
  const rows = Object.keys(S.cargo).map(k => `<div class="crow"><i style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}<b>${S.cargo[k]}</b></div>`).join('');
  $('mineCargo').innerHTML = rows || '<div class="crow dim">Bodega vacía</div>';
  $('mineInfo').innerHTML = `Rocas: ${MineScene.rocks.length} · Escudo: ${Math.round(MineScene.p.shield)}/${ship.shieldMax}` +
    (MineScene.loc.field.hazard === 'heat' ? ' · <span class="badt">🔥 CALOR</span>' : '');
  updateHUD();
}
function showBattleUI(on) { document.body.classList.toggle('battle', on); $('battleUI').classList.toggle('hidden', !on); if (on) { $('btnSpeed').textContent = 'Velocidad ×1'; $('btnRetreat').disabled = false; } }

// ---------- Hoja (panel grande) ----------
function openSheet(title, html, cls) {
  modalOpen = true;
  const s = $('sheet');
  s.className = 'sheet ' + (cls || '');
  s.innerHTML = `<div class="sh-head"><h2>${title}</h2><button class="x" onclick="closeSheet()">✕</button></div><div class="sh-body">${html}</div>`;
  s.classList.remove('hidden');
}
function closeSheet() {
  $('sheet').classList.add('hidden'); modalOpen = false; save(); updateHUD();
  if (scene === MapScene && !MapScene.travel) selectLoc(S.loc);
}

// ---------- Estación ----------
function openStation(tab) {
  if (tab) stationTab = tab;
  const l = LOC[S.loc];
  sfx('click');
  const tabs = [['market', '📦 Mercado'], ['yard', '🔧 Astillero'], ['services', '⛽ Servicios'], ['contracts', '📜 Contratos'], ['invest', '🏛 Inversión']];
  const rep = l.faction ? S.rep[l.faction] : 0;
  const html = `<div class="st-head">
      <div class="st-fac" style="--c:${l.faction ? FACTIONS[l.faction].c : '#fff'}">${l.faction ? FACTIONS[l.faction].n : ''} · Reputación <b>${Math.round(rep)}</b></div>
      <div class="st-cr">${fmt(S.credits)} ₵ · Bodega ${cargoUsed()}/${ship.cargoMax}</div></div>
    <div class="tabs">${tabs.map(([k, n]) => `<button class="tab ${k === stationTab ? 'on' : ''}" onclick="openStation('${k}')">${n}${k === 'contracts' && S.active.some(canDeliver) ? ' <i class="dot"></i>' : ''}</button>`).join('')}</div>
    <div class="tabbody">${stationBody(stationTab)}</div>`;
  const keep = $('sheet').querySelector('.tabbody');
  const sc = keep ? keep.scrollTop : 0;
  openSheet(`🛰 ${l.station} <small>${l.n}</small>`, html, 'station');
  const nb = $('sheet').querySelector('.tabbody'); if (nb) nb.scrollTop = sc;
  if (stationTab === 'yard') setTimeout(drawYardPreview, 0);
  updateHUD();
}
function stationBody(tab) {
  const id = S.loc, l = LOC[id];
  if (tab === 'market') {
    if (marketClosed(id)) return `<div class="empty">✊ Mercado cerrado por huelga. Vuelve en unos días.</div>`;
    const keys = ITEM_KEYS.filter(k => l.market[k] != null || S.cargo[k]);
    const oreCargo = ORES.some(k => S.cargo[k] && sellPrice(id, k));
    let h = `<div class="mkt-actions"><button class="btn primary" ${oreCargo ? '' : 'disabled'} onclick="sellAllOre()">Vender todo el mineral</button><span class="hint">Vender muchas unidades baja el precio; se recupera con los días.</span></div>
      <div class="mkt"><div class="mrow mh"><span>Producto</span><span>Venta</span><span>Tienes</span><span></span><span>Compra</span><span></span></div>`;
    for (const k of keys) {
      const sp = sellPrice(id, k), bp = buyPrice(id, k), have = S.cargo[k] || 0;
      const ratio = sp ? sp / ITEMS[k].b : 0;
      const trend = !sp ? '' : ratio > 1.4 ? '<i class="up">▲▲</i>' : ratio > 1.1 ? '<i class="up">▲</i>' : ratio < 0.75 ? '<i class="dn">▼▼</i>' : ratio < 0.95 ? '<i class="dn">▼</i>' : '';
      const ev = eventPriceMult(id, k) !== 1 ? '<i class="evi">⚡</i>' : '';
      h += `<div class="mrow">
        <span class="mname c-n"><i class="sw" style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}${ev}${ITEMS[k].ore ? '<small>mineral</small>' : ''}</span>
        <span class="price c-sp">${sp ? fmt(sp) + ' ₵ ' + trend : '<small class="dim">no compran</small>'}</span>
        <span class="have c-h">${have || '<small class="dim">0</small>'}</span>
        <span class="bb c-sb">${sp && have ? `<button onclick="mktSell('${k}',1)">1</button><button onclick="mktSell('${k}',10)">10</button><button class="all" onclick="mktSell('${k}',9999)">Todo</button>` : ''}</span>
        <span class="price c-bp">${bp ? fmt(bp) + ' ₵' : '<small class="dim">—</small>'}</span>
        <span class="bb c-bb">${bp ? `<button onclick="mktBuy('${k}',1)">1</button><button onclick="mktBuy('${k}',10)">10</button><button class="all" onclick="mktBuy('${k}',9999)">Máx</button>` : ''}</span></div>`;
    }
    return h + '</div>';
  }
  if (tab === 'yard') {
    if (!l.yard) return `<div class="empty">Esta estación no tiene astillero.</div>`;
    let h = `<div class="yard-top"><canvas id="yardShip" width="360" height="170"></canvas><div class="yard-stats">
      <h4>${S.shipName} <small>clase ${UPG.hull.names[S.lv.hull - 1]}</small></h4>
      <div>Bodega <b>${ship.cargoMax}</b> · Casco <b>${ship.hpMax}</b> · Tanque <b>${ship.fuelMax}</b></div>
      <div>Láser <b>${ship.laserDps}</b> dps · Armas <b>${ship.weaponDps.toFixed(0)}</b> dps · Escudo <b>${ship.shieldMax}</b></div>
      <div>Poder de combate <b>${ship.power.toFixed(1)}</b> · Astillero nivel máx. <b>${l.yard}</b></div></div></div><div class="upgs">`;
    for (const k of UPG_KEYS) {
      const u = UPG[k], lv = S.lv[k];
      const max = (l.yardMax && l.yardMax[k]) || l.yard;
      const next = lv < 5 ? lv + 1 : null;
      const cost = next ? u.cost[next - 1] : 0;
      const can = next && next <= max && S.credits >= cost;
      const stat = upgStat(k, next || lv);
      h += `<div class="upg ${lv >= 5 ? 'maxed' : ''}">
        <div class="uh"><span class="uicon">${u.icon}</span><b>${u.n}</b><span class="pips">${[1, 2, 3, 4, 5].map(i => `<i class="${i <= lv ? 'on' : ''}"></i>`).join('')}</span></div>
        <div class="un">${u.names[lv - 1]}${next ? ` → <b>${u.names[next - 1]}</b>` : ' · MÁXIMO'}</div>
        <div class="ud">${stat}</div>
        ${next ? `<button class="btn ${can ? 'primary' : ''}" ${can ? '' : 'disabled'} onclick="buyUpg('${k}')">${next > max ? `Requiere astillero Nv.${next}` : `Mejorar · ${fmt(cost)} ₵`}</button>` : ''}
      </div>`;
    }
    return h + '</div>';
  }
  if (tab === 'services') {
    const fp = fuelPrice(id), need = Math.ceil(ship.fuelMax - S.fuel), fcost = Math.ceil(need * fp);
    const hneed = Math.ceil(ship.hpMax - S.hull), rp = l.repair, hcost = Math.ceil(hneed * rp);
    return `<div class="svc">
      <div class="svcard"><h4>⛽ Combustible</h4><div class="meter big"><i style="width:${S.fuel / ship.fuelMax * 100}%"></i></div>
        <p>${Math.floor(S.fuel)} / ${ship.fuelMax} · <b>${fp} ₵</b> por unidad</p>
        <button class="btn primary" ${need > 0 && S.credits >= 1 ? '' : 'disabled'} onclick="refuel(9999)">Llenar tanque (${fmt(Math.min(fcost, S.credits))} ₵)</button>
        <button class="btn" ${need > 0 ? '' : 'disabled'} onclick="refuel(10)">+10</button></div>
      <div class="svcard"><h4>🔧 Reparación</h4><div class="meter big hp"><i style="width:${S.hull / ship.hpMax * 100}%"></i></div>
        <p>${Math.ceil(S.hull)} / ${ship.hpMax} · <b>${rp} ₵</b> por punto</p>
        <button class="btn primary" ${hneed > 0 ? '' : 'disabled'} onclick="repair()">Reparar todo (${fmt(Math.min(hcost, S.credits))} ₵)</button></div>
    </div>`;
  }
  if (tab === 'contracts') {
    const avail = S.contracts[id] || [];
    let h = '<div class="sub">Tus contratos activos</div>';
    if (!S.active.length) h += '<div class="empty small">Ninguno. Acepta uno abajo.</div>';
    for (const c of S.active) {
      const dl = c.deadline - S.day;
      h += `<div class="contract ${canDeliver(c) ? 'ready' : ''}"><div>${c.urgent ? '<span class="chip bad">URGENTE</span> ' : ''}${contractText(c)}<small>Recompensa ${fmt(c.reward)} ₵ · +${c.rep} rep. · vence en ${dl} día${dl !== 1 ? 's' : ''}${c.type === 'deliver' ? ` · tienes ${S.cargo[c.item] || 0}/${c.qty}` : ''}</small></div>
        ${canDeliver(c) ? `<button class="btn primary" onclick="deliver('${c.id}')">Entregar</button>` : ''}</div>`;
    }
    h += `<div class="sub">Disponibles en ${l.station}</div>`;
    if (!avail.length) h += '<div class="empty small">No hay contratos nuevos. Vuelve en unos días.</div>';
    for (const c of avail) {
      h += `<div class="contract"><div>${c.urgent ? '<span class="chip bad">URGENTE</span> ' : ''}${contractText(c)}<small>Recompensa <b class="cr">${fmt(c.reward)} ₵</b> · +${c.rep} rep. ${c.faction ? FACTIONS[c.faction].n : ''} · plazo ${c.days} días</small></div>
        <button class="btn" onclick="acceptContract('${id}','${c.id}');openStation()">Aceptar</button></div>`;
    }
    return h;
  }
  if (tab === 'invest') {
    const lv = S.invest[id] || 0;
    const cost = investCost(id);
    const needRep = lv < 3 ? INVEST.rep[lv] : 0;
    const rep = l.faction ? S.rep[l.faction] : 0;
    const okRep = rep >= needRep;
    let h = `<div class="inv"><p>Invierte en la infraestructura de <b>${l.station}</b>. Cada nivel te da <b>ingresos diarios</b> e <b>influencia</b> permanente en el sistema.</p><div class="invlv">`;
    for (let i = 0; i < 3; i++) {
      h += `<div class="ivc ${i < lv ? 'own' : i === lv ? 'next' : ''}"><b>${INVEST.names[i]}</b><small>+${INVEST.income[i]} ₵/día</small><small>+${INVEST.infl[i]} influencia</small><small>Rep. ${INVEST.rep[i]}</small><em>${i < lv ? '✔ TUYO' : fmt(Math.round(INVEST.cost[i] * (l.black ? 1.3 : 1))) + ' ₵'}</em></div>`;
    }
    h += '</div>';
    if (cost != null) h += `<button class="btn primary big" ${S.credits >= cost && okRep ? '' : 'disabled'} onclick="buyInvest()">${okRep ? `Invertir · ${fmt(cost)} ₵` : `Requiere reputación ${needRep} con ${FACTIONS[l.faction].n} (tienes ${Math.round(rep)})`}</button>`;
    else h += '<div class="empty small">Controlas el consorcio de esta estación. 👑</div>';
    h += `<p class="hint">Ingresos totales: <b>${fmt(dailyIncome())} ₵/día</b>. Sube reputación con contratos, ayuda humanitaria en crisis y combatiendo piratas.</p></div>`;
    return h;
  }
  return '';
}
function upgStat(k, lv) {
  const u = UPG[k], i = lv - 1;
  switch (k) {
    case 'hull': return `Bodega ${u.cargo[i]} · Casco ${u.hp[i]} · Masa ×${u.mass[i]}`;
    case 'laser': return `${u.dps[i]} daño/s · alcance ${u.range[i]}`;
    case 'engine': return `Velocidad ×${u.speed[i]} · Eficiencia ×${u.eff[i]} · Huida ${Math.round(u.flee[i] * 100)}%`;
    case 'tank': return `${u.fuel[i]} unidades`;
    case 'shield': return u.sp[i] ? `${u.sp[i]} puntos de escudo` : 'Sin escudos';
    case 'weapons': return `${u.dps[i]} daño/s en combate`;
    case 'drones': return `Imán ${u.magnet[i]} · ${u.count[i]} drone${u.count[i] !== 1 ? 's' : ''} recolector${u.count[i] !== 1 ? 'es' : ''}`;
    case 'scanner': return `Evita emboscadas ${Math.round(u.avoid[i] * 100)}%${i >= 1 ? ' · revela vetas ricas' : ''}`;
  }
}
function drawYardPreview() {
  const c = $('yardShip'); if (!c) return;
  const x = c.getContext('2d');
  x.clearRect(0, 0, c.width, c.height);
  const g = x.createRadialGradient(180, 85, 10, 180, 85, 180);
  g.addColorStop(0, '#16224a'); g.addColorStop(1, '#070b1c');
  x.fillStyle = g; x.fillRect(0, 0, c.width, c.height);
  x.strokeStyle = 'rgba(61,232,255,0.12)';
  for (let i = 0; i < c.width; i += 20) { x.beginPath(); x.moveTo(i, 0); x.lineTo(i, c.height); x.stroke(); }
  for (let i = 0; i < c.height; i += 20) { x.beginPath(); x.moveTo(0, i); x.lineTo(c.width, i); x.stroke(); }
  drawPlayerShip(x, S.lv, 190, 85, 0, 2.6 - S.lv.hull * 0.28, 0.6, performance.now() / 1000);
}
function mktSell(k, n) { if (marketClosed(S.loc)) return; const got = doSell(S.loc, k, n); if (got) { sfx('cash'); toast(`+${fmt(got)} ₵`, 'good'); } checkTut(); openStation(); }
function mktBuy(k, n) { if (marketClosed(S.loc)) return; if (cargoFree() <= 0) { toast('Bodega llena', 'bad'); return; } const b = doBuy(S.loc, k, n); if (b) sfx('click'); else toast('Créditos insuficientes', 'bad'); openStation(); }
function sellAllOre() {
  let total = 0;
  for (const k of ORES) if (S.cargo[k] && sellPrice(S.loc, k)) total += doSell(S.loc, k, S.cargo[k]);
  if (total) { sfx('cash'); toast(`Vendiste mineral por ${fmt(total)} ₵`, 'good'); }
  checkTut(); openStation();
}
function buyUpg(k) {
  const lv = S.lv[k]; const cost = UPG[k].cost[lv];
  if (S.credits < cost) return;
  S.credits -= cost; S.lv[k]++;
  if (k === 'hull') S.hull = ship.hpMax;
  if (k === 'tank') S.fuel = Math.min(S.fuel, ship.fuelMax);
  sfx('upgrade');
  toast(`${UPG[k].n}: ${UPG[k].names[S.lv[k] - 1]} instalado`, 'good');
  addNews('🔧', `Mejora instalada: ${UPG[k].n} ${UPG[k].names[S.lv[k] - 1]}`, '#3de8ff');
  checkTut(); openStation();
}
function refuel(n) {
  const fp = fuelPrice(S.loc);
  const can = Math.min(n, ship.fuelMax - S.fuel, Math.floor(S.credits / fp));
  if (can <= 0) return;
  S.fuel += can; S.credits -= Math.ceil(can * fp);
  sfx('click'); openStation();
}
function repair() {
  const rp = LOC[S.loc].repair;
  const can = Math.min(ship.hpMax - S.hull, Math.floor(S.credits / rp));
  if (can <= 0) return;
  S.hull += can; S.credits -= Math.ceil(can * rp);
  sfx('upgrade'); openStation();
}
function deliver(cid) { const c = S.active.find(x => x.id === cid); if (c && canDeliver(c)) completeContract(c); checkTut(); openStation(); }
function buyInvest() {
  const id = S.loc, cost = investCost(id);
  if (cost == null || S.credits < cost) return;
  S.credits -= cost; S.invest[id] = (S.invest[id] || 0) + 1;
  const l = LOC[id]; if (l.faction) repChange(l.faction, 5);
  sfx('win');
  addNews('🏛️', `Adquieres ${INVEST.names[S.invest[id] - 1]} en ${l.station}. Tu influencia crece.`, '#ffc857');
  toast(`Inversión completada: +${INVEST.infl[S.invest[id] - 1]} influencia`, 'good');
  checkTut(); openStation();
}

// ---------- Paneles globales ----------
function openShip() {
  sfx('click');
  const rows = Object.keys(S.cargo).map(k => `<div class="mrow two"><span class="mname"><i class="sw" style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}</span><span>${S.cargo[k]}</span><span><button class="mini" onclick="jettison('${k}')">Tirar</button></span></div>`).join('');
  let upg = '';
  for (const k of UPG_KEYS) upg += `<div class="srow"><span>${UPG[k].icon} ${UPG[k].n}</span><b>${UPG[k].names[S.lv[k] - 1]}</b><span class="pips">${[1, 2, 3, 4, 5].map(i => `<i class="${i <= S.lv[k] ? 'on' : ''}"></i>`).join('')}</span></div>`;
  openSheet(`🚀 ${S.shipName}`, `<div class="yard-top"><canvas id="yardShip" width="360" height="170"></canvas><div class="yard-stats">
    <div>Bodega <b>${cargoUsed()}/${ship.cargoMax}</b> · Casco <b>${Math.ceil(S.hull)}/${ship.hpMax}</b> · Combustible <b>${Math.floor(S.fuel)}/${ship.fuelMax}</b></div>
    <div>Láser <b>${ship.laserDps}</b> dps · alcance ${ship.laserRange}</div><div>Armas <b>${ship.weaponDps.toFixed(0)}</b> dps · Escudo <b>${ship.shieldMax}</b> · Poder <b>${ship.power.toFixed(1)}</b></div>
    <div>Valor estimado de la carga: <b class="cr">${fmt(cargoValueEstimate())} ₵</b></div></div></div>
    <div class="cols"><div><div class="sub">Sistemas</div>${upg}</div><div><div class="sub">Bodega</div>${rows || '<div class="empty small">Vacía</div>'}
    <div class="sub">Estadísticas</div><div class="srow"><span>Mineral extraído</span><b>${fmt(S.stats.mined)}</b></div><div class="srow"><span>Ganancias totales</span><b>${fmt(S.stats.earned)} ₵</b></div>
    <div class="srow"><span>Batallas ganadas / perdidas</span><b>${S.stats.won} / ${S.stats.lost}</b></div><div class="srow"><span>Contratos completados</span><b>${S.stats.contracts}</b></div><div class="srow"><span>Distancia recorrida</span><b>${(S.stats.dist / 100).toFixed(1)} UA</b></div></div></div>`);
  setTimeout(drawYardPreview, 0);
}
function jettison(k) { addCargo(k, -S.cargo[k]); sfx('click'); openShip(); }

function openFactions() {
  sfx('click');
  const inf = influence();
  let h = `<div class="inf-big"><div><small>INFLUENCIA</small><b>${inf}</b><span>/ 100</span></div><div class="meter big gold"><i style="width:${Math.min(100, inf)}%"></i></div><div class="rank">${rankName(inf)}</div></div>`;
  h += '<div class="sub">Reputación con facciones</div>';
  for (const f in FACTIONS) {
    const r = S.rep[f];
    h += `<div class="fac"><span style="color:${FACTIONS[f].c}">${FACTIONS[f].n}</span><div class="repbar"><i style="left:50%;width:${Math.abs(r) / 2}%;${r < 0 ? `left:${50 - Math.abs(r) / 2}%;background:#ff4d6d` : `background:${FACTIONS[f].c}`}"></i><em></em></div><b>${Math.round(r)}</b></div>`;
  }
  h += '<div class="sub">Tus inversiones</div>';
  const inv = Object.keys(S.invest);
  if (!inv.length) h += '<div class="empty small">Aún no inviertes en ninguna estación. Hazlo desde la pestaña Inversión de una estación.</div>';
  for (const id of inv) h += `<div class="srow"><span>${LOC[id].station}</span><b>${INVEST.names[S.invest[id] - 1]}</b><span class="pips">${[1, 2, 3].map(i => `<i class="${i <= S.invest[id] ? 'on' : ''}"></i>`).join('')}</span></div>`;
  h += `<p class="hint">Ingresos pasivos: <b>${fmt(dailyIncome())} ₵/día</b>. La influencia viene de inversiones, reputación positiva y victorias en combate. A 100 dominas el sistema.</p>`;
  h += '<div class="sub">Eventos activos</div>' + (S.events.length ? S.events.map(e => `<div class="ev">${e.icon} <b>${e.title}</b> <small>— ${e.text} (${e.end - S.day} días)</small></div>`).join('') : '<div class="empty small">El sistema está en calma… por ahora.</div>');
  openSheet('🏛 Facciones e influencia', h);
}
function openNews() {
  sfx('click');
  openSheet('📰 Noticias del sistema', S.news.map(n => `<div class="news"><i>DÍA ${n.day}</i><span>${n.icon}</span><div>${n.html}</div></div>`).join(''));
}
function openMenu() {
  sfx('click');
  openSheet('☰ Menú', `<div class="menu">
    <button class="btn primary big" onclick="closeSheet()">Continuar</button>
    <button class="btn big" onclick="openHelp()">Cómo jugar</button>
    <button class="btn big" onclick="save();toast('Partida guardada','good')">Guardar partida</button>
    <button class="btn big danger" onclick="confirmNew()">Nueva partida</button></div>`);
}
function confirmNew() {
  closeSheet();
  showModal({ icon: '⚠️', title: '¿Nueva partida?', html: 'Perderás tu progreso actual.', buttons: [
    { label: 'Sí, empezar de nuevo', cls: 'danger', fn: () => { newGame(); save(); setScene(MapScene); updateHUD(); updateTicker(); } },
    { label: 'Cancelar', fn: () => {} }] });
}
function openHelp() {
  openSheet('📖 Cómo jugar', `<div class="help">
    <h4>🎯 Meta</h4><p>Empiezas con una nave pequeña y 600 créditos. Mina, comercia y combate para ganar <b>100 de influencia</b> y dominar el Sistema Solar.</p>
    <h4>🗺 Mapa</h4><p>Toca un planeta, luna o campo de asteroides para ver información. Los planetas <b>orbitan</b>: las distancias cambian con los días. Viajar consume <b>combustible</b> según la distancia y el tamaño de tu nave.</p>
    <h4>⛏ Minería</h4><p><b>WASD / flechas</b> para moverte, <b>mantén el clic</b> para disparar el láser (o <b>Espacio</b>). Rompe asteroides grandes en pedazos y recoge el mineral. En móvil: joystick a la izquierda y botón LÁSER con autoapuntado. Las vetas brillantes dan doble mineral.</p>
    <h4>📦 Comercio</h4><p>Cada estación paga distinto. ▲ significa que el precio está alto. Compra barato en un lugar y vende caro en otro. Vender mucho satura el mercado.</p>
    <h4>☠ Piratas</h4><p>Las zonas lejanas son más ricas y más peligrosas. El combate es automático: depende de tu casco, escudos, armas y drones. Puedes huir, sobornar o pelear.</p>
    <h4>📰 Eventos</h4><p>Guerras, pandemias, hambrunas y booms cambian los precios. Aprovéchalos: llevar medicinas a una pandemia paga mucho y da reputación.</p>
    <h4>🏛 Influencia</h4><p>Invierte en estaciones (necesitas reputación con su facción) para ganar ingresos diarios e influencia.</p></div>`);
}
