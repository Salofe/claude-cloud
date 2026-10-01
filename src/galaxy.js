'use strict';
// ============ THE GALAXY: star systems, the jump gate, Tribute & Legacy ============
// Every star system reuses the same "slots" as Sol (a starter moon field, a capital,
// inner worlds, a belt, a gas giant with moons, a ringed giant, a black market, a frontier
// belt and a hidden final field). Each system is hand-made by overriding names, looks,
// ores, factions and texts on top of Sol, and gets harder: tougher rocks and pirates.

// pristine copy of the Solar System, taken before anything is modified
const SOL_SNAP = JSON.parse(JSON.stringify({ locs: LOCS, factions: FACTIONS, unlocks: UNLOCKS, projects: PROJECTS.map(p => ({ id: p.id, n: p.n, d: p.d, fx: p.fx })) }));

const SYSTEMS = {
  sol: {
    n: 'Sol', star: 'sol', rock: 1, enemy: 1, value: 1,
    boss: 'sentinel', bossFleet: ['sentinel', 'adrone', 'adrone', 'adrone'],
    signal: { title: 'A signal from the dark', text: 'Your deep-space dishes caught a <b>repeating signal</b> from the <b>Oort Cloud</b>, far beyond the Kuiper Belt. It is <b>not human</b>.' },
    gate: 'The Sentinel\'s core shatters — and deep in the Oort Cloud, a ring older than the Sun <b>lights up</b>. It is a <b>jump gate</b>.',
  },
  centauri: {
    n: 'Alpha Centauri', star: 'white', companion: 'orange', rock: 1.5, enemy: 1.35, value: 1,
    boss: 'queen', bossFleet: ['queen', 'swarmer', 'swarmer', 'swarmer'],
    signal: { title: 'Something is nesting', text: 'Probes beyond the Proxima Drift went silent one by one. The last image shows a <b>living nebula</b> — and something huge moving inside it: <b>the Hive</b>.' },
    gate: 'The Hive Queen bursts into glittering dust. In the heart of the nebula, a second ancient ring <b>wakes up</b>: the way deeper into the galaxy.',
    intro: 'You arrive through the gate at <b>Alpha Centauri</b>: two suns, crystal-rich belts and pirates <b>far tougher</b> than at home. Your fortune stayed behind — but your <b>Legacy</b> came with you.',
    factions: {
      tierra: { n: 'Pandora Accord', c: '#4fd8c0' }, marte: { n: 'Dune Clans', c: '#e8b46a' }, cinturon: { n: 'Prism Guild', c: '#c49cff' },
      exterior: { n: 'Typhon League', c: '#6aa8ff' }, piratas: { n: 'Red Market Cartel', c: '#ff4d6d' },
    },
    locs: {
      luna: { n: 'Tethys', station: 'First Light Base', tex: 'rock', col: ['#c9d2e8', '#4a5068'], desc: 'A quiet grey moon of Pandora. Your new beginning.',
        field: { n: 'Shepherd Rocks', ores: { iron: 4, titanium: 1.2, cobalt: 0.3, ice: 3 } } },
      tierra: { n: 'Pandora', station: 'Haven Port', tex: 'ocean', col: ['#7fe0a8', '#0b3a5c'], desc: 'A world of warm teal oceans under two suns. Pays well for every metal.' },
      venus: { n: 'Calypso', station: 'Orchid Spire', tex: 'gas', col: ['#f2d0ff', '#6a3a8a'], desc: 'A violet cloud world. Its floating cities crave luxury and ice.' },
      mercurio: { n: 'Cinder', station: 'Cinder Depot', tex: 'lava', col: ['#ffb060', '#4a1a0c'], desc: 'A molten world hugging Alpha Centauri A. Sunstone everywhere — and the heat.',
        field: { n: 'Glassfire Flats', ores: { titanium: 2, nickel: 2, sunstone: 2.5, iron: 1.5 }, crystal: 0.15 } },
      marte: { n: 'Dune', station: 'Sandgate', tex: 'rock', col: ['#f0c890', '#7a4a20'], desc: 'An endless desert ruled by proud clans. Water is worth more than gold here.' },
      ceres: { n: 'Halcyon', station: 'Prism Station', tex: 'rock', col: ['#d8c8ff', '#4a3a6a'], desc: 'Capital of the Shard Belt, where asteroids grow as crystals.',
        field: { n: 'Shard Belt', ores: { nickel: 2, he3: 2, platinum: 2.5, iridium: 1.1 }, crystal: 0.5 } },
      jupiter: { n: 'Typhon', tex: 'gas', col: ['#9ad8ff', '#1a3a8a'] },
      europa: { n: 'Nyx', station: 'Nyx Colony', tex: 'ice', col: ['#e8f6ff', '#5a7aa8'], desc: 'An ice moon of Typhon. The League buys iridium at any price.' },
      troyanos: { field: { n: 'Typhon Swarm', ores: { he3: 2.2, iridium: 3, ringpearl: 0.25 }, crystal: 0.2 }, station: 'Swarm Depot', desc: 'Rocks trapped in Typhon\'s gravity. Pirate nests everywhere.' },
      saturno: { n: 'Aurelia', tex: 'gas', col: ['#ffe0a0', '#9a5a20'], station: 'Halo Depot', desc: 'A golden ringed giant. Its rings are full of Ring Pearls.',
        field: { n: 'Aurelia Halo', ores: { ice: 2.5, he3: 3, ringpearl: 2.6, exotic: 0.6 }, crystal: 0.2 } },
      titan: { n: 'Mist', station: 'Mistport', tex: 'titan', col: ['#e0d0b0', '#6a5a40'], desc: 'A foggy moon of Aurelia with huge refineries.' },
      pluton: { n: 'Proxima b', station: 'Red Market', tex: 'rock', col: ['#ff9a80', '#4a1a14'], desc: 'A dim world orbiting the red dwarf Proxima. Anything is for sale.' },
      kuiper: { n: 'Proxima Drift', station: 'Drift Depot', desc: 'Frozen rocks drifting between the stars. Exotics — and the Cartel\'s carriers.',
        field: { n: 'Proxima Drift', ores: { ice: 1.5, iridium: 2.2, exotic: 2, voidshard: 0.1 } } },
      oort: { n: 'The Hive', station: 'Watchpost Omega', col: ['#b0ff9a', '#1a3a20'], desc: 'A living nebula. Something enormous breeds in its depths.',
        field: { n: 'Hive Nebula', ores: { ice: 3, ringpearl: 1.5, exotic: 2.2, voidshard: 0.42 } } },
    },
    unlocks: {
      0: { title: 'Tethys' }, 3: { title: 'Cinder & Dune', text: '<b>Cinder</b> burns with <b>Sunstone</b> but the heat eats your hull — buy <b>Shields</b>. <b>Dune</b> pays a fortune for ice.' },
      4: { title: 'The Shard Belt', text: '<b>Halcyon</b> and the <b>Shard Belt</b>: asteroids that grow as <b>crystals</b> and shatter into many shards when you break them. Catch them all! Pirates here are tougher than at home.' },
      6: { title: 'Typhon System', text: '<b>Nyx</b> and the <b>Typhon Swarm</b>: iridium everywhere. The <b>Scanner</b> reveals rich veins.' },
      7: { title: 'Aurelia & Influence', text: '<b>Mist</b> and the golden <b>Aurelia Halo</b>. <b>Invest</b> in stations: each level adds <b>+10% to ALL income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule Alpha Centauri.' },
      8: { title: 'Proxima', text: '<b>Proxima b</b>\'s Red Market and the <b>Proxima Drift</b>. Exotics and even <b>Void Shards</b>.' },
    },
    projects: {
      driver: { n: 'Tethys Mass Driver', d: 'A magnetic rail on Tethys hurls ore straight to Pandora.', fx: 'Tethys outpost output ×3' },
      elevator: { n: 'Pandora Space Elevator', d: 'A cable rising out of Pandora\'s oceans. Its industry is yours to supply.', fx: 'All ore sells for +25% everywhere' },
      terraform: { n: 'Terraform Dune', d: 'Comets, mirrors and seas poured onto the desert. Dune turns blue.', fx: 'Dune pays ×2 for everything · Dune Clans reputation +50' },
      ringstation: { n: 'Aurelia Halo Megastation', d: 'A city-sized refinery woven into Aurelia\'s golden rings.', fx: 'ALL drone income ×3' },
    },
  },
};

// the road to the core: 15 systems from the rim to the black hole
const GALAXY = [
  { id: 'sol', n: 'Sol', star: 'sol', x: -0.78, y: 0.42 },
  { id: 'centauri', n: 'Alpha Centauri', star: 'white', x: -0.62, y: 0.66 },
  { id: 'barnard', n: 'Barnard\'s Star', star: 'red', x: -0.30, y: 0.76 },
  { id: 'sirius', n: 'Sirius', star: 'white', x: 0.04, y: 0.72 },
  { id: 'tauceti', n: 'Tau Ceti', star: 'sol', x: 0.34, y: 0.56 },
  { id: 'eridani', n: 'Epsilon Eridani', star: 'orange', x: 0.56, y: 0.28 },
  { id: 'vega', n: 'Vega', star: 'blue', x: 0.62, y: -0.06 },
  { id: 'altair', n: 'Altair', star: 'white', x: 0.48, y: -0.36 },
  { id: 'kepler', n: 'Kepler', star: 'sol', x: 0.18, y: -0.52 },
  { id: 'rigel', n: 'Rigel', star: 'blue', x: -0.16, y: -0.46 },
  { id: 'betelgeuse', n: 'Betelgeuse', star: 'red', x: -0.38, y: -0.22 },
  { id: 'orion', n: 'Orion Nebula', star: 'blue', x: -0.36, y: 0.08 },
  { id: 'pulsar', n: 'The Pulsar', star: 'white', x: -0.14, y: 0.24 },
  { id: 'rim', n: 'Core Rim', star: 'orange', x: 0.12, y: 0.12 },
  { id: 'sgra', n: 'Sagittarius A*', star: 'hole', x: 0, y: 0 },
];
const sysId = () => (S && S.sys) || 'sol';
const sysDef = () => SYSTEMS[sysId()];
const sysName = () => sysDef().n;
const nextSystem = () => GALAXY[GALAXY.findIndex(g => g.id === sysId()) + 1];

// rebuild the world for a star system: start from Sol, then apply that system's overrides
function applySystem(id) {
  const D = SYSTEMS[id] || SYSTEMS.sol, base = SOL_SNAP;
  for (const l of LOCS) {
    const b = base.locs.find(x => x.id === l.id), o = (D.locs || {})[l.id] || {};
    for (const k of Object.keys(l)) if (k !== 'id') delete l[k];
    Object.assign(l, JSON.parse(JSON.stringify(b)), JSON.parse(JSON.stringify({ ...o, field: undefined })));
    if (b.field || o.field) l.field = { ...(b.field || {}), ...(o.field || {}) };
    if (!l.field || !Object.keys(l.field).length) delete l.field;
  }
  for (const f in FACTIONS) Object.assign(FACTIONS[f], base.factions[f], (D.factions || {})[f] || {});
  UNLOCKS.forEach((u, i) => Object.assign(u, base.unlocks[i], (D.unlocks || {})[i] || {}));
  for (const p of PROJECTS) Object.assign(p, base.projects.find(x => x.id === p.id), (D.projects || {})[p.id] || {});
  FIELDS.splice(0, FIELDS.length, ...NODES.filter(l => l.field));
  for (const k in TEX) delete TEX[k];
  snapshotLocBase();
  if (S) applyNukes();
}
// old saves (and new ores) may lack market entries: make sure every market item has a price state
function ensureMarkets() {
  for (const l of NODES) if (l.market) {
    S.sat[l.id] = S.sat[l.id] || {}; S.drift[l.id] = S.drift[l.id] || {};
    for (const k in l.market) { if (S.sat[l.id][k] == null) S.sat[l.id][k] = 1; if (S.drift[l.id][k] == null) S.drift[l.id][k] = 0; }
  }
}

// ---------- Tribute & Legacy ----------
const LEGACY = {
  ore:       { icon: '⛏', n: 'Prospector\'s Legacy', d: '+10% ore value everywhere', cost: lv => Math.round(8 * Math.pow(1.6, lv)) },
  drones:    { icon: '🤖', n: 'Drone Blueprints', d: 'Drones cost 8% less', cost: lv => Math.round(6 * Math.pow(1.6, lv)) },
  fuel:      { icon: '⛽', n: 'Efficient Drives', d: 'Fuel costs 8% less', cost: lv => Math.round(4 * Math.pow(1.5, lv)) },
  quick:     { icon: '🗺', n: 'Head Start', d: 'Start each system with the Star Map open and 50K credits', max: 1, cost: () => 15 },
  laserPlan: { icon: '✦', n: 'Laser Plans', d: 'Start each system with +5 laser levels', max: 3, cost: lv => 6 * Math.pow(2, lv) },
  cargoPlan: { icon: '▣', n: 'Cargo Plans', d: 'Start each system with +5 cargo bay levels', max: 3, cost: lv => 6 * Math.pow(2, lv) },
  extrPlan:  { icon: '⚗', n: 'Extractor Plans', d: 'Start each system with +5 extractor levels', max: 3, cost: lv => 6 * Math.pow(2, lv) },
};
const legacyLv = k => (S && S.galaxy && S.galaxy.legacy[k]) || 0;
const conquered = () => (S && S.galaxy ? S.galaxy.done.length : 0);
const tributeRate = () => conquered();   // per minute: each conquered system pays 1 Tribute a minute
function tributeTick(dt) { if (S && S.galaxy && conquered()) S.galaxy.tribute += tributeRate() * dt / 60; }
function buyLegacy(k) {
  const L = LEGACY[k], G = S.galaxy, lv = G.legacy[k] || 0;
  if (L.max && lv >= L.max) return false;
  const c = L.cost(lv); if (G.tribute < c) return false;
  G.tribute -= c; G.legacy[k] = lv + 1; save(); return true;
}
// one-off Tribute for leaving a system: the more you achieved there, the more it pays
function jumpBonus() {
  let b = 10, why = ['base 10'];
  if (S.gateOpen) { b += 5; why.push('final boss +5'); }
  const st = Object.values(S.allies || {}).reduce((a, x) => a + x, 0); if (st) { b += 3 * st; why.push(`ally stars +${3 * st}`); }
  const pj = Object.keys(S.projects || {}).length; if (pj) { b += 2 * pj; why.push(`megaprojects +${2 * pj}`); }
  return { b, why };
}
function jumpTo(id) {
  const D = SYSTEMS[id]; if (!D || !S.gateOpen) return false;
  const G = S.galaxy || { tribute: 0, legacy: {}, done: [], life: { earned: 0, mined: 0, kills: 0, days: 0 } };
  const from = sysId(), bonus = jumpBonus().b;
  if (!G.done.includes(from)) G.done.push(from);
  G.tribute += bonus;
  G.life.earned += S.stats.earned; G.life.mined += S.stats.mined; G.life.kills += S.stats.kills; G.life.days += S.day;
  const peak = S.stats.peak || 0, muted = S.muted;
  S = null;
  applySystem(id);
  newGame();
  Object.assign(S, { sys: id, galaxy: G, muted }); S.stats.peak = peak;
  // Legacy start bonuses
  S.lv.laser += 5 * (G.legacy.laserPlan || 0); S.lv.cargo += 5 * (G.legacy.cargoPlan || 0); S.lv.extractor += 5 * (G.legacy.extrPlan || 0);
  if (G.legacy.quick) { S.credits = 50000; S.stats.earned = UNLOCKS[U.MAP].at; checkUnlocks(); pendingUnlocks = []; }
  S.fuel = ship.fuelMax; S.hull = ship.hpMax;
  S.news = []; addNews('🌀', `You came through the gate to <b>${D.n}</b>. A new system to conquer.`, '#d9b3ff');
  save();
  shownCredits = S.credits;
  setScene(MineScene, 'luna');
  updateHUD(); updateTicker();
  setTimeout(() => showModal({ icon: '🌀', title: `Welcome to ${D.n}`, cls: 'unlock', html: `<div class="unl-tag">SYSTEM ${GALAXY.findIndex(g => g.id === id) + 1} / ${GALAXY.length}</div><p>${D.intro || ''}</p><p class="hint">+${bonus} Tribute for leaving ${SYSTEMS[from].n}. Conquered systems keep paying Tribute every minute — spend it on Legacy in the <b>Galaxy</b> map.</p>`, buttons: [{ label: 'Let\'s mine', cls: 'primary', fn: () => {} }] }), 400);
  return true;
}

// ---------- the final boss of each system opens its gate ----------
function finalBossKilled() {
  if (S.gateOpen) return;
  S.gateOpen = 1;
  const nx = nextSystem();
  addNews('🌀', `<b>The guardian is destroyed.</b> An ancient jump gate wakes up in ${LOC.oort.n}.`, '#d9b3ff');
  if (typeof pendingChoices !== 'undefined') pendingChoices.push({ icon: '🌀', title: 'The gate awakens', html: `<p>${sysDef().gate}</p><p>Open the <b>Galaxy</b> map to see where it leads${nx ? ` — next stop: <b>${nx.n}</b>` : ''}. You can stay as long as you like: the more you achieve here, the more <b>Tribute</b> you take with you.</p>`, choices: [{ label: 'Open the Galaxy map', cost: 0, fn: () => setTimeout(() => setScene(GalaxyScene), 50) }, { label: 'Later', cost: 0, fn: () => {} }] });
  save();
}

// ---------- the Galaxy map ----------
const GalaxyScene = {
  t: 0, sel: null, dust: null, prev: null,
  enter() {
    this.prev = this.prev || MapScene;
    if (!this.dust) {
      let s = 7; const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
      this.dust = Array.from({ length: 1400 }, () => {
        const arm = Math.floor(r() * 3), d = Math.pow(r(), 0.7), a = arm * TAU / 3 + d * 5.2 + (r() - 0.5) * 0.7 * (1 - d * 0.5);
        return { a, d, s: r() * 1.6 + 0.4, c: r() < 0.15 ? '#ffd2f0' : r() < 0.4 ? '#bcd4ff' : '#ffffff', o: r() * 0.6 + 0.2 };
      });
    }
    this.sel = this.sel || (nextSystem() || GALAXY[0]).id;
    document.body.classList.add('galaxy');
    $('galPanel').classList.remove('hidden');
    renderGalaxyPanel();
  },
  exit() { document.body.classList.remove('galaxy'); $('galPanel').classList.add('hidden'); },
  update(dt) { this.t += dt; },
  layout() { const wide = W > 760; const R = wide ? Math.min(W * 0.72, H) * 0.46 : Math.min(W * 0.45, (H * 0.44 - 90) / 1.8); return { cx: W * (wide ? 0.36 : 0.5), cy: wide ? H * 0.52 : 82 + R * 0.8, R }; },
  pos(g) { const { cx, cy, R } = this.layout(); return { x: cx + g.x * R, y: cy + g.y * R }; },
  draw(ctx) {
    const t = this.t, { cx, cy, R } = this.layout();
    drawSpaceBg(ctx, W, H, t * 4, t * 2, t);
    // spiral arms
    for (const p of this.dust) {
      const a = p.a + t * 0.01, r = p.d * R * 1.15;
      ctx.globalAlpha = p.o * (0.4 + 0.6 * (1 - p.d)); ctx.fillStyle = p.c;
      ctx.fillRect(cx + Math.cos(a) * r, cy + Math.sin(a) * r * 0.92, p.s, p.s);
    }
    ctx.globalAlpha = 1;
    glow(ctx, cx, cy, R * 0.5, '#ffb07a33', 0.9);
    // the route
    const done = (S.galaxy && S.galaxy.done) || [], cur = sysId();
    for (let i = 0; i < GALAXY.length - 1; i++) {
      const a = this.pos(GALAXY[i]), b = this.pos(GALAXY[i + 1]);
      const lit = done.includes(GALAXY[i].id) || GALAXY[i].id === cur;
      ctx.strokeStyle = lit ? 'rgba(217,179,255,0.55)' : 'rgba(140,160,220,0.18)'; ctx.lineWidth = lit ? 2 : 1;
      ctx.setLineDash(lit ? [] : [4, 6]); ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
    }
    ctx.setLineDash([]);
    // stars
    for (const g of GALAXY) {
      const p = this.pos(g), isDone = done.includes(g.id), isCur = g.id === cur, ready = !!SYSTEMS[g.id], sel = g.id === this.sel;
      if (g.star === 'hole') {
        glow(ctx, p.x, p.y, 46, '#ff9a5a55', 0.9);
        for (let k = 0; k < 3; k++) { ctx.strokeStyle = `rgba(255,${170 - k * 30},${90 - k * 20},${0.7 - k * 0.2})`; ctx.lineWidth = 3 - k; ctx.beginPath(); ctx.ellipse(p.x, p.y, 22 + k * 7, 8 + k * 3, t * 0.2, 0, TAU); ctx.stroke(); }
        ctx.fillStyle = '#000'; ctx.beginPath(); ctx.arc(p.x, p.y, 10, 0, TAU); ctx.fill();
      } else {
        ctx.globalAlpha = ready || isDone ? 1 : 0.45;
        drawSun(ctx, p.x, p.y, isCur ? 7 : 5, t, g.star);
        ctx.globalAlpha = 1;
      }
      if (isDone) { ctx.strokeStyle = '#ffd24a'; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(p.x, p.y, 14, 0, TAU); ctx.stroke(); }
      if (isCur) { const ph = (t * 0.8) % 1; ctx.globalAlpha = 1 - ph; ctx.strokeStyle = '#3de8ff'; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(p.x, p.y, 14 + ph * 16, 0, TAU); ctx.stroke(); ctx.globalAlpha = 1; }
      if (sel) { ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 1.5; ctx.setLineDash([3, 4]); ctx.beginPath(); ctx.arc(p.x, p.y, 20, 0, TAU); ctx.stroke(); ctx.setLineDash([]); }
      // on phones only the important names fit
      if (W <= 760 && !isCur && !sel && !(nextSystem() && g.id === nextSystem().id) && g.star !== 'hole') { if (!ready && !isDone && g.star !== 'hole') drawIcon(ctx, 'lock', p.x, p.y - 12, 8, 'rgba(200,210,240,0.5)'); continue; }
      ctx.font = `700 ${isCur || sel ? 12 : 11}px Rajdhani, sans-serif`; ctx.textAlign = 'center';
      ctx.fillStyle = isCur ? '#3de8ff' : isDone ? '#ffd24a' : ready ? '#e8f1ff' : 'rgba(200,210,240,0.5)';
      ctx.fillText(g.n.toUpperCase(), p.x, p.y + 30);
      if (!ready && !isDone && g.star !== 'hole') drawIcon(ctx, 'lock', p.x, p.y - 18, 10, 'rgba(200,210,240,0.6)');
    }
  },
  onDown(x, y) {
    let best = null, bd = 30;
    for (const g of GALAXY) { const p = this.pos(g), d = Math.hypot(p.x - x, p.y - y); if (d < bd) { bd = d; best = g.id; } }
    if (best) { this.sel = best; sfx('click'); renderGalaxyPanel(); }
  },
};
function renderGalaxyPanel() {
  const G = S.galaxy, g = GALAXY.find(x => x.id === GalaxyScene.sel), i = GALAXY.indexOf(g);
  const done = G ? G.done : [], cur = sysId(), nx = nextSystem();
  let h = `<div class="lp-head"><div><h3>The Galaxy</h3><small>${done.length} of ${GALAXY.length} systems conquered</small></div><button class="x" onclick="closeGalaxy()">✕</button></div>`;
  h += `<div class="gal-trib"><div><small>TRIBUTE</small><b>${Math.floor(G ? G.tribute : 0)}</b></div><span>${conquered() ? `+${tributeRate()} / min from ${conquered()} conquered system${conquered() > 1 ? 's' : ''}` : 'Conquer a system to earn Tribute'}</span></div>`;
  // selected star
  h += `<div class="sub">${g.n} <small class="dim">· system ${i + 1}</small></div>`;
  if (g.id === cur) h += `<p class="hint">You are here.${S.gateOpen ? '' : ' Rule this system and defeat its guardian to open the gate.'}</p>`;
  else if (done.includes(g.id)) h += `<p class="hint">Conquered. It pays you Tribute every minute.</p>`;
  else if (g.star === 'hole') h += `<p class="hint">The supermassive black hole at the heart of the galaxy. The end of the road — and maybe a door to something beyond.</p>`;
  else if (!SYSTEMS[g.id]) h += `<p class="hint">Uncharted. Arrives in a future update.</p>`;
  if (nx && g.id === nx.id) {
    const jb = jumpBonus();
    if (!SYSTEMS[nx.id]) h += `<p class="hint">The gate points here, but this system isn't charted yet — coming in a future update.</p>`;
    else if (!S.gateOpen) h += `<p class="hint">🔒 Defeat ${sysName()}'s guardian to open the gate.</p>`;
    else h += `<p class="hint">Jumping now gives <b>+${jb.b} Tribute</b> <small>(${jb.why.join(', ')})</small>. Your credits, ship upgrades, outposts and freighters stay behind; Tribute, Legacy and your records come with you.</p>
      <button class="btn primary big" onclick="confirmJump('${nx.id}')">🌀 Jump to ${nx.n}</button>`;
  }
  // legacy shop
  if (G) {
    h += '<div class="sub">Legacy <small class="dim">· permanent, all systems</small></div><div class="legacy">';
    for (const k in LEGACY) {
      const L = LEGACY[k], lv = G.legacy[k] || 0, maxed = L.max && lv >= L.max, c = L.cost(lv);
      h += `<div class="lg-row"><span>${L.icon} <b>${L.n}</b> ${L.max === 1 ? (lv ? '<small class="good">owned</small>' : '') : `<small>Lv ${lv}${L.max ? '/' + L.max : ''}</small>`}<br><small class="dim">${L.d}</small></span>
        <button class="btn small-btn" ${maxed || G.tribute < c ? 'disabled' : ''} onclick="buyLegacy('${k}') && (sfx('upgrade'), renderGalaxyPanel())">${maxed ? 'Max' : `${c} ⬢`}</button></div>`;
    }
    h += '</div>';
  } else h += '<p class="hint">Legacy upgrades unlock after your first jump: spend Tribute on permanent bonuses for every system.</p>';
  $('galPanel').innerHTML = h;
}
function openGalaxy() { sfx('click'); closeSheet(true); GalaxyScene.prev = scene === GalaxyScene ? GalaxyScene.prev : scene === MineScene ? null : scene; setScene(GalaxyScene); }
function closeGalaxy() { sfx('click'); setScene(has(U.MAP) ? MapScene : MineScene, has(U.MAP) ? undefined : S.loc); }
function confirmJump(id) {
  const D = SYSTEMS[id];
  showModal({ icon: '🌀', title: `Jump to ${D.n}?`, html: `<p>Everything you built in <b>${sysName()}</b> stays behind and becomes part of your empire: it pays <b>Tribute</b> every minute.</p><p>You start fresh in ${D.n}: credits, ship upgrades, outposts, freighters and reputation reset. You keep <b>Tribute, Legacy, alliances history and your records</b>.</p><p class="hint">Pirates and rocks are tougher there — but ore is worth more.</p>`,
    buttons: [{ label: 'Jump!', cls: 'primary', fn: () => { sfx('win'); jumpTo(id); } }, { label: 'Not yet', fn: () => {} }] });
}
