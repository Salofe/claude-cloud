const { open, run, record } = require('./lib.cjs');
const ev = (p, f, a) => p.evaluate(f, a);
const ORDER = ['centauri', 'barnard', 'sirius', 'tauceti', 'eridani', 'vega', 'altair', 'kepler', 'rigel', 'betelgeuse', 'orion', 'pulsar', 'rim', 'sgra'];
const upTo = id => ORDER.slice(0, ORDER.indexOf(id) + 1);
const ALLPROJ = ['driver', 'beacons', 'elevator', 'fleet', 'terraform', 'ringstation', 'dyson', 'nova'];
// arrive in a system as a strong pilot
const arrive = async (p, id, o = {}) => {
  await ev(p, ([chain, o]) => { T.start(); T.jumpChain(chain); T.late(Object.assign({ lv: { hull: 4, laser: 45, weapons: 45, shield: 40, magnet: 20 } }, o)); T.cinema(); }, [upTo(id), o]);
  await run(p, 800); await ev(p, () => T.clean());
};
const boss = async (p, id, sec = 7, field = 'oort') => {
  await arrive(p, id);
  await ev(p, f => { S.gateOpen = 0; T.mine(f); MineScene.p.y = DOCK_Y - 1500; MineScene.cam.y = MineScene.p.y; MineScene.ambush = { at: 0.4, warned: false, boss: 'final' }; T.pilot(); }, field);
  await bossWait(p);
  await record(p, 'boss-' + id, sec, bossKeep(p, sec));
};
const bossWait = async p => { for (let k = 0; k < 80; k++) { await run(p, 100); if (await ev(p, () => MineScene.enemies.length > 0)) break; } await run(p, 700); };
const bossKeep = (p, sec) => i => ev(p, ([i, n]) => {
  S.hull = ship.hpMax; T.clean();
  const big = MineScene.enemies.slice().sort((a, b) => b.max - a.max)[0];
  if (big && i < n - 48) big.hp = Math.max(big.hp, big.max * (0.75 - 0.45 * i / n));
}, [i, Math.round(sec * 30)]);
const sysMap = async (p, id) => {
  await arrive(p, id, { projects: [] });
  await run(p, 1500);
  await ev(p, () => { T.clean(); setScene(MapScene); hideLocPanel(); MapScene.zoomAll(); });
  await run(p, 2000);
  await ev(p, () => { T.clean(); hideLocPanel(); window.__z0 = (MapScene.camT || MapScene.cam).z; MapScene.camT = null; });
  await record(p, 'map-' + id, 3.5, i => ev(p, i => { T.clean(); MapScene.cam.x = 0; MapScene.cam.y = 0; MapScene.cam.z = __z0 * (1.35 + 0.35 * i / 105); }, i));
};
const sysMine = async (p, id, loc, sec = 4) => {
  await arrive(p, id);
  await ev(p, loc => { T.mine(loc); T.nearRocks(220); T.pilot(); }, loc);
  await run(p, 1500);
  await record(p, 'mine-' + id, sec);
};
const SHOTS = {
  async 'title-bg'(p) {
    await ev(p, () => { const st = document.createElement('style'); st.textContent = '#title .tbox{display:none!important}'; document.head.appendChild(st); });
    await run(p, 300);
    await record(p, 'title-bg', 10.5);
  },
  // ---------- first 15 min ----------
  async 'mine-early'(p) {
    await ev(p, () => { T.start(); T.cinema(); });
    await run(p, 600); await ev(p, () => { Object.assign(S.lv, { laser: 6, magnet: 4 }); T.nearRocks(200); T.pilot(); });
    await run(p, 1500);
    await record(p, 'mine-early', 7);
  },
  async 'dock-sell'(p) {
    await ev(p, () => { T.start(); T.hideUI(); S.stats.docks = 1; S.cargo = { titanium: 9, ice: 6, iron: 5 }; MineScene.leave(); });
    await run(p, 300);
    await record(p, 'dock-sell', 5, async i => { if (i === 60 || i === 95) await ev(p, () => { const b = document.querySelector('.upg .btn.primary:not([disabled])'); if (b) b.click(); }); });
  },
  // ---------- after 15 min: Sol empire ----------
  async 'mine-rich'(p) {
    await ev(p, () => { T.start(); T.late({ lv: { hull: 3 } }); T.cinema(); T.mine('mercurio'); T.nearRocks(220); T.pilot(); });
    await run(p, 1500);
    await record(p, 'mine-rich', 6);
  },
  async 'mine-saturn'(p) {
    await ev(p, () => { T.start(); T.late({ lv: { hull: 4 } }); T.cinema(); T.mine('saturno'); T.nearRocks(220); T.pilot(); });
    await run(p, 1500);
    await record(p, 'mine-saturn', 6);
  },
  async 'map-travel'(p) {
    await ev(p, () => { T.start(); T.late({ outposts: 1, projects: ['driver', 'elevator', 'fleet', 'ringstation', 'dyson'] }); T.cinema(); S.loc = 'tierra'; setScene(MapScene); MapScene.zoomAll(); });
    await run(p, 2000);
    await record(p, 'map-travel', 6, async i => { if (i === 6) await ev(p, () => { MapScene.startTravel('saturno'); if (MapScene.travel) MapScene.travel.dur = 7; }); });
  },
  async 'empire'(p) {
    await ev(p, () => { T.start(); T.late({ outposts: 1, projects: ['driver', 'beacons'] }); T.hideUI(); S.loc = 'tierra'; setScene(MapScene); MapScene.zoomAll(); });
    await run(p, 1200);
    await ev(p, () => $('bFac').click());
    await run(p, 400);
    await record(p, 'empire', 4);
  },
  async 'projects'(p) {
    await ev(p, () => { T.start(); T.late({ outposts: 1, projects: ['driver', 'beacons', 'elevator'] }); S.credits = 5e13; T.hideUI(); S.loc = 'tierra'; setScene(MapScene); MapScene.zoomAll(); });
    await run(p, 1200);
    await ev(p, () => $('bProj').click());
    await run(p, 400);
    await record(p, 'projects', 4);
  },
  async 'map-dyson'(p) {
    await ev(p, () => { T.start(); T.late({ outposts: 1, projects: ['driver', 'beacons', 'elevator', 'fleet', 'terraform', 'ringstation', 'dyson'] }); T.cinema(); S.loc = 'tierra'; setScene(MapScene); MapScene.camT = null; });
    await run(p, 300);
    await record(p, 'map-dyson', 5, i => ev(p, i => { T.clean(); MapScene.camT = null; MapScene.cam.x = 0; MapScene.cam.y = 0; MapScene.cam.z = 4.2 * Math.pow(1.5 / 4.2, Math.min(1, i / 140)); }, i));
  },
  async 'pirates'(p) {
    await ev(p, () => { T.start(); T.late({ lv: { weapons: 14, shield: 25 } }); T.cinema(); T.mine('troyanos'); T.nearRocks(300); MineScene.ambush = { at: 1.2, warned: false }; T.pilot(); });
    await run(p, 1000);
    await record(p, 'pirates', 6);
  },
  async 'boss-sol'(p) {
    await ev(p, () => { T.start(); T.late({ lv: { hull: 4, weapons: 40, shield: 40 } }); T.cinema(); T.mine('oort'); MineScene.p.y = DOCK_Y - 1500; MineScene.cam.y = MineScene.p.y; MineScene.ambush = { at: 0.4, warned: false, boss: 'final' }; T.pilot(); });
    await bossWait(p);
    await record(p, 'boss-sol', 8, bossKeep(p, 8));
  },
  // ---------- the galaxy ----------
  async 'jump'(p) {
    await ev(p, () => { T.start(); T.late({ lv: { hull: 4 } }); T.clean(); S.gateOpen = 1; setScene(JumpScene, 'centauri'); });
    await record(p, 'jump', 6, () => ev(p, () => { T.clean(); T.cinema(); }));
  },
  async 'galaxy'(p) {
    await ev(p, chain => { T.start(); T.jumpChain(chain); T.late(); T.cinema(); }, upTo('kepler'));
    await run(p, 1500); await ev(p, () => { T.clean(); setScene(GalaxyScene); });
    await run(p, 800); await ev(p, () => T.clean());
    await record(p, 'galaxy', 5);
  },
  async 'welcome-sirius'(p) {
    await ev(p, chain => { T.start(); T.jumpChain(chain.slice(0, -1)); T.late(); S.gateOpen = 1; jumpTo(chain[chain.length - 1]); }, upTo('sirius'));
    await run(p, 300);
    await record(p, 'welcome-sirius', 4);
  },
  'map-centauri': p => sysMap(p, 'centauri'),
  'map-barnard': p => sysMap(p, 'barnard'),
  'map-tauceti': p => sysMap(p, 'tauceti'),
  'map-eridani': p => sysMap(p, 'eridani'),
  'map-altair': p => sysMap(p, 'altair'),
  'map-kepler': p => sysMap(p, 'kepler'),
  'map-orion': p => sysMap(p, 'orion'),
  'map-pulsar': p => sysMap(p, 'pulsar'),
  'map-rim': p => sysMap(p, 'rim'),
  'map-sgra': p => sysMap(p, 'sgra'),
  'mine-kepler': p => sysMine(p, 'kepler', 'ceres'),
  'mine-orion': p => sysMine(p, 'orion', 'ceres'),
  'mine-pulsar': p => sysMine(p, 'pulsar', 'ceres'),
  'mine-betelgeuse': p => sysMine(p, 'betelgeuse', 'ceres'),
  'boss-sirius': p => boss(p, 'sirius'),
  'boss-vega': p => boss(p, 'vega'),
  'boss-rigel': p => boss(p, 'rigel'),
  'boss-betelgeuse': p => boss(p, 'betelgeuse'),
  'boss-rim': p => boss(p, 'rim'),
  'boss-sgra': p => boss(p, 'sgra', 9),
};
(async () => {
  const want = process.argv.slice(2);
  for (const [name, fn] of Object.entries(SHOTS)) {
    if (want.length && !want.includes(name)) continue;
    const p = await open();
    try { await fn(p); } catch (e) { console.log('FAIL', name, e.message.split('\n')[0]); }
    await p.browser_.close();
  }
})();
