// injected into the game page: helpers to stage trailer shots (runs on the virtual clock)
window.T = {
  start() { closeModal(); if (scene === TitleScene) $('newg').click(); closeModal(); pendingUnlocks = []; },
  clean() { closeModal(); pendingUnlocks = []; if (typeof pendingChoices !== 'undefined') pendingChoices.length = 0; },
  // a well-developed Sol (or other system) run
  late(o = {}) {
    T.clean();
    earn(o.earn || 2e9); S.credits = o.cr || 8e8; checkUnlocks(); T.clean();
    Object.assign(S.lv, { hull: 3, extractor: 18, laser: 30, magnet: 14, cargo: 20, refinery: 25, engine: 12, tank: 10, shield: 20, weapons: 25, scanner: 3 }, o.lv || {});
    S.hull = ship.hpMax; S.fuel = ship.fuelMax;
    if (o.outposts) for (const f of FIELDS) if (locOpen(f.id)) { buildOutpost(f.id); buyDrones(f.id, 'max'); }
    if (o.projects) for (const id of o.projects) buildProject(id);
    S.credits = o.cr || 8e8; T.clean(); updateHUD();
  },
  hideUI(on = true) {
    let st = document.getElementById('T-css'); if (!st) { st = document.createElement('style'); st.id = 'T-css'; document.head.appendChild(st); }
    st.textContent = on ? '#toasts,#coach,#eventBanner,#objective,#warHud,#mapTools,#locPanel,#galPanel{display:none!important}' : '';
  },
  hideHUD(on = true) {
    let st = document.getElementById('T-css2'); if (!st) { st = document.createElement('style'); st.id = 'T-css2'; document.head.appendChild(st); }
    st.textContent = on ? '#hud,#mineUI,#mapUI,.topbar,#toasts,#coach{display:none!important}' : '';
    T.noMinimap = on;
  },
  // clean cinematic frames: no HUD panels, no minimap (canvas effects, floaters and boss bars stay)
  cinema(on = true) {
    let st = document.getElementById('T-css3'); if (!st) { st = document.createElement('style'); st.id = 'T-css3'; document.head.appendChild(st); }
    st.textContent = on ? '#hud,#mineUI,#toasts,#coach,#eventBanner,#mapTools,#locPanel,#galPanel,#touchUI{display:none!important}' : '';
    window.NO_MINIMAP = on;
  },
  mine(loc) { T.clean(); S.loc = loc; setScene(MineScene, loc); T.clean(); },
  // simple autopilot: chase ore, laser the nearest rock, shoot enemies
  pilot(mode = 'mine') {
    clearInterval(T._pi);
    T._pi = setInterval(() => {
      if (scene !== MineScene) { joy.active = false; touchFire = false; return; }
      const M = MineScene, P = M.p;
      const en = (M.enemies || []).filter(e => e.hp > 0);
      if (en.length && mode !== 'calm') {
        let best = en[0], bd = 1e9; for (const e of en) { const d = Math.hypot(e.x - P.x, e.y - P.y); if (d < bd) { bd = d; best = e; } }
        const far = bd > 360; joy.active = far; if (far) { joy.dx = (best.x - P.x) / bd; joy.dy = (best.y - P.y) / bd; }
        touchFire = true; return;
      }
      if (M.chunks.some(ch => !ch.cr || true)) { const ch = M.chunks.slice().sort((a, b) => Math.hypot(a.x - P.x, a.y - P.y) - Math.hypot(b.x - P.x, b.y - P.y))[0]; if (ch) { const d = Math.hypot(ch.x - P.x, ch.y - P.y); if (d < 220 && d > 30 && Math.random() < 0.5) { joy.active = true; joy.dx = (ch.x - P.x) / d; joy.dy = (ch.y - P.y) / d; touchFire = true; return; } } }
      let best = null, bd = 1e9; for (const r of M.rocks) { const d = Math.hypot(r.x - P.x, r.y - P.y) - r.r; if (d < bd) { bd = d; best = r; } }
      if (!best) { joy.active = false; touchFire = false; return; }
      const far = bd > M.toolRange() * 0.55;
      joy.active = far; if (far) { joy.dx = (best.x - P.x) / (bd + best.r); joy.dy = (best.y - P.y) / (bd + best.r); }
      touchFire = true;
    }, 50);
  },
  stop() { clearInterval(T._pi); joy.active = false; touchFire = false; },
  // put the ship next to rocks so the shot starts in the action
  nearRocks(dy = 240) {
    const M = MineScene; const r = M.rocks.slice().sort((a, b) => b.r - a.r).find(r => r.y < DOCK_Y - 400) || M.rocks[0];
    if (!r) return; M.p.x = r.x + 40; M.p.y = r.y + dy; M.p.vx = M.p.vy = 0; M.cam.x = M.p.x; M.cam.y = M.p.y - 60;
  },
  jumpChain(list) { for (const s of list) { T.clean(); S.gateOpen = 1; jumpTo(s); T.clean(); } },
};
