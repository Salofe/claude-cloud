'use strict';
// ============ ESCENA: COMBATE AUTOMÁTICO ============
const BattleScene = {
  t: 0, parts: new Particles(), shots: [], ended: false, speed: 1, prev: null, done: null, log: [],
  start(fleet, enemyFirst, done) {
    this.prev = scene; this.done = done; this.t = 0; this.ended = false; this.speed = 1; this.shots = []; this.parts = new Particles(); this.log = [];
    this.fleetKeys = fleet;
    this.pl = { hp: S.hull, max: ship.hpMax, sp: ship.shieldMax, spMax: ship.shieldMax, dps: ship.weaponDps, cd: enemyFirst ? 1.2 : 0.4, shT: 0, x: 0, y: 0, hitT: 0, dead: false,
      guns: Math.max(1, S.lv.weapons), evade: 0.04 + S.lv.engine * 0.03, retreatT: 0 };
    this.en = fleet.map((k, i) => {
      const e = ENEMIES[k]; const sc = 1 + S.day / 400;
      return { k, n: e.n, hp: e.hp * sc, max: e.hp * sc, sp: e.sp * sc, spMax: e.sp * sc, dps: e.dps * sc, cd: enemyFirst ? rand(0.1, 0.5) : rand(0.6, 1.4), shT: 0, idx: i, hitT: 0, dead: false, bob: rand(0, TAU), evade: 0.06 };
    });
    this.drones = Array.from({ length: ship.drones }, (_, i) => ({ a: i * TAU / Math.max(1, ship.drones), cd: rand(0.3, 1) }));
    setScene(this);
  },
  enter() { showBattleUI(true); sfx('alarm'); },
  exit() { showBattleUI(false); },
  layout() {
    const pl = this.pl;
    pl.x = W * (W < 700 ? 0.22 : 0.26); pl.y = H * 0.52;
    const alive = this.en;
    alive.forEach((e, i) => {
      const n = alive.length;
      e.x = W * (W < 700 ? 0.75 : 0.72) + (i % 2) * 50 * (W < 700 ? 0.6 : 1);
      e.y = H * 0.52 + (i - (n - 1) / 2) * Math.min(95, H * 0.6 / n);
    });
  },
  fire(from, to, dmg, col, isPl) {
    const sx = from.x + (isPl ? 30 : -25), sy = from.y + rand(-6, 6);
    this.shots.push({ x: sx, y: sy, sx, sy, tx: to.x + rand(-8, 8), ty: to.y + rand(-8, 8), t: 0, dur: 0.35, dmg, col, to, isPl });
    sfx(isPl ? 'shoot' : 'eshoot');
  },
  applyHit(target, dmg, isPl) {
    if (target.dead) return;
    if (Math.random() < target.evade) { this.floatTxt(target.x, target.y - 30, 'MISS', '#9fb6ff'); return; }
    target.shT = 2.5;
    if (target.sp > 0) {
      const a = Math.min(target.sp, dmg); target.sp -= a; dmg -= a;
      this.parts.burst(target.x, target.y, 6, '#3de8ff', 80, 0.4, 2);
      target.shieldFlash = 0.3; sfx('shield');
    }
    if (dmg > 0) {
      target.hp -= dmg; target.hitT = 0.12;
      this.parts.burst(target.x + rand(-10, 10), target.y + rand(-8, 8), 8, isPl ? '#ffb347' : '#ff934a', 110, 0.5, 2.5);
      sfx('hit');
    }
    this.floatTxt(target.x, target.y - 30, Math.round(dmg > 0 ? dmg : 0) || 'shield', dmg > 0 ? '#ffffff' : '#3de8ff');
    if (target.hp <= 0) {
      target.dead = true; target.hp = 0;
      this.parts.burst(target.x, target.y, 50, '#ffb347', 260, 1.1, 4);
      this.parts.burst(target.x, target.y, 25, '#ffffff', 180, 0.6, 3);
      sfx('boom'); this.shake = 10;
    }
  },
  floats: [],
  floatTxt(x, y, txt, col) { this.floats.push({ x: x + rand(-15, 15), y, txt, col, life: 0.9 }); },
  update(dt) {
    this.layout();
    this.t += dt;
    const sdt = dt * this.speed;
    this.parts.update(sdt);
    for (const f of this.floats) { f.y -= 40 * sdt; f.life -= sdt; }
    this.floats = this.floats.filter(f => f.life > 0);
    this.shake = Math.max(0, (this.shake || 0) - dt * 25);
    for (const s of this.shots) {
      s.t += sdt;
      const k = Math.min(1, s.t / s.dur);
      s.x = lerp(s.sx, s.tx, k); s.y = lerp(s.sy, s.ty, k);
      if (k >= 1 && !s.done) { s.done = true; this.applyHit(s.to, s.dmg, !s.isPl); }
    }
    this.shots = this.shots.filter(s => !s.done);
    if (this.ended) return;
    const pl = this.pl, alive = this.en.filter(e => !e.dead);
    if (!alive.length) return this.finish(true);
    if (pl.hp <= 0) { pl.dead = true; return this.finish(false); }
    // escudos
    for (const u of [pl, ...alive]) {
      u.shT -= sdt; u.hitT -= sdt; if (u.shieldFlash) u.shieldFlash -= sdt;
      if (u.shT <= 0 && u.spMax > 0) u.sp = Math.min(u.spMax, u.sp + u.spMax * 0.12 * sdt);
    }
    // jugador dispara al más débil
    pl.cd -= sdt;
    if (pl.cd <= 0) {
      const tgt = alive.reduce((a, b) => (b.hp + b.sp < a.hp + a.sp ? b : a));
      const period = 0.7;
      const per = UPG.weapons.dps[S.lv.weapons - 1] * period / pl.guns;
      for (let g = 0; g < pl.guns; g++) setTimeout(() => { if (!this.ended && !tgt.dead) this.fire(pl, tgt, per * rand(0.85, 1.15), '#3de8ff', true); }, g * 90 / this.speed);
      pl.cd = period;
    }
    // drones
    for (const d of this.drones) {
      d.a += sdt * 2; d.cd -= sdt;
      d.x = pl.x + Math.cos(d.a) * 48; d.y = pl.y + Math.sin(d.a) * 30;
      if (d.cd <= 0) { d.cd = 0.8; const tgt = pick(alive); this.fire(d, tgt, 2.5 * 0.8, '#6dffb0', true); }
    }
    // enemigos
    for (const e of alive) {
      e.cd -= sdt;
      if (e.cd <= 0) { const period = rand(0.8, 1.2); this.fire(e, pl, e.dps * period * rand(0.85, 1.15), '#ff4d6d', false); e.cd = period; }
    }
  },
  retreat() {
    if (this.ended) return;
    const chance = clamp(ship.flee * 0.8, 0.1, 0.8);
    if (Math.random() < chance) { toast('Retreat successful!', 'good'); sfx('warp'); this.finish(null); }
    else { toast('Retreat failed', 'bad'); this.pl.cd += 1; document.getElementById('btnRetreat').disabled = true; setTimeout(() => { const b = document.getElementById('btnRetreat'); if (b) b.disabled = false; }, 2500); }
  },
  finish(win) {
    this.ended = true;
    S.hull = Math.max(0, Math.round(this.pl.hp));
    setTimeout(() => this.result(win), win === null ? 300 : 1200);
  },
  result(win) {
    const done = this.done;
    const back = () => { setScene(this.prev || MapScene); };
    if (win === true) {
      S.stats.won++;
      const loot = Math.round(this.fleetKeys.reduce((a, k) => a + ENEMIES[k].loot, 0) * rand(0.8, 1.2) * (1 + S.day / 300));
      const military = this.fleetKeys.includes('patrol');
      let salv = '';
      if (!military) {
        const it = pick(['arms', 'tech', 'meds', 'luxury', 'platinum', 'he3']);
        const n = Math.min(cargoFree(), randi(1, 2 + this.fleetKeys.length * 2));
        if (n > 0) { addCargo(it, n); salv = `<br>You salvage <b>${n} ${ITEMS[it].n}</b> from the wreckage.`; }
        repChange('piratas', -3, true);
        const near = LOC[S.loc].faction && LOC[S.loc].faction !== 'piratas' ? LOC[S.loc].faction : 'cinturon';
        repChange(near, 1 + this.fleetKeys.length, true);
        for (const c of S.active) if (c.type === 'bounty') { c.progress++; }
        for (const c of [...S.active]) if (c.type === 'bounty' && c.progress >= c.kills) completeContract(c);
      }
      sfx('win');
      addNews('🏆', `Defeated ${this.fleetKeys.length} ${military ? 'military' : 'pirate'} ship${this.fleetKeys.length > 1 ? 's' : ''}. Loot: ${fmt(loot)} cr`, '#6dffb0');
      earn(loot);
      showModal({ icon: '🏆', title: 'Victory!', html: `You destroyed the enemy fleet.<br>Loot: <b class="cr">${fmt(loot)} cr</b>${salv}<br>Hull: ${S.hull}/${ship.hpMax}`,
        buttons: [{ label: 'Continue', cls: 'primary', fn: () => { back(); updateHUD(); done && done(); } }] });
    } else if (win === null) {
      back(); done && done();
    } else {
      S.stats.lost++;
      if (MapScene.travel) { MapScene.travel = null; document.getElementById('travelBanner').classList.add('hidden'); }
      setScene(MapScene);
      towShip('Your ship was disabled in battle.');
    }
    save();
  },
  draw(ctx) {
    this.layout();
    const t = this.t;
    ctx.save();
    if (this.shake) ctx.translate((Math.random() - 0.5) * this.shake, (Math.random() - 0.5) * this.shake);
    drawSpaceBg(ctx, W, H, t * 40, 0, t, '#1c0b1e');
    const bl = LOC[(this.prev === MineScene && MineScene.loc) ? MineScene.loc.id : S.loc];
    const bgl = bl.parent ? LOC[bl.parent] : bl.follow ? LOC[bl.follow] : bl;
    if (bgl.id !== 'kuiper') { const pr = Math.min(W, H) * 0.55; drawPlanet(ctx, W * 0.5, H + pr * 0.55, pr, bgl, -Math.PI / 2, t); }
    // líneas de velocidad
    ctx.strokeStyle = 'rgba(160,190,255,0.15)'; ctx.lineWidth = 1;
    for (let i = 0; i < 30; i++) {
      const y = (i * 97.3) % H, x = W - ((t * 400 + i * 173) % (W + 200));
      ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + 60, y); ctx.stroke();
    }
    const pl = this.pl;
    const sc = W < 700 ? 1 : 1.7;
    if (!pl.dead) {
      drawPlayerShip(ctx, S.lv, pl.x, pl.y + Math.sin(t * 2) * 4, 0, sc * (1.4 - S.lv.hull * 0.08), 0.7, t);
      if (pl.shieldFlash > 0) { ctx.strokeStyle = `rgba(61,232,255,${pl.shieldFlash * 3})`; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(pl.x, pl.y, 50 * sc, 0, TAU); ctx.stroke(); }
      this.bars(ctx, pl.x, pl.y - 62 * sc, pl);
    }
    for (const d of this.drones) if (d.x) { glow(ctx, d.x, d.y, 9, '#6dffb088', 0.8); ctx.fillStyle = '#d4dcea'; ctx.beginPath(); ctx.arc(d.x, d.y, 3.5, 0, TAU); ctx.fill(); }
    for (const e of this.en) {
      if (e.dead) continue;
      const y = e.y + Math.sin(t * 2 + e.bob) * 5;
      drawEnemyShip(ctx, e.k, e.x, y, Math.PI, sc, t);
      if (e.hitT > 0) glow(ctx, e.x, y, 30, '#ffffff', 0.4);
      if (e.shieldFlash > 0) { ctx.strokeStyle = `rgba(255,120,150,${e.shieldFlash * 3})`; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(e.x, y, 30 * sc * ENEMIES[e.k].size, 0, TAU); ctx.stroke(); }
      this.bars(ctx, e.x, y - 34 * sc * ENEMIES[e.k].size, e);
    }
    ctx.globalCompositeOperation = 'lighter';
    for (const s of this.shots) {
      const a = Math.atan2(s.ty - s.sy, s.tx - s.sx);
      ctx.strokeStyle = s.col; ctx.lineWidth = 3;
      ctx.beginPath(); ctx.moveTo(s.x, s.y); ctx.lineTo(s.x - Math.cos(a) * 16, s.y - Math.sin(a) * 16); ctx.stroke();
      glow(ctx, s.x, s.y, 8, s.col, 0.8);
    }
    ctx.globalCompositeOperation = 'source-over';
    this.parts.draw(ctx);
    ctx.font = '700 15px Rajdhani, sans-serif'; ctx.textAlign = 'center';
    for (const f of this.floats) { ctx.globalAlpha = Math.min(1, f.life * 2); ctx.fillStyle = f.col; ctx.fillText(f.txt, f.x, f.y); }
    ctx.globalAlpha = 1;
    ctx.restore();
  },
  bars(ctx, x, y, u) {
    const w = 60;
    ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(x - w / 2 - 1, y - 1, w + 2, 10);
    ctx.fillStyle = u === this.pl ? '#6dffb0' : '#ff4d6d'; ctx.fillRect(x - w / 2, y, w * clamp(u.hp / u.max, 0, 1), 4);
    if (u.spMax > 0) { ctx.fillStyle = '#3de8ff'; ctx.fillRect(x - w / 2, y + 5, w * clamp(u.sp / u.spMax, 0, 1), 3); }
    if (u.n) { ctx.font = '600 11px Rajdhani, sans-serif'; ctx.textAlign = 'center'; ctx.fillStyle = 'rgba(255,200,210,0.85)'; ctx.fillText(u.n, x, y - 4); }
  },
};
function startBattle(fleet, enemyFirst, done) { BattleScene.start(fleet, enemyFirst, done); }
