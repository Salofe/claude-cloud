'use strict';
// ============ SCENE: MINING FIELD / SPACE ARENA ============
// The station sits at the bottom. Fly back down into the docking zone to sell.
// The higher up (farther from the station) you go, the richer the rocks.
const MW = 1800, MH = 3400, DOCK_Y = MH - 240;
const Z_HP = [1, 5, 16, 60, 220, 800];
const mineScale = () => 1.35 - (S.lv.hull - 1) * 0.08;
const shipR = () => shipLen(S.lv) * mineScale();
const SPACE = { id: 'space', n: 'Deep Space', col: ['#6a7fb0', '#1b2340'], field: { n: 'Deep Space', z: 2, ores: { iron: 3, nickel: 1 }, count: 10 } };

const MineScene = {
  t: 0, loc: null, rocks: [], chunks: [], drones: [], odrones: [], enemies: [], bolts: [], parts: new Particles(), cam: { x: 0, y: 0 }, shake: 0,
  p: null, dayTimer: 0, ambush: null, laserOn: false, laserHit: null, collected: {}, floaters: [], space: null,
  enter(arg) {
    if (arg && typeof arg === 'object') { this.space = arg; this.loc = { ...SPACE, field: { ...SPACE.field, z: arg.z } }; this.setup(); }
    else if (arg) { this.space = null; this.loc = LOC[arg]; this.setup(); }
    showMineUI(true);
    $('travelBanner').classList.add('hidden');
  },
  exit() { showMineUI(false); laserSound(false); this.laserOn = false; },
  get z() { return this.loc.field.z; },
  setup() {
    const f = this.loc.field;
    this.rocks = []; this.chunks = []; this.parts = new Particles(); this.floaters = []; this.enemies = []; this.bolts = [];
    this.hadCombat = false; this.clearT = 0; this.warp = null; this.armed = false;
    if (this.space) this.p = { x: MW / 2, y: MH / 2, vx: 0, vy: 0, a: -Math.PI / 2, shield: ship.shieldMax, shT: 0, fireCd: 0 };
    else this.p = { x: MW / 2, y: DOCK_Y + 60, vx: 0, vy: -260, a: -Math.PI / 2, shield: ship.shieldMax, shT: 0, fireCd: 0 };
    this.cam = { x: this.p.x, y: this.p.y - 120 };
    this.dayTimer = 0; this.collected = {};
    const rich = S.events.some(e => e.rich === this.loc.id);
    this.target = Math.round(f.count * (rich ? 1.25 : 1));
    if (this.space) {
      for (let i = 0; i < f.count; i++) { let x, y; do { x = rand(100, MW - 100); y = rand(100, MH - 100); } while (Math.hypot(x - this.p.x, y - this.p.y) < 300); this.spawnRock(x, y, pick([1, 2, 2, 3])); }
      Combat.spawn(this, this.space.fleet, this.space.z, false);
    } else {
      for (let i = 0; i < this.target; i++) {
        let x, y;
        if (i < 3) { x = MW / 2 + (i - 1) * 260 + rand(-40, 40); y = DOCK_Y - rand(380, 520); }
        else { x = rand(120, MW - 120); y = rand(120, DOCK_Y - 380); }
        this.spawnRock(x, y, i < 3 ? 3 : pick([3, 3, 2, 2, 1]), null, rich);
      }
    }
    this.escorts = built('fleet') ? [0, 1].map(i => ({ i, x: 0, y: 0, a: 0, gcd: rand(0, 1) })) : [];
    this.drones = [];
    for (let i = 0; i < ship.drones; i++) this.drones.push({ x: this.p.x, y: this.p.y, vx: 0, vy: 0, tgt: null, carry: null, a: i });
    this.odrones = [];
    const o = !this.space && S.outposts[this.loc.id];
    if (o) for (let i = 0; i < Math.min(16, o.n); i++) this.odrones.push({ x: 220 + rand(-30, 30), y: MH - 140, st: 'out', tgt: null, t: rand(0, 3) });
    this.ambush = null;
    if (!this.space) {
      const dg = locDanger(this.loc.id) * (1 - ship.avoid);
      if (Math.random() < dg * 0.9) this.ambush = { at: rand(20, 45), warned: false };
    }
  },
  depthOf(y) { return clamp(1 - y / (DOCK_Y - 300), 0, 1); },
  pickOre(depth) {
    const f = this.loc.field;
    const keys = Object.keys(f.ores).sort((a, b) => ITEMS[a].b - ITEMS[b].b);
    const ws = keys.map((k, i) => f.ores[k] * (1 + depth * 4 * (i / Math.max(1, keys.length - 1))));
    let r = Math.random() * ws.reduce((a, b) => a + b, 0);
    for (let i = 0; i < keys.length; i++) { r -= ws[i]; if (r <= 0) return keys[i]; }
    return keys[0];
  },
  spawnRock(x, y, tier, ore, rich) {
    const depth = this.space ? 0.3 : this.depthOf(y);
    if (!ore) ore = this.pickOre(depth);
    const R = [0, 20, 34, 56][tier] * rand(0.9, 1.15);
    const isRich = Math.random() < (rich ? 0.3 : 0.06) + depth * 0.2;
    const gold = !this.space && Math.random() < 0.006 + depth * 0.02;
    const nv = 2 + Math.floor(tier * 1.5);
    const hp = R * 0.7 * ITEMS[ore].h * Z_HP[this.z] * (gold ? 2 : 1);
    const rock = {
      x, y, vx: rand(-14, 14), vy: rand(-14, 14), rot: rand(0, TAU), vr: rand(-0.4, 0.4), r: R, tier, ore, rich: isRich, gold,
      hp, maxhp: hp, hit: 0, cold: this.loc.field.cold,
      shape: makeRockShape(9 + tier * 2, 0.22),
      veins: Array.from({ length: nv }, () => { const a = rand(0, TAU), d = rand(0, 0.6); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.07, 0.16)]; }),
      craters: Array.from({ length: tier }, () => { const a = rand(0, TAU), d = rand(0, 0.5); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.1, 0.2)]; }),
    };
    this.rocks.push(rock);
    return rock;
  },
  breakRock(r) {
    this.rocks = this.rocks.filter(x => x !== r);
    this.parts.burst(r.x, r.y, 14 + r.tier * 8, r.gold ? '#ffd24a' : '#c9b8a6', 120 + r.tier * 40, 0.8, 2.5);
    this.parts.burst(r.x, r.y, 6 + r.tier * 3, ITEMS[r.ore].c, 90, 1, 2.5);
    sfx('break'); this.shake = Math.max(this.shake, r.tier * 3);
    S.hints.laser = 1;
    if (r.gold) {
      const v = ITEMS[r.ore].b * incomeMult() * 30 * r.tier;
      for (let i = 0; i < 6; i++) { const a = rand(0, TAU), s = rand(40, 120); this.chunks.push({ x: r.x, y: r.y, vx: Math.cos(a) * s, vy: Math.sin(a) * s, cr: v / 6, gold: 1, rot: rand(0, TAU), life: 60 }); }
      this.floaters.push({ x: r.x, y: r.y - 30, txt: 'JACKPOT!', col: '#ffd24a', life: 2, big: 1 });
      S.stats.jackpots++; sfx('win');
    }
    if (r.tier > 1) {
      for (let i = 0; i < 2; i++) {
        const c = this.spawnRock(r.x + rand(-10, 10), r.y + rand(-10, 10), r.tier - 1, r.ore);
        const a = rand(0, TAU); c.vx = r.vx + Math.cos(a) * 50; c.vy = r.vy + Math.sin(a) * 50; c.rich = r.rich; c.gold = false; c.hp = c.maxhp = c.maxhp;
      }
      if (Math.random() < 0.5) this.dropChunk(r.x, r.y, r.ore);
    } else {
      const n = randi(1, 2) + (r.rich ? 2 : 0);
      for (let i = 0; i < n; i++) this.dropChunk(r.x, r.y, r.ore);
    }
  },
  dropChunk(x, y, ore) {
    const a = rand(0, TAU), v = rand(20, 60);
    this.chunks.push({ x, y, vx: Math.cos(a) * v, vy: Math.sin(a) * v, ore, rot: rand(0, TAU), life: 45 });
  },
  collect(c) {
    if (c.cr) {
      earn(c.cr);
      this.floaters.push({ x: this.p.x + rand(-20, 20), y: this.p.y - 26, txt: '+' + fmt(c.cr) + ' cr', col: '#ffd24a', life: 1.2 });
      sfx('cash');
      return true;
    }
    if (cargoFree() <= 0) return false;
    addCargo(c.ore, 1); S.stats.mined++;
    this.collected[c.ore] = (this.collected[c.ore] || 0) + 1;
    this.floaters.push({ x: this.p.x, y: this.p.y - 22, txt: '+1 ' + ITEMS[c.ore].n, col: ITEMS[c.ore].c, life: 1.1 });
    sfx('pickup');
    return true;
  },
  get inCombat() { return this.enemies.length > 0; },
  update(dt) {
    this.t += dt;
    const p = this.p;
    // --- movement ---
    let ax = 0, ay = 0;
    if (keys.has('KeyW') || keys.has('ArrowUp')) ay -= 1;
    if (keys.has('KeyS') || keys.has('ArrowDown')) ay += 1;
    if (keys.has('KeyA') || keys.has('ArrowLeft')) ax -= 1;
    if (keys.has('KeyD') || keys.has('ArrowRight')) ax += 1;
    if (joy.active) { ax = joy.dx; ay = joy.dy; }
    const al = Math.hypot(ax, ay);
    if (al > 1) { ax /= al; ay /= al; }
    const acc = 560 * ship.thrust / Math.pow(ship.mass, 0.3);
    p.vx += ax * acc * dt; p.vy += ay * acc * dt;
    const drag = Math.pow(0.4, dt);
    p.vx *= drag; p.vy *= drag;
    const maxV = 360 * ship.thrust;
    const v = Math.hypot(p.vx, p.vy);
    if (v > maxV) { p.vx *= maxV / v; p.vy *= maxV / v; }
    p.x = clamp(p.x + p.vx * dt, 40, MW - 40); p.y = clamp(p.y + p.vy * dt, 40, MH - 40);
    this.thrusting = Math.hypot(ax, ay);
    if (!S.hints.move) { this.moved = (this.moved || 0) + v * dt; if (this.moved > 160) S.hints.move = 1; }
    // --- aim & fire ---
    let aim = null, firing = false;
    const wm = { x: mouse.x - W / 2 + this.cam.x, y: mouse.y - H / 2 + this.cam.y };
    const combat = this.inCombat;
    if (touchFire) {
      let best = null, bd = 1e9;
      const list = combat ? this.enemies : this.rocks;
      for (const r of list) { const d = Math.hypot(r.x - p.x, r.y - p.y) - (r.r || 0); if (d < bd) { bd = d; best = r; } }
      if (best && (combat || bd < ship.laserRange + 40)) { aim = Math.atan2(best.y - p.y, best.x - p.x); firing = true; }
    } else if (mouse.down && !mouse.onUI) { aim = Math.atan2(wm.y - p.y, wm.x - p.x); firing = true; }
    if (keys.has('Space')) { firing = true; if (aim == null) aim = p.a; }
    const targetA = aim != null ? aim : (al > 0.1 ? Math.atan2(ay, ax) : p.a);
    const da = ((targetA - p.a + Math.PI) % TAU + TAU) % TAU - Math.PI;
    p.a += da * Math.min(1, dt * 10);
    this.laserHit = null;
    p.fireCd -= dt;
    if (firing && combat) {
      S.hints.guns = 1;
      if (p.fireCd <= 0) { Combat.firePlayer(this, aim != null ? aim : p.a); p.fireCd = 0.25; }
    } else if (firing) {
      const dir = aim != null ? aim : p.a;
      const dx = Math.cos(dir), dy = Math.sin(dir);
      let best = null, bt = ship.laserRange;
      for (const r of this.rocks) {
        const ox = r.x - p.x, oy = r.y - p.y;
        const proj = ox * dx + oy * dy;
        if (proj < 0) continue;
        const perp2 = ox * ox + oy * oy - proj * proj;
        const rr = r.r * 0.9;
        if (perp2 > rr * rr) continue;
        const tHit = proj - Math.sqrt(rr * rr - perp2);
        if (tHit < bt) { bt = tHit; best = r; }
      }
      const hx = p.x + dx * bt, hy = p.y + dy * bt;
      this.laserHit = { x: hx, y: hy, dir, rock: best };
      if (best) {
        best.hp -= ship.laserDps * dt; best.hit = 0.05;
        if (Math.random() < dt * 30) this.parts.add(hx, hy, -dx * 80 + rand(-60, 60), -dy * 80 + rand(-60, 60), 0.4, Math.random() < 0.5 ? ITEMS[best.ore].c : laserColor(laserTier()), 2, true);
        if (best.hp <= 0) this.breakRock(best);
      }
    }
    const lOn = firing && !combat;
    if (lOn !== this.laserOn) { this.laserOn = lOn; laserSound(lOn, laserTier()); }
    // --- rocks ---
    for (const r of this.rocks) {
      r.x += r.vx * dt; r.y += r.vy * dt; r.rot += r.vr * dt; r.hit = Math.max(0, r.hit - dt);
      const maxY = this.space ? MH - r.r : DOCK_Y - 120;
      if (r.x < r.r || r.x > MW - r.r) r.vx *= -1;
      if (r.y < r.r || r.y > maxY) r.vy *= -1;
      r.x = clamp(r.x, r.r, MW - r.r); r.y = clamp(r.y, r.r, maxY);
      const dx = p.x - r.x, dy = p.y - r.y, d = Math.hypot(dx, dy), md = r.r + shipR() * 0.4;
      if (d < md && d > 0) {
        const nx = dx / d, ny = dy / d;
        p.x = r.x + nx * md; p.y = r.y + ny * md;
        const rel = (p.vx - r.vx) * nx + (p.vy - r.vy) * ny;
        if (rel < 0) {
          p.vx -= 1.6 * rel * nx; p.vy -= 1.6 * rel * ny;
          r.vx += rel * nx * 0.2 / r.tier; r.vy += rel * ny * 0.2 / r.tier;
          if (-rel > 150) { this.damage((-rel - 130) * 0.04 * (1 + this.z)); sfx('bump'); this.shake = 6; }
        }
      }
    }
    // --- chunks & loot ---
    const cfree = cargoFree();
    for (const c of this.chunks) {
      c.x += c.vx * dt; c.y += c.vy * dt; c.vx *= Math.pow(0.5, dt); c.vy *= Math.pow(0.5, dt); c.life -= dt;
      const dx = p.x - c.x, dy = p.y - c.y, d = Math.hypot(dx, dy);
      const mag = c.cr ? ship.magnet * 1.5 : ship.magnet;
      if (d < mag && (cfree > 0 || c.cr)) { const f = 650 * (1 - d / mag) + 140; c.vx += dx / d * f * dt; c.vy += dy / d * f * dt; }
      if (d < 24 && this.collect(c)) c.dead = true;
      if (c.life <= 0) c.dead = true;
    }
    this.chunks = this.chunks.filter(c => !c.dead);
    // --- collector drones ---
    for (const dr of this.drones) {
      if (dr.tgt && (dr.tgt.dead || !this.chunks.includes(dr.tgt))) dr.tgt = null;
      if (!dr.tgt && !dr.carry && cargoFree() > 0) {
        let best = null, bd = 900;
        for (const c of this.chunks) { if (this.drones.some(o => o !== dr && o.tgt === c)) continue; const d = Math.hypot(c.x - dr.x, c.y - dr.y); if (d < bd) { bd = d; best = c; } }
        dr.tgt = best;
      }
      let tx, ty;
      if (dr.carry) { tx = p.x; ty = p.y; }
      else if (dr.tgt) { tx = dr.tgt.x; ty = dr.tgt.y; }
      else { const a = this.t * 1.5 + dr.a * TAU / Math.max(1, this.drones.length); tx = p.x + Math.cos(a) * 50; ty = p.y + Math.sin(a) * 50; }
      const dx = tx - dr.x, dy = ty - dr.y, d = Math.hypot(dx, dy) || 1;
      dr.vx = lerp(dr.vx, dx / d * Math.min(420, d * 6), dt * 6); dr.vy = lerp(dr.vy, dy / d * Math.min(420, d * 6), dt * 6);
      dr.x += dr.vx * dt; dr.y += dr.vy * dt;
      if (dr.tgt && d < 12) { dr.carry = dr.tgt; dr.tgt.dead = true; this.chunks = this.chunks.filter(c => c !== dr.carry); dr.tgt = null; }
      if (dr.carry && d < 20) { if (!this.collect(dr.carry)) this.chunks.push(Object.assign(dr.carry, { dead: false, x: dr.x, y: dr.y, vx: 0, vy: 0 })); dr.carry = null; }
    }
    // --- outpost drones (cosmetic) ---
    for (const od of this.odrones) {
      od.t -= dt;
      if (od.st === 'out') {
        if (!od.tgt || !this.rocks.includes(od.tgt)) od.tgt = pick(this.rocks.filter(r => r.y < DOCK_Y - 150)) || null;
        if (od.tgt) {
          const tx = od.tgt.x + Math.cos(od.t) * (od.tgt.r + 16), ty = od.tgt.y + Math.sin(od.t) * (od.tgt.r + 16);
          od.x = lerp(od.x, tx, dt * 1.8); od.y = lerp(od.y, ty, dt * 1.8);
          if (Math.hypot(tx - od.x, ty - od.y) < 30 && od.t < -2) { od.st = 'home'; }
        }
      } else {
        od.x = lerp(od.x, 220, dt * 1.2); od.y = lerp(od.y, MH - 150, dt * 1.2);
        if (Math.hypot(220 - od.x, MH - 150 - od.y) < 20) { od.st = 'out'; od.t = rand(2, 4); od.tgt = null; }
      }
    }
    // --- combat ---
    Combat.update(this, dt);
    if (this.clearT > 0) { this.clearT -= dt; if (this.clearT <= 0) this.finishSpace(true); }
    if (this.warp) {
      this.warp.t += dt;
      if (this.warp.t >= ship.warpTime) { sfx('warp'); toast('Warped out!', 'good'); this.finishSpace(false); return; }
    }
    // --- shields & hazards ---
    p.shT -= dt;
    if (p.shT <= 0) p.shield = Math.min(ship.shieldMax, p.shield + (4 + ship.shieldMax * 0.08) * dt);
    if (this.loc.field.hazard === 'heat') this.damage(1.2 * dt * (1 + this.z), true);
    // --- ambush ---
    if (this.ambush) {
      this.ambush.at -= dt;
      if (!this.ambush.warned && this.ambush.at < 3) { this.ambush.warned = true; toast('⚠ Pirates incoming!', 'bad'); sfx('alarm'); }
      if (this.ambush.at <= 0) {
        const fleet = buildFleet(locDanger(this.loc.id));
        this.ambush = null;
        if (S.rep.piratas >= 35) toast('Pirates recognize your ship and leave you alone', 'good');
        else Combat.spawn(this, fleet, this.z, true);
      }
    }
    // --- docking zone ---
    if (!this.space) {
      if (p.y < DOCK_Y - 250) this.armed = true;
      if (this.armed && p.y > DOCK_Y) { this.leave(); return; }
    }
    // --- time ---
    this.dayTimer += dt;
    if (this.dayTimer > 40 && has(U.MAP)) { this.dayTimer = 0; tickDay(); }
    if (!this.space && this.rocks.length < this.target * 0.5 && Math.random() < dt * 0.4) {
      const x = rand(120, MW - 120), y = rand(120, Math.min(DOCK_Y - 400, p.y - 500));
      if (y > 100) this.spawnRock(x, y, 3);
    }
    this.parts.update(dt);
    for (const f of this.floaters) { f.y -= 30 * dt; f.life -= dt; }
    this.floaters = this.floaters.filter(f => f.life > 0);
    const k = 1 - Math.pow(0.001, dt);
    this.cam.x = lerp(this.cam.x, p.x + p.vx * 0.3, k); this.cam.y = lerp(this.cam.y, p.y + p.vy * 0.3 - 60, k);
    this.shake = Math.max(0, this.shake - dt * 20);
    if (this.thrusting > 0.1 && Math.random() < dt * 40) {
      const bx = p.x - Math.cos(p.a) * shipR() * 0.75, by = p.y - Math.sin(p.a) * shipR() * 0.75;
      this.parts.add(bx, by, -Math.cos(p.a) * 60 + rand(-15, 15), -Math.sin(p.a) * 60 + rand(-15, 15), 0.45, ENGINE_COL[Math.min(4, Math.floor((S.lv.engine - 1) / 4))], 2.5);
    }
    this.coach();
    updateMineHUD();
  },
  coach() {
    const h = S.hints;
    let msg = '';
    if (this.inCombat && !h.guns) msg = isTouch ? 'Hold <b>FIRE</b> to shoot the pirates!' : 'Pirates! <b>Hold the mouse</b> to shoot your guns';
    else if (!h.move) msg = isTouch ? 'Drag anywhere on the left side to fly' : 'Fly with <b>WASD</b> or the <b>arrow keys</b>';
    else if (!h.laser) msg = isTouch ? 'Hold <b>LASER</b> — it aims at the nearest rock' : 'Hold the <b>mouse button</b> to fire your mining laser at a rock';
    else if (S.stats.mined < 4) msg = 'Fly close to the glowing crystals to scoop them up';
    else if (!this.space && cargoFree() <= 0) msg = '📦 Cargo full! Fly back <b>down</b> to the station ⬇';
    else if (!this.space && !h.deep && S.stats.docks >= 2 && this.p.y > DOCK_Y - 900) { msg = 'Tip: rocks get <b>richer</b> the farther up you fly ⬆'; }
    if (this.p.y < DOCK_Y - 1400) h.deep = 1;
    coach(msg);
  },
  damage(n, heat) {
    const p = this.p;
    if (p.shield > 0) { const a = Math.min(p.shield, n); p.shield -= a; n -= a; if (!heat) p.shT = 2.5; }
    if (n > 0) {
      S.hull -= n;
      if (S.hull <= 0) {
        S.hull = 0; laserSound(false); this.laserOn = false;
        S.stats.lost++;
        if (this.space && MapScene.travel) { MapScene.travel = null; $('travelBanner').classList.add('hidden'); }
        setScene(MapScene);
        towShip(this.inCombat ? 'Your ship was shot down.' : 'Your hull collapsed.');
      }
    }
  },
  onVictory() {
    sfx('win');
    const n = S.stats.kills;
    toast('☠ Pirates destroyed! Grab the loot.', 'good');
    for (const c of [...S.active]) if (c.type === 'bounty') { c.progress++; if (c.progress >= c.kills) completeContract(c); }
    repChange('piratas', -3, true);
    const near = LOC[S.loc].faction && LOC[S.loc].faction !== 'piratas' ? LOC[S.loc].faction : 'cinturon';
    repChange(near, 2, true);
    S.stats.won++;
    addNews('🏆', `Pirate fleet destroyed`, '#6dffb0');
    if (this.space) this.clearT = 4;
  },
  finishSpace(won) {
    if (!this.space) return;
    const done = this.space.done;
    // collect remaining loot automatically
    for (const c of this.chunks) if (c.cr) earn(c.cr);
    this.space = null; this.warp = null;
    save();
    setScene(MapScene);
    done && done();
  },
  draw(ctx) {
    const t = this.t;
    const sx = (Math.random() - 0.5) * this.shake, sy = (Math.random() - 0.5) * this.shake;
    const cx = this.cam.x - W / 2 + sx, cy = this.cam.y - H / 2 + sy;
    drawSpaceBg(ctx, W, H, cx, cy, t, this.loc.field.cold ? '#0c1838' : this.loc.field.hazard === 'heat' ? '#2a1408' : this.space ? '#1c0b1e' : null);
    const bgLoc = this.space ? LOC[S.loc] : this.loc.id === 'kuiper' ? LOC.pluton : this.loc.parent ? LOC[this.loc.parent] : this.loc.follow ? LOC[this.loc.follow] : this.loc;
    if (bgLoc && bgLoc.col) {
      const bx = W * 0.8 - cx * 0.03, by = H * 0.25 - (cy - MH) * 0.03;
      drawPlanet(ctx, bx, by, Math.min(W, H) * (bgLoc.size > 12 ? 0.28 : 0.16), bgLoc, Math.atan2(-by, -bx - W), t);
    }
    if (this.loc.field.hazard === 'heat') drawSun(ctx, -cx * 0.02 - 40, H * 0.5 - (cy - MH) * 0.02, 120, t);
    ctx.save();
    ctx.translate(-cx, -cy);
    ctx.strokeStyle = 'rgba(61,232,255,0.12)'; ctx.setLineDash([10, 12]); ctx.lineWidth = 2;
    ctx.strokeRect(20, 20, MW - 40, MH - 40); ctx.setLineDash([]);
    if (!this.space) this.drawStation(ctx, t);
    const p = this.p;
    if (cargoFree() > 0) { ctx.strokeStyle = 'rgba(61,232,255,0.07)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.arc(p.x, p.y, ship.magnet, 0, TAU); ctx.stroke(); }
    for (const r of this.rocks) if (r.x > cx - 100 && r.x < cx + W + 100 && r.y > cy - 100 && r.y < cy + H + 100) {
      drawRock(ctx, r, t, S.lv.scanner);
      if (r.gold) { glow(ctx, r.x, r.y, r.r * 2.4, '#ffd24a', 0.35 + 0.2 * Math.sin(t * 5)); if (Math.random() < 0.1) this.parts.add(r.x + rand(-r.r, r.r), r.y + rand(-r.r, r.r), 0, -20, 0.8, '#fff3b0', 2); }
    }
    for (const c of this.chunks) {
      if (c.cr) {
        glow(ctx, c.x, c.y, 16, '#ffd24aaa', 0.8);
        ctx.fillStyle = c.gold ? '#fff3b0' : '#ffd24a'; ctx.beginPath(); ctx.arc(c.x, c.y, 5.5, 0, TAU); ctx.fill();
        ctx.fillStyle = '#9a6a00'; ctx.font = 'bold 8px sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText('¢', c.x, c.y + 0.5); ctx.textBaseline = 'alphabetic';
      } else drawOreChunk(ctx, c, t);
    }
    // outpost drones
    for (const od of this.odrones) {
      if (od.st === 'out' && od.tgt && Math.hypot(od.tgt.x - od.x, od.tgt.y - od.y) < od.tgt.r + 30) {
        ctx.strokeStyle = 'rgba(109,255,176,0.6)'; ctx.lineWidth = 1.5;
        ctx.beginPath(); ctx.moveTo(od.x, od.y); ctx.lineTo(od.tgt.x, od.tgt.y); ctx.stroke();
      }
      glow(ctx, od.x, od.y, 9, '#6dffb0aa', 0.7);
      ctx.fillStyle = '#c9f7de'; ctx.fillRect(od.x - 3, od.y - 3, 6, 6);
    }
    if (this.laserHit) {
      const L = this.laserHit, col = laserColor(laserTier());
      const nx = p.x + Math.cos(L.dir) * shipR() * 0.9, ny = p.y + Math.sin(L.dir) * shipR() * 0.9;
      ctx.globalCompositeOperation = 'lighter';
      ctx.strokeStyle = col; ctx.globalAlpha = 0.35; ctx.lineWidth = 7 + laserTier() + Math.sin(t * 50) * 2;
      ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(L.x, L.y); ctx.stroke();
      ctx.globalAlpha = 1; ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 1.8;
      ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(L.x, L.y); ctx.stroke();
      ctx.globalCompositeOperation = 'source-over';
      glow(ctx, L.x, L.y, L.rock ? 26 : 10, col, 0.9);
    }
    for (const dr of this.drones) {
      glow(ctx, dr.x, dr.y, 10, '#3de8ff88', 0.8);
      ctx.fillStyle = '#d4dcea'; ctx.beginPath(); ctx.arc(dr.x, dr.y, 4, 0, TAU); ctx.fill();
      ctx.fillStyle = '#3de8ff'; ctx.beginPath(); ctx.arc(dr.x, dr.y, 1.8, 0, TAU); ctx.fill();
      if (dr.carry && dr.carry.ore) { ctx.fillStyle = ITEMS[dr.carry.ore].c; ctx.fillRect(dr.x - 2, dr.y + 4, 4, 4); }
    }
    Combat.draw(this, ctx, t);
    this.parts.draw(ctx);
    const lv = shipLv();
    drawPlayerShip(ctx, lv, p.x, p.y, p.a, mineScale(), this.thrusting, t);
    if (ship.shieldMax > 0 && p.shT > 1.8) {
      ctx.strokeStyle = `rgba(61,232,255,${(p.shT - 1.8) * 1.3})`; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(p.x, p.y, shipR() + 8, 0, TAU); ctx.stroke();
    }
    if (this.warp) {
      const k = this.warp.t / ship.warpTime;
      ctx.strokeStyle = `rgba(160,120,255,${0.4 + k * 0.6})`; ctx.lineWidth = 3;
      ctx.beginPath(); ctx.arc(p.x, p.y, shipR() + 14, -Math.PI / 2, -Math.PI / 2 + TAU * k); ctx.stroke();
      glow(ctx, p.x, p.y, shipR() * 2 * k + 10, '#a07cff', 0.5 * k);
    }
    ctx.textAlign = 'center';
    for (const f of this.floaters) {
      ctx.font = f.big ? '900 26px Orbitron, sans-serif' : '700 14px Rajdhani, sans-serif';
      ctx.globalAlpha = Math.min(1, f.life * 2); ctx.fillStyle = f.col; ctx.fillText(f.txt, f.x, f.y);
    }
    ctx.globalAlpha = 1;
    ctx.restore();
    // crosshair
    if (!isTouch && !mouse.onUI) {
      ctx.strokeStyle = this.inCombat ? 'rgba(255,90,120,0.9)' : 'rgba(61,232,255,0.8)'; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.arc(mouse.x, mouse.y, 9, 0, TAU);
      ctx.moveTo(mouse.x - 14, mouse.y); ctx.lineTo(mouse.x - 5, mouse.y); ctx.moveTo(mouse.x + 5, mouse.y); ctx.lineTo(mouse.x + 14, mouse.y);
      ctx.moveTo(mouse.x, mouse.y - 14); ctx.lineTo(mouse.x, mouse.y - 5); ctx.moveTo(mouse.x, mouse.y + 5); ctx.lineTo(mouse.x, mouse.y + 14);
      ctx.stroke();
    }
    // off-screen indicators: station & enemies
    if (!this.space && p.y < DOCK_Y - H * 0.45) {
      const full = cargoFree() <= 0;
      const dist = Math.round((DOCK_Y - p.y) / 10) * 10;
      const bx = W / 2, by = H - (isTouch ? 44 : 64);
      ctx.globalAlpha = full ? 0.8 + 0.2 * Math.sin(t * 6) : 0.6;
      ctx.fillStyle = full ? '#ffd24a' : '#3de8ff';
      ctx.font = '700 15px Rajdhani, sans-serif'; ctx.textAlign = 'center';
      ctx.fillText(`▼ STATION ${dist} m ▼`, bx, by);
      ctx.globalAlpha = 1;
    }
    for (const e of this.enemies) {
      const ex = e.x - cx, ey = e.y - cy;
      if (ex > 0 && ex < W && ey > 0 && ey < H) continue;
      const a = Math.atan2(ey - H / 2, ex - W / 2);
      const ix = W / 2 + Math.cos(a) * (Math.min(W, H) / 2 - 30), iy = H / 2 + Math.sin(a) * (Math.min(W, H) / 2 - 30);
      ctx.fillStyle = '#ff4d6d';
      ctx.save(); ctx.translate(ix, iy); ctx.rotate(a);
      ctx.beginPath(); ctx.moveTo(10, 0); ctx.lineTo(-6, -7); ctx.lineTo(-6, 7); ctx.closePath(); ctx.fill(); ctx.restore();
    }
    // minimap
    const mh = 150, mw = mh * MW / MH, mx = W - mw - 14, my = H - mh - (isTouch ? 210 : 40);
    ctx.fillStyle = 'rgba(8,14,34,0.75)'; ctx.strokeStyle = 'rgba(61,232,255,0.35)'; ctx.lineWidth = 1;
    ctx.fillRect(mx, my, mw, mh); ctx.strokeRect(mx, my, mw, mh);
    if (!this.space) { ctx.fillStyle = 'rgba(61,232,255,0.35)'; ctx.fillRect(mx, my + DOCK_Y / MH * mh, mw, mh - DOCK_Y / MH * mh); }
    for (const r of this.rocks) { ctx.fillStyle = r.gold ? '#ffd24a' : r.rich && S.lv.scanner >= 2 ? ITEMS[r.ore].c : 'rgba(200,190,170,0.7)'; ctx.fillRect(mx + r.x / MW * mw - 1, my + r.y / MH * mh - 1, r.tier * 0.8 + 0.6, r.tier * 0.8 + 0.6); }
    ctx.fillStyle = '#ff4d6d'; for (const e of this.enemies) ctx.fillRect(mx + e.x / MW * mw - 1.5, my + e.y / MH * mh - 1.5, 3, 3);
    ctx.fillStyle = '#3de8ff'; ctx.fillRect(mx + p.x / MW * mw - 2, my + p.y / MH * mh - 2, 4, 4);
    if (this.loc.field.hazard === 'heat' && ship.shieldMax <= 0) { ctx.fillStyle = `rgba(255,120,40,${0.08 + 0.05 * Math.sin(t * 4)})`; ctx.fillRect(0, 0, W, H); }
  },
  drawStation(ctx, t) {
    const l = this.loc;
    const col = l.faction ? FACTIONS[l.faction].c : '#6dffb0';
    // dock zone
    const g = ctx.createLinearGradient(0, DOCK_Y - 40, 0, MH);
    g.addColorStop(0, 'rgba(61,232,255,0)'); g.addColorStop(0.3, 'rgba(61,232,255,0.10)'); g.addColorStop(1, 'rgba(61,232,255,0.22)');
    ctx.fillStyle = g; ctx.fillRect(0, DOCK_Y - 40, MW, MH - DOCK_Y + 40);
    ctx.strokeStyle = `rgba(61,232,255,${0.5 + 0.3 * Math.sin(t * 3)})`; ctx.lineWidth = 3; ctx.setLineDash([18, 12]); ctx.lineDashOffset = -t * 30;
    ctx.beginPath(); ctx.moveTo(0, DOCK_Y); ctx.lineTo(MW, DOCK_Y); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle = 'rgba(61,232,255,0.8)'; ctx.font = '700 16px Rajdhani, sans-serif'; ctx.textAlign = 'center';
    for (let x = 150; x < MW; x += 300) ctx.fillText('▼ DOCK ▼', x, DOCK_Y - 12);
    // station body
    const sx = MW / 2, sy = MH - 70;
    glow(ctx, sx, sy, 380, col + '44', 0.8);
    ctx.fillStyle = '#39445e';
    roundRect(ctx, sx - 420, sy - 20, 840, 40, 12); ctx.fill();
    for (let i = -3; i <= 3; i++) {
      ctx.fillStyle = '#2d6fc4'; ctx.fillRect(sx + i * 120 - 40, sy - 60, 80, 34);
      ctx.strokeStyle = 'rgba(160,200,255,0.4)'; ctx.lineWidth = 1;
      for (let k = 1; k < 4; k++) { ctx.beginPath(); ctx.moveTo(sx + i * 120 - 40 + k * 20, sy - 60); ctx.lineTo(sx + i * 120 - 40 + k * 20, sy - 26); ctx.stroke(); }
    }
    const bg = ctx.createLinearGradient(0, sy - 110, 0, sy + 40);
    bg.addColorStop(0, '#dfe6f3'); bg.addColorStop(1, '#6f7c97');
    ctx.fillStyle = bg;
    roundRect(ctx, sx - 170, sy - 110, 340, 150, 24); ctx.fill();
    ctx.strokeStyle = '#1b2235'; ctx.lineWidth = 2; ctx.stroke();
    // hangar mouth
    ctx.fillStyle = '#0b1226'; roundRect(ctx, sx - 90, sy - 110, 180, 40, 10); ctx.fill();
    glow(ctx, sx, sy - 90, 90, '#3de8ff', 0.5 + 0.2 * Math.sin(t * 4));
    for (let i = 0; i < 8; i++) {
      const on = (Math.floor(t * 6) + i) % 8 < 2;
      ctx.fillStyle = on ? '#ffd24a' : '#5a4a20';
      ctx.fillRect(sx - 160 + i * 42, sy + 20, 16, 5);
    }
    ctx.fillStyle = col; ctx.font = '900 18px Orbitron, sans-serif'; ctx.fillText(l.station.toUpperCase(), sx, sy - 22);
    // drone outpost
    const o = S.outposts[l.id];
    if (o) {
      const ox = 220, oy = MH - 150;
      glow(ctx, ox, oy, 120, '#6dffb055', 0.8);
      ctx.fillStyle = '#4a5a74'; roundRect(ctx, ox - 70, oy - 30, 140, 60, 14); ctx.fill();
      ctx.strokeStyle = '#6dffb0'; ctx.lineWidth = 2; ctx.stroke();
      ctx.fillStyle = '#6dffb0'; ctx.font = '700 13px Rajdhani, sans-serif';
      ctx.fillText(`🤖 OUTPOST LV${o.lv}`, ox, oy - 4);
      ctx.fillStyle = '#ffd24a'; ctx.fillText(`+${fmt(outpostIncome(l.id))}/s`, ox, oy + 14);
    }
  },
  leave(toMap) {
    laserSound(false);
    const got = Object.entries(this.collected);
    if (got.length) addNews('⛏️', `Mined at ${this.loc.field.n}: ${got.map(([k, n]) => `${n} ${ITEMS[k].n}`).join(', ')}`, '#ffd24a');
    this.collected = {};
    for (const c of this.chunks) if (c.cr) earn(c.cr);
    save();
    if (!toMap && LOC[S.loc].station) openDock();
    else setScene(MapScene);
  },
};
function laserTier() { return clamp(1 + Math.floor((S.lv.laser - 1) / 8), 1, 5); }
function shipLv() {
  return { hull: S.lv.hull, laser: laserTier(), engine: clamp(1 + Math.floor((S.lv.engine - 1) / 4), 1, 5), weapons: S.lv.weapons > 1 ? clamp(1 + Math.ceil((S.lv.weapons - 1) / 8), 1, 5) : 1 };
}

function towShip(reason) {
  for (const k in S.cargo) { const n = Math.ceil(S.cargo[k] * 0.6); addCargo(k, -n); }
  const markets = NODES.filter(l => l.station && !l.black && locOpen(l.id));
  let best = markets[0], bd = 1e9;
  for (const l of markets) { const d = locDist(S.loc, l.id, S.day); if (d < bd) { bd = d; best = l; } }
  const fee = Math.round(Math.min(S.credits, S.credits * 0.08));
  S.credits -= fee; S.loc = best.id; S.hull = Math.max(S.hull, Math.round(ship.hpMax * 0.25));
  S.fuel = Math.max(S.fuel, 10);
  sfx('lose');
  showModal({ icon: '🚨', title: 'Towed to safety', danger: true, html: `${reason}<br>A tug brings you to <b>${best.station}</b>. You lost part of your cargo${fee ? ` and paid a <b>${fmt(fee)} cr</b> rescue fee` : ''}.`,
    buttons: [{ label: 'Continue', cls: 'primary', fn: () => { save(); openDock(); } }] });
}
