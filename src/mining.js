'use strict';
// ============ ESCENA: MINERÍA ============
const MW = 2100, MH = 2100;
const mineScale = () => 1.35 - (S.lv.hull - 1) * 0.08;
const shipR = () => shipLen(S.lv) * mineScale();
const MineScene = {
  t: 0, loc: null, rocks: [], chunks: [], drones: [], parts: new Particles(), cam: { x: 0, y: 0 }, shake: 0,
  p: null, dayTimer: 0, ambush: null, laserOn: false, laserHit: null, fullWarn: 0, broken: 0, collected: {}, heatWarn: 0, floaters: [],
  enter(locId) {
    this.loc = LOC[locId || this.loc.id];
    if (locId) this.setup();
    showMineUI(true);
  },
  exit() { showMineUI(false); laserSound(false); },
  setup() {
    const f = this.loc.field;
    this.rocks = []; this.chunks = []; this.parts = new Particles(); this.floaters = [];
    this.p = { x: MW / 2, y: MH - 300, vx: 0, vy: -40, a: -Math.PI / 2, shield: ship.shieldMax, shT: 0 };
    this.cam = { x: this.p.x, y: this.p.y };
    this.dayTimer = 0; this.broken = 0; this.collected = {};
    const depl = S.depl[this.loc.id] || 0;
    const rich = S.events.some(e => e.rich === this.loc.id);
    const n = Math.round(f.count * (1 - depl * 0.55) * (rich ? 1.2 : 1));
    for (let i = 0; i < n; i++) {
      let x, y;
      if (i < 3) { const a = -Math.PI / 2 + (i - 1) * 0.7; x = this.p.x + Math.cos(a) * rand(260, 380); y = this.p.y + Math.sin(a) * rand(260, 380); }
      else do { x = rand(150, MW - 150); y = rand(150, MH - 150); } while (Math.hypot(x - this.p.x, y - this.p.y) < 300);
      this.spawnRock(x, y, pick([3, 3, 2, 2, 1]) === 1 ? 2 : 3, null, rich);
    }
    this.drones = [];
    for (let i = 0; i < ship.drones; i++) this.drones.push({ x: this.p.x, y: this.p.y, vx: 0, vy: 0, tgt: null, carry: null, a: i });
    // emboscada
    this.ambush = null;
    const dg = locDanger(this.loc.id) * (1 - ship.avoid);
    if (Math.random() < dg * 0.7) this.ambush = { at: rand(22, 55), warned: false };
    this.heatWarn = 0;
  },
  spawnRock(x, y, tier, ore, rich) {
    const f = this.loc.field;
    if (!ore) {
      const tot = Object.values(f.ores).reduce((a, b) => a + b, 0);
      let r = Math.random() * tot; ore = Object.keys(f.ores)[0];
      for (const k in f.ores) { r -= f.ores[k]; if (r <= 0) { ore = k; break; } }
    }
    const R = [0, 20, 34, 56][tier] * rand(0.9, 1.15);
    const isRich = Math.random() < (rich ? 0.3 : 0.1);
    const nv = 2 + Math.floor(tier * 1.5);
    const rock = {
      x, y, vx: rand(-18, 18), vy: rand(-18, 18), rot: rand(0, TAU), vr: rand(-0.4, 0.4), r: R, tier, ore, rich: isRich,
      hp: R * 0.7 * ITEMS[ore].h, maxhp: R * 0.7 * ITEMS[ore].h, hit: 0, cold: f.cold,
      shape: makeRockShape(9 + tier * 2, 0.22),
      veins: Array.from({ length: nv }, () => { const a = rand(0, TAU), d = rand(0, 0.6); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.07, 0.16)]; }),
      craters: Array.from({ length: tier }, () => { const a = rand(0, TAU), d = rand(0, 0.5); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.1, 0.2)]; }),
    };
    this.rocks.push(rock);
    return rock;
  },
  breakRock(r) {
    this.rocks = this.rocks.filter(x => x !== r);
    this.parts.burst(r.x, r.y, 14 + r.tier * 8, '#c9b8a6', 120 + r.tier * 40, 0.8, 2.5);
    this.parts.burst(r.x, r.y, 6 + r.tier * 3, ITEMS[r.ore].c, 90, 1, 2.5);
    sfx('break'); this.shake = Math.max(this.shake, r.tier * 3);
    if (r.tier > 1) {
      for (let i = 0; i < 2; i++) {
        const c = this.spawnRock(r.x + rand(-10, 10), r.y + rand(-10, 10), r.tier - 1, r.ore);
        const a = rand(0, TAU); c.vx = r.vx + Math.cos(a) * 50; c.vy = r.vy + Math.sin(a) * 50; c.rich = r.rich;
      }
      if (Math.random() < 0.5) this.dropChunk(r.x, r.y, r.ore);
    } else {
      const n = randi(1, 2) + (r.rich ? 2 : 0);
      for (let i = 0; i < n; i++) this.dropChunk(r.x, r.y, r.ore);
    }
    S.hints.laser = 1;
    if (r.tier === 3) { this.broken++; S.depl[this.loc.id] = Math.min(1, (S.depl[this.loc.id] || 0) + 0.02); }
  },
  dropChunk(x, y, ore) {
    const a = rand(0, TAU), v = rand(20, 60);
    this.chunks.push({ x, y, vx: Math.cos(a) * v, vy: Math.sin(a) * v, ore, rot: rand(0, TAU), life: 45 });
  },
  collect(c) {
    if (cargoFree() <= 0) return false;
    addCargo(c.ore, 1); S.stats.mined++;
    this.collected[c.ore] = (this.collected[c.ore] || 0) + 1;
    this.floaters.push({ x: this.p.x, y: this.p.y - 20, txt: '+1 ' + ITEMS[c.ore].n, col: ITEMS[c.ore].c, life: 1.1 });
    sfx('pickup');
    return true;
  },
  update(dt) {
    this.t += dt;
    const p = this.p;
    // --- entrada ---
    let ax = 0, ay = 0;
    if (keys.has('KeyW') || keys.has('ArrowUp')) ay -= 1;
    if (keys.has('KeyS') || keys.has('ArrowDown')) ay += 1;
    if (keys.has('KeyA') || keys.has('ArrowLeft')) ax -= 1;
    if (keys.has('KeyD') || keys.has('ArrowRight')) ax += 1;
    if (joy.active) { ax = joy.dx; ay = joy.dy; }
    const al = Math.hypot(ax, ay);
    if (al > 1) { ax /= al; ay /= al; }
    const acc = 520 * ship.thrust / Math.pow(ship.mass, 0.35);
    p.vx += ax * acc * dt; p.vy += ay * acc * dt;
    const drag = Math.pow(0.4, dt);
    p.vx *= drag; p.vy *= drag;
    const maxV = 340 * ship.thrust;
    const v = Math.hypot(p.vx, p.vy);
    if (v > maxV) { p.vx *= maxV / v; p.vy *= maxV / v; }
    p.x = clamp(p.x + p.vx * dt, 40, MW - 40); p.y = clamp(p.y + p.vy * dt, 40, MH - 40);
    this.thrusting = Math.hypot(ax, ay);
    // --- apuntar / láser ---
    let aim = null;
    const wm = { x: mouse.x - W / 2 + this.cam.x, y: mouse.y - H / 2 + this.cam.y };
    let firing = false;
    if (touchFire) {
      let best = null, bd = ship.laserRange + 40;
      for (const r of this.rocks) { const d = Math.hypot(r.x - p.x, r.y - p.y) - r.r; if (d < bd) { bd = d; best = r; } }
      if (best) { aim = Math.atan2(best.y - p.y, best.x - p.x); firing = true; }
    } else if (mouse.down && !mouse.onUI) { aim = Math.atan2(wm.y - p.y, wm.x - p.x); firing = true; }
    if (keys.has('Space')) { firing = true; if (aim == null) aim = p.a; }
    const targetA = aim != null ? aim : (al > 0.1 ? Math.atan2(ay, ax) : p.a);
    let da = ((targetA - p.a + Math.PI) % TAU + TAU) % TAU - Math.PI;
    p.a += da * Math.min(1, dt * 10);
    this.laserHit = null;
    if (firing) {
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
        if (Math.random() < dt * 30) this.parts.add(hx, hy, -dx * 80 + rand(-60, 60), -dy * 80 + rand(-60, 60), 0.4, Math.random() < 0.5 ? ITEMS[best.ore].c : laserColor(S.lv.laser), 2, true);
        if (best.hp <= 0) this.breakRock(best);
      }
    }
    if (firing !== this.laserOn) { this.laserOn = firing; laserSound(firing, S.lv.laser); }
    // --- rocas ---
    for (const r of this.rocks) {
      r.x += r.vx * dt; r.y += r.vy * dt; r.rot += r.vr * dt; r.hit = Math.max(0, r.hit - dt);
      if (r.x < r.r || r.x > MW - r.r) r.vx *= -1;
      if (r.y < r.r || r.y > MH - r.r) r.vy *= -1;
      r.x = clamp(r.x, r.r, MW - r.r); r.y = clamp(r.y, r.r, MH - r.r);
      // colisión con nave
      const dx = p.x - r.x, dy = p.y - r.y, d = Math.hypot(dx, dy), md = r.r + shipR() * 0.4;
      if (d < md && d > 0) {
        const nx = dx / d, ny = dy / d;
        p.x = r.x + nx * md; p.y = r.y + ny * md;
        const rel = (p.vx - r.vx) * nx + (p.vy - r.vy) * ny;
        if (rel < 0) {
          p.vx -= 1.6 * rel * nx; p.vy -= 1.6 * rel * ny;
          r.vx += rel * nx * 0.2 / r.tier; r.vy += rel * ny * 0.2 / r.tier;
          if (-rel > 140) { this.damage((-rel - 120) * 0.05); sfx('bump'); this.shake = 6; }
        }
      }
    }
    // --- fragmentos ---
    const cfree = cargoFree();
    for (const c of this.chunks) {
      c.x += c.vx * dt; c.y += c.vy * dt; c.vx *= Math.pow(0.5, dt); c.vy *= Math.pow(0.5, dt); c.life -= dt;
      const dx = p.x - c.x, dy = p.y - c.y, d = Math.hypot(dx, dy);
      if (d < ship.magnet && cfree > 0) { const f = 600 * (1 - d / ship.magnet) + 120; c.vx += dx / d * f * dt; c.vy += dy / d * f * dt; }
      if (d < 22) { if (this.collect(c)) c.dead = true; else if (this.fullWarn <= 0) { this.fullWarn = 3; sfx('full'); } }
      if (c.life <= 0) c.dead = true;
    }
    this.fullWarn -= dt;
    this.chunks = this.chunks.filter(c => !c.dead);
    // --- drones recolectores ---
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
      else { const a = this.t * 1.5 + dr.a * TAU / Math.max(1, this.drones.length); tx = p.x + Math.cos(a) * 45; ty = p.y + Math.sin(a) * 45; }
      const dx = tx - dr.x, dy = ty - dr.y, d = Math.hypot(dx, dy) || 1;
      const sp = 380;
      dr.vx = lerp(dr.vx, dx / d * Math.min(sp, d * 6), dt * 6); dr.vy = lerp(dr.vy, dy / d * Math.min(sp, d * 6), dt * 6);
      dr.x += dr.vx * dt; dr.y += dr.vy * dt;
      if (dr.tgt && d < 12) { dr.carry = dr.tgt; dr.tgt.dead = true; this.chunks = this.chunks.filter(c => c !== dr.carry); dr.tgt = null; }
      if (dr.carry && d < 20) { if (!this.collect(dr.carry)) this.chunks.push(Object.assign(dr.carry, { dead: false, x: dr.x, y: dr.y, vx: 0, vy: 0 })); dr.carry = null; }
    }
    // --- escudo + peligros ---
    p.shT -= dt;
    if (p.shT <= 0) p.shield = Math.min(ship.shieldMax, p.shield + (4 + S.lv.shield * 2) * dt);
    if (this.loc.field.hazard === 'heat') {
      this.damage(1.1 * dt, true);
      this.heatWarn += dt;
    }
    // --- emboscada ---
    if (this.ambush) {
      this.ambush.at -= dt;
      if (!this.ambush.warned && this.ambush.at < 4) { this.ambush.warned = true; toast('⚠ Hostile ships incoming!', 'bad'); sfx('alarm'); }
      if (this.ambush.at <= 0) {
        this.ambush = null; laserSound(false); this.laserOn = false; mouse.down = false; touchFire = false;
        pirateEncounter(locDanger(this.loc.id), () => {});
        return;
      }
    }
    // --- tiempo ---
    this.dayTimer += dt;
    if (this.dayTimer > 40) { this.dayTimer = 0; tickDay(); updateHUD(); }
    // respawn lento de rocas si quedan pocas
    if (this.rocks.length < 4 && Math.random() < dt * 0.1) {
      const a = rand(0, TAU); this.spawnRock(clamp(p.x + Math.cos(a) * 900, 150, MW - 150), clamp(p.y + Math.sin(a) * 900, 150, MH - 150), 3);
    }
    this.parts.update(dt);
    for (const f of this.floaters) { f.y -= 30 * dt; f.life -= dt; }
    this.floaters = this.floaters.filter(f => f.life > 0);
    // cámara
    const k = 1 - Math.pow(0.001, dt);
    this.cam.x = lerp(this.cam.x, p.x + p.vx * 0.3, k); this.cam.y = lerp(this.cam.y, p.y + p.vy * 0.3, k);
    this.shake = Math.max(0, this.shake - dt * 20);
    // estela
    if (this.thrusting > 0.1 && Math.random() < dt * 40) {
      const bx = p.x - Math.cos(p.a) * shipR() * 0.75, by = p.y - Math.sin(p.a) * shipR() * 0.75;
      this.parts.add(bx, by, -Math.cos(p.a) * 60 + rand(-15, 15), -Math.sin(p.a) * 60 + rand(-15, 15), 0.45, '#ff9b4a', 2.5);
    }
    this.coach();
    updateMineHUD();
  },
  coach() {
    const h = S.hints;
    if (!h.move) { this.moved = (this.moved || 0) + Math.hypot(this.p.vx, this.p.vy) * 0.016; if (this.moved > 120) h.move = 1; }
    let msg = '';
    if (!h.move) msg = isTouch ? 'Drag anywhere on the left side to fly' : 'Fly with <b>WASD</b> or the <b>arrow keys</b>';
    else if (!h.laser) msg = isTouch ? 'Hold <b>LASER</b> — it aims at the nearest rock' : 'Hold the <b>mouse button</b> to fire your mining laser at a rock';
    else if (S.stats.mined < 4) msg = 'Fly close to the glowing crystals to scoop them up';
    if (cargoFree() <= 0) msg = '';
    coach(msg);
  },
  damage(n, heat) {
    const p = this.p;
    if (p.shield > 0) { const a = Math.min(p.shield, n); p.shield -= a; n -= a; if (!heat) p.shT = 2; }
    if (n > 0) {
      S.hull -= n;
      if (S.hull <= 0) {
        S.hull = 0; laserSound(false); this.laserOn = false;
        towShip('Your hull collapsed in the mining field.');
      }
    }
  },
  draw(ctx) {
    const t = this.t;
    const sx = (Math.random() - 0.5) * this.shake, sy = (Math.random() - 0.5) * this.shake;
    const cx = this.cam.x - W / 2 + sx, cy = this.cam.y - H / 2 + sy;
    drawSpaceBg(ctx, W, H, cx, cy, t, this.loc.cold ? '#0c1838' : this.loc.field.hazard === 'heat' ? '#2a1408' : null);
    // cuerpo celeste de fondo
    const bgLoc = this.loc.id === 'kuiper' ? LOC.pluton : this.loc.parent ? LOC[this.loc.parent] : this.loc.follow ? LOC[this.loc.follow] : this.loc;
    const bx = W * 0.78 - cx * 0.04, by = H * 0.3 - cy * 0.04;
    ctx.globalAlpha = 0.8; drawPlanet(ctx, bx, by, Math.min(W, H) * (bgLoc.size > 12 ? 0.26 : 0.15), bgLoc, Math.atan2(-by, -bx - W), t); ctx.globalAlpha = 1;
    if (this.loc.field.hazard === 'heat') drawSun(ctx, -cx * 0.02 - 40, H * 0.5 - cy * 0.02, 120, t);
    ctx.save();
    ctx.translate(-cx, -cy);
    // bordes del campo
    ctx.strokeStyle = 'rgba(61,232,255,0.15)'; ctx.setLineDash([10, 12]); ctx.lineWidth = 2;
    ctx.strokeRect(20, 20, MW - 40, MH - 40); ctx.setLineDash([]);
    // imán
    const p = this.p;
    if (cargoFree() > 0) {
      ctx.strokeStyle = 'rgba(61,232,255,0.07)'; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.arc(p.x, p.y, ship.magnet, 0, TAU); ctx.stroke();
    }
    for (const r of this.rocks) if (r.x > cx - 100 && r.x < cx + W + 100 && r.y > cy - 100 && r.y < cy + H + 100) drawRock(ctx, r, t, S.lv.scanner);
    for (const c of this.chunks) drawOreChunk(ctx, c, t);
    // láser
    if (this.laserHit) {
      const L = this.laserHit, col = laserColor(S.lv.laser);
      const nx = p.x + Math.cos(L.dir) * shipR() * 0.9, ny = p.y + Math.sin(L.dir) * shipR() * 0.9;
      ctx.globalCompositeOperation = 'lighter';
      ctx.strokeStyle = col; ctx.globalAlpha = 0.35; ctx.lineWidth = 7 + S.lv.laser + Math.sin(t * 50) * 2;
      ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(L.x, L.y); ctx.stroke();
      ctx.globalAlpha = 1; ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 1.8;
      ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(L.x, L.y); ctx.stroke();
      ctx.globalCompositeOperation = 'source-over';
      glow(ctx, L.x, L.y, L.rock ? 26 : 10, col, 0.9);
    }
    // drones
    for (const dr of this.drones) {
      glow(ctx, dr.x, dr.y, 10, '#3de8ff88', 0.8);
      ctx.fillStyle = '#d4dcea'; ctx.beginPath(); ctx.arc(dr.x, dr.y, 4, 0, TAU); ctx.fill();
      ctx.fillStyle = '#3de8ff'; ctx.beginPath(); ctx.arc(dr.x, dr.y, 1.8, 0, TAU); ctx.fill();
      if (dr.carry) { ctx.fillStyle = ITEMS[dr.carry.ore].c; ctx.fillRect(dr.x - 2, dr.y + 4, 4, 4); }
    }
    this.parts.draw(ctx);
    drawPlayerShip(ctx, S.lv, p.x, p.y, p.a, mineScale(), this.thrusting, t);
    if (ship.shieldMax > 0 && p.shT > 1.5) {
      ctx.strokeStyle = `rgba(61,232,255,${(p.shT - 1.5) * 1.5})`; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(p.x, p.y, shipR() + 8, 0, TAU); ctx.stroke();
    }
    // textos flotantes
    ctx.font = '600 13px Rajdhani, sans-serif'; ctx.textAlign = 'center';
    for (const f of this.floaters) { ctx.globalAlpha = Math.min(1, f.life * 2); ctx.fillStyle = f.col; ctx.fillText(f.txt, f.x, f.y); }
    ctx.globalAlpha = 1;
    ctx.restore();
    // miras
    if (!isTouch && !mouse.onUI) {
      ctx.strokeStyle = 'rgba(61,232,255,0.8)'; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.arc(mouse.x, mouse.y, 9, 0, TAU);
      ctx.moveTo(mouse.x - 14, mouse.y); ctx.lineTo(mouse.x - 5, mouse.y); ctx.moveTo(mouse.x + 5, mouse.y); ctx.lineTo(mouse.x + 14, mouse.y);
      ctx.moveTo(mouse.x, mouse.y - 14); ctx.lineTo(mouse.x, mouse.y - 5); ctx.moveTo(mouse.x, mouse.y + 5); ctx.lineTo(mouse.x, mouse.y + 14);
      ctx.stroke();
    }
    // minimapa
    const mm = 110, mx = W - mm - 14, my = H - mm - (isTouch ? 205 : 40);
    ctx.fillStyle = 'rgba(8,14,34,0.75)'; ctx.strokeStyle = 'rgba(61,232,255,0.35)'; ctx.lineWidth = 1;
    ctx.fillRect(mx, my, mm, mm); ctx.strokeRect(mx, my, mm, mm);
    for (const r of this.rocks) { ctx.fillStyle = r.rich && S.lv.scanner >= 2 ? ITEMS[r.ore].c : 'rgba(200,190,170,0.7)'; ctx.fillRect(mx + r.x / MW * mm - 1, my + r.y / MH * mm - 1, r.tier + 0.5, r.tier + 0.5); }
    ctx.fillStyle = '#3de8ff'; ctx.fillRect(mx + p.x / MW * mm - 2, my + p.y / MH * mm - 2, 4, 4);
    if (this.loc.field.hazard === 'heat' && ship.shieldMax <= 0) {
      ctx.fillStyle = `rgba(255,120,40,${0.08 + 0.05 * Math.sin(t * 4)})`; ctx.fillRect(0, 0, W, H);
    }
  },
  leave(toMap) {
    laserSound(false);
    const got = Object.entries(this.collected);
    if (got.length) addNews('⛏️', `Mined at ${this.loc.field.n}: ${got.map(([k, n]) => `${n} ${ITEMS[k].n}`).join(', ')}`, '#ffd24a');
    this.collected = {};
    save();
    if (!toMap && LOC[S.loc].station) openDock();
    else setScene(MapScene);
  },
};

function towShip(reason) {
  const lost = {};
  for (const k in S.cargo) { const n = Math.ceil(S.cargo[k] * 0.6); lost[k] = n; addCargo(k, -n); }
  const markets = NODES.filter(l => l.station && !l.black && locOpen(l.id));
  let best = markets[0], bd = 1e9;
  for (const l of markets) { const d = locDist(S.loc, l.id, S.day); if (d < bd) { bd = d; best = l; } }
  const fee = Math.round(Math.min(S.credits, 200 + S.credits * 0.1));
  S.credits -= fee; S.loc = best.id; S.hull = Math.max(S.hull, Math.round(ship.hpMax * 0.25));
  S.fuel = Math.max(S.fuel, 10);
  for (let i = 0; i < 3; i++) tickDay();
  sfx('lose');
  showModal({ icon: '🚨', title: 'Towed to safety', danger: true, html: `${reason}<br>A tug brings you to <b>${best.station}</b>. You lost part of your cargo and paid a <b>${fmt(fee)} cr</b> rescue fee.`,
    buttons: [{ label: 'Continue', cls: 'primary', fn: () => { save(); openDock(); } }] });
}
