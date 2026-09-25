'use strict';
// ============ REAL-TIME COMBAT (used inside the mining / space arena) ============
function buildFleet(danger) {
  let budget = (1 + danger * 7) * rand(0.7, 1.25);
  const fleet = [];
  const order = ['carrier', 'frigate', 'corsair', 'raider'];
  while (budget > 0.8 && fleet.length < 6) {
    const opts = order.filter(k => ENEMIES[k].pow <= budget);
    if (!opts.length) break;
    const k = Math.random() < 0.5 ? opts[0] : pick(opts);
    fleet.push(k); budget -= ENEMIES[k].pow;
  }
  if (!fleet.length) fleet.push('raider');
  return fleet;
}
function fleetThreat(fleet, z) {
  const m = Z_ENEMY[z];
  let ehp = 0, dps = 0;
  for (const k of fleet) { const e = ENEMIES[k]; ehp += (e.hp + e.sp) * m; dps += e.dmg * m * (e.burst || 1) / e.rate; }
  const mine = Math.sqrt(Math.max(1, S.hull + ship.shieldMax) * ship.weaponDps * 1.6);
  return Math.sqrt(ehp * dps) / mine;
}

const Combat = {
  spawn(sc, fleet, z, fromTop) {
    const m = Z_ENEMY[z];
    fleet.forEach((k, i) => {
      const e = ENEMIES[k];
      let x, y;
      if (fromTop) { x = clamp(sc.p.x + rand(-500, 500), 120, MW - 120); y = Math.max(80, sc.p.y - rand(650, 900)); }
      else { const a = rand(0, TAU); x = clamp(sc.p.x + Math.cos(a) * rand(520, 700), 80, MW - 80); y = clamp(sc.p.y + Math.sin(a) * rand(520, 700), 80, MH - 80); }
      sc.enemies.push({ k, x, y, vx: 0, vy: 0, a: 0, hp: e.hp * m, max: e.hp * m, sp: e.sp * m, spMax: e.sp * m, dmg: e.dmg * m,
        rate: e.rate, spd: e.spd, size: e.size, cd: rand(0.8, 2), burstLeft: 0, burstT: 0, strafe: Math.random() < 0.5 ? 1 : -1,
        prefer: rand(200, 330) * (0.8 + e.size * 0.3), shT: 0, hitT: 0, loot: e.loot * Z_LOOT[z], military: e.military });
    });
    sc.combatZ = z;
    sc.hadCombat = true;
  },
  fireEnemy(sc, e) {
    const p = sc.p;
    const dist = Math.hypot(p.x - e.x, p.y - e.y);
    const lead = dist / 460 * 0.6;
    const tx = p.x + p.vx * lead, ty = p.y + p.vy * lead;
    const a = Math.atan2(ty - e.y, tx - e.x) + rand(-0.09, 0.09);
    sc.bolts.push({ x: e.x + Math.cos(a) * 18 * e.size, y: e.y + Math.sin(a) * 18 * e.size, vx: Math.cos(a) * 460, vy: Math.sin(a) * 460, life: 2, dmg: e.dmg, foe: 1, col: e.military ? '#b6ff7a' : '#ff4d6d' });
    sfx('eshoot');
  },
  firePlayer(sc, aim) {
    const p = sc.p, r = shipR();
    const per = ship.weaponDps * 0.25 / 2;
    for (const side of [-1, 1]) {
      const ox = Math.cos(p.a) * r * 0.2 - Math.sin(p.a) * side * r * 0.35, oy = Math.sin(p.a) * r * 0.2 + Math.cos(p.a) * side * r * 0.35;
      const a = aim + rand(-0.03, 0.03);
      sc.bolts.push({ x: p.x + ox, y: p.y + oy, vx: Math.cos(a) * 880 + p.vx * 0.5, vy: Math.sin(a) * 880 + p.vy * 0.5, life: 1.1, dmg: per, foe: 0, col: '#3de8ff' });
    }
    sfx('shoot');
  },
  hitEnemy(sc, e, dmg) {
    e.shT = 2.2;
    if (e.sp > 0) { const a = Math.min(e.sp, dmg); e.sp -= a; dmg -= a; e.shieldFlash = 0.25; }
    if (dmg > 0) { e.hp -= dmg; e.hitT = 0.08; }
    if (e.hp <= 0 && !e.dead) this.kill(sc, e);
  },
  kill(sc, e) {
    e.dead = true;
    sc.parts.burst(e.x, e.y, 50, '#ffb347', 280, 1.1, 4);
    sc.parts.burst(e.x, e.y, 25, '#ffffff', 190, 0.6, 3);
    sfx('boom'); sc.shake = Math.max(sc.shake, 10);
    S.stats.kills++;
    // loot: credit orbs + some ore
    const orbs = randi(3, 6);
    for (let i = 0; i < orbs; i++) {
      const a = rand(0, TAU), v = rand(40, 140);
      sc.chunks.push({ x: e.x, y: e.y, vx: Math.cos(a) * v, vy: Math.sin(a) * v, cr: e.loot * incomeMult() / orbs, rot: rand(0, TAU), life: 40 });
    }
    if (!e.military && sc.loc && sc.loc.field) for (let i = 0; i < randi(1, 4); i++) sc.dropChunk(e.x, e.y, sc.pickOre(0.8));
  },
  update(sc, dt) {
    const p = sc.p;
    for (const e of sc.enemies) {
      if (e.dead) continue;
      const dx = p.x - e.x, dy = p.y - e.y, d = Math.hypot(dx, dy) || 1;
      const nx = dx / d, ny = dy / d;
      const radial = clamp((d - e.prefer) / 150, -1, 1);
      const tvx = (nx * radial + -ny * e.strafe * 0.8) * e.spd, tvy = (ny * radial + nx * e.strafe * 0.8) * e.spd;
      e.vx = lerp(e.vx, tvx, dt * 2); e.vy = lerp(e.vy, tvy, dt * 2);
      e.x = clamp(e.x + e.vx * dt, 40, MW - 40); e.y = clamp(e.y + e.vy * dt, 40, MH - 40);
      if (Math.random() < dt * 0.3) e.strafe *= -1;
      e.a = Math.atan2(dy, dx);
      e.shT -= dt; e.hitT -= dt; if (e.shieldFlash) e.shieldFlash -= dt;
      if (e.shT <= 0 && e.spMax) e.sp = Math.min(e.spMax, e.sp + e.spMax * 0.15 * dt);
      if (d < 750) {
        e.cd -= dt;
        if (e.cd <= 0) { e.burstLeft = ENEMIES[e.k].burst || 1; e.cd = e.rate * rand(0.85, 1.2); }
        if (e.burstLeft > 0) { e.burstT -= dt; if (e.burstT <= 0) { this.fireEnemy(sc, e); e.burstLeft--; e.burstT = 0.12; } }
      }
      if (Math.random() < dt * 20) sc.parts.add(e.x - Math.cos(e.a) * 16 * e.size, e.y - Math.sin(e.a) * 16 * e.size, rand(-20, 20), rand(-20, 20), 0.3, e.military ? '#9fe0ff' : '#ff6a3a', 2);
    }
    // escort gunships (Private Security Fleet)
    for (const es of sc.escorts || []) {
      const ang = sc.t * 0.9 + es.i * Math.PI;
      const tx = p.x + Math.cos(ang) * 110, ty = p.y + Math.sin(ang) * 110;
      es.x = lerp(es.x || tx, tx, dt * 3); es.y = lerp(es.y || ty, ty, dt * 3);
      const tgt = sc.enemies.filter(e => !e.dead).sort((a, b) => Math.hypot(a.x - es.x, a.y - es.y) - Math.hypot(b.x - es.x, b.y - es.y))[0];
      es.a = tgt ? Math.atan2(tgt.y - es.y, tgt.x - es.x) : p.a;
      es.gcd -= dt;
      if (tgt && es.gcd <= 0 && Math.hypot(tgt.x - es.x, tgt.y - es.y) < 650) {
        es.gcd = 0.35;
        sc.bolts.push({ x: es.x, y: es.y, vx: Math.cos(es.a) * 800, vy: Math.sin(es.a) * 800, life: 1, dmg: ship.weaponDps * 0.12, foe: 0, col: '#ffd24a' });
      }
    }
    // ship drones shoot too
    if (sc.enemies.some(e => !e.dead)) for (const dr of sc.drones) {
      dr.gcd = (dr.gcd || rand(0, 0.8)) - dt;
      if (dr.gcd <= 0) {
        dr.gcd = 0.8;
        const tgt = sc.enemies.filter(e => !e.dead).sort((a, b) => Math.hypot(a.x - dr.x, a.y - dr.y) - Math.hypot(b.x - dr.x, b.y - dr.y))[0];
        if (tgt && Math.hypot(tgt.x - dr.x, tgt.y - dr.y) < 550) {
          const a = Math.atan2(tgt.y - dr.y, tgt.x - dr.x);
          sc.bolts.push({ x: dr.x, y: dr.y, vx: Math.cos(a) * 700, vy: Math.sin(a) * 700, life: 1, dmg: ship.weaponDps * 0.12, foe: 0, col: '#6dffb0' });
        }
      }
    }
    // bolts
    const pr = shipR() * 0.55;
    for (const b of sc.bolts) {
      b.x += b.vx * dt; b.y += b.vy * dt; b.life -= dt;
      if (b.life <= 0) { b.dead = true; continue; }
      if (b.foe) {
        if (Math.hypot(b.x - p.x, b.y - p.y) < pr + 4) { b.dead = true; sc.damage(b.dmg); sc.parts.burst(b.x, b.y, 8, p.shield > 0 ? '#3de8ff' : '#ffb347', 90, 0.35, 2); sfx(p.shield > 0 ? 'shield' : 'hit'); sc.shake = Math.max(sc.shake, 4); continue; }
      } else {
        for (const e of sc.enemies) if (!e.dead && Math.hypot(b.x - e.x, b.y - e.y) < 18 * e.size + 3) {
          b.dead = true; this.hitEnemy(sc, e, b.dmg);
          sc.parts.burst(b.x, b.y, 5, e.sp > 0 ? '#ff8fb0' : '#ffd24a', 80, 0.3, 2);
          break;
        }
        if (b.dead) continue;
      }
      for (const r of sc.rocks) if (Math.hypot(b.x - r.x, b.y - r.y) < r.r * 0.85) {
        b.dead = true;
        sc.parts.burst(b.x, b.y, 4, '#c9b8a6', 60, 0.3, 2);
        if (!b.foe) { r.hp -= b.dmg * 0.5; r.hit = 0.05; if (r.hp <= 0) sc.breakRock(r); }
        break;
      }
    }
    sc.bolts = sc.bolts.filter(b => !b.dead);
    const before = sc.enemies.length;
    sc.enemies = sc.enemies.filter(e => !e.dead);
    if (before && !sc.enemies.length && sc.hadCombat) sc.onVictory();
  },
  draw(sc, ctx, t) {
    ctx.globalCompositeOperation = 'lighter';
    for (const b of sc.bolts) {
      const a = Math.atan2(b.vy, b.vx);
      ctx.strokeStyle = b.col; ctx.lineWidth = b.foe ? 3.5 : 3;
      ctx.beginPath(); ctx.moveTo(b.x, b.y); ctx.lineTo(b.x - Math.cos(a) * 16, b.y - Math.sin(a) * 16); ctx.stroke();
      glow(ctx, b.x, b.y, b.foe ? 10 : 8, b.col, 0.8);
    }
    ctx.globalCompositeOperation = 'source-over';
    for (const es of sc.escorts || []) if (es.x) drawPlayerShip(ctx, { hull: 1, engine: 3, weapons: 3, laser: 1 }, es.x, es.y, es.a, 0.8, 0.6, t);
    for (const e of sc.enemies) {
      drawEnemyShip(ctx, e.k, e.x, e.y, e.a, 1.3, t);
      if (e.hitT > 0) glow(ctx, e.x, e.y, 30 * e.size, '#ffffff', 0.6);
      if (e.shieldFlash > 0) { ctx.strokeStyle = `rgba(255,120,160,${e.shieldFlash * 3})`; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(e.x, e.y, 30 * e.size, 0, TAU); ctx.stroke(); }
      const w = 50 * e.size, y = e.y - 32 * e.size - 8;
      ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(e.x - w / 2 - 1, y - 1, w + 2, e.spMax ? 9 : 6);
      ctx.fillStyle = '#ff4d6d'; ctx.fillRect(e.x - w / 2, y, w * clamp(e.hp / e.max, 0, 1), 4);
      if (e.spMax) { ctx.fillStyle = '#ff9ec0'; ctx.fillRect(e.x - w / 2, y + 5, w * clamp(e.sp / e.spMax, 0, 1), 3); }
    }
  },
};
