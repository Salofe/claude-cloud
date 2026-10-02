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
// enemies of later systems get much tougher, but their damage grows slower (√) so fights stay short and fair
const enemyDmgMult = () => Math.sqrt(sysDef().enemy);
function fleetThreat(fleet, z) {
  const m = Z_ENEMY[z] * sysDef().enemy, md = Z_ENEMY[z] * enemyDmgMult();
  let ehp = 0, dps = 0;
  for (const k of fleet) { const e = ENEMIES[k]; ehp += (e.hp + e.sp) * m; dps += e.dmg * md * (e.burst || 1) / e.rate; }
  const mine = Math.sqrt(Math.max(1, S.hull + ship.shieldMax) * ship.weaponDps * 1.6);
  return Math.sqrt(ehp * dps) / mine;
}

Object.assign(TXT, {
  bat_shielded: { en: 'SHIELDED — destroy the shards first!', es: 'CON ESCUDO: ¡destruye primero los fragmentos!' },
  bat_phoenix: { en: 'THE PHOENIX RISES AGAIN!', es: '¡EL FÉNIX RENACE!' },
  bat_hydra: { en: 'THE HYDRA SPLITS IN TWO!', es: '¡LA HIDRA SE DIVIDE EN DOS!' },
});

const Combat = {
  spawn(sc, fleet, z, fromTop) {
    const m = Z_ENEMY[z] * sysDef().enemy, md = Z_ENEMY[z] * enemyDmgMult();
    fleet.forEach((k, i) => {
      const e = ENEMIES[k];
      let x, y;
      if (fromTop) { x = clamp(sc.p.x + rand(-500, 500), 120, MW - 120); y = Math.max(80, sc.p.y - rand(650, 900)); }
      else { const a = rand(0, TAU); x = clamp(sc.p.x + Math.cos(a) * rand(520, 700), 80, MW - 80); y = clamp(sc.p.y + Math.sin(a) * rand(520, 700), 80, MH - 80); }
      sc.enemies.push({ k, x, y, vx: 0, vy: 0, a: 0, hp: e.hp * m, max: e.hp * m, sp: e.sp * m, spMax: e.sp * m, dmg: e.dmg * md,
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
    const E = ENEMIES[e.k], n = E.spiral || E.radial || E.spread || 1, col = E.alien ? '#9ffcff' : E.hive ? '#b0ff9a' : E.mech ? '#ffb030' : E.serpent ? '#ffe080' : E.fort ? '#ffa860' : E.whale ? '#bfefff' : E.kraken ? '#d090ff' : E.radiant ? '#bfe8ff' : E.phoenix ? (e.reborn ? '#90c8ff' : '#ffb040') : E.hydra ? '#ff9ad8' : E.warden ? '#bfe8ff' : E.archon ? '#ffe080' : E.devourer ? '#d080ff' : e.military ? '#b6ff7a' : '#ff4d6d';
    if (E.spiral) e.spin = (e.spin || 0) + 0.32;
    for (let i = 0; i < n; i++) {
      const b = E.spiral ? e.spin + i * TAU / n : E.radial ? a + i * TAU / n : a + (i - (n - 1) / 2) * 0.2;
      sc.bolts.push({ x: e.x + Math.cos(b) * 18 * e.size, y: e.y + Math.sin(b) * 18 * e.size, vx: Math.cos(b) * 460, vy: Math.sin(b) * 460, life: 2, dmg: e.dmg, foe: 1, col });
    }
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
    if (ENEMIES[e.k].ward && sc.enemies.some(o => !o.dead && o.k === ENEMIES[e.k].summon)) {   // the Archon hides behind its shield shards
      dmg *= 0.1; e.wardFlash = 0.3;
      if (!sc.wardHint) { sc.wardHint = 1; sc.floaters.push({ x: e.x, y: e.y - 90, txt: tx('bat_shielded'), col: '#ffe080', life: 2.5, big: 1 }); }
    }
    if (e.sp > 0) { const a = Math.min(e.sp, dmg); e.sp -= a; dmg -= a; e.shieldFlash = 0.25; }
    if (dmg > 0) { e.hp -= dmg; e.hitT = 0.08; }
    if (e.hp <= 0 && !e.dead && ENEMIES[e.k].rebirth && !e.reborn) {   // the Phoenix rises once from its ashes
      e.reborn = 1; e.hp = e.max * 0.5; e.sp = e.spMax; e.shT = 0;
      sc.parts.burst(e.x, e.y, 90, '#90c8ff', 380, 1.2, 4); sc.shake = Math.max(sc.shake, 18); sfx('boom');
      for (let i = 0; i < 16; i++) { const b = i * TAU / 16; sc.bolts.push({ x: e.x, y: e.y, vx: Math.cos(b) * 380, vy: Math.sin(b) * 380, life: 2.2, dmg: e.dmg, foe: 1, col: '#90c8ff' }); }
      sc.floaters.push({ x: e.x, y: e.y - 90, txt: tx('bat_phoenix'), col: '#90c8ff', life: 2.5, big: 1 });
      return;
    }
    if (e.hp <= 0 && !e.dead) this.kill(sc, e);
  },
  kill(sc, e) {
    e.dead = true;
    sc.parts.burst(e.x, e.y, 50, '#ffb347', 280, 1.1, 4);
    sc.parts.burst(e.x, e.y, 25, '#ffffff', 190, 0.6, 3);
    sfx('boom'); sc.shake = Math.max(sc.shake, 10);
    S.stats.kills++;
    const KE = ENEMIES[e.k];
    if (KE.split) {   // the Hydra splits into two fast heads
      const m = e.max / KE.hp, H = ENEMIES[KE.split];
      for (const side of [-1, 1]) sc.enemies.push({ k: KE.split, x: e.x + side * 60, y: e.y, vx: side * 200, vy: 0, a: 0, hp: H.hp * m, max: H.hp * m, sp: H.sp * m, spMax: H.sp * m, dmg: H.dmg * e.dmg / KE.dmg,
        rate: H.rate, spd: H.spd, size: H.size, cd: rand(0.8, 1.6), burstLeft: 0, burstT: 0, strafe: side, prefer: rand(200, 300), shT: 0, hitT: 0, loot: H.loot * Z_LOOT[sc.combatZ || 0] });
      sc.floaters.push({ x: e.x, y: e.y - 80, txt: tx('bat_hydra'),
 col: '#ff9ad8', life: 2.5, big: 1 });
      sc.parts.burst(e.x, e.y, 80, '#ff9ad8', 300, 1.2, 4);
    } else if (KE.boss && sc.loc) {
      sc.shake = 24; sc.parts.burst(e.x, e.y, 120, KE.alien ? '#9ffcff' : '#ffd24a', 420, 1.6, 5);
      if (KE.final) { if (!sc.enemies.some(o => o !== e && !o.dead && ENEMIES[o.k].final)) finalBossKilled(); }
      else warlordKilled(sc.loc.id);
    }
    // loot: credit orbs + some ore
    const orbs = randi(3, 6);
    for (let i = 0; i < orbs; i++) {
      const a = rand(0, TAU), v = rand(40, 140);
      sc.chunks.push({ x: e.x, y: e.y, vx: Math.cos(a) * v, vy: Math.sin(a) * v, cr: e.loot * incomeMult() * (built('bounty') ? 3 : 1) / orbs, rot: rand(0, TAU), life: 40 });
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
      if (ENEMIES[e.k].dash) {
        e.dashCd = (e.dashCd == null ? 4 : e.dashCd) - dt;
        if (e.dashCd <= 0 && d < 750) { e.dashCd = 5; e.dashT = 0.9; e.dvx = nx * 650; e.dvy = ny * 650; sfx('alarm'); }
      }
      // Kraken: squirts ink clouds that slow you down and hide the field
      // Pulsar Warden: two arms of light rotate around it — they burn while lit
      if (ENEMIES[e.k].arms) {
        e.armA = (e.armA || 0) + 0.55 * dt; e.armT = ((e.armT || 0) + dt) % 5.5;
        if (e.armT > 0.8 && e.armT < 3.8) for (let k = 0; k < ENEMIES[e.k].arms; k++) {
          const a = e.armA + k * Math.PI, ux = Math.cos(a), uy = Math.sin(a), along = dx * ux + dy * uy, perp = Math.abs(dx * uy - dy * ux);
          if (along > 0 && along < 760 && perp < 26 + shipR() * 0.4) { sc.damage(e.dmg * 9 * dt); if (Math.random() < dt * 8) sfx('hit'); }
        }
      }
      // the Devourer: its gravity drags you in, and touching it hurts
      if (ENEMIES[e.k].well && d < 1100) {
        p.vx -= nx * 170 * dt; p.vy -= ny * 170 * dt;
        if (d < 34 * e.size) sc.damage(e.dmg * 8 * dt);
        if (Math.random() < dt * 30) { const a = rand(0, TAU), r0 = rand(200, 500); sc.parts.add(e.x + Math.cos(a) * r0, e.y + Math.sin(a) * r0, -Math.cos(a) * r0 * 1.5, -Math.sin(a) * r0 * 1.5, 0.6, Math.random() < 0.5 ? '#ffb060' : '#c080ff', 2); }
      }
      if (ENEMIES[e.k].ink) {
        e.inkCd = (e.inkCd == null ? 5 : e.inkCd) - dt;
        if (e.inkCd <= 0 && d < 850) {
          e.inkCd = 8; sc.inks = sc.inks || [];
          const ix = p.x + p.vx * 0.4, iy = p.y + p.vy * 0.4;
          sc.inks.push({ x: ix, y: iy, r: 0, R: 230, t: 7 });
          for (let i = 0; i < 24; i++) { const k = i / 24; sc.parts.add(lerp(e.x, ix, k), lerp(e.y, iy, k), rand(-30, 30), rand(-30, 30), 0.6, '#5a2a7a', 5); }
          sfx('bump');
        }
      }
      // Radiant Titan: aims a thin line at you, then fires a beam down it — move out of the line!
      if (ENEMIES[e.k].beam) {
        e.beamCd = (e.beamCd == null ? 5 : e.beamCd) - dt;
        if (!e.beam && e.beamCd <= 0 && d < 900) { e.beam = { a: Math.atan2(dy, dx), t: 1.3, fire: 0 }; tone(300, 1.3, 'sine', 0.05, 900); }
        if (e.beam) {
          const B = e.beam;
          if (B.t > 0) { B.t -= dt; if (B.t <= 0) { B.fire = 0.45; sfx('warp'); sc.shake = Math.max(sc.shake, 8);
            const ux = Math.cos(B.a), uy = Math.sin(B.a), rx = p.x - e.x, ry = p.y - e.y, along = rx * ux + ry * uy, perp = Math.abs(rx * uy - ry * ux);
            if (along > 0 && perp < 34 + shipR() * 0.4) { sc.damage(e.dmg * 12); sc.parts.burst(p.x, p.y, 20, '#bfe8ff', 160, 0.5, 3); } } }
          else { B.fire -= dt; if (B.fire <= 0) { e.beam = null; e.beamCd = 6; } }
        }
      }
      if (e.dashT > 0) {
        e.dashT -= dt; e.vx = e.dvx; e.vy = e.dvy;
        if (d < 30 * e.size) { e.dashT = 0; sc.damage(e.dmg * 10); p.vx += nx * 500; p.vy += ny * 500; sc.shake = 16; sfx('hit'); }
      } else { e.vx = lerp(e.vx, tvx, dt * 2); e.vy = lerp(e.vy, tvy, dt * 2); }
      e.x = clamp(e.x + e.vx * dt, 40, MW - 40); e.y = clamp(e.y + e.vy * dt, 40, MH - 40);
      if (Math.random() < dt * 0.3) e.strafe *= -1;
      e.a = Math.atan2(dy, dx);
      e.shT -= dt; e.hitT -= dt; if (e.shieldFlash) e.shieldFlash -= dt; if (e.wardFlash) e.wardFlash -= dt;
      if (e.shT <= 0 && e.spMax) e.sp = Math.min(e.spMax, e.sp + e.spMax * 0.15 * dt);
      if (d < 750 && !(e.beam && e.beam.t > 0)) {
        e.cd -= dt;
        if (e.cd <= 0) { e.burstLeft = ENEMIES[e.k].burst || 1; e.cd = e.rate * rand(0.85, 1.2); }
        if (e.burstLeft > 0) { e.burstT -= dt; if (e.burstT <= 0) { this.fireEnemy(sc, e); e.burstLeft--; e.burstT = 0.12; } }
      }
      const E = ENEMIES[e.k];
      if (E.summon) {
        e.sumT = (e.sumT == null ? (E.ward ? 0.5 : 4) : e.sumT) - dt;
        if (e.sumT <= 0 && sc.enemies.filter(x => !x.dead && x.k === E.summon).length < (E.summonMax || 6)) {
          e.sumT = E.ward ? 14 : E.summonMax ? 10 : 7;
          const m = e.max / (E.hp * 1), sw = ENEMIES[E.summon];
          for (let i = 0; i < (E.ward ? E.summonMax - sc.enemies.filter(x => !x.dead && x.k === E.summon).length : E.summonMax ? 1 : 2); i++) sc.enemies.push({ k: E.summon, x: e.x + rand(-40, 40), y: e.y + rand(-40, 40), vx: 0, vy: 0, a: 0, hp: sw.hp * m, max: sw.hp * m, sp: sw.sp * m, spMax: sw.sp * m, dmg: sw.dmg * e.dmg / E.dmg,
            rate: sw.rate, spd: sw.spd, size: sw.size, cd: rand(0.8, 2), burstLeft: 0, burstT: 0, strafe: Math.random() < 0.5 ? 1 : -1, prefer: rand(160, 260), shT: 0, hitT: 0, loot: sw.loot * Z_LOOT[sc.combatZ || 0] });
          sc.parts.burst(e.x, e.y, 20, E.hive ? '#b0ff9a' : '#ff8a4a', 150, 0.6, 2);
        }
      }
      if (E.serpent) { e.trail = e.trail || []; e.trT = (e.trT || 0) - dt; if (e.trT <= 0) { e.trT = 0.045; e.trail.unshift({ x: e.x, y: e.y }); if (e.trail.length > 16) e.trail.pop(); } }
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
    if (sc.inks) { for (const k of sc.inks) { k.t -= dt; k.r = Math.min(k.R, k.r + 600 * dt); } sc.inks = sc.inks.filter(k => k.t > 0); }
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
    for (const e of sc.enemies) if (ENEMIES[e.k].arms) {
      const lit = e.armT > 0.8 && e.armT < 3.8, warm = e.armT > 0.3 && e.armT <= 0.8;
      ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
      for (let k = 0; k < ENEMIES[e.k].arms; k++) {
        const a = (e.armA || 0) + k * Math.PI, x2 = e.x + Math.cos(a) * 760, y2 = e.y + Math.sin(a) * 760;
        if (lit) { ctx.strokeStyle = 'rgba(160,220,255,0.35)'; ctx.lineWidth = 46; ctx.beginPath(); ctx.moveTo(e.x, e.y); ctx.lineTo(x2, y2); ctx.stroke(); ctx.strokeStyle = 'rgba(255,255,255,0.9)'; ctx.lineWidth = 9; ctx.stroke(); }
        else { ctx.strokeStyle = `rgba(160,220,255,${warm ? 0.5 + 0.4 * Math.sin(t * 40) : 0.12})`; ctx.lineWidth = 2; ctx.setLineDash([12, 10]); ctx.beginPath(); ctx.moveTo(e.x, e.y); ctx.lineTo(x2, y2); ctx.stroke(); ctx.setLineDash([]); }
      }
      ctx.globalCompositeOperation = 'source-over'; ctx.lineCap = 'butt';
    }
    for (const e of sc.enemies) if (e.beam) {
      const B = e.beam, L = 1600, x2 = e.x + Math.cos(B.a) * L, y2 = e.y + Math.sin(B.a) * L;
      ctx.globalCompositeOperation = 'lighter';
      if (B.t > 0) { ctx.strokeStyle = `rgba(190,232,255,${0.25 + 0.35 * Math.abs(Math.sin(t * 30))})`; ctx.lineWidth = 1.5 + (1.3 - B.t) * 3; ctx.setLineDash([14, 8]); }
      else { ctx.strokeStyle = 'rgba(190,232,255,0.9)'; ctx.lineWidth = 50 * (B.fire / 0.45); ctx.setLineDash([]); }
      ctx.beginPath(); ctx.moveTo(e.x, e.y); ctx.lineTo(x2, y2); ctx.stroke(); ctx.setLineDash([]);
      if (B.t <= 0) { ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 10 * (B.fire / 0.45); ctx.beginPath(); ctx.moveTo(e.x, e.y); ctx.lineTo(x2, y2); ctx.stroke(); }
      ctx.globalCompositeOperation = 'source-over';
    }
    for (const e of sc.enemies) {
      if (e.trail) drawSerpentBody(ctx, e, t);
      drawEnemyShip(ctx, e.k, e.x, e.y, e.a, 1.3, t, e);
      if (e.hitT > 0) glow(ctx, e.x, e.y, 30 * e.size, '#ffffff', 0.6);
      if (ENEMIES[e.k].ward && sc.enemies.some(o => !o.dead && o.k === ENEMIES[e.k].summon)) { ctx.strokeStyle = `rgba(255,224,128,${0.5 + 0.3 * Math.sin(t * 6) + (e.wardFlash > 0 ? 0.3 : 0)})`; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(e.x, e.y, 34 * e.size, 0, TAU); ctx.stroke(); }
      if (e.shieldFlash > 0) { ctx.strokeStyle = `rgba(255,120,160,${e.shieldFlash * 3})`; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(e.x, e.y, 30 * e.size, 0, TAU); ctx.stroke(); }
      const w = 50 * e.size, y = e.y - 32 * e.size - 8;
      ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(e.x - w / 2 - 1, y - 1, w + 2, e.spMax ? 9 : 6);
      ctx.fillStyle = '#ff4d6d'; ctx.fillRect(e.x - w / 2, y, w * clamp(e.hp / e.max, 0, 1), 4);
      if (e.spMax) { ctx.fillStyle = '#ff9ec0'; ctx.fillRect(e.x - w / 2, y + 5, w * clamp(e.sp / e.spMax, 0, 1), 3); }
    }
    for (const k of sc.inks || []) {
      const a = Math.min(1, k.t / 1.5);
      for (let i = 0; i < 5; i++) {
        const an = i * 1.26 + k.R, ox = Math.cos(an) * k.r * 0.35, oy = Math.sin(an) * k.r * 0.35;
        const g = ctx.createRadialGradient(k.x + ox, k.y + oy, 0, k.x + ox, k.y + oy, k.r * 0.75);
        g.addColorStop(0, `rgba(14,4,24,${0.8 * a})`); g.addColorStop(0.7, `rgba(30,8,50,${0.55 * a})`); g.addColorStop(1, 'rgba(30,8,50,0)');
        ctx.fillStyle = g; ctx.beginPath(); ctx.arc(k.x + ox, k.y + oy, k.r * 0.75, 0, TAU); ctx.fill();
      }
    }
  },
};
