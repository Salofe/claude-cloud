'use strict';
// ============ SCENE: MINING FIELD / SPACE ARENA ============
// The station sits at the bottom. Fly back down into the docking zone to sell.
// The higher up (farther from the station) you go, the richer the rocks.
const MW = 1800, MH = 3400, DOCK_Y = MH - 240;
const Z_HP = [1, 3.5, 6, 11, 16, 38];   // each new zone is tougher, but its ore is worth even more
const mineScale = () => 1.35 - (S.lv.hull - 1) * 0.08;
const shipR = () => shipLen(S.lv) * mineScale();
Object.assign(TXT, {
  mine_deep_space: { en: 'Deep Space', es: 'Espacio profundo' },
  mine_overdrive: { en: '⚡ OVERDRIVE!', es: '⚡ ¡SOBREMARCHA!' },
  mine_scan_some: { en: '◈ Deep Scan: {n} geodes nearby!', es: '◈ Escáner profundo: ¡{n} geodas cerca!' },
  mine_scan_one: { en: '◈ Deep Scan: 1 geode nearby!', es: '◈ Escáner profundo: ¡1 geoda cerca!' },
  mine_scan_none: { en: '◈ Deep Scan: no geodes nearby', es: '◈ Escáner profundo: no hay geodas cerca' },
  mine_tool_drill: { en: '⛏ Drill: 3× power, short range — cracks armored rocks', es: '⛏ Taladro: 3× potencia, corto alcance; rompe rocas blindadas' },
  mine_tool_laser: { en: '✦ Laser: long range', es: '✦ Láser: largo alcance' },
  mine_calmed_one: { en: '1 living rock calmed', es: '1 roca viva calmada' },
  mine_calmed_some: { en: '{n} living rocks calmed', es: '{n} rocas vivas calmadas' },
  mine_comet_toast: { en: '☄ A comet is crossing the field — break it before it escapes!', es: '☄ Un cometa cruza el campo: ¡rómpelo antes de que escape!' },
  mine_comet_fl: { en: 'COMET! {n} {item}', es: '¡COMETA! {n} {item}' },
  mine_jackpot: { en: 'JACKPOT!', es: '¡PREMIO GORDO!' },
  mine_geode_fl: { en: 'GEODE! {n} {item}', es: '¡GEODA! {n} {item}' },
  mine_relic_gold: { en: 'GOLDEN TOUCH: ×2 ore', es: 'TOQUE DORADO: ×2 mineral' },
  mine_relic_lens: { en: 'GRAVITY LENS: giant magnet', es: 'LENTE GRAVITATORIA: imán gigante' },
  mine_relic_beam: { en: 'ANCIENT BEAM: ×2 laser', es: 'RAYO ANTIGUO: ×2 láser' },
  mine_relic_recharge: { en: 'RECHARGE: all tools ready!', es: 'RECARGA: ¡herramientas listas!' },
  mine_horizon: { en: 'Too close to the event horizon! Fly down!', es: '¡Muy cerca del horizonte de eventos! ¡Baja!' },
  mine_alive_pulse: { en: 'IT\'S ALIVE! It flees — calm it with the Tractor Pulse ({k})', es: '¡ESTÁ VIVA! Huye: cálmala con el Pulso tractor ({k})' },
  mine_alive_chase: { en: 'IT\'S ALIVE! It flees — chase it!', es: '¡ESTÁ VIVA! Huye: ¡persíguela!' },
  mine_armored_drill: { en: 'ARMORED — switch to the Drill ({k})', es: 'BLINDADA: cambia al Taladro ({k})' },
  mine_armored_laser: { en: 'ARMORED — your laser barely scratches it', es: 'BLINDADA: tu láser apenas la raya' },
  mine_black_hole: { en: 'A rock fell into the black hole — mine them before they drift up!', es: 'Una roca cayó al agujero negro: ¡mínalas antes de que suban!' },
  mine_comet_escaped: { en: 'The comet escaped…', es: 'El cometa escapó…' },
  mine_pulsar_phase: { en: '⚡ Pulsar beam incoming — Phase ({k}) to ride it!', es: '⚡ ¡Viene el rayo del púlsar! Usa Fase ({k}) para atravesarlo' },
  mine_pulsar: { en: '⚡ Pulsar beam incoming!', es: '⚡ ¡Viene el rayo del púlsar!' },
  mine_betel_warn: { en: '☀ Betelgeuse is about to pulse — get ready to mine!', es: '☀ Betelgeuse está por pulsar: ¡prepárate para minar!' },
  mine_molten: { en: 'MOLTEN! 2× laser · +50% ore', es: '¡FUNDIDAS! 2× láser · +50% mineral' },
  mine_warped: { en: 'Warped out!', es: '¡Saltaste fuera!' },
  mine_warn_final: { en: '📡 Something huge is moving toward you…', es: '📡 Algo enorme se acerca a ti…' },
  mine_warn_warlord: { en: '☠ The warlord\'s flagship is coming!', es: '☠ ¡Viene la nave insignia del caudillo!' },
  mine_warn_pirates: { en: '⚠ Pirates incoming!', es: '⚠ ¡Se acercan piratas!' },
  mine_pirates_leave: { en: 'Pirates recognize your ship and leave you alone', es: 'Los piratas reconocen tu nave y te dejan en paz' },
  // coach hints
  mine_c_guns_touch_pir: { en: 'Hold <b>FIRE</b> to shoot the pirates!', es: '¡Mantén <b>DISPARAR</b> para dispararles a los piratas!' },
  mine_c_guns_touch_host: { en: 'Hold <b>FIRE</b> to shoot the hostiles!', es: '¡Mantén <b>DISPARAR</b> para dispararles a los enemigos!' },
  mine_c_guns_pir: { en: 'Pirates! <b>Hold the mouse</b> to shoot your guns', es: '¡Piratas! <b>Mantén presionado el mouse</b> para disparar tus cañones' },
  mine_c_guns_host: { en: 'Hostiles! <b>Hold the mouse</b> to shoot your guns', es: '¡Enemigos! <b>Mantén presionado el mouse</b> para disparar tus cañones' },
  mine_c_boss_final: { en: '☠ The {name} arrives in <b>{n} s</b> — get ready, or fly <b>down</b> to escape', es: '☠ {name} llega en <b>{n} s</b>: prepárate, o vuela hacia <b>abajo</b> para escapar' },
  mine_c_boss_warlord: { en: '☠ The warlord\'s flagship arrives in <b>{n} s</b> — get ready, or fly <b>down</b> to escape', es: '☠ La nave insignia del caudillo llega en <b>{n} s</b>: prepárate, o vuela hacia <b>abajo</b> para escapar' },
  mine_c_move_touch: { en: 'Drag anywhere on the left side to fly', es: 'Arrastra en cualquier parte del lado izquierdo para volar' },
  mine_c_move: { en: 'Fly with <b>WASD</b> or the <b>arrow keys</b>', es: 'Vuela con <b>WASD</b> o las <b>flechas</b>' },
  mine_c_laser_touch: { en: 'Hold <b>LASER</b> — it aims at the nearest rock', es: 'Mantén <b>LÁSER</b>: apunta a la roca más cercana' },
  mine_c_laser: { en: 'Hold the <b>mouse button</b> to fire your mining laser at a rock', es: 'Mantén presionado el <b>botón del mouse</b> para disparar tu láser minero a una roca' },
  mine_c_scoop: { en: 'Fly close to the glowing crystals to scoop them up', es: 'Acércate a los cristales brillantes para recogerlos' },
  mine_c_full: { en: '📦 Cargo full! Fly back <b>down</b> to the station ⬇', es: '📦 ¡Bodega llena! Vuelve <b>abajo</b> a la estación ⬇' },
  mine_c_deep: { en: 'Tip: rocks get <b>richer</b> the farther up you fly ⬆', es: 'Consejo: las rocas son más <b>ricas</b> cuanto más arriba vuelas ⬆' },
  // defeat / victory
  mine_shot_down: { en: 'Your ship was shot down.', es: 'Derribaron tu nave.' },
  mine_hull_collapsed: { en: 'Your hull collapsed.', es: 'Tu casco colapsó.' },
  mine_victory: { en: '☠ Pirates destroyed! Grab the loot.', es: '☠ ¡Piratas destruidos! Recoge el botín.' },
  mine_news_victory: { en: 'Pirate fleet destroyed', es: 'Flota pirata destruida' },
  mine_raiders_cleared: { en: 'raiders cleared', es: 'asaltantes eliminados' },
  mine_news_mined: { en: 'Mined at {name}: {list}', es: 'Minado en {name}: {list}' },
  // canvas labels
  mine_station_dist: { en: '▼ STATION {n} m ▼', es: '▼ ESTACIÓN {n} m ▼' },
  mine_dock: { en: '▼ DOCK ▼', es: '▼ MUELLE ▼' },
  mine_outpost_lv: { en: 'OUTPOST LV{n}', es: 'PUESTO NV{n}' },
  mine_boss_final: { en: '{name} · guardian of {sys}', es: '{name} · guardián de {sys}' },
  mine_boss_warlord: { en: 'PIRATE WARLORD · prize {n} cr', es: 'CAUDILLO PIRATA · premio {n} cr' },
  // towed
  mine_towed_title: { en: 'Towed to safety', es: 'Remolcado a salvo' },
  mine_towed_html: { en: '{reason}<br>A tug brings you to <b>{station}</b>. You lost part of your cargo{fee}.', es: '{reason}<br>Un remolcador te lleva a <b>{station}</b>. Perdiste parte de tu carga{fee}.' },
  mine_towed_fee: { en: ' and paid a <b>{n} cr</b> rescue fee', es: ' y pagaste <b>{n} cr</b> por el rescate' },
  mine_continue: { en: 'Continue', es: 'Continuar' },
});
// key hint for tool tips: the key on desktop, the touch button's label on phones
const mineKey = (key, en, es) => (isTouch ? L(en, es) : key);
const SPACE = { id: 'space', n: tx('mine_deep_space'), col: ['#6a7fb0', '#1b2340'], field: { n: tx('mine_deep_space'), z: 2, ores: { iron: 3, nickel: 1 }, count: 10 } };

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
  get gravity() { return !!sysDef().gravity && !this.space; },
  setup() {
    const f = this.loc.field;
    this.rocks = []; this.chunks = []; this.parts = new Particles(); this.floaters = []; this.enemies = []; this.bolts = [];
    this.hadCombat = false; this.clearT = 0; this.warp = null; this.armed = false;
    if (this.space) this.p = { x: MW / 2, y: MH / 2, vx: 0, vy: 0, a: -Math.PI / 2, shield: ship.shieldMax, shT: 0, fireCd: 0 };
    else this.p = { x: MW / 2, y: DOCK_Y + 60, vx: 0, vy: -260, a: -Math.PI / 2, shield: ship.shieldMax, shT: 0, fireCd: 0 };
    this.cam = { x: this.p.x, y: this.p.y - 120 };
    this.dayTimer = 0; this.collected = {}; this.cometT = rand(20, 40); this.tool = this.tool || 'laser'; this.pullT = 0; this.pullCd = this.pullCd || 0; this.boostT = 0; this.boostCd = this.boostCd || 0; this.bombCd = this.bombCd || 0; this.bombs = []; this.blasts = []; this.etrail = []; this.scanCd = this.scanCd || 0; this.scanT = -1; this.moltenT = 0; this.waveT = -1; this.inks = []; this.forks = null;
    this.pulseIn = sysDef().pulses ? rand(20, 30) : 0;
    this.phaseCd = this.phaseCd || 0; this.phaseT = 0; this.relic = null; this.sweep = null; this.sweepIn = rand(8, 12); this.swallowed = 0;
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
      if (this.loc.id === 'oort' && !S.gateOpen) this.ambush = { at: rand(16, 24), warned: false, boss: 'final' };
      else if (warlordAt(this.loc.id)) this.ambush = { at: rand(14, 26), warned: false, boss: 1 };   // the warlord hunts anyone mining his field
      else if (Math.random() < dg * 0.9) this.ambush = { at: rand(20, 45), warned: false };
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
    const crystal = !this.space && !!this.loc.field.crystal && Math.random() < this.loc.field.crystal;
    const armored = !crystal && !this.space && !!this.loc.field.armored && Math.random() < this.loc.field.armored;
    const volatile = !crystal && !armored && !this.space && !!this.loc.field.explosive && Math.random() < this.loc.field.explosive;
    const living = !crystal && !armored && !volatile && !this.space && !!this.loc.field.living && Math.random() < this.loc.field.living;
    const plain = !crystal && !armored && !volatile && !living && !this.space;
    const magnetic = plain && !!this.loc.field.magnetic && Math.random() < this.loc.field.magnetic;
    const relic = plain && !magnetic && !!this.loc.field.relics && Math.random() < this.loc.field.relics;
    // geodes (Rigel onward) hide a big load of the field's best ore — the Deep Scanner shows where they are
    const geode = !this.space && tier >= 2 && !!this.loc.field.geodes && Math.random() < this.loc.field.geodes ? this.bestOre() : null;
    const hp = R * 0.7 * ITEMS[ore].h * Z_HP[this.z] * sysDef().rock * (gold ? 2 : 1) * (crystal ? 0.75 : 1);
    const rock = {
      x, y, vx: rand(-14, 14), vy: rand(-14, 14), rot: rand(0, TAU), vr: rand(-0.4, 0.4), r: R, tier, ore, rich: isRich, gold, crystal, armored, volatile, living, geode, magnetic, relic,
      hp, maxhp: hp, hit: 0, cold: this.loc.field.cold,
      shape: makeRockShape(9 + tier * 2, 0.22),
      veins: Array.from({ length: nv }, () => { const a = rand(0, TAU), d = rand(0, 0.6); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.07, 0.16)]; }),
      craters: Array.from({ length: tier }, () => { const a = rand(0, TAU), d = rand(0, 0.5); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.1, 0.2)]; }),
    };
    if (living) { const a = rand(0, TAU); rock.vx = Math.cos(a) * 30; rock.vy = Math.sin(a) * 30; rock.wa = a; }
    this.rocks.push(rock);
    return rock;
  },
  // comets streak across the field: break one before it escapes for ice and a load of the field's best ore
  // Overdrive (Vega): 8 s of triple cutting power and a faster ship
  boost() {
    if (!hasTool('overdrive') || this.space || this.boostCd > 0) return;
    this.boostT = 8; this.boostCd = 45; sfx('upgrade'); toast(tx('mine_overdrive'), 'good');
  },
  // Mining charge (Altair): drop it, it blows 1.2 s later
  bomb() {
    if (!hasTool('charges') || this.space || this.bombCd > 0) return;
    this.bombCd = 10; this.bombs = this.bombs || []; this.bombs.push({ x: this.p.x, y: this.p.y, t: 1.2 }); sfx('click');
  },
  bestOre() { return Object.keys(this.loc.field.ores).sort((a, b) => ITEMS[b].b - ITEMS[a].b)[0]; },
  // Deep Scanner (Rigel): a wave that reveals every geode (and rich or golden rock) around you
  scan() {
    if (!hasTool('deepscan') || this.space || this.scanCd > 0) return;
    this.scanCd = built('sonar') ? 7 : 14; this.scanT = 0; this.scanO = { x: this.p.x, y: this.p.y };
    let n = 0;
    for (const r of this.rocks) { const d = Math.hypot(r.x - this.p.x, r.y - this.p.y); if (d < 1800) { r.seen = 14; r.seenD = d / 2000; if (r.geode) n++; } }
    tone(300, 0.6, 'sine', 0.08, 1500); tone(1500, 0.5, 'sine', 0.04, null, 0.55);
    toast(tx(n > 1 ? 'mine_scan_some' : n ? 'mine_scan_one' : 'mine_scan_none', { n }), n ? 'good' : '');
  },
  // Phase Shift (the Pulsar): 3 s as a ghost — no damage, and you fly through rocks
  phase() {
    if (!hasTool('phase') || this.space || this.phaseCd > 0) return;
    this.phaseT = 3; this.phaseCd = 20; tone(900, 0.4, 'sine', 0.06, 300); haptic(20);
    this.parts.burst(this.p.x, this.p.y, 30, '#9ff3ff', 200, 0.5, 2);
  },
  pullRadius() { return Math.max(1000, ship.magnet * 4); },
  toolRange() { return this.tool === 'drill' ? Math.max(110, ship.laserRange * 0.45) * (built('borer') ? 1.6 : 1) : ship.laserRange; },
  toggleTool() {
    if (!hasTool('drill') || this.space) return;
    this.tool = this.tool === 'drill' ? 'laser' : 'drill'; sfx('click');
    toast(tx(this.tool === 'drill' ? 'mine_tool_drill' : 'mine_tool_laser'), 'good');
  },
  // Tractor Pulse: pull every ore chunk in a wide radius
  pulse() {
    if (!hasTool('tractor') || this.space || this.pullCd > 0) return;
    this.pullT = 2.5; this.pullCd = 14; sfx('upgrade'); this.shake = Math.max(this.shake, 4);
    this.parts.burst(this.p.x, this.p.y, 40, '#9fe0ff', 420, 0.6, 2);
    // living rocks are soothed by the pulse: they stop and drift toward you for a few seconds
    let calmed = 0;
    for (const r of this.rocks) if (r.living && Math.hypot(r.x - this.p.x, r.y - this.p.y) < this.pullRadius()) { r.calm = 6; r.flee = 0; calmed++; }
    if (calmed) this.floaters.push({ x: this.p.x, y: this.p.y - 40, txt: tx(calmed > 1 ? 'mine_calmed_some' : 'mine_calmed_one', { n: calmed }), col: '#9fffe0', life: 1.6 });
  },
  spawnComet() {
    const ores = Object.keys(this.loc.field.ores), best = ores.sort((a, b) => ITEMS[b].b - ITEMS[a].b)[0];
    const dir = Math.random() < 0.5 ? 1 : -1, p = this.p;
    const c = this.spawnRock(dir > 0 ? -40 : MW + 40, clamp(p.y + rand(-450, 250), 300, DOCK_Y - 500), 2, 'ice');
    Object.assign(c, { comet: 1, core: best, vx: dir * rand(150, 200), vy: rand(-25, 25), vr: rand(1.5, 3) * dir, rich: false, gold: false, cold: 1 });
    c.hp = c.maxhp = c.r * 0.7 * ITEMS[best].h * Z_HP[this.z] * sysDef().rock * 1.3; c.crystal = false;
    toast(tx('mine_comet_toast'), 'good'); sfx('event');
  },
  breakComet(r) {
    this.parts.burst(r.x, r.y, 60, '#bff6ff', 260, 1.1, 3);
    this.parts.burst(r.x, r.y, 24, ITEMS[r.core].c, 160, 1, 3);
    sfx('win'); this.shake = Math.max(this.shake, 10);
    const n = Math.round(6 * ship.yieldMult * (built('herding') ? 2 : 1));
    for (let i = 0; i < n; i++) this.dropChunk(r.x, r.y, r.core);
    for (let i = 0; i < 5; i++) this.dropChunk(r.x, r.y, 'ice');
    this.floaters.push({ x: r.x, y: r.y - 30, txt: tx('mine_comet_fl', { n, item: ITEMS[r.core].n }), col: '#bff6ff', life: 2, big: 1 });
    S.stats.comets = (S.stats.comets || 0) + 1;
  },
  // volatile rocks (Epsilon Eridani) blow up: they crack every rock nearby — chain reactions! — and singe you if you're close
  explode(x, y, R, power, hurt) {
    this.parts.burst(x, y, 60, '#ffb347', 340, 0.9, 4); this.parts.burst(x, y, 30, '#ff5a2a', 220, 0.7, 3);
    sfx('boom'); this.shake = Math.max(this.shake, 14);
    this.blasts = this.blasts || []; this.blasts.push({ x, y, R, t: 0 });
    for (const o of [...this.rocks]) {
      const d = Math.hypot(o.x - x, o.y - y) - o.r; if (d > R || o.comet) continue;
      o.hp -= (o.tier >= 3 ? o.maxhp * power : o.maxhp * 1.2) + ship.laserDps * 2; o.hit = 0.1;   // small & medium rocks shatter, big ones crack
      if (o.hp <= 0 && this.rocks.includes(o)) setTimeout(() => { if (this.rocks.includes(o)) this.breakRock(o); }, 90 + Math.random() * 120);
    }
    for (const e of this.enemies) if (Math.hypot(e.x - x, e.y - y) < R) Combat.hitEnemy(this, e, ship.weaponDps * 6);
    if (hurt && Math.hypot(this.p.x - x, this.p.y - y) < R * 0.8) this.damage(ship.hpMax * 0.05);
  },
  breakRock(r) {
    this.rocks = this.rocks.filter(x => x !== r);
    if (r.comet) return this.breakComet(r);
    if (r.volatile) this.explode(r.x, r.y, 140 + r.tier * 50 * (built('chainlab') ? 1.6 : 1), 0.7, true);
    this.parts.burst(r.x, r.y, 14 + r.tier * 8, r.gold ? '#ffd24a' : '#c9b8a6', 120 + r.tier * 40, 0.8, 2.5);
    this.parts.burst(r.x, r.y, 6 + r.tier * 3, ITEMS[r.ore].c, 90, 1, 2.5);
    sfx('break'); this.shake = Math.max(this.shake, r.tier * 3);
    S.hints.laser = 1;
    if (r.gold) {
      const v = ITEMS[r.ore].b * incomeMult() * 30 * r.tier;
      for (let i = 0; i < 6; i++) { const a = rand(0, TAU), s = rand(40, 120); this.chunks.push({ x: r.x, y: r.y, vx: Math.cos(a) * s, vy: Math.sin(a) * s, cr: v / 6, gold: 1, rot: rand(0, TAU), life: 60 }); }
      this.floaters.push({ x: r.x, y: r.y - 30, txt: tx('mine_jackpot'), col: '#ffd24a', life: 2, big: 1 });
      S.stats.jackpots++; sfx('win');
    }
    if (r.geode) {
      const n = Math.round((5 + r.tier * 3) * ship.yieldMult * (built('sonar') ? 2 : 1));
      for (let i = 0; i < n; i++) this.dropChunk(r.x, r.y, r.geode);
      this.parts.burst(r.x, r.y, 50, ITEMS[r.geode].c, 260, 1.1, 3.5); this.parts.burst(r.x, r.y, 20, '#ffffff', 180, 0.6, 2.5);
      this.floaters.push({ x: r.x, y: r.y - 30, txt: tx('mine_geode_fl', { n, item: ITEMS[r.geode].n }), col: ITEMS[r.geode].c, life: 2.2, big: 1 });
      S.stats.geodes = (S.stats.geodes || 0) + 1; sfx('win'); this.shake = Math.max(this.shake, 8);
    }
    if (r.magnetic) {   // magnetic burst: every ore chunk nearby flies to you
      for (const c of this.chunks) if (Math.hypot(c.x - r.x, c.y - r.y) < 800) c.home = 2;
      this.blasts.push({ x: r.x, y: r.y, R: 260, t: 0, col: '#7fb8ff' }); this.homeAt = { x: r.x, y: r.y };
      tone(220, 0.4, 'sine', 0.06, 880);
    }
    if (r.relic) this.grantRelic(r);
    if (r.crystal && r.tier > 1) {
      // crystals shatter into a spray of fast shards you have to chase
      const n = r.tier === 3 ? 5 : 3;
      this.parts.burst(r.x, r.y, 30, '#e8dcff', 220, 0.7, 2);
      for (let i = 0; i < n; i++) {
        const c = this.spawnRock(r.x, r.y, 1, r.ore), a = i / n * TAU + rand(-0.3, 0.3), v = rand(170, 240);
        Object.assign(c, { crystal: true, shard: true, vx: Math.cos(a) * v, vy: Math.sin(a) * v, vr: rand(-4, 4), rich: r.rich, gold: false });
        c.hp = c.maxhp = c.maxhp * 0.75;
      }
    } else if (r.tier > 1) {
      for (let i = 0; i < 2; i++) {
        const c = this.spawnRock(r.x + rand(-10, 10), r.y + rand(-10, 10), r.tier - 1, r.ore);
        const a = rand(0, TAU); c.vx = r.vx + Math.cos(a) * 50; c.vy = r.vy + Math.sin(a) * 50; c.rich = r.rich; c.gold = false; c.hp = c.maxhp = c.maxhp;
        if (r.armored && !c.armored) { c.armored = true; c.crystal = false; }
        c.volatile = false; c.geode = null; c.relic = false; c.magnetic = r.magnetic; c.living = r.living; if (r.living) { c.flee = 2; c.wa = a; }
      }
      const m = 0.5 * ship.yieldMult * this.oreBonus(r);
      for (let i = 0; i < Math.floor(m) + (Math.random() < m % 1 ? 1 : 0); i++) this.dropChunk(r.x, r.y, r.ore);
    } else {
      // crystal shards reward the chase (+20%), armored rocks reward the drill (×1.5)
      const m = (rand(1, 2) + (r.rich ? 2 : 0)) * ship.yieldMult * (r.shard ? 1.2 : 1) * (r.shard && built('resonance') ? 2 : 1) * (r.armored ? 1.5 : 1) * (r.armored && built('plasmaforge') ? 2 : 1) * (r.volatile ? 1.2 : 1) * this.oreBonus(r);
      const n = Math.floor(m) + (Math.random() < m % 1 ? 1 : 0);
      for (let i = 0; i < n; i++) this.dropChunk(r.x, r.y, r.ore);
    }
  },
  // living rocks (Kepler) and molten rocks (Betelgeuse pulses) are worth more
  oreBonus(r) { return (r.living ? 1.6 * (built('whisperer') ? 2 : 1) : 1) * (this.moltenT > 0 ? 1.5 : 1) * (r.magnetic && built('polarity') ? 2 : 1) * (r.charged > 0 ? (built('beamharvest') ? 3 : 2) : 1) * (this.relic && this.relic.k === 'gold' ? 2 : 1); },
  // ancient relics (Core Rim): break one for a 25 s power
  grantRelic(r) {
    const k = pick(['gold', 'lens', 'beam', 'recharge']), L = tx('mine_relic_' + k);
    if (k === 'recharge') { this.pullCd = this.boostCd = this.bombCd = this.scanCd = this.phaseCd = 0; }
    else this.relic = { k, t: 25 * (built('archive') ? 2 : 1), n: L.split(':')[0] };
    this.floaters.push({ x: r.x, y: r.y - 40, txt: L, col: '#ffe080', life: 2.6, big: 1 });
    this.parts.burst(r.x, r.y, 50, '#ffe080', 260, 1, 3); sfx('win');
    S.stats.relics = (S.stats.relics || 0) + 1;
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
    this.floaters.push({ x: this.p.x, y: this.p.y - 22, txt: `+1 ${ITEMS[c.ore].n} · ${fmt(oreUnit(c.ore))}`, col: ITEMS[c.ore].c, life: 1.1 });
    sfx('pickup');
    return true;
  },
  // armored rocks shrug off the laser; the drill cuts them (and everything) 3× faster at close range; molten rocks melt twice as fast
  laserDmg(r, drill) { return (this.relic && this.relic.k === 'beam' ? 2 : 1) * ship.laserDps * (this.boostT > 0 ? 3 : 1) * (drill ? (built('borer') ? 4.5 : 3) : 1) * (r.armored && !drill ? (built('plasmaforge') ? 0.6 : 0.15) : 1) * (this.moltenT > 0 ? 2 : 1); },
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
    const inInk = (this.inks || []).some(k => Math.hypot(p.x - k.x, p.y - k.y) < k.r * 0.8);
    // Sagittarius A*: the black hole above every field pulls on you; its event horizon burns
    if (this.gravity) {
      const g = (built('hawking') ? 35 : 70) * (1 + clamp(1 - p.y / 900, 0, 1) * 2);
      p.vy -= g * dt;
      if (p.y < 300) { this.damage(ship.hpMax * 0.06 * dt, true); if (!this.horizonHint) { this.horizonHint = 1; toast(tx('mine_horizon'), 'bad'); } }
    }
    const maxV = 360 * ship.thrust * (this.boostT > 0 ? 1.5 : 1) * (inInk ? 0.55 : 1);
    const v = Math.hypot(p.vx, p.vy);
    if (v > maxV) { p.vx *= maxV / v; p.vy *= maxV / v; }
    p.x = clamp(p.x + p.vx * dt, 40, MW - 40); p.y = clamp(p.y + p.vy * dt, 40, MH - 40);
    this.thrusting = Math.hypot(ax, ay);
    if (!S.hints.move) { this.moved = (this.moved || 0) + v * dt; if (this.moved > 160) S.hints.move = 1; }
    // --- aim & fire ---
    let aim = null, firing = false;
    const vz = viewZoom(), wm = { x: (mouse.x - W / 2) / vz + this.cam.x, y: (mouse.y - H / 2) / vz + this.cam.y };
    const combat = this.inCombat;
    if (touchFire) {
      // auto-aim: the nearest target (rock edge, or enemy hull); keep the current one only while it is still about as close,
      // so the beam doesn't flick between two rocks but never ignores one right next to you
      const list = combat ? this.enemies : this.rocks, edge = r => Math.hypot(r.x - p.x, r.y - p.y) - (r.r || (r.size ? 18 * r.size : 0));
      let best = null, bd = 1e9;
      for (const r of list) { if (r.dead) continue; const d = edge(r); if (d < bd) { bd = d; best = r; } }
      const lk = this.lock && list.includes(this.lock) && !this.lock.dead ? this.lock : null;
      if (lk && best !== lk) { const ld = edge(lk); if (ld <= bd + 40 && ld < (combat ? 900 : this.toolRange())) { best = lk; bd = ld; } }
      this.lock = best;
      const reach = combat ? 1e9 : this.toolRange() + 40;
      if (best && bd < reach * 2.5) { aim = Math.atan2(best.y - p.y, best.x - p.x); firing = bd < reach; }
    } else { this.lock = null; if (mouse.down && !mouse.onUI) { aim = Math.atan2(wm.y - p.y, wm.x - p.x); firing = true; } }
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
      let best = null, bt = this.toolRange();
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
      this.forks = null;
      if (best) {
        const drill = this.tool === 'drill';
        best.hp -= this.laserDmg(best, drill) * dt; best.hit = 0.05;
        if (best.living && !best.calm && !built('whisperer')) {
          if (!(best.flee > 0)) { this.parts.burst(best.x, best.y, 10, '#9fffe0', 90, 0.5, 2); if (!this.livingHint) { this.livingHint = 1; this.floaters.push({ x: best.x, y: best.y - best.r - 14, txt: hasTool('tractor') ? tx('mine_alive_pulse', { k: mineKey('E', 'PULL', 'ATRAER') }) : tx('mine_alive_chase'), col: '#9fffe0', life: 2.8, big: 1 }); } }
          best.flee = 2;
        }
        // Wide Beam (Betelgeuse): the laser forks into two more rocks near the target, at half power
        if (hasTool('widebeam') && !drill) {
          const near = this.rocks.filter(r => r !== best && !r.comet && Math.hypot(r.x - best.x, r.y - best.y) < 260 + best.r).sort((a, b) => Math.hypot(a.x - best.x, a.y - best.y) - Math.hypot(b.x - best.x, b.y - best.y)).slice(0, 2);
          this.forks = near.map(r => ({ x: r.x, y: r.y, r }));
          for (const r of near) { r.hp -= this.laserDmg(r, false) * 0.5 * dt; r.hit = 0.05; if (r.living && !r.calm && !built('whisperer')) r.flee = 2; }
          for (const r of near) if (r.hp <= 0 && this.rocks.includes(r)) this.breakRock(r);
        }
        if (best.armored && !drill && !this.armorHint) { this.armorHint = 1; this.floaters.push({ x: best.x, y: best.y - best.r - 14, txt: hasTool('drill') ? tx('mine_armored_drill', { k: mineKey('Q', 'DRILL', 'TALADRO') }) : tx('mine_armored_laser'), col: '#c8d0e0', life: 2.5, big: 1 }); }
        if (Math.random() < dt * 30) this.parts.add(hx, hy, -dx * 80 + rand(-60, 60), -dy * 80 + rand(-60, 60), 0.4, Math.random() < 0.5 ? ITEMS[best.ore].c : laserColor(laserTier()), 2, true);
        if (best.hp <= 0 && this.rocks.includes(best)) this.breakRock(best);
      }
    }
    const lOn = firing && !combat;
    if (lOn !== this.laserOn) { this.laserOn = lOn; laserSound(lOn, laserTier()); }
    // --- rocks ---
    for (const r of this.rocks) {
      r.x += r.vx * dt; r.y += r.vy * dt; r.rot += r.vr * dt; r.hit = Math.max(0, r.hit - dt);
      const maxY = this.space ? MH - r.r : DOCK_Y - 120;
      if (r.comet) {
        if (Math.random() < dt * 40) this.parts.add(r.x - r.vx * 0.08 + rand(-6, 6), r.y - r.vy * 0.08 + rand(-6, 6), -r.vx * 0.3 + rand(-20, 20), -r.vy * 0.3 + rand(-20, 20), 0.9, Math.random() < 0.6 ? '#bff6ff' : '#ffffff', 2.5, true);
        if (r.x < -80 || r.x > MW + 80) r.gone = 1;
        r.y = clamp(r.y, r.r, maxY);
      } else {
        if (r.living) {
          r.calm = Math.max(0, (r.calm || 0) - dt); r.flee = Math.max(0, (r.flee || 0) - dt);
          if (r.calm > 0) { const k = Math.pow(0.15, dt); r.vx *= k; r.vy *= k; }
          else if (r.flee > 0) { const ex = r.x - p.x, ey = r.y - p.y, ed = Math.hypot(ex, ey) || 1, sp = [0, 165, 125, 90][r.tier]; r.vx = lerp(r.vx, ex / ed * sp, dt * 2.5); r.vy = lerp(r.vy, ey / ed * sp, dt * 2.5); if (Math.random() < dt * 12) this.parts.add(r.x - r.vx * 0.2, r.y - r.vy * 0.2, rand(-15, 15), rand(-15, 15), 0.6, '#9fffe0', 2); }
          else { r.wa = (r.wa || 0) + rand(-1.2, 1.2) * dt; r.vx = lerp(r.vx, Math.cos(r.wa) * 28, dt * 0.8); r.vy = lerp(r.vy, Math.sin(r.wa) * 28, dt * 0.8); }
          r.swim = (r.swim || 0) + dt * (3 + Math.hypot(r.vx, r.vy) / 25);
        }
        if (r.seen > 0) { r.seen -= dt; if (r.seenD > 0) r.seenD -= dt; }
        if (r.charged > 0) r.charged -= dt;
        if (r.magnetic) {   // magnetic rocks drift toward each other and clump into clusters
          let mb = null, bd = 650;
          for (const o of this.rocks) if (o !== r && o.magnetic && !o.comet) { const d2 = Math.hypot(o.x - r.x, o.y - r.y); if (d2 < bd) { bd = d2; mb = o; } }
          r.near = mb;
          if (mb) {
            const ux = (mb.x - r.x) / (bd || 1), uy = (mb.y - r.y) / (bd || 1), gap = bd - r.r - mb.r;
            if (gap > 4) { const f = (built('polarity') ? 40 : 20) / r.tier; r.vx += ux * f * dt; r.vy += uy * f * dt; }
            else { r.x += ux * gap * 0.5; r.y += uy * gap * 0.5; const k = Math.pow(0.2, dt); r.vx *= k; r.vy *= k; }
            const sp = Math.hypot(r.vx, r.vy); if (sp > 70) { r.vx *= 70 / sp; r.vy *= 70 / sp; }
          }
        }
        if (this.gravity) { r.vy -= 7 * dt; if (r.vy < -32) r.vy = -32; if (r.y < r.r + 60) { r.gone = 1; r.swallowed = 1; } }
        if (r.shard) { const sp = Math.hypot(r.vx, r.vy); if (sp > 35) { const k = Math.pow(0.55, dt); r.vx *= k; r.vy *= k; } }
        if (r.x < r.r || r.x > MW - r.r) r.vx *= -1;
        if (r.y < r.r || r.y > maxY) r.vy *= -1;
        r.x = clamp(r.x, r.r, MW - r.r); r.y = clamp(r.y, r.r, maxY);
      }
      const dx = p.x - r.x, dy = p.y - r.y, d = Math.hypot(dx, dy), md = r.r + shipR() * 0.4;
      if (d < md && d > 0 && !(this.phaseT > 0)) {
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
    if (this.rocks.some(r => r.gone)) {
      for (const r of this.rocks) if (r.swallowed) {
        this.parts.burst(r.x, r.y, 20, '#ffb060', 120, 0.8, 2.5); this.swallowed++;
        if (built('hawking')) { const v = ITEMS[r.ore].b * r.tier * 2 * incomeMult(); earn(v); this.floaters.push({ x: r.x, y: r.y + 40, txt: `+${fmt(v)} cr (Hawking)`, col: '#ffd24a', life: 1.4 }); }
        else if (this.swallowed === 1) toast(tx('mine_black_hole'));
      }
      if (this.rocks.some(r => r.gone && !r.swallowed)) toast(tx('mine_comet_escaped'));
      this.rocks = this.rocks.filter(r => !r.gone);
    }
    if (!this.space && has(U.OUTPOST)) { this.cometT -= dt; if (this.cometT <= 0) { this.cometT = rand(45, 80) / ((sysDef().comets || 1) * (built('herding') ? 3 : 1)); if (!this.rocks.some(r => r.comet) && !this.inCombat) this.spawnComet(); } }
    // --- chunks & loot ---
    const cfree = cargoFree();
    this.pullT = Math.max(0, this.pullT - dt); this.pullCd = Math.max(0, this.pullCd - dt);
    this.boostT = Math.max(0, this.boostT - dt); this.boostCd = Math.max(0, this.boostCd - dt); this.bombCd = Math.max(0, this.bombCd - dt);
    for (const b of this.bombs) { b.t -= dt; if (b.t <= 0) { b.done = 1; this.explode(b.x, b.y, 230, 0.6, false); } }
    this.bombs = this.bombs.filter(b => !b.done);
    this.phaseCd = Math.max(0, this.phaseCd - dt); this.phaseT = Math.max(0, this.phaseT - dt);
    if (this.relic) { this.relic.t -= dt; if (this.relic.t <= 0) this.relic = null; }
    // the Pulsar's beam sweeps across the field: it charges rocks (×2 ore) and burns your hull
    if (sysDef().sweeps && !this.space) {
      this.sweepIn -= dt;
      if (this.sweepIn < 2 && !this.sweepWarned) { this.sweepWarned = 1; toast(hasTool('phase') ? tx('mine_pulsar_phase', { k: mineKey('X', 'PHASE', 'FASE') }) : tx('mine_pulsar'), 'bad'); tone(1200, 0.15, 'square', 0.04); tone(1200, 0.15, 'square', 0.04, null, 0.3); }
      if (this.sweepIn <= 0 && !this.sweep) { const dir = Math.random() < 0.5 ? 1 : -1; this.sweep = { t: 0, dur: 3, a0: Math.PI / 2 - 0.26 * dir, a1: Math.PI / 2 + 0.26 * dir, a: 0 }; sfx('warp'); }
      if (this.sweep) {
        const B = this.sweep; B.t += dt; B.a = lerp(B.a0, B.a1, B.t / B.dur);
        const ox = MW / 2, oy = -2400, ux = Math.cos(B.a), uy = Math.sin(B.a), lineD = (x, y) => Math.abs((x - ox) * uy - (y - oy) * ux);
        for (const r of this.rocks) if (lineD(r.x, r.y) < 70 + r.r) { if (!(r.charged > 0)) this.parts.burst(r.x, r.y, 6, '#bfe8ff', 80, 0.4, 2); r.charged = 15; }
        if (lineD(p.x, p.y) < 70 && !built('beamharvest')) { this.damage(ship.hpMax * 0.1 * dt, true); if (Math.random() < dt * 10) sfx('hit'); }
        if (B.t >= B.dur) { this.sweep = null; this.sweepIn = rand(12, 16); this.sweepWarned = 0; }
      }
    }
    this.scanCd = Math.max(0, this.scanCd - dt); if (this.scanT >= 0) { this.scanT += dt; if (this.scanT > 1) this.scanT = -1; }
    // Betelgeuse pulses: a heat wave washes over the field and every rock turns molten for a while
    if (sysDef().pulses && !this.space) {
      this.moltenT = Math.max(0, this.moltenT - dt); if (this.waveT >= 0) { this.waveT += dt; if (this.waveT > 1.4) this.waveT = -1; }
      this.pulseIn -= dt;
      if (this.pulseIn < 3 && !this.pulseWarned) { this.pulseWarned = 1; toast(tx('mine_betel_warn'), 'good'); tone(55, 2.8, 'sine', 0.3, 38); }
      if (this.pulseIn <= 0) {
        const hs = built('starheart');
        this.pulseIn = rand(50, 70) / (hs ? 2 : 1); this.pulseWarned = 0;
        this.moltenT = 10 * (hs ? 1.5 : 1); this.waveT = 0; this.shake = Math.max(this.shake, 8);
        sfx('boom'); this.floaters.push({ x: p.x, y: p.y - 70, txt: tx('mine_molten'), col: '#ffb040', life: 2.4, big: 1 });
      }
    }
    for (const b of this.blasts) b.t += dt; this.blasts = this.blasts.filter(b => b.t < 0.5);
    if (this.boostT > 0 && Math.random() < dt * 40) this.parts.add(this.p.x + rand(-14, 14), this.p.y + rand(-14, 14), -this.p.vx * 0.3, -this.p.vy * 0.3, 0.4, '#ffe14a', 2.5, true);
    for (const c of this.chunks) {
      c.x += c.vx * dt; c.y += c.vy * dt; c.vx *= Math.pow(0.5, dt); c.vy *= Math.pow(0.5, dt); c.life -= dt;
      const dx = p.x - c.x, dy = p.y - c.y, d = Math.hypot(dx, dy);
      const mag = (this.pullT > 0 ? this.pullRadius() : c.cr ? ship.magnet * 1.5 : ship.magnet) * (this.relic && this.relic.k === 'lens' ? 3 : 1);
      if (c.home > 0) { c.home -= dt; if (cfree > 0 || c.cr) { c.vx += dx / (d || 1) * 900 * dt; c.vy += dy / (d || 1) * 900 * dt; } }
      if (this.gravity) { c.vy -= 25 * dt; if (c.y < 30) c.dead = true; }
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
      if (this.warp.t >= ship.warpTime) { sfx('warp'); toast(tx('mine_warped'), 'good'); this.finishSpace(false); return; }
    }
    // --- shields & hazards ---
    p.shT -= dt;
    if (p.shT <= 0) p.shield = Math.min(ship.shieldMax, p.shield + (4 + ship.shieldMax * 0.08) * dt);
    if (this.loc.field.hazard === 'heat') this.damage(1.2 * dt * (1 + this.z), true);
    // --- ambush ---
    if (this.ambush) {
      this.ambush.at -= dt;
      if (!this.ambush.warned && this.ambush.at < 3) { this.ambush.warned = true; toast(tx(this.ambush.boss === 'final' ? 'mine_warn_final' : this.ambush.boss ? 'mine_warn_warlord' : 'mine_warn_pirates'), 'bad'); sfx('alarm'); }
      if (this.ambush.at <= 0) {
        const boss = this.ambush.boss === 'final' || (this.ambush.boss && warlordAt(this.loc.id));
        const fleet = this.ambush.boss === 'final' ? sysDef().bossFleet : boss ? ['warlord', ...buildFleet(0.25)] : buildFleet(locDanger(this.loc.id));
        this.ambush = null;
        if (boss) Combat.spawn(this, fleet, this.z, true);
        else if (S.rep.piratas >= 35) toast(tx('mine_pirates_leave'), 'good');
        else Combat.spawn(this, fleet, this.z, true);
      }
    }
    // --- docking zone ---
    if (!this.space) {
      if (p.y < DOCK_Y - 250) this.armed = true;
      if (this.armed && p.y > DOCK_Y) { this.leave(); return; }
    }

    if (this.gravity && !this.space && this.rocks.length < this.target * 0.8 && Math.random() < dt * 1.2) this.spawnRock(rand(120, MW - 120), rand(DOCK_Y * 0.55, DOCK_Y - 420), pick([3, 3, 2]));
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
    this.etrail = this.etrail || [];
    for (const e of this.etrail) e.life -= dt;
    while (this.etrail.length && this.etrail[0].life <= 0) this.etrail.shift();
    {
      const tx = p.x - Math.cos(p.a) * shipR() * 0.8, ty = p.y - Math.sin(p.a) * shipR() * 0.8, last = this.etrail[this.etrail.length - 1];
      if (this.thrusting > 0.1) { if (!last || Math.hypot(last.x - tx, last.y - ty) > 4) this.etrail.push({ x: tx, y: ty, life: 0.6, th: Math.min(1, this.thrusting) }); }
      else if (last && !last.gap) this.etrail.push({ x: tx, y: ty, life: 0.6, gap: 1 });
    }
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
    if (this.inCombat && !h.guns) { const host = this.enemies.some(e => ENEMIES[e.k].alien || ENEMIES[e.k].hive || ENEMIES[e.k].whale); msg = tx('mine_c_guns' + (isTouch ? '_touch' : '') + (host ? '_host' : '_pir')); }
    else if (this.ambush && this.ambush.boss && this.ambush.at > 0) msg = this.ambush.boss === 'final' ? tx('mine_c_boss_final', { name: ENEMIES[sysDef().boss].n, n: Math.ceil(this.ambush.at) }) : tx('mine_c_boss_warlord', { n: Math.ceil(this.ambush.at) });
    else if (!h.move) msg = tx(isTouch ? 'mine_c_move_touch' : 'mine_c_move');
    else if (!h.laser) msg = tx(isTouch ? 'mine_c_laser_touch' : 'mine_c_laser');
    else if (S.stats.mined < 4) msg = tx('mine_c_scoop');
    else if (!this.space && cargoFree() <= 0) msg = tx('mine_c_full');
    else if (!this.space && !h.deep && S.stats.docks >= 2 && this.p.y > DOCK_Y - 900) { msg = tx('mine_c_deep'); }
    if (this.p.y < DOCK_Y - 1400) h.deep = 1;
    coach(msg);
  },
  damage(n, heat) {
    const p = this.p;
    if (this.phaseT > 0) return;
    if (p.shield > 0) { const a = Math.min(p.shield, n); p.shield -= a; n -= a; if (!heat) p.shT = 2.5; }
    if (n > 0) {
      S.hull -= n;
      if (S.hull <= 0) {
        S.hull = 0; laserSound(false); this.laserOn = false;
        S.stats.lost++;
        if (this.space && MapScene.travel) { MapScene.travel = null; $('travelBanner').classList.add('hidden'); }
        setScene(MapScene);
        towShip(tx(this.inCombat ? 'mine_shot_down' : 'mine_hull_collapsed'));
      }
    }
  },
  onVictory() {
    sfx('win');
    const n = S.stats.kills;
    toast(tx('mine_victory'), 'good');
    const tr = MapScene.travel, here = [S.loc, tr && tr.from, tr && tr.to];
    for (const c of [...S.active]) if (c.type === 'bounty' && (!c.at || here.includes(c.at))) { c.progress++; if (c.progress >= c.kills) completeContract(c); }
    repChange('piratas', -3, true);
    const near = LOC[S.loc].faction && LOC[S.loc].faction !== 'piratas' ? LOC[S.loc].faction : 'cinturon';
    repChange(near, 2, true);
    S.stats.won++;
    addNews('🏆', tx('mine_news_victory'), '#6dffb0');
    // clearing raiders in the war zone helps the side you back
    const w = backedWar();
    if (w && here.some(id => id && w.locs.includes(id))) warPush(w, 6, tx('mine_raiders_cleared'));
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
    const vz = viewZoom(), VW = W / vz, VH = H / vz;
    const cx = this.cam.x - VW / 2 + sx, cy = this.cam.y - VH / 2 + sy;
    drawSpaceBg(ctx, W, H, cx, cy, t, this.loc.field.cold ? '#0c1838' : this.loc.field.hazard === 'heat' ? '#2a1408' : this.space ? '#1c0b1e' : null);
    const bgLoc = this.space ? LOC[S.loc] : this.loc.id === 'kuiper' ? LOC.pluton : this.loc.parent ? LOC[this.loc.parent] : this.loc.follow ? LOC[this.loc.follow] : this.loc;
    if (bgLoc && bgLoc.nuked) glow(ctx, W * 0.8 - cx * 0.03, H * 0.25 - (cy - MH) * 0.03, Math.min(W, H) * 0.5, '#ff5a2a55', 0.9);
    else if (bgLoc && bgLoc.col) {
      const bx = W * 0.8 - cx * 0.03, by = H * 0.25 - (cy - MH) * 0.03;
      drawPlanet(ctx, bx, by, Math.min(W, H) * (bgLoc.size > 12 ? 0.28 : 0.16), bgLoc, Math.atan2(-by, -bx - W), t);
    }
    if (this.loc.field.hazard === 'heat') drawSun(ctx, -cx * 0.02 - 40, H * 0.5 - (cy - MH) * 0.02, 120, t, sysDef().star);
    if (sysDef().gravity) drawBlackHole(ctx, W * 0.3 - cx * 0.015, H * 0.16 - (cy - MH) * 0.012, Math.min(W, H) * 0.07, t);
    if (sysDef().sweeps) {   // the pulsar itself, far away, its beams spinning
      const px = W * 0.22 - cx * 0.015, py = H * 0.14 - (cy - MH) * 0.012, a = t * 2.2;
      glow(ctx, px, py, 60, '#bfe8ff', 0.6);
      ctx.globalCompositeOperation = 'lighter';
      for (const k of [0, Math.PI]) { const g = ctx.createLinearGradient(px, py, px + Math.cos(a + k) * 420, py + Math.sin(a + k) * 420 * 0.4); g.addColorStop(0, 'rgba(200,235,255,0.5)'); g.addColorStop(1, 'rgba(200,235,255,0)'); ctx.strokeStyle = g; ctx.lineWidth = 10; ctx.beginPath(); ctx.moveTo(px, py); ctx.lineTo(px + Math.cos(a + k) * 420, py + Math.sin(a + k) * 420 * 0.4); ctx.stroke(); }
      ctx.globalCompositeOperation = 'source-over'; ctx.fillStyle = '#fff'; ctx.beginPath(); ctx.arc(px, py, 4, 0, TAU); ctx.fill();
    }
    starWash(ctx, W, H, sysDef().star, t);
    ctx.save();
    ctx.scale(vz, vz); ctx.translate(-cx, -cy);
    ctx.strokeStyle = 'rgba(61,232,255,0.12)'; ctx.setLineDash([10, 12]); ctx.lineWidth = 2;
    ctx.strokeRect(20, 20, MW - 40, MH - 40); ctx.setLineDash([]);
    if (!this.space) this.drawStation(ctx, t);
    const p = this.p;
    for (const b of this.bombs) { const k = 1 - b.t / 1.2; glow(ctx, b.x, b.y, 18 + k * 20, '#ff5a2a', 0.5 + k * 0.5); ctx.fillStyle = Math.sin(b.t * 30) > 0 ? '#ffffff' : '#ff3a2a'; ctx.beginPath(); ctx.arc(b.x, b.y, 6, 0, TAU); ctx.fill(); }
    for (const b of this.blasts) {
      const k = b.t / 0.5;
      if (b.col) { ctx.strokeStyle = b.col; ctx.globalAlpha = 1 - k; ctx.lineWidth = 4; ctx.beginPath(); ctx.arc(b.x, b.y, b.R * (0.2 + k), 0, TAU); ctx.stroke(); ctx.globalAlpha = 1; continue; }
      if (k < 0.5) glow(ctx, b.x, b.y, b.R * (0.5 + k), '#fff0c0', (1 - k * 2) * 0.9);
      glow(ctx, b.x, b.y, b.R * 0.8, '#ff6a2a', (1 - k) * 0.5);
      ctx.strokeStyle = `rgba(255,180,80,${1 - k})`; ctx.lineWidth = 6 * (1 - k) + 1; ctx.beginPath(); ctx.arc(b.x, b.y, b.R * (0.3 + k * 0.7), 0, TAU); ctx.stroke();
      ctx.strokeStyle = `rgba(255,255,255,${(1 - k) * 0.5})`; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(b.x, b.y, b.R * (0.15 + k * 0.9), 0, TAU); ctx.stroke();
    }
    if (this.boostT > 0) glow(ctx, p.x, p.y, 70, '#ffe14a', 0.25 + 0.1 * Math.sin(t * 20));
    if (this.pullT > 0) { ctx.strokeStyle = `rgba(159,224,255,${this.pullT / 2.5 * 0.5})`; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(p.x, p.y, this.pullRadius() * (1 - this.pullT / 2.5 * 0.3), 0, TAU); ctx.stroke(); }
    if (this.gravity) drawEventHorizon(ctx, MW / 2, -1400, 1300, t);
    if (this.sweep) {
      const B = this.sweep, ox = MW / 2, oy = -2400, L = 7000, x2 = ox + Math.cos(B.a) * L, y2 = oy + Math.sin(B.a) * L, f = Math.sin(Math.PI * B.t / B.dur);
      ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round';
      ctx.strokeStyle = `rgba(150,210,255,${0.22 * f})`; ctx.lineWidth = 220; ctx.beginPath(); ctx.moveTo(ox, oy); ctx.lineTo(x2, y2); ctx.stroke();
      ctx.strokeStyle = `rgba(200,235,255,${0.45 * f})`; ctx.lineWidth = 120; ctx.stroke();
      ctx.strokeStyle = `rgba(255,255,255,${0.8 * f})`; ctx.lineWidth = 26; ctx.stroke();
      ctx.globalCompositeOperation = 'source-over'; ctx.lineCap = 'butt';
    }
    // magnetic field lines between clumping rocks
    ctx.lineWidth = 1.2;
    for (const r of this.rocks) if (r.magnetic && r.near && (r.near.near !== r || r.x < r.near.x) && Math.hypot(r.x - r.near.x, r.y - r.near.y) < r.r + r.near.r + 260) {
      const o = r.near, mx = (r.x + o.x) / 2, my = (r.y + o.y) / 2, nx = -(o.y - r.y) * 0.25, ny = (o.x - r.x) * 0.25;
      for (const k of [-1, 1]) { ctx.strokeStyle = `rgba(127,184,255,${0.25 + 0.15 * Math.sin(t * 4 + k)})`; ctx.beginPath(); ctx.moveTo(r.x, r.y); ctx.quadraticCurveTo(mx + nx * k, my + ny * k, o.x, o.y); ctx.stroke(); }
    }
    if (this.scanT >= 0) { const k = this.scanT, R = k * 2000; ctx.strokeStyle = `rgba(127,224,255,${(1 - k) * 0.8})`; ctx.lineWidth = 3 + (1 - k) * 6; ctx.beginPath(); ctx.arc(this.scanO.x, this.scanO.y, R, 0, TAU); ctx.stroke(); ctx.lineWidth = 1; ctx.beginPath(); ctx.arc(this.scanO.x, this.scanO.y, R * 0.92, 0, TAU); ctx.stroke(); }
    if (cargoFree() > 0) { ctx.strokeStyle = 'rgba(61,232,255,0.07)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.arc(p.x, p.y, ship.magnet, 0, TAU); ctx.stroke(); }
    for (const r of this.rocks) if (r.x > cx - 160 && r.x < cx + VW + 160 && r.y > cy - 100 && r.y < cy + VH + 100) {
      if (r.comet) {
        const sp = Math.hypot(r.vx, r.vy) || 1, ux = r.vx / sp, uy = r.vy / sp, L = r.r * 5;
        const g = ctx.createLinearGradient(r.x, r.y, r.x - ux * L, r.y - uy * L); g.addColorStop(0, 'rgba(191,246,255,0.55)'); g.addColorStop(1, 'rgba(191,246,255,0)');
        ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(r.x - uy * r.r, r.y + ux * r.r); ctx.lineTo(r.x - ux * L, r.y - uy * L); ctx.lineTo(r.x + uy * r.r, r.y - ux * r.r); ctx.closePath(); ctx.fill();
        glow(ctx, r.x, r.y, r.r * 2.6, '#bff6ff', 0.55 + 0.15 * Math.sin(t * 8));
      }
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
      const L = this.laserHit, col = this.tool === 'drill' ? '#ffa030' : laserColor(laserTier());
      const nx = p.x + Math.cos(L.dir) * shipR() * 0.9, ny = p.y + Math.sin(L.dir) * shipR() * 0.9;
      ctx.globalCompositeOperation = 'lighter';
      ctx.strokeStyle = col; ctx.globalAlpha = 0.35; ctx.lineWidth = (this.tool === 'drill' ? 16 : 7 + laserTier()) + Math.sin(t * 50) * 2;
      if (this.tool === 'drill' && L.rock && Math.random() < 0.6) this.parts.add(L.x, L.y, rand(-120, 120), rand(-120, 120), 0.3, Math.random() < 0.5 ? '#ffd080' : '#ffffff', 2, true);
      ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(L.x, L.y); ctx.stroke();
      ctx.globalAlpha = 1; ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 1.8;
      ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(L.x, L.y); ctx.stroke();
      ctx.globalCompositeOperation = 'source-over';
      glow(ctx, L.x, L.y, L.rock ? 26 : 10, col, 0.9);
      if (this.forks) {
        ctx.globalCompositeOperation = 'lighter'; ctx.strokeStyle = col;
        for (const f of this.forks) {
          ctx.globalAlpha = 0.7; ctx.lineWidth = 2.5; ctx.beginPath(); ctx.moveTo(L.x, L.y);
          for (let i = 1; i < 6; i++) { const k = i / 6; ctx.lineTo(lerp(L.x, f.x, k) + rand(-8, 8), lerp(L.y, f.y, k) + rand(-8, 8)); }
          ctx.lineTo(f.x, f.y); ctx.stroke(); glow(ctx, f.x, f.y, 18, col, 0.7);
        }
        ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
      }
    }
    for (const dr of this.drones) {
      glow(ctx, dr.x, dr.y, 10, '#3de8ff88', 0.8);
      ctx.fillStyle = '#d4dcea'; ctx.beginPath(); ctx.arc(dr.x, dr.y, 4, 0, TAU); ctx.fill();
      ctx.fillStyle = '#3de8ff'; ctx.beginPath(); ctx.arc(dr.x, dr.y, 1.8, 0, TAU); ctx.fill();
      if (dr.carry && dr.carry.ore) { ctx.fillStyle = ITEMS[dr.carry.ore].c; ctx.fillRect(dr.x - 2, dr.y + 4, 4, 4); }
    }
    Combat.draw(this, ctx, t);
    this.parts.draw(ctx);
    // engine ribbon: a fading ion trail that follows your path
    if (this.etrail && this.etrail.length > 1) {
      const ec = ENGINE_COL[Math.min(4, Math.floor((S.lv.engine - 1) / 4))];
      ctx.globalCompositeOperation = 'lighter'; ctx.lineCap = 'round'; ctx.strokeStyle = ec;
      for (let i = 1; i < this.etrail.length; i++) {
        const a = this.etrail[i - 1], b = this.etrail[i]; if (a.gap || b.gap) continue;
        const k = b.life / 0.6; ctx.globalAlpha = k * 0.35 * b.th; ctx.lineWidth = 1 + k * 5 * mineScale();
        ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
      }
      ctx.globalAlpha = 1; ctx.lineCap = 'butt'; ctx.globalCompositeOperation = 'source-over';
    }
    const lv = shipLv();
    if (this.phaseT > 0) { ctx.globalAlpha = 0.4 + 0.15 * Math.sin(t * 20); glow(ctx, p.x, p.y, shipR() * 2.2, '#9ff3ff', 0.6); }
    drawPlayerShip(ctx, lv, p.x, p.y, p.a, mineScale(), this.thrusting, t);
    ctx.globalAlpha = 1;
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
      // long hints shrink to fit narrow screens and stay inside the view
      let fx = f.x;
      if (f.big) {
        let fw = ctx.measureText(f.txt).width;
        if (fw > VW - 24) { ctx.font = `900 ${Math.max(12, Math.floor(26 * (VW - 24) / fw))}px Orbitron, sans-serif`; fw = ctx.measureText(f.txt).width; }
        if (fw < VW - 12) fx = clamp(fx, cx + fw / 2 + 6, cx + VW - fw / 2 - 6);
      }
      ctx.globalAlpha = Math.min(1, f.life * 2); ctx.fillStyle = f.col; ctx.fillText(f.txt, fx, f.y);
    }
    ctx.globalAlpha = 1;
    ctx.restore();
    if (this.waveT >= 0) {
      const k = this.waveT / 1.4, x = -W * 0.3 + k * W * 1.6, g = ctx.createLinearGradient(x - W * 0.35, 0, x, 0);
      g.addColorStop(0, 'rgba(255,90,30,0)'); g.addColorStop(0.8, `rgba(255,120,40,${0.35 * (1 - k * 0.5)})`); g.addColorStop(1, 'rgba(255,220,150,0)');
      ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
    }
    if (this.moltenT > 0) { ctx.fillStyle = `rgba(255,80,20,${Math.min(0.08, this.moltenT * 0.02)})`; ctx.fillRect(0, 0, W, H); }
    drawDust(ctx, W, H, cx, cy, p.vx, p.vy - (this.gravity ? 420 : 0), this.loc.field.cold ? '#d8f0ff' : this.loc.field.hazard === 'heat' ? '#ffd0a0' : '#cfdcff');
    // crosshair
    if (!isTouch && !mouse.onUI) {
      ctx.strokeStyle = this.inCombat ? 'rgba(255,90,120,0.9)' : 'rgba(61,232,255,0.8)'; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.arc(mouse.x, mouse.y, 9, 0, TAU);
      ctx.moveTo(mouse.x - 14, mouse.y); ctx.lineTo(mouse.x - 5, mouse.y); ctx.moveTo(mouse.x + 5, mouse.y); ctx.lineTo(mouse.x + 14, mouse.y);
      ctx.moveTo(mouse.x, mouse.y - 14); ctx.lineTo(mouse.x, mouse.y - 5); ctx.moveTo(mouse.x, mouse.y + 5); ctx.lineTo(mouse.x, mouse.y + 14);
      ctx.stroke();
    }
    // off-screen indicators: station & enemies
    if (!this.space && p.y < DOCK_Y - VH * 0.45) {
      const full = cargoFree() <= 0;
      const dist = Math.round((DOCK_Y - p.y) / 10) * 10;
      const bx = W / 2, by = H - (isTouch ? 44 : 64);
      ctx.globalAlpha = full ? 0.8 + 0.2 * Math.sin(t * 6) : 0.6;
      ctx.fillStyle = full ? '#ffd24a' : '#3de8ff';
      ctx.font = '700 15px Rajdhani, sans-serif'; ctx.textAlign = 'center';
      ctx.fillText(tx('mine_station_dist', { n: dist }), bx, by);
      ctx.globalAlpha = 1;
    }
    for (const e of [...this.enemies, ...this.rocks.filter(r => r.comet || (r.geode && r.seen > 0 && !(r.seenD > 0)))]) {
      const ex = (e.x - cx) * vz, ey = (e.y - cy) * vz;
      if (ex > 0 && ex < W && ey > 0 && ey < H) continue;
      const a = Math.atan2(ey - H / 2, ex - W / 2);
      const ix = W / 2 + Math.cos(a) * (Math.min(W, H) / 2 - 30), iy = H / 2 + Math.sin(a) * (Math.min(W, H) / 2 - 30);
      ctx.fillStyle = e.comet ? '#bff6ff' : e.geode ? ITEMS[e.geode].c : '#ff4d6d';
      ctx.save(); ctx.translate(ix, iy); ctx.rotate(a);
      ctx.beginPath(); ctx.moveTo(10, 0); ctx.lineTo(-6, -7); ctx.lineTo(-6, 7); ctx.closePath(); ctx.fill(); ctx.restore();
    }
    // warlord health bar
    const boss = this.enemies.find(e => ENEMIES[e.k].boss && !e.dead);
    if (boss) {
      const bw = Math.min(520, W - 40), bx = (W - bw) / 2, by = 100;
      ctx.fillStyle = 'rgba(8,10,24,0.85)'; roundRect(ctx, bx - 10, by - 6, bw + 20, 42, 8); ctx.fill();
      ctx.strokeStyle = '#ff4d6d'; ctx.lineWidth = 1.5; ctx.stroke();
      drawIcon(ctx, 'skull', bx + 8, by + 8, 16, '#ffd24a');
      ctx.fillStyle = '#ffd24a'; ctx.font = '700 13px Rajdhani, sans-serif'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
      const bt = ENEMIES[boss.k].final ? tx('mine_boss_final', { name: ENEMIES[boss.k].n.toUpperCase(), sys: sysName() }) : tx('mine_boss_warlord', { n: fmt(warlordPrize()) });
      for (let fs = 13; fs > 9 && ctx.measureText(bt).width > bw - 26; fs--) ctx.font = `700 ${fs - 1}px Rajdhani, sans-serif`;   // longer (Spanish) titles shrink to fit a phone
      ctx.fillText(bt, bx + 22, by + 8, bw - 24);
      ctx.fillStyle = '#2a1018'; ctx.fillRect(bx, by + 19, bw, 9);
      ctx.fillStyle = '#ff4d6d'; ctx.fillRect(bx, by + 19, bw * clamp(boss.hp / boss.max, 0, 1), 9);
      ctx.fillStyle = '#ff9ec0'; ctx.fillRect(bx, by + 29, bw * clamp(boss.sp / Math.max(1, boss.spMax), 0, 1), 3);
      ctx.textAlign = 'center'; ctx.textBaseline = 'alphabetic';
    }
    // minimap
    const mh = isTouch ? 110 : 150, mw = mh * MW / MH;
    // the minimap never hides under the cargo panel: right side if free, else bottom left
    let mx = W - mw - (isTouch ? 8 : 14), my = isTouch ? hudBottom() + 8 : H - mh - 40;
    const mb = panelRect('.minebox');
    if (mb && mx < mb.right && mx + mw > mb.left && my < mb.bottom && my + mh > mb.top) { if (isTouch) my = mb.bottom + 8; else { mx = 14; my = H - mh - 40; } }
    ctx.fillStyle = 'rgba(8,14,34,0.75)'; ctx.strokeStyle = 'rgba(61,232,255,0.35)'; ctx.lineWidth = 1;
    ctx.fillRect(mx, my, mw, mh); ctx.strokeRect(mx, my, mw, mh);
    if (!this.space) { ctx.fillStyle = 'rgba(61,232,255,0.35)'; ctx.fillRect(mx, my + DOCK_Y / MH * mh, mw, mh - DOCK_Y / MH * mh); }
    for (const r of this.rocks) { ctx.fillStyle = r.comet ? '#bff6ff' : r.geode && r.seen > 0 ? ITEMS[r.geode].c : r.living ? '#9fffe0' : r.gold ? '#ffd24a' : r.rich && S.lv.scanner >= 2 ? ITEMS[r.ore].c : 'rgba(200,190,170,0.7)'; ctx.fillRect(mx + r.x / MW * mw - 1, my + r.y / MH * mh - 1, r.tier * 0.8 + 0.6, r.tier * 0.8 + 0.6); }
    ctx.fillStyle = '#ff4d6d'; for (const e of this.enemies) ctx.fillRect(mx + e.x / MW * mw - 1.5, my + e.y / MH * mh - 1.5, 3, 3);
    ctx.fillStyle = '#3de8ff'; ctx.fillRect(mx + p.x / MW * mw - 2, my + p.y / MH * mh - 2, 4, 4);
    if (this.flashAt) { const k = 1 - (performance.now() - this.flashAt) / 900; if (k > 0) { ctx.fillStyle = `rgba(255,255,255,${k})`; ctx.fillRect(0, 0, W, H); } else this.flashAt = 0; }
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
    for (let x = 150; x < MW; x += 300) ctx.fillText(tx('mine_dock'), x, DOCK_Y - 12);
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
      ctx.fillText(tx('mine_outpost_lv', { n: o.lv }), ox + 9, oy - 4);
      drawIcon(ctx, 'drone', ox - ctx.measureText(tx('mine_outpost_lv', { n: o.lv })).width / 2 - 5, oy - 5, 15);
      ctx.fillStyle = '#ffd24a'; ctx.fillText(`+${fmt(outpostIncome(l.id))}/s`, ox, oy + 14);
    }
  },
  leave(toMap) {
    laserSound(false);
    const got = Object.entries(this.collected);
    if (got.length) addNews('⛏️', tx('mine_news_mined', { name: this.loc.field.n, list: got.map(([k, n]) => `${n} ${ITEMS[k].n}`).join(', ') }), '#ffd24a');
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
  showModal({ icon: '🚨', title: tx('mine_towed_title'), danger: true, html: tx('mine_towed_html', { reason, station: best.station, fee: fee ? tx('mine_towed_fee', { n: fmt(fee) }) : '' }),
    buttons: [{ label: tx('mine_continue'), cls: 'primary', fn: () => { save(); openDock(); } }] });
}
