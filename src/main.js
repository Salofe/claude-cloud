'use strict';
// ============ MOTOR PRINCIPAL ============
const canvas = document.getElementById('c');
const ctx = canvas.getContext('2d');
let W = 0, H = 0, DPR = 1;
let scene = null;
const keys = new Set();
const mouse = { x: 0, y: 0, down: false, onUI: false };
const isTouch = matchMedia('(pointer: coarse)').matches || 'ontouchstart' in window;
let touchFire = false;
const joy = { active: false, dx: 0, dy: 0, id: null, ox: 0, oy: 0 };

function resize() {
  DPR = Math.min(2, window.devicePixelRatio || 1);
  W = window.innerWidth; H = window.innerHeight;
  canvas.width = W * DPR; canvas.height = H * DPR;
  canvas.style.width = W + 'px'; canvas.style.height = H + 'px';
}
window.addEventListener('resize', resize);
resize();

function setScene(sc, arg) {
  if (scene && scene.exit) scene.exit();
  scene = sc;
  if (sc && sc.enter) sc.enter(arg);
  mouse.down = false; touchFire = false;
}

// ---------- entrada ----------
window.addEventListener('keydown', e => {
  if (e.target.tagName === 'INPUT') return;
  keys.add(e.code);
  audioInit();
  if (e.code === 'Space' && scene === MineScene) e.preventDefault();
  if (scene === MineScene && !isBlocking()) { if (e.code === 'KeyQ') MineScene.toggleTool(); if (e.code === 'KeyE') MineScene.pulse(); if (e.code === 'KeyR') MineScene.boost(); if (e.code === 'KeyF') MineScene.bomb(); if (e.code === 'KeyC') MineScene.scan(); if (e.code === 'KeyX') MineScene.phase(); }
  if (e.code === 'Escape') {
    if (!$('sheet').classList.contains('hidden')) closeSheet();
    else if (scene === MineScene && !isBlocking()) MineScene.leave();
  }
});
window.addEventListener('keyup', e => keys.delete(e.code));
window.addEventListener('blur', () => { keys.clear(); mouse.down = false; });

canvas.addEventListener('mousedown', e => { audioInit(); mouse.down = true; mouse.onUI = false; mouse.x = e.clientX; mouse.y = e.clientY; if (scene && scene.onDown && !isBlocking()) scene.onDown(e.clientX, e.clientY); });
window.addEventListener('mousemove', e => { mouse.x = e.clientX; mouse.y = e.clientY; mouse.onUI = e.target !== canvas; if (scene && scene.onMove && !isBlocking()) scene.onMove(e.clientX, e.clientY, mouse.down); });
window.addEventListener('mouseup', e => { if (mouse.down && scene && scene.onUp && !isBlocking()) scene.onUp(e.clientX, e.clientY); mouse.down = false; });
canvas.addEventListener('wheel', e => { e.preventDefault(); if (scene && scene.onWheel && !isBlocking()) scene.onWheel(e.deltaY, e.clientX, e.clientY); }, { passive: false });
canvas.addEventListener('contextmenu', e => e.preventDefault());

// táctil en canvas (mapa: arrastrar/pellizcar)
let pinch = null;
canvas.addEventListener('touchstart', e => {
  audioInit();
  if (scene === MineScene) return;
  e.preventDefault();
  if (e.touches.length === 2) {
    const [a, b] = e.touches;
    pinch = { d: Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY) };
    if (scene.drag) scene.drag.moved = true;
  } else if (e.touches.length === 1 && scene && scene.onDown && !isBlocking()) {
    const t = e.touches[0]; mouse.down = true; scene.onDown(t.clientX, t.clientY);
  }
}, { passive: false });
canvas.addEventListener('touchmove', e => {
  if (scene === MineScene) return;
  e.preventDefault();
  if (e.touches.length === 2 && pinch && scene.onPinch) {
    const [a, b] = e.touches;
    const d = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
    scene.onPinch(d / pinch.d, (a.clientX + b.clientX) / 2, (a.clientY + b.clientY) / 2);
    pinch.d = d;
  } else if (e.touches.length === 1 && scene && scene.onMove) {
    const t = e.touches[0]; scene.onMove(t.clientX, t.clientY, true);
  }
}, { passive: false });
canvas.addEventListener('touchend', e => {
  if (scene === MineScene) return;
  e.preventDefault();
  if (e.touches.length === 0) {
    const t = e.changedTouches[0];
    if (!pinch && scene && scene.onUp && !isBlocking()) scene.onUp(t.clientX, t.clientY);
    pinch = null; mouse.down = false;
  }
}, { passive: false });

// joystick + botón láser (minería en móvil)
function setupTouchControls() {
  const zone = $('joyZone'), knob = $('joyKnob'), base = $('joyBase'), fire = $('fireBtn');
  zone.addEventListener('touchstart', e => {
    e.preventDefault(); audioInit();
    const t = e.changedTouches[0];
    joy.id = t.identifier; joy.active = true; joy.ox = t.clientX; joy.oy = t.clientY;
    base.style.left = (t.clientX - 55) + 'px'; base.style.top = (t.clientY - 55) + 'px'; base.classList.add('on');
    knob.style.transform = 'translate(0,0)';
  }, { passive: false });
  zone.addEventListener('touchmove', e => {
    e.preventDefault();
    for (const t of e.changedTouches) if (t.identifier === joy.id) {
      let dx = t.clientX - joy.ox, dy = t.clientY - joy.oy;
      const l = Math.hypot(dx, dy), m = 45;
      if (l > m) { dx *= m / l; dy *= m / l; }
      joy.dx = dx / m; joy.dy = dy / m;
      knob.style.transform = `translate(${dx}px,${dy}px)`;
    }
  }, { passive: false });
  const end = e => { for (const t of e.changedTouches) if (t.identifier === joy.id) { joy.active = false; joy.dx = joy.dy = 0; base.classList.remove('on'); } };
  zone.addEventListener('touchend', end); zone.addEventListener('touchcancel', end);
  fire.addEventListener('touchstart', e => { e.preventDefault(); touchFire = true; fire.classList.add('on'); }, { passive: false });
  $('toolBtn').addEventListener('touchstart', e => { e.preventDefault(); MineScene.toggleTool(); }, { passive: false });
  $('pullBtn').addEventListener('touchstart', e => { e.preventDefault(); MineScene.pulse(); }, { passive: false });
  $('boostBtn').addEventListener('touchstart', e => { e.preventDefault(); MineScene.boost(); }, { passive: false });
  $('bombBtn').addEventListener('touchstart', e => { e.preventDefault(); MineScene.bomb(); }, { passive: false });
  $('scanBtn').addEventListener('touchstart', e => { e.preventDefault(); MineScene.scan(); }, { passive: false });
  $('phaseBtn').addEventListener('touchstart', e => { e.preventDefault(); MineScene.phase(); }, { passive: false });
  for (const el of document.querySelectorAll('.tbtn')) { el.addEventListener('touchstart', () => el.classList.add('on'), { passive: true }); for (const ev of ['touchend', 'touchcancel']) el.addEventListener(ev, () => el.classList.remove('on')); }
  const fe = e => { e.preventDefault(); touchFire = false; fire.classList.remove('on'); };
  fire.addEventListener('touchend', fe); fire.addEventListener('touchcancel', fe);
}

// ---------- bucle ----------
let last = performance.now(), hudT = 0, saveT = 0, peakT = 0, postT = 0;
function frame(now) {
  const dt = Math.min(0.05, (now - last) / 1000); last = now;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (scene) {
    if (!isBlocking() || scene === MapScene || scene === TitleScene) scene.update(dt);
    scene.draw(ctx);
  }
  if (S && scene !== TitleScene) { incomeTick(dt); tributeTick(dt); hudTick(dt); dayClock(dt); }
  hudT += dt;
  if (hudT > 0.3 && S && scene !== TitleScene) { hudT = 0; updateHUD(); if ((saveT += 0.3) > 10) { saveT = 0; save(); }
    // leaderboard: check the record every 5 s, send it at most once a minute
    if ((peakT += 0.3) >= 5) { peakT = 0; trackPeak(); }
    if ((postT += 0.3) >= 60) { postT = 0; postPeak(); } }
  requestAnimationFrame(frame);
}

// ---------- player-facing text (English + Spanish) ----------
Object.assign(TXT, {
  main_tag: { en: 'Mine · Upgrade · Cross the Galaxy', es: 'Mina · Mejora · Cruza la Galaxia' },
  main_play: { en: '▶ PLAY', es: '▶ JUGAR' },
  main_howto: { en: 'How to play', es: 'Cómo jugar' },
  main_foot: { en: 'Mouse & keyboard or touch · Saves automatically', es: 'Mouse y teclado o táctil · Guardado automático' },
  main_foot_touch: { en: 'Touch controls · Saves automatically', es: 'Controles táctiles · Guardado automático' },
  main_credits: { en: 'Credits', es: 'Créditos' },
  main_day: { en: 'Day', es: 'Día' },
  main_cargo: { en: 'Cargo', es: 'Carga' },
  main_hull: { en: 'Hull', es: 'Casco' },
  main_fuel: { en: 'Fuel', es: 'Combust.' },
  main_influence: { en: 'Influence', es: 'Influencia' },
  main_ship: { en: 'Ship', es: 'Nave' },
  main_news: { en: 'News', es: 'Noticias' },
  main_empire: { en: 'Empire', es: 'Imperio' },
  main_megaprojects: { en: 'Megaprojects', es: 'Megaproyectos' },
  main_projects: { en: 'Projects', es: 'Proyectos' },
  main_galaxy: { en: 'Galaxy', es: 'Galaxia' },
  main_sound: { en: 'Sound', es: 'Sonido' },
  main_menu: { en: 'Menu', es: 'Menú' },
  main_myship: { en: 'My ship', es: 'Mi nave' },
  main_wholesys: { en: 'Whole system', es: 'Todo el sistema' },
  main_t_fire: { en: 'FIRE', es: 'DISPARAR' },
  main_t_drill: { en: 'DRILL', es: 'TALADRO' },
  main_t_pull: { en: 'PULL', es: 'ATRAER' },
  main_t_boost: { en: 'BOOST', es: 'TURBO' },
  main_t_bomb: { en: 'BOMB', es: 'BOMBA' },
  main_t_scan: { en: 'SCAN', es: 'ESCANEAR' },
  main_t_phase: { en: 'PHASE', es: 'FASE' },
  main_bt_pirates: { en: '⚔ PIRATES', es: '⚔ PIRATAS' },
  main_bt_warp: { en: '⚡ Warp out', es: '⚡ Escapar' },
  main_bt_continue: { en: 'Continue ▶', es: 'Continuar ▶' },
  main_meta_desc: { en: 'Mine asteroids, upgrade your ship, trade between planets and rule the Solar System.', es: 'Mina asteroides, mejora tu nave, comercia entre planetas y gobierna el Sistema Solar.' },
  main_continue: { en: '▶ Continue', es: '▶ Continuar' },
  main_conq1: { en: '1 system conquered', es: '1 sistema conquistado' },
  main_conq: { en: '{n} systems conquered', es: '{n} sistemas conquistados' },
  main_newgame: { en: 'New game', es: 'Nueva partida' },
  main_new_title: { en: 'Start a new game?', es: '¿Empezar una nueva partida?' },
  main_new_html: { en: 'Your saved game will be overwritten.', es: 'Tu partida guardada se va a sobrescribir.' },
  main_new_ok: { en: 'Start over', es: 'Empezar de cero' },
  main_cancel: { en: 'Cancel', es: 'Cancelar' },
  main_thumb_tag: { en: 'MINE · TRADE · CROSS THE GALAXY', es: 'MINA · COMERCIA · CRUZA LA GALAXIA' },
  main_wb_trib: { en: 'Your conquered systems sent <b>+{n} Tribute</b>.', es: 'Tus sistemas conquistados enviaron <b>+{n} de Tributo</b>.' },
  main_wb_capped: { en: 'You were away <b>{t}</b>. Drones only work unsupervised for <b>{cap}</b>, so you were paid for the <b>last 8 hours</b>.', es: 'Estuviste fuera <b>{t}</b>. Los drones solo trabajan sin supervisión <b>{cap}</b>, así que te pagaron las <b>últimas 8 horas</b>.' },
  main_wb_away: { en: 'You were away <b>{t}</b>.', es: 'Estuviste fuera <b>{t}</b>.' },
  main_wb_day1: { en: '<b>1 day</b> passed in the system.', es: 'Pasó <b>1 día</b> en el sistema.' },
  main_wb_days: { en: '<b>{n} days</b> passed in the system.', es: 'Pasaron <b>{n} días</b> en el sistema.' },
  main_wb_title: { en: 'Welcome back!', es: '¡Bienvenido de vuelta!' },
  main_wb_earned: { en: 'Your drones and freighters earned', es: 'Tus drones y cargueros ganaron' },
  main_wb_rate: { en: '({pct}% of your income rate, max {cap})', es: '({pct}% de tu ritmo de ingresos, máx. {cap})' },
  main_wb_collect: { en: 'Collect', es: 'Cobrar' },
  main_toast_away: { en: '🤖 Drones earned +{n} cr while you were away', es: '🤖 Tus drones ganaron +{n} cr mientras no estabas' },
});
// static text in index.html: elements marked data-tx / data-tx-title get the player's language at boot
function translateStatic() {
  for (const el of document.querySelectorAll('[data-tx]')) el.textContent = tx(el.dataset.tx);
  for (const el of document.querySelectorAll('[data-tx-title]')) el.title = tx(el.dataset.txTitle);
  if (isTouch) document.querySelector('#title .foot').textContent = tx('main_foot_touch');
  const md = document.querySelector('meta[name="description"]'); if (md) md.content = tx('main_meta_desc');
}

// ---------- pantalla de título ----------
const TitleScene = {
  t: 0,
  enter() {
    $('title').classList.remove('hidden'); $('hud').classList.add('hidden');
    const sv = hasSave();
    $('cont').classList.toggle('hidden', !sv);
    if (sv) { const d = loadSave(); $('cont').innerHTML = `${tx('main_continue')} <small>${fmt(d.credits)} cr · ${(SYSTEMS[d.sys || 'sol'] || SYSTEMS.sol).n}${d.galaxy ? ` · ${tx(d.galaxy.done.length === 1 ? 'main_conq1' : 'main_conq', { n: d.galaxy.done.length })}` : ''}</small>`; }
    $('newg').textContent = sv ? tx('main_newgame') : tx('main_play');
    $('newg').classList.toggle('primary', !sv);
  },
  exit() { $('title').classList.add('hidden'); $('hud').classList.remove('hidden'); },
  update(dt) { this.t += dt; },
  draw(ctx) {
    const t = this.t;
    drawSpaceBg(ctx, W, H, t * 8, t * 3, t);
    const cx = W * 0.5, cy = H * 0.55, z = Math.min(W, H) / 1250;
    drawSun(ctx, cx, cy, 16 * z * 2, t);
    const day = t * 6;
    for (const l of LOCS) {
      if (l.parent || l.follow) continue;
      ctx.strokeStyle = 'rgba(120,160,255,0.1)'; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.ellipse(cx, cy, l.r * z * 1.7, l.r * z * 0.75, 0, 0, TAU); ctx.stroke();
      const a = l.a0 + day / l.period * TAU * 3;
      const px = cx + Math.cos(a) * l.r * z * 1.7, py = cy + Math.sin(a) * l.r * z * 0.75;
      if (l.id === 'kuiper') continue;
      drawPlanet(ctx, px, py, Math.max(3, l.size * z * 2.2), l, Math.atan2(cy - py, cx - px), t);
    }
    // nave que cruza
    const sx = ((t * 70) % (W + 400)) - 200, sy = H * 0.32 + Math.sin(t * 0.8) * 20;
    drawPlayerShip(ctx, { hull: 4, engine: 4, weapons: 3, laser: 3 }, sx, sy, 0.05, 1.1, 1, t);
    // a few big asteroids tumbling past in the foreground
    if (!this.rocks) this.rocks = [0, 1, 2, 3].map(i => ({ r: [70, 38, 54, 26][i], ore: ['iron', 'nickel', 'cobalt', 'he3'][i], tier: 3, shape: makeRockShape(11, 0.22),
      veins: Array.from({ length: 5 }, () => { const a = rand(0, TAU), d = rand(0, 0.6); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.07, 0.15)]; }),
      craters: Array.from({ length: 3 }, () => [rand(-0.5, 0.5), rand(-0.5, 0.5), rand(0.1, 0.2)]), sp: [9, 16, 12, 22][i], y0: [0.82, 0.18, 0.62, 0.9][i], ph: i * 0.27, hit: 0, hp: 1, maxhp: 1 }));
    for (const r of this.rocks) {
      const span = W + 300; r.x = ((r.ph * span + t * r.sp) % span) - 150; r.y = H * r.y0 + Math.sin(t * 0.2 + r.ph * 9) * 20; r.rot = t * 0.08 * (r.sp % 2 ? 1 : -1) + r.ph;
      drawRock(ctx, r, t, 0);
    }
    drawDust(ctx, W, H, t * 40, t * 6, 40, 6);
  },
};

function startGame(cont) {
  audioInit();
  if (cont) S = loadSave();
  if (!S) { applySystem('sol'); newGame(); save(); }
  applySystem(sysId());
  ensureMarkets();
  shownCredits = S.credits;
  pendingUnlocks = [];
  if (cont && has(U.MAP)) setScene(MapScene);
  else setScene(MineScene, cont ? (LOC[S.loc].field ? S.loc : 'luna') : 'luna');
  if (!cont) S.loc = 'luna';
  updateHUD(); updateTicker();
  if (cont) {
    const off = offlineGains();
    if (off) setTimeout(() => welcomeBack(off), 300);
  }
}

// ---------- inicio ----------
function init() {
  translateStatic();
  startIconizer();
  setupTouchControls();
  $('bGal').onclick = openGalaxy; $('bShip').onclick = openShip; $('bProj').onclick = openProjects; $('bFac').onclick = openFactions; $('bNews').onclick = openNews; $('bMenu').onclick = openMenu;
  const snd = $('bSnd');
  snd.textContent = muted ? '🔇' : '🔊';
  snd.onclick = () => { audioInit(); setMuted(!muted); snd.textContent = muted ? '🔇' : '🔊'; };
  $('zIn').onclick = () => MapScene.onWheel(-300, W / 2, H / 2);
  $('zOut').onclick = () => MapScene.onWheel(300, W / 2, H / 2);
  $('zHome').onclick = () => MapScene.focus(S.loc);
  $('zAll').onclick = () => MapScene.zoomAll();
  $('btnWarp').onclick = () => { if (MineScene.space && !MineScene.warp) { MineScene.warp = { t: 0 }; sfx('warp'); } };
  $('btnContinue').onclick = () => MineScene.finishSpace(true);
  $('newg').onclick = () => { if (hasSave()) { showModal({ icon: '⚠️', title: tx('main_new_title'), html: tx('main_new_html'), buttons: [{ label: tx('main_new_ok'), cls: 'danger', fn: () => { S = null; try { localStorage.removeItem(SAVE_KEY); } catch (e) {} startGame(false); } }, { label: tx('main_cancel'), fn: () => {} }] }); } else startGame(false); };
  $('cont').onclick = () => startGame(true);
  $('howto').onclick = () => { openHelp(); };
  const params = new URLSearchParams(location.search);
  if (params.has('thumb')) return thumbMode(params.get('thumb'));
  setScene(TitleScene);
  requestAnimationFrame(frame);
}

// ---------- modo miniatura (portada del juego) ----------
function thumbMode(kind) {
  document.body.classList.add('thumb');
  newGame();
  S.lv = { hull: 4, laser: 26, magnet: 10, cargo: 5, refinery: 5, engine: 14, tank: 3, shield: 10, weapons: 18, scanner: 3 };
  $('title').classList.add('hidden'); $('hud').classList.add('hidden');
  const t = 12.3;
  drawSpaceBg(ctx, W, H, 120, 80, t, '#141a44');
  drawPlanet(ctx, W * 0.83, H * 0.26, H * 0.36, LOC.saturno, Math.PI * 0.85, t);
  drawSun(ctx, -W * 0.02, H * 0.95, 70, t);
  MineScene.loc = LOC.saturno;
  const rocks = [];
  const mk = (x, y, tier, ore, rich) => { const r = { x, y, r: [0, 20, 34, 56][tier] * 1.5, tier, ore, rich, rot: rand(0, TAU), hit: 0, shape: makeRockShape(9 + tier * 2, 0.22),
    veins: Array.from({ length: 3 + tier * 2 }, () => { const a = rand(0, TAU), d = rand(0, 0.6); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.07, 0.16)]; }),
    craters: Array.from({ length: tier }, () => { const a = rand(0, TAU), d = rand(0, 0.5); return [Math.cos(a) * d, Math.sin(a) * d, rand(0.1, 0.2)]; }) }; rocks.push(r); return r; };
  const big = mk(W * 0.64, H * 0.6, 3, 'iridium', true);
  mk(W * 0.86, H * 0.78, 2, 'platinum', false); mk(W * 0.5, H * 0.86, 1, 'ice', false); mk(W * 0.92, H * 0.5, 1, 'he3', true); mk(W * 0.24, H * 0.92, 2, 'nickel', false); mk(W * 0.72, H * 0.14, 1, 'exotic', true);
  for (const r of rocks) drawRock(ctx, r, t, 3);
  const sx = W * 0.3, sy = H * 0.62;
  const ang = Math.atan2(big.y - sy, big.x - sx);
  // láser
  const col = laserColor(4), nx = sx + Math.cos(ang) * 90 * Math.min(1, W / 1024), ny = sy + Math.sin(ang) * 90 * Math.min(1, W / 1024);
  const hx = big.x - Math.cos(ang) * big.r * 0.8, hy = big.y - Math.sin(ang) * big.r * 0.8;
  ctx.globalCompositeOperation = 'lighter';
  ctx.strokeStyle = col; ctx.globalAlpha = 0.4; ctx.lineWidth = 16;
  ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(hx, hy); ctx.stroke();
  ctx.globalAlpha = 1; ctx.strokeStyle = '#fff'; ctx.lineWidth = 3;
  ctx.beginPath(); ctx.moveTo(nx, ny); ctx.lineTo(hx, hy); ctx.stroke();
  ctx.globalCompositeOperation = 'source-over';
  glow(ctx, hx, hy, 60, col, 1);
  const P = new Particles();
  for (let i = 0; i < 60; i++) { const a = ang + Math.PI + rand(-1.2, 1.2), v = rand(10, 80); P.add(hx + Math.cos(a) * v, hy + Math.sin(a) * v, 0, 0, rand(0.3, 1), Math.random() < 0.5 ? ITEMS.iridium.c : col, rand(1.5, 4)); }
  P.draw(ctx);
  for (let i = 0; i < 7; i++) drawOreChunk(ctx, { x: sx + 60 + i * 38 + rand(-10, 10), y: sy + 70 + Math.sin(i) * 26, ore: pick(['iridium', 'platinum', 'he3']), rot: i }, 0);
  // piratas a lo lejos
  drawEnemyShip(ctx, 'corsair', W * 0.95, H * 0.93, Math.PI * 1.1, 1.3, t);
  drawEnemyShip(ctx, 'raider', W * 0.88, H * 0.97, Math.PI * 1.05, 1.1, t);
  drawPlayerShip(ctx, shipLv(), sx, sy, ang, 3.0 * Math.min(1, W / 1280 * 1.25), 1, t);
  // título
  if (kind !== 'clean') {
    const s = Math.min(W / 1280, H / 720);
    ctx.textAlign = 'left';
    ctx.font = `900 ${Math.round(92 * s)}px Orbitron, 'Arial Black', sans-serif`;
    ctx.shadowColor = '#3de8ff'; ctx.shadowBlur = 30 * s;
    ctx.fillStyle = '#ffffff';
    ctx.fillText('SOLAR', 60 * s, 130 * s);
    ctx.fillStyle = '#3de8ff';
    ctx.fillText('PROSPECTOR', 60 * s, 225 * s);
    ctx.shadowBlur = 0;
    ctx.font = `600 ${Math.round(30 * s)}px Rajdhani, sans-serif`;
    ctx.fillStyle = '#ffd24a';
    ctx.fillText(tx('main_thumb_tag'), 64 * s, 275 * s);
  }
  document.body.dataset.ready = '1';
}

// one shared clock: a day every DAY_SEC seconds on any screen. It pauses while a popup
// asks you something, during fights, and while travelling (trips count their own days).
function dayClock(dt) {
  if (!has(U.MAP) || !$('modal').classList.contains('hidden')) return;
  if (MapScene.travel || (scene === MineScene && MineScene.inCombat)) return;
  S.dayT = (S.dayT || 0) + Math.min(dt, 0.25);
  if (S.dayT >= DAY_SEC) { S.dayT -= DAY_SEC; tickDay(); updateHUD(); }
}
function welcomeBack(off) {
  const trib = off.trib >= 1 ? `<p>${tx('main_wb_trib', { n: Math.floor(off.trib) })}</p>` : '';
  const away = off.capped
    ? tx('main_wb_capped', { t: fmtTime(off.real), cap: fmtTime(OFFLINE_CAP) })
    : tx('main_wb_away', { t: fmtTime(off.real) });
  const days = off.days ? `<p class="hint">${tx(off.days === 1 ? 'main_wb_day1' : 'main_wb_days', { n: off.days })}</p>${off.news.length ? `<div class="wb-news">${off.news.map(n => `<div>${n.icon} ${n.html}</div>`).join('')}</div>` : ''}` : '';
  showModal({ icon: '🤖', title: tx('main_wb_title'), html: `<p>${away}</p>${off.g >= 1 ? `<p>${tx('main_wb_earned')}<br><b class="cr big-num">+${fmt(off.g)} cr</b>${off.capped ? `<br><small class="dim">${tx('main_wb_rate', { pct: Math.round(OFFLINE_RATE * 100), cap: fmtTime(OFFLINE_CAP) })}</small>` : ''}</p>` : ''}${days}`,
    buttons: [{ label: tx('main_wb_collect'), cls: 'primary', fn: () => {} }] });
  if (trib) $('modal').querySelector('.mbody').insertAdjacentHTML('beforeend', trib);
}
function fmtTime(s) { s = Math.floor(s); const d = Math.floor(s / 86400), h = Math.floor(s % 86400 / 3600), m = Math.floor(s % 3600 / 60); return d ? `${d}d${h ? ` ${h}h` : ''}` : h ? `${h}h${m ? ` ${m}m` : ''}` : m ? `${m}m` : `${s}s`; }
window.addEventListener('pagehide', () => { save(); postPeak(); });
document.addEventListener('visibilitychange', () => { if (!S) return; if (document.hidden) { save(); postPeak(); } else { const off = offlineGains(); if (!off) return; updateHUD(); if (off.real >= 300 && $('modal').classList.contains('hidden')) welcomeBack(off); else if (off.g >= 1) toast(tx('main_toast_away', { n: fmt(off.g) }), 'good'); } });
window.addEventListener('load', init);
