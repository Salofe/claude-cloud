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
  if (e.code === 'Escape') {
    if (!$('sheet').classList.contains('hidden')) closeSheet();
    else if (scene === MineScene && !modalOpen) MineScene.leave();
  }
});
window.addEventListener('keyup', e => keys.delete(e.code));
window.addEventListener('blur', () => { keys.clear(); mouse.down = false; });

canvas.addEventListener('mousedown', e => { audioInit(); mouse.down = true; mouse.onUI = false; mouse.x = e.clientX; mouse.y = e.clientY; if (scene && scene.onDown && !modalOpen) scene.onDown(e.clientX, e.clientY); });
window.addEventListener('mousemove', e => { mouse.x = e.clientX; mouse.y = e.clientY; mouse.onUI = e.target !== canvas; if (scene && scene.onMove && !modalOpen) scene.onMove(e.clientX, e.clientY, mouse.down); });
window.addEventListener('mouseup', e => { if (mouse.down && scene && scene.onUp && !modalOpen) scene.onUp(e.clientX, e.clientY); mouse.down = false; });
canvas.addEventListener('wheel', e => { e.preventDefault(); if (scene && scene.onWheel && !modalOpen) scene.onWheel(e.deltaY, e.clientX, e.clientY); }, { passive: false });
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
  } else if (e.touches.length === 1 && scene && scene.onDown && !modalOpen) {
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
    if (!pinch && scene && scene.onUp && !modalOpen) scene.onUp(t.clientX, t.clientY);
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
  const fe = e => { e.preventDefault(); touchFire = false; fire.classList.remove('on'); };
  fire.addEventListener('touchend', fe); fire.addEventListener('touchcancel', fe);
}

// ---------- bucle ----------
let last = performance.now(), hudT = 0;
function frame(now) {
  const dt = Math.min(0.05, (now - last) / 1000); last = now;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (scene) {
    if (!modalOpen || scene === BattleScene || (scene === MapScene && !MapScene.travel)) {
      if (!(modalOpen && scene === MineScene)) scene.update(dt);
    } else if (scene === MapScene) MapScene.t += dt;
    scene.draw(ctx);
  }
  hudT += dt;
  if (hudT > 0.3 && S && scene !== TitleScene) { hudT = 0; updateHUD(); }
  requestAnimationFrame(frame);
}

// ---------- pantalla de título ----------
const TitleScene = {
  t: 0,
  enter() { $('title').classList.remove('hidden'); $('hud').classList.add('hidden'); $('cont').classList.toggle('hidden', !hasSave()); },
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
    drawPlayerShip(ctx, { hull: 3, engine: 4, weapons: 2, laser: 3 }, sx, sy, 0.05, 1.3, 1, t);
  },
};

function startGame(cont) {
  audioInit();
  if (cont) S = loadSave();
  if (!S) { newGame(); save(); }
  setScene(MapScene);
  updateHUD(); updateTicker();
  if (!cont) setTimeout(() => showModal({ icon: '🚀', title: 'A bordo', html: `La <b>${S.shipName}</b> es tuya: una nave minera modesta con 600 créditos y un sueño.<br><br>
    <b>Mina</b> asteroides, <b>comercia</b> entre planetas, <b>sobrevive</b> a los piratas y aprovecha las crisis del sistema para <b>ganar influencia</b>.<br><br>Sigue los objetivos de la esquina superior izquierda.`,
    buttons: [{ label: '¡Vamos!', cls: 'primary', fn: () => selectLoc('luna') }, { label: 'Cómo jugar', fn: openHelp }] }), 300);
  checkTut();
}

// ---------- inicio ----------
function init() {
  setupTouchControls();
  $('bShip').onclick = openShip; $('bFac').onclick = openFactions; $('bNews').onclick = openNews; $('bMenu').onclick = openMenu;
  const snd = $('bSnd');
  snd.textContent = muted ? '🔇' : '🔊';
  snd.onclick = () => { audioInit(); setMuted(!muted); snd.textContent = muted ? '🔇' : '🔊'; };
  $('zIn').onclick = () => MapScene.onWheel(-300, W / 2, H / 2);
  $('zOut').onclick = () => MapScene.onWheel(300, W / 2, H / 2);
  $('zHome').onclick = () => MapScene.focus(S.loc);
  $('zAll').onclick = () => MapScene.zoomAll();
  $('btnLeave').onclick = () => MineScene.leave();
  $('btnSpeed').onclick = () => { BattleScene.speed = BattleScene.speed === 1 ? 2 : BattleScene.speed === 2 ? 4 : 1; $('btnSpeed').textContent = 'Velocidad ×' + BattleScene.speed; };
  $('btnRetreat').onclick = () => BattleScene.retreat();
  $('newg').onclick = () => { if (hasSave()) { showModal({ icon: '⚠️', title: '¿Nueva partida?', html: 'Se sobrescribirá tu partida guardada.', buttons: [{ label: 'Empezar de nuevo', cls: 'danger', fn: () => { S = null; try { localStorage.removeItem(SAVE_KEY); } catch (e) {} startGame(false); } }, { label: 'Cancelar', fn: () => {} }] }); } else startGame(false); };
  $('cont').onclick = () => startGame(true);
  $('howto').onclick = () => { openHelp(); };
  for (const el of document.querySelectorAll('.ui')) {
    el.addEventListener('mouseenter', () => mouse.onUI = true);
    el.addEventListener('mouseleave', () => mouse.onUI = false);
  }
  const params = new URLSearchParams(location.search);
  if (params.has('thumb')) return thumbMode(params.get('thumb'));
  setScene(TitleScene);
  requestAnimationFrame(frame);
}

// ---------- modo miniatura (portada del juego) ----------
function thumbMode(kind) {
  document.body.classList.add('thumb');
  newGame();
  S.lv = { hull: 4, laser: 4, engine: 4, tank: 3, shield: 3, weapons: 3, drones: 3, scanner: 3 };
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
  drawPlayerShip(ctx, S.lv, sx, sy, ang, 3.0 * Math.min(1, W / 1280 * 1.25), 1, t);
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
    ctx.fillText('MINA · COMERCIA · DOMINA EL SISTEMA SOLAR', 64 * s, 275 * s);
  }
  document.body.dataset.ready = '1';
}

window.addEventListener('load', init);
