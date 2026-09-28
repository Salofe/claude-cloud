import { chromium } from 'playwright';
import fs from 'fs';
const HERE = new URL('.', import.meta.url).pathname;
export async function launch({ w = 1280, h = 720, log = false, tier = null, dsf = 1 } = {}) {
  const browser = await chromium.launch({ args: ['--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--ignore-gpu-blocklist', '--disable-background-timer-throttling', '--disable-renderer-backgrounding'] });
  const context = await browser.newContext({ viewport: { width: 960, height: 540 }, deviceScaleFactor: dsf, ignoreHTTPSErrors: true });
  const page = await context.newPage();
  if (tier) await page.addInitScript(`window.__TIER=${JSON.stringify(tier)}`);
  page.on('console', m => { const t = m.text(); if (log || m.type() === 'error') if (!/toNonIndexed|GL Driver|KHR_parallel|ERR_CERT/.test(t)) console.log('[page]', m.type(), t.slice(0, 400)); });
  page.on('pageerror', e => console.log('[pageerror]', e.message));
  await page.addInitScript({ path: HERE + 'vclock.js' });
  await page.addInitScript({ path: HERE + 'host_full.js' });
  await page.addInitScript({ path: HERE + 'director.js' });
  await page.goto('http://localhost:8765/index.html', { timeout: 180000 });
  await page.waitForFunction(() => window.__game && document.getElementById('boot') === null, null, { timeout: 180000, polling: 500 });
  await page.evaluate(() => { window.__VT.manual(); window.__DIR.install(window.__game); });
  page.__size = [w, h];
  return { browser, page };
}
// switch to the capture resolution only once the (cheap to render) match is running
export async function fullRes(page) {
  const [w, h] = page.__size;
  await page.setViewportSize({ width: w, height: h });
  await page.evaluate(() => { window.dispatchEvent(new Event('resize')); window.__game.renderer.resize(); });
  const sz = await page.evaluate(() => [window.__game.canvas.width, window.__game.canvas.height, innerWidth]);
  console.log('canvas', sz);
}
export async function ff(page, sec, { render = false, step = 1000 / 60 } = {}) {
  await page.evaluate(({ sec, render, step }) => {
    const g = window.__game;
    const orig = g.renderer.render; if (!render) g.renderer.render = () => {};
    try { const n = Math.round(sec * 1000 / step); for (let i = 0; i < n; i++) window.__VT.advance(step); }
    finally { g.renderer.render = orig; }
  }, { sec, render, step });
}
// Start a local match: puppet = our player driven by the bot brain.
export async function setupMatch(page, { map = 'halcyon', mode = 'control', hero = '', lineup = null, botLevel = 3, ultBoost = 0, noSwap = true } = {}) {
  await page.evaluate(({ map, mode, lineup, ultBoost, noSwap }) => {
    const g = window.__game, H = window.__HOST;
    g.input.locked = () => true;
    H.puppet = 1; H.lineup = lineup; H.ultBoost = ultBoost; H.noSwap = noSwap;
    g.input.read = () => { const p = window.__puppetIn || {}; const o = { mx: 0, mz: 0, yaw: 0, pitch: 0, fire: false, alt: false, jump: false, a1: false, a2: false, ult: false, reload: false }; for (const k in p) { const v = p[k]; if (typeof v === 'number' || typeof v === 'boolean') o[k] = v; } g.input.yaw = o.yaw; g.input.pitch = o.pitch; return o; };
    g.pickMap(mode, map);
    g.createMatch('Vex', { map });
  }, { map, mode, lineup, ultBoost, noSwap });
  await ff(page, 1);
  await page.evaluate(({ hero, botLevel }) => { const g = window.__game; g.setOpt(10 + botLevel); if (hero) g.requestHero(hero); }, { hero, botLevel });
  await ff(page, 0.5);
  await page.evaluate(() => { const g = window.__game; g.setOpt(0); g.requestStart(); });
  await ff(page, 0.5);
  await page.evaluate(({ hero }) => { if (hero) window.__game.requestHero(hero); }, { hero });
  await ff(page, 0.5);
}
export async function info(page) {
  return page.evaluate(() => { const R = window.__HOST.R, s = R.s; const us = Object.values(s.players).concat(Object.values(s.bots)); return { t: +(R.tick / 60).toFixed(2), ph: s.m.ph, u: us.map(u => [u.id, u.hero, u.team, +u.x.toFixed(1), +u.y.toFixed(1), +u.z.toFixed(1), u.alive ? 1 : 0, Math.round(u.hp), Math.round(u.ultC || 0)]) }; });
}
// Capture `frames` output frames at `fps`; speed scales sim time (0 = frozen, 0.25 = slow-mo).
export async function shoot(page, { shot, frames, fps = 30, speed = 1, dir, start = 0, speedFn = null, fmt = 'jpeg' }) {
  fs.mkdirSync(dir, { recursive: true });
  await page.evaluate(s => window.__DIR.set(s), shot);
  for (let i = 0; i < frames; i++) {
    const sp = speedFn ? speedFn(i / fps) : speed;
    await page.evaluate(({ ms, fdt }) => {
      const g = window.__game, VT = window.__VT;
      window.__DIR.tick(fdt);
      if (ms <= 0) { g.renderer.render(); return; }
      const orig = g.renderer.render; g.renderer.render = () => {};
      let left = ms;
      try { while (left > 1000 / 60 + 1e-6) { VT.advance(1000 / 60); left -= 1000 / 60; } } finally { g.renderer.render = orig; }
      VT.advance(left);
    }, { ms: 1000 / fps * sp, fdt: 1 / fps });
    const f = `${dir}/f${String(start + i).padStart(5, '0')}.${fmt === 'png' ? 'png' : 'jpg'}`;
    await page.screenshot(fmt === 'png' ? { path: f, timeout: 0 } : { path: f, type: 'jpeg', quality: 95, timeout: 0 });
  }
}
