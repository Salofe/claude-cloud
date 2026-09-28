import { launch, ff, setupMatch, shoot } from './rig.mjs';
import { MATCHES } from './matches.mjs';
import fs from 'fs';
const key = process.argv[2];
const cands = JSON.parse(process.argv[3]); // [[t, id, label, r, h]]
const { browser, page } = await launch({ w: 960, h: 540 });
await setupMatch(page, { ...MATCHES[key], ultBoost: 90 });
let now = await page.evaluate(() => window.__HOST.R.tick / 60);
cands.sort((a, b) => a[0] - b[0]);
for (const [t, id, label, r = 9, h = 4] of cands) {
  const tick = await page.evaluate(() => window.__HOST.R.tick);
  const target = Math.round(t * 60);
  if (target > tick) {
    // advance in exact 1/60 steps so we land on the same tick as the scout
    await page.evaluate(n => { const g = window.__game, o = g.renderer.render; g.renderer.render = () => {}; try { for (let i = 0; i < n; i++) window.__VT.advance(1000 / 60); } finally { g.renderer.render = o; } }, target - tick);
  }
  await page.evaluate(({ id, r, h }) => window.__DIR.set({ type: 'orbit', target: id, r0: r, h0: h, a0: 0.8, spin: 0, fov: 60 }), { id, r, h });
  await page.evaluate(() => window.__game.renderer.render());
  await page.screenshot({ path: `prev/${key}_${t.toFixed(2)}_${label}.jpg`, type: 'jpeg', quality: 80 });
}
await browser.close();
console.log(key, 'previews done');
