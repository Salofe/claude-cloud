import { launch } from './rig.mjs';
const [W, H] = [+process.argv[2], +process.argv[3]];
const views = JSON.parse(process.argv[4]);
const { browser, page } = await launch({ w: W, h: H });
await page.setViewportSize({ width: W, height: H });
await page.evaluate(() => { window.dispatchEvent(new Event('resize')); window.__game.renderer.resize(); });
let i = 0;
for (const v of views) {
  await page.evaluate(v => { window.__DIR.set({ type: 'dolly', from: v.from, to: v.from, look: v.look, fov0: v.fov, dur: 1 }); window.__DIR.hideHud = true; window.__VT.advance(1000 / 30); }, v);
  await page.screenshot({ path: `lineup_${W}_${i++}.jpg`, type: 'jpeg', quality: 92, timeout: 600000 });
}
await browser.close();
