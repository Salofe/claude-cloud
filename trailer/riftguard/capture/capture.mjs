// Capture one or more shots (chronological) from a match. Usage: node capture.mjs job.json W H
import { launch, ff, setupMatch, shoot, fullRes } from './rig.mjs';
import { MATCHES } from './matches.mjs';
import fs from 'fs';
const job = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const W = +process.argv[3] || 1920, H = +process.argv[4] || 1080, OUT = process.argv[5] || 'shots';
const t0 = Date.now();
const { browser, page } = await launch({ w: W, h: H });
page.on('requestfailed', r => console.log('[reqfail]', r.url().slice(0, 120), r.failure() && r.failure().errorText));
await setupMatch(page, { ...MATCHES[job.match], ultBoost: 90 });
await fullRes(page);
for (const s of job.shots) {
  const tick = await page.evaluate(() => window.__HOST.R.tick);
  const target = Math.round(s.t * 60);
  if (target < tick) { console.log('SKIP (past)', s.name); continue; }
  await page.evaluate(n => { const g = window.__game, o = g.renderer.render; g.renderer.render = () => {}; try { for (let i = 0; i < n; i++) window.__VT.advance(1000 / 60); } finally { g.renderer.render = o; } }, target - tick);
  console.log('at', s.name, JSON.stringify(await page.evaluate(() => { const S = window.__HOST.R.s; return [window.__HOST.R.tick / 60, Object.values(S.bots).concat(Object.values(S.players)).map(u => [u.id, u.hero, +u.x.toFixed(1), +u.y.toFixed(1), +u.z.toFixed(1)])]; })));
  const ramp = s.ramp || null; // [[outSec, speed], ...] linear
  const speedFn = ramp ? (x => { if (x <= ramp[0][0]) return ramp[0][1]; for (let i = 1; i < ramp.length; i++) if (x <= ramp[i][0]) { const [a, sa] = ramp[i - 1], [b, sb] = ramp[i]; return sa + (sb - sa) * (x - a) / (b - a); } return ramp[ramp.length - 1][1]; }) : null;
  const dirp = `${OUT}/${s.name}`;
  if (fs.existsSync(dirp) && fs.readdirSync(dirp).length >= s.frames) { console.log('already done', s.name); continue; }
  const ts = Date.now();
  await shoot(page, { shot: s.shot, frames: s.frames, speed: s.speed === undefined ? 1 : s.speed, speedFn, dir: `${OUT}/${s.name}` });
  console.log('shot', s.name, s.frames, 'frames in', ((Date.now() - ts) / 1000).toFixed(0), 's');
}
await browser.close();
console.log('job done', process.argv[2], ((Date.now() - t0) / 1000).toFixed(0), 's');
