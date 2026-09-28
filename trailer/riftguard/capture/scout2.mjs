import { launch, ff, setupMatch, info } from './rig.mjs';
import { MATCHES } from './matches.mjs';
import fs from 'fs';
const key = process.argv[2], secs = +process.argv[3] || 120, tag = process.argv[4] || '';
const M = MATCHES[key];
const { browser, page } = await launch({});
await setupMatch(page, { ...M, ultBoost: 90 });
await page.evaluate(() => {
  const R = window.__HOST.R; window.__evs = [];
  Object.defineProperty(R, 'events', { configurable: true, get() { return this._ev; }, set(v) { v.push = function (e) { if (/^(kill|ult|abl|nova|phase|cap|emerge|grip|dmg)$/.test(e.name)) window.__evs.push([+(R.tick / 60).toFixed(3), e.name, e.data]); return Array.prototype.push.call(this, e); }; this._ev = v; } });
  R.events = [];
});
const log = [];
for (let t = 0; t < secs; t += 0.5) { await ff(page, 0.5); log.push(await info(page)); }
const evs = await page.evaluate(() => window.__evs);
fs.writeFileSync(`scout_${key}${tag}.json`, JSON.stringify({ log, evs }));
const ults = evs.filter(e => e[1] === 'ult').length, kills = evs.filter(e => e[1] === 'kill').length;
console.log(key, 'done: ults', ults, 'kills', kills, 'lineup', JSON.stringify(log[log.length - 1].u.map(u => [u[0], u[1]])));
await browser.close();
