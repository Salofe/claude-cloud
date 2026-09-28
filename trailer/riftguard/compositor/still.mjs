import { chromium } from '../work/node_modules/playwright/index.mjs';
import fs from 'fs';
const ts = process.argv.slice(2).map(Number);
const b = await chromium.launch();
const p = await b.newPage({ viewport: { width: 1920, height: 1080 } });
p.on('pageerror', e => console.log('ERR', e.message));
await p.goto('http://localhost:8766/comp/index.html');
await p.evaluate(() => window.ready);
for (const t of ts) {
  const data = await p.evaluate(async t => { await window.draw(t); return document.getElementById('c').toDataURL('image/jpeg', 0.9); }, t);
  fs.writeFileSync(`still_${t}.jpg`, Buffer.from(data.split(',')[1], 'base64'));
}
await b.close();
