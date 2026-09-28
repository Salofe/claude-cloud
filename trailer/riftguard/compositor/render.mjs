import { chromium } from '../work/node_modules/playwright/index.mjs';
import fs from 'fs';
const [,, from = '0', to = '30', out = 'frames', step = '1'] = process.argv;
fs.mkdirSync(new URL(out + '/', import.meta.url).pathname, { recursive: true });
const b = await chromium.launch();
const p = await b.newPage({ viewport: { width: 1920, height: 1080 } });
p.on('pageerror', e => console.log('ERR', e.message));
await p.goto('http://localhost:8766/comp/index.html');
await p.evaluate(() => window.ready);
const f0 = Math.round(+from * 30), f1 = Math.round(+to * 30);
for (let f = f0; f < f1; f += +step) {
  const data = await p.evaluate(async t => { await window.draw(t); return document.getElementById('c').toDataURL('image/jpeg', 0.95); }, f / 30);
  fs.writeFileSync(new URL(`${out}/f${String(f).padStart(5, '0')}.jpg`, import.meta.url).pathname, Buffer.from(data.split(',')[1], 'base64'));
}
await b.close();
console.log('rendered', f0, f1);
