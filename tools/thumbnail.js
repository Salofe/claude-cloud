// Genera las miniaturas del juego (requiere Playwright): node tools/thumbnail.js
const path = require('path');
let chromium;
try { ({ chromium } = require('playwright')); } catch (e) { ({ chromium } = require('/opt/node22/lib/node_modules/playwright')); }
const dist = path.resolve(__dirname, '..', 'dist');
(async () => {
  const b = await chromium.launch();
  for (const [w, h, name] of [[1280, 720, 'thumbnail.png'], [800, 800, 'thumbnail-square.png']]) {
    const p = await b.newPage({ viewport: { width: w, height: h }, deviceScaleFactor: 1 });
    await p.goto('file://' + path.join(dist, 'index.html') + '?thumb=1');
    await p.waitForSelector('body[data-ready="1"]');
    await p.waitForTimeout(300);
    await p.screenshot({ path: path.join(dist, name) });
    await p.close();
  }
  await b.close();
  console.log('Miniaturas generadas en dist/');
})();
