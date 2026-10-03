const { open, run, record } = require('./lib.cjs');
(async () => {
  const p = await open();
  await p.evaluate(() => { localStorage.removeItem('solar_prospector_v3'); });
  const t0 = Date.now();
  await record(p, 'probe-title', 2);
  console.log('ms/frame', (Date.now() - t0) / 60);
  await p.browser_.close();
})();
