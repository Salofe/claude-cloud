// Deterministic frame capture of Solar Prospector: virtual clock (Playwright page.clock), 1080p, 30 fps.
const { chromium } = require('/opt/node22/lib/node_modules/playwright');
const fs = require('fs'), path = require('path'), { execFileSync } = require('child_process');
const GAME = 'file:///home/user/claude-cloud/dist/index.html?lang=es';
const FRAMES = process.env.FRAMES_DIR || '/tmp/claude-0/-home-user-claude-cloud/4799a72c-bc12-5475-a0f3-43f0486685cf/scratchpad/frames';
const OUT = path.join(__dirname, '..', 'public', 'clips');
const FPS = 30, W = 1920, H = 1080;
const FFMPEG = path.join(__dirname, '..', 'node_modules', '.bin', 'remotion');

async function open(opts = {}) {
  const b = await chromium.launch({ args: ['--autoplay-policy=no-user-gesture-required'] });
  const c = await b.newContext({ viewport: { width: opts.w || 1280, height: opts.h || 720 }, deviceScaleFactor: opts.dpr || 1.5 });
  await c.addInitScript(() => { try { localStorage.setItem('sp_quality', 'high'); } catch (e) {} window.Clawcade = { lang: () => 'es', t: o => o.es || o.en }; });
  const p = await c.newPage();
  p.errs = []; p.on('pageerror', e => p.errs.push(e.message + ' ' + (e.stack || '').split('\n')[1]));
  await p.clock.install({ time: new Date('2026-10-03T12:00:00Z') });
  await p.goto(opts.url || GAME);
  await p.clock.runFor(800);
  await p.addScriptTag({ path: path.join(__dirname, 'page.js') });
  p.cdp = await c.newCDPSession(p);
  p.browser_ = b;
  return p;
}
// advance the virtual clock; CSS animations are stepped in lockstep so UI pulses look right
async function step(p, ms) {
  await p.clock.runFor(ms);
  await p.evaluate(ms => { for (const a of document.getAnimations()) { if (a.playState !== 'paused') a.pause(); a.currentTime = (a.currentTime || 0) + ms; } }, ms);
}
async function run(p, ms) { for (let t = 0; t < ms; t += 50) await step(p, 50); }
// record `sec` seconds into public/clips/<name>.mp4; `each(i)` runs in node before every frame
async function record(p, name, sec, each) {
  const dir = path.join(FRAMES, name); fs.rmSync(dir, { recursive: true, force: true }); fs.mkdirSync(dir, { recursive: true });
  const n = Math.round(sec * FPS);
  for (let i = 0; i < n; i++) {
    if (each) await each(i);
    const { data } = await p.cdp.send('Page.captureScreenshot', { format: 'jpeg', quality: 93 });
    fs.writeFileSync(path.join(dir, String(i).padStart(5, '0') + '.jpg'), Buffer.from(data, 'base64'));
    await step(p, 1000 / FPS);
  }
  fs.mkdirSync(OUT, { recursive: true });
  execFileSync(FFMPEG, ['ffmpeg', '-y', '-loglevel', 'error', '-framerate', String(FPS), '-i', path.join(dir, '%05d.jpg'), '-c:v', 'libx264', '-preset', 'medium', '-crf', '17', '-pix_fmt', 'yuv420p', '-movflags', '+faststart', path.join(OUT, name + '.mp4')]);
  fs.rmSync(dir, { recursive: true, force: true });
  console.log('clip', name, n, 'frames', p.errs.length ? 'ERRS ' + p.errs.slice(0, 3).join(' | ') : '');
}
module.exports = { open, step, run, record, FPS };
