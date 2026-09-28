// Virtual clock: every timer, rAF and clock read runs on a time we control, so a frame
// that takes 3 s to render still lands exactly 1/fps after the previous one.
(function () {
  const R = { now: performance.now.bind(performance), setTimeout: window.setTimeout.bind(window), dateNow: Date.now };
  let vt = 0; const epoch = 1790000000000;
  // seeded Math.random so visuals and any stray randomness replay identically
  let seed = 0x9e3779b9;
  function rnd() { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }
  Math.random = rnd;
  const timers = new Map(); let nextId = 1;
  const rafs = new Map(); let rafId = 1;
  performance.now = () => vt;
  Date.now = () => epoch + vt;
  window.setTimeout = function (fn, ms, ...a) { if (typeof fn !== 'function') return 0; const id = nextId++; timers.set(id, { t: vt + Math.max(0, +ms || 0), fn, a, iv: 0 }); return id; };
  window.setInterval = function (fn, ms, ...a) { if (typeof fn !== 'function') return 0; const id = nextId++; const iv = Math.max(1, +ms || 0); timers.set(id, { t: vt + iv, fn, a, iv }); return id; };
  window.clearTimeout = window.clearInterval = id => { timers.delete(id); };
  window.requestAnimationFrame = fn => { const id = rafId++; rafs.set(id, fn); return id; };
  window.cancelAnimationFrame = id => { rafs.delete(id); };
  function runTimersUntil(target) {
    for (let guard = 0; guard < 200000; guard++) {
      let best = null, bid = 0;
      for (const [id, t] of timers) if (t.t <= target && (!best || t.t < best.t || (t.t === best.t && id < bid))) { best = t; bid = id; }
      if (!best) break;
      if (best.t > vt) vt = best.t;
      if (best.iv) best.t += best.iv; else timers.delete(bid);
      try { best.fn(...best.a); } catch (e) { console.error('[vclock timer]', e && e.stack || e); }
    }
    vt = target;
  }
  function runRafs() { const list = [...rafs]; rafs.clear(); for (const [, fn] of list) { try { fn(vt); } catch (e) { console.error('[vclock raf]', e && e.stack || e); } } }
  const VT = window.__VT = {
    mode: 'real', now: () => vt,
    advance(ms) { runTimersUntil(vt + ms); runRafs(); },
    // switch to manual stepping from a fixed, run-independent state
    manual() {
      VT.mode = 'manual'; vt = 100000; seed = 0x12345678;
      for (const [, t] of timers) t.t = t.iv ? vt + t.iv : vt;
    },
    realSetTimeout: R.setTimeout,
  };
  let last = R.now();
  (function pump() {
    if (VT.mode === 'real') { const n = R.now(); const d = Math.min(100, n - last); last = n; VT.advance(d); } else last = R.now();
    R.setTimeout(pump, 16);
  })();
})();
