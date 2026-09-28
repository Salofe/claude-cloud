// Local stand-in for the Clawcade platform: answers the Server client's postMessage protocol
// and runs the game's own authoritative SERVER code (bots, abilities, rounds) inside the page.
(function () {
  const realPost = window.postMessage.bind(window);
  const inbox = [], outbox = [];
  let flushQueued = false;
  function queueFlush() { if (!flushQueued) { flushQueued = true; setTimeout(flush, 0); } }
  function flush() {
    flushQueued = false;
    while (inbox.length || outbox.length) {
      while (inbox.length) handle(inbox.shift());
      while (outbox.length) window.dispatchEvent(new MessageEvent('message', { data: outbox.shift(), source: window }));
    }
  }
  window.postMessage = function (m, o, t) {
    if (m && m.clawcade === 'srv') { inbox.push(m); queueFlush(); return; }
    return realPost(m, o, t);
  };
  const raw = m => { outbox.push(Object.assign({ clawcade: 'srv' }, m)); queueFlush(); };
  const msg = m => raw({ op: 'msg', data: JSON.stringify(m) });

  const HOST = window.__HOST = { R: null, puppet: 0, snapRate: 60, pendingName: '', role: '' };
  let R = null, ctx = null, interval = 0;

  function call(fn, seedV, args) {
    const r = LIB.rng(seedV); ctx.random = r; const saved = Math.random; Math.random = r;
    try { return fn.apply(null, args); } catch (e) { console.error('[host] server code error', e && e.stack || e); } finally { Math.random = saved; }
  }
  function build(src) {
    src = src.replace('tick(s,dt2,ctx){s.lastNow=ctx.now;', 'tick(s,dt2,ctx){s.lastNow=ctx.now;if(globalThis.__puppetHook)globalThis.__puppetHook(s,ctx,dt2,{BotBrain,Units,PlayerSim,Bots,Match,Roster});');
    const saved = Math.random, r0 = LIB.rng(1); Math.random = r0; let def; try { def = (0, eval)('(' + src + ')')(); } finally { Math.random = saved; }
    const tickRate = def.tickRate || 60, dt = 1 / tickRate, hb = def.hitbox || {};
    R = HOST.R = { def, dt, tickRate, tick: 0, seed: 424242, names: {}, cmds: {}, ack: {}, events: [], s: null, curSrc: null, emitN: {}, world: new LIB.World() };
    const host = {
      server: true, dt, tickRate, world: R.world,
      hitbox: { radius: +hb.radius || 0.4, height: +hb.height || 1.8, head: hb.head === undefined ? 0.25 : +hb.head },
      positions() { const out = []; for (const k in R.s.players) { const q = R.s.players[k]; if (typeof q.x === 'number') out.push([+k, q.x, q.y || 0, q.z || 0, q.alive === false ? 0 : 1, q.team === undefined ? null : q.team]); } return out; },
      players() { return Object.keys(R.s.players).map(k => R.s.players[k]); },
      emit(name, data, opts) {
        let tag = null;
        if (R.curSrc) { const n = R.emitN[name] = (R.emitN[name] || 0) + 1; tag = [R.curSrc[0], R.curSrc[1], n]; }
        R.events.push({ name, data: JSON.parse(JSON.stringify(data === undefined ? null : data)), to: opts && opts.to || 0, tag });
      },
      name(id) { return R.names[id] || ''; },
    };
    ctx = LIB.makeCtx(host);
    ctx.now = 0; ctx.time = 0; ctx.tick = 0;
    R.s = call(def.init, R.seed, [ctx]) || {};
    if (!R.s.players) R.s.players = {};
    clearInterval(interval);
    interval = setInterval(step, 1000 / tickRate);
  }
  function addPlayer(id, name) {
    R.names[id] = name; ctx.id = id; ctx.now = ctx.time = R.tick * R.dt; ctx.tick = R.tick;
    const p = call(R.def.join, LIB.hash2(id, 7), [R.s, id, ctx]) || {};
    p.id = id; R.s.players[id] = p; R.cmds[id] = []; R.ack[id] = 0;
    R.events.push({ name: '__join', data: { id, name }, to: 0, tag: null });
    msg({ t: 'welcome', id, seed: R.seed, tickRate: R.tickRate, snapRate: HOST.snapRate, players: Object.keys(R.names).map(k => [+k, R.names[k]]), st: performance.now() });
  }
  function step() {
    const dt = R.dt;
    for (const id in R.cmds) {
      const p = R.s.players[id], q = R.cmds[id];
      while (q.length) {
        const c = q.shift(); if (!p) continue;
        R.curSrc = [+id, c[0]]; R.emitN = {};
        ctx.id = +id; ctx.seq = c[0]; ctx.time = c[0] * dt; ctx.now = R.tick * dt; ctx.tick = R.tick;
        call(R.def.move, LIB.hash2(+id, c[0]), [p, c[2], dt, R.s, ctx]);
        R.ack[id] = c[0];
      }
    }
    R.curSrc = null; ctx.id = 0; ctx.now = ctx.time = R.tick * dt; ctx.tick = R.tick;
    if (R.def.tick) call(R.def.tick, LIB.hash2(R.tick, 99991), [R.s, dt, ctx]);
    R.tick++;
    const every = Math.max(1, Math.round(R.tickRate / HOST.snapRate));
    if (R.tick % every === 0) {
      const st = performance.now();
      for (const id in R.cmds) {
        ctx.id = +id;
        const v = call(R.def.view, LIB.hash2(R.tick, +id), [R.s, +id, ctx]);
        const ev = R.events.filter(e => !e.to || e.to === +id).map(e => [e.name, e.data, e.tag]);
        msg({ t: 'snap', st, tk: R.tick, v, me: R.s.players[id], ack: R.ack[id], ev });
      }
      R.events = [];
    }
  }
  function handle(m) {
    if (m.op === 'create' || m.op === 'join') { HOST.pendingName = m.name || 'Player'; HOST.role = m.op; raw({ op: 'open', code: 'RIFT' }); return; }
    if (m.op === 'rooms') { raw({ op: 'rooms', rid: m.rid, rooms: [] }); return; }
    if (m.op === 'leave') { clearInterval(interval); R = HOST.R = null; return; }
    if (m.op !== 'send') return;
    let d; try { d = JSON.parse(m.data); } catch (e) { return; }
    if (d.t === 'code') { build(d.src); addPlayer(1, HOST.pendingName); }
    else if (d.t === 'in') { if (R && R.cmds[1]) for (const c of d.c) R.cmds[1].push(c); }
    else if (d.t === 'ping') msg({ t: 'pong', c: d.c, s: performance.now() });
  }

  // Lets the bot brain drive our own player, so first-person shots show real fights with the real HUD.
  window.__puppetHook = function (s, ctx, dt, L) {
    // trailer tweaks: fixed hero lineups and faster ult charge so the good stuff happens on camera
    if (HOST.lineup && (s.m.ph === 'select' || s.m.ph === 'live')) {
      const all = Object.values(s.bots);
      for (const u of all) { const want = HOST.lineup[u.id]; if (want && u.hero !== want && !u.__lined) { L.Roster.applyHero(s, ctx, u, want); u.__lined = 1; } }
    }
    if (HOST.ultBoost && s.m.ph === 'live') {
      const all = Object.values(s.bots).concat(Object.values(s.players));
      for (const u of all) if (u.alive && u.hero) { const cost = L.Units.hero(u).ult.cost; u.ultC = Math.min(cost, (u.ultC || 0) + HOST.ultBoost * dt); }
    }
    if (HOST.noSwap) for (const u of Object.values(s.bots)) u.next = u.next && u.__lined ? '' : u.next;
    const id = HOST.puppet; if (!id) return;
    const u = s.players[id]; if (!u) return;
    const b = s.brain[id] || (s.brain[id] = L.BotBrain.create(ctx));
    const sid = ctx.id, stime = ctx.time; ctx.id = id;
    try { window.__puppetIn = u.alive ? L.BotBrain.think(s, ctx, u, b, dt) : L.BotBrain.idle(b); } catch (e) { console.error('[puppet]', e && e.stack || e); }
    ctx.id = sid; ctx.time = stime;
  };
})();
