// Trailer camera director. Runs inside the page after the game boots.
window.__DIR = (function () {
  const D = { shot: null, t: 0, hideHud: false, sm: null, plates: false, showMe: true, freeze: false };
  let g = null;
  const V = (x, y, z) => ({ x, y, z });
  const lerp = (a, b, k) => a + (b - a) * k;
  const ease = k => k < 0 ? 0 : k > 1 ? 1 : k * k * (3 - 2 * k);
  const last = {};
  function unit(id) {
    if (!g) return null;
    let u = null;
    if (g.me && (id === g.myId || id === 'me')) u = g.me;
    else u = g.players.find(p => p.id === id) || null;
    // prefer the avatar actually drawn this frame (its root can lag the network state during leaps)
    const av = g.world && g.world.avatars && g.world.avatars.get(u ? u.id : id);
    if (u && av && av.root) u = Object.assign({}, u, { x: av.root.position.x, y: av.root.position.y, z: av.root.position.z });
    if (u && typeof u.x === 'number') last[id] = { x: u.x, y: u.y || 0, z: u.z, yaw: u.yaw, pitch: u.pitch, hero: u.hero };
    if (u && typeof u.x === 'number') return u;
    const S = window.__HOST && window.__HOST.R && window.__HOST.R.s; const su = S && (S.bots[id] || S.players[id]);
    return su ? { x: su.x, y: su.y, z: su.z, yaw: su.yaw, pitch: su.pitch, hero: su.hero } : (last[id] || null);
  }
  D.unit = unit;
  function ray(o, d, max) { const c = g.session && g.session.net && g.session.net.ctx; if (!c) return null; const l = Math.hypot(d.x, d.y, d.z) || 1; return c.raycast([o.x, o.y, o.z], [d.x / l, d.y / l, d.z / l], max); }
  function clear(from, to) { const d = { x: to.x - from.x, y: to.y - from.y, z: to.z - from.z }, L = Math.hypot(d.x, d.y, d.z); const h = ray(from, d, L); return h ? h.t / L : 1; }
  // score orbit angles: unobstructed camera + as many fighters in view as possible
  function bestAngle(c0, r, h, pref) {
    let best = pref || 0, bs = -1e9;
    const others = (g.players || []).concat(g.me ? [g.me] : []).filter(u => u.alive !== false && typeof u.x === 'number' && Math.hypot(u.x - c0.x, u.z - c0.z) < 16);
    for (let i = 0; i < 24; i++) {
      const a = (pref || 0) + i / 24 * Math.PI * 2;
      const p = V(c0.x + Math.sin(a) * r, c0.y + h, c0.z + Math.cos(a) * r);
      let sc = clear(c0, p) * 10;
      // also test the arc the camera will travel through
      for (const u of others) sc += clear(p, V(u.x, chestY(u), u.z)) > 0.98 ? 1 : 0;
      sc -= Math.abs(Math.atan2(Math.sin(a - (pref || 0)), Math.cos(a - (pref || 0)))) * 0.3;
      if (sc > bs) { bs = sc; best = a; }
    }
    return best;
  }
  function headY(u) { const H = g.heroes[u.hero]; return (u.y || 0) + (H ? H.body.h * 0.85 : 1.6); }
  function chestY(u) { const H = g.heroes[u.hero]; return (u.y || 0) + (H ? H.body.h * 0.6 : 1.1); }
  D.install = function (game) {
    g = game;
    const R = g.renderer, orig = R.render.bind(R);
    try { g.ui.hud.banners.setNet = () => {}; g.ui.hud.banners.net.textContent = ''; g.ui.hud.banners.net.style.display = 'none'; } catch (e) {}
    R.render = function () {
      if (D.shot && D.shot.type !== 'fp') {
        const c = R.camera, s = D.shot, dt = 1 / 60;
        const k = s.dur ? Math.min(1, D.t / s.dur) : 0;
        let pos = null, look = null, fov = s.fov || 50, roll = s.roll || 0;
        const tgtU = s.target !== undefined ? unit(s.target) : null;
        if (s.type === 'follow' && tgtU) {
          // over-the-shoulder chase: behind the unit's facing
          const yaw = tgtU.yaw || 0, back = s.dist || 3.2, side = s.side === undefined ? 0.9 : s.side, up = s.height || 0.6;
          const fx = -Math.sin(yaw), fz = -Math.cos(yaw), rx = Math.cos(yaw), rz = -Math.sin(yaw);
          pos = V(tgtU.x - fx * back + rx * side, headY(tgtU) + up, tgtU.z - fz * back + rz * side);
          const pitch = tgtU.pitch || 0, cp = Math.cos(pitch);
          look = V(tgtU.x + fx * 12 * cp + rx * side * 0.3, headY(tgtU) + Math.sin(pitch) * 12 + 0.1, tgtU.z + fz * 12 * cp + rz * side * 0.3);
        } else if (s.type === 'orbit') {
          const c0 = tgtU ? V(tgtU.x, chestY(tgtU), tgtU.z) : V(...(s.center || [0, 1, 0]));
          if (s.auto && D.a0 === undefined) D.a0 = bestAngle(c0, s.r0 || 5, s.h0 || 1, s.a0 || 0);
          const a = (D.a0 !== undefined ? D.a0 : (s.a0 || 0)) + (s.spin === undefined ? 0.4 : s.spin) * D.t, r = lerp(s.r0 || 5, s.r1 || s.r0 || 5, ease(k));
          pos = V(c0.x + Math.sin(a) * r, c0.y + lerp(s.h0 || 1, s.h1 === undefined ? (s.h0 || 1) : s.h1, ease(k)), c0.z + Math.cos(a) * r);
          look = V(c0.x, c0.y + (s.lookUp || 0), c0.z);
        } else if (s.type === 'dolly') {
          const e = s.linear ? k : ease(k);
          pos = V(lerp(s.from[0], s.to[0], e), lerp(s.from[1], s.to[1], e), lerp(s.from[2], s.to[2], e));
          if (tgtU) look = V(tgtU.x, chestY(tgtU), tgtU.z);
          else { const l0 = s.look0 || s.look, l1 = s.look1 || s.look; look = V(lerp(l0[0], l1[0], e), lerp(l0[1], l1[1], e), lerp(l0[2], l1[2], e)); }
          fov = lerp(s.fov0 || fov, s.fov1 || s.fov0 || fov, e);
        } else if (s.type === 'track') {
          // camera at a fixed offset from a point, looking at a (moving) unit
          pos = V(...s.pos);
          look = tgtU ? V(tgtU.x, chestY(tgtU), tgtU.z) : V(...s.look);
        }
        if (pos && look && s.collide !== false && (s.type === 'orbit' || s.type === 'follow')) {
          const piv = s.type === 'follow' && tgtU ? V(tgtU.x, headY(tgtU), tgtU.z) : look;
          const d = { x: pos.x - piv.x, y: pos.y - piv.y, z: pos.z - piv.z }, L = Math.hypot(d.x, d.y, d.z);
          const hh = ray(piv, d, L);
          if (hh && hh.t < L) { const k2 = Math.max(0.15, (hh.t - 0.35) / L); pos = V(piv.x + d.x * k2, piv.y + d.y * k2, piv.z + d.z * k2); }
        }
        if (pos && look) {
          // critically damped smoothing for tracking shots
          const sm = s.smooth === undefined ? 0 : s.smooth;
          if (!D.sm || D.t === 0 || !sm) D.sm = { p: { ...pos }, l: { ...look } };
          else { const a = 1 - Math.exp(-dt / sm); for (const ax of ['x', 'y', 'z']) { D.sm.p[ax] += (pos[ax] - D.sm.p[ax]) * a; D.sm.l[ax] += (look[ax] - D.sm.l[ax]) * a; } }
          let p = D.sm.p, l = D.sm.l;
          const sh = s.shake || 0, T = D.t;
          c.position.set(p.x + sh * Math.sin(T * 13.1) * 0.05, p.y + sh * Math.sin(T * 17.3 + 1) * 0.04, p.z + sh * Math.sin(T * 11.7 + 2) * 0.05);
          c.lookAt(l.x, l.y, l.z);
          if (roll) c.rotateZ(roll);
          if (c.fov !== fov) { c.fov = fov; c.updateProjectionMatrix(); }
        }
        R.showViewmodel = false;
        if (!D.plates) for (const a of g.world.avatars.map ? g.world.avatars.map.values() : []) if (a.plate) a.plate.sprite.visible = false;
      }
      const ui = document.getElementById('ui'); if (ui) ui.style.visibility = D.hideHud ? 'hidden' : 'visible';
      orig();
    };
    // show our own (puppet) player as a normal avatar in third-person shots
    const W = g.world, wu = W.update.bind(W);
    W.update = function (dt, st) {
      if (D.shot && D.shot.type !== 'fp' && D.showMe && st && st.me && st.players) {
        const me = Object.assign({}, st.me);
        st = Object.assign({}, st, { players: st.players.concat([me]), me: null });
      }
      return wu(dt, st);
    };
  };
  D.set = function (shot) { D.shot = shot; D.t = 0; D.sm = null; D.a0 = undefined; D.hideHud = !!(shot && shot.type !== 'fp') || !!(shot && shot.hideHud); };
  D.tick = function (dt) { D.t += dt; };
  return D;
})();
