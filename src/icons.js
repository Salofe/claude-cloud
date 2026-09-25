// ============ ICONS: a hand-drawn vector set that replaces every emoji ============
// Each icon lives on a 24×24 grid in one duotone neon style:
//   f = translucent body fill, s = outline strokes, d = solid details.
// The same paths render as inline SVG in the UI and via Path2D on the canvases.
// The game text still uses the emoji as keys; renderIcons() swaps them out.
const cP = (x, y, r) => `M${x - r} ${y}a${r} ${r} 0 1 0 ${2 * r} 0a${r} ${r} 0 1 0 ${-2 * r} 0z`;
const ellP = (cx, cy, rx, ry, deg) => {
  const a = deg * Math.PI / 180, dx = rx * Math.cos(a), dy = rx * Math.sin(a), f = n => +n.toFixed(2);
  return `M${f(cx - dx)} ${f(cy - dy)}A${rx} ${ry} ${deg} 1 0 ${f(cx + dx)} ${f(cy + dy)}A${rx} ${ry} ${deg} 1 0 ${f(cx - dx)} ${f(cy - dy)}z`;
};
const raysP = (cx, cy, r1, r2, n, off = 0) => {
  let d = '';
  for (let i = 0; i < n; i++) { const a = off + i * Math.PI * 2 / n, c = Math.cos(a), s = Math.sin(a); d += `M${(cx + c * r1).toFixed(2)} ${(cy + s * r1).toFixed(2)}L${(cx + c * r2).toFixed(2)} ${(cy + s * r2).toFixed(2)}`; }
  return d;
};
const starP = (cx, cy, r1, r2, n) => {
  let d = '';
  for (let i = 0; i < n * 2; i++) { const a = -Math.PI / 2 + i * Math.PI / n, r = i % 2 ? r2 : r1; d += (i ? 'L' : 'M') + (cx + Math.cos(a) * r).toFixed(2) + ' ' + (cy + Math.sin(a) * r).toFixed(2); }
  return d + 'z';
};

const ICON = {
  drone: { c: '#6dffb0', f: 'M7.5 11h9v4.5a3.5 3.5 0 0 1-3.5 3.5h-2a3.5 3.5 0 0 1-3.5-3.5z', s: 'M7.5 11h9v4.5a3.5 3.5 0 0 1-3.5 3.5h-2a3.5 3.5 0 0 1-3.5-3.5zM7.5 12.5H4.5V8M16.5 12.5h3V8M1.5 7.5h6M16.5 7.5h6M12 11V8.5M10 21.5l.8-2.5M14 21.5l-.8-2.5', d: 'M9.5 13.8h5v1.8h-5z' + cP(12, 7.6, 1.1) },
  crown: { c: '#ffd24a', f: 'M4.5 17.5 3 7.5l5 4 4-6.5 4 6.5 5-4-1.5 10z', s: 'M4.5 17.5 3 7.5l5 4 4-6.5 4 6.5 5-4-1.5 10zM4.5 20.5h15', d: cP(12, 13.5, 1.3) + cP(3, 6.5, 1.2) + cP(21, 6.5, 1.2) + cP(12, 4, 1.2) },
  bolt: { c: '#ffd24a', f: 'M13.5 2 5 13.5h6.2L10 22l9-12h-6.5z', s: 'M13.5 2 5 13.5h6.2L10 22l9-12h-6.5z' },
  shield: { c: '#3de8ff', f: 'M12 2.5 20 5.5v6c0 5-3.4 8.6-8 10-4.6-1.4-8-5-8-10v-6z', s: 'M12 2.5 20 5.5v6c0 5-3.4 8.6-8 10-4.6-1.4-8-5-8-10v-6zM12 6.5v11.5M8 10.5h8' },
  lock: { c: '#8fa3c7', f: 'M5.5 11h13v10h-13z', s: 'M5.5 11h13v10h-13zM8.5 11V8a3.5 3.5 0 0 1 7 0v3', d: cP(12, 15, 1.4) + 'M11.3 15.5h1.4v3h-1.4z' },
  unlock: { c: '#6dffb0', f: 'M5.5 11h13v10h-13z', s: 'M5.5 11h13v10h-13zM8.5 11V7.5a3.5 3.5 0 0 1 6.8-1.2', d: cP(12, 15, 1.4) + 'M11.3 15.5h1.4v3h-1.4z' },
  pick: { c: '#ffb04a', f: 'M8 4.5c4.5-1.8 9.5-.8 11.5 2.5 1.2 2 1.2 4.3.5 6.5-.8-3.2-3.2-6-6.5-7.3-1.8-.7-3.8-1-5.5-1.7z', s: 'M8 4.5c4.5-1.8 9.5-.8 11.5 2.5 1.2 2 1.2 4.3.5 6.5-.8-3.2-3.2-6-6.5-7.3-1.8-.7-3.8-1-5.5-1.7zM15 9 4 20.5', d: 'M2.8 19.3l1.9 1.9-1 1-1.9-1.9z' },
  skull: { c: '#ff6b7d', f: 'M12 3a7.5 7.5 0 0 0-7.5 7.5c0 2.6 1.3 4.5 3 5.7v3.3h9v-3.3c1.7-1.2 3-3.1 3-5.7A7.5 7.5 0 0 0 12 3z', s: 'M12 3a7.5 7.5 0 0 0-7.5 7.5c0 2.6 1.3 4.5 3 5.7v3.3h9v-3.3c1.7-1.2 3-3.1 3-5.7A7.5 7.5 0 0 0 12 3zM10.5 19.5v-2.2M13.5 19.5v-2.2', d: cP(9, 11, 1.9) + cP(15, 11, 1.9) + 'M12 13.2l1 2h-2z' },
  fuel: { c: '#ffb04a', f: 'M5 8 9 4h8a2 2 0 0 1 2 2v14a1 1 0 0 1-1 1H6a1 1 0 0 1-1-1z', s: 'M5 8 9 4h8a2 2 0 0 1 2 2v14a1 1 0 0 1-1 1H6a1 1 0 0 1-1-1zM11 2.5h5.5', d: 'M12 10c1.8 2.3 2.8 3.8 2.8 5a2.8 2.8 0 0 1-5.6 0c0-1.2 1-2.7 2.8-5z' },
  freighter: { c: '#3de8ff', f: 'M2.5 8h12v8h-12z', s: 'M2.5 8h12v8h-12zM14.5 9.5h3.5l3.5 2.5-3.5 2.5h-3.5M6.5 8v8M10.5 8v8M2.5 10H1M2.5 14H1', d: cP(17.8, 12, 0.9) },
  ship: { c: '#7ab8ff', f: 'M12 2.5c3 2.5 4.5 6 4.5 10l3 4v3l-4.5-1.5h-6L4.5 19.5v-3l3-4c0-4 1.5-7.5 4.5-10z', s: 'M12 2.5c3 2.5 4.5 6 4.5 10l3 4v3l-4.5-1.5h-6L4.5 19.5v-3l3-4c0-4 1.5-7.5 4.5-10zM10.3 20.3 12 23l1.7-2.7', d: cP(12, 9.5, 1.7) },
  swords: { c: '#ff6b7d', s: 'M4 4l10.5 10.5M20 4 9.5 14.5M12.5 16.5l4-4M7.5 12.5l4 4M15.8 15.8l3.7 3.7M8.2 15.8l-3.7 3.7', d: cP(20, 20, 1.3) + cP(4, 20, 1.3) },
  play: { f: 'M7 4.5v15l12-7.5z', s: 'M7 4.5v15l12-7.5z' },
  satellite: { c: '#3de8ff', f: 'M2.5 7 6.5 3l4 4-4 4zM13.5 17l4-4 4 4-4 4z', s: 'M2.5 7 6.5 3l4 4-4 4zM13.5 17l4-4 4 4-4 4zM9 12l3-3 3 3-3 3zM8.5 9l1.5 1.5M14 14l1.5 1.5M10.5 16.5l-3 3', d: cP(6.8, 20.2, 1.2) },
  fire: { c: '#ff8a4a', f: 'M12 2.5c1 3.5 5.5 5.5 5.5 11a5.5 5.5 0 0 1-11 0c0-2.5 1-4 2.5-5.5 0 2 1 3 2 3.5-.5-3.5.5-6.5 1-9z', s: 'M12 2.5c1 3.5 5.5 5.5 5.5 11a5.5 5.5 0 0 1-11 0c0-2.5 1-4 2.5-5.5 0 2 1 3 2 3.5-.5-3.5.5-6.5 1-9z', d: 'M12 14c1 1.3 2 2.2 2 3.5a2 2 0 0 1-4 0c0-1.2.8-2.2 2-3.5z' },
  crate: { c: '#ffc857', f: 'M12 2.5l8.5 4.5v10L12 21.5 3.5 17V7z', s: 'M12 2.5l8.5 4.5v10L12 21.5 3.5 17V7zM3.5 7 12 11.5 20.5 7M12 11.5v10M7.8 4.8l8.4 4.5' },
  dove: { c: '#e8f1ff', f: 'M3 13.5c3-.5 5.5-2.5 7-5.5 1-2 3-3.5 5-3.5 1.5 0 2.5.8 3.5 2l2.5.5-2.5 1.5c0 5-4 9-9.5 9-2.5 0-4.5-1-6-2.5l3-1c-1.5-.2-2.5-.5-3-1z', s: 'M3 13.5c3-.5 5.5-2.5 7-5.5 1-2 3-3.5 5-3.5 1.5 0 2.5.8 3.5 2l2.5.5-2.5 1.5c0 5-4 9-9.5 9-2.5 0-4.5-1-6-2.5l3-1c-1.5-.2-2.5-.5-3-1zM8.5 14c2.5 0 4.5-1.5 5.5-4.5', d: cP(16.3, 6.8, 0.8) },
  blast: { c: '#ff8a4a', f: 'M12 2l2 5.5 5.5-2.5-2.5 5.5L22 12l-5 2 2.5 5.5-5.5-2.5L12 22l-2-5-5.5 2.5L7 14l-5-2 5-2-2.5-5.5L10 7z', s: 'M12 2l2 5.5 5.5-2.5-2.5 5.5L22 12l-5 2 2.5 5.5-5.5-2.5L12 22l-2-5-5.5 2.5L7 14l-5-2 5-2-2.5-5.5L10 7z', d: cP(12, 12, 2.6) },
  crane: { c: '#ffc857', f: 'M4.5 21V7h3v14z', s: 'M4.5 21V7h3v14zM4.5 4h16M6 7l3-3M17.5 4v6M2.5 21h8M4.5 11l3 3M4.5 16l3 3M17.5 10v2a1.5 1.5 0 1 1-1.5 1.5', d: 'M19.5 3h2.5v3h-2.5z' },
  comet: { c: '#7fdfff', f: cP(16, 8, 3.4), s: cP(16, 8, 3.4) + 'M13.3 10.8 3.5 20.5M12.2 7.8 5 14.5M16.2 11.4 10 17.5', d: cP(16, 8, 1.3) },
  capitol: { c: '#d9b3ff', f: 'M3 9 12 3.5 21 9z', s: 'M3 9 12 3.5 21 9zM5.5 11.5v6M9.8 11.5v6M14.2 11.5v6M18.5 11.5v6M3 20.5h18M4 9.5h16' },
  bank: { c: '#ffd24a', f: 'M3.5 4.5h17v14h-17z', s: 'M3.5 4.5h17v14h-17z' + cP(12, 11.5, 4.2) + 'M12 7.3v8.4M7.8 11.5h8.4M6 18.5v2.5M18 18.5v2.5', d: cP(12, 11.5, 1.4) },
  trophy: { c: '#ffd24a', f: 'M7 3.5h10v5a5 5 0 0 1-10 0z', s: 'M7 3.5h10v5a5 5 0 0 1-10 0zM7 5.5H4.5a3 3 0 0 0 3 4.5M17 5.5h2.5a3 3 0 0 1-3 4.5M12 13.5V17M9.5 17h5v3.5h-5zM8 20.5h8', d: starP(12, 8, 2.3, 1, 5) },
  speaker: { f: 'M3.5 9h4l5-4.5v15l-5-4.5h-4z', s: 'M3.5 9h4l5-4.5v15l-5-4.5h-4zM15.5 9a4 4 0 0 1 0 6M18 6.5a7.5 7.5 0 0 1 0 11' },
  mute: { f: 'M3.5 9h4l5-4.5v15l-5-4.5h-4z', s: 'M3.5 9h4l5-4.5v15l-5-4.5h-4zM16 9.5l5 5M21 9.5l-5 5' },
  siren: { c: '#ff4d6d', f: 'M6.5 17v-5a5.5 5.5 0 0 1 11 0v5z', s: 'M6.5 17v-5a5.5 5.5 0 0 1 11 0v5zM4.5 17h15v3.5h-15zM12 2v2.2M4 5.5l1.6 1.6M20 5.5l-1.6 1.6M1.5 12.5h2M20.5 12.5h2', d: 'M10.5 11a1.5 1.5 0 0 1 3 0v6h-3z' },
  wrench: { c: '#9fc7ff', f: 'M14.5 3a5 5 0 0 0-4.6 6.9L3.5 16.3a2.2 2.2 0 0 0 3.1 3.1L13 13a5 5 0 0 0 6.6-6.2l-3 3-2.8-.6-.6-2.8 3-3A5 5 0 0 0 14.5 3z', s: 'M14.5 3a5 5 0 0 0-4.6 6.9L3.5 16.3a2.2 2.2 0 0 0 3.1 3.1L13 13a5 5 0 0 0 6.6-6.2l-3 3-2.8-.6-.6-2.8 3-3A5 5 0 0 0 14.5 3z' },
  contract: { c: '#ffc857', f: 'M6 3h9l4 4v14H6z', s: 'M6 3h9l4 4v14H6zM15 3v4h4M9 11h7M9 14h7M9 17h3.5', d: starP(16, 17.5, 1.8, .8, 5) },
  map: { c: '#6dffb0', f: 'M3 6l6-2.5 6 2.5 6-2.5v14L15 20l-6-2.5L3 20z', s: 'M3 6l6-2.5 6 2.5 6-2.5v14L15 20l-6-2.5L3 20zM9 3.5v14M15 6v14', d: cP(12, 10.5, 1.3) },
  strike: { c: '#ff9f43', f: 'M4.5 3.5h15v9h-15z', s: 'M4.5 3.5h15v9h-15zM12 12.5v9M9 21.5h6', d: 'M11.1 5.3h1.8l-.3 4h-1.2z' + cP(12, 10.7, 0.9) },
  bulb: { c: '#ffd24a', f: 'M12 2.5a6.5 6.5 0 0 0-3.8 11.8c.8.6 1.3 1.5 1.3 2.5v.2h5v-.2c0-1 .5-1.9 1.3-2.5A6.5 6.5 0 0 0 12 2.5z', s: 'M12 2.5a6.5 6.5 0 0 0-3.8 11.8c.8.6 1.3 1.5 1.3 2.5v.2h5v-.2c0-1 .5-1.9 1.3-2.5A6.5 6.5 0 0 0 12 2.5zM9.5 19.5h5M10.5 22h3M12 17V12l-1.5-1.5M12 12l1.5-1.5' },
  galaxy: { c: '#d9b3ff', f: cP(12, 12, 6.5), s: 'M12 12c3-3 8.5-1.5 8.5 3M12 12c-3 3-8.5 1.5-8.5-3M12 12c-3-3-1.5-8.5 3-8.5M12 12c3 3 1.5 8.5-3 8.5', d: cP(12, 12, 2) + cP(19.5, 5, .8) + cP(4, 19.5, .7) },
  news: { c: '#cfe0ff', f: 'M3.5 4.5h13v15a1.5 1.5 0 0 1-1.5 1.5H5a1.5 1.5 0 0 1-1.5-1.5z', s: 'M3.5 4.5h13v15a1.5 1.5 0 0 1-1.5 1.5H5a1.5 1.5 0 0 1-1.5-1.5zM16.5 9h4v10a2 2 0 0 1-2 2H15M6.5 12.5h7M6.5 15.5h7M6.5 18.5h4.5', d: 'M6.5 7h7v3h-7z' },
  menu: { s: 'M4 6.5h16M4 12h16M4 17.5h16' },
  warning: { c: '#ffc857', f: 'M12 3 22 20.5H2z', s: 'M12 3 22 20.5H2z', d: 'M11.1 9h1.8l-.3 6h-1.2z' + cP(12, 17.4, 1) },
  gem: { c: '#7fdfff', f: 'M6.5 4h11L22 9.5 12 21 2 9.5z', s: 'M6.5 4h11L22 9.5 12 21 2 9.5zM2 9.5h20M9 4 7.5 9.5 12 21l4.5-11.5L15 4' },
  flag: { c: '#ff6b7d', f: 'M5 4c3-1.5 5 1 8 0s5-1.5 7-.5v9c-2-1-4-.5-7 .5s-5-1.5-8 0z', s: 'M5 21.5V3M5 4c3-1.5 5 1 8 0s5-1.5 7-.5v9c-2-1-4-.5-7 .5s-5-1.5-8 0z', d: cP(12.5, 8.2, 1.6) },
  sun: { c: '#ffd24a', f: cP(12, 12, 4.6), s: cP(12, 12, 4.6) + raysP(12, 12, 7, 10, 8) },
  factory: { c: '#9fc7ff', f: 'M3 20.5V10l5 3v-3l5 3v-3l5 3V4h3v16.5z', s: 'M3 20.5V10l5 3v-3l5 3v-3l5 3V4h3v16.5zM2 20.5h20', d: 'M6 16h2v2H6zM10.5 16h2v2h-2zM15 16h2v2h-2z' },
  briefcase: { c: '#e0a870', f: 'M3 8h18v12H3z', s: 'M3 8h18v12H3zM9 8V5.5h6V8M3 13h18', d: 'M10.5 12h3v2.5h-3z' },
  medal: { c: '#ffd24a', f: cP(12, 15.5, 5), s: 'M8 2.5l2.5 8M16 2.5l-2.5 8' + cP(12, 15.5, 5), d: starP(12, 15.5, 2.8, 1.2, 5) },
  alliance: { c: '#6dffb0', f: cP(9, 12, 5.5) + cP(15, 12, 5.5), s: cP(9, 12, 5.5) + cP(15, 12, 5.5), d: cP(12, 12, 1.4) },
  dish: { c: '#3de8ff', f: 'M4 9a8 8 0 0 0 11 11z', s: 'M4 9a8 8 0 0 0 11 11zM9.5 14.5 15 9M14.5 6a4 4 0 0 1 3.5 3.5M15 2.5a7.5 7.5 0 0 1 6.5 6.5M6.5 18.5l-2 3h6', d: cP(15, 9, 1.3) },
  book: { c: '#cfe0ff', f: 'M3 5c3-1 6-1 9 1v14c-3-2-6-2-9-1zM21 5c-3-1-6-1-9 1v14c3-2 6-2 9-1z', s: 'M3 5c3-1 6-1 9 1v14c-3-2-6-2-9-1zM21 5c-3-1-6-1-9 1v14c3-2 6-2 9-1z' },
  virus: { c: '#7dff8a', f: cP(12, 12, 5), s: cP(12, 12, 5) + raysP(12, 12, 5, 8.5, 8, Math.PI / 8), d: [0, 1, 2, 3, 4, 5, 6, 7].map(i => { const a = Math.PI / 8 + i * Math.PI / 4; return cP(+(12 + Math.cos(a) * 9.3).toFixed(2), +(12 + Math.sin(a) * 9.3).toFixed(2), 1.2); }).join('') + cP(10.5, 11, 1.2) + cP(13.6, 13.4, 1) },
  wheat: { c: '#ffc857', f: 'M12 18c-3 0-4.5-2-4.5-4.5 3 0 4.5 2 4.5 4.5zM12 18c3 0 4.5-2 4.5-4.5-3 0-4.5 2-4.5 4.5zM12 13c-3 0-4.5-2-4.5-4.5 3 0 4.5 2 4.5 4.5zM12 13c3 0 4.5-2 4.5-4.5-3 0-4.5 2-4.5 4.5zM12 8.5c-1.5-1.5-1.5-3.5 0-6 1.5 2.5 1.5 4.5 0 6z', s: 'M12 22V8.5M12 18c-3 0-4.5-2-4.5-4.5 3 0 4.5 2 4.5 4.5zM12 18c3 0 4.5-2 4.5-4.5-3 0-4.5 2-4.5 4.5zM12 13c-3 0-4.5-2-4.5-4.5 3 0 4.5 2 4.5 4.5zM12 13c3 0 4.5-2 4.5-4.5-3 0-4.5 2-4.5 4.5zM12 8.5c-1.5-1.5-1.5-3.5 0-6 1.5 2.5 1.5 4.5 0 6z' },
  habitat: { c: '#9fc7ff', f: 'M3 19a9 9 0 0 1 18 0z', s: 'M3 19a9 9 0 0 1 18 0zM1.5 19h21M10 19v-4h4v4M12 10V6.5M6.5 14.5h1.5M16 14.5h1.5', d: cP(12, 5.8, 1.2) },
  coin: { c: '#ffd24a', f: cP(12, 12, 8.5), s: cP(12, 12, 8.5) + 'M12 6v12M14.8 9.2c-.5-1-1.6-1.6-2.8-1.6-1.6 0-2.8.8-2.8 2.1 0 3 5.8 1.6 5.8 4.6 0 1.4-1.3 2.2-3 2.2-1.3 0-2.5-.6-3-1.6' },
  down: { c: '#ff6b7d', f: 'M6.5 7.5l4 4.5 3-3 5.5 6.5V20.5H6.5z', s: 'M3.5 3.5v17h17M6.5 7.5l4 4.5 3-3 5.5 6.5M15.5 15.5H19V12' },
  up: { c: '#6dffb0', f: 'M6.5 16l4-4.5 3 3 5.5-6.5v12.5H6.5z', s: 'M3.5 3.5v17h17M6.5 16l4-4.5 3 3 5.5-6.5M15.5 8H19v3.5' },
  atom: { c: '#7fdfff', s: ellP(12, 12, 9.5, 3.6, 0) + ellP(12, 12, 9.5, 3.6, 60) + ellP(12, 12, 9.5, 3.6, -60), d: cP(12, 12, 2) },
  party: { c: '#ff7ad9', f: 'M3 21l5-14 9 9z', s: 'M3 21l5-14 9 9zM13 3.5c.5 1.5 0 3-1.5 3.5M20.5 11c-1.5-.5-3 0-3.5 1.5M16.5 3l.4 1.6M20.5 7.1l1.6-.4', d: cP(18.3, 4.3, 1) + cP(15, 8.4, .9) + cP(20.2, 15, 1) },
  ballot: { c: '#d9b3ff', f: 'M3.5 12h17v8.5h-17z', s: 'M3.5 12h17v8.5h-17zM7.5 12h9M8.5 12V3.5h7V12M10 7.5l1.5 1.5 2.5-3' },
  sprout: { c: '#7dff8a', f: 'M12 12.5c0-4-2.5-6.5-7.5-6.5 0 4 2.5 6.5 7.5 6.5zM12 15c0-3.5 2.5-6 6.5-6 0 3.5-2.5 6-6.5 6z', s: 'M12 21.5V12M12 12.5c0-4-2.5-6.5-7.5-6.5 0 4 2.5 6.5 7.5 6.5zM12 15c0-3.5 2.5-6 6.5-6 0 3.5-2.5 6-6.5 6zM7 21.5h10' },
  fireworks: { c: '#ff7ad9', s: raysP(12, 10, 3.2, 7.8, 8) + 'M12 22v-4', d: cP(12, 10, 1.6) + [0, 1, 2, 3, 4, 5, 6, 7].map(i => { const a = i * Math.PI / 4 + Math.PI / 8; return cP(+(12 + Math.cos(a) * 8.6).toFixed(2), +(10 + Math.sin(a) * 8.6).toFixed(2), .7); }).join('') },
  spy: { c: '#8fa3c7', f: 'M7 10.5 8.5 4.5h7l1.5 6z' + cP(8, 16, 2.8) + cP(16, 16, 2.8), s: 'M7 10.5 8.5 4.5h7l1.5 6zM3 11h18M10.8 16h2.4' + cP(8, 16, 2.8) + cP(16, 16, 2.8) },
  sos: { c: '#ff6b7d', f: cP(12, 12, 9) + cP(12, 12, 4.5), s: cP(12, 12, 9) + cP(12, 12, 4.5), d: 'M5 3.6 3.6 5l4.6 4.6 1.4-1.4zM19 20.4l1.4-1.4-4.6-4.6-1.4 1.4zM20.4 5 19 3.6l-4.6 4.6 1.4 1.4zM3.6 19 5 20.4l4.6-4.6-1.4-1.4z' },
  astronaut: { c: '#e8f1ff', f: cP(12, 10, 6.8), s: cP(12, 10, 6.8) + 'M5 22c0-3.3 3-5.3 7-5.3s7 2 7 5.3', d: 'M8.5 7.5h7a1.5 1.5 0 0 1 1.5 1.5v1a3 3 0 0 1-3 3h-4a3 3 0 0 1-3-3V9a1.5 1.5 0 0 1 1.5-1.5z' },
  check: { c: '#6dffb0', s: 'M4.5 12.5l5 5L20 6.5' },
  done: { c: '#6dffb0', f: 'M4 4h16v16H4z', s: 'M4 4h16v16H4zM7.5 12.5l3 3 6-7' },
  fail: { c: '#ff6b7d', f: cP(12, 12, 9), s: cP(12, 12, 9) + 'M8.5 8.5l7 7M15.5 8.5l-7 7' },
  mars: { c: '#ff7a4a', f: cP(12, 12, 8.5), s: cP(12, 12, 8.5) + 'M4.5 9c3 1.2 8 .5 13-2.3M3.8 14c4.5 1.3 10 1 16-1.2', d: cP(15, 16.8, 1.3) + cP(8, 11.8, 1) },
  saturn: { c: '#ffc857', f: cP(12, 12, 5.5), s: cP(12, 12, 5.5) + ellP(12, 12, 10.5, 3.2, -20) },
  magnet: { c: '#ff6b7d', f: 'M5 3.5h4.5V12a2.5 2.5 0 0 0 5 0V3.5H19V12a7 7 0 0 1-14 0z', s: 'M5 3.5h4.5V12a2.5 2.5 0 0 0 5 0V3.5H19V12a7 7 0 0 1-14 0zM5 7.5h4.5M14.5 7.5H19', d: 'M5 3.5h4.5v4H5zM14.5 3.5H19v4h-4.5z' },
  elevator: { c: '#9fc7ff', f: cP(12, 4, 2.2), s: cP(12, 4, 2.2) + 'M12 6.2V22M7.5 22h9M10 22l2-4.5 2 4.5M3 7.5c5 2.2 13 2.2 18 0', d: 'M10.4 11h3.2v3h-3.2z' },
  globe: { c: '#6dffb0', f: cP(12, 12, 9), s: cP(12, 12, 9) + 'M3.5 9h5l2 3-2 3 1 5.5M14 3.3l-1 3.7 3 2.5h4.8M15.8 20.3l.5-4 3.2-1.6' },
  portal: { c: '#d9b3ff', f: 'M12 2 20.7 7v10L12 22l-8.7-5V7z', s: 'M12 2 20.7 7v10L12 22l-8.7-5V7z' + cP(12, 12, 4.6), d: cP(12, 12, 1.8) },
  ring: { c: '#7fdfff', f: cP(12, 12, 9) + cP(12, 12, 5.5), s: cP(12, 12, 9) + cP(12, 12, 5.5) + 'M12 3v2.5M12 18.5V21M3 12h2.5M18.5 12H21', d: cP(12, 12, 2) },
  hull: { c: '#9fc7ff', f: 'M12 2l5 7v7l3 4-8-2-8 2 3-4V9z', s: 'M12 2l5 7v7l3 4-8-2-8 2 3-4V9zM12 6.5V18M7 12h10' },
  laser: { c: '#ff6bd6', f: 'M12 2l2.2 7.8L22 12l-7.8 2.2L12 22l-2.2-7.8L2 12l7.8-2.2z', s: 'M12 2l2.2 7.8L22 12l-7.8 2.2L12 22l-2.2-7.8L2 12l7.8-2.2z', d: cP(12, 12, 1.8) },
  hold: { c: '#ffc857', f: 'M3.5 6h17v12h-17z', s: 'M3.5 6h17v12h-17zM3.5 12h17M9.2 6v12M14.8 6v12' },
  flask: { c: '#7dff8a', f: 'M10.5 3v6L5 19a1.5 1.5 0 0 0 1.3 2.2h11.4A1.5 1.5 0 0 0 19 19l-5.5-10V3z', s: 'M10.5 3v6L5 19a1.5 1.5 0 0 0 1.3 2.2h11.4A1.5 1.5 0 0 0 19 19l-5.5-10V3zM9 3h6M7.2 15h9.6', d: cP(10.5, 18, 1) + cP(14, 17.6, 1.2) },
  engine: { c: '#ff8a4a', f: 'M8 3h8v6l3 7H5l3-7z', s: 'M8 3h8v6l3 7H5l3-7zM8 9h8', d: 'M8 17.5c1.2 2 2.5 3.5 4 5 1.5-1.5 2.8-3 4-5z' },
  tank: { c: '#ffb04a', f: 'M6 5a6 2.5 0 0 1 12 0v14a6 2.5 0 0 1-12 0z', s: 'M6 5a6 2.5 0 0 1 12 0v14a6 2.5 0 0 1-12 0zM6 5a6 2.5 0 0 0 12 0M6 12a6 2.5 0 0 0 12 0' },
  guns: { c: '#ff6b7d', f: 'M6 3h3v10H6zM15 3h3v10h-3zM4 13h16v4l-3 4H7l-3-4z', s: 'M6 3h3v10H6zM15 3h3v10h-3zM4 13h16v4l-3 4H7l-3-4z', d: cP(12, 17, 1.5) },
  radar: { c: '#6dffb0', f: 'M12 12V3a9 9 0 0 1 6.4 2.6z', s: cP(12, 12, 9) + cP(12, 12, 5) + 'M12 12l6.4-6.4', d: cP(15.5, 9.2, 1.1) + cP(8, 15, .9) },
  target: { s: cP(12, 12, 7) + 'M12 2v5M12 17v5M2 12h5M17 12h5', d: cP(12, 12, 1.6) },
  system: { s: cP(12, 12, 5.5) + cP(12, 12, 9.5), d: cP(12, 12, 2.4) + cP(17.5, 12, 1.4) + cP(5.3, 5.3, 1.3) },
  arrowDown: { s: 'M12 3.5v16M6 13.5l6 6 6-6' },
  arrowUp: { s: 'M12 20.5v-16M6 10.5l6-6 6 6' },
  fleet: { c: '#3de8ff', f: 'M12 2.5l3.5 7-3.5-1.8-3.5 1.8zM6 11.5l3.5 7-3.5-1.8-3.5 1.8zM18 11.5l3.5 7-3.5-1.8-3.5 1.8z', s: 'M12 2.5l3.5 7-3.5-1.8-3.5 1.8zM6 11.5l3.5 7-3.5-1.8-3.5 1.8zM18 11.5l3.5 7-3.5-1.8-3.5 1.8z' },
};

// emoji / symbol → icon. Game text keeps these as keys.
const GLYPH = {
  '🤖': 'drone', '👑': 'crown', '⚡': 'bolt', '🛡': 'shield', '🔒': 'lock', '🔓': 'unlock', '⛏': 'pick', '☠': 'skull',
  '⛽': 'fuel', '🚚': 'freighter', '🚀': 'ship', '⚔': 'swords', '▶': 'play', '🛰': 'satellite', '🔥': 'fire', '📦': 'crate',
  '🕊': 'dove', '💥': 'blast', '🏗': 'crane', '☄': 'comet', '🏛': 'capitol', '🏦': 'bank', '🏆': 'trophy', '🔊': 'speaker',
  '🔇': 'mute', '🚨': 'siren', '🔧': 'wrench', '📜': 'contract', '🗺': 'map', '✊': 'strike', '💡': 'bulb', '🌌': 'galaxy',
  '📰': 'news', '☰': 'menu', '⚠': 'warning', '💎': 'gem', '🏴': 'flag', '☀': 'sun', '🏭': 'factory', '💼': 'briefcase',
  '🎖': 'medal', '🤝': 'alliance', '📡': 'dish', '📖': 'book', '☣': 'virus', '🌾': 'wheat', '🛖': 'habitat', '🤑': 'coin',
  '📉': 'down', '📈': 'up', '⚛': 'atom', '🎉': 'party', '🗳': 'ballot', '🌱': 'sprout', '🎆': 'fireworks', '🕵': 'spy',
  '🆘': 'sos', '🧑‍🚀': 'astronaut', '✅': 'done', '✔': 'check', '❌': 'fail', '🔴': 'mars', '🪐': 'saturn', '🧲': 'magnet',
  '🗼': 'elevator', '🌍': 'globe', '🌀': 'portal', '💫': 'ring', '⬢': 'hull', '✦': 'laser', '⌬': 'magnet', '▣': 'hold',
  '⚗': 'flask', '⇮': 'engine', '◍': 'tank', '✚': 'guns', '◈': 'radar', '◎': 'target', '✺': 'system', '⬇': 'arrowDown',
  '⬆': 'arrowUp', '⛴': 'fleet',
};
const GLYPH_RE = new RegExp('(' + Object.keys(GLYPH).sort((a, b) => b.length - a.length).map(k => k.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('|') + ')\\uFE0F?', 'gu');

function ico(name, cls = '') {
  const I = ICON[name]; if (!I) return '';
  return `<svg class="ico ${cls}" viewBox="0 0 24 24" aria-hidden="true"${I.c ? ` style="color:${I.c}"` : ''}>`
    + (I.f ? `<path class="f" d="${I.f}"/>` : '') + (I.s ? `<path class="s" d="${I.s}"/>` : '') + (I.d ? `<path class="d" d="${I.d}"/>` : '') + '</svg>';
}
const glyphIcon = g => GLYPH[g.replace(/️/g, '')];

// swap emoji inside any text node for inline icons
function iconizeNode(root) {
  if (root.nodeType === 3) { iconizeText(root); return; }
  if (root.nodeType !== 1 || root.namespaceURI === 'http://www.w3.org/2000/svg') return;
  const w = document.createTreeWalker(root, NodeFilter.SHOW_TEXT), list = [];
  for (let n = w.nextNode(); n; n = w.nextNode()) { GLYPH_RE.lastIndex = 0; if (GLYPH_RE.test(n.data)) list.push(n); }
  for (const n of list) iconizeText(n);
}
function iconizeText(n) {
  GLYPH_RE.lastIndex = 0;
  if (!n.parentNode || !GLYPH_RE.test(n.data)) return;
  const tpl = document.createElement('template');
  tpl.innerHTML = n.data.replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c])).replace(GLYPH_RE, m => ico(glyphIcon(m)) || m);
  n.parentNode.replaceChild(tpl.content, n);
}
function startIconizer() {
  iconizeNode(document.body);
  new MutationObserver(ms => { for (const m of ms) { if (m.type === 'characterData') iconizeText(m.target); else for (const n of m.addedNodes) iconizeNode(n); } })
    .observe(document.body, { childList: true, subtree: true, characterData: true });
}

// ---------- canvas ----------
const ICON_PATHS = {};
function iconPaths(name) {
  if (!ICON_PATHS[name]) { const I = ICON[name]; ICON_PATHS[name] = { f: I.f && new Path2D(I.f), s: I.s && new Path2D(I.s), d: I.d && new Path2D(I.d) }; }
  return ICON_PATHS[name];
}
function drawIcon(ctx, name, x, y, size, col) {
  const I = ICON[name]; if (!I) return;
  const P = iconPaths(name), c = col || I.c || '#cfe0ff', k = size / 24;
  ctx.save(); ctx.translate(x - size / 2, y - size / 2); ctx.scale(k, k);
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  // dark halo keeps icons readable over planets and nebula
  if (P.s) { ctx.strokeStyle = 'rgba(4,8,20,0.85)'; ctx.lineWidth = 4.6; ctx.stroke(P.s); }
  if (P.f) { ctx.fillStyle = c; ctx.globalAlpha = 0.28; ctx.fill(P.f, 'evenodd'); ctx.globalAlpha = 1; }
  ctx.shadowColor = c; ctx.shadowBlur = 6 / k;
  if (P.s) { ctx.strokeStyle = c; ctx.lineWidth = 1.8; ctx.stroke(P.s); }
  if (P.d) { ctx.fillStyle = c; ctx.fill(P.d, 'evenodd'); }
  ctx.restore();
}
// draw a row of emoji keys (e.g. map markers) as icons, centered on x
function drawIconRow(ctx, glyphs, x, y, size, gap = 3) {
  const names = []; for (const m of glyphs.matchAll(GLYPH_RE)) { const n = glyphIcon(m[0]); if (n) names.push(n); }
  const w = names.length * size + (names.length - 1) * gap;
  names.forEach((n, i) => drawIcon(ctx, n, x - w / 2 + size / 2 + i * (size + gap), y, size));
}
