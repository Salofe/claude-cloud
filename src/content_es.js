'use strict';
// ============ SPANISH GAME CONTENT ============
// The world's text (ores, factions, planets, unlocks, megaprojects, upgrades, enemies, every star system's
// story) is written in English inside the data; when the game runs in Spanish this table is laid over it at boot.
const ES_CONTENT = /*ES_CONTENT*/{ base: {}, systems: {} }/*END_ES_CONTENT*/;
function mergeText(dst, src) {
  for (const k in src) {
    const v = src[k];
    if (v && typeof v === 'object' && !Array.isArray(v) && dst[k] && typeof dst[k] === 'object') mergeText(dst[k], v);
    else if (dst) dst[k] = v;
  }
}
// ores, factions, Sol's worlds, unlocks, projects, upgrades, enemies, ranks — before Sol's snapshot is taken
function applyEsBase() {
  if (!ES) return;
  const B = ES_CONTENT.base || {};
  for (const k in B.items || {}) if (ITEMS[k]) ITEMS[k].n = B.items[k].n;
  for (const k in B.factions || {}) if (FACTIONS[k]) FACTIONS[k].n = B.factions[k].n;
  for (const k in B.locs || {}) if (LOC[k]) mergeText(LOC[k], B.locs[k]);
  (B.unlocks || []).forEach((u, i) => { if (UNLOCKS[i] && u) mergeText(UNLOCKS[i], u); });
  for (const k in B.projects || {}) { const p = PROJECTS.find(x => x.id === k); if (p) mergeText(p, B.projects[k]); }
  for (const k in B.upg || {}) if (UPG[k]) mergeText(UPG[k], B.upg[k]);
  for (const k in B.enemies || {}) if (ENEMIES[k]) ENEMIES[k].n = B.enemies[k].n;
  (B.ranks || []).forEach((r, i) => { if (RANKS[i] && r) RANKS[i][1] = r; });
}
// every star system's names and story
function applyEsSystems() {
  if (!ES) return;
  for (const id in ES_CONTENT.systems || {}) {
    const D = SYSTEMS[id], E = ES_CONTENT.systems[id]; if (!D || !E) continue;
    const { locs, ...rest } = E;
    mergeText(D, rest);
    for (const lid in locs || {}) {
      const { layoutDesc, ...l } = locs[lid];
      if (D.locs && D.locs[lid]) mergeText(D.locs[lid], l); else if (Object.keys(l).length) { D.locs = D.locs || {}; D.locs[lid] = l; }
      if (layoutDesc && D.layout && D.layout[lid]) D.layout[lid].desc = layoutDesc;
    }
  }
  const G = (ES_CONTENT.base || {}).galaxy || {};
  for (const g of GALAXY) if (G[g.id]) g.n = G[g.id];
}
function applyEsLegacy() {
  if (!ES) return;
  for (const k in (ES_CONTENT.base || {}).legacy || {}) if (LEGACY[k]) mergeText(LEGACY[k], ES_CONTENT.base.legacy[k]);
}
