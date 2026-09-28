// Four matches, one per map; lineups respect 1 tank / 2 damage / 1 support per team.
// Team 1 = puppet (id 1) + bots 1000-1002; team 2 = bots 1003-1006.
export const MATCHES = {
  A: { map: 'emberfall', mode: 'control', hero: 'mako', lineup: { 1000: 'monolith', 1001: 'arclight', 1002: 'vita', 1003: 'kodiak', 1004: 'nyx', 1005: 'cinder', 1006: 'solace' } },
  B: { map: 'neon', mode: 'escort', hero: 'kestrel', lineup: { 1000: 'anchor', 1001: 'riptide', 1002: 'sigil', 1003: 'citadel', 1004: 'glaive', 1005: 'rime', 1006: 'hex' } },
  C: { map: 'skyreach', mode: 'control', hero: 'arclight', lineup: { 1000: 'bramble', 1001: 'sprocket', 1002: 'bloom', 1003: 'monolith', 1004: 'kestrel', 1005: 'mako', 1006: 'kite' } },
  D: { map: 'halcyon', mode: 'control', hero: 'nyx', lineup: { 1000: 'kodiak', 1001: 'riptide', 1002: 'solace', 1003: 'anchor', 1004: 'glaive', 1005: 'rime', 1006: 'vita' } },
};
