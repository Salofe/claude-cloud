'use strict';
// ============ GAME DATA ============
const TAU = Math.PI * 2;
const rand = (a, b) => a + Math.random() * (b - a);
const randi = (a, b) => Math.floor(rand(a, b + 1));
const pick = arr => arr[Math.floor(Math.random() * arr.length)];
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const lerp = (a, b, t) => a + (b - a) * t;
const SUFFIX = ['', 'K', 'M', 'B', 'T', 'Qa', 'Qi', 'Sx'];
function fmt(n) {
  if (Math.abs(n) < 10 && n % 1) return (Math.floor(n * 10) / 10).toString();
  n = Math.floor(n);
  const a = Math.abs(n);
  if (a < 10000) return n.toLocaleString('en-US');
  const e = Math.min(SUFFIX.length - 1, Math.floor(Math.log10(a) / 3));
  const v = n / Math.pow(1000, e);
  return (Math.abs(v) >= 100 ? v.toFixed(0) : Math.abs(v) >= 10 ? v.toFixed(1) : v.toFixed(2)) + SUFFIX[e];
}

// Ore values climb steeply from zone to zone.
const ITEMS = {
  iron:      { n: 'Iron',           b: 4,    c: '#b06a3c', ore: 1, h: 1.0 },
  ice:       { n: 'Ice',            b: 6,    c: '#8fd8ff', ore: 1, h: 0.7 },
  titanium:  { n: 'Titanium',       b: 30,   c: '#7f8da3', ore: 1, h: 1.4 },
  cobalt:    { n: 'Cobalt',         b: 90,   c: '#3156ff', ore: 1, h: 1.25 },
  nickel:    { n: 'Nickel',         b: 50,   c: '#3fcf5a', ore: 1, h: 1.2 },
  he3:       { n: 'Helium-3',       b: 120,  c: '#ffd84a', ore: 1, h: 1.3 },
  platinum:  { n: 'Platinum',       b: 250,  c: '#f4f4f4', ore: 1, h: 1.7 },
  sunstone:  { n: 'Sunstone',       b: 400,  c: '#ff7a1a', ore: 1, h: 1.6 },
  iridium:   { n: 'Iridium',        b: 1200, c: '#a050ff', ore: 1, h: 2.2 },
  ringpearl: { n: 'Ring Pearl',     b: 2500, c: '#2ee6c4', ore: 1, h: 2.0 },
  exotic:    { n: 'Exotic Crystal', b: 9000, c: '#ff3fc8', ore: 1, h: 2.8 },
  voidshard: { n: 'Void Shard',     b: 16000, c: '#ff2b3a', ore: 1, h: 3.0 },
  food:      { n: 'Food',           b: 60,  c: '#96e072' },
  meds:      { n: 'Medicine',       b: 180, c: '#ff6b7d' },
  machinery: { n: 'Machinery',      b: 150, c: '#e0b35e' },
  tech:      { n: 'Electronics',    b: 250, c: '#69b8ff' },
  arms:      { n: 'Weapons',        b: 320, c: '#ff934a' },
  luxury:    { n: 'Luxuries',       b: 480, c: '#f7e3a1' },
};
const ITEM_KEYS = Object.keys(ITEMS);
const ORES = ITEM_KEYS.filter(k => ITEMS[k].ore);
const GOODS = ITEM_KEYS.filter(k => !ITEMS[k].ore);

const FACTIONS = {
  tierra:   { n: 'Earth Union',     c: '#5fb4ff', locs: ['tierra', 'luna', 'venus'] },
  marte:    { n: 'Mars Republic',   c: '#ff7a50', locs: ['marte'] },
  cinturon: { n: 'Belt Coalition',  c: '#ffc857', locs: ['ceres'] },
  exterior: { n: 'Outer League',    c: '#6dffb0', locs: ['europa', 'titan'] },
  piratas:  { n: 'Black Syndicate', c: '#ff4d6d', locs: ['pluton'] },
};

// field.z = zone tier: drives rock toughness, enemy strength, loot and outposts
// Field depots buy ore cheap (quick cash); planets with cities pay much more.
const DEPOT = { iron: 0.6, ice: 0.6, titanium: 0.6, cobalt: 0.6, nickel: 0.6, he3: 0.6, platinum: 0.6, sunstone: 0.6, iridium: 0.6, ringpearl: 0.6, exotic: 0.6, voidshard: 0.6 };
const LOCS = [
  { id: 'mercurio', n: 'Mercury', r: 62, period: 70, a0: 1.2, size: 5, tex: 'rock', col: ['#d8c3a5', '#6b5a48'], danger: 0.06, tier: 3,
    station: 'Caloris Depot', depot: 1, fuel: 5, repair: 3, market: { ...DEPOT },
    field: { n: 'Caloris Plains', z: 1, ores: { iron: 2, titanium: 2, platinum: 1.6, sunstone: 1.4 }, count: 26, hazard: 'heat' },
    desc: 'Scorched rock next to the Sun. Platinum and fiery Sunstone — but the heat burns unshielded hulls.' },
  { id: 'venus', n: 'Venus', r: 98, period: 120, a0: 2.7, size: 8, tex: 'venus', col: ['#f3d9a0', '#a8793b'], faction: 'tierra', danger: 0.04, tier: 5,
    station: 'Aphrodite Cloud City', fuel: 6, repair: 3,
    market: { iron: 1.8, ice: 3.2, titanium: 2.0, platinum: 2.4, sunstone: 2.4, cobalt: 2.0, ringpearl: 2.8, food: 2.2, machinery: 2.4, tech: 0.5, meds: 0.45, luxury: 0.45 },
    desc: 'Floating cities above acid clouds. They make luxuries and medicine, and crave water.' },
  { id: 'tierra', n: 'Earth', r: 142, period: 190, a0: 0.2, size: 9, tex: 'earth', col: ['#5fb4ff', '#15407e'], faction: 'tierra', danger: 0.03, tier: 2,
    station: 'Gateway Port', fuel: 5, repair: 3,
    market: { iron: 2.4, nickel: 2.3, ice: 1.6, titanium: 2.5, platinum: 2.6, he3: 2.8, iridium: 2.4, exotic: 2.4, cobalt: 2.3, sunstone: 2.6, ringpearl: 2.4, voidshard: 2.4, food: 0.45, meds: 0.5, machinery: 0.8, tech: 0.45, arms: 1.6, luxury: 1.2 },
    desc: 'The cradle of humanity. Pays 50–70% more for every metal you bring.' },
  { id: 'luna', n: 'Moon', parent: 'tierra', r: 17, period: 27, a0: 0, size: 4, tex: 'moon', col: ['#e3e3e3', '#6a6a72'], faction: 'tierra', danger: 0.02, tier: 0,
    station: 'Tranquility Base', fuel: 4, repair: 2.5,
    market: { iron: 0.7, nickel: 0.7, ice: 0.75, titanium: 0.7, he3: 0.7, food: 1.8, meds: 1.6, machinery: 1.8, tech: 1.6 },
    field: { n: 'Lunar Maria', z: 0, ores: { iron: 5, ice: 3, titanium: 1.2, he3: 0.3 }, count: 24 },
    desc: 'Your home base. A calm mining field with a station at the bottom.' },
  { id: 'marte', n: 'Mars', r: 196, period: 330, a0: 4.1, size: 7, tex: 'mars', col: ['#ff8a5c', '#7a2a14'], faction: 'marte', danger: 0.05, tier: 3,
    station: 'Olympus City', fuel: 5, repair: 3,
    market: { iron: 2.0, nickel: 2.1, ice: 3.8, titanium: 2.2, platinum: 2.2, he3: 2.4, iridium: 2.2, cobalt: 2.4, sunstone: 2.2, ringpearl: 2.2, voidshard: 2.0, food: 2.6, meds: 2.0, machinery: 0.45, tech: 2.0, arms: 0.4, luxury: 2.2 },
    desc: 'A militarized republic. Pays a fortune for ice — water is life on Mars.' },
  { id: 'ceres', n: 'Ceres', r: 262, period: 560, a0: 5.4, size: 5, tex: 'rock', col: ['#b7b0a4', '#4c463e'], faction: 'cinturon', danger: 0.22, tier: 4,
    station: 'Ceres Station', fuel: 5, repair: 3.5,
    market: { iron: 0.7, nickel: 0.75, ice: 1.4, titanium: 0.75, platinum: 0.8, he3: 0.9, iridium: 0.8, cobalt: 0.75, sunstone: 0.8, food: 2.6, meds: 2.2, machinery: 2.2, tech: 2.4, arms: 2.0, luxury: 2.4 },
    field: { n: 'Main Belt', z: 2, ores: { titanium: 1, nickel: 3, cobalt: 2.5, iridium: 1.75 }, count: 30 },
    desc: 'Capital of the Asteroid Belt. Nickel, blue cobalt, iridium… and pirates.' },
  { id: 'jupiter', n: 'Jupiter', r: 345, period: 1000, a0: 1.0, size: 19, tex: 'jupiter', col: ['#e8c49a', '#8a5a36'], body: 1, tier: 6 },
  { id: 'europa', n: 'Europa', parent: 'jupiter', r: 30, period: 11, a0: 0, size: 4, tex: 'europa', col: ['#f2eadb', '#8f7a60'], faction: 'exterior', danger: 0.12, tier: 6,
    station: 'Europa Colony', fuel: 4, repair: 3.5,
    market: { iron: 2.2, nickel: 2.2, ice: 0.6, titanium: 2.0, platinum: 2.2, he3: 1.4, iridium: 3.0, exotic: 2.2, cobalt: 2.2, sunstone: 2.0, ringpearl: 2.6, voidshard: 2.2, food: 3.0, meds: 2.6, machinery: 2.4, tech: 2.6, arms: 2.0, luxury: 2.6 },
    desc: 'A colony beneath the ice. Desperate for food and technology; pays well for iridium.' },
  { id: 'troyanos', n: 'Trojans', follow: 'jupiter', offset: 1.05, size: 5, col: ['#a49a8e', '#3e3831'], danger: 0.35, tier: 6,
    station: 'L4 Depot', depot: 1, fuel: 6, repair: 4, market: { ...DEPOT },
    field: { n: 'Jupiter Trojans', z: 3, ores: { he3: 1.2, cobalt: 1, iridium: 4 }, count: 30 },
    desc: 'An asteroid swarm at Jupiter\'s L4 point. Iridium everywhere. Pirate territory.' },
  { id: 'saturno', n: 'Saturn', r: 430, period: 1700, a0: 3.4, size: 16, tex: 'saturn', col: ['#f0dca4', '#8e7440'], ring: 1, danger: 0.25, tier: 7,
    station: 'Ring Depot', depot: 1, fuel: 5, repair: 4, market: { ...DEPOT },
    field: { n: 'Rings of Saturn', z: 4, ores: { ice: 2, he3: 4, ringpearl: 3.6, exotic: 0.55 }, count: 32 },
    desc: 'The rings: Helium-3, glowing Ring Pearls, and the first exotic crystals.' },
  { id: 'titan', n: 'Titan', parent: 'saturno', r: 32, period: 16, a0: 2, size: 5, tex: 'titan', col: ['#f0a95c', '#7a4a1c'], faction: 'exterior', danger: 0.12, tier: 7,
    station: 'Titan Refinery', fuel: 3, repair: 3,
    market: { iron: 2.2, nickel: 2.2, ice: 1.0, titanium: 2.1, platinum: 2.3, he3: 3.2, iridium: 2.4, exotic: 2.6, cobalt: 2.2, sunstone: 2.0, ringpearl: 2.6, voidshard: 2.6, food: 2.8, meds: 2.6, machinery: 0.5, tech: 2.8, arms: 2.2, luxury: 1.8 },
    desc: 'Methane refineries. Pays top price for Helium-3.' },
  { id: 'pluton', n: 'Pluto', r: 540, period: 2800, a0: 5.9, size: 5, tex: 'pluto', col: ['#e6d2bf', '#5a463c'], faction: 'piratas', danger: 0.3, tier: 8, black: 1,
    station: 'Charon Haven', fuel: 9, repair: 5,
    market: { iron: 1.8, nickel: 1.8, ice: 1.6, titanium: 1.9, platinum: 2.0, he3: 2.0, iridium: 2.8, exotic: 3.5, cobalt: 1.8, sunstone: 2.0, ringpearl: 2.8, voidshard: 3.4, food: 3.0, meds: 3.2, tech: 2.6, arms: 0.45, luxury: 3.0, machinery: 2.4 },
    desc: 'A black market at the edge of the system. Best prices for exotics. No questions asked.' },
  { id: 'kuiper', n: 'Kuiper Belt', r: 600, period: 3300, a0: 5.45, size: 6, col: ['#9fb6ff', '#2a3566'], danger: 0.55, tier: 8,
    station: 'Frontier Depot', depot: 1, fuel: 8, repair: 5, market: { ...DEPOT },
    field: { n: 'Kuiper Belt', z: 5, ores: { ice: 1.5, iridium: 2, ringpearl: 1.2, exotic: 2 }, count: 32, cold: 1 },
    desc: 'The frozen frontier. Exotic crystals glow everywhere… guarded by pirate carriers.' },
  // revealed by the alien signal once you rule the system
  { id: 'oort', n: 'Oort Cloud', r: 760, period: 5200, a0: 4.6, size: 7, col: ['#7fdfff', '#1a2a55'], danger: 0.45, tier: 8, secret: 1,
    station: 'Deep Signal Outpost', depot: 1, fuel: 10, repair: 6, market: { ...DEPOT },
    field: { n: 'Oort Cloud', z: 5, ores: { ice: 4, exotic: 2.2, voidshard: 0.45 }, count: 34, cold: 1 },
    desc: 'The edge of the Sun\'s reach. Something ancient is broadcasting from deep inside the cloud.' },
];
const LOC = Object.fromEntries(LOCS.map(l => [l.id, l]));
const NODES = LOCS.filter(l => !l.body);
const FIELDS = NODES.filter(l => l.field);
for (const l of LOCS) if (l.market) for (const o of ORES) if (l.market[o] == null) l.market[o] = 0.95;

// ============ PROGRESSION (lifetime earnings) ============
const UNLOCKS = [
  { at: 0 },
  { at: 250, icon: '🤖', title: 'Drone Outposts', text: 'Build an <b>outpost</b> in a mining field and add <b>drones</b>. They mine <b>slowly</b> but <b>never stop</b> — even while you\'re away. Open the <b>Outpost</b> tab when docked.', upg: ['cargo', 'extractor'] },
  { at: 2000, icon: '🗺️', title: 'Star Map', text: 'From now on <b>you choose where to sell</b>. Station depots pay little; <b>Earth pays about 3×</b> for metals — load up and fly there! Travel uses fuel, which refills when you dock. <b>Refinery</b> upgrades boost ALL ore income.', upg: ['refinery', 'engine', 'tank'] },
  { at: 15000, icon: '🔴', title: 'Mars & Mercury', text: '<b>Mercury</b> is covered in <b>Platinum</b> and <b>Sunstone</b> (worth 60–100× iron) but the heat burns your hull — buy <b>Shields</b>. <b>Mars</b> pays a fortune for ice.', upg: ['shield'] },
  { at: 500000, icon: '☄️', title: 'The Asteroid Belt', text: '<b>Ceres</b> and the Main Belt: nickel, <b>cobalt</b>, iridium… and <b>pirates</b>. You fly and shoot in battle — buy <b>Weapons</b>!', upg: ['weapons'] },
  { at: 4e6, icon: '📈', title: 'Trade & Events', text: 'Stations let you <b>buy and sell goods</b> and offer <b>contracts</b>. Buy goods cheap on one planet and sell them on the next stop of your ore runs. System <b>events</b> — wars, plagues, booms — swing prices. <b>Venus</b> is open.', upg: [] },
  { at: 20e6, icon: '🪐', title: 'Jupiter System', text: '<b>Europa</b> and the <b>Trojan</b> asteroids: iridium worth <b>300× iron</b>. The <b>Scanner</b> reveals rich veins.', upg: ['scanner'] },
  { at: 150e6, icon: '👑', title: 'Saturn & Influence', text: '<b>Titan</b> and the <b>Rings</b>. <b>Invest</b> in stations: each level adds <b>+10% of your base income</b> (ore, drones, freighters) and <b>influence</b>. Reach <b>100 influence</b> to rule the system.', upg: [] },
  { at: 1.5e9, icon: '💎', title: 'The Frontier', text: '<b>Pluto</b>\'s black market and the <b>Kuiper Belt</b>. Exotic crystals are worth <b>2,000× iron</b>.', upg: [] },
];
const U = { OUTPOST: 1, MAP: 2, MARS: 3, BELT: 4, TRADE: 5, JUPITER: 6, SATURN: 7, FRONTIER: 8 };

// ============ UPGRADES (exponential) ============
// cost(lv) = price to go from lv to lv+1
const UPG = {
  hull:     { n: 'Ship Class', icon: '⬢', stage: 0, max: 5, d: 'A new hull is a whole new ship: bigger base cargo and armor.',
              names: ['Sparrow', 'Mule', 'Albatross', 'Leviathan', 'Colossus'],
              costs: [400, 15000, 800000, 60e6], cargo: [20, 50, 120, 300, 800], hp: [60, 160, 450, 1300, 4000], mass: [1, 1.2, 1.45, 1.75, 2.1] },
  extractor:{ n: 'Extractor', icon: '⛏', stage: 1, max: 30, c0: 80, g: 1.75, d: 'Rocks drop more ore — +15% per level. Fill your hold faster.' },
  laser:    { n: 'Mining Laser', icon: '✦', stage: 0, max: 60, c0: 40, g: 1.45, d: 'Cut rocks faster. Farther zones have much tougher rock.' },
  magnet:   { n: 'Magnet', icon: '⌬', stage: 0, max: 25, c0: 30, g: 1.5, d: 'Pull ore from farther away. Every 3 levels adds a collector drone.' },
  cargo:    { n: 'Cargo Bay', icon: '▣', stage: 1, max: 40, c0: 60, g: 1.6, d: '+25% cargo space per level.' },
  refinery: { n: 'Refinery', icon: '⚗', stage: 2, max: 60, c0: 400, g: 1.6, d: '+7% value on ALL ore — including your drones.' },
  engine:   { n: 'Engines', icon: '⇮', stage: 2, max: 20, c0: 300, g: 1.7, d: 'Fly faster, use less fuel, warp out of fights sooner.' },
  tank:     { n: 'Fuel Tank', icon: '◍', stage: 2, max: 15, c0: 200, g: 1.7, d: 'Reach farther destinations.' },
  shield:   { n: 'Shields', icon: '🛡', stage: 3, max: 50, c0: 1500, g: 1.45, d: 'Absorb damage and heat. Regenerate over time.' },
  weapons:  { n: 'Guns', icon: '✚', stage: 4, max: 60, c0: 3000, g: 1.42, d: 'Twin cannons for fighting pirates. Hold fire to shoot.' },
  scanner:  { n: 'Scanner', icon: '◈', stage: 6, max: 5, c0: 2e6, g: 4, d: 'Reveals rich veins and helps avoid ambushes.' },
};
const UPG_KEYS = Object.keys(UPG);
function upgCost(k, lv) { const u = UPG[k]; return u.costs ? u.costs[lv - 1] : Math.round(u.c0 * Math.pow(u.g, lv - 1)); }

// ============ DRONE OUTPOSTS ============
// per field zone: build cost, drone base cost, drone income per second
// Balanced like classic idle games: automation starts at a small fraction of
// what active mining earns (~10–15%), each drone takes 5+ minutes to pay back,
// costs grow 18% per drone, and every outpost level only holds 5 more drones.
const OUTPOST = {
  build: [150, 4000, 30000, 250000, 2e6, 15e6],
  drone: [30, 600, 2400, 18000, 120000, 750000],
  rate:  [0.1, 2, 8, 60, 400, 2500],
  growth: 1.18,
  slots: 5,              // drone slots per outpost level
  lvCost: [15, 100, 700, 5000, 35000, 250000, 1.8e6, 1.3e7, 1e8], // × build cost, to reach level 2..10
  maxLv: 10,
};
const outpostRate = (z, lv, n) => OUTPOST.rate[z] * n * Math.pow(2, lv - 1);
const outpostCap = lv => OUTPOST.slots * lv;

// ============ MEGAPROJECTS (things to do with a fortune) ============
const PROJECTS = [
  { id: 'driver', icon: '🧲', n: 'Lunar Mass Driver', loc: 'luna', stage: 2, cost: 40000, infl: 2,
    d: 'A kilometer-long magnetic rail on the Moon hurls ore straight to Earth.', fx: 'Moon outpost output ×3' },
  { id: 'beacons', icon: '📡', n: 'Deep Space Beacons', loc: null, stage: 3, cost: 600000, infl: 3,
    d: 'A navigation network spanning the inner system.', fx: 'Travel 50% faster · fuel −30%' },
  { id: 'fleet', icon: '⛴', n: 'Private Security Fleet', loc: null, stage: 4, cost: 10e6, infl: 5,
    d: 'Hire a fleet of gunships that patrol your routes — and fly with you into battle.', fx: 'Pirate danger −50% · 2 escort gunships in every fight' },
  { id: 'elevator', icon: '🗼', n: 'Earth Space Elevator', loc: 'tierra', stage: 5, cost: 200e6, infl: 6,
    d: 'A cable 36,000 km tall. Earth\'s industry is now yours to supply.', fx: 'All ore sells for +25% everywhere' },
  { id: 'terraform', icon: '🌍', n: 'Terraform Mars', loc: 'marte', stage: 6, cost: 3e9, infl: 12,
    d: 'Ice comets, orbital mirrors and a century of work in one budget line. Mars turns blue.', fx: 'Mars pays ×2 for everything · Mars Republic reputation +50' },
  { id: 'gates', icon: '🌀', n: 'Jump Gate Network', loc: null, stage: 7, cost: 40e9, infl: 10,
    d: 'Wormhole gates at every station. Distance no longer matters.', fx: 'Instant, free travel anywhere' },
  { id: 'ringstation', icon: '💫', n: 'Saturn Ring Megastation', loc: 'saturno', stage: 7, cost: 250e9, infl: 10,
    d: 'A city-sized refinery woven into Saturn\'s rings.', fx: 'ALL drone income ×3' },
  { id: 'dyson', icon: '☀️', n: 'Dyson Swarm', loc: null, stage: 8, cost: 5e12, infl: 25,
    d: 'Billions of mirrors around the Sun. You now own a star\'s worth of power.', fx: 'ALL income ×5' },
  { id: 'nova', icon: '💥', n: 'Nova Cannon', loc: null, stage: 8, cost: 2e13, infl: 10, req: 'dyson',
    d: 'A beam that channels the Dyson Swarm into a single point. Nothing can stand against it.', fx: 'Lets you DESTROY planets (from the Star Map)' },
];
// signature megaprojects: each star system has one of its own (sys = where it can be built)
PROJECTS.push(
  { id: 'resonance', sys: 'centauri', icon: '💎', n: 'Crystal Resonance Array', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'Tuned sonic emitters make every crystal sing as it breaks — the shards split along their richest veins.', fx: 'Crystal shards drop ×2 ore' },
  { id: 'borer', sys: 'barnard', icon: '⛏', n: 'Deep Core Borer', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'A planet-cracking drill head, shrunk down and bolted onto your ship.', fx: 'Drill reach +60% and drill power ×1.5' },
  { id: 'plasmaforge', sys: 'sirius', icon: '🔥', n: 'Plasma Forge', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'Star-hot plasma melts the armor off asteroids before your beam even arrives.', fx: 'Laser does 60% to armored rocks · armored rocks drop ×2 ore' },
  { id: 'exchange', sys: 'tauceti', icon: '📈', n: 'Galactic Stock Exchange', loc: 'tierra', stage: 5, cost: 300e6, infl: 8,
    d: 'You list the entire star system on the galactic market. Everyone wants a share.', fx: 'Freighter & trade income ×3' },
  { id: 'chainlab', sys: 'eridani', icon: '💥', n: 'Chain Reaction Lab', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'Blasting Guild scientists tune every volatile rock in the system to go off just right.', fx: 'Explosive rocks blast 60% wider' },
  { id: 'herding', sys: 'vega', icon: '☄', n: 'Comet Herding Array', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'Gravity shepherds steer the system\'s comets straight through your mining fields.', fx: 'Comets come 3× as often and drop ×2 ore' },
  { id: 'bounty', sys: 'altair', icon: '☠', n: 'Bounty Exchange', loc: 'tierra', stage: 4, cost: 50e6, infl: 6,
    d: 'Every free city in Altair pays you for every pirate you blow up.', fx: 'Pirate loot ×3' },
  { id: 'whisperer', sys: 'kepler', icon: '🎵', n: 'Reef Whisperers', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'Singers of the Reef Keepers teach your ship the song living rocks love. They swim right up to your laser.', fx: 'Living rocks stop fleeing and drop ×2 ore' },
  { id: 'sonar', sys: 'rigel', icon: '◈', n: 'Quantum Sonar Array', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'A sonar that hears the echo of every geode in the system — even the ones that haven\'t formed yet.', fx: 'Deep Scan recharges 2× faster · geodes drop ×2 ore' },
  { id: 'starheart', sys: 'betelgeuse', icon: '☀', n: 'Starheart Tap', loc: 'ceres', stage: 4, cost: 50e6, infl: 6,
    d: 'You drill a pipe into the heart of a dying star. It pulses more often, and you are ready every time.', fx: 'Stellar pulses come 2× as often and last 50% longer' },
);
const PROJ = Object.fromEntries(PROJECTS.map(p => [p.id, p]));

// ============ INVESTMENTS ============
const STATION_TIER = { luna: 1, tierra: 2, venus: 4, marte: 4, ceres: 10, europa: 40, titan: 150, pluton: 400 };
const INVEST = { names: ['Warehouse', 'Refinery', 'Consortium'], cost: [5e6, 50e6, 500e6], infl: [3, 6, 10], bonus: 0.10, rep: [0, 15, 35] };

// ============ ENEMIES (real-time combat) ============
const ENEMIES = {
  raider:  { n: 'Raider',          hp: 30,  sp: 0,   dmg: 4,  rate: 1.2, spd: 210, size: 0.8,  loot: 40,  pow: 1 },
  corsair: { n: 'Corsair',         hp: 80,  sp: 25,  dmg: 6,  rate: 1.3, spd: 180, size: 1.05, loot: 110, pow: 2.5 },
  frigate: { n: 'Pirate Frigate',  hp: 200, sp: 70,  dmg: 8,  rate: 1.6, spd: 135, size: 1.4,  loot: 320, pow: 5, burst: 3 },
  carrier: { n: 'Pirate Carrier',  hp: 600, sp: 200, dmg: 11, rate: 2.4, spd: 90,  size: 2.0,  loot: 1200, pow: 11, burst: 5 },
  warlord: { n: 'Pirate Warlord',  hp: 520, sp: 230, dmg: 5, rate: 1.3, spd: 95, size: 2.7, loot: 6000, pow: 20, burst: 5, boss: 1 },
  sentinel: { n: 'Alien Sentinel',  hp: 650, sp: 500, dmg: 2.5, rate: 1.0, spd: 70, size: 3.2, loot: 20000, pow: 30, burst: 3, spread: 3, boss: 1, final: 1, alien: 1 },
  queen:   { n: 'Hive Queen',      hp: 760, sp: 260, dmg: 2.5, rate: 1.2, spd: 60, size: 3.4, loot: 20000, pow: 30, burst: 4, boss: 1, final: 1, hive: 1, summon: 'swarmer' },
  colossus: { n: 'Mining Colossus', hp: 900, sp: 200, dmg: 3, rate: 2.4, spd: 45, size: 3.6, loot: 20000, pow: 30, burst: 1, radial: 12, boss: 1, final: 1, mech: 1 },
  serpent: { n: 'Solar Serpent',   hp: 600, sp: 250, dmg: 2, rate: 0.9, spd: 210, size: 3.0, loot: 20000, pow: 30, burst: 6, boss: 1, final: 1, serpent: 1 },
  dreadnought: { n: 'Merchant Dreadnought', hp: 680, sp: 400, dmg: 1.6, rate: 1.4, spd: 55, size: 3.8, loot: 20000, pow: 30, burst: 2, spread: 5, boss: 1, final: 1, summon: 'corsair', summonMax: 3 },
  citadel: { n: 'Dust Citadel',    hp: 1000, sp: 300, dmg: 1.4, rate: 0.22, spd: 0, size: 4.2, loot: 20000, pow: 30, burst: 1, spiral: 4, boss: 1, final: 1, fort: 1 },
  leviathan: { n: 'Ice Leviathan', hp: 760, sp: 300, dmg: 2.5, rate: 1.6, spd: 80, size: 3.8, loot: 20000, pow: 30, burst: 3, spread: 3, dash: 1, boss: 1, final: 1, whale: 1 },
  pirateking: { n: 'Pirate King',  hp: 720, sp: 420, dmg: 2.2, rate: 1.2, spd: 90, size: 3.4, loot: 20000, pow: 30, burst: 3, spread: 3, boss: 1, final: 1, summon: 'raider', summonMax: 4 },
  kraken:  { n: 'Space Kraken',    hp: 800, sp: 280, dmg: 2.2, rate: 1.3, spd: 70, size: 3.8, loot: 20000, pow: 30, burst: 2, spread: 4, boss: 1, final: 1, kraken: 1, ink: 1 },
  radiant: { n: 'Radiant Titan',   hp: 860, sp: 340, dmg: 2.0, rate: 2.0, spd: 50, size: 3.8, loot: 20000, pow: 30, burst: 1, radial: 10, boss: 1, final: 1, radiant: 1, beam: 1 },
  phoenix: { n: 'Stellar Phoenix', hp: 540, sp: 260, dmg: 2.2, rate: 1.1, spd: 150, size: 3.4, loot: 20000, pow: 30, burst: 3, spread: 3, dash: 1, rebirth: 1, boss: 1, final: 1, phoenix: 1 },
  swarmer: { n: 'Swarmer',         hp: 26,  sp: 0,   dmg: 2,  rate: 0.9, spd: 270, size: 0.55, loot: 150,  pow: 1, hive: 1 },
  adrone:  { n: 'Sentinel Drone',  hp: 40,  sp: 40,  dmg: 3,  rate: 1.0, spd: 230, size: 0.7,  loot: 300,  pow: 1, alien: 1 },
  patrol:  { n: 'Military Patrol', hp: 160, sp: 80,  dmg: 7,  rate: 1.4, spd: 170, size: 1.25, loot: 400, pow: 4.5, military: 1 },
};
const Z_ENEMY = [0.5, 0.7, 1, 2.2, 5, 12];   // enemy stat multiplier by zone (combat is a side dish: tools/balance-sim.js checks fights stay short)
const Z_LOOT = [1, 5, 30, 250, 2500, 25000];

const RANKS = [
  [0, 'Rookie'], [8, 'Pilot'], [20, 'Contractor'], [35, 'Tycoon'],
  [55, 'Magnate'], [75, 'Belt Legend'], [100, 'Solar Sovereign'],
];
