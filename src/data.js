'use strict';
// ============ GAME DATA ============
const TAU = Math.PI * 2;
const rand = (a, b) => a + Math.random() * (b - a);
const randi = (a, b) => Math.floor(rand(a, b + 1));
const pick = arr => arr[Math.floor(Math.random() * arr.length)];
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const lerp = (a, b, t) => a + (b - a) * t;
const fmt = n => Math.round(n).toLocaleString('en-US');

const ITEMS = {
  iron:      { n: 'Iron',           b: 14,  c: '#d7a98a', ore: 1, h: 1.0 },
  nickel:    { n: 'Nickel',         b: 22,  c: '#9fe0b8', ore: 1, h: 1.2 },
  ice:       { n: 'Ice',            b: 16,  c: '#a6ecff', ore: 1, h: 0.7 },
  titanium:  { n: 'Titanium',       b: 45,  c: '#dfe6ff', ore: 1, h: 1.6 },
  platinum:  { n: 'Platinum',       b: 85,  c: '#fff1b8', ore: 1, h: 2.0 },
  he3:       { n: 'Helium-3',       b: 120, c: '#ffd24a', ore: 1, h: 1.5 },
  iridium:   { n: 'Iridium',        b: 170, c: '#c38bff', ore: 1, h: 2.6 },
  exotic:    { n: 'Exotic Crystal', b: 360, c: '#ff5fd7', ore: 1, h: 3.2 },
  food:      { n: 'Food',           b: 24,  c: '#96e072' },
  meds:      { n: 'Medicine',       b: 70,  c: '#ff6b7d' },
  machinery: { n: 'Machinery',      b: 58,  c: '#e0b35e' },
  tech:      { n: 'Electronics',    b: 95,  c: '#69b8ff' },
  arms:      { n: 'Weapons',        b: 125, c: '#ff934a' },
  luxury:    { n: 'Luxuries',       b: 185, c: '#f7e3a1' },
};
const ITEM_KEYS = Object.keys(ITEMS);
const ORES = ITEM_KEYS.filter(k => ITEMS[k].ore);
const GOODS = ITEM_KEYS.filter(k => !ITEMS[k].ore);

const FACTIONS = {
  tierra:   { n: 'Earth Union',        c: '#5fb4ff', locs: ['tierra', 'luna', 'venus'] },
  marte:    { n: 'Mars Republic',      c: '#ff7a50', locs: ['marte'] },
  cinturon: { n: 'Belt Coalition',     c: '#ffc857', locs: ['ceres'] },
  exterior: { n: 'Outer League',       c: '#6dffb0', locs: ['europa', 'titan'] },
  piratas:  { n: 'Black Syndicate',    c: '#ff4d6d', locs: ['pluton'] },
};

// r = orbit radius (map units), period = days per orbit, tier = unlock stage required
const LOCS = [
  { id: 'mercurio', n: 'Mercury', r: 62, period: 70, a0: 1.2, size: 5, tex: 'rock', col: ['#d8c3a5', '#6b5a48'], danger: 0.06, tier: 2,
    field: { n: 'Caloris Plains', ores: { iron: 4, platinum: 3, iridium: 1.2, titanium: 1 }, count: 16, hazard: 'heat' },
    desc: 'Scorched rock next to the Sun. Precious metals — but the heat burns unshielded hulls.' },
  { id: 'venus', n: 'Venus', r: 98, period: 120, a0: 2.7, size: 8, tex: 'venus', col: ['#f3d9a0', '#a8793b'], faction: 'tierra', danger: 0.04, tier: 4,
    station: 'Aphrodite Cloud City', fuel: 6, repair: 3,
    market: { ice: 1.9, titanium: 1.3, platinum: 1.25, food: 1.3, machinery: 1.45, tech: 0.9, meds: 0.85, luxury: 0.6 },
    desc: 'Floating cities above acid clouds. They make luxuries and medicine, and crave water.' },
  { id: 'tierra', n: 'Earth', r: 142, period: 190, a0: 0.2, size: 9, tex: 'earth', col: ['#5fb4ff', '#15407e'], faction: 'tierra', danger: 0.03, tier: 1,
    station: 'Gateway Port', fuel: 5, repair: 3,
    market: { iron: 1.3, nickel: 1.3, ice: 1.0, titanium: 1.4, platinum: 1.55, he3: 1.7, iridium: 1.45, exotic: 1.5, food: 0.6, meds: 0.65, machinery: 0.9, tech: 0.6, arms: 1.15, luxury: 0.8 },
    desc: 'The cradle of humanity. Pays more for every metal you bring.' },
  { id: 'luna', n: 'Moon', parent: 'tierra', r: 17, period: 27, a0: 0, size: 4, tex: 'moon', col: ['#e3e3e3', '#6a6a72'], faction: 'tierra', danger: 0.02, tier: 0,
    station: 'Tranquility Base', fuel: 4, repair: 2.5,
    market: { iron: 1.0, nickel: 1.0, ice: 1.15, titanium: 1.0, he3: 1.0, food: 1.25, meds: 1.1, machinery: 1.2, tech: 1.1 },
    field: { n: 'Lunar Maria', ores: { iron: 5, ice: 2.5, titanium: 1, he3: 0.5 }, count: 18 },
    desc: 'Your home base. A calm mining field and a small station.' },
  { id: 'marte', n: 'Mars', r: 196, period: 330, a0: 4.1, size: 7, tex: 'mars', col: ['#ff8a5c', '#7a2a14'], faction: 'marte', danger: 0.05, tier: 2,
    station: 'Olympus City', fuel: 5, repair: 3,
    market: { iron: 0.9, nickel: 1.1, ice: 2.0, titanium: 1.2, platinum: 1.2, he3: 1.3, food: 1.6, meds: 1.35, machinery: 0.65, tech: 1.3, arms: 0.6, luxury: 1.3 },
    desc: 'A militarized republic. Pays double for ice — water is life on Mars.' },
  { id: 'ceres', n: 'Ceres', r: 262, period: 560, a0: 5.4, size: 5, tex: 'rock', col: ['#b7b0a4', '#4c463e'], faction: 'cinturon', danger: 0.22, tier: 3,
    station: 'Ceres Station', fuel: 5, repair: 3.5,
    market: { iron: 0.8, nickel: 0.8, ice: 1.3, titanium: 1.0, platinum: 1.1, he3: 1.2, iridium: 1.1, food: 1.7, meds: 1.5, machinery: 1.3, tech: 1.45, arms: 1.3, luxury: 1.4 },
    field: { n: 'Main Belt', ores: { iron: 3, nickel: 4, titanium: 2.2, platinum: 1.5, ice: 1 }, count: 24 },
    desc: 'Capital of the Asteroid Belt. Rich in nickel and platinum. Pirates prowl here.' },
  { id: 'jupiter', n: 'Jupiter', r: 345, period: 1000, a0: 1.0, size: 19, tex: 'jupiter', col: ['#e8c49a', '#8a5a36'], body: 1, tier: 5 },
  { id: 'europa', n: 'Europa', parent: 'jupiter', r: 30, period: 11, a0: 0, size: 4, tex: 'europa', col: ['#f2eadb', '#8f7a60'], faction: 'exterior', danger: 0.12, tier: 5,
    station: 'Europa Colony', fuel: 4, repair: 3.5,
    market: { iron: 1.5, nickel: 1.4, ice: 0.6, titanium: 1.2, platinum: 1.15, he3: 0.9, iridium: 1.3, exotic: 1.2, food: 2.0, meds: 1.6, machinery: 1.5, tech: 1.5, arms: 1.2, luxury: 1.5 },
    desc: 'A colony beneath the ice. Desperate for food and technology.' },
  { id: 'troyanos', n: 'Trojans', follow: 'jupiter', offset: 1.05, size: 5, col: ['#a49a8e', '#3e3831'], danger: 0.35, tier: 5,
    field: { n: 'Jupiter Trojans', ores: { titanium: 3, platinum: 2.5, nickel: 2, iridium: 1.2, he3: 0.5 }, count: 22 },
    desc: 'An asteroid swarm at Jupiter\'s L4 point. Platinum and iridium. Pirate territory.' },
  { id: 'saturno', n: 'Saturn', r: 430, period: 1700, a0: 3.4, size: 16, tex: 'saturn', col: ['#f0dca4', '#8e7440'], ring: 1, danger: 0.2, tier: 6,
    field: { n: 'Rings of Saturn', ores: { ice: 5, he3: 2.5, iridium: 1.2, platinum: 0.6 }, count: 26 },
    desc: 'The rings: endless ice and pockets of Helium-3.' },
  { id: 'titan', n: 'Titan', parent: 'saturno', r: 32, period: 16, a0: 2, size: 5, tex: 'titan', col: ['#f0a95c', '#7a4a1c'], faction: 'exterior', danger: 0.12, tier: 6,
    station: 'Titan Refinery', fuel: 3, repair: 3,
    market: { iron: 1.6, nickel: 1.5, ice: 0.7, titanium: 1.35, platinum: 1.35, he3: 0.8, iridium: 1.3, exotic: 1.35, food: 1.9, meds: 1.7, machinery: 1.4, tech: 1.6, arms: 1.4, luxury: 0.9 },
    desc: 'Methane refineries. The cheapest fuel in the system.' },
  { id: 'pluton', n: 'Pluto', r: 540, period: 2800, a0: 5.9, size: 5, tex: 'pluto', col: ['#e6d2bf', '#5a463c'], faction: 'piratas', danger: 0.3, tier: 7, black: 1,
    station: 'Charon Haven', fuel: 9, repair: 5,
    market: { iron: 1.2, nickel: 1.2, ice: 1.0, titanium: 1.2, platinum: 1.3, he3: 1.2, iridium: 1.5, exotic: 1.8, food: 1.8, meds: 2.0, tech: 1.5, arms: 0.55, luxury: 1.6, machinery: 1.3 },
    desc: 'A black market at the edge of the system. No questions asked. Best prices for exotics.' },
  { id: 'kuiper', n: 'Kuiper Belt', r: 600, period: 3300, a0: 5.45, size: 6, col: ['#9fb6ff', '#2a3566'], danger: 0.55, tier: 7,
    field: { n: 'Kuiper Belt', ores: { ice: 3, he3: 2, iridium: 2, exotic: 1.4 }, count: 24, cold: 1 },
    desc: 'The frozen frontier. Exotic crystals glow here… and so do the biggest pirate ships.' },
];
const LOC = Object.fromEntries(LOCS.map(l => [l.id, l]));
const NODES = LOCS.filter(l => !l.body);
// every station buys every ore (auto-sell on docking)
for (const l of LOCS) if (l.market) for (const o of ORES) if (l.market[o] == null) l.market[o] = 0.95;

// ============ PROGRESSION ============
// Unlocks happen by lifetime earnings. Each adds a new layer of the game.
const UNLOCKS = [
  { at: 0 },
  { at: 600, icon: '🗺️', title: 'Star Map unlocked', text: 'You can now fly to <b>Earth</b>. It pays <b>30–70% more</b> for metals. Travel uses fuel — your tank refills when you dock.', upg: ['engine', 'tank'] },
  { at: 3000, icon: '🔴', title: 'Mars & Mercury', text: '<b>Mars</b> pays double for Ice. <b>Mercury</b> is full of Platinum, but the heat burns your hull — <b>Shields</b> are now for sale.', upg: ['shield'] },
  { at: 8000, icon: '☄️', title: 'The Asteroid Belt', text: '<b>Ceres</b> and the Main Belt are open: nickel, platinum… and <b>pirates</b>. Battles are automatic — buy <b>Weapons</b> to win them.', upg: ['weapons'] },
  { at: 18000, icon: '📈', title: 'Trade & Contracts', text: 'Stations now let you <b>buy and sell goods</b>, offer <b>contracts</b>, and the system has <b>events</b> — wars, plagues, booms — that swing prices. <b>Venus</b> is open.', upg: [] },
  { at: 40000, icon: '🪐', title: 'Jupiter System', text: '<b>Europa</b> colony and the <b>Trojan</b> asteroids are open. Iridium! The <b>Scanner</b> reveals rich veins and avoids ambushes.', upg: ['scanner'] },
  { at: 90000, icon: '👑', title: 'Saturn & Influence', text: '<b>Titan</b> and the <b>Rings</b> are open. You can now <b>invest</b> in stations for daily income and <b>influence</b>. Reach <b>100 influence</b> to rule the system.', upg: [] },
  { at: 180000, icon: '💎', title: 'The Frontier', text: '<b>Pluto</b>\'s black market and the <b>Kuiper Belt</b> are open. Exotic crystals are worth a fortune — and guarded by pirate carriers.', upg: [] },
];
const U = { MAP: 1, MARS: 2, BELT: 3, TRADE: 4, JUPITER: 5, SATURN: 6, FRONTIER: 7 };

// ============ UPGRADES ============
const UPG = {
  hull:    { n: 'Hull', icon: '⬢', d: 'Cargo space & armor. A new hull is a whole new ship!', stage: 0,
             names: ['Sparrow', 'Mule', 'Albatross', 'Leviathan', 'Colossus'],
             cost: [0, 450, 2500, 12000, 50000],
             cargo: [20, 45, 90, 160, 280], hp: [60, 110, 180, 280, 420], mass: [1, 1.25, 1.6, 2.0, 2.5] },
  laser:   { n: 'Mining Laser', icon: '✦', d: 'Cut rocks faster, from farther away.', stage: 0,
             names: ['Cutter', 'Driller', 'Fissure', 'Sunlance', 'Annihilator'],
             cost: [0, 300, 1500, 7000, 28000], dps: [12, 20, 32, 50, 78], range: [190, 230, 270, 310, 360] },
  drones:  { n: 'Magnet & Drones', icon: '⌬', d: 'Pull ore from farther. Drones collect it for you and help in fights.', stage: 0,
             names: ['Magnet', 'Swarm I', 'Swarm II', 'Swarm III', 'Hive'],
             cost: [0, 250, 1400, 6500, 25000], magnet: [130, 180, 230, 290, 360], count: [0, 1, 2, 3, 4] },
  engine:  { n: 'Engines', icon: '▲', d: 'Fly faster, use less fuel, escape pirates.', stage: 1,
             names: ['Chemical', 'Ion', 'Plasma', 'Fusion', 'Torch'],
             cost: [0, 600, 3000, 11000, 36000], thrust: [1, 1.15, 1.3, 1.5, 1.75], speed: [1, 1.25, 1.55, 1.9, 2.4], eff: [1, 1.15, 1.35, 1.6, 1.9], flee: [0.3, 0.4, 0.5, 0.62, 0.75] },
  tank:    { n: 'Fuel Tank', icon: '◍', d: 'Reach farther destinations.', stage: 1,
             names: ['Basic', 'Extended', 'Double', 'Cryo', 'Deep Space'],
             cost: [0, 400, 2000, 8000, 24000], fuel: [60, 100, 150, 215, 300] },
  shield:  { n: 'Shields', icon: '◎', d: 'Absorb damage and heat. Regenerate over time.', stage: 2,
             names: ['None', 'Deflector', 'Barrier', 'Aegis', 'Bastion'],
             cost: [0, 1200, 4500, 14000, 40000], sp: [0, 30, 65, 110, 170] },
  weapons: { n: 'Weapons', icon: '✚', d: 'Auto-turrets that fight pirates for you.', stage: 3,
             names: ['Light Cannon', 'Autocannon', 'Railgun', 'Plasma Battery', 'Storm'],
             cost: [0, 1200, 4500, 14000, 40000], dps: [6, 12, 22, 36, 56] },
  scanner: { n: 'Scanner', icon: '◈', d: 'Reveals rich veins and helps avoid ambushes.', stage: 5,
             names: ['Passive', 'Active', 'Deep', 'Quantum', 'Omniscient'],
             cost: [0, 2500, 7000, 18000, 45000], avoid: [0, 0.12, 0.22, 0.32, 0.42] },
};
const UPG_KEYS = Object.keys(UPG);

// ============ INVESTMENTS ============
const INVEST = {
  names: ['Warehouse', 'Refinery', 'Consortium'],
  cost: [6000, 22000, 70000],
  income: [60, 220, 650],
  infl: [3, 6, 10],
  rep: [0, 15, 35],
};

// ============ ENEMIES ============
const ENEMIES = {
  raider:   { n: 'Raider',          hp: 36,  sp: 0,   dps: 4.5, pow: 1,   loot: 120, size: 0.8 },
  corsair:  { n: 'Corsair',         hp: 85,  sp: 20,  dps: 9,   pow: 2.5, loot: 320, size: 1.05 },
  frigate:  { n: 'Pirate Frigate',  hp: 180, sp: 55,  dps: 16,  pow: 5.1, loot: 800, size: 1.4 },
  carrier:  { n: 'Pirate Carrier',  hp: 420, sp: 120, dps: 30,  pow: 10.5, loot: 2200, size: 2.0 },
  patrol:   { n: 'Military Patrol', hp: 140, sp: 60,  dps: 14,  pow: 4.5, loot: 500, size: 1.25, military: 1 },
};

const RANKS = [
  [0, 'Rookie'], [8, 'Pilot'], [20, 'Contractor'], [35, 'Trader'],
  [55, 'Magnate'], [75, 'Belt Legend'], [100, 'Solar Sovereign'],
];
