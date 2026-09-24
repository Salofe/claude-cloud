'use strict';
// ============ DATOS DEL JUEGO ============
const TAU = Math.PI * 2;
const rand = (a, b) => a + Math.random() * (b - a);
const randi = (a, b) => Math.floor(rand(a, b + 1));
const pick = arr => arr[Math.floor(Math.random() * arr.length)];
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const lerp = (a, b, t) => a + (b - a) * t;
const fmt = n => Math.round(n).toLocaleString('es-MX');

const ITEMS = {
  iron:      { n: 'Hierro',          b: 14,  c: '#c9a58a', ore: 1, h: 1.0 },
  nickel:    { n: 'Níquel',          b: 22,  c: '#9fd9b4', ore: 1, h: 1.2 },
  ice:       { n: 'Hielo',           b: 16,  c: '#a6ecff', ore: 1, h: 0.7 },
  titanium:  { n: 'Titanio',         b: 45,  c: '#d3dcf2', ore: 1, h: 1.6 },
  platinum:  { n: 'Platino',         b: 85,  c: '#fff1b8', ore: 1, h: 2.0 },
  he3:       { n: 'Helio-3',         b: 120, c: '#ffd24a', ore: 1, h: 1.5 },
  iridium:   { n: 'Iridio',          b: 170, c: '#c38bff', ore: 1, h: 2.6 },
  exotic:    { n: 'Cristal Exótico', b: 360, c: '#ff5fd7', ore: 1, h: 3.2 },
  food:      { n: 'Alimentos',       b: 24,  c: '#96e072' },
  meds:      { n: 'Medicinas',       b: 70,  c: '#ff6b7d' },
  machinery: { n: 'Maquinaria',      b: 58,  c: '#e0b35e' },
  tech:      { n: 'Electrónica',     b: 95,  c: '#69b8ff' },
  arms:      { n: 'Armamento',       b: 125, c: '#ff934a' },
  luxury:    { n: 'Lujos',           b: 185, c: '#f7e3a1' },
};
const ITEM_KEYS = Object.keys(ITEMS);
const ORES = ITEM_KEYS.filter(k => ITEMS[k].ore);

const FACTIONS = {
  tierra:   { n: 'ONU Terrestre',          c: '#5fb4ff', locs: ['tierra', 'luna', 'venus'] },
  marte:    { n: 'República de Marte',     c: '#ff7a50', locs: ['marte'] },
  cinturon: { n: 'Coalición del Cinturón', c: '#ffc857', locs: ['ceres'] },
  exterior: { n: 'Liga Exterior',          c: '#6dffb0', locs: ['europa', 'titan'] },
  piratas:  { n: 'Sindicato Negro',        c: '#ff4d6d', locs: ['pluton'] },
};

// r = radio orbital (unidades del mapa), period = días por órbita
const LOCS = [
  { id: 'mercurio', n: 'Mercurio', r: 62, period: 70, a0: 1.2, size: 5, col: ['#d8c3a5', '#6b5a48'], danger: 0.06,
    field: { n: 'Llanuras Calóricas', ores: { iron: 4, platinum: 3, iridium: 1.2, titanium: 1 }, count: 16, hazard: 'heat' },
    desc: 'Roca abrasada junto al Sol. Metales preciosos, pero el calor castiga el casco sin escudos.' },
  { id: 'venus', n: 'Venus', r: 98, period: 120, a0: 2.7, size: 8, col: ['#f3d9a0', '#a8793b'], faction: 'tierra', danger: 0.04,
    station: 'Afrodita, Ciudad Nube', fuel: 6, repair: 3, yard: 0,
    market: { iron: 1.2, nickel: 1.15, ice: 1.9, titanium: 1.3, platinum: 1.25, food: 1.3, machinery: 1.45, tech: 0.9, meds: 0.85, luxury: 0.6 },
    desc: 'Ciudades flotantes sobre nubes ácidas. Producen lujos y medicinas; mueren por agua.' },
  { id: 'tierra', n: 'Tierra', r: 142, period: 190, a0: 0.2, size: 9, col: ['#5fb4ff', '#15407e'], faction: 'tierra', danger: 0.03,
    station: 'Puerto Gateway', fuel: 5, repair: 3, yard: 5,
    market: { iron: 1.25, nickel: 1.3, ice: 1.0, titanium: 1.4, platinum: 1.55, he3: 1.7, iridium: 1.45, exotic: 1.5, food: 0.6, meds: 0.65, machinery: 0.9, tech: 0.6, arms: 1.15, luxury: 0.8 },
    desc: 'La cuna. Mercado enorme, astillero completo y hambre infinita de metales.' },
  { id: 'luna', n: 'Luna', parent: 'tierra', r: 17, period: 27, a0: 0, size: 4, col: ['#e3e3e3', '#6a6a72'], faction: 'tierra', danger: 0.02,
    station: 'Base Tranquilidad', fuel: 4, repair: 2.5, yard: 2,
    market: { iron: 0.95, nickel: 1.0, ice: 1.35, titanium: 1.1, he3: 1.15, food: 1.25, meds: 1.1, machinery: 1.2, tech: 1.1 },
    field: { n: 'Mares Lunares', ores: { iron: 5, ice: 2.5, titanium: 1, he3: 0.5 }, count: 18 },
    desc: 'Campo minero tranquilo, ideal para empezar. Combustible barato.' },
  { id: 'marte', n: 'Marte', r: 196, period: 330, a0: 4.1, size: 7, col: ['#ff8a5c', '#7a2a14'], faction: 'marte', danger: 0.05,
    station: 'Ciudad Olimpo', fuel: 5, repair: 3, yard: 4, yardMax: { weapons: 5, shield: 5 },
    market: { iron: 0.75, nickel: 1.1, ice: 1.8, titanium: 1.2, platinum: 1.2, he3: 1.3, food: 1.6, meds: 1.35, machinery: 0.65, tech: 1.3, arms: 0.6, luxury: 1.3 },
    desc: 'República militarizada. Armas y maquinaria baratas; paga bien el agua y la comida.' },
  { id: 'ceres', n: 'Ceres', r: 262, period: 560, a0: 5.4, size: 5, col: ['#b7b0a4', '#4c463e'], faction: 'cinturon', danger: 0.22,
    station: 'Estación Ceres', fuel: 5, repair: 3.5, yard: 3,
    market: { iron: 0.7, nickel: 0.7, ice: 1.2, titanium: 0.95, platinum: 1.0, he3: 1.2, iridium: 1.1, food: 1.7, meds: 1.5, machinery: 1.3, tech: 1.45, arms: 1.3, luxury: 1.4 },
    field: { n: 'Cinturón Principal', ores: { iron: 4, nickel: 4, titanium: 2, platinum: 1.3, ice: 1 }, count: 24 },
    desc: 'Capital del Cinturón. Rico en níquel y platino; los piratas rondan.' },
  { id: 'jupiter', n: 'Júpiter', r: 345, period: 1000, a0: 1.0, size: 19, col: ['#e8c49a', '#8a5a36'], body: 1, bands: 1 },
  { id: 'europa', n: 'Europa', parent: 'jupiter', r: 30, period: 11, a0: 0, size: 4, col: ['#f2eadb', '#8f7a60'], faction: 'exterior', danger: 0.12,
    station: 'Colonia Europa', fuel: 4, repair: 3.5, yard: 3,
    market: { iron: 1.4, nickel: 1.35, ice: 0.55, titanium: 1.15, platinum: 1.1, he3: 0.9, iridium: 1.3, food: 2.0, meds: 1.6, machinery: 1.5, tech: 1.5, arms: 1.2, luxury: 1.5 },
    desc: 'Colonia bajo el hielo. Desesperada por comida y tecnología.' },
  { id: 'troyanos', n: 'Troyanos', follow: 'jupiter', offset: 1.05, size: 5, col: ['#a49a8e', '#3e3831'], danger: 0.35,
    field: { n: 'Troyanos de Júpiter', ores: { titanium: 3, platinum: 2.5, nickel: 2, iridium: 1, he3: 0.5 }, count: 22 },
    desc: 'Enjambre en el punto L4 de Júpiter. Titanio, platino e iridio. Territorio pirata.' },
  { id: 'saturno', n: 'Saturno', r: 430, period: 1700, a0: 3.4, size: 16, col: ['#f0dca4', '#8e7440'], bands: 1, ring: 1, danger: 0.2,
    field: { n: 'Anillos de Saturno', ores: { ice: 6, he3: 2.2, iridium: 1, platinum: 0.6 }, count: 26 },
    desc: 'Los anillos: hielo interminable y bolsas de Helio-3.' },
  { id: 'titan', n: 'Titán', parent: 'saturno', r: 32, period: 16, a0: 2, size: 5, col: ['#f0a95c', '#7a4a1c'], faction: 'exterior', danger: 0.12,
    station: 'Refinería Titán', fuel: 3, repair: 3, yard: 5,
    market: { iron: 1.5, nickel: 1.4, ice: 0.7, titanium: 1.3, platinum: 1.3, he3: 0.75, iridium: 1.25, exotic: 1.3, food: 1.9, meds: 1.7, machinery: 1.4, tech: 1.6, arms: 1.4, luxury: 0.9 },
    desc: 'Refinerías de metano. El combustible más barato del sistema y un astillero de primera.' },
  { id: 'pluton', n: 'Plutón', r: 540, period: 2800, a0: 5.9, size: 5, col: ['#d9c2b0', '#5a463c'], faction: 'piratas', danger: 0.3,
    station: 'Refugio de Caronte', fuel: 9, repair: 5, yard: 4, yardMax: { weapons: 5, shield: 5 }, black: 1,
    market: { ice: 1.0, titanium: 1.1, platinum: 1.2, he3: 1.1, iridium: 1.4, exotic: 1.75, food: 1.8, meds: 2.0, tech: 1.5, arms: 0.55, luxury: 1.6, machinery: 1.3 },
    desc: 'Mercado negro al borde del sistema. Nadie hace preguntas.' },
  { id: 'kuiper', n: 'Kuiper', r: 600, period: 3300, a0: 5.45, size: 6, col: ['#9fb6ff', '#2a3566'], danger: 0.55,
    field: { n: 'Cinturón de Kuiper', ores: { ice: 4, he3: 2, iridium: 2, exotic: 1.2 }, count: 24, cold: 1 },
    desc: 'Frontera helada. Aquí brillan los cristales exóticos… y las naves pirata más grandes.' },
];
const LOC = Object.fromEntries(LOCS.map(l => [l.id, l]));
const NODES = LOCS.filter(l => !l.body);

// ============ MEJORAS ============
const UPG = {
  hull:    { n: 'Casco', icon: '⬢', d: 'Capacidad de carga e integridad estructural. Más grande = más combustible por viaje.',
             names: ['Gorrión', 'Mula', 'Albatros', 'Leviatán', 'Coloso'],
             cost: [0, 1500, 6000, 22000, 70000],
             cargo: [20, 45, 90, 160, 280], hp: [60, 110, 180, 280, 420], mass: [1, 1.3, 1.7, 2.2, 2.8] },
  laser:   { n: 'Láser minero', icon: '✦', d: 'Daño y alcance del láser. Rompe rocas duras más rápido.',
             names: ['Cortador', 'Perforador', 'Fisura', 'Lanza solar', 'Aniquilador'],
             cost: [0, 800, 3000, 10000, 32000], dps: [12, 20, 32, 50, 78], range: [190, 230, 270, 310, 360] },
  engine:  { n: 'Propulsores', icon: '▲', d: 'Velocidad, eficiencia de combustible y probabilidad de huir.',
             names: ['Químico', 'Iónico', 'Plasma', 'Fusión', 'Antorcha'],
             cost: [0, 900, 3500, 12000, 38000], thrust: [1, 1.15, 1.3, 1.5, 1.75], speed: [1, 1.25, 1.55, 1.9, 2.4], eff: [1, 1.15, 1.35, 1.6, 1.9], flee: [0.3, 0.4, 0.5, 0.62, 0.75] },
  tank:    { n: 'Tanque', icon: '◍', d: 'Capacidad de combustible. Necesario para llegar al sistema exterior.',
             names: ['Básico', 'Extendido', 'Doble', 'Criogénico', 'Profundo'],
             cost: [0, 600, 2500, 8000, 25000], fuel: [60, 100, 150, 215, 300] },
  shield:  { n: 'Escudos', icon: '◎', d: 'Absorben daño en combate y calor. Se regeneran.',
             names: ['Ninguno', 'Deflector', 'Barrera', 'Égida', 'Bastión'],
             cost: [0, 1000, 4000, 13000, 40000], sp: [0, 30, 65, 110, 170] },
  weapons: { n: 'Armas', icon: '✚', d: 'Torretas automáticas para defenderte de piratas.',
             names: ['Cañón ligero', 'Autocañón', 'Railgun', 'Batería de plasma', 'Tormenta'],
             cost: [0, 1000, 4000, 13000, 40000], dps: [6, 12, 22, 36, 56] },
  drones:  { n: 'Drones', icon: '⌬', d: 'Imán de mineral y drones que recogen por ti (y ayudan en combate).',
             names: ['Imán', 'Enjambre I', 'Enjambre II', 'Enjambre III', 'Colmena'],
             cost: [0, 700, 2800, 9000, 30000], magnet: [130, 180, 230, 290, 360], count: [0, 1, 2, 3, 4] },
  scanner: { n: 'Escáner', icon: '◈', d: 'Revela vetas ricas y ayuda a evitar emboscadas.',
             names: ['Pasivo', 'Activo', 'Profundo', 'Cuántico', 'Omnisciente'],
             cost: [0, 500, 2000, 7000, 22000], avoid: [0, 0.12, 0.22, 0.32, 0.42] },
};
const UPG_KEYS = Object.keys(UPG);

// ============ INVERSIONES ============
const INVEST = {
  names: ['Almacén', 'Refinería', 'Consorcio'],
  cost: [4000, 16000, 55000],
  income: [45, 170, 520],
  infl: [3, 6, 10],
  rep: [5, 20, 40],
};

// ============ ENEMIGOS ============
const ENEMIES = {
  raider:   { n: 'Saqueador',       hp: 36,  sp: 0,   dps: 4.5, pow: 1,  loot: 120, size: 0.8 },
  corsair:  { n: 'Corsario',        hp: 85,  sp: 20,  dps: 9,   pow: 2.5, loot: 320, size: 1.05 },
  frigate:  { n: 'Fragata pirata',  hp: 180, sp: 55,  dps: 16,  pow: 5.1, loot: 800, size: 1.4 },
  carrier:  { n: 'Nave nodriza',    hp: 420, sp: 120, dps: 30,  pow: 10.5, loot: 2200, size: 2.0 },
  patrol:   { n: 'Patrulla militar', hp: 140, sp: 60, dps: 14,  pow: 4.5, loot: 500, size: 1.25, military: 1 },
};

const RANKS = [
  [0, 'Aprendiz'], [8, 'Piloto'], [20, 'Contratista'], [35, 'Comerciante'],
  [55, 'Magnate'], [75, 'Leyenda del Cinturón'], [100, 'Soberanía Solar'],
];

const TUTORIAL = [
  { t: 'Viaja a la Luna', d: 'Toca la Luna en el mapa y pulsa VIAJAR.', r: 100 },
  { t: 'Mina 10 de mineral', d: 'Entra al campo minero y dispara el láser a los asteroides.', r: 150 },
  { t: 'Vende tu carga', d: 'Atraca en una estación y vende en el Mercado.', r: 150 },
  { t: 'Mejora tu nave', d: 'Compra una mejora en un Astillero (Luna o Tierra).', r: 250 },
  { t: 'Acepta un contrato', d: 'Revisa la pestaña Contratos de cualquier estación.', r: 300 },
  { t: 'Llega al Cinturón', d: 'Viaja a Ceres: más riqueza… y piratas.', r: 500 },
  { t: 'Invierte en una estación', d: 'Las inversiones dan ingresos diarios e influencia.', r: 1000 },
  { t: 'Alcanza 100 de influencia', d: 'Domina el Sistema Solar.', r: 0 },
];
