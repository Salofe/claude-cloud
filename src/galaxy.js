'use strict';
// ============ THE GALAXY: star systems, the jump gate, Tribute & Legacy ============
// Every star system reuses the same "slots" as Sol (a starter moon field, a capital,
// inner worlds, a belt, a gas giant with moons, a ringed giant, a black market, a frontier
// belt and a hidden final field). Each system is hand-made by overriding names, looks,
// ores, factions and texts on top of Sol, and gets harder: tougher rocks and pirates.

// pristine copy of the Solar System, taken before anything is modified
const SOL_SNAP = JSON.parse(JSON.stringify({ locs: LOCS, factions: FACTIONS, unlocks: UNLOCKS, projects: PROJECTS.map(p => ({ id: p.id, icon: p.icon, n: p.n, d: p.d, fx: p.fx })) }));

const SYSTEMS = {
  sol: {
    n: 'Sol', star: 'sol', rock: 1, enemy: 1, value: 1,
    boss: 'sentinel', bossFleet: ['sentinel', 'adrone', 'adrone', 'adrone'],
    signal: { title: 'A signal from the dark', text: 'Your deep-space dishes caught a <b>repeating signal</b> from the <b>Oort Cloud</b>, far beyond the Kuiper Belt. It is <b>not human</b>.' },
    gate: 'The Sentinel\'s core shatters — and deep in the Oort Cloud, a ring older than the Sun <b>lights up</b>. It is a <b>jump gate</b>.',
  },
  centauri: {
    n: 'Alpha Centauri', star: 'white', companion: 'orange', rock: 1.5, enemy: 1.35, value: 1,
    boss: 'queen', bossFleet: ['queen', 'swarmer', 'swarmer', 'swarmer'],
    signal: { title: 'Something is nesting', text: 'Probes beyond the Proxima Drift went silent one by one. The last image shows a <b>living nebula</b> — and something huge moving inside it: <b>the Hive</b>.' },
    gate: 'The Hive Queen bursts into glittering dust. In the heart of the nebula, a second ancient ring <b>wakes up</b>: the way deeper into the galaxy.',
    intro: 'You arrive through the gate at <b>Alpha Centauri</b>: two suns, crystal-rich belts and pirates <b>far tougher</b> than at home. Your fortune stayed behind — but your <b>Legacy</b> came with you.',
    factions: {
      tierra: { n: 'Pandora Accord', c: '#4fd8c0' }, marte: { n: 'Dune Clans', c: '#e8b46a' }, cinturon: { n: 'Prism Guild', c: '#c49cff' },
      exterior: { n: 'Typhon League', c: '#6aa8ff' }, piratas: { n: 'Red Market Cartel', c: '#ff4d6d' },
    },
    locs: {
      luna: { n: 'Tethys', station: 'First Light Base', tex: 'rock', col: ['#c9d2e8', '#4a5068'], desc: 'A quiet grey moon of Pandora. Your new beginning.',
        field: { n: 'Shepherd Rocks', ores: { iron: 4, titanium: 1.2, cobalt: 0.3, ice: 3 } } },
      tierra: { n: 'Pandora', station: 'Haven Port', tex: 'ocean', col: ['#7fe0a8', '#0b3a5c'], desc: 'A world of warm teal oceans under two suns. Pays well for every metal.' },
      venus: { n: 'Calypso', station: 'Orchid Spire', tex: 'gas', col: ['#f2d0ff', '#6a3a8a'], desc: 'A violet cloud world. Its floating cities crave luxury and ice.' },
      mercurio: { n: 'Cinder', station: 'Cinder Depot', tex: 'lava', col: ['#ffb060', '#4a1a0c'], desc: 'A molten world hugging Alpha Centauri A. Sunstone everywhere — and the heat.',
        field: { n: 'Glassfire Flats', ores: { titanium: 2, nickel: 2, sunstone: 2.5, iron: 1.5 }, crystal: 0.15 } },
      marte: { n: 'Dune', station: 'Sandgate', tex: 'rock', col: ['#f0c890', '#7a4a20'], desc: 'An endless desert ruled by proud clans. Water is worth more than gold here.' },
      ceres: { n: 'Halcyon', station: 'Prism Station', tex: 'rock', col: ['#d8c8ff', '#4a3a6a'], desc: 'Capital of the Shard Belt, where asteroids grow as crystals.',
        field: { n: 'Shard Belt', ores: { nickel: 2, he3: 2, platinum: 2.5, iridium: 1.1 }, crystal: 0.5 } },
      jupiter: { n: 'Typhon', tex: 'gas', col: ['#9ad8ff', '#1a3a8a'] },
      europa: { n: 'Nyx', station: 'Nyx Colony', tex: 'ice', col: ['#e8f6ff', '#5a7aa8'], desc: 'An ice moon of Typhon. The League buys iridium at any price.' },
      troyanos: { field: { n: 'Typhon Swarm', ores: { he3: 2.2, iridium: 3, ringpearl: 0.25 }, crystal: 0.2 }, station: 'Swarm Depot', desc: 'Rocks trapped in Typhon\'s gravity. Pirate nests everywhere.' },
      saturno: { n: 'Aurelia', tex: 'gas', col: ['#ffe0a0', '#9a5a20'], station: 'Halo Depot', desc: 'A golden ringed giant. Its rings are full of Ring Pearls.',
        field: { n: 'Aurelia Halo', ores: { ice: 2.5, he3: 3, ringpearl: 2.6, exotic: 0.6 }, crystal: 0.2 } },
      titan: { n: 'Mist', station: 'Mistport', tex: 'titan', col: ['#e0d0b0', '#6a5a40'], desc: 'A foggy moon of Aurelia with huge refineries.' },
      pluton: { n: 'Proxima b', station: 'Red Market', tex: 'rock', col: ['#ff9a80', '#4a1a14'], desc: 'A dim world orbiting the red dwarf Proxima. Anything is for sale.' },
      kuiper: { n: 'Proxima Drift', station: 'Drift Depot', desc: 'Frozen rocks drifting between the stars. Exotics — and the Cartel\'s carriers.',
        field: { n: 'Proxima Drift', ores: { ice: 1.5, iridium: 2.2, exotic: 2, voidshard: 0.1 } } },
      oort: { n: 'The Hive', station: 'Watchpost Omega', col: ['#b0ff9a', '#1a3a20'], desc: 'A living nebula. Something enormous breeds in its depths.',
        field: { n: 'Hive Nebula', ores: { ice: 3, ringpearl: 1.5, exotic: 2.2, voidshard: 0.42 } } },
    },
    unlocks: {
      0: { title: 'Tethys' }, 3: { title: 'Cinder & Dune', text: '<b>Cinder</b> burns with <b>Sunstone</b> but the heat eats your hull — buy <b>Shields</b>. <b>Dune</b> pays a fortune for ice.' },
      4: { title: 'The Shard Belt', text: '<b>Halcyon</b> and the <b>Shard Belt</b>: asteroids that grow as <b>crystals</b> and shatter into many shards when you break them. Catch them all! Pirates here are tougher than at home.' },
      6: { title: 'Typhon System', text: '<b>Nyx</b> and the <b>Typhon Swarm</b>: iridium everywhere. The <b>Scanner</b> reveals rich veins.' },
      7: { title: 'Aurelia & Influence', text: '<b>Mist</b> and the golden <b>Aurelia Halo</b>. <b>Invest</b> in stations: each level adds <b>+10% of your base income</b> (ore, drones, freighters) and <b>influence</b>. Reach <b>100 influence</b> to rule Alpha Centauri.' },
      8: { title: 'Proxima', text: '<b>Proxima b</b>\'s Red Market and the <b>Proxima Drift</b>. Exotics and even <b>Void Shards</b>.' },
    },
    projects: {
      driver: { icon: "🚀", n: "Tethys Railgun Highway", d: "A railgun that fires ore crates in a perfect arc straight into Pandora's orbit.", fx: "Tethys outpost output ×3" },
      beacons: { n: "Binary Slingshot Lanes", d: "Navigation buoys that slingshot ships around both suns at once.", fx: "Travel 50% faster · fuel −30%" },
      fleet: { icon: "💎", n: "Crystal Drone Armada", d: "Self-repairing gunships grown from living crystal. They fly with you into every fight.", fx: "Pirate danger −50% · 2 escort gunships in every fight" },
      elevator: { icon: "💫", n: "Pandora Orbital Ring", d: "Not one cable — a whole ring around the planet, with a hundred elevators hanging from it.", fx: "All ore sells for +25% everywhere" },
      terraform: { icon: "🌱", n: "Dune Ocean Seeding", d: "Ice comets from the Proxima Drift rain onto Dune for a decade. The desert becomes an archipelago.", fx: "Dune pays ×2 for everything · Dune Clans reputation +50" },
      gates: { n: "Shard Gate Web", d: "Wormhole gates cut from giant crystals that resonate across the whole system.", fx: "Instant, free travel anywhere" },
      ringstation: { n: "Aurelia Halo Foundry", d: "A refinery that orbits inside the golden halo, sipping Ring Pearls like nectar.", fx: "ALL drone income ×3" },
      dyson: { n: "Twin-Star Dyson Lattice", d: "Mirrors woven between both suns. The power bounces back and forth and keeps growing.", fx: "ALL income ×5" },
      nova: { icon: "⚡", n: "Binary Nova Lance", d: "Both suns fire through a single crystal lens. Planets do not survive it.", fx: "Lets you DESTROY planets (from the Star Map)" },
    },
  },
};

// systems 3–5
Object.assign(SYSTEMS, {
  barnard: {
    n: 'Barnard\'s Star', star: 'red', rock: 2.25, enemy: 1.82, value: 1, gift: 'drill',
    boss: 'colossus', bossFleet: ['colossus', 'corsair', 'corsair'],
    signal: { title: 'The machine wakes', text: 'Seismic readings from the abandoned mega-mine at <b>The Pit</b>: something enormous is <b>still digging</b> down there — and it attacks every ship that comes close.' },
    gate: 'The Colossus collapses into scrap. Beneath it, the old miners had dug up an ancient ring — and it is <b>waking up</b>.',
    intro: 'Barnard\'s Star: a dim red dwarf where miners have dug for centuries. The Haulers Union gives you their best tool, the <b>Drill</b>: press <b>Q</b> (or the DRILL button) to switch. It cuts 3× faster, but only up close. You keep it forever.',
    factions: {
      tierra: { n: 'Forge Compact', c: '#ff9a5a' }, marte: { n: 'Rust Brotherhood', c: '#d8805a' }, cinturon: { n: 'Deep Haulers Union', c: '#e0c060' },
      exterior: { n: 'Ember League', c: '#ff7a9a' }, piratas: { n: 'Black Furnace', c: '#ff4d6d' },
    },
    locs: {
      luna: { n: 'Cinderling', station: 'Old Shaft Base', tex: 'rock', col: ['#b8a898', '#3a3028'], desc: 'A cold, pocked moon of Forge. Generations of miners started here.', field: { n: 'Old Shafts', ores: { iron: 5, nickel: 0.9, titanium: 1, ice: 2.5 } } },
      tierra: { n: 'Forge', station: 'Anvil Port', tex: 'ice', col: ['#ffd0b0', '#6a3a30'], desc: 'A tidally locked world: one side frozen, one side burning. Its forges never sleep.' },
      venus: { n: 'Ashveil', station: 'Smoke Spire', tex: 'gas', col: ['#e0a898', '#5a2a20'], desc: 'Thick ash clouds over a hot world. Rich, decadent and thirsty for ice.' },
      mercurio: { n: 'Brand', station: 'Brand Depot', tex: 'lava', col: ['#ff7040', '#2a0a05'], desc: 'A scorched rock close to the red sun. Platinum lies in the open.', field: { n: 'Scorch Plains', ores: { titanium: 1.5, cobalt: 1.2, platinum: 3.6 } } },
      marte: { n: 'Rustfall', station: 'Rustfall City', tex: 'rock', col: ['#d07850', '#4a2010'], desc: 'Iron-red canyons and stubborn people. Pays well for ice.' },
      ceres: { n: 'Hollowrock', station: 'Haulers Hall', tex: 'rock', col: ['#a8a090', '#3a3630'], desc: 'The Haulers\' capital, hollowed out by centuries of mining.', field: { n: 'The Deep Belt', ores: { nickel: 2, cobalt: 3, sunstone: 1.5, iridium: 1.02 } } },
      jupiter: { n: 'Goliath', tex: 'gas', col: ['#f0b080', '#6a3010'] },
      europa: { n: 'Ember', station: 'Ember Colony', tex: 'ice', col: ['#ffd8c8', '#8a4a40'], desc: 'A warm ice moon with hot springs. The League buys iridium.' },
      troyanos: { station: 'Trojan Depot', desc: 'Rocks trapped in Goliath\'s gravity. Sunstone and iridium.', field: { n: 'Goliath Trojans', ores: { sunstone: 3.75, iridium: 2.8, ringpearl: 0.15 } } },
      saturno: { n: 'Halo', tex: 'gas', col: ['#f0d0b0', '#7a5030'], station: 'Halo Depot', desc: 'A pale ringed giant glowing red in the dim light.', field: { n: 'Halo Rings', ores: { ice: 2.5, he3: 3, ringpearl: 2.5, exotic: 0.51 } } },
      titan: { n: 'Brimstone', station: 'Sulfur Works', tex: 'titan', col: ['#f0d080', '#6a5020'], desc: 'A sulfur moon of Halo with enormous refineries.' },
      pluton: { n: 'Coalsack', station: 'The Furnace', tex: 'rock', col: ['#806060', '#201010'], desc: 'A soot-black world. The Black Furnace sells anything.' },
      kuiper: { n: 'Barnard Drift', station: 'Drift Depot', desc: 'Frozen rocks at the edge of the red sun\'s reach.', field: { n: 'Barnard Drift', ores: { ice: 2.32, ringpearl: 2.2, exotic: 1.6, voidshard: 0.1 } } },
      oort: { n: 'The Pit', station: 'Last Lamp Outpost', col: ['#ffb070', '#3a1a08'], desc: 'An abandoned mega-mine at the edge of the system. Something still works down there.', field: { n: 'The Pit', ores: { ice: 3, iridium: 2, exotic: 2, voidshard: 0.81 } } },
    },
    unlocks: {
      0: { title: 'Cinderling' }, 3: { title: 'Brand & Rustfall', text: '<b>Brand</b> is covered in <b>Platinum</b> but its heat burns your hull — buy <b>Shields</b>. <b>Rustfall</b> pays a fortune for ice.' },
      4: { title: 'The Deep Belt', text: '<b>Hollowrock</b> and the <b>Deep Belt</b>: cobalt, sunstone and iridium… and <b>pirates</b>, tougher than ever. Use the <b>Drill (Q)</b> on big rocks.' },
      6: { title: 'Goliath System', text: '<b>Ember</b> and the <b>Goliath Trojans</b>. The <b>Scanner</b> reveals rich veins.' },
      7: { title: 'Halo & Influence', text: '<b>Brimstone</b> and the <b>Halo Rings</b>. <b>Invest</b> in stations (each level <b>+10% base income</b>) for income and <b>influence</b>. Reach <b>100 influence</b> to rule Barnard\'s Star.' },
      8: { title: 'Coalsack', text: '<b>Coalsack</b>\'s black market and the <b>Barnard Drift</b>.' },
    },
    projects: {
      driver: { icon: "🏗", n: "Cinderling Gravity Catapult", d: "A gravity sling built from old mine elevators throws ore uphill to Forge.", fx: "Cinderling outpost output ×3" },
      beacons: { icon: "🔥", n: "Red Dwarf Lighthouses", d: "Giant flare-lamps that light safe lanes through the dim red system.", fx: "Travel 50% faster · fuel −30%" },
      fleet: { icon: "🤖", n: "Iron Golem Legion", d: "Retired mining mechs, re-armed and hungry for pirates. Two of them fly beside you in every fight.", fx: "Pirate danger −50% · 2 escort gunships in every fight" },
      elevator: { icon: "🔧", n: "Forge Skyhook", d: "A spinning tether that snatches cargo off Forge's frozen side and flings it into orbit.", fx: "All ore sells for +25% everywhere" },
      terraform: { icon: "🏭", n: "Rustfall Atmosphere Factories", d: "Thousand-kilometre chimneys pump air into Rustfall's canyons until it rains.", fx: "Rustfall pays ×2 for everything · Rust Brotherhood reputation +50" },
      gates: { icon: "⛏", n: "Mine-Shaft Wormholes", d: "The old miners dug so deep they punched through space-time. You just put up signs.", fx: "Instant, free travel anywhere" },
      ringstation: { icon: "⚗", n: "Halo Nanoforge", d: "Trillions of nanobots in Halo's rings build drones out of ring dust.", fx: "ALL drone income ×3" },
      dyson: { n: "Red Sun Harvester", d: "A dim star, a dense swarm: you squeeze every last photon out of Barnard's Star.", fx: "ALL income ×5" },
      nova: { n: "Core Breaker", d: "The biggest drill ever made. It does not mine planets — it opens them.", fx: "Lets you DESTROY planets (from the Star Map)" },
    },
  },
  sirius: {
    n: 'Sirius', star: 'white', companion: 'blue', rock: 3.38, enemy: 2.46, value: 1,
    boss: 'serpent', bossFleet: ['serpent', 'raider', 'raider'],
    signal: { title: 'Something lives in the flares', text: 'Ships near the <b>Flare Reach</b> report a shape swimming through the solar storms — a living ribbon of fire. They call it the <b>Solar Serpent</b>.' },
    gate: 'The Serpent unravels into sparks. Where it nested, an ancient ring <b>glows white-hot</b> and opens.',
    intro: 'Sirius burns twice as bright as Sol. Its asteroids are <b>armored</b>: heat-forged metal shells your laser barely scratches. Switch to the <b>Drill (Q)</b> to crack them.',
    factions: {
      tierra: { n: 'Sirian Directorate', c: '#9cc8ff' }, marte: { n: 'Canis Clans', c: '#ffb070' }, cinturon: { n: 'Iron Choir', c: '#c0c8d8' },
      exterior: { n: 'Lumen League', c: '#7affd8' }, piratas: { n: 'Dogstar Raiders', c: '#ff4d6d' },
    },
    locs: {
      luna: { n: 'Glint', station: 'Glint Base', tex: 'rock', col: ['#e0e8f0', '#50586a'], desc: 'A bright, glassy moon of Lumen.', field: { n: 'Glint Scree', ores: { iron: 4, ice: 2, titanium: 1.5, cobalt: 0.23 }, armored: 0.12 } },
      tierra: { n: 'Lumen', station: 'Radiant Port', tex: 'ocean', col: ['#a8f0ff', '#0a4a6a'], desc: 'A dazzling sea world under a white-hot sun. Pays well for metals.' },
      venus: { n: 'Mirage', station: 'Glass Spire', tex: 'gas', col: ['#fff0d0', '#a07040'], desc: 'A shimmering cloud world. Its cities crave luxury and ice.' },
      mercurio: { n: 'Anvil', station: 'Anvil Depot', tex: 'lava', col: ['#ffd070', '#3a1a05'], desc: 'A molten forge-world. Sunstone everywhere — and the heat.', field: { n: 'Molten Fields', ores: { iron: 2, titanium: 2, platinum: 1, sunstone: 1.5 }, armored: 0.25 } },
      marte: { n: 'Canis', station: 'Howl City', tex: 'rock', col: ['#e8b080', '#6a3a20'], desc: 'Dry plains and proud clans. Water is worth more than gold.' },
      ceres: { n: 'Ironheart', station: 'Choir Station', tex: 'rock', col: ['#b8c0cc', '#3a4048'], desc: 'Capital of the Iron Belt, where every rock wears armor.', field: { n: 'Iron Belt', ores: { nickel: 2, cobalt: 2, platinum: 2.5, iridium: 1.18 }, armored: 0.45 } },
      jupiter: { n: 'Argent', tex: 'gas', col: ['#e8eeff', '#4a5a8a'] },
      europa: { n: 'Frost', station: 'Frost Colony', tex: 'ice', col: ['#f0faff', '#6a8ab0'], desc: 'An ice moon of Argent. Pays well for iridium.' },
      troyanos: { station: 'Swarm Depot', desc: 'Argent\'s Trojan rocks, many of them armored.', field: { n: 'Argent Swarm', ores: { he3: 2.74, iridium: 3.2, ringpearl: 0.15 }, armored: 0.3 } },
      saturno: { n: 'Corona', tex: 'gas', col: ['#fff0b0', '#a07020'], station: 'Corona Depot', desc: 'A golden ringed giant lit like a lantern.', field: { n: 'Corona Rings', ores: { ice: 2, he3: 2.5, ringpearl: 3, exotic: 0.37 }, armored: 0.25 } },
      titan: { n: 'Haze', station: 'Hazeport', tex: 'titan', col: ['#f0e0c0', '#7a6a40'], desc: 'A hazy moon of Corona with huge refineries.' },
      pluton: { n: 'Dogstar', station: 'Raider Bazaar', tex: 'ice', col: ['#ffffff', '#7080a0'], desc: 'A small frozen world near the white dwarf Sirius B. The Raiders sell anything.' },
      kuiper: { n: 'Sirius Drift', station: 'Drift Depot', desc: 'Armored rocks drifting far from the glare.', field: { n: 'Sirius Drift', ores: { ice: 2.19, iridium: 2, exotic: 1.9, voidshard: 0.1 }, armored: 0.2 } },
      oort: { n: 'Flare Reach', station: 'Shade Outpost', col: ['#ffd070', '#4a2008'], desc: 'Where Sirius\' solar storms reach farthest. Something swims in the flares.', field: { n: 'Flare Reach', ores: { ice: 2, ringpearl: 2, exotic: 2, voidshard: 0.45 }, armored: 0.2 } },
    },
    unlocks: {
      0: { title: 'Glint' }, 3: { title: 'Anvil & Canis', text: '<b>Anvil</b> burns with <b>Sunstone</b> — buy <b>Shields</b>. <b>Canis</b> pays a fortune for ice. Many rocks here are <b>armored</b>: use the <b>Drill (Q)</b>.' },
      4: { title: 'The Iron Belt', text: '<b>Ironheart</b> and the <b>Iron Belt</b>: almost half the rocks are armored. Drill them! Pirates are fierce here.' },
      6: { title: 'Argent System', text: '<b>Frost</b> and the <b>Argent Swarm</b>. The <b>Scanner</b> reveals rich veins.' },
      7: { title: 'Corona & Influence', text: '<b>Haze</b> and the <b>Corona Rings</b>. <b>Invest</b> in stations (each level <b>+10% base income</b>) for income and <b>influence</b>. Reach <b>100 influence</b> to rule Sirius.' },
      8: { title: 'Dogstar', text: '<b>Dogstar</b>\'s Raider Bazaar and the <b>Sirius Drift</b>.' },
    },
    projects: {
      driver: { icon: "☀", n: "Glint Photon Sails", d: "Ore crates with mirror sails, pushed home by the light of Sirius itself.", fx: "Glint outpost output ×3" },
      beacons: { icon: "⚡", n: "Starlight Highways", d: "Laser-lit lanes that ships surf at impossible speeds.", fx: "Travel 50% faster · fuel −30%" },
      fleet: { icon: "🛡", n: "Mirror Knight Squadron", d: "Chrome gunships that bounce pirate fire right back at them.", fx: "Pirate danger −50% · 2 escort gunships in every fight" },
      elevator: { icon: "💡", n: "Lumen Light Fountain", d: "A column of solid light lifts cargo from the sea straight to orbit.", fx: "All ore sells for +25% everywhere" },
      terraform: { icon: "🌍", n: "Canis Sky-Seas", d: "Floating oceans hang in the sky above Canis, held up by magnetic fields.", fx: "Canis pays ×2 for everything · Canis Clans reputation +50" },
      gates: { n: "Light-Speed Mirror Gates", d: "Step into a mirror on one world, step out of another.", fx: "Instant, free travel anywhere" },
      ringstation: { icon: "🔥", n: "Corona Plasma Crown", d: "A crown of plasma refineries ringing Corona, hot enough to forge stars.", fx: "ALL drone income ×3" },
      dyson: { n: "Sirius Starlift", d: "You don't just catch starlight — you lift matter straight out of Sirius.", fx: "ALL income ×5" },
      nova: { icon: "☄", n: "White Dwarf Hammer", d: "You fling a chunk of white-dwarf matter at a planet. One teaspoon weighs as much as a mountain.", fx: "Lets you DESTROY planets (from the Star Map)" },
    },
  },
  tauceti: {
    n: 'Tau Ceti', star: 'sol', rock: 5.06, enemy: 3.32, value: 1, gift: 'tractor',
    boss: 'dreadnought', bossFleet: ['dreadnought', 'frigate'],
    signal: { title: 'The Toll Gate', text: 'The Mercantile\'s oldest secret: beyond the drift sits an ancient gate — and a <b>Merchant Dreadnought</b> that charges every ship a toll in blood. Nobody has ever paid it and lived.' },
    gate: 'The Dreadnought breaks apart and its escorts scatter. The Toll Gate is <b>free</b> — and it points deeper into the galaxy.',
    intro: 'Tau Ceti: the richest trade empire in the sector. The Mercantile gives you a <b>Tractor Pulse</b>: press <b>E</b> (or PULL) to pull every ore chunk around you. You keep it forever.',
    factions: {
      tierra: { n: 'Ceti Mercantile', c: '#ffd24a' }, marte: { n: 'Free Port Guild', c: '#ff9a6a' }, cinturon: { n: 'Ore Consortium', c: '#7ae0a0' },
      exterior: { n: 'Outer Exchange', c: '#8ab0ff' }, piratas: { n: 'Smugglers\' Ring', c: '#ff4d6d' },
    },
    locs: {
      luna: { n: 'Penny', station: 'Mint Base', tex: 'rock', col: ['#d8c8a0', '#4a4030'], desc: 'A dull moon of Aurum where fortunes begin.', field: { n: 'Coin Fields', ores: { iron: 4, ice: 3, titanium: 1, nickel: 0.87 } } },
      tierra: { n: 'Aurum', station: 'Grand Exchange', tex: 'ocean', col: ['#f0e0a0', '#1a5a6a'], desc: 'Capital of the richest trade empire in the sector.' },
      venus: { n: 'Silk', station: 'Silk Spire', tex: 'gas', col: ['#ffd0f0', '#7a3a6a'], desc: 'A rose-colored cloud world of luxury traders.' },
      mercurio: { n: 'Kiln', station: 'Kiln Depot', tex: 'lava', col: ['#ffa050', '#3a1005'], desc: 'A furnace world. Platinum and sunstone in the open.', field: { n: 'Kiln Flats', ores: { iron: 2, nickel: 2, platinum: 2, sunstone: 1.22 } } },
      marte: { n: 'Bazaar', station: 'Free Port', tex: 'rock', col: ['#e0a070', '#5a3010'], desc: 'A desert market world. Pays well for ice.' },
      ceres: { n: 'Ledger', station: 'Consortium Hall', tex: 'rock', col: ['#a8b0a0', '#3a4038'], desc: 'The Consortium\'s belt capital.', field: { n: 'Ledger Belt', ores: { cobalt: 1.5, nickel: 3, he3: 2, iridium: 1.39 } } },
      jupiter: { n: 'Treasury', tex: 'gas', col: ['#f0c070', '#6a4010'] },
      europa: { n: 'Vault', station: 'Vault Colony', tex: 'ice', col: ['#fff4e0', '#8a7050'], desc: 'An ice moon of Treasury. Pays well for iridium.' },
      troyanos: { station: 'Treasury Depot', desc: 'Treasury\'s Trojan swarm, rich in iridium.', field: { n: 'Treasury Swarm', ores: { he3: 1, sunstone: 1.5, iridium: 3.49 } } },
      saturno: { n: 'Crown', tex: 'gas', col: ['#e8e0ff', '#5a4a8a'], station: 'Crown Depot', desc: 'A lilac ringed giant, the jewel of Tau Ceti.', field: { n: 'Crown Rings', ores: { ice: 3, he3: 2, ringpearl: 3.2, exotic: 0.37 } } },
      titan: { n: 'Mint', station: 'Mintworks', tex: 'titan', col: ['#e0f0d0', '#5a7040'], desc: 'A green-hazed moon of Crown with huge refineries.' },
      pluton: { n: 'Freeport', station: 'Smugglers\' Den', tex: 'rock', col: ['#c0a0a0', '#302020'], desc: 'Where the Smugglers\' Ring trades everything the Mercantile won\'t.' },
      kuiper: { n: 'Ceti Drift', station: 'Drift Depot', desc: 'The cold outskirts of the empire.', field: { n: 'Ceti Drift', ores: { iridium: 3.39, ringpearl: 2, exotic: 1.7, voidshard: 0.08 } } },
      oort: { n: 'The Toll Gate', station: 'Tollhouse', col: ['#ffd24a', '#3a2a08'], desc: 'An ancient gate guarded by a Merchant Dreadnought.', field: { n: 'Toll Gate', ores: { ice: 3, he3: 2, exotic: 2.5, voidshard: 0.82 } } },
    },
    unlocks: {
      0: { title: 'Penny' }, 3: { title: 'Kiln & Bazaar', text: '<b>Kiln</b> is full of <b>Platinum</b> and <b>Sunstone</b> — buy <b>Shields</b>. <b>Bazaar</b> pays a fortune for ice. Use your <b>Tractor Pulse (E)</b> to grab everything.' },
      4: { title: 'The Ledger Belt', text: '<b>Ledger</b> and its belt: nickel, cobalt, iridium… and the hardest pirates yet.' },
      6: { title: 'Treasury System', text: '<b>Vault</b> and the <b>Treasury Swarm</b>. The <b>Scanner</b> reveals rich veins.' },
      7: { title: 'Crown & Influence', text: '<b>Mint</b> and the <b>Crown Rings</b>. <b>Invest</b> in stations (each level <b>+10% base income</b>) for income and <b>influence</b>. Reach <b>100 influence</b> to rule Tau Ceti.' },
      8: { title: 'Freeport', text: '<b>Freeport</b>\'s Smugglers\' Den and the <b>Ceti Drift</b>.' },
    },
    projects: {
      driver: { icon: "🤑", n: "Penny Coin Cannon", d: "Ore is minted into coins on Penny and fired straight into the Grand Exchange vault.", fx: "Penny outpost output ×3" },
      beacons: { icon: "📈", n: "Hyperlane Toll Network", d: "Faster lanes for everyone — and you collect every toll.", fx: "Travel 50% faster · fuel −30%" },
      fleet: { icon: "💼", n: "Mercenary Guild Armada", d: "The best pirates money can buy, now hunting the rest. Two ride with you in every fight.", fx: "Pirate danger −50% · 2 escort gunships in every fight" },
      elevator: { icon: "🏦", n: "Aurum Elevator Mall", d: "A space elevator with ten thousand shops. Shoppers ride it all the way to orbit.", fx: "All ore sells for +25% everywhere" },
      terraform: { icon: "🎉", n: "Bazaar Paradise Resort", d: "Seas, palm forests and casinos poured onto the desert. Tourists pay double for everything.", fx: "Bazaar pays ×2 for everything · Free Port Guild reputation +50" },
      gates: { n: "Instant Commerce Portals", d: "Order anything, anywhere — it arrives before you finish paying.", fx: "Instant, free travel anywhere" },
      ringstation: { icon: "🎆", n: "Crown Casino-Refinery", d: "A refinery hidden inside the galaxy's biggest casino. The drones never stop and neither do the slots.", fx: "ALL drone income ×3" },
      dyson: { icon: "🏦", n: "Ceti Star Bank", d: "You buy the star. Every photon it makes pays you interest.", fx: "ALL income ×5" },
      nova: { icon: "🤑", n: "Planetary Repossession Beam", d: "If a planet can't pay its debts, you take it. All of it.", fx: "Lets you DESTROY planets (from the Star Map)" },
    },
  },
});

// systems 6–8
Object.assign(SYSTEMS, {
 "eridani": {
  "n": "Epsilon Eridani",
  "star": "orange",
  "rock": 4.48,
  "enemy": 3.4,
  "value": 1,
  "boss": "citadel",
  "bossFleet": [
   "citadel",
   "raider",
   "raider"
  ],
  "signal": {
   "title": "A fortress in the dust",
   "text": "Deep inside the <b>Dust Veil</b> a pirate warlord built the <b>Dust Citadel</b> — a fortress that sprays fire in every direction. It sits right on top of an ancient gate."
  },
  "gate": "The Citadel cracks open and the dust settles. Beneath its foundations, an ancient ring <b>flickers to life</b>.",
  "intro": "Epsilon Eridani hides inside a huge <b>dust disk</b>. Many of its asteroids are <b>volatile</b>: they glow with magma cracks and <b>explode</b> when broken — cracking every rock around them. Set off chain reactions, but keep your distance!",
  "factions": {
   "tierra": {
    "n": "Veil Assembly",
    "c": "#ffb070"
   },
   "marte": {
    "n": "Ash Nomads",
    "c": "#e09060"
   },
   "cinturon": {
    "n": "Blasting Guild",
    "c": "#ffd060"
   },
   "exterior": {
    "n": "Haze Compact",
    "c": "#a0c0ff"
   },
   "piratas": {
    "n": "Dust Corsairs",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Kindle",
    "station": "Spark Base",
    "tex": "rock",
    "col": [
     "#c8b090",
     "#40342a"
    ],
    "desc": "A dusty moon of Hearth, glittering with volatile rocks.",
    "field": {
     "n": "Spark Fields",
     "ores": {
      "iron": 4,
      "ice": 2.5,
      "cobalt": 0.34,
      "titanium": 1
     },
     "explosive": 0.12
    }
   },
   "tierra": {
    "n": "Hearth",
    "station": "Veil Port",
    "tex": "ocean",
    "col": [
     "#e0c080",
     "#2a4a5a"
    ],
    "desc": "A warm, hazy ocean world under an amber sun."
   },
   "venus": {
    "n": "Sable",
    "station": "Velvet Spire",
    "tex": "gas",
    "col": [
     "#d0a0c0",
     "#4a2a40"
    ],
    "desc": "A dark velvet cloud world of wealthy nomads."
   },
   "mercurio": {
    "n": "Fuse",
    "station": "Fuse Depot",
    "tex": "lava",
    "col": [
     "#ffa040",
     "#3a1004"
    ],
    "desc": "A world that crackles with heat and volatile ore.",
    "field": {
     "n": "Fuse Flats",
     "ores": {
      "iron": 2,
      "nickel": 2,
      "sunstone": 2.69,
      "titanium": 1.5
     },
     "explosive": 0.25
    }
   },
   "marte": {
    "n": "Ashland",
    "station": "Cinder Gate",
    "tex": "rock",
    "col": [
     "#c89070",
     "#4a2818"
    ],
    "desc": "Grey ash deserts and proud nomads. Pays well for ice."
   },
   "ceres": {
    "n": "Powderkeg",
    "station": "Blasting Hall",
    "tex": "rock",
    "col": [
     "#b09878",
     "#3a3026"
    ],
    "desc": "The Blasting Guild's capital. Everything here goes boom.",
    "field": {
     "n": "Powder Belt",
     "ores": {
      "titanium": 1.5,
      "he3": 2.5,
      "platinum": 2.5,
      "iridium": 1.18
     },
     "explosive": 0.35
    }
   },
   "jupiter": {
    "n": "Smolder",
    "tex": "gas",
    "col": [
     "#ffb880",
     "#7a3a20"
    ]
   },
   "europa": {
    "n": "Cinderglass",
    "station": "Glass Colony",
    "tex": "ice",
    "col": [
     "#ffe8d8",
     "#8a5a48"
    ],
    "desc": "An ice moon dusted with soot. Pays well for iridium."
   },
   "troyanos": {
    "station": "Smolder Depot",
    "desc": "Smolder's Trojan rocks, many of them volatile.",
    "field": {
     "n": "Smolder Swarm",
     "ores": {
      "platinum": 4.13,
      "iridium": 3,
      "ringpearl": 0.3
     },
     "explosive": 0.25
    }
   },
   "saturno": {
    "n": "Veil",
    "station": "Veil Ring Depot",
    "tex": "gas",
    "col": [
     "#e8d0b0",
     "#6a5038"
    ],
    "desc": "A ringed giant half hidden in the dust disk.",
    "field": {
     "n": "Veil Rings",
     "ores": {
      "ice": 2,
      "he3": 3.42,
      "ringpearl": 3,
      "exotic": 0.5
     },
     "explosive": 0.2
    }
   },
   "titan": {
    "n": "Murk",
    "station": "Murkworks",
    "tex": "titan",
    "col": [
     "#c0b090",
     "#504430"
    ],
    "desc": "A murky moon of Veil with vast refineries."
   },
   "pluton": {
    "n": "Snuff",
    "station": "Corsair Den",
    "tex": "rock",
    "col": [
     "#908070",
     "#201814"
    ],
    "desc": "A soot-black rock where the Dust Corsairs trade."
   },
   "kuiper": {
    "n": "The Dust Veil",
    "station": "Veil Depot",
    "desc": "The thick outer dust disk. Volatile rocks drift everywhere.",
    "field": {
     "n": "The Dust Veil",
     "ores": {
      "ice": 2.91,
      "ringpearl": 2,
      "exotic": 1.8,
      "voidshard": 0.1
     },
     "explosive": 0.25
    }
   },
   "oort": {
    "n": "Citadel Reach",
    "station": "Last Spark Outpost",
    "col": [
     "#ffa860",
     "#3a1a08"
    ],
    "desc": "The heart of the dust, where the Citadel stands guard.",
    "field": {
     "n": "Citadel Reach",
     "ores": {
      "ice": 3,
      "iridium": 2,
      "exotic": 2,
      "voidshard": 0.81
     },
     "explosive": 0.2
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Kindle"
   },
   "3": {
    "title": "Fuse & Ashland",
    "text": "<b>Fuse</b> burns with <b>Sunstone</b> — buy <b>Shields</b>. <b>Ashland</b> pays a fortune for ice. Watch for <b>volatile rocks</b>: they explode when broken!"
   },
   "4": {
    "title": "The Powder Belt",
    "text": "<b>Powderkeg</b> and the <b>Powder Belt</b>: a third of the rocks are volatile. Break one in a cluster and watch the chain reaction."
   },
   "6": {
    "title": "Smolder System",
    "text": "<b>Cinderglass</b> and the <b>Smolder Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Veil & Influence",
    "text": "<b>Murk</b> and the <b>Veil Rings</b>. <b>Invest</b> in stations (each level <b>+10% base income</b>) for income and <b>influence</b>. Reach <b>100 influence</b> to rule Epsilon Eridani."
   },
   "8": {
    "title": "Snuff",
    "text": "<b>Snuff</b>'s Corsair Den and <b>the Dust Veil</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🏗",
    "n": "Dustline Conveyor",
    "d": "A conveyor belt 400,000 km long, running through the dust disk straight to Hearth.",
    "fx": "Kindle outpost output ×3"
   },
   "beacons": {
    "icon": "💡",
    "n": "Dust-Piercing Lanterns",
    "d": "Neutrino lamps that see straight through the dust clouds.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "🏴",
    "n": "Sandstorm Corsairs",
    "d": "Ex-pirates in dust-camouflaged gunships, now on your payroll. Two fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "⬆",
    "n": "Gravity-Free Zone",
    "d": "You switch off gravity over a whole city. Cargo just floats up to orbit.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Planet Wash",
    "d": "A thousand comets scrub the ash off Ashland and leave a blue world behind.",
    "fx": "Ashland pays ×2 for everything · Ash Nomads reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Dust Tunnels",
    "d": "Wormholes hidden inside the dust clouds — only your pilots know the way.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "🏭",
    "n": "Disk Harvester Wheel",
    "d": "A wheel the size of a moon rolls through the dust disk, scooping up ore.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Dusty Dyson Veil",
    "d": "You turn the entire dust disk into one giant solar panel.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Gravity Grenade",
    "d": "A pocket black hole, thrown like a grenade. Planets fold in on themselves.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 },
 "vega": {
  "n": "Vega",
  "star": "blue",
  "rock": 6.05,
  "enemy": 4.1,
  "value": 1,
  "gift": "overdrive",
  "comets": 3,
  "boss": "leviathan",
  "bossFleet": [
   "leviathan",
   "raider",
   "raider"
  ],
  "signal": {
   "title": "Something huge in the ice",
   "text": "Comet herders swear a creature the size of a station swims between the frozen moons — the <b>Ice Leviathan</b>. It rams ships. It guards the gate."
  },
  "gate": "The Leviathan shatters into a blizzard of ice. Where it lived, an ancient ring <b>thaws and opens</b>.",
  "intro": "Vega: a blue star spinning so fast it's squashed flat. <b>Comets</b> rain through every field (3× as many). The comet herders give you <b>Overdrive</b>: press <b>R</b> (or BOOST) for 8 s of triple cutting power and speed — perfect for catching comets. You keep it forever.",
  "factions": {
   "tierra": {
    "n": "Azure Directorate",
    "c": "#7ab8ff"
   },
   "marte": {
    "n": "Frost Clans",
    "c": "#a8e0ff"
   },
   "cinturon": {
    "n": "Comet Herders",
    "c": "#bff6ff"
   },
   "exterior": {
    "n": "Glacier League",
    "c": "#9a9aff"
   },
   "piratas": {
    "n": "Icebreakers",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Sleet",
    "station": "Snowcap Base",
    "tex": "ice",
    "col": [
     "#e8f4ff",
     "#5a7090"
    ],
    "desc": "A frozen moon of Azure, swept by comets.",
    "field": {
     "n": "Sleet Drifts",
     "ores": {
      "iron": 3.5,
      "ice": 4,
      "titanium": 1,
      "he3": 0.31
     }
    }
   },
   "tierra": {
    "n": "Azure",
    "station": "Blue Harbor",
    "tex": "ocean",
    "col": [
     "#b0e0ff",
     "#0a3a7a"
    ],
    "desc": "A deep blue ocean world under a blinding blue sun."
   },
   "venus": {
    "n": "Opal",
    "station": "Opal Spire",
    "tex": "gas",
    "col": [
     "#e8e0ff",
     "#5a5a9a"
    ],
    "desc": "An iridescent cloud world of wealthy collectors."
   },
   "mercurio": {
    "n": "Glare",
    "station": "Glare Depot",
    "tex": "lava",
    "col": [
     "#a0d0ff",
     "#101a3a"
    ],
    "desc": "A world melted by blue starlight. Platinum lies everywhere.",
    "field": {
     "n": "Glare Plains",
     "ores": {
      "ice": 1,
      "titanium": 2,
      "cobalt": 2,
      "platinum": 6
     }
    }
   },
   "marte": {
    "n": "Rime",
    "station": "Frostgate",
    "tex": "ice",
    "col": [
     "#d0e8ff",
     "#3a5070"
    ],
    "desc": "A frozen desert. Strangely, it still pays well for ice."
   },
   "ceres": {
    "n": "Herdstone",
    "station": "Comet Ranch",
    "tex": "rock",
    "col": [
     "#a8b8c8",
     "#303844"
    ],
    "desc": "The comet herders' capital.",
    "field": {
     "n": "Herd Belt",
     "ores": {
      "ice": 2,
      "nickel": 2,
      "he3": 2.5,
      "iridium": 1.59
     }
    }
   },
   "jupiter": {
    "n": "Frostmaw",
    "tex": "gas",
    "col": [
     "#c0e8ff",
     "#2a4a8a"
    ]
   },
   "europa": {
    "n": "Shiver",
    "station": "Shiver Colony",
    "tex": "ice",
    "col": [
     "#f0fbff",
     "#7090b0"
    ],
    "desc": "An ice moon of Frostmaw. Pays well for iridium."
   },
   "troyanos": {
    "station": "Frostmaw Depot",
    "desc": "Frostmaw's Trojans, glittering with ice.",
    "field": {
     "n": "Frostmaw Swarm",
     "ores": {
      "ice": 2,
      "he3": 2,
      "iridium": 7.27
     }
    }
   },
   "saturno": {
    "n": "Halcyon Ice",
    "station": "Glacier Depot",
    "tex": "gas",
    "col": [
     "#e0f0ff",
     "#4a6aa0"
    ],
    "desc": "A pale blue ringed giant whose rings are mostly comets.",
    "field": {
     "n": "Comet Rings",
     "ores": {
      "ice": 4,
      "he3": 2,
      "ringpearl": 3,
      "exotic": 0.47
     }
    }
   },
   "titan": {
    "n": "Slush",
    "station": "Slushworks",
    "tex": "titan",
    "col": [
     "#d0e0f0",
     "#506070"
    ],
    "desc": "A slushy moon with enormous refineries."
   },
   "pluton": {
    "n": "Breakwater",
    "station": "Icebreaker Market",
    "tex": "ice",
    "col": [
     "#ffffff",
     "#6070a0"
    ],
    "desc": "Where the Icebreakers sell what they steal."
   },
   "kuiper": {
    "n": "Vega Drift",
    "station": "Drift Depot",
    "desc": "Endless frozen comets at the edge of Vega's glare.",
    "field": {
     "n": "Vega Drift",
     "ores": {
      "ice": 3.34,
      "ringpearl": 2,
      "exotic": 2,
      "voidshard": 0.1
     }
    }
   },
   "oort": {
    "n": "The Deep Freeze",
    "station": "Thaw Outpost",
    "col": [
     "#bfefff",
     "#0a2a4a"
    ],
    "desc": "A frozen sea of comets where the Leviathan hunts.",
    "field": {
     "n": "The Deep Freeze",
     "ores": {
      "ice": 4,
      "ringpearl": 2,
      "exotic": 2,
      "voidshard": 0.87
     }
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Sleet"
   },
   "3": {
    "title": "Glare & Rime",
    "text": "<b>Glare</b> is covered in <b>Platinum</b> — buy <b>Shields</b>. <b>Rime</b> pays well for ice. Comets everywhere: use <b>Overdrive (R)</b> to catch them!"
   },
   "4": {
    "title": "The Herd Belt",
    "text": "<b>Herdstone</b> and the <b>Herd Belt</b>, where the comet herders live. The Icebreaker pirates are fierce."
   },
   "6": {
    "title": "Frostmaw System",
    "text": "<b>Shiver</b> and the <b>Frostmaw Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Halcyon Ice & Influence",
    "text": "<b>Slush</b> and the <b>Comet Rings</b>. <b>Invest</b> in stations (each level <b>+10% base income</b>) for income and <b>influence</b>. Reach <b>100 influence</b> to rule Vega."
   },
   "8": {
    "title": "Breakwater",
    "text": "<b>Breakwater</b>'s Icebreaker Market and the <b>Vega Drift</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "☄",
    "n": "Comet Express",
    "d": "You hitch ore containers to passing comets and let them deliver.",
    "fx": "Sleet outpost output ×3"
   },
   "beacons": {
    "icon": "🌀",
    "n": "Hyperspin Lanes",
    "d": "Vega spins so fast its gravity flings ships along these lanes.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "🛡",
    "n": "Ice Phantom Wing",
    "d": "Gunships cloaked in ice. Pirates never see them coming — two fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "🚀",
    "n": "Cryo Cannon",
    "d": "Cargo is frozen into ice bullets and shot straight into orbit.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🔥",
    "n": "Thaw Engine",
    "d": "You melt a frozen world into a garden in a single afternoon.",
    "fx": "Rime pays ×2 for everything · Frost Clans reputation +50"
   },
   "gates": {
    "icon": "⚛",
    "n": "Frozen-Time Gates",
    "d": "Gates that freeze time during the trip: you arrive before you left.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Comet Ring Ranch",
    "d": "You herd comets into the giant's rings and farm them for ore.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Blue Star Siphon",
    "d": "Vega's light is so fierce you just put up a straw.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "☄",
    "n": "Comet Bombardment",
    "d": "You redirect every comet in the system at a single planet.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 },
 "altair": {
  "n": "Altair",
  "star": "white",
  "rock": 8.17,
  "enemy": 4.9,
  "value": 1,
  "gift": "charges",
  "boss": "pirateking",
  "bossFleet": [
   "pirateking",
   "corsair",
   "corsair"
  ],
  "signal": {
   "title": "The Pirate King",
   "text": "Every pirate in Altair answers to one captain: the <b>Pirate King</b>. His flagship guards the old gate at <b>Skull Harbor</b> — and he calls his raiders the moment you show up."
  },
  "gate": "The King's flagship goes down in flames and his fleet scatters. The gate at Skull Harbor is <b>yours</b>.",
  "intro": "Altair is a <b>pirate empire</b>: raids everywhere, and loot to match. A defector gives you <b>Mining Charges</b>: press <b>F</b> (or BOMB) to drop a charge that blows up 1.2 s later, cracking every rock around it — and hurting pirates too. You keep them forever.",
  "factions": {
   "tierra": {
    "n": "Altair Free Cities",
    "c": "#9ad8ff"
   },
   "marte": {
    "n": "Iron Wardens",
    "c": "#c8a070"
   },
   "cinturon": {
    "n": "Salvage Brotherhood",
    "c": "#b0d080"
   },
   "exterior": {
    "n": "Far Reach Alliance",
    "c": "#c0a0ff"
   },
   "piratas": {
    "n": "The Pirate Crown",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Driftwood",
    "station": "Last Chance Base",
    "tex": "rock",
    "col": [
     "#b8b0a0",
     "#3a3630"
    ],
    "desc": "A battered moon of Haven, scarred by raids.",
    "field": {
     "n": "Driftwood Scrap",
     "ores": {
      "iron": 4.5,
      "titanium": 1.5,
      "ice": 2,
      "nickel": 0.59
     }
    },
    "danger": 0.1
   },
   "tierra": {
    "n": "Haven",
    "station": "Free Harbor",
    "tex": "ocean",
    "col": [
     "#90d8c0",
     "#0a3a4a"
    ],
    "desc": "The last free capital in a pirate system.",
    "danger": 0.08
   },
   "venus": {
    "n": "Gilded",
    "station": "Treasure Spire",
    "tex": "gas",
    "col": [
     "#ffe0a0",
     "#7a5020"
    ],
    "desc": "A golden cloud world where pirates spend their loot."
   },
   "mercurio": {
    "n": "Brimstone Reef",
    "station": "Reef Depot",
    "tex": "lava",
    "col": [
     "#ff9050",
     "#300a04"
    ],
    "desc": "A burning reef of rock. Sunstone and pirates.",
    "field": {
     "n": "Burning Reef",
     "ores": {
      "iron": 1.5,
      "cobalt": 2,
      "platinum": 1.5,
      "sunstone": 0.91
     }
    }
   },
   "marte": {
    "n": "Bulwark",
    "station": "Warden Fort",
    "tex": "rock",
    "col": [
     "#c09878",
     "#3a2a1a"
    ],
    "desc": "A fortress world that has never fallen to the pirates. Pays well for ice."
   },
   "ceres": {
    "n": "Scrapheap",
    "station": "Salvage Hall",
    "tex": "rock",
    "col": [
     "#a0a088",
     "#30302a"
    ],
    "desc": "Salvagers live on what the pirates leave behind.",
    "field": {
     "n": "Wreck Belt",
     "ores": {
      "cobalt": 2,
      "platinum": 2,
      "sunstone": 1.5,
      "iridium": 0.53
     }
    }
   },
   "jupiter": {
    "n": "Leviathan's Eye",
    "tex": "gas",
    "col": [
     "#d0c0ff",
     "#3a2a7a"
    ]
   },
   "europa": {
    "n": "Cove",
    "station": "Cove Colony",
    "tex": "ice",
    "col": [
     "#e8f0ff",
     "#607090"
    ],
    "desc": "A hidden ice moon. Pays well for iridium."
   },
   "troyanos": {
    "station": "Ambush Depot",
    "desc": "Trojan rocks crawling with pirate nests.",
    "field": {
     "n": "Ambush Alley",
     "ores": {
      "sunstone": 4.36,
      "iridium": 3,
      "ringpearl": 0.2
     }
    }
   },
   "saturno": {
    "n": "Skullring",
    "station": "Ring Depot",
    "tex": "gas",
    "col": [
     "#e0c8c8",
     "#6a3a3a"
    ],
    "desc": "A ringed giant whose rings hide a thousand pirate bases.",
    "field": {
     "n": "Skull Rings",
     "ores": {
      "he3": 3,
      "ringpearl": 2.5,
      "ice": 2,
      "exotic": 0.47
     }
    }
   },
   "titan": {
    "n": "Rumhaze",
    "station": "Rum Refinery",
    "tex": "titan",
    "col": [
     "#e0b080",
     "#6a4020"
    ],
    "desc": "A boozy, foggy moon with huge refineries."
   },
   "pluton": {
    "n": "Tortuga",
    "station": "Crown Market",
    "tex": "rock",
    "col": [
     "#d08080",
     "#301010"
    ],
    "desc": "The capital of the Pirate Crown. Everything is for sale."
   },
   "kuiper": {
    "n": "Plunder Drift",
    "station": "Drift Depot",
    "desc": "Where pirates hide their stolen ore.",
    "field": {
     "n": "Plunder Drift",
     "ores": {
      "iridium": 4.99,
      "exotic": 2,
      "ringpearl": 1.5,
      "voidshard": 0.1
     }
    }
   },
   "oort": {
    "n": "Skull Harbor",
    "station": "Lookout Post",
    "col": [
     "#ff8080",
     "#3a0a0a"
    ],
    "desc": "The Pirate King's harbor, built around an ancient gate.",
    "field": {
     "n": "Skull Harbor",
     "ores": {
      "ice": 3,
      "exotic": 2.5,
      "ringpearl": 1.5,
      "voidshard": 0.44
     }
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Driftwood"
   },
   "3": {
    "title": "Brimstone Reef & Bulwark",
    "text": "<b>Brimstone Reef</b> burns with <b>Sunstone</b> — buy <b>Shields</b>. <b>Bulwark</b> pays a fortune for ice. Use your <b>Mining Charges (F)</b> on big clusters!"
   },
   "4": {
    "title": "The Wreck Belt",
    "text": "<b>Scrapheap</b> and the <b>Wreck Belt</b>. Pirates everywhere — and their loot is worth it."
   },
   "6": {
    "title": "Leviathan's Eye",
    "text": "<b>Cove</b> and <b>Ambush Alley</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Skullring & Influence",
    "text": "<b>Rumhaze</b> and the <b>Skull Rings</b>. <b>Invest</b> in stations (each level <b>+10% base income</b>) for income and <b>influence</b>. Reach <b>100 influence</b> to rule Altair."
   },
   "8": {
    "title": "Tortuga",
    "text": "<b>Tortuga</b>, capital of the Pirate Crown, and the <b>Plunder Drift</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🏴",
    "n": "Smuggler's Chute",
    "d": "A secret railgun the pirates built to move loot. Now it moves your ore.",
    "fx": "Driftwood outpost output ×3"
   },
   "beacons": {
    "icon": "📡",
    "n": "Black Flag Network",
    "d": "Pirate radio towers that know every lane — and every ambush.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "⚔",
    "n": "Turncoat Armada",
    "d": "Half the pirate fleet switches sides for the right price. Two ships fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "🏗",
    "n": "Plunder Lift",
    "d": "A cargo lift made of captured pirate ships welded end to end.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Hideout Gardens",
    "d": "You turn Bulwark's grim fortress plains into a jungle resort.",
    "fx": "Bulwark pays ×2 for everything · Iron Wardens reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Ghost Gates",
    "d": "Stolen gates hidden in nebula pockets. Nobody knows where they lead — except you.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "☠",
    "n": "Skull Ring Shipyard",
    "d": "A pirate shipyard in the rings, now building mining drones for you.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "👑",
    "n": "Crown of Altair",
    "d": "A Dyson swarm shaped like a pirate crown. Very subtle.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Doomsday Broadside",
    "d": "Every captured pirate cannon in the system, firing at once.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 }
});

// systems 9–11
Object.assign(SYSTEMS, {
 "kepler": {
  "n": "Kepler",
  "star": "sol",
  "rock": 9.4,
  "enemy": 5.5,
  "value": 1,
  "boss": "kraken",
  "bossFleet": [
   "kraken",
   "raider",
   "raider"
  ],
  "signal": {
   "title": "Something in the trench",
   "text": "Fishing crews keep losing ships near the <b>Kraken's Trench</b>. The black box of the last one recorded a single word: <b>tentacles</b>. Whatever lives down there is sitting on the ancient gate."
  },
  "gate": "The Kraken sinks into the dark, trailing glowing ink. At the bottom of the trench, an ancient ring <b>opens like an eye</b>.",
  "intro": "Kepler is a system of <b>ocean worlds</b> — and its asteroids are <b>alive</b>. <b>Living rocks</b> glow with spots and swim around; when your laser stings them they <b>flee</b>. Chase them down (Overdrive helps!) or use the <b>Tractor Pulse (E)</b> to calm them for a few seconds. They drop <b>60% more ore</b>.",
  "factions": {
   "tierra": {
    "n": "Tidal Republic",
    "c": "#6fd8e0"
   },
   "marte": {
    "n": "Salt Clans",
    "c": "#e0d0a0"
   },
   "cinturon": {
    "n": "Reef Keepers",
    "c": "#7fffb0"
   },
   "exterior": {
    "n": "Deepwater Pact",
    "c": "#7a9aff"
   },
   "piratas": {
    "n": "Black Tide",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Shoal",
    "station": "Shoal Base",
    "tex": "ice",
    "col": [
     "#c8f0f0",
     "#2a5a6a"
    ],
    "desc": "A wet little moon of Thalassa. Its rocks swim in schools.",
    "field": {
     "n": "Shoal Shallows",
     "ores": {
      "iron": 3,
      "ice": 3,
      "nickel": 1,
      "cobalt": 0.11
     },
     "living": 0.12
    }
   },
   "tierra": {
    "n": "Thalassa",
    "station": "Deepwater Port",
    "tex": "ocean",
    "col": [
     "#6fd0ff",
     "#043a6a"
    ],
    "desc": "A world with no land at all. The cities float."
   },
   "venus": {
    "n": "Pearlhaze",
    "station": "Nacre Spire",
    "tex": "gas",
    "col": [
     "#f0e8f8",
     "#7a6a9a"
    ],
    "desc": "A shimmering cloud world. Its people love pearls."
   },
   "mercurio": {
    "n": "Scald",
    "station": "Steam Vents Depot",
    "tex": "lava",
    "col": [
     "#ffb070",
     "#2a3a4a"
    ],
    "desc": "Boiling seas and steam geysers. Sunstone under the foam.",
    "field": {
     "n": "Scald Geysers",
     "ores": {
      "titanium": 2,
      "nickel": 2,
      "platinum": 1.5,
      "sunstone": 1.22
     },
     "living": 0.15
    }
   },
   "marte": {
    "n": "Saltflat",
    "station": "Salt Gate",
    "tex": "rock",
    "col": [
     "#e8e0c8",
     "#6a5a40"
    ],
    "desc": "The only dry planet in Kepler — and it's dying of thirst. Pays well for ice."
   },
   "ceres": {
    "n": "Reef",
    "station": "Reefhold",
    "tex": "rock",
    "col": [
     "#90c8a8",
     "#24443a"
    ],
    "desc": "The Reef Keepers' home, built inside a giant living reef.",
    "field": {
     "n": "The Living Reef",
     "ores": {
      "nickel": 2,
      "cobalt": 2,
      "platinum": 1,
      "ringpearl": 0.35
     },
     "living": 0.3
    }
   },
   "jupiter": {
    "n": "Maelstrom",
    "tex": "gas",
    "col": [
     "#a0e0f0",
     "#1a4a7a"
    ]
   },
   "europa": {
    "n": "Undertow",
    "station": "Undertow Colony",
    "tex": "ice",
    "col": [
     "#e0f8ff",
     "#4a7a9a"
    ],
    "desc": "An ice moon over a warm hidden ocean. Pays well for iridium."
   },
   "troyanos": {
    "station": "Maelstrom Depot",
    "desc": "Maelstrom's Trojans, where living rocks gather to feed.",
    "field": {
     "n": "Maelstrom Shoals",
     "ores": {
      "he3": 2,
      "platinum": 1,
      "iridium": 2,
      "ringpearl": 0.36
     },
     "living": 0.22
    }
   },
   "saturno": {
    "n": "Coralring",
    "station": "Coral Ring Depot",
    "tex": "gas",
    "col": [
     "#f0d8c8",
     "#7a5a6a"
    ],
    "desc": "A giant whose rings are made of something like coral.",
    "field": {
     "n": "Coral Rings",
     "ores": {
      "ice": 2,
      "ringpearl": 3,
      "iridium": 1,
      "exotic": 0.07
     },
     "living": 0.22
    }
   },
   "titan": {
    "n": "Kelpmire",
    "station": "Kelpworks",
    "tex": "titan",
    "col": [
     "#a0c890",
     "#2a4a2a"
    ],
    "desc": "A moon covered in floating kelp forests and refineries."
   },
   "pluton": {
    "n": "Wreckreef",
    "station": "Smuggler's Grotto",
    "tex": "rock",
    "col": [
     "#7a8a8a",
     "#1a2a2a"
    ],
    "desc": "A reef of sunken ships where the Black Tide trades."
   },
   "kuiper": {
    "n": "The Abyss",
    "station": "Abyss Buoy",
    "desc": "A dark sea of rock at the edge of the system. Big things swim here.",
    "field": {
     "n": "The Abyss",
     "ores": {
      "ice": 1,
      "ringpearl": 3,
      "iridium": 1,
      "exotic": 2.12
     },
     "living": 0.2
    }
   },
   "oort": {
    "n": "Kraken's Trench",
    "station": "Last Buoy",
    "col": [
     "#7fe0e0",
     "#0a2a3a"
    ],
    "desc": "A trench in space. Something with tentacles lives at the bottom.",
    "field": {
     "n": "Kraken's Trench",
     "ores": {
      "ice": 2,
      "ringpearl": 2,
      "exotic": 2,
      "voidshard": 0.45
     },
     "living": 0.15
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Shoal"
   },
   "3": {
    "title": "Scald & Saltflat",
    "text": "<b>Scald</b> boils with <b>Sunstone</b> — buy <b>Shields</b>. <b>Saltflat</b> pays a fortune for ice. Some rocks here are <b>alive</b>: they flee when you laser them, but drop 60% more ore."
   },
   "4": {
    "title": "The Living Reef",
    "text": "<b>Reef</b> and <b>the Living Reef</b>: almost a third of the rocks swim. Calm them with the <b>Tractor Pulse (E)</b> and cut them while they're still."
   },
   "6": {
    "title": "Maelstrom System",
    "text": "<b>Undertow</b> and the <b>Maelstrom Shoals</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Coralring & Influence",
    "text": "<b>Kelpmire</b> and the <b>Coral Rings</b>. <b>Invest</b> for <b>+10% income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule Kepler."
   },
   "8": {
    "title": "Wreckreef",
    "text": "<b>Wreckreef</b>'s Smuggler's Grotto and <b>the Abyss</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🚀",
    "n": "Tamed Rock Herd",
    "d": "You whistle, and a herd of living rocks swims your ore home all by itself.",
    "fx": "Shoal outpost output ×3"
   },
   "beacons": {
    "icon": "💡",
    "n": "Glowing Plankton Lanes",
    "d": "You seed the trade lanes with glowing plankton. Ships just follow the lights.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "🛡",
    "n": "Coral Gunship Pod",
    "d": "Living gunships grown from reef coral. They hunt in pairs — two fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "🗼",
    "n": "Geyser Launcher",
    "d": "You cap the biggest geyser on Scald. Every few minutes it blasts a full cargo hold into orbit.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Ocean Drop",
    "d": "You drop an entire ocean on Saltflat. It arrives as one very large, very wet comet.",
    "fx": "Saltflat pays ×2 for everything · Salt Clans reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Whirlpool Gates",
    "d": "You teach the Maelstrom to spin wormholes. Dive in, pop out anywhere.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Coral Ring Reef",
    "d": "You grow a living reef all the way around Coralring. It eats asteroids and spits out pure ore.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Sunlit Sea",
    "d": "A shell of water around the star: one ocean the size of a solar system, glowing with light.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Tsunami Cannon",
    "d": "You fire a wave of compressed ocean. It does not stop at the planet's surface.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 },
 "rigel": {
  "n": "Rigel",
  "star": "blue",
  "rock": 10.9,
  "enemy": 6.1,
  "value": 1,
  "gift": "deepscan",
  "boss": "radiant",
  "bossFleet": [
   "radiant",
   "corsair",
   "corsair"
  ],
  "signal": {
   "title": "A giant made of light",
   "text": "Something stands in the <b>Radiant Rift</b> — a crystal giant that burns brighter than the star. Ships that get close see a thin blue line… and then nothing. <b>Watch for the line and dodge.</b>"
  },
  "gate": "The Radiant Titan cracks and its light pours out like water. In the glare, an ancient ring <b>focuses into a gate</b>.",
  "intro": "Rigel is a <b>blue supergiant</b>, so bright it lights up the whole sky. Its heat bakes hidden <b>geodes</b> inside some asteroids. The Geode Cutters give you the <b>Deep Scanner</b>: press <b>C</b> (or SCAN) to send out a wave that shows every geode nearby. Break a geode for a <b>huge load of the field's best ore</b>. You keep it forever.",
  "factions": {
   "tierra": {
    "n": "Rigel Concord",
    "c": "#8ab8ff"
   },
   "marte": {
    "n": "Prism Guild",
    "c": "#c0a0ff"
   },
   "cinturon": {
    "n": "Geode Cutters",
    "c": "#7fe0ff"
   },
   "exterior": {
    "n": "Halo Union",
    "c": "#b0c8ff"
   },
   "piratas": {
    "n": "Glare Raiders",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Glint",
    "station": "Glint Base",
    "tex": "ice",
    "col": [
     "#e0f0ff",
     "#3a5a8a"
    ],
    "desc": "A frost moon that sparkles like a mirror ball.",
    "field": {
     "n": "Glint Fields",
     "ores": {
      "iron": 4,
      "ice": 2,
      "titanium": 2.77
     },
     "geodes": 0.06
    }
   },
   "tierra": {
    "n": "Bluehaven",
    "station": "Halo Harbor",
    "tex": "ocean",
    "col": [
     "#8ad0ff",
     "#0a2a6a"
    ],
    "desc": "A blue world under a blue sun. Everyone wears sunglasses."
   },
   "venus": {
    "n": "Sapphire",
    "station": "Sapphire Spire",
    "tex": "gas",
    "col": [
     "#a0b8ff",
     "#2a2a8a"
    ],
    "desc": "A deep blue cloud world, rich and proud."
   },
   "mercurio": {
    "n": "Searlight",
    "station": "Flare Depot",
    "tex": "lava",
    "col": [
     "#d0e8ff",
     "#1a2a5a"
    ],
    "desc": "Scorched white by Rigel. Platinum and geodes everywhere.",
    "field": {
     "n": "Searing Plains",
     "ores": {
      "titanium": 1,
      "cobalt": 1,
      "platinum": 2,
      "sunstone": 0.29
     },
     "geodes": 0.1
    }
   },
   "marte": {
    "n": "Prism",
    "station": "Prism Gate",
    "tex": "rock",
    "col": [
     "#c8b8e8",
     "#3a2a5a"
    ],
    "desc": "A glassy desert that splits light into rainbows. Pays well for ice."
   },
   "ceres": {
    "n": "Quarry",
    "station": "Geode Hall",
    "tex": "rock",
    "col": [
     "#a8b0c8",
     "#2a3040"
    ],
    "desc": "The Geode Cutters' capital. Every rock here has been cut open.",
    "field": {
     "n": "The Geode Belt",
     "ores": {
      "cobalt": 2,
      "platinum": 2,
      "sunstone": 1,
      "iridium": 0.52
     },
     "geodes": 0.2
    }
   },
   "jupiter": {
    "n": "Behemoth",
    "tex": "gas",
    "col": [
     "#b0d0ff",
     "#1a3a8a"
    ]
   },
   "europa": {
    "n": "Frostlight",
    "station": "Frostlight Colony",
    "tex": "ice",
    "col": [
     "#f0f8ff",
     "#6a8ab0"
    ],
    "desc": "An ice moon that glows at night. Pays well for iridium."
   },
   "troyanos": {
    "station": "Behemoth Depot",
    "desc": "Behemoth's Trojans, packed with geodes.",
    "field": {
     "n": "Behemoth Swarm",
     "ores": {
      "platinum": 2,
      "sunstone": 3,
      "iridium": 6.63
     },
     "geodes": 0.15
    }
   },
   "saturno": {
    "n": "Halo",
    "station": "Halo Ring Depot",
    "tex": "gas",
    "col": [
     "#e8f0ff",
     "#5a6aa0"
    ],
    "desc": "A giant with rings so bright they cast shadows.",
    "field": {
     "n": "Halo Rings",
     "ores": {
      "he3": 3,
      "sunstone": 2,
      "iridium": 2,
      "exotic": 0.67
     },
     "geodes": 0.12
    }
   },
   "titan": {
    "n": "Lumen",
    "station": "Lumenworks",
    "tex": "titan",
    "col": [
     "#d0d8f0",
     "#4a5070"
    ],
    "desc": "A pale moon of refineries that run on starlight."
   },
   "pluton": {
    "n": "Umbra",
    "station": "Shadow Market",
    "tex": "rock",
    "col": [
     "#5a5a7a",
     "#101020"
    ],
    "desc": "The only dark place in Rigel. The Glare Raiders love it."
   },
   "kuiper": {
    "n": "Rigel Reach",
    "station": "Reach Depot",
    "desc": "The far edge of Rigel's glare, full of geodes.",
    "field": {
     "n": "Rigel Reach",
     "ores": {
      "sunstone": 1,
      "iridium": 2,
      "exotic": 1.47
     },
     "geodes": 0.12
    }
   },
   "oort": {
    "n": "The Radiant Rift",
    "station": "Shade Outpost",
    "col": [
     "#a0d0ff",
     "#0a1a4a"
    ],
    "desc": "A rift of pure light where a crystal giant stands guard.",
    "field": {
     "n": "The Radiant Rift",
     "ores": {
      "platinum": 2,
      "iridium": 1,
      "exotic": 2,
      "voidshard": 0.28
     },
     "geodes": 0.1
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Glint"
   },
   "3": {
    "title": "Searlight & Prism",
    "text": "<b>Searlight</b> is scorched white — buy <b>Shields</b>. <b>Prism</b> pays a fortune for ice. Press <b>C</b> to <b>Deep Scan</b> for hidden geodes!"
   },
   "4": {
    "title": "The Geode Belt",
    "text": "<b>Quarry</b> and the <b>Geode Belt</b>: one rock in five hides a geode. Scan, then crack them open."
   },
   "6": {
    "title": "Behemoth System",
    "text": "<b>Frostlight</b> and the <b>Behemoth Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Halo & Influence",
    "text": "<b>Lumen</b> and the <b>Halo Rings</b>. <b>Invest</b> for <b>+10% income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule Rigel."
   },
   "8": {
    "title": "Umbra",
    "text": "<b>Umbra</b>'s Shadow Market and <b>Rigel Reach</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🚀",
    "n": "Photon Sail Freight",
    "d": "Rigel's light is so strong you just put sails on the cargo and let it get blown home.",
    "fx": "Glint outpost output ×3"
   },
   "beacons": {
    "icon": "📡",
    "n": "Mirror Relay",
    "d": "Giant mirrors bounce your ships across the system. They arrive slightly tanned.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "⚔",
    "n": "Prism Lancers",
    "d": "Gunships with crystal hulls that split every shot into a rainbow. Two fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "⬆",
    "n": "Light-Pressure Lift",
    "d": "Cargo pods with mirror bellies. Point them at Rigel and they fall upward.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Continental Sunshade",
    "d": "An umbrella the size of a continent turns Prism from a glassy desert into a meadow.",
    "fx": "Prism pays ×2 for everything · Prism Guild reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Lightway Gates",
    "d": "You turn your ships into light, beam them across the system, and turn them back. Mostly the same.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Halo Melt Ring",
    "d": "Focused starlight melts asteroids into a glowing river of ore that runs around Halo's rings.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Supergiant Lens",
    "d": "A lens wider than a planet's orbit focuses a blue supergiant straight onto your bank account.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Rigel Lance",
    "d": "You focus the Supergiant Lens into one beam. Planets never know what hit them.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 },
 "betelgeuse": {
  "n": "Betelgeuse",
  "star": "red",
  "rock": 12.6,
  "enemy": 6.8,
  "value": 1,
  "gift": "widebeam",
  "pulses": 1,
  "boss": "phoenix",
  "bossFleet": [
   "phoenix",
   "raider",
   "raider"
  ],
  "signal": {
   "title": "Born from the fire",
   "text": "Every time Betelgeuse pulses, something huge rises out of the flames near the <b>Phoenix Nest</b>. The Exodus Fleet calls it the <b>Stellar Phoenix</b>. Legends say you have to kill it <b>twice</b>."
  },
  "gate": "The Phoenix burns out for good, and its ashes swirl into a ring. An ancient gate <b>ignites</b>.",
  "intro": "Betelgeuse is a <b>red supergiant about to explode</b>. Every minute or so it <b>pulses</b>: a wave of heat washes over the field and every rock turns <b>molten</b> for a few seconds — <b>double laser damage and +50% ore</b>. Mine hard when the wave hits! The Forge Syndicate gives you the <b>Wide Beam</b>: your laser now <b>forks</b> into two more rocks near your target. You keep it forever.",
  "factions": {
   "tierra": {
    "n": "Last Light Accord",
    "c": "#ffa080"
   },
   "marte": {
    "n": "Ash Brotherhood",
    "c": "#d08060"
   },
   "cinturon": {
    "n": "Forge Syndicate",
    "c": "#ffc060"
   },
   "exterior": {
    "n": "Exodus Fleet",
    "c": "#a0a0ff"
   },
   "piratas": {
    "n": "Cinder Reavers",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Ember",
    "station": "Emberwatch",
    "tex": "rock",
    "col": [
     "#d09070",
     "#3a1a10"
    ],
    "desc": "A moon glowing dull red in Betelgeuse's light.",
    "field": {
     "n": "Ember Fields",
     "ores": {
      "iron": 5,
      "ice": 2,
      "sunstone": 0.1
     }
    }
   },
   "tierra": {
    "n": "Dusk",
    "station": "Dusk Harbor",
    "tex": "ocean",
    "col": [
     "#e09080",
     "#3a1a2a"
    ],
    "desc": "An ocean world where the sun never stops setting."
   },
   "venus": {
    "n": "Crimson",
    "station": "Crimson Spire",
    "tex": "gas",
    "col": [
     "#ff8070",
     "#5a1020"
    ],
    "desc": "A blood-red cloud world. The richest people pack their bags here."
   },
   "mercurio": {
    "n": "Pyre",
    "station": "Pyre Depot",
    "tex": "lava",
    "col": [
     "#ff7040",
     "#2a0804"
    ],
    "desc": "A planet inside the star's outer layers. It is very, very hot.",
    "field": {
     "n": "Pyre Flats",
     "ores": {
      "iron": 2,
      "titanium": 1,
      "cobalt": 2,
      "sunstone": 2.11
     },
     "geodes": 0.06
    }
   },
   "marte": {
    "n": "Ashfall",
    "station": "Ash Gate",
    "tex": "rock",
    "col": [
     "#a08070",
     "#2a1a14"
    ],
    "desc": "Ash falls like snow here. Pays well for ice."
   },
   "ceres": {
    "n": "Forge",
    "station": "Foundry Hall",
    "tex": "rock",
    "col": [
     "#c08060",
     "#3a2014"
    ],
    "desc": "The Forge Syndicate melts asteroids in the star's heat.",
    "field": {
     "n": "The Forge Belt",
     "ores": {
      "nickel": 2,
      "cobalt": 1,
      "sunstone": 2,
      "iridium": 0.57
     },
     "geodes": 0.08
    }
   },
   "jupiter": {
    "n": "Inferno",
    "tex": "gas",
    "col": [
     "#ffa060",
     "#7a1a10"
    ]
   },
   "europa": {
    "n": "Steam",
    "station": "Steamvent Colony",
    "tex": "ice",
    "col": [
     "#f0d0c8",
     "#7a4a4a"
    ],
    "desc": "An ice moon slowly melting into steam. Pays well for iridium."
   },
   "troyanos": {
    "station": "Inferno Depot",
    "desc": "Inferno's Trojans, glowing in the red light.",
    "field": {
     "n": "Inferno Swarm",
     "ores": {
      "he3": 2,
      "sunstone": 3,
      "iridium": 6.98
     },
     "geodes": 0.06
    }
   },
   "saturno": {
    "n": "Gloam",
    "station": "Gloam Ring Depot",
    "tex": "gas",
    "col": [
     "#e0a090",
     "#5a2a2a"
    ],
    "desc": "A giant whose icy rings are slowly boiling away.",
    "field": {
     "n": "Gloam Rings",
     "ores": {
      "he3": 2,
      "sunstone": 2,
      "iridium": 2,
      "voidshard": 0.29
     },
     "geodes": 0.06
    }
   },
   "titan": {
    "n": "Smelt",
    "station": "Smeltworks",
    "tex": "titan",
    "col": [
     "#d09070",
     "#4a2a1a"
    ],
    "desc": "A moon of giant furnaces."
   },
   "pluton": {
    "n": "Exodus",
    "station": "Evacuation Market",
    "tex": "rock",
    "col": [
     "#8080a0",
     "#1a1a2a"
    ],
    "desc": "Everyone is trying to leave before the star blows. Everything is on sale."
   },
   "kuiper": {
    "n": "The Red Shroud",
    "station": "Shroud Depot",
    "desc": "Gas the star threw off long ago, now full of ore.",
    "field": {
     "n": "The Red Shroud",
     "ores": {
      "sunstone": 2,
      "iridium": 2,
      "voidshard": 0.67
     },
     "geodes": 0.06
    }
   },
   "oort": {
    "n": "Phoenix Nest",
    "station": "Ashen Outpost",
    "col": [
     "#ffb060",
     "#3a0a04"
    ],
    "desc": "A nest of flame at the edge of the system.",
    "field": {
     "n": "Phoenix Nest",
     "ores": {
      "ice": 2,
      "sunstone": 2,
      "exotic": 1,
      "voidshard": 0.89
     },
     "geodes": 0.06
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Ember"
   },
   "3": {
    "title": "Pyre & Ashfall",
    "text": "<b>Pyre</b> burns with <b>Sunstone</b> — buy <b>Shields</b>. <b>Ashfall</b> pays a fortune for ice. When Betelgeuse <b>pulses</b>, every rock turns molten — mine fast!"
   },
   "4": {
    "title": "The Forge Belt",
    "text": "<b>Forge</b> and the <b>Forge Belt</b>. Your <b>Wide Beam</b> shines in a crowd: aim at clusters."
   },
   "6": {
    "title": "Inferno System",
    "text": "<b>Steam</b> and the <b>Inferno Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Gloam & Influence",
    "text": "<b>Smelt</b> and the <b>Gloam Rings</b>. <b>Invest</b> for <b>+10% income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule Betelgeuse."
   },
   "8": {
    "title": "Exodus",
    "text": "<b>Exodus</b>'s Evacuation Market and <b>the Red Shroud</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🚀",
    "n": "Flare Surfers",
    "d": "Your ore rides the star's own solar flares like a wave, all the way home.",
    "fx": "Ember outpost output ×3"
   },
   "beacons": {
    "icon": "💡",
    "n": "Pulse Riders",
    "d": "Ships launch at the exact moment Betelgeuse pulses and surf the shockwave.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "🔥",
    "n": "Ember Wing",
    "d": "Fireproof gunships that fly through solar flares for fun. Two fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "⬆",
    "n": "Thermal Updraft Tower",
    "d": "A tower so hot that the air inside rises at orbital speed. Cargo goes up with it.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Planet Fridge",
    "d": "You wrap Ashfall in a giant cooling blanket. Snow falls for the first time in a billion years.",
    "fx": "Ashfall pays ×2 for everything · Ash Brotherhood reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Borrowed Shockwave",
    "d": "You borrow tomorrow's supernova shockwave and ride it today. Instant travel, slightly singed.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Star-Lifting Ring",
    "d": "You siphon the star's outer layers and refine them into ore. It had plenty to spare.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Supernova Bottle",
    "d": "A shell built to catch the supernova when it comes. Until then, it's the biggest battery ever made.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Early Supernova",
    "d": "Why wait? You set off a tiny slice of Betelgeuse's supernova — aimed.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 }
});

// systems 12–15
Object.assign(SYSTEMS, {
 "orion": {
  "n": "Orion Nebula",
  "star": "blue",
  "rock": 13.6,
  "enemy": 7.3,
  "value": 1,
  "boss": "hydra",
  "bossFleet": [
   "hydra",
   "raider",
   "raider"
  ],
  "signal": {
   "title": "Three heads in the cloud",
   "text": "Deep in the nebula something with <b>three glowing heads</b> guards the old gate at <b>Hydra's Cradle</b>. The Lodestone Union warns: <b>cut it down and it splits in two</b>."
  },
  "gate": "The last Hydra head dissolves into glowing gas. From the newborn stars, an ancient ring <b>takes shape</b>.",
  "intro": "The <b>Orion Nebula</b> is a nursery where new stars are born. Many asteroids here are <b>magnetic</b>: they slowly <b>pull together into clusters</b> — perfect for your Charges and Wide Beam. When a magnetic rock breaks, it sends out a <b>magnetic burst</b> that pulls every ore chunk nearby straight to your ship.",
  "factions": {
   "tierra": {
    "n": "Nursery Council",
    "c": "#ff9ad8"
   },
   "marte": {
    "n": "Trapezium Guard",
    "c": "#c0a0ff"
   },
   "cinturon": {
    "n": "Lodestone Union",
    "c": "#7fb8ff"
   },
   "exterior": {
    "n": "Nebula Drifters",
    "c": "#a0ffd8"
   },
   "piratas": {
    "n": "Veil Wolves",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Cradle",
    "station": "Cradle Base",
    "tex": "ice",
    "col": [
     "#f0d8ff",
     "#4a3a7a"
    ],
    "desc": "A frosty moon wrapped in pink nebula gas.",
    "field": {
     "n": "Cradle Drift",
     "ores": {
      "iron": 3,
      "ice": 2,
      "titanium": 1,
      "nickel": 0.53
     },
     "magnetic": 0.1
    }
   },
   "tierra": {
    "n": "Bloom",
    "station": "Bloom Harbor",
    "tex": "ocean",
    "col": [
     "#ff9ad8",
     "#2a1a6a"
    ],
    "desc": "An ocean world under skies full of baby stars."
   },
   "venus": {
    "n": "Rosette",
    "station": "Rosette Spire",
    "tex": "gas",
    "col": [
     "#ffb0d0",
     "#6a2a5a"
    ],
    "desc": "A rose-colored cloud world. Very fancy."
   },
   "mercurio": {
    "n": "Protostar",
    "station": "Ignition Depot",
    "tex": "lava",
    "col": [
     "#ffd0a0",
     "#4a1a3a"
    ],
    "desc": "A planet orbiting a star that is still being born.",
    "field": {
     "n": "Ignition Plains",
     "ores": {
      "titanium": 2,
      "cobalt": 2,
      "platinum": 1,
      "sunstone": 1.08
     },
     "magnetic": 0.15
    }
   },
   "marte": {
    "n": "Trapezium",
    "station": "Trapezium Gate",
    "tex": "rock",
    "col": [
     "#c8b0e0",
     "#3a2a4a"
    ],
    "desc": "A fortress world lit by four bright young stars. Pays well for ice."
   },
   "ceres": {
    "n": "Lodestone",
    "station": "Magnet Hall",
    "tex": "rock",
    "col": [
     "#9ab0d0",
     "#2a3048"
    ],
    "desc": "A giant magnet in space. Compasses here just spin.",
    "field": {
     "n": "The Lodestone Belt",
     "ores": {
      "nickel": 1,
      "cobalt": 2,
      "platinum": 2,
      "iridium": 0.95
     },
     "magnetic": 0.3
    }
   },
   "jupiter": {
    "n": "Horsehead",
    "tex": "gas",
    "col": [
     "#c08070",
     "#2a1018"
    ]
   },
   "europa": {
    "n": "Mane",
    "station": "Mane Colony",
    "tex": "ice",
    "col": [
     "#f0e0ff",
     "#7a5a9a"
    ],
    "desc": "An ice moon in the shadow of the Horsehead. Pays well for iridium."
   },
   "troyanos": {
    "station": "Horsehead Depot",
    "desc": "Magnetic rocks tumbling in the Horsehead's shadow.",
    "field": {
     "n": "Horsehead Swarm",
     "ores": {
      "he3": 2,
      "platinum": 2,
      "iridium": 2,
      "ringpearl": 0.61
     },
     "magnetic": 0.2
    }
   },
   "saturno": {
    "n": "Pillar",
    "station": "Pillar Ring Depot",
    "tex": "gas",
    "col": [
     "#e0c0e0",
     "#5a3a6a"
    ],
    "desc": "A giant inside a pillar of glowing gas.",
    "field": {
     "n": "Pillar Rings",
     "ores": {
      "ice": 2,
      "he3": 2,
      "ringpearl": 2,
      "exotic": 0.35
     },
     "magnetic": 0.2
    }
   },
   "titan": {
    "n": "Glowworm",
    "station": "Glowworks",
    "tex": "titan",
    "col": [
     "#d0f0c0",
     "#3a5a3a"
    ],
    "desc": "A moon that glows faintly green at night."
   },
   "pluton": {
    "n": "Shadowveil",
    "station": "Wolf Den",
    "tex": "rock",
    "col": [
     "#6a5a7a",
     "#14101a"
    ],
    "desc": "Hidden in a dark cloud. The Veil Wolves live here."
   },
   "kuiper": {
    "n": "The Nursery Edge",
    "station": "Edge Depot",
    "desc": "Where the nebula thins out into dark space.",
    "field": {
     "n": "The Nursery Edge",
     "ores": {
      "iridium": 2,
      "ringpearl": 2,
      "exotic": 1.28
     },
     "magnetic": 0.2
    }
   },
   "oort": {
    "n": "Hydra's Cradle",
    "station": "Starlight Outpost",
    "col": [
     "#ff9ad8",
     "#2a0a3a"
    ],
    "desc": "A cloud of newborn stars — and a three-headed guardian.",
    "field": {
     "n": "Hydra's Cradle",
     "ores": {
      "ice": 2,
      "ringpearl": 1,
      "exotic": 2,
      "voidshard": 0.23
     },
     "magnetic": 0.15
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Cradle"
   },
   "3": {
    "title": "Protostar & Trapezium",
    "text": "<b>Protostar</b> burns hot — buy <b>Shields</b>. <b>Trapezium</b> pays a fortune for ice. <b>Magnetic rocks</b> pull together into clusters: blast them with Charges!"
   },
   "4": {
    "title": "The Lodestone Belt",
    "text": "<b>Lodestone</b> and its belt: a third of the rocks are magnetic. Break one and every ore chunk nearby flies to you."
   },
   "6": {
    "title": "Horsehead System",
    "text": "<b>Mane</b> and the <b>Horsehead Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Pillar & Influence",
    "text": "<b>Glowworm</b> and the <b>Pillar Rings</b>. <b>Invest</b> for <b>+10% income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule the Orion Nebula."
   },
   "8": {
    "title": "Shadowveil",
    "text": "<b>Shadowveil</b>'s Wolf Den and <b>the Nursery Edge</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🧲",
    "n": "Magnetic Railway",
    "d": "A track of magnets so strong your ore just slides home on its own.",
    "fx": "Cradle outpost output ×3"
   },
   "beacons": {
    "icon": "💡",
    "n": "Starbirth Beacons",
    "d": "You light the lanes with baby stars. They are very bright and a bit loud.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "🛡",
    "n": "Nebula Wolfpack",
    "d": "You tame the Veil Wolves' fastest ships. Two hunt with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "🗼",
    "n": "Magnet Lift",
    "d": "Two giant magnets, one on the ground and one in orbit. Flip the switch and cargo goes up.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Star Nursery Garden",
    "d": "You plant a baby star next to Trapezium. Now it has seasons, rain and flowers.",
    "fx": "Trapezium pays ×2 for everything · Trapezium Guard reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Nebula Folds",
    "d": "You fold the nebula like a map so any two places touch.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Lodestone Halo",
    "d": "A ring-shaped magnet around Pillar pulls ore out of the whole nebula.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Starbirth Farm",
    "d": "Why use one star? You grow a whole field of them and harvest their light.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Star Seed Cannon",
    "d": "You fire a baby star at a planet. It grows up very fast.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 },
 "pulsar": {
  "n": "The Pulsar",
  "star": "white",
  "rock": 14.9,
  "enemy": 8,
  "value": 1,
  "gift": "phase",
  "sweeps": 1,
  "boss": "warden",
  "bossFleet": [
   "warden",
   "corsair",
   "corsair"
  ],
  "signal": {
   "title": "The lighthouse keeper",
   "text": "At the heart of the Pulsar's beam stands the <b>Pulsar Warden</b> — a spinning station with two arms of pure light. <b>Stay out of its arms</b>, or phase right through them."
  },
  "gate": "The Warden stops spinning and goes dark. In the sudden silence, an ancient ring <b>starts to tick</b>.",
  "intro": "<b>The Pulsar</b> is a dead star spinning hundreds of times a second. Every few seconds its <b>beam sweeps across your field</b>: rocks it touches get <b>charged</b> (×2 ore for a while), but it also burns your hull. The Beam Riders give you the <b>Phase Shift</b>: press <b>X</b> (or PHASE) to become a ghost for 3 s — no damage, and you fly straight through rocks. Ride the beam! You keep it forever.",
  "factions": {
   "tierra": {
    "n": "Lighthouse Assembly",
    "c": "#b0c8ff"
   },
   "marte": {
    "n": "Tick Clans",
    "c": "#e0c0a0"
   },
   "cinturon": {
    "n": "Beam Riders",
    "c": "#9ff3ff"
   },
   "exterior": {
    "n": "Silent Choir",
    "c": "#c0a0ff"
   },
   "piratas": {
    "n": "Static Raiders",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Tick",
    "station": "Tick Base",
    "tex": "rock",
    "col": [
     "#c0c8d8",
     "#30364a"
    ],
    "desc": "A moon that flashes every time the beam goes by.",
    "field": {
     "n": "Tick Fields",
     "ores": {
      "iron": 4,
      "ice": 2,
      "titanium": 2.77
     }
    }
   },
   "tierra": {
    "n": "Metronome",
    "station": "Beacon Harbor",
    "tex": "ocean",
    "col": [
     "#a0c0ff",
     "#0a1a4a"
    ],
    "desc": "A world where everyone lives by the beam. Very punctual people."
   },
   "venus": {
    "n": "Chime",
    "station": "Chime Spire",
    "tex": "gas",
    "col": [
     "#e0e8ff",
     "#4a4a8a"
    ],
    "desc": "Its clouds ring like bells when the beam hits them."
   },
   "mercurio": {
    "n": "Flash",
    "station": "Flash Depot",
    "tex": "lava",
    "col": [
     "#ffffff",
     "#2a2a5a"
    ],
    "desc": "Right next to the beam. Bring shields.",
    "field": {
     "n": "Flash Plains",
     "ores": {
      "nickel": 2,
      "platinum": 2,
      "sunstone": 0.23
     }
    }
   },
   "marte": {
    "n": "Echo",
    "station": "Echo Gate",
    "tex": "rock",
    "col": [
     "#c0a890",
     "#3a2a20"
    ],
    "desc": "A silent desert that echoes every pulse. Pays well for ice."
   },
   "ceres": {
    "n": "Strobe",
    "station": "Beam Hall",
    "tex": "rock",
    "col": [
     "#a8b8d0",
     "#283040"
    ],
    "desc": "The Beam Riders' home. They time everything to the pulse.",
    "field": {
     "n": "The Strobe Belt",
     "ores": {
      "platinum": 2,
      "sunstone": 2,
      "iridium": 0.17
     }
    }
   },
   "jupiter": {
    "n": "Gyre",
    "tex": "gas",
    "col": [
     "#c0d8ff",
     "#2a3a7a"
    ]
   },
   "europa": {
    "n": "Hush",
    "station": "Hush Colony",
    "tex": "ice",
    "col": [
     "#f0f8ff",
     "#6a7aa0"
    ],
    "desc": "The only quiet place in the system. Pays well for iridium."
   },
   "troyanos": {
    "station": "Gyre Depot",
    "desc": "Gyre's Trojans, crackling with static.",
    "field": {
     "n": "Gyre Swarm",
     "ores": {
      "platinum": 2,
      "sunstone": 2,
      "iridium": 5.06
     }
    }
   },
   "saturno": {
    "n": "Spindle",
    "station": "Spindle Ring Depot",
    "tex": "gas",
    "col": [
     "#e0e8f8",
     "#4a5a8a"
    ],
    "desc": "A giant whose rings spin in time with the pulsar.",
    "field": {
     "n": "Spindle Rings",
     "ores": {
      "ice": 2,
      "iridium": 2,
      "ringpearl": 1,
      "exotic": 0.24
     }
    }
   },
   "titan": {
    "n": "Cog",
    "station": "Cogworks",
    "tex": "titan",
    "col": [
     "#c8c0b0",
     "#4a4030"
    ],
    "desc": "A moon of clockwork factories."
   },
   "pluton": {
    "n": "Static",
    "station": "Static Market",
    "tex": "rock",
    "col": [
     "#7a7a9a",
     "#14141f"
    ],
    "desc": "Where the Static Raiders sell what they steal."
   },
   "kuiper": {
    "n": "The Silent Reach",
    "station": "Reach Depot",
    "desc": "Far from the beam, but never quite out of it.",
    "field": {
     "n": "The Silent Reach",
     "ores": {
      "ice": 2,
      "ringpearl": 2,
      "exotic": 1.45
     }
    }
   },
   "oort": {
    "n": "The Warden's Lighthouse",
    "station": "Blind Spot Outpost",
    "col": [
     "#e0f0ff",
     "#101a3a"
    ],
    "desc": "The center of the beam, where the Warden spins.",
    "field": {
     "n": "The Warden's Lighthouse",
     "ores": {
      "ice": 2,
      "exotic": 1,
      "voidshard": 0.24
     }
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Tick"
   },
   "3": {
    "title": "Flash & Echo",
    "text": "<b>Flash</b> sits in the beam — buy <b>Shields</b>. <b>Echo</b> pays a fortune for ice. When the beam sweeps by, press <b>X</b> to <b>Phase</b> through it and mine the charged rocks!"
   },
   "4": {
    "title": "The Strobe Belt",
    "text": "<b>Strobe</b> and the <b>Strobe Belt</b>. Charged rocks drop double ore — time your mining to the pulse."
   },
   "6": {
    "title": "Gyre System",
    "text": "<b>Hush</b> and the <b>Gyre Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Spindle & Influence",
    "text": "<b>Cog</b> and the <b>Spindle Rings</b>. <b>Invest</b> for <b>+10% income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule the Pulsar."
   },
   "8": {
    "title": "Static",
    "text": "<b>Static</b>'s market and <b>the Silent Reach</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "⚡",
    "n": "Pulse Catapult",
    "d": "Cargo launches on every pulse — 700 times a second.",
    "fx": "Tick outpost output ×3"
   },
   "beacons": {
    "icon": "📡",
    "n": "Clockwork Lanes",
    "d": "Every ship moves exactly in time with the pulsar. Nobody is ever late again.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "⚔",
    "n": "Strobe Squadron",
    "d": "Gunships that only exist between pulses. Pirates can't hit what isn't there. Two fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "⬆",
    "n": "Beam Lift",
    "d": "You park cargo in the pulsar's beam and it gets flicked into orbit.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Planet Clock",
    "d": "You slow Echo's spin to a perfect 24 hours. Turns out that's all it needed.",
    "fx": "Echo pays ×2 for everything · Tick Clans reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Time-Slice Gates",
    "d": "You step out of one pulse and into the next — somewhere else.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Spinning Ring Foundry",
    "d": "Spindle's rings spin so fast they sort ore by weight all by themselves.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Neutron Dynamo",
    "d": "You put a generator on the fastest-spinning thing in the galaxy.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Pulsar Lance",
    "d": "You aim the pulsar. Just once. Just a little.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 },
 "rim": {
  "n": "Core Rim",
  "star": "orange",
  "rock": 16.3,
  "enemy": 8.8,
  "value": 1,
  "boss": "archon",
  "bossFleet": [
   "archon"
  ],
  "signal": {
   "title": "The last guardian",
   "text": "At <b>Archon's Gate</b> an ancient machine still stands watch: <b>the Archon</b>. It hides behind <b>shield shards</b> — destroy the shards first, then strike."
  },
  "gate": "The Archon bows, and its light goes out. The oldest gate in the galaxy <b>opens</b> — and it points straight at the black hole.",
  "intro": "The <b>Core Rim</b> is the edge of the galaxy's center, full of ruins from a lost civilization. Some asteroids are <b>ancient relics</b>, covered in glowing glyphs. Break one to release a <b>relic power</b> for 25 s: double ore, a giant magnet, a super laser, or all your tools recharged at once.",
  "factions": {
   "tierra": {
    "n": "Rim Concordat",
    "c": "#ffc080"
   },
   "marte": {
    "n": "Relic Wardens",
    "c": "#d0b070"
   },
   "cinturon": {
    "n": "Glyph Diggers",
    "c": "#ffe080"
   },
   "exterior": {
    "n": "Old Light Pilgrims",
    "c": "#c0a0ff"
   },
   "piratas": {
    "n": "Tomb Raiders",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Shard",
    "station": "Dig Site One",
    "tex": "rock",
    "col": [
     "#d0b890",
     "#3a2a18"
    ],
    "desc": "A moon covered in old ruins. Every rock might be a relic.",
    "field": {
     "n": "First Dig",
     "ores": {
      "iron": 3,
      "ice": 3,
      "cobalt": 0.51
     },
     "relics": 0.08
    }
   },
   "tierra": {
    "n": "Elder",
    "station": "Elder Harbor",
    "tex": "ocean",
    "col": [
     "#e0c090",
     "#2a3a5a"
    ],
    "desc": "A gentle ocean world built on top of ancient cities."
   },
   "venus": {
    "n": "Gilt",
    "station": "Gilt Spire",
    "tex": "gas",
    "col": [
     "#ffe0a0",
     "#7a5a20"
    ],
    "desc": "A golden cloud world. The rich collect relics here."
   },
   "mercurio": {
    "n": "Kiln",
    "station": "Kiln Depot",
    "tex": "lava",
    "col": [
     "#ffa050",
     "#3a1404"
    ],
    "desc": "A burning world where the ancients forged their machines.",
    "field": {
     "n": "Kiln Flats",
     "ores": {
      "titanium": 2,
      "cobalt": 2,
      "platinum": 1,
      "iridium": 0.21
     },
     "relics": 0.12
    }
   },
   "marte": {
    "n": "Obelisk",
    "station": "Obelisk Gate",
    "tex": "rock",
    "col": [
     "#c0a070",
     "#3a2a14"
    ],
    "desc": "A desert of giant black obelisks. Pays well for ice."
   },
   "ceres": {
    "n": "Vault",
    "station": "Glyph Hall",
    "tex": "rock",
    "col": [
     "#b8a080",
     "#30281c"
    ],
    "desc": "The Glyph Diggers' city, carved inside an ancient vault.",
    "field": {
     "n": "The Vault Belt",
     "ores": {
      "cobalt": 2,
      "he3": 2,
      "ringpearl": 0.29
     },
     "relics": 0.25
    }
   },
   "jupiter": {
    "n": "Colossus Prime",
    "tex": "gas",
    "col": [
     "#ffc890",
     "#7a3a1a"
    ]
   },
   "europa": {
    "n": "Rune",
    "station": "Rune Colony",
    "tex": "ice",
    "col": [
     "#fff0d8",
     "#7a6a4a"
    ],
    "desc": "Glyphs glow under the ice. Pays well for iridium."
   },
   "troyanos": {
    "station": "Prime Depot",
    "desc": "Trojan rocks full of old machinery.",
    "field": {
     "n": "Ruin Swarm",
     "ores": {
      "he3": 2,
      "platinum": 2,
      "iridium": 2,
      "exotic": 0.12
     },
     "relics": 0.18
    }
   },
   "saturno": {
    "n": "Ringwork",
    "station": "Ringwork Depot",
    "tex": "gas",
    "col": [
     "#f0d8a8",
     "#6a4a2a"
    ],
    "desc": "Its rings are not natural. Somebody built them.",
    "field": {
     "n": "Ringwork Rings",
     "ores": {
      "he3": 2,
      "iridium": 2,
      "voidshard": 0.16
     },
     "relics": 0.18
    }
   },
   "titan": {
    "n": "Archive",
    "station": "Archiveworks",
    "tex": "titan",
    "col": [
     "#d8c090",
     "#4a3a20"
    ],
    "desc": "A moon-sized library, now a refinery."
   },
   "pluton": {
    "n": "Crypt",
    "station": "Tomb Market",
    "tex": "rock",
    "col": [
     "#7a6a5a",
     "#1a140e"
    ],
    "desc": "The Tomb Raiders sell stolen relics here."
   },
   "kuiper": {
    "n": "The Boneyard",
    "station": "Boneyard Depot",
    "desc": "A graveyard of ancient ships, picked clean — almost.",
    "field": {
     "n": "The Boneyard",
     "ores": {
      "ice": 2,
      "iridium": 2,
      "exotic": 1.86
     },
     "relics": 0.18
    }
   },
   "oort": {
    "n": "Archon's Gate",
    "station": "Last Lamp Outpost",
    "col": [
     "#ffd080",
     "#2a1a04"
    ],
    "desc": "The oldest gate in the galaxy, and its last guardian.",
    "field": {
     "n": "Archon's Gate",
     "ores": {
      "ice": 2,
      "ringpearl": 2,
      "voidshard": 0.96
     },
     "relics": 0.12
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Shard"
   },
   "3": {
    "title": "Kiln & Obelisk",
    "text": "<b>Kiln</b> burns hot — buy <b>Shields</b>. <b>Obelisk</b> pays a fortune for ice. Rocks with glowing glyphs are <b>relics</b>: break them for a power-up!"
   },
   "4": {
    "title": "The Vault Belt",
    "text": "<b>Vault</b> and the <b>Vault Belt</b>: one rock in four is a relic."
   },
   "6": {
    "title": "Colossus Prime System",
    "text": "<b>Rune</b> and the <b>Ruin Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Ringwork & Influence",
    "text": "<b>Archive</b> and the <b>Ringwork Rings</b>. <b>Invest</b> for <b>+10% income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule the Core Rim."
   },
   "8": {
    "title": "Crypt",
    "text": "<b>Crypt</b>'s Tomb Market and <b>the Boneyard</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🏛",
    "n": "Ancient Conveyor",
    "d": "You find the ancients' cargo system. It still works. It was waiting for you.",
    "fx": "Shard outpost output ×3"
   },
   "beacons": {
    "icon": "💡",
    "n": "Glyph Lanes",
    "d": "You switch on the old glyphs. They glow along every lane, showing the way.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "🤖",
    "n": "Reawakened Sentinels",
    "d": "Two ancient guardian machines decide they like you. They fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "🗼",
    "n": "Obelisk Lift",
    "d": "Turns out the obelisks are elevators. Who knew?",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Garden Machine",
    "d": "An ancient machine that turns deserts into jungles. You press the big button.",
    "fx": "Obelisk pays ×2 for everything · Relic Wardens reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "The Old Network",
    "d": "You reconnect the ancients' gate network. It goes everywhere.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Ringwork Restart",
    "d": "You restart Ringwork's artificial rings. They were mining machines all along.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "The Ancients' Sphere",
    "d": "You finish the Dyson sphere the ancients left half-built a million years ago.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "World Eraser",
    "d": "The reason the ancients disappeared. Please be careful with it.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 },
 "sgra": {
  "n": "Sagittarius A*",
  "star": "hole",
  "rock": 17.8,
  "enemy": 9.6,
  "value": 1,
  "gravity": 1,
  "boss": "devourer",
  "bossFleet": [
   "devourer",
   "raider",
   "raider"
  ],
  "signal": {
   "title": "Something is eating the light",
   "text": "At the <b>Event Horizon</b> lives the <b>Devourer</b> — a creature that feeds on the black hole itself. Its gravity <b>pulls you in</b>. This is the last fight in the galaxy."
  },
  "gate": "The Devourer falls into the black hole it fed on. The center of the galaxy is quiet. <b>You made it.</b>",
  "intro": "<b>Sagittarius A*</b>: the supermassive black hole at the center of the Milky Way. Its <b>gravity pulls on everything</b> — your ship, the rocks, the ore. Rocks drift up toward the black hole and get swallowed, so mine fast and don't fly too close to the <b>event horizon</b> at the top of every field. This is the last system. Finish it, and you've crossed the galaxy.",
  "factions": {
   "tierra": {
    "n": "Core Republic",
    "c": "#ffd0a0"
   },
   "marte": {
    "n": "Horizon Monks",
    "c": "#c0a0ff"
   },
   "cinturon": {
    "n": "Spiral Miners",
    "c": "#ffb070"
   },
   "exterior": {
    "n": "Last Frontier",
    "c": "#a0c0ff"
   },
   "piratas": {
    "n": "Void Reavers",
    "c": "#ff4d6d"
   }
  },
  "locs": {
   "luna": {
    "n": "Spark",
    "station": "Brink Base",
    "tex": "rock",
    "col": [
     "#d0a080",
     "#2a1a10"
    ],
    "desc": "A small moon right on the brink of the deep.",
    "field": {
     "n": "Brink Fields",
     "ores": {
      "iron": 4,
      "ice": 2,
      "platinum": 0.14
     }
    }
   },
   "tierra": {
    "n": "Haven Core",
    "station": "Core Harbor",
    "tex": "ocean",
    "col": [
     "#90b0ff",
     "#101a4a"
    ],
    "desc": "The capital of the galaxy's center. The sky is all stars."
   },
   "venus": {
    "n": "Radiance",
    "station": "Radiance Spire",
    "tex": "gas",
    "col": [
     "#ffe0b0",
     "#7a4a2a"
    ],
    "desc": "A cloud world lit by the glowing accretion disk."
   },
   "mercurio": {
    "n": "Swirl",
    "station": "Swirl Depot",
    "tex": "lava",
    "col": [
     "#ffa060",
     "#3a0a04"
    ],
    "desc": "A planet slowly spiraling inward. Hot and rich.",
    "field": {
     "n": "Swirl Flats",
     "ores": {
      "iron": 2,
      "titanium": 2,
      "sunstone": 1.88
     }
    }
   },
   "marte": {
    "n": "Stillness",
    "station": "Monk Gate",
    "tex": "rock",
    "col": [
     "#a090c0",
     "#2a2040"
    ],
    "desc": "The Horizon Monks meditate here, watching the black hole. Pays well for ice."
   },
   "ceres": {
    "n": "Spiral",
    "station": "Spiral Hall",
    "tex": "rock",
    "col": [
     "#c09070",
     "#3a2418"
    ],
    "desc": "The Spiral Miners chase ore as it falls inward.",
    "field": {
     "n": "The Spiral Belt",
     "ores": {
      "nickel": 2,
      "sunstone": 2,
      "iridium": 0.33
     }
    }
   },
   "jupiter": {
    "n": "Maw",
    "tex": "gas",
    "col": [
     "#ff9a60",
     "#4a0a10"
    ]
   },
   "europa": {
    "n": "Drift",
    "station": "Drift Colony",
    "tex": "ice",
    "col": [
     "#e0e8ff",
     "#4a4a7a"
    ],
    "desc": "An ice moon stretched into an egg by gravity. Pays well for iridium."
   },
   "troyanos": {
    "station": "Maw Depot",
    "desc": "Rocks falling in a long, slow spiral.",
    "field": {
     "n": "Maw Swarm",
     "ores": {
      "ice": 2,
      "iridium": 2,
      "voidshard": 0.02
     }
    }
   },
   "saturno": {
    "n": "Disk",
    "station": "Disk Depot",
    "tex": "gas",
    "col": [
     "#ffd0a0",
     "#6a2a10"
    ],
    "desc": "A giant skimming the edge of the accretion disk.",
    "field": {
     "n": "The Accretion Rings",
     "ores": {
      "ice": 3,
      "iridium": 2,
      "voidshard": 0.21
     }
    }
   },
   "titan": {
    "n": "Lantern",
    "station": "Lanternworks",
    "tex": "titan",
    "col": [
     "#ffe0a0",
     "#5a3a10"
    ],
    "desc": "A moon that glows in the disk's light."
   },
   "pluton": {
    "n": "Edge",
    "station": "Last Market",
    "tex": "rock",
    "col": [
     "#7a6a8a",
     "#14101a"
    ],
    "desc": "The last market before the deep. The Void Reavers trade here."
   },
   "kuiper": {
    "n": "The Accretion Disk",
    "station": "Disk Edge Depot",
    "desc": "A river of glowing rock pouring into the black hole.",
    "field": {
     "n": "The Accretion Disk",
     "ores": {
      "ice": 2,
      "exotic": 1,
      "voidshard": 0.02
     }
    }
   },
   "oort": {
    "n": "Event Horizon",
    "station": "Point of No Return",
    "col": [
     "#ffb060",
     "#000000"
    ],
    "desc": "The edge of the black hole. The Devourer feeds here.",
    "field": {
     "n": "Event Horizon",
     "ores": {
      "ice": 2,
      "exotic": 2,
      "voidshard": 0.07
     }
    }
   }
  },
  "unlocks": {
   "0": {
    "title": "Spark"
   },
   "3": {
    "title": "Swirl & Stillness",
    "text": "<b>Swirl</b> burns hot — buy <b>Shields</b>. <b>Stillness</b> pays a fortune for ice. Mind the <b>gravity</b>: everything drifts toward the black hole."
   },
   "4": {
    "title": "The Spiral Belt",
    "text": "<b>Spiral</b> and the <b>Spiral Belt</b>. Rocks that reach the event horizon are gone for good — catch them first."
   },
   "6": {
    "title": "Maw System",
    "text": "<b>Drift</b> and the <b>Maw Swarm</b>. The <b>Scanner</b> reveals rich veins."
   },
   "7": {
    "title": "Disk & Influence",
    "text": "<b>Lantern</b> and the <b>Accretion Rings</b>. <b>Invest</b> for <b>+10% income</b> and <b>influence</b>. Reach <b>100 influence</b> to rule the center of the galaxy."
   },
   "8": {
    "title": "Edge",
    "text": "<b>Edge</b>'s Last Market and <b>the Accretion Disk</b>."
   }
  },
  "projects": {
   "driver": {
    "icon": "🌀",
    "n": "Gravity Slingshot",
    "d": "You just drop the ore and let the black hole throw it home. Physics!",
    "fx": "Spark outpost output ×3"
   },
   "beacons": {
    "icon": "📡",
    "n": "Time-Dilation Lanes",
    "d": "Near the black hole, time slows down. Your trips take ages — for everyone else.",
    "fx": "Travel 50% faster · fuel −30%"
   },
   "fleet": {
    "icon": "🛡",
    "n": "Horizon Guard",
    "d": "Monks in gunships, perfectly calm, perfectly accurate. Two fly with you in every fight.",
    "fx": "Pirate danger −50% · 2 escort gunships in every fight"
   },
   "elevator": {
    "icon": "⬆",
    "n": "Frame-Drag Lift",
    "d": "The black hole spins space itself. Your cargo rides the spin up into orbit.",
    "fx": "All ore sells for +25% everywhere"
   },
   "terraform": {
    "icon": "🌱",
    "n": "Hawking Greenhouse",
    "d": "Warm black-hole glow turns Stillness into a garden. The monks approve.",
    "fx": "Stillness pays ×2 for everything · Horizon Monks reputation +50"
   },
   "gates": {
    "icon": "🌀",
    "n": "Wormhole Web",
    "d": "You tie wormholes to the black hole's spin. They go anywhere in the galaxy.",
    "fx": "Instant, free travel anywhere"
   },
   "ringstation": {
    "icon": "💫",
    "n": "Accretion Mill",
    "d": "A wheel in the accretion disk catches falling ore before it's gone.",
    "fx": "ALL drone income ×3"
   },
   "dyson": {
    "icon": "☀",
    "n": "Penrose Engine",
    "d": "You throw junk at a spinning black hole and catch it coming back with more energy. Infinite power.",
    "fx": "ALL income ×5"
   },
   "nova": {
    "icon": "💥",
    "n": "Pocket Singularity",
    "d": "A tiny black hole in a box. Open with care.",
    "fx": "Lets you DESTROY planets (from the Star Map)"
   }
  }
 }
});

// ---------- every system has its own shape ----------
// Layout overrides on top of each system's names: which worlds are moons of what, orbit sizes,
// stretched (ecc) and tilted orbits, the star's size, how the belts look and the sights on the map.
const LAYOUT = {
  centauri: { sys: { belts: { ceres: { style: 'double', w: 30 } }, tour: 'Pandora is no planet: it is a <b>moon of the gas giant Typhon</b>, with its own tiny moon Tethys. The Halcyon belt is split in two rings.' },
    locs: { jupiter: { r: 220, size: 22, period: 600 }, tierra: { parent: 'jupiter', r: 40, period: 30, a0: 1, desc: 'An ocean moon of the giant Typhon, with its own little moon. Pays well for every metal.' }, luna: { parent: 'tierra', r: 15 }, europa: { parent: 'jupiter', r: 64, period: 18 },
      venus: { r: 120, ecc: 0.1 }, mercurio: { r: 70, ecc: 0.25, tilt: 0.6 }, marte: { r: 300, ecc: 0.12, tilt: 2 }, ceres: { r: 345 }, saturno: { r: 455 }, troyanos: { follow: 'saturno', offset: -1.05 }, pluton: { r: 565, ecc: 0.35, tilt: 2.4 }, kuiper: { r: 625 }, oort: { r: 780 } } },
  barnard: { sys: { starScale: 0.7, belts: { ceres: { style: 'wide', w: 26 }, kuiper: { style: 'wide', w: 40 } }, tour: 'A small, dim red dwarf: its worlds <b>huddle close together</b>, so hops between them are short and cheap — and everything orbits fast.' },
    locs: { mercurio: { r: 40, period: 40 }, venus: { r: 64, period: 70 }, tierra: { r: 92, period: 110 }, luna: { r: 12 }, marte: { r: 126, period: 170 }, ceres: { r: 170, period: 260 }, jupiter: { r: 228, period: 420 }, saturno: { r: 290, period: 600 }, pluton: { r: 352, ecc: 0.2, period: 900 }, kuiper: { r: 400 }, oort: { r: 520 } } },
  sirius: { sys: { starScale: 1.3, mapfx: ['glare'], belts: { ceres: { w: 12, n: 700 }, kuiper: { style: 'arcs', w: 50 } }, tour: 'The brightest star in the sky. Its worlds keep far away, and the Ironheart belt is <b>a ring around the giant Argent</b>.' },
    locs: { mercurio: { r: 95 }, venus: { r: 150 }, tierra: { r: 205 }, marte: { r: 262, ecc: 0.2, tilt: 1.2 }, jupiter: { r: 335, size: 22 }, ceres: { parent: 'jupiter', r: 50, period: 40, desc: 'A station inside the great ring around Argent. Iron, nickel, cobalt… and pirates.' }, europa: { parent: 'jupiter', r: 78 },
      saturno: { r: 470 }, troyanos: { follow: 'saturno', offset: 1.05 }, pluton: { r: 590, ecc: 0.3, tilt: 2.8 }, kuiper: { r: 650 }, oort: { r: 800 } } },
  tauceti: { sys: { belts: { ceres: { w: 12, n: 1000 }, kuiper: { style: 'double', w: 50 } }, tour: 'Aurum and Silk are <b>twin worlds circling each other</b>, and the black market of Freeport hides <b>among the moons of Crown</b>.' },
    locs: { mercurio: { r: 75 }, tierra: { r: 150 }, venus: { parent: 'tierra', r: 30, period: 20, size: 8 }, luna: { r: 14 }, marte: { r: 205, ecc: 0.1 }, ceres: { r: 252 }, jupiter: { r: 332 }, saturno: { r: 425 }, titan: { r: 30 }, pluton: { parent: 'saturno', r: 50, period: 26 }, kuiper: { r: 560 }, oort: { r: 720 } } },
  eridani: { sys: { mapfx: ['disk'], belts: { ceres: { style: 'wide', w: 40 }, kuiper: { style: 'wide', w: 80 } }, tour: 'A thick <b>dust disk</b> fills the whole system. Even the corsair den of Snuff hides inside it, close to the star.' },
    locs: { mercurio: { r: 60 }, venus: { r: 105 }, tierra: { r: 150 }, marte: { r: 205 }, pluton: { r: 248, ecc: 0.15, period: 520 }, ceres: { r: 295 }, jupiter: { r: 365 }, saturno: { r: 445 }, kuiper: { r: 565 }, oort: { r: 740 } } },
  vega: { sys: { mapfx: ['comets'], belts: { ceres: { style: 'arcs', w: 40 }, kuiper: { style: 'arcs', w: 70 } }, tour: 'Everything here spins fast on <b>tilted, stretched orbits</b>, the belts are herds of ice, and comets streak across the map.' },
    locs: { mercurio: { r: 70, ecc: 0.2, tilt: 0.3, period: 40 }, venus: { r: 112, ecc: 0.15, tilt: 1.4, period: 66 }, tierra: { r: 158, ecc: 0.1, tilt: 2.3, period: 105 }, marte: { r: 212, ecc: 0.25, tilt: 0.9, period: 180 }, ceres: { r: 272, ecc: 0.2, tilt: 0.5, period: 300 },
      jupiter: { r: 352, ecc: 0.15, tilt: 1.8, period: 550 }, saturno: { r: 442, ecc: 0.2, tilt: 2.6, period: 900 }, pluton: { r: 545, ecc: 0.45, tilt: 0.2, period: 1500 }, kuiper: { r: 612, ecc: 0.3, tilt: 1.1 }, oort: { r: 770, ecc: 0.2 } } },
  altair: { sys: { belts: { ceres: { style: 'arcs', w: 36 } }, tour: 'Tortuga, the pirate capital, <b>swings in on a stretched orbit right past Haven</b>. Ambush Alley trails behind Bulwark, and the great storm-giant is the outermost world.' },
    locs: { tierra: { r: 140 }, pluton: { r: 180, ecc: 0.35, tilt: 1, period: 240 }, marte: { r: 225 }, troyanos: { follow: 'marte', offset: 1.05 }, ceres: { r: 282 }, saturno: { r: 345 }, jupiter: { r: 455, size: 24 }, kuiper: { r: 585 }, oort: { r: 760 } } },
  kepler: { sys: { tour: 'Thalassa, Pearlhaze and Undertow are all <b>moons of the giant Maelstrom</b> — a little system inside the system — and Wreckreef hides among Coralring\'s moons.' },
    locs: { jupiter: { r: 215, size: 24, period: 640 }, tierra: { parent: 'jupiter', r: 44, period: 28, desc: 'An ocean moon of the giant Maelstrom. No land at all: the cities float.' }, luna: { parent: 'tierra', r: 14 }, venus: { parent: 'jupiter', r: 72, period: 45, desc: 'A shimmering cloud moon of Maelstrom. Its people love pearls.' }, europa: { parent: 'jupiter', r: 98, period: 60 },
      mercurio: { r: 90 }, marte: { r: 295 }, ceres: { r: 345 }, saturno: { r: 455 }, troyanos: { follow: 'saturno', offset: -1.05 }, pluton: { parent: 'saturno', r: 54, period: 30 }, kuiper: { r: 600 }, oort: { r: 760 } } },
  rigel: { sys: { starScale: 1.9, mapfx: ['glare'], belts: { ceres: { style: 'double', w: 30 } }, tour: 'Rigel is <b>enormous</b> — so big and bright that its worlds keep their distance.' },
    locs: { mercurio: { r: 120 }, venus: { r: 175 }, tierra: { r: 235 }, marte: { r: 295 }, ceres: { r: 350 }, jupiter: { r: 425 }, saturno: { r: 505 }, pluton: { r: 600 }, kuiper: { r: 665 }, oort: { r: 820 } } },
  betelgeuse: { sys: { starScale: 3.2, mapfx: ['flares'], belts: { ceres: { style: 'wide', w: 30 } }, tour: 'The star is <b>so swollen</b> it fills the middle of the map — Pyre orbits just above its boiling surface.' },
    locs: { mercurio: { r: 78, period: 50 }, venus: { r: 140 }, tierra: { r: 192 }, marte: { r: 250, ecc: 0.15 }, ceres: { r: 302 }, jupiter: { r: 372 }, saturno: { r: 452 }, pluton: { r: 560, ecc: 0.3, tilt: 2 }, kuiper: { r: 620 }, oort: { r: 790 } } },
  orion: { sys: { mapfx: ['nebula'], belts: { ceres: { style: 'arcs', w: 44 }, kuiper: { style: 'arcs', w: 70 } }, tour: 'Newborn worlds on <b>wild, stretched orbits</b> inside glowing clouds; the belts are still clumping together.' },
    locs: { mercurio: { r: 80, ecc: 0.35, tilt: 2.5 }, venus: { r: 122, ecc: 0.3, tilt: 0.4 }, tierra: { r: 166, ecc: 0.25, tilt: 1.6 }, marte: { r: 226, ecc: 0.4, tilt: 2.9 }, ceres: { r: 282, ecc: 0.2, tilt: 0.8 }, jupiter: { r: 362, ecc: 0.3, tilt: 2.1 }, saturno: { r: 452, ecc: 0.25, tilt: 1.2 }, pluton: { r: 545, ecc: 0.5, tilt: 0.1 }, kuiper: { r: 612, ecc: 0.25, tilt: 1.9 }, oort: { r: 780, ecc: 0.3 } } },
  pulsar: { sys: { starScale: 0.55, mapfx: ['beams'], belts: { ceres: { w: 10, n: 800 }, kuiper: { w: 14, n: 600 } }, tour: 'Its worlds orbit in <b>perfect clockwork</b>: perfectly round, evenly spaced orbits, like the marks on a clock face — while the pulsar\'s beams sweep over them.' },
    locs: { mercurio: { r: 70, period: 40, a0: 0.0 }, venus: { r: 125, period: 80, a0: 0.785 }, tierra: { r: 180, period: 120, a0: 1.57 }, marte: { r: 235, period: 160, a0: 2.355 }, ceres: { r: 290, period: 240, a0: 3.14 }, jupiter: { r: 345, period: 320, a0: 3.925 }, saturno: { r: 400, period: 400, a0: 4.71 }, pluton: { r: 455, period: 480, a0: 5.495 }, kuiper: { r: 510, period: 640 }, oort: { r: 640, a0: 0 } } },
  rim: { sys: { mapfx: ['artring'], belts: { ceres: { style: 'arcs', w: 30 } }, tour: 'A <b>golden ring built by the ancients</b> circles the whole star — Ringwork rides right on it.' },
    locs: { mercurio: { r: 75 }, venus: { r: 130 }, tierra: { r: 185 }, marte: { r: 240 }, ceres: { r: 300 }, jupiter: { r: 380 }, saturno: { r: 470 }, pluton: { r: 560 }, kuiper: { r: 630 }, oort: { r: 790 } } },
  sgra: { sys: { mapfx: ['spiral'], belts: { ceres: { style: 'spiral', w: 30 }, kuiper: { style: 'spiral', w: 50 } }, tour: 'Everything <b>spirals inward</b>: fast, stretched orbits and glowing arms of gas falling toward the black hole.' },
    locs: { mercurio: { r: 92, ecc: 0.3, period: 30 }, venus: { r: 140, ecc: 0.25, tilt: 1, period: 55 }, tierra: { r: 196, ecc: 0.2, tilt: 2, period: 90 }, marte: { r: 250, ecc: 0.3, tilt: 3, period: 140 }, ceres: { r: 300, period: 190 }, jupiter: { r: 372, ecc: 0.2, tilt: 0.5, period: 280 }, saturno: { r: 452, ecc: 0.25, tilt: 1.5, period: 400 }, pluton: { r: 545, ecc: 0.5, tilt: 2.4, period: 600 }, kuiper: { r: 602, period: 900 }, oort: { r: 770 } } },
};
for (const id in LAYOUT) Object.assign(SYSTEMS[id], LAYOUT[id].sys, { layout: LAYOUT[id].locs });

// the road to the core: 15 systems from the rim to the black hole
const GALAXY = [
  { id: 'sol', n: 'Sol', star: 'sol', x: -0.78, y: 0.42 },
  { id: 'centauri', n: 'Alpha Centauri', star: 'white', x: -0.62, y: 0.66 },
  { id: 'barnard', n: 'Barnard\'s Star', star: 'red', x: -0.30, y: 0.76 },
  { id: 'sirius', n: 'Sirius', star: 'white', x: 0.04, y: 0.72 },
  { id: 'tauceti', n: 'Tau Ceti', star: 'sol', x: 0.34, y: 0.56 },
  { id: 'eridani', n: 'Epsilon Eridani', star: 'orange', x: 0.56, y: 0.28 },
  { id: 'vega', n: 'Vega', star: 'blue', x: 0.62, y: -0.06 },
  { id: 'altair', n: 'Altair', star: 'white', x: 0.48, y: -0.36 },
  { id: 'kepler', n: 'Kepler', star: 'sol', x: 0.18, y: -0.52 },
  { id: 'rigel', n: 'Rigel', star: 'blue', x: -0.16, y: -0.46 },
  { id: 'betelgeuse', n: 'Betelgeuse', star: 'red', x: -0.38, y: -0.22 },
  { id: 'orion', n: 'Orion Nebula', star: 'blue', x: -0.36, y: 0.08 },
  { id: 'pulsar', n: 'The Pulsar', star: 'white', x: -0.14, y: 0.24 },
  { id: 'rim', n: 'Core Rim', star: 'orange', x: 0.12, y: 0.12 },
  { id: 'sgra', n: 'Sagittarius A*', star: 'hole', x: 0, y: 0 },
];
const sysId = () => (S && S.sys) || 'sol';
const sysDef = () => SYSTEMS[sysId()];
const sysName = () => sysDef().n;
const nextSystem = () => GALAXY[GALAXY.findIndex(g => g.id === sysId()) + 1];

// rebuild the world for a star system: start from Sol, then apply that system's overrides
function applySystem(id) {
  const D = SYSTEMS[id] || SYSTEMS.sol, base = SOL_SNAP;
  for (const l of LOCS) {
    const b = base.locs.find(x => x.id === l.id), o = { ...((D.locs || {})[l.id] || {}), ...((D.layout || {})[l.id] || {}) };
    for (const k of Object.keys(l)) if (k !== 'id') delete l[k];
    Object.assign(l, JSON.parse(JSON.stringify(b)), JSON.parse(JSON.stringify({ ...o, field: undefined })));
    if (b.field || o.field) l.field = { ...(b.field || {}), ...(o.field || {}) };
    if (!l.field || !Object.keys(l.field).length) delete l.field;
  }
  for (const f in FACTIONS) Object.assign(FACTIONS[f], base.factions[f], (D.factions || {})[f] || {});
  UNLOCKS.forEach((u, i) => Object.assign(u, base.unlocks[i], (D.unlocks || {})[i] || {}));
  for (const p of PROJECTS) Object.assign(p, base.projects.find(x => x.id === p.id), (D.projects || {})[p.id] || {});
  FIELDS.splice(0, FIELDS.length, ...NODES.filter(l => l.field));
  for (const k in TEX) delete TEX[k];
  snapshotLocBase();
  if (S) applyNukes();
}
// old saves (and new ores) may lack market entries: make sure every market item has a price state
function ensureMarkets() {
  for (const l of NODES) if (l.market) {
    S.sat[l.id] = S.sat[l.id] || {}; S.drift[l.id] = S.drift[l.id] || {};
    for (const k in l.market) { if (S.sat[l.id][k] == null) S.sat[l.id][k] = 1; if (S.drift[l.id][k] == null) S.drift[l.id][k] = 0; }
  }
}

// ---------- Tribute & Legacy ----------
const LEGACY = {
  ore:       { icon: '⛏', n: 'Prospector\'s Legacy', d: '+10% ore value everywhere', cost: lv => Math.round(8 * Math.pow(1.6, lv)) },
  drones:    { icon: '🤖', n: 'Drone Blueprints', d: 'Drones cost 8% less', cost: lv => Math.round(6 * Math.pow(1.6, lv)) },
  fuel:      { icon: '⛽', n: 'Efficient Drives', d: 'Fuel costs 8% less', cost: lv => Math.round(4 * Math.pow(1.5, lv)) },
  quick:     { icon: '🗺', n: 'Head Start', d: 'Start each system with the Star Map open and 50K credits', max: 1, cost: () => 15 },
  laserPlan: { icon: '✦', n: 'Laser Plans', d: 'Start each system with +5 laser levels', max: 3, cost: lv => 6 * Math.pow(2, lv) },
  cargoPlan: { icon: '▣', n: 'Cargo Plans', d: 'Start each system with +5 cargo bay levels', max: 3, cost: lv => 6 * Math.pow(2, lv) },
  extrPlan:  { icon: '⚗', n: 'Extractor Plans', d: 'Start each system with +5 extractor levels', max: 3, cost: lv => 6 * Math.pow(2, lv) },
};
// the cheapest Legacy upgrade you could buy right now (null if none)
function legacyAffordable() {
  const G = S && S.galaxy; if (!G) return null;
  let best = null;
  for (const k in LEGACY) { const L = LEGACY[k], lv = G.legacy[k] || 0; if (L.max && lv >= L.max) continue; const c = L.cost(lv); if (c <= G.tribute && (!best || c < best.c)) best = { k, c }; }
  return best;
}
const legacyLv = k => (S && S.galaxy && S.galaxy.legacy[k]) || 0;
// tools found in the galaxy stay with you forever (drill from Barnard, tractor pulse from Tau Ceti)
const hasTool = k => !!(S && S.galaxy && S.galaxy.tools && S.galaxy.tools[k]);
const conquered = () => (S && S.galaxy ? S.galaxy.done.length : 0);
const tributeRate = () => conquered();   // per minute: each conquered system pays 1 Tribute a minute
function tributeTick(dt) { if (S && S.galaxy && conquered()) S.galaxy.tribute += tributeRate() * dt / 60; }
function buyLegacy(k) {
  const L = LEGACY[k], G = S.galaxy, lv = G.legacy[k] || 0;
  if (L.max && lv >= L.max) return false;
  const c = L.cost(lv); if (G.tribute < c) return false;
  G.tribute -= c; G.legacy[k] = lv + 1;
  // start bonuses also apply right away in the system you're in
  if (k === 'laserPlan') S.lv.laser += 5; if (k === 'cargoPlan') S.lv.cargo += 5; if (k === 'extrPlan') S.lv.extractor += 5;
  if (k === 'quick') { S.credits += 50000; S.stats.earned = Math.max(S.stats.earned, UNLOCKS[U.MAP].at); checkUnlocks(); }
  if (typeof recalcShip === 'function') recalcShip();
  save(); updateHUD(); return true;
}
// one-off Tribute for leaving a system: the more you achieved there, the more it pays
// megaprojects pay Tribute by how big they are: 2 for the Mass Driver … 15 for the Nova Cannon
const projTribute = p => Math.round(2 + 1.5 * Math.log10(p.cost / 4e4));
const allyFactions = () => Object.keys(FACTIONS).filter(f => f !== 'piratas' && factionAlive(f));
function jumpBonus() {
  let b = 10, why = ['base 10'];
  if (S.gateOpen) { b += 5; why.push('final boss +5'); }
  // wars are a side dish: only your first 3 ally stars count for Tribute (5 each)
  const st = Math.min(3, Object.values(S.allies || {}).reduce((a, x) => a + x, 0)); if (st) { b += 5 * st; why.push(`ally stars +${5 * st}`); }
  const pj = sysProjects().filter(p => built(p.id)).reduce((a, p) => a + projTribute(p), 0); if (pj) { b += pj; why.push(`megaprojects +${pj}`); }
  // what is still on the table in this system
  const left = [];
  if (!S.gateOpen) left.push({ n: 'Defeat the final guardian', t: 5 });
  for (const p of sysProjects()) if (!built(p.id)) left.push({ n: p.n, t: projTribute(p), cost: p.cost });
  const starsLeft = 3 - Math.min(3, Object.values(S.allies || {}).reduce((a, x) => a + x, 0));
  if (starsLeft) left.push({ n: `Win ${starsLeft} more war${starsLeft > 1 ? 's' : ''} as an ally`, t: 5 * starsLeft });
  return { b, why, left, max: b + left.reduce((a, x) => a + x.t, 0) };
}
function jumpTo(id) {
  const D = SYSTEMS[id]; if (!D || !S.gateOpen) return false;
  const G = S.galaxy || { tribute: 0, legacy: {}, done: [], life: { earned: 0, mined: 0, kills: 0, days: 0 } };
  const from = sysId(), bonus = jumpBonus().b;
  if (!G.done.includes(from)) G.done.push(from);
  G.tools = G.tools || {}; if (D.gift) G.tools[D.gift] = 1;
  G.tribute += bonus;
  G.life.earned += S.stats.earned; G.life.mined += S.stats.mined; G.life.kills += S.stats.kills; G.life.days += S.day;
  const peak = S.stats.peak || 0, muted = S.muted;
  S = null;
  applySystem(id);
  newGame();
  Object.assign(S, { sys: id, galaxy: G, muted }); S.stats.peak = peak;
  // Legacy start bonuses
  S.lv.laser += 5 * (G.legacy.laserPlan || 0); S.lv.cargo += 5 * (G.legacy.cargoPlan || 0); S.lv.extractor += 5 * (G.legacy.extrPlan || 0);
  if (G.legacy.quick) { S.credits = 50000; S.stats.earned = UNLOCKS[U.MAP].at; checkUnlocks(); pendingUnlocks = []; }
  S.fuel = ship.fuelMax; S.hull = ship.hpMax;
  S.news = []; addNews('🌀', `You came through the gate to <b>${D.n}</b>. A new system to conquer.`, '#d9b3ff');
  save();
  shownCredits = S.credits;
  setScene(MineScene, 'luna');
  updateHUD(); updateTicker();
  setTimeout(() => { showModal({ icon: '', title: `Welcome to ${D.n}`, cls: 'unlock', html: `<div class="unl-tag">SYSTEM ${GALAXY.findIndex(g => g.id === id) + 1} / ${GALAXY.length}</div><canvas id="sysPortrait" class="sys-portrait" width="460" height="230"></canvas>${D.tour ? `<p class="tour">${D.tour}</p>` : ''}<p>${D.intro || ''}</p><div class="trib-call">⬢ <b>${Math.floor(G.tribute)} Tribute</b> to spend (+${bonus} for leaving ${SYSTEMS[from].n}). Spend it on <b>Legacy</b> now — permanent bonuses that make ${D.n} much faster.</div>`,
    buttons: legacyAffordable() ? [{ label: '⬢ Spend Tribute on Legacy', cls: 'primary', fn: () => setTimeout(() => { GalaxyScene.sel = id; openGalaxy(); }, 50) }, { label: 'Later', fn: () => {} }] : [{ label: 'Let\'s mine', cls: 'primary', fn: () => {} }] }); startPortrait(); }, 400);
  return true;
}

// an animated portrait of the system you just arrived in: its star, orbits, belts and worlds
function startPortrait() {
  const c = $('sysPortrait'); if (!c) return;
  const x = c.getContext('2d'), w = c.width, h = c.height, t0 = performance.now();
  let maxR = 0; for (const l of NODES) if (!l.secret) { const p = locPos(l, 0); maxR = Math.max(maxR, Math.hypot(p.x, p.y)); }
  const sc = Math.min(w * 0.48, h * 0.9) / (maxR + 30);
  const frame = () => {
    if (!document.body.contains(c)) return;
    const t = (performance.now() - t0) / 1000, day = t * 6;
    x.fillStyle = '#04060f'; x.fillRect(0, 0, w, h);
    const cx = w / 2, cy = h / 2;
    x.save(); x.translate(cx, cy); x.scale(1, 0.62); x.translate(-cx, -cy);   // a tilted view
    for (const f of sysDef().mapfx || []) if (f === 'disk' || f === 'nebula' || f === 'spiral' || f === 'glare') glow(x, cx, cy, maxR * sc * 1.1, f === 'nebula' ? '#ff7ac833' : f === 'glare' ? '#9cc8ff33' : '#ff9a5a33', 0.9);
    if ((sysDef().mapfx || []).includes('artring')) { x.strokeStyle = 'rgba(255,210,120,0.6)'; x.lineWidth = 3; x.beginPath(); x.arc(cx, cy, 470 * sc, 0, TAU); x.stroke(); }
    for (const l of LOCS) if (!l.parent && !l.follow && !l.secret && l.r) { x.strokeStyle = 'rgba(120,170,255,0.22)'; x.lineWidth = 1; x.beginPath(); x.ellipse(cx, cy, l.r * sc, l.r * sc * (1 - (l.ecc || 0)), l.tilt || 0, 0, TAU); x.stroke(); }
    for (const id of ['ceres', 'kuiper']) {
      const b = LOC[id], B = Object.assign({}, BELT_DEF[id], (sysDef().belts || {})[id] || {}); if (B.style === 'none') continue;
      const cols = beltCols(id), c0 = b.parent ? locPos(b.parent, day) : { x: 0, y: 0 }, R = b.parent ? b.r * 1.6 : b.r + B.dr;
      for (let i = 0; i < 420; i++) {
        const q = BELTP[i]; let a = q.a + day / B.period * TAU * q.sp, rr = R + q.u * B.w;
        if (B.style === 'arcs') { a = q.k * TAU / 3 + q.u * 0.55 + day / B.period * TAU; rr = R + (q.v - 0.5) * B.w * 0.8; }
        else if (B.style === 'double') rr = R + (q.k === 0 ? -1 : 1) * B.w * 0.75 + q.u * B.w * 0.25;
        else if (B.style === 'spiral') { a = q.v * TAU * 1.5 + (q.k % 2) * Math.PI + day / B.period * TAU; rr = R * (0.35 + q.v * 0.9) + q.u * B.w * 0.3; }
        else if (B.style === 'wide') rr = R + q.u * B.w * 2.6;
        const p = orbitXY(b.parent ? {} : b, a, rr); x.fillStyle = cols[Math.floor(q.c * cols.length)]; x.globalAlpha = 0.7; x.fillRect(cx + (c0.x + p.x) * sc, cy + (c0.y + p.y) * sc, 1.2, 1.2);
      }
      x.globalAlpha = 1;
    }
    x.restore();
    drawSun(x, cx, cy, 9 * (sysDef().starScale || 1), t, sysDef().star);
    if (sysDef().companion) drawSun(x, cx + 34, cy - 14, 5, t, sysDef().companion);
    for (const l of LOCS) {
      if (l.secret || l.id === 'troyanos') continue;
      // moons spread out so you can see them
      const pp = o => { const r0 = locPos(o, day); if (!o.parent) return r0; const q0 = locPos(o.parent, day), q = pp(LOC[o.parent]); return { x: q.x + (r0.x - q0.x) * 2.6, y: q.y + (r0.y - q0.y) * 2.6 }; };
      const p = pp(l);
      const px = cx + p.x * sc, py = cy + p.y * sc * 0.62, r = Math.max(2.5, l.size * 0.55);
      drawPlanet(x, px, py, r, l, Math.atan2(cy - py, cx - px), t);
      if (!l.parent) { x.fillStyle = 'rgba(220,235,255,0.75)'; x.font = '600 10px Rajdhani, sans-serif'; x.textAlign = 'center'; x.fillText(l.n, px, py + r + 10); }
    }
    requestAnimationFrame(frame);
  };
  frame();
}

// ---------- the final boss of each system opens its gate ----------
function finalBossKilled() {
  if (S.gateOpen) return;
  S.gateOpen = 1;
  const nx = nextSystem();
  if (!nx) return showEnding();
  addNews('🌀', `<b>The guardian is destroyed.</b> An ancient jump gate wakes up in ${LOC.oort.n}.`, '#d9b3ff');
  if (typeof pendingChoices !== 'undefined') pendingChoices.push({ icon: '🌀', title: 'The gate awakens', html: `<p>${sysDef().gate}</p><p>Open the <b>Galaxy</b> map to see where it leads${nx ? ` — next stop: <b>${nx.n}</b>` : ''}. You can stay as long as you like: the more you achieve here, the more <b>Tribute</b> you take with you.</p>`, choices: [{ label: 'Open the Galaxy map', cost: 0, fn: () => setTimeout(() => setScene(GalaxyScene), 50) }, { label: 'Later', cost: 0, fn: () => {} }] });
  save();
}

// ---------- the end of the road: the heart of the galaxy ----------
function showEnding() {
  const G = S.galaxy || { done: [], life: { earned: 0, mined: 0, kills: 0, days: 0 }, tribute: 0 };
  G.finished = 1; if (!G.done.includes(sysId())) G.done.push(sysId());
  const L = G.life, earned = L.earned + S.stats.earned, mined = L.mined + S.stats.mined, kills = L.kills + S.stats.kills, days = L.days + S.day;
  addNews('🌌', '<b>The Devourer is gone.</b> You crossed the whole Milky Way, from the rim to its heart.', '#ffd24a');
  save();
  if (typeof pendingChoices !== 'undefined') pendingChoices.push({ icon: '🌌', title: 'The heart of the galaxy', html: `<p>${sysDef().gate}</p>
    <p>From a little moon in the Solar System to the black hole at the center of the Milky Way: <b>15 star systems</b>, all yours.</p>
    <div class="ending-stats"><div><b>${fmt(earned)}</b><small>credits earned</small></div><div><b>${fmt(mined)}</b><small>ore mined</small></div><div><b>${fmt(kills)}</b><small>pirates defeated</small></div><div><b>${fmt(days)}</b><small>days in space</small></div></div>
    <p class="hint">Far beyond the galaxy's edge, your dishes catch a new signal… from <b>Andromeda</b>. A new galaxy is coming in a future update.</p>
    <p>You can keep playing here as long as you like — your Tribute keeps flowing.</p>`,
    choices: [{ label: 'Keep playing', cost: 0, fn: () => {} }, { label: 'Open the Galaxy map', cost: 0, fn: () => setTimeout(() => setScene(GalaxyScene), 50) }] });
}

// ---------- the Galaxy map ----------
const GalaxyScene = {
  t: 0, sel: null, dust: null, prev: null,
  enter() {
    this.prev = this.prev || MapScene;
    if (!this.dust) {
      let s = 7; const r = () => (s = (s * 16807) % 2147483647) / 2147483647;
      this.dust = Array.from({ length: 1400 }, () => {
        const arm = Math.floor(r() * 3), d = Math.pow(r(), 0.7), a = arm * TAU / 3 + d * 5.2 + (r() - 0.5) * 0.7 * (1 - d * 0.5);
        return { a, d, s: r() * 1.6 + 0.4, c: r() < 0.15 ? '#ffd2f0' : r() < 0.4 ? '#bcd4ff' : '#ffffff', o: r() * 0.6 + 0.2 };
      });
    }
    this.sel = this.sel || (nextSystem() || GALAXY[0]).id;
    document.body.classList.add('galaxy');
    $('galPanel').classList.remove('hidden');
    renderGalaxyPanel();
  },
  exit() { document.body.classList.remove('galaxy'); $('galPanel').classList.add('hidden'); },
  update(dt) { this.t += dt; },
  layout() { const wide = W > 760; const R = wide ? Math.min(W * 0.72, H) * 0.46 : Math.min(W * 0.45, (H * 0.44 - 90) / 1.8); return { cx: W * (wide ? 0.36 : 0.5), cy: wide ? H * 0.52 : 82 + R * 0.8, R }; },
  pos(g) { const { cx, cy, R } = this.layout(); return { x: cx + g.x * R, y: cy + g.y * R }; },
  draw(ctx) {
    const t = this.t, { cx, cy, R } = this.layout();
    drawSpaceBg(ctx, W, H, t * 4, t * 2, t);
    // spiral arms
    for (const p of this.dust) {
      const a = p.a + t * 0.01, r = p.d * R * 1.15;
      ctx.globalAlpha = p.o * (0.4 + 0.6 * (1 - p.d)); ctx.fillStyle = p.c;
      ctx.fillRect(cx + Math.cos(a) * r, cy + Math.sin(a) * r * 0.92, p.s, p.s);
    }
    ctx.globalAlpha = 1;
    glow(ctx, cx, cy, R * 0.5, '#ffb07a33', 0.9);
    // the route
    const done = (S.galaxy && S.galaxy.done) || [], cur = sysId();
    for (let i = 0; i < GALAXY.length - 1; i++) {
      const a = this.pos(GALAXY[i]), b = this.pos(GALAXY[i + 1]);
      const lit = done.includes(GALAXY[i].id) || GALAXY[i].id === cur;
      ctx.strokeStyle = lit ? 'rgba(217,179,255,0.55)' : 'rgba(140,160,220,0.18)'; ctx.lineWidth = lit ? 2 : 1;
      ctx.setLineDash(lit ? [] : [4, 6]); ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
    }
    ctx.setLineDash([]);
    // stars
    for (const g of GALAXY) {
      const p = this.pos(g), isDone = done.includes(g.id), isCur = g.id === cur, ready = !!SYSTEMS[g.id], sel = g.id === this.sel;
      if (g.star === 'hole') {
        glow(ctx, p.x, p.y, 46, '#ff9a5a55', 0.9);
        for (let k = 0; k < 3; k++) { ctx.strokeStyle = `rgba(255,${170 - k * 30},${90 - k * 20},${0.7 - k * 0.2})`; ctx.lineWidth = 3 - k; ctx.beginPath(); ctx.ellipse(p.x, p.y, 22 + k * 7, 8 + k * 3, t * 0.2, 0, TAU); ctx.stroke(); }
        ctx.fillStyle = '#000'; ctx.beginPath(); ctx.arc(p.x, p.y, 10, 0, TAU); ctx.fill();
      } else {
        ctx.globalAlpha = ready || isDone ? 1 : 0.45;
        drawSun(ctx, p.x, p.y, isCur ? 7 : 5, t, g.star);
        ctx.globalAlpha = 1;
      }
      if (isDone) { ctx.strokeStyle = '#ffd24a'; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(p.x, p.y, 14, 0, TAU); ctx.stroke(); }
      if (isCur) { const ph = (t * 0.8) % 1; ctx.globalAlpha = 1 - ph; ctx.strokeStyle = '#3de8ff'; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(p.x, p.y, 14 + ph * 16, 0, TAU); ctx.stroke(); ctx.globalAlpha = 1; }
      if (sel) { ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 1.5; ctx.setLineDash([3, 4]); ctx.beginPath(); ctx.arc(p.x, p.y, 20, 0, TAU); ctx.stroke(); ctx.setLineDash([]); }
      // on phones only the important names fit
      if (W <= 760 && !isCur && !sel && !(nextSystem() && g.id === nextSystem().id) && g.star !== 'hole') { if (!ready && !isDone && g.star !== 'hole') drawIcon(ctx, 'lock', p.x, p.y - 12, 8, 'rgba(200,210,240,0.5)'); continue; }
      ctx.font = `700 ${isCur || sel ? 12 : 11}px Rajdhani, sans-serif`; ctx.textAlign = 'center';
      ctx.fillStyle = isCur ? '#3de8ff' : isDone ? '#ffd24a' : ready ? '#e8f1ff' : 'rgba(200,210,240,0.5)';
      ctx.fillText(g.n.toUpperCase(), p.x, p.y + 30);
      if (!ready && !isDone && g.star !== 'hole') drawIcon(ctx, 'lock', p.x, p.y - 18, 10, 'rgba(200,210,240,0.6)');
    }
  },
  onDown(x, y) {
    let best = null, bd = 30;
    for (const g of GALAXY) { const p = this.pos(g), d = Math.hypot(p.x - x, p.y - y); if (d < bd) { bd = d; best = g.id; } }
    if (best) { this.sel = best; sfx('click'); renderGalaxyPanel(); }
  },
};
function renderGalaxyPanel() {
  const G = S.galaxy, g = GALAXY.find(x => x.id === GalaxyScene.sel), i = GALAXY.indexOf(g);
  const done = G ? G.done : [], cur = sysId(), nx = nextSystem();
  let h = `<div class="lp-head"><div><h3>The Galaxy</h3><small>${done.length} of ${GALAXY.length} systems conquered</small></div><button class="x" onclick="closeGalaxy()">✕</button></div>`;
  h += `<div class="gal-trib"><div><small>TRIBUTE</small><b>${Math.floor(G ? G.tribute : 0)}</b></div><span>${conquered() ? `+${tributeRate()} / min from ${conquered()} conquered system${conquered() > 1 ? 's' : ''}` : 'Conquer a system to earn Tribute'}</span></div>`;
  const legacyHtml = () => {
    let x = `<div class="sub">Legacy <small class="dim">· permanent, all systems · bought plans also apply right now</small></div><div class="legacy">`;
    for (const k in LEGACY) {
      const L = LEGACY[k], lv = G.legacy[k] || 0, maxed = L.max && lv >= L.max, c = L.cost(lv);
      x += `<div class="lg-row ${!maxed && G.tribute >= c ? 'can' : ''}"><span>${L.icon} <b>${L.n}</b> ${L.max === 1 ? (lv ? '<small class="good">owned</small>' : '') : `<small>Lv ${lv}${L.max ? '/' + L.max : ''}</small>`}<br><small class="dim">${L.d}</small></span>
        <button class="btn small-btn" ${maxed || G.tribute < c ? 'disabled' : ''} onclick="buyLegacy('${k}') && (sfx('upgrade'), renderGalaxyPanel())">${maxed ? 'Max' : `${c} ⬢`}</button></div>`;
    }
    return x + '</div>';
  };
  const spendFirst = G && legacyAffordable();
  if (spendFirst) h += `<div class="trib-call">⬢ You have <b>${Math.floor(G.tribute)} Tribute</b> to spend. Legacy upgrades are permanent and make every system faster.</div>` + legacyHtml();
  // selected star
  h += `<div class="sub">${g.n} <small class="dim">· system ${i + 1}</small></div>`;
  if (g.id === cur) h += `<p class="hint">You are here.${S.gateOpen ? '' : ' Rule this system and defeat its guardian to open the gate.'}</p>`;
  else if (done.includes(g.id)) h += `<p class="hint">Conquered. It pays you Tribute every minute.</p>`;
  else if (g.star === 'hole') h += `<p class="hint">The supermassive black hole at the heart of the galaxy. The end of the road — and maybe a door to something beyond.</p>`;
  else if (!SYSTEMS[g.id]) h += `<p class="hint">Uncharted. Arrives in a future update.</p>`;
  if (nx && g.id === nx.id) {
    const jb = jumpBonus();
    if (!SYSTEMS[nx.id]) h += `<p class="hint">The gate points here, but this system isn't charted yet — coming in a future update.</p>`;
    else if (!S.gateOpen) h += `<p class="hint">🔒 Defeat ${sysName()}'s guardian to open the gate.</p>`;
    else {
      const full = jb.b >= jb.max;
      h += `<div class="jump-box ${full ? 'full' : ''}"><div class="jb-top"><span>Tribute if you jump now</span><b>${jb.b}<small> / ${jb.max}</small></b></div>
        <div class="meter gold"><i style="width:${Math.round(jb.b / jb.max * 100)}%"></i></div>
        ${full ? '<div class="jb-note good">✔ You earned everything here.</div>' : `<div class="jb-note">⚠ <b>${jb.max - jb.b} Tribute</b> still left in ${sysName()}:</div>${jb.left.slice(0, 3).map(x => `<div class="srow"><span>${x.n}</span><b>+${x.t}</b></div>`).join('')}${jb.left.length > 3 ? `<small class="dim">…and ${jb.left.length - 3} more (select ${sysName()})</small>` : ''}`}</div>
        <button class="btn primary big" onclick="confirmJump('${nx.id}')">🌀 Jump to ${nx.n}</button>
        <p class="hint">Credits, ship upgrades, outposts and freighters stay behind. Tribute, Legacy and records come with you.</p>`;
    }
  }
  if (g.id === cur) {
    const jb = jumpBonus();
    h += `<div class="sub">Tribute for leaving ${sysName()} <small class="dim">· ${jb.b} of ${jb.max} possible</small></div><div class="meter gold"><i style="width:${Math.round(jb.b / jb.max * 100)}%"></i></div>`;
    if (jb.left.length) h += `<div class="trib-left">${jb.left.slice(0, 8).map(x => `<div class="srow"><span>${x.n}${x.cost ? ` <small class="dim">${fmt(x.cost)} cr</small>` : ''}</span><b>+${x.t}</b></div>`).join('')}</div>`;
  }
  // legacy shop
  if (G) { if (!spendFirst) h += legacyHtml(); }
  else h += '<p class="hint">Legacy upgrades unlock after your first jump: spend Tribute on permanent bonuses for every system.</p>';
  $('galPanel').innerHTML = h;
}
function openGalaxy() { sfx('click'); closeSheet(true); GalaxyScene.prev = scene === GalaxyScene ? GalaxyScene.prev : scene === MineScene ? null : scene; setScene(GalaxyScene); }
function closeGalaxy() { sfx('click'); setScene(has(U.MAP) ? MapScene : MineScene, has(U.MAP) ? undefined : S.loc); }
function confirmJump(id) {
  const D = SYSTEMS[id];
  showModal({ icon: '🌀', title: `Jump to ${D.n}?`, html: `<p>Everything you built in <b>${sysName()}</b> stays behind and becomes part of your empire: it pays <b>Tribute</b> every minute.</p><p>You start fresh in ${D.n}: credits, ship upgrades, outposts, freighters and reputation reset. You keep <b>Tribute, Legacy, alliances history and your records</b>.</p><p class="hint">Pirates and rocks are tougher there.</p><div class="trib-call">You'll arrive with <b>${Math.floor((S.galaxy ? S.galaxy.tribute : 0) + jumpBonus().b)} Tribute</b>. Spend it on <b>Legacy</b> as soon as you land (Galaxy button) — it's what makes each new system faster.</div>`,
    buttons: [{ label: 'Jump!', cls: 'primary', fn: () => { sfx('win'); jumpTo(id); } }, { label: 'Not yet', fn: () => {} }] });
}
