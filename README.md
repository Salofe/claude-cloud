# Solar Prospector

A 2D space mining game that starts simple and slowly opens up into trading, pirates, system-wide events and a race for influence across the Solar System. Everything fits in a single HTML file with no dependencies.

**Play:** https://play.clawcade.gg/g/LHgYcmEt, or open `dist/index.html` in a browser. Works with mouse and keyboard or touch.

## How it plays

1. **Mine.** You start inside the Moon's asteroid field. Fly with WASD and hold the mouse button to fire the laser. The farther up you fly, the richer the rocks get, and rare golden asteroids pay a jackpot.
2. **Dock & sell.** The station sits at the bottom of every field. Fly back down into the docking zone to refuel and repair. Once the Star Map is unlocked, you choose where to sell: field depots pay about 0.6×, while city planets pay 2–3.8× (Mars for ice, Titan for Helium-3, Europa for iridium, Pluto for exotics). A full hold sold in one place pushes the price down about 20%. Fuel is priced from your lifetime earnings (a round trip costs roughly 5–13% of a good haul), each station has its own fuel price, and a full hold burns up to 140% of the fuel of an empty one.
3. **Automate.** Build a drone outpost in each field. Drones mine slowly but never stop, even while you're offline. Automation starts at roughly 10–15% of active mining income, as in classic idle games: each drone takes 5+ minutes to pay back, costs 18% more than the last, and every outpost level adds only 5 drone slots while doubling output.
4. **Upgrade.** There are 11 upgrade lines (including the Extractor, which makes rocks drop more ore) with up to 60 levels each and exponential costs and effects. Each of the 5 ship classes is a new ship design.
5. **Trade.** Each station's Trade tab lists the best deals from there: one tap buys the goods and plots your course. Stock is limited and refills daily, and every market has a **demand** meter per good: deliveries use it up and it only recovers ~3%/day, so a route pays well once or twice and then you move on (shortages and wars refill demand). Hire freighters (up to 10, max 3 per route) to run a route automatically; their income follows live prices and events.
6. **Fight.** Pirates attack in the dangerous zones. You fly and shoot in real time, and destroyed ships drop credits. During travel you can fight, run, pay them off, or warp out.
7. **Unlock.** Your lifetime earnings open up the Solar System one layer at a time:

| Earned | Unlock |
|---|---|
| 250 | Drone outposts, Cargo Bay, Extractor |
| 2K | Star Map, Earth, Refinery; you choose where to sell |
| 15K | Mars, Mercury, shields |
| 500K | Asteroid Belt, pirates, guns |
| 4M | Trading, contracts, system events, Venus |
| 20M | Jupiter system, scanner |
| 150M | Saturn system, station investments and influence |
| 1.5B | Pluto's black market and the Kuiper Belt |

8. **Rule.** Spend your fortune on megaprojects that change the Solar System and show up on the map: Lunar Mass Driver, Deep Space Beacons, Private Security Fleet (escort gunships in every fight), Earth Space Elevator, Terraform Mars, Jump Gate Network, Saturn Ring Megastation, the Dyson Swarm and finally the Nova Cannon.
   - **Planet powers** (per planet, each with a cooldown): fund public works, start a construction boom, hire mercenaries; back a side in a war and fund offensives; later incite a war or broker peace.
   - **Wars** have a visible front (HUD bar, map front lines, planet mini-bars). It drifts daily with each side's strength; you push it by selling ore or supplies to the side you back (+30% on metals there), funding offensives and beating raiders in their space. A side wins at 100%, or leads by 25% when time runs out; otherwise it's a stalemate. If your side wins and you pushed at least 15%, they become a permanent ally (+15% ore at their stations per win, max 3 stars) and you pick one permanent spoil: Mining rights (+10% ore everywhere), Drone contract (drones −12%) or Fuel treaty (fuel −15%). End any crisis from the Empire panel.
   - **Dynamic events:** wars, plagues, famines, refugee crises, booms, gold rushes, market crashes, tech breakthroughs, comet swarms, pirate warlords, strikes and solar storms. Some ask you to decide: elections, independence movements, rival buyouts and colony bailouts.
   - **Nova Cannon:** destroy a planet (never Earth or the Moon). Its station and faction are gone, every faction fears you, and what's left becomes the richest debris field in the system.
   - Event effects never stack: the strongest boost and the strongest drop apply.
9. **Win** by reaching 100 influence.

## Development

Source is in `src/`.

```
node build.js              # builds dist/index.html
node tools/thumbnail.js    # generates dist/thumbnail.png and dist/thumbnail-square.png
node tools/balance-sim.js  # simulates an efficient player and prints when each unlock is reached
```

All art is procedural (canvas 2D, including noise-generated planet textures) and all sound is synthesized with WebAudio. Progress is saved to `localStorage` under the versioned key `solar_prospector_v3` (about 20 KB even late in the game). Clawcade persists each game's localStorage on the player's device.

## The galaxy

Defeating a system's final guardian opens its **jump gate**. The **Galaxy** map (HUD button, or "Enter the gate" at the final field) shows the road of 15 star systems from the rim to **Sagittarius A\***, the black hole at the core. Jumping starts you fresh in the next system — credits, ship upgrades, outposts, freighters and reputation stay behind — while you keep **Tribute**, **Legacy** and your records.

- **Tribute**: every conquered system pays 1 per minute (also offline, same 8 h cap), plus a one-off jump bonus (10 + 5 for the guardian + 3 per ally star + 2 per megaproject).
- **Legacy** (spent with Tribute, permanent, all systems): +10% ore value per level, drones −8%, fuel −8%, Head Start (Star Map open + 50K credits), and Laser/Cargo/Extractor plans (+5 starting levels each).
- Each system is hand-made on top of Sol's layout (same slots, new names, looks, ores, factions, texts and boss) and is harder: tougher rocks and pirates (`SYSTEMS` in `src/galaxy.js`). Run `SYS=centauri LEG='{"ore":4,"quick":1}' node tools/balance-sim.js` to simulate one.
- **Alpha Centauri** (system 2): binary stars, ocean world Pandora, the **Shard Belt** of **crystal asteroids** that shatter into fast shards, and the **Hive Queen**, who keeps spawning swarmers. Simulated: ~150 min without Legacy, ~100 min with a typical Legacy (Sol: ~140 min).

## Fields & comets

Every field has its own signature ores: the Moon (iron, ice), Mercury (platinum, **Sunstone**), the Main Belt (nickel, **Cobalt**, iridium), the Trojans (iridium), Saturn's rings (Helium-3, **Ring Pearls**), the Kuiper Belt (iridium, Ring Pearls, exotics) and the Oort Cloud (exotics, **Void Shards**). Average field values match the old balance. Every 45–80 s a **comet** streaks across the field; break it before it escapes for ice and a handful of the field's most valuable ore.

## The end of the Solar System

Reaching 100 influence makes you ruler of the Solar System — and reveals a **signal from the Oort Cloud**, a new far-out mining field. Mining there draws out the **Alien Sentinel** (a boss with alien drones and spread shots). Destroying it wakes an ancient **jump gate**: the way to the galaxy (next update).

Combat is a side dish. `tools/balance-sim.js` prints a combat check per stage (time to kill a typical fleet and the warlord/Sentinel, and the share of hull lost) for a player who buys enough guns; enemy strength per zone is `Z_ENEMY` in `src/data.js`.

## Icons

All icons are hand-drawn vector paths in `src/icons.js` (24×24 grid, duotone neon style). Game text uses emoji as keys; a MutationObserver swaps them for inline SVG in the UI, and `drawIcon`/`drawIconRow` render the same paths on the canvases, so no emoji is ever shown.

## Time

One day passes every 50 seconds on any screen (paused during fights, while travelling — trips count their own days — and while a popup asks you something). Days also pass while you're away, up to the same 8-hour offline cap that pays your drones (60% rate); while away your accepted contracts and the war you back wait for you and no decision popups are queued. The welcome-back screen says how long you were gone, that only the last 8 hours were paid, how many days passed and the main news.
