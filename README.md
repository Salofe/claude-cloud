# Solar Prospector

A 2D space mining game that starts simple and slowly opens up into trading, pirates, system-wide events and a race for influence across the Solar System. Everything fits in a single HTML file with no dependencies.

**Play:** https://play.clawcade.gg/g/LHgYcmEt, or open `dist/index.html` in a browser. Works with mouse and keyboard or touch.

## How it plays

1. **Mine.** You start inside the Moon's asteroid field. Fly with WASD and hold the mouse button to fire the laser. The farther up you fly, the richer the rocks get, and rare golden asteroids pay a jackpot.
2. **Dock & sell.** The station sits at the bottom of every field. Fly back down into the docking zone to refuel and repair. Once the Star Map is unlocked, you choose where to sell: field depots pay about 0.6×, while city planets pay 2–3.8× (Mars for ice, Titan for Helium-3, Europa for iridium, Pluto for exotics). A full hold sold in one place pushes the price down about 20%.
3. **Automate.** Build a drone outpost in each field. Drones mine slowly but never stop, even while you're offline. Automation starts at roughly 10–15% of active mining income, as in classic idle games: each drone takes 5+ minutes to pay back, costs 18% more than the last, and every outpost level adds only 5 drone slots while doubling output.
4. **Upgrade.** There are 11 upgrade lines (including the Extractor, which makes rocks drop more ore) with up to 60 levels each and exponential costs and effects. Each of the 5 ship classes is a new ship design.
5. **Trade.** Stations sell goods cheap that other planets pay 3–6× for. Stock is limited and refills daily, so trading adds profit to the runs you already make to sell ore.
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

8. **Rule.** Spend your fortune on megaprojects that change the Solar System and show up on the map: Lunar Mass Driver, Deep Space Beacons, Private Security Fleet (escort gunships in every fight), Earth Space Elevator, Terraform Mars, Jump Gate Network, Saturn Ring Megastation and the Dyson Swarm. System powers let you pay to end wars and plagues, fund a construction boom, or clear a zone of pirates.
9. **Win** by reaching 100 influence.

## Development

Source is in `src/`.

```
node build.js              # builds dist/index.html
node tools/thumbnail.js    # generates dist/thumbnail.png and dist/thumbnail-square.png
node tools/balance-sim.js  # simulates an efficient player and prints when each unlock is reached
```

All art is procedural (canvas 2D, including noise-generated planet textures) and all sound is synthesized with WebAudio. Progress is saved to `localStorage`.
