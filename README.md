# Solar Prospector

A 2D space mining game that starts simple and slowly opens up into trading, pirates, system-wide events and a race for influence across the Solar System. Everything fits in a single HTML file with no dependencies.

**Play:** https://play.clawcade.gg/g/LHgYcmEt, or open `dist/index.html` in a browser. Works with mouse and keyboard or touch.

## How it plays

1. **Mine.** You start inside the Moon's asteroid field. Fly with WASD and hold the mouse button to fire the laser. The farther up you fly, the richer the rocks get, and rare golden asteroids pay a jackpot.
2. **Dock & sell.** The station sits at the bottom of every field. Fly back down into the docking zone to refuel and repair. Once the Star Map is unlocked, you choose where to sell: field depots pay little for quick cash, while planets like Earth pay about double. The dock screen shows which stations pay more and how much fuel it takes to get there.
3. **Automate.** Build a drone outpost in each field. Drones mine slowly but never stop, even while you're offline. Automation starts at roughly 10–15% of active mining income, as in classic idle games: each drone takes 5+ minutes to pay back, costs 18% more than the last, and every outpost level adds only 5 drone slots while doubling output.
4. **Upgrade.** There are 10 upgrade lines with up to 60 levels each and exponential costs and effects. Each of the 5 ship classes is a new ship design.
5. **Fight.** Pirates attack in the dangerous zones. You fly and shoot in real time, and destroyed ships drop credits. During travel you can fight, run, pay them off, or warp out.
6. **Unlock.** Your lifetime earnings open up the Solar System one layer at a time:

| Earned | Unlock |
|---|---|
| 250 | Drone outposts |
| 1.5K | Star Map, Earth, Refinery |
| 10K | Mars, Mercury, shields |
| 60K | Asteroid Belt, pirates, guns |
| 400K | Trading, contracts, system events, Venus |
| 3M | Jupiter system, scanner |
| 25M | Saturn system, station investments and influence |
| 200M | Pluto's black market and the Kuiper Belt |

7. **Rule.** Spend your fortune on megaprojects that change the Solar System and show up on the map: Lunar Mass Driver, Deep Space Beacons, Private Security Fleet (escort gunships in every fight), Earth Space Elevator, Terraform Mars, Jump Gate Network, Saturn Ring Megastation and the Dyson Swarm. System powers let you pay to end wars and plagues, fund a construction boom, or clear a zone of pirates.
8. **Win** by reaching 100 influence.

## Development

Source is in `src/`.

```
node build.js              # builds dist/index.html
node tools/thumbnail.js    # generates dist/thumbnail.png and dist/thumbnail-square.png
```

All art is procedural (canvas 2D, including noise-generated planet textures) and all sound is synthesized with WebAudio. Progress is saved to `localStorage`.
