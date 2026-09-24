# Solar Prospector

A 2D space mining game that starts simple and slowly opens up into trading, pirates, system-wide events and a race for influence across the Solar System. Everything fits in a single HTML file with no dependencies.

**Play:** https://play.clawcade.gg/g/LHgYcmEt, or open `dist/index.html` in a browser. Works with mouse and keyboard or touch.

## How it plays

1. **Mine.** You start inside the Moon's asteroid field. Fly with WASD and hold the mouse button to fire the laser. Big rocks split apart and drop glowing ore.
2. **Dock.** Docking sells your ore, refuels and repairs automatically. Spend your credits on upgrade cards. A new hull gives you a whole new ship (5 designs).
3. **Unlock.** Your lifetime earnings open up the game one layer at a time:

| Earned | Unlock |
|---|---|
| 600 | Star Map, travel and fuel, Earth |
| 3,000 | Mars, Mercury, shields |
| 8,000 | Asteroid Belt, pirates and auto-battles, weapons |
| 18,000 | Trading, contracts, system events (wars, plagues, booms), Venus |
| 40,000 | Jupiter system, scanner |
| 90,000 | Saturn system, station investments and influence |
| 180,000 | Pluto's black market and the Kuiper Belt |

4. **Win** by reaching 100 influence.

## Development

Source is in `src/`.

```
node build.js              # builds dist/index.html
node tools/thumbnail.js    # generates dist/thumbnail.png and dist/thumbnail-square.png
```

All art is procedural (canvas 2D, including noise-generated planet textures) and all sound is synthesized with WebAudio. Progress is saved to `localStorage`.
