# Riftguard: 30-second trailer

`riftguard_trailer.mp4` is a 30-second, 1080p30 trailer for **Riftguard, a 4v4 hero arena** ([play.clawcade.gg/g/CXhdNnoY](https://play.clawcade.gg/g/CXhdNnoY)).
`riftguard_trailer_vertical.mp4` is the same cut at 1080×1920 for TikTok, Reels and Shorts. The footage sits in a 1080×1440 panel (a 1.33× crop) over a blurred fill, and the titles are re-laid out for the platforms' safe zones (`compositor/vertical.html`).

Everything in it was made with code. The footage is real gameplay rendered by the game itself, the score is synthesized, and the titles are composited on a canvas.

## Edit (120 BPM, one bar = 2 s)

| Time | Section | What's on screen |
|---|---|---|
| 0–4 s | Hook | Three bullet-time freeze frames with an orbiting camera: **20 HEROES / 4V4 ONLINE / 0 DOWNLOADS**. Time ramps back to full speed under *IT RUNS IN YOUR BROWSER*, then a white flash |
| 4–12 s | Drop | One cut per beat: first-person kills with the real HUD, Monolith's Eruption, Riptide's Tsunami, Rime's blizzard on the payload, Kodiak's Ursa Major |
| 12–16 s | Roll call | Eight heroes, 0.5 s each, in slow motion with name, role and tagline |
| 16–24 s | Climax | Arclight Overload with a speed ramp, Cinder's Firestorm, the 4 maps, a slow-motion team fight, first-person Rampage |
| 24–30 s | End card | A beat of silence, a logo slam over the hero lineup, then *PLAY FREE IN YOUR BROWSER* and the play link |

## How it was made

This follows the "every frame is a pure function of time" approach used for code-rendered videos, applied to a live 3D game.

1. **Virtual clock** (`capture/vclock.js`). `performance.now`, `Date.now`, timers, `requestAnimationFrame` and `Math.random` are replaced with a clock that only advances when the capture script says so. A frame that takes 5 s to render in headless Chromium still lands exactly 1/30 s after the previous one.
2. **Local server** (`capture/host.js`). This is a stand-in for the Clawcade platform that answers the Clawcade Server protocol over `postMessage` and runs the game's own authoritative `SERVER` code in the page: bots, abilities, ultimates, rounds. Matches are fully deterministic, so a moment found while scouting replays identically when captured. A small hook lets the bot brain drive our own player (the "puppet"), which gives first-person shots with the real HUD. The same hook sets fixed hero lineups and faster ult charge so the good stuff happens on camera.
3. **Scouting** (`capture/scout2.mjs`, `analyze.py`, `preview.mjs`). Four matches, one per map, are fast-forwarded without rendering and every kill and ultimate is logged. Candidate moments are ranked (ults near crowds, multi-kills) and checked with preview stills.
4. **Camera director** (`capture/director.js`). It provides orbit, over-the-shoulder follow, dolly and track shots. Orbit angles are picked by line-of-sight raycasts against the game's collision world, the camera is pulled in when it would clip into walls, and it aims at the rendered avatar. Slow motion and freeze frames come from advancing the clock less, or not at all, per output frame.
5. **Capture** (`capture/capture.mjs`, `jobs/*.json`, `runall.sh`). Each job boots the game, replays a match to the chosen tick and captures its shots at 1920×1080. Four jobs run in parallel.
6. **Score** (`audio/music.py`). The score is synthesized in NumPy/SciPy at 120 BPM in D minor: braams, impacts, a riser and reverse cymbal into the drop, a hybrid drum groove, sidechained bass and arps, stabs on each roll-call cut, a heroic lead in the climax, and a logo hit. All hits sit on the edit's cut points.
7. **Compositor** (`compositor/index.html`, `render.mjs`). A canvas page with `draw(t)` holds the edit decision list, the game's own typography (Oxanium italic with the logo's gold gradient, Rajdhani labels), zoom punches, chromatic aberration on cuts, the grade, vignette, grain, and the end card. `render.mjs` writes the frames, then ffmpeg muxes them with the score.

## Re-rendering

```
# serve the downloaded game bundle (index.html, game.js, styles.css) on :8765 and this folder's parent on :8766
cd capture && npm i playwright ffmpeg-static
node scout2.mjs A 150            # scout a match (A–D in matches.mjs)
./runall.sh                      # capture every job in jobs/ at 1080p
cd ../audio && python3 music.py  # score.wav
cd ../compositor && node render.mjs 0 30 frames
ffmpeg -framerate 30 -i frames/f%05d.jpg -i ../audio/score.wav -c:v libx264 -crf 18 -pix_fmt yuv420p -c:a aac -b:a 256k -shortest riftguard_trailer.mp4
```

The game bundle itself isn't in this folder. The capture scripts load a local copy of the published build, with one line patched in `TierSettings` so render quality can be overridden.
