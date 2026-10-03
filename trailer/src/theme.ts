import { loadFont } from "@remotion/fonts";
import { staticFile } from "remotion";

// fonts ship with the project (the render machine may not reach Google Fonts)
export const HEAD = "Orbitron";
export const BODY = "Rajdhani";
loadFont({ family: HEAD, url: staticFile("fonts/orbitron.woff2"), weight: "400 900" });
loadFont({ family: BODY, url: staticFile("fonts/rajdhani-600.woff2"), weight: "600" });
loadFont({ family: BODY, url: staticFile("fonts/rajdhani-700.woff2"), weight: "700" });

export const FPS = 30;
export const BEAT = 15; // 120 BPM
export const BAR = 60;
/** first frame of a 1-based bar */
export const bar = (n: number, beat = 0) => (n - 1) * BAR + beat * BEAT;

export const CYAN = "#3de8ff";
export const GOLD = "#ffc857";
export const VIOLET = "#b48cff";
export const RED = "#ff4d6d";
