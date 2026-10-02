'use strict';
// ============ LANGUAGE: English + Spanish ============
// Clawcade picks the language (its ES/EN switch, else the device's) and reloads the game when it changes,
// so we read it once at boot. Outside Clawcade: ?lang=es or the browser language.
const LANG = (() => {
  try { const q = new URLSearchParams(location.search).get('lang'); if (q) return q.slice(0, 2) === 'es' ? 'es' : 'en'; } catch (e) {}
  try { if (typeof Clawcade !== 'undefined' && Clawcade.lang) return Clawcade.lang() === 'es' ? 'es' : 'en'; } catch (e) {}
  return (navigator.language || 'en').slice(0, 2) === 'es' ? 'es' : 'en';
})();
const ES = LANG === 'es';
document.documentElement.lang = LANG;
// every player-facing string lives in TXT: { key: { en, es } }. Each module adds its own section with Object.assign(TXT, {...}).
const TXT = {};
// tx('key', { n: 5 }) → the string in the player's language, with {n}-style placeholders filled in
function tx(key, vars) {
  const e = TXT[key];
  let s = !e ? key : (ES && e.es != null ? e.es : e.en);
  if (vars) s = s.replace(/\{(\w+)\}/g, (m, k) => (vars[k] != null ? vars[k] : m));
  return s;
}
// pick between two strings directly (only for tiny one-off pieces like plural endings)
const L = (en, es) => (ES ? es : en);
// plural helper: plural(3, 'rock', 'rocks') — Spanish passes its own forms
const plural = (n, one, many) => (n === 1 ? one : many);
