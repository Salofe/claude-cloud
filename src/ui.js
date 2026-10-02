'use strict';
// ============ INTERFACE (DOM) ============
const $ = id => document.getElementById(id);
const isBlocking = () => !$('modal').classList.contains('hidden') || !$('sheet').classList.contains('hidden');
let dockTab = 'upg', lastDock = null, shownCredits = 0;

// ---------- strings (English + Spanish) ----------
Object.assign(TXT, {
  ui_sysnews_day: { en: 'SYSTEM NEWS · DAY {d}', es: 'NOTICIAS · DÍA {d}' },
  ui_day: { en: 'DAY {d}', es: 'DÍA {d}' },
  ui_war_front: { en: 'WAR FRONT', es: 'FRENTE DE GUERRA' },
  ui_next_unlock: { en: 'NEXT UNLOCK', es: 'PRÓXIMO DESBLOQUEO' },
  ui_earned_of: { en: '{a} / {b} cr earned', es: '{a} / {b} cr ganados' },
  ui_final_goal: { en: 'FINAL GOAL', es: 'META FINAL' },
  ui_reach100: { en: '👑 Reach 100 influence', es: '👑 Llega a 100 de influencia' },
  ui_infl_line: { en: 'Influence {n}/100 · invest & upgrade outposts', es: 'Influencia {n}/100 · invierte y mejora puestos' },
  ui_infl_signal: { en: ' · then trace the signal beyond {loc}', es: ' · luego rastrea la señal más allá de {loc}' },
  ui_final_guardian: { en: 'FINAL GUARDIAN', es: 'GUARDIÁN FINAL' },
  ui_find_source: { en: '📡 Find the source in {loc}', es: '📡 Encuentra la fuente en {loc}' },
  ui_find_source_d: { en: 'Mine there to draw it out. Bring good guns and shields.', es: 'Mina allí para hacerlo salir. Lleva buenos cañones y escudos.' },
  ui_gate_open: { en: 'THE GATE IS OPEN', es: 'EL PORTAL ESTÁ ABIERTO' },
  ui_galaxy_awaits: { en: '🌀 The galaxy awaits', es: '🌀 La galaxia te espera' },
  ui_galaxy_awaits_d: { en: 'Open the Galaxy map to jump — or stay and earn more Tribute first.', es: 'Abre el mapa de la Galaxia para saltar, o quédate y gana más Tributo primero.' },
  ui_gal_trib: { en: 'Galaxy — {n} Tribute to spend on Legacy', es: 'Galaxia: {n} de Tributo para gastar en Legado' },
  ui_galaxy: { en: 'Galaxy', es: 'Galaxia' },
  ui_new_upgs: { en: 'New upgrades available at any station.', es: 'Nuevas mejoras disponibles en cualquier estación.' },
  ui_tease: { en: '📡 Your dishes also pick up a <b>faint signal from beyond {loc}</b>. Rule the system (100 influence) to trace it.', es: '📡 Tus antenas también captan una <b>señal débil desde más allá de {loc}</b>. Gobierna el sistema (100 de influencia) para rastrearla.' },
  ui_new_tag: { en: 'NEW!', es: '¡NUEVO!' },
  ui_awesome: { en: 'Awesome!', es: '¡Genial!' },
  ui_you_rule: { en: 'You rule {sys}!', es: '¡Gobiernas {sys}!' },
  ui_solar_system: { en: 'the Solar System', es: 'el Sistema Solar' },
  ui_victory_body: { en: 'In <b>{d} days</b> you went from chipping rocks on {loc} to the most powerful force in the system.<br><br>\n    Ore mined: <b>{mined}</b><br>Total earnings: <b>{earned} cr</b><br>Battles won: <b>{won}</b><br>Contracts: <b>{c}</b>',
    es: 'En <b>{d} días</b> pasaste de picar rocas en {loc} a ser la fuerza más poderosa del sistema.<br><br>\n    Mineral extraído: <b>{mined}</b><br>Ganancias totales: <b>{earned} cr</b><br>Batallas ganadas: <b>{won}</b><br>Contratos: <b>{c}</b>' },
  ui_keep_playing: { en: 'Keep playing', es: 'Seguir jugando' },
  ui_signal_news: { en: '<b>{t}</b> — {loc} appears on your map.', es: '<b>{t}</b>: {loc} aparece en tu mapa.' },
  ui_signal_body: { en: 'A new location is on your map: <b>{loc}</b>. Mining there will draw out its <b>guardian — a boss fight</b>. Bring your best <b>guns and shields</b>; defeating it opens the way to the stars.',
    es: 'Hay un nuevo lugar en tu mapa: <b>{loc}</b>. Minar allí hará salir a su <b>guardián (un combate contra un jefe)</b>. Lleva tus mejores <b>cañones y escudos</b>; derrotarlo abre el camino a las estrellas.' },
  ui_set_course: { en: 'Set course', es: 'Fijar rumbo' },
  // map panel
  ui_unknown_signal: { en: 'Unknown signal', es: 'Señal desconocida' },
  ui_beyond: { en: 'Beyond {loc}', es: 'Más allá de {loc}' },
  ui_signal_locked: { en: '📡 Something out here is broadcasting — and it is not human.<br><small>Rule the system (<b>100 influence</b>, you have {n}) to trace it.</small>',
    es: '📡 Algo aquí afuera está transmitiendo, y no es humano.<br><small>Gobierna el sistema (<b>100 de influencia</b>, tienes {n}) para rastrearlo.</small>' },
  ui_signal_desc: { en: 'Whatever waits there will not be friendly. It guards the way out of {sys}.', es: 'Lo que sea que espere allí no será amistoso. Custodia la salida de {sys}.' },
  ui_unlocks_at: { en: '🔒 Unlocks at <b>{n} cr</b> lifetime earnings', es: '🔒 Se desbloquea con <b>{n} cr</b> de ganancias totales' },
  ui_chip_mining: { en: '⛏ Mining', es: '⛏ Minería' },
  ui_safe: { en: 'Safe', es: 'Seguro' },
  ui_some_pirates: { en: 'Some pirates', es: 'Algunos piratas' },
  ui_dangerous: { en: '☠ Dangerous', es: '☠ Peligroso' },
  ui_ally_line: { en: ' Your ally: ore sells <b>+{n}%</b> here', es: ' Tu aliado: el mineral se vende <b>+{n}%</b> aquí' },
  ui_value_per_unit: { en: 'Value per unit — most valuable first. Cities pay 2–3.5× that, depots ~0.6×.', es: 'Valor por unidad, del más valioso al menos. Las ciudades pagan 2–3.5× eso; los depósitos, ~0.6×.' },
  ui_heat_warn: { en: '🔥 Extreme heat — damages your hull unless you have shields.', es: '🔥 Calor extremo: daña tu casco si no tienes escudos.' },
  ui_ore_sells: { en: 'Your ore sells for <b class="cr">{v} cr</b> here', es: 'Tu mineral se vende por <b class="cr">{v} cr</b> aquí' },
  ui_ore_at: { en: ' <small>({v} at {loc})</small>', es: ' <small>({v} en {loc})</small>' },
  ui_pays_well: { en: 'Pays well for', es: 'Paga bien por' },
  ui_your_power: { en: '⚡ Your power', es: '⚡ Tu poder' },
  ui_dock_at: { en: '🛰 Dock at {st}', es: '🛰 Atracar en {st}' },
  ui_mine_guardian: { en: '☠ Mine & face the guardian', es: '☠ Minar y enfrentar al guardián' },
  ui_mine_field: { en: '⛏ Mine {f}', es: '⛏ Minar {f}' },
  ui_enter_gate: { en: '🌀 Enter the gate', es: '🌀 Entrar al portal' },
  ui_out_of_fuel: { en: 'You ran out of fuel.', es: 'Te quedaste sin combustible.' },
  ui_call_tug: { en: '🚨 Call a tug', es: '🚨 Llamar a un remolcador' },
  ui_fuel: { en: 'Fuel', es: 'Combustible' },
  ui_time: { en: 'Time', es: 'Tiempo' },
  ui_days1: { en: '{n} day', es: '{n} día' },
  ui_daysN: { en: '{n} days', es: '{n} días' },
  ui_fuel_price: { en: 'Fuel price', es: 'Precio comb.' },
  ui_ambush_risk: { en: 'Ambush risk', es: 'Emboscada' },
  ui_fly_here: { en: '🚀 Fly here', es: '🚀 Volar aquí' },
  ui_no_fuel: { en: '⛽ Not enough fuel — upgrade your tank or wait for a closer orbit', es: '⛽ No te alcanza el combustible: mejora tu tanque o espera una órbita más cercana' },
  ui_face_boss: { en: 'Face the {b}?', es: '¿Pelear contra {b}?' },
  ui_boss_body: { en: 'It arrives about <b>20 seconds</b> after you start mining. Destroy it to open the gate — or fly back <b>down</b> to the station to escape.',
    es: 'Llega unos <b>20 segundos</b> después de que empiezas a minar. Destrúyelo para abrir el portal, o vuelve <b>abajo</b> a la estación para escapar.' },
  ui_lets_fight: { en: 'Let\'s fight', es: '¡A pelear!' },
  ui_not_yet: { en: 'Not yet', es: 'Todavía no' },
  ui_g_ready: { en: 'Ready', es: 'Listo' },
  ui_g_ready_t: { en: 'Your ship can take it.', es: 'Tu nave puede con él.' },
  ui_g_tough: { en: 'Tough', es: 'Difícil' },
  ui_g_tough_t: { en: 'Doable — keep moving and dodge its shots.', es: 'Se puede: no dejes de moverte y esquiva sus disparos.' },
  ui_g_vhard: { en: 'Very hard', es: 'Muy difícil' },
  ui_g_vhard_t: { en: 'Upgrade Guns and Shields (or a bigger hull) first.', es: 'Primero mejora Cañones y Escudos (o consigue una nave más grande).' },
  ui_g_deadly: { en: 'Deadly', es: 'Mortal' },
  ui_g_deadly_t: { en: 'You would be shot down. Upgrade Guns, Shields and Ship Class first.', es: 'Te derribarían. Primero mejora Cañones, Escudos y Clase de nave.' },
  ui_guardian: { en: '☠ Guardian: {b}', es: '☠ Guardián: {b}' },
  ui_chances: { en: 'Your chances: <em>{l}</em> — {t}', es: 'Tus posibilidades: <em>{l}</em> — {t}' },
  // mining HUD
  ui_pirate_ambush: { en: '☠ Pirate ambush', es: '☠ Emboscada pirata' },
  ui_each: { en: '{n} ea', es: '{n} c/u' },
  ui_hold_empty: { en: 'Cargo hold empty', es: 'Bodega vacía' },
  ui_worth: { en: 'Worth', es: 'Valor' },
  ui_depth: { en: 'Depth {d}% · richness ×{r}', es: 'Prof. {d}% · riqueza ×{r}' },
  ui_t_drill: { en: '⛏ Drill', es: '⛏ Taladro' },
  ui_t_laser: { en: '✦ Laser', es: '✦ Láser' },
  ui_t_pulse_cd: { en: 'Pulse {n}s', es: 'Pulso {n}s' },
  ui_t_pulse_ok: { en: '🧲 Pulse ready', es: '🧲 Pulso listo' },
  ui_t_od_on: { en: '⚡ OVERDRIVE {n}s', es: '⚡ SOBREMARCHA {n}s' },
  ui_t_od_cd: { en: 'Overdrive {n}s', es: 'Sobremarcha {n}s' },
  ui_t_od_ok: { en: '⚡ Overdrive ready', es: '⚡ Sobremarcha lista' },
  ui_t_bomb_cd: { en: 'Charge {n}s', es: 'Carga {n}s' },
  ui_t_bomb_ok: { en: '💥 Charge ready', es: '💥 Carga lista' },
  ui_t_scan_cd: { en: 'Scan {n}s', es: 'Escaneo {n}s' },
  ui_t_scan_ok: { en: '◈ Deep Scan ready', es: '◈ Escáner listo' },
  ui_t_wide: { en: '✦ Wide Beam', es: '✦ Rayo ancho' },
  ui_t_phase_on: { en: 'PHASED {n}s', es: 'EN FASE {n}s' },
  ui_t_phase_cd: { en: 'Phase {n}s', es: 'Fase {n}s' },
  ui_t_phase_ok: { en: '◎ Phase ready', es: '◎ Fase lista' },
  ui_beam_in: { en: '⚡ Beam in {n}s', es: '⚡ Rayo en {n}s' },
  ui_molten: { en: '☀ MOLTEN {n}s', es: '☀ FUNDIDO {n}s' },
  ui_pulse_in: { en: '☀ Pulse in {n}s', es: '☀ Pulso en {n}s' },
  ui_b_boost: { en: 'BOOST', es: 'TURBO' },
  ui_b_bomb: { en: 'BOMB', es: 'BOMBA' },
  ui_b_scan: { en: 'SCAN', es: 'ESCANEAR' },
  ui_b_pull: { en: 'PULL', es: 'ATRAER' },
  ui_b_phase: { en: 'PHASE', es: 'FASE' },
  ui_b_laser: { en: 'LASER', es: 'LÁSER' },
  ui_b_drill: { en: 'DRILL', es: 'TALADRO' },
  ui_b_fire: { en: 'FIRE', es: 'DISPARAR' },
  ui_shield_hud: { en: 'Shield {a}/{b}', es: 'Escudo {a}/{b}' },
  ui_heat: { en: '🔥 HEAT', es: '🔥 CALOR' },
  ui_bt_hostile: { en: 'HOSTILE', es: 'HOSTIL' },
  ui_bt_hostiles: { en: 'HOSTILES', es: 'HOSTILES' },
  ui_bt_pirate: { en: 'PIRATE', es: 'PIRATA' },
  ui_bt_pirates: { en: 'PIRATES', es: 'PIRATAS' },
  ui_area_clear: { en: '✔ AREA CLEAR — resuming course', es: '✔ ZONA DESPEJADA: retomando rumbo' },
  ui_warping: { en: 'Warping… {n}%', es: 'Escapando… {n}%' },
  ui_warp_out: { en: '⚡ Warp out ({n}s)', es: '⚡ Escapar ({n}s)' },
  // dock
  ui_tab_upg: { en: '🔧 Upgrades', es: '🔧 Mejoras' },
  ui_tab_outpost: { en: '🤖 Outpost', es: '🤖 Puesto' },
  ui_tab_trade: { en: '📦 Trade', es: '📦 Comercio' },
  ui_tab_contracts: { en: '📜 Contracts', es: '📜 Contratos' },
  ui_tab_planet: { en: '🏛 Planet', es: '🏛 Planeta' },
  ui_sold: { en: 'SOLD', es: 'VENDIDO' },
  ui_strike_nosale: { en: 'Market closed by a strike — ore not sold.', es: 'Mercado cerrado por huelga: no se vendió el mineral.' },
  ui_refueled: { en: '⛽ Refueled +{n} (−{c} cr)', es: '⛽ Recargado +{n} (−{c} cr)' },
  ui_repaired_free: { en: '🔧 Repaired +{n} (free for new pilots)', es: '🔧 Reparado +{n} (gratis para pilotos nuevos)' },
  ui_repaired: { en: '🔧 Repaired +{n} (−{c} cr)', es: '🔧 Reparado +{n} (−{c} cr)' },
  ui_cargo_cap: { en: 'CARGO', es: 'CARGA' },
  ui_black_mkt: { en: '☠ Black market: selling a full hold here costs about −{n} reputation with every faction.', es: '☠ Mercado negro: vender una bodega llena aquí cuesta unos −{n} de reputación con cada facción.' },
  ui_strike: { en: 'Market closed by a strike.', es: 'Mercado cerrado por huelga.' },
  ui_sell_all: { en: 'Sell all here · <b>{v} cr</b>', es: 'Vender todo aquí · <b>{v} cr</b>' },
  ui_nothing_sells: { en: 'Nothing in your hold sells well here.', es: 'Nada de tu bodega se vende bien aquí.' },
  ui_pays: { en: 'pays', es: 'paga' },
  ui_best_price: { en: 'This is the best price you can get right now.', es: 'Es el mejor precio que puedes conseguir ahora.' },
  ui_launch: { en: '⛏ Launch — {f}', es: '⛏ Despegar — {f}' },
  ui_star_map: { en: '🗺 Star Map', es: '🗺 Mapa estelar' },
  ui_full_again: { en: ' · full again in ~{n} days', es: ' · se recupera en ~{n} días' },
  ui_no_cr_space: { en: 'Not enough credits or space', es: 'No te alcanzan los créditos o el espacio' },
  ui_bought_run: { en: 'Bought {n} {g} — course plotted to {loc}', es: 'Compraste {n} {g}: rumbo fijado a {loc}' },
  ui_freighter_btn: { en: '🚚 Freighter · {c} <small>(+{i}/s)</small>', es: '🚚 Carguero · {c} <small>(+{i}/s)</small>' },
  ui_fleet: { en: '🚚 Fleet <b>{n}/{max}</b> · max {p} per route · next costs <b>{c} cr</b>', es: '🚚 Flota <b>{n}/{max}</b> · máx. {p} por ruta · el siguiente cuesta <b>{c} cr</b>' },
  ui_fleet_full: { en: ' · <b>full</b> — +{s} slots unlock with <b>{u}</b>', es: ' · <b>llena</b>: +{s} espacios se desbloquean con <b>{u}</b>' },
  ui_fleet_max: { en: ' · <b>maximum fleet reached</b>', es: ' · <b>flota máxima alcanzada</b>' },
  ui_fleet_next: { en: ' <small>(+{s} slots with {u})</small>', es: ' <small>(+{s} espacios con {u})</small>' },
  ui_no_freighter: { en: 'Cannot hire a freighter here', es: 'No puedes contratar un carguero aquí' },
  ui_freighter_runs: { en: '🚚 Freighter now runs {g} to {loc}', es: '🚚 Ahora un carguero lleva {g} a {loc}' },
  ui_war_push: { en: '⚔ Selling here pushes the front <b>+{n}%</b> for {f}', es: '⚔ Vender aquí empuja el frente <b>+{n}%</b> a favor de {f}' },
  ui_newb: { en: 'NEW', es: 'NUEVO' },
  ui_lv: { en: 'Lv', es: 'Nv' },
  ui_maxed: { en: 'MAXED', es: 'MÁXIMO' },
  ui_buy: { en: 'Buy', es: 'Comprar' },
  ui_need: { en: 'Need', es: 'Cuesta' },
  ui_more_upg1: { en: '🔒 {n} more upgrade unlocks as you progress.', es: '🔒 {n} mejora más se desbloquea a medida que avanzas.' },
  ui_more_upgN: { en: '🔒 {n} more upgrades unlock as you progress.', es: '🔒 {n} mejoras más se desbloquean a medida que avanzas.' },
  ui_strike_long: { en: '✊ Market closed by a strike. Come back in a few days.', es: '✊ Mercado cerrado por huelga. Vuelve en unos días.' },
  ui_best_trades: { en: '💡 Best trades from here', es: '💡 Mejores negocios desde aquí' },
  ui_buy_lc: { en: 'buy', es: 'compra' },
  ui_profit_for: { en: '≈ +{p} for {u}', es: '≈ +{p} por {u}' },
  ui_buy_fly: { en: 'Buy {n} & fly there', es: 'Comprar {n} y volar' },
  ui_no_routes: { en: 'Nothing here is worth hauling right now — the markets that want these goods are saturated. Try another station, or wait for demand to return.',
    es: 'Ahora mismo no vale la pena transportar nada de aquí: los mercados que quieren estos bienes están saturados. Prueba otra estación o espera a que vuelva la demanda.' },
  ui_trade_hint: { en: 'Buy where it\'s cheap (▼), sell where it\'s wanted (▲) — or hire a 🚚 freighter to run the route for you forever. Each market only wants so much: deliveries use up its <b>demand</b>, which returns slowly (~3%/day). Shortages and wars create fresh demand.',
    es: 'Compra donde está barato (▼) y vende donde lo quieren (▲), o contrata un 🚚 carguero para que haga la ruta por ti para siempre. Cada mercado solo quiere cierta cantidad: las entregas gastan su <b>demanda</b>, que vuelve lentamente (~3%/día). La escasez y las guerras crean nueva demanda.' },
  ui_m_good: { en: 'Good', es: 'Producto' },
  ui_m_sell: { en: 'Sell', es: 'Venta' },
  ui_m_have: { en: 'Have', es: 'Tienes' },
  ui_m_buy: { en: 'Buy', es: 'Compra' },
  ui_left: { en: '{n} left', es: 'quedan {n}' },
  ui_all: { en: 'All', es: 'Todo' },
  ui_max: { en: 'Max', es: 'Máx' },
  ui_active_contracts: { en: 'Your active contracts', es: 'Tus contratos activos' },
  ui_none_yet: { en: 'None yet. Accept one below.', es: 'Ninguno todavía. Acepta uno abajo.' },
  ui_urgent: { en: 'URGENT', es: 'URGENTE' },
  ui_reward_left1: { en: 'Reward {r} cr · {d} day left', es: 'Recompensa {r} cr · queda {d} día' },
  ui_reward_leftN: { en: 'Reward {r} cr · {d} days left', es: 'Recompensa {r} cr · quedan {d} días' },
  ui_you_have: { en: ' · you have {a}/{b}', es: ' · tienes {a}/{b}' },
  ui_deliver: { en: 'Deliver', es: 'Entregar' },
  ui_offered_at: { en: 'Offered at {st}', es: 'Ofrecidos en {st}' },
  ui_no_contracts: { en: 'No new contracts. Check back in a few days.', es: 'No hay contratos nuevos. Vuelve en unos días.' },
  ui_reward_offer: { en: 'Reward <b class="cr">{r} cr</b> · +{rep} rep · {d} days', es: 'Recompensa <b class="cr">{r} cr</b> · +{rep} rep · {d} días' },
  ui_accept: { en: 'Accept', es: 'Aceptar' },
  ui_power_on: { en: '⚡ Your power on {loc}', es: '⚡ Tu poder en {loc}' },
  ui_politics_locked: { en: '🔒 Investments and politics (wars, peace deals) unlock with {u}.', es: '🔒 Las inversiones y la política (guerras, tratados de paz) se desbloquean con {u}.' },
  ui_level1: { en: 'level', es: 'nivel' },
  ui_levelN: { en: 'levels', es: 'niveles' },
  ui_invest_intro: { en: 'Invest in <b>{st}</b>. Each level adds <b>+10% of your base income</b> from ore, drones and freighters (all stations stack: {n} {lvls} so far = <b>+{p}%</b>) and permanent <b>influence</b>.',
    es: 'Invierte en <b>{st}</b>. Cada nivel suma <b>+10% de tus ingresos base</b> de mineral, drones y cargueros (todas las estaciones se acumulan: {n} {lvls} hasta ahora = <b>+{p}%</b>) e <b>influencia</b> permanente.' },
  ui_invest_next: { en: 'Next level: passive income <b>{a}/s → {b}/s</b> · ore prices <b>+{p}%</b>', es: 'Siguiente nivel: ingresos pasivos <b>{a}/s → {b}/s</b> · precio del mineral <b>+{p}%</b>' },
  ui_base_income10: { en: '+10% base income', es: '+10% ingresos base' },
  ui_plus_infl: { en: '+{n} influence', es: '+{n} influencia' },
  ui_needs_rep: { en: 'Needs rep {n}', es: 'Requiere rep. {n}' },
  ui_owned: { en: '✔ OWNED', es: '✔ TUYO' },
  ui_invest_btn: { en: 'Invest · {c} cr', es: 'Invertir · {c} cr' },
  ui_invest_needrep: { en: 'Needs {n} reputation with {f} (you have {r})', es: 'Requiere {n} de reputación con {f} (tienes {r})' },
  ui_you_control: { en: 'You control this station\'s consortium. 👑', es: 'Controlas el consorcio de esta estación. 👑' },
  ui_income_mult: { en: 'Income multiplier: <b>×{m}</b>. Raise reputation with contracts, crisis relief and fighting pirates.', es: 'Multiplicador de ingresos: <b>×{m}</b>. Sube tu reputación con contratos, ayuda en crisis y combatiendo piratas.' },
  // upgrade deltas
  ui_d_hull: { en: 'New ship: <b>{n}</b><br>Base cargo {c} · Armor {a}', es: 'Nueva nave: <b>{n}</b><br>Carga base {c} · Blindaje {a}' },
  ui_d_laser: { en: 'Mining power {v}', es: 'Poder minero {v}' },
  ui_d_range: { en: 'Range {v}', es: 'Alcance {v}' },
  ui_d_drone1: { en: ' · <b>+1 drone</b>', es: ' · <b>+1 dron</b>' },
  ui_d_drones: { en: ' · drones {n}', es: ' · drones {n}' },
  ui_d_cargo: { en: 'Cargo {v}', es: 'Carga {v}' },
  ui_d_extr: { en: 'Ore per rock {v}', es: 'Mineral por roca {v}' },
  ui_d_ref: { en: 'All ore value {v}', es: 'Valor de todo el mineral {v}' },
  ui_d_engine: { en: 'Speed {v} · Warp {w}s', es: 'Velocidad {v} · Escape {w}s' },
  ui_d_tank: { en: 'Fuel {v}', es: 'Combustible {v}' },
  ui_d_shield: { en: 'Shield {v}', es: 'Escudo {v}' },
  ui_d_weapons: { en: 'Firepower {v}', es: 'Potencia de fuego {v}' },
  ui_d_scanner: { en: 'Ambush avoidance {v}', es: 'Evasión de emboscadas {v}' },
  ui_cargo_full: { en: 'Cargo hold full', es: 'Bodega llena' },
  ui_no_credits: { en: 'Not enough credits', es: 'No te alcanzan los créditos' },
  ui_new_ship: { en: 'New ship: {n}', es: 'Nueva nave: {n}' },
  ui_new_ship_t: { en: 'New ship: {n}!', es: '¡Nueva nave: {n}!' },
  ui_new_ship_stats: { en: 'Cargo <b>{c}</b> · Armor <b>{a}</b>', es: 'Carga <b>{c}</b> · Blindaje <b>{a}</b>' },
  ui_nice: { en: 'Nice!', es: '¡Buenísimo!' },
  // outpost
  ui_op_build_t: { en: 'Build a Drone Outpost', es: 'Construye un puesto minero' },
  ui_op_build_d: { en: 'Drones slowly mine <b>{f}</b> for you — even when you\'re somewhere else or offline.', es: 'Los drones minan <b>{f}</b> poco a poco por ti, incluso cuando estás en otro lado o desconectado.' },
  ui_op_build_r: { en: 'Each drone earns <b class="cr">{n} cr/s</b> here. Starts with room for {s} drones.', es: 'Cada dron gana <b class="cr">{n} cr/s</b> aquí. Empieza con espacio para {s} drones.' },
  ui_op_build_btn: { en: 'Build outpost · {c} cr', es: 'Construir puesto · {c} cr' },
  ui_op_level: { en: 'OUTPOST · LEVEL {n}', es: 'PUESTO · NIVEL {n}' },
  ui_op_drones: { en: '{n} drones × {p} cr/s', es: '{n} drones × {p} cr/s' },
  ui_drones: { en: 'Drones', es: 'Drones' },
  ui_op_slots: { en: '{n} / {c} slots', es: '{n} / {c} espacios' },
  ui_op_full: { en: 'All slots full — upgrade the outpost for <b>+{s} slots</b> and <b>×2 output</b>.', es: 'Todos los espacios llenos: mejora el puesto para <b>+{s} espacios</b> y <b>×2 producción</b>.' },
  ui_op_plus1: { en: '+1 drone · {c}', es: '+1 dron · {c}' },
  ui_op_max: { en: 'MAX', es: 'MÁX' },
  ui_op_lv_sub: { en: 'Outpost level', es: 'Nivel del puesto' },
  ui_op_lv_btn: { en: 'Level {n}: <b>×2 output</b> & +{s} slots · {c} cr', es: 'Nivel {n}: <b>×2 producción</b> y +{s} espacios · {c} cr' },
  ui_op_maxlv: { en: 'Max level reached 👑', es: 'Nivel máximo alcanzado 👑' },
  ui_op_hint: { en: 'Drones are slow but never stop — they keep earning while you\'re offline. Each costs 18% more than the last. Refinery upgrades, investments and megaprojects multiply their income.',
    es: 'Los drones son lentos pero nunca paran: siguen ganando mientras estás desconectado. Cada uno cuesta 18% más que el anterior. Las mejoras de Refinería, las inversiones y los megaproyectos multiplican sus ingresos.' },
  ui_op_online: { en: 'Outpost online! Your drones are mining.', es: '¡Puesto en línea! Tus drones están minando.' },
  ui_plus_drone1: { en: '+{n} drone', es: '+{n} dron' },
  ui_plus_droneN: { en: '+{n} drones', es: '+{n} drones' },
  ui_op_upgraded: { en: 'Outpost upgraded: ×2 output!', es: '¡Puesto mejorado: ×2 producción!' },
  ui_inv0: { en: 'Warehouse', es: 'Almacén' },
  ui_inv1: { en: 'Refinery', es: 'Refinería' },
  ui_inv2: { en: 'Consortium', es: 'Consorcio' },
  ui_inva0: { en: 'Warehouse', es: 'un Almacén' },
  ui_inva1: { en: 'Refinery', es: 'una Refinería' },
  ui_inva2: { en: 'Consortium', es: 'un Consorcio' },
  ui_invest_news: { en: 'You bought a {inv} on {st}. Your influence grows.', es: 'Compraste {inv} en {st}. Tu influencia crece.' },
  ui_invest_done: { en: 'Investment complete: +10% all income, +{n} influence', es: 'Inversión completa: +10% a todos los ingresos, +{n} de influencia' },
  // ship / empire / projects
  ui_dump: { en: 'Dump', es: 'Tirar' },
  ui_ship_class: { en: '{n} class', es: 'clase {n}' },
  ui_systems: { en: 'Systems', es: 'Sistemas' },
  ui_hold: { en: 'Cargo hold {a}/{b}', es: 'Bodega {a}/{b}' },
  ui_empty: { en: 'Empty', es: 'Vacía' },
  ui_stats: { en: 'Stats', es: 'Estadísticas' },
  ui_ore_mined: { en: 'Ore mined', es: 'Mineral extraído' },
  ui_lifetime: { en: 'Lifetime earnings', es: 'Ganancias totales' },
  ui_record: { en: 'Record credits (leaderboard)', es: 'Récord de créditos (clasificación)' },
  ui_ore_values: { en: 'Ore values', es: 'Valor del mineral' },
  ui_per_unit: { en: '· per unit', es: '· por unidad' },
  ui_battles: { en: 'Battles won / lost', es: 'Batallas ganadas / perdidas' },
  ui_contracts: { en: 'Contracts', es: 'Contratos' },
  ui_passive: { en: 'PASSIVE INCOME', es: 'INGRESOS PASIVOS' },
  ui_income_split: { en: 'Drones {d}/s · Freighters {f}/s · ore multiplier ×{m}', es: 'Drones {d}/s · Cargueros {f}/s · multiplicador de mineral ×{m}' },
  ui_freighters: { en: 'Freighters {a}/{b}', es: 'Cargueros {a}/{b}' },
  ui_outposts: { en: 'Outposts', es: 'Puestos mineros' },
  ui_locked: { en: 'locked', es: 'bloqueado' },
  ui_op_row: { en: 'Lv {lv} · {n} drones', es: 'Nv {lv} · {n} drones' },
  ui_build_for: { en: 'Build for {c}', es: 'Construir: {c}' },
  ui_influence: { en: 'INFLUENCE', es: 'INFLUENCIA' },
  ui_infl_from: { en: 'Influence comes from investments, outpost levels, megaprojects, reputation, pirate kills{peace}{fear}.', es: 'La influencia viene de inversiones, niveles de puestos, megaproyectos, reputación, piratas derribados{peace}{fear}.' },
  ui_peace1: { en: ', {n} peace deal', es: ', {n} tratado de paz' },
  ui_peaceN: { en: ', {n} peace deals', es: ', {n} tratados de paz' },
  ui_fear1: { en: ', and fear ({n} planet destroyed)', es: ' y el miedo ({n} planeta destruido)' },
  ui_fearN: { en: ', and fear ({n} planets destroyed)', es: ' y el miedo ({n} planetas destruidos)' },
  ui_wars: { en: 'Wars', es: 'Guerras' },
  ui_allies: { en: 'Allies (won wars)', es: 'Aliados (guerras ganadas)' },
  ui_ore_plus: { en: 'ore +{n}%', es: 'mineral +{n}%' },
  ui_fac_rep: { en: 'Faction reputation', es: 'Reputación con facciones' },
  ui_active_events: { en: 'Active events', es: 'Eventos activos' },
  ui_end_it: { en: '🕊️ End it · {c}', es: '🕊️ Terminarlo · {c}' },
  ui_calm: { en: 'The system is calm… for now.', es: 'El sistema está en calma… por ahora.' },
  ui_empire_t: { en: '🤖 Your Empire', es: '🤖 Tu Imperio' },
  ui_proj_hint: { en: 'Spend your fortune on projects that change the system forever. Each one also adds influence.', es: 'Invierte tu fortuna en proyectos que cambian el sistema para siempre. Cada uno también suma influencia.' },
  ui_requires: { en: 'Requires the {p}', es: 'Requiere: {p}' },
  ui_unlocks_with: { en: 'Unlocks with: {u}', es: 'Se desbloquea con: {u}' },
  ui_proj_infl: { en: ' · +{n} influence', es: ' · +{n} influencia' },
  ui_trib_jump: { en: '+{n} Tribute when you jump', es: '+{n} de Tributo al saltar' },
  ui_built: { en: '✔ BUILT', es: '✔ CONSTRUIDO' },
  ui_build: { en: 'Build', es: 'Construir' },
  ui_sys_powers: { en: 'System powers', es: 'Poderes del sistema' },
  ui_powers_hint: { en: 'Select any planet on the Star Map (or open its 🏛 Planet tab) to fund booms, hire mercenaries, and later start wars, back a side or broker peace. End crises from the Empire panel.',
    es: 'Selecciona cualquier planeta en el Mapa estelar (o abre su pestaña 🏛 Planeta) para financiar auges, contratar mercenarios y, más adelante, iniciar guerras, apoyar a un bando o negociar la paz. Termina las crisis desde el panel Imperio.' },
  ui_megaprojects: { en: '🌌 Megaprojects', es: '🌌 Megaproyectos' },
  ui_proj_done: { en: '{p} complete!', es: '¡{p} completado!' },
  ui_megaproject: { en: 'MEGAPROJECT', es: 'MEGAPROYECTO' },
  ui_trib_leave: { en: ' · +{n} Tribute when you leave this system', es: ' · +{n} de Tributo al dejar este sistema' },
  ui_behold: { en: 'Behold!', es: '¡Impresionante!' },
  ui_destroy_q: { en: 'Destroy {l}?', es: '¿Destruir {l}?' },
  ui_destroy_body: { en: 'This cannot be undone. {who} and everyone\'s business there will be wiped out, and every faction will fear — and hate — you.<br><br>What remains will be <b>the richest debris field in the system</b>.',
    es: 'Esto no se puede deshacer. {who} y todos los negocios de allí serán borrados, y todas las facciones te temerán… y te odiarán.<br><br>Lo que quede será <b>el campo de escombros más rico del sistema</b>.' },
  ui_fire_cost: { en: '🔥 FIRE · {c} cr', es: '🔥 DISPARAR · {c} cr' },
  ui_stand_down: { en: 'Stand down', es: 'Retirarse' },
  ui_not_avail: { en: 'Not available right now', es: 'No disponible ahora' },
  ui_power_done: { en: 'Done. The system bends to your will.', es: 'Hecho. El sistema se doblega a tu voluntad.' },
  ui_you_chose: { en: 'You chose: {c}', es: 'Elegiste: {c}' },
  ui_news_t: { en: '📰 System News', es: '📰 Noticias del sistema' },
  // menu
  ui_menu_t: { en: '☰ Menu', es: '☰ Menú' },
  ui_resume: { en: 'Resume', es: 'Continuar' },
  ui_how_to_play: { en: 'How to play', es: 'Cómo jugar' },
  ui_first_sale: { en: '🎉 First sale! Now buy an <b>upgrade</b> below — it makes your next trip faster', es: '🎉 ¡Primera venta! Ahora compra una <b>mejora</b> aquí abajo: tu próximo viaje será más rápido' },
  ui_music_on: { en: '🎵 Music: on', es: '🎵 Música: sí' },
  ui_gfx_auto: { en: '✺ Graphics: auto', es: '✺ Gráficos: automático' },
  ui_gfx_high: { en: '✺ Graphics: high', es: '✺ Gráficos: altos' },
  ui_gfx_low: { en: '✺ Graphics: smooth (light)', es: '✺ Gráficos: fluidos (ligeros)' },
  ui_music_off: { en: '🎵 Music: off', es: '🎵 Música: no' },
  ui_new_game: { en: 'New game', es: 'Nueva partida' },
  ui_new_game_q: { en: 'Start a new game?', es: '¿Empezar una nueva partida?' },
  ui_progress_lost: { en: 'Your current progress will be lost.', es: 'Perderás tu progreso actual.' },
  ui_yes_restart: { en: 'Yes, start over', es: 'Sí, empezar de nuevo' },
  ui_cancel: { en: 'Cancel', es: 'Cancelar' },
  // help
  ui_help_t: { en: '📖 How to play', es: '📖 Cómo jugar' },
  ui_h_mine: { en: '⛏ Mine', es: '⛏ Minar' },
  ui_h_mine_p: { en: 'Fly with <b>WASD</b> or arrows, <b>hold the mouse</b> to fire your laser (or Space). Big rocks break into smaller ones and drop glowing ore. Glowing veins give double ore. Watch for <b>comets</b> streaking across the field: break one before it escapes for a load of the field\'s best ore.',
    es: 'Vuela con <b>WASD</b> o las flechas y <b>mantén presionado el mouse</b> (o Espacio) para disparar el láser. Las rocas grandes se rompen en otras más pequeñas y sueltan mineral brillante. Las vetas brillantes dan el doble de mineral. Atento a los <b>cometas</b> que cruzan el campo: rompe uno antes de que escape y obtendrás un montón del mejor mineral del campo.' },
  ui_h_mine_pt: { en: 'Steer with the <b>joystick</b> (drag on the left side of the screen) and <b>hold LASER</b> to fire. Big rocks break into smaller ones and drop glowing ore. Glowing veins give double ore. Watch for <b>comets</b> streaking across the field: break one before it escapes for a load of the field\'s best ore.',
    es: 'Muévete con el <b>joystick</b> (arrastra en el lado izquierdo de la pantalla) y <b>mantén LÁSER</b> para disparar. Las rocas grandes se rompen en otras más pequeñas y sueltan mineral brillante. Las vetas brillantes dan el doble de mineral. Atento a los <b>cometas</b> que cruzan el campo: rompe uno antes de que escape y obtendrás un montón del mejor mineral del campo.' },
  ui_h_dock: { en: '🛰 Dock', es: '🛰 Muelle' },
  ui_h_dock_p: { en: 'The station is at the <b>bottom</b> of every field. Fly back down into the docking zone to sell your ore, refuel and repair. Rocks get richer the <b>higher</b> you fly.',
    es: 'La estación está en la parte de <b>abajo</b> de cada campo. Vuelve a bajar a la zona de atraque para vender tu mineral, recargar combustible y reparar. Las rocas son más ricas cuanto más <b>arriba</b> vuelas.' },
  ui_h_drones: { en: '🤖 Drones', es: '🤖 Drones' },
  ui_h_drones_p: { en: 'Build an outpost in each field and buy drones. They earn credits every second — even while you\'re offline.', es: 'Construye un puesto minero en cada campo y compra drones. Ganan créditos cada segundo, incluso mientras estás desconectado.' },
  ui_h_pirates: { en: '⚔ Pirates', es: '⚔ Piratas' },
  ui_h_pirates_p: { en: 'In dangerous zones pirates attack. <b>Hold the mouse</b> to fire your guns. Destroyed ships drop credits.', es: 'En las zonas peligrosas te atacan piratas. <b>Mantén presionado el mouse</b> para disparar tus cañones. Las naves destruidas sueltan créditos.' },
  ui_h_pirates_pt: { en: 'In dangerous zones pirates attack. <b>Hold FIRE</b> to shoot your guns. Destroyed ships drop credits.', es: 'En las zonas peligrosas te atacan piratas. <b>Mantén DISPARAR</b> para usar tus cañones. Las naves destruidas sueltan créditos.' },
  ui_h_unlock: { en: '🔓 Unlock', es: '🔓 Desbloqueos' },
  ui_h_unlock_p: { en: 'The more you earn, the more of the Solar System opens up: the star map, new planets, pirates, trading, events and finally influence.', es: 'Cuanto más ganas, más se abre el Sistema Solar: el mapa estelar, nuevos planetas, piratas, comercio, eventos y, al final, la influencia.' },
  ui_h_travel: { en: '🗺 Travel', es: '🗺 Viajes' },
  ui_h_travel_p: { en: 'Planets orbit the Sun, so distances change every day. Farther places pay more and are more dangerous. Fuel gets pricier as you get richer, and a <b>full hold burns more</b> — pick your sell trips wisely. Prices differ per station.',
    es: 'Los planetas orbitan el Sol, así que las distancias cambian cada día. Los lugares más lejanos pagan más y son más peligrosos. El combustible se encarece a medida que te haces rico, y una <b>bodega llena gasta más</b>: elige bien tus viajes de venta. Los precios varían en cada estación.' },
  ui_h_wars: { en: '⚔ Wars', es: '⚔ Guerras' },
  ui_h_wars_p: { en: 'When two factions fight, <b>back a side</b> at one of their stations. Their stations pay +30% for metals and every ore sale there <b>pushes the front</b> (see the bar). Help them win to gain a <b>permanent ally</b>: +15% ore at their stations (up to 3 stars) and spoils of war.',
    es: 'Cuando dos facciones pelean, <b>apoya a un bando</b> en una de sus estaciones. Sus estaciones pagan +30% por los metales y cada venta de mineral allí <b>empuja el frente</b> (mira la barra). Ayúdalos a ganar para conseguir un <b>aliado permanente</b>: +15% por el mineral en sus estaciones (hasta 3 estrellas) y botín de guerra.' },
  ui_h_trade: { en: '📦 Trade', es: '📦 Comercio' },
  ui_h_trade_p: { en: 'The Trade tab shows the best deals from each station: one tap buys the goods and plots your course. Hire 🚚 freighters to run a route for you forever.', es: 'La pestaña Comercio muestra los mejores negocios desde cada estación: un toque compra los bienes y fija tu rumbo. Contrata 🚚 cargueros para que hagan una ruta por ti para siempre.' },
  ui_h_power: { en: '🏛 Power', es: '🏛 Poder' },
  ui_h_power_p: { en: 'Select a planet on the map (or open its Planet tab) to fund public works, start booms, hire mercenaries — back a side in wars and fund offensives; later incite wars or broker peace. Each action has a cooldown per planet. The Nova Cannon can even destroy a world…',
    es: 'Selecciona un planeta en el mapa (o abre su pestaña Planeta) para financiar obras públicas, impulsar auges y contratar mercenarios; apoya a un bando en las guerras y financia ofensivas; más adelante, provoca guerras o negocia la paz. Cada acción tiene un tiempo de espera por planeta. El Cañón Nova puede incluso destruir un mundo…' },
  ui_h_tools: { en: '⛏ Tools', es: '⛏ Herramientas' },
  ui_h_tools_p: { en: 'Some star systems give you tools you keep forever: the <b>Drill</b> (<b>{drill}</b>: 3× power at short range, cracks <b>armored</b> rocks), the <b>Tractor Pulse</b> (<b>{pull}</b>: pulls every ore chunk around you), <b>Overdrive</b> (<b>{boost}</b>: 8 s of triple power and speed) and <b>Mining Charges</b> (<b>{bomb}</b>: a bomb that cracks every rock around it), the <b>Deep Scanner</b> (<b>{scan}</b>: shows hidden <b>geodes</b> — break one for a huge load of the field\'s best ore) and the <b>Wide Beam</b> (your laser forks into two more rocks). <b>Volatile</b> rocks explode when broken — chain them! <b>Living</b> rocks flee from your laser but drop 60% more ore — calm them with the Tractor Pulse. The <b>Phase Shift</b> (<b>{phase}</b>) makes you a ghost for 3 s: no damage, and you fly through rocks. <b>Magnetic</b> rocks clump together and pull loose ore to you when they break; <b>relic</b> rocks give a 25 s power when broken.',
    es: 'Algunos sistemas estelares te dan herramientas que conservas para siempre: el <b>Taladro</b> (<b>{drill}</b>: 3× de poder a corta distancia, rompe rocas <b>blindadas</b>), el <b>Pulso tractor</b> (<b>{pull}</b>: atrae todos los trozos de mineral a tu alrededor), la <b>Sobremarcha</b> (<b>{boost}</b>: 8 s de triple poder y velocidad), las <b>Cargas mineras</b> (<b>{bomb}</b>: una bomba que rompe todas las rocas a su alrededor), el <b>Escáner profundo</b> (<b>{scan}</b>: muestra <b>geodas</b> ocultas; rompe una para obtener un montón del mejor mineral del campo) y el <b>Rayo ancho</b> (tu láser se bifurca hacia dos rocas más). Las rocas <b>volátiles</b> explotan al romperse: ¡encadénalas! Las rocas <b>vivas</b> huyen de tu láser pero sueltan 60% más mineral; cálmalas con el Pulso tractor. El <b>Cambio de fase</b> (<b>{phase}</b>) te vuelve un fantasma durante 3 s: no recibes daño y atraviesas rocas. Las rocas <b>magnéticas</b> se agrupan y atraen hacia ti el mineral suelto al romperse; las rocas <b>reliquia</b> dan un poder de 25 s al romperse.' },
  ui_h_drill_t: { en: 'DRILL button', es: 'botón TALADRO' },
  ui_h_galaxy: { en: '🌀 Galaxy', es: '🌀 Galaxia' },
  ui_h_galaxy_p: { en: 'Each system\'s guardian opens a jump gate. In the <b>Galaxy</b> map you jump to the next star: you start fresh there, but conquered systems pay <b>Tribute</b> forever, which buys permanent <b>Legacy</b> bonuses. 15 systems lead to the black hole at the core.',
    es: 'El guardián de cada sistema abre un portal de salto. En el mapa de la <b>Galaxia</b> saltas a la siguiente estrella: allí empiezas de cero, pero los sistemas conquistados pagan <b>Tributo</b> para siempre, con el que compras bonificaciones permanentes de <b>Legado</b>. 15 sistemas llevan al agujero negro del núcleo.' },
  ui_h_win: { en: '👑 Win', es: '👑 Victoria' },
  ui_h_win_p: { en: 'Invest in stations to earn influence. Reach <b>100 influence</b> to rule the system — then defeat its guardian and jump through the gate to the next star.', es: 'Invierte en estaciones para ganar influencia. Llega a <b>100 de influencia</b> para gobernar el sistema; luego derrota a su guardián y cruza el portal hacia la siguiente estrella.' },
});
const uiDays = n => tx(n === 1 ? 'ui_days1' : 'ui_daysN', { n });

function toast(msg, cls) {
  if (OFFLINE) return;
  const el = document.createElement('div');
  el.className = 'toast ' + (cls || '');
  el.innerHTML = msg;
  $('toasts').appendChild(el);
  setTimeout(() => el.classList.add('out'), 2600);
  setTimeout(() => el.remove(), 3100);
}
function coach(msg) {
  const el = $('coach');
  if (!msg) { el.classList.remove('show'); return; }
  if (el._m !== msg) { el.innerHTML = msg; el._m = msg; }
  el.classList.add('show');
}

function showModal(o) {
  const m = $('modal');
  m.innerHTML = `<div class="mbox ${o.danger ? 'danger' : ''} ${o.cls || ''}">
    ${o.icon ? `<div class="micon">${o.icon}</div>` : ''}
    <h2>${o.title}</h2><div class="mbody">${o.html || ''}</div>
    <div class="mbtns"></div></div>`;
  const bx = m.querySelector('.mbtns');
  o.buttons.forEach(b => {
    const el = document.createElement('button');
    el.className = 'btn ' + (b.cls || '');
    el.innerHTML = b.label; el.disabled = !!b.disabled;
    el.onclick = () => { sfx('click'); closeModal(); b.fn && b.fn(); updateHUD(); };
    bx.appendChild(el);
  });
  m.classList.remove('hidden');
  if (o.after) o.after(m);
}
function closeModal() { $('modal').classList.add('hidden'); }

function showEventBanner(ev) {
  if (OFFLINE) return;
  const b = $('eventBanner');
  b.innerHTML = `<span class="eicon">${ev.icon}</span><div><small>${tx('ui_sysnews_day', { d: S.day })}</small><b>${ev.title}</b><p>${ev.text}</p></div>`;
  b.classList.add('show');
  sfx('event');
  clearTimeout(b._t); b._t = setTimeout(() => b.classList.remove('show'), 6500);
}
function updateTicker() {
  const el = $('tickerIn'); if (!el || !S) return;
  el.innerHTML = S.news.slice(0, 8).map(n => `<span><i>${tx('ui_day', { d: n.day })}</i> ${n.icon} ${n.html.replace(/<[^>]+>/g, '')}</span>`).join('<span class="sep">◆</span>');
}

// ---------- HUD ----------
function hudTick(dt) {
  if (!S) return;
  const d = S.credits - shownCredits;
  if (Math.abs(d) < 1) shownCredits = S.credits;
  else shownCredits += d * Math.min(1, dt * 6) + Math.sign(d) * Math.min(Math.abs(d), dt * 40);
  $('hCr').textContent = fmt(shownCredits);
  $('hCr').parentElement.classList.toggle('up', d > 1);
  const inc = totalIncome();
  $('hRate').textContent = inc > 0 ? `+${fmt(inc)}/s` : '';
}
function updateWarBar() {
  const el = $('warHud'), w = S && backedWar();
  el.classList.toggle('hidden', !w);
  if (w) el.innerHTML = `<small>${tx('ui_war_front')}</small>${warBarHTML(w)}`;
}
function updateHUD() {
  if (!S) return;
  for (const el of document.querySelectorAll('[data-need]')) el.classList.toggle('locked', S.unlock < +el.dataset.need);
  $('hDay').textContent = S.day;
  $('hDayT').style.width = Math.min(100, (S.dayT || 0) / DAY_SEC * 100) + '%';
  updateWarBar();
  $('hFuel').style.width = (S.fuel / ship.fuelMax * 100) + '%';
  $('hFuelT').textContent = `${Math.floor(S.fuel)}/${ship.fuelMax}`;
  $('hHull').style.width = (S.hull / ship.hpMax * 100) + '%';
  $('hHullT').textContent = `${fmt(Math.ceil(S.hull))}/${fmt(ship.hpMax)}`;
  $('hCargo').style.width = (cargoUsed() / ship.cargoMax * 100) + '%';
  $('hCargoT').textContent = `${fmt(cargoUsed())}/${fmt(ship.cargoMax)}`;
  const inf = influence();
  $('hInfl').textContent = inf;
  $('hRank').textContent = rankName(inf);
  $('hFuel').parentElement.classList.toggle('low', S.fuel < ship.fuelMax * 0.2);
  $('hHull').parentElement.classList.toggle('low', S.hull < ship.hpMax * 0.3);
  $('hCargo').parentElement.classList.toggle('full', cargoFree() <= 0);
  const nu = nextUnlock();
  const o = $('objective');
  if (nu) {
    const prev = UNLOCKS[S.unlock].at, pct = clamp((S.stats.earned - prev) / (nu.at - prev), 0, 1);
    o.innerHTML = `<small>${tx('ui_next_unlock')}</small><b>${nu.icon} ${nu.title}</b><div class="meter gold"><i style="width:${pct * 100}%"></i></div><span>${tx('ui_earned_of', { a: fmt(S.stats.earned), b: fmt(nu.at) })}</span>`;
  } else if (!S.won) {
    o.innerHTML = `<small>${tx('ui_final_goal')}</small><b>${tx('ui_reach100')}</b><div class="meter gold"><i style="width:${Math.min(100, inf)}%"></i></div><span>${tx('ui_infl_line', { n: inf })}${has(U.FRONTIER) ? tx('ui_infl_signal', { loc: LOC.kuiper.n }) : ''}</span>`;
  } else if (!S.gateOpen) o.innerHTML = `<small>${tx('ui_final_guardian')}</small><b>${tx('ui_find_source', { loc: LOC.oort.n })}</b><span>${tx('ui_find_source_d')}</span>`;
  else o.innerHTML = `<small>${tx('ui_gate_open')}</small><b>${tx('ui_galaxy_awaits')}</b><span>${tx('ui_galaxy_awaits_d')}</span>`;
  $('bGal').classList.toggle('hidden', !(S.gateOpen || (S.galaxy && S.galaxy.done.length)));
  { const la = legacyAffordable(); $('bGal').classList.toggle('notify', !!la); $('bGal').dataset.n = la ? Math.floor(S.galaxy.tribute) : ''; $('bGal').title = la ? tx('ui_gal_trib', { n: Math.floor(S.galaxy.tribute) }) : tx('ui_galaxy'); }
  if (!S.won && has(U.SATURN) && inf >= 100 && !isBlocking()) victory();
  if (pendingUnlocks.length && $('modal').classList.contains('hidden') && !(scene === MineScene && (MineScene.inCombat || MineScene.space)) && !(MapScene.travel)) showUnlock(pendingUnlocks.shift());
  else if (pendingChoices.length && $('modal').classList.contains('hidden') && $('sheet').classList.contains('hidden') && scene !== MineScene && !MapScene.travel) showChoice(pendingChoices.shift());
}
function showUnlock(i) {
  const u = UNLOCKS[i];
  sfx('win');
  const upg = u.upg.length ? `<div class="unl-upg">${u.upg.map(k => `<span class="chip ore">${UPG[k].icon} ${UPG[k].n}</span>`).join('')}</div><small>${tx('ui_new_upgs')}</small>` : '';
  const tease = i === UNLOCKS.length - 1 ? `<p class="hint">${tx('ui_tease', { loc: LOC.kuiper.n })}</p>` : '';
  showModal({ icon: u.icon, title: u.title, cls: 'unlock', html: `<div class="unl-tag">${tx('ui_new_tag')}</div><p>${u.text}</p>${upg}${tease}`,
    buttons: [{ label: tx('ui_awesome'), cls: 'primary', fn: () => { if (!$('sheet').classList.contains('hidden') && LOC[S.loc].station) renderDock(); updateHUD(); } }] });
  const el = $('objective'); el.classList.remove('flash'); void el.offsetWidth; el.classList.add('flash');
}
function victory() {
  S.won = true; save();
  sfx('win');
  showModal({ icon: '👑', title: tx('ui_you_rule', { sys: sysId() === 'sol' ? tx('ui_solar_system') : sysName() }), html: tx('ui_victory_body', { d: S.day, loc: LOC.luna.n, mined: fmt(S.stats.mined), earned: fmt(S.stats.earned), won: S.stats.won, c: S.stats.contracts }),
    buttons: [{ label: tx('ui_keep_playing'), cls: 'primary', fn: () => setTimeout(revealSignal, 400) }] });
}
// after you rule the system, something calls from beyond the Kuiper Belt
function revealSignal() {
  if (S.signal) return;
  S.signal = 1; save();
  addNews('📡', tx('ui_signal_news', { t: sysDef().signal.title, loc: LOC.oort.n }), '#7fdfff');
  sfx('event');
  showModal({ icon: '📡', title: sysDef().signal.title, cls: 'unlock', html: `<div class="unl-tag">${tx('ui_new_tag')}</div><p>${sysDef().signal.text}</p><p>${tx('ui_signal_body', { loc: LOC.oort.n })}</p>`,
    buttons: [{ label: tx('ui_set_course'), cls: 'primary', fn: () => {} }] });
}

// ---------- map panel ----------
function selectLoc(id) {
  MapScene.sel = id;
  const l = LOC[id];
  const p = $('locPanel');
  const here = id === S.loc;
  let html = `<div class="lp-head"><div><h3>${l.n}</h3><small>${[l.station, l.field && l.field.n].filter(Boolean).join(' · ')}</small></div><button class="x" onclick="hideLocPanel()">✕</button></div>`;
  if (l.secret && !S.signal) {
    html = `<div class="lp-head"><div><h3>${tx('ui_unknown_signal')}</h3><small>${tx('ui_beyond', { loc: LOC.kuiper.n })}</small></div><button class="x" onclick="hideLocPanel()">✕</button></div>`;
    html += `<div class="locked-box">${tx('ui_signal_locked', { n: influence() })}</div><p class="desc">${tx('ui_signal_desc', { sys: sysId() === 'sol' ? tx('ui_solar_system') : sysName() })}</p>`;
    p.innerHTML = html; p.classList.remove('hidden'); return;
  }
  if (!locOpen(id)) {
    const u = UNLOCKS[l.tier];
    html += `<div class="locked-box">${tx('ui_unlocks_at', { n: fmt(u.at) })}<br><small>${u.title}</small></div><p class="desc">${l.desc}</p>`;
    p.innerHTML = html; p.classList.remove('hidden'); return;
  }
  html += `<p class="desc">${l.desc}</p><div class="chips">`;
  if (l.field) html += `<span class="chip ore">${tx('ui_chip_mining')}</span>`;
  if (l.station) html += `<span class="chip" style="--c:${l.faction ? FACTIONS[l.faction].c : '#fff'}">🛰 ${l.station}</span>`;
  const dg = locDanger(id);
  if (has(U.BELT)) html += dg < 0.1 ? `<span class="chip good">${tx('ui_safe')}</span>` : dg < 0.3 ? `<span class="chip warn">${tx('ui_some_pirates')}</span>` : `<span class="chip bad">${tx('ui_dangerous')}</span>`;
  html += '</div>';
  const evs = S.events.filter(e => e.locs && e.locs.includes(id));
  if (evs.length) html += `<div class="evs">${evs.map(e => `<div class="ev">${e.icon} <b>${e.title}</b> <small>(${e.end - S.day}d)</small></div>`).join('')}</div>`;
  for (const e of evs) if (e.war) html += warBarHTML(e);
  if (l.faction && (S.allies || {})[l.faction]) html += `<div class="valline"><span class="ally-stars sm">${'★'.repeat(S.allies[l.faction])}</span>${tx('ui_ally_line', { n: Math.round(S.allies[l.faction] * WAR.starBonus * 100) })}</div>`;
  if (l.field) {
    const ores = Object.keys(l.field.ores).sort((a, b) => ITEMS[b].b - ITEMS[a].b);
    html += `<div class="ores">${ores.map(o => `<span class="ore" style="--c:${ITEMS[o].c}">${ITEMS[o].n} <b>${fmt(oreUnit(o))}</b></span>`).join('')}</div><small class="dim">${tx('ui_value_per_unit')}</small>`;
    if (l.field.hazard === 'heat') html += `<div class="warnline">${tx('ui_heat_warn')}</div>`;
  }
  if (l.market && !here && cargoUsed()) {
    const v = oreValueAt(id);
    if (v) html += `<div class="valline">${tx('ui_ore_sells', { v: fmt(v) })}${LOC[S.loc].market ? tx('ui_ore_at', { v: fmt(oreValueAt(S.loc)), loc: LOC[S.loc].n }) : ''}</div>`;
  }
  if (l.market && has(U.TRADE) && !here) {
    const hot = Object.keys(l.market).map(k => ({ k, m: priceRatio(id, k) })).filter(x => x.m >= 1.45).sort((a, b) => b.m - a.m).slice(0, 4);
    if (hot.length) html += `<div class="sub">${tx('ui_pays_well')}</div><div class="ores">${hot.map(x => `<span class="ore" style="--c:${ITEMS[x.k].c}">${ITEMS[x.k].n} <b>×${x.m.toFixed(1)}</b></span>`).join('')}</div>`;
  }
  if (id === 'oort' && !S.gateOpen) html += guardianBox();
  const pws = powersAt(id);
  if (pws.length) html += `<div class="sub">${tx('ui_your_power')}</div>${powerButtons(pws)}`;
  if (here) {
    html += `<div class="lp-actions">`;
    if (l.station) html += `<button class="btn primary big" onclick="openDock()">${tx('ui_dock_at', { st: l.station })}</button>`;
    if (l.field) html += `<button class="btn ore big" onclick="enterMine()">${id === 'oort' && !S.gateOpen ? tx('ui_mine_guardian') : tx('ui_mine_field', { f: l.field.n })}</button>`;
    if (id === 'oort' && S.gateOpen) html += `<button class="btn primary big" onclick="openGalaxy()">${tx('ui_enter_gate')}</button>`;
    if (!l.station) {
      const stations = NODES.filter(x => x.station && locOpen(x.id));
      const reachable = stations.some(x => travelInfo(x.id).fuel <= S.fuel);
      if (!reachable) html += `<button class="btn danger big" onclick="towShip(tx('ui_out_of_fuel'))">${tx('ui_call_tug')}</button>`;
    }
    html += `</div>`;
  } else {
    const info = travelInfo(id);
    const ok = info.fuel <= S.fuel;
    html += `<div class="travel">
      <div><small>${tx('ui_fuel')}</small><b class="${ok ? '' : 'badt'}">${info.fuel} <small>/ ${Math.floor(S.fuel)}</small></b></div>
      <div><small>${tx('ui_time')}</small><b>${uiDays(info.days)}</b></div>
      ${l.station ? `<div><small>${tx('ui_fuel_price')}</small><b>${fmt(fuelPrice(id))} <small>cr</small></b></div>` : ''}
      ${has(U.BELT) ? `<div><small>${tx('ui_ambush_risk')}</small><b class="${info.danger > 0.3 ? 'badt' : ''}">${Math.round(info.danger * 100)}%</b></div>` : ''}</div>
      <button class="btn primary big" ${ok ? '' : 'disabled'} onclick="MapScene.startTravel('${id}')">${ok ? tx('ui_fly_here') : tx('ui_no_fuel')}</button>`;
  }
  p.innerHTML = html;
  p.classList.remove('hidden');
}
function hideLocPanel() { $('locPanel').classList.add('hidden'); MapScene.sel = null; }
function enterMine() {
  sfx('click');
  if (S.loc === 'oort' && !S.gateOpen) {
    const b = ENEMIES[sysDef().boss];
    return showModal({ icon: '☠', title: tx('ui_face_boss', { b: b.n }), danger: true, html: `${guardianBox()}<p>${tx('ui_boss_body')}</p>`,
      buttons: [{ label: tx('ui_lets_fight'), cls: 'danger', fn: () => { closeSheet(true); setScene(MineScene, S.loc); } }, { label: tx('ui_not_yet'), fn: () => {} }] });
  }
  closeSheet(true); setScene(MineScene, S.loc);
}
// how ready you are for this system's final guardian
function guardianBox() {
  const b = ENEMIES[sysDef().boss], th = fleetThreat(sysDef().bossFleet, 5);
  const [lbl, col, tip] = th < 0.9 ? [tx('ui_g_ready'), '#6dffb0', tx('ui_g_ready_t')] : th < 1.5 ? [tx('ui_g_tough'), '#ffc857', tx('ui_g_tough_t')] : th < 2.4 ? [tx('ui_g_vhard'), '#ff934a', tx('ui_g_vhard_t')] : [tx('ui_g_deadly'), '#ff4d6d', tx('ui_g_deadly_t')];
  return `<div class="guardian" style="--c:${col}"><b>${tx('ui_guardian', { b: b.n })}</b><span>${tx('ui_chances', { l: lbl, t: tip })}</span></div>`;
}

function showMapUI(on) {
  $('mapTools').classList.toggle('hidden', !on);
  if (!on) $('locPanel').classList.add('hidden');
}
function showMineUI(on) {
  document.body.classList.toggle('mining', on);
  $('mineUI').classList.toggle('hidden', !on);
  $('touchUI').classList.toggle('hidden', !on || !isTouch);
  if (!on) { coach(''); $('battleUI').classList.add('hidden'); document.body.classList.remove('battle'); }
  if (on) $('mineName').textContent = MineScene.space ? tx('ui_pirate_ambush') : MineScene.loc.field.n;
}

function updateMineHUD() {
  const now = performance.now();
  if (updateMineHUD.t && now - updateMineHUD.t < 150) return;
  updateMineHUD.t = now;
  const sc = MineScene;
  // what's in your hold, each with how good it is: value tier and price per unit
  const rows = Object.keys(S.cargo).sort((a, b) => ITEMS[b].b - ITEMS[a].b).map(k => `<div class="crow"><i style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}${ITEMS[k].ore ? `<span class="tier">${oreStars(k)}</span><small class="unit">${tx('ui_each', { n: fmt(oreUnit(k)) })}</small>` : ''}<b>${fmt(S.cargo[k])}</b></div>`).join('');
  const val = LOC[S.loc].market ? oreValueAt(S.loc) : 0;
  $('mineCargo').innerHTML = (rows || `<div class="crow dim">${tx('ui_hold_empty')}</div>`) + (val ? `<div class="crow val">${tx('ui_worth')}<b class="cr">${fmt(val)} cr</b></div>` : '');
  const depth = sc.space ? '' : `<span class="depth">${tx('ui_depth', { d: Math.round(sc.depthOf(sc.p.y) * 100), r: (1 + sc.depthOf(sc.p.y) * 4).toFixed(1) })}</span>`;
  const tools = sc.space ? '' : (isTouch ? '' : (hasTool('drill') ? `<span class="tool">${sc.tool === 'drill' ? tx('ui_t_drill') : tx('ui_t_laser')} <small>[Q]</small></span>` : '') + (hasTool('tractor') ? `<span class="tool">${sc.pullCd > 0 ? tx('ui_t_pulse_cd', { n: Math.ceil(sc.pullCd) }) : tx('ui_t_pulse_ok')} <small>[E]</small></span>` : '')
    + (hasTool('overdrive') ? `<span class="tool">${sc.boostT > 0 ? tx('ui_t_od_on', { n: Math.ceil(sc.boostT) }) : sc.boostCd > 0 ? tx('ui_t_od_cd', { n: Math.ceil(sc.boostCd) }) : tx('ui_t_od_ok')} <small>[R]</small></span>` : '')
    + (hasTool('charges') ? `<span class="tool">${sc.bombCd > 0 ? tx('ui_t_bomb_cd', { n: Math.ceil(sc.bombCd) }) : tx('ui_t_bomb_ok')} <small>[F]</small></span>` : '')
    + (hasTool('deepscan') ? `<span class="tool">${sc.scanCd > 0 ? tx('ui_t_scan_cd', { n: Math.ceil(sc.scanCd) }) : tx('ui_t_scan_ok')} <small>[C]</small></span>` : '')
    + (hasTool('widebeam') ? `<span class="tool">${tx('ui_t_wide')}</span>` : '')
    + (hasTool('phase') ? `<span class="tool">${sc.phaseT > 0 ? tx('ui_t_phase_on', { n: Math.ceil(sc.phaseT) }) : sc.phaseCd > 0 ? tx('ui_t_phase_cd', { n: Math.ceil(sc.phaseCd) }) : tx('ui_t_phase_ok')} <small>[X]</small></span>` : ''))
    + (sc.relic ? `<span class="tool" style="color:#ffe080">🏛 ${sc.relic.n} ${Math.ceil(sc.relic.t)}s</span>` : '')
    + (sysDef().sweeps && !sc.space && sc.sweepIn < 4 && !sc.sweep ? `<span class="tool" style="color:#9ff3ff">${tx('ui_beam_in', { n: Math.ceil(sc.sweepIn) })}</span>` : '')
    + (sc.moltenT > 0 ? `<span class="tool" style="color:#ffb040">${tx('ui_molten', { n: Math.ceil(sc.moltenT) })}</span>` : sysDef().pulses && !sc.space && sc.pulseIn < 10 ? `<span class="tool">${tx('ui_pulse_in', { n: Math.ceil(sc.pulseIn) })}</span>` : '');
  for (const [id, k, cd, lbl, mx] of [['boostBtn', 'overdrive', sc.boostCd, tx('ui_b_boost'), 45], ['bombBtn', 'charges', sc.bombCd, tx('ui_b_bomb'), 10], ['scanBtn', 'deepscan', sc.scanCd, tx('ui_b_scan'), built('sonar') ? 7 : 14], ['pullBtn', 'tractor', sc.pullCd, tx('ui_b_pull'), 14], ['phaseBtn', 'phase', sc.phaseCd, tx('ui_b_phase'), 20]]) { const ok = !hasTool(k) || sc.space; $(id).classList.toggle('hidden', ok); $(id).textContent = cd > 0 ? Math.ceil(cd) + 's' : lbl; $(id).classList.toggle('cd', cd > 0); $(id).style.setProperty('--p', cd > 0 ? (1 - cd / mx).toFixed(3) : 1); }
  $('toolBtn').classList.toggle('hidden', !hasTool('drill') || sc.space); $('toolBtn').textContent = sc.tool === 'drill' ? tx('ui_b_laser') : tx('ui_b_drill');

  $('mineInfo').innerHTML = tools + (ship.shieldMax ? `<span>${tx('ui_shield_hud', { a: fmt(sc.p.shield), b: fmt(ship.shieldMax) })}</span>` : '') + (sc.loc.field.hazard === 'heat' ? ` <span class="badt">${tx('ui_heat')}</span>` : '');
  const combat = sc.inCombat || sc.clearT > 0;
  $('fireBtn').textContent = sc.inCombat ? tx('ui_b_fire') : tx('ui_b_laser');
  document.body.classList.toggle('battle', combat);
  $('battleUI').classList.toggle('hidden', !combat);
  if (combat) {
    const many = sc.enemies.length > 1;
    $('btTitle').innerHTML = sc.inCombat ? `⚔ ${sc.enemies.length} ${sc.enemies.some(e => ENEMIES[e.k].alien || ENEMIES[e.k].hive || ENEMIES[e.k].whale || ENEMIES[e.k].kraken || ENEMIES[e.k].radiant || ENEMIES[e.k].phoenix || ENEMIES[e.k].hydra || ENEMIES[e.k].warden || ENEMIES[e.k].archon || ENEMIES[e.k].devourer) ? tx(many ? 'ui_bt_hostiles' : 'ui_bt_hostile') : tx(many ? 'ui_bt_pirates' : 'ui_bt_pirate')}` : tx('ui_area_clear');
    $('btnWarp').classList.toggle('hidden', !sc.space || !sc.inCombat);
    $('btnWarp').textContent = sc.warp ? tx('ui_warping', { n: Math.round(sc.warp.t / ship.warpTime * 100) }) : tx('ui_warp_out', { n: ship.warpTime.toFixed(1) });
    $('btnContinue').classList.toggle('hidden', !(sc.space && !sc.inCombat));
  }
  updateHUD();
}

function showBattleUI(on) {}

function openSheet(title, html, cls) {
  const s = $('sheet');
  s.className = 'sheet ' + (cls || '');
  s.innerHTML = `<div class="sh-head"><h2>${title}</h2><button class="x" onclick="closeSheet()">✕</button></div><div class="sh-body">${html}</div>`;
  s.classList.remove('hidden');
}
function closeSheet(silent) {
  const s = $('sheet');
  const wasDock = s.classList.contains('dock') && !s.classList.contains('hidden');
  s.classList.add('hidden'); save(); updateHUD();
  if (silent) return;
  if (wasDock && !has(U.MAP) && LOC[S.loc].field) { setScene(MineScene, S.loc); return; }
  if (scene === MapScene && !MapScene.travel) { showMapUI(true); selectLoc(S.loc); }
}

// ---------- DOCK (station) ----------
function openDock() {
  sfx('click');
  if (scene !== MapScene) setScene(MapScene);
  showMapUI(false);
  lastDock = dockAtStation();
  dockTab = 'upg';
  renderDock(true);
  if (lastDock.total > 0) { sfx('cash'); for (let i = 1; i < Math.min(6, 2 + Math.log10(lastDock.total)); i++) tone(1318 + i * 120, 0.08, 'square', 0.04, null, i * 0.12); }
  document.body.classList.toggle('newbie', S.stats.docks <= 4);
}
function renderDock(fresh) {
  const l = LOC[S.loc];
  const tabs = [['upg', tx('ui_tab_upg')]];
  if (has(U.OUTPOST) && l.field) tabs.push(['outpost', tx('ui_tab_outpost') + (!S.outposts[l.id] && S.credits >= buildCost(l.id) ? ' <i class="dot"></i>' : '')]);
  if (has(U.TRADE) && !l.depot) tabs.push(['trade', tx('ui_tab_trade')], ['contracts', tx('ui_tab_contracts') + (S.active.some(canDeliver) ? ' <i class="dot"></i>' : '')]);
  if (has(U.TRADE) && !l.depot && (powersAt(l.id).length || (has(U.SATURN) && STATION_TIER[l.id]))) tabs.push(['planet', tx('ui_tab_planet')]);
  let receipt = '';
  const r = lastDock;
  if (fresh && r && (r.sold.length || r.fuel || r.repair)) {
    receipt = `<div class="receipt">
      ${r.sold.length ? `<div class="rc-main"><div><small>${tx('ui_sold')}</small><span>${r.sold.map(([k, n]) => `<i class="sw" style="background:${ITEMS[k].c}"></i>${n} ${ITEMS[k].n}`).join(' &nbsp; ')}</span></div><b class="cr" id="rcTotal" data-v="${r.total}">+0 cr</b></div>` : ''}
      ${r.total > 0 && S.stats.docks <= 1 ? `<div class="rc-first">${tx('ui_first_sale')}</div>` : ''}
      ${marketClosed(S.loc) ? `<div class="rc-sub badt">${tx('ui_strike_nosale')}</div>` : ''}
      ${r.fuel || r.repair ? `<div class="rc-sub">${r.fuel ? tx('ui_refueled', { n: r.fuel, c: fmt(r.fuelCost) }) : ''} ${r.repair ? (r.repairCost ? tx('ui_repaired', { n: r.repair, c: fmt(r.repairCost) }) : tx('ui_repaired_free', { n: r.repair })) : ''}</div>` : ''}
    </div>`;
  }
  let sellbox = '';
  const oreN = cargoUsed();
  if (oreN && has(U.MAP)) {
    const here = cargoValueAt(S.loc), alts = betterMarkets(S.loc);
    sellbox = `<div class="sellbox">
      <div class="sb-cargo"><small>${tx('ui_cargo_cap')}</small><span>${ITEM_KEYS.filter(k => S.cargo[k]).map(k => `<i class="sw" style="background:${ITEMS[k].c}"></i>${fmt(S.cargo[k])} ${ITEMS[k].n}`).join(' &nbsp; ')}</span></div>
      ${warSellHint()}
      ${l.black && !marketClosed(S.loc) ? `<div class="warhint badt">${tx('ui_black_mkt', { n: Math.round(blackMarketLoss(cargoUsed())) })}</div>` : ''}
      <div class="sb-row">
        ${marketClosed(S.loc) ? `<div class="badt">${tx('ui_strike')}</div>` : here ? `<button class="btn primary" onclick="sellHere()">${tx('ui_sell_all', { v: fmt(here) })}</button>` : `<small>${tx('ui_nothing_sells')}</small>`}
        <div class="sb-alts">${alts.length ? alts.map(a => `<span onclick="closeSheet();selectLoc('${a.id}')"><b>${LOC[a.id].n}</b> ${tx('ui_pays')} <b class="cr">${fmt(a.v)}</b> <em>+${Math.round((a.v / Math.max(1, here) - 1) * 100)}%</em> <small>· ${a.fuel} ⛽</small></span>`).join('') : `<small>${tx('ui_best_price')}</small>`}</div>
      </div></div>`;
  }
  const body = dockBody(dockTab);
  const foot = [];
  if (l.field) foot.push(`<button class="btn ore big" onclick="enterMine()">${tx('ui_launch', { f: l.field.n })}</button>`);
  if (has(U.MAP)) foot.push(`<button class="btn big" onclick="closeSheet()">${tx('ui_star_map')}</button>`);
  const keep = $('sheet').querySelector('.tabbody');
  const sc = keep && !fresh ? keep.scrollTop : 0;
  openSheet(`🛰 ${l.station} <small>${l.n}</small>`, `${receipt}${sellbox}
    ${tabs.length > 1 ? `<div class="tabs">${tabs.map(([k, n]) => `<button class="tab ${k === dockTab ? 'on' : ''}" onclick="dockTab='${k}';renderDock()">${n}</button>`).join('')}</div>` : ''}
    <div class="tabbody">${body}</div>
    <div class="dock-foot">${foot.join('')}</div>`, 'dock');
  const nb = $('sheet').querySelector('.tabbody'); if (nb) nb.scrollTop = sc;
  const rt = $('rcTotal');
  if (rt) countUp(rt, +rt.dataset.v);
  for (const k of UPG_KEYS) if (upgOpen(k)) S.seenUpg[k] = 1;
  save();   // every purchase/sale re-renders the dock, so this checkpoints them
  updateHUD();
}
function powerButtons(pws) {
  return `<div class="powers">${pws.map(o => `<button class="btn small-btn ${o.kind === 'nuke' ? 'danger' : ''}" ${o.ok ? '' : 'disabled'} onclick="doPower('${o.kind}','${o.arg}')" title="${o.d || ''}">${o.icon} ${o.label} · ${fmt(o.cost)}${o.why ? ` <small>(${o.why})</small>` : o.d ? ` <small>— ${o.d}</small>` : ''}</button>`).join('')}</div>`;
}
function demandChip(loc, g) {
  const d = demandOf(loc, g), [t, c] = demandLabel(d);
  return `<span class="dem ${c}" title="${t}${d < 1 ? tx('ui_full_again', { n: demandDays(loc, g) }) : ''}"><i style="width:${Math.round(d * 100)}%"></i><b>${t}</b></span>`;
}
function tradeRun(g, to) {
  const n = doBuy(S.loc, g, 9999);
  if (!n) { toast(tx('ui_no_cr_space'), 'bad'); return; }
  sfx('click'); toast(tx('ui_bought_run', { n, g: ITEMS[g].n, loc: LOC[to].n }), 'good');
  save(); closeSheet(); selectLoc(to); MapScene.focus(to);
}
function freighterBtn(id, r) {
  const why = freighterBlock(id, r.to, r.g), inc = freighterIncome({ from: id, to: r.to, g: r.g }), fc = FREIGHT.cost();
  return why ? `<button class="btn small-btn" disabled title="${why.long.replace(/<[^>]+>/g, '')}">🚚 ${why.short}</button>`
    : `<button class="btn small-btn" onclick="doFreighter('${id}','${r.to}','${r.g}')">${tx('ui_freighter_btn', { c: fmt(fc), i: fmt(inc) })}</button>`;
}
// fleet status, so it's clear what limits more freighters
function fleetLine() {
  const n = (S.freighters || []).length, max = FREIGHT.max(), nx = FREIGHT.nextSlots();
  const full = n >= max;
  return `<div class="fleetline ${full ? 'full' : ''}">${tx('ui_fleet', { n, max, p: FREIGHT.perRoute, c: fmt(FREIGHT.cost()) })}${full ? (nx ? tx('ui_fleet_full', { s: nx[1], u: UNLOCKS[nx[0]].title }) : tx('ui_fleet_max')) : nx ? tx('ui_fleet_next', { s: nx[1], u: UNLOCKS[nx[0]].title }) : ''}</div>`;
}
function doFreighter(from, to, g) {
  const why = freighterBlock(from, to, g);
  if (why || !hireFreighter(from, to, g)) { toast(why ? why.short : tx('ui_no_freighter'), 'bad'); return; }
  sfx('upgrade'); toast(tx('ui_freighter_runs', { g: ITEMS[g].n, loc: LOC[to].n }), 'good'); renderDock();
}
function warSellHint() {
  const w = backedWar(); if (!w || LOC[S.loc].faction !== w.backed || marketClosed(S.loc)) return '';
  let p = salePushAmt(S.loc, 'iron', oreValueAt(S.loc));
  for (const k of GOODS) if (S.cargo[k] && wantsGood(S.loc, k)) p += salePushAmt(S.loc, k, goodsValue(S.loc, k, S.cargo[k]));
  return p >= 0.5 ? `<div class="warhint">${tx('ui_war_push', { n: Math.round(p), f: FACTIONS[w.backed].n })}</div>` : '';
}
function sellHere() {
  const r = sellAllOre(S.loc);
  for (const k of GOODS) if (S.cargo[k] && wantsGood(S.loc, k)) { const n = S.cargo[k]; const got = doSell(S.loc, k, n); r.sold.push([k, n, got]); r.total += got; }
  if (!r.total) return;
  sfx('cash');
  lastDock = { ...r, fuel: 0, repair: 0 };
  renderDock(true);
}
function countUp(el, v) {
  const t0 = performance.now(), dur = Math.min(1200, 300 + v / 4);
  const step = now => { const k = Math.min(1, (now - t0) / dur); el.textContent = '+' + fmt(v * (1 - Math.pow(1 - k, 3))) + ' cr'; if (k < 1) requestAnimationFrame(step); };
  requestAnimationFrame(step);
}
function dockBody(tab) {
  const id = S.loc, l = LOC[id];
  if (tab === 'upg') {
    let h = '<div class="upgs">';
    for (const k of UPG_KEYS) {
      if (!upgOpen(k)) continue;
      const u = UPG[k], lv = S.lv[k];
      const maxed = lv >= u.max;
      const cost = maxed ? 0 : upgCost(k, lv);
      const can = !maxed && S.credits >= cost;
      const nMax = maxed ? 0 : affordableLevels(k);
      h += `<div class="upg ${maxed ? 'maxed' : ''} ${can ? 'can' : ''} ${k === lastBought ? 'just' : ''}">
        ${!S.seenUpg[k] ? `<span class="newb">${tx('ui_newb')}</span>` : ''}
        <div class="uh"><span class="uicon">${u.icon}</span><b>${u.n}</b><span class="lvl">${k === 'hull' ? u.names[lv - 1] : tx('ui_lv') + ' ' + lv + `<small>/${u.max}</small>`}</span></div>
        <div class="lvbar"><i style="width:${lv / u.max * 100}%"></i></div>
        <div class="ud">${maxed ? `<b>${tx('ui_maxed')}</b>` : upgDelta(k, lv, lv + 1)}</div>
        ${maxed ? '' : `<div class="ubtns"><button class="btn ${can ? 'primary' : ''}" ${can ? '' : 'disabled'} onclick="buyUpg('${k}')">${can ? tx('ui_buy') : tx('ui_need')} · ${fmt(cost)}</button>${nMax > 1 && k !== 'hull' ? `<button class="btn primary maxb" onclick="buyUpg('${k}', ${nMax})">×${nMax}</button>` : ''}</div>`}
      </div>`;
    }
    h += '</div>';
    const locked = UPG_KEYS.filter(k => !upgOpen(k));
    if (locked.length) h += `<p class="hint center">${tx(locked.length > 1 ? 'ui_more_upgN' : 'ui_more_upg1', { n: locked.length })}</p>`;
    return h;
  }
  if (tab === 'outpost') return outpostBody(id);
  if (tab === 'trade') {
    if (marketClosed(id)) return `<div class="empty">${tx('ui_strike_long')}</div>`;
    const keys = ITEM_KEYS.filter(k => (!ITEMS[k].ore && l.market[k] != null) || S.cargo[k]);
    const routes = tradeRoutes(id);
    const fc = FREIGHT.cost(), fn = (S.freighters || []).length;
    let h = routes.length ? `<div class="routes"><div class="sub">${tx('ui_best_trades')}</div>${routes.slice(0, 3).map(r => `<div class="route">
      <div><i class="sw" style="background:${ITEMS[r.g].c}"></i><b>${ITEMS[r.g].n}</b> ${tx('ui_buy_lc')} ${fmt(r.bp)} → <b>${LOC[r.to].n}</b> ${tx('ui_pays')} ${fmt(r.sp)} <em>×${(r.avg / r.bp).toFixed(1)}</em> ${demandChip(r.to, r.g)} <small>${tx('ui_profit_for', { p: fmt(r.profit * 0.9), u: r.units })}</small></div>
      <div class="rt-btns"><button class="btn small-btn primary" ${r.units && S.credits >= r.bp ? '' : 'disabled'} onclick="tradeRun('${r.g}','${r.to}')">${tx('ui_buy_fly', { n: r.units })}</button>
      ${has(U.TRADE) ? freighterBtn(id, r) : ''}</div></div>`).join('')}${has(U.TRADE) ? fleetLine() : ''}</div>` : `<p class="hint">${tx('ui_no_routes')}</p>`;
    h += `<p class="hint">${tx('ui_trade_hint')}</p>
      <div class="mkt"><div class="mrow mh"><span>${tx('ui_m_good')}</span><span>${tx('ui_m_sell')}</span><span>${tx('ui_m_have')}</span><span></span><span>${tx('ui_m_buy')}</span><span></span></div>`;
    for (const k of keys) {
      const sp = sellPrice(id, k), bp = buyPrice(id, k), have = S.cargo[k] || 0;
      const ratio = sp ? priceRatio(id, k) : 0;
      const trend = !sp ? '' : ratio > 1.4 ? '<i class="up">▲▲</i>' : ratio > 1.1 ? '<i class="up">▲</i>' : ratio < 0.75 ? '<i class="dn">▼▼</i>' : ratio < 0.95 ? '<i class="dn">▼</i>' : '';
      const ev = eventPriceMult(id, k) !== 1 ? '<i class="evi">⚡</i>' : '';
      h += `<div class="mrow">
        <span class="mname c-n"><i class="sw" style="background:${ITEMS[k].c}"></i>${ITEMS[k].n}${ev}</span>
        <span class="price c-sp">${sp ? fmt(sp) + ' ' + trend + (wantsGood(id, k) ? demandChip(id, k) : '') : '<small class="dim">—</small>'}</span>
        <span class="have c-h">${have || '<small class="dim">0</small>'}</span>
        <span class="bb c-sb">${sp && have ? `<button onclick="mktSell('${k}',1)">1</button><button onclick="mktSell('${k}',10)">10</button><button class="all" onclick="mktSell('${k}',9999)">${tx('ui_all')}</button>` : ''}</span>
        <span class="price c-bp">${bp ? fmt(bp) + `<small class="stock">${tx('ui_left', { n: stockLeft(id, k) })}</small>` : '<small class="dim">—</small>'}</span>
        <span class="bb c-bb">${bp ? `<button onclick="mktBuy('${k}',1)">1</button><button onclick="mktBuy('${k}',10)">10</button><button class="all" onclick="mktBuy('${k}',9999)">${tx('ui_max')}</button>` : ''}</span></div>`;
    }
    return h + '</div>';
  }
  if (tab === 'contracts') {
    const avail = S.contracts[id] || [];
    let h = `<div class="sub">${tx('ui_active_contracts')}</div>`;
    if (!S.active.length) h += `<div class="empty small">${tx('ui_none_yet')}</div>`;
    for (const c of S.active) {
      const dl = c.deadline - S.day;
      h += `<div class="contract ${canDeliver(c) ? 'ready' : ''}"><div>${c.urgent ? `<span class="chip bad">${tx('ui_urgent')}</span> ` : ''}${contractText(c)}<small>${tx(dl !== 1 ? 'ui_reward_leftN' : 'ui_reward_left1', { r: fmt(c.reward), d: dl })}${c.type === 'deliver' ? tx('ui_you_have', { a: S.cargo[c.item] || 0, b: c.qty }) : ''}</small></div>
        ${canDeliver(c) ? `<button class="btn primary" onclick="deliver('${c.id}')">${tx('ui_deliver')}</button>` : ''}</div>`;
    }
    h += `<div class="sub">${tx('ui_offered_at', { st: l.station })}</div>`;
    if (!avail.length) h += `<div class="empty small">${tx('ui_no_contracts')}</div>`;
    for (const c of avail) {
      h += `<div class="contract"><div>${c.urgent ? `<span class="chip bad">${tx('ui_urgent')}</span> ` : ''}${contractText(c)}<small>${tx('ui_reward_offer', { r: fmt(c.reward), rep: c.rep, d: c.days })}</small></div>
        <button class="btn" onclick="acceptContract('${id}','${c.id}');renderDock()">${tx('ui_accept')}</button></div>`;
    }
    return h;
  }
  if (tab === 'planet') {
    const pws = powersAt(id);
    let h = pws.length ? `<div class="sub">${tx('ui_power_on', { loc: l.n })}</div>${powerButtons(pws)}` : '';
    if (has(U.SATURN) && STATION_TIER[id]) h += dockBody('invest');
    else if (!has(U.SATURN)) h += `<p class="hint center">${tx('ui_politics_locked', { u: UNLOCKS[U.SATURN].title })}</p>`;
    return h;
  }
  if (tab === 'invest') {
    const lv = S.invest[id] || 0;
    const cost = investCost(id);
    const needRep = lv < 3 ? INVEST.rep[lv] : 0;
    const rep = l.faction ? S.rep[l.faction] : 0;
    const okRep = rep >= needRep;
    // investments add +10% of BASE income each (additive): show exactly what the next level does
    let inv = 0; for (const k in S.invest) inv += S.invest[k];
    const now = totalIncome(), next = now * (1 + INVEST.bonus * (inv + 1)) / (1 + INVEST.bonus * inv);
    let h = `<div class="inv"><p>${tx('ui_invest_intro', { st: l.station, n: inv, lvls: tx(inv === 1 ? 'ui_level1' : 'ui_levelN'), p: Math.round(inv * INVEST.bonus * 100) })}</p>
      <div class="inv-now">${tx('ui_invest_next', { a: fmt(now), b: fmt(next), p: Math.round(INVEST.bonus / (1 + INVEST.bonus * inv) * 100) })}</div><div class="invlv">`;
    for (let i = 0; i < 3; i++) {
      h += `<div class="ivc ${i < lv ? 'own' : i === lv ? 'next' : ''}"><b>${INVEST.names[i] ? tx('ui_inv' + i) : ''}</b><small>${tx('ui_base_income10')}</small><small>${tx('ui_plus_infl', { n: INVEST.infl[i] })}</small>${INVEST.rep[i] ? `<small>${tx('ui_needs_rep', { n: INVEST.rep[i] })}</small>` : ''}<em>${i < lv ? tx('ui_owned') : fmt(INVEST.cost[i] * (STATION_TIER[id] || 5)) + ' cr'}</em></div>`;
    }
    h += '</div>';
    if (cost != null) h += `<button class="btn primary big" ${S.credits >= cost && okRep ? '' : 'disabled'} onclick="buyInvest()">${okRep ? tx('ui_invest_btn', { c: fmt(cost) }) : tx('ui_invest_needrep', { n: needRep, f: FACTIONS[l.faction].n, r: Math.round(rep) })}</button>`;
    else h += `<div class="empty small">${tx('ui_you_control')}</div>`;
    h += `<p class="hint">${tx('ui_income_mult', { m: incomeMult().toFixed(2) })}</p></div>`;
    return h;
  }
  return '';
}
function upgDelta(k, a, b) {
  const ar = (x, y) => `${x} → <b>${y}</b>`;
  const at = (lv, f) => { const o = S.lv[k]; S.lv[k] = lv; const v = f(); S.lv[k] = o; return v; };
  switch (k) {
    case 'hull': return tx('ui_d_hull', { n: UPG.hull.names[b - 1], c: ar(UPG.hull.cargo[a - 1], UPG.hull.cargo[b - 1]), a: ar(UPG.hull.hp[a - 1], UPG.hull.hp[b - 1]) });
    case 'laser': return tx('ui_d_laser', { v: ar(fmt(at(a, () => ship.laserDps)), fmt(at(b, () => ship.laserDps))) });
    case 'magnet': return tx('ui_d_range', { v: ar(at(a, () => ship.magnet), at(b, () => ship.magnet)) }) + (at(b, () => ship.drones) > at(a, () => ship.drones) ? tx('ui_d_drone1') : tx('ui_d_drones', { n: at(a, () => ship.drones) }));
    case 'cargo': return tx('ui_d_cargo', { v: ar(at(a, () => ship.cargoMax), at(b, () => ship.cargoMax)) });
    case 'extractor': return tx('ui_d_extr', { v: ar('×' + at(a, () => ship.yieldMult).toFixed(2), '×' + at(b, () => ship.yieldMult).toFixed(2)) });
    case 'refinery': return tx('ui_d_ref', { v: ar('×' + at(a, () => ship.refinery).toFixed(2), '×' + at(b, () => ship.refinery).toFixed(2)) });
    case 'engine': return tx('ui_d_engine', { v: ar('×' + at(a, () => ship.speed).toFixed(2), '×' + at(b, () => ship.speed).toFixed(2)), w: at(b, () => ship.warpTime).toFixed(1) });
    case 'tank': return tx('ui_d_tank', { v: ar(at(a, () => ship.fuelMax), at(b, () => ship.fuelMax)) });
    case 'shield': return tx('ui_d_shield', { v: ar(fmt(at(a, () => ship.shieldMax)), fmt(at(b, () => ship.shieldMax))) });
    case 'weapons': return tx('ui_d_weapons', { v: ar(fmt(at(a, () => ship.weaponDps)), fmt(at(b, () => ship.weaponDps))) });
    case 'scanner': return tx('ui_d_scanner', { v: ar(Math.round(at(a, () => ship.avoid) * 100) + '%', Math.round(at(b, () => ship.avoid) * 100) + '%') });
  }
}
function affordableLevels(k) {
  let n = 0, c = 0, lv = S.lv[k];
  while (lv + n < UPG[k].max && n < 100) { const nc = upgCost(k, lv + n); if (c + nc > S.credits) break; c += nc; n++; }
  return n;
}

function drawShipPreview(id, lv, t) {
  const c = $(id); if (!c) return;
  const x = c.getContext('2d');
  const w = c.width, h = c.height;
  x.clearRect(0, 0, w, h);
  const g = x.createRadialGradient(w / 2, h / 2, 10, w / 2, h / 2, w / 2);
  g.addColorStop(0, '#16224a'); g.addColorStop(1, '#070b1c');
  x.fillStyle = g; x.fillRect(0, 0, w, h);
  x.strokeStyle = 'rgba(61,232,255,0.1)';
  for (let i = 0; i < w; i += 20) { x.beginPath(); x.moveTo(i, 0); x.lineTo(i, h); x.stroke(); }
  for (let i = 0; i < h; i += 20) { x.beginPath(); x.moveTo(0, i); x.lineTo(w, i); x.stroke(); }
  const Hd = HULLS[lv.hull - 1];
  const ex = Hd.hull[0][0] - Hd.tail + 28, ey = Math.abs(Hd.wing[1][1]) * 2 + 8;
  const sc = Math.min(w * 0.78 / ex, h * 0.8 / ey);
  const cx = (Hd.hull[0][0] + Hd.tail - 22) / 2;
  drawPlayerShip(x, lv, w / 2 - cx * sc, h / 2 + Math.sin(t * 1.5) * 3, 0, sc, 0.7 + 0.3 * Math.sin(t * 3), t);
}
function mktSell(k, n) { if (marketClosed(S.loc)) return; const before = S.credits; doSell(S.loc, k, n); const got = S.credits - before; if (got) { sfx('cash'); toast(`+${fmt(got)} cr`, 'good'); } renderDock(); }
function mktBuy(k, n) { if (marketClosed(S.loc)) return; if (cargoFree() <= 0) { toast(tx('ui_cargo_full'), 'bad'); return; } const b = doBuy(S.loc, k, n); if (b) sfx('click'); else toast(tx('ui_no_credits'), 'bad'); renderDock(); }
let lastBought = null;
function buyUpg(k, n) {
  n = n || 1;
  let bought = 0;
  for (let i = 0; i < n; i++) {
    const lv = S.lv[k]; if (lv >= UPG[k].max) break;
    const cost = upgCost(k, lv); if (S.credits < cost) break;
    S.credits -= cost; S.lv[k]++; bought++;
  }
  if (!bought) return;
  lastBought = k; setTimeout(() => { if (lastBought === k) lastBought = null; }, 900);
  if (k === 'hull') S.hull = ship.hpMax;
  if (k === 'tank' && has(U.MAP)) S.fuel = ship.fuelMax;
  sfx('upgrade');
  renderDock();
  if (k === 'hull') {
    addNews('🚀', tx('ui_new_ship', { n: UPG.hull.names[S.lv.hull - 1] }), '#3de8ff');
    showModal({ icon: '', title: tx('ui_new_ship_t', { n: UPG.hull.names[S.lv.hull - 1] }), cls: 'unlock', html: `<canvas id="newShip" width="420" height="200"></canvas><p>${tx('ui_new_ship_stats', { c: fmt(ship.cargoMax), a: fmt(ship.hpMax) })}</p>`,
      buttons: [{ label: tx('ui_nice'), cls: 'primary', fn: () => {} }],
      after: () => { const t0 = performance.now(); const anim = () => { if ($('newShip')) { drawShipPreview('newShip', shipLv(), (performance.now() - t0) / 1000); requestAnimationFrame(anim); } }; anim(); } });
  } else toast(`${UPG[k].n} → ${tx('ui_lv')} ${S.lv[k]}${bought > 1 ? ` (+${bought})` : ''}`, 'good');
}
function outpostBody(id) {
  const l = LOC[id], o = S.outposts[id], z = l.field.z;
  const boost = (id === 'luna' && built('driver') ? 3 : 1) * (built('ringstation') ? 3 : 1);
  if (!o) {
    const c = buildCost(id);
    return `<div class="op-empty"><div class="op-art">🤖</div><h3>${tx('ui_op_build_t')}</h3>
      <p>${tx('ui_op_build_d', { f: l.field.n })}</p>
      <p>${tx('ui_op_build_r', { n: fmt(OUTPOST.rate[z] * incomeMult() * boost), s: OUTPOST.slots })}</p>
      <button class="btn primary big" ${S.credits >= c ? '' : 'disabled'} onclick="doBuild('${id}')">${tx('ui_op_build_btn', { c: fmt(c) })}</button></div>`;
  }
  const cap = outpostCap(o.lv), full = o.n >= cap;
  const inc = outpostIncome(id), per = OUTPOST.rate[z] * Math.pow(2, o.lv - 1) * incomeMult() * boost;
  const d1 = droneCost(id, 1), n10 = Math.min(10, cap - o.n), d10 = droneCost(id, n10), nm = maxAffordableDrones(id);
  const lc = outpostLvCost(id);
  let slots = '';
  for (let i = 0; i < cap; i++) slots += `<i class="${i < o.n ? 'on' : ''}"></i>`;
  return `<div class="op">
    <div class="op-top"><div><small>${tx('ui_op_level', { n: o.lv })}</small><b class="cr">+${fmt(inc)} cr/s</b><span>${tx('ui_op_drones', { n: o.n, p: fmt(per) })}</span></div><div class="op-drones">${slots}</div></div>
    <div class="sub">${tx('ui_drones')} <span class="dim">${tx('ui_op_slots', { n: o.n, c: cap })}</span></div>
    ${full ? `<div class="empty small">${tx('ui_op_full', { s: OUTPOST.slots })}</div>` : `<div class="op-row">
      <button class="btn ${S.credits >= d1 ? 'primary' : ''}" ${S.credits >= d1 ? '' : 'disabled'} onclick="doDrones('${id}',1)">${tx('ui_op_plus1', { c: fmt(d1) })}</button>
      ${n10 > 1 ? `<button class="btn ${S.credits >= d10 ? 'primary' : ''}" ${S.credits >= d10 ? '' : 'disabled'} onclick="doDrones('${id}',${n10})">+${n10} · ${fmt(d10)}</button>` : ''}
      <button class="btn ${nm ? 'primary' : ''}" ${nm ? '' : 'disabled'} onclick="doDrones('${id}','max')">${tx('ui_op_max')}${nm ? ` (+${nm})` : ''}</button>
    </div>`}
    <div class="sub">${tx('ui_op_lv_sub')}</div>
    ${lc != null ? `<button class="btn ${S.credits >= lc ? 'primary' : ''} big" ${S.credits >= lc ? '' : 'disabled'} onclick="doOutLv('${id}')">${tx('ui_op_lv_btn', { n: o.lv + 1, s: OUTPOST.slots, c: fmt(lc) })}</button>` : `<div class="empty small">${tx('ui_op_maxlv')}</div>`}
    <p class="hint">${tx('ui_op_hint')}</p>
  </div>`;
}

function doBuild(id) { if (buildOutpost(id)) { sfx('win'); toast(tx('ui_op_online'), 'good'); renderDock(); } }
function doDrones(id, k) { const n = buyDrones(id, k); if (n) { sfx('upgrade'); toast(tx(n > 1 ? 'ui_plus_droneN' : 'ui_plus_drone1', { n }), 'good'); renderDock(); } }
function doOutLv(id) { if (upgradeOutpost(id)) { sfx('win'); toast(tx('ui_op_upgraded'), 'good'); renderDock(); } }

function deliver(cid) { const c = S.active.find(x => x.id === cid); if (c && canDeliver(c)) completeContract(c); renderDock(); }
function buyInvest() {
  const id = S.loc, cost = investCost(id);
  if (cost == null || S.credits < cost) return;
  S.credits -= cost; S.invest[id] = (S.invest[id] || 0) + 1;
  const l = LOC[id]; if (l.faction) repChange(l.faction, 5);
  sfx('win');
  addNews('🏛️', tx('ui_invest_news', { inv: tx('ui_inva' + (S.invest[id] - 1)), st: l.station }), '#ffc857');
  toast(tx('ui_invest_done', { n: INVEST.infl[S.invest[id] - 1] }), 'good');
  renderDock();
}

// ---------- global panels ----------
// every ore you can reach in this system, most valuable first
function oreGuide() {
  const seen = new Set(); for (const l of FIELDS) if (locOpen(l.id)) for (const k in l.field.ores) seen.add(k);
  for (const k in S.cargo) if (ITEMS[k].ore) seen.add(k);
  return [...seen].sort((a, b) => ITEMS[b].b - ITEMS[a].b).map(k => `<div class="srow"><span><i class="sw" style="background:${ITEMS[k].c}"></i> ${ITEMS[k].n} <span class="tier">${oreStars(k)}</span></span><b>${fmt(oreUnit(k))} cr</b></div>`).join('');
}
function openShip() {
  sfx('click');
  const rows = Object.keys(S.cargo).map(k => `<div class="srow"><span><i class="sw" style="background:${ITEMS[k].c}"></i> ${ITEMS[k].n}</span><b>${S.cargo[k]}</b><button class="mini" onclick="jettison('${k}')">${tx('ui_dump')}</button></div>`).join('');
  let upg = '';
  for (const k of UPG_KEYS) if (upgOpen(k)) upg += `<div class="srow"><span>${UPG[k].icon} ${UPG[k].n}</span><b>${k === 'hull' ? UPG.hull.names[S.lv.hull - 1] : tx('ui_lv') + ' ' + S.lv[k] + ' / ' + UPG[k].max}</b></div>`;
  openSheet(`🚀 ${S.shipName} <small>${tx('ui_ship_class', { n: UPG.hull.names[S.lv.hull - 1] })}</small>`, `<div class="yard-top"><canvas id="shipView" width="420" height="190"></canvas></div>
    <div class="cols"><div><div class="sub">${tx('ui_systems')}</div>${upg}</div><div><div class="sub">${tx('ui_hold', { a: cargoUsed(), b: ship.cargoMax })}</div>${rows || `<div class="empty small">${tx('ui_empty')}</div>`}
    <div class="sub">${tx('ui_stats')}</div><div class="srow"><span>${tx('ui_ore_mined')}</span><b>${fmt(S.stats.mined)}</b></div><div class="srow"><span>${tx('ui_lifetime')}</span><b>${fmt(S.stats.earned)} cr</b></div><div class="srow"><span>${tx('ui_record')}</span><b class="cr">${fmt(S.stats.peak || 0)} cr</b></div>
    <div class="sub">${tx('ui_ore_values')} <small class="dim">${tx('ui_per_unit')}</small></div>${oreGuide()}
    ${has(U.BELT) ? `<div class="srow"><span>${tx('ui_battles')}</span><b>${S.stats.won} / ${S.stats.lost}</b></div>` : ''}${has(U.TRADE) ? `<div class="srow"><span>${tx('ui_contracts')}</span><b>${S.stats.contracts}</b></div>` : ''}</div></div>`);
  const t0 = performance.now();
  const anim = () => { if (!$('sheet').classList.contains('hidden') && $('shipView')) { drawShipPreview('shipView', shipLv(), (performance.now() - t0) / 1000); requestAnimationFrame(anim); } };
  anim();
}
function jettison(k) { addCargo(k, -S.cargo[k]); sfx('click'); openShip(); }

function openFactions() {
  sfx('click');
  const inf = influence();
  let h = '';
  const tot = totalIncome();
  h += `<div class="inf-big"><div><small>${tx('ui_passive')}</small><b class="cr">${fmt(tot)}</b><span>cr/s</span></div><div class="hint center">${tx('ui_income_split', { d: fmt(droneIncome()), f: fmt(freightIncome()), m: incomeMult().toFixed(2) })}</div></div>`;
  if ((S.freighters || []).length) {
    h += `<div class="sub">${tx('ui_freighters', { a: S.freighters.length, b: FREIGHT.max() })}</div>${fleetLine()}`;
    for (const f of S.freighters) h += `<div class="srow"><span>🚚 ${ITEMS[f.g].n}: ${LOC[f.from].n} → ${LOC[f.to].n}</span><b class="cr">+${fmt(freighterIncome(f))}/s</b></div>`;
  }
  h += `<div class="sub">${tx('ui_outposts')}</div>`;
  for (const l of FIELDS) {
    if (l.secret && !locOpen(l.id)) continue;
    const o = S.outposts[l.id];
    if (!locOpen(l.id)) { h += `<div class="srow dim"><span>🔒 ${l.field.n}</span><b>${tx('ui_locked')}</b></div>`; continue; }
    h += `<div class="srow"><span>${o ? '🤖' : '⬜'} ${l.field.n}</span>${o ? `<span class="dim">${tx('ui_op_row', { lv: o.lv, n: o.n })}</span><b class="cr">+${fmt(outpostIncome(l.id))}/s</b>` : `<b class="dim">${tx('ui_build_for', { c: fmt(buildCost(l.id)) })}</b>`}</div>`;
  }
  if (has(U.SATURN)) {
    h += `<div class="inf-big" style="margin-top:14px"><div><small>${tx('ui_influence')}</small><b>${inf}</b><span>/ 100</span></div><div class="meter big gold"><i style="width:${Math.min(100, inf)}%"></i></div><div class="rank">${rankName(inf)}</div></div>`;
    h += `<p class="hint">${tx('ui_infl_from', { peace: S.peace ? tx(S.peace > 1 ? 'ui_peaceN' : 'ui_peace1', { n: S.peace }) : '', fear: (S.nuked || []).length ? tx(S.nuked.length > 1 ? 'ui_fearN' : 'ui_fear1', { n: S.nuked.length }) : '' })}</p>`;
  }
  const wars = S.events.filter(e => e.war);
  if (wars.length) h += `<div class="sub">${tx('ui_wars')}</div>` + wars.map(e => warBarHTML(e)).join('');
  const allies = Object.keys(S.allies || {}).filter(f => S.allies[f]);
  if (allies.length) {
    h += `<div class="sub">${tx('ui_allies')}</div>`;
    for (const f of allies) h += `<div class="srow"><span><b style="color:${FACTIONS[f].c}">${FACTIONS[f].n}</b> <span class="ally-stars sm">${'★'.repeat(S.allies[f])}${'☆'.repeat(WAR.maxStars - S.allies[f])}</span></span><span class="dim">${(S.spoils[f] || []).map(k => `${SPOILS[k].icon} ${SPOILS[k].n}`).join(' · ')}</span><b class="cr">${tx('ui_ore_plus', { n: Math.round(S.allies[f] * WAR.starBonus * 100) })}</b></div>`;
  }
  if (has(U.TRADE)) {
    h += `<div class="sub">${tx('ui_fac_rep')}</div>`;
    for (const f in FACTIONS) {
      const r = S.rep[f];
      h += `<div class="fac"><span style="color:${FACTIONS[f].c}">${FACTIONS[f].n}</span><div class="repbar"><i style="left:50%;width:${Math.abs(r) / 2}%;${r < 0 ? `left:${50 - Math.abs(r) / 2}%;background:#ff4d6d` : `background:${FACTIONS[f].c}`}"></i><em></em></div><b>${Math.round(r)}</b></div>`;
    }
    const bad = e => e.war || e.relief || e.closed || e.storm || e.fuelPrice || (e.danger && e.danger.some(d => d.add > 0));
    h += `<div class="sub">${tx('ui_active_events')}</div>` + (S.events.length ? S.events.map(e => `<div class="ev">${e.icon} <b>${e.title}</b> <small>— ${e.text} (${e.end - S.day}d)</small>${bad(e) ? `<button class="btn small-btn" ${S.credits >= POWERS.end.cost() ? '' : 'disabled'} onclick="doPower('end','${e.uid}')">${tx('ui_end_it', { c: fmt(POWERS.end.cost()) })}</button>` : ''}</div>`).join('') : `<div class="empty small">${tx('ui_calm')}</div>`);
  }
  openSheet(tx('ui_empire_t'), h);
}

function openProjects() {
  sfx('click');
  let h = `<p class="hint">${tx('ui_proj_hint')}</p><div class="projs">`;
  for (const p of sysProjects()) {
    const done = built(p.id), open = projectOpen(p), can = open && !done && S.credits >= p.cost;
    const pct = Math.min(100, S.credits / p.cost * 100);
    h += `<div class="proj ${done ? 'done' : ''} ${open ? '' : 'locked'} ${can ? 'can' : ''}">
      <div class="pj-icon">${open || done ? p.icon : '🔒'}</div>
      <div class="pj-main"><b>${p.n}</b>${p.loc ? `<small>${LOC[p.loc].n}</small>` : ''}<p>${open ? p.d : has(p.stage) && p.req ? tx('ui_requires', { p: PROJ[p.req].n }) : tx('ui_unlocks_with', { u: UNLOCKS[p.stage].title })}</p>
        <div class="pj-fx">⚡ ${p.fx}${tx('ui_proj_infl', { n: p.infl })}${S.signal || S.galaxy ? ` · <span class="trib">${tx('ui_trib_jump', { n: projTribute(p) })}</span>` : ''}</div>
        ${done ? `<div class="pj-done">${tx('ui_built')}</div>` : open ? `<div class="pj-bar"><i style="width:${pct}%"></i></div><button class="btn ${can ? 'primary' : ''}" ${can ? '' : 'disabled'} onclick="doProject('${p.id}')">${can ? tx('ui_build') : tx('ui_need')} · ${fmt(p.cost)} cr</button>` : ''}
      </div></div>`;
  }
  h += '</div>';
  if (has(U.TRADE)) h += `<div class="sub">${tx('ui_sys_powers')}</div><p class="hint">${tx('ui_powers_hint')}</p>`;
  openSheet(tx('ui_megaprojects'), h);
}
function doProject(id) {
  if (!buildProject(id)) return;
  const p = PROJ[id];
  sfx('win');
  closeSheet(true);
  showModal({ icon: p.icon, title: tx('ui_proj_done', { p: p.n }), cls: 'unlock', html: `<div class="unl-tag">${tx('ui_megaproject')}</div><p>${p.d}</p><p><b class="cr">⚡ ${p.fx}</b></p><small>${tx('ui_plus_infl', { n: p.infl })}${S.signal || S.galaxy ? tx('ui_trib_leave', { n: projTribute(p) }) : ''}</small>`,
    buttons: [{ label: tx('ui_behold'), cls: 'primary', fn: () => { if (scene === MapScene && !MapScene.travel) { showMapUI(true); if (p.loc) { selectLoc(p.loc); MapScene.focus(p.loc); } else MapScene.zoomAll(); } } }] });
}
function doPower(kind, arg) {
  if (kind === 'nuke') {
    const l = LOC[arg];
    showModal({ icon: '💥', title: tx('ui_destroy_q', { l: l.n }), danger: true, html: tx('ui_destroy_body', { who: l.station || l.n }),
      buttons: [{ label: tx('ui_fire_cost', { c: fmt(POWERS.nuke.cost()) }), cls: 'danger', fn: () => { if (usePower('nuke', arg)) { closeSheet(true); setScene(MapScene); MapScene.focus(arg); selectLoc(arg); } } }, { label: tx('ui_stand_down'), fn: () => {} }] });
    return;
  }
  if (!usePower(kind, arg)) { toast(tx('ui_not_avail'), 'bad'); return; }
  sfx('win'); toast(tx('ui_power_done'), 'good');
  const sh = $('sheet');
  if (!sh.classList.contains('hidden')) { if (sh.classList.contains('dock')) renderDock(); else openFactions(); }
  else if (MapScene.sel) selectLoc(MapScene.sel);
  updateHUD();
}
function showChoice(ev) {
  sfx('event');
  showModal({ icon: ev.icon, title: ev.title, html: ev.html || `<p>${ev.text}</p>`, cls: 'unlock',
    buttons: ev.choices.map(c => ({ label: c.label, cls: c.cost ? 'primary' : '', disabled: c.cost > S.credits, fn: () => { if (c.cost > S.credits) return; S.credits -= c.cost; c.fn(); if (c.cost) addNews(ev.icon, tx('ui_you_chose', { c: c.label.split(' · ')[0] }), '#ffd24a'); save(); } })) });
}

function openNews() {
  sfx('click');
  openSheet(tx('ui_news_t'), S.news.map(n => `<div class="news"><i>${tx('ui_day', { d: n.day })}</i><span>${n.icon}</span><div>${n.html}</div></div>`).join(''));
}
function openMenu() {
  sfx('click');
  openSheet(tx('ui_menu_t'), `<div class="menu">
    <button class="btn primary big" onclick="closeSheet()">${tx('ui_resume')}</button>
    <button class="btn big" onclick="openHelp()">${tx('ui_how_to_play')}</button>
    <button class="btn big" id="gfxBtn" onclick="setQuality({ auto: 'high', high: 'low', low: 'auto' }[QUALITY.mode] || 'auto'); this.textContent = tx('ui_gfx_' + QUALITY.mode)">${tx('ui_gfx_' + (QUALITY.mode || 'auto'))}</button>
    <button class="btn big" id="musicBtn" onclick="audioInit(); MUSIC.setOn(!MUSIC.on); this.textContent = MUSIC.on ? tx('ui_music_on') : tx('ui_music_off')">${typeof MUSIC !== 'undefined' && MUSIC.on ? tx('ui_music_on') : tx('ui_music_off')}</button>
    <button class="btn big danger" onclick="confirmNew()">${tx('ui_new_game')}</button></div>`);
}
function confirmNew() {
  closeSheet(true);
  showModal({ icon: '⚠️', title: tx('ui_new_game_q'), html: tx('ui_progress_lost'), buttons: [
    { label: tx('ui_yes_restart'), cls: 'danger', fn: () => { pendingUnlocks = []; newGame(); save(); shownCredits = 0; setScene(MineScene, 'luna'); updateHUD(); updateTicker(); } },
    { label: tx('ui_cancel'), fn: () => {} }] });
}
function openHelp() {
  const T = typeof isTouch !== 'undefined' && isTouch;
  // tool keys on desktop, the on-screen button labels on touch devices
  const keys = T ? { drill: tx('ui_h_drill_t'), pull: tx('ui_b_pull'), boost: tx('ui_b_boost'), bomb: tx('ui_b_bomb'), scan: tx('ui_b_scan'), phase: tx('ui_b_phase') }
    : { drill: 'Q', pull: 'E', boost: 'R', bomb: 'F', scan: 'C', phase: 'X' };
  const sec = (h, p) => `<h4>${tx(h)}</h4><p>${p}</p>`;
  openSheet(tx('ui_help_t'), `<div class="help">
    ${sec('ui_h_mine', tx(T ? 'ui_h_mine_pt' : 'ui_h_mine_p'))}
    ${sec('ui_h_dock', tx('ui_h_dock_p'))}
    ${sec('ui_h_drones', tx('ui_h_drones_p'))}
    ${sec('ui_h_pirates', tx(T ? 'ui_h_pirates_pt' : 'ui_h_pirates_p'))}
    ${sec('ui_h_unlock', tx('ui_h_unlock_p'))}
    ${sec('ui_h_travel', tx('ui_h_travel_p'))}
    ${sec('ui_h_wars', tx('ui_h_wars_p'))}
    ${sec('ui_h_trade', tx('ui_h_trade_p'))}
    ${sec('ui_h_power', tx('ui_h_power_p'))}
    ${sec('ui_h_tools', tx('ui_h_tools_p', keys))}
    ${sec('ui_h_galaxy', tx('ui_h_galaxy_p'))}
    ${sec('ui_h_win', tx('ui_h_win_p'))}</div>`);
}
