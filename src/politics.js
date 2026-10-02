'use strict';
// ============ EVENTS, POLITICS, FREIGHTERS & THE NOVA CANNON ============

// ---------- player-facing text (English + Spanish) ----------
Object.assign(TXT, {
  pol_collect: { en: 'Collect', es: 'Cobrar' },
  pol_ok: { en: 'OK', es: 'OK' },
  // warlords
  pol_wl_news: { en: '<b>You destroyed the pirate warlord</b> at {field}: +{n} cr', es: '<b>Destruiste al caudillo pirata</b> en {field}: +{n} cr' },
  pol_wl_title: { en: 'Warlord destroyed!', es: '¡Caudillo pirata destruido!' },
  pol_wl_html: { en: '<p>The warlord\'s flagship breaks apart over {field}. The system is safer — and richer for you.</p><p><b class="cr big-num">+{n} cr</b></p>',
    es: '<p>La nave insignia del caudillo se despedaza sobre {field}. El sistema está más seguro, y tú, más rico.</p><p><b class="cr big-num">+{n} cr</b></p>' },
  // natural events
  pol_ev_plague_t: { en: 'Plague on {n}', es: 'Plaga en {n}' },
  pol_ev_plague: { en: 'An outbreak hits {st}. Medicine sells ×3 there — delivering it earns big reputation.', es: 'Un brote azota {st}. Las medicinas se venden ×3 ahí; entregarlas da mucha reputación.' },
  pol_ev_famine_t: { en: 'Famine on {n}', es: 'Hambruna en {n}' },
  pol_ev_famine: { en: '{st}\'s farms failed. Food sells ×2.6 there.', es: 'Fallaron las granjas de {st}. La comida se vende ×2.6 ahí.' },
  pol_ev_refugees_t: { en: 'Refugee crisis on {n}', es: 'Crisis de refugiados en {n}' },
  pol_ev_refugees: { en: 'Thousands flee to {st}. Food and medicine sell ×2 there.', es: 'Miles huyen a {st}. La comida y las medicinas se venden ×2 ahí.' },
  pol_ev_boom_t: { en: 'Construction boom on {n}', es: 'Auge de construcción en {n}' },
  pol_ev_boom: { en: '{st} is expanding. Metals and machinery sell ×1.8 there.', es: '{st} se expande. Metales y maquinaria se venden ×1.8 ahí.' },
  pol_ev_goldrush_t: { en: 'Gold rush on {n}', es: 'Fiebre del oro en {n}' },
  pol_ev_goldrush: { en: 'Speculators flood {st}. EVERY ore sells ×1.6 there.', es: 'Los especuladores invaden {st}. TODO el mineral se vende ×1.6 ahí.' },
  pol_ev_crash_t: { en: 'Market crash on {n}', es: 'Desplome del mercado en {n}' },
  pol_ev_crash: { en: 'A bank collapse at {st}. Ore prices there are halved — sell elsewhere.', es: 'Quiebra bancaria en {st}. Ahí el mineral vale la mitad: vende en otro lado.' },
  pol_ev_tech_t: { en: 'Tech breakthrough on {n}', es: 'Avance tecnológico en {n}' },
  pol_ev_tech: { en: 'New chip fabs on {n}: Electronics are half price there and sell ×1.4 everywhere else.', es: 'Nuevas fábricas de chips en {n}: la electrónica cuesta la mitad ahí y se vende ×1.4 en todos los demás lugares.' },
  pol_ev_rich_t: { en: 'Rich strike: {field}', es: 'Veta rica: {field}' },
  pol_ev_rich: { en: 'Probes found rich veins at {n}. More ore and more golden rocks!', es: 'Las sondas hallaron vetas ricas en {n}. ¡Más mineral y más rocas doradas!' },
  pol_ev_comets_t: { en: 'Comet swarm at {field}', es: 'Lluvia de cometas en {field}' },
  pol_ev_comets: { en: 'A comet storm seeds {n} with ice and Helium-3 — and every station pays ×1.5 for them.', es: 'Una tormenta de cometas llena {n} de hielo y Helio-3, y todas las estaciones los pagan ×1.5.' },
  pol_ev_pirates_t: { en: 'Pirate surge near {n}', es: 'Oleada pirata cerca de {n}' },
  pol_ev_pirates: { en: 'The {f} gathers fleets near {n}. Hunting them pays well.', es: 'El {f} reúne flotas cerca de {n}. Cazarlas paga bien.' },
  pol_ev_warlord_t: { en: 'Pirate warlord at {field}', es: 'Caudillo pirata en {field}' },
  pol_ev_warlord: { en: 'A notorious warlord raids {field}. He hunts anyone who mines there — destroy his flagship for a huge prize{bounty}.', es: 'Un temido caudillo pirata asalta {field}. Caza a quien mine ahí: destruye su nave insignia por un premio enorme{bounty}.' },
  pol_ev_warlord_b: { en: ', or take the bounty at {st}', es: ', o acepta la recompensa en {st}' },
  pol_ev_fuel_t: { en: 'Fuel crisis', es: 'Crisis de combustible' },
  pol_ev_fuel: { en: 'Sabotage at the refineries. Fuel costs double; Ice and Helium-3 sell ×1.4.', es: 'Sabotaje en las refinerías. El combustible cuesta el doble; el hielo y el Helio-3 se venden ×1.4.' },
  pol_ev_he3_t: { en: 'Helium-3 rush', es: 'Fiebre del Helio-3' },
  pol_ev_he3: { en: 'New fusion reactors everywhere. Helium-3 sells ×1.9.', es: 'Nuevos reactores de fusión por todas partes. El Helio-3 se vende ×1.9.' },
  pol_ev_strike_t: { en: 'Strike at {st}', es: 'Huelga en {st}' },
  pol_ev_strike: { en: 'Dockworkers on {n} walk out. Market closed; fuel and repairs only.', es: 'Los estibadores de {n} paran. Mercado cerrado; solo combustible y reparaciones.' },
  pol_ev_storm_t: { en: 'Solar storm', es: 'Tormenta solar' },
  pol_ev_storm: { en: 'A coronal mass ejection sweeps the inner system. Travel near the Sun damages your hull.', es: 'Una eyección de masa coronal barre el sistema interior. Viajar cerca del Sol daña tu casco.' },
  pol_ev_festival_t: { en: 'Festival on {n}', es: 'Festival en {n}' },
  pol_ev_festival: { en: '{st} celebrates. Luxuries sell ×1.9 and food ×1.4 there.', es: '{st} está de fiesta. Los lujos se venden ×1.9 y la comida ×1.4 ahí.' },
  // decision events
  pol_ev_election_t: { en: 'Election on {n}', es: 'Elecciones en {n}' },
  pol_ev_election: { en: 'Two parties fight for {st}. Your money could decide it.', es: 'Dos partidos se disputan {st}. Tu dinero podría decidirlo.' },
  pol_ch_industry: { en: 'Back the Industrialists · {c}', es: 'Apoyar a los Industriales · {c}' },
  pol_ev_industry_t: { en: 'Industrialists rule {n}', es: 'Los Industriales gobiernan {n}' },
  pol_ev_industry: { en: 'Machinery and weapons half price there; metals sell ×1.3.', es: 'Maquinaria y armas a mitad de precio ahí; los metales se venden ×1.3.' },
  pol_ch_greens: { en: 'Back the Greens · {c}', es: 'Apoyar a los Verdes · {c}' },
  pol_ev_greens_t: { en: 'Greens rule {n}', es: 'Los Verdes gobiernan {n}' },
  pol_ev_greens: { en: 'Ice, food and Helium-3 sell ×1.8 there.', es: 'Hielo, comida y Helio-3 se venden ×1.8 ahí.' },
  pol_ch_stayout: { en: 'Stay out of it', es: 'No meterte' },
  pol_ev_indep_t: { en: '{n} wants independence', es: '{n} quiere independizarse' },
  pol_ev_indep: { en: 'Separatists on {n} are rising against the {f}\'s influence.', es: 'Los separatistas de {n} se alzan contra la influencia de {f}.' },
  pol_ch_separatists: { en: 'Fund the separatists · {c}', es: 'Financiar a los separatistas · {c}' },
  pol_ev_free_t: { en: 'Free {n}', es: '{n} libre' },
  pol_ev_free: { en: 'The new government rewards its friends: ore sells ×1.5 there.', es: 'El nuevo gobierno premia a sus amigos: el mineral se vende ×1.5 ahí.' },
  pol_ch_government: { en: 'Fund the government · {c}', es: 'Financiar al gobierno · {c}' },
  pol_ev_order_t: { en: 'Order on {n}', es: 'Orden en {n}' },
  pol_ev_order: { en: 'Patrols everywhere: no pirates there for 40 days.', es: 'Patrullas por todas partes: sin piratas ahí durante 40 días.' },
  pol_ch_ignore: { en: 'Ignore it', es: 'Ignorarlo' },
  pol_ev_buyout_t: { en: 'Rival miner bankrupt at {field}', es: 'Minero rival en quiebra en {field}' },
  pol_ev_buyout: { en: 'Their equipment is for sale at half price: it would upgrade your outpost there one level (×2 output).', es: 'Venden su equipo a mitad de precio: subiría un nivel tu puesto minero de ahí (producción ×2).' },
  pol_ch_buy: { en: 'Buy it · {c}', es: 'Comprarlo · {c}' },
  pol_news_buyout: { en: 'You bought out a rival at {field}', es: 'Compraste a un rival en {field}' },
  pol_ch_pass: { en: 'Pass', es: 'Paso' },
  pol_ev_loan_t: { en: '{st} asks for a bailout', es: '{st} pide un rescate' },
  pol_ev_loan: { en: 'They need {n} cr now and promise to repay ×1.6 in 20 days. Colonies usually keep their word…', es: 'Necesitan {n} cr ya y prometen devolver ×1.6 en 20 días. Las colonias suelen cumplir su palabra…' },
  pol_ch_lend: { en: 'Lend {n}', es: 'Prestar {n}' },
  pol_ch_refuse: { en: 'Refuse', es: 'Negarte' },
  // wars
  pol_war_t: { en: 'War: {a} vs {b}', es: 'Guerra: {a} vs {b}' },
  pol_war: { en: 'Weapons sell ×2.3, medicine ×1.5 and fuel costs more in their markets. Routes get dangerous. Back a side and sell your ore there to push the front.',
    es: 'Las armas se venden ×2.3, las medicinas ×1.5 y el combustible sube en sus mercados. Las rutas se vuelven peligrosas. Apoya a un bando y véndele tu mineral para empujar el frente.' },
  pol_spoil_rights: { en: 'Mining rights', es: 'Derechos mineros' },
  pol_spoil_rights_d: { en: '+10% ore from every rock, everywhere', es: '+10% de mineral de cada roca, en todas partes' },
  pol_spoil_drones: { en: 'Drone contract', es: 'Contrato de drones' },
  pol_spoil_drones_d: { en: 'Drones cost 12% less at every outpost', es: 'Los drones cuestan 12% menos en cada puesto minero' },
  pol_spoil_fuel: { en: 'Fuel treaty', es: 'Tratado de combustible' },
  pol_spoil_fuel_d: { en: 'Fuel is 15% cheaper at every station', es: 'El combustible es 15% más barato en cada estación' },
  pol_front_toast: { en: 'Front +{n}% for {f} ({why})', es: 'Frente +{n}% para {f} ({why})' },
  pol_why_delivered: { en: '{item} delivered', es: 'entrega de {item}' },
  pol_why_offensive: { en: 'offensive', es: 'ofensiva' },
  pol_bar_you: { en: '<small>You back <b style="color:{c}">{f}</b> · your push +{n}%</small>', es: '<small>Apoyas a <b style="color:{c}">{f}</b> · tu empuje +{n}%</small>' },
  pol_bar_join: { en: '<small>Back a side at one of their stations to take part</small>', es: '<small>Apoya a un bando en una de sus estaciones para participar</small>' },
  pol_bar_final: { en: 'final', es: 'final' },
  pol_bar_left: { en: '{n}d left', es: 'quedan {n} d' },
  pol_vs: { en: ' vs ', es: ' vs ' },
  pol_and: { en: ' and ', es: ' y ' },
  pol_won_news: { en: '<b>{w}</b> won the war ({names})', es: '<b>{w}</b> ganó la guerra ({names})' },
  pol_truce_news: { en: 'Stalemate: {names} sign a truce', es: 'Empate: {names} firman una tregua' },
  pol_ally: { en: '<p><b>{f}</b> is now your ally: <b>ore sells +{n}%</b> at all their stations, forever.</p>', es: '<p><b>{f}</b> ahora es tu aliado: <b>el mineral se vende +{n}%</b> en todas sus estaciones, para siempre.</p>' },
  pol_wins_t: { en: '{f} wins!', es: '¡{f} gana!' },
  pol_choose_spoils: { en: '<p>Choose your spoils of war (permanent):</p>', es: '<p>Elige tu botín de guerra (permanente):</p>' },
  pol_spoils_news: { en: 'Spoils of war: {s} from {f}', es: 'Botín de guerra: {s} de {f}' },
  pol_war_bonus: { en: '<p>They already gave you everything they have — a war bonus of <b class="cr">{n} cr</b> instead.</p>', es: '<p>Ya te dieron todo lo que tienen: en su lugar, un bono de guerra de <b class="cr">{n} cr</b>.</p>' },
  pol_wins_plain_t: { en: '{f} wins', es: '{f} gana' },
  pol_barely: { en: '<p>They won, but you barely helped (push +{n}%, needed +{m}%). No alliance this time.</p>', es: '<p>Ganaron, pero apenas ayudaste (empuje +{n}%, se necesitaba +{m}%). Esta vez no hay alianza.</p>' },
  pol_lost_t: { en: '{f} lost the war', es: '{f} perdió la guerra' },
  pol_stalemate_t: { en: 'The war ended in a stalemate', es: 'La guerra terminó en empate' },
  pol_beaten: { en: 'Your side was beaten.', es: 'Tu bando fue derrotado.' },
  pol_nobreak: { en: 'Neither side broke through.', es: 'Ningún bando logró romper el frente.' },
  pol_nospoils: { en: ' No spoils this time — but your ore buys you another chance in the next war.', es: ' Esta vez no hay botín, pero tu mineral te da otra oportunidad en la próxima guerra.' },
  // loans
  pol_default_news: { en: '{n} defaulted on your loan.', es: '{n} no pagó tu préstamo.' },
  pol_default_toast: { en: '{n} defaulted on your loan', es: '{n} no pagó tu préstamo' },
  pol_repaid_news: { en: '{st} repaid your loan: +{a} cr', es: '{st} pagó tu préstamo: +{a} cr' },
  pol_repaid_toast: { en: 'Loan repaid: +{a} cr', es: 'Préstamo pagado: +{a} cr' },
  // powers
  pol_pw_works: { en: 'Fund public works', es: 'Financiar obras públicas' },
  pol_pw_works_d: { en: '+12 reputation with this planet', es: '+12 de reputación con este planeta' },
  pol_pw_boom: { en: 'Fund a boom', es: 'Financiar un auge' },
  pol_pw_boom_d: { en: 'Every ore sells ×1.9 here for 20 days', es: 'Todo el mineral se vende ×1.9 aquí por 20 días' },
  pol_pw_purge: { en: 'Hire mercenaries', es: 'Contratar mercenarios' },
  pol_pw_purge_d: { en: 'No pirates here for 30 days', es: 'Sin piratas aquí por 30 días' },
  pol_pw_end: { en: 'End this crisis', es: 'Terminar esta crisis' },
  pol_pw_incite: { en: 'Incite a war', es: 'Provocar una guerra' },
  pol_pw_incite_d: { en: 'Start a war against another faction. Wars pay: weapons ×2.3. Risky if discovered.', es: 'Inicia una guerra contra otra facción. Las guerras pagan: armas ×2.3. Arriesgado si te descubren.' },
  pol_pw_back: { en: 'Back this side', es: 'Apoyar a este bando' },
  pol_pw_back_d: { en: 'Their stations pay +30% for metals during the war and every sale pushes the front. Win → a permanent ally.', es: 'Sus estaciones pagan +30% por metales durante la guerra y cada venta empuja el frente. Si ganan → un aliado permanente.' },
  pol_pw_offensive: { en: 'Fund an offensive', es: 'Financiar una ofensiva' },
  pol_pw_offensive_d: { en: 'Push the front +20% right now', es: 'Empuja el frente +20% ahora mismo' },
  pol_pw_peace: { en: 'Broker peace', es: 'Negociar la paz' },
  pol_pw_peace_d: { en: 'End the war: +20 rep with both sides, +3 influence.', es: 'Termina la guerra: +20 de reputación con ambos bandos, +3 de influencia.' },
  pol_pw_nuke: { en: 'Fire the Nova Cannon', es: 'Disparar el Cañón Nova' },
  pol_pw_nuke_d: { en: 'Destroy this planet.', es: 'Destruye este planeta.' },
  pol_ready_1: { en: 'ready in 1 day', es: 'lista en 1 día' },
  pol_ready_n: { en: 'ready in {n} days', es: 'lista en {n} días' },
  pol_why_boom: { en: 'a boom is already running', es: 'ya hay un auge en curso' },
  pol_why_secured: { en: 'already secured', es: 'ya está asegurado' },
  pol_incite_vs: { en: 'Incite war vs {f}', es: 'Provocar guerra vs {f}' },
  pol_why_war: { en: 'another war is running', es: 'ya hay otra guerra en curso' },
  pol_why_backed: { en: 'you already back a side in another war', es: 'ya apoyas a un bando en otra guerra' },
  pol_end_news: { en: 'Your money ended it: <b>{t}</b>. The system owes you one.', es: 'Tu dinero le puso fin: <b>{t}</b>. El sistema te debe una.' },
  pol_leak_news: { en: 'Leaked: <b>you</b> started the war between {a} and {b}!', es: '¡Filtración: <b>tú</b> iniciaste la guerra entre {a} y {b}!' },
  pol_leak_toast: { en: 'Your plot was discovered! −30 reputation with both sides', es: '¡Descubrieron tu complot! −30 de reputación con ambos bandos' },
  pol_war_news: { en: 'War breaks out between {a} and {b}. Nobody suspects you.', es: 'Estalla la guerra entre {a} y {b}. Nadie sospecha de ti.' },
  pol_works_news: { en: 'You funded public works on {n}', es: 'Financiaste obras públicas en {n}' },
  pol_myboom_t: { en: 'Your boom on {n}', es: 'Tu auge en {n}' },
  pol_myboom: { en: 'You funded a building frenzy at {st}. Every ore sells ×1.9 there.', es: 'Financiaste una fiebre constructora en {st}. Todo el mineral se vende ×1.9 ahí.' },
  pol_boom_news: { en: 'You funded a construction boom on {n}', es: 'Financiaste un auge de construcción en {n}' },
  pol_purge_t: { en: '{n} secured', es: '{n} asegurado' },
  pol_purge: { en: 'Your mercenaries hunt every pirate near {n}. No ambushes there for 30 days.', es: 'Tus mercenarios cazan a todo pirata cerca de {n}. Sin emboscadas ahí por 30 días.' },
  pol_purge_news: { en: 'Mercenaries cleared the pirates near {n}', es: 'Los mercenarios barrieron a los piratas cerca de {n}' },
  pol_back_news: { en: 'You back {f} in the war', es: 'Apoyas a {f} en la guerra' },
  pol_offensive_news: { en: 'You funded an offensive for {f}', es: 'Financiaste una ofensiva para {f}' },
  pol_peace_news: { en: 'You brokered peace between {names}. The system celebrates your name.', es: 'Negociaste la paz entre {names}. El sistema celebra tu nombre.' },
  // the Nova Cannon
  pol_wreck_station: { en: '{n} Salvage Depot', es: 'Depósito de chatarra de {n}' },
  pol_wreck_field: { en: '{n} Debris', es: 'Restos de {n}' },
  pol_wreck_desc: { en: 'What\'s left of {n}. A glowing debris field of shattered crust — the richest mining in the system.', es: 'Lo que queda de {n}. Un campo brillante de corteza destrozada: la minería más rica del sistema.' },
  pol_nuked_news: { en: '<b>{n} has been destroyed.</b> The whole system trembles before you.', es: '<b>{n} fue destruido.</b> Todo el sistema tiembla ante ti.' },
  // freighters
  pol_fleet_full: { en: 'Fleet full {n}/{max}', es: 'Flota llena {n}/{max}' },
  pol_fleet_full_l: { en: 'Your fleet is full ({n}/{max}).', es: 'Tu flota está llena ({n}/{max}).' },
  pol_fleet_more: { en: ' <b>+{k} slots</b> unlock with <b>{t}</b>.', es: ' Se desbloquean <b>+{k} espacios</b> con <b>{t}</b>.' },
  pol_fleet_max: { en: ' That is the maximum fleet size.', es: ' Es el tamaño máximo de flota.' },
  pol_route_full: { en: 'Route full {p}/{p}', es: 'Ruta llena {p}/{p}' },
  pol_route_full_l: { en: 'This route already has {p} freighters — more would flood the market. Try another good or destination.', es: 'Esta ruta ya tiene {p} cargueros: más saturarían el mercado. Prueba otro producto u otro destino.' },
  pol_need_cr: { en: 'Need {c} cr', es: 'Necesitas {c} cr' },
  pol_next_freighter: { en: 'The next freighter costs <b>{c} cr</b> (each one costs 35% more than the last).', es: 'El próximo carguero cuesta <b>{c} cr</b> (cada uno cuesta 35% más que el anterior).' },
  pol_hired_news: { en: 'Freighter hired: {item} {a} → {b}', es: 'Carguero contratado: {item} {a} → {b}' },
});

// ---------- helpers ----------
const WAR_PAIRS = [['tierra', 'marte'], ['marte', 'cinturon'], ['tierra', 'exterior'], ['cinturon', 'exterior'], ['marte', 'exterior']];
const openMarkets = () => NODES.filter(x => x.market && !x.depot && locOpen(x.id));
const cityOpen = id => LOC[id].market && !LOC[id].depot && locOpen(id);
const factionAlive = f => FACTIONS[f].locs.some(id => !LOC[id].nuked);
const kindActive = (kind, loc) => S.events.some(e => e.kind === kind && (!loc || (e.locs || []).includes(loc)));
// costs scale with how rich you've become, so powers stay meaningful all game
const pcost = (f, min) => Math.round(Math.max(min, S.stats.earned * f));
function addEvent(ev) {
  if (ev.mine && ev.kind) S.events = S.events.filter(e => !(e.mine && e.kind === ev.kind && (e.locs || []).some(l => (ev.locs || []).includes(l))));
  ev.start = S.day; ev.end = S.day + ev.dur; ev.uid = uid();
  // a shortage or boom creates fresh appetite for those goods
  for (const p of ev.price || []) if (p.m > 1 && p.loc !== '*' && !ITEMS[p.item].ore && LOC[p.loc] && LOC[p.loc].market) {
    S.demand[p.loc] = S.demand[p.loc] || {}; S.demand[p.loc][p.item] = Math.max(demandOf(p.loc, p.item), 0.85);
  }
  S.events.push(ev);
  return ev;
}

// ---------- pirate warlords ----------
// the bounty is posted at the field's own city, or the nearest open city if the field only has a depot
function warlordCity(id) {
  const l = LOC[id];
  if (l.market && !l.depot && l.faction !== 'piratas') return l;
  return NODES.filter(x => x.market && !x.depot && x.faction && x.faction !== 'piratas' && locOpen(x.id) && !x.nuked)
    .sort((a, b) => locDist(id, a.id, S.day) - locDist(id, b.id, S.day))[0] || null;
}
const warlordAt = id => S.events.find(e => e.warlord === id);
const warlordPrize = () => Math.round(4 * haulRef());
function warlordKilled(id) {
  const e = warlordAt(id); if (!e) return;
  S.events = S.events.filter(x => x !== e);
  const prize = warlordPrize();
  earn(prize);
  repChange('piratas', -10, true);
  const city = warlordCity(id); if (city && city.faction) repChange(city.faction, 20, true);
  for (const c of [...S.active]) if (c.type === 'bounty' && c.at === id) completeContract(c);
  for (const k in S.contracts) S.contracts[k] = S.contracts[k].filter(c => !(c.type === 'bounty' && c.at === id));
  addNews('🏆', tx('pol_wl_news', { field: LOC[id].field.n, n: fmt(prize) }), '#ffd24a');
  if (typeof pendingChoices !== 'undefined') pendingChoices.push({ icon: '🏆', title: tx('pol_wl_title'), html: tx('pol_wl_html', { field: LOC[id].field.n, n: fmt(prize) }), choices: [{ label: tx('pol_collect'), cost: 0, fn: () => {} }] });
  save();
}

// ---------- natural system events ----------
const EVENT_GEN = [
  { kind: 'war', w: 1.1, make() {
      if (S.events.some(e => e.war)) return null;
      const pairs = WAR_PAIRS.filter(p => p.every(f => factionAlive(f) && FACTIONS[f].locs.some(locOpen)));
      if (!pairs.length) return null;
      return makeWar(...pick(pairs), randi(28, 50));
  } },
  { kind: 'plague', w: 1, make() {
      const c = openMarkets().filter(x => !x.black && x.market.meds > 1);
      if (!c.length) return null; const l = pick(c);
      return { icon: '☣️', title: tx('pol_ev_plague_t', { n: l.n }), text: tx('pol_ev_plague', { st: l.station }),
        dur: randi(18, 32), locs: [l.id], price: [{ loc: l.id, item: 'meds', m: 3 }, { loc: l.id, item: 'food', m: 1.3 }], relief: { loc: l.id, item: 'meds' } };
  } },
  { kind: 'famine', w: 1, make() {
      const c = openMarkets().filter(x => x.market.food > 1);
      if (!c.length) return null; const l = pick(c);
      return { icon: '🌾', title: tx('pol_ev_famine_t', { n: l.n }), text: tx('pol_ev_famine', { st: l.station }),
        dur: randi(15, 28), locs: [l.id], price: [{ loc: l.id, item: 'food', m: 2.6 }], relief: { loc: l.id, item: 'food' } };
  } },
  { kind: 'refugees', w: 0.7, make() {
      const c = openMarkets().filter(x => x.market.food > 1 && x.market.meds > 1);
      if (!c.length) return null; const l = pick(c);
      return { icon: '🛖', title: tx('pol_ev_refugees_t', { n: l.n }), text: tx('pol_ev_refugees', { st: l.station }),
        dur: randi(15, 25), locs: [l.id], price: [{ loc: l.id, item: 'food', m: 2 }, { loc: l.id, item: 'meds', m: 2 }], relief: { loc: l.id, item: 'food' } };
  } },
  { kind: 'boom', w: 1.1, make() {
      const l = pick(openMarkets());
      return l && { icon: '🏗️', title: tx('pol_ev_boom_t', { n: l.n }), text: tx('pol_ev_boom', { st: l.station }),
        dur: randi(20, 35), locs: [l.id], price: ['iron', 'nickel', 'titanium', 'platinum', 'machinery'].map(i => ({ loc: l.id, item: i, m: 1.8 })) };
  } },
  { kind: 'goldrush', w: 0.6, make() {
      const l = pick(openMarkets());
      return l && { icon: '🤑', title: tx('pol_ev_goldrush_t', { n: l.n }), text: tx('pol_ev_goldrush', { st: l.station }),
        dur: randi(10, 16), locs: [l.id], price: ORES.map(i => ({ loc: l.id, item: i, m: 1.6 })) };
  } },
  { kind: 'crash', w: 0.6, make() {
      const l = pick(openMarkets());
      return l && { icon: '📉', title: tx('pol_ev_crash_t', { n: l.n }), text: tx('pol_ev_crash', { st: l.station }),
        dur: randi(8, 14), locs: [l.id], price: ORES.map(i => ({ loc: l.id, item: i, m: 0.5 })) };
  } },
  { kind: 'techboom', w: 0.7, make() {
      const prod = openMarkets().filter(x => x.market.tech <= 1);
      if (!prod.length) return null; const l = pick(prod);
      return { icon: '💡', title: tx('pol_ev_tech_t', { n: l.n }), text: tx('pol_ev_tech', { n: l.n }),
        dur: randi(12, 20), locs: [l.id], price: [{ loc: l.id, item: 'tech', m: 0.5 }, { loc: '*', item: 'tech', m: 1.4 }] };
  } },
  { kind: 'rich', w: 1, make() {
      const l = pick(NODES.filter(x => x.field && locOpen(x.id)));
      return l && { icon: '💎', title: tx('pol_ev_rich_t', { field: l.field.n }), text: tx('pol_ev_rich', { n: l.n }),
        dur: randi(15, 25), locs: [l.id], rich: l.id };
  } },
  { kind: 'comets', w: 0.6, make() {
      const l = pick(NODES.filter(x => x.field && locOpen(x.id)));
      return l && { icon: '☄️', title: tx('pol_ev_comets_t', { field: l.field.n }), text: tx('pol_ev_comets', { n: l.n }),
        dur: randi(12, 20), locs: [l.id], rich: l.id, price: [{ loc: '*', item: 'ice', m: 1.5 }, { loc: '*', item: 'he3', m: 1.5 }] };
  } },
  { kind: 'pirates', w: 0.9, make() {
      if (!has(U.BELT)) return null;
      const l = pick(NODES.filter(x => x.id !== 'pluton' && locOpen(x.id)));
      return l && { icon: '☠️', title: tx('pol_ev_pirates_t', { n: l.n }), text: tx('pol_ev_pirates', { n: l.n, f: FACTIONS.piratas.n }),
        dur: randi(15, 30), locs: [l.id], danger: [{ loc: l.id, add: 0.35 }] };
  } },
  { kind: 'warlord', w: 0.4, make() {
      if (!has(U.BELT)) return null;
      const l = pick(NODES.filter(x => x.field && locOpen(x.id) && x.field.z >= 2));
      if (!l) return null;
      const city = warlordCity(l.id);
      const ev = { kind: 'warlord', icon: '🏴‍☠️', title: tx('pol_ev_warlord_t', { field: l.field.n }), warlord: l.id, uid: uid(),
        text: tx('pol_ev_warlord', { field: l.field.n, bounty: city ? tx('pol_ev_warlord_b', { st: city.station }) : '' }),
        dur: randi(20, 30), locs: [l.id], danger: [{ loc: l.id, add: 0.5 }] };
      if (city) {
        const c = S.contracts[city.id] || (S.contracts[city.id] = []);
        c.unshift({ type: 'bounty', id: uid(), from: city.id, at: l.id, kills: 3, reward: Math.round(Math.max(3 * 1500 * Z_LOOT[l.field.z], 1.5 * haulRef())), rep: 25, days: ev.dur, faction: city.faction, urgent: 1 });
      }
      return ev;
  } },
  { kind: 'fuel', w: 0.6, make() {
      return { icon: '⛽', title: tx('pol_ev_fuel_t'), text: tx('pol_ev_fuel'),
        dur: randi(12, 22), locs: [], fuelPrice: 2, price: [{ loc: '*', item: 'ice', m: 1.4 }, { loc: '*', item: 'he3', m: 1.4 }] };
  } },
  { kind: 'he3rush', w: 0.6, make() {
      return { icon: '⚛️', title: tx('pol_ev_he3_t'), text: tx('pol_ev_he3'),
        dur: randi(18, 30), locs: ['tierra', 'marte'].filter(locOpen), price: [{ loc: '*', item: 'he3', m: 1.9 }] };
  } },
  { kind: 'strike', w: 0.5, make() {
      const l = pick(openMarkets().filter(x => x.id !== 'luna' && x.id !== 'tierra'));
      return l && { icon: '✊', title: tx('pol_ev_strike_t', { st: l.station }), text: tx('pol_ev_strike', { n: l.n }),
        dur: randi(5, 10), locs: [l.id], closed: [l.id] };
  } },
  { kind: 'storm', w: 0.5, make() {
      return { icon: '☀️', title: tx('pol_ev_storm_t'), text: tx('pol_ev_storm'),
        dur: randi(6, 12), locs: ['mercurio', 'venus', 'tierra', 'luna'].filter(locOpen), storm: ['mercurio', 'venus', 'tierra', 'luna'] };
  } },
  { kind: 'festival', w: 0.6, make() {
      const l = pick(openMarkets());
      return l && { icon: '🎉', title: tx('pol_ev_festival_t', { n: l.n }), text: tx('pol_ev_festival', { st: l.station }),
        dur: randi(8, 14), locs: [l.id], price: [{ loc: l.id, item: 'luxury', m: 1.9 }, { loc: l.id, item: 'food', m: 1.4 }] };
  } },
  // ----- events that ask YOU to decide -----
  { kind: 'election', w: 0.7, choice: 1, make() {
      const c = openMarkets().filter(x => x.faction && x.faction !== 'piratas' && !kindActive('policy', x.id));
      if (!c.length) return null; const l = pick(c); const cost = pcost(0.004, 150000);
      return { icon: '🗳️', title: tx('pol_ev_election_t', { n: l.n }), text: tx('pol_ev_election', { st: l.station }), choices: [
        { label: tx('pol_ch_industry', { c: fmt(cost) }), cost, fn: () => { addEvent({ kind: 'policy', mine: 1, icon: '🏭', title: tx('pol_ev_industry_t', { n: l.n }), text: tx('pol_ev_industry'), dur: 30, locs: [l.id],
            price: [{ loc: l.id, item: 'machinery', m: 0.5 }, { loc: l.id, item: 'arms', m: 0.5 }, ...['iron', 'nickel', 'titanium', 'platinum'].map(i => ({ loc: l.id, item: i, m: 1.3 }))] }); repChange(l.faction, 10); } },
        { label: tx('pol_ch_greens', { c: fmt(cost) }), cost, fn: () => { addEvent({ kind: 'policy', mine: 1, icon: '🌱', title: tx('pol_ev_greens_t', { n: l.n }), text: tx('pol_ev_greens'), dur: 30, locs: [l.id],
            price: [{ loc: l.id, item: 'ice', m: 1.8 }, { loc: l.id, item: 'food', m: 1.8 }, { loc: l.id, item: 'he3', m: 1.8 }] }); repChange(l.faction, 10); } },
        { label: tx('pol_ch_stayout'), cost: 0, fn: () => {} },
      ] };
  } },
  { kind: 'independence', w: 0.5, choice: 1, make() {
      const c = ['ceres', 'europa', 'titan'].filter(id => cityOpen(id) && !kindActive('free', id) && !kindActive('order', id));
      if (!c.length) return null; const l = LOC[pick(c)]; const cost = pcost(0.006, 250000);
      return { icon: '🏴', title: tx('pol_ev_indep_t', { n: l.n }), text: tx('pol_ev_indep', { n: l.n, f: FACTIONS.tierra.n }), choices: [
        { label: tx('pol_ch_separatists', { c: fmt(cost) }), cost, fn: () => { repChange(l.faction, 20); repChange('tierra', -15); addEvent({ kind: 'free', mine: 1, icon: '🎆', title: tx('pol_ev_free_t', { n: l.n }), text: tx('pol_ev_free'), dur: 40, locs: [l.id], price: ORES.map(i => ({ loc: l.id, item: i, m: 1.5 })) }); } },
        { label: tx('pol_ch_government', { c: fmt(cost) }), cost, fn: () => { repChange('tierra', 20); repChange(l.faction, -10); addEvent({ kind: 'order', mine: 1, icon: '🛡️', title: tx('pol_ev_order_t', { n: l.n }), text: tx('pol_ev_order'), dur: 40, locs: [l.id], danger: [{ loc: l.id, add: -1 }] }); } },
        { label: tx('pol_ch_ignore'), cost: 0, fn: () => {} },
      ] };
  } },
  { kind: 'buyout', w: 0.5, choice: 1, make() {
      const ids = Object.keys(S.outposts).filter(id => outpostLvCost(id) != null);
      if (!ids.length) return null; const id = pick(ids); const cost = Math.round(outpostLvCost(id) * 0.5);
      return { icon: '💼', title: tx('pol_ev_buyout_t', { field: LOC[id].field.n }), text: tx('pol_ev_buyout'), choices: [
        { label: tx('pol_ch_buy', { c: fmt(cost) }), cost, fn: () => { const o = S.outposts[id]; if (!o || o.lv >= OUTPOST.maxLv) { S.credits += cost; return; } o.lv++; addNews('💼', tx('pol_news_buyout', { field: LOC[id].field.n }), '#6dffb0'); } },
        { label: tx('pol_ch_pass'), cost: 0, fn: () => {} },
      ] };
  } },
  { kind: 'loan', w: 0.5, choice: 1, make() {
      const c = openMarkets().filter(x => x.faction && x.faction !== 'piratas');
      if (!c.length) return null; const l = pick(c); const amt = pcost(0.01, 300000);
      return { icon: '🏦', title: tx('pol_ev_loan_t', { st: l.station }), text: tx('pol_ev_loan', { n: fmt(amt) }), choices: [
        { label: tx('pol_ch_lend', { n: fmt(amt) }), cost: amt, fn: () => { (S.loans = S.loans || []).push({ loc: l.id, due: S.day + 20, amt: Math.round(amt * 1.6) }); repChange(l.faction, 8); } },
        { label: tx('pol_ch_refuse'), cost: 0, fn: () => repChange(l.faction, -3) },
      ] };
  } },
];
let pendingChoices = [];
function spawnEvent() {
  for (let tries = 0; tries < 6; tries++) {
    const pool = EVENT_GEN.filter(g => !g.choice || has(U.TRADE));
    const total = pool.reduce((a, e) => a + e.w, 0);
    let r = Math.random() * total, gen = pool[0];
    for (const e of pool) { r -= e.w; if (r <= 0) { gen = e; break; } }
    const ev = gen.make();
    if (!ev) continue;
    ev.kind = gen.kind;
    if (ev.choices && OFFLINE) continue;   // decisions only come up while you're playing
    if (ev.choices) { pendingChoices.push(ev); addNews(ev.icon, `<b>${ev.title}</b> — ${ev.text}`, '#ffc857'); return; }
    if ((ev.locs || []).some(id => kindActive(ev.kind, id)) || (!ev.locs.length && kindActive(ev.kind))) continue;
    addEvent(ev);
    addNews(ev.icon, `<b>${ev.title}</b> — ${ev.text}`, '#ffc857');
    showEventBanner(ev);
    if (ev.relief) {
      const l = LOC[ev.relief.loc];
      const qty = Math.max(6, Math.round(ship.cargoMax * rand(0.3, 0.6)));
      (S.contracts[l.id] = S.contracts[l.id] || []).unshift({ type: 'deliver', id: uid(), from: l.id, to: l.id, item: ev.relief.item, qty,
        reward: Math.round(qty * itemBase(ev.relief.item) * 3.2 / 10) * 10, rep: 15, days: ev.dur, faction: l.faction, urgent: 1 });
    }
    return;
  }
}
function makeWar(a, b, dur) {
  const locs = [...FACTIONS[a].locs, ...FACTIONS[b].locs].filter(id => locOpen(id) && !LOC[id].nuked);
  return { kind: 'war', icon: '⚔️', title: tx('pol_war_t', { a: FACTIONS[a].n, b: FACTIONS[b].n }),
    text: tx('pol_war'),
    dur, war: [a, b], locs, front: 0, push: 0,
    price: locs.flatMap(l => [{ loc: l, item: 'arms', m: 2.3 }, { loc: l, item: 'meds', m: 1.5 }, { loc: l, item: 'machinery', m: 1.3 }]),
    danger: locs.map(l => ({ loc: l, add: 0.22 })), fuelPrice: 1.3 };
}
function onEventEnd(e) {
  if (e.war && !e.resolved) {
    const f = e.front || 0;
    endWar(e, Math.abs(f) >= WAR.decisive ? (f > 0 ? e.war[0] : e.war[1]) : null);
  }
}

// ---------- the war front ----------
// e.front runs from −100 (e.war[1] wins) to +100 (e.war[0] wins). It drifts each
// day with each side's strength; you push it by selling ore/supplies to the side
// you back, funding offensives and beating raiders in their space.
const WAR = { decisive: 25, minPush: 15, maxStars: 3, starBonus: 0.15 };
const SPOILS = {
  rights: { icon: '⛏', n: tx('pol_spoil_rights'), d: tx('pol_spoil_rights_d') },
  drones: { icon: '🤖', n: tx('pol_spoil_drones'), d: tx('pol_spoil_drones_d') },
  fuel:   { icon: '⛽', n: tx('pol_spoil_fuel'), d: tx('pol_spoil_fuel_d') },
};
const warSign = (e, f) => e.war[0] === f ? 1 : -1;
const backedWar = () => S.events.find(e => e.war && e.backed && !e.resolved);
function facStrength(f) { return FACTIONS[f].locs.filter(id => !LOC[id].nuked).length; }
// value of "one good haul" right now, so pushes stay meaningful all game
const haulRef = () => 40 * Math.pow(Math.max(1000, S.stats.earned), 0.72);
function warPush(e, amt, why) {
  if (!e || !e.backed || e.resolved || amt <= 0) return 0;
  amt = Math.min(amt, 100 - warSign(e, e.backed) * (e.front || 0)); if (amt <= 0) return 0;
  e.front = clamp((e.front || 0) + warSign(e, e.backed) * amt, -100, 100);
  e.push = (e.push || 0) + amt;
  if (why) toast(tx('pol_front_toast', { n: Math.round(amt), f: FACTIONS[e.backed].n, why }), 'good');
  if (Math.abs(e.front) >= 100) endWar(e, e.backed);
  if (typeof updateWarBar === 'function') updateWarBar();
  return amt;
}
// how far a sale of this value pushes the front (0 if it doesn't count)
function salePushAmt(locId, item, value) {
  const e = backedWar(); if (!e || LOC[locId].faction !== e.backed) return 0;
  const k = ITEMS[item].ore ? 15 : item === 'arms' ? 30 : 20;
  return Math.min(30, value / haulRef() * k);
}
function warSalePush(locId, item, value) {
  const a = salePushAmt(locId, item, value);
  if (a >= 0.5) warPush(backedWar(), a, tx('pol_why_delivered', { item: ITEMS[item].n }));
}
function warDay(e) {
  if (e.resolved || (OFFLINE && e.backed)) return;
  const [a, b] = e.war;
  e.front = clamp((e.front || 0) + (facStrength(a) - facStrength(b)) * 0.6 + rand(-4, 4), -100, 100);
  if (Math.abs(e.front) >= 100) endWar(e, e.front > 0 ? a : b);
}
function warBarHTML(e, big) {
  const [a, b] = e.war, f = e.front || 0, pct = (100 + f) / 2;
  const you = e.backed ? tx('pol_bar_you', { c: FACTIONS[e.backed].c, f: FACTIONS[e.backed].n, n: Math.round(e.push || 0) }) : tx('pol_bar_join');
  return `<div class="warbar ${big ? 'big' : ''}"><div class="wb-names"><b style="color:${FACTIONS[a].c}">${FACTIONS[a].n}</b><span>⚔ ${e.resolved ? tx('pol_bar_final') : tx('pol_bar_left', { n: Math.max(0, e.end - S.day) })}</span><b style="color:${FACTIONS[b].c}">${FACTIONS[b].n}</b></div>
    <div class="wb-track"><i style="width:${pct}%;background:${FACTIONS[a].c}"></i><i style="width:${100 - pct}%;background:${FACTIONS[b].c}"></i><em style="left:${pct}%"></em><span class="wb-mid"></span></div>${you}</div>`;
}
function endWar(e, winner) {
  if (e.resolved) return;
  e.resolved = 1;
  S.events = S.events.filter(x => x !== e);
  const names = e.war.map(f => FACTIONS[f].n).join(tx('pol_vs'));
  if (winner) { addNews('🏆', tx('pol_won_news', { w: FACTIONS[winner].n, names }), FACTIONS[winner].c); repChange(winner, 3, true); }
  else addNews('🕊️', tx('pol_truce_news', { names }), '#8fa3c7');
  if (!e.backed || typeof pendingChoices === 'undefined') return;
  const f = e.backed, bar = warBarHTML(e, true);
  if (winner === f && e.push >= WAR.minPush) {
    S.allies = S.allies || {}; S.spoils = S.spoils || {};
    const stars = S.allies[f] = Math.min(WAR.maxStars, (S.allies[f] || 0) + 1);
    repChange(f, 15, true);
    const owned = S.spoils[f] = S.spoils[f] || [];
    const opts = Object.keys(SPOILS).filter(k => !owned.includes(k));
    const starTxt = `<div class="ally-stars">${'★'.repeat(stars)}${'☆'.repeat(WAR.maxStars - stars)}</div>` + tx('pol_ally', { f: FACTIONS[f].n, n: Math.round(stars * WAR.starBonus * 100) });
    if (opts.length) pendingChoices.push({ icon: '🏆', title: tx('pol_wins_t', { f: FACTIONS[f].n }), html: bar + starTxt + tx('pol_choose_spoils'),
      choices: opts.map(k => ({ label: `${SPOILS[k].n} — ${SPOILS[k].d}`, cost: 0, fn: () => { owned.push(k); addNews(SPOILS[k].icon, tx('pol_spoils_news', { s: SPOILS[k].n, f: FACTIONS[f].n }), '#ffd24a'); } })) });
    else { const prize = Math.round(haulRef() * 3); earn(prize); pendingChoices.push({ icon: '🏆', title: tx('pol_wins_t', { f: FACTIONS[f].n }), html: bar + starTxt + tx('pol_war_bonus', { n: fmt(prize) }), choices: [{ label: tx('pol_collect'), cost: 0, fn: () => {} }] }); }
  } else if (winner === f) {
    repChange(f, 8, true);
    pendingChoices.push({ icon: '🏆', title: tx('pol_wins_plain_t', { f: FACTIONS[f].n }), html: bar + tx('pol_barely', { n: Math.round(e.push || 0), m: WAR.minPush }), choices: [{ label: tx('pol_ok'), cost: 0, fn: () => {} }] });
  } else {
    repChange(f, -8, true);
    pendingChoices.push({ icon: winner ? '💥' : '🕊️', title: winner ? tx('pol_lost_t', { f: FACTIONS[f].n }) : tx('pol_stalemate_t'), html: bar + `<p>${winner ? tx('pol_beaten') : tx('pol_nobreak')}${tx('pol_nospoils')}</p>`, choices: [{ label: tx('pol_ok'), cost: 0, fn: () => {} }] });
  }
}
function politicsDay() {
  for (const e of [...S.events]) if (e.war) warDay(e);
  if (!S.loans) return;
  for (const ln of [...S.loans]) if (S.day >= ln.due) {
    S.loans = S.loans.filter(x => x !== ln);
    const l = LOC[ln.loc];
    if (l.nuked || Math.random() < 0.1) { addNews('🏦', tx('pol_default_news', { n: l.n }), '#ff6b7d'); toast(tx('pol_default_toast', { n: l.n }), 'bad'); }
    else { earn(ln.amt); addNews('🏦', tx('pol_repaid_news', { st: l.station, a: fmt(ln.amt) }), '#6dffb0'); toast(tx('pol_repaid_toast', { a: fmt(ln.amt) }), 'good'); }
  }
}

// ---------- player powers (one per location, with cooldowns) ----------
const POWERS = {
  works:  { icon: '🏛️', n: tx('pol_pw_works'), stage: U.TRADE, cd: 15, cost: () => pcost(0.003, 100000), d: tx('pol_pw_works_d') },
  boom:   { icon: '🏗️', n: tx('pol_pw_boom'), stage: U.TRADE, cd: 45, cost: () => pcost(0.006, 300000), d: tx('pol_pw_boom_d') },
  purge:  { icon: '🛡️', n: tx('pol_pw_purge'), stage: U.TRADE, cd: 30, cost: () => pcost(0.005, 250000), d: tx('pol_pw_purge_d') },
  end:    { icon: '🕊️', n: tx('pol_pw_end'), stage: U.TRADE, cd: 0, cost: () => pcost(0.004, 200000) },
  incite: { icon: '🔥', n: tx('pol_pw_incite'), stage: U.SATURN, cd: 60, cost: () => pcost(0.02, 5e7), d: tx('pol_pw_incite_d') },
  back:   { icon: '🎖️', n: tx('pol_pw_back'), stage: U.TRADE, cd: 0, cost: () => pcost(0.004, 150000), d: tx('pol_pw_back_d') },
  offensive: { icon: '🚀', n: tx('pol_pw_offensive'), stage: U.TRADE, cd: 8, cost: () => pcost(0.008, 300000), d: tx('pol_pw_offensive_d') },
  peace:  { icon: '🤝', n: tx('pol_pw_peace'), stage: U.SATURN, cd: 0, cost: () => pcost(0.015, 4e7), d: tx('pol_pw_peace_d') },
  nuke:   { icon: '💥', n: tx('pol_pw_nuke'), stage: U.FRONTIER, cd: 0, cost: () => pcost(0.05, 1e12), d: tx('pol_pw_nuke_d') },
};
const NUKABLE = ['mercurio', 'venus', 'marte', 'ceres', 'europa', 'titan', 'pluton'];
function cdLeft(id, kind) { const d = ((S.cd || {})[id] || {})[kind]; return d ? Math.max(0, d - S.day) : 0; }
function setCd(id, kind, days) { S.cd = S.cd || {}; (S.cd[id] = S.cd[id] || {})[kind] = S.day + days; }
function warOf(f) { return S.events.find(e => e.war && e.war.includes(f)); }
// Which powers can be used at a location right now? -> [{ kind, arg, label, cost, ok, why }]
function powersAt(id) {
  const l = LOC[id], out = [];
  if (!has(U.TRADE) || !locOpen(id) || l.nuked) return out;
  const add = (kind, extra) => {
    const P = POWERS[kind]; if (!has(P.stage)) return;
    const cost = P.cost(), cd = cdLeft(id, kind);
    const o = { kind, arg: id, icon: P.icon, label: P.n, d: P.d, cost, ...extra };
    o.ok = !cd && S.credits >= cost && !o.why;
    if (cd && !o.why) { o.why = cd > 1 ? tx('pol_ready_n', { n: cd }) : tx('pol_ready_1'); o.cdWait = 1; }
    out.push(o);
  };
  const city = l.market && !l.depot;
  if (city && l.faction && l.faction !== 'piratas') add('works');
  if (city) add('boom', kindActive('boom', id) ? { why: tx('pol_why_boom') } : {});
  if (has(U.BELT) && !l.secret && ((l.danger || 0) >= 0.1 || warlordAt(id))) add('purge', S.events.some(e => e.mine && e.kind === 'purge' && e.locs.includes(id)) ? { why: tx('pol_why_secured') } : {});
  if (city && l.faction && l.faction !== 'piratas' && has(U.TRADE)) {
    const w = warOf(l.faction);
    if (!w && has(U.SATURN)) {
      for (const f of ['tierra', 'marte', 'cinturon', 'exterior']) if (f !== l.faction && factionAlive(f) && FACTIONS[f].locs.some(locOpen))
        add('incite', { arg: id + '|' + f, label: tx('pol_incite_vs', { f: FACTIONS[f].n }), why: S.events.some(e => e.war) ? tx('pol_why_war') : null });
    } else if (w) {
      const other = backedWar();
      if (!w.backed) add('back', other && other !== w ? { why: tx('pol_why_backed') } : {});
      else if (w.backed === l.faction) add('offensive');
      if (has(U.SATURN)) add('peace');
    }
  }
  if (has(U.FRONTIER) && built('nova') && NUKABLE.includes(id)) add('nuke');
  return out;
}
function usePower(kind, arg) {
  const P = POWERS[kind]; const c = P.cost();
  if (S.credits < c) return false;
  let id = arg;
  if (kind === 'end') {
    const e = S.events.find(x => x.uid === arg); if (!e || e.mine) return false;
    S.credits -= c;
    S.events = S.events.filter(x => x !== e); e.resolved = 1;
    const facs = new Set((e.locs || []).map(l => LOC[l].faction).filter(f => f && f !== 'piratas'));
    for (const f of facs) repChange(f, 10, true);
    addNews('🕊️', tx('pol_end_news', { t: e.title }), '#6dffb0');
    save(); return true;
  }
  if (kind === 'incite') {
    const [loc, f2] = arg.split('|'); id = loc;
    if (cdLeft(id, kind) || S.events.some(e => e.war)) return false;
    const f1 = LOC[loc].faction;
    S.credits -= c;
    const w = makeWar(f1, f2, randi(30, 45)); w.kind = 'war'; w.incited = 1; addEvent(w);
    showEventBanner(w);
    if (Math.random() < 0.25) { repChange(f1, -30); repChange(f2, -30); addNews('🕵️', tx('pol_leak_news', { a: FACTIONS[f1].n, b: FACTIONS[f2].n }), '#ff6b7d'); toast(tx('pol_leak_toast'), 'bad'); }
    else addNews('⚔️', tx('pol_war_news', { a: FACTIONS[f1].n, b: FACTIONS[f2].n }), '#ffc857');
    setCd(id, kind, P.cd); save(); return true;
  }
  const l = LOC[id];
  if (cdLeft(id, kind)) return false;
  const opt = powersAt(id).find(o => o.kind === kind);
  if (!opt || opt.why && !opt.cdWait) return false;
  S.credits -= c;
  if (kind === 'works') { repChange(l.faction, 12); addNews('🏛️', tx('pol_works_news', { n: l.n }), '#6dffb0'); }
  else if (kind === 'boom') {
    addEvent({ kind: 'boom', mine: 1, icon: '🏗️', title: tx('pol_myboom_t', { n: l.n }), text: tx('pol_myboom', { st: l.station }),
      dur: 20, locs: [id], price: ORES.map(i => ({ loc: id, item: i, m: 1.9 })) });
    if (l.faction) repChange(l.faction, 6, true);
    addNews('🏗️', tx('pol_boom_news', { n: l.n }), '#ffd24a');
  } else if (kind === 'purge') {
    S.events = S.events.filter(e => !(e.kind === 'pirates' || e.kind === 'warlord') || !e.locs.includes(id));
    addEvent({ kind: 'purge', mine: 1, icon: '🛡️', title: tx('pol_purge_t', { n: l.n }), text: tx('pol_purge', { n: l.n }),
      dur: 30, locs: [id], danger: [{ loc: id, add: -1 }] });
    repChange('piratas', -5, true);
    addNews('🛡️', tx('pol_purge_news', { n: l.n }), '#6dffb0');
  } else if (kind === 'back') {
    const w = warOf(l.faction); if (!w || w.backed) { S.credits += c; return false; }
    if (backedWar()) { S.credits += c; return false; }
    w.backed = l.faction; w.push = 0; w.front = w.front || 0;
    const enemy = w.war.find(f => f !== l.faction);
    // their war industry buys metals: +30% at the stations of the side you back
    for (const id of FACTIONS[l.faction].locs) if (!LOC[id].nuked) for (const it of ['iron', 'titanium', 'nickel', 'platinum', 'iridium']) w.price.push({ loc: id, item: it, m: 1.3 });
    repChange(l.faction, 15); repChange(enemy, -15);
    addNews('🎖️', tx('pol_back_news', { f: FACTIONS[l.faction].n }), '#ffd24a');
  } else if (kind === 'offensive') {
    const w = warOf(l.faction); if (!w || w.backed !== l.faction) { S.credits += c; return false; }
    warPush(w, 20, tx('pol_why_offensive'));
    for (const x of FACTIONS[l.faction].locs) setCd(x, 'offensive', POWERS.offensive.cd);
    addNews('🚀', tx('pol_offensive_news', { f: FACTIONS[l.faction].n }), '#ffd24a');
  } else if (kind === 'peace') {
    const w = warOf(l.faction); if (!w) { S.credits += c; return false; }
    S.events = S.events.filter(e => e !== w); w.resolved = 1;
    for (const f of w.war) repChange(f, 20, true);
    S.peace = Math.min(5, (S.peace || 0) + 1);
    addNews('🤝', tx('pol_peace_news', { names: w.war.map(f => FACTIONS[f].n).join(tx('pol_and')) }), '#6dffb0');
  } else if (kind === 'nuke') {
    destroyPlanet(id);
  }
  if (P.cd) setCd(id, kind, P.cd);
  save();
  return true;
}

// ---------- the Nova Cannon: destroying planets ----------
const LOC_BASE = {};
// what a location looks like before any nukes (rebuilt whenever the star system changes)
function snapshotLocBase() { for (const l of LOCS) LOC_BASE[l.id] = { station: l.station, market: l.market, faction: l.faction, field: l.field, depot: l.depot, desc: l.desc, danger: l.danger, black: l.black, tex: l.tex, col: l.col }; }
snapshotLocBase();
function resetLocs() {
  for (const l of LOCS) { Object.assign(l, LOC_BASE[l.id]); delete l.nuked; if (!LOC_BASE[l.id].field) delete l.field; if (!LOC_BASE[l.id].station) delete l.station; }
  FIELDS.splice(0, FIELDS.length, ...NODES.filter(l => l.field));
}
function wreckLoc(id) {
  const l = LOC[id];
  l.nuked = 1;
  l.station = tx('pol_wreck_station', { n: l.n }); l.depot = 1; l.market = { ...DEPOT };
  delete l.faction; delete l.black;
  l.field = { n: tx('pol_wreck_field', { n: l.n }), z: 5, ores: { exotic: 3, iridium: 3, platinum: 2 }, count: 36 };
  l.desc = tx('pol_wreck_desc', { n: l.n });
  l.danger = 0.35; l.col = ['#ff8a4a', '#3a1208'];
  FIELDS.splice(0, FIELDS.length, ...NODES.filter(x => x.field));
}
function applyNukes() { resetLocs(); for (const id of S.nuked || []) wreckLoc(id); }
function destroyPlanet(id) {
  const l = LOC[id], name = l.n, fac = l.faction;
  S.nuked = S.nuked || []; S.nuked.push(id);
  delete S.invest[id]; delete S.contracts[id]; delete S.outposts[id];
  S.active = S.active.filter(c => c.to !== id && c.from !== id);
  S.events = S.events.filter(e => !(e.locs || []).includes(id) || e.war);
  S.freighters = (S.freighters || []).filter(f => f.from !== id && f.to !== id);
  wreckLoc(id);
  if (fac && !factionAlive(fac)) S.events = S.events.filter(e => !(e.war && e.war.includes(fac)));
  if (fac) repChange(fac, factionAlive(fac) ? -60 : -100, true);
  for (const f in FACTIONS) if (f !== fac && f !== 'piratas') repChange(f, -20, true);
  repChange('piratas', 25, true);
  addNews('💥', tx('pol_nuked_news', { n: name }), '#ff4d6d');
  if (typeof MapScene !== 'undefined') MapScene.nukeFx = { id, t: 0 };
  sfx('boom'); setTimeout(() => sfx('boom'), 250); setTimeout(() => sfx('lose'), 600);
}

// ---------- freighters: automated trade routes ----------
// fleet size grows with progress: 10 at Trade, +4 at Saturn, +4 at the Frontier
const FREIGHT_SLOTS = [[U.TRADE, 10], [U.SATURN, 4], [U.FRONTIER, 4]];
const FREIGHT = {
  max: () => FREIGHT_SLOTS.reduce((n, [st, k]) => n + (has(st) ? k : 0), 0),
  nextSlots: () => FREIGHT_SLOTS.find(([st]) => !has(st)),
  perRoute: 3,
  cap: () => Math.round(8 * Math.pow(1.6, Math.max(0, S.unlock - 5))),
  cost: () => Math.round(1e6 * Math.pow(3, Math.max(0, S.unlock - 5)) * Math.pow(1.35, (S.freighters || []).length)),
};
function routeCycle(from, to) { const days = Math.max(1, Math.round(locDist(from, to, S.day) / 22)); return 2 * (3 + days * 1.2); }
function tradeMult() { let inv = 0; for (const id in S.invest) inv += S.invest[id]; return (1 + INVEST.bonus * inv) * (built('dyson') ? 5 : 1) * (built('exchange') ? 3 : 1); }
function freighterIncome(f) {
  if (!cityOpen(f.from) || !cityOpen(f.to) || marketClosed(f.from) || marketClosed(f.to)) return 0;
  const bp = buyPrice(f.from, f.g), sp = sellPrice(f.to, f.g);
  if (!bp || !sp) return 0;
  return Math.max(0, sp - bp) * FREIGHT.cap() / routeCycle(f.from, f.to) * tradeMult();
}
function freightIncome() { let v = 0; for (const f of S.freighters || []) v += freighterIncome(f); return v; }
// best trades starting at a station (used by the Trade tab and freighters).
// Only counts what the destination still wants: a saturated market isn't offered.
function tradeRoutes(id, all) {
  const out = [];
  if (!cityOpen(id)) return out;
  const D = demandCap();
  for (const g of GOODS) {
    const bp = buyPrice(id, g); if (!bp) continue;
    let best = null;
    for (const C of NODES) if (cityOpen(C.id) && C.id !== id && C.market[g] != null && !marketClosed(C.id)) {
      const sp = sellPrice(C.id, g); if (!sp) continue;
      const d = demandOf(C.id, g), f0 = demandFactor(C.id, g);
      const units = Math.min(stockLeft(id, g), ship.cargoMax, Math.floor(d * D));
      if (units < 1 || d < 0.2) continue;
      const f1 = 0.15 + 0.85 * (d - units / D), avg = Math.round(sp * (f0 + f1) / 2 / f0);
      const profit = (avg - bp) * units;
      if (avg > bp * 1.15 && (!best || profit > best.profit)) best = { to: C.id, sp, avg, units, profit, d };
    }
    if (best) out.push({ g, from: id, bp, ...best });
  }
  return out.sort((a, b) => b.profit - a.profit);
}
const routeCount = (from, to, g) => (S.freighters || []).filter(f => f.from === from && f.to === to && f.g === g).length;
// why a freighter can't be hired on this route right now (null = it can)
function freighterBlock(from, to, g) {
  const n = (S.freighters || []).length, max = FREIGHT.max(), nx = FREIGHT.nextSlots();
  if (n >= max) return { short: tx('pol_fleet_full', { n, max }), long: tx('pol_fleet_full_l', { n, max }) + (nx ? tx('pol_fleet_more', { k: nx[1], t: UNLOCKS[nx[0]].title }) : tx('pol_fleet_max')) };
  if (routeCount(from, to, g) >= FREIGHT.perRoute) return { short: tx('pol_route_full', { p: FREIGHT.perRoute }), long: tx('pol_route_full_l', { p: FREIGHT.perRoute }) };
  const c = FREIGHT.cost();
  if (S.credits < c) return { short: tx('pol_need_cr', { c: fmt(c) }), long: tx('pol_next_freighter', { c: fmt(c) }) };
  return null;
}
function hireFreighter(from, to, g) {
  S.freighters = S.freighters || [];
  const c = FREIGHT.cost();
  if (freighterBlock(from, to, g)) return false;
  S.credits -= c; S.freighters.push({ from, to, g, t0: Math.random() });
  addNews('🚚', tx('pol_hired_news', { item: ITEMS[g].n, a: LOC[from].n, b: LOC[to].n }), '#6dffb0');
  save();
  return true;
}
