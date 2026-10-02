'use strict';
// ============ SPANISH GAME CONTENT ============
// The world's text (ores, factions, planets, unlocks, megaprojects, upgrades, enemies, every star system's
// story) is written in English inside the data; when the game runs in Spanish this table is laid over it at boot.
const ES_CONTENT = /*ES_CONTENT*/{
 "base": {
  "items": {
   "iron": {
    "n": "Hierro"
   },
   "ice": {
    "n": "Hielo"
   },
   "titanium": {
    "n": "Titanio"
   },
   "cobalt": {
    "n": "Cobalto"
   },
   "nickel": {
    "n": "Níquel"
   },
   "he3": {
    "n": "Helio-3"
   },
   "platinum": {
    "n": "Platino"
   },
   "sunstone": {
    "n": "Piedra solar"
   },
   "iridium": {
    "n": "Iridio"
   },
   "ringpearl": {
    "n": "Perla de anillo"
   },
   "exotic": {
    "n": "Cristal exótico"
   },
   "voidshard": {
    "n": "Fragmento del vacío"
   },
   "food": {
    "n": "Comida"
   },
   "meds": {
    "n": "Medicinas"
   },
   "machinery": {
    "n": "Maquinaria"
   },
   "tech": {
    "n": "Electrónica"
   },
   "arms": {
    "n": "Armas"
   },
   "luxury": {
    "n": "Lujos"
   }
  },
  "factions": {
   "tierra": {
    "n": "Unión Terrestre"
   },
   "marte": {
    "n": "República de Marte"
   },
   "cinturon": {
    "n": "Coalición del Cinturón"
   },
   "exterior": {
    "n": "Liga Exterior"
   },
   "piratas": {
    "n": "Sindicato Negro"
   }
  },
  "locs": {
   "mercurio": {
    "n": "Mercurio",
    "station": "Depósito Caloris",
    "desc": "Roca calcinada junto al Sol. Platino y ardiente Piedra solar, pero el calor quema los cascos sin escudos.",
    "field": {
     "n": "Llanuras de Caloris"
    }
   },
   "venus": {
    "n": "Venus",
    "station": "Ciudad Nube Afrodita",
    "desc": "Ciudades flotantes sobre nubes de ácido. Fabrican lujos y medicinas, y mueren por agua."
   },
   "tierra": {
    "n": "Tierra",
    "station": "Puerto Portal",
    "desc": "La cuna de la humanidad. Paga 50–70% más por cada metal que traigas."
   },
   "luna": {
    "n": "Luna",
    "station": "Base Tranquilidad",
    "desc": "Tu base. Un campo minero tranquilo con una estación abajo.",
    "field": {
     "n": "Mares lunares"
    }
   },
   "marte": {
    "n": "Marte",
    "station": "Ciudad Olimpo",
    "desc": "Una república militarizada. Paga una fortuna por el hielo: en Marte, el agua es vida."
   },
   "ceres": {
    "n": "Ceres",
    "station": "Estación Ceres",
    "desc": "Capital del Cinturón de asteroides. Níquel, cobalto azul, iridio… y piratas.",
    "field": {
     "n": "Cinturón principal"
    }
   },
   "jupiter": {
    "n": "Júpiter"
   },
   "europa": {
    "n": "Europa",
    "station": "Colonia Europa",
    "desc": "Una colonia bajo el hielo. Necesita comida y tecnología con urgencia. Paga bien por el iridio."
   },
   "troyanos": {
    "n": "Troyanos",
    "station": "Depósito L4",
    "desc": "Un enjambre de asteroides en el punto L4 de Júpiter. Iridio por todas partes. Territorio pirata.",
    "field": {
     "n": "Troyanos de Júpiter"
    }
   },
   "saturno": {
    "n": "Saturno",
    "station": "Depósito del Anillo",
    "desc": "Los anillos: Helio-3, brillantes Perlas de anillo y los primeros cristales exóticos.",
    "field": {
     "n": "Anillos de Saturno"
    }
   },
   "titan": {
    "n": "Titán",
    "station": "Refinería Titán",
    "desc": "Refinerías de metano. Paga el mejor precio por el Helio-3."
   },
   "pluton": {
    "n": "Plutón",
    "station": "Refugio Caronte",
    "desc": "Un mercado negro en el borde del sistema. Los mejores precios por exóticos. Sin preguntas."
   },
   "kuiper": {
    "n": "Cinturón de Kuiper",
    "station": "Depósito Frontera",
    "desc": "La frontera helada. Los cristales exóticos brillan por todas partes… custodiados por portanaves piratas.",
    "field": {
     "n": "Cinturón de Kuiper"
    }
   },
   "oort": {
    "n": "Nube de Oort",
    "station": "Puesto Señal Profunda",
    "desc": "El límite del alcance del Sol. Algo antiguo transmite desde lo más profundo de la nube.",
    "field": {
     "n": "Nube de Oort"
    }
   }
  },
  "unlocks": [
   {},
   {
    "title": "Puestos mineros",
    "text": "Construye un <b>puesto minero</b> en un campo y añade <b>drones</b>. Minan <b>despacio</b> pero <b>nunca paran</b>, incluso cuando no estás. Abre la pestaña <b>Puesto</b> al atracar."
   },
   {
    "title": "Mapa estelar",
    "text": "Desde ahora <b>tú eliges dónde vender</b>. Los depósitos de las estaciones pagan poco; <b>la Tierra paga unas 3×</b> por los metales: ¡llena la bodega y vuela hacia allá! Viajar gasta combustible, que se recarga al atracar. Las mejoras de <b>Refinería</b> aumentan TODOS los ingresos por mineral."
   },
   {
    "title": "Marte y Mercurio",
    "text": "<b>Mercurio</b> está cubierto de <b>Platino</b> y <b>Piedra solar</b> (valen 60–100× el hierro), pero el calor quema tu casco: compra <b>Escudos</b>. <b>Marte</b> paga una fortuna por el hielo."
   },
   {
    "title": "El Cinturón de asteroides",
    "text": "<b>Ceres</b> y el Cinturón principal: níquel, <b>cobalto</b>, iridio… y <b>piratas</b>. En combate tú pilotas y disparas: ¡compra <b>Cañones</b>!"
   },
   {
    "title": "Comercio y eventos",
    "text": "Las estaciones te permiten <b>comprar y vender bienes</b> y ofrecen <b>contratos</b>. Compra barato en un planeta y vende en la siguiente parada de tus rutas de mineral. Los <b>eventos</b> del sistema (guerras, plagas, auges) mueven los precios. <b>Venus</b> está abierto."
   },
   {
    "title": "Sistema de Júpiter",
    "text": "<b>Europa</b> y los asteroides <b>Troyanos</b>: iridio que vale <b>300× el hierro</b>. El <b>Escáner</b> revela vetas ricas."
   },
   {
    "title": "Saturno e influencia",
    "text": "<b>Titán</b> y los <b>Anillos</b>. <b>Invierte</b> en estaciones: cada nivel suma <b>+10% de tus ingresos base</b> (mineral, drones, cargueros) e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar el sistema."
   },
   {
    "title": "La Frontera",
    "text": "El mercado negro de <b>Plutón</b> y el <b>Cinturón de Kuiper</b>. Los cristales exóticos valen <b>2,000× el hierro</b>."
   }
  ],
  "projects": {
   "driver": {
    "n": "Catapulta Lunar",
    "d": "Un riel magnético de un kilómetro en la Luna lanza mineral directo a la Tierra.",
    "fx": "Producción del puesto de Luna ×3"
   },
   "beacons": {
    "n": "Balizas de Espacio Profundo",
    "d": "Una red de navegación que cubre el sistema interior.",
    "fx": "Viajes 50% más rápidos · combustible −30%"
   },
   "fleet": {
    "n": "Flota de Seguridad Privada",
    "d": "Contrata naves armadas que patrullan tus rutas y vuelan contigo en combate.",
    "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
   },
   "elevator": {
    "n": "Ascensor Espacial Terrestre",
    "d": "Un cable de 36,000 km de alto. Ahora tú abasteces la industria de la Tierra.",
    "fx": "Todo el mineral se vende +25% en todas partes"
   },
   "terraform": {
    "n": "Terraformar Marte",
    "d": "Cometas de hielo, espejos orbitales y un siglo de trabajo en una sola partida del presupuesto. Marte se vuelve azul.",
    "fx": "Marte paga ×2 por todo · reputación con República de Marte +50"
   },
   "gates": {
    "n": "Red de Portales de Salto",
    "d": "Portales de agujero de gusano en cada estación. La distancia ya no importa.",
    "fx": "Viajes instantáneos y gratis a cualquier lugar"
   },
   "ringstation": {
    "n": "Megaestación del Anillo",
    "d": "Una refinería del tamaño de una ciudad, tejida en los anillos de Saturno.",
    "fx": "TODOS los ingresos de drones ×3"
   },
   "dyson": {
    "n": "Enjambre Dyson",
    "d": "Miles de millones de espejos alrededor del Sol. Ahora tienes la energía de una estrella.",
    "fx": "TODOS los ingresos ×5"
   },
   "nova": {
    "n": "Cañón Nova",
    "d": "Un rayo que concentra el Enjambre Dyson en un solo punto. Nada puede resistirlo.",
    "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
   },
   "resonance": {
    "n": "Matriz de Resonancia Cristalina",
    "d": "Emisores sónicos afinados hacen cantar cada cristal al romperse: los fragmentos se parten por sus vetas más ricas.",
    "fx": "Los fragmentos de cristal sueltan ×2 mineral"
   },
   "borer": {
    "n": "Perforadora de Núcleo",
    "d": "Un cabezal capaz de partir planetas, miniaturizado y atornillado a tu nave.",
    "fx": "Alcance del taladro +60% y potencia ×1.5"
   },
   "plasmaforge": {
    "n": "Forja de Plasma",
    "d": "Plasma ardiente como una estrella derrite el blindaje de los asteroides antes de que llegue tu rayo.",
    "fx": "El láser hace 60% a rocas blindadas · rocas blindadas sueltan ×2 mineral"
   },
   "exchange": {
    "n": "Bolsa Galáctica",
    "d": "Cotizas todo el sistema estelar en el mercado galáctico. Todos quieren una parte.",
    "fx": "Ingresos de cargueros y comercio ×3"
   },
   "chainlab": {
    "n": "Laboratorio de Reacción en Cadena",
    "d": "Los científicos del Gremio de Dinamiteros ajustan cada roca volátil del sistema para que estalle justo a punto.",
    "fx": "Las rocas volátiles explotan 60% más amplio"
   },
   "herding": {
    "n": "Pastoreo de Cometas",
    "d": "Pastores gravitatorios guían los cometas del sistema directo por tus campos mineros.",
    "fx": "Cometas 3× más frecuentes y sueltan ×2 mineral"
   },
   "bounty": {
    "n": "Bolsa de Recompensas",
    "d": "Cada ciudad libre de Altair te paga por cada pirata que vuelas en pedazos.",
    "fx": "Botín pirata ×3"
   },
   "whisperer": {
    "n": "Susurradores del Arrecife",
    "d": "Los cantores de los Custodios del Arrecife enseñan a tu nave la canción que aman las rocas vivas. Nadan directo hacia tu láser.",
    "fx": "Las rocas vivas ya no huyen y sueltan ×2 mineral"
   },
   "sonar": {
    "n": "Sonar Cuántico",
    "d": "Un sonar que oye el eco de cada geoda del sistema, incluso las que aún no se forman.",
    "fx": "Escáner profundo recarga 2× más rápido · geodas sueltan ×2 mineral"
   },
   "polarity": {
    "n": "Motor de Polaridad",
    "d": "Inviertes los polos de toda la nebulosa. Las rocas magnéticas se juntan como viejas amigas.",
    "fx": "Rocas magnéticas se agrupan 2× más rápido y sueltan ×2 mineral"
   },
   "beamharvest": {
    "n": "Cosechadora de Rayos",
    "d": "Colectores que beben el rayo del púlsar antes de que te alcance y lo vierten en las rocas.",
    "fx": "El rayo ya no te daña · rocas cargadas sueltan ×3 mineral"
   },
   "archive": {
    "n": "Archivo de Reliquias",
    "d": "Los Excavadores de Glifos por fin leyeron las instrucciones de las reliquias.",
    "fx": "Los poderes de reliquia duran el doble"
   },
   "hawking": {
    "n": "Refinería Hawking",
    "d": "Lo que cae al agujero negro sale como un leve brillo de radiación, y tú lo cobras.",
    "fx": "Las rocas que traga el agujero negro te pagan · gravedad a la mitad"
   },
   "starheart": {
    "n": "Toma del Corazón Estelar",
    "d": "Perforas una tubería hasta el corazón de una estrella moribunda. Late más seguido, y siempre estás listo.",
    "fx": "Pulsos estelares 2× más frecuentes y 50% más largos"
   }
  },
  "upg": {
   "hull": {
    "n": "Clase de nave",
    "d": "Un casco nuevo es una nave nueva: más carga base y más blindaje.",
    "names": [
     "Gorrión",
     "Mula",
     "Albatros",
     "Leviatán",
     "Coloso"
    ]
   },
   "extractor": {
    "n": "Extractor",
    "d": "Las rocas sueltan más mineral: +15% por nivel. Llena tu bodega más rápido."
   },
   "laser": {
    "n": "Láser minero",
    "d": "Corta rocas más rápido. Las zonas lejanas tienen rocas mucho más duras."
   },
   "magnet": {
    "n": "Imán",
    "d": "Atrae mineral desde más lejos. Cada 3 niveles suma un dron recolector."
   },
   "cargo": {
    "n": "Bodega",
    "d": "+25% de espacio de carga por nivel."
   },
   "refinery": {
    "n": "Refinería",
    "d": "+7% de valor en TODO el mineral, incluido el de tus drones."
   },
   "engine": {
    "n": "Motores",
    "d": "Vuela más rápido, gasta menos combustible y escapa antes de los combates."
   },
   "tank": {
    "n": "Tanque de combustible",
    "d": "Llega a destinos más lejanos."
   },
   "shield": {
    "n": "Escudos",
    "d": "Absorben daño y calor. Se regeneran con el tiempo."
   },
   "weapons": {
    "n": "Cañones",
    "d": "Cañones dobles para pelear con piratas. Mantén pulsado para disparar."
   },
   "scanner": {
    "n": "Escáner",
    "d": "Revela vetas ricas y ayuda a evitar emboscadas."
   }
  },
  "enemies": {
   "raider": {
    "n": "Asaltante"
   },
   "corsair": {
    "n": "Corsario"
   },
   "frigate": {
    "n": "Fragata Pirata"
   },
   "carrier": {
    "n": "Portanaves Pirata"
   },
   "warlord": {
    "n": "Caudillo Pirata"
   },
   "sentinel": {
    "n": "Centinela Alienígena"
   },
   "queen": {
    "n": "Reina de la Colmena"
   },
   "colossus": {
    "n": "Coloso Minero"
   },
   "serpent": {
    "n": "Serpiente Solar"
   },
   "dreadnought": {
    "n": "Acorazado Mercante"
   },
   "citadel": {
    "n": "Ciudadela de Polvo"
   },
   "leviathan": {
    "n": "Leviatán de Hielo"
   },
   "pirateking": {
    "n": "Rey Pirata"
   },
   "kraken": {
    "n": "Kraken Espacial"
   },
   "radiant": {
    "n": "Titán Radiante"
   },
   "phoenix": {
    "n": "Fénix Estelar"
   },
   "hydra": {
    "n": "Hidra Nebular"
   },
   "hydrahead": {
    "n": "Cabeza de Hidra"
   },
   "warden": {
    "n": "Guardián del Púlsar"
   },
   "archon": {
    "n": "El Arconte"
   },
   "shard": {
    "n": "Fragmento de Escudo"
   },
   "devourer": {
    "n": "El Devorador"
   },
   "swarmer": {
    "n": "Enjambrador"
   },
   "adrone": {
    "n": "Dron Centinela"
   },
   "patrol": {
    "n": "Patrulla Militar"
   }
  },
  "ranks": [
   "Novato",
   "Piloto",
   "Contratista",
   "Empresario",
   "Magnate",
   "Leyenda del Cinturón",
   "Soberano Solar"
  ],
  "legacy": {
   "ore": {
    "n": "Legado del Prospector",
    "d": "+10% de valor del mineral en todas partes"
   },
   "drones": {
    "n": "Planos de drones",
    "d": "Los drones cuestan 8% menos"
   },
   "fuel": {
    "n": "Motores eficientes",
    "d": "El combustible cuesta 8% menos"
   },
   "quick": {
    "n": "Ventaja inicial",
    "d": "Empieza cada sistema con el Mapa estelar abierto y 50K créditos"
   },
   "laserPlan": {
    "n": "Planos de láser",
    "d": "Empieza cada sistema con +5 niveles de láser"
   },
   "cargoPlan": {
    "n": "Planos de bodega",
    "d": "Empieza cada sistema con +5 niveles de bodega"
   },
   "extrPlan": {
    "n": "Planos de extractor",
    "d": "Empieza cada sistema con +5 niveles de extractor"
   }
  },
  "galaxy": {
   "sol": "Sol",
   "centauri": "Alfa Centauri",
   "barnard": "Estrella de Barnard",
   "sirius": "Sirio",
   "tauceti": "Tau Ceti",
   "eridani": "Épsilon Eridani",
   "vega": "Vega",
   "altair": "Altair",
   "kepler": "Kepler",
   "rigel": "Rigel",
   "betelgeuse": "Betelgeuse",
   "orion": "Nebulosa de Orión",
   "pulsar": "El Púlsar",
   "rim": "Borde del Núcleo",
   "sgra": "Sagitario A*"
  }
 },
 "systems": {
  "altair": {
   "n": "Altair",
   "intro": "Altair es un <b>imperio pirata</b>: asaltos por todos lados, y botín a la altura. Un desertor te da <b>Cargas mineras</b>: pulsa <b>F</b> (o BOMBA) para soltar una carga que estalla 1.2 s después, partiendo todas las rocas a su alrededor — y dañando también a los piratas. Son tuyas para siempre.",
   "gate": "La nave insignia del Rey se hunde en llamas y su flota se dispersa. El portal de Puerto Calavera es <b>tuyo</b>.",
   "tour": "Tortuga, la capital pirata, <b>pasa en una órbita alargada justo al lado de Haven</b>. El Callejón de la Emboscada va detrás de Bulwark, y el gran gigante de tormentas es el mundo más exterior.",
   "signal": {
    "title": "El Rey Pirata",
    "text": "Todos los piratas de Altair responden a un solo capitán: el <b>Rey Pirata</b>. Su nave insignia vigila el viejo portal de <b>Puerto Calavera</b> — y llama a sus asaltantes en cuanto apareces."
   },
   "factions": {
    "tierra": {
     "n": "Ciudades Libres de Altair"
    },
    "marte": {
     "n": "Custodios de Hierro"
    },
    "cinturon": {
     "n": "Hermandad Chatarrera"
    },
    "exterior": {
     "n": "Alianza de los Confines"
    },
    "piratas": {
     "n": "La Corona Pirata"
    }
   },
   "locs": {
    "luna": {
     "n": "Driftwood",
     "station": "Base Última Oportunidad",
     "desc": "Una luna maltrecha de Haven, marcada por los asaltos.",
     "field": {
      "n": "Chatarra de Driftwood"
     }
    },
    "tierra": {
     "n": "Haven",
     "station": "Puerto Libre",
     "desc": "La última capital libre en un sistema pirata."
    },
    "venus": {
     "n": "Gilded",
     "station": "Aguja del Tesoro",
     "desc": "Un mundo de nubes doradas donde los piratas gastan su botín."
    },
    "mercurio": {
     "n": "Arrecife de Azufre",
     "station": "Depósito del Arrecife",
     "desc": "Un arrecife de roca en llamas. Piedra solar y piratas.",
     "field": {
      "n": "Arrecife Ardiente"
     }
    },
    "marte": {
     "n": "Bulwark",
     "station": "Fuerte Custodio",
     "desc": "Un mundo fortaleza que nunca cayó ante los piratas. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Scrapheap",
     "station": "Salón Chatarrero",
     "desc": "Los chatarreros viven de lo que dejan los piratas.",
     "field": {
      "n": "Cinturón de Restos"
     }
    },
    "jupiter": {
     "n": "Ojo del Leviatán"
    },
    "europa": {
     "n": "Cove",
     "station": "Colonia Cove",
     "desc": "Una luna helada y oculta. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Emboscada",
     "desc": "Rocas troyanas plagadas de nidos piratas.",
     "field": {
      "n": "Callejón de la Emboscada"
     }
    },
    "saturno": {
     "n": "Skullring",
     "station": "Depósito de los Anillos",
     "desc": "Un gigante anillado cuyos anillos esconden mil bases piratas.",
     "field": {
      "n": "Anillos Calavera"
     }
    },
    "titan": {
     "n": "Rumhaze",
     "station": "Refinería de Ron",
     "desc": "Una luna brumosa y bien regada de ron, con refinerías enormes."
    },
    "pluton": {
     "n": "Tortuga",
     "station": "Mercado de la Corona",
     "desc": "La capital de la Corona Pirata. Todo está a la venta."
    },
    "kuiper": {
     "n": "Deriva del Botín",
     "station": "Depósito de la Deriva",
     "desc": "Donde los piratas esconden el mineral robado.",
     "field": {
      "n": "Deriva del Botín"
     }
    },
    "oort": {
     "n": "Puerto Calavera",
     "station": "Puesto Vigía",
     "desc": "El puerto del Rey Pirata, construido alrededor de un portal antiguo.",
     "field": {
      "n": "Puerto Calavera"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Driftwood"
    },
    "3": {
     "title": "Arrecife de Azufre y Bulwark",
     "text": "El <b>Arrecife de Azufre</b> arde con <b>Piedra solar</b> — compra <b>Escudos</b>. <b>Bulwark</b> paga una fortuna por el hielo. ¡Usa tus <b>Cargas mineras (F)</b> en los grupos grandes!"
    },
    "4": {
     "title": "El Cinturón de Restos",
     "text": "<b>Scrapheap</b> y el <b>Cinturón de Restos</b>. Piratas por todas partes — y su botín vale la pena."
    },
    "6": {
     "title": "Ojo del Leviatán",
     "text": "<b>Cove</b> y el <b>Callejón de la Emboscada</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Skullring e influencia",
     "text": "<b>Rumhaze</b> y los <b>Anillos Calavera</b>. <b>Invierte</b> en estaciones (cada nivel da <b>+10% de ingresos base</b>) para ganar ingresos e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Altair."
    },
    "8": {
     "title": "Tortuga",
     "text": "<b>Tortuga</b>, capital de la Corona Pirata, y la <b>Deriva del Botín</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Tobogán del Contrabandista",
     "d": "Un cañón de riel secreto que los piratas construyeron para mover su botín. Ahora mueve tu mineral.",
     "fx": "Producción del puesto de Driftwood ×3"
    },
    "beacons": {
     "n": "Red Bandera Negra",
     "d": "Torres de radio piratas que conocen cada ruta — y cada emboscada.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Armada Traidora",
     "d": "Media flota pirata se cambia de bando por el precio justo. Dos naves vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Elevador del Botín",
     "d": "Un elevador de carga hecho de naves piratas capturadas, soldadas una tras otra.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Jardines del Escondite",
     "d": "Conviertes las sombrías llanuras fortificadas de Bulwark en un resort selvático.",
     "fx": "Bulwark paga ×2 por todo · reputación con Custodios de Hierro +50"
    },
    "gates": {
     "n": "Portales Fantasma",
     "d": "Portales robados, ocultos en bolsas de nebulosa. Nadie sabe adónde llevan — excepto tú.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Astillero de los Anillos Calavera",
     "d": "Un astillero pirata en los anillos que ahora construye drones mineros para ti.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Corona de Altair",
     "d": "Un enjambre de Dyson con forma de corona pirata. Muy sutil.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Andanada del Juicio Final",
     "d": "Todos los cañones piratas capturados del sistema, disparando a la vez.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "barnard": {
   "n": "Estrella de Barnard",
   "intro": "La Estrella de Barnard: una tenue enana roja donde los mineros llevan siglos excavando. El Sindicato de Transportistas de las Profundidades te regala su mejor herramienta, el <b>Taladro</b>: pulsa <b>Q</b> (o el botón TALADRO) para cambiar. Corta 3× más rápido, pero solo de cerca. Es tuyo para siempre.",
   "gate": "El Coloso se desploma convertido en chatarra. Debajo, los viejos mineros habían desenterrado un anillo antiguo… y está <b>despertando</b>.",
   "tour": "Una enana roja pequeña y tenue: sus mundos <b>se apiñan muy juntos</b>, así que los saltos entre ellos son cortos y baratos… y todo orbita rápido.",
   "signal": {
    "title": "La máquina despierta",
    "text": "Lecturas sísmicas desde la megamina abandonada de <b>El Pozo</b>: algo enorme <b>sigue excavando</b> allá abajo, y ataca a toda nave que se acerca."
   },
   "factions": {
    "tierra": {
     "n": "Pacto de la Forja"
    },
    "marte": {
     "n": "Hermandad del Óxido"
    },
    "cinturon": {
     "n": "Sindicato de Transportistas de las Profundidades"
    },
    "exterior": {
     "n": "Liga de Ember"
    },
    "piratas": {
     "n": "Horno Negro"
    }
   },
   "locs": {
    "luna": {
     "n": "Cinderling",
     "station": "Base Pozo Viejo",
     "desc": "Una luna fría y llena de cráteres de Forge. Generaciones de mineros empezaron aquí.",
     "field": {
      "n": "Pozos Viejos"
     }
    },
    "tierra": {
     "n": "Forge",
     "station": "Puerto Yunque",
     "desc": "Un mundo en rotación sincrónica: un lado congelado, el otro ardiendo. Sus forjas nunca duermen."
    },
    "venus": {
     "n": "Ashveil",
     "station": "Aguja de Humo",
     "desc": "Densas nubes de ceniza sobre un mundo caliente. Rico, decadente y sediento de hielo."
    },
    "mercurio": {
     "n": "Brand",
     "station": "Depósito Brand",
     "desc": "Una roca calcinada cerca del sol rojo. El platino está a la vista.",
     "field": {
      "n": "Llanuras Calcinadas"
     }
    },
    "marte": {
     "n": "Rustfall",
     "station": "Ciudad Rustfall",
     "desc": "Cañones rojo óxido y gente testaruda. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Hollowrock",
     "station": "Salón de los Transportistas",
     "desc": "La capital de los Transportistas, vaciada por siglos de minería.",
     "field": {
      "n": "El Cinturón Profundo"
     }
    },
    "jupiter": {
     "n": "Goliath"
    },
    "europa": {
     "n": "Ember",
     "station": "Colonia Ember",
     "desc": "Una luna helada y tibia con aguas termales. La Liga compra iridio."
    },
    "troyanos": {
     "station": "Depósito Troyano",
     "desc": "Rocas atrapadas por la gravedad de Goliath. Piedra solar e iridio.",
     "field": {
      "n": "Troyanos de Goliath"
     }
    },
    "saturno": {
     "n": "Halo",
     "station": "Depósito Halo",
     "desc": "Un pálido gigante con anillos que brilla rojo bajo la luz tenue.",
     "field": {
      "n": "Anillos de Halo"
     }
    },
    "titan": {
     "n": "Brimstone",
     "station": "Planta de Azufre",
     "desc": "Una luna de azufre de Halo con enormes refinerías."
    },
    "pluton": {
     "n": "Coalsack",
     "station": "El Horno",
     "desc": "Un mundo negro como el hollín. El Horno Negro vende de todo."
    },
    "kuiper": {
     "n": "Deriva de Barnard",
     "station": "Depósito de la Deriva",
     "desc": "Rocas heladas en el límite del alcance del sol rojo.",
     "field": {
      "n": "Deriva de Barnard"
     }
    },
    "oort": {
     "n": "El Pozo",
     "station": "Puesto Última Lámpara",
     "desc": "Una megamina abandonada en el borde del sistema. Algo sigue funcionando allá abajo.",
     "field": {
      "n": "El Pozo"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Cinderling"
    },
    "3": {
     "title": "Brand y Rustfall",
     "text": "<b>Brand</b> está cubierto de <b>Platino</b>, pero su calor te quema el casco: compra <b>Escudos</b>. <b>Rustfall</b> paga una fortuna por el hielo."
    },
    "4": {
     "title": "El Cinturón Profundo",
     "text": "<b>Hollowrock</b> y el <b>Cinturón Profundo</b>: cobalto, piedra solar e iridio… y <b>piratas</b> más duros que nunca. Usa el <b>Taladro (Q)</b> en las rocas grandes."
    },
    "6": {
     "title": "Sistema Goliath",
     "text": "<b>Ember</b> y los <b>Troyanos de Goliath</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Halo e influencia",
     "text": "<b>Brimstone</b> y los <b>Anillos de Halo</b>. <b>Invierte</b> en estaciones (cada nivel <b>+10% de ingresos base</b>) para ganar ingresos e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar la Estrella de Barnard."
    },
    "8": {
     "title": "Coalsack",
     "text": "El mercado negro de <b>Coalsack</b> y la <b>Deriva de Barnard</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Catapulta Gravitatoria de Cinderling",
     "d": "Una honda gravitatoria hecha con viejos ascensores de mina lanza el mineral cuesta arriba hasta Forge.",
     "fx": "Producción del puesto de Cinderling ×3"
    },
    "beacons": {
     "n": "Faros de la Enana Roja",
     "d": "Lámparas de bengala gigantes que iluminan rutas seguras por el tenue sistema rojo.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Legión de Gólems de Hierro",
     "d": "Mechas mineros retirados, rearmados y con hambre de piratas. Dos de ellos vuelan a tu lado en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Gancho Celeste de Forge",
     "d": "Un cable giratorio que arrebata la carga del lado helado de Forge y la lanza a la órbita.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Fábricas de Atmósfera de Rustfall",
     "d": "Chimeneas de mil kilómetros bombean aire a los cañones de Rustfall hasta que llueve.",
     "fx": "Rustfall paga ×2 por todo · reputación con Hermandad del Óxido +50"
    },
    "gates": {
     "n": "Agujeros de Gusano Mineros",
     "d": "Los viejos mineros cavaron tan hondo que perforaron el espacio-tiempo. Tú solo pusiste los letreros.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Nanoforja de Halo",
     "d": "Billones de nanobots en los anillos de Halo fabrican drones con polvo de anillo.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Cosechadora del Sol Rojo",
     "d": "Una estrella tenue, un enjambre denso: le exprimes hasta el último fotón a la Estrella de Barnard.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Rompenúcleos",
     "d": "El taladro más grande jamás construido. No mina planetas: los abre.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "betelgeuse": {
   "n": "Betelgeuse",
   "intro": "Betelgeuse es una <b>supergigante roja a punto de explotar</b>. Cada minuto, más o menos, <b>pulsa</b>: una ola de calor barre el campo y todas las rocas quedan <b>fundidas</b> por unos segundos — <b>doble daño de láser y +50% de mineral</b>. ¡Mina con todo cuando llegue la ola! El Sindicato de la Forja te da el <b>Rayo ancho</b>: ahora tu láser se <b>bifurca</b> hacia dos rocas más cerca de tu objetivo. Es tuyo para siempre.",
   "gate": "El Fénix se apaga para siempre y sus cenizas giran hasta formar un anillo. Un portal antiguo se <b>enciende</b>.",
   "tour": "La estrella está <b>tan hinchada</b> que llena el centro del mapa — Pyre orbita justo encima de su superficie hirviente.",
   "signal": {
    "title": "Nacido del fuego",
    "text": "Cada vez que Betelgeuse pulsa, algo enorme surge de las llamas cerca del <b>Nido del Fénix</b>. La Flota del Éxodo lo llama el <b>Fénix Estelar</b>. Dicen las leyendas que hay que matarlo <b>dos veces</b>."
   },
   "factions": {
    "tierra": {
     "n": "Pacto de la Última Luz"
    },
    "marte": {
     "n": "Hermandad de la Ceniza"
    },
    "cinturon": {
     "n": "Sindicato de la Forja"
    },
    "exterior": {
     "n": "Flota del Éxodo"
    },
    "piratas": {
     "n": "Saqueadores de la Brasa"
    }
   },
   "locs": {
    "luna": {
     "n": "Ember",
     "station": "Vigía Ember",
     "desc": "Una luna que brilla con un rojo apagado bajo la luz de Betelgeuse.",
     "field": {
      "n": "Campos de Ember"
     }
    },
    "tierra": {
     "n": "Dusk",
     "station": "Puerto Dusk",
     "desc": "Un mundo oceánico donde el sol nunca termina de ponerse."
    },
    "venus": {
     "n": "Crimson",
     "station": "Aguja Crimson",
     "desc": "Un mundo de nubes rojo sangre. Aquí los más ricos hacen las maletas."
    },
    "mercurio": {
     "n": "Pyre",
     "station": "Depósito Pyre",
     "desc": "Un planeta dentro de las capas exteriores de la estrella. Hace muchísimo calor.",
     "field": {
      "n": "Llanuras de Pyre"
     }
    },
    "marte": {
     "n": "Ashfall",
     "station": "Puerta de Ceniza",
     "desc": "Aquí la ceniza cae como nieve. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Forge",
     "station": "Salón de la Fundición",
     "desc": "El Sindicato de la Forja funde asteroides con el calor de la estrella.",
     "field": {
      "n": "El Cinturón de Forge"
     }
    },
    "jupiter": {
     "n": "Inferno"
    },
    "europa": {
     "n": "Steam",
     "station": "Colonia Fumarola",
     "desc": "Una luna de hielo que se derrite lentamente en vapor. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Inferno",
     "desc": "Los troyanos de Inferno, brillando bajo la luz roja.",
     "field": {
      "n": "Enjambre de Inferno"
     }
    },
    "saturno": {
     "n": "Gloam",
     "station": "Depósito Anillo Gloam",
     "desc": "Un gigante cuyos anillos helados se evaporan poco a poco.",
     "field": {
      "n": "Anillos de Gloam"
     }
    },
    "titan": {
     "n": "Smelt",
     "station": "Fundiciones Smelt",
     "desc": "Una luna de hornos gigantes."
    },
    "pluton": {
     "n": "Exodus",
     "station": "Mercado de Evacuación",
     "desc": "Todos intentan irse antes de que la estrella explote. Todo está en oferta."
    },
    "kuiper": {
     "n": "El Manto Rojo",
     "station": "Depósito del Manto",
     "desc": "Gas que la estrella expulsó hace mucho, ahora lleno de mineral.",
     "field": {
      "n": "El Manto Rojo"
     }
    },
    "oort": {
     "n": "Nido del Fénix",
     "station": "Puesto de las Cenizas",
     "desc": "Un nido de llamas en el borde del sistema.",
     "field": {
      "n": "Nido del Fénix"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Ember"
    },
    "3": {
     "title": "Pyre y Ashfall",
     "text": "<b>Pyre</b> arde con <b>Piedra solar</b> — compra <b>Escudos</b>. <b>Ashfall</b> paga una fortuna por el hielo. Cuando Betelgeuse <b>pulsa</b>, todas las rocas se funden: ¡mina rápido!"
    },
    "4": {
     "title": "El Cinturón de Forge",
     "text": "<b>Forge</b> y el <b>Cinturón de Forge</b>. Tu <b>Rayo ancho</b> brilla entre muchas rocas: apunta a los grupos."
    },
    "6": {
     "title": "Sistema Inferno",
     "text": "<b>Steam</b> y el <b>Enjambre de Inferno</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Gloam e influencia",
     "text": "<b>Smelt</b> y los <b>Anillos de Gloam</b>. <b>Invierte</b> para ganar <b>+10% de ingresos</b> e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Betelgeuse."
    },
    "8": {
     "title": "Exodus",
     "text": "El Mercado de Evacuación de <b>Exodus</b> y <b>el Manto Rojo</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Surfistas de Llamaradas",
     "d": "Tu mineral surfea las llamaradas solares de la propia estrella hasta llegar a casa.",
     "fx": "Producción del puesto de Ember ×3"
    },
    "beacons": {
     "n": "Jinetes del Pulso",
     "d": "Las naves despegan justo cuando Betelgeuse pulsa y surfean la onda expansiva.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Ala Ember",
     "d": "Naves de combate a prueba de fuego que cruzan llamaradas solares por diversión. Dos vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Torre de Corriente Térmica",
     "d": "Una torre tan caliente que el aire de adentro sube a velocidad orbital. La carga sube con él.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Refri Planetario",
     "d": "Envuelves Ashfall en una manta refrigerante gigante. Nieva por primera vez en mil millones de años.",
     "fx": "Ashfall paga ×2 por todo · reputación con Hermandad de la Ceniza +50"
    },
    "gates": {
     "n": "Onda Prestada",
     "d": "Tomas prestada la onda expansiva de la supernova de mañana y la surfeas hoy. Viaje instantáneo, algo chamuscado.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Anillo Elevaestrellas",
     "d": "Succionas las capas exteriores de la estrella y las refinas en mineral. Le sobraba bastante.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Botella de Supernova",
     "d": "Una coraza hecha para atrapar la supernova cuando llegue. Mientras tanto, es la batería más grande jamás construida.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Supernova Anticipada",
     "d": "¿Para qué esperar? Detonas un pedacito de la supernova de Betelgeuse — con puntería.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "centauri": {
   "n": "Alfa Centauri",
   "intro": "Cruzas el portal y llegas a <b>Alfa Centauri</b>: dos soles, cinturones repletos de cristal y piratas <b>mucho más duros</b> que en casa. Tu fortuna se quedó atrás, pero tu <b>Legado</b> viajó contigo.",
   "gate": "La Reina de la Colmena estalla en polvo brillante. En el corazón de la nebulosa, un segundo anillo antiguo <b>despierta</b>: el camino hacia lo más profundo de la galaxia.",
   "tour": "Pandora no es un planeta: es una <b>luna del gigante gaseoso Typhon</b>, con su propia lunita, Tethys. El cinturón de Halcyon está dividido en dos anillos.",
   "signal": {
    "title": "Algo está anidando",
    "text": "Las sondas más allá de la Deriva de Próxima se apagaron una tras otra. La última imagen muestra una <b>nebulosa viva</b>… y algo enorme moviéndose dentro: <b>la Colmena</b>."
   },
   "factions": {
    "tierra": {
     "n": "Pacto de Pandora"
    },
    "marte": {
     "n": "Clanes de Dune"
    },
    "cinturon": {
     "n": "Gremio del Prisma"
    },
    "exterior": {
     "n": "Liga de Typhon"
    },
    "piratas": {
     "n": "Cártel del Mercado Rojo"
    }
   },
   "locs": {
    "luna": {
     "n": "Tethys",
     "station": "Base Primera Luz",
     "desc": "Una tranquila luna gris de Pandora. Tu nuevo comienzo.",
     "field": {
      "n": "Rocas Pastoras"
     }
    },
    "tierra": {
     "n": "Pandora",
     "station": "Puerto Refugio",
     "desc": "Un mundo de cálidos océanos turquesa bajo dos soles. Paga bien por cualquier metal.",
     "layoutDesc": "Una luna oceánica del gigante Typhon, con su propia lunita. Paga bien por cualquier metal."
    },
    "venus": {
     "n": "Calypso",
     "station": "Aguja Orquídea",
     "desc": "Un mundo de nubes violetas. Sus ciudades flotantes ansían lujos y hielo."
    },
    "mercurio": {
     "n": "Cinder",
     "station": "Depósito Cinder",
     "desc": "Un mundo fundido pegado a Alfa Centauri A. Piedra solar por todas partes… y un calor brutal.",
     "field": {
      "n": "Llanuras de Vidrio Ardiente"
     }
    },
    "marte": {
     "n": "Dune",
     "station": "Puerta de Arena",
     "desc": "Un desierto infinito gobernado por clanes orgullosos. Aquí el agua vale más que el oro."
    },
    "ceres": {
     "n": "Halcyon",
     "station": "Estación Prisma",
     "desc": "Capital del Cinturón de Fragmentos, donde los asteroides crecen como cristales.",
     "field": {
      "n": "Cinturón de Fragmentos"
     }
    },
    "jupiter": {
     "n": "Typhon"
    },
    "europa": {
     "n": "Nyx",
     "station": "Colonia Nyx",
     "desc": "Una luna helada de Typhon. La Liga compra iridio a cualquier precio."
    },
    "troyanos": {
     "station": "Depósito del Enjambre",
     "desc": "Rocas atrapadas por la gravedad de Typhon. Nidos piratas por todos lados.",
     "field": {
      "n": "Enjambre de Typhon"
     }
    },
    "saturno": {
     "n": "Aurelia",
     "station": "Depósito Halo",
     "desc": "Un gigante dorado con anillos repletos de Perlas de anillo.",
     "field": {
      "n": "Halo de Aurelia"
     }
    },
    "titan": {
     "n": "Mist",
     "station": "Puerto Bruma",
     "desc": "Una luna neblinosa de Aurelia con enormes refinerías."
    },
    "pluton": {
     "n": "Próxima b",
     "station": "Mercado Rojo",
     "desc": "Un mundo tenue que orbita la enana roja Próxima. Aquí todo está a la venta."
    },
    "kuiper": {
     "n": "Deriva de Próxima",
     "station": "Depósito de la Deriva",
     "desc": "Rocas heladas a la deriva entre las estrellas. Exóticos… y los portanaves del Cártel.",
     "field": {
      "n": "Deriva de Próxima"
     }
    },
    "oort": {
     "n": "La Colmena",
     "station": "Puesto de Vigía Omega",
     "desc": "Una nebulosa viva. Algo enorme se reproduce en sus profundidades.",
     "field": {
      "n": "Nebulosa Colmena"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Tethys"
    },
    "3": {
     "title": "Cinder y Dune",
     "text": "<b>Cinder</b> arde con <b>Piedra solar</b>, pero el calor te devora el casco: compra <b>Escudos</b>. <b>Dune</b> paga una fortuna por el hielo."
    },
    "4": {
     "title": "El Cinturón de Fragmentos",
     "text": "<b>Halcyon</b> y el <b>Cinturón de Fragmentos</b>: asteroides que crecen como <b>cristales</b> y estallan en muchos fragmentos al romperlos. ¡Atrápalos todos! Aquí los piratas son más duros que en casa."
    },
    "6": {
     "title": "Sistema Typhon",
     "text": "<b>Nyx</b> y el <b>Enjambre de Typhon</b>: iridio por todas partes. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Aurelia e influencia",
     "text": "<b>Mist</b> y el dorado <b>Halo de Aurelia</b>. <b>Invierte</b> en estaciones: cada nivel suma <b>+10% de tus ingresos base</b> (mineral, drones, cargueros) e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Alfa Centauri."
    },
    "8": {
     "title": "Próxima",
     "text": "El Mercado Rojo de <b>Próxima b</b> y la <b>Deriva de Próxima</b>. Exóticos e incluso <b>Fragmentos del vacío</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Autopista Cañón de Riel de Tethys",
     "d": "Un cañón de riel que dispara cajas de mineral en un arco perfecto directo a la órbita de Pandora.",
     "fx": "Producción del puesto de Tethys ×3"
    },
    "beacons": {
     "n": "Rutas Honda Binaria",
     "d": "Boyas de navegación que lanzan las naves en efecto honda alrededor de ambos soles a la vez.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Armada de Drones de Cristal",
     "d": "Naves de combate autorreparables cultivadas a partir de cristal vivo. Vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Anillo Orbital de Pandora",
     "d": "No es un solo cable: es un anillo entero alrededor del planeta, con cien ascensores colgando de él.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Siembra Oceánica de Dune",
     "d": "Durante una década, cometas de hielo de la Deriva de Próxima llueven sobre Dune. El desierto se vuelve un archipiélago.",
     "fx": "Dune paga ×2 por todo · reputación con Clanes de Dune +50"
    },
    "gates": {
     "n": "Red de Portales de Fragmentos",
     "d": "Portales de agujero de gusano tallados en cristales gigantes que resuenan por todo el sistema.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Fundición del Halo de Aurelia",
     "d": "Una refinería que orbita dentro del halo dorado, sorbiendo Perlas de anillo como néctar.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Red Dyson de Estrella Doble",
     "d": "Espejos tejidos entre ambos soles. La energía rebota de uno a otro y no deja de crecer.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Lanza Nova Binaria",
     "d": "Ambos soles disparan a través de una sola lente de cristal. Ningún planeta sobrevive.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "eridani": {
   "n": "Épsilon Eridani",
   "intro": "Épsilon Eridani se esconde dentro de un enorme <b>disco de polvo</b>. Muchos de sus asteroides son <b>volátiles</b>: brillan con grietas de magma y <b>explotan</b> al romperse, rompiendo todas las rocas a su alrededor. ¡Provoca reacciones en cadena, pero mantén la distancia!",
   "gate": "La Ciudadela se resquebraja y el polvo se asienta. Bajo sus cimientos, un anillo antiguo <b>cobra vida</b>.",
   "tour": "Un espeso <b>disco de polvo</b> llena todo el sistema. Hasta la guarida corsaria de Snuff se oculta dentro, cerca de la estrella.",
   "signal": {
    "title": "Una fortaleza en el polvo",
    "text": "En lo más profundo del <b>Velo de Polvo</b>, un caudillo pirata construyó la <b>Ciudadela de Polvo</b>: una fortaleza que escupe fuego en todas direcciones. Está justo encima de un portal antiguo."
   },
   "factions": {
    "tierra": {
     "n": "Asamblea del Velo"
    },
    "marte": {
     "n": "Nómadas de Ceniza"
    },
    "cinturon": {
     "n": "Gremio de Dinamiteros"
    },
    "exterior": {
     "n": "Pacto de la Bruma"
    },
    "piratas": {
     "n": "Corsarios del Polvo"
    }
   },
   "locs": {
    "luna": {
     "n": "Kindle",
     "station": "Base Chispa",
     "desc": "Una luna polvorienta de Hearth, salpicada de rocas volátiles.",
     "field": {
      "n": "Campos de Chispas"
     }
    },
    "tierra": {
     "n": "Hearth",
     "station": "Puerto del Velo",
     "desc": "Un mundo oceánico cálido y brumoso bajo un sol ámbar."
    },
    "venus": {
     "n": "Sable",
     "station": "Aguja de Terciopelo",
     "desc": "Un mundo de nubes oscuras como el terciopelo, hogar de nómadas ricos."
    },
    "mercurio": {
     "n": "Fuse",
     "station": "Depósito Fuse",
     "desc": "Un mundo que crepita de calor y mineral volátil.",
     "field": {
      "n": "Llanuras de Fuse"
     }
    },
    "marte": {
     "n": "Ashland",
     "station": "Puerta de Brasas",
     "desc": "Desiertos de ceniza gris y nómadas orgullosos. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Powderkeg",
     "station": "Sede de Dinamiteros",
     "desc": "La capital del Gremio de Dinamiteros. Aquí todo hace ¡bum!",
     "field": {
      "n": "Cinturón de Pólvora"
     }
    },
    "jupiter": {
     "n": "Smolder"
    },
    "europa": {
     "n": "Cinderglass",
     "station": "Colonia de Vidrio",
     "desc": "Una luna helada cubierta de hollín. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Smolder",
     "desc": "Las rocas troyanas de Smolder, muchas de ellas volátiles.",
     "field": {
      "n": "Enjambre de Smolder"
     }
    },
    "saturno": {
     "n": "Veil",
     "station": "Depósito de los Anillos de Veil",
     "desc": "Un gigante con anillos medio oculto en el disco de polvo.",
     "field": {
      "n": "Anillos de Veil"
     }
    },
    "titan": {
     "n": "Murk",
     "station": "Talleres Murk",
     "desc": "Una luna turbia de Veil con refinerías inmensas."
    },
    "pluton": {
     "n": "Snuff",
     "station": "Guarida Corsaria",
     "desc": "Una roca negra como el hollín donde comercian los Corsarios del Polvo."
    },
    "kuiper": {
     "n": "El Velo de Polvo",
     "station": "Depósito del Velo",
     "desc": "El espeso disco de polvo exterior. Hay rocas volátiles a la deriva por todas partes.",
     "field": {
      "n": "El Velo de Polvo"
     }
    },
    "oort": {
     "n": "Confín de la Ciudadela",
     "station": "Puesto Última Chispa",
     "desc": "El corazón del polvo, donde la Ciudadela monta guardia.",
     "field": {
      "n": "Confín de la Ciudadela"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Kindle"
    },
    "3": {
     "title": "Fuse y Ashland",
     "text": "<b>Fuse</b> arde con <b>Piedra solar</b>: compra <b>Escudos</b>. <b>Ashland</b> paga una fortuna por el hielo. Cuidado con las <b>rocas volátiles</b>: ¡explotan al romperse!"
    },
    "4": {
     "title": "El Cinturón de Pólvora",
     "text": "<b>Powderkeg</b> y el <b>Cinturón de Pólvora</b>: un tercio de las rocas son volátiles. Rompe una en un grupo y mira la reacción en cadena."
    },
    "6": {
     "title": "Sistema Smolder",
     "text": "<b>Cinderglass</b> y el <b>Enjambre de Smolder</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Veil e influencia",
     "text": "<b>Murk</b> y los <b>Anillos de Veil</b>. <b>Invierte</b> en estaciones (cada nivel da <b>+10% de ingresos base</b>) para ganar ingresos e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Épsilon Eridani."
    },
    "8": {
     "title": "Snuff",
     "text": "La Guarida Corsaria de <b>Snuff</b> y <b>el Velo de Polvo</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Cinta del Polvo",
     "d": "Una cinta transportadora de 400,000 km que cruza el disco de polvo directo a Hearth.",
     "fx": "Producción del puesto de Kindle ×3"
    },
    "beacons": {
     "n": "Faros Atravesapolvo",
     "d": "Lámparas de neutrinos que ven a través de las nubes de polvo.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Corsarios de la Tormenta de Arena",
     "d": "Expiratas en cañoneras con camuflaje de polvo, ahora en tu nómina. Dos vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Zona Sin Gravedad",
     "d": "Apagas la gravedad sobre una ciudad entera. La carga sube flotando hasta la órbita.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Lavado Planetario",
     "d": "Mil cometas limpian la ceniza de Ashland y dejan atrás un mundo azul.",
     "fx": "Ashland paga ×2 por todo · reputación con Nómadas de Ceniza +50"
    },
    "gates": {
     "n": "Túneles de Polvo",
     "d": "Agujeros de gusano ocultos en las nubes de polvo: solo tus pilotos conocen el camino.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Rueda Cosechadora del Disco",
     "d": "Una rueda del tamaño de una luna rueda por el disco de polvo recogiendo mineral.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Velo Dyson Polvoriento",
     "d": "Conviertes todo el disco de polvo en un panel solar gigante.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Granada Gravitatoria",
     "d": "Un agujero negro de bolsillo, lanzado como granada. Los planetas colapsan sobre sí mismos.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "kepler": {
   "n": "Kepler",
   "intro": "Kepler es un sistema de <b>mundos oceánicos</b> — y sus asteroides están <b>vivos</b>. Las <b>rocas vivas</b> brillan con manchas y nadan de un lado a otro; cuando tu láser las pica, <b>huyen</b>. Persíguelas (¡la Sobremarcha ayuda!) o usa el <b>Pulso tractor (E)</b> para calmarlas unos segundos. Sueltan un <b>60% más de mineral</b>.",
   "gate": "El Kraken se hunde en la oscuridad, dejando un rastro de tinta brillante. En el fondo de la fosa, un anillo antiguo <b>se abre como un ojo</b>.",
   "tour": "Thalassa, Pearlhaze y Undertow son todas <b>lunas del gigante Maelstrom</b> — un pequeño sistema dentro del sistema — y Wreckreef se esconde entre las lunas de Coralring.",
   "signal": {
    "title": "Algo en la fosa",
    "text": "Las tripulaciones pesqueras siguen perdiendo naves cerca de la <b>Fosa del Kraken</b>. La caja negra de la última grabó una sola palabra: <b>tentáculos</b>. Lo que sea que vive ahí abajo está sentado sobre el portal antiguo."
   },
   "factions": {
    "tierra": {
     "n": "República de la Marea"
    },
    "marte": {
     "n": "Clanes de la Sal"
    },
    "cinturon": {
     "n": "Custodios del Arrecife"
    },
    "exterior": {
     "n": "Pacto de Aguas Profundas"
    },
    "piratas": {
     "n": "Marea Negra"
    }
   },
   "locs": {
    "luna": {
     "n": "Shoal",
     "station": "Base Shoal",
     "desc": "Una pequeña luna húmeda de Thalassa. Sus rocas nadan en cardúmenes.",
     "field": {
      "n": "Bajíos de Shoal"
     }
    },
    "tierra": {
     "n": "Thalassa",
     "station": "Puerto Aguas Profundas",
     "desc": "Un mundo sin nada de tierra firme. Las ciudades flotan.",
     "layoutDesc": "Una luna oceánica del gigante Maelstrom. Sin nada de tierra firme: las ciudades flotan."
    },
    "venus": {
     "n": "Pearlhaze",
     "station": "Aguja de Nácar",
     "desc": "Un mundo de nubes resplandecientes. Su gente adora las perlas.",
     "layoutDesc": "Una luna de nubes resplandecientes de Maelstrom. Su gente adora las perlas."
    },
    "mercurio": {
     "n": "Scald",
     "station": "Depósito de los Respiraderos",
     "desc": "Mares hirviendo y géiseres de vapor. Piedra solar bajo la espuma.",
     "field": {
      "n": "Géiseres de Scald"
     }
    },
    "marte": {
     "n": "Saltflat",
     "station": "Puerta de Sal",
     "desc": "El único planeta seco de Kepler — y se muere de sed. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Reef",
     "station": "Bastión del Arrecife",
     "desc": "El hogar de los Custodios del Arrecife, construido dentro de un arrecife vivo gigante.",
     "field": {
      "n": "El Arrecife Vivo"
     }
    },
    "jupiter": {
     "n": "Maelstrom"
    },
    "europa": {
     "n": "Undertow",
     "station": "Colonia Undertow",
     "desc": "Una luna helada sobre un océano cálido y oculto. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Maelstrom",
     "desc": "Los troyanos de Maelstrom, donde las rocas vivas se reúnen a comer.",
     "field": {
      "n": "Bancos de Maelstrom"
     }
    },
    "saturno": {
     "n": "Coralring",
     "station": "Depósito del Anillo de Coral",
     "desc": "Un gigante cuyos anillos están hechos de algo parecido al coral.",
     "field": {
      "n": "Anillos de Coral"
     }
    },
    "titan": {
     "n": "Kelpmire",
     "station": "Planta de Algas",
     "desc": "Una luna cubierta de bosques de algas flotantes y refinerías."
    },
    "pluton": {
     "n": "Wreckreef",
     "station": "Gruta del Contrabandista",
     "desc": "Un arrecife de naves hundidas donde comercia la Marea Negra."
    },
    "kuiper": {
     "n": "El Abismo",
     "station": "Boya del Abismo",
     "desc": "Un mar oscuro de roca en el borde del sistema. Aquí nadan cosas grandes.",
     "field": {
      "n": "El Abismo"
     }
    },
    "oort": {
     "n": "Fosa del Kraken",
     "station": "Última Boya",
     "desc": "Una fosa en el espacio. Algo con tentáculos vive en el fondo.",
     "field": {
      "n": "Fosa del Kraken"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Shoal"
    },
    "3": {
     "title": "Scald y Saltflat",
     "text": "<b>Scald</b> hierve de <b>Piedra solar</b> — compra <b>Escudos</b>. <b>Saltflat</b> paga una fortuna por el hielo. Algunas rocas aquí están <b>vivas</b>: huyen cuando les disparas el láser, pero sueltan un 60% más de mineral."
    },
    "4": {
     "title": "El Arrecife Vivo",
     "text": "<b>Reef</b> y <b>El Arrecife Vivo</b>: casi un tercio de las rocas nadan. Cálmalas con el <b>Pulso tractor (E)</b> y córtalas mientras están quietas."
    },
    "6": {
     "title": "Sistema Maelstrom",
     "text": "<b>Undertow</b> y los <b>Bancos de Maelstrom</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Coralring e influencia",
     "text": "<b>Kelpmire</b> y los <b>Anillos de Coral</b>. <b>Invierte</b> para ganar <b>+10% de ingresos</b> e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Kepler."
    },
    "8": {
     "title": "Wreckreef",
     "text": "La Gruta del Contrabandista de <b>Wreckreef</b> y <b>El Abismo</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Manada de Rocas Domadas",
     "d": "Silbas, y una manada de rocas vivas lleva tu mineral a casa nadando, sola.",
     "fx": "Producción del puesto de Shoal ×3"
    },
    "beacons": {
     "n": "Rutas de Plancton Brillante",
     "d": "Siembras las rutas comerciales con plancton brillante. Las naves solo siguen las luces.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Banco de Cañoneras de Coral",
     "d": "Cañoneras vivas cultivadas con coral del arrecife. Cazan en parejas — dos vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Lanzador Géiser",
     "d": "Tapas el géiser más grande de Scald. Cada pocos minutos lanza una bodega llena a la órbita.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Océano en Caída",
     "d": "Dejas caer un océano entero sobre Saltflat. Llega como un cometa muy grande y muy mojado.",
     "fx": "Saltflat paga ×2 por todo · reputación con Clanes de la Sal +50"
    },
    "gates": {
     "n": "Portales Remolino",
     "d": "Le enseñas a Maelstrom a girar agujeros de gusano. Te zambulles y sales en cualquier parte.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Arrecife del Anillo de Coral",
     "d": "Cultivas un arrecife vivo que rodea todo Coralring. Se come los asteroides y escupe mineral puro.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Mar Soleado",
     "d": "Una capa de agua alrededor de la estrella: un océano del tamaño de un sistema solar, rebosante de luz.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Cañón Tsunami",
     "d": "Disparas una ola de océano comprimido. No se detiene en la superficie del planeta.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "orion": {
   "n": "Nebulosa de Orión",
   "intro": "La <b>Nebulosa de Orión</b> es un vivero donde nacen nuevas estrellas. Muchos asteroides aquí son <b>magnéticos</b>: poco a poco <b>se juntan en grupos</b> — perfectos para tus Cargas y tu Rayo ancho. Cuando una roca magnética se rompe, lanza un <b>pulso magnético</b> que atrae cada trozo de mineral cercano directo a tu nave.",
   "gate": "La última cabeza de la Hidra se disuelve en gas brillante. De las estrellas recién nacidas, un anillo antiguo <b>toma forma</b>.",
   "tour": "Mundos recién nacidos en <b>órbitas salvajes y estiradas</b> dentro de nubes brillantes; los cinturones todavía se están agrupando.",
   "signal": {
    "title": "Tres cabezas en la nube",
    "text": "En lo profundo de la nebulosa, algo con <b>tres cabezas brillantes</b> custodia el viejo portal en <b>La Cuna de la Hidra</b>. La Unión de Lodestone advierte: <b>si la cortas, se divide en dos</b>."
   },
   "factions": {
    "tierra": {
     "n": "Consejo del Vivero"
    },
    "marte": {
     "n": "Guardia de Trapezium"
    },
    "cinturon": {
     "n": "Unión de Lodestone"
    },
    "exterior": {
     "n": "Errantes de la Nebulosa"
    },
    "piratas": {
     "n": "Lobos del Velo"
    }
   },
   "locs": {
    "luna": {
     "n": "Cradle",
     "station": "Base Cradle",
     "desc": "Una luna helada envuelta en gas rosado de la nebulosa.",
     "field": {
      "n": "Deriva de Cradle"
     }
    },
    "tierra": {
     "n": "Bloom",
     "station": "Puerto Bloom",
     "desc": "Un mundo oceánico bajo cielos llenos de estrellas bebé."
    },
    "venus": {
     "n": "Rosette",
     "station": "Aguja Rosette",
     "desc": "Un mundo de nubes color rosa. Muy elegante."
    },
    "mercurio": {
     "n": "Protostar",
     "station": "Depósito Ignición",
     "desc": "Un planeta que orbita una estrella que todavía está naciendo.",
     "field": {
      "n": "Llanuras de Ignición"
     }
    },
    "marte": {
     "n": "Trapezium",
     "station": "Puerta Trapezium",
     "desc": "Un mundo fortaleza iluminado por cuatro estrellas jóvenes y brillantes. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Lodestone",
     "station": "Salón del Imán",
     "desc": "Un imán gigante en el espacio. Aquí las brújulas solo giran.",
     "field": {
      "n": "El Cinturón de Lodestone"
     }
    },
    "jupiter": {
     "n": "Horsehead"
    },
    "europa": {
     "n": "Mane",
     "station": "Colonia Mane",
     "desc": "Una luna de hielo a la sombra de Horsehead. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Horsehead",
     "desc": "Rocas magnéticas dando tumbos a la sombra de Horsehead.",
     "field": {
      "n": "Enjambre de Horsehead"
     }
    },
    "saturno": {
     "n": "Pillar",
     "station": "Depósito Anillo Pillar",
     "desc": "Un gigante dentro de un pilar de gas brillante.",
     "field": {
      "n": "Anillos de Pillar"
     }
    },
    "titan": {
     "n": "Glowworm",
     "station": "Talleres Luminosos",
     "desc": "Una luna que brilla con un verde tenue de noche."
    },
    "pluton": {
     "n": "Shadowveil",
     "station": "Guarida del Lobo",
     "desc": "Escondido en una nube oscura. Aquí viven los Lobos del Velo."
    },
    "kuiper": {
     "n": "El Borde del Vivero",
     "station": "Depósito del Borde",
     "desc": "Donde la nebulosa se diluye en el espacio oscuro.",
     "field": {
      "n": "El Borde del Vivero"
     }
    },
    "oort": {
     "n": "La Cuna de la Hidra",
     "station": "Puesto Luz Estelar",
     "desc": "Una nube de estrellas recién nacidas — y un guardián de tres cabezas.",
     "field": {
      "n": "La Cuna de la Hidra"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Cradle"
    },
    "3": {
     "title": "Protostar y Trapezium",
     "text": "<b>Protostar</b> arde — compra <b>Escudos</b>. <b>Trapezium</b> paga una fortuna por el hielo. Las <b>rocas magnéticas</b> se juntan en grupos: ¡reviéntalas con Cargas!"
    },
    "4": {
     "title": "El Cinturón de Lodestone",
     "text": "<b>Lodestone</b> y su cinturón: un tercio de las rocas son magnéticas. Rompe una y cada trozo de mineral cercano vuela hacia ti."
    },
    "6": {
     "title": "Sistema Horsehead",
     "text": "<b>Mane</b> y el <b>Enjambre de Horsehead</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Pillar e influencia",
     "text": "<b>Glowworm</b> y los <b>Anillos de Pillar</b>. <b>Invierte</b> para ganar <b>+10% de ingresos</b> e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar la Nebulosa de Orión."
    },
    "8": {
     "title": "Shadowveil",
     "text": "La Guarida del Lobo de <b>Shadowveil</b> y <b>el Borde del Vivero</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Ferrocarril Magnético",
     "d": "Una vía de imanes tan potentes que tu mineral se desliza solito hasta casa.",
     "fx": "Producción del puesto de Cradle ×3"
    },
    "beacons": {
     "n": "Balizas Nacestrellas",
     "d": "Iluminas las rutas con estrellas bebé. Son muy brillantes y algo ruidosas.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Manada de la Nebulosa",
     "d": "Domas las naves más rápidas de los Lobos del Velo. Dos cazan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Elevador Magnético",
     "d": "Dos imanes gigantes, uno en tierra y otro en órbita. Activas el interruptor y la carga sube.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Jardín Vivero Estelar",
     "d": "Plantas una estrella bebé junto a Trapezium. Ahora tiene estaciones, lluvia y flores.",
     "fx": "Trapezium paga ×2 por todo · reputación con Guardia de Trapezium +50"
    },
    "gates": {
     "n": "Pliegues Nebulares",
     "d": "Doblas la nebulosa como un mapa para que dos lugares cualesquiera se toquen.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Halo de Lodestone",
     "d": "Un imán en forma de anillo alrededor de Pillar atrae mineral de toda la nebulosa.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Granja de Estrellas",
     "d": "¿Para qué usar una sola estrella? Cultivas un campo entero y cosechas su luz.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Cañón de Semillas Estelares",
     "d": "Le disparas una estrella bebé a un planeta. Crece muy rápido.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "pulsar": {
   "n": "El Púlsar",
   "intro": "<b>El Púlsar</b> es una estrella muerta que gira cientos de veces por segundo. Cada pocos segundos su <b>haz barre tu campo</b>: las rocas que toca quedan <b>cargadas</b> (×2 de mineral por un rato), pero también te quema el casco. Los Jinetes del Haz te dan el <b>Cambio de fase</b>: pulsa <b>X</b> (o FASE) para volverte un fantasma por 3 s — sin daño, y atraviesas las rocas. ¡Surfea el haz! Es tuyo para siempre.",
   "gate": "El Guardián deja de girar y se apaga. En el repentino silencio, un anillo antiguo <b>empieza a hacer tictac</b>.",
   "tour": "Sus mundos orbitan como un <b>reloj perfecto</b>: órbitas redondas y equidistantes, como las marcas de una esfera — mientras los haces del púlsar las barren.",
   "signal": {
    "title": "El guardián del faro",
    "text": "En el corazón del haz del Púlsar se alza el <b>Guardián del Púlsar</b> — una estación giratoria con dos brazos de luz pura. <b>Aléjate de sus brazos</b>, o atraviésalos en fase."
   },
   "factions": {
    "tierra": {
     "n": "Asamblea del Faro"
    },
    "marte": {
     "n": "Clanes de Tick"
    },
    "cinturon": {
     "n": "Jinetes del Haz"
    },
    "exterior": {
     "n": "Coro Silencioso"
    },
    "piratas": {
     "n": "Asaltantes de la Estática"
    }
   },
   "locs": {
    "luna": {
     "n": "Tick",
     "station": "Base Tick",
     "desc": "Una luna que destella cada vez que pasa el haz.",
     "field": {
      "n": "Campos de Tick"
     }
    },
    "tierra": {
     "n": "Metronome",
     "station": "Puerto Baliza",
     "desc": "Un mundo donde todos viven al ritmo del haz. Gente muy puntual."
    },
    "venus": {
     "n": "Chime",
     "station": "Aguja Chime",
     "desc": "Sus nubes suenan como campanas cuando el haz las golpea."
    },
    "mercurio": {
     "n": "Flash",
     "station": "Depósito Flash",
     "desc": "Justo al lado del haz. Trae escudos.",
     "field": {
      "n": "Llanuras de Flash"
     }
    },
    "marte": {
     "n": "Echo",
     "station": "Puerta Echo",
     "desc": "Un desierto silencioso donde resuena cada pulso. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Strobe",
     "station": "Salón del Haz",
     "desc": "El hogar de los Jinetes del Haz. Sincronizan todo con el pulso.",
     "field": {
      "n": "El Cinturón de Strobe"
     }
    },
    "jupiter": {
     "n": "Gyre"
    },
    "europa": {
     "n": "Hush",
     "station": "Colonia Hush",
     "desc": "El único lugar tranquilo del sistema. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Gyre",
     "desc": "Los troyanos de Gyre, chisporroteando de estática.",
     "field": {
      "n": "Enjambre de Gyre"
     }
    },
    "saturno": {
     "n": "Spindle",
     "station": "Depósito Anillo Spindle",
     "desc": "Un gigante cuyos anillos giran al compás del púlsar.",
     "field": {
      "n": "Anillos de Spindle"
     }
    },
    "titan": {
     "n": "Cog",
     "station": "Talleres Cog",
     "desc": "Una luna de fábricas de relojería."
    },
    "pluton": {
     "n": "Static",
     "station": "Mercado Static",
     "desc": "Donde los Asaltantes de la Estática venden lo que roban."
    },
    "kuiper": {
     "n": "El Confín Silencioso",
     "station": "Depósito del Confín",
     "desc": "Lejos del haz, pero nunca del todo fuera de él.",
     "field": {
      "n": "El Confín Silencioso"
     }
    },
    "oort": {
     "n": "El Faro del Guardián",
     "station": "Puesto Punto Ciego",
     "desc": "El centro del haz, donde gira el Guardián.",
     "field": {
      "n": "El Faro del Guardián"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Tick"
    },
    "3": {
     "title": "Flash y Echo",
     "text": "<b>Flash</b> está en pleno haz — compra <b>Escudos</b>. <b>Echo</b> paga una fortuna por el hielo. Cuando pase el haz, pulsa <b>X</b> para usar el <b>Cambio de fase</b>, atravesarlo y minar las rocas cargadas."
    },
    "4": {
     "title": "El Cinturón de Strobe",
     "text": "<b>Strobe</b> y el <b>Cinturón de Strobe</b>. Las rocas cargadas sueltan el doble de mineral — sincroniza tu minería con el pulso."
    },
    "6": {
     "title": "Sistema Gyre",
     "text": "<b>Hush</b> y el <b>Enjambre de Gyre</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Spindle e influencia",
     "text": "<b>Cog</b> y los <b>Anillos de Spindle</b>. <b>Invierte</b> para ganar <b>+10% de ingresos</b> e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar el Púlsar."
    },
    "8": {
     "title": "Static",
     "text": "El mercado de <b>Static</b> y <b>el Confín Silencioso</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Catapulta de Pulsos",
     "d": "La carga sale disparada con cada pulso — 700 veces por segundo.",
     "fx": "Producción del puesto de Tick ×3"
    },
    "beacons": {
     "n": "Rutas de Relojería",
     "d": "Cada nave se mueve exactamente al ritmo del púlsar. Nadie vuelve a llegar tarde.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Escuadrón Estroboscópico",
     "d": "Naves de combate que solo existen entre pulsos. Los piratas no pueden darle a lo que no está. Dos vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Elevador de Haz",
     "d": "Estacionas la carga en el haz del púlsar y sale catapultada a la órbita.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Reloj Planetario",
     "d": "Frenas el giro de Echo hasta unas 24 horas perfectas. Resulta que era todo lo que necesitaba.",
     "fx": "Echo paga ×2 por todo · reputación con Clanes de Tick +50"
    },
    "gates": {
     "n": "Portales de Instante",
     "d": "Sales de un pulso y entras en el siguiente — en otro lugar.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Fundición del Anillo Giratorio",
     "d": "Los anillos de Spindle giran tan rápido que clasifican el mineral por peso solitos.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Dínamo de Neutrones",
     "d": "Le pones un generador a lo que gira más rápido en toda la galaxia.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Lanza del Púlsar",
     "d": "Apuntas el púlsar. Solo una vez. Solo un poquito.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "rigel": {
   "n": "Rigel",
   "intro": "Rigel es una <b>supergigante azul</b>, tan brillante que ilumina todo el cielo. Su calor hornea <b>geodas</b> ocultas dentro de algunos asteroides. Los Talladores de Geodas te dan el <b>Escáner profundo</b>: pulsa <b>C</b> (o ESCANEAR) para lanzar una onda que muestra todas las geodas cercanas. Rompe una geoda y obtén una <b>enorme carga del mejor mineral del campo</b>. Es tuyo para siempre.",
   "gate": "El Titán Radiante se agrieta y su luz se derrama como agua. En medio del resplandor, un anillo antiguo <b>se enfoca hasta volverse un portal</b>.",
   "tour": "Rigel es <b>enorme</b> — tan grande y brillante que sus mundos guardan la distancia.",
   "signal": {
    "title": "Un gigante hecho de luz",
    "text": "Algo se alza en <b>La Grieta Radiante</b>: un gigante de cristal que arde más que la estrella. Las naves que se acercan ven una fina línea azul… y luego nada. <b>Atento a la línea y esquiva.</b>"
   },
   "factions": {
    "tierra": {
     "n": "Concordia de Rigel"
    },
    "marte": {
     "n": "Gremio del Prisma"
    },
    "cinturon": {
     "n": "Talladores de Geodas"
    },
    "exterior": {
     "n": "Unión del Halo"
    },
    "piratas": {
     "n": "Asaltantes del Resplandor"
    }
   },
   "locs": {
    "luna": {
     "n": "Glint",
     "station": "Base Glint",
     "desc": "Una luna helada que destella como una bola de espejos.",
     "field": {
      "n": "Campos de Glint"
     }
    },
    "tierra": {
     "n": "Bluehaven",
     "station": "Puerto Halo",
     "desc": "Un mundo azul bajo un sol azul. Todos usan lentes de sol."
    },
    "venus": {
     "n": "Sapphire",
     "station": "Aguja de Zafiro",
     "desc": "Un mundo de nubes azul profundo, rico y orgulloso."
    },
    "mercurio": {
     "n": "Searlight",
     "station": "Depósito Llamarada",
     "desc": "Calcinado hasta el blanco por Rigel. Platino y geodas por todas partes.",
     "field": {
      "n": "Llanuras Abrasadoras"
     }
    },
    "marte": {
     "n": "Prism",
     "station": "Puerta Prism",
     "desc": "Un desierto vidrioso que descompone la luz en arcoíris. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Quarry",
     "station": "Salón de las Geodas",
     "desc": "La capital de los Talladores de Geodas. Aquí cada roca ya fue abierta.",
     "field": {
      "n": "El Cinturón de Geodas"
     }
    },
    "jupiter": {
     "n": "Behemoth"
    },
    "europa": {
     "n": "Frostlight",
     "station": "Colonia Frostlight",
     "desc": "Una luna helada que brilla de noche. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Behemoth",
     "desc": "Los troyanos de Behemoth, repletos de geodas.",
     "field": {
      "n": "Enjambre de Behemoth"
     }
    },
    "saturno": {
     "n": "Halo",
     "station": "Depósito del Anillo Halo",
     "desc": "Un gigante con anillos tan brillantes que proyectan sombras.",
     "field": {
      "n": "Anillos de Halo"
     }
    },
    "titan": {
     "n": "Lumen",
     "station": "Planta Lumen",
     "desc": "Una luna pálida de refinerías que funcionan con luz estelar."
    },
    "pluton": {
     "n": "Umbra",
     "station": "Mercado de las Sombras",
     "desc": "El único lugar oscuro de Rigel. A los Asaltantes del Resplandor les encanta."
    },
    "kuiper": {
     "n": "Confín de Rigel",
     "station": "Depósito del Confín",
     "desc": "El límite lejano del resplandor de Rigel, lleno de geodas.",
     "field": {
      "n": "Confín de Rigel"
     }
    },
    "oort": {
     "n": "La Grieta Radiante",
     "station": "Puesto Sombra",
     "desc": "Una grieta de luz pura donde un gigante de cristal hace guardia.",
     "field": {
      "n": "La Grieta Radiante"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Glint"
    },
    "3": {
     "title": "Searlight y Prism",
     "text": "<b>Searlight</b> está calcinado hasta el blanco — compra <b>Escudos</b>. <b>Prism</b> paga una fortuna por el hielo. ¡Pulsa <b>C</b> para usar el <b>Escáner profundo</b> y hallar geodas ocultas!"
    },
    "4": {
     "title": "El Cinturón de Geodas",
     "text": "<b>Quarry</b> y <b>El Cinturón de Geodas</b>: una de cada cinco rocas esconde una geoda. Escanea y luego ábrelas."
    },
    "6": {
     "title": "Sistema Behemoth",
     "text": "<b>Frostlight</b> y el <b>Enjambre de Behemoth</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Halo e influencia",
     "text": "<b>Lumen</b> y los <b>Anillos de Halo</b>. <b>Invierte</b> para ganar <b>+10% de ingresos</b> e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Rigel."
    },
    "8": {
     "title": "Umbra",
     "text": "El Mercado de las Sombras de <b>Umbra</b> y el <b>Confín de Rigel</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Carga a Vela Fotónica",
     "d": "La luz de Rigel es tan fuerte que basta con ponerle velas a la carga y dejar que el viento la lleve a casa.",
     "fx": "Producción del puesto de Glint ×3"
    },
    "beacons": {
     "n": "Relé de Espejos",
     "d": "Espejos gigantes hacen rebotar tus naves por todo el sistema. Llegan un poco bronceadas.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Lanceros del Prisma",
     "d": "Cañoneras con cascos de cristal que dividen cada disparo en un arcoíris. Dos vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Elevador de Presión Lumínica",
     "d": "Cápsulas de carga con panza de espejo. Apúntalas a Rigel y caen hacia arriba.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Parasol Continental",
     "d": "Una sombrilla del tamaño de un continente convierte a Prism de desierto vidrioso en pradera.",
     "fx": "Prism paga ×2 por todo · reputación con Gremio del Prisma +50"
    },
    "gates": {
     "n": "Portales de Luz",
     "d": "Conviertes tus naves en luz, las transmites a través del sistema y las vuelves a armar. Casi iguales.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Anillo de Fundición de Halo",
     "d": "La luz estelar concentrada funde asteroides en un río brillante de mineral que corre por los anillos de Halo.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Lente Supergigante",
     "d": "Una lente más ancha que la órbita de un planeta enfoca una supergigante azul directo a tu cuenta bancaria.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Lanza de Rigel",
     "d": "Concentras la Lente Supergigante en un solo rayo. Los planetas nunca saben qué los golpeó.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "rim": {
   "n": "Borde del Núcleo",
   "intro": "El <b>Borde del Núcleo</b> es la orilla del centro de la galaxia, lleno de ruinas de una civilización perdida. Algunos asteroides son <b>reliquias antiguas</b>, cubiertas de glifos brillantes. Rompe una para liberar un <b>poder de reliquia</b> durante 25 s: doble mineral, un imán gigante, un súper láser o todas tus herramientas recargadas de golpe.",
   "gate": "El Arconte se inclina y su luz se apaga. El portal más antiguo de la galaxia <b>se abre</b>… y apunta directo al agujero negro.",
   "tour": "Un <b>anillo dorado construido por los antiguos</b> rodea toda la estrella, y Ringwork viaja justo sobre él.",
   "signal": {
    "title": "El último guardián",
    "text": "En el <b>Portal del Arconte</b> una máquina antigua sigue montando guardia: <b>el Arconte</b>. Se esconde tras <b>fragmentos de escudo</b>: destruye primero los fragmentos y luego ataca."
   },
   "factions": {
    "tierra": {
     "n": "Concordato del Borde"
    },
    "marte": {
     "n": "Guardianes de Reliquias"
    },
    "cinturon": {
     "n": "Excavadores de Glifos"
    },
    "exterior": {
     "n": "Peregrinos de la Luz Antigua"
    },
    "piratas": {
     "n": "Saqueadores de Tumbas"
    }
   },
   "locs": {
    "luna": {
     "n": "Shard",
     "station": "Excavación Uno",
     "desc": "Una luna cubierta de ruinas antiguas. Cualquier roca podría ser una reliquia.",
     "field": {
      "n": "Primera Excavación"
     }
    },
    "tierra": {
     "n": "Elder",
     "station": "Puerto Elder",
     "desc": "Un apacible mundo oceánico construido sobre ciudades antiguas."
    },
    "venus": {
     "n": "Gilt",
     "station": "Aguja Gilt",
     "desc": "Un mundo dorado de nubes. Aquí los ricos coleccionan reliquias."
    },
    "mercurio": {
     "n": "Kiln",
     "station": "Depósito Kiln",
     "desc": "Un mundo ardiente donde los antiguos forjaban sus máquinas.",
     "field": {
      "n": "Llanuras de Kiln"
     }
    },
    "marte": {
     "n": "Obelisk",
     "station": "Puerta Obelisk",
     "desc": "Un desierto de obeliscos negros gigantes. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Vault",
     "station": "Salón de los Glifos",
     "desc": "La ciudad de los Excavadores de Glifos, tallada dentro de una bóveda antigua.",
     "field": {
      "n": "El Cinturón de Vault"
     }
    },
    "jupiter": {
     "n": "Colossus Prime"
    },
    "europa": {
     "n": "Rune",
     "station": "Colonia Rune",
     "desc": "Los glifos brillan bajo el hielo. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Prime",
     "desc": "Rocas troyanas llenas de maquinaria antigua.",
     "field": {
      "n": "Enjambre de Ruinas"
     }
    },
    "saturno": {
     "n": "Ringwork",
     "station": "Depósito Ringwork",
     "desc": "Sus anillos no son naturales. Alguien los construyó.",
     "field": {
      "n": "Anillos de Ringwork"
     }
    },
    "titan": {
     "n": "Archive",
     "station": "Talleres Archive",
     "desc": "Una biblioteca del tamaño de una luna, ahora convertida en refinería."
    },
    "pluton": {
     "n": "Crypt",
     "station": "Mercado de Tumbas",
     "desc": "Los Saqueadores de Tumbas venden aquí reliquias robadas."
    },
    "kuiper": {
     "n": "El Cementerio",
     "station": "Depósito del Cementerio",
     "desc": "Un cementerio de naves antiguas, saqueado hasta los huesos… casi.",
     "field": {
      "n": "El Cementerio"
     }
    },
    "oort": {
     "n": "Portal del Arconte",
     "station": "Puesto de la Última Lámpara",
     "desc": "El portal más antiguo de la galaxia y su último guardián.",
     "field": {
      "n": "Portal del Arconte"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Shard"
    },
    "3": {
     "title": "Kiln y Obelisk",
     "text": "<b>Kiln</b> quema: compra <b>Escudos</b>. <b>Obelisk</b> paga una fortuna por el hielo. Las rocas con glifos brillantes son <b>reliquias</b>: ¡rómpelas para obtener un poder!"
    },
    "4": {
     "title": "El Cinturón de Vault",
     "text": "<b>Vault</b> y el <b>Cinturón de Vault</b>: una de cada cuatro rocas es una reliquia."
    },
    "6": {
     "title": "Sistema Colossus Prime",
     "text": "<b>Rune</b> y el <b>Enjambre de Ruinas</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Ringwork e influencia",
     "text": "<b>Archive</b> y los <b>Anillos de Ringwork</b>. <b>Invierte</b> para ganar <b>+10% de ingresos</b> e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar el Borde del Núcleo."
    },
    "8": {
     "title": "Crypt",
     "text": "El Mercado de Tumbas de <b>Crypt</b> y <b>el Cementerio</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Transportador Antiguo",
     "d": "Encuentras el sistema de carga de los antiguos. Todavía funciona. Te estaba esperando.",
     "fx": "Producción del puesto de Shard ×3"
    },
    "beacons": {
     "n": "Rutas de Glifos",
     "d": "Enciendes los viejos glifos. Brillan a lo largo de cada ruta, marcando el camino.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Centinelas Despertados",
     "d": "Dos antiguas máquinas guardianas deciden que les caes bien. Vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Ascensor Obelisco",
     "d": "Resulta que los obeliscos son ascensores. ¿Quién lo diría?",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Máquina Jardín",
     "d": "Una máquina antigua que convierte desiertos en selvas. Aprietas el botón grande.",
     "fx": "Obelisk paga ×2 por todo · reputación con Guardianes de Reliquias +50"
    },
    "gates": {
     "n": "La Vieja Red",
     "d": "Reconectas la red de portales de los antiguos. Llega a todas partes.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Reactivación de Ringwork",
     "d": "Reactivas los anillos artificiales de Ringwork. Siempre fueron máquinas mineras.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "La Esfera de los Antiguos",
     "d": "Terminas la esfera de Dyson que los antiguos dejaron a medias hace un millón de años.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Borrador de Mundos",
     "d": "La razón por la que desaparecieron los antiguos. Por favor, úsalo con cuidado.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "sgra": {
   "n": "Sagitario A*",
   "intro": "<b>Sagitario A*</b>: el agujero negro supermasivo en el centro de la Vía Láctea. Su <b>gravedad atrae todo</b>: tu nave, las rocas, el mineral. Las rocas flotan hacia el agujero negro y son tragadas, así que mina rápido y no te acerques demasiado al <b>horizonte de eventos</b>, en la parte superior de cada campo. Este es el último sistema. Termínalo y habrás cruzado la galaxia.",
   "gate": "El Devorador cae en el agujero negro del que se alimentaba. El centro de la galaxia está en calma. <b>Lo lograste.</b>",
   "tour": "Todo <b>gira en espiral hacia dentro</b>: órbitas rápidas y estiradas, y brazos de gas brillante cayendo hacia el agujero negro.",
   "signal": {
    "title": "Algo se está comiendo la luz",
    "text": "En el <b>Horizonte de Eventos</b> vive el <b>Devorador</b>, una criatura que se alimenta del propio agujero negro. Su gravedad <b>te arrastra</b>. Este es el último combate de la galaxia."
   },
   "factions": {
    "tierra": {
     "n": "República del Núcleo"
    },
    "marte": {
     "n": "Monjes del Horizonte"
    },
    "cinturon": {
     "n": "Mineros de la Espiral"
    },
    "exterior": {
     "n": "Última Frontera"
    },
    "piratas": {
     "n": "Saqueadores del Vacío"
    }
   },
   "locs": {
    "luna": {
     "n": "Spark",
     "station": "Base del Abismo",
     "desc": "Una pequeña luna justo al borde del abismo.",
     "field": {
      "n": "Campos del Abismo"
     }
    },
    "tierra": {
     "n": "Haven Core",
     "station": "Puerto del Núcleo",
     "desc": "La capital del centro de la galaxia. El cielo está lleno de estrellas."
    },
    "venus": {
     "n": "Radiance",
     "station": "Aguja Radiance",
     "desc": "Un mundo de nubes iluminado por el resplandeciente disco de acreción."
    },
    "mercurio": {
     "n": "Swirl",
     "station": "Depósito Swirl",
     "desc": "Un planeta que cae lentamente en espiral. Caliente y rico.",
     "field": {
      "n": "Llanuras de Swirl"
     }
    },
    "marte": {
     "n": "Stillness",
     "station": "Puerta de los Monjes",
     "desc": "Los Monjes del Horizonte meditan aquí, contemplando el agujero negro. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Spiral",
     "station": "Salón de la Espiral",
     "desc": "Los Mineros de la Espiral persiguen el mineral mientras cae hacia dentro.",
     "field": {
      "n": "El Cinturón de la Espiral"
     }
    },
    "jupiter": {
     "n": "Maw"
    },
    "europa": {
     "n": "Drift",
     "station": "Colonia Drift",
     "desc": "Una luna de hielo estirada como un huevo por la gravedad. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Maw",
     "desc": "Rocas que caen en una espiral larga y lenta.",
     "field": {
      "n": "Enjambre de Maw"
     }
    },
    "saturno": {
     "n": "Disk",
     "station": "Depósito Disk",
     "desc": "Un gigante que roza el borde del disco de acreción.",
     "field": {
      "n": "Los Anillos de Acreción"
     }
    },
    "titan": {
     "n": "Lantern",
     "station": "Talleres Lantern",
     "desc": "Una luna que brilla con la luz del disco."
    },
    "pluton": {
     "n": "Edge",
     "station": "Último Mercado",
     "desc": "El último mercado antes del abismo. Los Saqueadores del Vacío comercian aquí."
    },
    "kuiper": {
     "n": "El Disco de Acreción",
     "station": "Depósito del Borde del Disco",
     "desc": "Un río de roca incandescente que se vierte en el agujero negro.",
     "field": {
      "n": "El Disco de Acreción"
     }
    },
    "oort": {
     "n": "Horizonte de Eventos",
     "station": "Punto Sin Retorno",
     "desc": "El borde del agujero negro. Aquí se alimenta el Devorador.",
     "field": {
      "n": "Horizonte de Eventos"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Spark"
    },
    "3": {
     "title": "Swirl y Stillness",
     "text": "<b>Swirl</b> quema: compra <b>Escudos</b>. <b>Stillness</b> paga una fortuna por el hielo. Ojo con la <b>gravedad</b>: todo flota hacia el agujero negro."
    },
    "4": {
     "title": "El Cinturón de la Espiral",
     "text": "<b>Spiral</b> y el <b>Cinturón de la Espiral</b>. Las rocas que llegan al horizonte de eventos se pierden para siempre: atrápalas antes."
    },
    "6": {
     "title": "Sistema Maw",
     "text": "<b>Drift</b> y el <b>Enjambre de Maw</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Disk e influencia",
     "text": "<b>Lantern</b> y los <b>Anillos de Acreción</b>. <b>Invierte</b> para ganar <b>+10% de ingresos</b> e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar el centro de la galaxia."
    },
    "8": {
     "title": "Edge",
     "text": "El Último Mercado de <b>Edge</b> y <b>el Disco de Acreción</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Honda Gravitatoria",
     "d": "Sueltas el mineral y dejas que el agujero negro lo lance a casa. ¡Física!",
     "fx": "Producción del puesto de Spark ×3"
    },
    "beacons": {
     "n": "Rutas de Dilatación Temporal",
     "d": "Cerca del agujero negro, el tiempo se frena. Tus viajes duran siglos… para todos los demás.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Guardia del Horizonte",
     "d": "Monjes en cañoneras, perfectamente serenos, perfectamente certeros. Dos vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Ascensor de Arrastre",
     "d": "El agujero negro hace girar el propio espacio. Tu carga sube a la órbita montada en ese giro.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Invernadero Hawking",
     "d": "El cálido brillo del agujero negro convierte Stillness en un jardín. Los monjes lo aprueban.",
     "fx": "Stillness paga ×2 por todo · reputación con Monjes del Horizonte +50"
    },
    "gates": {
     "n": "Red de Agujeros de Gusano",
     "d": "Atas agujeros de gusano al giro del agujero negro. Llegan a cualquier punto de la galaxia.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Molino de Acreción",
     "d": "Una rueda en el disco de acreción atrapa el mineral que cae antes de que se pierda.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Motor de Penrose",
     "d": "Lanzas chatarra a un agujero negro giratorio y la atrapas de vuelta con más energía. Energía infinita.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Singularidad de Bolsillo",
     "d": "Un agujero negro diminuto en una caja. Ábrela con cuidado.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "sirius": {
   "n": "Sirio",
   "intro": "Sirio brilla el doble que el Sol. Sus asteroides son <b>blindados</b>: corazas de metal forjadas al calor que tu láser apenas raya. Cambia al <b>Taladro (Q)</b> para partirlas.",
   "gate": "La Serpiente se deshace en chispas. Donde anidaba, un anillo antiguo <b>arde al rojo blanco</b> y se abre.",
   "tour": "La estrella más brillante del cielo. Sus mundos orbitan muy lejos, y el cinturón de Ironheart es <b>un anillo alrededor del gigante Argent</b>.",
   "signal": {
    "title": "Algo vive en las llamaradas",
    "text": "Naves cerca del <b>Confín de las Llamaradas</b> reportan una figura que nada entre las tormentas solares: una cinta de fuego viva. La llaman la <b>Serpiente Solar</b>."
   },
   "factions": {
    "tierra": {
     "n": "Directorio Siriano"
    },
    "marte": {
     "n": "Clanes de Canis"
    },
    "cinturon": {
     "n": "Coro de Hierro"
    },
    "exterior": {
     "n": "Liga de Lumen"
    },
    "piratas": {
     "n": "Saqueadores de Dogstar"
    }
   },
   "locs": {
    "luna": {
     "n": "Glint",
     "station": "Base Glint",
     "desc": "Una luna brillante y vítrea de Lumen.",
     "field": {
      "n": "Pedregal de Glint"
     }
    },
    "tierra": {
     "n": "Lumen",
     "station": "Puerto Radiante",
     "desc": "Un deslumbrante mundo marino bajo un sol al rojo blanco. Paga bien por los metales."
    },
    "venus": {
     "n": "Mirage",
     "station": "Aguja de Cristal",
     "desc": "Un resplandeciente mundo de nubes. Sus ciudades ansían lujos y hielo."
    },
    "mercurio": {
     "n": "Anvil",
     "station": "Depósito Anvil",
     "desc": "Un mundo-forja fundido. Piedra solar por todas partes… y un calor brutal.",
     "field": {
      "n": "Campos Fundidos"
     }
    },
    "marte": {
     "n": "Canis",
     "station": "Ciudad Aullido",
     "desc": "Llanuras secas y clanes orgullosos. El agua vale más que el oro."
    },
    "ceres": {
     "n": "Ironheart",
     "station": "Estación Coro",
     "desc": "Capital del Cinturón de Hierro, donde cada roca lleva armadura.",
     "field": {
      "n": "Cinturón de Hierro"
     },
     "layoutDesc": "Una estación dentro del gran anillo que rodea Argent. Hierro, níquel, cobalto… y piratas."
    },
    "jupiter": {
     "n": "Argent"
    },
    "europa": {
     "n": "Frost",
     "station": "Colonia Frost",
     "desc": "Una luna helada de Argent. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito del Enjambre",
     "desc": "Las rocas troyanas de Argent, muchas de ellas blindadas.",
     "field": {
      "n": "Enjambre de Argent"
     }
    },
    "saturno": {
     "n": "Corona",
     "station": "Depósito Corona",
     "desc": "Un gigante dorado con anillos, iluminado como un farol.",
     "field": {
      "n": "Anillos de Corona"
     }
    },
    "titan": {
     "n": "Haze",
     "station": "Puerto Calima",
     "desc": "Una luna brumosa de Corona con enormes refinerías."
    },
    "pluton": {
     "n": "Dogstar",
     "station": "Bazar de los Saqueadores",
     "desc": "Un pequeño mundo helado cerca de la enana blanca Sirio B. Los Saqueadores venden de todo."
    },
    "kuiper": {
     "n": "Deriva de Sirio",
     "station": "Depósito de la Deriva",
     "desc": "Rocas blindadas a la deriva, lejos del resplandor.",
     "field": {
      "n": "Deriva de Sirio"
     }
    },
    "oort": {
     "n": "Confín de las Llamaradas",
     "station": "Puesto Sombra",
     "desc": "Hasta donde llegan las tormentas solares de Sirio. Algo nada entre las llamaradas.",
     "field": {
      "n": "Confín de las Llamaradas"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Glint"
    },
    "3": {
     "title": "Anvil y Canis",
     "text": "<b>Anvil</b> arde con <b>Piedra solar</b>: compra <b>Escudos</b>. <b>Canis</b> paga una fortuna por el hielo. Muchas rocas aquí son <b>blindadas</b>: usa el <b>Taladro (Q)</b>."
    },
    "4": {
     "title": "El Cinturón de Hierro",
     "text": "<b>Ironheart</b> y el <b>Cinturón de Hierro</b>: casi la mitad de las rocas son blindadas. ¡Taládralas! Aquí los piratas son feroces."
    },
    "6": {
     "title": "Sistema Argent",
     "text": "<b>Frost</b> y el <b>Enjambre de Argent</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Corona e influencia",
     "text": "<b>Haze</b> y los <b>Anillos de Corona</b>. <b>Invierte</b> en estaciones (cada nivel <b>+10% de ingresos base</b>) para ganar ingresos e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Sirio."
    },
    "8": {
     "title": "Dogstar",
     "text": "El Bazar de los Saqueadores de <b>Dogstar</b> y la <b>Deriva de Sirio</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Velas Fotónicas de Glint",
     "d": "Cajas de mineral con velas de espejo, empujadas a casa por la mismísima luz de Sirio.",
     "fx": "Producción del puesto de Glint ×3"
    },
    "beacons": {
     "n": "Autopistas de Luz Estelar",
     "d": "Rutas iluminadas por láser que las naves surfean a velocidades imposibles.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Escuadrón de Caballeros Espejo",
     "d": "Naves de combate cromadas que devuelven el fuego pirata directo a quien lo dispara.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Fuente de Luz de Lumen",
     "d": "Una columna de luz sólida eleva la carga desde el mar directo a la órbita.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Mares Celestes de Canis",
     "d": "Océanos flotantes cuelgan del cielo de Canis, sostenidos por campos magnéticos.",
     "fx": "Canis paga ×2 por todo · reputación con Clanes de Canis +50"
    },
    "gates": {
     "n": "Portales Espejo a la Velocidad de la Luz",
     "d": "Entras en un espejo en un mundo y sales por otro.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Corona de Plasma de Corona",
     "d": "Una corona de refinerías de plasma que rodea a Corona, tan caliente que podría forjar estrellas.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Elevador Estelar de Sirio",
     "d": "No solo atrapas la luz de la estrella: extraes materia directamente de Sirio.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Martillo de Enana Blanca",
     "d": "Lanzas un trozo de materia de enana blanca contra un planeta. Una cucharadita pesa tanto como una montaña.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "sol": {
   "n": "Sol",
   "gate": "El núcleo del Centinela estalla en pedazos, y en lo profundo de la Nube de Oort, un anillo más antiguo que el Sol <b>se enciende</b>. Es un <b>portal de salto</b>.",
   "signal": {
    "title": "Una señal desde la oscuridad",
    "text": "Tus antenas de espacio profundo captaron una <b>señal repetitiva</b> desde la <b>Nube de Oort</b>, mucho más allá del Cinturón de Kuiper. <b>No es humana</b>."
   }
  },
  "tauceti": {
   "n": "Tau Ceti",
   "intro": "Tau Ceti: el imperio comercial más rico del sector. La Mercantil de Ceti te da un <b>Pulso tractor</b>: pulsa <b>E</b> (o ATRAER) para atraer todos los trozos de mineral a tu alrededor. Es tuyo para siempre.",
   "gate": "El Acorazado se parte en pedazos y sus escoltas huyen. El Portal del Peaje es <b>gratis</b>… y apunta más adentro de la galaxia.",
   "tour": "Aurum y Silk son <b>mundos gemelos que giran uno alrededor del otro</b>, y el mercado negro de Freeport se esconde <b>entre las lunas de Crown</b>.",
   "signal": {
    "title": "El Portal del Peaje",
    "text": "El secreto más antiguo de la Mercantil de Ceti: más allá de la deriva hay un portal antiguo… y un <b>Acorazado Mercante</b> que cobra a cada nave un peaje de sangre. Nadie lo ha pagado y vivido para contarlo."
   },
   "factions": {
    "tierra": {
     "n": "Mercantil de Ceti"
    },
    "marte": {
     "n": "Gremio de Puerto Libre"
    },
    "cinturon": {
     "n": "Consorcio Minero"
    },
    "exterior": {
     "n": "Bolsa Exterior"
    },
    "piratas": {
     "n": "Red de Contrabandistas"
    }
   },
   "locs": {
    "luna": {
     "n": "Penny",
     "station": "Base Ceca",
     "desc": "Una luna gris de Aurum donde empiezan las fortunas.",
     "field": {
      "n": "Campos de Monedas"
     }
    },
    "tierra": {
     "n": "Aurum",
     "station": "Gran Bolsa",
     "desc": "Capital del imperio comercial más rico del sector."
    },
    "venus": {
     "n": "Silk",
     "station": "Aguja de Silk",
     "desc": "Un mundo de nubes rosadas lleno de comerciantes de lujo."
    },
    "mercurio": {
     "n": "Kiln",
     "station": "Depósito Kiln",
     "desc": "Un mundo horno. Platino y piedra solar a la vista.",
     "field": {
      "n": "Llanuras de Kiln"
     }
    },
    "marte": {
     "n": "Bazaar",
     "station": "Puerto Libre",
     "desc": "Un mundo mercado desértico. Paga bien por el hielo."
    },
    "ceres": {
     "n": "Ledger",
     "station": "Sede del Consorcio",
     "desc": "La capital del Consorcio en el cinturón.",
     "field": {
      "n": "Cinturón de Ledger"
     }
    },
    "jupiter": {
     "n": "Treasury"
    },
    "europa": {
     "n": "Vault",
     "station": "Colonia Vault",
     "desc": "Una luna helada de Treasury. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Treasury",
     "desc": "El enjambre troyano de Treasury, rico en iridio.",
     "field": {
      "n": "Enjambre de Treasury"
     }
    },
    "saturno": {
     "n": "Crown",
     "station": "Depósito Crown",
     "desc": "Un gigante lila con anillos, la joya de Tau Ceti.",
     "field": {
      "n": "Anillos de Crown"
     }
    },
    "titan": {
     "n": "Mint",
     "station": "Talleres Mint",
     "desc": "Una luna de Crown con bruma verde y refinerías enormes."
    },
    "pluton": {
     "n": "Freeport",
     "station": "Guarida de Contrabandistas",
     "desc": "Donde la Red de Contrabandistas vende todo lo que la Mercantil de Ceti no vende."
    },
    "kuiper": {
     "n": "Deriva de Ceti",
     "station": "Depósito de la Deriva",
     "desc": "Las frías afueras del imperio.",
     "field": {
      "n": "Deriva de Ceti"
     }
    },
    "oort": {
     "n": "El Portal del Peaje",
     "station": "Casa del Peaje",
     "desc": "Un portal antiguo custodiado por un Acorazado Mercante.",
     "field": {
      "n": "Portal del Peaje"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Penny"
    },
    "3": {
     "title": "Kiln y Bazaar",
     "text": "<b>Kiln</b> está lleno de <b>Platino</b> y <b>Piedra solar</b>: compra <b>Escudos</b>. <b>Bazaar</b> paga una fortuna por el hielo. Usa tu <b>Pulso tractor (E)</b> para atraparlo todo."
    },
    "4": {
     "title": "El Cinturón de Ledger",
     "text": "<b>Ledger</b> y su cinturón: níquel, cobalto, iridio… y los piratas más duros hasta ahora."
    },
    "6": {
     "title": "Sistema Treasury",
     "text": "<b>Vault</b> y el <b>Enjambre de Treasury</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Crown e influencia",
     "text": "<b>Mint</b> y los <b>Anillos de Crown</b>. <b>Invierte</b> en estaciones (cada nivel da <b>+10% de ingresos base</b>) para ganar ingresos e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Tau Ceti."
    },
    "8": {
     "title": "Freeport",
     "text": "La Guarida de Contrabandistas de <b>Freeport</b> y la <b>Deriva de Ceti</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Cañón de Monedas de Penny",
     "d": "El mineral se acuña en monedas en Penny y se dispara directo a la bóveda de la Gran Bolsa.",
     "fx": "Producción del puesto de Penny ×3"
    },
    "beacons": {
     "n": "Red de Peajes Hiperruta",
     "d": "Rutas más rápidas para todos… y tú cobras cada peaje.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Armada del Gremio Mercenario",
     "d": "Los mejores piratas que el dinero puede comprar, ahora cazando al resto. Dos te acompañan en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Centro Comercial Elevador de Aurum",
     "d": "Un ascensor espacial con diez mil tiendas. Los compradores suben hasta la órbita.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Resort Paraíso de Bazaar",
     "d": "Mares, bosques de palmeras y casinos sobre el desierto. Los turistas pagan el doble por todo.",
     "fx": "Bazaar paga ×2 por todo · reputación con Gremio de Puerto Libre +50"
    },
    "gates": {
     "n": "Portales de Comercio Instantáneo",
     "d": "Pide lo que sea, donde sea: llega antes de que termines de pagar.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Casino-Refinería de Crown",
     "d": "Una refinería escondida dentro del casino más grande de la galaxia. Los drones nunca paran, y las tragamonedas tampoco.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Banco Estelar de Ceti",
     "d": "Compras la estrella. Cada fotón que produce te paga intereses.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Rayo de Embargo Planetario",
     "d": "Si un planeta no puede pagar sus deudas, te lo quedas. Entero.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  },
  "vega": {
   "n": "Vega",
   "intro": "Vega: una estrella azul que gira tan rápido que está achatada. Los <b>cometas</b> llueven en todos los campos (3× más). Los pastores de cometas te dan la <b>Sobremarcha</b>: pulsa <b>R</b> (o TURBO) para tener 8 s de triple potencia de corte y velocidad, ideal para atrapar cometas. Es tuya para siempre.",
   "gate": "El Leviatán estalla en una ventisca de hielo. Donde vivía, un anillo antiguo <b>se descongela y se abre</b>.",
   "tour": "Aquí todo gira rápido en <b>órbitas inclinadas y alargadas</b>, los cinturones son manadas de hielo y los cometas cruzan el mapa.",
   "signal": {
    "title": "Algo enorme en el hielo",
    "text": "Los pastores de cometas juran que una criatura del tamaño de una estación nada entre las lunas heladas: el <b>Leviatán de Hielo</b>. Embiste naves. Custodia el portal."
   },
   "factions": {
    "tierra": {
     "n": "Directorio Azur"
    },
    "marte": {
     "n": "Clanes de la Escarcha"
    },
    "cinturon": {
     "n": "Pastores de Cometas"
    },
    "exterior": {
     "n": "Liga Glaciar"
    },
    "piratas": {
     "n": "Rompehielos"
    }
   },
   "locs": {
    "luna": {
     "n": "Sleet",
     "station": "Base Cumbre Nevada",
     "desc": "Una luna helada de Azure, barrida por cometas.",
     "field": {
      "n": "Ventisqueros de Sleet"
     }
    },
    "tierra": {
     "n": "Azure",
     "station": "Puerto Azul",
     "desc": "Un mundo oceánico azul profundo bajo un sol azul cegador."
    },
    "venus": {
     "n": "Opal",
     "station": "Aguja de Opal",
     "desc": "Un mundo de nubes iridiscentes, hogar de coleccionistas ricos."
    },
    "mercurio": {
     "n": "Glare",
     "station": "Depósito Glare",
     "desc": "Un mundo derretido por la luz azul de la estrella. Hay platino por todas partes.",
     "field": {
      "n": "Llanuras de Glare"
     }
    },
    "marte": {
     "n": "Rime",
     "station": "Puerta Helada",
     "desc": "Un desierto congelado. Curiosamente, aún paga bien por el hielo."
    },
    "ceres": {
     "n": "Herdstone",
     "station": "Rancho de Cometas",
     "desc": "La capital de los pastores de cometas.",
     "field": {
      "n": "Cinturón del Rebaño"
     }
    },
    "jupiter": {
     "n": "Frostmaw"
    },
    "europa": {
     "n": "Shiver",
     "station": "Colonia Shiver",
     "desc": "Una luna helada de Frostmaw. Paga bien por el iridio."
    },
    "troyanos": {
     "station": "Depósito Frostmaw",
     "desc": "Los troyanos de Frostmaw, brillantes de hielo.",
     "field": {
      "n": "Enjambre de Frostmaw"
     }
    },
    "saturno": {
     "n": "Hielo Halcyon",
     "station": "Depósito Glaciar",
     "desc": "Un gigante azul pálido con anillos hechos casi solo de cometas.",
     "field": {
      "n": "Anillos de Cometas"
     }
    },
    "titan": {
     "n": "Slush",
     "station": "Talleres Slush",
     "desc": "Una luna de aguanieve con refinerías enormes."
    },
    "pluton": {
     "n": "Breakwater",
     "station": "Mercado Rompehielos",
     "desc": "Donde los Rompehielos venden lo que roban."
    },
    "kuiper": {
     "n": "Deriva de Vega",
     "station": "Depósito de la Deriva",
     "desc": "Cometas helados sin fin al borde del resplandor de Vega.",
     "field": {
      "n": "Deriva de Vega"
     }
    },
    "oort": {
     "n": "La Gran Helada",
     "station": "Puesto del Deshielo",
     "desc": "Un mar helado de cometas donde caza el Leviatán.",
     "field": {
      "n": "La Gran Helada"
     }
    }
   },
   "unlocks": {
    "0": {
     "title": "Sleet"
    },
    "3": {
     "title": "Glare y Rime",
     "text": "<b>Glare</b> está cubierto de <b>Platino</b>: compra <b>Escudos</b>. <b>Rime</b> paga bien por el hielo. Hay cometas por todas partes: ¡usa la <b>Sobremarcha (R)</b> para atraparlos!"
    },
    "4": {
     "title": "El Cinturón del Rebaño",
     "text": "<b>Herdstone</b> y el <b>Cinturón del Rebaño</b>, donde viven los pastores de cometas. Los piratas Rompehielos son feroces."
    },
    "6": {
     "title": "Sistema Frostmaw",
     "text": "<b>Shiver</b> y el <b>Enjambre de Frostmaw</b>. El <b>Escáner</b> revela vetas ricas."
    },
    "7": {
     "title": "Hielo Halcyon e influencia",
     "text": "<b>Slush</b> y los <b>Anillos de Cometas</b>. <b>Invierte</b> en estaciones (cada nivel da <b>+10% de ingresos base</b>) para ganar ingresos e <b>influencia</b>. Llega a <b>100 de influencia</b> para gobernar Vega."
    },
    "8": {
     "title": "Breakwater",
     "text": "El Mercado Rompehielos de <b>Breakwater</b> y la <b>Deriva de Vega</b>."
    }
   },
   "projects": {
    "driver": {
     "n": "Expreso Cometa",
     "d": "Enganchas contenedores de mineral a cometas que pasan y ellos hacen la entrega.",
     "fx": "Producción del puesto de Sleet ×3"
    },
    "beacons": {
     "n": "Rutas de Hipergiro",
     "d": "Vega gira tan rápido que su gravedad lanza las naves por estas rutas.",
     "fx": "Viajes 50% más rápidos · combustible −30%"
    },
    "fleet": {
     "n": "Escuadrón Fantasma de Hielo",
     "d": "Cañoneras camufladas en hielo. Los piratas nunca las ven venir; dos vuelan contigo en cada combate.",
     "fx": "Peligro pirata −50% · 2 naves escolta en cada combate"
    },
    "elevator": {
     "n": "Criocañón",
     "d": "La carga se congela en balas de hielo y se dispara directo a la órbita.",
     "fx": "Todo el mineral se vende +25% en todas partes"
    },
    "terraform": {
     "n": "Motor de Deshielo",
     "d": "Derrites un mundo congelado y lo conviertes en un jardín en una sola tarde.",
     "fx": "Rime paga ×2 por todo · reputación con Clanes de la Escarcha +50"
    },
    "gates": {
     "n": "Portales de Tiempo Congelado",
     "d": "Portales que congelan el tiempo durante el viaje: llegas antes de haber salido.",
     "fx": "Viajes instantáneos y gratis a cualquier lugar"
    },
    "ringstation": {
     "n": "Rancho de Anillos de Cometas",
     "d": "Arreas cometas hacia los anillos del gigante y los cosechas para sacar mineral.",
     "fx": "TODOS los ingresos de drones ×3"
    },
    "dyson": {
     "n": "Sifón de la Estrella Azul",
     "d": "La luz de Vega es tan feroz que basta con ponerle una pajita.",
     "fx": "TODOS los ingresos ×5"
    },
    "nova": {
     "n": "Bombardeo de Cometas",
     "d": "Rediriges todos los cometas del sistema hacia un solo planeta.",
     "fx": "Te permite DESTRUIR planetas (desde el Mapa estelar)"
    }
   }
  }
 }
}/*END_ES_CONTENT*/;
function mergeText(dst, src) {
  for (const k in src) {
    const v = src[k];
    if (v && typeof v === 'object' && !Array.isArray(v) && dst[k] && typeof dst[k] === 'object') mergeText(dst[k], v);
    else if (dst) dst[k] = v;
  }
}
// ores, factions, Sol's worlds, unlocks, projects, upgrades, enemies, ranks — before Sol's snapshot is taken
function applyEsBase() {
  if (!ES) return;
  const B = ES_CONTENT.base || {};
  for (const k in B.items || {}) if (ITEMS[k]) ITEMS[k].n = B.items[k].n;
  for (const k in B.factions || {}) if (FACTIONS[k]) FACTIONS[k].n = B.factions[k].n;
  for (const k in B.locs || {}) if (LOC[k]) mergeText(LOC[k], B.locs[k]);
  (B.unlocks || []).forEach((u, i) => { if (UNLOCKS[i] && u) mergeText(UNLOCKS[i], u); });
  for (const k in B.projects || {}) { const p = PROJECTS.find(x => x.id === k); if (p) mergeText(p, B.projects[k]); }
  for (const k in B.upg || {}) if (UPG[k]) mergeText(UPG[k], B.upg[k]);
  for (const k in B.enemies || {}) if (ENEMIES[k]) ENEMIES[k].n = B.enemies[k].n;
  (B.ranks || []).forEach((r, i) => { if (RANKS[i] && r) RANKS[i][1] = r; });
}
// every star system's names and story
function applyEsSystems() {
  if (!ES) return;
  for (const id in ES_CONTENT.systems || {}) {
    const D = SYSTEMS[id], E = ES_CONTENT.systems[id]; if (!D || !E) continue;
    const { locs, ...rest } = E;
    mergeText(D, rest);
    for (const lid in locs || {}) {
      const { layoutDesc, ...l } = locs[lid];
      if (D.locs && D.locs[lid]) mergeText(D.locs[lid], l); else if (Object.keys(l).length) { D.locs = D.locs || {}; D.locs[lid] = l; }
      if (layoutDesc && D.layout && D.layout[lid]) D.layout[lid].desc = layoutDesc;
    }
  }
  const G = (ES_CONTENT.base || {}).galaxy || {};
  for (const g of GALAXY) if (G[g.id]) g.n = G[g.id];
}
function applyEsLegacy() {
  if (!ES) return;
  for (const k in (ES_CONTENT.base || {}).legacy || {}) if (LEGACY[k]) mergeText(LEGACY[k], ES_CONTENT.base.legacy[k]);
}

// On touch devices the story texts name the on-screen buttons instead of keyboard keys ("press R (or BOOST)" → "tap BOOST")
const TOUCH_BTN = { Q: ['DRILL', 'TALADRO'], E: ['PULL', 'ATRAER'], R: ['BOOST', 'TURBO'], F: ['BOMB', 'BOMBA'], C: ['SCAN', 'ESCANEAR'], X: ['PHASE', 'FASE'] };
function touchify(s) {
  if (typeof s !== 'string') return s;
  const btn = k => TOUCH_BTN[k][ES ? 1 : 0];
  return s
    .replace(/\b([Pp]ress|[Pp]ulsa) <b>([QERFCX])<\/b> \((?:or|o) (?:the |el botón )?([^)]+?)(?: button)?\)/g, (m, v, k, b) => `${v[0] === 'P' ? (ES ? 'Toca' : 'Tap') : (ES ? 'toca' : 'tap')} <b>${b}</b>`)
    .replace(/\b([Pp]ress|[Pp]ulsa) <b>([QERFCX])<\/b>/g, (m, v, k) => `${v[0] === 'P' ? (ES ? 'Toca' : 'Tap') : (ES ? 'toca' : 'tap')} <b>${btn(k)}</b>`)
    .replace(/ \(([QERFCX])\)/g, (m, k) => ` (${btn(k)})`);
}
function touchifyContent() {
  const walk = o => { for (const k in o) { if (typeof o[k] === 'string') o[k] = touchify(o[k]); else if (o[k] && typeof o[k] === 'object') walk(o[k]); } };
  for (const id in SYSTEMS) { const D = SYSTEMS[id]; for (const k of ['intro', 'signal', 'unlocks', 'tour']) if (D[k]) { if (typeof D[k] === 'string') D[k] = touchify(D[k]); else walk(D[k]); } }
  for (const u of SOL_SNAP.unlocks) walk(u);
  for (const u of UNLOCKS) walk(u);
}
