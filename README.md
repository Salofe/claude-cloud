# Solar Prospector

Juego 2D de minería espacial, comercio y construcción de imperio en el Sistema Solar. Todo cabe en un solo archivo HTML, sin dependencias.

**Jugar:** abre `dist/index.html` en el navegador. Funciona con ratón y teclado o con pantalla táctil.

## El ciclo de juego

1. **Mina.** Vuela entre asteroides (WASD) y rómpelos con el láser (clic sostenido). Los grandes se parten en pedazos y sueltan mineral. Las vetas brillantes dan el doble.
2. **Viaja.** Los planetas orbitan, así que las distancias cambian cada día. Viajar gasta combustible según la distancia y el tamaño de tu nave.
3. **Vende y comercia.** Cada estación paga distinto (Tierra, Luna, Venus, Marte, Ceres, Europa, Titán y el mercado negro de Plutón). Si vendes mucho de golpe, el precio baja.
4. **Mejora.** Hay 8 sistemas con 5 niveles cada uno: casco, láser, propulsores, tanque, escudos, armas, drones y escáner. La nave se ve más grande con cada mejora.
5. **Sobrevive.** Los piratas te emboscan en las rutas y en los campos peligrosos. El combate es automático y depende de tu equipo. Puedes pelear, huir o sobornar.
6. **Aprovecha las crisis.** Guerras, pandemias, hambrunas, booms de construcción, tormentas solares y huelgas cambian los precios y el nivel de peligro.
7. **Crece.** Cumple contratos, gana reputación con 5 facciones e invierte en estaciones para tener ingresos pasivos e influencia. Llega a 100 de influencia para dominar el sistema.

## Zonas

| Zona | Minerales | Riesgo |
|---|---|---|
| Luna | Hierro, Hielo, Titanio, Helio-3 | Muy bajo |
| Mercurio | Platino, Iridio (calor extremo) | Bajo |
| Cinturón (Ceres) | Níquel, Platino, Titanio | Medio |
| Anillos de Saturno | Hielo, Helio-3, Iridio | Medio |
| Troyanos de Júpiter | Titanio, Platino, Iridio | Alto |
| Cinturón de Kuiper | Cristal Exótico, Iridio | Muy alto |

## Desarrollo

El código fuente está en `src/`. Para compilar el archivo único:

```
node build.js              # genera dist/index.html
node tools/thumbnail.js    # genera dist/thumbnail.png y dist/thumbnail-square.png
```

El arte es 100 % procedural (canvas 2D) y el sonido se sintetiza con WebAudio. La partida se guarda en `localStorage`.
