// Bundles src/ into a single file: dist/index.html
const fs = require('fs');
const order = ['data', 'art', 'icons', 'audio', 'state', 'politics', 'map', 'mining', 'battle', 'ui', 'main'];
const js = order.map(f => `// ---- ${f}.js ----\n` + fs.readFileSync(`src/${f}.js`, 'utf8')).join('\n');
const css = fs.readFileSync('src/style.css', 'utf8');
let html = fs.readFileSync('src/index.html', 'utf8');
html = html.replace('/*CSS*/', () => css).replace('/*JS*/', () => js.replace(/<\/script/g, '<\\/script'));
fs.mkdirSync('dist', { recursive: true });
fs.writeFileSync('dist/index.html', html);
console.log('dist/index.html', (html.length / 1024).toFixed(1) + ' KB');
