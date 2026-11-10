"""Análisis sin fase: ¿los genotipos de una persona son compatibles con el haplotipo de los portadores de una variante rara,
y a lo largo de cuánta distancia? Compara al objetivo con la distribución en portadores y no portadores del panel.
Uso: f11_haplo_compat.py <panel_chip.vcf.gz> <objetivo.vcf.gz> <panel_completo.vcf.gz> <chr:pos> <panel de poblaciones>"""
import sys, subprocess, collections, bisect
import numpy as np
chipf, mef, fullf, site, popf = sys.argv[1:6]
BT = '/opt/mm/bt/bin/bcftools'; SP = int(site.split(':')[1])
def q(f, fmt, extra=()): return subprocess.run([BT, 'query', *extra, '-f', fmt, f], capture_output=True, text=True).stdout.splitlines()
samples = subprocess.run([BT, 'query', '-l', chipf], capture_output=True, text=True).stdout.split()
pop = {}
for l in open(popf):
    f = l.split()
    if f[0] != 'sample': pop[f[0]] = (f[1], f[2])
truth = dict(l.split('\t') for l in q(fullf, '[%SAMPLE\t%GT\n]', ('-r', site)))
me = {}
for l in q(mef, '%POS\t%REF\t%ALT[\t%GT]\n'):
    p, r, a, g = l.split('\t'); g = g.replace('|', '/').split('/')
    if '.' not in g: me[(int(p), r, a)] = int(g[0]) + int(g[1])
pos = []; H = []; G_me = []
for l in q(chipf, '%POS\t%REF\t%ALT[\t%GT]\n'):
    f = l.split('\t'); k = (int(f[0]), f[1], f[2])
    if k not in me: continue
    pos.append(k[0]); G_me.append(me[k]); H.append([int(x) for g in f[3:] for x in g.split('|')])
pos = np.array(pos); H = np.array(H, dtype=np.int8); G_me = np.array(G_me, dtype=np.int8)
G = H[:, 0::2] + H[:, 1::2]
idx = bisect.bisect(list(pos), SP)
car_haps = []   # (sample index, hap column)
for i, s in enumerate(samples):
    g = truth[s].split('|')
    for h in (0, 1):
        if g[h] == '1': car_haps.append((i, 2 * i + h))
print('SNPs del chip en la región:', len(pos), '| haplotipos portadores:', len(car_haps))
def run(g, h):
    bad = ((g == 0) & (h == 1)) | ((g == 2) & (h == 0))
    L = idx - 1
    while L >= 0 and not bad[L]: L -= 1
    R = idx
    while R < len(pos) and not bad[R]: R += 1
    return (pos[R - 1] - pos[L + 1]) / 1e6, R - L - 1, pos[L + 1], pos[R - 1]
def best(g, skip=None):
    r = [(run(g, H[:, c]), samples[si]) for si, c in car_haps if si != skip]
    return sorted(r, reverse=True)
mine = best(G_me)
print('TÚ contra cada haplotipo portador (Mb compatibles, nº SNPs, desde, hasta, portador):')
for (mb, n, a, b), s in mine: print(f'   {mb:.2f} Mb  {n:4d} SNPs  {a}-{b}  {s} {pop[s][0]}')
my = mine[0][0][0]
rows = []
for i, s in enumerate(samples):
    b = best(G[:, i], skip=i)[0][0][0]
    rows.append((b, s, '1' in truth[s], pop[s]))
car = sorted([r for r in rows if r[2]], reverse=True)
print('Portadores reales: su mejor compatibilidad con OTRO portador:', [(round(r[0], 2), r[1], r[3][0]) for r in car])
for grp, f in [('EUR', lambda r: r[3][1] == 'EUR'), ('EUR+AMR', lambda r: r[3][1] in ('EUR', 'AMR')), ('IBS+TSI', lambda r: r[3][0] in ('IBS', 'TSI')), ('todos', lambda r: True)]:
    non = np.array([r[0] for r in rows if not r[2] and f(r)])
    print(f'{grp:8s} no portadores n={len(non)}: mediana {np.median(non):.2f} Mb, p95 {np.percentile(non,95):.2f}, p99 {np.percentile(non,99):.2f}, máx {non.max():.2f}; con ≥ tu valor ({my:.2f} Mb): {int((non >= my).sum())} ({100*(non >= my).mean():.2f}%)')
ncar_ge = sum(1 for r in car if r[0] >= my)
print(f'portadores con ≥ tu valor: {ncar_ge} de {len(car)}')
