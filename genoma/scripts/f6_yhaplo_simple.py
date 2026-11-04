"""Asignación de haplogrupo Y con el índice YBrowse (hg19) y etiquetas ISOGG.
Para cada llamada del chip en Y, marca derivado/ancestral según allele_anc/allele_der en la misma posición."""
import csv, sys, collections, re
genome, ybrowse = sys.argv[1:3]
calls = {}
for l in open(genome):
    if l[0] == '#': continue
    rs, ch, pos, g = l.rstrip('\n').split('\t')
    if ch == 'Y' and g != '--' and len(g) >= 1 and set(g) <= set('ACGT'):
        calls[int(pos)] = g[0]
der = collections.defaultdict(list); anc = collections.defaultdict(list); n = collections.Counter()
for r in csv.DictReader(open(ybrowse)):
    try: p = int(r['start'])
    except: continue
    if p not in calls: continue
    a, d, lab = r['allele_anc'], r['allele_der'], r['ISOGG_haplogroup']
    if lab in ('', 'unknown', 'Not listed', '.') or len(a) != 1 or len(d) != 1: continue
    g = calls[p]
    if g == d: der[lab].append(r['Name']); n['der'] += 1
    elif g == a: anc[lab].append(r['Name']); n['anc'] += 1
    else: n['otro'] += 1
print('llamadas Y:', len(calls), dict(n))
def norm(l): return l.replace('~', '').strip()
labs = sorted(der, key=lambda x: len(norm(x)))
# líneas del camino: etiquetas derivadas que son prefijo de la más profunda consistente
cands = sorted(der, key=lambda x: (len(norm(x)), len(der[x])), reverse=True)
print('\nEtiquetas con SNPs DERIVADOS (etiqueta: n_derivados / n_ancestrales):')
for lab in sorted(der, key=lambda x: norm(x)):
    print(f'  {lab:22s} der={len(der[lab]):3d} anc={len(anc.get(lab,[])):3d}  {",".join(der[lab][:6])}')
deep = [l for l in der if norm(l).startswith('G')]
print('\nRama G: subclados con llamadas ANCESTRALES (lo que se descarta):')
best = max((l for l in der if len(der[l]) >= 1 and len(anc.get(l, [])) <= len(der[l]) // 3), key=lambda x: len(norm(x)))
print('  más profundo con evidencia derivada mayoritaria:', best)
for lab in sorted(anc, key=norm):
    if norm(lab).startswith(norm(best)[:4]) and len(norm(lab)) > len(norm(best)) - 3:
        print(f'  {lab:22s} anc={len(anc[lab]):3d} der={len(der.get(lab,[])):3d} {",".join(anc[lab][:5])}')
