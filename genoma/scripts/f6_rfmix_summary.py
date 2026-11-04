"""Resume RFMix: fracciones por ancestría (en cM y en Mb), X vs autosomas, tramos y estimación de generaciones.
Modelo de pulso único (Gravel 2012 simplificado): tramos de la ancestría minoritaria ~ Exponencial(tasa = T*(1-m)) por Morgan."""
import glob, os, json, collections, sys
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
R = S + '/anc/rfmix'
segs = []; tot = collections.defaultdict(lambda: collections.Counter()); totcm = collections.defaultdict(lambda: collections.Counter())
tracts = collections.defaultdict(list)
for f in sorted(glob.glob(R + '/out_*.msp.tsv')):
    c = os.path.basename(f)[4:-8]
    lines = open(f).read().splitlines()
    codes = dict(x.split('=') for x in lines[0].split(':', 1)[1].split())  # "#Subpopulation order/codes: AFR=0 EUR=1 NAT=2"
    inv = {v: k for k, v in codes.items()}
    rows = [l.split('\t') for l in lines[2:]]
    nh = len(rows[0]) - 6
    haps = [0] if c == 'X' else list(range(nh))
    for h in haps:
        cur = None
        for r in rows:
            spos, epos, scm, ecm = int(r[1]), int(r[2]), float(r[3]), float(r[4])
            a = inv[r[6 + h]]
            key = 'X' if c == 'X' else 'A'
            tot[key][a] += epos - spos; totcm[key][a] += ecm - scm
            segs.append((c if c == 'X' else int(c), spos, epos, h, a))
            if cur and cur[0] == a and abs(cur[2] - spos) < 2e6: cur = (a, cur[1], epos, cur[3], ecm)
            else:
                if cur and key == 'A': tracts[cur[0]].append(cur[4] - cur[3])
                cur = (a, spos, epos, scm, ecm)
        if cur and key == 'A': tracts[cur[0]].append(cur[4] - cur[3])
res = {}
for key in ('A', 'X'):
    t = sum(totcm[key].values())
    res[key] = {a: round(v / t, 4) for a, v in totcm[key].items()} if t else {}
    res[key + '_Mb'] = {a: round(v / 1e6, 1) for a, v in tot[key].items()}
print('Autosomas (fracción en cM):', res['A'])
print('X (fracción en cM):', res['X'])
gen = {}
for a, L in tracts.items():
    m = res['A'].get(a, 0)
    if a == 'EUR' or not L: continue
    meancM = sum(L) / len(L)
    T = 100.0 / (meancM * (1 - m)) if meancM > 0 else None
    gen[a] = dict(n=len(L), media_cM=round(meancM, 1), mediana_cM=round(sorted(L)[len(L)//2], 1), max_cM=round(max(L), 1), T_generaciones=round(T, 1) if T else None)
    print(a, gen[a])
json.dump(dict(frac=res, generaciones=gen, segs=segs), open(R + '/resumen.json', 'w'))
