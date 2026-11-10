"""Resume el RFMix del dúo faseado por herencia. Columnas: HIJO.0 = copia materna, HIJO.1 = copia paterna,
MADRE.0 = transmitida, MADRE.1 = no transmitida. Fracciones en cM, tramos y fecha de mezcla (pulso único, como f6_rfmix_summary).
Uso: f12_rfmix_resumen.py <dir_rfmix> <HIJO> <MADRE> <salida.json>"""
import glob, os, json, collections, sys
R, KID, MOM, out = sys.argv[1:5]
cols = [f'{KID}.0', f'{KID}.1', f'{MOM}.0', f'{MOM}.1']
totcm = {k: collections.Counter() for k in cols}; xcm = {k: collections.Counter() for k in cols}
segs = {k: [] for k in cols}; tracts = {k: collections.defaultdict(list) for k in cols}
agree = collections.Counter()
for f in sorted(glob.glob(R + '/out_*.msp.tsv')):
    c = os.path.basename(f)[4:-8]
    L = open(f).read().splitlines()
    inv = {v: k for k, v in (x.split('=') for x in L[0].split(':', 1)[1].split())}
    hd = L[1].split('\t'); ix = {k: hd.index(k) for k in cols}
    cur = {k: None for k in cols}
    for l in L[2:]:
        r = l.split('\t'); spos, epos, scm, ecm = int(r[1]), int(r[2]), float(r[3]), float(r[4])
        if c != 'X': agree['igual' if r[ix[cols[0]]] == r[ix[cols[2]]] else 'distinto'] += ecm - scm
        for k in cols:
            a = inv[r[ix[k]]]
            (xcm if c == 'X' else totcm)[k][a] += ecm - scm
            cu = cur[k]
            if cu and cu[0] == a and abs(cu[2] - spos) < 2e6: cu[2] = epos; cu[4] = ecm
            else:
                if cu:
                    segs[k].append((c if c == 'X' else int(c), cu[1], cu[2], cu[0]))
                    if c != 'X': tracts[k][cu[0]].append(cu[4] - cu[3])
                cur[k] = [a, spos, epos, scm, ecm]
    for k in cols:
        cu = cur[k]
        if cu:
            segs[k].append((c if c == 'X' else int(c), cu[1], cu[2], cu[0]))
            if c != 'X': tracts[k][cu[0]].append(cu[4] - cu[3])
def frac(d):
    t = sum(d.values()); return {a: round(v / t, 4) for a, v in sorted(d.items())} if t else {}
res = dict(autosomas={k: frac(totcm[k]) for k in cols}, X={k: frac(xcm[k]) for k in cols})
for who, (a, b) in {KID: (cols[0], cols[1]), MOM: (cols[2], cols[3])}.items():
    res['autosomas'][who] = frac(totcm[a] + totcm[b]); res['X'][who] = frac(xcm[a] + xcm[b])
t = sum(agree.values()); res['concordancia_hijo_materno_vs_madre_transmitido'] = round(agree['igual'] / t, 4) if t else None
gen = {}
for who, ks in {KID + '_materno': [cols[0]], KID + '_paterno': [cols[1]], MOM: [cols[2], cols[3]]}.items():
    m = frac(sum((totcm[k] for k in ks), collections.Counter())); g = {}
    for a in ('NAT', 'AFR'):
        Ls = [x for k in ks for x in tracts[k].get(a, [])]
        if not Ls: continue
        mean = sum(Ls) / len(Ls)
        g[a] = dict(n=len(Ls), media_cM=round(mean, 1), max_cM=round(max(Ls), 1), T_generaciones=round(100.0 / (mean * (1 - m.get(a, 0))), 1))
    gen[who] = g
res['generaciones'] = gen; res['segs'] = segs
json.dump(res, open(out, 'w'))
for k, v in res['autosomas'].items(): print('autosomas', k, v)
for k, v in res['X'].items(): print('X', k, v)
print('concordancia', res['concordancia_hijo_materno_vs_madre_transmitido']); print(json.dumps(gen))
