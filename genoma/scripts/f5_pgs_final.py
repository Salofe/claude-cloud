"""Agrega PGS por cromosoma y normaliza: (1) Z ajustado por ancestría (media y varianza modeladas con PCs de 1000G,
como pgsc_calc/Khera 2019); (2) percentil contra poblaciones de 1000G. Usa la proyección PCA de Santiago."""
import glob, os, sys, collections, json
import numpy as np
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
W = S + '/pgs/work'; A = S + '/anc/kg'
chrs = sorted(int(os.path.basename(f)[8:-4]) for f in glob.glob(W + '/sant_chr*.tsv'))
pop = {}
for l in open(S + '/ref/integrated_call_samples_v3.20130502.ALL.panel'):
    f = l.split()
    if f[0] != 'sample': pop[f[0]] = (f[1], f[2])
kg = None; ids = None; sant = collections.Counter(); nv = collections.Counter(); pids = None
for c in chrs:
    lines = open(f'{W}/kg_chr{c}.sscore').read().splitlines()
    hdr = lines[0].split('\t'); cols = [h.replace('_SUM', '') for h in hdr[1:]]
    m = np.array([[float(x) for x in l.split('\t')[1:]] for l in lines[1:]])
    cid = [l.split('\t')[0] for l in lines[1:]]
    if kg is None: kg = m; ids = cid; pids = cols
    else:
        assert cid == ids and cols == pids; kg += m
    for l in open(f'{W}/sant_chr{c}.tsv'):
        pid, v, n = l.split('\t'); sant[pid] += float(v); nv[pid] += int(n)
# PCs
pcs = {}; npc = 10
for l in open(A + '/proj.sscore').read().splitlines()[1:]:
    f = l.split('\t'); pcs[f[0]] = np.array([float(x) for x in f[-20:]][:npc])
X = np.array([pcs[i] for i in ids]); Xs = pcs['SANTIAGO']
Xd = np.column_stack([np.ones(len(ids)), X]); xs = np.concatenate([[1], Xs])
meta = {}
for f in glob.glob(S + '/pgs/PGS*_hmPOS_GRCh37.txt.gz'):
    import gzip
    pid = os.path.basename(f).split('_')[0]; d = {}
    for l in gzip.open(f, 'rt'):
        if not l.startswith('#'): break
        if '=' in l: k, v = l[1:].strip().split('=', 1); d[k] = v
    meta[pid] = d
res = {}
for j, pid in enumerate(pids):
    y = kg[:, j]
    beta, *_ = np.linalg.lstsq(Xd, y, rcond=None)
    resid = y - Xd @ beta
    # varianza dependiente de PCs: modelar log(resid^2)
    g, *_ = np.linalg.lstsq(Xd, np.log(resid ** 2 + 1e-12), rcond=None)
    corr = np.mean(resid ** 2) / np.mean(np.exp(Xd @ g))
    mu = xs @ beta; sd = np.sqrt(np.exp(xs @ g) * corr)
    z = (sant[pid] - mu) / sd
    pct = {}
    for P in ['IBS', 'TSI', 'CEU', 'GBR', 'MXL', 'PEL', 'CLM', 'PUR', 'YRI', 'CHB']:
        v = np.array([y[i] for i, s in enumerate(ids) if pop[s][0] == P])
        pct[P] = round(100 * float(np.mean(v < sant[pid])), 1)
        pct[P + '_z'] = round(float((sant[pid] - v.mean()) / v.std()), 2)
    from math import erf, sqrt
    res[pid] = dict(trait=meta[pid].get('trait_reported'), name=meta[pid].get('pgs_name'), variants_scoring=meta[pid].get('variants_number'),
                    used=nv[pid], cover=round(nv[pid] / float(meta[pid].get('variants_number', 1)), 3),
                    z_ancestry=round(float(z), 2), pct_ancestry=round(50 * (1 + erf(z / sqrt(2))), 1), raw=sant[pid], **pct)
    print(f"{pid:10s} {res[pid]['trait'][:28]:28s} uso {nv[pid]:>8} ({res[pid]['cover']:.0%}) Zanc={z:+.2f} pct={res[pid]['pct_ancestry']:5.1f} | IBS {pct['IBS']:5.1f} MXL {pct['MXL']:5.1f} PEL {pct['PEL']:5.1f} CEU {pct['CEU']:5.1f}")
json.dump(dict(chrs=chrs, res=res), open(S + '/pgs/pgs_resultados.json', 'w'), indent=1)
