"""Divide los scoring files armonizados (GRCh37) por cromosoma: pos, effect, other, PGS, weight.
Usa hm_chr/hm_pos/effect_allele/other_allele (o hm_inferOtherAllele). Excluye filas sin posición armonizada."""
import gzip, glob, os, collections, sys
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
out = S + '/pgs/bychr'; os.makedirs(out, exist_ok=True)
fh = {}
stats = {}
for f in sorted(glob.glob(S + '/pgs/PGS*_hmPOS_GRCh37.txt.gz')):
    pid = os.path.basename(f).split('_')[0]
    n = collections.Counter(); hdr = None
    meta = {}
    for l in gzip.open(f, 'rt'):
        if l.startswith('#'):
            if '=' in l: k, v = l[1:].strip().split('=', 1); meta[k] = v
            continue
        x = l.rstrip('\n').split('\t')
        if hdr is None: hdr = {k: i for i, k in enumerate(x)}; continue
        n['filas'] += 1
        c = x[hdr['hm_chr']] if 'hm_chr' in hdr else ''
        p = x[hdr['hm_pos']] if 'hm_pos' in hdr else ''
        if not c or not p or c not in [str(i) for i in range(1, 23)] + ['X']: n['sin_pos'] += 1; continue
        ea = x[hdr['effect_allele']].upper()
        oa = x[hdr['other_allele']].upper() if 'other_allele' in hdr and x[hdr['other_allele']] else ''
        if not oa and 'hm_inferOtherAllele' in hdr: oa = x[hdr['hm_inferOtherAllele']].upper()
        if not oa or '/' in oa: n['sin_otro_alelo_recuperable'] += 1; oa = '?'
        w = x[hdr['effect_weight']]
        if c not in fh: fh[c] = open(f'{out}/chr{c}.tsv', 'w')
        fh[c].write(f'{p}\t{ea}\t{oa}\t{pid}\t{w}\n'); n['ok'] += 1
    stats[pid] = (dict(n), meta.get('pgs_name'), meta.get('trait_reported'), meta.get('weight_type'))
    print(pid, stats[pid], file=sys.stderr)
for h in fh.values(): h.close()
