"""Fasea el X (no-PAR) de la madre con el X del hijo varón: el alelo del hijo es el transmitido.
Salida: VCF de 2 muestras. Hijo como a|a (haploide duplicado), madre transmitido|no transmitido.
Uso: f12_duo_X.py <hijo_medido.vcf.gz> <madre_medido.vcf.gz> <sitios_panel.tsv(POS REF ALT)> <salida.vcf> <HIJO> <MADRE>"""
import sys, gzip, collections
kv, mv, sites, out, KID, MOM = sys.argv[1:7]
PAR1, PAR2 = 2699520, 154931044
def load(f):
    d = {}
    for l in gzip.open(f, 'rt'):
        if l[0] == '#': continue
        x = l.rstrip('\n').split('\t')
        if x[0] != 'X' or not (PAR1 < int(x[1]) < PAR2): continue
        d[int(x[1])] = (x[2], x[3], x[4], x[9].replace('|', '/').split('/'))
    return d
k, m = load(kv), load(mv)
ref = collections.defaultdict(list)
for l in open(sites):
    p, r, a = l.rstrip('\n').split('\t'); ref[int(p)].append((r, a))
st = collections.Counter()
with open(out, 'w') as o:
    o.write('##fileformat=VCFv4.2\n##contig=<ID=X>\n##FORMAT=<ID=GT,Number=1,Type=String,Description="Genotype">\n')
    o.write(f'#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\t{KID}\t{MOM}\n')
    for p in sorted(set(k) & set(m)):
        rs, r, ak, gk = k[p]; _, _, am, gm = m[p]
        if '.' in gk or '.' in gm or len(gk) != 1 or len(gm) != 2: st['sin_dato'] += 1; continue
        alts = {x for x in (ak, am) if x != '.'}
        if len(alts) > 1: st['multialelico'] += 1; continue
        cands = [ra for ra in ref.get(p, []) if ra[0] == r and len(ra[1]) == 1]
        if alts: cands = [ra for ra in cands if ra[1] in alts]
        if len(cands) != 1: st['no_en_panel'] += 1; continue
        a = cands[0][1]; t = gk[0]
        if t not in gm: st['error_mendeliano'] += 1; continue
        u = gm[0] if gm[1] == t else gm[1] if gm[0] == t else t
        if gm[0] == gm[1]: u = t
        o.write(f'X\t{p}\t{rs}\t{r}\t{a}\t.\tPASS\t.\tGT\t{t}|{t}\t{t}|{u}\n'); st['ok'] += 1
print(dict(st))
