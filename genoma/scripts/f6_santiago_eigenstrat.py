"""Genotipo de Santiago en los SNPs de un .snp EIGENSTRAT (AADR).
Modo 'medido': solo genotipos del chip. Modo 'imputado': medido + imputado (|DS-entero|<=0.1; SNPs HO ya ascertados como comunes).
Salida: columna .geno (conteo del alelo de la col. 5 del .snp; 9 = falta)."""
import sys, gzip, os, subprocess
snpfile, mode, outgeno = sys.argv[1:4]
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
snps = []
for l in open(snpfile):
    f = l.split(); snps.append((f[1], int(f[3]), f[4], f[5]))
want = {}
for i, (c, p, a1, a2) in enumerate(snps):
    want.setdefault(c, {})[p] = i
# medidos: genoma crudo (alelos en + strand)
gt = {}
for l in open(S + '/data/genome.txt'):
    if l[0] == '#': continue
    rs, c, p, g = l.rstrip('\n').split('\t')
    c = {'X': '23', 'Y': '24', 'MT': '90'}.get(c, c)
    if c in want and int(p) in want[c] and g != '--' and set(g) <= set('ACGT'):
        gt[want[c][int(p)]] = ('m', g if len(g) == 2 else g * 2)
nm = len(gt); ni = 0
if mode == 'imputado':
    for c in list(want):
        if c in ('24', '90'): continue
        cc = 'X' if c == '23' else c
        f = f'{S}/imp/imp_chr{cc}.vcf.gz'
        if not os.path.exists(f + '.tbi'): continue
        reg = '\n'.join(f'{cc}\t{p}' for p in sorted(want[c])) + '\n'
        open(S + '/anc/_reg.txt', 'w').write(reg)
        out = subprocess.run(['/opt/mm/bt/bin/bcftools', 'query', '-R', S + '/anc/_reg.txt', '-i', 'TYPE="snp"',
                              '-f', '%POS\t%REF\t%ALT\t%INFO/AF\t[%DS]\t[%GT]\n', f], capture_output=True, text=True).stdout
        for line in out.splitlines():
            p, r, a, af, ds, g = line.split('\t')
            i = want[c].get(int(p))
            if i is None or i in gt: continue
            af = float(af); ds = float(ds)
            # OJO: INFO/AF de Beagle con 1 muestra = dosis propia; no sirve como MAF. Los SNPs HO ya son comunes.
            if abs(ds - round(ds)) > 0.1: continue
            k = int(round(ds))
            if c == '23': k = min(k, 1) * 2  # X haploide como homocigoto
            gt[i] = ('i', r * (2 - k) + a * k if c != '23' else (a * 2 if k else r * 2))
            ni += 1
miss = 0; incompat = 0
with open(outgeno, 'w') as o:
    for i, (c, p, a1, a2) in enumerate(snps):
        v = gt.get(i)
        if v is None: o.write('9\n'); miss += 1; continue
        g = v[1]
        if not set(g) <= {a1, a2}: o.write('9\n'); incompat += 1; continue
        o.write(f'{g.count(a1)}\n')
print(f'{mode}: medidos {nm}, imputados {ni}, faltan {miss}, incompatibles {incompat}, total {len(snps)}', file=sys.stderr)
