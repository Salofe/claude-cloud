"""Evalúa el experimento de enmascaramiento: r2 entre dosis imputada y genotipo real por clase de MAF (variantes no medidas)."""
import sys, subprocess, collections
M = sys.argv[1]; BT = '/opt/mm/bt/bin/bcftools'
def q(f, fmt):
    return subprocess.run([BT, 'query', '-i', 'TYPE="snp"', '-f', fmt, f], capture_output=True, text=True).stdout.splitlines()
tr = {}
for l in q(M + '/truth.vcf.gz', '%POS:%REF:%ALT\t[%GT\t]\n'):
    x = l.rstrip('\t').split('\t'); tr[x[0]] = x[1:]
bins = collections.defaultdict(lambda: [0]*7)
for l in q(M + '/imp.vcf.gz', '%POS:%REF:%ALT\t%INFO/IMP\t[%DS\t]\n'):
    x = l.rstrip('\t').split('\t')
    if x[1] != '1' or x[0] not in tr: continue
    gx = [sum(int(a) for a in g.replace('|', '/').split('/')) for g in tr[x[0]]]
    y = [float(v) for v in x[2:]]
    p = sum(gx) / (2 * len(gx)); maf = min(p, 1 - p)
    b = 'a) 0-1%' if maf < 0.01 else ('b) 1-5%' if maf < 0.05 else ('c) 5-20%' if maf < 0.2 else 'd) 20-50%'))
    for xi, yi in zip(gx, y):
        B = bins[b]; B[0] += 1; B[1] += xi; B[2] += yi; B[3] += xi*xi; B[4] += yi*yi; B[5] += xi*yi; B[6] += (round(yi) == xi)
for b in sorted(bins):
    n, sx, sy, sxx, syy, sxy, cc = bins[b]
    den = (n*sxx - sx*sx) * (n*syy - sy*sy)
    r2 = ((n*sxy - sx*sy) ** 2 / den) if den > 0 else float('nan')
    print(f'MAF (en los 30 probados) {b[3:]}: {n} genotipos, r2(dosis, verdad) = {r2:.3f}, concordancia del genotipo = {cc/n:.3f}')
