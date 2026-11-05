"""Relee logs de qpAdm y arma una tabla: pesos, SE, p (patrón completo o f4rank 0 si es una sola fuente)."""
import glob, os, re, sys
W = sys.argv[1]; out = sys.argv[2]
rows = []
for f in sorted(glob.glob(W + '/*.log')):
    name = os.path.basename(f)[:-4]; txt = open(f).read()
    left = open(W + f'/{name}.left').read().split()
    m = re.search(r'best coefficients:\s+([-\d.\s]+)\n', txt); se = re.search(r'std\. errors:\s+([-\d.\s]+)\n', txt)
    p = None
    for line in txt.splitlines():
        if re.match(r'\s*0+\s+\d+\s+[-\d.]+\s+[-\d.e+]+\s+[-\d.e+]+', line): p = line.split()[4]; break
    if p is None:
        mm = re.search(r'f4rank: 0 dof:\s+\d+ chisq:\s+[\d.]+ tail:\s+([\d.e+-]+)', txt)
        if mm: p = mm.group(1)
    rows.append((name, left[0], ','.join(left[1:]), m.group(1).split() if m else [], se.group(1).split() if se else [], p))
with open(out, 'w') as o:
    o.write('modelo\tobjetivo\tfuentes\tpesos\tSE\tp\n')
    for n, t, s, c, e, p in rows:
        o.write(f"{n}\t{t}\t{s}\t{' '.join(c)}\t{' '.join(e)}\t{p}\n")
        print(f"{n:26s} {t:12s} | " + ' '.join(f"{x}={a}±{b}" for x, a, b in zip(s.split(','), c, e)) + f" | p={p}")
