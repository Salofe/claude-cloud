"""Fase 4: construye VCF GRCh38 para PharmCAT a partir de genotipos 23andMe (GRCh37) mapeando por rsID
al archivo de posiciones de PharmCAT. Solo incluye posiciones MEDIDAS (o imputadas si se da un TSV extra).
Comprueba que los alelos del genotipo estén en {REF, ALT} (o su complemento) y reporta discordancias."""
import sys, gzip
positions, genome, out = sys.argv[1:4]
extra = sys.argv[4] if len(sys.argv) > 4 else None  # TSV rsid\tgenotipo (imputado)
comp = str.maketrans('ACGT', 'TGCA')
g = {}
for l in open(genome):
    if l[0] == '#': continue
    rs, ch, pos, gt = l.rstrip('\n').split('\t')
    if gt != '--' and set(gt) <= set('ACGT'): g[rs] = gt
src = {k: 'medido' for k in g}
if extra:
    for l in open(extra):
        rs, gt = l.split()[:2]
        if rs not in g: g[rs] = gt; src[rs] = 'imputado'
n = {'medido': 0, 'imputado': 0, 'discordante': 0, 'flip': 0}
lines = []
hdr = []
for l in gzip.open(positions, 'rt'):
    if l.startswith('##'):
        if l.startswith('##contig') or l.startswith('##fileformat') or l.startswith('##FORMAT') or l.startswith('##INFO'): hdr.append(l)
        continue
    if l.startswith('#'): continue
    f = l.rstrip('\n').split('\t')
    ch, pos, ids, ref, alt = f[:5]
    alts = alt.split(',')
    if len(ref) != 1 or any(len(a) != 1 for a in alts): continue
    gt = None
    for rs in ids.split(';'):
        if rs in g: gt = g[rs]; s = src[rs]; break
    if gt is None: continue
    alleles = [ref] + alts
    al = list(gt)
    if not set(al) <= set(alleles):
        fl = [a.translate(comp) for a in al]
        if set(fl) <= set(alleles): al = fl; n['flip'] += 1
        else:
            n['discordante'] += 1; print('DISCORDANTE', ch, pos, ids, ref, alt, gt, file=sys.stderr); continue
    idx = [str(alleles.index(a)) for a in al]
    gts = '/'.join(idx)
    n[s] += 1
    lines.append((ch, int(pos), ids, ref, alt, gts, s))
with open(out, 'w') as o:
    o.write('##fileformat=VCFv4.2\n')
    for h in hdr:
        if not h.startswith('##fileformat'): o.write(h)
    if not any(h.startswith('##FORMAT=<ID=GT') for h in hdr):
        o.write('##FORMAT=<ID=GT,Number=1,Type=String,Description="Genotype">\n')
    o.write('#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\tSANTIAGO\n')
    order = {f'chr{i}': i for i in range(1, 23)}; order['chrX'] = 23; order['chrY'] = 24; order['chrM'] = 25
    for ch, pos, ids, ref, alt, gts, s in sorted(lines, key=lambda x: (order.get(x[0], 99), x[1])):
        o.write(f'{ch}\t{pos}\t{ids}\t{ref}\t{alt}\t.\tPASS\t.\tGT\t{gts}\n')
print(n)
