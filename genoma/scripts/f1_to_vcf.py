"""Fase 1: 23andMe (sin CR) -> VCF GRCh37 con REF de human_g1k_v37.fasta.
Autosomas diploides; X no-PAR, Y y MT haploides (hombre). Indels I/D se excluyen (se tratan aparte).
Escribe estadísticas de QC en stdout."""
import sys, pysam, collections
genome, fasta, out = sys.argv[1:4]
SAMPLE = sys.argv[4] if len(sys.argv) > 4 else 'SANTIAGO'
SEX = sys.argv[5] if len(sys.argv) > 5 else 'M'   # 'F': X diploide en todo el cromosoma, sin Y
fa = pysam.FastaFile(fasta)
PAR = [(60001, 2699520), (154931044, 155260560)]
comp = str.maketrans('ACGT', 'TGCA')
order = [str(i) for i in range(1, 23)] + ['X', 'Y', 'MT']
st = collections.Counter()
recs = collections.defaultdict(list)
seen = set()
for line in open(genome):
    if line.startswith('#'): continue
    rs, ch, pos, gt = line.rstrip('\n').split('\t')
    st['total'] += 1
    if gt == '--': st['nocall'] += 1; continue
    if set(gt) <= set('ID'): st['indel_ID'] += 1; continue
    if not set(gt) <= set('ACGT'): st['otro'] += 1; continue
    pos = int(pos)
    key = (ch, pos)
    if key in seen: st['duplicado_pos'] += 1; continue
    fch = 'MT' if ch == 'MT' else ch
    ref = fa.fetch(fch, pos - 1, pos).upper()
    al = list(gt)
    if SEX == 'F' and ch == 'Y': st['Y_en_mujer'] += 1; continue
    haploid = ch in ('Y', 'MT') or (SEX == 'M' and ch == 'X' and not any(a <= pos <= b for a, b in PAR))
    if haploid and len(al) == 2:
        if al[0] != al[1]: st['het_en_haploide'] += 1; continue
        al = al[:1]
    if not haploid and len(al) == 1: st['haploide_en_diploide'] += 1; continue
    alts = sorted(set(a for a in al if a != ref))
    if len(alts) > 1: st['no_coincide_ref_trialelico'] += 1; continue
    alt = alts[0] if alts else '.'
    if ref not in 'ACGT': st['ref_N'] += 1; continue
    gts = '/'.join('0' if a == ref else '1' for a in al)
    seen.add(key)
    recs[ch].append((pos, rs, ref, alt, gts))
    st['pasa'] += 1
    st['pasa_' + ('auto' if ch not in ('X', 'Y', 'MT') else ch)] += 1
    if alt == '.': st['hom_ref'] += 1
with open(out, 'w') as o:
    o.write('##fileformat=VCFv4.2\n##reference=human_g1k_v37\n')
    for c in order: o.write(f'##contig=<ID={c},length={fa.get_reference_length(c)}>\n')
    o.write('##FORMAT=<ID=GT,Number=1,Type=String,Description="Genotype">\n')
    o.write('#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\t' + SAMPLE + '\n')
    for c in order:
        for pos, rs, ref, alt, g in sorted(recs[c]):
            o.write(f'{c}\t{pos}\t{rs}\t{ref}\t{alt}\t.\tPASS\t.\tGT\t{g}\n')
for k, v in sorted(st.items()): print(f'{k}\t{v}')
