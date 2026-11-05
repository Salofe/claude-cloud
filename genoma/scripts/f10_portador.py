"""Cobertura de portador (genes recesivos de cribado preconcepcional): cuántas variantes ClinVar P/LP (>=1 estrella)
mide el chip en esos genes y cuántas copias lleva la persona. Solo SNVs medidos."""
import sys, collections, re
genome, clin = sys.argv[1:3]
GENES = set("""CFTR GJB2 GJB6 HBB HBA1 HBA2 PAH GALT BTD ATP7B ACADM MEFV HEXA SERPINA1 HFE GBA1 GBA ASPA BLM FANCC ELP1 MCOLN1 SMPD1
CAPN3 DHCR7 POLG SLC26A4 USH2A ABCA4 PKHD1 MMUT PCCA PCCB IVD MCCC1 MCCC2 CPT2 ACADVL HADHA ALDOB ASL ASS1 CBS GAA IDUA NPC1 TPP1
CLN3 PPT1 CNGB3 NPHS1 NPHS2 SLC12A3 AGXT ACADS TYR OCA2 GLB1 DYSF COL7A1 ERCC6 PEX1 PEX6 CYP21A2 SMN1 G6PD MPL ATM BCKDHB
FAH GNPTAB HSD17B4 LAMB3 LAMA3 MKS1 NEB PMM2 RARS2 SLC22A5 TMEM216 VPS13B ZFYVE26 SPG11 GLDC HPS1 SGCA SGCB SGCD SGCG FKRP""".split())
gt = {}
for line in open(genome):
    if line.startswith('#'): continue
    rs, ch, pos, g = line.rstrip('\n').split('\t')
    if g == '--' or not set(g) <= set('ACGT'): continue
    gt.setdefault((ch, int(pos)), (rs, g))
PLP = ('Pathogenic', 'Likely_pathogenic', 'Pathogenic/Likely_pathogenic')
n = collections.Counter(); hits = []; genes_cov = collections.Counter()
for line in open(clin):
    f = line.rstrip('\n').split('\t')
    ch, pos, cid, ref, alt, sig, rev, gene, dn, mc, afe, aft, rsn, conf = f
    g0 = gene.split(':')[0].split('|')[0]
    if g0 not in GENES: continue
    comps = [c for c in re.split(r'[|,]', sig) if c]
    if not any(c in PLP for c in comps): continue
    if 'no_assertion' in rev or 'no_classification' in rev: continue
    n['plp_genes_total'] += 1
    k = (ch, int(pos))
    if k not in gt: continue
    n['plp_medidas'] += 1; genes_cov[g0] += 1
    rs, g = gt[k]
    allele = ref if alt == '.' else alt
    d = g.count(allele)
    if d: hits.append((g0, rs, ch, pos, ref, alt, g, d, rev, dn[:60]))
print(dict(n)); print('genes con al menos 1 variante medida:', len(genes_cov))
print('top genes:', genes_cov.most_common(15))
print('copias del alelo patogénico encontradas:', len(hits))
for h in hits: print('\t'.join(map(str, h)))
