"""Fase 3: cruce de genotipos MEDIDOS (23andMe) con ClinVar GRCh37 (SNVs).
Cuenta copias del alelo clasificado. ALT '.' en ClinVar = el alelo de la referencia es el clasificado.
Salida: TSV con todas las coincidencias P/LP, conflictivas con P, riesgo/drug_response, y ACMG SF."""
import sys, collections, re
genome, clin, out = sys.argv[1:4]
ACMG = set("""ACTA2 ACTC1 ACVRL1 APC APOB ATP7B BAG3 BMPR1A BRCA1 BRCA2 BTD CACNA1S CALM1 CALM2 CALM3 CASQ2 COL3A1 DES DSC2 DSG2 DSP ENG FBN1 FLNC GAA GLA HFE HNF1A KCNH2 KCNQ1 LDLR LMNA MAX MEN1 MLH1 MSH2 MSH6 MYBPC3 MYH11 MYH7 MYL2 MYL3 NF2 OTC PALB2 PCSK9 PKP2 PMS2 PRKAG2 PTEN RB1 RBM20 RET RPE65 RYR1 RYR2 SCN5A SDHAF2 SDHB SDHC SDHD SMAD3 SMAD4 STK11 TGFBR1 TGFBR2 TMEM43 TNNC1 TNNI3 TNNT2 TP53 TPM1 TRDN TSC1 TSC2 TTN TTR VHL WT1""".split())
gt = {}
for line in open(genome):
    if line.startswith('#'): continue
    rs, ch, pos, g = line.rstrip('\n').split('\t')
    if g == '--' or not set(g) <= set('ACGT'): continue
    gt.setdefault((ch, int(pos)), (rs, g))
hits = []
stat = collections.Counter()
for line in open(clin):
    f = line.rstrip('\n').split('\t')
    ch, pos, cid, ref, alt, sig, rev, gene, dn, mc, afe, aft, rsn, conf = f
    k = (ch, int(pos))
    if k not in gt: continue
    stat['clinvar_en_chip'] += 1
    rs, g = gt[k]
    allele = ref if alt == '.' else alt
    if not set(g) <= {ref, alt} and alt != '.':
        # genotipo con un alelo distinto de REF/ALT de este registro: otro cambio en la misma posición
        pass
    dose = g.count(allele)
    comps = [c for c in re.split(r'[|,]', sig) if c]
    sigl = sig.lower()
    cls = None
    if any(c in ('Pathogenic', 'Likely_pathogenic', 'Pathogenic/Likely_pathogenic', 'Pathogenic/Likely_pathogenic/Pathogenic,_low_penetrance', 'Pathogenic,_low_penetrance', 'Likely_pathogenic,_low_penetrance') for c in comps):
        cls = 'P/LP'
    elif sigl.startswith('conflicting') and re.search(r'(^|\|)(pathogenic|likely_pathogenic)_\(', conf.lower()):
        cls = 'conflicto_con_P'
    elif any(x in sigl for x in ('risk_factor', 'drug_response', 'association', 'protective', 'affects')):
        cls = 'otro_' + sig
    if cls is None: continue
    stat['registros_' + cls.split('_')[0]] += 1
    if dose == 0: continue
    genes = ';'.join(x.split(':')[0] for x in gene.split('|')) if gene != '.' else '.'
    acmg = any(x in ACMG for x in genes.split(';'))
    hits.append([cls, ch, pos, rs, 'rs' + rsn if rsn != '.' else '.', ref, alt, allele, g, dose, sig, rev, genes, 'SI' if acmg else '', dn, mc, afe, aft, conf, cid])
hits.sort(key=lambda h: (h[0] != 'P/LP', h[0] != 'conflicto_con_P', h[12]))
with open(out, 'w') as o:
    o.write('clase\tchr\tpos\tid_chip\trs_clinvar\tref\talt\talelo_clasificado\tgenotipo\tcopias\tCLNSIG\trevision\tgen\tACMG_SF\tcondicion\tconsecuencia\tAF_ExAC\tAF_1kG\tCLNSIGCONF\tClinVarID\n')
    for h in hits: o.write('\t'.join(map(str, h)) + '\n')
for k, v in sorted(stat.items()): print(k, v)
print('coincidencias con >=1 copia:', collections.Counter(h[0] if not h[0].startswith('otro') else 'otro' for h in hits))
