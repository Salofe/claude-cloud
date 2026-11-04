"""Fase 9: puntaje por rasgo facial/pelo = suma de beta*(dosis_efecto - 2*p_IBS) con dirección publicada (GWAS Catalog).
Para Xiong 2019 se añade el rasgo (distancia entre landmarks) de la Tabla 1 del paper (lista del handoff), con signo del catálogo."""
import csv, collections, json, sys
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
XIONG = {'rs143353512':'Prn-AlL','rs200243292':'EnR-ChL','rs77142479':'EnL-Sn','rs10202675':'EnR-AlR','rs2884836':'ExR-ChR','rs113663609':'EnR-ChR',
 'rs12504954':'Prn-AlL','rs2225718':'EnR-AlR','rs7738892':'EnR-N','rs1700048':'ExR-ChL','rs9642796':'AlL-Ls','rs201719697':'ExL-AlL','rs1863716':'Prn-AlR',
 'rs7325564':'N-Prn','rs1989285':'N-Prn','rs16949899':'ExR-ChL','rs7404301':'AlL-Ls','rs1229119':'ExR-ChR','rs34032897':'EnR-N','rs6535972':'EnL-AlL',
 'rs2230578':'EnL-Sn','rs8077906':'Prn-EnL','rs35473710':'AlR-ChL','rs4813454':'AlL-AlR'}
LAND = {'Prn-AlL':'punta de nariz ↔ ala nasal (proyección de la punta)','Prn-AlR':'punta de nariz ↔ ala nasal (proyección de la punta)','EnR-ChL':'ojo interno ↔ comisura (altura media de la cara)',
 'EnL-Sn':'ojo interno ↔ subnasal (altura de la nariz)','EnR-AlR':'ojo interno ↔ ala nasal (altura de la nariz)','ExR-ChR':'ojo externo ↔ comisura (altura media de la cara)',
 'EnR-ChR':'ojo interno ↔ comisura (altura media de la cara)','EnR-N':'ojo interno ↔ nasion (profundidad del puente)','ExR-ChL':'ojo externo ↔ comisura opuesta (altura/anchura media)',
 'AlL-Ls':'ala nasal ↔ labio superior','ExL-AlL':'ojo externo ↔ ala nasal','N-Prn':'nasion ↔ punta (largo de la nariz)','EnL-AlL':'ojo interno ↔ ala nasal (altura de la nariz)',
 'Prn-EnL':'punta ↔ ojo interno','AlR-ChL':'ala nasal ↔ comisura','AlL-AlR':'ala ↔ ala (ancho de la nariz)'}
g = {r['rsid']: r for r in csv.DictReader(open(S + '/face/genos.tsv'), delimiter='\t')}
rows = []
for r in csv.DictReader(open(S + '/face/assoc.tsv'), delimiter='\t'):
    if r['pmid'] not in ('31763980', '22341974', '27193062', '26105758', '27560520', '29220522', '17952075', '20585627'): continue
    if not r['direction'] and not r['or']: continue
    gg = g.get(r['rsid'])
    if not gg or gg['fuente'] not in ('medido', 'imputado'): continue
    ea = r['effect_allele']
    if ea not in (gg['ref'], gg['alt']) or not gg['AF_IBS']: continue
    pI = float(gg['AF_IBS']) if ea == gg['alt'] else 1 - float(gg['AF_IBS'])
    pM = float(gg['AF_MXL']) if ea == gg['alt'] else 1 - float(gg['AF_MXL'])
    d = gg['genotipo'].count(ea) if gg['genotipo'] else None
    if d is None: continue
    if r['direction']:
        b = float(r['beta']) * (1 if r['direction'] == 'increase' else -1)
    else:
        import math; b = math.log(float(r['or']))
    trait = r['trait']
    if r['pmid'] == '31763980' and r['rsid'] in XIONG: trait = f"Xiong 2019 {XIONG[r['rsid']]} — {LAND[XIONG[r['rsid']]]}"
    rows.append(dict(pmid=r['pmid'], rsid=r['rsid'], trait=trait, ea=ea, dose=d, p_IBS=round(pI, 3), p_MXL=round(pM, 3), beta=b,
                     dev=round(b * (d - 2 * pI), 4), fuente=gg['fuente'], genotipo=gg['genotipo']))
by = collections.defaultdict(list)
for r in rows: by[(r['pmid'], r['trait'])].append(r)
out = []
for (pm, t), lst in sorted(by.items()):
    s = sum(x['dev'] for x in lst)
    out.append(dict(pmid=pm, trait=t, n=len(lst), score=round(s, 3), snps=[(x['rsid'], x['ea'], x['genotipo'], x['dose'], x['p_IBS'], round(x['beta'], 3), x['fuente']) for x in lst]))
    print(f"{pm} | {t[:80]:80s} | n={len(lst)} | desv={s:+.3f}  " + '; '.join(f"{x['rsid']} {x['ea']}x{x['dose']} (p={x['p_IBS']}) b={x['beta']:+.3f}" for x in lst)[:400])
json.dump(out, open(S + '/face/face_scores.json', 'w'), indent=1)
