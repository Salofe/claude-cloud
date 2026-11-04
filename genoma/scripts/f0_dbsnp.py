"""Consulta dbSNP (solo rsIDs públicos, sin genotipos) para obtener REF/ALT en GRCh37 (NC_0000xx.yy de GRCh37)."""
import json, sys, time, urllib.request, csv
tsv, out = sys.argv[1], sys.argv[2]
rows = list(csv.DictReader(open(tsv), delimiter='\t'))
res = []
for row in rows:
    rs = row['rsid']
    if not rs.startswith('rs'): res.append((rs, '', '', '', 'internal')); continue
    url = f'https://api.ncbi.nlm.nih.gov/variation/v0/refsnp/{rs[2:]}'
    for t in range(4):
        try:
            d = json.load(urllib.request.urlopen(url, timeout=30)); break
        except Exception as e:
            time.sleep(2 ** t); d = None
    if d is None or 'primary_snapshot_data' not in d:
        res.append((rs, '', '', '', 'merged/err' if d else 'err')); continue
    p = d['primary_snapshot_data']
    pos = ref = ''; alts = set()
    for pl in p['placements_with_allele']:
        for a in pl['alleles']:
            s = a['allele'].get('spdi')
            if not s: continue
            # GRCh37 chromosomes: NC_0000NN.(10|11|...) ; use assembly name
        asm = [x for x in pl.get('placement_annot', {}).get('seq_id_traits_by_assembly', []) if 'GRCh37' in x.get('assembly_name', '')]
        if asm:
            for a in pl['alleles']:
                s = a['allele'].get('spdi')
                if not s: continue
                pos = s['position'] + 1; ref = s['deleted_sequence']
                if s['inserted_sequence'] != s['deleted_sequence']: alts.add(s['inserted_sequence'])
            break
    genes = set()
    for ann in p.get('allele_annotations', []):
        for asm in ann.get('assembly_annotation', []):
            for g in asm.get('genes', []): genes.add(g.get('locus'))
    res.append((rs, pos, ref, ','.join(sorted(alts)), ','.join(sorted(x for x in genes if x))))
    time.sleep(0.35)
with open(out, 'w') as f:
    f.write('rsid\tpos37_dbsnp\tref\talt\tgenes\n')
    for r in res: f.write('\t'.join(map(str, r)) + '\n')
print('ok', len(res))
