"""Descarga asociaciones del GWAS Catalog (API v2) para estudios faciales/pelo por PMID. Guarda TSV."""
import json, sys, time, urllib.request
pmids = sys.argv[2:]; out = sys.argv[1]
def get(url):
    for t in range(5):
        try: return json.load(urllib.request.urlopen(url, timeout=90))
        except Exception: time.sleep(2 ** t)
with open(out, 'w') as o:
    o.write('pmid\trsid\teffect_allele\tbeta\tdirection\tor\tp\ttrait\traf\n')
    for pm in pmids:
        page = 0; n = 0
        while True:
            d = get(f'https://www.ebi.ac.uk/gwas/rest/api/v2/associations?pubmed_id={pm}&size=200&page={page}')
            if not d: break
            for a in d.get('_embedded', {}).get('associations', []):
                for sa in a.get('snp_allele') or []:
                    b = a.get('beta') or ''
                    val = dirn = ''
                    if b and b != '-':
                        parts = b.split(); val = parts[0]
                        dirn = 'increase' if 'increase' in b else ('decrease' if 'decrease' in b else '')
                    o.write('\t'.join(map(str, [pm, sa.get('rs_id'), sa.get('effect_allele'), val, dirn, a.get('or_value') or '', a.get('p_value'),
                                               '; '.join(a.get('reported_trait') or []), a.get('risk_frequency') or ''])) + '\n')
                    n += 1
            pg = d.get('page', {})
            if page + 1 >= pg.get('totalPages', 0): break
            page += 1
        print(pm, n, file=sys.stderr)
