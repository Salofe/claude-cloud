"""Consulta GWAS Catalog REST v2 por rsID (dato público) y lista alelo de riesgo, OR/beta, rasgo, PMID."""
import json, sys, urllib.request, time
def assoc(rs, n=50):
    url = f'https://www.ebi.ac.uk/gwas/rest/api/v2/associations?rs_id={rs}&size={n}'
    for t in range(4):
        try: return json.load(urllib.request.urlopen(url, timeout=60)).get('_embedded', {}).get('associations', [])
        except Exception: time.sleep(2 ** t)
    return None
if __name__ == '__main__':
    filt = None
    args = sys.argv[1:]
    if args and args[0].startswith('--filt='): filt = args[0][7:].lower(); args = args[1:]
    for rs in args:
        a = assoc(rs)
        print('==', rs, '' if a is not None else 'ERROR')
        for x in a or []:
            tr = '; '.join(x.get('reported_trait') or [])
            if filt and filt not in tr.lower(): continue
            print('  ', x.get('snp_effect_allele'), 'OR=', x.get('or_value'), 'beta=', x.get('beta'), x.get('beta_unit'), x.get('beta_direction'), 'p=', x.get('p_value'), '|', tr[:60], '| PMID', x.get('pubmed_id'), '| RAF', x.get('risk_frequency'))
