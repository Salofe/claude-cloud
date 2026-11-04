"""Lista scores del PGS Catalog por rasgo (EFO/MONDO) con nº de variantes, método, ancestría y publicación."""
import json, sys, urllib.request, time
def get(url):
    for t in range(4):
        try: return json.load(urllib.request.urlopen(url, timeout=60))
        except Exception as e: time.sleep(2 ** t)
for efo in sys.argv[1:]:
    url = f'https://www.pgscatalog.org/rest/score/search?trait_id={efo}&limit=250'
    res = []
    while url:
        d = get(url)
        if not d: break
        res += d['results']; url = d.get('next')
    print(f'== {efo}: {len(res)} scores')
    res.sort(key=lambda r: -r['variants_number'])
    for r in res[:40]:
        anc = r.get('ancestry_distribution', {}).get('gwas', {}).get('dist', {})
        pub = r['publication']
        print(f"  {r['id']}\t{r['variants_number']:>9}\t{(r.get('method_name') or '')[:22]:22s}\t{pub.get('firstauthor')} {pub.get('date_publication','')[:4]}\t{r['trait_reported'][:40]}\tGWAS:{anc}")
