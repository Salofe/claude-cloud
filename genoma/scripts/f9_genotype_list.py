"""Genotipa una lista de rsIDs: medido (chip) o imputado (MAF>=1% en 1000G, |DS-entero|<=0.1), y frecuencia en 1000G
(IBS, CEU, MXL, PEL, YRI). Posición GRCh37 desde dbSNP (solo rsIDs públicos). Salida TSV."""
import sys, json, time, urllib.request, subprocess, collections, os
inp, out = sys.argv[1:3]
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
BT = '/opt/mm/bt/bin/bcftools'
rsids = sorted(set(l.split()[0] for l in open(inp) if l.strip().startswith('rs')))
cache_f = S + '/face/pos_cache.json'
cache = json.load(open(cache_f)) if os.path.exists(cache_f) else {}
def dbsnp(rs):
    for t in range(4):
        try:
            d = json.load(urllib.request.urlopen(f'https://api.ncbi.nlm.nih.gov/variation/v0/refsnp/{rs[2:]}', timeout=30)); break
        except Exception: time.sleep(2 ** t); d = None
    if not d or 'primary_snapshot_data' not in d: return None
    for pl in d['primary_snapshot_data']['placements_with_allele']:
        tr = pl.get('placement_annot', {}).get('seq_id_traits_by_assembly', [])
        if any('GRCh37' in x.get('assembly_name', '') for x in tr) and pl['seq_id'].startswith('NC_0000'):
            chrom = str(int(pl['seq_id'].split('.')[0][-2:])); chrom = {'23': 'X', '24': 'Y'}.get(chrom, chrom)
            s = pl['alleles'][0]['allele']['spdi']
            return [chrom, s['position'] + 1]
    return None
for rs in rsids:
    if rs not in cache: cache[rs] = dbsnp(rs); time.sleep(0.34)
json.dump(cache, open(cache_f, 'w'))
meas = {}
for l in open(S + '/data/genome.txt'):
    if l[0] == '#': continue
    r, c, p, g = l.rstrip('\n').split('\t')
    if r in cache and g != '--' and set(g) <= set('ACGT'): meas[r] = g
bychr = collections.defaultdict(list)
for rs, v in cache.items():
    if rs in rsids and v: bychr[v[0]].append((rs, v[1]))
imp = {}; freq = {}
pops = {}
for l in open(S + '/ref/integrated_call_samples_v3.20130502.ALL.panel'):
    f = l.split()
    if f[0] != 'sample' and f[1] in ('IBS', 'CEU', 'MXL', 'PEL', 'YRI'): pops.setdefault(f[1], []).append(f[0])
popf = S + '/face/popfile.txt'
open(popf, 'w').write(''.join(f'{s}\t{p}\n' for p, ss in pops.items() for s in ss))
open(popf.replace('popfile', 'samples'), 'w').write(''.join(f'{s}\n' for ss in pops.values() for s in ss))
for c, lst in bychr.items():
    reg = S + f'/face/reg_{c}.txt'; open(reg, 'w').write(''.join(f'{c}\t{p}\n' for _, p in lst))
    posrs = {p: rs for rs, p in lst}
    f = f'{S}/imp/imp_chr{c}.vcf.gz'
    if os.path.exists(f + '.tbi'):
        q = subprocess.run([BT, 'query', '-R', reg, '-f', '%POS\t%ID\t%REF\t%ALT\t[%DS]\t%INFO/IMP\n', f], capture_output=True, text=True).stdout
        for line in q.splitlines():
            p, i, r, a, ds, im = line.split('\t')
            rs = posrs.get(int(p))
            if rs and (i == rs or i == '.'): imp[rs] = (r, a, float(ds))
    k = f'{S}/ref/1kg/chr{c}.vcf.gz'
    if os.path.exists(k + '.tbi'):
        q = subprocess.run(f"{BT} view -R {reg} -S {popf.replace('popfile','samples')} {k} -Ou 2>/dev/null | {BT} +fill-tags -Ou -- -S {popf} -t AF | {BT} query -f '%POS\\t%REF\\t%ALT\\t%INFO/AF_IBS\\t%INFO/AF_CEU\\t%INFO/AF_MXL\\t%INFO/AF_PEL\\t%INFO/AF_YRI\\n'",
                           shell=True, capture_output=True, text=True).stdout
        for line in q.splitlines():
            p, r, a, *afs = line.split('\t')
            rs = posrs.get(int(p))
            if rs: freq[rs] = (r, a, afs)
with open(out, 'w') as o:
    o.write('rsid\tchr\tpos\tref\talt\tfuente\tgenotipo\tds_alt\tAF_IBS\tAF_CEU\tAF_MXL\tAF_PEL\tAF_YRI\n')
    for rs in rsids:
        v = cache.get(rs)
        if not v: o.write(f'{rs}\t\t\t\t\tsin_posicion\n'); continue
        fr = freq.get(rs); r, a = (fr[0], fr[1]) if fr else (imp[rs][0], imp[rs][1]) if rs in imp else ('', '')
        afs = fr[2] if fr else [''] * 5
        if rs in meas:
            g = meas[rs]; ds = g.count(a) if a else ''; src = 'medido'
        elif rs in imp:
            ds = imp[rs][2]; maf = min(float(afs[0] or 0.5), 1 - float(afs[0] or 0.5)) if afs[0] else 0.5
            src = 'imputado' if abs(ds - round(ds)) <= 0.1 else 'imputado_incierto'
            g = imp[rs][0] * (2 - round(ds)) + imp[rs][1] * round(ds)
        else: g = ''; ds = ''; src = 'no_disponible'
        o.write('\t'.join(map(str, [rs, v[0], v[1], r, a, src, g, ds] + afs)) + '\n')
print('ok', len(rsids))
