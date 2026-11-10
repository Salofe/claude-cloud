"""Genotipa una lista de rsIDs en el dúo madre-hijo ya faseado e imputado (fam_chr*.vcf.gz).
Hijo: alelo materno | alelo paterno. Madre: alelo transmitido | no transmitido. En sitios imputados da la probabilidad
del alelo ALT en cada haplotipo (AP1, AP2). Posición GRCh37 desde dbSNP (solo rsIDs públicos, caché local).
Uso: f12_familia_list.py <lista_rsids.txt> <salida.tsv> <dir_fam> <HIJO> <MADRE> <genoma_hijo.txt> <genoma_madre.txt>"""
import sys, json, time, urllib.request, subprocess, collections, os
inp, out, FAM, KID, MOM, gk, gm = sys.argv[1:8]
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
BT = '/opt/mm/bt/bin/bcftools'
rsids = [l.split()[0] for l in open(inp) if l.strip().startswith('rs')]
rsids = list(dict.fromkeys(rsids))
cache_f = S + '/face/pos_cache.json'
cache = json.load(open(cache_f)) if os.path.exists(cache_f) else {}
def dbsnp(rs):
    d = None
    for t in range(4):
        try: d = json.load(urllib.request.urlopen(f'https://api.ncbi.nlm.nih.gov/variation/v0/refsnp/{rs[2:]}', timeout=30)); break
        except Exception: time.sleep(2 ** t)
    if not d or 'primary_snapshot_data' not in d: return None
    for pl in d['primary_snapshot_data']['placements_with_allele']:
        tr = pl.get('placement_annot', {}).get('seq_id_traits_by_assembly', [])
        if any('GRCh37' in x.get('assembly_name', '') for x in tr) and pl['seq_id'].startswith('NC_0000'):
            chrom = str(int(pl['seq_id'].split('.')[0][-2:])); chrom = {'23': 'X', '24': 'Y'}.get(chrom, chrom)
            return [chrom, pl['alleles'][0]['allele']['spdi']['position'] + 1]
    return None
for rs in rsids:
    if rs not in cache: cache[rs] = dbsnp(rs); time.sleep(0.34)
json.dump(cache, open(cache_f, 'w'))
def meas(f):
    d = {}
    for l in open(f):
        if l[0] == '#': continue
        r, c, p, g = l.rstrip('\n').split('\t')
        if r in cache and g != '--' and set(g) <= set('ACGT'): d[r] = g
    return d
mk, mm = meas(gk), meas(gm)
bychr = collections.defaultdict(list)
for rs in rsids:
    v = cache.get(rs)
    if v: bychr[v[0]].append((rs, v[1]))
res = {}
for c, lst in bychr.items():
    f = f'{FAM}/fam_chr{c}.vcf.gz'
    if not os.path.exists(f + '.tbi'): continue
    reg = f'{FAM}/_reg_{c}.txt'; open(reg, 'w').write(''.join(f'{c}\t{p}\n' for _, p in lst))
    posrs = collections.defaultdict(list)
    for rs, p in lst: posrs[p].append(rs)
    q = subprocess.run([BT, 'query', '-R', reg, '-s', f'{KID},{MOM}', '-f', '%POS\t%ID\t%REF\t%ALT\t%INFO/IMP[\t%GT\t%DS\t%AP1\t%AP2]\n', f], capture_output=True, text=True).stdout
    for line in q.splitlines():
        p, i, r, a, im, kgt, kds, k1, k2, mgt, mds, m1, m2 = line.split('\t')
        for rs in posrs.get(int(p), []):
            if i == rs or (i == '.' and len(r) == 1 and len(a) == 1 and rs not in res):
                res[rs] = dict(ref=r, alt=a, imp=(im == '1'), k=(kgt, kds, k1, k2), m=(mgt, mds, m1, m2))
    os.remove(reg)
def al(g, r, a): return '|'.join(r if x == '0' else a for x in g.split('|'))
with open(out, 'w') as o:
    o.write('rsid\tchr\tpos\tref\talt\tfuente\thijo_materno|paterno\thijo_P(alt)_mat\thijo_P(alt)_pat\tmadre_transmitido|no\tmadre_ds\thijo_chip\tmadre_chip\torigen_del_alt_en_hijo\n')
    for rs in rsids:
        v = cache.get(rs); x = res.get(rs)
        if not v: o.write(f'{rs}\t\t\t\t\tsin_posicion\n'); continue
        if not x: o.write(f'{rs}\t{v[0]}\t{v[1]}\t\t\tno_en_panel\t\t\t\t\t\t{mk.get(rs, "")}\t{mm.get(rs, "")}\t\n'); continue
        kgt, kds, k1, k2 = x['k']; mgt, mds, m1, m2 = x['m']
        src = 'imputado' if x['imp'] else 'medido'
        ka = kgt.split('|')
        orig = {('1', '1'): 'ambos', ('1', '0'): 'materno', ('0', '1'): 'paterno', ('0', '0'): 'ninguno'}[tuple(ka)]
        if x['imp'] and (abs(float(k1) - round(float(k1))) > 0.1 or abs(float(k2) - round(float(k2))) > 0.1): orig += '_incierto'
        o.write('\t'.join([rs, v[0], str(v[1]), x['ref'], x['alt'], src, al(kgt, x['ref'], x['alt']), k1, k2, al(mgt, x['ref'], x['alt']), mds, mk.get(rs, ''), mm.get(rs, ''), orig]) + '\n')
print('ok', len(rsids), 'con dato', len(res))
