"""PGS por haplotipo del hijo en un dúo faseado por herencia: cuánto del score viene de la copia materna y cuánto de la paterna.
Usa las mismas variantes y pesos que f5_pgs_chr.py (modo imputado) y la media/DE ajustadas por ancestría de f5_pgs_final.py.
z_mat y z_pat se expresan en DE del score diploide, cada uno respecto a media/2; z_mat + z_pat = z total.
Uso: PGSROOT=<set> f12_pgs_haplo.py <dir_fam> <HIJO> <resultados.json del hijo> <salida.tsv>"""
import os, sys, subprocess, collections, json
FAM, KID, resf, out = sys.argv[1:5]
PGSR = os.environ['PGSROOT']; W = PGSR + '/work'; BT = '/opt/mm/bt/bin/bcftools'
comp = {'A': 'T', 'C': 'G', 'G': 'C', 'T': 'A'}
tot = {0: collections.Counter(), 1: collections.Counter()}; nv = collections.Counter()
for c in range(1, 23):
    f = f'{PGSR}/bychr/chr{c}.tsv'
    if not os.path.exists(f) or not os.path.exists(f'{W}/kg_chr{c}.sscore.vars'): continue
    used = set(open(f'{W}/kg_chr{c}.sscore.vars').read().split())
    rows = collections.defaultdict(list)
    for l in open(f):
        p, ea, oa, pid, w = l.rstrip('\n').split('\t'); rows[int(p)].append((ea, oa, pid, float(w)))
    reg = f'{W}/hreg{c}.txt'; open(reg, 'w').write(''.join(f'{c}\t{p}\n' for p in sorted(rows)))
    q = subprocess.run([BT, 'query', '-R', reg, '-s', KID, '-i', 'TYPE="snp"', '-f', '%POS\t%REF\t%ALT[\t%AP1\t%AP2]\n', f'{FAM}/fam_chr{c}.vcf.gz'], capture_output=True, text=True, check=True).stdout
    os.remove(reg)
    for line in q.splitlines():
        p, r, a, a1, a2 = line.split('\t')
        vid = f'{c}:{p}:{r}:{a}'
        if vid not in used: continue
        for ea, oa, pid, w in rows[int(p)]:
            if ea == a and oa in (r, '?'): wa = w
            elif ea == r and oa in (a, '?'): wa = -w
            elif comp.get(ea) == a and comp.get(oa, '?') in (r, '?'): wa = w
            elif comp.get(ea) == r and comp.get(oa, '?') in (a, '?'): wa = -w
            else: continue
            tot[0][pid] += wa * float(a1); tot[1][pid] += wa * float(a2); nv[pid] += 1
res = json.load(open(resf))['res']
with open(out, 'w') as o:
    o.write('pgs\trasgo\tvariantes\tz_total\tz_materno\tz_paterno\n')
    for pid in sorted(nv):
        r = res.get(pid)
        if not r or 'mu_ancestry' not in r: continue
        mu, sd = r['mu_ancestry'], r['sd_ancestry']
        zm = (tot[0][pid] - mu / 2) / sd; zp = (tot[1][pid] - mu / 2) / sd
        o.write(f"{pid}\t{r['trait']}\t{nv[pid]}\t{zm+zp:+.2f}\t{zm:+.2f}\t{zp:+.2f}\n")
print('ok', len(nv))
