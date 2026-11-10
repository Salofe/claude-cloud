"""PGS por cromosoma para Santiago (dosis imputadas) y los 2,504 de 1000G (genotipos), mismas variantes.
Pesos expresados respecto al alelo ALT (la constante se cancela al comparar con la referencia).
Filtros: SNPs bialélicos, no palindrómicos, MAF>=1% en 1000G (plink2 --maf 0.01)."""
import os, sys, os, subprocess, collections
c = sys.argv[1]
MODE = sys.argv[2] if len(sys.argv) > 2 else 'imp'   # 'med' = solo variantes medidas en el chip
SUF = '' if MODE == 'imp' else '_med'
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
PGSR = os.environ.get('PGSROOT', S + '/pgs')
W = f'{PGSR}/work'; os.makedirs(W, exist_ok=True)
BT = '/opt/mm/bt/bin/bcftools'; P2 = '/opt/mm/bt/bin/plink2'
comp = {'A': 'T', 'C': 'G', 'G': 'C', 'T': 'A'}
rows = collections.defaultdict(list); pids = set()
for l in open(f'{PGSR}/bychr/chr{c}.tsv'):
    p, ea, oa, pid, w = l.rstrip('\n').split('\t')
    rows[int(p)].append((ea, oa, pid, float(w))); pids.add(pid)
pids = sorted(pids)
# sitios del panel (= sitios imputados de Santiago) en posiciones de PGS, con su dosis
reg = f'{W}/reg{c}.txt'
with open(reg, 'w') as o:
    for p in sorted(rows): o.write(f'{c}\t{p}\n')
IMPF = os.environ.get('GIMP', S + '/imp/imp_chr{c}.vcf.gz').format(c=c)   # VCF imputado (GIMP admite {c})
SMP = ['-s', os.environ['GSAMPLE']] if os.environ.get('GSAMPLE') else []      # muestra, si el VCF tiene varias
q = subprocess.run([BT, 'query', '-R', reg, *SMP, '-i', 'TYPE="snp"', '-f', '%POS\t%REF\t%ALT\t[%DS]\t%INFO/IMP\n', IMPF],
                   capture_output=True, text=True, check=True).stdout
sites = {}
for line in q.splitlines():
    p, r, a, ds, imp = line.split('\t')
    if MODE == 'med' and imp == '1': continue
    if ',' in a or len(r) != 1 or len(a) != 1: continue
    sites.setdefault(int(p), []).append((r, a, float(ds)))
st = collections.Counter()
score = {}  # id -> {pid: w_alt}
dose = {}
for p, lst in rows.items():
    if p not in sites or len(sites[p]) != 1: st['sin_sitio_o_multi'] += len(lst); continue
    r, a, ds = sites[p][0]
    if {r, a} in ({'A', 'T'}, {'C', 'G'}): st['palindromico'] += len(lst); continue
    vid = f'{c}:{p}:{r}:{a}'
    for ea, oa, pid, w in lst:
        if (ea == a and oa in (r, '?')): wa = w
        elif (ea == r and oa in (a, '?')): wa = -w
        elif comp.get(ea) == a and comp.get(oa, '?') in (r, '?'): wa = w; st['flip'] += 1
        elif comp.get(ea) == r and comp.get(oa, '?') in (a, '?'): wa = -w; st['flip'] += 1
        else: st['alelos_no_coinciden'] += 1; continue
        score.setdefault(vid, {})[pid] = score.get(vid, {}).get(pid, 0) + wa
        dose[vid] = ds; st['ok'] += 1
sf = f'{W}/score_chr{c}{SUF}.tsv'
with open(sf, 'w') as o:
    o.write('ID\tA1\t' + '\t'.join(pids) + '\n')
    for vid, d in score.items():
        o.write(vid + '\t' + vid.split(':')[3] + '\t' + '\t'.join(repr(d.get(pid, 0.0)) for pid in pids) + '\n')
with open(f'{W}/extract_chr{c}{SUF}.txt', 'w') as o:
    o.write('\n'.join(score) + '\n')
cmd = [P2, '--vcf', f'{S}/ref/1kg/chr{c}.vcf.gz', '--set-all-var-ids', '@:#:$r:$a', '--new-id-max-allele-len', '60', 'truncate',
       '--extract', f'{W}/extract_chr{c}{SUF}.txt', '--maf', '0.01', '--threads', '2', '--memory', '3000',
       '--score', sf, '1', '2', 'header-read', 'cols=scoresums', 'list-variants', '--score-col-nums', f'3-{len(pids)+2}',
       '--out', f'{W}/kg_chr{c}{SUF}']
REUSE = os.environ.get('GKGREUSE')
if REUSE and os.path.exists(f'{REUSE}/kg_chr{c}{SUF}.sscore.vars'):
    import shutil
    for ext in ('.sscore', '.sscore.vars'): shutil.copy(f'{REUSE}/kg_chr{c}{SUF}{ext}', f'{W}/kg_chr{c}{SUF}{ext}')
else:
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0: print(r.stdout[-2000:], r.stderr[-2000:]); sys.exit(1)
used = set(open(f'{W}/kg_chr{c}{SUF}.sscore.vars').read().split())
# Santiago
tot = collections.Counter(); nvar = collections.Counter()
for vid in used:
    if vid not in score: continue
    for pid, wa in score[vid].items():
        tot[pid] += wa * dose[vid]
        if wa != 0: nvar[pid] += 1
with open(f'{W}/sant_chr{c}{SUF}.tsv', 'w') as o:
    for pid in pids: o.write(f'{pid}\t{tot[pid]!r}\t{nvar[pid]}\n')
print(c, dict(st), 'usadas', len(used))
