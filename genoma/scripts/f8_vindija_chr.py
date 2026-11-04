"""Fase 8: alelos 'neandertales' en sitios del chip. Candidato = alelo con AF<=0.5% en africanos no mezclados (1000G
YRI/ESN/GWD/MSL/LWK) y >=2% en alguna superpoblación no africana. Se consulta Vindija33.19 (remoto, tabix) y se
retienen sitios donde Vindija es homocigota para ese alelo. Cuenta copias en Santiago y en los 2,504 de 1000G."""
import sys, os, subprocess, collections
c = sys.argv[1]
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
N = S + '/nea'; BT = '/opt/mm/bt/bin/bcftools'; P2 = '/opt/mm/bt/bin/plink2'
if os.path.exists(f'{N}/vin_chr{c}.done'): sys.exit(0)
def rd(g):
    d = {}
    for l in open(f'{N}/freq_chr{c}.{g}.afreq').read().splitlines()[1:]:
        f = l.split('\t'); d[f[1]] = (f[2], f[3], float(f[4]))
    return d
af = {g: rd(g) for g in ['AFRU', 'EUR', 'EAS', 'AMR', 'SAS']}
cand = {}
for vid, (r, a, fa) in af['AFRU'].items():
    others = [af[g][vid][2] for g in ['EUR', 'EAS', 'AMR', 'SAS'] if vid in af[g]]
    if fa <= 0.005 and max(others) >= 0.02: cand[vid] = a           # alelo ALT ausente en África
    elif fa >= 0.995 and min(others) <= 0.98: cand[vid] = r          # alelo REF ausente en África
reg = f'{N}/vreg_{c}.txt'
with open(reg, 'w') as o:
    for vid in sorted(cand, key=lambda x: int(x.split(':')[1])): o.write(f"{c}\t{vid.split(':')[1]}\n")
url = f'https://cdna.eva.mpg.de/neandertal/Vindija/VCF/Vindija33.19/chr{c}_mq25_mapab100.vcf.gz'
q = subprocess.run([BT, 'query', '-R', reg, '-f', '%POS\t%REF\t%ALT\t[%GT]\n', url], capture_output=True, text=True, cwd=N)
vin = {}
for line in q.stdout.splitlines():
    p, r, a, g = line.split('\t'); vin[p] = (r, a, g)
keep = {}
for vid, nal in cand.items():
    _, p, r, a = vid.split(':')
    v = vin.get(p)
    if not v or v[0] != r: continue
    vr, va, g = v
    alle = [vr] + ([] if va == '.' else va.split(','))
    if g not in ('0/0', '1/1'): continue
    gal = alle[int(g[0])]
    if gal == nal: keep[vid] = nal
# conteos 1000G (score con peso 1 al alelo neandertal)
sf = f'{N}/nscore_{c}.txt'
with open(sf, 'w') as o:
    for vid, nal in keep.items(): o.write(f'{vid}\t{nal}\t1\n')
subprocess.run([P2, '--pfile', f'{N}/kg_chip_chr{c}', '--score', sf, '1', '2', '3', 'cols=dosagesum,scoresums', 'no-mean-imputation',
                '--out', f'{N}/nkg_{c}', '--threads', '2'], capture_output=True)
# Santiago (medido)
meas = {}
for l in open(S + '/data/genome.txt'):
    if l[0] == '#': continue
    rs, ch, p, g = l.rstrip('\n').split('\t')
    if ch == c: meas[p] = g
n = 0; tot = 0
with open(f'{N}/nsant_{c}.tsv', 'w') as o:
    for vid, nal in keep.items():
        p = vid.split(':')[1]; g = meas.get(p, '--')
        if g == '--': continue
        k = g.count(nal); n += 1; tot += k
        o.write(f'{vid}\t{nal}\t{g}\t{k}\n')
open(f'{N}/vin_chr{c}.done', 'w').write(f'{len(cand)}\t{len(vin)}\t{len(keep)}\t{n}\t{tot}\n')
print(f'chr{c}: candidatos {len(cand)}, con dato en Vindija {len(vin)}, Vindija homocigota alelo no-africano {len(keep)}, Santiago {tot} copias en {n} sitios', flush=True)
