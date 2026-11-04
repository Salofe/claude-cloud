#!/bin/bash
# Experimento de precisión: 20 MXL + 10 IBS de 1000G reducidos a los sitios del chip de Santiago (chr$1), imputados con el panel SIN ellos.
c=${1:-20}
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
M=$S/imp/mask; mkdir -p $M
awk 'NR>1 && $2=="MXL"{print $1}' $S/ref/integrated_call_samples_v3.20130502.ALL.panel | head -20 > $M/t.txt
awk 'NR>1 && $2=="IBS"{print $1}' $S/ref/integrated_call_samples_v3.20130502.ALL.panel | head -10 >> $M/t.txt
bcftools query -f '%CHROM\t%POS\n' $S/imp/t_$c.fix.vcf.gz > $M/pos.txt
bcftools view -S $M/t.txt -R $M/pos.txt $S/ref/1kg/chr$c.vcf.gz -Oz -o $M/target.vcf.gz && tabix -f $M/target.vcf.gz
bcftools view -S ^$M/t.txt $S/ref/1kg/chr$c.vcf.gz -Oz -o $M/ref.vcf.gz && tabix -f $M/ref.vcf.gz
bcftools view -S $M/t.txt -q 0.01:minor $S/ref/1kg/chr$c.vcf.gz -Oz -o $M/truth.vcf.gz && tabix -f $M/truth.vcf.gz
java -Xmx3g -jar /opt/mm/gen/share/beagle-5.5_27Feb25.75f-0/beagle.jar ref=$M/ref.vcf.gz gt=$M/target.vcf.gz map=$S/ref/maps/plink.chr$c.GRCh37.map out=$M/imp nthreads=2 > $M/beagle.log 2>&1
tabix -f $M/imp.vcf.gz
python3 - $M <<'PY'
import sys, subprocess, collections, math
M = sys.argv[1]
def load(f, field):
    q = subprocess.run(['/opt/mm/bt/bin/bcftools', 'query', '-i', 'TYPE="snp"', '-f', f'%POS:%REF:%ALT\\t%INFO/IMP\\t[%{field}\\t]\\n', f], capture_output=True, text=True).stdout
    d = {}
    for l in q.splitlines():
        x = l.rstrip('\t').split('\t'); d[x[0]] = (x[1], x[2:])
    return d
tr = load(M + '/truth.vcf.gz', 'GT'); im = load(M + '/imp.vcf.gz', 'DS')
bins = collections.defaultdict(lambda: [0, 0, 0, 0, 0, 0, 0])  # n, sx, sy, sxx, syy, sxy, conc
for k, (_, gts) in tr.items():
    if k not in im or im[k][0] != '1': continue  # solo variantes imputadas (no medidas)
    x = [sum(int(a) for a in g.replace('|', '/').split('/')) for g in gts]
    y = [float(v) for v in im[k][1]]
    p = sum(x) / (2 * len(x)); maf = min(p, 1 - p)
    b = '1-5%' if maf < 0.05 else ('5-20%' if maf < 0.2 else '20-50%')
    for xi, yi in zip(x, y):
        B = bins[b]; B[0] += 1; B[1] += xi; B[2] += yi; B[3] += xi*xi; B[4] += yi*yi; B[5] += xi*yi; B[6] += (round(yi) == xi)
for b in ('1-5%', '5-20%', '20-50%'):
    n, sx, sy, sxx, syy, sxy, cc = bins[b]
    r = (n*sxy - sx*sy) / math.sqrt((n*sxx - sx*sx) * (n*syy - sy*sy))
    print(f'MAF {b}: genotipos {n}, r2 dosis-verdad = {r*r:.3f}, concordancia genotipo = {cc/n:.3f}')
PY
rm -f $M/ref.vcf.gz*
