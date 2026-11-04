#!/bin/bash
# Fase 2: imputación de un cromosoma con Beagle 5.5 y panel 1000G phase 3 (filtrado MAC>=2).
# Uso: f2_impute_chr.sh <chr>
set -e
c=$1
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
I=$S/imp; mkdir -p $I
REF=$S/ref/1kg/chr$c.vcf.gz
[ -s $I/imp_chr$c.vcf.gz.tbi ] && { echo "ya existe chr$c"; exit 0; }
mkdir $I/lock_$c 2>/dev/null || exit 0
trap "rmdir $I/lock_$c 2>/dev/null" EXIT
# 1) objetivo: sitios medidos del chr (X: solo no-PAR, haploide)
if [ "$c" = X ]; then RG="X:2699521-154931043"; else RG="$c"; fi
bcftools view -r $RG $S/vcf/medido_raw.vcf.gz -Oz -o $I/t_$c.raw.vcf.gz && tabix -f $I/t_$c.raw.vcf.gz
bcftools query -f '%CHROM\t%POS\n' $I/t_$c.raw.vcf.gz > $I/t_$c.pos
bcftools query -R $I/t_$c.pos -f '%CHROM\t%POS\t%REF\t%ALT\n' $REF > $I/t_$c.refsites
# 2) completar ALT desde el panel y descartar sitios incompatibles
python3 - $I/t_$c.raw.vcf.gz $I/t_$c.refsites $I/t_$c.fix.vcf <<'PY'
import sys, gzip, collections
raw, sites, out = sys.argv[1:4]
ref = collections.defaultdict(list)
for l in open(sites):
    ch, p, r, a = l.rstrip('\n').split('\t'); ref[p].append((r, a))
st = collections.Counter()
with gzip.open(raw, 'rt') as f, open(out, 'w') as o:
    for l in f:
        if l[0] == '#': o.write(l); continue
        x = l.rstrip('\n').split('\t'); p, r, a, g = x[1], x[3], x[4], x[9]
        cands = [ra for ra in ref.get(p, []) if ra[0] == r]
        if not cands: st['no_en_panel'] += 1; continue
        if a == '.':
            snv = [ra for ra in cands if len(ra[1]) == 1]
            if len(snv) != 1: st['ambiguo'] += 1; continue
            x[4] = snv[0][1]; st['homref_completado'] += 1
        elif not any(ra[1] == a for ra in cands): st['alt_distinto'] += 1; continue
        st['ok'] += 1
        o.write('\t'.join(x) + '\n')
print(sys.argv[3], dict(st), file=sys.stderr)
PY
bgzip -f $I/t_$c.fix.vcf && tabix -f $I/t_$c.fix.vcf.gz
MAP=$S/ref/maps/plink.chr$c.GRCh37.map
java -Xmx4g -jar /opt/mm/gen/share/beagle-5.5_27Feb25.75f-0/beagle.jar ref=$REF gt=$I/t_$c.fix.vcf.gz map=$MAP out=$I/imp_chr$c nthreads=${NT:-2} impute=true gp=false ap=false > $I/beagle_chr$c.stdout 2>&1
tabix -f $I/imp_chr$c.vcf.gz
rm -f $I/t_$c.raw.vcf.gz* $I/t_$c.refsites $I/t_$c.pos
echo "IMPUTADO chr$c $(date +%T)"
