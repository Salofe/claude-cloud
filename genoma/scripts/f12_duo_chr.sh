#!/bin/bash
# Dúo madre-hijo, un autosoma: (1) une los genotipos medidos, (2) faseo estadístico con Beagle, (3) corrección mendeliana,
# (4) imputación con entrada ya faseada. Salida: $F/fam_chr$c.vcf.gz (hijo: materno|paterno; madre: transmitido|no transmitido).
# Uso: f12_duo_chr.sh <chr> <hijo_medido.vcf.gz> <madre_medido.vcf.gz> <HIJO> <MADRE> <outdir>
set -e
c=$1; KV=$2; MV=$3; KID=$4; MOM=$5; F=$6
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
BG="java -Xmx7g -jar /opt/mm/gen/share/beagle-5.5_27Feb25.75f-0/beagle.jar"
REF=$S/ref/1kg/chr$c.vcf.gz; MAP=$S/ref/maps/plink.chr$c.GRCh37.map; D=$(cd "$(dirname "$0")" && pwd)
mkdir -p $F; cd $F
[ -s fam_chr$c.vcf.gz.tbi ] && { echo "ya existe chr$c"; exit 0; }
bcftools merge -r $c -m none $KV $MV -Ou | bcftools view -M2 -Oz -o m_$c.raw.vcf.gz && tabix -f m_$c.raw.vcf.gz
bcftools query -f '%CHROM\t%POS\n' m_$c.raw.vcf.gz | sort -u -k2,2n > m_$c.pos
bcftools query -R m_$c.pos -f '%POS\t%REF\t%ALT\n' $REF > m_$c.refsites
# completar ALT desde el panel (homocigotos de referencia) y descartar sitios incompatibles o duplicados
python3 - m_$c.raw.vcf.gz m_$c.refsites m_$c.fix.vcf <<'PY'
import sys, gzip, collections
raw, sites, out = sys.argv[1:4]
ref = collections.defaultdict(list)
for l in open(sites):
    p, r, a = l.rstrip('\n').split('\t'); ref[p].append((r, a))
st = collections.Counter(); seen = set()
with gzip.open(raw, 'rt') as f, open(out, 'w') as o:
    for l in f:
        if l[0] == '#': o.write(l); continue
        x = l.rstrip('\n').split('\t'); p, r, a = x[1], x[3], x[4]
        if p in seen: st['pos_duplicada'] += 1; continue
        cands = [ra for ra in ref.get(p, []) if ra[0] == r]
        if not cands: st['no_en_panel'] += 1; continue
        if a == '.':
            snv = [ra for ra in cands if len(ra[1]) == 1]
            if len(snv) != 1: st['ambiguo'] += 1; continue
            x[4] = snv[0][1]
        elif not any(ra[1] == a for ra in cands): st['alt_distinto'] += 1; continue
        seen.add(p); st['ok'] += 1; o.write('\t'.join(x) + '\n')
print(sys.argv[3], dict(st), file=sys.stderr)
PY
bgzip -f m_$c.fix.vcf && tabix -f m_$c.fix.vcf.gz
$BG ref=$REF gt=m_$c.fix.vcf.gz map=$MAP out=ph_$c nthreads=${NT:-4} impute=false seed=1 > ph_$c.stdout 2>&1
python3 $D/f12_duo_fase.py ph_$c.vcf.gz m_$c.fix.vcf.gz duo_$c.vcf $KID $MOM > duo_$c.stats
bgzip -f duo_$c.vcf && tabix -f duo_$c.vcf.gz
$BG ref=$REF gt=duo_$c.vcf.gz map=$MAP out=fam_chr$c nthreads=${NT:-4} impute=true gp=false ap=true seed=1 > fam_$c.stdout 2>&1
tabix -f fam_chr$c.vcf.gz
rm -f m_$c.raw.vcf.gz* m_$c.pos m_$c.refsites ph_$c.vcf.gz ph_$c.log
echo "DUO chr$c $(date +%T) $(cat duo_$c.stats | cut -c1-300)"
