#!/bin/bash
# ¿Qué tan fiable es una dosis imputada ~0.75 en una variante rara? Se imputan europeos del panel (reducidos al chip,
# quitándolos del panel) y, en TODAS las variantes raras de la región (MAC 4–12 en el panel), se compara dosis vs genotipo real.
# Uso: f11_calib_raras.sh <panel.vcf.gz> <panel_chip.vcf.gz> <map> <lista_objetivos.txt> <nfolds> <outdir>
set -e
PANEL=$1; CHIP=$2; MAP=$3; TG=$4; NF=$5; O=$6
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
mkdir -p $O; cd $O
bcftools view -G -c ${MACMIN:-4} -C ${MACMAX:-12} -v snps -m2 -M2 $PANEL | bcftools query -f '%CHROM\t%POS\n' | sort -u -k1,1 -k2,2n > raras.pos
bcftools query -f '%CHROM\t%POS\n' $CHIP > chip.pos
awk 'NR==FNR{c[$2]=1;next} !($2 in c)' chip.pos raras.pos > raras_nochip.pos; wc -l < raras_nochip.pos
shuf --random-source=<(yes) $TG | split -n l/$NF -d - tf
for f in tf*; do
  [ -s out_$f.tsv ] && continue
  bcftools view -S ^$f $PANEL -Oz -o ref.vcf.gz
  if [ -n "$PHASED" ]; then bcftools view -S $f $CHIP -Oz -o tg.vcf.gz   # objetivos con su fase real (caso de un dúo/trío)
  else bcftools view -S $f $CHIP | bcftools +setGT -- -t a -n u 2>/dev/null | bcftools view -Oz -o tg.vcf.gz; fi
  java -Xmx6g -jar /opt/mm/gen/share/beagle-5.5_27Feb25.75f-0/beagle.jar ref=ref.vcf.gz gt=tg.vcf.gz map=$MAP out=imp nthreads=4 impute=true gp=false ap=false seed=11 > log_$f.txt 2>&1
  bcftools index -f imp.vcf.gz
  bcftools query -R raras_nochip.pos -f '%POS\t%REF\t%ALT[\t%DS]\n' imp.vcf.gz > ds.tsv
  bcftools view -S $f -R raras_nochip.pos $PANEL | bcftools query -f '%POS\t%REF\t%ALT[\t%GT]\n' > gt.tsv
  python3 - $f <<'PY'
import sys
f = sys.argv[1]
gt = {}
for l in open('gt.tsv'):
    x = l.rstrip('\n').split('\t'); gt[tuple(x[:3])] = [g.count('1') for g in x[3:]]
with open(f'out_{f}.tsv', 'w') as o:
    for l in open('ds.tsv'):
        x = l.rstrip('\n').split('\t'); k = tuple(x[:3])
        if k not in gt: continue
        for d, g in zip(x[3:], gt[k]):
            d = float(d)
            if d >= 0.05 or g > 0: o.write(f'{k[0]}\t{d}\t{g}\n')
PY
  rm -f ref.vcf.gz tg.vcf.gz imp.vcf.gz* ds.tsv gt.tsv; echo "$f $(date +%T)"
done
echo RARAS_DONE
