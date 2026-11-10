#!/bin/bash
# Calibración de la imputación de UNA variante rara: cada persona del panel se reduce a los sitios del chip,
# se quita del panel y se imputa con el resto (folds). Salida: dosis imputada vs genotipo real.
# Uso: f11_calib_imputacion.sh <panel.vcf.gz> <panel_chip.vcf.gz> <map> <chr:pos> <nfolds> <outdir>
set -e
PANEL=$1; CHIP=$2; MAP=$3; SITE=$4; NF=$5; O=$6
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
mkdir -p $O; cd $O
bcftools query -l $PANEL > samples.txt
bcftools query -r $SITE -f '[%SAMPLE\t%GT\n]' $PANEL > truth.tsv
# portadores en folds distintos; el resto al azar (semilla fija)
python3 - $NF <<'PY'
import sys, random
nf = int(sys.argv[1]); random.seed(7)
tr = dict(l.split() for l in open('truth.tsv'))
car = [s for s, g in tr.items() if '1' in g]; non = [s for s in tr if s not in car]
random.shuffle(non); random.shuffle(car)
folds = [[] for _ in range(nf)]
for i, s in enumerate(car): folds[i % nf].append(s)
for i, s in enumerate(non): folds[i % nf].append(s)
for k, f in enumerate(folds): open(f'fold{k}.txt', 'w').write('\n'.join(f) + '\n')
print('portadores:', len(car), 'folds:', nf)
PY
for k in $(seq 0 $((NF-1))); do
  [ -s res$k.tsv ] && continue
  bcftools view -S ^fold$k.txt $PANEL -Oz -o ref$k.vcf.gz
  bcftools view -S fold$k.txt $CHIP | bcftools +setGT -- -t a -n u 2>/dev/null | bcftools view -Oz -o tg$k.vcf.gz
  java -Xmx6g -jar /opt/mm/gen/share/beagle-5.5_27Feb25.75f-0/beagle.jar ref=ref$k.vcf.gz gt=tg$k.vcf.gz map=$MAP out=imp$k nthreads=4 impute=true gp=false ap=true seed=$((100+k)) > log$k.txt 2>&1
  bcftools index -f imp$k.vcf.gz
  bcftools query -r $SITE -f '[%SAMPLE\t%GT\t%DS\n]' imp$k.vcf.gz > res$k.tsv
  rm -f ref$k.vcf.gz tg$k.vcf.gz imp$k.vcf.gz imp$k.vcf.gz.csi
  echo "fold $k $(date +%T)"
done
echo CAL_DONE
