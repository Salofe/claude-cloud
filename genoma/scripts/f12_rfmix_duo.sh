#!/bin/bash
# RFMix v2 sobre el dúo ya faseado por herencia (duo_$c.vcf.gz: hijo materno|paterno, madre transmitido|no transmitido).
# Refs 1000G: IBS (EUR), YRI (AFR), nativos >=95% (NAT), igual que f6_rfmix_chr.sh.  Uso: f12_rfmix_duo.sh <chr|X> <dir_fam>
c=$1; F=$2
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
R=$F/rfmix; mkdir -p $R; A=$S/anc/rfmix
[ -s $R/out_$c.msp.tsv ] && exit 0
if [ "$c" = X ]; then SM=$A/smapX.txt; Q=$F/duo_X.vcf.gz; else SM=$A/samplemap.txt; Q=$F/duo_$c.vcf.gz; fi
[ -s $Q ] || exit 1
cut -f1 $SM > $R/refs_$c.txt
bcftools view -v snps -m2 -M2 $Q -Oz -o $R/q_$c.vcf.gz && tabix -f $R/q_$c.vcf.gz
bcftools query -f '%CHROM\t%POS\n' $R/q_$c.vcf.gz > $R/pos_$c.txt
bcftools view -S $R/refs_$c.txt -R $R/pos_$c.txt -v snps -m2 -M2 $S/ref/1kg/chr$c.vcf.gz -Oz -o $R/r_$c.vcf.gz && tabix -f $R/r_$c.vcf.gz
zcat $S/ref/maps/chr$c.b37.gmap.gz | awk -v c=$c 'NR>1{print c"\t"$1"\t"$3}' > $R/gmap_$c.txt
rfmix -f $R/q_$c.vcf.gz -r $R/r_$c.vcf.gz -m $SM -g $R/gmap_$c.txt -o $R/out_$c --chromosome=$c --n-threads=${NT:-2} -t 30 -w 10 > $R/log_$c.txt 2>&1 \
  && echo "RFMIX chr$c $(date +%T)" || { echo "RFMIX FAIL chr$c"; tail -3 $R/log_$c.txt; }
rm -f $R/r_$c.vcf.gz* $R/q_$c.vcf.gz* $R/pos_$c.txt $R/refs_$c.txt
