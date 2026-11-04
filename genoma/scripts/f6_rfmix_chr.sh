#!/bin/bash
# RFMix v2 por cromosoma: query = haplotipos faseados de Santiago (Beagle) en sitios MEDIDOS; refs 1000G: IBS (EUR), YRI (AFR), 26 nativos >=95% (NAT).
c=$1
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
BT=/opt/mm/bt/bin/bcftools; R=$S/anc/rfmix; mkdir -p $R
[ -s $R/out_$c.msp.tsv ] && exit 0
[ -s $S/imp/imp_chr$c.vcf.gz.tbi ] || exit 1
[ -s $S/ref/1kg/chr$c.vcf.gz.tbi ] || exit 1
if [ ! -s $R/samplemap.txt ]; then
  awk 'NR>1 && $2=="IBS"{print $1"\tEUR"} NR>1 && $2=="YRI"{print $1"\tAFR"}' $S/ref/integrated_call_samples_v3.20130502.ALL.panel > $R/samplemap.txt
  awk '{print $1"\tNAT"}' $S/anc/natsel/nat95.txt >> $R/samplemap.txt
  cut -f1 $R/samplemap.txt > $R/refs.txt
fi
$BT view -e 'INFO/IMP=1' -v snps -m2 -M2 $S/imp/imp_chr$c.vcf.gz -Oz -o $R/q_$c.vcf.gz && tabix -f $R/q_$c.vcf.gz
$BT query -f '%CHROM\t%POS\n' $R/q_$c.vcf.gz > $R/pos_$c.txt
$BT view -S $R/refs.txt -R $R/pos_$c.txt -v snps -m2 -M2 $S/ref/1kg/chr$c.vcf.gz -Oz -o $R/r_$c.vcf.gz && tabix -f $R/r_$c.vcf.gz
zcat $S/ref/maps/chr$c.b37.gmap.gz | awk -v c=$c 'NR>1{print c"\t"$1"\t"$3}' > $R/gmap_$c.txt
/opt/mm/gen/bin/rfmix -f $R/q_$c.vcf.gz -r $R/r_$c.vcf.gz -m $R/samplemap.txt -g $R/gmap_$c.txt -o $R/out_$c --chromosome=$c --n-threads=2 -t 30 -w 10 > $R/log_$c.txt 2>&1 \
  && echo "RFMIX chr$c $(date +%T)" || { echo "RFMIX FAIL chr$c"; tail -3 $R/log_$c.txt; }
rm -f $R/r_$c.vcf.gz*
