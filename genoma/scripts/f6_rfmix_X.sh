#!/bin/bash
# RFMix en X no-PAR: query = X medido de Santiago (haploide, codificado 0|0 / 1|1); referencia = MUJERES de IBS, YRI y nativas >=95%.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
R=$S/anc/rfmix; c=X
[ -s $R/out_X.msp.tsv ] && exit 0
[ -s $S/imp/t_X.fix.vcf.gz ] || exit 1; [ -s $S/ref/1kg/chrX.vcf.gz.tbi ] || exit 1
bcftools view -v snps -m2 -M2 $S/imp/t_X.fix.vcf.gz | awk 'BEGIN{OFS="\t"} /^#/{print;next} {g=$10; if(g=="0"||g=="0/0")$10="0|0"; else if(g=="1"||g=="1/1")$10="1|1"; else next; print}' | bgzip > $R/q_X.vcf.gz; tabix -f $R/q_X.vcf.gz
awk 'NR>1 && $4=="female" && ($2=="IBS"||$2=="YRI"){print $1"\t"($2=="IBS"?"EUR":"AFR")}' $S/ref/integrated_call_samples_v3.20130502.ALL.panel > $R/smapX.txt
awk 'NR==FNR{sex[$1]=$4;next} sex[$1]=="female"{print $1"\tNAT"}' $S/ref/integrated_call_samples_v3.20130502.ALL.panel $S/anc/natsel/nat95.txt >> $R/smapX.txt
cut -f1 $R/smapX.txt > $R/refsX.txt; cut -f2 $R/smapX.txt | sort | uniq -c
bcftools query -f '%CHROM\t%POS\n' $R/q_X.vcf.gz > $R/pos_X.txt
bcftools view -S $R/refsX.txt -R $R/pos_X.txt -v snps -m2 -M2 $S/ref/1kg/chrX.vcf.gz -Oz -o $R/r_X.vcf.gz && tabix -f $R/r_X.vcf.gz
zcat $S/ref/maps/chrX.b37.gmap.gz | awk 'NR>1{print "X\t"$1"\t"$3}' > $R/gmap_X.txt
rfmix -f $R/q_X.vcf.gz -r $R/r_X.vcf.gz -m $R/smapX.txt -g $R/gmap_X.txt -o $R/out_X --chromosome=X --n-threads=2 -t 30 -w 10 > $R/log_X.txt 2>&1 && echo "RFMIX chrX $(date +%T)" || { echo "RFMIX FAIL chrX"; tail -3 $R/log_X.txt; }
