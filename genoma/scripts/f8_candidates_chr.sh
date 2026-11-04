#!/bin/bash
# Fase 8: frecuencias por población (1000G) en las posiciones medidas del chip, por cromosoma.
c=$1
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
N=$S/nea; mkdir -p $N
[ -s $N/freq_chr$c.done ] && exit 0
[ -s $S/ref/1kg/chr$c.vcf.gz.tbi ] || { echo "panel chr$c no listo"; exit 1; }
awk -F'\t' -v c=$c '$2==c && $4!="--" && $4 ~ /^[ACGT]+$/ {print c"\t"$3"\t"$3"\t"$1}' $S/data/genome.txt > $N/range_chr$c.txt
awk 'NR>1{g=$3; if($2=="ASW"||$2=="ACB") g="AFRAM"; else if($3=="AFR") g="AFRU"; print $1"\t"$2"\t"$3"\t"g}' $S/ref/integrated_call_samples_v3.20130502.ALL.panel | awk 'BEGIN{print "#IID\tPOP\tSUPER\tGRP"}{print}' > $N/pops.tsv
/opt/mm/bt/bin/plink2 --vcf $S/ref/1kg/chr$c.vcf.gz --set-all-var-ids '@:#:$r:$a' --new-id-max-allele-len 60 truncate \
  --extract range $N/range_chr$c.txt --snps-only just-acgt --max-alleles 2 --pheno $N/pops.tsv --loop-cats GRP --freq \
  --threads 2 --memory 3000 --out $N/freq_chr$c > /dev/null 2>&1 || exit 1
/opt/mm/bt/bin/plink2 --vcf $S/ref/1kg/chr$c.vcf.gz --set-all-var-ids '@:#:$r:$a' --new-id-max-allele-len 60 truncate \
  --extract range $N/range_chr$c.txt --snps-only just-acgt --max-alleles 2 --make-pgen --threads 2 --memory 3000 --out $N/kg_chip_chr$c > /dev/null 2>&1 || exit 1
echo ok > $N/freq_chr$c.done; echo "freq chr$c"
