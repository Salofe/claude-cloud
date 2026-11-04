#!/bin/bash
# ADMIXTURE no supervisado K=3..6 con referencias de 1000G (IBS TSI CEU YRI PEL MXL CLM PUR CHB) + Santiago, SNPs podados.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
P2=/opt/mm/bt/bin/plink2; A=$S/anc/kg; D=$S/anc/admx_kg; mkdir -p $D
awk 'NR>1 && ($2=="IBS"||$2=="TSI"||$2=="CEU"||$2=="YRI"||$2=="PEL"||$2=="MXL"||$2=="CLM"||$2=="PUR"||$2=="CHB"){print $1}' $S/ref/integrated_call_samples_v3.20130502.ALL.panel > $D/keep.txt
echo SANTIAGO >> $D/keep.txt
$P2 --pfile $A/kgS --keep $D/keep.txt --extract $A/prune.prune.in --geno 0.01 --make-bed --out $D/d --threads 3 > /dev/null 2>&1
cd $D
for K in 3 4 5 6; do /opt/mm/gen/bin/admixture --cv -j3 -s 7 d.bed $K > log$K.out 2>&1; grep CV log$K.out; done
