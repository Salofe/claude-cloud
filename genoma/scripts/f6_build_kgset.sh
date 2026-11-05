#!/bin/bash
# Une 1000G (sitios del chip) + Santiago (medido); LD-prune y PCA de 1000G con proyección de Santiago.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
P2=/opt/mm/bt/bin/plink2; P1=/opt/mm/gen/bin/plink; A=$S/anc/kg; mkdir -p $A
rm -f $A/mergelist.txt
for c in $(seq 1 22); do
  $P2 --vcf $S/imp/t_$c.fix.vcf.gz --set-all-var-ids '@:#:$r:$a' --new-id-max-allele-len 60 truncate --snps-only just-acgt \
      --max-alleles 2 --make-bed --out $A/s_chr$c --threads 3 > /dev/null 2>&1 || { echo "falta t_$c"; exit 1; }
  $P2 --pfile $S/nea/kg_chip_chr$c --extract <(cut -f2 $A/s_chr$c.bim) --make-bed --out $A/k_chr$c --threads 3 > /dev/null 2>&1 || exit 1
  echo "$A/k_chr$c" >> $A/mergelist.txt; echo "$A/s_chr$c" >> $A/mergelist.txt
done
head -1 $A/mergelist.txt > $A/first.txt; tail -n +2 $A/mergelist.txt > $A/rest.txt
$P1 --bfile $(cat $A/first.txt) --merge-list $A/rest.txt --make-bed --out $A/kgS --allow-no-sex > $A/merge.log 2>&1
if [ -s $A/kgS-merge.missnp ]; then
  for f in $(cat $A/mergelist.txt); do $P1 --bfile $f --exclude $A/kgS-merge.missnp --make-bed --out ${f}_x --allow-no-sex > /dev/null 2>&1; done
  sed 's/$/_x/' $A/mergelist.txt > $A/ml2.txt; head -1 $A/ml2.txt > $A/first.txt; tail -n +2 $A/ml2.txt > $A/rest.txt
  $P1 --bfile $(cat $A/first.txt) --merge-list $A/rest.txt --make-bed --out $A/kgS --allow-no-sex > $A/merge.log 2>&1
fi
grep -E "people|variants" $A/merge.log | tail -3
awk '$2!="SANTIAGO"{print $1"\t"$2}' $A/kgS.fam > $A/kg_ids.txt
printf "6\t25000000\t35000000\tMHC\n8\t7000000\t13000000\tinv8\n" > $A/excl.txt
$P2 --bfile $A/kgS --keep $A/kg_ids.txt --maf 0.05 --exclude range $A/excl.txt --indep-pairwise 200 50 0.2 --out $A/prune --threads 3 > /dev/null 2>&1
$P2 --bfile $A/kgS --keep $A/kg_ids.txt --extract $A/prune.prune.in --pca 20 allele-wts --freq --out $A/pca --threads 3 > /dev/null 2>&1
$P2 --bfile $A/kgS --extract $A/prune.prune.in --read-freq $A/pca.afreq --score $A/pca.eigenvec.allele 2 6 header-read no-mean-imputation variance-standardize --score-col-nums 7-26 --out $A/proj --threads 3 > /dev/null 2>&1
echo "PCA_DONE $(wc -l < $A/prune.prune.in) SNPs podados"
