#!/bin/bash
# Une 1000G (sitios del chip) + Santiago (medido) por cromosoma; luego genoma completo, LD-prune y PCA de 1000G con proyección.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
P2=/opt/mm/bt/bin/plink2; A=$S/anc/kg; mkdir -p $A
for c in $(seq 1 22); do
  [ -s $A/m_chr$c.pgen ] && continue
  # Santiago: objetivo corregido de la imputación (ALT completado desde el panel)
  $P2 --vcf $S/imp/t_$c.fix.vcf.gz --set-all-var-ids '@:#:$r:$a' --new-id-max-allele-len 60 truncate --snps-only just-acgt \
      --make-pgen --out $A/s_chr$c --threads 2 > /dev/null 2>&1 || { echo "falta t_$c"; exit 1; }
  cut -f3 $A/s_chr$c.pvar | grep -v '^ID' > $A/s_chr$c.ids
  $P2 --pfile $S/nea/kg_chip_chr$c --extract $A/s_chr$c.ids --make-pgen --out $A/k_chr$c --threads 2 > /dev/null 2>&1 || exit 1
  cut -f3 $A/k_chr$c.pvar | grep -v '^ID' > $A/k_chr$c.ids
  $P2 --pfile $A/s_chr$c --extract $A/k_chr$c.ids --make-pgen --out $A/s2_chr$c --threads 2 > /dev/null 2>&1
  printf "$A/k_chr$c\n$A/s2_chr$c\n" > $A/ml_$c.txt
  $P2 --pmerge-list $A/ml_$c.txt pfile --make-pgen --out $A/m_chr$c --threads 2 > /dev/null 2>&1 || { echo "merge fallo $c"; tail -5 $A/m_chr$c.log; exit 1; }
  rm -f $A/s_chr$c.* $A/s2_chr$c.* $A/k_chr$c.*
  echo "merged chr$c"
done
for c in $(seq 1 22); do echo $A/m_chr$c; done > $A/all.txt
$P2 --pmerge-list $A/all.txt pfile --make-pgen --out $A/kgS --threads 3 > /dev/null 2>&1
# LD-prune en 1000G (sin Santiago), MAF>=5%, fuera de MHC y la inversión de chr8
grep -v SANTIAGO $A/kgS.psam | cut -f1 > $A/kg_ids.txt
printf "6\t25000000\t35000000\tMHC\n8\t7000000\t13000000\tinv8\n" > $A/excl.txt
$P2 --pfile $A/kgS --keep $A/kg_ids.txt --maf 0.05 --exclude range $A/excl.txt --indep-pairwise 200 50 0.2 --out $A/prune --threads 3 > /dev/null 2>&1
$P2 --pfile $A/kgS --keep $A/kg_ids.txt --extract $A/prune.prune.in --pca 20 allele-wts --freq --out $A/pca --threads 3 > /dev/null 2>&1
$P2 --pfile $A/kgS --extract $A/prune.prune.in --read-freq $A/pca.afreq --score $A/pca.eigenvec.allele 2 5 header-read no-mean-imputation variance-standardize --score-col-nums 6-25 --out $A/proj --threads 3 > /dev/null 2>&1
echo "PCA_DONE $(wc -l < $A/prune.prune.in) SNPs podados"
