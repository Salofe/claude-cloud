#!/bin/bash
# Tras la imputación del dúo: listas de genotipos con origen parental, proyección PCA de la madre y sus PGS.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
M=$S/mama; F=$S/fam; D=/home/user/claude-cloud/genoma/scripts
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
until grep -q DUO_ALL_DONE $F/duo_all.log; do sleep 30; done
cd $D
python3 f12_familia_list.py $F/listas/todo.txt $F/listas/todo.tsv $F SANTIAGO MAMA $S/data/genome.txt $M/data/genome.txt
# PCA: proyectar a los dos desde los genotipos faseados (sin faltantes) sobre los mismos pesos de 1000G
mkdir -p $M/kg; A=$S/anc/kg
bcftools concat $(for c in $(seq 1 22); do echo $F/duo_$c.vcf.gz; done) -Oz -o $M/kg/duo_all.vcf.gz
plink2 --vcf $M/kg/duo_all.vcf.gz --set-all-var-ids '@:#:$r:$a' --new-id-max-allele-len 60 truncate --snps-only just-acgt --max-alleles 2 \
  --extract $A/prune.prune.in --read-freq $A/pca.afreq --score $A/pca.eigenvec.allele 2 6 header-read no-mean-imputation variance-standardize \
  --score-col-nums 7-26 --out $M/kg/projduo --threads 2 > $M/kg/proj.log 2>&1
grep -v SANTIAGO $A/proj.sscore > $M/kg/proj.sscore; awk -F"\t" -v OFS="\t" '$1=="MAMA"{print "0",$0}' $M/kg/projduo.sscore >> $M/kg/proj.sscore
echo "PCA $(grep -c . $M/kg/proj.sscore)"; rm -f $M/kg/duo_all.vcf.gz
export GIMP="$F/fam_chr{c}.vcf.gz" GSAMPLE=MAMA GKG=$M/kg
for N in pgs4 pgs3 pgs pgs2; do
  export PGSROOT=$M/$N
  seq 1 22 | xargs -P 2 -I{} python3 f5_pgs_chr.py {} med > $M/$N/chr_med.log 2>&1
  if [ -d $S/$N/work ]; then export GKGREUSE=$S/$N/work; else unset GKGREUSE; fi
  seq 1 22 | xargs -P 2 -I{} python3 f5_pgs_chr.py {} > $M/$N/chr_imp.log 2>&1
  unset GKGREUSE
  python3 f5_pgs_final.py _med > $M/$N/final_med.txt 2>&1; python3 f5_pgs_final.py > $M/$N/final_imp.txt 2>&1
  echo "PGS $N $(date +%T) $(grep -c Zanc $M/$N/final_med.txt) med, $(grep -c Zanc $M/$N/final_imp.txt) imp"
done
echo POST_DONE
