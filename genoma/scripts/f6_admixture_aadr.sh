#!/bin/bash
# ADMIXTURE no supervisado K=3..8 con referencias modernas del AADR (HO) + Santiago (medido+imputado seguro).
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
D=$S/anc/admx; mkdir -p $D; cd $D
export PATH=/opt/mm/gen/bin:$PATH
printf "Spanish\nSpanish_North\nBasque\nItalian_North\nItalian_South\nSardinian\nFrench\nRussian\nMoroccan\nMozabite\nTurkish\nYoruba\nMandenka\nHan\nMixe\nZapotec\nMixtec\nMayan\nPima\nNahua\nKaritiana\nSurui\nQuechua\nSantiago\n" > pops.txt
cat > par <<P
genotypename: $S/anc/m_imp.geno
snpname: $S/anc/m_imp.snp
indivname: $S/anc/m_imp.ind
outputformat: PACKEDPED
genotypeoutname: $D/d.bed
snpoutname: $D/d.bim
indivoutname: $D/d.fam
poplistname: $D/pops.txt
P
convertf -p par > cf.log 2>&1
awk 'NR==FNR{p[$1]=$3;next}{print $2"\t"p[$2]}' $S/anc/m_imp.ind d.fam > ids.txt
# limitar tamaño por población (máx 25) para equilibrar
awk 'BEGIN{srand(3)} {n[$2]++; if(n[$2]<=25) print "0\t"$1}' <(awk '{print $1"\t"$2}' ids.txt) > /dev/null
awk '{c[$2]++; if(c[$2]<=25) print $1}' ids.txt > keep_ids.txt
awk 'NR==FNR{k[$1]=1;next} ($2 in k){print $1"\t"$2}' keep_ids.txt d.fam > keep.txt
plink --bfile d --keep keep.txt --geno 0.05 --maf 0.01 --indep-pairwise 200 50 0.2 --out pr > /dev/null 2>&1
plink --bfile d --keep keep.txt --extract pr.prune.in --make-bed --out dp > /dev/null 2>&1
awk 'NR==FNR{p[$1]=$2;next}{print $2"\t"p[$2]}' ids.txt dp.fam > dp.ids
wc -l dp.bim dp.fam
for K in 3 4 5 6 7 8; do admixture --cv -j3 -s 7 dp.bed $K > log$K.out 2>&1; grep CV log$K.out; done
echo ADMX_DONE
