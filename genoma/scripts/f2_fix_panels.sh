#!/bin/bash
# Arregla paneles: quita duplicados exactos (chr8, chr14, …) y deja X solo no-PAR; reimputa.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
cd $S/ref/1kg
for c in 8 14; do
  bcftools norm -d exact chr$c.vcf.gz -Oz -o chr$c.dd.vcf.gz && mv chr$c.dd.vcf.gz chr$c.vcf.gz && tabix -f -p vcf chr$c.vcf.gz && echo "dedup chr$c"
done
bcftools view -r X:2699521-154931043 chrX.vcf.gz -Oz -o chrX.np.vcf.gz && bcftools norm -d exact chrX.np.vcf.gz -Oz -o chrX.vcf.gz.new && mv chrX.vcf.gz.new chrX.vcf.gz && rm chrX.np.vcf.gz && tabix -f -p vcf chrX.vcf.gz && echo "X no-PAR"
for c in 8 14 X; do rm -f $S/imp/imp_chr$c.vcf.gz $S/imp/imp_chr$c.log; NT=2 bash /home/user/claude-cloud/genoma/scripts/f2_impute_chr.sh $c 2>&1 | grep -v JAVA_TOOL; done
echo FIX_DONE
