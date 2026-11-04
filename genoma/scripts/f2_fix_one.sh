#!/bin/bash
# Deduplica el panel de un cromosoma y reimputa si no hay imputación válida.
c=$1
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/bt/bin:/opt/mm/gen/bin:$PATH
[ -s $S/imp/imp_chr$c.vcf.gz.tbi ] && exit 0
cd $S/ref/1kg && bcftools norm -d exact chr$c.vcf.gz -Oz -o chr$c.dd.vcf.gz && mv chr$c.dd.vcf.gz chr$c.vcf.gz && tabix -f -p vcf chr$c.vcf.gz && echo "dedup chr$c"
rm -f $S/imp/imp_chr$c.vcf.gz $S/imp/imp_chr$c.log; rmdir $S/imp/lock_$c 2>/dev/null
NT=2 bash /home/user/claude-cloud/genoma/scripts/f2_impute_chr.sh $c 2>&1 | grep -v JAVA_TOOL
