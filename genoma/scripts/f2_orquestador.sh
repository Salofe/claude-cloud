#!/bin/bash
# Imputa cada cromosoma en cuanto su panel de 1000G está listo (índice .tbi presente).
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
todo="${ORDER:-1 2 3 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 X}"
while [ -n "$todo" ]; do
  rest=""
  for c in $todo; do
    if [ -s $S/imp/imp_chr$c.vcf.gz.tbi ]; then continue; fi
    if [ -s $S/ref/1kg/chr$c.vcf.gz.tbi ]; then
      NT=2 bash /home/user/claude-cloud/genoma/scripts/f2_impute_chr.sh $c 2>&1 | grep -v JAVA_TOOL
    else rest="$rest $c"; fi
  done
  todo=$rest; [ -n "$todo" ] && sleep 60
done
echo ORQ_DONE
