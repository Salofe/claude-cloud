#!/bin/bash
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
todo="1 2 3 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22"
while [ -n "$todo" ]; do
  rest=""
  for c in $todo; do
    [ -s $S/pgs/work/sant_chr$c.tsv ] && continue
    if [ -s $S/imp/imp_chr$c.vcf.gz.tbi ]; then nice -n 5 python3 /home/user/claude-cloud/genoma/scripts/f5_pgs_chr.py $c; else rest="$rest $c"; fi
  done
  todo=$rest; [ -n "$todo" ] && sleep 60
done
echo PGS_DONE
