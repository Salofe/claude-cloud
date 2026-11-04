#!/bin/bash
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
todo="$(seq 1 22 | tr '\n' ' ') X"
while [ -n "$todo" ]; do rest=""
  for c in $todo; do
    if [ "$c" = X ]; then bash /home/user/claude-cloud/genoma/scripts/f6_rfmix_X.sh || rest="$rest X"
    else bash /home/user/claude-cloud/genoma/scripts/f6_rfmix_chr.sh $c || rest="$rest $c"; fi
  done; todo=$rest; [ -n "$todo" ] && sleep 60
done; echo RFMIX_ALL_DONE
