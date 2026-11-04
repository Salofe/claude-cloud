#!/bin/bash
# Lanza consultas de Vindija por cromosoma (3 en paralelo) en cuanto existan las frecuencias.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
cd $S/nea
todo="$(seq 2 22 | tr '\n' ' ')"
while [ -n "$todo" ]; do
  rest=""
  for c in $todo; do
    [ -s vin_chr$c.done ] && continue
    if [ -s freq_chr$c.done ] && [ $(pgrep -fc "f8_vindija_chr.py") -lt 3 ]; then
      nohup python3 /home/user/claude-cloud/genoma/scripts/f8_vindija_chr.py $c >> $S/work/vin.log 2>&1 &
      sleep 2
    else rest="$rest $c"; fi
  done
  todo=$rest; sleep 30
done
wait; echo VIN_DONE >> $S/work/vin.log
