#!/bin/bash
todo="$(seq 1 22 | tr '\n' ' ')"
while [ -n "$todo" ]; do rest=""; for c in $todo; do nice -n 5 bash /home/user/claude-cloud/genoma/scripts/f8_candidates_chr.sh $c || rest="$rest $c"; done; todo=$rest; [ -n "$todo" ] && sleep 60; done; echo F8_DONE
