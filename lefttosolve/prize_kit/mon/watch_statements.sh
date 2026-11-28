#!/bin/bash
# Statement-merge watcher (Monitor). Every 60 s: for each watched id whose statement just appeared on upstream main,
# push the re-file branch at once and print one line: READY <id> <branch> <first proof PR> | SKIP/FAIL <reason>.
# Watched: own statements (own_statement_ids.txt), statements we adapted to (rival_statement_waits.txt: id stmtPR ourPR),
# and sniped statements (mon/snipe_waits.txt: id ourPR).
SP=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad
M=$SP/open/mon; PRR=$SP/open/prrepo; SEEN=$M/seen.txt; touch $SEEN
while true; do
  if git -C $PRR fetch -q --filter=blob:none --depth 1 origin +HEAD:refs/mon/head 2>/dev/null; then
    files=$(git -C $PRR ls-tree --name-only refs/mon/head statements/ proofs/ 2>/dev/null)
    for id in $(cat $SP/open/own_statement_ids.txt) $(awk '{print $1}' $SP/open/rival_statement_waits.txt $M/snipe_waits.txt 2>/dev/null | sort -u); do
      grep -qx "$id" $SEEN && continue
      grep -qx "statements/$id.lean" <<<"$files" || continue
      echo "$id" >> $SEEN
      if grep -qx "proofs/$id.lean" <<<"$files"; then echo "SKIP $id: proof already on main"; continue; fi
      if grep -qx "$id" $SP/open/own_statement_ids.txt; then
        out=$($M/refile.sh $id 2>&1); orig=$(grep -oE "^#[0-9]+ Salofe open $id " <<<"$out" | head -1 | grep -oE '[0-9]+' | head -1)
        br=$(grep -oE "PUSHED oma/$id-p[0-9]" <<<"$out" | cut -d' ' -f2)
        [ -n "$br" ] && echo "READY own $id $br ${orig:-?}" || echo "FAIL own $id: $(tail -1 <<<"$out")"
      elif grep -q "^$id " $SP/open/rival_statement_waits.txt; then
        ours=$(grep "^$id " $SP/open/rival_statement_waits.txt | awk '{print $3}')
        out=$($M/refile.sh $id $SP/open/adapt/$id/proof_for_rival.lean 2>&1); br=$(grep -oE "PUSHED oma/$id-p[0-9]" <<<"$out" | cut -d' ' -f2)
        [ -n "$br" ] && echo "READY adapted $id $br $ours" || echo "FAIL adapted $id: $(tail -1 <<<"$out")"
      else
        grep "^$id " $M/snipe_waits.txt | head -1 > $M/ev_$id.txt
        out=$($M/refile_batch.sh $M/ev_$id.txt $M/ev_$id.out 2>&1)
        if [ -s $M/ev_$id.out ]; then read -r i br orig < $M/ev_$id.out; echo "READY snipe $id $br $orig"; else echo "SKIP snipe $id: $(tail -1 <<<"$out")"; fi
      fi
    done
  else
    echo "fetch failed $(date -u +%H:%M)" >&2
  fi
  sleep 60
done
