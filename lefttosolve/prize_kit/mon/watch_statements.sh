#!/bin/bash
# Emit one line per newly merged statement among our own ids and the rival waits.
SP=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad
PRR=$SP/open/prrepo; SEEN=$SP/open/mon/seen.txt; touch $SEEN
while true; do
  if git -C $PRR fetch -q --filter=blob:none --depth 1 origin +HEAD:refs/mon/head 2>/dev/null; then
    files=$(git -C $PRR ls-tree --name-only refs/mon/head statements/ proofs/ 2>/dev/null)
    for id in $(cat $SP/open/own_statement_ids.txt) $(awk '{print $1}' $SP/open/rival_statement_waits.txt); do
      grep -qx "$id" $SEEN && continue
      if grep -qx "statements/$id.lean" <<<"$files"; then
        p=no; grep -qx "proofs/$id.lean" <<<"$files" && p=yes
        echo "STATEMENT MERGED: $id (proof on main: $p)"; echo "$id" >> $SEEN
      fi
    done
  else
    echo "fetch failed $(date -u +%H:%M)" >&2
  fi
  sleep 150
done
