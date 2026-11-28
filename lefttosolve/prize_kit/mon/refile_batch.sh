#!/bin/bash
# refile_batch.sh <list file: "id origPR" per line> <out file>
# For each id: skip if a proof is on main or another account has an open PR titled exactly id; take our proof from the
# fork branch oma/<id>; push it as a fresh commit on oma/<id>-p2 (or -p3 if -p2 exists). Writes "id branch origPR".
SP=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad
F=/home/user/open-math-agents; PRR=$SP/open/prrepo; LIST=$1; OUT=$2; : > $OUT
git -C $PRR fetch -q --filter=blob:none --depth 1 origin +HEAD:refs/mon/head
git -C $F fetch -q origin oma-base
while read -r id orig; do
  [ -z "$id" ] && continue
  if git -C $PRR cat-file -e refs/mon/head:proofs/$id.lean 2>/dev/null; then echo "SKIP $id: proof on main"; continue; fi
  if ! git -C $PRR cat-file -e refs/mon/head:statements/$id.lean 2>/dev/null; then echo "SKIP $id: statement not on main"; continue; fi
  riv=$(gh api -X GET search/issues -f q="repo:lefttosolve2/open-math-agents is:pr is:open in:title $id" --jq "[.items[] | select(.title==\"$id\" and .user.login!=\"Salofe\") | \"#\(.number) \(.user.login)\"] | join(\" \")" 2>/dev/null); sleep 2.1
  if [ -n "$riv" ]; then echo "SKIP $id: rival open PR $riv"; continue; fi
  git -C $F fetch -q origin "oma/$id" 2>/dev/null || { echo "SKIP $id: no fork branch oma/$id"; continue; }
  src=$(git -C $F show FETCH_HEAD:proofs/$id.lean 2>/dev/null) || { echo "SKIP $id: no proofs/$id.lean on oma/$id"; continue; }
  br=oma/$id-p2; git -C $F ls-remote --exit-code origin refs/heads/$br >/dev/null 2>&1 && br=oma/$id-p3
  W=$SP/submit/$id-re; rm -rf $W; git -C $F worktree prune
  git -C $F worktree add -q -f -B $br $W origin/oma-base && git -C $F show FETCH_HEAD:proofs/$id.lean > $W/proofs/$id.lean && git -C $W add proofs/$id.lean && \
  git -C $W commit -q -m "$id" -m "Re-filed now that the statement is on main." -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ" || { echo "FAIL $id: commit"; git -C $F worktree remove --force $W; continue; }
  # the file must be byte-identical to the checked one
  cmp -s <(git -C $F show FETCH_HEAD:proofs/$id.lean) $W/proofs/$id.lean || { echo "FAIL $id: bytes differ"; git -C $F worktree remove --force $W; continue; }
  ok=0; for t in 1 2 3 4; do git -C $W push -q -u origin $br 2>/dev/null && { ok=1; break; }; sleep $((t*3)); done
  git -C $F worktree remove --force $W
  [ $ok = 1 ] && { echo "$id $br $orig" >> $OUT; echo "PUSHED $id $br"; } || echo "FAIL $id: push"
done < $LIST
