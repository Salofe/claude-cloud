#!/bin/bash
# refile.sh <id> [proof_src]: verify statement on main matches ours, push oma/<id>-p2 with our proof, print PR numbers.
SP=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad
F=/home/user/open-math-agents; PRR=$SP/open/prrepo; id=$1; src=${2:-$SP/open/formalize/proofs/$id.lean}
git -C $PRR fetch -q --filter=blob:none --depth 1 origin +HEAD:refs/mon/head
if git -C $PRR cat-file -e refs/mon/head:proofs/$id.lean 2>/dev/null; then echo "SKIP $id: proof already on main"; exit 1; fi
if [ -z "$2" ]; then
  a=$(git -C $PRR show refs/mon/head:statements/$id.lean | sha1sum | cut -c1-12); b=$(sha1sum < $SP/open/formalize/statements/$id.lean | cut -c1-12)
  [ "$a" = "$b" ] || { echo "WARN $id: statement on main differs from ours ($a vs $b)"; exit 2; }
fi
gh api -X GET search/issues -f q="repo:lefttosolve2/open-math-agents is:pr in:title $id" --jq '.items[] | "#\(.number) \(.user.login) \(.state) \(.title) c=\(.comments)"'
git -C $F fetch -q origin oma-base
W=$SP/submit/$id-p2; rm -rf $W; git -C $F worktree prune
git -C $F worktree add -q -f -B oma/$id-p2 $W origin/oma-base && cp $src $W/proofs/$id.lean && git -C $W add proofs/$id.lean && \
git -C $W commit -q -m "$id" -m "Re-filed now that the statement is on main." -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ" && \
for t in 1 2 3 4; do git -C $W push -q -f -u origin oma/$id-p2 2>/dev/null && break; sleep $((t*3)); done
git -C $F worktree remove --force $W; echo "PUSHED oma/$id-p2 $(git -C $F rev-parse --short origin/oma-base)"
