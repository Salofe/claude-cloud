#!/bin/bash
# Usage: push_branch.sh <id> ; checks upstream (proof + ancestors) then pushes oma/<id> from a private worktree based on origin/oma-base
set -u
id=$1; SP=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad; R=/home/user/guillaumebaud-coder/open-math-agents; F=/home/user/open-math-agents
REF=""
for i in 1 2 3 4 5; do timeout 200 git -C $R fetch -q --depth 1 origin HEAD 2>/dev/null && REF=$(git -C $R rev-parse FETCH_HEAD 2>/dev/null) && [ -n "$REF" ] && break; sleep 8; done
[ -z "$REF" ] && { echo "UPSTREAM FETCH FAILED"; exit 2; }
x=$id
if git -C $R cat-file -e $REF:proofs/$x.lean 2>/dev/null; then echo "SOLVED UPSTREAM: $x"; exit 3; fi
while echo "$x" | grep -qE '\.R[0-9]+\.H[0-9]+$'; do x=$(echo $x | sed -E 's/\.R[0-9]+\.H[0-9]+$//'); if git -C $R cat-file -e $REF:proofs/$x.lean 2>/dev/null; then echo "ANCESTOR SOLVED UPSTREAM: $x"; exit 3; fi; done
echo "upstream $REF: open"
for i in 1 2 3 4 5; do git -C $F fetch -q origin oma-base 2>/dev/null && break; sleep 5; done
W=$SP/submit/$id; rm -rf "$W"; git -C $F worktree prune
git -C $F worktree add -q -f -B oma/$id "$W" origin/oma-base || { echo "WORKTREE FAILED"; exit 4; }
cp $SP/oma-check/proofs/$id.lean "$W/proofs/" && git -C "$W" add proofs/$id.lean
git -C "$W" commit -q -m "$id" -m "Checked locally with tools/check.sh." -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ"
ok=0; for i in 1 2 3 4; do git -C "$W" -c push.negotiate=true push -q -u origin oma/$id && ok=1 && break; sleep $((2**i)); done
git -C $F worktree remove --force "$W"
[ $ok = 1 ] && echo "PUSHED oma/$id" || { echo "PUSH FAILED"; exit 5; }
