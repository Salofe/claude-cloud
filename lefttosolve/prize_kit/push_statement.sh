#!/bin/bash
# Usage: push_statement.sh <id> <statement file> ; pushes oma/<id>-statement with statements/<id>.lean from origin/oma-base
set -u
id=$1; SRC=$2; SP=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad; F=/home/user/open-math-agents
for i in 1 2 3 4 5; do git -C $F fetch -q origin oma-base 2>/dev/null && break; sleep 5; done
W=$SP/submit/$id-statement; rm -rf "$W"; git -C $F worktree prune
git -C $F worktree add -q -f -B oma/$id-statement "$W" origin/oma-base || { echo "WORKTREE FAILED"; exit 4; }
mkdir -p "$W/statements"; cp "$SRC" "$W/statements/$id.lean" && git -C "$W" add statements/$id.lean
git -C "$W" commit -q -m "Statement: $id" -m "States the OEIS conjecture for review. A checker-accepted Lean proof is filed right after this PR." -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ"
ok=0; for i in 1 2 3 4; do git -C "$W" -c push.negotiate=true push -q -u origin oma/$id-statement && ok=1 && break; sleep $((2**i)); done
git -C $F worktree remove --force "$W"
[ $ok = 1 ] && echo "PUSHED oma/$id-statement" || { echo "PUSH FAILED"; exit 5; }
