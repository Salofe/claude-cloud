#!/bin/bash
# Rebuild snipe_waits.txt: our open proof PRs (last 36 h) for site-statement ids whose statement is not on main yet
# and with no proof on main. Each line: id origPR. The statement watcher re-files these when the statement merges.
SP=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad; M=$SP/open/mon; PRR=$SP/open/prrepo
git -C $PRR fetch -q --filter=blob:none --depth 1 origin +HEAD:refs/mon/head || exit 0
git -C $PRR ls-tree --name-only refs/mon/head proofs/ | sed 's|proofs/||;s|\.lean$||' > $M/main_proofs.txt
git -C $PRR ls-tree --name-only refs/mon/head statements/ | sed 's|statements/||;s|\.lean$||' > $M/main_statements.txt
NOW=$(date -u +%s); T=$(( NOW - 36*3600 )); : > $M/recent_ours.tsv
while [ $T -lt $NOW ]; do
  A=$(date -u -d @$T +%Y-%m-%dT%H:%M:%SZ); B=$(date -u -d @$((T+21600)) +%Y-%m-%dT%H:%M:%SZ)
  for p in 1 2 3 4; do
    r=$(gh api -X GET search/issues -f q="repo:lefttosolve2/open-math-agents is:pr is:open author:Salofe created:$A..$B" -f per_page=100 -f page=$p --jq '.items[] | "\(.number)\t\(.title)"' 2>/dev/null)
    sleep 2.1; [ -z "$r" ] && break; echo "$r" >> $M/recent_ours.tsv
  done
  T=$((T+21600))
done
python3 -I - "$M" <<'PY'
import sys,re
M=sys.argv[1]
proofs=set(open(f'{M}/main_proofs.txt').read().split()); stm=set(open(f'{M}/main_statements.txt').read().split())
own=set(open(f'{M}/../own_statement_ids.txt').read().split())
seen={}
for l in open(f'{M}/recent_ours.tsv'):
    n,t=l.rstrip('\n').split('\t')
    if not re.match(r'^(oeis-a\d+|mo-\d+|mse-\d+|opg-[\w-]+|arxiv-[\w.]+|wp-[\w-]+|lit-[\w-]+)$', t): continue
    if t in own or t in proofs or t in stm: continue
    seen.setdefault(t,n)
open(f'{M}/snipe_waits.txt','w').write(''.join(f'{t} {n}\n' for t,n in sorted(seen.items())))
print(len(seen),'snipe ids waiting for their statement')
PY
