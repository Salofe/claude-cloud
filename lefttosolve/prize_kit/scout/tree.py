import json,re,os,sys
from functools import lru_cache
sys.setrecursionlimit(10000)
TR=int(sys.argv[1]) if len(sys.argv)>1 else 300
pool={x['id']:x for x in json.load(open('open/prize_pool.json'))}
d=json.load(open('prize_scout/pool_reds.json'))
def strip_comments(s):
    res, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth == 0 and s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j; continue
        if s.startswith("/-", i): depth += 1; i += 2; continue
        if depth and s.startswith("-/", i): depth -= 1; i += 2; continue
        if depth == 0: res.append(s[i])
        i += 1
    return "".join(res)
def hyps(code):
    found={}
    for m in re.finditer(r"^def\s+H([1-9])\s*:\s*Prop\s*:=\s*(.*?)(?=^\s*(?:def|theorem|lemma|end|namespace|open|section|variable|@\[)\b|\Z)", code, re.S|re.M):
        found[int(m.group(1))]=m.group(2).strip()
    return found
allreds=set(); allproofs=set()
for i,v in d.items():
    allreds|=set(v['reds']); allproofs|=set(v['proofs'])
H={r:hyps(strip_comments(open(f'prize_scout/reds/{r}.lean').read())) for r in allreds}
def reds_of(t): return sorted(r for r in allreds if re.fullmatch(re.escape(t)+r'\.R\d+', r))
@lru_cache(None)
def closed(t):
    if t in allproofs: return True
    for r in reds_of(t):
        if H[r] and all(closed(f'{r}.H{k}') for k in H[r]): return True
    return False
out=[]; leaves=[]
def show(t, depth, pts):
    for r in reds_of(t):
        ks=sorted(H[r]); share=pts/len(ks) if ks else 0
        out.append('  '*depth+f'[{r.split(".")[-1]}] ({len(ks)} steps, {share:.1f} pts each)')
        for k in ks:
            s=f'{r}.H{k}'
            st='PROVED' if s in allproofs else ('closed-by-sub' if closed(s) else 'OPEN')
            txt=' '.join(H[r][k].split())
            out.append('  '*(depth+1)+f'H{k} {st}: {txt[:TR]}')
            if s not in allproofs:
                if st=='OPEN' and not reds_of(s): leaves.append((s,share,txt))
                show(s, depth+2, share)
for i in pool:
    if not d[i]['reds']: continue
    out.append(f"\n##### {i}  ({pool[i]['kind']}, {pool[i]['prize']}, {pool[i]['points']} pts)  closed={closed(i)}")
    show(i,1,pool[i]['points'])
open('prize_scout/red_tree.txt','w').write('\n'.join(out))
json.dump(leaves, open('prize_scout/open_leaves.json','w'), indent=1)
print(len(out), 'lines;', len(leaves), 'open leaf steps (unreduced)')
