import sys
# stdin graph6; output graphs that are provably non-vertex-transitive via individualization-refinement invariant (stdout),
# others (possibly VT) to stderr
def parse(s):
    n=ord(s[0])-63; adj=[[] for _ in range(n)]; k=0
    for j in range(1,n):
        for i in range(j):
            if (ord(s[1+k//6])-63)>>(5-k%6)&1:
                adj[i].append(j); adj[j].append(i)
            k+=1
    return n,adj
def trace(n,adj,v):
    col=[0]*n; col[v]=1
    tr=[]
    for _ in range(n):
        sig=[(col[x],tuple(sorted(col[y] for y in adj[x]))) for x in range(n)]
        ids={}
        for s in sorted(set(sig)): ids[s]=len(ids)
        new=[ids[s] for s in sig]
        hist=tuple(sorted((s,sig.count(s)) for s in set(sig)))
        tr.append(hist)
        if len(ids)==len(set(col)): 
            col=new; break
        col=new
    return tuple(tr)
cnt=0; nv=0
for line in sys.stdin:
    s=line.strip()
    if not s: continue
    n,adj=parse(s); cnt+=1
    t0=trace(n,adj,0)
    if any(trace(n,adj,v)!=t0 for v in range(1,n)):
        nv+=1; sys.stdout.write(s+'\n')
    else: sys.stderr.write(s+'\n')
