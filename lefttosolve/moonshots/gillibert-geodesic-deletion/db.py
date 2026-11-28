import sys
# stdin graph6: classify distance-balanced (|W_uv|=|W_vu| all edges) -> stdout, else stderr
def parse(s):
    n=ord(s[0])-63; adj=[[] for _ in range(n)]; k=0
    for j in range(1,n):
        for i in range(j):
            if (ord(s[1+k//6])-63)>>(5-k%6)&1:
                adj[i].append(j); adj[j].append(i)
            k+=1
    return n,adj
def bfs(n,adj,s):
    d=[-1]*n; d[s]=0; fr=[s]
    while fr:
        nf=[]
        for v in fr:
            for w in adj[v]:
                if d[w]<0: d[w]=d[v]+1; nf.append(w)
        fr=nf
    return d
for line in sys.stdin:
    s=line.strip()
    if not s: continue
    n,adj=parse(s)
    D=[bfs(n,adj,v) for v in range(n)]
    tr=[sum(D[v]) for v in range(n)]
    ok=len(set(tr))==1   # connected: DB iff transmission regular
    (sys.stdout if ok else sys.stderr).write(s+'\n')
