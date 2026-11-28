import sys
# Test antipode statements on VT graphs (graph6 input), base vertex v0=0 by transitivity.
# For each geodesic (v0,v1,v2) [v2 at distance 2 via v1] and y in N(v0)-{v1}:
#  Q1: exists x* in Ant(v2) with Down_{x*}(y) not subset {v0,v1}
#  Q1p: exists x* in Ant(v2) such that for all y: Down_{x*}(y) not subset {v0,v1}
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
tot=0; cnt=[0,0,0,0]; ex=[]
for fn in sys.argv[1:]:
  for idx,line in enumerate(open(fn)):
    s=line.strip()
    if not s: continue
    n,adj=parse(s)
    D0=bfs(n,adj,0)
    if min(D0)<0 or n<3: continue
    dist=[bfs(n,adj,v) for v in range(n)]
    Dm=max(D0)
    if Dm<3: continue
    tot+=1
    q1=True; q1p=True
    for v1 in adj[0]:
        for v2 in adj[v1]:
            if dist[0][v2]!=2: continue
            ants=[x for x in range(n) if dist[v2][x]==Dm]
            ys=[y for y in adj[0] if y!=v1]
            okall=False
            for x in ants:
                good=True
                for y in ys:
                    down=[z for z in adj[y] if dist[z][x]==dist[y][x]-1]
                    if y!=x and all(z in (0,v1) for z in down): good=False;break
                if good: okall=True;break
            if not okall: q1p=False
            for y in ys:
                ok=False
                for x in ants:
                    down=[z for z in adj[y] if dist[z][x]==dist[y][x]-1]
                    if y==x or not all(z in (0,v1) for z in down): ok=True;break
                if not ok: q1=False
    if q1: cnt[0]+=1
    if q1p: cnt[1]+=1
    if not q1 and len(ex)<12: ex.append((fn.split('/')[-1],idx+1,n,len(adj[0]),Dm))
print('graphs with diam>=3:',tot,'Q1 holds:',cnt[0],'Q1p holds:',cnt[1])
print('Q1 failures (examples):',ex)
