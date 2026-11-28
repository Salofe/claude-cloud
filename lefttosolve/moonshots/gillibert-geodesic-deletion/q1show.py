import sys
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
fn=sys.argv[1]; idx=int(sys.argv[2])
s=open(fn).read().split('\n')[idx-1].strip()
n,adj=parse(s)
for v in range(n): print(v,adj[v])
dist=[bfs(n,adj,v) for v in range(n)]
Dm=max(dist[0]); shown=0
for v1 in adj[0]:
    for v2 in adj[v1]:
        if dist[0][v2]!=2: continue
        ants=[x for x in range(n) if dist[v2][x]==Dm]
        for y in adj[0]:
            if y==v1: continue
            bad=True
            for x in ants:
                down=[z for z in adj[y] if dist[z][x]==dist[y][x]-1]
                if not all(z in (0,v1) for z in down): bad=False
            if bad and shown<4:
                shown+=1
                print('v0=0 v1=%d v2=%d y=%d ants(v2)=%s'%(v1,v2,y,ants),' d(y,v2)=',dist[y][v2],' y~v1:',v1 in adj[y])
                for x in ants: print('   x*=%d d(v0,x)=%d d(v1,x)=%d d(y,x)=%d down(y)=%s'%(x,dist[0][x],dist[v1][x],dist[y][x],[z for z in adj[y] if dist[z][x]==dist[y][x]-1]))
