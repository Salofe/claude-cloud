import sys
def parse(s):
    n=ord(s[0])-63; adj=[set() for _ in range(n)]; k=0
    for j in range(1,n):
        for i in range(j):
            if (ord(s[1+k//6])-63)>>(5-k%6)&1:
                adj[i].add(j); adj[j].add(i)
            k+=1
    return n,adj
def bfs(n,adj,s,forb=()):
    d=[-1]*n; d[s]=0; fr=[s]
    while fr:
        nf=[]
        for v in fr:
            for w in adj[v]:
                if d[w]<0 and w not in forb: d[w]=d[v]+1; nf.append(w)
        fr=nf
    return d
def comps(n,adj,rem):
    rem=set(rem); res=[]
    while rem:
        s=next(iter(rem)); c={s}; st=[s]
        while st:
            v=st.pop()
            for w in adj[v]:
                if w in rem and w not in c: c.add(w); st.append(w)
        res.append(sorted(c)); rem-=c
    return res
fn=sys.argv[1]; idx=int(sys.argv[2]); path=list(map(int,sys.argv[3:]))
s=open(fn).read().split('\n')[idx-1].strip()
n,adj=parse(s)
print('n',n,'degrees',sorted(set(len(a) for a in adj)))
for v in range(n): print(v,sorted(adj[v]))
# invariants: distance degree sequence + triangles
for v in range(n):
    d=bfs(n,adj,v); tri=sum(1 for a in adj[v] for b in adj[v] if a<b and b in adj[a])
    print('v',v,'levels',[d.count(i) for i in range(max(d)+1)],'tri',tri)
print('path',path, 'dist',bfs(n,adj,path[0])[path[-1]])
cs=comps(n,adj,set(range(n))-set(path))
for c in cs:
    print('component',c,'attached to',sorted(set(p for p in path for x in c if p in adj[x])))
