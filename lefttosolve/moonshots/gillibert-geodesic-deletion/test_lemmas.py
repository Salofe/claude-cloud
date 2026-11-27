import random, sys
random.seed(12345)
def bfs(adj,s,forb=None):
    n=len(adj); d=[-1]*n; d[s]=0; fr=[s]
    while fr:
        nf=[]
        for v in fr:
            for w in adj[v]:
                if d[w]<0 and (forb is None or w not in forb): d[w]=d[v]+1; nf.append(w)
        fr=nf
    return d
def rand_graph(n,p):
    while True:
        adj=[set() for _ in range(n)]
        for i in range(n):
            for j in range(i):
                if random.random()<p: adj[i].add(j); adj[j].add(i)
        if min(bfs(adj,0))>=0: return adj
def comp_of(adj,S,z):
    n=len(adj); seen={z}; st=[z]
    while st:
        v=st.pop()
        for w in adj[v]:
            if w not in S and w not in seen: seen.add(w); st.append(w)
    return seen
# L1: Lemma H on random graphs with random S
cnt=0; viol=0
for it in range(3000):
    n=random.randint(6,22); adj=rand_graph(n,random.choice([0.15,0.2,0.3]))
    D=[bfs(adj,v) for v in range(n)]
    S=set(random.sample(range(n),random.randint(1,max(1,n//3))))
    for z in range(n):
        if z in S: continue
        cz=comp_of(adj,S,z)
        for u in range(n):
            if u==z: continue
            if all(D[u][s]<=D[z][s] for s in S):
                for x in range(n):
                    if D[z][x]<D[u][x]:
                        cnt+=1
                        if x in S or x not in cz: viol+=1
print('L1 (half-space lemma): instances',cnt,'violations',viol)
# L2: domination interval for geodesics; plus Lemma H corollary with u=v_s
cnt=0; viol=0; cnt2=0; viol2=0
for it in range(3000):
    n=random.randint(6,24); adj=rand_graph(n,random.choice([0.12,0.15,0.2]))
    D=[bfs(adj,v) for v in range(n)]
    a=random.randrange(n); b=max(range(n),key=lambda x:D[a][x]+random.random())
    # random geodesic a->b
    P=[a]
    while P[-1]!=b:
        v=P[-1]; P.append(random.choice([w for w in adj[v] if D[w][b]==D[v][b]-1]))
    l=len(P)-1; S=set(P)
    for z in range(n):
        if z in S: continue
        f=[D[z][P[t]] for t in range(l+1)]
        lo=max(t-f[t] for t in range(l+1)); hi=min(t+f[t] for t in range(l+1))
        lo=max(lo,0); hi=min(hi,l)
        cnt+=1
        if lo>hi: viol+=1; continue
        cz=comp_of(adj,S,z)
        for s in range(lo,hi+1):
            assert all(f[t]>=abs(t-s) for t in range(l+1))
            for x in range(n):
                if D[z][x]<D[P[s]][x]:
                    cnt2+=1
                    if x in S or x not in cz: viol2+=1
print('L2 (dominating path vertex exists): instances',cnt,'violations',viol,'; half-space inside component: instances',cnt2,'violations',viol2)
# Lemma Z' on circulants: automorphisms = translations and reflections
cnt=0; viol=0
for it in range(4000):
    n=random.randint(7,40)
    conn=set()
    for _ in range(random.randint(1,3)):
        c=random.randint(1,n//2); conn.add(c); conn.add(n-c)
    adj=[set((i+c)%n for c in conn if c%n!=0) for i in range(n)]
    for v in range(n): adj[v].discard(v)
    if min(bfs(adj,0))<0: continue
    # random set A: grow connected set
    size=random.randint(1,(n-1)//2)
    A={random.randrange(n)}
    while len(A)<size:
        cand=[w for v in A for w in adj[v] if w not in A]
        if not cand: break
        A.add(random.choice(cand))
    if 2*len(A)>=n: continue
    comp=set(range(n))-A
    c0=next(iter(comp))
    if len(comp_of(adj,A,c0))!=len(comp): continue
    NA=set(w for v in A for w in adj[v])-A
    for g in range(n):
        for sgn in (1,-1):
            cnt+=1
            if all(((sgn*x+g)%n) in A for x in NA): viol+=1
print("Lemma Z' (boundary cannot be mapped into the pocket) on circulants: instances",cnt,'violations',viol)
