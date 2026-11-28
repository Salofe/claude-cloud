import sys, itertools, random
# generate bicirculants of given n; output adj format for those that are DDR (all vertices same level sizes); name encodes params
def build(n,R,L,T):
    N=2*n; adj=[set() for _ in range(N)]
    for i in range(n):
        for r in R:
            j=(i+r)%n
            if j!=i: adj[i].add(j); adj[j].add(i)
        for l in L:
            j=(i+l)%n
            if j!=i: adj[n+i].add(n+j); adj[n+j].add(n+i)
        for t in T:
            j=(i+t)%n
            adj[i].add(n+j); adj[n+j].add(i)
    return adj
def levels(adj,s):
    N=len(adj); d=[-1]*N; d[s]=0; fr=[s]; res=[1]
    while fr:
        nf=[]
        for v in fr:
            for w in adj[v]:
                if d[w]<0: d[w]=d[v]+1; nf.append(w)
        if nf: res.append(len(nf))
        fr=nf
    return tuple(res), sum(res)
def trace(adj,v):
    n=len(adj); col=[0]*n; col[v]=1; tr=[]
    for _ in range(n):
        sig=[(col[x],tuple(sorted(col[y] for y in adj[x]))) for x in range(n)]
        ids={}
        for s in sorted(set(sig)): ids[s]=len(ids)
        new=[ids[s] for s in sig]
        tr.append(tuple(sorted((s,sig.count(s)) for s in set(sig))))
        if len(ids)==len(set(col)): col=new; break
        col=new
    return tuple(tr)
random.seed(int(sys.argv[1])); nmin=int(sys.argv[2]); nmax=int(sys.argv[3]); tries=int(sys.argv[4])
seen=set(); out=0
for _ in range(tries):
    n=random.randint(nmin,nmax)
    a=random.randint(0,2); b=random.randint(1,3)
    R=random.sample(range(1,n//2+1),min(a,n//2)); 
    L=random.sample(range(1,n//2+1),min(a,n//2))
    T=[0]+random.sample(range(1,n),b-1)
    adj=build(n,R,L,T)
    degs=set(len(x) for x in adj)
    if len(degs)!=1: continue
    l0,c0=levels(adj,0)
    if c0!=2*n: continue
    l1,c1=levels(adj,n)
    if l0!=l1: continue
    key=(n,tuple(sorted(R)),tuple(sorted(L)),tuple(sorted(T)))
    if key in seen: continue
    seen.add(key)
    vt = trace(adj,0)==trace(adj,n)
    if vt: continue   # keep only provably non-VT DDR graphs
    out+=1
    sys.stdout.write('%d bic_n%d_R%s_L%s_T%s\n'%(2*n,n,'.'.join(map(str,sorted(R))),'.'.join(map(str,sorted(L))),'.'.join(map(str,sorted(T)))))
    for v in range(2*n): sys.stdout.write(' '.join(map(str,sorted(adj[v])))+'\n')
sys.stderr.write('generated %d DDR non-VT bicirculants\n'%out)
