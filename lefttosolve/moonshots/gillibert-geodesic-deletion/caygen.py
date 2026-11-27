import sys, random, itertools
# Generate random connected Cayley graphs (inverse-closed generating sets) on several group families; output in 'adj' format.
random.seed(int(sys.argv[1])); budget=int(sys.argv[2]); maxorder=int(sys.argv[3])
def perm_mul(a,b): return tuple(a[i] for i in b)          # (a*b)(i)=a[b[i]]
def perm_inv(a):
    r=[0]*len(a)
    for i,x in enumerate(a): r[x]=i
    return tuple(r)
def metacyclic(n,m,r):
    # Z_n : Z_m with (a,b)*(c,d) = (a + r^b * c mod n, b+d mod m), need r^m = 1 mod n
    pw=[pow(r,b,n) for b in range(m)]
    mul=lambda x,y: ((x[0]+pw[x[1]]*y[0])%n,(x[1]+y[1])%m)
    inv=lambda x: ((-pw[(-x[1])%m]*x[0])%n,(-x[1])%m)
    return mul,inv,(0,0)
def heis(p):
    mul=lambda x,y: ((x[0]+y[0])%p,(x[1]+y[1])%p,(x[2]+y[2]+x[0]*y[1])%p)
    inv=lambda x: ((-x[0])%p,(-x[1])%p,(-x[2]+x[0]*x[1])%p)
    return mul,inv,(0,0,0)
def abel(mods):
    mul=lambda x,y: tuple((a+b)%m for a,b,m in zip(x,y,mods))
    inv=lambda x: tuple((-a)%m for a,m in zip(x,mods))
    return mul,inv,tuple(0 for _ in mods)
def build(mul,inv,e,gens,maxorder):
    gs=[]
    for g in gens:
        if g==e: continue
        for h in (g,inv(g)):
            if h not in gs: gs.append(h)
    idx={e:0}; order=[e]; adj=[]
    i=0
    while i<len(order):
        x=order[i]; row=[]
        for g in gs:
            y=mul(x,g)
            j=idx.get(y)
            if j is None:
                j=len(order); idx[y]=j; order.append(y)
                if j>=maxorder: return None
            row.append(j)
        adj.append(row); i+=1
    return adj
out=0; tries=0
while out<budget and tries<budget*20:
    tries+=1
    fam=random.choice(['sym','sym','meta','meta','meta','heis','abel','abel'])
    if fam=='sym':
        k=random.choice([5,6,6,7,7])
        mul,inv,e=perm_mul,perm_inv,tuple(range(k))
        ng=random.choice([2,2,3])
        gens=[]
        for _ in range(ng):
            t=random.random()
            if t<0.4:
                a,b=random.sample(range(k),2); p=list(range(k)); p[a],p[b]=p[b],p[a]; gens.append(tuple(p))
            else:
                p=list(range(k)); random.shuffle(p); gens.append(tuple(p))
        name='sym%d'%k
    elif fam=='meta':
        n=random.randint(5,3000); m=random.choice([2,2,3,4,5,6,7,8])
        cands=[r for r in range(1,n) if pow(r,m,n)==1]
        r=random.choice(cands)
        mul,inv,e=metacyclic(n,m,r)
        ng=random.choice([2,2,3])
        gens=[(random.randrange(n),random.randrange(m)) for _ in range(ng)]
        name='meta%d_%d_%d'%(n,m,r)
    elif fam=='heis':
        p=random.choice([3,5,7,11,13,17])
        mul,inv,e=heis(p)
        gens=[tuple(random.randrange(p) for _ in range(3)) for _ in range(random.choice([2,3]))]
        name='heis%d'%p
    else:
        mods=[random.randint(2,60) for _ in range(random.choice([1,2,2,3]))]
        mul,inv,e=abel(mods)
        gens=[tuple(random.randrange(m) for m in mods) for _ in range(random.choice([2,3,4]))]
        name='abel'+'x'.join(map(str,mods))
    adj=build(mul,inv,e,gens,maxorder)
    if adj is None or len(adj)<6: continue
    n=len(adj)
    # skip if generators failed to generate distinct neighbours (multi-edges) : dedupe
    adj=[sorted(set(r)-{i}) for i,r in enumerate(adj)]
    if len(set(len(r) for r in adj))!=1 or len(adj[0])<3: continue
    out+=1
    sys.stdout.write('%d %s_g%s\n'%(n,name,'_'.join(''.join(map(str,g)) if n<0 else str(abs(hash(g))%100000) for g in gens)))
    for r in adj: sys.stdout.write(' '.join(map(str,r))+'\n')
sys.stderr.write('generated %d graphs in %d tries\n'%(out,tries))
