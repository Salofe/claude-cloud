import sys, itertools
out=sys.stdout
def emit(name,adj):
    n=len(adj)
    out.write('%d %s\n'%(n,name))
    for r in adj: out.write(' '.join(map(str,sorted(r)))+'\n')
def from_vertices(verts,adjf,name):
    idx={v:i for i,v in enumerate(verts)}
    adj=[[idx[w] for w in adjf(v)] for v in verts]
    emit(name,adj)
# Kneser / odd graphs
for n,k in [(5,2),(7,3),(9,4),(11,5),(8,3),(10,4),(11,4),(13,6),(13,5),(12,5)]:
    verts=[frozenset(c) for c in itertools.combinations(range(n),k)]
    if len(verts)>6000: continue
    rest=lambda v: [frozenset(c) for c in itertools.combinations(sorted(set(range(n))-v),k)]
    from_vertices(verts,rest,'Kneser_%d_%d'%(n,k))
# Johnson graphs
for n,k in [(6,3),(7,3),(8,3),(8,4),(9,4),(10,4),(10,5),(12,3),(12,6)]:
    verts=[frozenset(c) for c in itertools.combinations(range(n),k)]
    if len(verts)>6000: continue
    def nb(v,n=n): return [frozenset(v-{a}|{b}) for a in v for b in range(n) if b not in v]
    from_vertices(verts,nb,'Johnson_%d_%d'%(n,k))
# doubled odd graphs (bipartite double of odd graph): k-1 and k subsets of [2k-1], inclusion
for k in [3,4,5,6]:
    n=2*k-1
    A=[frozenset(c) for c in itertools.combinations(range(n),k-1)]
    B=[frozenset(c) for c in itertools.combinations(range(n),k)]
    verts=A+B
    def nb(v,n=n,k=k):
        if len(v)==k-1: return [v|{b} for b in range(n) if b not in v]
        return [v-{a} for a in v]
    from_vertices(verts,nb,'DoubledOdd_%d'%k)
# Hamming graphs H(d,q), folded cubes, halved cubes
for d,q in [(3,3),(4,3),(5,3),(3,4),(4,4),(3,5),(2,7),(6,2),(8,2),(10,2),(6,3)]:
    verts=list(itertools.product(range(q),repeat=d))
    def nb(v,d=d,q=q): return [v[:i]+(x,)+v[i+1:] for i in range(d) for x in range(q) if x!=v[i]]
    from_vertices(verts,nb,'Hamming_%d_%d'%(d,q))
for d in [5,6,7,8,9,10,11]:
    verts=[v for v in itertools.product(range(2),repeat=d) if v[0]==0]   # folded cube: identify v ~ complement
    def canon(v): 
        return v if v[0]==0 else tuple(1-x for x in v)
    def nb(v,d=d): return list({canon(v[:i]+(1-v[i],)+v[i+1:]) for i in range(d)})
    from_vertices(verts,nb,'FoldedCube_%d'%d)
for d in [5,6,7,8,9,10]:
    verts=[v for v in itertools.product(range(2),repeat=d) if sum(v)%2==0]
    def nb(v,d=d):
        r=[]
        for i in range(d):
            for j in range(i+1,d):
                w=list(v); w[i]^=1; w[j]^=1; r.append(tuple(w))
        return r
    from_vertices(verts,nb,'HalvedCube_%d'%d)
# products of cycles: Cartesian C_a x C_b, tensor, strong; C_a x C_b x C_c
def cyc(n): return lambda i: [(i+1)%n,(i-1)%n]
for a,b in [(5,7),(6,8),(7,9),(9,11),(12,15),(20,31),(8,40),(3,50),(4,60),(5,80)]:
    verts=[(i,j) for i in range(a) for j in range(b)]
    from_vertices(verts,lambda v,a=a,b=b: [((v[0]+1)%a,v[1]),((v[0]-1)%a,v[1]),(v[0],(v[1]+1)%b),(v[0],(v[1]-1)%b)],'CartCyc_%d_%d'%(a,b))
    if a%2==1 or b%2==1:
        from_vertices(verts,lambda v,a=a,b=b: [((v[0]+s)%a,(v[1]+t)%b) for s in (1,-1) for t in (1,-1)],'TensorCyc_%d_%d'%(a,b))
    from_vertices(verts,lambda v,a=a,b=b: [((v[0]+s)%a,(v[1]+t)%b) for s in (1,0,-1) for t in (1,0,-1) if (s,t)!=(0,0)],'StrongCyc_%d_%d'%(a,b))
    # triangular / hexagonal-type tori
    from_vertices(verts,lambda v,a=a,b=b: [((v[0]+1)%a,v[1]),((v[0]-1)%a,v[1]),(v[0],(v[1]+1)%b),(v[0],(v[1]-1)%b),((v[0]+1)%a,(v[1]+1)%b),((v[0]-1)%a,(v[1]-1)%b)],'TriTorus_%d_%d'%(a,b))
for a,b,c in [(4,5,6),(5,5,5),(6,7,8),(3,4,50),(10,10,10)]:
    verts=[(i,j,k) for i in range(a) for j in range(b) for k in range(c)]
    from_vertices(verts,lambda v,a=a,b=b,c=c: [((v[0]+1)%a,v[1],v[2]),((v[0]-1)%a,v[1],v[2]),(v[0],(v[1]+1)%b,v[2]),(v[0],(v[1]-1)%b,v[2]),(v[0],v[1],(v[2]+1)%c),(v[0],v[1],(v[2]-1)%c)],'Cart3Cyc_%d_%d_%d'%(a,b,c))
# lexicographic products C_n[K_m-bar] and C_n[K_m], prisms over them
for n,m in [(7,2),(8,3),(12,2),(15,3),(20,4),(30,2)]:
    verts=[(i,x) for i in range(n) for x in range(m)]
    from_vertices(verts,lambda v,n=n,m=m: [((v[0]+s)%n,x) for s in (1,-1) for x in range(m)],'LexCycEmpty_%d_%d'%(n,m))
    from_vertices(verts,lambda v,n=n,m=m: [((v[0]+s)%n,x) for s in (1,-1) for x in range(m)]+[(v[0],x) for x in range(m) if x!=v[1]],'LexCycComplete_%d_%d'%(n,m))
