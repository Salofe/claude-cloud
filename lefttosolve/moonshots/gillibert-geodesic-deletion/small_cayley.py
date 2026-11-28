import itertools, sys
def g6(n, edges):
    bits=[]
    for j in range(1,n):
        for i in range(j):
            bits.append(1 if (i,j) in edges else 0)
    while len(bits)%6: bits.append(0)
    s=chr(n+63)
    for k in range(0,len(bits),6):
        v=0
        for b in bits[k:k+6]: v=v*2+b
        s+=chr(v+63)
    return s
def cyclic(mods):
    els=list(itertools.product(*[range(m) for m in mods]))
    mul=lambda a,b: tuple((x+y)%m for x,y,m in zip(a,b,mods))
    return els,mul
def perm_group(gens):
    k=len(gens[0]); e=tuple(range(k)); els=[e]; seen={e}
    mul=lambda a,b: tuple(a[i] for i in b)
    i=0
    while i<len(els):
        for g in gens:
            y=mul(els[i],g)
            if y not in seen: seen.add(y); els.append(y)
        i+=1
    return els,mul
groups=[cyclic([m]) for m in range(3,10)]+[cyclic([2,2]),cyclic([2,4]),cyclic([2,2,2]),cyclic([3,3])]
groups.append(perm_group([(1,2,0),(1,0,2)]))                         # S3
groups.append(perm_group([(1,2,3,0),(0,3,2,1)]))                     # D4
groups.append(perm_group([(1,2,3,0,5,6,7,4),(4,7,6,5,2,1,0,3)]))     # Q8 (regular representation: i and j)
out=set()
for els,mul in groups:
    n=len(els); idx={x:i for i,x in enumerate(els)}; e=els[0]
    assert all(mul(e,x)==x for x in els)
    inv={}
    for x in els:
        for y in els:
            if mul(x,y)==e: inv[x]=y
    classes=[]; done=set()
    for x in els[1:]:
        if x in done: continue
        c={x,inv[x]}; done|=c; classes.append(sorted(c))
    for r in range(1,len(classes)+1):
        for comb in itertools.combinations(classes,r):
            S=[x for c in comb for x in c]
            edges=set()
            for x in els:
                for s in S:
                    a,b=idx[x],idx[mul(x,s)]
                    if a!=b: edges.add((min(a,b),max(a,b)))
            out.add(g6(n,edges))
for s in sorted(out): print(s)
