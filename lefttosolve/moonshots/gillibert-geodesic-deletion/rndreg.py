import random, sys
def g6(n, edges):
    bits=[]
    es=set(edges)
    for j in range(1,n):
        for i in range(j):
            bits.append(1 if (i,j) in es else 0)
    while len(bits)%6: bits.append(0)
    s=chr(n+63)
    for k in range(0,len(bits),6):
        v=0
        for b in bits[k:k+6]: v=v*2+b
        s+=chr(v+63)
    return s
random.seed(int(sys.argv[1]))
N=int(sys.argv[2])
cnt=0
while cnt<N:
    n=random.randint(8,40)
    d=random.choice([3,3,4])
    if n*d%2: continue
    pts=[v for v in range(n) for _ in range(d)]
    random.shuffle(pts)
    es=set(); ok=True
    for k in range(0,len(pts),2):
        a,b=pts[k],pts[k+1]
        if a==b or (min(a,b),max(a,b)) in es: ok=False;break
        es.add((min(a,b),max(a,b)))
    if not ok: continue
    print(g6(n,sorted(es))); cnt+=1
