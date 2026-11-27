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
for _ in range(N):
    n=random.randint(5,14)
    p=random.choice([0.15,0.2,0.3,0.4])
    edges=[(i,j) for j in range(n) for i in range(j) if random.random()<p]
    print(g6(n,edges))
