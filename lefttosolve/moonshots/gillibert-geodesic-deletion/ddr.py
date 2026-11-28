import sys
# classify graph6 graphs: DDR (distance-degree regular) or not; write DDR ones to stdout, others to stderr
def parse(s):
    n=ord(s[0])-63; adj=[0]*n; k=0
    for j in range(1,n):
        for i in range(j):
            if (ord(s[1+k//6])-63)>>(5-k%6)&1:
                adj[i]|=1<<j; adj[j]|=1<<i
            k+=1
    return n,adj
def levels(n,adj,s):
    seen=1<<s; fr=1<<s; res=[]
    while fr:
        res.append(bin(fr).count('1'))
        nb=0; m=fr
        while m:
            v=(m&-m).bit_length()-1; m&=m-1; nb|=adj[v]
        fr=nb&~seen; seen|=fr
    return tuple(res)
for line in sys.stdin:
    s=line.strip()
    if not s: continue
    n,adj=parse(s)
    l0=levels(n,adj,0)
    ok=all(levels(n,adj,v)==l0 for v in range(1,n))
    (sys.stdout if ok else sys.stderr).write(s+'\n')
