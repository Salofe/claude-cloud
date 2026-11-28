import sys
# stdin graph6 -> stdout those connected graphs with constant eccentricity D and exactly one vertex at distance D from each vertex
def parse(s):
    n=ord(s[0])-63; adj=[0]*n; k=0
    for j in range(1,n):
        for i in range(j):
            if (ord(s[1+k//6])-63)>>(5-k%6)&1:
                adj[i]|=1<<j; adj[j]|=1<<i
            k+=1
    return n,adj
def lastlevel(n,adj,s):
    seen=1<<s; fr=1<<s; depth=0; last=fr
    while True:
        nb=0; m=fr
        while m:
            v=(m&-m).bit_length()-1; m&=m-1; nb|=adj[v]
        fr=nb&~seen
        if not fr: break
        seen|=fr; depth+=1; last=fr
    return depth, bin(last).count('1'), bin(seen).count('1')
for line in sys.stdin:
    s=line.strip()
    if not s: continue
    n,adj=parse(s)
    if n<3 or n>62: continue
    d0,c0,r0=lastlevel(n,adj,0)
    if r0!=n or c0!=1: continue
    ok=True
    for v in range(1,n):
        d,c,r=lastlevel(n,adj,v)
        if d!=d0 or c!=1: ok=False;break
    if ok: print(s)
