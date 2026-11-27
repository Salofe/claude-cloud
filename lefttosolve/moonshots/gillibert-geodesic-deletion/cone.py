import sys
def parse(s):
    n=ord(s[0])-63; adj=[0]*n; k=0
    for j in range(1,n):
        for i in range(j):
            if (ord(s[1+k//6])-63)>>(5-k%6)&1:
                adj[i]|=1<<j; adj[j]|=1<<i
            k+=1
    return n,adj
def bfs(n,adj,s):
    d=[-1]*n; d[s]=0; fr=[s]
    while fr:
        nf=[]
        for v in fr:
            m=adj[v]
            while m:
                w=(m&-m).bit_length()-1; m&=m-1
                if d[w]<0: d[w]=d[v]+1; nf.append(w)
        fr=nf
    return d
def comps(adj,mask):
    res=[]
    while mask:
        s=mask&-mask; seen=s; fr=s
        while fr:
            v=(fr&-fr).bit_length()-1; fr&=fr-1
            nw=adj[v]&mask&~seen; seen|=nw; fr|=nw
        res.append(seen); mask&=~seen
    return res
tot=0; fail=0
for fn in sys.argv[1:]:
    for idx,line in enumerate(open(fn)):
        s=line.strip()
        if not s: continue
        n,adj=parse(s)
        full=(1<<n)-1
        if len(comps(adj,full))!=1 or n<3: continue
        tot+=1
        d0=bfs(n,adj,0); deg=bin(adj[0]).count('1')
        m=adj[0]; bad=[]
        while m:
            v1=(m&-m).bit_length()-1; m&=m-1
            d1=bfs(n,adj,v1)
            Y=0
            for x in range(n):
                if d0[x]<=d1[x]: Y|=1<<x
            Y&=~1
            cs=comps(adj,Y)
            if len(cs)>1: bad.append((v1,sorted(bin(c).count('1') for c in cs)))
        if bad:
            fail+=1
            # twins?
            opent=any(adj[0]==adj[x] for x in range(1,n))
            closedt=any((adj[0]|1)==(adj[x]|(1<<x)) for x in range(1,n))
            diam=max(d0)
            print(fn.split('/')[-1],idx+1,'n',n,'deg',deg,'diam',diam,'opentwins',opent,'closedtwins',closedt,'bad',bad[:3],len(bad))
print('connected graphs',tot,'with failing depth-1 cone',fail)
