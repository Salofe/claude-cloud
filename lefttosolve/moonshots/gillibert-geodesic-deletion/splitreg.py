import sys
# split graph6 stdin into regular (stdout) / non-regular (stderr)
for line in sys.stdin:
    s=line.strip()
    if not s: continue
    n=ord(s[0])-63
    if n>62: 
        continue
    deg=[0]*n; k=0
    for j in range(1,n):
        for i in range(j):
            if (ord(s[1+k//6])-63)>>(5-k%6)&1:
                deg[i]+=1; deg[j]+=1
            k+=1
    (sys.stdout if len(set(deg))==1 else sys.stderr).write(s+'\n')
