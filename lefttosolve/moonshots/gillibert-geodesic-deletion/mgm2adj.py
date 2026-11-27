import sys,re
data=sys.stdin.read()
# entries: Name[n,k] := Graph<n | {{a,b}, ...}>;
for m in re.finditer(r'(\w+)\[(\d+),(\d+)\]\s*:=\s*Graph<\s*(\d+)\s*\|\s*\{(.*?)\}\s*>\s*;', data, re.S):
    name,nn,k,n,body=m.group(1),int(m.group(2)),int(m.group(3)),int(m.group(4)),m.group(5)
    adj=[[] for _ in range(n)]
    for e in re.finditer(r'\{\s*(\d+)\s*,\s*(\d+)\s*\}', body):
        a,b=int(e.group(1))-1,int(e.group(2))-1
        adj[a].append(b); adj[b].append(a)
    sys.stdout.write('%d %s_%d_%d\n'%(n,name,nn,k))
    for v in range(n):
        sys.stdout.write(' '.join(map(str,adj[v]))+'\n')
