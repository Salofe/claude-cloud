// Bitset version (n<=64) of the pruned minimal-separating-geodesic search; graph6 on stdin; base vertex 0 (vertex-transitive input).
#include <bits/stdc++.h>
using namespace std; typedef unsigned long long u64;
static int n; static u64 adj[64], fwdm[64], full; static int lvl[64];
static long long nodes; static bool found; static int v0, v1g; static int pathv[64]; static int maxDepth;
static inline u64 reach(u64 start,u64 allowed){ u64 seen=start&allowed, fr=seen; while(fr){ int v=__builtin_ctzll(fr); fr&=fr-1; u64 nw=adj[v]&allowed&~seen; seen|=nw; fr|=nw;} return seen; }
static void dfs(int v,int i,u64 pm){
  if(found) return; nodes++;
  bool prune=false;
  if(i>=1){
    u64 D=0, fr=fwdm[v]; D=fr; while(fr){int x=__builtin_ctzll(fr); fr&=fr-1; u64 nw=fwdm[x]&~D; D|=nw; fr|=nw;}
    u64 Y=adj[v0]&~(1ULL<<v1g);
    if(!Y) prune=true; else { u64 s=Y&-Y; u64 r=reach(s,full&~pm&~D); if((Y&~r)==0) prune=true; }
    if(!prune){ u64 rem=full&~pm; if(!rem) found=true; else { u64 r=reach(rem&-rem,rem); if(r!=rem) found=true; } if(i>maxDepth) maxDepth=i; }
  }
  if(!prune&&!found){ u64 f=fwdm[v]; while(f){int w=__builtin_ctzll(f); f&=f-1; if(i==0) v1g=w; dfs(w,i+1,pm|(1ULL<<w)); if(found) return; } }
}
int main(){ string s; long long tot=0,con=0,ce=0,totn=0,maxn=0; long long dh[8]={0};
  while(getline(cin,s)){ if(s.empty()) continue; n=s[0]-63; if(n>64||n<1) continue; for(int i=0;i<n;i++) adj[i]=0; int k=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){ int b=(s[1+k/6]-63)>>(5-k%6)&1; k++; if(b){adj[i]|=1ULL<<j; adj[j]|=1ULL<<i;} }
    tot++; full=(n==64)?~0ULL:((1ULL<<n)-1); if(n<3) continue; if(reach(1,full)!=full) continue; con++;
    // levels from 0
    for(int i=0;i<n;i++) lvl[i]=-1; u64 seen=1, fr=1; int L=0; lvl[0]=0; vector<u64> lm; lm.push_back(1);
    while(true){ u64 nb=0, m=fr; while(m){int v=__builtin_ctzll(m); m&=m-1; nb|=adj[v];} nb&=~seen; if(!nb) break; L++; u64 m2=nb; while(m2){int v=__builtin_ctzll(m2); m2&=m2-1; lvl[v]=L;} lm.push_back(nb); seen|=nb; fr=nb; }
    lm.push_back(0);
    for(int v=0;v<n;v++) fwdm[v]=adj[v]&lm[lvl[v]+1];
    nodes=0; found=false; v0=0; maxDepth=0;
    // cut vertex check
    { u64 rem=full&~1ULL; u64 r=reach(rem&-rem,rem); if(r!=rem) found=true; }
    if(!found) dfs(0,0,1ULL);
    totn+=nodes; if(nodes>maxn) maxn=nodes; dh[min(maxDepth,7)]++;
    if(found){ ce++; if(ce<=20) printf("COUNTER %s\n",s.c_str()); }
  }
  printf("depthhist:"); for(int i=0;i<8;i++) if(dh[i]) printf(" %d:%lld",i,dh[i]); printf("\n");
  printf("total %lld connected %lld capped 0 counterexamples %lld nodes %lld maxnodes %lld\n",tot,con,ce,totn,maxn); }
