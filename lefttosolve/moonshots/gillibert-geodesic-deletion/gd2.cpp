// Geodesic deletion checker.
// For each input graph (assumed connected), search for a MINIMAL separating geodesic
// starting at base vertex 0 (mode vt) or at every vertex (mode all).
// Minimal separating geodesic P=(v0..vl): G-V(P) disconnected, but removing either end
// vertex from P gives a non-separating path. Then every component of G-V(P) is adjacent to v0,
// so N(v0)\{v1} meets >=2 components.  Pruning: for a prefix P[0..i] (i>=1), let D be the set of
// strict descendants of v_i in the BFS dag from v0.  Every extension S satisfies
// S subset P[0..i] u D, so G-P[0..i]-D is a subgraph of G-S.  If N(v0)\{v1} lies in a single
// component of G-P[0..i]-D, no minimal separating geodesic has this prefix.
// Formats: -f mgm  (lines "n|k|GrphUnd" then "[ { a, b, c }, ... ]"), -f g6 (graph6), -f s6 (sparse6),
//          -f adj (line: n then n lines of neighbours, 0-based, separated by spaces; blank line between graphs)
#include <bits/stdc++.h>
using namespace std;
static int n; static vector<vector<int>> adj;
static vector<int> lvl, inP, stampD, stampV, bq; static int curD=0, curV=0;
static vector<vector<int>> fwd;
static int maxDepthG=0, depthThr=1000000; static long long depthHist[64]; static long long nodes, nodeCap=50000000LL; static bool capped, found;
static vector<int> path; static vector<int> witness;
static int base;
static bool bruteMode=false;

static void bfsLevels(int s){
  lvl.assign(n,-1); lvl[s]=0; int h=0,t=0; bq[t++]=s;
  while(h<t){int v=bq[h++]; for(int w:adj[v]) if(lvl[w]<0){lvl[w]=lvl[v]+1; bq[t++]=w;}}
  for(int v=0;v<n;v++){ fwd[v].clear(); for(int w:adj[v]) if(lvl[w]==lvl[v]+1) fwd[v].push_back(w);} 
}
// BFS in G minus inP minus (stampD==curD if useD) from s; returns number reached
static int bfsAvoid(int s,bool useD){
  curV++; int h=0,t=0; bq[t++]=s; stampV[s]=curV;
  while(h<t){int v=bq[h++]; for(int w:adj[v]){ if(stampV[w]==curV||inP[w]) continue; if(useD&&stampD[w]==curD) continue; stampV[w]=curV; bq[t++]=w; }}
  return t;
}
static void dfs(int v,int i){
  if(found||capped) return; nodes++; if(nodes>nodeCap){capped=true;return;}
  inP[v]=1; path.push_back(v);
  bool prune=false;
  if(i>=1){
    int v0=path[0], v1=path[1];
    if(!bruteMode){
      // descendants
      curD++; int h=0,t=0; // reuse a local queue
      static vector<int> dq; if((int)dq.size()<n) dq.resize(n);
      for(int w:fwd[v]) if(stampD[w]!=curD){stampD[w]=curD; dq[t++]=w;}
      while(h<t){int x=dq[h++]; for(int w:fwd[x]) if(stampD[w]!=curD){stampD[w]=curD; dq[t++]=w;}}
      int s=-1; for(int w:adj[v0]) if(w!=v1){s=w;break;}
      if(s<0) prune=true; else {
        bfsAvoid(s,true); bool all=true; for(int w:adj[v0]) if(w!=v1 && stampV[w]!=curV){all=false;break;}
        if(all) prune=true;
      }
    }
    if(!prune){
      int s=-1; for(int x=0;x<n;x++) if(!inP[x]){s=x;break;}
      int rem=n-(i+1);
      if(s<0){ found=true; witness=path; }
      else { int r=bfsAvoid(s,false); if(r<rem){ found=true; witness=path; } }
    }
  }
  if(!prune && i>maxDepthG) maxDepthG=i;
  if(!prune && !found){ for(int w:fwd[v]){ dfs(w,i+1); if(found||capped) break; } }
  inP[v]=0; path.pop_back();
}
static bool connectedAll(){ curV++; int h=0,t=0; bq[t++]=0; stampV[0]=curV; while(h<t){int v=bq[h++]; for(int w:adj[v]) if(stampV[w]!=curV){stampV[w]=curV; bq[t++]=w;}} return t==n; }
static bool isRegular(){ for(int v=1;v<n;v++) if(adj[v].size()!=adj[0].size()) return false; return true; }

static long long totBad=0,totG=0,totConn=0,totCapped=0,totCE=0,totNodes=0,maxNodes=0; static string maxName;
static bool allMode=false; static int printCE=20;
static void processGraph(const string&name){
  totG++;
  lvl.assign(n,-1); inP.assign(n,0); stampD.assign(n,0); stampV.assign(n,0); bq.assign(n,0); fwd.assign(n,{}); curD=curV=0;
  { bool bad=false; for(int v=0;v<n&&!bad;v++){ if(adj[v].size()!=adj[0].size()) bad=true; for(int w:adj[v]){ if(w<0||w>=n||w==v){bad=true;break;} bool f=false; for(int u:adj[w]) if(u==v) f=true; if(!f){bad=true;break;} } }
    if(bad){ totBad++; if(totBad<=5) printf("BADGRAPH %s n=%d\n",name.c_str(),n); } }
  if(n<3||!connectedAll()) return; totConn++;
  nodes=0; capped=false; found=false; path.clear(); maxDepthG=0;
  int nb = allMode? n:1;
  for(base=0;base<nb&&!found&&!capped;base++){
    bfsLevels(base);
    // l=0: cut vertex?
    inP[base]=1; int s=adj[base].empty()?-1:adj[base][0]; if(s>=0){ int r=bfsAvoid(s,false); if(r<n-1){found=true; witness={base};} } inP[base]=0;
    if(!found) dfs(base,0);
  }
  totNodes+=nodes; if(nodes>maxNodes){maxNodes=nodes; maxName=name;}
  depthHist[min(maxDepthG,63)]++; if(maxDepthG>=depthThr){ printf("DEEP %s n=%d deg=%zu depth=%d nodes=%lld\n",name.c_str(),n,adj[0].size(),maxDepthG,nodes); }
  if(capped){ totCapped++; printf("CAPPED %s n=%d deg=%zu nodes=%lld\n",name.c_str(),n,adj[0].size(),nodes); fflush(stdout);} 
  if(found){ totCE++; if(totCE<=printCE){ printf("COUNTER %s n=%d path:",name.c_str(),n); for(int v:witness) printf(" %d",v); printf("\n"); fflush(stdout);} }
}
static bool parseG6(const string&s){
  size_t p=0; if(s.size()<1) return false; 
  if(s[0]=='>'){ return false; }
  int nn; if(s[0]!=126){ nn=s[0]-63; p=1; } else if(s[1]!=126){ nn=((s[1]-63)<<12)|((s[2]-63)<<6)|(s[3]-63); p=4; } else return false;
  n=nn; adj.assign(n,{}); long long k=0; 
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ int b=(s[p+k/6]-63)>>(5-k%6)&1; k++; if(b){adj[i].push_back(j); adj[j].push_back(i);} }
  return true;
}
static bool parseS6(const string&s){
  if(s.size()<2||s[0]!=':') return false; size_t p=1; int nn;
  if(s[p]!=126){ nn=s[p]-63; p+=1; } else if(s[p+1]!=126){ nn=((s[p+1]-63)<<12)|((s[p+2]-63)<<6)|(s[p+3]-63); p+=4; } else return false;
  n=nn; adj.assign(n,{}); int k=1; while((1<<k)<n) k++; if(n==1) k=1; 
  // bit reader
  vector<int> bits; for(size_t q=p;q<s.size();q++){ int c=s[q]-63; for(int b=5;b>=0;b--) bits.push_back((c>>b)&1); }
  size_t pos=0; int v=0; set<pair<int,int>> seen;
  while(pos+1+k<=bits.size()){
    int b=bits[pos++]; int x=0; for(int t=0;t<k;t++) x=(x<<1)|bits[pos++];
    if(b) v++;
    if(v>=n) break;
    if(x>v) v=x; else { if(x!=v){ int a=min(x,v), c=max(x,v); if(!seen.count({a,c})){ seen.insert({a,c}); adj[a].push_back(c); adj[c].push_back(a);} } }
  }
  return true;
}
int main(int argc,char**argv){
  string fmt="g6"; long long skip=0, limit=-1; 
  for(int i=1;i<argc;i++){ string a=argv[i]; if(a=="-f") fmt=argv[++i]; else if(a=="-all") allMode=true; else if(a=="-brute") bruteMode=true; else if(a=="-cap") nodeCap=atoll(argv[++i]); else if(a=="-skip") skip=atoll(argv[++i]); else if(a=="-limit") limit=atoll(argv[++i]); else if(a=="-printce") printCE=atoi(argv[++i]); else if(a=="-deep") depthThr=atoi(argv[++i]); }
  string line; long long idx=0; string name; time_t t0=time(0); long long lastRep=0;
  auto report=[&](){ fprintf(stderr,"[%lds] graphs %lld connected %lld capped %lld counterexamples %lld nodes %lld maxnodes %lld (%s) last=%s\n",(long)(time(0)-t0),totG,totConn,totCapped,totCE,totNodes,maxNodes,maxName.c_str(),name.c_str()); fflush(stderr); };
  if(fmt=="mgm"){
    while(getline(cin,line)){
      if(line.empty()) continue;
      if(line[0]!='['){ name=line; continue; }
      idx++; if(idx<=skip) continue; if(limit>=0 && idx>skip+limit) break;
      // parse adjacency
      vector<vector<int>> a; const char*c=line.c_str(); vector<int> cur; bool in=false; long val=-1;
      for(;*c;c++){ if(*c=='{'){in=true;cur.clear();val=-1;} else if(*c=='}'){ if(val>=0)cur.push_back((int)val-1); val=-1; a.push_back(cur); in=false;} else if(isdigit((unsigned char)*c)){ if(val<0)val=0; val=val*10+(*c-'0'); } else { if(in&&val>=0){cur.push_back((int)val-1);} val=-1; } }
      n=a.size(); adj=a; processGraph(name);
      if(totG-lastRep>=2000){lastRep=totG; report();}
    }
  } else if(fmt=="g6"||fmt=="s6"){
    while(getline(cin,line)){
      if(line.empty()) continue; idx++; if(idx<=skip) continue; if(limit>=0 && idx>skip+limit) break;
      bool ok = (line[0]==':')? parseS6(line): parseG6(line); if(!ok) continue;
      name="#"+to_string(idx); processGraph(name.c_str());
      if(totG-lastRep>=200000){lastRep=totG; report();}
    }
  } else if(fmt=="adj"){
    while(true){ if(!(cin>>n)) break; string nm; getline(cin,nm); adj.assign(n,{}); for(int v=0;v<n;v++){ getline(cin,line); stringstream ss(line); int w; while(ss>>w) adj[v].push_back(w);} idx++; name=nm.empty()? "#"+to_string(idx):nm; if(idx<=skip) continue; if(limit>=0&&idx>skip+limit) break; processGraph(name); if(totG-lastRep>=2000){lastRep=totG; report();} }
  }
  report();
  printf("depthhist:"); for(int i=0;i<64;i++) if(depthHist[i]) printf(" %d:%lld",i,depthHist[i]); printf("\n");
  printf("total %lld connected %lld capped %lld counterexamples %lld nodes %lld maxnodes %lld (%s) nonregular_or_asymmetric %lld\n",totG,totConn,totCapped,totCE,totNodes,maxNodes,maxName.c_str(),totBad);
  return 0;
}
