// exact.c -- exhaustive enumeration of Hamiltonian paths from vertex 0 in a sparse labelled graph.
// Input: LABELS lines as printed by "ftc -D":
//   LABELS meta | n=.. deg=.. K=.. | u:l u:l ...      (deg entries per vertex)
// Since the graph is vertex-transitive and labels are automorphism-invariant, every Hamiltonian path has
// an automorphic image starting at vertex 0, so the set of count vectors found is complete.
// Output: VEC meta | n deg K | sizes | status nodes | list of vectors
// usage: exact [-L nodelimit] [-N maxn]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 400
#define MAXD 8
#define MAXK 6
typedef unsigned long long u64;

static int n, deg, K;
static int nbr[MAXN][MAXD]; static unsigned char lab[MAXN][MAXD];
static char vis[MAXN];
static int avail[MAXN];      // number of unvisited neighbours
static int cnt[MAXK];
static u64 nodes, node_limit = 2000000000ULL; static int aborted;
static u64 npaths;
// vector set: open hash of packed keys
#define HSZ (1<<16)
static u64 hkeys[HSZ]; static char hused[HSZ]; static int hcount;
static void hadd(void){
    u64 key = 0; for (int i = 0; i < K; i++) key = key * 1024 + (u64)cnt[i];
    u64 h = (key * 0x9E3779B97F4A7C15ULL) >> 48;
    while (hused[h]) { if (hkeys[h] == key) return; h = (h + 1) & (HSZ-1); }
    hused[h] = 1; hkeys[h] = key; hcount++;
}
static int stack[MAXN], qmark[MAXN], qstamp;
// connectivity of unvisited vertices from the current end v (through unvisited vertices)
static int reach_all(int v, int remaining){
    qstamp++; int sp = 0, c = 0;
    for (int i = 0; i < deg; i++) { int u = nbr[v][i]; if (!vis[u] && qmark[u] != qstamp) { qmark[u] = qstamp; stack[sp++] = u; c++; } }
    while (sp) { int x = stack[--sp]; for (int i = 0; i < deg; i++) { int u = nbr[x][i]; if (!vis[u] && qmark[u] != qstamp) { qmark[u] = qstamp; stack[sp++] = u; c++; } } }
    return c == remaining;
}
static void dfs(int v, int remaining){
    if (aborted) return;
    if (++nodes > node_limit) { aborted = 1; return; }
    if (remaining == 0) { npaths++; hadd(); return; }
    // dead-end analysis: unvisited w with avail(w)+adj(v,w) <= 1
    // (only neighbours of recently visited vertices can change; do a cheap global check every level for small n)
    int forced_last = -1;
    for (int w = 0; w < n; w++) if (!vis[w]) {
        int a = avail[w];
        int adjv = 0; for (int i = 0; i < deg; i++) if (nbr[w][i] == v) { adjv = 1; break; }
        if (a + adjv == 0) return;
        if (a + adjv == 1) { if (remaining > 1) { if (forced_last >= 0) return; forced_last = w; } }
    }
    if (!reach_all(v, remaining)) return;
    for (int i = 0; i < deg; i++) {
        int u = nbr[v][i];
        if (vis[u]) continue;
        // if u is a forced-last vertex and remaining > 1, cannot go there now
        if (forced_last == u && remaining > 1) continue;
        vis[u] = 1; cnt[lab[v][i]]++;
        for (int j = 0; j < deg; j++) avail[nbr[u][j]]--;
        dfs(u, remaining - 1);
        for (int j = 0; j < deg; j++) avail[nbr[u][j]]++;
        vis[u] = 0; cnt[lab[v][i]]--;
        if (aborted) return;
    }
}
int main(int argc, char **argv){
    int maxn = MAXN;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-L") && i+1 < argc) node_limit = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "-N") && i+1 < argc) maxn = atoi(argv[++i]);
    }
    size_t cap = 1<<22; char *line = malloc(cap);
    while (fgets(line, cap, stdin)) {
        if (strncmp(line, "LABELS", 6)) continue;
        char *b1 = strchr(line, '|'); if (!b1) continue; *b1 = 0;
        char *b2 = strchr(b1+1, '|'); if (!b2) continue; *b2 = 0;
        char meta[256]; strncpy(meta, line + 7, 255); meta[255] = 0;
        size_t L = strlen(meta); while (L && meta[L-1] == ' ') meta[--L] = 0;
        if (sscanf(b1+1, " n=%d deg=%d K=%d", &n, &deg, &K) != 3) continue;
        if (n > maxn || n > MAXN || deg > MAXD || K > MAXK) { continue; }
        char *p = b2 + 1; int ok = 1;
        for (int v = 0; v < n && ok; v++) for (int i = 0; i < deg; i++) {
            char *e; long u = strtol(p, &e, 10); if (e == p || *e != ':') { ok = 0; break; }
            p = e + 1; long l = strtol(p, &e, 10); if (e == p) { ok = 0; break; }
            p = e; nbr[v][i] = (int)u; lab[v][i] = (unsigned char)l;
        }
        if (!ok) { printf("VEC %s | parse error\n", meta); continue; }
        int msz[MAXK]; memset(msz, 0, sizeof msz);
        for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) if (v < nbr[v][i]) msz[lab[v][i]]++;
        memset(vis, 0, sizeof vis); memset(cnt, 0, sizeof cnt);
        memset(hused, 0, sizeof hused); hcount = 0; nodes = 0; aborted = 0; npaths = 0;
        for (int v = 0; v < n; v++) avail[v] = deg;
        vis[0] = 1; for (int j = 0; j < deg; j++) avail[nbr[0][j]]--;
        dfs(0, n - 1);
        printf("VEC %s | %d %d %d |", meta, n, deg, K);
        for (int i = 0; i < K; i++) printf(" %d", msz[i]);
        printf(" | %s nodes=%llu paths=%llu nvec=%d |", aborted ? "INCOMPLETE" : "COMPLETE", nodes, npaths, hcount);
        for (int h = 0; h < HSZ; h++) if (hused[h]) {
            u64 key = hkeys[h]; int c[MAXK];
            for (int i = K-1; i >= 0; i--) { c[i] = (int)(key % 1024); key /= 1024; }
            printf(" ("); for (int i = 0; i < K; i++) printf("%d%s", c[i], i+1 < K ? "," : ""); printf(")");
        }
        printf("\n"); fflush(stdout);
    }
    return 0;
}
