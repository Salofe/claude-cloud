// ftc.c -- fair traversal checker for sparse connected vertex-transitive graphs given by adjacency lists.
// Input lines:  n meta... | a_0 a_1 ... (n*d integers, d neighbours per vertex, 0-based)
// Same method as ft.c (edge orbits by verified automorphisms, column generation with a rotation walk,
// exact check of a PASS), but with array data structures so that n can be large (<= MAXN).
//
// usage: ftc [-v] [-s seed] [-e effort] [-N maxn] [-n minn] < graphs.txt
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1300
#define MAXD 12
#define MAXK 12
#define MAXCOLS 400
typedef unsigned long long u64;
typedef __int128 i128;

static int n, deg;
static int nbr[MAXN][MAXD];
static unsigned char lab[MAXN][MAXD];
static int K;
static int msz[MAXK];
static int verbose = 0;
static int limit_flag;

static u64 rs = 88172645463325252ULL;
static inline u64 rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static inline int rndint(int m){ return (int)(rnd() % (u64)m); }
static inline double rnd01(void){ return (double)(rnd()>>11) * (1.0/9007199254740992.0); }

static int adjacent(int a, int b){ for (int i = 0; i < deg; i++) if (nbr[a][i] == b) return 1; return 0; }
static int edge_lab(int a, int b){ for (int i = 0; i < deg; i++) if (nbr[a][i] == b) return lab[a][i]; fprintf(stderr, "internal: edge_lab of non-edge\n"); exit(3); }

static int connected(void){
    static int st[MAXN]; static char seen[MAXN];
    memset(seen, 0, n); int sp = 0, c = 1; st[sp++] = 0; seen[0] = 1;
    while (sp) { int v = st[--sp]; for (int i = 0; i < deg; i++) { int u = nbr[v][i]; if (!seen[u]) { seen[u] = 1; c++; st[sp++] = u; } } }
    return c == n;
}

// ---------------- automorphism search
static u64 RH[2*MAXN+16];
typedef struct { int col; u64 h; int v; } SigT;
static int cmp_sig(const void *a, const void *b){
    const SigT *x = a, *y = b;
    if (x->col != y->col) return x->col < y->col ? -1 : 1;
    if (x->h != y->h) return x->h < y->h ? -1 : 1;
    return 0;
}
static SigT sg[2*MAXN]; static int newc[2*MAXN];
static int refine(int *ca, int *cb){
    int ncol = -1;
    for (;;) {
        for (int v = 0; v < n; v++) {
            u64 h = 0, g = 0;
            for (int i = 0; i < deg; i++) { h += RH[ca[nbr[v][i]]]; g += RH[cb[nbr[v][i]]]; }
            sg[v].col = ca[v]; sg[v].h = h; sg[v].v = v;
            sg[n+v].col = cb[v]; sg[n+v].h = g; sg[n+v].v = n+v;
        }
        qsort(sg, 2*n, sizeof(SigT), cmp_sig);
        int nc = -1, bal = 0; int pc = 0; u64 ph = 0;
        for (int i = 0; i < 2*n; i++) {
            if (i == 0 || sg[i].col != pc || sg[i].h != ph) {
                if (bal != 0) return -1;
                nc++; pc = sg[i].col; ph = sg[i].h;
            }
            if (sg[i].v < n) { bal++; } else { bal--; }
            newc[i] = nc;
        }
        if (bal != 0) return -1;
        nc++;
        for (int i = 0; i < 2*n; i++) { if (sg[i].v < n) ca[sg[i].v] = newc[i]; else cb[sg[i].v - n] = newc[i]; }
        if (nc == ncol) return nc;
        ncol = nc;
    }
}
static long nodes_left;
static int is_aut(const int *p){
    static char seen[MAXN]; memset(seen, 0, n);
    for (int v = 0; v < n; v++) {
        if (p[v] < 0 || p[v] >= n || seen[p[v]]) return 0;
        seen[p[v]] = 1;
        for (int i = 0; i < deg; i++) if (!adjacent(p[v], p[nbr[v][i]])) return 0;
    }
    return 1;
}
static int search(int *ca, int *cb, int *perm, int depth){
    int ncol = refine(ca, cb);
    if (ncol < 0) return 0;
    if (ncol == n) {
        static int inv[MAXN];
        for (int w = 0; w < n; w++) inv[cb[w]] = w;
        for (int v = 0; v < n; v++) perm[v] = inv[ca[v]];
        return is_aut(perm) ? 1 : 0;
    }
    int *cnt = calloc(ncol, sizeof(int));
    for (int v = 0; v < n; v++) cnt[ca[v]]++;
    int best = -1;
    for (int c = 0; c < ncol; c++) if (cnt[c] >= 2 && (best < 0 || cnt[c] < cnt[best])) best = c;
    free(cnt);
    int v = 0; while (ca[v] != best) v++;
    int *ca2 = malloc(sizeof(int)*n), *cb2 = malloc(sizeof(int)*n);
    int res = 0;
    for (int w = 0; w < n; w++) if (cb[w] == best) {
        if (nodes_left-- <= 0) { res = -1; break; }
        memcpy(ca2, ca, sizeof(int)*n); memcpy(cb2, cb, sizeof(int)*n);
        ca2[v] = ncol; cb2[w] = ncol;
        int r = search(ca2, cb2, perm, depth+1);
        if (r != 0) { res = r; break; }
    }
    free(ca2); free(cb2);
    return res;
}
#define NODE_LIMIT 20000
// BFS distances from src into dist[]
static void bfs_dist(int src, int *dist){
    static int qu[MAXN];
    for (int x = 0; x < n; x++) dist[x] = -1;
    int qh = 0, qt = 0; qu[qt++] = src; dist[src] = 0;
    while (qh < qt) { int v = qu[qh++]; for (int i = 0; i < deg; i++) { int u = nbr[v][i]; if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[qt++] = u; } } }
}
// initial colourings from distance pairs: ca[x] = code(dA1[x], dA2[x]), cb[x] = code(dB1[x], dB2[x]) with dense ids
static void dist_colour(const int *dA1, const int *dA2, const int *dB1, const int *dB2, int *ca, int *cb){
    static int key[2*MAXN], ord[2*MAXN];
    for (int x = 0; x < n; x++) { key[x] = dA1[x] * (MAXN+1) + (dA2 ? dA2[x] : 0); key[n+x] = dB1[x] * (MAXN+1) + (dB2 ? dB2[x] : 0); }
    // dense ids: counting via sorting of keys
    for (int i = 0; i < 2*n; i++) ord[i] = i;
    // simple shell sort by key
    for (int gap = n; gap > 0; gap /= 2) for (int i = gap; i < 2*n; i++) { int t = ord[i], j = i; while (j >= gap && key[ord[j-gap]] > key[t]) { ord[j] = ord[j-gap]; j -= gap; } ord[j] = t; }
    int id = -1, prev = -1;
    for (int i = 0; i < 2*n; i++) { int o = ord[i]; if (i == 0 || key[o] != prev) { id++; prev = key[o]; } if (o < n) ca[o] = id; else cb[o-n] = id; }
}

static int ufp[MAXN];
static int uf_find(int x){ while (ufp[x] != x) { ufp[x] = ufp[ufp[x]]; x = ufp[x]; } return x; }
static void uf_union(int a, int b){ a = uf_find(a); b = uf_find(b); if (a != b) ufp[a] = b; }

static int (*trans)[MAXN], (*transinv)[MAXN];
static int compute_orbits(void){
    static int gens[64][MAXN]; int ngens = 0;
    static char has[MAXN]; memset(has, 0, n);
    static int ca[MAXN], cb[MAXN], perm[MAXN];
    limit_flag = 0;
    static int d0[MAXN]; bfs_dist(0, d0);
    has[0] = 1; for (int x = 0; x < n; x++) trans[0][x] = x;
    for (;;) {
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int v = 0; v < n; v++) if (has[v]) for (int g = 0; g < ngens; g++) {
                int w = gens[g][v];
                if (!has[w]) { for (int x = 0; x < n; x++) trans[w][x] = gens[g][trans[v][x]]; has[w] = 1; changed = 1; }
            }
        }
        int v = 0; while (v < n && has[v]) v++;
        if (v == n) break;
        { static int dv[MAXN]; bfs_dist(v, dv); dist_colour(d0, 0, dv, 0, ca, cb); }
        nodes_left = NODE_LIMIT * 10L;
        int r = search(ca, cb, perm, 0);
        if (r != 1) return -1;
        if (ngens >= 64) return -1;
        memcpy(gens[ngens++], perm, sizeof(int)*n);
    }
    for (int v = 0; v < n; v++) for (int x = 0; x < n; x++) transinv[v][trans[v][x]] = x;
    for (int x = 0; x < n; x++) ufp[x] = x;
    int reps[MAXD], nreps = 0;
    for (int i = 0; i < deg; i++) {
        int u = nbr[0][i], found = 0;
        for (int j = 0; j < nreps; j++) if (uf_find(reps[j]) == uf_find(u)) { found = 1; break; }
        if (found) continue;
        for (int j = 0; j < nreps && !found; j++) {
            int r0 = reps[j];
            { static int dr[MAXN], du[MAXN]; bfs_dist(r0, dr); bfs_dist(u, du); dist_colour(d0, dr, d0, du, ca, cb); }
            nodes_left = NODE_LIMIT;
            int r = search(ca, cb, perm, 0);
            if (r == 1) {
                if (perm[0] != 0 || perm[r0] != u) { fprintf(stderr, "internal: bad stabiliser perm\n"); exit(3); }
                for (int t = 0; t < deg; t++) uf_union(nbr[0][t], perm[nbr[0][t]]);
                found = 1;
            } else if (r == -1) limit_flag = 1;
        }
        if (!found) reps[nreps++] = u;
    }
    for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) {
        int w = nbr[v][i];
        uf_union(transinv[v][w], transinv[w][v]);
    }
    static int cid[MAXN]; for (int x = 0; x < n; x++) cid[x] = -1;
    K = 0;
    for (int i = 0; i < deg; i++) { int r = uf_find(nbr[0][i]); if (cid[r] < 0) cid[r] = K++; }
    memset(msz, 0, sizeof msz);
    for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) {
        int w = nbr[v][i];
        int c = cid[uf_find(transinv[v][w])];
        lab[v][i] = (unsigned char)c;
        if (v < w) msz[c]++;
    }
    for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) {
        int w = nbr[v][i];
        if (lab[v][i] != edge_lab(w, v)) { fprintf(stderr, "internal: asymmetric labels\n"); exit(3); }
    }
    for (int v = 0; v < n; v++) {
        int c[MAXK]; memset(c, 0, sizeof(int)*K);
        for (int i = 0; i < deg; i++) c[lab[v][i]]++;
        for (int t = 0; t < K; t++) if (c[t]*n != 2*msz[t]) { fprintf(stderr, "internal: orbit degree mismatch\n"); exit(3); }
    }
    return 0;
}

// ---------------- Hamiltonian paths
static int P[MAXN], pos[MAXN];
static int cnt[MAXK];
static void recount(void){
    memset(cnt, 0, sizeof(int)*K);
    for (int i = 0; i + 1 < n; i++) cnt[edge_lab(P[i], P[i+1])]++;
}
static int valid_path(const int *p){
    static char seen[MAXN]; memset(seen, 0, n);
    for (int i = 0; i < n; i++) { if (p[i] < 0 || p[i] >= n || seen[p[i]]) return 0; seen[p[i]] = 1; }
    for (int i = 0; i + 1 < n; i++) if (!adjacent(p[i], p[i+1])) return 0;
    return 1;
}
static void reverse_seg(int i, int j){
    while (i < j) { int t = P[i]; P[i] = P[j]; P[j] = t; pos[P[i]] = i; pos[P[j]] = j; i++; j--; }
    if (i == j) pos[P[i]] = i;
}
static const double *posa_bias = 0;   // if set, extensions prefer edge classes with larger weight
static int posa(long maxit, int attempts){
    static char in[MAXN];
    for (int attempt = 0; attempt < attempts; attempt++) {
        int len = 1; memset(in, 0, n);
        P[0] = rndint(n); pos[P[0]] = 0; in[P[0]] = 1;
        for (long it = 0; it < maxit && len < n; it++) {
            int t = P[len-1];
            int cand[MAXD], nc = 0;
            for (int i = 0; i < deg; i++) if (!in[nbr[t][i]]) cand[nc++] = nbr[t][i];
            if (nc) {
                int u = cand[rndint(nc)];
                if (posa_bias && nc > 1 && (rnd() & 7) != 0) {
                    double bv = -1e300;
                    for (int q = 0; q < nc; q++) { double v = posa_bias[edge_lab(t, cand[q])] + 1e-3 * rnd01(); if (v > bv) { bv = v; u = cand[q]; } }
                }
                P[len] = u; pos[u] = len; in[u] = 1; len++;
                continue;
            }
            if ((rnd() & 7) == 7 || len < 3) { reverse_seg(0, len-1); continue; }
            int x = nbr[t][rndint(deg)];
            int i = pos[x];
            if (i >= len-2) continue;
            reverse_seg(i+1, len-1);
        }
        if (len == n) return 1;
    }
    return 0;
}

// ---------------- LP
static int cols[MAXCOLS][MAXK]; static int ncols;
static int (*colpath)[MAXN];
static double Binv[MAXK][MAXK], xB[MAXK], ydual[MAXK];
static int basis[MAXK];
static int in_basis[MAXCOLS];

static int find_col(const int *c){
    for (int j = ncols-1; j >= 0; j--) { if (memcmp(cols[j], c, sizeof(int)*K) == 0) return j; }
    return -1;
}
static int add_col_from_path(void){
    if (find_col(cnt) >= 0) return -1;
    if (ncols >= MAXCOLS) return -1;
    memcpy(cols[ncols], cnt, sizeof(int)*K);
    memcpy(colpath[ncols], P, sizeof(int)*n);
    in_basis[ncols] = 0;
    return ncols++;
}
static void lp_init(void){
    for (int i = 0; i < K; i++) { for (int j = 0; j < K; j++) Binv[i][j] = (i == j); xB[i] = msz[i]; basis[i] = -(i+1); }
    for (int j = 0; j < ncols; j++) in_basis[j] = 0;
}
static double lp_solve(void){
    long iter = 0; int bland = 0; long degen = 0;
    for (;;) {
        for (int i = 0; i < K; i++) { double s = 0; for (int r = 0; r < K; r++) if (basis[r] < 0) s += Binv[r][i]; ydual[i] = s; }
        double obj = 0; for (int r = 0; r < K; r++) if (basis[r] < 0) obj += xB[r];
        if (obj < 1e-7) return obj;
        int ent = -1; double best = 1e-7;
        for (int j = 0; j < ncols; j++) if (!in_basis[j]) {
            double rc = 0; for (int i = 0; i < K; i++) rc += ydual[i]*cols[j][i];
            if (rc > best) { ent = j; if (bland) break; best = rc; }
        }
        if (ent < 0) return obj;
        double d[MAXK];
        for (int r = 0; r < K; r++) { double s = 0; for (int i = 0; i < K; i++) s += Binv[r][i]*cols[ent][i]; d[r] = s; }
        int lv = -1; double bestratio = 1e300;
        for (int r = 0; r < K; r++) if (d[r] > 1e-9) {
            double ratio = xB[r]/d[r];
            if (ratio < bestratio - 1e-12) { bestratio = ratio; lv = r; }
            else if (ratio < bestratio + 1e-12) {
                int a = basis[r] < 0, b0 = basis[lv] < 0;
                if (a && !b0) lv = r;
                else if (a == b0 && basis[r] < basis[lv]) lv = r;
            }
        }
        if (lv < 0) { fprintf(stderr, "internal: unbounded phase 1\n"); exit(3); }
        if (bestratio < 1e-12) { degen++; if (degen > 50) bland = 1; } else { degen = 0; }
        double piv = d[lv];
        for (int i = 0; i < K; i++) Binv[lv][i] /= piv;
        xB[lv] /= piv;
        for (int r = 0; r < K; r++) if (r != lv && fabs(d[r]) > 0) {
            double f = d[r];
            for (int i = 0; i < K; i++) Binv[r][i] -= f*Binv[lv][i];
            xB[r] -= f*xB[lv]; if (xB[r] < 0 && xB[r] > -1e-9) xB[r] = 0;
        }
        if (basis[lv] >= 0) in_basis[basis[lv]] = 0;
        basis[lv] = ent; in_basis[ent] = 1;
        if (++iter > 200000) { fprintf(stderr, "internal: simplex iteration limit\n"); return obj; }
    }
}
static int exact_check(const int *sup, int s){
    static i128 M[MAXK][MAXK+1];
    for (int i = 0; i < K; i++) { for (int j = 0; j < s; j++) M[i][j] = cols[sup[j]][i]; M[i][s] = msz[i]; }
    i128 prev = 1; int prow[MAXK]; int used[MAXK]; memset(used, 0, sizeof used);
    for (int c = 0; c < s; c++) {
        int r = -1; for (int i = 0; i < K; i++) if (!used[i] && M[i][c] != 0) { r = i; break; }
        if (r < 0) return 0;
        used[r] = 1; prow[c] = r;
        i128 piv = M[r][c];
        for (int i = 0; i < K; i++) if (i != r) {
            i128 f = M[i][c];
            for (int j = 0; j <= s; j++) {
                i128 a, b, d2;
                if (__builtin_mul_overflow(M[i][j], piv, &a)) return -1;
                if (__builtin_mul_overflow(f, M[r][j], &b)) return -1;
                if (__builtin_sub_overflow(a, b, &d2)) return -1;
                if (d2 % prev != 0) return -1;
                M[i][j] = d2 / prev;
            }
        }
        prev = piv;
    }
    for (int i = 0; i < K; i++) if (!used[i] && M[i][s] != 0) return 0;
    for (int c = 0; c < s; c++) {
        i128 num = M[prow[c]][s], den = M[prow[c]][c];
        if (den == 0) return 0;
        if ((num > 0 && den < 0) || (num < 0 && den > 0)) return 0;
    }
    return 1;
}

static double walk(const double *y, long steps, double T0, double T1, int addall, double thresh, int maxadd){
    double val = 0; for (int i = 0; i < K; i++) val += y[i]*cnt[i];
    double best = val; int added = 0;
    if (!addall && val > thresh) { if (add_col_from_path() >= 0) added++; }
    for (long s = 0; s < steps; s++) {
        double T = T0 + (T1 - T0) * (double)s / (double)steps;
        if ((rnd() & 3) == 0) reverse_seg(0, n-1);
        int t = P[n-1];
        int j = rndint(deg);
        int x = nbr[t][j];
        int i = pos[x];
        if (i >= n-2) continue;
        int la = lab[t][j], lr = edge_lab(x, P[i+1]);
        double dl = y[la] - y[lr];
        if (dl < 0) { if (T <= 0) continue; if (rnd01() >= exp(dl/T)) continue; }
        reverse_seg(i+1, n-1);
        cnt[la]++; cnt[lr]--;
        val += dl;
        if (la != lr) {
            if (addall) { if (added < maxadd && add_col_from_path() >= 0) added++; }
            else if (val > thresh && val >= best - 1e-12 && added < maxadd) { if (add_col_from_path() >= 0) added++; }
            if (val > best) best = val;
        }
    }
    return best;
}


// ---------------- constructive seeds: sequential traversal of a 2-factor formed by a set of orbits
// For an orbit set S (bitmask) whose edges form a 2-factor, look for a Hamiltonian path that runs through each
// cycle of the 2-factor in one piece (so it uses exactly #cycles-1 edges outside S). Depth-first search over
// (cycle, entry vertex); by vertex-transitivity the path may start at vertex 0.
static int seed_cyc[MAXN];          // cycle id of each vertex
static int seed_nxt[MAXN][2];       // the two S-neighbours of each vertex
static int seed_out[MAXN];          // a non-S neighbour (cubic: unique); -1 if several
static char seed_used[MAXN];        // cycle visited
static int seed_ncyc, seed_len;
static long seed_nodes;
static int seedP[MAXN];
static int seed_dfs(int x, int done){
    // enter cycle of x at x; traverse it ending at one of the two S-neighbours of x
    if (seed_nodes-- <= 0) return 0;
    int c = seed_cyc[x];
    seed_used[c] = 1;
    for (int dir = 0; dir < 2; dir++) {
        // walk from x in direction dir around the cycle
        int start = seed_len, prev = x, cur = seed_nxt[x][dir];
        seedP[seed_len++] = x;
        while (cur != x) {
            seedP[seed_len++] = cur;
            int nx = (seed_nxt[cur][0] == prev) ? seed_nxt[cur][1] : seed_nxt[cur][0];
            if (seed_nxt[cur][0] == seed_nxt[cur][1]) nx = x;   // 2-cycle safety
            prev = cur; cur = nx;
        }
        int y = prev;   // last vertex of the run
        if (done + 1 == seed_ncyc) { if (seed_len == n) return 1; }
        else {
            for (int i = 0; i < deg; i++) {
                int z = nbr[y][i];
                if (seed_cyc[z] == c || seed_used[seed_cyc[z]]) continue;
                if (seed_dfs(z, done + 1)) return 1;
            }
        }
        seed_len = start;
        if (seed_nxt[x][0] == seed_nxt[x][1]) break;
    }
    seed_used[c] = 0;
    return 0;
}
static int seed_added;
static void add_seed_path(void){
    for (int i = 0; i < n; i++) { P[i] = seedP[i]; pos[P[i]] = i; }
    if (!valid_path(P)) { fprintf(stderr, "internal: invalid seed path\n"); exit(3); }
    recount();
    if (add_col_from_path() >= 0) seed_added++;
}
// Periodic transversal: fix a short segment of a "sequential traversal" starting at vertex 0 (p cycles, chosen by a
// pattern of directions/exits), let sigma be a known automorphism with sigma(0) = entry of the (p+1)-st cycle, and
// continue the traversal by the images of the segment under sigma, sigma^2, ...  If the cycles met are pairwise
// distinct until all are used, this is a Hamiltonian path running through every cycle of the 2-factor in one piece.
// (Heuristic source of paths only: the result is validated like every other path.)
static int seed_periodic_try(const int *ex0, const int *ey0, int p, int xnext){
    static int ex[16], ey[16];
    const int *sig = trans[xnext];
    for (int i = 0; i < p; i++) { ex[i] = ex0[i]; ey[i] = ey0[i]; }
    memset(seed_used, 0, seed_ncyc);
    seed_len = 0; int count = 0;
    for (;;) {
        for (int i = 0; i < p; i++) {
            int x = ex[i], y = ey[i], c = seed_cyc[x];
            if (seed_used[c]) return 0;
            seed_used[c] = 1;
            if (seed_nxt[x][0] != y && seed_nxt[x][1] != y) return 0;
            int prev = x, cur = (seed_nxt[x][0] == y) ? seed_nxt[x][1] : seed_nxt[x][0];
            if (seed_len >= n) return 0;
            seedP[seed_len++] = x;
            while (cur != x) {
                if (seed_len >= n) return 0;
                seedP[seed_len++] = cur;
                if (cur == y) break;
                int nx = (seed_nxt[cur][0] == prev) ? seed_nxt[cur][1] : seed_nxt[cur][0];
                prev = cur; cur = nx;
            }
            if (seedP[seed_len-1] != y) return 0;
            if (++count == seed_ncyc) return seed_len == n;
        }
        for (int i = 0; i < p; i++) { ex[i] = sig[ex[i]]; ey[i] = sig[ey[i]]; }
    }
}
static int seed_per_ex[16], seed_per_ey[16];
static long seed_per_budget;
static int seed_periodic_rec(int depth, int x, int maxp){
    // x = entry of cycle number depth of the segment
    if (depth >= 1) {
        if (seed_per_budget-- <= 0) return 0;
        if (seed_periodic_try(seed_per_ex, seed_per_ey, depth, x)) return 1;
    }
    if (depth == maxp) return 0;
    for (int j = 0; j < depth; j++) if (seed_cyc[seed_per_ex[j]] == seed_cyc[x]) return 0;
    for (int dir = 0; dir < 2; dir++) {
        int y = seed_nxt[x][dir];
        seed_per_ex[depth] = x; seed_per_ey[depth] = y;
        for (int i = 0; i < deg; i++) {
            int z = nbr[y][i];
            if (seed_cyc[z] == seed_cyc[x]) continue;
            if (seed_periodic_rec(depth + 1, z, maxp)) return 1;
        }
    }
    return 0;
}
static int seed_periodic(void){
    for (int maxp = 1; maxp <= 8; maxp++) {
        seed_per_budget = 600;
        if (seed_periodic_rec(0, 0, maxp)) return 1;
    }
    return 0;
}
static void seeds(void){
    for (int S = 1; S < (1 << K) - 1; S++) {
        int dS = 0; for (int i = 0; i < deg; i++) if (S >> lab[0][i] & 1) dS++;
        if (dS != 2) continue;
        for (int v = 0; v < n; v++) {
            int c = 0; seed_out[v] = -1;
            for (int i = 0; i < deg; i++) { if (S >> lab[v][i] & 1) seed_nxt[v][c++] = nbr[v][i]; else seed_out[v] = nbr[v][i]; }
            seed_cyc[v] = -1;
        }
        seed_ncyc = 0;
        for (int v = 0; v < n; v++) if (seed_cyc[v] < 0) {
            int prev = -1, cur = v;
            while (seed_cyc[cur] < 0) { seed_cyc[cur] = seed_ncyc; int nx = (seed_nxt[cur][0] == prev) ? seed_nxt[cur][1] : seed_nxt[cur][0]; prev = cur; cur = nx; }
            seed_ncyc++;
        }
        memset(seed_used, 0, seed_ncyc);
        seed_len = 0; seed_nodes = 200000;
        if (seed_dfs(0, 0)) {
            add_seed_path();
            // for a single cycle also add the path missing the other kind of edge (shift start by one)
            if (seed_ncyc == 1) { int t0 = seedP[0]; for (int i = 0; i + 1 < n; i++) seedP[i] = seedP[i+1]; seedP[n-1] = t0; add_seed_path(); }
        } else if (seed_ncyc > 1 && seed_periodic()) {
            if (valid_path(seedP)) add_seed_path();
        }
    }
}

// ---------------- structural seed for cubic graphs with a 2-factor of 4-cycles ("blobs") that is a union of orbits
// Collapse each pair of opposite blob vertices: H is a cubic graph on n/2 "pairs" (slot 0 = twin edge = the blob,
// slots 1,2 = the two matching edges of the pair).  Perfect matchings Y of H correspond to configurations:
// twin edge in Y  <=> blob crossed twice (uses all 4 matching edges);  otherwise the blob is run through once and the
// two Y-edges are its two unused matching edges.  A Hamiltonian cycle exists for Y iff H minus the non-twin Y-edges
// is connected (then switching at twice-crossed blobs merges the cycles).  We anneal over Y to minimise the number
// of twin edges, build the Hamiltonian cycle explicitly and offer it as a column.  (Only a heuristic source of
// paths: every path is validated like any other.)
static int c4_opp[MAXN], c4_mate[MAXN], c4_pid[MAXN], c4_a[MAXN][2];
static int hN, hrep[MAXN][2], hnb[MAXN][3], hsl[MAXN][3], ym[MAXN], ybest[MAXN];
static int c4_ufp[MAXN];
static int c4_find(int x){ while (c4_ufp[x] != x) { c4_ufp[x] = c4_ufp[c4_ufp[x]]; x = c4_ufp[x]; } return x; }
static int c4_comp(void){
    for (int i = 0; i < hN; i++) c4_ufp[i] = i;
    int c = hN;
    for (int A = 0; A < hN; A++) for (int sl = 0; sl < 3; sl++) {
        if (sl != 0 && ym[A] == sl) continue;
        int a = c4_find(A), b = c4_find(hnb[A][sl]);
        if (a != b) { c4_ufp[a] = b; c--; }
    }
    return c;
}
static int c4_detect(int S){
    for (int v = 0; v < n; v++) {
        int c = 0; c4_mate[v] = -1;
        for (int i = 0; i < deg; i++) { if (S >> lab[v][i] & 1) { if (c < 2) c4_a[v][c] = nbr[v][i]; c++; } else c4_mate[v] = nbr[v][i]; }
        if (c != 2 || c4_mate[v] < 0) return 0;
    }
    for (int v = 0; v < n; v++) {
        int a = c4_a[v][0], b = c4_a[v][1];
        int xa = (c4_a[a][0] == v) ? c4_a[a][1] : c4_a[a][0];
        int xb = (c4_a[b][0] == v) ? c4_a[b][1] : c4_a[b][0];
        if (xa != xb || xa == v || xa == a || xa == b) return 0;
        c4_opp[v] = xa;
    }
    hN = 0;
    for (int v = 0; v < n; v++) c4_pid[v] = -1;
    for (int v = 0; v < n; v++) if (c4_pid[v] < 0) { c4_pid[v] = c4_pid[c4_opp[v]] = hN; hrep[hN][0] = v; hrep[hN][1] = c4_opp[v]; hN++; }
    for (int A = 0; A < hN; A++) {
        int v = hrep[A][0];
        hnb[A][0] = c4_pid[c4_a[v][0]]; hsl[A][0] = 0;
        for (int r = 0; r < 2; r++) {
            int w = c4_mate[hrep[A][r]]; int B = c4_pid[w];
            if (B == A || B == hnb[A][0]) return 0;      // degenerate (matching edge inside a blob)
            hnb[A][1+r] = B; hsl[A][1+r] = (hrep[B][0] == w) ? 1 : 2;
        }
    }
    return 1;
}
static int c4_padj[MAXN][2];
static int c4_S_cur = 0;           // orbit mask of the blob structure currently loaded in hN/hrep/hnb (0 = none)
static double c4_y[MAXK];          // direction used by the annealer
// objective contribution of the blob containing pair A (given the matching ym)
static double c4_blob_val(int A){
    int B = hnb[A][0];
    int a0 = hrep[A][0], b0 = hrep[B][0];
    int cl0 = edge_lab(a0, b0), cl1 = edge_lab(a0, hrep[B][1]);   // the two classes of blob edges (may coincide)
    double yM = c4_y[edge_lab(a0, c4_mate[a0])];
    if (ym[A] == 0) { double m = c4_y[cl0] > c4_y[cl1] ? c4_y[cl0] : c4_y[cl1]; return 2.0*m + 2.0*yM; }
    int a = hrep[A][ym[A]-1], b = hrep[B][ym[B]-1];
    int c1 = edge_lab(a, b); int c2 = (c1 == cl0) ? cl1 : cl0;
    return c4_y[c1] + 2.0*c4_y[c2] + yM;
}
static int c4_single_cycle(void){
    int len = 0, prev = -1, cur = 0;
    do { len++; int nx = (c4_padj[cur][0] == prev) ? c4_padj[cur][1] : c4_padj[cur][0]; prev = cur; cur = nx; } while (cur != 0 && len <= n);
    return len == n;
}
static int c4_build_path(const double *y, int cutM){
    // build the 2-factor from ybest, merge cycles by switching at twice-crossed blobs, improve options greedily
    // for direction y, cut into a path (at a matching edge if cutM, else at a blob edge)
    static char isT[MAXN]; static int opt[MAXN];
    for (int A = 0; A < hN; A++) {
        int B = hnb[A][0]; if (A > B) continue;
        int a0 = hrep[A][0], a1 = hrep[A][1], b0 = hrep[B][0], b1 = hrep[B][1];
        if (ybest[A] == 0) {
            if (ybest[B] != 0) return 0;
            isT[A] = 1; opt[A] = 0;
            c4_padj[a0][0] = b0; c4_padj[a0][1] = c4_mate[a0]; c4_padj[b0][0] = a0; c4_padj[b0][1] = c4_mate[b0];
            c4_padj[a1][0] = b1; c4_padj[a1][1] = c4_mate[a1]; c4_padj[b1][0] = a1; c4_padj[b1][1] = c4_mate[b1];
        } else {
            if (ybest[B] == 0) return 0;
            isT[A] = 0;
            int a = hrep[A][ybest[A]-1], ao = hrep[A][2-ybest[A]], b = hrep[B][ybest[B]-1], bo = hrep[B][2-ybest[B]];
            c4_padj[ao][0] = b; c4_padj[ao][1] = c4_mate[ao];
            c4_padj[b][0] = ao; c4_padj[b][1] = a;
            c4_padj[a][0] = b; c4_padj[a][1] = bo;
            c4_padj[bo][0] = a; c4_padj[bo][1] = c4_mate[bo];
        }
    }
    static int cid[MAXN];
    for (int iter = 0; iter < n; iter++) {
        for (int v = 0; v < n; v++) cid[v] = -1;
        int nc = 0;
        for (int s0 = 0; s0 < n; s0++) if (cid[s0] < 0) {
            int prev = -1, cur = s0, guard = 0;
            do { cid[cur] = nc; int nx = (c4_padj[cur][0] == prev) ? c4_padj[cur][1] : c4_padj[cur][0];
                 prev = cur; cur = nx; if (++guard > n + 2) return 0; } while (cur != s0);
            nc++;
        }
        if (nc == 1) break;
        int sw = 0;
        for (int A = 0; A < hN && !sw; A++) {
            int B = hnb[A][0]; if (A > B || !isT[A]) continue;
            int a0 = hrep[A][0], a1 = hrep[A][1], b0 = hrep[B][0], b1 = hrep[B][1];
            if (cid[a0] != cid[a1]) {
                if (opt[A] == 0) { c4_padj[a0][0] = b1; c4_padj[b1][0] = a0; c4_padj[a1][0] = b0; c4_padj[b0][0] = a1; opt[A] = 1; }
                else { c4_padj[a0][0] = b0; c4_padj[b0][0] = a0; c4_padj[a1][0] = b1; c4_padj[b1][0] = a1; opt[A] = 0; }
                sw = 1;
            }
        }
        if (!sw) return 0;
    }
    // greedy improvement of the options of twice-crossed blobs for direction y (keeping a single cycle)
    for (int A = 0; A < hN; A++) {
        int B = hnb[A][0]; if (A > B || !isT[A]) continue;
        int a0 = hrep[A][0], a1 = hrep[A][1], b0 = hrep[B][0], b1 = hrep[B][1];
        double ycur = y[edge_lab(a0, opt[A] == 0 ? b0 : b1)], yalt = y[edge_lab(a0, opt[A] == 0 ? b1 : b0)];
        if (yalt <= ycur + 1e-12) continue;
        if (opt[A] == 0) { c4_padj[a0][0] = b1; c4_padj[b1][0] = a0; c4_padj[a1][0] = b0; c4_padj[b0][0] = a1; opt[A] = 1; }
        else { c4_padj[a0][0] = b0; c4_padj[b0][0] = a0; c4_padj[a1][0] = b1; c4_padj[b1][0] = a1; opt[A] = 0; }
        if (!c4_single_cycle()) {   // undo
            if (opt[A] == 0) { c4_padj[a0][0] = b1; c4_padj[b1][0] = a0; c4_padj[a1][0] = b0; c4_padj[b0][0] = a1; opt[A] = 1; }
            else { c4_padj[a0][0] = b0; c4_padj[b0][0] = a0; c4_padj[a1][0] = b1; c4_padj[b1][0] = a1; opt[A] = 0; }
        }
    }
    static int cyc[MAXN]; int len = 0, prev = -1, cur = 0;
    do { cyc[len++] = cur; int nx = (c4_padj[cur][0] == prev) ? c4_padj[cur][1] : c4_padj[cur][0]; prev = cur; cur = nx; } while (cur != 0 && len <= n);
    if (len != n) return 0;
    int cut = -1;
    for (int i = 0; i < n; i++) { int isM = (cyc[(i+1) % n] == c4_mate[cyc[i]]); if (isM == cutM) { cut = i; break; } }
    if (cut < 0) return 0;
    for (int i = 0; i < n; i++) { P[i] = cyc[(cut + 1 + i) % n]; pos[P[i]] = i; }
    if (!valid_path(P)) { fprintf(stderr, "internal: invalid c4 path\n"); exit(3); }
    recount();
    return add_col_from_path() >= 0;
}
static int c4_twins_found = -1;
static int c4_fresh_count = 0;
// anneal over perfect matchings of H for direction y (on count vectors); returns number of columns added
static int c4_anneal(int S, const double *y, long steps, int fresh){
    if (c4_S_cur != S) { if (!c4_detect(S)) { c4_S_cur = 0; return 0; } c4_S_cur = S; fresh = 1; }
    for (int i = 0; i < K; i++) c4_y[i] = y[i];
    if (fresh) {
        for (int A = 0; A < hN; A++) ym[A] = 0;
        // if every straight circuit is even, start from a random "all blobs run through once" configuration:
        // each circuit is matched along itself (two choices per circuit)
        static char seen[MAXN]; static int circ[MAXN], cslot[MAXN]; int allEven = 1;
        memset(seen, 0, hN);
        for (int A = 0; A < hN && allEven; A++) if (!seen[A]) {
            int L = 0, cur = A, inslot = -1;
            // walk the circuit using slots 1,2; record the slot used to leave each vertex
            do {
                seen[cur] = 1; circ[L] = cur;
                int outslot = (inslot == 1) ? 2 : 1;      // leave by the other circuit slot (first step: slot 1)
                if (inslot < 0) outslot = 1;
                cslot[L] = outslot; L++;
                int nx = hnb[cur][outslot]; inslot = hsl[cur][outslot]; cur = nx;
            } while (cur != A && L <= hN);
            if (cur != A || (L & 1)) { allEven = 0; break; }
            int off = (int)(rnd() & 1);
            for (int i = 0; i < L; i += 2) {
                int a = circ[(i + off) % L], b = circ[(i + off + 1) % L];
                int sl = cslot[(i + off) % L];
                if (hnb[a][sl] != b) { allEven = 0; break; }
                ym[a] = sl; ym[b] = hsl[a][sl];
            }
        }
        if (!allEven || (c4_fresh_count++ & 1)) for (int A = 0; A < hN; A++) ym[A] = 0;
    }
    int twins = 0; for (int A = 0; A < hN; A++) if (ym[A] == 0) twins++;
    twins /= 2;
    int comp = c4_comp();
    double val = 0; for (int A = 0; A < hN; A++) if (A < hnb[A][0]) val += c4_blob_val(A);
    double LAM = 1.3;
    double bestval = -1e300; int besttw = -1;
    if (comp == 1) { bestval = val; besttw = twins; memcpy(ybest, ym, sizeof(int)*hN); }
    double E = -val + LAM * (comp - 1);
    static int cA[80], cW[80], sW[80], sArr[80], oldA[80], oldW[80]; static int cst[MAXN], wst[MAXN], cpos[MAXN], bst[MAXN]; static int stp = 0;
    static int blist[170];
    for (long s = 0; s < steps; s++) {
        double T = 0.9 + (0.03 - 0.9) * (double)s / (double)steps;
        stp++; int len = 0, cur = rndint(hN), start = -1, arr = -1;
        for (;;) {
            if (cst[cur] == stp) { start = cpos[cur]; break; }
            if (wst[cur] == stp || len >= 70) { start = -1; break; }
            cst[cur] = stp; cpos[cur] = len;
            int w = hnb[cur][ym[cur]];
            if (cst[w] == stp || wst[w] == stp) { start = -1; break; }
            wst[w] = stp;
            int sl; do { sl = rndint(3); } while (sl == ym[w]);
            cA[len] = cur; cW[len] = w; sW[len] = sl; sArr[len] = arr; len++;
            arr = hsl[w][sl]; cur = hnb[w][sl];
        }
        if (start < 0) continue;
        if (len - start < 1) continue;
        sArr[start] = arr;
        // affected blobs
        int nb = 0; double before = 0, after = 0;
        for (int i = start; i < len; i++) for (int t2 = 0; t2 < 2; t2++) {
            int A = t2 ? cW[i] : cA[i]; int bid = A < hnb[A][0] ? A : hnb[A][0];
            if (bst[bid] != stp) { bst[bid] = stp; blist[nb++] = bid; }
        }
        for (int i = 0; i < nb; i++) before += c4_blob_val(blist[i]);
        int dtw = 0;
        for (int i = start; i < len; i++) { oldA[i] = ym[cA[i]]; oldW[i] = ym[cW[i]]; if (ym[cA[i]] == 0) dtw--; }
        for (int i = start; i < len; i++) { ym[cA[i]] = sArr[i]; ym[cW[i]] = sW[i]; if (sW[i] == 0) dtw++; }
        for (int i = 0; i < nb; i++) after += c4_blob_val(blist[i]);
        int ncomp = c4_comp();
        double val2 = val - before + after;
        double E2 = -val2 + LAM * (ncomp - 1);
        if (E2 <= E || rnd01() < exp((E - E2) / T)) {
            E = E2; twins += dtw; comp = ncomp; val = val2;
            if (comp == 1 && val > bestval + 1e-9) { bestval = val; besttw = twins; memcpy(ybest, ym, sizeof(int)*hN); }
        } else {
            for (int i = start; i < len; i++) { ym[cA[i]] = oldA[i]; ym[cW[i]] = oldW[i]; }
        }
    }
    int added = 0;
    if (besttw >= 0) {
        int yMi = edge_lab(hrep[0][0], c4_mate[hrep[0][0]]);
        // cut at a matching edge when that class is disfavoured, else at a blob edge; offer both when cheap
        if (c4_build_path(y, 1)) added++;
        if (c4_build_path(y, 0)) added++;
        (void)yMi;
        if (c4_twins_found < 0 || besttw < c4_twins_found) c4_twins_found = besttw;
        if (verbose) fprintf(stderr, "c4: S=%d hN=%d besttw=%d val=%.2f added=%d\n", S, hN, besttw, bestval, added);
    }
    return added;
}
// Small sets of twice-crossed blobs: when every straight circuit is even, choose k random twin edges (k = 0..4), which
// forces the matching on every circuit that carries one of their ends (gaps between ends must be even), and keep the
// configurations for which H minus the non-twin matching edges is connected.  This finds the Hamiltonian cycles with
// very few twice-crossed blobs that the local annealing moves miss on graphs with long straight circuits.
static int c4_tp_done = 0;
static int tw_cvert[MAXN], tw_cslot[MAXN], tw_cstart[MAXN], tw_clen[MAXN], tw_cidx[MAXN], tw_cpos[MAXN], tw_nc;
static char tw_isT[MAXN];
static int tw_added, tw_succ; static long tw_budget;
static const double *tw_y;
// build the matching forced by the twin set tw_isT (circuits without twin ends get a random alternation);
// returns 1 and offers the Hamiltonian cycle if the configuration is valid and connected
static int tw_eval(void){
    for (int c = 0; c < tw_nc; c++) {
        int st = tw_cstart[c], L = tw_clen[c], first = -1;
        for (int i = 0; i < L; i++) if (tw_isT[tw_cvert[st + i]]) { first = i; break; }
        if (first < 0) {
            if (L & 1) return 0;
            int off = (int)(rnd() & 1);
            for (int i = 0; i < L; i += 2) {
                int a = tw_cvert[st + (i + off) % L], b = tw_cvert[st + (i + off + 1) % L], sl = tw_cslot[st + (i + off) % L];
                if (hnb[a][sl] != b) return 0;
                ym[a] = sl; ym[b] = hsl[a][sl];
            }
            continue;
        }
        int i = first;
        for (int cntv = 0; cntv < L; ) {
            ym[tw_cvert[st + i % L]] = 0;
            int j = i + 1; while (!tw_isT[tw_cvert[st + j % L]]) j++;
            int gap = j - i - 1;
            if (gap & 1) return 0;
            for (int q = i + 1; q + 1 < j; q += 2) {
                int a = tw_cvert[st + q % L], b = tw_cvert[st + (q + 1) % L], sl = tw_cslot[st + q % L];
                if (hnb[a][sl] != b) return 0;
                ym[a] = sl; ym[b] = hsl[a][sl];
            }
            cntv += j - i; i = j;
        }
    }
    for (int A = 0; A < hN; A++) if (tw_isT[A]) ym[A] = 0;
    if (c4_comp() != 1) return 0;
    memcpy(ybest, ym, sizeof(int)*hN);
    int got = 0;
    if (c4_build_path(tw_y, 1)) { tw_added++; got = 1; }
    if (c4_build_path(tw_y, 0)) { tw_added++; got = 1; }
    if (got) { tw_succ++; int tw = 0; for (int A = 0; A < hN; A++) if (ym[A] == 0) tw++; tw /= 2; if (c4_twins_found < 0 || tw < c4_twins_found) c4_twins_found = tw; }
    return got;
}
// closed walks in the "circuit graph": twins t_1..t_m with t_i joining circuit Z_i to Z_{i+1} (Z_{m+1} = Z_1) such that
// the two twin ends on every Z_i are at odd distance (then all gaps are even)
static int tw_used_c[MAXN]; static int tw_A0;
static int tw_dfs(int Bprev, int depth, int maxdepth){
    // Bprev: twin end just placed on the current circuit; choose the next twin end A on the same circuit at odd distance
    if (tw_budget-- <= 0) return 0;
    int c = tw_cidx[Bprev], st = tw_cstart[c], L = tw_clen[c], q = tw_cpos[Bprev];
    int nodd = L / 2, r0 = rndint(nodd > 0 ? nodd : 1);
    for (int k = 0; k < nodd; k++) {
        int d = 2 * ((k + r0) % nodd) + 1;          // odd distance
        int A = tw_cvert[st + (q + d) % L];
        if (tw_isT[A]) continue;
        int B = hnb[A][0];
        if (tw_isT[B]) continue;
        int cb = tw_cidx[B];
        if (cb == tw_cidx[tw_A0]) {
            if (cb == c) continue;
            int dd = tw_cpos[B] - tw_cpos[tw_A0]; if (dd < 0) dd = -dd;
            if (!(dd & 1)) continue;
            tw_isT[A] = tw_isT[B] = 1;
            int got = tw_eval();
            tw_isT[A] = tw_isT[B] = 0;
            if (got) return 1;
            continue;
        }
        if (depth + 1 >= maxdepth || tw_used_c[cb] || cb == c) continue;
        tw_isT[A] = tw_isT[B] = 1; tw_used_c[cb] = 1;
        int got = tw_dfs(B, depth + 1, maxdepth);
        tw_isT[A] = tw_isT[B] = 0; tw_used_c[cb] = 0;
        if (got) return 1;
    }
    return 0;
}
static int c4_twinset_seed(int S, const double *y){
    if (c4_S_cur != S) { if (!c4_detect(S)) { c4_S_cur = 0; return 0; } c4_S_cur = S; }
    static char seen[MAXN];
    memset(seen, 0, hN); tw_nc = 0; int tot = 0, allEven = 1;
    for (int A = 0; A < hN; A++) if (!seen[A]) {
        int L = 0, cur = A, inslot = -1;
        do {
            if (seen[cur]) return 0;
            seen[cur] = 1; tw_cvert[tot + L] = cur; tw_cidx[cur] = tw_nc; tw_cpos[cur] = L;
            int outslot = (inslot == 1) ? 2 : 1;
            tw_cslot[tot + L] = outslot; L++;
            int nx = hnb[cur][outslot]; inslot = hsl[cur][outslot]; cur = nx;
        } while (cur != A && L <= hN);
        if (cur != A) return 0;
        if (L & 1) allEven = 0;
        tw_cstart[tw_nc] = tot; tw_clen[tw_nc] = L; tot += L; tw_nc++;
    }
    if (tot != hN || !allEven) return 0;
    tw_added = 0; tw_succ = 0; tw_y = y;
    memset(tw_isT, 0, hN);
    for (int trial = 0; trial < 6 && tw_succ < 1; trial++) tw_eval();          // no twice-crossed blob at all
    for (int c = 0; c < tw_nc; c++) tw_used_c[c] = 0;
    for (int maxdepth = 1; maxdepth <= 6 && tw_succ < 3; maxdepth++) {
        for (int trial = 0; trial < 12 && tw_succ < 3; trial++) {
            int A0 = rndint(hN), B0 = hnb[A0][0];
            tw_A0 = A0; tw_isT[A0] = tw_isT[B0] = 1;
            if (tw_cidx[A0] == tw_cidx[B0]) {
                int dd = tw_cpos[A0] - tw_cpos[B0]; if (dd < 0) dd = -dd;
                if (dd & 1) tw_eval();
            } else if (maxdepth >= 2) {
                tw_used_c[tw_cidx[A0]] = 1; tw_used_c[tw_cidx[B0]] = 1;
                tw_budget = 4000;
                tw_dfs(B0, 1, maxdepth);
                tw_used_c[tw_cidx[A0]] = 0; tw_used_c[tw_cidx[B0]] = 0;
            }
            tw_isT[A0] = tw_isT[B0] = 0;
        }
    }
    if (verbose) fprintf(stderr, "c4 twin cycles: S=%d hN=%d circuits=%d successes=%d added=%d\n", S, hN, tw_nc, tw_succ, tw_added);
    return tw_added;
}
// ---------------- structured seeds for cubic graphs whose three edge classes are perfect matchings (K = 3)
// A Hamiltonian cycle is the complement of a perfect matching N.  Start from N = class z (the complement is the
// 2-factor of (x,y)-cycles) and switch N along whole (x,z)- or (y,z)-cycles (N takes the x- resp. y-edges there);
// switched cycles must be vertex-disjoint.  Greedily accept switches that reduce the number of cycles of the
// complement, with a random order biased towards one of the two types.  For flag graphs of maps this produces the
// "face cycles + bands" Hamiltonian cycles that local moves do not find.  (Heuristic source of paths only.)
static int pm3_nb[MAXN][3], pm3_N[MAXN];
static int pm3_done = 0;
static int pm3_id[MAXN], pm3_id2[MAXN];
static int pm3_count(int *id){
    for (int v = 0; v < n; v++) id[v] = -1;
    int c = 0;
    for (int s0 = 0; s0 < n; s0++) if (id[s0] < 0) {
        int prev = -1, cur = s0;
        for (;;) {
            id[cur] = c;
            int a = pm3_nb[cur][(pm3_N[cur] + 1) % 3], b = pm3_nb[cur][(pm3_N[cur] + 2) % 3];
            int nx = (a == prev) ? b : a;
            if (a == b) nx = a;
            prev = cur; cur = nx;
            if (cur == s0) break;
        }
        c++;
    }
    return c;
}
static int pm3_seed(void){
    if (deg != 3 || K != 3) return 0;
    for (int v = 0; v < n; v++) {
        int seenm = 0;
        for (int i = 0; i < 3; i++) { pm3_nb[v][lab[v][i]] = nbr[v][i]; seenm |= 1 << lab[v][i]; }
        if (seenm != 7) return 0;
    }
    static int cyc_of[2][MAXN]; static int cstart[2][MAXN+1]; static int cvert[2][MAXN];
    static int order[2*MAXN]; static double key[2*MAXN]; static int dstamp[MAXN]; static int dst = 0;
    int added = 0;
    for (int z = 0; z < 3; z++) {
        int xs[2] = { (z + 1) % 3, (z + 2) % 3 };
        int ncy[2];
        for (int t = 0; t < 2; t++) {
            int x = xs[t]; ncy[t] = 0; int tot = 0;
            for (int v = 0; v < n; v++) cyc_of[t][v] = -1;
            for (int v = 0; v < n; v++) if (cyc_of[t][v] < 0) {
                cstart[t][ncy[t]] = tot;
                int cur = v, cl = x;
                while (cyc_of[t][cur] < 0) { cyc_of[t][cur] = ncy[t]; cvert[t][tot++] = cur; cur = pm3_nb[cur][cl]; cl = (cl == x) ? z : x; }
                ncy[t]++;
            }
            cstart[t][ncy[t]] = tot;
        }
        static const double biases[5] = { -4.0, -0.4, 0.0, 0.4, 4.0 };
        for (int bi = 0; bi < 5; bi++) for (int rep = 0; rep < 3; rep++) {
            int eff = (rep < 2);        // require fully efficient merges (no dead cycles) in two of three runs
            for (int v = 0; v < n; v++) pm3_N[v] = z;
            int cur = pm3_count(pm3_id);
            int nc = 0;
            for (int t = 0; t < 2; t++) for (int c = 0; c < ncy[t]; c++) { order[nc] = t * MAXN + c; key[nc] = rnd01() + (t ? biases[bi] : 0.0); nc++; }
            for (int i = 1; i < nc; i++) { int o = order[i]; double k = key[i]; int j = i - 1; while (j >= 0 && key[j] > k) { key[j+1] = key[j]; order[j+1] = order[j]; j--; } key[j+1] = k; order[j+1] = o; }
            for (int pass = 0; pass < 6 && cur > 1; pass++) {
                int changed = 0;
                for (int i = 0; i < nc && cur > 1; i++) {
                    int t = order[i] / MAXN, c = order[i] % MAXN, x = xs[t];
                    int okc = 1, d = 0; dst++;
                    for (int q = cstart[t][c]; q < cstart[t][c+1]; q++) {
                        int v = cvert[t][q];
                        if (pm3_N[v] != z) { okc = 0; break; }
                        if (dstamp[pm3_id[v]] != dst) { dstamp[pm3_id[v]] = dst; d++; }
                    }
                    if (!okc || d < 2) continue;
                    for (int q = cstart[t][c]; q < cstart[t][c+1]; q++) pm3_N[cvert[t][q]] = x;
                    int c2 = pm3_count(pm3_id2);
                    if (eff ? (c2 == cur - (d - 1)) : (c2 < cur)) { cur = c2; changed = 1; memcpy(pm3_id, pm3_id2, sizeof(int)*n); }
                    else { for (int q = cstart[t][c]; q < cstart[t][c+1]; q++) pm3_N[cvert[t][q]] = z; }
                }
                if (!changed) break;
            }
            if (cur != 1) continue;
            static int cyc[MAXN]; int len = 0, prev = -1, cu = 0;
            do {
                cyc[len++] = cu;
                int a = pm3_nb[cu][(pm3_N[cu] + 1) % 3], b = pm3_nb[cu][(pm3_N[cu] + 2) % 3];
                int nx = (a == prev) ? b : a; prev = cu; cu = nx;
            } while (cu != 0 && len < n);
            if (len != n || cu != 0) continue;
            for (int cl = 0; cl < 3; cl++) {
                int cut = -1;
                for (int i = 0; i < n; i++) if (edge_lab(cyc[i], cyc[(i+1) % n]) == cl) { cut = i; break; }
                if (cut < 0) continue;
                for (int i = 0; i < n; i++) seedP[i] = cyc[(cut + 1 + i) % n];
                if (valid_path(seedP)) { int before = ncols; add_seed_path(); if (ncols > before) { added++; if (verbose) fprintf(stderr, "pm3 col z=%d bias=%d eff=%d (%d,%d,%d)\n", z, bi, eff, cols[ncols-1][0], cols[ncols-1][1], cols[ncols-1][2]); } }
            }
        }
    }
    if (verbose) fprintf(stderr, "pm3 seeds: added=%d\n", added);
    return added;
}
static int c4_masks[8], c4_nmasks = 0;
static void c4_seed(void){
    c4_twins_found = -1; c4_nmasks = 0; c4_S_cur = 0;
    if (deg != 3) return;
    for (int S = 1; S < (1 << K) - 1; S++) {
        int dS = 0; for (int i = 0; i < deg; i++) if (S >> lab[0][i] & 1) dS++;
        if (dS != 2) continue;
        if (!c4_detect(S)) continue;
        c4_S_cur = S;
        if (c4_nmasks < 8) c4_masks[c4_nmasks++] = S;
        // (the annealer is only called from the pricing loop, when the rotation walk has failed once)
    }
    c4_fresh_count = 0; c4_tp_done = 0; pm3_done = 0;
    c4_S_cur = 0;   // force a fresh start (re-detection and all-twin matching) at the first annealing call
    if (0) {
    }
}

static int effort = 1;
static int use_seeds = 1;
static const char *extra_path_file = 0; static int extra_added = 0;
static int use_c4 = 1;
static int dump = 0;
static int certmode = 0;
static int certsup[MAXK], certn = 0;
static int explore = 0;
static double slack[2*MAXK];
static void explore_dirs(void){
    long m = 0; for (int i = 0; i < K; i++) m += msz[i];
    for (int d = 0; d < 2*K; d++) {
        double w[MAXK]; for (int i = 0; i < K; i++) w[i] = 0; w[d/2] = (d & 1) ? -1.0 : 1.0;
        double best = -1e300;
        for (int rep = 0; rep < 3*explore; rep++) {
            if (rep > 0) { if (posa(3000L*n, 20)) recount(); }
            double b = walk(w, 3000L*n, 0.4, 0.0, 0, 1e300, 0);
            if (b > best) best = b;
            b = walk(w, 1500L*n, 0.15, 0.0, 0, 1e300, 0);
            if (b > best) best = b;
        }
        double fairv = (double)(n-1) * (double)msz[d/2] / (double)m * ((d & 1) ? -1.0 : 1.0);
        slack[d] = best - fairv;
    }
}
static int process(double *yout, int *ncolsout){
    ncols = 0;
    if (!posa(3000L*n, 20)) { if (!posa(100000L*n, 20)) return -1; }
    if (!valid_path(P)) { fprintf(stderr, "internal: invalid path\n"); exit(3); }
    recount();
    add_col_from_path();
    if (K == 1) return 2;
    seed_added = 0;
    static int posaP[MAXN]; memcpy(posaP, P, sizeof(int)*n);
    if (use_seeds) seeds();
    if (extra_path_file) {
        // extra Hamiltonian paths supplied by the user (one per line, n vertex indices); each is validated here and,
        // if it ends up in the certificate, validated again by the final exact check
        FILE *f = fopen(extra_path_file, "r");
        if (f) {
            for (;;) {
                int okr = 1;
                for (int i = 0; i < n; i++) if (fscanf(f, "%d", &seedP[i]) != 1) { okr = 0; break; }
                if (!okr) break;
                if (!valid_path(seedP)) { fprintf(stderr, "extra path rejected (not a Hamiltonian path)\n"); continue; }
                add_seed_path(); extra_added++;
            }
            fclose(f);
        }
    }
    // continue the random walk from the (typical) rotation-extension path, not from the extreme seed path
    memcpy(P, posaP, sizeof(int)*n); for (int i2 = 0; i2 < n; i2++) pos[P[i2]] = i2; recount();
    if (use_c4) c4_seed();
    double y0[MAXK]; for (int i = 0; i < K; i++) y0[i] = 0;
    walk(y0, 200L*n, 1.0, 1.0, 1, 0, 30);
    lp_init();
    for (int round = 0; round < 100000; round++) {
        double obj = lp_solve();
        if (obj < 1e-7) {
            int sup[MAXK], s = 0;
            for (int r = 0; r < K; r++) if (basis[r] >= 0 && xB[r] > 1e-9) sup[s++] = basis[r];
            for (int j = 0; j < s; j++) {
                if (!valid_path(colpath[sup[j]])) { fprintf(stderr, "internal: invalid stored path\n"); exit(3); }
                int c[MAXK]; memset(c, 0, sizeof(int)*K);
                for (int i = 0; i + 1 < n; i++) c[edge_lab(colpath[sup[j]][i], colpath[sup[j]][i+1])]++;
                if (memcmp(c, cols[sup[j]], sizeof(int)*K) != 0) { fprintf(stderr, "internal: count mismatch\n"); exit(3); }
            }
            int e = exact_check(sup, s);
            *ncolsout = ncols;
            certn = s; for (int j = 0; j < s; j++) certsup[j] = sup[j];
            if (verbose) { fprintf(stderr, "support:"); for (int j = 0; j < s; j++) { fprintf(stderr, " ("); for (int i = 0; i < K; i++) fprintf(stderr, "%d%s", cols[sup[j]][i], i+1 < K ? "," : ")"); fprintf(stderr, "x%.4f", xB[0]); } fprintf(stderr, "\n"); }
            if (e == 1) return 1;
            return -2;
        }
        double y[MAXK]; double mx = -1e300, mn = 1e300;
        for (int i = 0; i < K; i++) { if (ydual[i] > mx) mx = ydual[i]; if (ydual[i] < mn) mn = ydual[i]; }
        double sc = (mx - mn > 1e-12) ? 1.0/(mx - mn) : 1.0;
        for (int i = 0; i < K; i++) y[i] = ydual[i]*sc;
        int before = ncols;
        double thr = 1e-7*sc;
        int ok = 0;
        for (int attempt = 0; attempt < 8*effort && !ok; attempt++) {
            if (attempt >= 2 && (attempt & 1)) {
                static int savP[MAXN]; memcpy(savP, P, sizeof(int)*n);
                int pok = posa(3000L*n, 20);
                if (pok) recount();
                else { memcpy(P, savP, sizeof(int)*n); for (int i2 = 0; i2 < n; i2++) pos[P[i2]] = i2; recount(); }   // failed restart: keep the old path
            }
            long steps = (4000L << (attempt < 6 ? attempt : 6)) * n / 8;
            if (attempt == 1 && !pm3_done) {
                pm3_done = 1;
                static int savP2[MAXN]; memcpy(savP2, P, sizeof(int)*n);
                pm3_seed();
                memcpy(P, savP2, sizeof(int)*n); for (int i2 = 0; i2 < n; i2++) pos[P[i2]] = i2; recount();
                for (int j = before; j < ncols; j++) { double v = 0; for (int i = 0; i < K; i++) v += y[i]*cols[j][i]; if (v > thr) ok = 1; }
                if (ok) break;
            }
            if (c4_nmasks > 0 && attempt == 1 && !c4_tp_done) {
                c4_tp_done = 1;
                for (int q2 = 0; q2 < c4_nmasks; q2++) c4_twinset_seed(c4_masks[q2], y);
                c4_S_cur = 0;
                for (int j = before; j < ncols; j++) { double v = 0; for (int i = 0; i < K; i++) v += y[i]*cols[j][i]; if (v > thr) ok = 1; }
                if (ok) break;
            }
            if (c4_nmasks > 0 && (attempt % 2 == 1)) {
                for (int q2 = 0; q2 < c4_nmasks; q2++) c4_anneal(c4_masks[q2], y, (1500L << (attempt < 8 ? attempt/2 : 4)) * (n/2), (attempt % 4 == 3));
                for (int j = before; j < ncols; j++) { double v = 0; for (int i = 0; i < K; i++) v += y[i]*cols[j][i]; if (v > thr) ok = 1; }
                if (ok) break;
            }
            walk(y, steps, 0.3, 0.0, 0, thr, 20);
            for (int j = before; j < ncols; j++) { double v = 0; for (int i = 0; i < K; i++) v += y[i]*cols[j][i]; if (v > thr) ok = 1; }
        }
        if (ncols >= MAXCOLS - 30) {
            int keep[MAXK], nk = 0;
            for (int r = 0; r < K; r++) if (basis[r] >= 0) keep[nk++] = basis[r];
            static int tc[MAXK+1][MAXK]; static int tp[MAXK+1][MAXN];
            for (int j = 0; j < nk; j++) { memcpy(tc[j], cols[keep[j]], sizeof(int)*K); memcpy(tp[j], colpath[keep[j]], sizeof(int)*n); }
            int newest = ncols - 1;
            memcpy(tc[nk], cols[newest], sizeof(int)*K); memcpy(tp[nk], colpath[newest], sizeof(int)*n);
            for (int j = 0; j <= nk; j++) { memcpy(cols[j], tc[j], sizeof(int)*K); memcpy(colpath[j], tp[j], sizeof(int)*n); }
            ncols = nk + 1;
            lp_init();
            continue;
        }
        if (!ok) { for (int i = 0; i < K; i++) yout[i] = ydual[i]; *ncolsout = ncols; return 0; }
    }
    return 0;
}

int main(int argc, char **argv){
    int maxn = MAXN, minn = 2;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (!strcmp(argv[i], "-s") && i+1 < argc) rs = strtoull(argv[++i], 0, 10) * 2654435761ULL + 88172645463325252ULL;
        else if (!strcmp(argv[i], "-e") && i+1 < argc) effort = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-N") && i+1 < argc) maxn = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-d")) dump = 1;
        else if (!strcmp(argv[i], "-S")) use_seeds = 0;
        else if (!strcmp(argv[i], "-P") && i+1 < argc) extra_path_file = argv[++i];
        else if (!strcmp(argv[i], "-C")) use_c4 = 0;
        else if (!strcmp(argv[i], "-c")) certmode = 1;
        else if (!strcmp(argv[i], "-x") && i+1 < argc) explore = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-D")) dump = 2;
        else if (!strcmp(argv[i], "-n") && i+1 < argc) minn = atoi(argv[++i]);
    }
    { u64 t = 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 2*MAXN+16; i++) { t ^= t<<13; t ^= t>>7; t ^= t<<17; RH[i] = t * 0x2545F4914F6CDD1DULL; } }
    trans = malloc(sizeof(int[MAXN])*MAXN); transinv = malloc(sizeof(int[MAXN])*MAXN);
    colpath = malloc(sizeof(int[MAXN])*MAXCOLS);
    size_t cap = 1<<22; char *line = malloc(cap);
    static int vals[MAXN*MAXD];
    long idx = 0, npass = 0, nfail = 0, net = 0, nskip = 0, nother = 0;
    while (fgets(line, cap, stdin)) {
        idx++;
        char *bar = strchr(line, '|');
        if (!bar) continue;
        *bar = 0;
        char meta[256]; strncpy(meta, line, 255); meta[255] = 0;
        size_t L = strlen(meta); while (L && (meta[L-1] == ' ' || meta[L-1] == '\n')) meta[--L] = 0;
        int nn = atoi(line);
        if (nn < minn || nn > maxn || nn > MAXN) { nskip++; continue; }
        long cntv = 0; char *p = bar + 1;
        for (;;) { char *e; long x = strtol(p, &e, 10); if (e == p) break; if (cntv < MAXN*MAXD) vals[cntv] = (int)x; cntv++; p = e; }
        if (cntv % nn != 0 || cntv / nn > MAXD || cntv / nn < 1) { printf("%s ERR badlist\n", meta); nother++; continue; }
        n = nn; deg = (int)(cntv / nn);
        int bad = 0;
        for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) { nbr[v][i] = vals[v*deg+i]; if (nbr[v][i] < 0 || nbr[v][i] >= n || nbr[v][i] == v) bad = 1; }
        if (!bad) for (int v = 0; v < n && !bad; v++) for (int i = 0; i < deg; i++) {
            if (!adjacent(nbr[v][i], v)) bad = 1;
            for (int j = 0; j < i; j++) if (nbr[v][i] == nbr[v][j]) bad = 1;
        }
        if (bad) { printf("%s ERR badgraph\n", meta); nother++; continue; }
        if (!connected()) { nskip++; continue; }
        if (compute_orbits() != 0) { printf("%s ERR notVT\n", meta); nother++; fflush(stdout); continue; }
        if (dump) {
            printf("LABELS %s | n=%d deg=%d K=%d |", meta, n, deg, K);
            for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) printf(" %d:%d", nbr[v][i], lab[v][i]);
            printf("\n");
            if (dump == 2) continue;
        }
        double y[MAXK]; int nc = 0;
        clock_t t0 = clock();
        int r = process(y, &nc);
        double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
        printf("%s deg=%d K=%d t=%.2f [", meta, deg, K, secs);
        for (int i = 0; i < K; i++) printf("%d%s", msz[i], i+1 < K ? "," : "");
        printf("] ");
        if (r == 1) {
            printf("PASS cols=%d%s", nc, limit_flag ? " LIMIT" : ""); npass++;
            if (c4_twins_found >= 0) printf(" c4t=%d", c4_twins_found);
            if (explore) { explore_dirs(); double mn = 1e300; for (int d2 = 0; d2 < 2*K; d2++) if (slack[d2] < mn) mn = slack[d2];
                printf(" minslack=%.3f slacks=[", mn); for (int d2 = 0; d2 < 2*K; d2++) printf("%.2f%s", slack[d2], d2+1 < 2*K ? "," : ""); printf("]"); }
            printf("\n");
            if (certmode) {
                printf("CERT %s | n=%d deg=%d K=%d | sizes", meta, n, deg, K);
                for (int i = 0; i < K; i++) printf(" %d", msz[i]);
                printf(" | adj");
                for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) printf(" %d", nbr[v][i]);
                printf(" | paths %d", certn);
                for (int j = 0; j < certn; j++) { printf(" ;"); for (int i = 0; i < n; i++) printf(" %d", colpath[certsup[j]][i]); }
                printf("\n");
            }
        }
        else if (r == 2) { printf("ET%s\n", limit_flag ? " LIMIT" : ""); net++; }
        else if (r == -1) { printf("NOHAM\n"); nother++; }
        else if (r == -2) { printf("EXACTFAIL\n"); nother++; }
        else {
            printf("FAIL cols=%d%s y=[", nc, limit_flag ? " LIMIT" : "");
            for (int i = 0; i < K; i++) printf("%.6f%s", y[i], i+1 < K ? "," : "");
            printf("]");
            printf(" colsfound:");
            for (int j = 0; j < ncols && j < 60; j++) { printf(" ("); for (int i = 0; i < K; i++) printf("%d%s", cols[j][i], i+1 < K ? "," : ""); printf(")"); }
            printf("\n"); nfail++;
        }
        fflush(stdout);
    }
    fprintf(stderr, "done: lines=%ld pass=%ld et=%ld fail=%ld other=%ld skipped=%ld\n", idx, npass, net, nfail, nother, nskip);
    return 0;
}
