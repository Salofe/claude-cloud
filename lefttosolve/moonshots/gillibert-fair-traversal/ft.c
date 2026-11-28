// ft.c -- fair traversal checker for connected vertex-transitive graphs (graph6 on stdin, n <= 62).
//
// For each graph: compute the edge orbits of Aut(G) (own individualisation-refinement search, every
// automorphism used is verified), then look for Hamiltonian paths whose orbit-count vectors contain the
// "fair" direction (orbit sizes m_1..m_k) in their cone.  Column generation: phase-1 simplex over the
// pool of count vectors found so far; pricing by a biased rotation walk on Hamiltonian paths.
// A PASS is verified exactly (integer Bareiss solve on the support, every path re-validated).
// A FAIL only means that the heuristic did not find the needed paths: it must be analysed exactly.
//
// usage: ft [-v] [-s seed] [-e effort] [-m maxdeg] [-M mindeg] < graphs.g6
// output: one line per graph:  idx n deg k sizes... STATUS extra
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXN 64
#define MAXK 64
#define MAXCOLS 6000
typedef unsigned long long u64;
typedef __int128 i128;

static int n, deg;
static u64 adj[MAXN];
static int nbr[MAXN][MAXN];
static unsigned char lab[MAXN][MAXN];
static int K;            // number of edge orbits
static int msz[MAXK];    // orbit sizes
static int verbose = 0;
static int limit_flag;   // set if an automorphism search hit the node limit

// ---------------- RNG
static u64 rs = 88172645463325252ULL;
static inline u64 rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static inline int rndint(int m){ return (int)(rnd() % (u64)m); }
static inline double rnd01(void){ return (double)(rnd()>>11) * (1.0/9007199254740992.0); }

// ---------------- graph6
static int parse_g6(const char *s){
    const unsigned char *p = (const unsigned char*)s;
    if (*p < 63 || *p > 125) return -1;
    n = *p - 63; p++;
    memset(adj, 0, sizeof adj);
    int bit = 0, val = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (bit == 0) { if (*p < 63 || *p > 126) return -1; val = *p - 63; p++; bit = 6; }
        bit--;
        if ((val >> bit) & 1) { adj[i] |= 1ULL<<j; adj[j] |= 1ULL<<i; }
    }
    deg = __builtin_popcountll(adj[0]);
    for (int v = 0; v < n; v++) {
        if (__builtin_popcountll(adj[v]) != deg) return -2;
        int c = 0; u64 m = adj[v];
        while (m) { int u = __builtin_ctzll(m); m &= m-1; nbr[v][c++] = u; }
    }
    return 0;
}
static int connected(void){
    u64 seen = 1, fr = 1;
    while (fr) { int v = __builtin_ctzll(fr); fr &= fr-1; u64 nw = adj[v] & ~seen; seen |= nw; fr |= nw; }
    return seen == ((n == 64) ? ~0ULL : ((1ULL<<n)-1));
}

// ---------------- automorphism search (pair refinement)
static u64 RH[4*MAXN+16];
typedef struct { int col; u64 h; int v; } SigT;
static int cmp_sig(const void *a, const void *b){
    const SigT *x = a, *y = b;
    if (x->col != y->col) return x->col < y->col ? -1 : 1;
    if (x->h != y->h) return x->h < y->h ? -1 : 1;
    return 0;
}
// refine the pair of colourings (ca on copy A, cb on copy B) to a stable one; returns number of
// colours, or -1 if some colour class is unbalanced between the two copies.
static int refine(int *ca, int *cb){
    SigT sg[2*MAXN];
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
        int newc[2*MAXN];
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
        for (int i = 0; i < 2*n; i++) {
            if (sg[i].v < n) ca[sg[i].v] = newc[i]; else cb[sg[i].v - n] = newc[i];
        }
        if (nc == ncol) return nc;
        ncol = nc;
    }
}
static long nodes_left;
static int is_aut(const int *p){
    u64 seen = 0;
    for (int v = 0; v < n; v++) {
        if (p[v] < 0 || p[v] >= n) return 0;
        seen |= 1ULL<<p[v];
        u64 m = 0;
        for (int i = 0; i < deg; i++) m |= 1ULL<<p[nbr[v][i]];
        if (m != adj[p[v]]) return 0;
    }
    return seen == ((n == 64) ? ~0ULL : ((1ULL<<n)-1));
}
// returns 1 and perm (A -> B) if an automorphism compatible with the colourings exists, 0 if none,
// -1 if the node limit was hit.
static int search(int *ca, int *cb, int *perm){
    int ncol = refine(ca, cb);
    if (ncol < 0) return 0;
    if (ncol == n) {
        int inv[MAXN];
        for (int w = 0; w < n; w++) inv[cb[w]] = w;
        for (int v = 0; v < n; v++) perm[v] = inv[ca[v]];
        return is_aut(perm) ? 1 : 0;
    }
    int cnt[MAXN]; memset(cnt, 0, sizeof(int)*ncol);
    for (int v = 0; v < n; v++) cnt[ca[v]]++;
    int best = -1;
    for (int c = 0; c < ncol; c++) if (cnt[c] >= 2 && (best < 0 || cnt[c] < cnt[best])) best = c;
    int v = 0; while (ca[v] != best) v++;
    int ca2[MAXN], cb2[MAXN];
    for (int w = 0; w < n; w++) if (cb[w] == best) {
        if (nodes_left-- <= 0) return -1;
        memcpy(ca2, ca, sizeof(int)*n); memcpy(cb2, cb, sizeof(int)*n);
        ca2[v] = ncol; cb2[w] = ncol;
        int r = search(ca2, cb2, perm);
        if (r != 0) return r;
    }
    return 0;
}
#define NODE_LIMIT 300000
static int ufp[MAXN];
static int uf_find(int x){ while (ufp[x] != x) { ufp[x] = ufp[ufp[x]]; x = ufp[x]; } return x; }
static void uf_union(int a, int b){ a = uf_find(a); b = uf_find(b); if (a != b) ufp[a] = b; }

static int trans[MAXN][MAXN], transinv[MAXN][MAXN];
// returns 0 ok, -1 not vertex-transitive / search failure
static int compute_orbits(void){
    static int gens[MAXN][MAXN]; int ngens = 0;
    int has[MAXN]; memset(has, 0, sizeof has);
    int ca[MAXN], cb[MAXN], perm[MAXN];
    limit_flag = 0;
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
        for (int x = 0; x < n; x++) { ca[x] = 0; cb[x] = 0; }
        ca[0] = 1; cb[v] = 1;
        nodes_left = NODE_LIMIT * 10L;
        int r = search(ca, cb, perm);
        if (r != 1) return -1;
        memcpy(gens[ngens++], perm, sizeof(int)*n);
    }
    for (int v = 0; v < n; v++) for (int x = 0; x < n; x++) transinv[v][trans[v][x]] = x;
    for (int x = 0; x < n; x++) ufp[x] = x;
    int reps[MAXN], nreps = 0;
    for (int i = 0; i < deg; i++) {
        int u = nbr[0][i], found = 0;
        for (int j = 0; j < nreps; j++) if (uf_find(reps[j]) == uf_find(u)) { found = 1; break; }
        if (found) continue;
        for (int j = 0; j < nreps && !found; j++) {
            int r0 = reps[j];
            for (int x = 0; x < n; x++) { ca[x] = 0; cb[x] = 0; }
            ca[0] = 1; cb[0] = 1; ca[r0] = 2; cb[u] = 2;
            nodes_left = NODE_LIMIT;
            int r = search(ca, cb, perm);
            if (r == 1) {
                if (perm[0] != 0 || perm[r0] != u) { fprintf(stderr, "internal: bad stabiliser perm\n"); exit(3); }
                for (int t = 0; t < deg; t++) uf_union(nbr[0][t], perm[nbr[0][t]]);
                found = 1;
            } else if (r == -1) limit_flag = 1;
        }
        if (!found) reps[nreps++] = u;
    }
    // reverse arcs and consistency merges (all justified by verified automorphisms)
    for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) {
        int w = nbr[v][i];
        uf_union(transinv[v][w], transinv[w][v]);
    }
    int cid[MAXN]; for (int x = 0; x < n; x++) cid[x] = -1;
    K = 0;
    for (int i = 0; i < deg; i++) { int r = uf_find(nbr[0][i]); if (cid[r] < 0) cid[r] = K++; }
    memset(msz, 0, sizeof msz);
    for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) {
        int w = nbr[v][i];
        int c = cid[uf_find(transinv[v][w])];
        lab[v][w] = (unsigned char)c;
        if (v < w) msz[c]++;
    }
    for (int v = 0; v < n; v++) for (int i = 0; i < deg; i++) {
        int w = nbr[v][i];
        if (lab[v][w] != lab[w][v]) { fprintf(stderr, "internal: asymmetric labels\n"); exit(3); }
    }
    // sanity: every vertex sees 2*m_c/n edges of class c
    for (int v = 0; v < n; v++) {
        int c[MAXK]; memset(c, 0, sizeof(int)*K);
        for (int i = 0; i < deg; i++) c[lab[v][nbr[v][i]]]++;
        for (int t = 0; t < K; t++) if (c[t]*n != 2*msz[t]) { fprintf(stderr, "internal: orbit degree mismatch\n"); exit(3); }
    }
    return 0;
}

// ---------------- Hamiltonian paths
static int P[MAXN], pos[MAXN];
static int cnt[MAXK];     // count vector of current path
static void recount(void){
    memset(cnt, 0, sizeof(int)*K);
    for (int i = 0; i + 1 < n; i++) cnt[lab[P[i]][P[i+1]]]++;
}
static int valid_path(const int *p){
    u64 seen = 0;
    for (int i = 0; i < n; i++) { if (seen >> p[i] & 1) return 0; seen |= 1ULL<<p[i]; }
    for (int i = 0; i + 1 < n; i++) if (!(adj[p[i]] >> p[i+1] & 1)) return 0;
    return 1;
}
static void reverse_seg(int i, int j){
    while (i < j) { int t = P[i]; P[i] = P[j]; P[j] = t; pos[P[i]] = i; pos[P[j]] = j; i++; j--; }
    if (i == j) pos[P[i]] = i;
}
// Posa rotation-extension. returns 1 if a Hamiltonian path was found.
static int posa(long maxit){
    for (int attempt = 0; attempt < 20; attempt++) {
        int len = 1; u64 in = 0;
        P[0] = rndint(n); pos[P[0]] = 0; in = 1ULL<<P[0];
        for (long it = 0; it < maxit && len < n; it++) {
            int t = P[len-1];
            u64 U = adj[t] & ~in;
            if (U) {
                int c = __builtin_popcountll(U), r = rndint(c);
                while (r--) U &= U-1;
                int u = __builtin_ctzll(U);
                P[len] = u; pos[u] = len; in |= 1ULL<<u; len++;
                continue;
            }
            if ((it & 7) == 7) { reverse_seg(0, len-1); continue; }
            if (len < 3) { reverse_seg(0, len-1); continue; }
            int x = nbr[t][rndint(deg)];
            int i = pos[x];
            if (i >= len-2) continue;
            reverse_seg(i+1, len-1);
        }
        if (len == n) return 1;
    }
    return 0;
}

// ---------------- column pool and LP
static int cols[MAXCOLS][MAXK]; static int ncols;
static int colpath[MAXCOLS][MAXN];
static double Binv[MAXK][MAXK], xB[MAXK], ydual[MAXK];
static int basis[MAXK];  // >=0: column index; <0: artificial for row -(b+1)
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
#define TOL 1e-9
// run phase-1 simplex on the current pool. returns objective (sum of artificials).
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
                // tie: prefer artificial leaving, then smallest index (Bland)
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
// exact check: the orbit-size vector is a nonnegative combination of the given columns (support).
// returns 1 ok, 0 not, -1 overflow.
static int exact_check(const int *sup, int s){
    static i128 M[MAXK][MAXK+1];
    for (int i = 0; i < K; i++) { for (int j = 0; j < s; j++) M[i][j] = cols[sup[j]][i]; M[i][s] = msz[i]; }
    i128 prev = 1; int prow[MAXK]; int used[MAXK]; memset(used, 0, sizeof used);
    for (int c = 0; c < s; c++) {
        int r = -1; for (int i = 0; i < K; i++) if (!used[i] && M[i][c] != 0) { r = i; break; }
        if (r < 0) return 0;  // dependent columns: treat as failure of this check
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
    // now rows prow[c] have M[prow[c]][c] = prev (common), other entries in columns < s are 0
    for (int i = 0; i < K; i++) if (!used[i] && M[i][s] != 0) return 0;
    for (int c = 0; c < s; c++) {
        i128 num = M[prow[c]][s], den = M[prow[c]][c];
        if (den == 0) return 0;
        if ((num > 0 && den < 0) || (num < 0 && den > 0)) return 0;
    }
    return 1;
}

// biased rotation walk maximising y.c ; adds improving columns. returns best value of y.c seen.
static double walk(const double *y, long steps, double T0, double T1, int addall, double thresh, int maxadd){
    double val = 0; for (int i = 0; i < K; i++) val += y[i]*cnt[i];
    double best = val; int added = 0;
    if (!addall && val > thresh) { if (add_col_from_path() >= 0) added++; }
    for (long s = 0; s < steps; s++) {
        double T = T0 + (T1 - T0) * (double)s / (double)steps;
        if ((rnd() & 3) == 0) reverse_seg(0, n-1);
        int t = P[n-1];
        int x = nbr[t][rndint(deg)];
        int i = pos[x];
        if (i >= n-2) continue;
        int la = lab[x][t], lr = lab[x][P[i+1]];
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

static int effort = 1;
// returns: 1 PASS, 0 FAIL(heuristic), 2 edge-transitive pass, -1 no Hamiltonian path found, -2 exact check problem
static int process(double *yout, int *ncolsout){
    ncols = 0;
    if (!posa(20000L*n)) { if (!posa(400000L*n)) return -1; }
    if (!valid_path(P)) { fprintf(stderr, "internal: invalid path\n"); exit(3); }
    recount();
    add_col_from_path();
    if (K == 1) return 2;
    double y0[MAXK]; for (int i = 0; i < K; i++) y0[i] = 0;
    walk(y0, 200L*n, 1.0, 1.0, 1, 0, 100);   // unbiased walk, collect everything (ncols capped below)
    lp_init();
    int fails = 0;
    for (int round = 0; round < 100000; round++) {
        double obj = lp_solve();
        if (obj < 1e-7) {
            int sup[MAXK], s = 0;
            for (int r = 0; r < K; r++) if (basis[r] >= 0 && xB[r] > 1e-9) sup[s++] = basis[r];
            for (int j = 0; j < s; j++) {
                if (!valid_path(colpath[sup[j]])) { fprintf(stderr, "internal: invalid stored path\n"); exit(3); }
                int c[MAXK]; memset(c, 0, sizeof(int)*K);
                for (int i = 0; i + 1 < n; i++) c[lab[colpath[sup[j]][i]][colpath[sup[j]][i+1]]]++;
                if (memcmp(c, cols[sup[j]], sizeof(int)*K) != 0) { fprintf(stderr, "internal: count mismatch\n"); exit(3); }
            }
            int e = exact_check(sup, s);
            *ncolsout = ncols;
            if (e == 1) return 1;
            return -2;
        }
        // pricing
        double y[MAXK]; double mx = -1e300, mn = 1e300;
        for (int i = 0; i < K; i++) { if (ydual[i] > mx) mx = ydual[i]; if (ydual[i] < mn) mn = ydual[i]; }
        double sc = (mx - mn > 1e-12) ? 1.0/(mx - mn) : 1.0;
        for (int i = 0; i < K; i++) y[i] = ydual[i]*sc;
        int before = ncols;
        double thr = 1e-7*sc;
        // value of y.c must exceed 0 to price in
        int ok = 0;
        for (int attempt = 0; attempt < 6*effort && !ok; attempt++) {
            if (attempt >= 2 && (attempt & 1)) { if (posa(20000L*n)) recount(); else { fprintf(stderr, "internal: posa failed on restart\n"); } }
            long steps = (2000L << (attempt < 6 ? attempt : 6)) * n / 8;
            walk(y, steps, 0.3, 0.0, 0, thr, 40);
            for (int j = before; j < ncols; j++) { double v = 0; for (int i = 0; i < K; i++) v += y[i]*cols[j][i]; if (v > thr) ok = 1; }
        }
        if (ncols >= MAXCOLS - 10) { // compact pool: keep basis columns only
            int keep[MAXK], nk = 0;
            for (int r = 0; r < K; r++) if (basis[r] >= 0) keep[nk++] = basis[r];
            static int tc[MAXK][MAXK], tp[MAXK][MAXN];
            for (int j = 0; j < nk; j++) { memcpy(tc[j], cols[keep[j]], sizeof(int)*K); memcpy(tp[j], colpath[keep[j]], sizeof(int)*n); }
            // also keep the newest columns
            int newest = ncols - 1;
            memcpy(tc[nk], cols[newest], sizeof(int)*K); memcpy(tp[nk], colpath[newest], sizeof(int)*n);
            for (int j = 0; j <= nk; j++) { memcpy(cols[j], tc[j], sizeof(int)*K); memcpy(colpath[j], tp[j], sizeof(int)*n); }
            ncols = nk + 1;
            lp_init();
            continue;
        }
        if (!ok) {
            fails++;
            if (fails >= 1) { for (int i = 0; i < K; i++) yout[i] = ydual[i]; *ncolsout = ncols; return 0; }
        }
    }
    return 0;
}

int main(int argc, char **argv){
    int maxdeg = 1000, mindeg = 0; long only = -1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (!strcmp(argv[i], "-s") && i+1 < argc) rs = strtoull(argv[++i], 0, 10) * 2654435761ULL + 88172645463325252ULL;
        else if (!strcmp(argv[i], "-e") && i+1 < argc) effort = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-m") && i+1 < argc) maxdeg = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-M") && i+1 < argc) mindeg = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-o") && i+1 < argc) only = atol(argv[++i]);
    }
    { u64 t = 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 4*MAXN+16; i++) { t ^= t<<13; t ^= t>>7; t ^= t<<17; RH[i] = t * 0x2545F4914F6CDD1DULL; } }
    static char line[4096];
    long idx = 0, npass = 0, nfail = 0, net = 0, nskip = 0, nother = 0;
    while (fgets(line, sizeof line, stdin)) {
        idx++;
        if (only >= 0 && idx != only) continue;
        size_t L = strlen(line); while (L && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        if (L == 0) continue;
        int pr = parse_g6(line);
        if (pr != 0) { printf("%ld ? ? ERR parse(%d) %s\n", idx, pr, line); nother++; continue; }
        if (n < 2 || deg < mindeg || deg > maxdeg) { nskip++; continue; }
        if (!connected()) { nskip++; continue; }
        if (compute_orbits() != 0) { printf("%ld %d %d ERR notVT %s\n", idx, n, deg, line); nother++; continue; }
        double y[MAXK]; int nc = 0;
        int r = process(y, &nc);
        printf("%ld %d %d %d [", idx, n, deg, K);
        for (int i = 0; i < K; i++) printf("%d%s", msz[i], i+1 < K ? "," : "");
        printf("] ");
        if (r == 1) { printf("PASS cols=%d%s\n", nc, limit_flag ? " LIMIT" : ""); npass++; }
        else if (r == 2) { printf("ET%s\n", limit_flag ? " LIMIT" : ""); net++; }
        else if (r == -1) { printf("NOHAM %s\n", line); nother++; }
        else if (r == -2) { printf("EXACTFAIL %s\n", line); nother++; }
        else {
            printf("FAIL cols=%d%s y=[", nc, limit_flag ? " LIMIT" : "");
            for (int i = 0; i < K; i++) printf("%.6f%s", y[i], i+1 < K ? "," : "");
            printf("] %s\n", line); nfail++;
            if (verbose) {
                for (int j = 0; j < ncols; j++) { printf("  col"); for (int i = 0; i < K; i++) printf(" %d", cols[j][i]); printf("\n"); }
            }
        }
        fflush(stdout);
    }
    fprintf(stderr, "done: graphs=%ld pass=%ld et=%ld fail=%ld other=%ld skipped=%ld\n", idx, npass, net, nfail, nother, nskip);
    return 0;
}
