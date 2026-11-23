"""Extra terms of the two-block model for general k (numpy; sympy / jax only for some modes).

Setting (see garbage_fast.py and notes/extra_terms.md). Rows 0..2k-1, first-block columns 0..k-1.
For a pairing pi = {R, R^c} let q(R) be the k x k permanent of the rows R on the first block. The
two-block model needs N = C(2k,k)/2 squares plus E(k) extra k-split products, where E(k) is the least
number of split products that add up to  - Gamma(c),  Gamma(c) = sum_pi c_pi q(R) q(R^c),  for some
c with every c_pi nonzero.  Gamma(c) = sum_m (A c)_m w_m  over the perfect matchings m of the rows,
(A c)_m = sum of c_pi over the pairings that separate every pair of m, w_m = the monomials in which
the two rows of each pair of m share a column and every column is used.

RESULTS
  1. Walsh characters (exact, all k; `char`, `verify`).  For a set Q of rows with |Q| even put
     c_R = (-1)^{|R cap Q|}  (well defined on pairings, every c_R = +-1).  Then
         (A c)_m = (-1)^{|Q|/2} 2^{k-1}   if no pair of m joins Q to Q^c,   0 otherwise.
     k even, Q = R0 = {0..k-1}:  Gamma(c) = (-1)^{k/2} 2^{k-1} sum_{J subset of the columns, |J| = k/2}
         M_J(R0) M_{J^c}(R0^c),   M_J(S) = sum of the monomials of the rows S that use every column of J twice.
       So  E(k) <= C(k, k/2):  2, 6, 20, 70 for k = 2, 4, 6, 8  (T_k - 1 = 2, 18, 140, 1106).
     k odd, Q = {0..k-2}, R0 = Q + {k-1}:  E(k) <= (k+1)/2 * C(k, (k-1)/2):  6, 30, 140 for k = 3, 5, 7.
     Consequences (c = 1/c): the 2k x 2k permanent is a limit of N + E split products and an EXACT sum of
     N + 2E.  k = 4: limit 41, exact 47 (Laplace 70, squares 53).  `verify 4` checks all of this on the
     full 8^8 integer tensors.
  2. All extra terms on ONE pairing (k >= 3): at least min_i k!/(i! i! (k-2i)!) terms, i >= 1 (paper).
     With the forced zeros computed by `single`: exactly 6 (k = 3), 6 (k = 4), 30 (k = 5), 20 (k = 6).
  3. Matching sub-model (every pairing carries a function h_R on S_k; `check`, `active`, `solve`).
     The formulation reproduces 2 at k = 2 and 5 at k = 3.  At k = 4 it is NOT competitive: every
     admissible active set has at least 3 pairings (exact), and the rank-surrogate search finds nothing
     below cost 45 with all constants nonzero (numerical; the character solution of item 1 is outside
     this sub-model, it uses the matchings with two pairs inside R0).

Usage
  python3 garbage_general.py check            formulation of the matching sub-model against k = 2, 3
  python3 garbage_general.py char 6           character identity on matchings (exact integers), any k <= 6
  python3 garbage_general.py verify 4         full integer tensors: garbage cancels, limit and exact counts (k <= 4)
  python3 garbage_general.py single 5         one pairing: which constants are forced to vanish, by type
  python3 garbage_general.py active 4 3       matching sub-model: admissible active sets with <= 3 pairings
  python3 garbage_general.py solve 4 all 6    matching sub-model: rank-surrogate search (needs jax)
  python3 garbage_general.py solve 3 012,013,024 6
"""
import itertools
import math
import sys
import time
from fractions import Fraction as Fr

import numpy as np


# ----------------------------------------------------------------------------- combinatorics
def pairings(k):
    return [R for R in itertools.combinations(range(2 * k), k) if 0 in R]


def matchings(elts):
    """Perfect matchings of a list of rows."""
    elts = list(elts)
    if not elts:
        yield ()
        return
    a = elts[0]
    for b in elts[1:]:
        rest = [e for e in elts if e not in (a, b)]
        for m in matchings(rest):
            yield ((a, b),) + m


def sign(p):
    return (-1) ** sum(1 for i in range(len(p)) for j in range(i) if p[j] > p[i])


class Sub:
    """Tables of the matching sub-model for 2k rows.

    prs[p]      pairing (the side R that contains row 0, sorted), comp[p] its complement
    ms[i]       perfect matching of the rows
    Sk[s]       permutation b of range(k); on the pairing p it stands for the matching
                {R[a], R^c[b[a]]}: a bijection R -> R^c after sorting both sides
    flag[p, s]  index of that matching;  bij[p, i] = s, or -1 when p does not separate ms[i]
    A           matchings x pairings incidence matrix (1 when the pairing separates the matching)
    kern[s, t]  index of Sk[t]^-1 o Sk[s]: the group matrix of g is K[s, t] = g[kern[s, t]]
    """

    def __init__(self, k):
        self.k = k
        n = 2 * k
        self.prs = pairings(k)
        self.comp = [tuple(i for i in range(n) if i not in R) for R in self.prs]
        self.N = len(self.prs)
        self.ms = list(matchings(range(n)))
        self.M = len(self.ms)
        self.mindex = {frozenset(frozenset(e) for e in m): i for i, m in enumerate(self.ms)}
        self.Sk = list(itertools.permutations(range(k)))
        self.sidx = {s: i for i, s in enumerate(self.Sk)}
        self.f = len(self.Sk)
        self.flag = np.zeros((self.N, self.f), dtype=int)
        self.bij = -np.ones((self.N, self.M), dtype=int)
        for p, (R, Rc) in enumerate(zip(self.prs, self.comp)):
            for s, b in enumerate(self.Sk):
                i = self.mindex[frozenset(frozenset((R[a], Rc[b[a]])) for a in range(k))]
                self.flag[p, s] = i
                self.bij[p, i] = s
        self.A = (self.bij >= 0).T.astype(np.int64)
        self.names = [''.join(map(str, R)) for R in self.prs]
        self.sgn = np.array([sign(s) for s in self.Sk])
        mul = np.zeros((self.f, self.f), dtype=int)          # mul[s, t] = Sk[s] o Sk[t]
        inv = np.zeros(self.f, dtype=int)
        for s, a in enumerate(self.Sk):
            for t, b in enumerate(self.Sk):
                mul[s, t] = self.sidx[tuple(a[b[i]] for i in range(k))]
            inv[s] = self.sidx[tuple(int(x) for x in np.argsort(a))]
        self.mul, self.inv = mul, inv
        self.kern = mul[inv][:, :].T.copy()                   # kern[s, t] = mul[inv[t], s]

    def push(self, h):
        """h[p, s] = value of h_R at the bijection s. Returns sum over the pairings, as a vector on matchings."""
        out = np.zeros(self.M, dtype=h.dtype)
        for p in range(self.N):
            np.add.at(out, self.flag[p], h[p])
        return out


# ----------------------------------------------------------------------------- exact linear algebra
def rref_exact(rows):
    """Reduced row echelon form over Q (list of lists of ints / Fractions). Returns (matrix, pivot columns)."""
    Mx = [[Fr(x) for x in r] for r in rows]
    piv = []
    rk = 0
    ncol = len(Mx[0]) if Mx else 0
    for c in range(ncol):
        p = next((r for r in range(rk, len(Mx)) if Mx[r][c] != 0), None)
        if p is None:
            continue
        Mx[rk], Mx[p] = Mx[p], Mx[rk]
        pv = Mx[rk][c]
        Mx[rk] = [x / pv for x in Mx[rk]]
        for r in range(len(Mx)):
            if r != rk and Mx[r][c] != 0:
                fct = Mx[r][c]
                Mx[r] = [x - fct * y for x, y in zip(Mx[r], Mx[rk])]
        piv.append(c)
        rk += 1
    return Mx[:rk], piv


def rank_exact(rows):
    return len(rref_exact(rows)[1])


def forced_zeros_exact(B):
    """Coordinates that vanish on the whole kernel of the integer matrix B: e_j lies in the row space,
    i.e. the reduced echelon form has the row e_j. Returns (kernel dimension, list of forced coordinates)."""
    if len(B) == 0:
        return (len(B[0]) if len(B) else 0), []
    R, piv = rref_exact(B)
    ncol = len(B[0])
    forced = [piv[i] for i, r in enumerate(R) if sum(1 for x in r if x != 0) == 1]
    return ncol - len(piv), forced


def cost_exact(S, h):
    """Cost of a function h on S_k (exact numbers, in the order S.Sk): the least number of products
    phi(sigma) psi(tau) whose sum is g(tau^-1 sigma), g = h - c, over the nonzero constants c. This is
    sum over the nontrivial irreducibles rho of dim(rho) rank(h^(rho)), plus 1 when the mean of h is 0.
    Returns (cost, best c or None when the mean vanishes)."""
    f = S.f
    mean = sum(Fr(x) for x in h) / f
    if mean != 0:
        g = [Fr(x) - mean for x in h]
        return rank_exact([[g[S.kern[s, t]] for t in range(f)] for s in range(f)]), mean
    return rank_exact([[Fr(h[S.kern[s, t]]) for t in range(f)] for s in range(f)]) + 1, None


# ----------------------------------------------------------------------------- mode: check (k = 2, 3)
def check_formulation(verbose=True):
    """The matching sub-model against the known answers: cost 2 at k = 2, cost 5 at k = 3."""
    ok = True
    # k = 2: exhaustive over small integer values (the cost only depends on the pattern
    # h = (x, y) per pairing: 0 for x = y != 0, 1 for x = y = 0, 2 for x = -y != 0 or x != +-y)
    S = Sub(2)
    best = None
    for hh in itertools.product(range(-3, 4), repeat=6):
        h = np.array(hh, dtype=object).reshape(3, 2)
        if any(S.push(h)):
            continue
        c = sum(cost_exact(S, list(h[p]))[0] for p in range(3))
        if best is None or c < best[0]:
            best = (c, h.tolist())
    ok &= best[0] == 2
    if verbose:
        print(f"k = 2: least cost over all integer solutions with entries in [-3, 3]: {best[0]}  (expected 2), e.g. h = {best[1]}")
        print("       (paper: the three constraints h_R(m) + h_R'(m) = 0 exclude cost <= 1, see notes/extra_terms.md)")
    # k = 3: the identity C5 / TERMS5 of garbage_fast.py
    import garbage_fast as gf
    S = Sub(3)
    assert S.prs == gf.pairings(3) and S.Sk == gf.S3
    h = np.zeros((S.N, S.f), dtype=object)
    for p in range(S.N):
        h[p, :] = Fr(gf.C5[p])
    invariant = True
    for pi in sorted({t[0] for t in gf.TERMS5}):
        K = [[sum(Fr(s * F[si] * G[ti]) for (p, s, F, G) in gf.TERMS5 if p == pi) for ti in range(S.f)] for si in range(S.f)]
        g = {}
        for si in range(S.f):
            for ti in range(S.f):
                b = int(S.kern[si, ti])
                if g.setdefault(b, K[si][ti]) != K[si][ti]:
                    invariant = False
        for b, v in g.items():
            h[pi, b] += v
    res = S.push(h)
    costs = [cost_exact(S, list(h[p]))[0] for p in range(S.N)]
    ok &= invariant and not any(res) and sum(costs) == 5
    if verbose:
        print(f"k = 3: the E = 5 identity of garbage_fast.py: extra terms on each pairing are a function of tau^-1 sigma: {invariant};"
              f" constraint sum_R h_R(m) = 0 on the 15 matchings: {not any(res)}; cost {sum(costs)} (expected 5)")
        for p in range(S.N):
            if costs[p]:
                print(f"       pairing {S.names[p]}: cost {costs[p]}, h = {[str(x) for x in h[p]]}")
    try:
        low = gf.syntheme_check(verbose=False)
        ok &= bool(low)
        if verbose:
            print(f"k = 3: garbage_fast.syntheme_check (exact: no solution of cost <= 4 in the sub-model): {bool(low)}")
    except ImportError:
        if verbose:
            print("k = 3: sympy missing, lower bound not rechecked")
    if verbose:
        print("FORMULATION CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return ok


# ----------------------------------------------------------------------------- Walsh characters
def char_data(k):
    """(Q, R0, sign s, E): c_R = (-1)^{|R cap Q|}, (A c)_m = s for the matchings without a pair joining
    Q and Q^c, and Gamma(c) = s * (E split products on the pairing R0)."""
    if k % 2 == 0:
        Q = set(range(k))
        return Q, tuple(range(k)), (-1) ** (k // 2) * 2 ** (k - 1), math.comb(k, k // 2)
    Q = set(range(k - 1))
    return Q, tuple(range(k)), (-1) ** ((k - 1) // 2) * 2 ** (k - 1), (k + 1) // 2 * math.comb(k, (k - 1) // 2)


def char_check(k, verbose=True):
    """Exact, on matchings: for every even Q of the form {0..2q-1}, A chi_Q = (-1)^q 2^(k-1) [m has no
    pair joining Q and Q^c]; and the table of counts for the choice of char_data(k)."""
    S = Sub(k)
    ok = True
    for q in range(0, k + 1):
        Q = set(range(2 * q))
        c = np.array([(-1) ** len(Q & set(R)) for R in S.prs], dtype=np.int64)
        gam = S.A @ c
        want = np.array([(-1) ** q * 2 ** (k - 1) if all((a in Q) == (b in Q) for a, b in m) else 0 for m in S.ms])
        ok &= bool((gam == want).all())
    Q, R0, s, E = char_data(k)
    N = S.N
    T = sum(math.factorial(k) // (math.factorial(i) ** 2 * math.factorial(k - 2 * i)) for i in range(k // 2 + 1))
    if verbose:
        print(f"k = {k}: A chi_Q = (-1)^(|Q|/2) 2^(k-1) [m respects Q] for |Q| = 0, 2, .., 2k: {ok}")
        print(f"       Q = {sorted(Q)}: E = {E} extra terms on the pairing {''.join(map(str, R0))} (T_k - 1 = {T - 1});"
              f" limit N + E = {N + E}, exact N + 2E = {N + 2 * E}, squares N + T_k - 1 = {N + T - 1}, Laplace 2N = {2 * N}")
    return ok


def verify_tensors(k, verbose=True):
    """Full integer tensors in (Z^2k)^(x 2k), k <= 4. With c_R = (-1)^{|R cap Q|} and the E products
    P_e = F_e(R0) G_e(R0^c) of char_data(k) (first block), P'_e (second block):
       lam^0:  sum_R c_R q1(R) q1(R^c) - s sum_e P_e = 0
       lam^1:  sum_R q1(R) q2(R^c) + q2(R) q1(R^c) = perm
       lam^2:  sum_R c_R q2(R) q2(R^c) - s sum_e P'_e = 0
       exact:  perm = sum_R (c_R q1 + q2)(R) (q1 + c_R q2)(R^c) - s sum_e P_e - s sum_e P'_e   (N + 2E products)
    and for lam != 0:  perm + lam * (sum_R c_R q2 q2) = sum_R (c_R q1 + lam q2)(R) (q1/lam + c_R q2)(R^c) - (s/lam) sum_e P_e
    (N + E products), which is the lam^0 and lam^1 statements together."""
    assert k <= 4, "8^8 entries is the largest tensor this check handles"
    t0 = time.time()
    m = 2 * k
    Q, R0, s, E = char_data(k)
    q1 = np.zeros((m,) * k, dtype=np.int32)
    q2 = np.zeros((m,) * k, dtype=np.int32)
    for p in itertools.permutations(range(k)):
        q1[p] = 1
        q2[tuple(c + k for c in p)] = 1
    tup = np.indices((m,) * k, dtype=np.int8).reshape(k, -1)
    cnt = np.stack([(tup == c).sum(axis=0) for c in range(m)])        # column multiplicities of the index tuples

    def weight_tensor(w):                                             # tuples of k rows with column multiplicities w
        return np.all(cnt == np.array(w, dtype=cnt.dtype)[:, None], axis=0).reshape((m,) * k).astype(np.int32)

    def place(R, f, g):
        Rc = tuple(i for i in range(m) if i not in R)
        return np.ascontiguousarray(np.transpose(np.multiply.outer(f, g), np.argsort(R + Rc))).ravel()

    extra = []                                                        # (block, F on R0, G on R0^c)
    if k % 2 == 0:
        for J in itertools.combinations(range(k), k // 2):
            for blk in (0, 1):
                w, w2 = [0] * m, [0] * m
                for j in range(k):
                    (w if j in J else w2)[j + blk * k] = 2
                extra.append((blk, weight_tensor(w), weight_tensor(w2)))
    else:
        for J in itertools.combinations(range(k), (k - 1) // 2):
            for j in (j for j in range(k) if j not in J):
                for blk in (0, 1):
                    sub = np.zeros((m,) * (k - 1), dtype=np.int32)     # rows 0..k-2: every column of J twice
                    for idx in itertools.product([c + blk * k for c in J], repeat=k - 1):
                        if all(idx.count(c + blk * k) == 2 for c in J):
                            sub[idx] = 1
                    F = np.zeros((m,) * k, dtype=np.int32)
                    F[..., j + blk * k] = sub                         # row k-1 uses column j
                    w2 = [0] * m
                    for c in range(k):
                        if c not in J:
                            w2[c + blk * k] = 1 if c == j else 2      # rows k..2k-1: column j once, the rest twice
                    extra.append((blk, F, weight_tensor(w2)))
    prs = pairings(k)
    c = [(-1) ** len(Q & set(R)) for R in prs]
    n = m ** m
    lam0, lam1, lam2, tot = (np.zeros(n, dtype=np.int32) for _ in range(4))
    for cR, R in zip(c, prs):
        lam0 += cR * place(R, q1, q1)
        lam1 += place(R, q1, q2)
        lam1 += place(R, q2, q1)
        lam2 += cR * place(R, q2, q2)
        tot += place(R, cR * q1 + q2, q1 + cR * q2)
    nE = 0
    for blk, F, G in extra:
        t = -s * place(R0, F, G)
        if blk == 0:
            lam0 += t
            nE += 1
        else:
            lam2 += t
        tot += t
    cc = np.zeros((m, n), dtype=np.int8)                              # the permanent tensor
    tmp = np.arange(n, dtype=np.int64)
    for _ in range(m):
        d = (tmp % m).astype(np.int8)
        tmp //= m
        for col in range(m):
            cc[col] += (d == col)
    perm = np.all(cc == 1, axis=0).astype(np.int32)
    N = len(prs)
    r0, r1, r2, r3 = not lam0.any(), bool(np.array_equal(lam1, perm)), not lam2.any(), bool(np.array_equal(tot, perm))
    ok = r0 and r1 and r2 and r3 and nE == E and all(x in (1, -1) for x in c)
    if verbose:
        print(f"k = {k}: N = {N}, c_R = (-1)^|R cap {sorted(Q)}| (all +-1: {sorted(set(c))}), E = {nE} extra products on "
              f"{''.join(map(str, R0))}, scalar {-s}")
        print(f"   lam^0  sum_R c_R q1(R) q1(R^c) + extras = 0                  : {r0}")
        print(f"   lam^1  sum_R q1 q2 + q2 q1 = perm_{m} ({int(perm.sum())} = {m}! entries)   : {r1}")
        print(f"   lam^2  sum_R c_R q2(R) q2(R^c) + extras(second block) = 0    : {r2}")
        print(f"   exact  perm_{m} = sum of N + 2E = {N + 2 * nE} split products            : {r3}     (Laplace: {2 * N})")
        print(f"   limit  perm_{m} is a limit of N + E = {N + nE} split products  (lam^0 and lam^1)   [{time.time() - t0:.0f} s]")
        print("ALL EXACT CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return ok


# ----------------------------------------------------------------------------- one pairing
def single_pairing(k, verbose=True):
    """All extra terms on the pairing R0 = {0..k-1}. A matching has type i when i of its pairs lie
    inside R0. For t = 1, 2, ..: the constants c with (A c)_m = 0 on all matchings of type >= t, and
    the pairings on which every such c vanishes, listed by d(R) = min(|R cap R0|, k - |R cap R0|).
    A block of type i costs at least k!/(i! i! (k-2i)!) products. Exact rational arithmetic for
    k <= 4, floating-point ranks of 0/1 matrices above."""
    S = Sub(k)
    R0 = set(range(k))
    typ = np.array([sum(1 for (a, b) in m if a in R0 and b in R0) for m in S.ms])
    dist = np.array([min(len(R0 & set(R)), k - len(R0 & set(R))) for R in S.prs])
    out = {}
    if verbose:
        print(f"k = {k}: N = {S.N}; matchings by type {np.bincount(typ).tolist()}; "
              f"cost of one block of type i: {[math.factorial(k) // (math.factorial(i) ** 2 * math.factorial(k - 2 * i)) for i in range(k // 2 + 1)]}")
    for t in range(1, k // 2 + 1):
        B = S.A[typ >= t]
        if k <= 4:
            dim, forced = forced_zeros_exact(B.tolist())
            free = np.ones(S.N, bool)
            free[forced] = False
        else:
            sv = np.linalg.svd(B.astype(float), full_matrices=True)
            r = int((sv[1] > 1e-9).sum())
            ker = sv[2][r:]
            dim = ker.shape[0]
            free = np.linalg.norm(ker, axis=0) > 1e-9
        out[t] = {int(d): (int(free[dist == d].sum()), int((dist == d).sum())) for d in sorted(set(dist))}
        if verbose:
            print(f"   (A c) = 0 on all types >= {t}: dimension {dim}; pairings where c need not vanish, by d(R): "
                  + ', '.join(f"d={d}: {a} of {b}" for d, (a, b) in out[t].items()))
    return out


# ----------------------------------------------------------------------------- matching sub-model: active sets
def row_action(S):
    """Action of S_2k on the pairings, one row per group element."""
    n = 2 * S.k
    ix = {frozenset(R): i for i, R in enumerate(S.prs)}
    full = frozenset(range(n))
    tab = []
    for g in itertools.permutations(range(n)):
        row = []
        for R in S.prs:
            Rg = frozenset(g[r] for r in R)
            row.append(ix[Rg] if 0 in Rg else ix[full - Rg])
        tab.append(row)
    return np.unique(np.array(tab, dtype=np.int64), axis=0)


def active_sets(k, tmax, verbose=True):
    """Sets T of pairings (up to S_2k) that can be the pairings of nonzero cost: a matching not separated
    by any pairing of T gives the equation (A c)_m = 0 with c supported off T, and no c_R, R not in T,
    may vanish identically on the solutions. Exact rational arithmetic. Returns {t: [admissible T]}."""
    S = Sub(k)
    tab = row_action(S)

    def canon(T):
        im = np.sort(tab[:, list(T)], axis=1)
        key = np.zeros(len(im), dtype=np.int64)
        for j in range(im.shape[1]):
            key = key * 64 + im[:, j]
        return tuple(int(x) for x in im[np.argmin(key)])

    reps, out = [()], {}
    for t in range(1, tmax + 1):
        reps = sorted({canon(T + (p,)) for T in reps for p in range(S.N) if p not in T})
        good = []
        for T in reps:
            cov = S.A[:, list(T)].sum(axis=1) > 0
            rest = [p for p in range(S.N) if p not in T]
            B = S.A[~cov][:, rest]
            dim, forced = forced_zeros_exact(B.tolist()) if B.shape[0] else (len(rest), [])
            if dim > 0 and not forced:
                good.append((T, dim, int(cov.sum())))
        out[t] = good
        if verbose:
            print(f"k = {k}, |T| = {t}: {len(reps)} orbits of sets, {len(good)} admissible")
            for T, dim, ncov in good:
                print(f"     {[S.names[p] for p in T]}: solutions for the constants of dimension {dim}, {ncov} matchings covered")
    return out


# ----------------------------------------------------------------------------- matching sub-model: numerical search
def irreps(S):
    """Real orthogonal matrix forms of the nontrivial irreducibles of S_k, k <= 4: name -> (k!, d, d)."""
    k = S.k
    assert k <= 4
    out = {'sgn': S.sgn.reshape(-1, 1, 1).astype(float)}

    def reduce(P):                               # permutation matrices -> their sum-zero part
        n = P.shape[1]
        Qm = np.linalg.qr(np.eye(n) - 1.0 / n)[0][:, :n - 1]
        return np.einsum('ia,sij,jb->sab', Qm, P, Qm)

    if k >= 3:
        P = np.zeros((S.f, k, k))
        for s, a in enumerate(S.Sk):
            for i in range(k):
                P[s, a[i], i] = 1
        out['std'] = reduce(P)
    if k == 4:
        out['std*sgn'] = out['std'] * S.sgn[:, None, None]
        spl = [frozenset([frozenset([0, i]), frozenset(set(range(4)) - {0, i})]) for i in (1, 2, 3)]
        P = np.zeros((S.f, 3, 3))
        for s, a in enumerate(S.Sk):
            for i, sp_ in enumerate(spl):
                P[s, spl.index(frozenset(frozenset(a[x] for x in blk) for blk in sp_)), i] = 1
        out['22'] = reduce(P)
    assert 1 + sum(R.shape[1] ** 2 for R in out.values()) == S.f
    for R in out.values():
        for s in range(0, S.f, 5):
            for t in range(0, S.f, 7):
                assert np.allclose(R[S.mul[s, t]], R[s] @ R[t])
    return out


class Family:
    """All solutions of the matching sub-model with h_R arbitrary on the pairings of T and constant
    elsewhere, and a smooth surrogate of the cost (log det of the Fourier blocks) on that space."""

    def __init__(self, S, T):
        self.S, self.T = S, list(T)
        self.rest = [p for p in range(S.N) if p not in self.T]
        self.irr = irreps(S)
        f = S.f
        nu = len(self.rest) + len(self.T) * f
        E = np.zeros((S.N * f, nu))
        for j, p in enumerate(self.rest):
            E[p * f:(p + 1) * f, j] = 1
        for j, p in enumerate(self.T):
            E[p * f:(p + 1) * f, len(self.rest) + j * f:len(self.rest) + (j + 1) * f] = np.eye(f)
        L = np.zeros((S.M, S.N * f))
        for p in range(S.N):
            L[S.flag[p], p * f + np.arange(f)] = 1
        sv = np.linalg.svd(L @ E, full_matrices=True)
        self.V = sv[2][int((sv[1] > 1e-9).sum()):].T
        self.dim = self.V.shape[1]
        self.nrest = len(self.rest)

    def unpack(self, theta):
        z = self.V @ (theta / np.linalg.norm(theta)) * np.sqrt(self.V.shape[0])
        return z[:self.nrest], z[self.nrest:].reshape(len(self.T), self.S.f)

    def cost(self, theta, tol=1e-6):
        """(cost, number of pairings whose constant vanishes, description) by thresholding singular values.
        The constant of a pairing is a_R off T and the mean of h_R on T; each vanishing one costs 1."""
        a, h = self.unpack(theta)
        zeros = int((np.abs(a) < tol).sum())
        c, det = zeros, []
        for j in range(len(self.T)):
            cj, desc = 0, []
            if abs(h[j].mean()) < tol:
                cj += 1
                zeros += 1
                desc.append('mean0')
            for nm, R in self.irr.items():
                r = int((np.linalg.svd(np.einsum('s,sab->ab', h[j], R), compute_uv=False) > tol).sum())
                cj += R.shape[1] * r
                if r:
                    desc.append(f"{nm}:{r}")
            c += cj
            if cj:
                det.append(f"{self.S.names[self.T[j]]}[{cj}: {' '.join(desc)}]")
        return c, zeros, '; '.join(det)

    def minimise(self, rng, deltas=(1e-1, 1e-2, 1e-3, 1e-4, 1e-6, 1e-8, 1e-10), maxiter=400):
        import jax
        import jax.numpy as jnp
        import scipy.optimize as so
        jax.config.update('jax_enable_x64', True)
        if not hasattr(self, '_vg'):
            Vj = jnp.array(self.V)
            reps = [jnp.array(R) for R in self.irr.values()]
            nrest, nT, f = self.nrest, len(self.T), self.S.f

            def loss(theta, delta):
                z = Vj @ (theta / jnp.linalg.norm(theta)) * jnp.sqrt(Vj.shape[0])
                a, h = z[:nrest], z[nrest:].reshape(nT, f)
                mean = jnp.mean(h, axis=1)
                val = -0.5 * jnp.sum(jnp.log(a * a + delta)) - 0.5 * jnp.sum(jnp.log(mean * mean + delta))
                for R in reps:
                    d = R.shape[1]
                    hat = jnp.einsum('ps,sab->pab', h, R)
                    val = val + 0.5 * d * jnp.sum(jnp.linalg.slogdet(jnp.einsum('pab,pcb->pac', hat, hat) + delta * jnp.eye(d))[1])
                return val

            self._vg = jax.jit(jax.value_and_grad(loss))
        theta = rng.standard_normal(self.dim)
        for dl in deltas:
            def fun(x, dl=dl):
                v, g = self._vg(jnp.array(x), dl)
                return float(v), np.asarray(g, dtype=float)
            theta = so.minimize(fun, theta, jac=True, method='L-BFGS-B', options=dict(maxiter=maxiter)).x
            theta = theta / np.linalg.norm(theta)
        return theta


def solve(k, active, restarts, seed=0, verbose=True):
    """Rank-surrogate search in the matching sub-model. Returns (best cost with no vanishing constant, best cost)."""
    S = Sub(k)
    T = list(range(S.N)) if active == 'all' else [S.names.index(x) for x in active.split(',')]
    F = Family(S, T)
    rng = np.random.default_rng(seed)
    best_nz, best = None, None
    if verbose:
        print(f"k = {k}: active pairings {'all' if active == 'all' else active}; solution space of dimension {F.dim}", flush=True)
    for r in range(restarts):
        t0 = time.time()
        th = F.minimise(rng)
        c, zeros, desc = F.cost(th)
        best = c if best is None else min(best, c)
        if zeros == 0:
            best_nz = c if best_nz is None else min(best_nz, c)
        if verbose:
            print(f"   restart {r}: cost {c} ({zeros} vanishing constants)  {desc[:300]}  [{time.time() - t0:.0f} s]", flush=True)
    if verbose:
        print(f"best cost {best}; best cost with no vanishing constant: {best_nz}")
    return best_nz, best


if __name__ == '__main__':
    args = sys.argv[1:]
    mode = args[0] if args else 'check'
    if mode == 'check':
        raise SystemExit(0 if check_formulation() else 1)
    if mode == 'char':
        raise SystemExit(0 if all(char_check(k) for k in ([int(args[1])] if len(args) > 1 else range(2, 7))) else 1)
    if mode == 'verify':
        raise SystemExit(0 if verify_tensors(int(args[1]) if len(args) > 1 else 4) else 1)
    if mode == 'single':
        single_pairing(int(args[1]))
    elif mode == 'active':
        active_sets(int(args[1]), int(args[2]) if len(args) > 2 else 3)
    elif mode == 'solve':
        solve(int(args[1]), args[2] if len(args) > 2 else 'all', int(args[3]) if len(args) > 3 else 5,
              int(args[4]) if len(args) > 4 else 0)
    else:
        print(__doc__)
