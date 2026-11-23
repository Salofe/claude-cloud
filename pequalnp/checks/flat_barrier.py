"""How far can flattening ranks go against mixed k-split products of perm_2k?  (notes/next_steps.md, item A1)

Method under test ("restricted flattening"): restrict row i to a generic subspace of dimension d_i
(1 <= d_i <= m = 2k; d_i = 1 means substituting a fixed vector), pick a set T of rows, and compare
ranks of the flattening (rows in T | rows not in T).

  * a split product F(S) G(S^c) has rank <= rho(S) = min(D(S&T), D(S-T)) * min(D(S^c&T), D(S^c-T)),
    D(X) = prod_{i in X} d_i, with equality for generic F, G (Kronecker product of two generic flattenings);
  * the restricted permanent has some rank R(d, T) <= Rbar = min(D(T), D(T^c), C(m,t'), C(m,t'')),
    t', t'' = numbers of rows with d_i > 1 in T, T^c.  R is computed numerically (--true) or replaced by Rbar.

Every (d, T) gives the necessary condition  sum_pi n_pi * rho(pi) >= R  on the numbers n_pi of terms on
each pairing pi.  The best lower bound this method can give on the total number of terms, for terms
allowed on a set P of pairings with multiplicities <= cap_pi, is the integer program
        min sum n_pi   s.t. all conditions, 0 <= n_pi <= cap_pi.
Printed: its LP relaxation (rows capped at R, which is equivalent for integers) and the integer optimum.

usage: python3 flat_barrier.py K [--true] [--dims 1,2,4,8] [--equal]
"""
import argparse, itertools, math, sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

ap = argparse.ArgumentParser()
ap.add_argument('k', type=int)
ap.add_argument('--true', action='store_true', help='use numerically computed ranks of the restricted permanent')
ap.add_argument('--dims', default='')
ap.add_argument('--equal', action='store_true', help='all rows get the same dimension d (plain flattening after restriction)')
args = ap.parse_args()
k = args.k; m = 2 * k
dims = [int(x) for x in args.dims.split(',')] if args.dims else list(range(1, m + 1))
rows = list(range(m))
pairings = [S for S in itertools.combinations(rows, k) if 0 in S]
N = len(pairings)
Sm = np.zeros((N, m), bool)
for i, S in enumerate(pairings):
    Sm[i, list(S)] = True

_perm = None
def perm_tensor():
    global _perm
    if _perm is None:
        _perm = np.zeros((m,) * m)
        for p in itertools.permutations(range(m)):
            _perm[p] = 1
    return _perm

_cache = {}
def true_rank(d, T):
    """rank of the (T | T^c) flattening of perm_m with row i restricted to a random d_i-dimensional subspace"""
    Tc = [i for i in rows if i not in T]
    key = (tuple(sorted(d[i] for i in T)), tuple(sorted(d[i] for i in Tc)))
    key = min(key, key[::-1])
    if key in _cache:
        return _cache[key]
    rng = np.random.default_rng(hash(key) % (2 ** 31))
    X = perm_tensor()
    for i in rows:
        if d[i] < m:
            B = rng.standard_normal((d[i], m))
            X = np.moveaxis(np.tensordot(B, X, axes=(1, i)), 0, i)
    X = np.transpose(X, list(T) + Tc).reshape(int(np.prod([d[i] for i in T])), -1)
    s = np.linalg.svd(X, compute_uv=False)
    r = int((s > 1e-9 * s[0]).sum())
    _cache[key] = r
    return r

def all_constraints():
    """returns list of (a (N,) capped row, R, d, T)"""
    out = {}
    if args.equal:
        dvecs = np.array([[d] * m for d in dims])
    else:
        dvecs = np.array(list(itertools.product(dims, repeat=m)))
    logd = dvecs.astype(float)
    for t in range(1, k + 1):
        for T in itertools.combinations(rows, t):
            if t == k and 0 not in T:
                continue
            Tm = np.zeros(m, bool); Tm[list(T)] = True
            DT = np.prod(np.where(Tm, dvecs, 1), axis=1).astype(float)
            DTc = np.prod(np.where(~Tm, dvecs, 1), axis=1).astype(float)
            t1 = (dvecs[:, Tm] > 1).sum(1); t2 = (dvecs[:, ~Tm] > 1).sum(1)
            comb = np.array([math.comb(m, j) for j in range(m + 1)], float)
            Rbar = np.minimum(np.minimum(DT, DTc), np.minimum(comb[t1], comb[t2]))
            rho = np.empty((len(dvecs), N))
            for i in range(N):
                S = Sm[i]
                x = np.prod(np.where(S & Tm, dvecs, 1), axis=1); y = np.prod(np.where(S & ~Tm, dvecs, 1), axis=1)
                x2 = np.prod(np.where(~S & Tm, dvecs, 1), axis=1); y2 = np.prod(np.where(~S & ~Tm, dvecs, 1), axis=1)
                rho[:, i] = np.minimum(x, y) * np.minimum(x2, y2)
            keep = np.where(rho.min(1) < Rbar)[0]      # otherwise a single term anywhere satisfies it
            for j in keep:
                R = true_rank(dvecs[j], T) if args.true else Rbar[j]
                a = np.minimum(rho[j] / R, 1.0)
                key = tuple(np.round(a, 9))
                if key not in out:
                    out[key] = (a, R, tuple(dvecs[j]), T)
    return list(out.values())

cons = all_constraints()
A = np.array([c[0] for c in cons])
print(f"k={k} m={m} N={N} pairings; dims {dims}{' (equal)' if args.equal else ''}; "
      f"{'TRUE ranks of the restricted permanent' if args.true else 'upper bound Rbar for the permanent'}; "
      f"{len(cons)} distinct non-trivial conditions", flush=True)

def solve(cap, integer, label):
    res = milp(np.ones(N), constraints=LinearConstraint(A, 1 - 1e-9, np.inf), bounds=Bounds(0, cap),
               integrality=np.ones(N) if integer else np.zeros(N))
    if res.status != 0:
        print(f"  {label}: infeasible (the method excludes this family outright)")
        return None
    n = res.x
    print(f"  {label}: {'integer' if integer else 'LP'} optimum {res.fun:.4f}"
          + (f"   n = {dict((''.join(map(str, pairings[i])), int(round(n[i]))) for i in range(N) if n[i] > 0.5)}" if integer else ''))
    if integer:
        slack = A @ np.round(n) - 1
        tight = np.argsort(slack)[:3]
        for j in tight:
            print(f"      tight condition: d={cons[j][2]} T={cons[j][3]} R={cons[j][1]:.0f} slack={slack[j]:.3f}")
    return n

big = np.full(N, 10 * m * k)
print("(i) terms allowed on all pairings")
solve(big, False, 'all pairings')
solve(big, True, 'all pairings')
cyc = np.zeros(N)
for i in range(k):
    S = tuple(sorted((i + j) % m for j in range(k)))
    if 0 not in S:
        S = tuple(r for r in rows if r not in S)
    cyc[pairings.index(S)] = 10 * m * k
print(f"(iii) terms allowed only on the {k} cyclic-interval pairings")
solve(cyc, True, 'cyclic intervals')
one = np.zeros(N); one[0] = 10 * m * k * 100
print("(iv) terms allowed only on one pairing (Laplace; the method must give C(m,k) here)")
solve(one, True, 'one pairing')
if k == 3:
    mult = {'012': 3, '013': 3, '024': 2}
    cap = np.array([mult.get(''.join(map(str, S)), 1) for S in pairings], float)
    print("(ii) the multiset of pairings of the 15-term identity (012 x3, 013 x3, 024 x2, the other seven x1)")
    solve(cap, True, '15-term multiset')
    w = np.round(cap)
    print(f"      smallest slack of the 15-term multiset itself: {(A @ w - 1).min():.3f}")
