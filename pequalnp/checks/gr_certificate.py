"""Exact certificates that GR(perm_m) = m, i.e. codim Z_m = m, for m = 3, 4, 5.

Z_m = { B in C^{(m-1) x m} : all m maximal subpermanents of B vanish }  (a cone, m equations).
If ONE m-dimensional linear subspace L of C^{(m-1) x m} meets Z_m only in 0, then dim Z_m <= m(m-1) - m
(projective dimension theorem), hence codim Z_m = m.
L = { B(t) : t in C^m } with integer coefficients.  Phi_c(t) = perm(B(t) without column c): m forms of
degree m-1 in m variables.  They have no common zero t != 0 over C  <=>  the ideal contains every monomial of
degree N = m(m-2)+1 (Macaulay bound)  <=  the Macaulay matrix in degree N has full column rank over Q
<=  it has full column rank modulo one prime p.   All arithmetic is exact (integers mod p).

  m = 3, 5: partial circulant  B_ij = t_{(i+j) mod m}  (Z_m-graded, the matrix splits into m blocks)
  m = 4   : rows t, A2 t, A3 t with fixed small integer matrices (the circulant fails for even m)
"""
import itertools, sys
from math import comb
import numpy as np

P = 32003

def poly_mul_add(acc, f, g_mon, coef=1):
    for mon, c in f.items():
        key = tuple(a + b for a, b in zip(mon, g_mon))
        acc[key] = (acc.get(key, 0) + c * coef)

def linear_form(vec, m):
    """dict monomial->coef for sum_j vec[j] t_j"""
    out = {}
    for j, c in enumerate(vec):
        if c:
            e = [0] * m; e[j] = 1
            out[tuple(e)] = c
    return out

def pmul(f, g):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            k = tuple(a + b for a, b in zip(m1, m2))
            out[k] = out.get(k, 0) + c1 * c2
    return {k: v for k, v in out.items() if v}

def subperm_polys(rows, m):
    """rows: list of m-1 lists of linear forms (entries B_ij(t)); returns Phi_c as polynomial dicts (exact ints)."""
    phis = []
    for c in range(m):
        cols = [j for j in range(m) if j != c]
        acc = {}
        for sig in itertools.permutations(cols):
            term = {tuple([0] * m): 1}
            for r in range(m - 1):
                term = pmul(term, rows[r][sig[r]])
                if not term:
                    break
            for k, v in term.items():
                acc[k] = acc.get(k, 0) + v
        phis.append({k: v for k, v in acc.items() if v})
    return phis

def monomials(m, d):
    if m == 1:
        yield (d,); return
    for a in range(d + 1):
        for rest in monomials(m - 1, d - a):
            yield (a,) + rest

def rank_mod_p(M, p=P):
    M = M % p
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        if r == rows:
            break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        below = np.nonzero(M[r + 1:, c])[0] + r + 1
        if below.size:
            M[below] = (M[below] - np.outer(M[below, c], M[r])) % p
        r += 1
    return r

def certificate(m, rows, grading=None):
    """grading: None, or function monomial -> element of Z_m (the Phi_c must be homogeneous for it)."""
    phis = subperm_polys(rows, m)
    d = m - 1
    N = m * (m - 2) + 1
    assert all(sum(k) == d for f in phis for k in f)
    blocks = [None] if grading is None else list(range(m))
    ok = True
    total_cols = 0
    for g in blocks:
        colmons = [mon for mon in monomials(m, N) if grading is None or grading(mon) == g]
        index = {mon: i for i, mon in enumerate(colmons)}
        rws = []
        for f in phis:
            if grading is not None:
                degs = {grading(k) for k in f}
                assert len(degs) == 1, "Phi_c not homogeneous for the grading"
                fd = degs.pop()
            for mult in monomials(m, N - d):
                if grading is not None and (grading(mult) + fd) % m != g:
                    continue
                row = {}
                for k, v in f.items():
                    key = tuple(a + b for a, b in zip(k, mult))
                    row[index[key]] = v % P
                rws.append(row)
        M = np.zeros((len(rws), len(colmons)), dtype=np.int64)
        for i, row in enumerate(rws):
            for j, v in row.items():
                M[i, j] = v
        rk = rank_mod_p(M)
        total_cols += len(colmons)
        print(f"   m={m} block {g}: Macaulay matrix {M.shape[0]} x {M.shape[1]} in degree {N}, rank mod {P} = {rk}"
              f"  -> {'full column rank' if rk == len(colmons) else 'NOT full'}", flush=True)
        ok &= (rk == len(colmons))
    assert total_cols == comb(N + m - 1, m - 1)
    print(f"m={m}: every monomial of degree {N} lies in the ideal of the subpermanents restricted to L: {ok}"
          f"   => {'GR(perm_%d) = %d  (codim Z_m = m), certified' % (m, m) if ok else 'no certificate from this L'}", flush=True)
    return ok

def circulant_rows(m):
    return [[linear_form([1 if k == (i + j) % m else 0 for k in range(m)], m) for j in range(m)] for i in range(m - 1)]

def krylov_rows(m, mats):
    rows = []
    for A in mats:
        rows.append([linear_form(list(A[j]), m) for j in range(m)])     # row = A t, entry j = sum_k A[j][k] t_k
    return rows

if __name__ == '__main__':
    which = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    if 3 in which:
        certificate(3, circulant_rows(3), grading=lambda mon: sum(i * e for i, e in enumerate(mon)) % 3)
    if 4 in which:
        rng = np.random.default_rng(12345)
        for attempt in range(5):
            mats = [np.eye(4, dtype=int)] + [rng.integers(-3, 4, size=(4, 4)) for _ in range(2)]
            print("   m=4 trial matrices A2, A3 =", [A.tolist() for A in mats[1:]])
            if certificate(4, krylov_rows(4, mats)):
                break
    if 5 in which:
        certificate(5, circulant_rows(5), grading=lambda mon: sum(i * e for i, e in enumerate(mon)) % 5)
