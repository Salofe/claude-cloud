"""Exact certificate that an m-dimensional linear space L of (m-1) x m matrices meets
Z_m = {B : all m maximal subpermanents of B vanish} only in 0.  Consequence: codim Z_m >= m.

L = {B(t) : t in C^m},  B_ij(t) = f_t(m*i + j),  f_t(u) = t_0 + t_1 u + .. + t_{m-1} u^{m-1}
(the values of a polynomial of degree < m at the nodes 0, 1, .., m(m-1)-1, written row by row).
Phi_c(t) = perm(B(t) without column c),  c = 0..m-1 :  m forms of degree m-1 in m variables, integer coefficients.

Method: Hilbert function of F_p[t]/(Phi_0..Phi_{m-1}) degree by degree through the inverse system of the ideal.
  I_D^perp = {phi in (R_D)^* : phi(I_D) = 0},  h_D = dim I_D^perp = dim (R/I)_D.
  For D > m-1:  I_D = sum_i t_i I_{D-1},  so  I_D^perp = {phi : t_i.phi in I_{D-1}^perp for all i},
  where (t_i.phi)(g) = phi(t_i g);  phi -> (t_i.phi)_i identifies I_D^perp with the tuples (psi_i) in
  (I_{D-1}^perp)^m with  t_j.psi_i = t_i.psi_j  (i < j).  So h_D is the nullity of a matrix built from the
  contraction matrices of the previous degree; only the quotient (total dimension (m-1)^m) is stored.
If h_N = 0 for N = m(m-2)+1 then the Macaulay matrix of degree N has full column rank mod p, hence over Q,
every monomial of degree N lies in the ideal, and the Phi_c have no common zero t != 0 over C.
All arithmetic is exact: integers mod p held in float64, every intermediate value below 2^53.
"""
import itertools, sys, time
import numpy as np
from scipy.linalg.blas import dgemm

P = 32003
for _a in sys.argv[1:]:
    if _a.startswith('--prime='):
        P = int(_a.split('=')[1])

# ---------------------------------------------------------------- linear algebra mod p (float64, exact)
def echelon(A, p=P, bs=64):
    """A: float64 Fortran-ordered integer-valued matrix.  Row echelon form mod p without row exchanges, in place.
    Returns (pivrows, pivcols): row pivrows[k] is the k-th echelon row (unit pivot in column pivcols[k])."""
    R, C = A.shape
    done = np.zeros(R, dtype=bool)
    pivrows, pivcols = [], []
    c0 = 0
    while c0 < C and len(pivrows) < R:
        c1 = min(C, c0 + bs)
        act = np.flatnonzero(~done)
        S = np.remainder(A[act, c0:c1], p)
        b = c1 - c0
        Mloc = np.zeros((len(act), b))
        ldone = np.zeros(len(act), dtype=bool)
        newpiv, invs = [], []
        for cc in range(b):
            cand = np.flatnonzero((S[:, cc] != 0) & ~ldone)
            if cand.size == 0:
                continue
            q = int(cand[0])
            inv = pow(int(S[q, cc]), p - 2, p)
            S[q, cc:] = np.remainder(S[q, cc:] * inv, p)
            mult = S[:, cc].copy(); mult[ldone] = 0; mult[q] = 0
            Mloc[:, len(newpiv)] = mult
            nzr = np.flatnonzero(mult)
            if nzr.size:
                S[nzr, cc:] = np.remainder(S[nzr, cc:] - np.outer(mult[nzr], S[q, cc:]), p)
            ldone[q] = True
            newpiv.append(q); invs.append(inv); pivcols.append(c0 + cc)
        A[act, c0:c1] = S
        k = len(newpiv)
        if k:
            prow = act[newpiv]
            if c1 < C:
                T = A[:, c1:]
                U = np.empty((k, C - c1))
                for a in range(k):
                    row = np.remainder(T[prow[a], :], p)
                    if a:
                        row = np.remainder(row - Mloc[newpiv[a], :a] @ U[:a], p)
                    U[a] = np.remainder(row * invs[a], p)
                Mfull = np.zeros((R, k), order='F')
                Mfull[act] = Mloc[:, :k]
                Mfull[prow] = 0
                out = dgemm(-1.0, Mfull, U, beta=1.0, c=T, overwrite_c=1)
                if not np.shares_memory(out, A):
                    A[:, c1:] = out
                A[prow, c1:] = U
            done[prow] = True
            pivrows.extend(int(x) for x in prow)
        c0 = c1
    return pivrows, pivcols

def nullspace(A, p=P):
    """Basis (columns) of {x : A x = 0 mod p};  A (float64, Fortran order) is destroyed."""
    R, C = A.shape
    if R == 0:
        return np.eye(C)
    pivrows, pivcols = echelon(A, p)
    rank = len(pivrows)
    pset = set(pivcols)
    free = [c for c in range(C) if c not in pset]
    K = np.zeros((C, len(free)))
    if free:
        K[free, np.arange(len(free))] = 1
        if rank:
            U = A[pivrows]
            UF = np.remainder(U[:, free], p)
            UP = np.remainder(U[:, pivcols], p)
            del U
            V = np.zeros((rank, len(free)))
            blk = 128
            for hi in range(rank, 0, -blk):
                lo = max(0, hi - blk)
                W = UF[lo:hi].copy()
                if hi < rank:
                    W += np.remainder(UP[lo:hi, hi:] @ V[hi:], p)
                for k in range(hi - 1, lo - 1, -1):
                    acc = W[k - lo]
                    if k < hi - 1:
                        acc = acc + UP[k, k + 1:hi] @ V[k + 1:hi]
                    V[k] = np.remainder(-acc, p)
            K[pivcols, :] = V
    return K

def rank_mod_p(M, p=P):
    A = np.asfortranarray(np.remainder(M, p), dtype=np.float64)
    return len(echelon(A, p)[0])

# ---------------------------------------------------------------- polynomials
def monomials(nv, d):
    if nv == 1:
        yield (d,); return
    for a in range(d + 1):
        for rest in monomials(nv - 1, d - a):
            yield (a,) + rest

def pmul(f, g):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            k = tuple(a + b for a, b in zip(m1, m2))
            out[k] = out.get(k, 0) + c1 * c2
    return {k: v for k, v in out.items() if v}

def subperm_polys(m, entry):
    """entry(i, j) = list of the m integer coefficients of the linear form B_ij(t).  Returns the m maximal
    subpermanents (column c omitted) as dicts monomial -> integer (exact Python integers)."""
    one = tuple([0] * m)
    lin = [[{tuple(1 if a == k else 0 for a in range(m)): int(v) for k, v in enumerate(entry(i, j)) if v}
            for j in range(m)] for i in range(m - 1)]
    phis = []
    for c in range(m):
        cols = [j for j in range(m) if j != c]
        # dynamic programme over subsets of columns (rows taken in order)
        dp = {0: {one: 1}}
        for i in range(m - 1):
            nd = {}
            for mask, f in dp.items():
                for a, j in enumerate(cols):
                    if not mask >> a & 1:
                        g = pmul(f, lin[i][j])
                        tgt = nd.setdefault(mask | 1 << a, {})
                        for k, v in g.items():
                            tgt[k] = tgt.get(k, 0) + v
            dp = nd
        f = dp[(1 << (m - 1)) - 1]
        phis.append({k: v for k, v in f.items() if v})
    return phis

# ---------------------------------------------------------------- Hilbert function through the dual space
def hilbert_function(m, phis, Dmax=None, p=P, verbose=True):
    d = m - 1
    Dmax = Dmax or m * (m - 2) + 1
    unit = [tuple(1 if a == i else 0 for a in range(m)) for i in range(m)]
    mons_lo = list(monomials(m, d - 1))
    mons_d = list(monomials(m, d)); idx_d = {mon: i for i, mon in enumerate(mons_d)}
    E = np.zeros((len(phis), len(mons_d)), order='F')
    for a, f in enumerate(phis):
        assert all(sum(k) == d for k in f)
        for k, v in f.items():
            E[a, idx_d[k]] = v % p
    K = nullspace(E, p)
    X = []                                   # X[i] : I_D^perp -> I_{D-1}^perp, contraction with t_i
    for i in range(m):
        rows = [idx_d[tuple(x + y for x, y in zip(mon, unit[i]))] for mon in mons_lo]
        X.append(K[rows, :].copy())
    H = {d - 1: len(mons_lo), d: K.shape[1]}
    if verbose:
        print(f"   D={d}: h = {H[d]}", flush=True)
    pairs = [(i, j) for i in range(m) for j in range(i + 1, m)]
    for D in range(d + 1, Dmax + 1):
        t0 = time.time()
        hp, hpp = H[D - 1], H[D - 2]
        A = np.zeros((len(pairs) * hpp, m * hp), order='F')
        for a, (i, j) in enumerate(pairs):       # t_j.psi_i - t_i.psi_j = 0
            A[a * hpp:(a + 1) * hpp, i * hp:(i + 1) * hp] = X[j]
            A[a * hpp:(a + 1) * hpp, j * hp:(j + 1) * hp] = np.remainder(-X[i], p)
        shape = A.shape
        K = nullspace(A, p)
        del A
        Xn = [K[i * hp:(i + 1) * hp, :].copy() for i in range(m)]
        for i, j in pairs:                       # every kernel vector is verified
            assert not np.remainder(X[j] @ Xn[i] - X[i] @ Xn[j], p).any()
        H[D] = K.shape[1]
        X = Xn
        if verbose:
            print(f"   D={D}: h = {H[D]}   (matrix {shape[0]} x {shape[1]}, {time.time()-t0:.1f} s)", flush=True)
        if H[D] == 0:
            for D2 in range(D + 1, Dmax + 1):
                H[D2] = 0
            break
    return H

def ci_hilbert(m):
    c = np.array([1], dtype=object)
    for _ in range(m):
        c = np.convolve(c, np.array([1] * (m - 1), dtype=object))
    return [int(x) for x in c]

def macaulay_h(m, phis, D, p=P):
    """h_D directly: (#monomials of degree D) - rank of the Macaulay matrix in degree D (for cross-checks)."""
    d = m - 1
    cols = list(monomials(m, D)); index = {mon: i for i, mon in enumerate(cols)}
    mults = list(monomials(m, D - d))
    M = np.zeros((len(mults) * len(phis), len(cols)), order='F')
    r = 0
    for f in phis:
        for mu in mults:
            for k, v in f.items():
                M[r, index[tuple(a + b for a, b in zip(k, mu))]] = v % p
            r += 1
    return len(cols) - len(echelon(M, p)[0])

def poly_eval_entry(m):
    return lambda i, j: [(m * i + j) ** k for k in range(m)]

def run(m, entry, label, crosscheck=()):
    t0 = time.time()
    phis = subperm_polys(m, entry)
    print(f"m={m}  [{label}]  {len(phis)} forms of degree {m-1}, numbers of terms {[len(f) for f in phis]}, prime {P}", flush=True)
    H = hilbert_function(m, phis)
    ci = ci_hilbert(m)
    N = m * (m - 2) + 1
    same = all(H[D] == (ci[D] if D < len(ci) else 0) for D in range(m - 1, N + 1))
    print(f"   Hilbert function = coefficients of (1+z+..+z^{m-2})^{m} in every degree {m-1}..{N}: {same};  h_{N} = {H[N]}", flush=True)
    ok = True
    for D in crosscheck:
        hd = macaulay_h(m, phis, D)
        print(f"   cross-check, Macaulay matrix in degree {D}: h = {hd}  ({'agrees' if hd == H[D] else 'DISAGREES'})", flush=True)
        ok &= (hd == H[D])
    cert = ok and H[N] == 0
    print(f"m={m}: L meets Z_{m} only in 0, hence codim Z_{m} >= {m}: {'CERTIFIED' if cert else 'NO CERTIFICATE'}"
          f"   ({time.time()-t0:.1f} s)", flush=True)
    return cert, H

if __name__ == '__main__':
    which = [int(a) for a in sys.argv[1:] if not a.startswith('-')] or [3, 4, 5]
    for m in which:
        N = m * (m - 2) + 1
        cc = range(m, N + 1) if m <= 5 else (range(6, 12) if m == 6 else ())
        run(m, poly_eval_entry(m), "B_ij = f(m*i+j), deg f < m", crosscheck=cc)
