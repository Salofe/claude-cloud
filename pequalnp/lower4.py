"""Lower bounds for mixed split decompositions of the 4 x 4 permanent: computations.

P is the 4 x 4 permanent as a tensor in (C^4)^{(x)4}: P[j0, j1, j2, j3] = 1 when (j0..j3) is a
permutation. A split product for the pairing 01|23 is F[j0, j1] * G[j2, j3]; for 02|13 it is
F[j0, j2] * G[j1, j3]; for 03|12 it is F[j0, j3] * G[j1, j2].

Proved in Lean (lean/PvsNP/FourByFourLower.lean, no sorry, standard axioms only):
  * gamma_not_split, twoBlock_no_211, twoBlock_five_le: the two-block model needs five terms.
  * five_le_card_of_permanent_eq_sum_split / permanent_ne_sum_four_isSplit: P is not a sum of
    four split products, whatever the pairings (any field of characteristic zero).
  * not_tendsto_sum_split_four / not_tendsto_sum_four_isSplit(_complex): P is not a LIMIT of
    sums of four split products, over R and over C.
This script checks the ingredients of those proofs independently (exactly with sympy, and
numerically), and collects the numerical evidence on decompositions with FIVE terms.

The argument. Fix row 0 to the all-ones vector. P becomes the 3-tensor
  E(w, x, y) = sum over distinct (i, j, k) of w_i x_j y_k,
and a split product becomes (linear form in ONE of w, x, y) times (bilinear form in the other
two): a slice. A sum of split products with n1, n2, n3 terms of the three pairings therefore
vanishes on U1 x U2 x U3 for subspaces of codimension <= n1, n2, n3; this is a closed
condition (Grassmannians are compact), so it also holds for limits.
For u in C^4 let B_u = E(u, ., .): the symmetric matrix with zero diagonal and entries
(B_u)_{ab} = u_c + u_d, {c, d} the complement of {a, b}.
  LEMMA R.  rank B_u <= 1 only for u = 0, and rank B_u <= 2 exactly on ten lines:
            u = e_a - e_b (six) and u = 1 - 2 e_a (four).
If E = 0 on U1 x U2 x U3 then rank B_u <= codim U2 + codim U3 for every u in U1. With
(n1, n2, n3) a permutation of (2,1,1) or (2,2,0) some U_i has dimension >= 2 while the other
two codimensions add up to <= 2: a plane inside ten lines, impossible. With (3,1,0) some U_i
is nonzero while the other codimensions add up to <= 1: impossible. (4,0,0) is excluded by
the flattening rank 6 of P.

Modes:
  python3 lower4.py t1       exact checks for the two-block model (sympy)
  python3 lower4.py lemma    exact proof of LEMMA R by branching on linear factors (sympy)
  python3 lower4.py slices   numerical minimum of |E restricted to U1 x U2 x U3| over complex
                             subspaces of given codimensions (positive = no slice decomposition,
                             even in the limit)
  python3 lower4.py fit N [restarts] [seed]
                             Levenberg-Marquardt fits of P by N mixed split products, every
                             pattern of pairings: residual, and size of the terms
                             (N = 4: obstruction; N = 5: limit versus exact)
  python3 lower4.py track    for 5 terms: residual against the size of the terms along one fit
                             (a limit decomposition has residual -> 0 only while terms blow up)
  python3 lower4.py p410     pattern (4,1,0) is not even a limit: exact and numerical checks
  python3 lower4.py t3       symbolic identities used in the proof that pattern (3,1,1) has no
                             EXACT decomposition
"""
import itertools
import sys

import numpy as np

M = 4
PAIRINGS = {'01': ((0, 1), (2, 3)), '02': ((0, 2), (1, 3)), '03': ((0, 3), (1, 2))}


def perm_tensor():
    T = np.zeros((M,) * 4)
    for p in itertools.permutations(range(M)):
        T[p] = 1
    return T


# ---------------------------------------------------------------------------------------------
# T1: the two-block model, exact
# ---------------------------------------------------------------------------------------------

def t1():
    import sympy as sp
    c1, c2, c3 = sp.symbols('c1 c2 c3')
    s = sp.Matrix([[0, 1], [1, 0]])
    idx = list(itertools.product(range(2), repeat=4))

    def gamma(j):
        a, b, c, d = j
        return c1 * s[a, b] * s[c, d] + c2 * s[a, c] * s[b, d] + c3 * s[a, d] * s[b, c]

    print("Gamma(c) = c1 s(01)s(23) + c2 s(02)s(13) + c3 s(03)s(12) on (C^2)^{(x)4}")
    print("nonzero entries:", {''.join(map(str, j)): gamma(j) for j in idx if gamma(j) != 0})
    for name, (left, right) in PAIRINGS.items():
        rows = list(itertools.product(range(2), repeat=2))
        Mx = sp.zeros(4, 4)
        for i, (p, q) in enumerate(rows):
            for k, (r, t) in enumerate(rows):
                j = [0] * 4
                j[left[0]], j[left[1]], j[right[0]], j[right[1]] = p, q, r, t
                Mx[i, k] = gamma(tuple(j))
        minors = set()
        for r2 in itertools.combinations(range(4), 2):
            for k2 in itertools.combinations(range(4), 2):
                mn = sp.expand(Mx.extract(list(r2), list(k2)).det())
                if mn != 0:
                    minors.add(mn)
        # rank <= 1  <=>  all 2 x 2 minors vanish. Show that this forces c1 c2 c3 = 0:
        t = sp.symbols('t')
        G = sp.groebner(list(minors) + [1 - t * c1 * c2 * c3], t, c1, c2, c3, order='lex')
        print(f"pairing {name}: flattening\n{Mx}\n  2x2 minors: {sorted(map(str, minors))}")
        print(f"  ideal(minors, 1 - t c1 c2 c3) = (1): {list(G.exprs) == [1]}"
              "   [so a single split product of this pairing never cancels Gamma(c) with all c_i != 0]")
    # The (2,1,1) case of the model, pairing 01 with two terms. Proof identities:
    #   Gram 3 x 3 determinant of two-dimensional vectors vanishes; Cauchy-Binet in dimension 2.
    v = sp.symbols('p1 p2 x1 x2 q1 q2 r1 r2 y1 y2 s1 s2')
    p1, p2, x1, x2, q1, q2, r1, r2, y1, y2, s1, s2 = v
    dot = lambda a, b: a[0] * b[0] + a[1] * b[1]
    U = [(p1, p2), (x1, x2), (q1, q2)]
    W = [(r1, r2), (y1, y2), (s1, s2)]
    gram = sp.Matrix(3, 3, lambda i, k: dot(U[i], W[k]))
    print("Gram determinant of 3 + 3 vectors in dimension 2 vanishes:", sp.expand(gram.det()) == 0)
    cb = dot(U[0], W[0]) * dot(U[1], W[1]) - dot(U[0], W[1]) * dot(U[1], W[0]) \
        - (p1 * x2 - p2 * x1) * (r1 * y2 - r2 * y1)
    print("Cauchy-Binet <a,c><b,d> - <a,d><b,c> = det(a,b) det(c,d):", sp.expand(cb) == 0)
    print("""Proof of the (2,1,1) case (Lean: twoBlock_core). Two terms of pairing 01, vectors in C^2
indexed by the term: x = F1[.,0,1], x' = F1[.,1,0], y = G1[.,0,1], y' = G1[.,1,0], z = G2[.,0,1],
w = F2[.,0,1], p = F1[.,0,0], p' = F1[.,1,1], r = G1[.,0,0], r' = G1[.,1,1].
 (2,0)-part: sum_v F1_v (x) G1_v = -(c2 v_02 + c3 v_03) gives the Gram matrix of (p, x, p') against
 (r', y, r) = diag(-(c2+c3), -c3, -(c2+c3)); its determinant -(c2+c3)^2 c3 must vanish: c3 = -c2.
 Then <x,y> = <x',y'> = c2, <x,y'> = <x',y> = -c2, and the (1,1)-part gives <x,z> = <x',z> = 1,
 <w,y> = <w,y'> = 1. Cauchy-Binet three times:
   det(x,x') det(y,y') = c2^2 - c2^2 = 0,   det(x,x') det(z,y) = -2 c2,   det(x,w) det(y,y') = 2 c2,
 so -4 c2^2 = det(x,x') det(y,y') det(z,y) det(x,w) = 0, contradicting c2 != 0.""")


# ---------------------------------------------------------------------------------------------
# LEMMA R, exact
# ---------------------------------------------------------------------------------------------

def lemma():
    import sympy as sp
    u = sp.symbols('u0:4')
    pairs = list(itertools.combinations(range(4), 2))

    def comp(a, b):
        return [i for i in range(4) if i not in (a, b)]

    B = sp.zeros(4, 4)
    for a, b in pairs:
        c, d = comp(a, b)
        B[a, b] = B[b, a] = u[c] + u[d]
    E = np.einsum('a,abcd->bcd', np.ones(4), perm_tensor())
    Bnum = sp.Matrix(4, 4, lambda j, k: sum(int(E[i, j, k]) * u[i] for i in range(4)))
    print("B_u = E(u,.,.) has entries u_c + u_d off the diagonal:", (B - Bnum).expand() == sp.zeros(4, 4))
    minors3 = []
    for r3 in itertools.combinations(range(4), 3):
        for k3 in itertools.combinations(range(4), 3):
            minors3.append(sp.factor(B.extract(list(r3), list(k3)).det()))
    # principal minors are 2 * (product of the three entries of a triangle)
    for r3 in itertools.combinations(range(4), 3):
        a, b, c = r3
        assert sp.expand(B.extract(list(r3), list(r3)).det() - 2 * B[a, b] * B[b, c] * B[a, c]) == 0
    print("principal 3x3 minors are 2 b_ab b_bc b_ac: checked")
    # The variety {rank B_u <= 2} = {all 3 x 3 minors vanish}, computed exactly by branching:
    # restrict the minors to a linear subspace; if one of them is a nonzero product of linear
    # forms, the variety inside that subspace is the union over its factors; recurse.
    found = []

    def solve(basis_vecs):
        if not basis_vecs:
            return
        ts = sp.symbols(f't0:{len(basis_vecs)}')
        vec = sum((t * n for t, n in zip(ts, basis_vecs)), sp.zeros(4, 1))
        sub = dict(zip(u, vec))
        rest = [sp.factor(sp.expand(m.subs(sub))) for m in minors3]
        rest = [m for m in rest if m != 0]
        if not rest:
            found.append(sp.Matrix.hstack(*basis_vecs))
            return
        for m in rest:
            factors = [f for f, _ in sp.factor_list(m)[1]]
            if all(sp.Poly(f, *ts).total_degree() == 1 for f in factors):
                break
        else:
            raise AssertionError("no remaining minor splits into linear forms")
        for f in factors:
            row = sp.Matrix([[sp.Poly(f, *ts).coeff_monomial(t) for t in ts]])
            sub_basis = []
            for k in row.nullspace():
                sub_basis.append(sum((k[i] * basis_vecs[i] for i in range(len(basis_vecs))), sp.zeros(4, 1)))
            solve(sub_basis)

    solve([sp.eye(4).col(i) for i in range(4)])
    dims = sorted({Mx.shape[1] for Mx in found})
    print(f"the variety rank B_u <= 2 is a union of linear subspaces of dimensions {dims} "
          f"({len(found)} found by branching, with repetitions)")
    assert dims == [1], dims
    sols = set()
    for Mx in found:
        w = Mx.col(0)
        w = w / [x for x in w if x != 0][0]
        sols.add(tuple(w))
    sols = sorted(sols)
    print(f"rank B_u <= 2 exactly on {len(sols)} lines:")
    for w in sols:
        Bw = B.subs(dict(zip(u, w)))
        ker = Bw.nullspace()
        print(f"   u = {tuple(int(x) for x in w)}   rank {Bw.rank()}   kernel basis "
              f"{[tuple(int(x) for x in k) for k in ker]}")
        assert Bw.rank() == 2
    expected = set()
    for a, b in pairs:
        v = [0] * 4
        v[a], v[b] = 1, -1
        expected.add(tuple(sp.Integer(x) for x in v))
    for a in range(4):
        v = [1] * 4
        v[a] = -1
        w = [sp.Rational(x, v[0]) for x in v]
        expected.add(tuple(w))
    print("these are e_a - e_b and 1 - 2 e_a:", set(sols) == expected)
    # rank <= 1: symmetric with zero diagonal means all entries vanish, hence u = 0
    A, _ = sp.linear_eq_to_matrix([B[a, b] for a, b in pairs], list(u))
    print("B_u = 0 only for u = 0 (rank of the linear system):", A.rank() == 4)
    print("""Consequence. If E vanishes on U1 x U2 x U3 then for u in U1 the matrix B_u vanishes on U2 x U3,
so rank B_u <= codim U2 + codim U3. Hence codimensions (a, b, c) with a + b + c <= 4 are impossible
unless one of them is 4: for (2,1,1), (2,2,0) a plane would lie in the ten lines, for (3,1,0) a nonzero
u would have rank B_u <= 1. (E is symmetric, so the order of the three arguments does not matter.)""")


# ---------------------------------------------------------------------------------------------
# numerical minimum of E on U1 x U2 x U3
# ---------------------------------------------------------------------------------------------

def slices(trials=40, seed=0):
    from scipy.linalg import null_space
    from scipy.optimize import minimize
    rng = np.random.default_rng(seed)
    E = np.einsum('a,abcd->bcd', np.ones(4), perm_tensor())

    def basis(covs):
        return null_space(np.array(covs)) if covs else np.eye(4)

    def obj(z, shape):
        i, sub = 0, []
        for n in shape:
            cov = []
            for _ in range(n):
                v = z[i:i + 4] + 1j * z[i + 4:i + 8]
                i += 8
                cov.append(v / np.linalg.norm(v))
            sub.append(basis(cov))
        R = np.einsum('abc,ai,bj,ck->ijk', E, *sub)
        return float(np.linalg.norm(R))

    print("minimum over complex subspaces of codimension (a, b, c) of the norm of E on U1 x U2 x U3")
    print("(orthonormal bases; the subspaces are generic of that codimension, limits included)")
    for shape in [(2, 1, 1), (2, 2, 0), (3, 1, 0), (1, 1, 1), (3, 1, 1), (3, 2, 0), (2, 2, 1), (4, 1, 0)]:
        best = np.inf
        for _ in range(trials):
            z0 = rng.standard_normal(8 * sum(shape))
            r = minimize(obj, z0, args=(shape,), method='BFGS', options={'gtol': 1e-12, 'maxiter': 3000})
            best = min(best, r.fun)
        verdict = "no slice decomposition, even in the limit" if best > 1e-3 else "E has such slice decompositions"
        print(f"   codimensions {shape}: min = {best:.6f}   ({verdict})", flush=True)


# ---------------------------------------------------------------------------------------------
# fits of P by mixed split products
# ---------------------------------------------------------------------------------------------

class Split:
    """sum_v F_v (axes R_v) * G_v (other axes), complex factors."""

    def __init__(self, pairings, rng, scale=0.7):
        self.R = [PAIRINGS[p][0] for p in pairings]
        self.Rc = [PAIRINGS[p][1] for p in pairings]
        z = lambda: (rng.standard_normal((M, M)) + 1j * rng.standard_normal((M, M))) / np.sqrt(2) * scale
        self.F = [z() for _ in pairings]
        self.G = [z() for _ in pairings]
        self.perm = [np.argsort(r + rc) for r, rc in zip(self.R, self.Rc)]

    def get(self):
        return np.concatenate([a.ravel() for a in self.F + self.G])

    def set(self, theta):
        n = len(self.F)
        blocks = theta.reshape(2 * n, M, M)
        self.F = [blocks[i] for i in range(n)]
        self.G = [blocks[n + i] for i in range(n)]

    def value(self):
        out = 0
        for f, g, pm in zip(self.F, self.G, self.perm):
            out = out + np.transpose(np.multiply.outer(f, g), pm)
        return out.ravel()

    def jac(self):
        n = M ** 4
        eye = np.eye(M * M).reshape(M * M, M, M)
        cols = []
        for block in (0, 1):
            for f, g, pm in zip(self.F, self.G, self.perm):
                if block == 0:
                    t = np.multiply.outer(eye, g)
                else:
                    t = np.moveaxis(np.multiply.outer(f, eye), 2, 0)
                cols.append(np.transpose(t, [0] + [1 + i for i in pm]).reshape(M * M, n).T)
        return np.concatenate(cols, axis=1)

    def size(self):
        """max over terms of |F| |G| (invariant under rescaling the two factors)."""
        return max(float(np.linalg.norm(f) * np.linalg.norm(g)) for f, g in zip(self.F, self.G))


def lm(model, y, iters=1500, tol=1e-28, lam=1e-2, trace=None):
    ynorm = float(y @ y)
    theta = model.get()
    r = model.value() - y
    loss = np.vdot(r, r).real / ynorm
    hist = [loss]
    for it in range(1, iters + 1):
        J = model.jac()
        H = J.conj().T @ J
        g = J.conj().T @ r
        dg = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / len(g))
        ok = False
        for _ in range(30):
            try:
                step = np.linalg.solve(H + lam * np.diag(dg), -g)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            model.set(theta + step)
            r2 = model.value() - y
            loss2 = np.vdot(r2, r2).real / ynorm
            if np.isfinite(loss2) and loss2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            model.set(theta)
            break
        theta, r, loss = theta + step, r2, loss2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if trace is not None and it in trace:
            trace[it] = (loss, model.size())
        if loss < tol or (len(hist) > 200 and hist[-200] / loss < 1.02):
            break
    return loss


def patterns(n):
    """Multisets of n pairings up to the symmetry permuting the three pairings."""
    out = []
    for a in range(n, -1, -1):
        for b in range(min(a, n - a), -1, -1):
            c = n - a - b
            if c <= b:
                out.append((a, b, c))
    return out


def fit(n, restarts=30, seed=0):
    rng = np.random.default_rng(seed)
    y = perm_tensor().ravel()
    print(f"P as a sum of {n} mixed split products; relative residual |sum - P|^2 / |P|^2, complex factors,")
    print(f"{restarts} random starts per pattern (a, b, c) = number of terms of pairing 01|23, 02|13, 03|12.")
    print("'exact' counts starts ending below 1e-24 with terms of size < 1e3; size = max |F||G| over the terms.")
    for pat in patterns(n):
        names = ['01'] * pat[0] + ['02'] * pat[1] + ['03'] * pat[2]
        res = []
        for _ in range(restarts):
            model = Split(names, rng)
            loss = lm(model, y)
            res.append((loss, model.size()))
        losses = np.array([r[0] for r in res])
        sizes = np.array([r[1] for r in res])
        exact = int(np.sum((losses < 1e-24) & (sizes < 1e3)))
        i = int(np.argmin(losses))
        small = losses < 1e-10
        msg = (f"pattern {pat}: best residual {losses[i]:.3e} (size of terms there {sizes[i]:.2e}); "
               f"median residual {np.median(losses):.3e}; exact {exact}/{restarts}")
        if small.any():
            msg += f"; among the {int(small.sum())} starts below 1e-10 the sizes range {sizes[small].min():.1e} .. {sizes[small].max():.1e}"
        print(msg, flush=True)


def track(restarts=3, seed=1):
    rng = np.random.default_rng(seed)
    y = perm_tensor().ravel()
    marks = [30, 100, 300, 1000, 3000, 6000]
    print("5 terms: residual against the size of the terms along one fit (iteration: residual, size, residual * size^2)")
    for pat in patterns(5):
        if pat == (5, 0, 0):
            continue
        names = ['01'] * pat[0] + ['02'] * pat[1] + ['03'] * pat[2]
        for trial in range(restarts):
            model = Split(names, rng)
            trace = {k: None for k in marks}
            loss = lm(model, y, iters=marks[-1], trace=trace)
            row = "  ".join(f"{k}: {v[0]:.1e}, {v[1]:.1e}, {v[0] * v[1] ** 2:.2f}" for k, v in trace.items() if v)
            print(f"pattern {pat} start {trial}: final {loss:.2e} size {model.size():.1e} | {row}", flush=True)


def p410(trials=40, seed=0):
    """Four terms of pairing 01|23 plus one term X(r0, r2) Y(r1, r3) of pairing 02|13.

    Proof that this is impossible even in the limit. Let L0 = span(1, e0). Take a plane L2 inside
    {r2 : X(1, r2) = X(e0, r2) = 0}. For r0 in L0 and r2 in L2 the term of pairing 02|13 vanishes,
    so the pairing between L0 (x) C^4 and L2 (x) C^4 given by P has rank <= 4 (in the limit: for
    some plane L2, by compactness). But
     (a) the forms perm(r0, r1, ., .), r0 in L0, r1 in C^4, span ALL symmetric forms with zero
         diagonal (dimension 6), and
     (b) for every plane L2 the zero-diagonal symmetric forms B with B(L2, .) = 0 form a space
         of dimension <= 1: B is a quadratic form q on C^4 / L2 = C^2 vanishing at the images
         z_0..z_3 of the basis vectors (zero diagonal), these images span C^2, and a nonzero
         binary quadric vanishing at two independent points is determined up to a scalar.
    So that rank is >= 6 - 1 = 5. Contradiction."""
    import sympy as sp
    from scipy.optimize import minimize
    P = perm_tensor()
    pairs = list(itertools.combinations(range(4), 2))
    rows = []
    for r0 in (np.ones(4), np.eye(4)[0]):
        for i in range(4):
            Bm = np.einsum('a,b,abcd->cd', r0, np.eye(4)[i], P)
            assert np.allclose(Bm, Bm.T) and np.allclose(np.diag(Bm), 0)
            rows.append([int(Bm[a, b]) for a, b in pairs])
    print("(a) rank of the 8 forms perm(r0, e_i, ., .), r0 in {1, e0}, inside the 6-dimensional space of")
    print("    zero-diagonal symmetric forms:", sp.Matrix(rows).rank())
    # (b) exactly, in the six affine charts of the Grassmannian of planes in C^4
    a, b, c, d = sp.symbols('a b c d')
    bs = sp.symbols('b01 b02 b03 b12 b13 b23')
    Bs = sp.zeros(4, 4)
    for (i, j), v in zip(pairs, bs):
        Bs[i, j] = Bs[j, i] = v
    ok = True
    for piv in pairs:
        free = [i for i in range(4) if i not in piv]
        m1, m2 = sp.zeros(4, 1), sp.zeros(4, 1)
        m1[piv[0]], m2[piv[1]] = 1, 1
        m1[free[0]], m1[free[1]], m2[free[0]], m2[free[1]] = a, b, c, d
        eqs = list(Bs * m1) + list(Bs * m2)
        A, _ = sp.linear_eq_to_matrix(eqs, list(bs))
        # dim of solutions <= 1  <=>  rank A >= 5  <=>  the 5 x 5 minors have no common zero
        minors = set()
        for rr in itertools.combinations(range(8), 5):
            for cc in itertools.combinations(range(6), 5):
                mn = sp.factor(A.extract(list(rr), list(cc)).det())
                if mn != 0:
                    minors.add(mn)
        G = sp.groebner(list(minors), a, b, c, d, order='grevlex')
        ok = ok and list(G.exprs) == [1]
    print("(b) in all six charts the 5 x 5 minors of the system B m1 = B m2 = 0 generate the unit ideal:", ok)
    # numerically: the rank of P restricted to r0 in L0, r2 in L2 is >= 5 for every plane L2
    rng = np.random.default_rng(seed)
    L0 = np.linalg.qr(np.array([[1, 1, 1, 1], [1, 0, 0, 0.]]).T.astype(complex))[0]

    def sig5(z):
        L2 = np.linalg.qr((z[:8] + 1j * z[8:]).reshape(4, 2))[0]
        R = np.einsum('abcd,ai,ck->ibkd', P, L0, L2).reshape(8, 8)
        return np.linalg.svd(R, compute_uv=False)[4]

    best = min(minimize(sig5, rng.standard_normal(16), method='Nelder-Mead',
                        options={'xatol': 1e-10, 'fatol': 1e-12, 'maxiter': 20000, 'maxfev': 20000}).fun
               for _ in range(trials))
    print(f"numerically: min over planes L2 of the 5th singular value of P on (L0 (x) C^4) x (L2 (x) C^4) = {best:.4f}")


def t3():
    """Identities behind the proofs that P has no EXACT decomposition of patterns (3,2,0), (3,1,1).

    (Paper proofs, not machine-checked; this function checks their symbolic ingredients.)

    For l with nonzero coordinates, perm(l, u, x, y) = (prod l) E(u/l, x/l, y/l), so by LEMMA R
    the matrix B^l_u = perm(l, u, ., .) has rank <= 2 exactly for u = l_a e_a - l_b e_b and
    u = l - 2 l_a e_a (up to scalars), and then B^l_u = a (x) b + b (x) a with
        pair (a, b):  a_l = l_a e_b - l_b e_a,  b_l = l_d e_c + l_c e_d   ({c, d} the complement),
        star a:       a_l = e_a,                b_l = 2 sum_{j != a} (prod_{i != a, j} l_i) e_j.
    Write alt_ab(x, y) = x_a y_b - x_b y_a and s_cd(x, y) = x_c y_d + x_d y_c.

    Common first step. Let P = sum_{v=1..3} F_v(r0, r1) G_v(r2, r3) + (terms of the other two
    pairings), exactly, and put r0 = l. The three covectors F_v(l, .) have a common zero u != 0,
    and perm(l, u, ., .) is then a sum of at most two rank-one forms, so u is one of the ten
    vectors above ("type" of l). Each type is a closed condition on l, the torus is irreducible,
    so one type holds for all l. If it is a pair type (a, b): F_v(l, l_a e_a - l_b e_b) = 0 for
    all l, which forces F_v = f_v s_ab + (terms where r1 uses columns c, d) [checked below].

    Pattern (3,2,0): the other terms are X_1(r0, r2) Y_1(r1, r3) + X_2(r0, r2) Y_2(r1, r3). Then
    perm(l, u, ., .) = X_1(l, .) (x) Y_1(u, .) + X_2(l, .) (x) Y_2(u, .) has rank 2, so
    span(X_1(l, .), X_2(l, .)) = span(a_l, b_l) is two-dimensional. For a star type the linear
    forms X_i(l, .) would be multiples of e_a for all l (b_l is quadratic in l): dimension one,
    excluded. So the type is a pair (a, b) and X_i(l, .) in span(a_l, b_l) for all l, that is
    X_1, X_2 in span(alt_ab, s_cd). Now put r0 = e_c, r2 = e_a: the two terms X_i Y_i vanish,
    F_v(e_c, r1) only involves columns c, d of r1, but perm(e_c, r1, e_a, r3) = r1_b r3_d + r1_d r3_b.
    Contradiction.

    Pattern (3,1,1): the other terms are X(r0, r2) Y(r1, r3) + X'(r0, r3) Y'(r1, r2). Then
    perm(l, u, ., .) = X(l, .) (x) Y(u, .) + Y'(u, .) (x) X'(l, .), so X(l, .) and X'(l, .) lie in
    span(a_l, b_l) (and p1 q2 + p2 q1 = 0 in the coordinates printed below).
      Star type a: X = xi(r0) r2_a and X' = xi'(r0) r3_a have rank one. Fixing r2 = l instead (the
      same argument with the roles (r3; r0, r1)) the covector X(., l) = l_a xi has a constant
      direction, which only a star type allows: xi is a multiple of some e_a', and
      Y'(., l) too. Fixing r3 and then r1 in the same way, all of X, X', Y, Y' are monomials, so the
      two extra terms have flattening rank one each for the pairing 01|23 and P would have
      flattening rank <= 3 + 1 + 1 < 6. Contradiction.
      Pair type (a, b): X, X' in span(alt_ab, s_cd). Fixing r2 = l, the covector X(., l) is again
      in span(a_l, b_l) for the same pair (a nonzero element of span(alt_ab, s_cd) has rank 2 or
      4 and is of no other type), so Y' in span(alt_ab, s_cd) and G_v = g_v s_ab + (r3 in columns
      c, d). Fixing r1 = l and r3 = l likewise: Y in span(alt_ab, s_cd), F_v = f_v s_ab + (block
      c, d), G_v = g_v s_ab + (block c, d). So every factor is block diagonal for the column blocks
      {a, b} and {c, d}. The part of P with r0, r2 in block {a, b} and r1, r3 in block {c, d} is
      s_ab(r0, r2) s_cd(r1, r3); only the term X Y contributes to it, with
      (multiple of alt_ab)(r0, r2) * (multiple of s_cd)(r1, r3). Contradiction.

    Pattern (2,2,1) is not covered: fixing one row gives slices of shape (2,2,1), where only
    rank B_u <= 3 is forced, and E does have such slice configurations."""
    import sympy as sp
    l = sp.symbols('l0:4')
    u = sp.symbols('u0:4')

    def Bl(lv, uv):
        Bm = sp.zeros(4, 4)
        for c in range(4):
            for d in range(4):
                if c != d:
                    a, b = [i for i in range(4) if i not in (c, d)]
                    Bm[c, d] = lv[a] * uv[b] + lv[b] * uv[a]
        return Bm

    P = perm_tensor()
    chk = sp.Matrix(4, 4, lambda c, d: sum(int(P[i, j, c, d]) * l[i] * u[j] for i in range(4) for j in range(4)))
    print("B^l_u = perm(l, u, ., .) has entries l_a u_b + l_b u_a:", (chk - Bl(l, u)).expand() == sp.zeros(4, 4))
    D = sp.diag(*l)
    scaled = (sp.prod(l) * D.inv() * Bl([1] * 4, [u[i] / l[i] for i in range(4)]) * D.inv())
    print("B^l_u = (prod l) D^-1 B^1_{u/l} D^-1:", sp.simplify(scaled - Bl(l, u)) == sp.zeros(4, 4))
    e = lambda i: sp.Matrix([1 if k == i else 0 for k in range(4)])
    ok = True
    for a, b in itertools.combinations(range(4), 2):
        c, d = [i for i in range(4) if i not in (a, b)]
        uu = l[a] * e(a) - l[b] * e(b)
        av = l[a] * e(b) - l[b] * e(a)
        bv = l[d] * e(c) + l[c] * e(d)
        ok = ok and (Bl(l, list(uu)) - av * bv.T - bv * av.T).expand() == sp.zeros(4, 4)
    print("pair type: B^l_u = a b^T + b a^T for u = l_a e_a - l_b e_b:", ok)
    ok = True
    for a in range(4):
        uu = sp.Matrix(l) - 2 * l[a] * e(a)
        al = sp.zeros(4, 1)
        for j in range(4):
            if j != a:
                al[j] = 2 * sp.prod([l[i] for i in range(4) if i not in (a, j)])
        ok = ok and (Bl(l, list(uu)) - e(a) * al.T - al * e(a).T).expand() == sp.zeros(4, 4)
    print("star type: B^l_u = e_a alpha^T + alpha e_a^T for u = l - 2 l_a e_a:", ok)
    # F(l, l_a e_a - l_b e_b) = 0 for all l  <=>  F = f s_ab + (columns c, d of the second argument)
    F = sp.Matrix(4, 4, sp.symbols('f0:16'))
    a, b, c, d = 0, 1, 2, 3
    expr = sp.expand((sp.Matrix(l).T * F * (l[a] * e(a) - l[b] * e(b)))[0])
    eqs = sp.Poly(expr, *l).coeffs()
    sol = sp.solve(eqs, list(F), dict=True)[0]
    Fs = F.subs(sol)
    print("F(l, l_0 e_0 - l_1 e_1) = 0 for all l forces F =")
    sp.pprint(Fs)
    # condition for a b^T + b a^T to lie in phi (x) V + V (x) psi with phi = p1 a + p2 b, psi = q1 a + q2 b
    p1, p2, q1, q2 = sp.symbols('p1 p2 q1 q2')
    S2 = sp.Matrix([[0, 1], [1, 0]])
    lhs = (sp.Matrix([[-p2, p1]]) * S2 * sp.Matrix([-q2, q1]))[0]
    print("a b^T + b a^T in phi (x) V + V (x) psi  <=>", sp.factor(lhs), "= 0   (phi = p1 a + p2 b, psi = q1 a + q2 b)")


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'lemma'
    if mode == 't1':
        t1()
    elif mode == 'lemma':
        lemma()
    elif mode == 'slices':
        slices(*(int(a) for a in sys.argv[2:]))
    elif mode == 'fit':
        fit(*(int(a) for a in sys.argv[2:]))
    elif mode == 'track':
        track(*(int(a) for a in sys.argv[2:]))
    elif mode == 'p410':
        p410(*(int(a) for a in sys.argv[2:]))
    elif mode == 't3':
        t3()
    else:
        print(__doc__)
