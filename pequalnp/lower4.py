"""Lower bounds for mixed split decompositions of the 4 x 4 permanent: computations.

P is the 4 x 4 permanent as a tensor in (C^4)^{(x)4}: P[j0, j1, j2, j3] = 1 when (j0..j3) is a
permutation. A split product for the pairing 01|23 is F[j0, j1] * G[j2, j3]; for 02|13 it is
F[j0, j2] * G[j1, j3]; for 03|12 it is F[j0, j3] * G[j1, j2].

What is proved elsewhere (lean/PvsNP/FourByFourLower.lean, checked by Lean):
  * gamma_not_split, twoBlock_five_le: the two-block model needs five terms            (T1)
  * five_le_card_of_permanent_eq_sum_split: P is not a sum of four split products,
    whatever the pairings (any field of characteristic zero)                           (T2, exact)
The limit version of T2 (P is not a LIMIT of sums of four split products) has a short proof
on paper; this script checks its ingredients exactly and numerically:

  Fix row 0 to the all-ones vector. P becomes the 3-tensor E(w, x, y) = sum over distinct
  (i, j, k) of w_i x_j y_k, and a split product becomes (linear form in ONE of w, x, y) times
  (bilinear form in the other two): a slice. So a sum of four split products with n1, n2, n3
  terms of the three pairings gives subspaces U1, U2, U3 of codimension <= n1, n2, n3 with
  E = 0 on U1 x U2 x U3; this condition is closed (Grassmannians are compact).
  For u in C^4 let B_u = E(u, ., .): the symmetric matrix with zero diagonal and entries
  (B_u)_{ab} = u_c + u_d, {c, d} the complement of {a, b}.
  LEMMA R.  rank B_u <= 1 only for u = 0, and rank B_u <= 2 exactly on ten lines:
            u = e_a - e_b (six) and u = 1 - 2 e_a (four).
  If E = 0 on U1 x U2 x U3 then rank B_u <= codim U2 + codim U3 for every u in U1. With
  (n1, n2, n3) a permutation of (2,1,1) or (2,2,0) some U_i has dimension >= 2 and the other
  two codimensions add up to <= 2: a plane inside ten lines, impossible. With (3,1,0) some U_i
  is nonzero and the other codimensions add up to <= 1: impossible. (4,0,0) is excluded by the
  flattening rank 6 of P.

Modes:
  python3 lower4.py t1       exact checks for the two-block model (sympy)
  python3 lower4.py lemma    exact proof of LEMMA R by case enumeration (sympy), and the
                             kernels / admissible hyperplane pairs of the ten lines
  python3 lower4.py slices   numerical minimum of |E restricted to U1 x U2 x U3| over complex
                             subspaces of given codimensions (positive = no slice decomposition,
                             even in the limit)
  python3 lower4.py fit N    Levenberg-Marquardt fits of P by N mixed split products, every
                             pattern of pairings: residual, and size of the terms
                             (N = 4: obstruction; N = 5: limit versus exact)
  python3 lower4.py track    for 5 terms: residual against the size of the terms along one fit
                             (a limit decomposition has residual -> 0 only while terms blow up)
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
    else:
        print(__doc__)
