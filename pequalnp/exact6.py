"""Exact decompositions of the 6 x 6 permanent into 3-split products: searches and exact checks.

Question: is the EXACT mixed split rank of perm_6 at k = 3 equal to Laplace's 20, or smaller?
(The limit value is <= 15; at 4 x 4 the exact value is 6 = Laplace and the limit value is 5.)
See notes/exact_6x6.md for the results; this file holds everything that produced them.

MODEL. perm_6 = sum_v F_v(rows S_v) G_v(rows not in S_v), every F_v, G_v a real trilinear form given
by its coefficients on a set of allowed column triples (--cls):
    full       all 216 triples (use checks/splitfast.py for this one: same model, faster assembly);
    inj        the 120 injective triples;
    paired     one column out of each pair {j, j+3}: 48 triples;
    twoblock   triples inside columns {0,1,2} or inside {3,4,5}: 54 triples (the two-block model at lam = 1).
All 6^6 coefficient equations that some term can reach are imposed (exact model, no grading).

SOLVER. Levenberg-Marquardt on the sparse Jacobian with a one-sided cap on the mean square of the
unknowns (penalty rho * max(0, |x|^2 / (cap * nu) - 1)), so that limit-type approximations (residual
decaying while the factors grow; expected here because the limit value is <= 15) show up as a positive
floor of the residual that moves with the cap, and only bounded solutions reach rounding level.
A start counts as EXACT when the relative squared residual is < 1e-20.

Modes
  run     --cls C --sets "012x2;013;..." --starts n --cap c     search one configuration
  suite   NAME                                                  a named list of configurations (see SUITES)
  rank2b  two-block model in the rank formulation (see the note, Section 3): minimise
          sum_P rank M_P by alternating projections / LM on a factorised model with n_P terms per pairing
  check   exact integer checks of the statements used in the note (Sections 3 and 4)
"""
import argparse
import itertools
import time
import warnings

import numpy as np
import scipy.linalg
import scipy.sparse as sp

warnings.filterwarnings('ignore', category=scipy.linalg.LinAlgWarning)

TUP = list(itertools.product(range(6), repeat=3))
PAIRS = [S for S in itertools.combinations(range(6), 3) if 0 in S]


def allowed(cls):
    if cls == 'full':
        ok = [True] * 216
    elif cls == 'inj':
        ok = [len(set(t)) == 3 for t in TUP]
    elif cls == 'paired':
        ok = [len({c % 3 for c in t}) == 3 for t in TUP]
    elif cls == 'twoblock':
        ok = [all(c < 3 for c in t) or all(c >= 3 for c in t) for t in TUP]
    elif cls == 'twoblock_inj':
        ok = [len(set(t)) == 3 and (all(c < 3 for c in t) or all(c >= 3 for c in t)) for t in TUP]
    else:
        raise ValueError(cls)
    return np.nonzero(ok)[0]


def perm_target():
    T = np.zeros(6 ** 6)
    pw = 6 ** np.arange(5, -1, -1)
    for p in itertools.permutations(range(6)):
        T[int(np.dot(p, pw))] = 1.0
    return T


def parse_sets(s):
    out = []
    for part in s.split(';'):
        part = part.strip()
        if not part:
            continue
        rows, mult = part.split('x') if 'x' in part else (part, '1')
        out += [tuple(int(c) for c in rows)] * int(mult)
    return out


class Model:
    """sum_v F_v(S_v) G_v(S_v^c) with coefficient supports given by cls (a name or a list of
    (codesF, codesG) per term)."""

    def __init__(self, sets, cls='twoblock'):
        self.sets = [tuple(sorted(S)) for S in sets]
        self.n = len(self.sets)
        tup = np.array(TUP)
        rows, ia, ib = [], [], []
        self.off = []
        off = 0
        for v, S in enumerate(self.sets):
            Sc = tuple(r for r in range(6) if r not in S)
            if isinstance(cls, str):
                cF = cG = allowed(cls)
            else:
                cF, cG = cls[v]
            pF = 6 ** (5 - np.array(S))
            pG = 6 ** (5 - np.array(Sc))
            eF = tup[cF] @ pF
            eG = tup[cG] @ pG
            rw = (eF[:, None] + eG[None, :]).ravel()
            a = np.repeat(np.arange(len(cF)), len(cG)) + off
            b = np.tile(np.arange(len(cG)), len(cF)) + off + len(cF)
            rows.append(rw)
            ia.append(a)
            ib.append(b)
            self.off.append((off, len(cF), len(cG)))
            off += len(cF) + len(cG)
        self.nu = off
        target = perm_target()
        touched = np.zeros(6 ** 6, dtype=bool)
        for rw in rows:
            touched[rw] = True
        self.const = float((target[~touched] ** 2).sum())
        newrow = np.cumsum(touched) - 1
        self.rows = np.concatenate([newrow[rw] for rw in rows])
        self.ia = np.concatenate(ia)
        self.ib = np.concatenate(ib)
        self.target = target[touched]
        self.touched = touched
        self.neq = int(touched.sum())
        self.norm2 = 720.0
        R = np.concatenate([self.rows, self.rows])
        C = np.concatenate([self.ia, self.ib])
        pat = sp.coo_matrix((np.arange(1, len(R) + 1, dtype=np.float64), (R, C)), shape=(self.neq, self.nu)).tocsr()
        self._pat = pat
        self._perm = pat.data.astype(np.int64) - 1

    def residual(self, x):
        return np.bincount(self.rows, weights=x[self.ia] * x[self.ib], minlength=self.neq) - self.target

    def jac(self, x):
        v = np.concatenate([x[self.ib], x[self.ia]])
        return sp.csr_matrix((v[self._perm], self._pat.indices, self._pat.indptr), shape=self._pat.shape)

    def balance(self, x):
        x = x.copy()
        for o, dF, dG in self.off:
            nf, ng = np.linalg.norm(x[o:o + dF]), np.linalg.norm(x[o + dF:o + dF + dG])
            if nf > 0 and ng > 0:
                s = np.sqrt(ng / nf)
                x[o:o + dF] *= s
                x[o + dF:o + dF + dG] /= s
        return x

    def term_norms(self, x):
        return np.array([np.linalg.norm(x[o:o + dF]) * np.linalg.norm(x[o + dF:o + dF + dG]) for o, dF, dG in self.off])

    def full_tensor(self, x):
        """the 6^6 tensor of the sum (only touched entries can be nonzero)."""
        Y = np.zeros(6 ** 6)
        Y[self.touched] = np.bincount(self.rows, weights=x[self.ia] * x[self.ib], minlength=self.neq)
        return Y


def lm(M, x, iters=400, cap=4.0, lam=1e-2, rho=10.0, tol=1e-24, patience=50, log=None):
    """Levenberg-Marquardt with a cap on |x|^2 / nu. Returns x, relative squared residual (without
    the penalty), number of iterations."""
    B2 = cap * M.nu

    def pen(x):
        return rho * max(0.0, float(x @ x) / B2 - 1.0)

    r = M.residual(x)
    p = pen(x)
    loss = float(r @ r) + p * p
    hist = [loss]
    for it in range(iters):
        J = M.jac(x)
        JT = J.T.tocsr()
        H = (JT @ J).toarray()
        g = JT @ r
        if p > 0:
            gp = rho * 2 * x / B2
            H += np.outer(gp, gp)
            g = g + gp * p
        dg = np.maximum(np.diag(H), 1e-12 * np.trace(H) / len(g))
        ok = False
        for _ in range(30):
            A = H.copy()
            A[np.diag_indices_from(A)] += lam * dg
            try:
                step = scipy.linalg.solve(A, -g, assume_a='pos', check_finite=False)
            except (np.linalg.LinAlgError, scipy.linalg.LinAlgError):
                lam *= 10
                continue
            x2 = x + step
            r2 = M.residual(x2)
            p2 = pen(x2)
            l2 = float(r2 @ r2) + p2 * p2
            if np.isfinite(l2) and l2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            break
        x, r, p, loss = x2, r2, p2, l2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if log and (it < 3 or it % 20 == 0):
            log(f"      it {it:4d} loss {loss:.3e} rms {np.sqrt(float(x @ x) / M.nu):.2f} lam {lam:.1e}")
        if loss < tol * M.norm2 or (len(hist) > patience and hist[-patience] / loss < 1.05):
            break
    rel = (float(r @ r) + M.const) / M.norm2
    return x, rel, len(hist)


def search(sets, cls, starts, cap=4.0, iters=400, seed=0, scale=0.5, verbose=False, label=None, keep=None):
    """Random starts for one configuration. Returns (number of exact hits, list of (rel, rms))."""
    M = Model(sets, cls)
    rng = np.random.default_rng(seed)
    res = []
    hits = 0
    t0 = time.time()
    for s in range(starts):
        x0 = rng.standard_normal(M.nu) * scale
        t1 = time.time()
        x, rel, its = lm(M, x0, iters=iters, cap=cap, log=print if verbose else None)
        rms = float(np.sqrt(x @ x / M.nu))
        res.append((rel, rms))
        hit = rel < 1e-20
        hits += hit
        if hit and keep is not None:
            keep.append((M, M.balance(x)))
        print(f"    start {s}: rel {rel:.3e} rms {rms:.2f} max term {M.term_norms(x).max():.1f} its {its} "
              f"{time.time() - t1:.0f}s{'  EXACT' if hit else ''}", flush=True)
    best = min(r for r, _ in res)
    print(f"SUMMARY {label or ''} cls={cls} n={len(sets)} cap={cap} unknowns={M.nu} unreachable={M.const:.0f}: "
          f"exact {hits}/{starts}, best rel {best:.3e}, median rel {np.median([r for r, _ in res]):.3e}, "
          f"{time.time() - t0:.0f}s", flush=True)
    return hits, res


def cfg(mult):
    """mult: dict pairing index -> number of terms (PAIRS order 012,013,014,015,023,024,025,034,035,045)."""
    out = []
    for i, c in sorted(mult.items()):
        out += [PAIRS[i]] * c
    return out


def pairing_perms():
    """the action of S_6 (row permutations) on the ten pairings, as index permutations (deduplicated)."""
    idx = {P: i for i, P in enumerate(PAIRS)}
    out = set()
    for g in itertools.permutations(range(6)):
        im = []
        for P in PAIRS:
            Q = tuple(sorted(g[r] for r in P))
            if 0 not in Q:
                Q = tuple(r for r in range(6) if r not in Q)
            im.append(idx[Q])
        out.add(tuple(im))
    return sorted(out)


def orbits(total, lo=1, hi=None):
    """orbit representatives under S_6 of the vectors (n_P) with lo <= n_P <= hi and sum = total."""
    hi = total if hi is None else hi
    G = np.array(pairing_perms())
    seen, reps = set(), []

    def rec(pref, rest):
        if len(pref) == 10:
            if rest == 0:
                yield tuple(pref)
            return
        left = 10 - len(pref) - 1
        for c in range(lo, min(hi, rest - lo * left) + 1):
            yield from rec(pref + [c], rest - c)
    for v in rec([], total):
        if v in seen:
            continue
        orb = {tuple(r) for r in np.array(v)[G]}
        seen |= orb
        reps.append(tuple(int(c) for c in max(orb)))
    return reps


def enum_search(total, cls, starts, cap, lo=1, hi=None, seed=0, iters=300, skip=0, limit=None):
    reps = orbits(total, lo, hi)
    print(f"{len(reps)} orbits of term vectors with sum {total}, {lo} <= n_P <= {hi}", flush=True)
    tot_hits = 0
    table = []
    for i, v in enumerate(reps[skip:limit] if limit else reps[skip:]):
        sets = cfg(dict(enumerate(v)))
        M = Model(sets, cls)
        rng = np.random.default_rng(seed + i)
        rels = []
        for s in range(starts):
            x, rel, its = lm(M, rng.standard_normal(M.nu) * 0.5, iters=iters, cap=cap)
            rels.append(rel)
        h = sum(r < 1e-20 for r in rels)
        tot_hits += h
        table.append((v, h, min(rels)))
        print(f"  n_P = {v}: exact {h}/{starts}, best rel {min(rels):.2e}, median {np.median(rels):.2e}", flush=True)
    best = min(t[2] for t in table)
    print(f"SUMMARY enum total={total} cls={cls} cap={cap}: {len(table)} configurations, {starts} starts each, "
          f"configurations with an exact hit: {sum(t[1] > 0 for t in table)}, smallest residual {best:.2e}", flush=True)
    return table


S15 = cfg({0: 3, 1: 3, 2: 1, 3: 1, 4: 1, 5: 2, 6: 1, 7: 1, 8: 1, 9: 1})      # row sets of the 15-term limit identity

SUITES = {
    # validation
    'val20': [('laplace: 20 on one pairing', cfg({0: 20})), ('2 on each pairing', cfg({i: 2 for i in range(10)}))],
    # (b) two terms on nine pairings, one on the tenth (unique up to S_6)
    'b19': [('2 on nine, 1 on one', cfg({**{i: 2 for i in range(10)}, 9: 1}))],
    # (a) the 15 row sets of the limit identity plus four extra terms
    'a19': [
        ('S15 + 012,013,024,045', cfg({0: 4, 1: 4, 2: 1, 3: 1, 4: 1, 5: 3, 6: 1, 7: 1, 8: 1, 9: 2})),
        ('S15 + 014,015,023,025', cfg({0: 3, 1: 3, 2: 2, 3: 2, 4: 2, 5: 2, 6: 2, 7: 1, 8: 1, 9: 1})),
        ('S15 + 034,035,045,014', cfg({0: 3, 1: 3, 2: 2, 3: 1, 4: 1, 5: 2, 6: 1, 7: 2, 8: 2, 9: 2})),
        ('S15 + 012x2,013x2', cfg({0: 5, 1: 5, 2: 1, 3: 1, 4: 1, 5: 2, 6: 1, 7: 1, 8: 1, 9: 1})),
    ],
    'a18': [
        ('S15 + 012,013,024', cfg({0: 4, 1: 4, 2: 1, 3: 1, 4: 1, 5: 3, 6: 1, 7: 1, 8: 1, 9: 1})),
        ('S15 + 014,023,045', cfg({0: 3, 1: 3, 2: 2, 3: 1, 4: 2, 5: 2, 6: 1, 7: 1, 8: 1, 9: 2})),
    ],
    # (c) few pairings, many terms each
    'c19': [
        ('012x10;034x9', cfg({0: 10, 7: 9})),
        ('012x7;034x6;015x6', cfg({0: 7, 7: 6, 3: 6})),
        ('012x5;013x5;024x5;034x4', cfg({0: 5, 1: 5, 5: 5, 7: 4})),
        ('012x4;034x4;015x4;024x4;035x3', cfg({0: 4, 7: 4, 3: 4, 5: 4, 8: 3})),
    ],
    # (d) squares on all pairings plus nine extras spread in other ways
    'd19': [
        ('3 on four, 2 on one, 1 on five', cfg({0: 3, 1: 3, 5: 3, 7: 3, 2: 2, 3: 1, 4: 1, 6: 1, 8: 1, 9: 1})),
        ('4 on three, 1 on seven', cfg({0: 4, 1: 4, 5: 4, 2: 1, 3: 1, 4: 1, 6: 1, 7: 1, 8: 1, 9: 1})),
        ('10 on one, 1 on nine', cfg({0: 10, **{i: 1 for i in range(1, 10)}})),
        ('5 on 012, 5 on 345-side partner 013, 1 on eight... (5,6,1^8)', cfg({0: 5, 1: 6, **{i: 1 for i in range(2, 10)}})),
        ('3 on 012, 2 on seven, 1 on two', cfg({0: 3, 1: 2, 2: 2, 3: 2, 4: 2, 5: 2, 6: 2, 7: 2, 8: 1, 9: 1})),
    ],
}


# ------------------------------------------------------------------ exact checks for the note
def matchings():
    def rec(rows):
        if not rows:
            yield ()
            return
        a = rows[0]
        for b in rows[1:]:
            rest = [r for r in rows if r not in (a, b)]
            for m in rec(rest):
                yield ((a, b),) + m
    return list(rec(list(range(6))))


def separates(P, m):
    return all((a in P) != (b in P) for a, b in m)


def check():
    """Exact (integer / rational) checks of the statements of notes/exact_6x6.md, Section 3."""
    import sympy
    ms = matchings()
    assert len(ms) == 15
    A = sympy.Matrix(15, 10, lambda i, j: int(separates(PAIRS[j], ms[i])))
    print("1. matrix A (15 matchings x 10 pairings, A[m,P] = 1 iff P separates m): rank", A.rank(),
          "(= 10: the ten tensors v_P = q(P) q(P^c) are linearly independent)")
    assert A.rank() == 10
    assert all(sum(A[i, j] for j in range(10)) == 4 for i in range(15)) and all(sum(A[i, j] for i in range(15)) == 6 for j in range(10))
    # weight-(2,2,2) monomials of the block-1 tensor space (3^6): index tuples using each column twice
    mons = [t for t in itertools.product(range(3), repeat=6) if all(t.count(c) == 2 for c in range(3))]
    pos = {t: i for i, t in enumerate(mons)}
    assert len(mons) == 90
    perms3 = list(itertools.permutations(range(3)))

    def vec(P, coefF, coefG):
        """sum_{s,t} coefF[s] coefG[t] x_s(P) y_t(P^c) as a vector on the 90 monomials."""
        Pc = [r for r in range(6) if r not in P]
        v = [0] * 90
        for s, cs in zip(perms3, coefF):
            for t, ct in zip(perms3, coefG):
                if cs * ct:
                    tup = [0] * 6
                    for i, r in enumerate(P):
                        tup[r] = s[i]
                    for i, r in enumerate(Pc):
                        tup[r] = t[i]
                    v[pos[tuple(tup)]] += cs * ct
        return v
    one = [1] * 6
    unit = [[int(i == j) for j in range(6)] for i in range(6)]
    V = [vec(P, one, one) for P in PAIRS]
    tang = {i: [vec(P, one, u) for u in unit] + [vec(P, u, one) for u in unit] for i, P in enumerate(PAIRS)}
    print("2. weight-(2,2,2) parts of the tangent spaces L_P + R_P = q(P) (x) V(P^c) + V(P) (x) q(P^c):")
    dims = [sympy.Matrix(tang[i]).rank() for i in range(10)]
    print("   dimensions", dims, "(6 + 6 - 1 each)")
    allrank = sympy.Matrix([v for i in range(10) for v in tang[i]]).rank()
    print("   dimension of the sum over all ten pairings:", allrank, "of 90")
    ok = True
    for i0 in range(10):
        S = [v for i in range(10) if i != i0 for v in tang[i]]
        r0 = sympy.Matrix(S).rank()
        r1 = sympy.Matrix(S + [V[i0]]).rank()
        ok &= (r1 == r0 + 1)
    print("   v_P0 is NOT in the sum of the tangent spaces of the other nine pairings, for every P0:", ok)
    assert ok
    # symmetrisation: the S_3-average of q(P) (x) H is mean(H) * v_P
    def sym(v):
        out = [sympy.Rational(0)] * 90
        for g in perms3:
            for t, c in zip(mons, v):
                if c:
                    out[pos[tuple(g[x] for x in t)]] += sympy.Rational(c, 6)
        return out
    ok = True
    for i, P in enumerate(PAIRS[:3]):
        for u in unit:
            ok &= sym(vec(P, one, u)) == [sympy.Rational(x, 6) for x in V[i]]
            ok &= sym(vec(P, u, one)) == [sympy.Rational(x, 6) for x in V[i]]
    print("   S_3-average of q(P) (x) e_t and of e_s (x) q(P^c) equals v_P / 6:", ok)
    assert ok
    # 3. the rank statements of Lemma 2 / Lemma 3 on random integer instances
    rng = np.random.default_rng(1)
    d = 6
    x, w, y, z = [sympy.Matrix(d, 1, [1] * d) for _ in range(4)]

    def Mmat(G1, G2):
        return sympy.Matrix(sympy.BlockMatrix([[G1, x * y.T], [z * w.T, G2]]))

    def rv():
        return sympy.Matrix(d, 1, [int(t) for t in rng.integers(-5, 6, d)])
    c = sympy.Rational(3, 7)
    r = {}
    r['square'] = Mmat(c * x * w.T, x * y.T / c).rank()
    r['A'] = Mmat(x * rv().T, z * rv().T).rank()
    r["A'"] = Mmat(rv() * w.T, rv() * y.T).rank()
    r['B'] = Mmat(c * x * w.T + rv() * rv().T, z * y.T / c).rank()
    r["B'"] = Mmat(c * x * w.T, z * y.T / c + rv() * rv().T).rank()
    r['C'] = Mmat(sympy.zeros(d, d), z * rv().T + rv() * y.T).rank()
    r["C'"] = Mmat(x * rv().T + rv() * w.T, sympy.zeros(d, d)).rank()
    r['square, wrong constant'] = Mmat(c * x * w.T, 2 * z * y.T / c).rank()
    r['tangent in both blocks, two-sided'] = Mmat(x * rv().T + rv() * w.T, z * rv().T + rv() * y.T).rank()
    print("3. rank of M_P = [[Gamma1, x y^T], [z w^T, Gamma2]] for the types of Lemma 3:", r)
    assert r['square'] == 1 and all(r[t] == 2 for t in ['A', "A'", 'B', "B'", 'C', "C'"])
    assert r['square, wrong constant'] == 2 and r['tangent in both blocks, two-sided'] > 2
    worst = 10
    for _ in range(200):
        a, b = int(rng.integers(0, 5)), int(rng.integers(0, 5))
        G1 = sum((rv() * rv().T for _ in range(a)), sympy.zeros(d, d))
        G2 = sum((rv() * rv().T for _ in range(b)), sympy.zeros(d, d))
        if rng.random() < 0.5 and a and b:      # force the equality case: x in col, w in row, alpha * beta = 1
            G1 = G1 - G1 + x * w.T * c + sum((rv() * rv().T for _ in range(a - 1)), sympy.zeros(d, d))
            G2 = z * y.T / c + sum((rv() * rv().T for _ in range(b - 1)), sympy.zeros(d, d))
        worst = min(worst, Mmat(G1, G2).rank() - (G1.rank() + G2.rank() - 1))
    print("   min over 200 random instances of rank M_P - (rank Gamma1 + rank Gamma2 - 1):", worst, "(Lemma 2: >= 0)")
    assert worst == 0
    print("ALL EXACT CHECKS PASSED")


# ------------------------------------------------------------------ (d): squares plus pure extras
def pure_setup():
    """index tables of the GMF two-block sub-model: lam[i][s, t] = index (0..89) of the weight-(2,2,2)
    monomial x_s(P_i) y_t(P_i^c), s, t permutations of the three columns."""
    mons = [t for t in itertools.product(range(3), repeat=6) if all(t.count(c) == 2 for c in range(3))]
    pos = {t: i for i, t in enumerate(mons)}
    perms3 = list(itertools.permutations(range(3)))
    lam = np.zeros((10, 6, 6), dtype=np.int64)
    for i, P in enumerate(PAIRS):
        Pc = [r for r in range(6) if r not in P]
        for a, s in enumerate(perms3):
            for b, t in enumerate(perms3):
                tup = [0] * 6
                for j, r in enumerate(P):
                    tup[r] = s[j]
                for j, r in enumerate(Pc):
                    tup[r] = t[j]
                lam[i, a, b] = pos[tuple(tup)]
    return lam


def pure_search(e1, e2, starts, seed=0, cap=25.0, iters=300, verbose=False):
    """Squares on all ten pairings (constants c_P in block 1, d_P = 1 / c_P in block 2) plus pure
    extra products: e1 = pairing indices of the block-1 extras, e2 = of the block-2 extras, all
    factors generalised matrix functions (6 coefficients). Unknowns c, d, (u_e, h_e).
    Equations: 90 (block 1) + 90 (block 2) + 10 (c_P d_P = 1). An exact solution is an exact
    decomposition of perm_6 into 10 + len(e1) + len(e2) split products."""
    lam = pure_setup()
    ext = [(0, p) for p in e1] + [(1, p) for p in e2]
    nu = 20 + 12 * len(ext)
    rng = np.random.default_rng(seed)

    def res_jac(x):
        r = np.zeros(190)
        J = np.zeros((190, nu))
        for b in range(2):
            for i in range(10):
                idx = lam[i].ravel()
                np.add.at(r, 90 * b + idx, x[10 * b + i])
                J[90 * b + idx, 10 * b + i] += 1.0
        for e, (b, p) in enumerate(ext):
            o = 20 + 12 * e
            u, h = x[o:o + 6], x[o + 6:o + 12]
            idx = 90 * b + lam[p]
            np.add.at(r, idx.ravel(), np.outer(u, h).ravel())
            for a in range(6):
                J[idx[a, :], o + a] += h
                J[idx[:, a], o + 6 + a] += u
        r[180:] = x[:10] * x[10:20] - 1.0
        J[180 + np.arange(10), np.arange(10)] = x[10:20]
        J[180 + np.arange(10), 10 + np.arange(10)] = x[:10]
        return r, J
    hits = 0
    best = np.inf
    sols = []
    B2 = cap * nu
    for s in range(starts):
        x = rng.standard_normal(nu)
        x[10:20] = 1.0 / x[:10]
        lamd = 1e-2
        r, J = res_jac(x)
        loss = r @ r + 10 * max(0.0, x @ x / B2 - 1) ** 2
        for it in range(iters):
            H = J.T @ J
            g = J.T @ r
            p = max(0.0, x @ x / B2 - 1)
            if p > 0:
                gp = np.sqrt(10) * 2 * x / B2
                H += np.outer(gp, gp)
                g += gp * np.sqrt(10) * p
            dg = np.maximum(np.diag(H), 1e-12)
            ok = False
            for _ in range(25):
                try:
                    step = scipy.linalg.solve(H + lamd * np.diag(dg), -g, assume_a='pos')
                except Exception:
                    lamd *= 10
                    continue
                x2 = x + step
                r2, J2 = res_jac(x2)
                l2 = r2 @ r2 + 10 * max(0.0, x2 @ x2 / B2 - 1) ** 2
                if np.isfinite(l2) and l2 < loss:
                    ok = True
                    break
                lamd *= 5
            if not ok:
                break
            x, r, J, loss = x2, r2, J2, l2
            lamd = max(lamd / 3, 1e-12)
            if loss < 1e-26:
                break
        rr = float(r @ r)
        best = min(best, rr)
        if rr < 1e-20:
            hits += 1
            sols.append(x.copy())
        if verbose:
            print(f"    start {s}: residual {rr:.3e} max|x| {np.abs(x).max():.1f} min|c| {np.abs(x[:10]).min():.2e}")
    print(f"SUMMARY pure extras block1 {list(e1)} block2 {list(e2)}: {10 + len(ext)} terms, exact {hits}/{starts}, "
          f"best squared residual {best:.3e}", flush=True)
    return hits, best, sols


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode')
    ap.add_argument('name', nargs='?')
    ap.add_argument('--cls', default='twoblock')
    ap.add_argument('--sets', default='')
    ap.add_argument('--starts', type=int, default=4)
    ap.add_argument('--cap', type=float, default=4.0)
    ap.add_argument('--iters', type=int, default=400)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--scale', type=float, default=0.5)
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--e1', default='0,0,1,1,5')
    ap.add_argument('--e2', default='0,0,1,1,5')
    ap.add_argument('--lo', type=int, default=1)
    ap.add_argument('--hi', type=int, default=None)
    a = ap.parse_args()
    if a.mode == 'run':
        search(parse_sets(a.sets), a.cls, a.starts, cap=a.cap, iters=a.iters, seed=a.seed, scale=a.scale,
               verbose=a.verbose, label=a.sets)
    elif a.mode == 'pure':
        pure_search([int(t) for t in a.e1.split(',') if t], [int(t) for t in a.e2.split(',') if t], a.starts,
                    seed=a.seed, cap=a.cap, iters=a.iters, verbose=a.verbose)
    elif a.mode == 'check':
        check()
    elif a.mode == 'enum':
        enum_search(int(a.name), a.cls, a.starts, a.cap, lo=a.lo, hi=a.hi, seed=a.seed, iters=a.iters)
    elif a.mode == 'suite':
        for label, sets in SUITES[a.name]:
            print(f"== {label}  ({len(sets)} terms)", flush=True)
            search(sets, a.cls, a.starts, cap=a.cap, iters=a.iters, seed=a.seed, scale=a.scale, verbose=a.verbose,
                   label=label)
