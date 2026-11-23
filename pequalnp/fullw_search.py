"""Searches for limit decompositions of the 2k x 2k permanent outside the two-block form.

Same graded system as fullw.py (read its docstring first): columns carry integer weights w,
the tensor Y = sum_v F_v(rows S_v) G_v(rows not in S_v) must have no component of weight
< W = sum(w) and its weight-W component must be the permanent. New here:

  * CLASSES. A sparse builder in which every factor can be restricted to a set of column
    classes (the set of columns a monomial of the factor uses). Three choices (--classes):
      all       every class: the full model of fullw.py (120 coefficients per factor at 6 x 6);
      twoblock  the classes {first block}, {second block}: the two-block model (12 coefficients);
      paired    one column out of every pair {j, j + k}: 6 * 8 = 48 coefficients per factor at
                6 x 6. This sub-model contains the two-block model and the known 15 terms, is
                closed under the row-wise unipotent symmetry below, and does NOT force a term
                on every pairing of the rows (a term can cover permutations of 8 column sets).
                It is about 20 times cheaper than the full model.
  * complex unknowns (--complex), a per-term FLOOR (--floor), a term-deletion local search
    (mode delete), the tangent space at the known solution (mode kernel), and a 4 x 4 table
    of gradings and patterns (mode table4).

WHY A PLAIN LEAST-SQUARES SEARCH IS NOT TRUSTWORTHY (pseudo-solutions). Scaling the weight-a
component of both factors of ONE term by s^(a - W/2) keeps that term's weight-W part and
multiplies its weight-d part by s^(d - W). So every term can shed its low-weight garbage by
growing, one term at a time, and the solver only needs perm = sum_v [F_v G_v]_W (weight-W
parts of products, each worth up to W + 1 products). A cap on the size of the unknowns turns
this into a floor of the loss, typically 1e-5 .. 1e-10 relative, that says NOTHING about the
existence of a decomposition: at 4 x 4 the provably impossible patterns (5,0,0) (flattening
rank 6) and four terms (Lean: border rank 5) reach 3e-8 and 2e-10 (mode table4). Only
residuals at rounding level with bounded unknowns count.
FLOOR: a lower bound gamma on |bottom-weight component|^2 of every factor, together with the
cap, blocks the per-term escape (the term cannot grow its top without shrinking its bottom).
It restricts the search to solutions in which every factor has a bottom component.

SYMMETRY (proved on paper, checked numerically). Let A_r be any linear map of the row space
that strictly raises the column weight, one for every row r, and u = (1 + A_0) (x) .. (x)
(1 + A_{m-1}). Then u Y = Y + (components of higher weight made from lower ones), so u maps
solutions of the graded system to solutions with the same row sets and the same number of
terms. For w = (0,0,0,1,1,1) this group has dimension 6 * 9 = 54; its orbit of the known
two-block 15 terms consists of 15-term solutions with all mixed components nonzero. So the
two-block form is not an invariant notion; "outside the two-block form" must mean outside
this orbit.

RESULTS (6 x 6, w = (0,0,0,1,1,1); S15 = the row sets of the known 15 terms; "solved" means
relative residual < 1e-18; run on a heavily loaded machine, so the numbers of starts are small)
  * recovery of a 15-term solution on S15 from random starts
      two-block classes (360 unknowns): cap only 0 of 90 real, 0 of 30 complex;
        complex + floor: gamma 0.3: 0/40, 1: 1/140 (three caps), 3: 2/40, 10: 4/40, 30: 2/40;
      paired classes (1440 unknowns): cap only 0 of 6 real, 0 of 12 complex;
        complex + floor 1, |x|^2 <= 6000: 1 of 8. That solution has all mixed coefficients
        below 7e-4 (pure ones up to 5): it is a two-block solution.
      From the known solution plus noise 0.5, 1.0, 1.5 per entry (paired, real): 3/3 each.
    So the best strategy found recovers 15 terms at about one start in eight to ten; searches
    below 15 with a handful of starts are weak evidence only.
  * 14 terms, paired classes, complex + floor 1, |x|^2 <= 6000 (the strategy above): nothing
    solved. Configuration: solved/starts, best relative residual
      012x3;013x2;024x2;014;015;023;025;034;035;045  (10 pairings)  0/6  1.8e-3
      012x3;013x3;024x2;014;015;023;025;034;035      (9 pairings)   0/4  1.4e-2
      012x3;013x2;024x2;035x2;014;015;023;025;034    (9 pairings)   0/1  1.6e-2
      012x2;013x2;014x2;023x2;025x2;034x2;045x2      (7 pairings)   0/3  1.0e-2
      012x3;034x3;015x3;024x3;035x2                  (5 pairings)   0/2  9.1e-2
      012x4;013x4;024x3;034x3                        (4 pairings)   0/4  9.2e-2
    With a recovery rate near 1/8 at 15 terms this excludes nothing.
  * exact model, paired classes: 20 terms (two on every pairing) solved from 4 of 4 random
    starts; 19 terms (one pairing with a single term): 0 of 2, residuals 8e-2 and 1e-4 at
    the cap (the second is a limit-type approximation, not an exact solution).
  * mode delete (paired classes): removing any one of the 15 terms by continuation leaves
    either 72 permutations uncovered (residual 0.1; the eight squares other than those on
    013 and 024) or a pseudo-solution (9e-6 .. 4e-5; the other seven terms).
  * mode kernel: the Jacobian at the known solution has kernel of dimension 31 (two-block),
    67 (paired), 139 (full, injective). Of the 36 new directions in the paired model 18 are
    the row-wise unipotent ones; a random combination of the other 18 does not integrate
    (the solver moves back 88 percent of the perturbation, independently of its size).
  * In the paired model a term on the pairing S | S^c reaches exactly the permutations whose
    column pairs are each split by S, so the pairings used must split every perfect
    matching of the rows: at least 4 pairings (15 minimal sets, e.g. 012, 013, 024, 034).
  * mode table4 (4 x 4, complex, cap; 20 starts each): five terms are found for the patterns
    (3,1,1) and (2,2,1) with w = (0,0,1,1) (17, 16), (0,1,1,1) (13, 3), (0,1,1,2) (2, 1),
    (0,1,2,3) (9, 7), and (3,1,1) with (0,0,1,2) (1); never with w = (0,0,0,1); never for
    (4,1,0), (3,2,0), (5,0,0) or four terms.

A factor F on the rows S is stored as a vector indexed by the injective maps S -> columns
(--full: all maps).

Usage (every run prints a SUMMARY line):
  python3 fullw_search.py table4 --starts 20
  python3 fullw_search.py kernel
  python3 fullw_search.py delete --classes paired
  python3 fullw_search.py run 0,0,0,1,1,1 S15 --classes twoblock --complex --floor 3 --capabs 3000 --starts 40
  python3 fullw_search.py run 0,0,0,1,1,1 S15 --classes paired --strategy known:0.3
  python3 fullw_search.py run 0,0,0,1,1,1 "012x2;013x2;014x2;015x2;023x2;024x2;025x2;034x2;035x2;045x2" \
          --classes paired --exact --complex --capabs 6000
  python3 fullw_search.py run 0,0,1,1 "01x2;02x2;03" --k 2 --full --complex --starts 20
"""
import argparse
import itertools
import time
import warnings

import numpy as np
import scipy.linalg
import scipy.sparse as sp

warnings.filterwarnings('ignore', category=scipy.linalg.LinAlgWarning)


class Model:
    """terms: list of (S, allowF, allowG); S a k-tuple of rows; allowF / allowG either None
    (every class) or a collection of frozensets of columns the factor may use."""

    def __init__(self, k, w, terms, exact=False, inj=True, mu=1.0):
        m = 2 * k
        self.k, self.m, self.w = k, m, list(w)
        idx = np.array(list(itertools.product(range(m), repeat=m)), dtype=np.int64)
        wt = np.array(w)[idx].sum(axis=1)
        W = sum(w)
        is_perm = np.array([len(set(row)) == m for row in idx])
        keep = np.ones(len(idx), dtype=bool) if exact else wt <= W
        if inj:
            cnt = np.zeros((len(idx), m), dtype=np.int64)
            for r in range(m):
                cnt[np.arange(len(idx)), idx[:, r]] += 1
            keep &= cnt.max(axis=1) <= 2
        idx, wt = idx[keep], wt[keep]
        target = is_perm[keep].astype(float)
        low = wt < W
        sw = np.where(low, np.sqrt(mu), 1.0)
        powers = m ** np.arange(k - 1, -1, -1)
        tuples = list(itertools.product(range(m), repeat=k))
        base_ok = np.array([(len(set(t)) == k) or not inj for t in tuples])
        tsets = [frozenset(t) for t in tuples]
        self.tuples = tuples

        def table(allow):
            ok = base_ok.copy()
            if allow is not None:
                allow = set(allow)
                ok &= np.array([s in allow for s in tsets])
            comp = np.full(len(tuples), -1, dtype=np.int64)
            comp[ok] = np.arange(ok.sum())
            return comp, int(ok.sum()), np.nonzero(ok)[0]

        self.terms = [(tuple(S), aF, aG) for S, aF, aG in terms]
        self.n = len(terms)
        self.offF, self.offG, self.codesF, self.codesG = [], [], [], []
        rows, ia, ib = [], [], []
        off = 0
        for S, aF, aG in self.terms:
            Sc = tuple(r for r in range(m) if r not in S)
            cF, dF, lF = table(aF)
            cG, dG, lG = table(aG)
            a = cF[idx[:, list(S)] @ powers]
            b = cG[idx[:, list(Sc)] @ powers]
            rw = np.nonzero((a >= 0) & (b >= 0))[0]
            self.offF.append((off, dF))
            self.offG.append((off + dF, dG))
            self.codesF.append(lF)
            self.codesG.append(lG)
            rows.append(rw)
            ia.append(a[rw] + off)
            ib.append(b[rw] + off + dF)
            off += dF + dG
        self.nu = off
        # drop the equations no term touches (their residual is constant)
        touched = np.zeros(len(idx), dtype=bool)
        for rw in rows:
            touched[rw] = True
        self.const = float((target[~touched] ** 2).sum())   # unreachable part of the permanent
        newrow = np.cumsum(touched) - 1
        self.rows = [newrow[rw] for rw in rows]
        self.ia, self.ib = ia, ib
        self.target = target[touched]
        self.sw = sw[touched]
        self.low = low[touched]
        self.neq = int(touched.sum())
        self.norm2 = float(target @ target)
        R = np.concatenate([np.concatenate([rw, rw]) for rw in self.rows])
        C = np.concatenate([np.concatenate([a, b]) for a, b in zip(ia, ib)])
        nnz = len(R)
        pat = sp.coo_matrix((np.arange(1, nnz + 1, dtype=np.float64), (R, C)), shape=(self.neq, self.nu)).tocsr()
        self._pat = pat
        self._perm = pat.data.astype(np.int64) - 1
        self._swR = self.sw[R]
        self._allrows = np.concatenate(self.rows)
        self._allia = np.concatenate(ia)
        self._allib = np.concatenate(ib)

    def raw(self, x):
        p = x[self._allia] * x[self._allib]
        if np.iscomplexobj(p):
            r = (np.bincount(self._allrows, weights=p.real, minlength=self.neq)
                 + 1j * np.bincount(self._allrows, weights=p.imag, minlength=self.neq))
        else:
            r = np.bincount(self._allrows, weights=p, minlength=self.neq)
        return r - self.target

    def residual(self, x):
        return self.raw(x) * self.sw

    def split_loss(self, x):
        """(squared residual of the weight-W equations, of the lower weights), unweighted."""
        r = np.abs(self.raw(x)) ** 2
        return float(r[~self.low].sum()) + self.const, float(r[self.low].sum())

    def jac(self, x):
        vals = []
        for a, b in zip(self.ia, self.ib):
            vals.append(x[b])
            vals.append(x[a])
        v = np.concatenate(vals) * self._swR
        return sp.csr_matrix((v[self._perm], self._pat.indices, self._pat.indptr), shape=self._pat.shape)

    def term_norms(self, x):
        out = []
        for (oF, dF), (oG, dG) in zip(self.offF, self.offG):
            out.append(np.linalg.norm(x[oF:oF + dF]) * np.linalg.norm(x[oG:oG + dG]))
        return np.array(out)

    def balance(self, x):
        """Rescale every term so that |F_v| = |G_v| (a symmetry of the system)."""
        x = x.copy()
        for (oF, dF), (oG, dG) in zip(self.offF, self.offG):
            nf, ng = np.linalg.norm(x[oF:oF + dF]), np.linalg.norm(x[oG:oG + dG])
            if nf > 0 and ng > 0:
                s = np.sqrt(ng / nf)
                x[oF:oF + dF] *= s
                x[oG:oG + dG] /= s
        return x


def lm(M, x, iters=300, cap=4.0, lam=1e-2, rho=10.0, log=None, tol=1e-24, patience=60, ridge=None, gauge=None,
       floor=None):
    """Levenberg-Marquardt on M with the size cap of fullw.lm. Returns (x, weighted loss).
    ridge: optional vector of weights; adds sum_i ridge_i |x_i|^2 to the loss (used to push
    chosen terms to zero continuously: the term-deletion local search).
    gauge: optional (sign vector, kappa); adds the square of kappa * sum_i sign_i |x_i|^2 / nu.
    With sign = +1 on the components of top weight and -1 on those of bottom weight this pins
    the position on each orbit of the scaling flow (two-sided, where the cap is one-sided), so
    the lower components cannot be shrunk by scaling at all. It vanishes on one point of every
    orbit, so it does not move the solutions.
    floor: optional (list of index arrays, gamma); for every block b adds the square of
    rho * max(0, 1 - |x_b|^2 / gamma). With the blocks = bottom-weight components of every
    factor this forbids the PER-TERM scaling escape (see FLOOR in the module docstring)."""
    B2 = cap * M.nu

    def penalty(x):
        return rho * max(0.0, np.vdot(x, x).real / B2 - 1.0)

    def sq(r):
        return np.vdot(r, r).real

    def rdg(x):
        out = 0.0 if ridge is None else float((ridge * np.abs(x) ** 2).sum())
        if gauge is not None:
            out += (gauge[1] * float((gauge[0] * np.abs(x) ** 2).sum()) / M.nu) ** 2
        if floor is not None:
            for b in floor[0]:
                out += (rho * max(0.0, 1.0 - float((np.abs(x[b]) ** 2).sum()) / floor[1])) ** 2
        return out

    r = M.residual(x)
    pen = penalty(x)
    loss = sq(r) + pen * pen + rdg(x)
    hist = [loss]
    for it in range(iters):
        J = M.jac(x)
        JH = J.conj().T.tocsr()
        H = (JH @ J).toarray()
        g = JH @ r
        if pen > 0:
            # real unknowns: exact Gauss-Newton term of the penalty; complex: exact gradient,
            # positive semidefinite approximation of its Hessian
            gp = rho * 2 * x / B2
            H += np.outer(gp, gp.conj())
            g = g + gp * pen
        if ridge is not None:
            H[np.diag_indices_from(H)] += ridge
            g = g + ridge * x
        g = np.array(g)
        if floor is not None:
            for b in floor[0]:
                pf = rho * (1.0 - float((np.abs(x[b]) ** 2).sum()) / floor[1])
                if pf > 0:
                    gf = -2 * rho * x[b] / floor[1]
                    H[np.ix_(b, b)] += np.outer(gf, gf.conj())
                    g[b] = g[b] + gf * pf
        if gauge is not None:
            pb = gauge[1] * float((gauge[0] * np.abs(x) ** 2).sum()) / M.nu
            gb = 2 * gauge[1] * gauge[0] * x / M.nu
            H += np.outer(gb, gb.conj())
            g = g + gb * pb
        dg = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / len(g))
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
            p2 = penalty(x2)
            l2 = sq(r2) + p2 * p2 + rdg(x2)
            if np.isfinite(l2) and l2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            break
        x, r, pen, loss = x2, r2, p2, l2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if log and (it < 3 or it % 10 == 0):
            log(f"      it {it:4d} loss {loss:.3e} rms {np.sqrt(sq(x) / M.nu):.2f} lam {lam:.1e}")
        if loss < tol or (len(hist) > patience and hist[-patience] / loss < 1.05):
            break
    return x, loss


def parse_splits(s, k):
    out = []
    for part in s.split(';'):
        part = part.strip()
        if not part:
            continue
        rows, mult = part.split('x') if 'x' in part else (part, '1')
        S = tuple(int(c) for c in rows)
        assert len(S) == k
        out += [S] * int(mult)
    return out


# ----------------------------------------------------------------------- the known 15 terms
PAIRS3 = [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5), (0, 4, 5)]
SPLITS15 = PAIRS3 + [(0, 1, 2), (0, 1, 2), (0, 1, 3), (0, 1, 3), (0, 2, 4)]
C15 = [3, -15, 3, 9, -18, -6, 6, -18, 6, 30]
EXTRA15 = [(-2, [3, 3, -1, -2, -1, -2], [9, 6, 3, -3, -6, -9]), (-2, [-1, -2, 3, 3, -2, -1], [3, -3, 9, 6, -9, -6]),
           (-2, [5, 5, -7, 2, -7, 2], [2, 1, 1, -1, -1, -2]), (-2, [-7, 2, 5, 5, 2, -7], [1, -1, 2, 1, -2, -1]),
           (12, [1, -1, -1, 1, 1, -1], [1, -1, -1, 1, 1, -1])]


def known15(M):
    """The 15-term identity of garbage_fast.py written in the unknowns of M (a 6 x 6 model with
    weights (0,0,0,1,1,1), injective factors, terms SPLITS15, every class allowed)."""
    def gmf(codes, coef, cols):
        pos = {M.tuples[c]: i for i, c in enumerate(codes)}
        v = np.zeros(len(codes))
        p, q, r = cols
        for cf, t in zip(coef, [(p, q, r), (p, r, q), (q, p, r), (q, r, p), (r, p, q), (r, q, p)]):
            v[pos[t]] += cf
        return v
    x = np.zeros(M.nu)
    one = [1] * 6
    for v in range(15):
        (oF, dF), (oG, dG) = M.offF[v], M.offG[v]
        cF, cG = M.codesF[v], M.codesG[v]
        if v < 10:
            cc = C15[v]
            s = abs(cc) ** 0.5
            F = (cc * gmf(cF, one, (0, 1, 2)) + gmf(cF, one, (3, 4, 5))) / s
            G = (gmf(cG, one, (0, 1, 2)) + gmf(cG, one, (3, 4, 5)) / cc) * s
        else:
            co, a, b = EXTRA15[v - 10]
            fa, gb = gmf(cF, a, (0, 1, 2)), gmf(cG, b, (0, 1, 2))
            s = (np.linalg.norm(gb) / (abs(co) * np.linalg.norm(fa))) ** 0.5
            F, G = co * fa * s, gb / s
        x[oF:oF + dF] = F
        x[oG:oG + dG] = G
    return x


def two_block_classes(k):
    return [frozenset(range(k)), frozenset(range(k, 2 * k))]


def gauge_signs(M):
    """+1 on the factor components that use only columns of maximal weight, -1 on those that
    use only columns of minimal weight, 0 elsewhere."""
    w = np.array(M.w)
    sg = np.zeros(M.nu)
    for v in range(M.n):
        for (o, d), cod in ((M.offF[v], M.codesF[v]), (M.offG[v], M.codesG[v])):
            ws = np.array([[w[c] for c in M.tuples[cc]] for cc in cod])
            sg[o:o + d] = np.where((ws == w.max()).all(axis=1), 1.0, 0.0) - np.where((ws == w.min()).all(axis=1), 1.0, 0.0)
    return sg


def bottom_blocks(M):
    """For every factor, the indices of its components that use only columns of minimal weight."""
    w = np.array(M.w)
    out = []
    for v in range(M.n):
        for (o, d), cod in ((M.offF[v], M.codesF[v]), (M.offG[v], M.codesG[v])):
            ws = np.array([[w[c] for c in M.tuples[cc]] for cc in cod])
            out.append(o + np.nonzero((ws == w.min()).all(axis=1))[0])
    return out


def solve(M, x0, iters, cap, stages=(1.0,), log=None, ridge=None, gauge=None, floor=None):
    """LM, optionally in stages with decreasing weight mu on the lower components.
    Returns x, relative residual (unweighted, all equations), rms entry."""
    x = x0
    for mu in stages:
        M.sw = np.where(M.low, np.sqrt(mu), 1.0)
        R = np.concatenate([np.concatenate([rw, rw]) for rw in M.rows])
        M._swR = M.sw[R]
        x, _ = lm(M, x, iters=iters, cap=cap, log=log, ridge=ridge, gauge=gauge, floor=floor)
    a, b = M.split_loss(x)
    return x, (a + b) / M.norm2, a / M.norm2, b / M.norm2, float(np.sqrt(np.vdot(x, x).real / M.nu))


def paired_classes(k):
    """Column classes that use exactly one column of every pair {j, j + k}."""
    return [frozenset(j + k * b for j, b in zip(range(k), bits)) for bits in itertools.product((0, 1), repeat=k)]


def class_set(name, k):
    return {'all': None, 'paired': paired_classes(k), 'twoblock': two_block_classes(k)}[name]


def random_start(M, rng, scale, cplx):
    x0 = rng.standard_normal(M.nu) * scale
    if cplx:
        x0 = x0 + 1j * scale * rng.standard_normal(M.nu)
    return x0


def cmd_run(args):
    k = args.k
    w = [int(c) for c in args.weights.split(',')]
    splits = SPLITS15 if args.splits in ('', 'S15') else parse_splits(args.splits, k)
    cls = class_set(args.classes, k)
    M = Model(k, w, [(S, cls, cls) for S in splits], exact=args.exact, inj=not args.full)
    cap = args.capabs / M.nu if args.capabs else args.cap
    floor = (bottom_blocks(M), args.floor) if args.floor > 0 else None
    print(f"k={k} w={w} terms={M.n} classes={args.classes} equations={M.neq} unknowns={M.nu} "
          f"{'exact' if args.exact else 'limit'} {'all maps' if args.full else 'injective'} "
          f"{'complex' if args.complex else 'real'} floor={args.floor} cap(mean square)={cap:.2f} "
          f"unreachable part of the permanent={M.const}", flush=True)
    rng_seed = args.seed
    hits, out = 0, []
    for trial in range(args.starts):
        t0 = time.time()
        rng = np.random.default_rng(rng_seed + trial)
        kind, _, eps = args.strategy.partition(':')
        if kind == 'random':
            x0 = random_start(M, rng, args.scale, args.complex)
        elif kind == 'known':      # the known 15 terms plus noise (6 x 6, weights 0,0,0,1,1,1, SPLITS15 only)
            x0 = known15(M) + float(eps or 0.1) * rng.standard_normal(M.nu)
        else:
            raise SystemExit('unknown strategy')
        x, rel, relW, rellow, rms = solve(M, x0, args.iters, cap, [1.0], None, floor=floor)
        hits += rel < 1e-18
        out.append(rel)
        print(f"  start {rng_seed + trial}: rel residual {rel:.3e} (weight W {relW:.1e}, lower {rellow:.1e}) |x|^2 "
              f"{np.vdot(x, x).real:.0f} max|entry| {np.abs(x).max():.1f}  ({time.time() - t0:.0f} s)", flush=True)
        if rel < 1e-18 and args.save:
            np.save(f"{args.save}_{rng_seed + trial}.npy", x)
    print(f"SUMMARY run w={w} classes={args.classes} splits={args.splits or 'S15'} terms={M.n} "
          f"{'exact' if args.exact else 'limit'} {'complex' if args.complex else 'real'} floor={args.floor}: "
          f"{hits}/{args.starts} solved, best rel residual {min(out):.3e}, median {np.median(out):.1e}", flush=True)


def cmd_delete(args):
    """Term-deletion local search from the known 15 terms: a ridge on one term is raised in
    steps until the term is gone, re-optimising the others at every step."""
    cls = class_set(args.classes, 3)
    M = Model(3, [0, 0, 0, 1, 1, 1], [(S, cls, cls) for S in SPLITS15])
    which = [int(c) for c in args.drop.split(',')] if args.drop else list(range(15))
    for v in which:
        t0 = time.time()
        x = known15(M)
        ridge = np.zeros(M.nu)
        (oF, dF), (oG, dG) = M.offF[v], M.offG[v]
        for nu in (1e-3, 1e-2, 1e-1, 1.0, 10.0, 1e3, 1e6, 1e12):
            ridge[oF:oF + dF] = nu
            ridge[oG:oG + dG] = nu
            x, _ = lm(M, x, iters=args.iters, cap=args.cap, ridge=ridge, patience=30)
        a, b = M.split_loss(x)
        print(f"  delete term {v} (rows {M.terms[v][0]}): rel residual of the other 14 terms {(a + b) / M.norm2:.3e} "
              f"(weight W {a / M.norm2:.1e}, lower {b / M.norm2:.1e})  ({time.time() - t0:.0f} s)", flush=True)


def cmd_kernel(args):
    """Tangent space of the solution set at the known 15 terms, in three models."""
    for name in ('twoblock', 'paired', 'all'):
        cls = class_set(name, 3)
        M = Model(3, [0, 0, 0, 1, 1, 1], [(S, cls, cls) for S in SPLITS15])
        x = known15(M)
        J = M.jac(x)
        ev = np.linalg.eigvalsh((J.T @ J).toarray())
        a, b = M.split_loss(x)
        print(f"  classes {name}: unknowns {M.nu}, equations {M.neq}, residual of the known solution {a + b:.1e}, "
              f"kernel of the Jacobian has dimension {int((ev < 1e-9 * ev[-1]).sum())}", flush=True)


def cmd_table4(args):
    """4 x 4: which gradings and patterns have graded limit decompositions (the validated case)."""
    pats = {'(3,1,1)': '01x3;02;03', '(2,2,1)': '01x2;02x2;03', '(4,1,0)': '01x4;02', '(3,2,0)': '01x3;02x2',
            '(5,0,0)': '01x5', '4 terms (2,1,1)': '01x2;02;03'}
    for w in ([0, 0, 1, 1], [0, 0, 0, 1], [0, 1, 1, 1], [0, 1, 1, 2], [0, 0, 1, 2], [0, 1, 2, 3]):
        for name, sp in pats.items():
            M = Model(2, w, [(S, None, None) for S in parse_splits(sp, 2)], inj=False)
            out = []
            for s in range(args.starts):
                x0 = random_start(M, np.random.default_rng(s), 0.5, True)
                out.append(solve(M, x0, 300, 4.0)[1])
            print(f"SUMMARY 4x4 w={w} pattern {name}: {sum(r < 1e-18 for r in out)}/{args.starts} solved, "
                  f"best rel {min(out):.1e}, median {np.median(out):.1e}", flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['run', 'delete', 'kernel', 'table4'])
    ap.add_argument('weights', nargs='?', default='0,0,0,1,1,1')
    ap.add_argument('splits', nargs='?', default='', help='e.g. "012x3;013;024", or S15 for the 15 known terms')
    ap.add_argument('--k', type=int, default=3)
    ap.add_argument('--classes', default='all', choices=['all', 'paired', 'twoblock'])
    ap.add_argument('--starts', type=int, default=4)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--iters', type=int, default=300)
    ap.add_argument('--cap', type=float, default=4.0, help='bound on the mean square of the unknowns')
    ap.add_argument('--capabs', type=float, default=0.0, help='bound on |x|^2 instead of --cap')
    ap.add_argument('--floor', type=float, default=0.0, help='lower bound on |bottom component|^2 of every factor')
    ap.add_argument('--complex', action='store_true')
    ap.add_argument('--full', action='store_true', help='all column maps in the factors (default: injective)')
    ap.add_argument('--exact', action='store_true')
    ap.add_argument('--scale', type=float, default=0.5, help='standard deviation of the random start')
    ap.add_argument('--strategy', default='random', help='random | known:<eps>')
    ap.add_argument('--drop', default='', help='delete mode: comma separated term indices (default all 15)')
    ap.add_argument('--save', default='', help='prefix for .npy files of solved starts')
    args = ap.parse_args()
    {'run': cmd_run, 'delete': cmd_delete, 'kernel': cmd_kernel, 'table4': cmd_table4}[args.mode](args)
