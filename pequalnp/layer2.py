"""Layer 2 of the permanent: mixed (2, m-2) decompositions of the m^m permanent tensor.

perm_m is a tensor with one factor K^m per ROW.  A 2-split term on the row pair {a, b} is

    F(row a, row b) * G(the other m-2 rows),     F an m x m array, G an m^(m-2) array.

Laplace expansion along one fixed pair of rows uses C(m, 2) terms.  This file asks whether
terms on DIFFERENT pairs can do it with fewer, exactly or in the limit.  A configuration is a
multigraph on the rows (one edge per term).

Solver.  Levenberg-Marquardt on the polynomial system  sum_v F_v (x) G_v = perm  with the exact
sparse Jacobian (every equation involves two unknowns of each term), complex unknowns by
default (--real for real ones).  Options:
  --inj       factors supported on injective column choices (F off-diagonal, G on distinct
              columns).  NOT known to be without loss of generality; it is an ansatz.
  --weights   graded limit system: give column j the integer weight w_j and match only the
              components of weight <= sum(w).  A bounded exact solution is a limit decomposition
              (scale column j by lam^w_j, divide by lam^sum(w), let lam -> 0).
Border diagnostic (--border).  Minimise  |residual|^2 + mu * sum_v (|F_v|^2 + |G_v|^2)  for a
decreasing sequence of mu, warm started.  With  f = |residual|^2 / m!  and  S = max_v |F_v||G_v|:
  exact decomposition:   f -> rounding with S bounded;
  limit decomposition:   f -> 0 while S grows, f * S^2 roughly constant (order-one limit);
  neither:               f stalls at a positive value whatever S does.
Only the first is a proof-grade statement after exact verification; the other two are evidence.

Usage examples
  python3 layer2.py validate                         # m = 4 checks and m = 5 Laplace
  python3 layer2.py fit --m 5 --config "01x10" --restarts 3
  python3 layer2.py fit --m 5 --config "01x4;02x2;03x2;04" --border --restarts 4
  python3 layer2.py count --m 5 --terms 9             # number of configurations up to symmetry
  python3 layer2.py scan --m 5 --terms 9 --family star --border --restarts 2
  python3 layer2.py scan --m 5 --terms 9 --family all --shard 0/4 --restarts 1 --real --inj
"""
import argparse
import itertools
import json
import math
import sys
import time

import numpy as np
import scipy.linalg
import scipy.sparse as sp


# ----------------------------------------------------------------------------- configurations

def parse_config(s):
    """ "01x4;02x2;34" -> [(0,1)]*4 + [(0,2)]*2 + [(3,4)]"""
    out = []
    for part in s.split(';'):
        part = part.strip()
        if not part:
            continue
        if 'x' in part:
            rows, mult = part.split('x')
        else:
            rows, mult = part, '1'
        pair = tuple(sorted(int(c) for c in rows))
        assert len(pair) == 2 and pair[0] != pair[1]
        out += [pair] * int(mult)
    return out


def show_config(pairs):
    cnt = {}
    for p in pairs:
        cnt[p] = cnt.get(p, 0) + 1
    return ';'.join('%d%d%s' % (a, b, '' if c == 1 else 'x%d' % c) for (a, b), c in sorted(cnt.items()))


def all_configs(m, terms):
    """All multigraphs with `terms` edges on m labelled rows, up to relabelling of the rows.
    For m = 4 a pair and its complement give the same kind of term and are identified.
    Returns a list of multiplicity vectors over the list of pairs, and the list of pairs."""
    pairs = list(itertools.combinations(range(m), 2))
    if m == 4:
        pairs = [(0, 1), (0, 2), (0, 3)]
    P = len(pairs)
    pos = {p: i for i, p in enumerate(pairs)}
    actions = set()
    for g in itertools.permutations(range(m)):
        act = []
        for (a, b) in pairs:
            q = tuple(sorted((g[a], g[b])))
            if q not in pos:  # m = 4: replace by the complement
                q = tuple(sorted(set(range(m)) - set(q)))
            act.append(pos[q])
        actions.add(tuple(act))
    actions = np.array(sorted(actions))                      # (|G|, P)
    vecs = np.array([np.bincount(c, minlength=P) for c in
                     itertools.combinations_with_replacement(range(P), terms)])
    base = int(terms + 1)
    wts = base ** np.arange(P - 1, -1, -1, dtype=np.int64)
    best = np.zeros(len(vecs), dtype=np.int64)
    for act in actions:
        img = np.zeros_like(vecs)
        img[:, act] = vecs
        best = np.maximum(best, img @ wts)
    canon = vecs @ wts == best
    return [v for v in vecs[canon]], pairs


def vec_to_pairs(vec, pairs):
    out = []
    for c, p in zip(vec, pairs):
        out += [p] * int(c)
    return out


def is_star(vec, pairs):
    used = [p for c, p in zip(vec, pairs) if c]
    return any(all(r in p for p in used) for r in set(used[0]))


def flattening_ok(m, pairs_list):
    """Necessary condition from the flattening along each pair {a,b} (rank C(m,2) for perm_m):
    a term on {a,b} has rank 1, a term on a pair disjoint from {a,b} has rank <= m^(m-4)... we use
    the crude bounds 1 / min(m^2, m^(m-4)) / unbounded."""
    need = m * (m - 1) // 2
    for ab in itertools.combinations(range(m), 2):
        tot = 0
        for p in pairs_list:
            k = len(set(p) & set(ab))
            if p == ab:
                tot += 1
            elif k == 0:
                tot += min(m * m, m ** (m - 4)) if m > 4 else 1
            else:
                tot += need
        if tot < need:
            return False
    return True


# ----------------------------------------------------------------------------- the model

class Model:
    def __init__(self, m, pairs, real=False, inj=False, weights=None):
        self.m, self.pairs, self.real, self.inj = m, list(pairs), real, inj
        self.n = len(self.pairs)
        idx = np.array(list(itertools.product(range(m), repeat=m)), dtype=np.int64)
        target = np.array([len(set(t)) == m for t in idx], dtype=float)
        keep = np.ones(len(idx), dtype=bool)
        if weights is not None:
            w = np.array(weights)
            keep &= w[idx].sum(axis=1) <= w.sum()
        if inj:
            cnt = np.zeros((len(idx), m), dtype=np.int64)
            for r in range(m):
                cnt[np.arange(len(idx)), idx[:, r]] += 1
            keep &= cnt.max(axis=1) <= 2
        k2 = m - 2
        pw2 = m ** np.arange(1, -1, -1)
        pwg = m ** np.arange(k2 - 1, -1, -1)
        if inj:
            cF = np.full(m * m, -1, dtype=np.int64)
            okF = np.array([a != b for a in range(m) for b in range(m)])
            cF[okF] = np.arange(okF.sum())
            tup = np.array(list(itertools.product(range(m), repeat=k2)))
            okG = np.array([len(set(t)) == k2 for t in tup])
            cG = np.full(m ** k2, -1, dtype=np.int64)
            cG[okG] = np.arange(okG.sum())
            self.dF, self.dG = int(okF.sum()), int(okG.sum())
        else:
            cF, cG = np.arange(m * m), np.arange(m ** k2)
            self.dF, self.dG = m * m, m ** k2
        fa, ga, mk = [], [], []
        for (a, b) in self.pairs:
            rest = [r for r in range(m) if r not in (a, b)]
            ia = cF[idx[:, [a, b]] @ pw2]
            ib = cG[idx[:, rest] @ pwg]
            mk.append((ia >= 0) & (ib >= 0))
            fa.append(ia)
            ga.append(ib)
        mk = np.array(mk)
        keep &= mk.any(axis=0) | (target > 0)
        self.target = target[keep]
        self.N = int(keep.sum())
        self.tnorm = float(self.target @ self.target)
        self.fa = [np.where(k[keep], a[keep], 0) for a, k in zip(fa, mk)]
        self.ga = [np.where(k[keep], g[keep], 0) for g, k in zip(ga, mk)]
        self.mk = [k[keep].astype(float) for k in mk]
        self.per = self.dF + self.dG
        self.p = self.n * self.per
        # fixed sparsity pattern of the Jacobian, row major: for each equation, (F_v, G_v) for v = 0..n-1
        cols = np.empty((self.N, 2 * self.n), dtype=np.int64)
        for v in range(self.n):
            cols[:, 2 * v] = v * self.per + self.fa[v]
            cols[:, 2 * v + 1] = v * self.per + self.dF + self.ga[v]
        self.cols = cols.ravel()
        self.indptr = np.arange(0, self.N * 2 * self.n + 1, 2 * self.n)
        self.dtype = float if real else complex

    def random(self, rng, scale=0.5):
        if self.real:
            return rng.standard_normal(self.p) * scale
        return (rng.standard_normal(self.p) + 1j * rng.standard_normal(self.p)) * scale / np.sqrt(2)

    def split(self, th):
        T = th.reshape(self.n, self.per)
        return T[:, :self.dF], T[:, self.dF:]

    def residual(self, th):
        F, G = self.split(th)
        r = -self.target.astype(self.dtype)
        for v in range(self.n):
            r = r + self.mk[v] * F[v, self.fa[v]] * G[v, self.ga[v]]
        return r

    def jac(self, th):
        F, G = self.split(th)
        data = np.empty((self.N, 2 * self.n), dtype=self.dtype)
        for v in range(self.n):
            data[:, 2 * v] = self.mk[v] * G[v, self.ga[v]]
            data[:, 2 * v + 1] = self.mk[v] * F[v, self.fa[v]]
        return sp.csr_matrix((data.ravel(), self.cols, self.indptr), shape=(self.N, self.p))

    def sizes(self, th):
        F, G = self.split(th)
        return np.linalg.norm(F, axis=1) * np.linalg.norm(G, axis=1)

    def balance(self, th):
        """Gauge: rescale every term so that |F_v| = |G_v| (does not change the tensor)."""
        F, G = self.split(th.copy())
        nf, ng = np.linalg.norm(F, axis=1), np.linalg.norm(G, axis=1)
        s = np.sqrt(ng / np.maximum(nf, 1e-300))
        out = np.concatenate([F * s[:, None], G / s[:, None]], axis=1)
        return out.ravel()


def lm(M, th, mu=0.0, iters=300, tol=1e-26, lam=1e-2, stall=40, tmax=None):
    """Levenberg-Marquardt for |r(th)|^2 + mu |th|^2.  Returns th, f = |r|^2/|target|^2, iterations."""
    t0 = time.time()
    r = M.residual(th)
    obj = np.vdot(r, r).real + mu * np.vdot(th, th).real
    hist = [obj]
    it = 0
    for it in range(1, iters + 1):
        J = M.jac(th)
        JH = J.conj().T.tocsr()
        H = (JH @ J).toarray()
        g = JH @ r + mu * th
        d = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / M.p) + mu
        ok = False
        for _ in range(25):
            A = H.copy()
            A[np.diag_indices_from(A)] += mu + lam * d
            try:
                step = scipy.linalg.solve(A, -g, assume_a='pos', check_finite=False)
            except (np.linalg.LinAlgError, scipy.linalg.LinAlgError):
                lam *= 10
                continue
            th2 = th + step
            r2 = M.residual(th2)
            obj2 = np.vdot(r2, r2).real + mu * np.vdot(th2, th2).real
            if np.isfinite(obj2) and obj2 < obj:
                ok = True
                break
            lam *= 5
        if not ok:
            break
        th, r, obj = th2, r2, obj2
        lam = max(lam / 3, 1e-13)
        hist.append(obj)
        fres = np.vdot(r, r).real / M.tnorm
        if fres < tol and mu == 0:
            break
        if len(hist) > stall and hist[-stall] - obj < 1e-3 * obj and (mu > 0 or hist[-stall] / obj < 1.02):
            break
        if tmax is not None and time.time() - t0 > tmax:
            break
    return th, np.vdot(r, r).real / M.tnorm, it


def fit(M, rng, restarts=1, iters=300, border=False, mus=None, verbose=False, tmax=None):
    """Plain fits (mu = 0), or with border=True the penalised continuation.  Returns a list of dicts."""
    out = []
    for s in range(restarts):
        th = M.random(rng)
        rec = dict(start=s)
        if border:
            curve = []
            for mu in (mus or [1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8]):
                th, f, it = lm(M, th, mu=mu, iters=iters, stall=25, tmax=tmax)
                th = M.balance(th)
                S = float(M.sizes(th).max())
                curve.append((mu, f, S, f * S * S, it))
                if verbose:
                    print('      mu %.0e  f %.3e  S %.3e  f*S^2 %.3e  (%d it)' % curve[-1], flush=True)
            rec.update(curve=curve, f=curve[-1][1], S=curve[-1][2])
        else:
            th, f, it = lm(M, th, iters=iters, tmax=tmax)
            th = M.balance(th)
            rec.update(f=f, S=float(M.sizes(th).max()), it=it)
        rec['theta'] = th
        out.append(rec)
    return out


def classify(curve):
    """Reading of a penalised continuation curve [(mu, f, S, f S^2, it)]."""
    f = np.array([c[1] for c in curve])
    S = np.array([c[2] for c in curve])
    if f[-1] < 1e-12 and S[-1] < 1e3:
        return 'exact'
    if f[-1] < 1e-5 and f[-1] < 0.2 * f[-3] and S[-1] > 1.5 * S[-3]:
        return 'limit?'
    if f[-1] > 0.7 * f[-3]:
        return 'stalls'
    return 'unclear'


# ----------------------------------------------------------------------------- commands

def cmd_validate(args):
    rng = np.random.default_rng(args.seed)
    print('m = 4 (pairings 01|23, 02|13, 03|12; a term on a pair = a term on its complement)')
    for cfg, expect in [('01x6', 'exact'), ('01x3;02;03', 'limit only'), ('01x2;02x2;03', 'limit only'),
                        ('01x4;02', 'nothing'), ('01x3;02x2', 'nothing'),
                        ('01x2;02;03', 'nothing'), ('01x4', 'nothing'), ('01x2;02x2', 'nothing')]:
        M = Model(4, parse_config(cfg), real=args.real)
        res = fit(M, rng, restarts=args.restarts, border=True, iters=200)
        best = min(res, key=lambda r: r['f'])
        print('  %-14s expect %-10s : best of %d starts  f %.2e  S %.2e  f*S^2 %.2e  -> %s' % (
            cfg, expect, args.restarts, best['f'], best['S'], best['f'] * best['S'] ** 2, classify(best['curve'])),
            flush=True)
        print('       curve (mu, f, S): ' + '  '.join('(%.0e, %.1e, %.1e)' % c[:3] for c in best['curve']))
    print('m = 5, ten terms on one pair (Laplace) and ten terms, one on each pair (Laplace along two columns)')
    for cfg in ['01x10', '01;02;03;04;12;13;14;23;24;34']:
        M = Model(5, parse_config(cfg), real=args.real)
        t0 = time.time()
        res = fit(M, rng, restarts=2, iters=400)
        print('  %-30s f = %s   sizes %s   (%.0f s)' % (cfg, ['%.1e' % r['f'] for r in res],
                                                      ['%.1f' % r['S'] for r in res], time.time() - t0), flush=True)


def run_config(m, pairs, args, rng):
    M = Model(m, pairs, real=args.real, inj=args.inj, weights=args.weights)
    t0 = time.time()
    res = fit(M, rng, restarts=args.restarts, iters=args.iters, border=args.border, verbose=args.verbose,
              tmax=args.tmax)
    best = min(res, key=lambda r: r['f'])
    rec = dict(config=show_config(pairs), terms=len(pairs), unknowns=M.p, equations=M.N,
               f=[float('%.3e' % r['f']) for r in res], S=[float('%.3e' % r['S']) for r in res],
               best=float('%.3e' % best['f']), secs=round(time.time() - t0, 1))
    if args.border:
        rec['verdict'] = [classify(r['curve']) for r in res]
        rec['curve_best'] = [[float('%.2e' % x) for x in c[:4]] for c in best['curve']]
    else:
        rec['solved'] = int(sum(r['f'] < 1e-18 for r in res))
    if args.save and best['f'] < args.save_below:
        np.save(args.save, best['theta'])
    return rec


def cmd_fit(args):
    rng = np.random.default_rng(args.seed)
    print(json.dumps(run_config(args.m, parse_config(args.config), args, rng)), flush=True)


def cmd_count(args):
    vecs, pairs = all_configs(args.m, args.terms)
    stars = sum(is_star(v, pairs) for v in vecs)
    flat = sum(flattening_ok(args.m, vec_to_pairs(v, pairs)) for v in vecs)
    by = {}
    for v in vecs:
        by[int((v > 0).sum())] = by.get(int((v > 0).sum()), 0) + 1
    print('m = %d, %d terms: %d configurations up to relabelling of the rows; %d are stars (all pairs through '
          'one row); %d pass the flattening count; by number of distinct pairs: %s' % (
              args.m, args.terms, len(vecs), stars, flat, dict(sorted(by.items()))))


def cmd_scan(args):
    rng = np.random.default_rng(args.seed)
    vecs, pairs = all_configs(args.m, args.terms)
    if args.family == 'star':
        vecs = [v for v in vecs if is_star(v, pairs)]
    elif args.family == 'nonstar':
        vecs = [v for v in vecs if not is_star(v, pairs)]
    if args.max_pairs:
        vecs = [v for v in vecs if (v > 0).sum() <= args.max_pairs]
    if args.sample and len(vecs) > args.sample:
        pick = np.random.default_rng(12345).choice(len(vecs), args.sample, replace=False)
        vecs = [vecs[i] for i in sorted(pick)]
    if args.shard:
        i, k = (int(x) for x in args.shard.split('/'))
        vecs = vecs[i::k]
    print('# scanning %d configurations (m = %d, %d terms, family %s)' % (len(vecs), args.m, args.terms, args.family),
          flush=True)
    for v in vecs:
        print(json.dumps(run_config(args.m, vec_to_pairs(v, pairs), args, rng)), flush=True)
    print('# done', flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['validate', 'fit', 'count', 'scan'])
    ap.add_argument('--m', type=int, default=5)
    ap.add_argument('--config', type=str, default='')
    ap.add_argument('--terms', type=int, default=9)
    ap.add_argument('--family', choices=['all', 'star', 'nonstar'], default='all')
    ap.add_argument('--max-pairs', type=int, default=0)
    ap.add_argument('--sample', type=int, default=0)
    ap.add_argument('--shard', type=str, default='')
    ap.add_argument('--restarts', type=int, default=2)
    ap.add_argument('--iters', type=int, default=300)
    ap.add_argument('--tmax', type=float, default=None, help='time limit in seconds for one LM run')
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--real', action='store_true')
    ap.add_argument('--inj', action='store_true')
    ap.add_argument('--border', action='store_true')
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--weights', type=lambda s: [int(x) for x in s.split(',')], default=None)
    ap.add_argument('--save', type=str, default='')
    ap.add_argument('--save-below', type=float, default=1e-6)
    args = ap.parse_args()
    dict(validate=cmd_validate, fit=cmd_fit, count=cmd_count, scan=cmd_scan)[args.cmd](args)
