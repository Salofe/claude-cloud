"""Fast exact-decomposition search: is a tensor (det_m or perm_m) a sum of n split products with given row sets?

Same model as splitrank.py (sum_v F_v(rows S_v) * G_v(rows not in S_v), arbitrary real tensors F_v, G_v), but the
Gauss-Newton matrix J^T J is assembled block by block from small contractions of the factors instead of from
the explicit Jacobian, so 6 x 6 (46656 equations, about 4000 unknowns) takes about a second per iteration.

usage: python3 splitfast.py det|perm M "012;013;..."  [--restarts R] [--seed s] [--iters I]
       row sets separated by ';', a suffix xN repeats a row set N times (e.g. "01x3;02;03").
A run counts as an exact decomposition only if the relative squared residual reaches rounding level (< 1e-20)
with bounded factors; a residual that stalls is evidence, not proof, that none exists.
"""
import argparse, itertools, time
import numpy as np
import scipy.linalg

def sgn(p):
    p = list(p); s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]: s = -s
    return s

def target(kind, m):
    T = np.zeros((m,) * m)
    for p in itertools.permutations(range(m)):
        T[p] = sgn(p) if kind == 'det' else 1
    return T

LO = 'abcdefghij'; UP = 'ABCDEFGHIJ'; SM = 'klmnopqrst'

class Model:
    def __init__(self, m, sets, rng, scale=0.5):
        self.m = m
        self.blocks = []   # (X rows of the free tensor, index of its cofactor block)
        self.par = []
        for S in sets:
            S = tuple(sorted(S)); Sc = tuple(i for i in range(m) if i not in S)
            i = len(self.par)
            self.blocks += [(S, i + 1), (Sc, i)]
            self.par += [rng.standard_normal((m,) * len(S)) * scale, rng.standard_normal((m,) * len(Sc)) * scale]
        self.sizes = [p.size for p in self.par]
        self.off = np.concatenate([[0], np.cumsum(self.sizes)])
    def get(self): return np.concatenate([p.ravel() for p in self.par])
    def set(self, th):
        self.par = [th[self.off[i]:self.off[i + 1]].reshape(self.par[i].shape) for i in range(len(self.par))]
    def value(self):
        Y = 0
        for i in range(0, len(self.par), 2):
            S, _ = self.blocks[i]; Sc, _ = self.blocks[i + 1]
            Y = Y + np.transpose(np.multiply.outer(self.par[i], self.par[i + 1]), np.argsort(S + Sc))
        return Y
    def grad(self, R):
        out = []
        for (X, c) in self.blocks:
            Xc = tuple(i for i in range(self.m) if i not in X)
            out.append(np.tensordot(R, self.par[c], axes=(Xc, tuple(range(len(Xc))))).ravel())
        return np.concatenate(out)
    def gram(self):
        m = self.m; n = self.off[-1]
        H = np.empty((n, n)); I = np.eye(m)
        for p, (X1, c1) in enumerate(self.blocks):
            X1c = [i for i in range(m) if i not in X1]
            for q, (X2, c2) in enumerate(self.blocks):
                if q < p: continue
                X2c = [i for i in range(m) if i not in X2]
                l1 = ''.join(UP[i] if i in X2 else SM[i] for i in X1c)     # cofactor 1 lives on X1^c
                l2 = ''.join(LO[i] if i in X1 else SM[i] for i in X2c)     # cofactor 2 lives on X2^c
                ops = [self.par[c1], self.par[c2]]; subs = [l1, l2]
                for i in X1:
                    if i in X2: ops.append(I); subs.append(LO[i] + UP[i])
                outs = ''.join(LO[i] for i in X1) + ''.join(UP[i] for i in X2)
                B = np.einsum(','.join(subs) + '->' + outs, *ops, optimize=True).reshape(self.sizes[p], self.sizes[q])
                H[self.off[p]:self.off[p + 1], self.off[q]:self.off[q + 1]] = B
                if q > p: H[self.off[q]:self.off[q + 1], self.off[p]:self.off[p + 1]] = B.T
        return H

def lm(model, Y0, iters=400, tol=1e-24, lam=1e-2, verbose=False):
    ynorm = float((Y0 ** 2).sum())
    th = model.get(); R = model.value() - Y0; loss = float((R ** 2).sum()) / ynorm
    hist = [loss]
    for it in range(iters):
        H = model.gram(); g = model.grad(R)
        dg = np.maximum(np.diag(H), 1e-12 * np.trace(H) / len(g))
        ok = False
        for _ in range(25):
            try:
                step = scipy.linalg.solve(H + lam * np.diag(dg), -g, assume_a='pos')
            except Exception:
                lam *= 10; continue
            model.set(th + step); R2 = model.value() - Y0; loss2 = float((R2 ** 2).sum()) / ynorm
            if np.isfinite(loss2) and loss2 < loss:
                ok = True; break
            lam *= 5
        if not ok:
            model.set(th); break
        th, R, loss = th + step, R2, loss2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-13)
        hist.append(loss)
        if verbose and it % 20 == 0: print(f'    it {it} loss {loss:.3e} lam {lam:.1e}', flush=True)
        if loss < tol or (len(hist) > 60 and hist[-60] / loss < 1.05):
            break
    return loss, float(np.sqrt((th ** 2).mean())), len(hist)

def parse(s):
    out = []
    for part in s.split(';'):
        part = part.strip()
        if not part: continue
        mult = 1
        if 'x' in part: part, mm = part.split('x'); mult = int(mm)
        out += [tuple(int(c) for c in part)] * mult
    return out

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('kind'); ap.add_argument('m', type=int); ap.add_argument('sets')
    ap.add_argument('--restarts', type=int, default=3); ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--iters', type=int, default=400); ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    sets = parse(a.sets); Y0 = target(a.kind, a.m)
    print(f'{a.kind}_{a.m}: {len(sets)} split products on row sets {a.sets}', flush=True)
    hits = 0; best = np.inf
    for r in range(a.restarts):
        t0 = time.time(); model = Model(a.m, sets, rng)
        loss, rms, its = lm(model, Y0, iters=a.iters, verbose=a.verbose)
        hits += loss < 1e-20; best = min(best, loss)
        print(f'  restart {r}: relative squared residual {loss:.3e}  rms of unknowns {rms:.2f}  iterations {its}  {time.time() - t0:.0f}s', flush=True)
    print(f'SUMMARY {a.kind}_{a.m} n={len(sets)}: {hits}/{a.restarts} restarts reach rounding level; best residual {best:.3e}', flush=True)
