"""Find a polynomial curve of split sums whose limit is the 4x4 permanent tensor (needs jax).
Usage: python3 splitcurve.py 12,12,12,13,14 <order q> <restarts> [seed]

Each term v has factors F_v(t) = sum_s t^s F_{v,s}, G_v(t) likewise (s = 0..q); we ask
sum_v [F_v(t) | G_v(t)]_{type v} = t^q P + O(t^(q+1))."""
import sys, itertools, numpy as np
import jax, jax.numpy as jnp
jax.config.update('jax_enable_x64', True)

m = 4
P = np.zeros((m,) * 4)
for p in itertools.permutations(range(m)):
    P[p] = 1
Pj = jnp.array(P)
EIN = {'12': 'ab,cd->abcd', '13': 'ac,bd->abcd', '14': 'ad,bc->abcd'}

def build(types, q):
    nt = len(types)
    def coeffs(theta):
        Fs = theta[: nt * (q + 1) * 16].reshape(nt, q + 1, 4, 4)
        Gs = theta[nt * (q + 1) * 16:].reshape(nt, q + 1, 4, 4)
        out = []
        for s in range(q + 1):
            acc = jnp.zeros((4, 4, 4, 4))
            for v, ty in enumerate(types):
                for i in range(s + 1):
                    acc = acc + jnp.einsum(EIN[ty], Fs[v, i], Gs[v, s - i])
            out.append(acc)
        return out
    def res(theta):
        c = coeffs(theta)
        c[q] = c[q] - Pj
        return jnp.concatenate([x.ravel() for x in c])
    return jax.jit(res), jax.jit(jax.jacfwd(res)), 2 * nt * (q + 1) * 16

def lm(res, jac, x, iters=3000, lam=1e-2, verbose=False):
    r = np.array(res(x)); loss = r @ r
    hist = [loss]
    for it in range(iters):
        J = np.array(jac(x)); H = J.T @ J; g = J.T @ r
        dg = np.maximum(np.diag(H), 1e-12 * np.trace(H) / len(g))
        ok = False
        for _ in range(40):
            try: step = np.linalg.solve(H + lam * np.diag(dg), -g)
            except np.linalg.LinAlgError: lam *= 10; continue
            r2 = np.array(res(x + step)); l2 = r2 @ r2
            if np.isfinite(l2) and l2 < loss: ok = True; break
            lam *= 5
        if not ok: break
        x, r, loss = x + step, r2, l2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if verbose and it % 200 == 0: print(f"   it {it} loss {loss:.3e} |x| {np.linalg.norm(x):.2f}", flush=True)
        if loss < 1e-27: break
        if len(hist) > 300 and hist[-300] / loss < 1.05: break
    return x, loss

if __name__ == '__main__':
    types = sys.argv[1].split(',')
    q = int(sys.argv[2]); restarts = int(sys.argv[3]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    res, jac, n = build(types, q)
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    for trial in range(restarts):
        x0 = rng.standard_normal(n) * 0.5
        x, loss = lm(res, jac, x0)
        print(f"types {types} q={q} trial {trial}: residual {loss / 24:.3e} |x| {np.linalg.norm(x):.2f}", flush=True)
        if loss < best[0]: best = (loss, x)
        if loss < 1e-24: break
    print(f"BEST types {types} q={q}: {best[0] / 24:.3e}")
