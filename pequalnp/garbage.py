"""How many extra terms does the square construction need? (needs jax)

Two-block border decompositions of the 2k x 2k permanent (see twoblock.py) reduce to this:
every pairing {R, R^c} of the rows gets one "square" term, and the squares leave behind

    Gamma(c) = sum over pairings  c_pi * q(R) * q(R^c),     every c_pi nonzero,

where q(R) is the k x k permanent of rows R on the first k columns. The number of terms of
the border decomposition is  N + E,  N = C(2k, k) / 2 the number of pairings and E the least
number of split products (any pairings, any factors) that add up to -Gamma(c) for some
choice of nonzero c. Laplace expansion corresponds to E = N.

This script fixes E and a choice of pairings for the extra terms, and solves for c and the
factors over the complex numbers, with every c_pi of modulus one (free phase). A relative residual at rounding level with every |c_pi| bounded away from zero is a
border decomposition with N + E terms.

Usage: python3 garbage.py <k> <E> [max_configs] [restarts] [seed]
"""
import itertools
import sys

import numpy as np
import jax
import jax.numpy as jnp

jax.config.update('jax_enable_x64', True)

# 0.0: every c_pi has modulus one (only its phase is free). 1.0: moduli are free too, which
# lets the solver run off to c_pi = 0, so use it only to polish a modulus-one solution.
MOD = 0.0


def pairings(k):
    return [R for R in itertools.combinations(range(2 * k), k) if 0 in R]


def perm_indicator(k):
    T = np.zeros((k,) * k)
    for p in itertools.permutations(range(k)):
        T[p] = 1
    return T


def setup(k):
    prs = pairings(k)
    orders = []
    for R in prs:
        Rc = tuple(i for i in range(2 * k) if i not in R)
        orders.append(tuple(int(i) for i in np.argsort(R + Rc)))
    q = perm_indicator(k)
    V = np.stack([np.transpose(np.multiply.outer(q, q), orders[i]).ravel() for i in range(len(prs))])
    return prs, orders, V


def build(k, extra, orders, V):
    """extra: tuple of pairing indices, one per extra term. Unknowns: c (N, with c_0 = 1) and
    the factors of the extra terms."""
    N = V.shape[0]
    E = len(extra)
    d = k ** k
    Vj = jnp.array(V)

    def res(theta):
        # complex unknowns stored as (real, imaginary) halves; c_pi = exp(a + i b) is never zero
        half = theta.shape[0] // 2
        z = theta[:half] + 1j * theta[half:]
        c = jnp.concatenate([jnp.ones(1, dtype=z.dtype), jnp.exp(MOD * z[:N - 1].real + 1j * z[:N - 1].imag)])
        F = z[N - 1:N - 1 + E * d].reshape(E, d)
        G = z[N - 1 + E * d:].reshape(E, d)
        acc = c @ Vj.astype(z.dtype)
        acc = acc.reshape((k,) * (2 * k))
        for e, pi in enumerate(extra):
            t = jnp.outer(F[e], G[e]).reshape((k,) * (2 * k))
            acc = acc + jnp.transpose(t, orders[pi])
        r = acc.ravel()
        return jnp.concatenate([r.real, r.imag])

    return jax.jit(res), jax.jit(jax.jacfwd(res)), 2 * (N - 1 + 2 * E * d)


def lm(res, jac, x, iters=400, lam=1e-2):
    r = np.array(res(x))
    loss = r @ r
    hist = [loss]
    for _ in range(iters):
        J = np.array(jac(x))
        H = J.T @ J
        g = J.T @ r
        dg = np.maximum(np.diag(H), 1e-12 * np.trace(H) / len(g))
        ok = False
        for _ in range(40):
            try:
                step = np.linalg.solve(H + lam * np.diag(dg), -g)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            r2 = np.array(res(x + step))
            l2 = r2 @ r2
            if np.isfinite(l2) and l2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            break
        x, r, loss = x + step, r2, l2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if loss < 1e-26 or (len(hist) > 60 and hist[-60] / loss < 1.02):
            break
    return x, loss


def canonical_configs(k, E, prs):
    """Multisets of E pairings up to permutations of the rows."""
    n = 2 * k
    idx = {frozenset(R): i for i, R in enumerate(prs)}

    def image(i, p):
        R = frozenset(p[r] for r in prs[i])
        if 0 not in R:
            R = frozenset(range(n)) - R
        return idx[R]

    perms = list(itertools.permutations(range(n)))
    if len(perms) > 720:
        rng = np.random.default_rng(0)
        perms = [perms[i] for i in rng.choice(len(perms), 720, replace=False)]
    table = [[image(i, p) for i in range(len(prs))] for p in perms]
    seen, out = set(), []
    for combo in itertools.combinations_with_replacement(range(len(prs)), E):
        key = min(tuple(sorted(t[i] for i in combo)) for t in table)
        if key not in seen:
            seen.add(key)
            out.append(combo)
    return out


if __name__ == '__main__':
    k = int(sys.argv[1])
    E = int(sys.argv[2])
    max_configs = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    prs, orders, V = setup(k)
    N = len(prs)
    rng = np.random.default_rng(seed)
    cfgs = canonical_configs(k, E, prs)
    if max_configs and len(cfgs) > max_configs:
        cfgs = [cfgs[i] for i in sorted(rng.choice(len(cfgs), max_configs, replace=False))]
    names = [''.join(str(r + 1) for r in R) for R in prs]
    found = 0
    best_all = np.inf
    for extra in cfgs:
        res, jac, n = build(k, extra, orders, V)
        best, bestc = np.inf, None
        for _ in range(restarts):
            x0 = rng.standard_normal(n) * 0.5
            x, loss = lm(res, jac, x0)
            half = len(x) // 2
            c = np.concatenate([[1.0], np.exp(MOD * x[:N - 1] + 1j * x[half:half + N - 1])])
            rel = loss / float(V[0] @ V[0])
            if rel < best:
                best, bestc = rel, c
        ok = best < 1e-22 and np.abs(bestc).min() > 1e-4 and np.abs(bestc).max() < 1e4
        found += ok
        best_all = min(best_all, best)
        tag = "BORDER DECOMPOSITION" if ok else ("degenerate c" if best < 1e-22 else "")
        print(f"  extra on {[names[i] for i in extra]}: residual {best:.2e} min|c| {np.abs(bestc).min():.2e} "
              f"max|c| {np.abs(bestc).max():.2e} {tag}", flush=True)
    print(f"SUMMARY k={k} E={E}: {found} of {len(cfgs)} configurations give a border decomposition with "
          f"{N + E} terms (classical {2 * N}); best residual {best_all:.2e}", flush=True)
