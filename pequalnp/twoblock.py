"""Border split decompositions of the 2k x 2k permanent in the two-block model (needs jax).

Split the columns into blocks B1 = first k, B2 = last k, and the rows into a k-set R and its
complement. A term is F(rows R) * G(rows R^c) where F = F1 + F2, F1 only uses columns of B1
and F2 only columns of B2 (same for G). Grading the product by how many rows use B1:

    weight (2,0):  F1 G1      must cancel across all terms
    weight (1,1):  F1 G2 + F2 G1   must add up to the permanent
    weight (0,2):  F2 G2      is left free

Any exact solution of the first two conditions gives a border decomposition: rescale the B2
columns by lam, divide by lam, and the free part enters with a factor lam. For k = 2 this is
exactly the Lean-checked five-term identity (lean/PvsNP/FiveTerm.lean).

The (1,1) condition is block diagonal: only terms with row set R or R^c contribute to the
components of the pairing {R, R^c}, so every pairing needs at least one term. The classical
count (Laplace) is two terms per pairing, C(2k, k) in total.

Usage: python3 twoblock.py <k> <counts> [restarts] [seed]
  counts: number of terms per pairing, in the order printed by --list, e.g. 3,1,1 for k = 2.
"""
import itertools
import sys

import numpy as np
import jax
import jax.numpy as jnp

jax.config.update('jax_enable_x64', True)


def pairings(k):
    return [R for R in itertools.combinations(range(2 * k), k) if 0 in R]


def perm_indicator(k):
    T = np.zeros((k,) * k)
    for p in itertools.permutations(range(k)):
        T[p] = 1
    return T


def build(k, counts):
    prs = pairings(k)
    assert len(counts) == len(prs)
    terms = [i for i, c in enumerate(counts) for _ in range(c)]  # pairing index of each term
    nt = len(terms)
    d = k ** k
    one = jnp.array(perm_indicator(k).ravel())
    target = jnp.outer(one, one)
    # axes permutation that puts (rows of R, rows of R^c) back in row order
    orders = []
    for R in prs:
        Rc = tuple(i for i in range(2 * k) if i not in R)
        orders.append(tuple(int(i) for i in np.argsort(R + Rc)))

    def res(theta):
        F1, F2, G1, G2 = theta.reshape(4, nt, d)
        out = []
        acc20 = jnp.zeros((k,) * (2 * k))
        for v, pi in enumerate(terms):
            t = jnp.outer(F1[v], G1[v]).reshape((k,) * (2 * k))
            acc20 = acc20 + jnp.transpose(t, orders[pi])
        out.append(acc20.ravel())
        for pi in range(len(prs)):
            a = -target
            b = -target
            for v, pv in enumerate(terms):
                if pv == pi:
                    a = a + jnp.outer(F1[v], G2[v])
                    b = b + jnp.outer(F2[v], G1[v])
            out.append(a.ravel())
            out.append(b.ravel())
        return jnp.concatenate(out)

    return jax.jit(res), jax.jit(jax.jacfwd(res)), 4 * nt * d, nt


def lm(res, jac, x, iters=600, lam=1e-2):
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
        if loss < 1e-26 or (len(hist) > 80 and hist[-80] / loss < 1.02):
            break
    return x, loss


if __name__ == '__main__':
    k = int(sys.argv[1])
    if sys.argv[2] == '--list':
        for i, R in enumerate(pairings(k)):
            print(i, ''.join(str(r + 1) for r in R))
        sys.exit(0)
    counts = [int(c) for c in sys.argv[2].split(',')]
    restarts = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    res, jac, n, nt = build(k, counts)
    rng = np.random.default_rng(seed)
    scale = np.sqrt(float(np.math.factorial(k)) if hasattr(np, 'math') else 1.0)
    norm2 = 2 * len(counts) * float(len(list(itertools.permutations(range(k)))) ** 2)
    best, hits = np.inf, 0
    for trial in range(restarts):
        x0 = rng.standard_normal(n) * 0.5
        x, loss = lm(res, jac, x0)
        rel = loss / norm2
        best = min(best, rel)
        hits += rel < 1e-22
        print(f"  trial {trial}: relative residual {rel:.3e} |x| {np.linalg.norm(x):.1f}", flush=True)
    print(f"SUMMARY k={k} counts={counts} terms={nt} (classical {2 * len(counts)}): "
          f"{hits}/{restarts} exact, best {best:.3e}", flush=True)
