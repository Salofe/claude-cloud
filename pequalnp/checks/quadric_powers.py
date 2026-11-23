"""Is the monomial x_1 ... x_{2k} a sum of s k-th powers of quadratic forms (complex coefficients)?
   prod x_j = sum_{i<s} (x^T Q_i x)^k,  Q_i complex symmetric 2k x 2k (scalars absorbed).
Least squares on random real sample points (more points than monomials of degree 2k), Levenberg-Marquardt.
A limit (border) solution shows up as residual -> 0 with growing |Q|."""
import sys, math, numpy as np
k = int(sys.argv[1]); s = int(sys.argv[2]); starts = int(sys.argv[3]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
n = 2 * k
nmon = math.comb(n + 2 * k - 1, 2 * k)
P = int(1.3 * nmon) + 50
rng = np.random.default_rng(1234)
X = rng.standard_normal((P, n)); X /= np.linalg.norm(X, axis=1, keepdims=True) / math.sqrt(n)
target = X.prod(axis=1)
iu = np.triu_indices(n)
nq = len(iu[0])
# monomials x_a x_b (a<=b) at the sample points
Z = X[:, iu[0]] * X[:, iu[1]] * np.where(iu[0] == iu[1], 1.0, 2.0)      # (P, nq): x^T Q x = Z @ q
tn = np.linalg.norm(target)
def res_jac(q):                                   # q complex (s, nq)
    V = Z @ q.T                                   # (P, s) values of the quadrics
    r = (V ** k).sum(axis=1) - target
    J = (k * V ** (k - 1))[:, :, None] * Z[:, None, :]          # (P, s, nq) complex derivative wrt q (holomorphic)
    return r, J.reshape(P, s * nq)
def lm(q, iters=300):
    lam = 1e-2
    r, J = res_jac(q); loss = np.vdot(r, r).real
    for it in range(iters):
        H = J.conj().T @ J; g = J.conj().T @ r
        ok = False
        for _ in range(25):
            try:
                step = np.linalg.solve(H + lam * np.diag(np.maximum(np.diag(H).real, 1e-12)), -g)
            except np.linalg.LinAlgError:
                lam *= 10; continue
            q2 = q + step.reshape(s, nq)
            r2, J2 = res_jac(q2); l2 = np.vdot(r2, r2).real
            if np.isfinite(l2) and l2 < loss:
                ok = True; break
            lam *= 5
        if not ok: break
        q, r, J, loss = q2, r2, J2, l2
        lam = max(lam / 3, 1e-12)
        if loss / tn ** 2 < 1e-26: break
    return q, loss / tn ** 2
rng2 = np.random.default_rng(seed)
best = np.inf; hits = 0
for st in range(starts):
    q = (rng2.standard_normal((s, nq)) + 1j * rng2.standard_normal((s, nq))) * 0.3
    q, rel = lm(q)
    best = min(best, rel); hits += rel < 1e-20
    print(f"  start {st}: relative residual {rel:.3e}  max|Q| {np.abs(q).max():.2f}", flush=True)
print(f"SUMMARY k={k} (n={n}, {nmon} monomials, {P} points) s={s}: {hits}/{starts} solved, best {best:.3e}   [pairing bound 2^(k-1) = {2 ** (k - 1)}]")
