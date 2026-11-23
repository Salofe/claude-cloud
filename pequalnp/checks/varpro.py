"""Independent check of the 4x4 numerics by variable projection (not the project's LM code).

P = 4x4 permanent tensor. A decomposition with a terms of pairing 01|23, b of 02|13, c of 03|12 exists
iff for some F_v, G_v the 16x16 matrix  M = flat_{01|23}( P - sum_{02|13 terms} - sum_{03|12 terms} )  has
rank <= a.  By Eckart-Young the best choice of the a terms of pairing 01|23 leaves  f = sum_{i>a} sigma_i(M)^2.
We minimise  f / |P|^2  over the b + c other terms only (complex factors), with the SIZE of each of them
(|F||G|, Frobenius) capped by C:   term = C * tanh(rho) * F/|F| (x) G/|G|.
  exact decomposition with terms of size <= C  <=>  min f = 0 at cap C;
  border-only behaviour  <=>  min f > 0 for every finite C, decreasing to 0 as C grows.
Usage: python3 varpro.py a,b,c caps(comma) starts [seed]
"""
import sys, itertools
import numpy as np
import jax, jax.numpy as jnp
from scipy.optimize import minimize
jax.config.update('jax_enable_x64', True)

P = np.zeros((4,) * 4)
for p in itertools.permutations(range(4)):
    P[p] = 1
MP = jnp.array(P.reshape(16, 16))          # rows (j0 j1), columns (j2 j3)

def build(a, b, c):
    nt = b + c
    def M_of(theta, cap):
        z = theta[:nt * 32] + 1j * theta[nt * 32: 2 * nt * 32]
        rho = theta[2 * nt * 32:]
        F = z[:nt * 16].reshape(nt, 4, 4); G = z[nt * 16:].reshape(nt, 4, 4)
        T = jnp.zeros((4, 4, 4, 4), dtype=z.dtype)
        for v in range(nt):
            f = F[v] / jnp.sqrt(jnp.sum(jnp.abs(F[v]) ** 2)); g = G[v] / jnp.sqrt(jnp.sum(jnp.abs(G[v]) ** 2))
            s = cap * jnp.tanh(rho[v])
            if v < b:   # pairing 02|13: F[j0, j2] G[j1, j3]
                T = T + s * jnp.einsum('ac,bd->abcd', f, g)
            else:       # pairing 03|12: F[j0, j3] G[j1, j2]
                T = T + s * jnp.einsum('ad,bc->abcd', f, g)
        return MP - T.reshape(16, 16)
    def obj(theta, cap):
        M = M_of(theta, cap)
        ev = jnp.linalg.eigvalsh(M @ M.conj().T)          # ascending, real
        return jnp.sum(ev[: 16 - a]) / 24.0
    return jax.jit(obj), jax.jit(jax.grad(obj)), 2 * nt * 32 + nt

if __name__ == '__main__':
    a, b, c = (int(x) for x in sys.argv[1].split(','))
    caps = [float(x) for x in sys.argv[2].split(',')]
    starts = int(sys.argv[3]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    obj, gobj, n = build(a, b, c)
    rng = np.random.default_rng(seed)
    print(f"pattern ({a},{b},{c}): min over {starts} starts of the relative residual after optimal rank-{a} projection")
    for cap in caps:
        vals = []
        for _ in range(starts):
            x0 = rng.standard_normal(n)
            r = minimize(lambda x: float(obj(x, cap)), x0, jac=lambda x: np.array(gobj(x, cap)), method='L-BFGS-B',
                         options={'maxiter': 4000, 'ftol': 1e-16, 'gtol': 1e-12})
            vals.append(r.fun)
        vals = np.sort(vals)
        print(f"   cap {cap:8.1f}: min {vals[0]:.4e}   2nd {vals[1]:.4e}   median {vals[len(vals)//2]:.4e}   "
              f"min*cap^2 {vals[0] * cap ** 2:.4f}", flush=True)
