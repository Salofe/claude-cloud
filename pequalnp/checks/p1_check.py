"""Independent exact check of the square construction (P1) for k = 2, 3, 4.
Dense integer tensors of shape (2k,)*(2k). Written from scratch (does not import project code).

Graded identity to check (one term per unordered pairing {R, R^c}, R containing row 0):
  lam^0:  sum_pairings q1(R) q1(R^c)                      == 2^(k-1) * I
          I = indicator of index tuples using each of the first k columns exactly twice
          I == sum_{w in {0,1,2}^k, |w| = k} mono_w(R0) (x) mono_{2-w}(R0^c)   (T_k terms)
  lam^1:  sum_pairings [q1(R) q2(R^c) + q2(R) q1(R^c)]    == perm tensor
so  lam*perm = sum_pairings (q1+lam q2)(R) (q1+lam q2)(R^c) - 2^(k-1) I - lam^2 * (N products).
"""
import itertools, sys, math
import numpy as np

def run(k):
    m = 2 * k
    shape = (m,) * m
    # permanent tensor
    P = np.zeros(shape, dtype=np.int64)
    for p in itertools.permutations(range(m)):
        P[p] = 1
    # k-row tensors: q1 = perm on columns 0..k-1, q2 = perm on columns k..2k-1 (as tensors over all m columns)
    q1 = np.zeros((m,) * k, dtype=np.int64)
    q2 = np.zeros((m,) * k, dtype=np.int64)
    for p in itertools.permutations(range(k)):
        q1[p] = 1
        q2[tuple(c + k for c in p)] = 1

    def place(R, f, g):
        Rc = tuple(i for i in range(m) if i not in R)
        t = np.multiply.outer(f, g)
        return np.transpose(t, np.argsort(R + Rc))

    pairings = [R for R in itertools.combinations(range(m), k) if 0 in R]
    N = len(pairings)
    assert N == math.comb(m, k) // 2
    lam0 = np.zeros(shape, dtype=np.int64)
    lam1 = np.zeros(shape, dtype=np.int64)
    for R in pairings:
        lam0 += place(R, q1, q1)
        lam1 += place(R, q1, q2) + place(R, q2, q1)
    # indicator I
    I = np.zeros(shape, dtype=np.int64)
    idx = np.indices(shape).reshape(m, -1)            # (m, m^m)
    cnt_ok = np.ones(idx.shape[1], dtype=bool)
    for c in range(m):
        cnt = (idx == c).sum(axis=0)
        cnt_ok &= (cnt == (2 if c < k else 0))
    I = cnt_ok.reshape(shape).astype(np.int64)
    ok1 = np.array_equal(lam1, P)
    ok0 = np.array_equal(lam0, 2 ** (k - 1) * I)
    # expansion of I along R0 = rows 0..k-1 into T_k products
    ws = [w for w in itertools.product(range(3), repeat=k) if sum(w) == k]
    Tk = len(ws)
    tup = np.indices((m,) * k).reshape(k, -1)
    def mono(w):
        ok = np.ones(tup.shape[1], dtype=bool)
        for c in range(m):
            ok &= ((tup == c).sum(axis=0) == (w[c] if c < k else 0))
        return ok.reshape((m,) * k).astype(np.int64)
    R0 = tuple(range(k))
    acc = np.zeros(shape, dtype=np.int64)
    for w in ws:
        acc += place(R0, mono(w), mono(tuple(2 - a for a in w)))
    okI = np.array_equal(acc, I)
    # rank of the R0-flattening of I (to confirm T_k is optimal for a single pairing)
    if k <= 3:
        rk = np.linalg.matrix_rank(I.reshape(m ** k, m ** k).astype(float))
    else:
        rk = None
    # the refinement: w = (1..1) product merges with the square on R0 (weighted square), N + T_k - 1
    print(f"k={k}: N={N} T_k={Tk} lam^1 part == perm: {ok1};  lam^0 part == 2^(k-1) I: {ok0};  "
          f"I == sum of T_k products on R0: {okI};  rank of R0-flattening of I: {rk};  "
          f"count N+T_k={N+Tk}, N+T_k-1={N+Tk-1}, Laplace={2*N}", flush=True)

for k in [int(a) for a in sys.argv[1:]]:
    run(k)
