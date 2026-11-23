"""Exact check of the square construction for k = 4 (8 x 8 permanent), dense int32 tensors 8^8,
memory-lean. Same identities as p1_check.py."""
import itertools, math
import numpy as np
k = 4; m = 8
shape = (m,) * m
n = m ** m
# column counts per flat index, computed digit by digit (uint8)
flat = np.arange(n, dtype=np.int64)
cnt = np.zeros((m, n), dtype=np.uint8)
tmp = flat.copy()
digits = []
for pos in range(m):          # last axis is the least significant digit
    d = (tmp % m).astype(np.uint8); tmp //= m
    for c in range(m):
        cnt[c] += (d == c)
del tmp, flat
isperm = np.all(cnt == 1, axis=0)
I = np.all(cnt[:k] == 2, axis=0)
print("perm entries:", int(isperm.sum()), "(8! =", math.factorial(8), ")  I entries:", int(I.sum()),
      "(8!/2^4 =", math.factorial(8) // 16, ")", flush=True)
del cnt
q1 = np.zeros((m,) * k, dtype=np.int32); q2 = np.zeros((m,) * k, dtype=np.int32)
for p in itertools.permutations(range(k)):
    q1[p] = 1; q2[tuple(c + k for c in p)] = 1
def place(R, f, g):
    Rc = tuple(i for i in range(m) if i not in R)
    t = np.multiply.outer(f, g)
    return np.ascontiguousarray(np.transpose(t, np.argsort(R + Rc))).ravel()
pairings = [R for R in itertools.combinations(range(m), k) if 0 in R]
N = len(pairings)
lam0 = np.zeros(n, dtype=np.int32); lam1 = np.zeros(n, dtype=np.int32)
for R in pairings:
    lam0 += place(R, q1, q1)
    lam1 += place(R, q1, q2); lam1 += place(R, q2, q1)
print("N =", N, " lam^1 part == perm:", bool(np.array_equal(lam1, isperm.astype(np.int32))),
      " lam^0 part == 2^(k-1) I:", bool(np.array_equal(lam0, (2 ** (k - 1)) * I.astype(np.int32))), flush=True)
del lam0, lam1
ws = [w for w in itertools.product(range(3), repeat=k) if sum(w) == k]
tup = np.indices((m,) * k).reshape(k, -1)
def mono(w):
    ok = np.ones(tup.shape[1], dtype=bool)
    for c in range(m):
        ok &= ((tup == c).sum(axis=0) == (w[c] if c < k else 0))
    return ok.reshape((m,) * k).astype(np.int32)
acc = np.zeros(n, dtype=np.int32)
R0 = tuple(range(k))
for w in ws:
    acc += place(R0, mono(w), mono(tuple(2 - a for a in w)))
print("T_k =", len(ws), " I == sum of T_k products on R0:", bool(np.array_equal(acc, I.astype(np.int32))),
      " => N + T_k =", N + len(ws), ", N + T_k - 1 =", N + len(ws) - 1, ", Laplace =", 2 * N, flush=True)
