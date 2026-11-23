"""Checks for the proof that codim Z_m = m (GR(perm_m) = m) via 'sum matrices' B_{s,t} = (s_i + t_l).

(1) formula: perm[(s_i + t_l)]_{l != c} = sum_j j!(n-j)! e_{n-j}(s) e_j(t without t_c)        (sympy, m = 3, 4, 5)
(2) for t with d distinct values the set { s : B_{s,t} in Z_m } is cut out by d independent linear conditions on
    (e_1(s), .., e_n(s)): it has dimension n - d, and it is empty for d = m                    (sympy Groebner, m = 4)
(3) point counts over F_q of { (s,t) : B_{s,t} in Z_m } : about c * q^(m-1)                      (m = 3, 4, 5)
"""
import itertools, math
import numpy as np
import sympy as sp

def subperm_syms(m, s, t):
    n = m - 1
    out = []
    for c in range(m):
        cols = [l for l in range(m) if l != c]
        out.append(sp.expand(sum(sp.prod([s[i] + t[sig[i]] for i in range(n)]) for sig in itertools.permutations(cols))))
    return out

def esym(vals, j):
    return sum(sp.prod(c) for c in itertools.combinations(vals, j)) if j else sp.Integer(1)

print("(1) formula check")
for m in (3, 4, 5):
    n = m - 1
    s = sp.symbols(f's0:{n}'); t = sp.symbols(f't0:{m}')
    phis = subperm_syms(m, s, t)
    ok = True
    for c in range(m):
        tc = [t[l] for l in range(m) if l != c]
        rhs = sum(math.factorial(j) * math.factorial(n - j) * esym(s, n - j) * esym(tc, j) for j in range(n + 1))
        ok &= sp.expand(phis[c] - rhs) == 0
    print(f"   m={m}: Phi_c = sum_j j!(n-j)! e_(n-j)(s) e_j(t^(c)) for all c: {ok}")

print("(2) fibres over fixed t, m = 4 (n = 3): Groebner basis of the ideal of {Phi_c(s) = 0} in Q[s0,s1,s2]")
m, n = 4, 3
s = sp.symbols('s0:3')
for tv in [(1, 2, 3, 5), (1, 1, 2, 3), (0, 0, 2, 3), (1, 1, 2, 2), (1, 1, 1, 2), (0, 0, 0, 2), (1, 1, 1, 1), (2, 5, 5, -7)]:
    d = len(set(tv))
    phis = subperm_syms(m, s, tv)
    G = sp.groebner(phis, *s, order='grevlex')
    if list(G.exprs) == [1]:
        dim = 'empty'
    else:
        # dimension via the independent-set bound on leading monomials (exact for a Groebner basis)
        lms = [sp.Poly(g, *s).monoms(order='grevlex')[0] for g in G.exprs]
        dim = -1
        for r in range(n, -1, -1):
            for S in itertools.combinations(range(n), r):
                # S is independent iff no leading monomial involves only variables in S
                if not any(all(e == 0 for i, e in enumerate(lm) if i not in S) for lm in lms):
                    dim = r; break
            if dim >= 0:
                break
    print(f"   t = {tv} (d = {d} distinct values): dimension of the fibre = {dim}   (predicted: {'empty' if d == m else n - d})")

print("(3) point counts of {(s,t) in F_q^n x F_q^m : all maximal subpermanents of (s_i + t_l) vanish}")
def count(m, q):
    n = m - 1
    S = np.array(list(itertools.product(range(q), repeat=n)), dtype=np.int64)      # (q^n, n)
    total = 0; total_distinct = 0
    for tv in itertools.product(range(q), repeat=m):
        ok = np.ones(len(S), dtype=bool)
        for c in range(m):
            cols = [l for l in range(m) if l != c]
            acc = np.zeros(len(S), dtype=np.int64)
            for sig in itertools.permutations(cols):
                pr = np.ones(len(S), dtype=np.int64)
                for i in range(n):
                    pr = pr * (S[:, i] + tv[sig[i]]) % q
                acc += pr
            ok &= (acc % q == 0)
            if not ok.any():
                break
        k = int(ok.sum())
        total += k
        if len(set(tv)) == m:
            total_distinct += k
    return total, total_distinct
for m, qs in ((3, (5, 7, 11, 13)), (4, (5, 7, 11)), (5, (7,))):
    for q in qs:
        tot, dist = count(m, q)
        print(f"   m={m} q={q}: count = {tot}, count / q^(m-1) = {tot / q ** (m - 1):.3f}, "
              f"count / q^m = {tot / q ** m:.3f};  with pairwise distinct t: {dist}", flush=True)
