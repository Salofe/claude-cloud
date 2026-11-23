"""Canonical rectangle partition of the perfect matchings of {0..2k-1} (k even), and the resulting
decomposition of det_2k into C(3k/2, k/2) k-split products.

Rule: order the edges of a perfect matching M by their smaller endpoint; S(M) = union of the first k/2 edges.
For a k-set S with mu = min(complement of S), the matchings with S(M) = S are exactly a u b with
  a a perfect matching of S all of whose edges have an endpoint < mu,   b ANY perfect matching of S^c:
a rectangle X_S x Y_all.  Number of S with X_S nonempty: sum_{mu=k/2..k} C(2k-1-mu, k-mu) = C(3k/2, k/2).

det(R) = Pf(R W R^T) = sum_M sgn(M) prod_{{a,b} in M, a<b} w(r_a, r_b),  w(x,y) = sum_j x_j y_{j+k} - x_{j+k} y_j
(up to a global sign fixed below), so  det = sum_S sgn(S,S^c) F_S(rows S) * Pf(rows S^c),
F_S = sum_{a in X_S} sgn(a) prod w.   Exact check on a random integer matrix."""
import itertools, math, random, sys
from fractions import Fraction

def matchings(vs):
    vs = list(vs)
    if not vs:
        yield []
        return
    a = vs[0]
    for i in range(1, len(vs)):
        b = vs[i]
        rest = vs[1:i] + vs[i + 1:]
        for mm in matchings(rest):
            yield [(a, b)] + mm

def sgn_seq(seq):
    s = 1
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                s = -s
    return s

def sgn_matching(mm):                      # sign of the permutation (a1 b1 a2 b2 ...), a_i < b_i
    return sgn_seq([v for e in mm for v in e])

def det_int(M):
    n = len(M); M = [[Fraction(x) for x in row] for row in M]; d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return 0
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                for cc in range(c, n): M[r][cc] -= f * M[c][cc]
    return d

for k in [int(a) for a in sys.argv[1:]]:
    n = 2 * k
    # combinatorial check of the partition
    count = {}
    for mm in matchings(range(n)):
        first = sorted(mm)[:k // 2]
        S = tuple(sorted(v for e in first for v in e))
        count[S] = count.get(S, 0) + 1
    ok = True
    nb = math.prod(range(k - 1, 0, -2))                     # (k-1)!! matchings of S^c
    for S, c in count.items():
        mu = min(v for v in range(n) if v not in S)
        XS = [a for a in matchings(S) if all(min(e) < mu for e in a)]
        ok &= (c == len(XS) * nb)
    print(f"k={k}: {sum(count.values())} matchings, {len(count)} rectangles (formula C(3k/2,k/2) = {math.comb(3*k//2, k//2)}), "
          f"all rectangles full products X_S x Y_all: {ok};  counting bound {math.ceil(math.comb(2*k,k)/math.comb(k,k//2))},  N = {math.comb(2*k,k)//2}")
    # exact identity on a random integer matrix
    random.seed(k)
    R = [[random.randint(-3, 3) for _ in range(n)] for _ in range(n)]
    w = [[sum(R[a][j] * R[b][j + k] - R[a][j + k] * R[b][j] for j in range(k)) for b in range(n)] for a in range(n)]
    def pf_sum(ms):
        return sum(sgn_matching(a) * math.prod(w[e[0]][e[1]] for e in a) for a in ms)
    total = 0
    for S in count:
        Sc = tuple(v for v in range(n) if v not in S)
        mu = Sc[0]
        XS = [a for a in matchings(S) if all(min(e) < mu for e in a)]
        total += sgn_seq(list(S) + list(Sc)) * pf_sum(XS) * pf_sum(list(matchings(Sc)))
    d = det_int(R)
    print(f"      det = {d},  sum of {len(count)} split products = {total},  ratio {Fraction(total, 1) / d if d else 'n/a'}")
