"""Exact-arithmetic checks of open, self-contained statements on the pequalnp.com record.

Each check either confirms the statement on exact rational/integer arithmetic (for the concrete
instances this is a full verification of the mathematical content; for the universally
quantified ones it is a bounded search for a counterexample) or reports a counterexample.
Nothing here is a Lean proof: the project's only judge is its Lean checker.
"""
from fractions import Fraction as F
from itertools import product, permutations
from math import comb
import random

results = {}


def report(lemma, ok, note):
    results[lemma] = (ok, note)
    print(f"{lemma}: {'HOLDS' if ok else 'FAILS'} - {note}")


# ---- integer polynomials as coefficient lists (index = degree) ----
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pneg(a):
    return [-x for x in a]


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def ppow(a, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, a)
    return out


def mono(c, d):
    return [0] * d + [c]


def psum(*terms):
    out = [0]
    for t in terms:
        out = padd(out, t)
    return out


def peval(a, x):
    acc = 0
    for c in reversed(a):
        acc = acc * x + c
    return acc


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def divides_monic(d, a):
    """Does the monic integer polynomial d divide a? (exact long division)"""
    a = trim(a)
    d = trim(d)
    assert d[-1] == 1
    while len(a) >= len(d):
        c = a[-1]
        s = len(a) - len(d)
        for i, x in enumerate(d):
            a[s + i] -= c * x
        a = trim(a)
    return not a


def sign_changes(vals):
    return all(vals[i] * vals[i + 1] < 0 for i in range(len(vals) - 1))


# L-gct-126, L-gct-154: polynomial identities over Z imply them in every commutative ring.
# Checked on a grid that exceeds the degree in every variable (degree <= 3, resp. <= 9).
ok = all(24 * x * y * z == (x + y + z) ** 3 - (x + y - z) ** 3 - (x - y + z) ** 3 + (x - y - z) ** 3
         for x, y, z in product(range(-3, 4), repeat=3))
report("L-gct-126", ok, "Fischer identity, exact on a 7^3 integer grid (degree 3 per variable)")

ok = all((g + e) ** 3 + (g - e) ** 3 + 2 * (e * e * f - g) ** 3
         == 6 * e * e * g * (1 + f * g) - 6 * e ** 4 * g * f * f + 2 * e ** 6 * f ** 3
         for g, e, f in product(range(-5, 6), repeat=3))
report("L-gct-154", ok, "three-cubes identity, exact on an 11^3 integer grid (degree <= 6 per variable)")

# L-gct-132
u = psum(mono(360, 0), mono(-342, 1), mono(42, 3))
v = psum(mono(119, 2), mono(-60, 3), mono(1, 4))
w = padd(pmul(u, u), pneg(pmul(v, v)))
d = [1]
for j in range(1, 7):
    d = pmul(d, [-j, 1])
report("L-gct-132", divides_monic(d, w) and any(trim(w)),
       "(X-1)...(X-6) | u^2 - v^2 by exact division, and u^2 - v^2 != 0")

# L-gct-147
u = psum(mono(-57, 0), mono(912, 5), mono(-969, 6), mono(969, 16), mono(-912, 17), mono(57, 22))
v = psum(mono(272, 1), mono(-374, 2), mono(646, 10), mono(-646, 12), mono(374, 20), mono(-272, 21))
w = padd(pmul(u, u), pneg(pmul(v, v)))
report("L-gct-147", divides_monic(ppow([-1, 1], 16), w) and not divides_monic(ppow([-1, 1], 17), w),
       "(X-1)^16 | u^2 - v^2 and (X-1)^17 does not, by exact division")


# L-gct-137: four sign changes of the polynomial on rationals in (0, 1) give four roots.
def f137(x):
    return 200 * x ** 14 - 200 * x ** 13 + 25 * x ** 2 - 25 * x + 6


pts = [F(k, 1000) for k in range(1, 1000)]
vals = [f137(x) for x in pts]
brackets = [(pts[i], pts[i + 1]) for i in range(len(pts) - 1) if vals[i] * vals[i + 1] < 0]
report("L-gct-137", len(brackets) >= 4,
       f"{len(brackets)} sign changes on the grid k/1000 in (0,1); brackets {[(str(a), str(b)) for a, b in brackets]}")


# L-gct-141: seven sign changes at positive rationals give seven positive roots.
def f141(x):
    return ((26281829643807702458406 * x ** 18 - 315357758844690494658 * x ** 35) * (7705 + 21 * x ** 25)
            - (-150303984092195142770 + 673011295193275874620 * x ** 4) * (8817 + 375016 * x ** 13))


pts = [F(k, 2000) for k in range(1, 8000)]
vals = [f141(x) for x in pts]
zeros = [str(p) for p, val in zip(pts, vals) if val == 0]
brackets = [(pts[i], pts[i + 1]) for i in range(len(pts) - 1) if vals[i] * vals[i + 1] < 0]
report("L-gct-141", len(brackets) + len(zeros) >= 7,
       f"{len(brackets)} sign changes and {len(zeros)} exact zeros on the grid k/2000 in (0,4); "
       f"brackets {[(str(a), str(b)) for a, b in brackets]}")


# L-gct-146: exists six increasing positive rationals with five sign changes.
def f146(x):
    return -x ** 6 + 2 * 10 ** 8 * x ** 5 - 10 ** 16 * x ** 4 + 10 ** 24 * (x - 1) ** 2


cands = sorted(set([F(1, 2), F(9, 10), F(99, 100), F(999, 1000), F(9999, 10000), F(1), F(10001, 10000),
                    F(1001, 1000), F(11, 10), F(2), F(10), F(100), F(1000)]
                   + [F(10) ** k for k in range(3, 10)] + [F(10) ** 8 + s * F(10) ** k for k in range(0, 9) for s in (-1, 1)]
                   + [F(2 * 10 ** 8), F(3 * 10 ** 8), F(10 ** 9)]))
chain = []
for x in cands:
    val = f146(x)
    if x > 0 and val != 0 and (not chain or chain[-1][1] * val < 0):
        chain.append((x, val))
report("L-gct-146", len(chain) >= 6,
       f"alternating chain of length {len(chain)}: {[str(x) for x, _ in chain[:6]]}")


# L-gct-148 and L-gct-155: nine sign changes on the ten stated points.
def f148(x):
    s = F(1, 16)
    return (s ** 9 * x ** 7 - s ** 16 * x ** 9) ** 3 + (-x + s ** 25 * x ** 11) ** 3 + (s * x ** 3 - s ** 4 * x ** 5) ** 3


pts = [F(4), F(9), F(64), F(4097, 64), F(65), F(1025), F(16380), F(16384), F(32769), F(262144)]
vals = [f148(x) for x in pts]
report("L-gct-148", sign_changes(vals), f"signs at the ten points: {''.join('+' if x > 0 else '-' if x < 0 else '0' for x in vals)}")


def f155(x):
    return (40 * x ** 7 - 13 * x ** 9) ** 3 + (x ** 11 - x) ** 3 + (13 * x ** 3 - 40 * x ** 5) ** 3


pts = [F(1, 4), F(2, 5), F(1, 2), F(3, 4), F(9, 10), F(11, 10), F(3, 2), F(2), F(5, 2), F(3)]
vals = [f155(x) for x in pts]
report("L-gct-155", sign_changes(vals), f"signs at the ten points: {''.join('+' if x > 0 else '-' if x < 0 else '0' for x in vals)}")

# L-gct-145: bounded search, m <= 220.
bad = [(m, k) for m in range(0, 221) for k in range(0, m // 2 + 1)
       if sum(comb(m, w_) for w_ in range(k + 1)) * (k ** k * (m - k) ** (m - k)) > m ** m]
report("L-gct-145", not bad, f"no counterexample with m <= 220 (0^0 = 1 as in Lean){'' if not bad else ' first: ' + str(bad[0])}")

# L-gct-127: bounded search.
pc = lambda a: bin(a).count("1")
bad = [(a, b) for a in range(0, 700) for b in range(0, 700) if pc(a + b) > pc(a) + pc(b)]
report("L-gct-127", not bad, "no counterexample with a, b < 700")

# L-gct-149: exhaustive for n <= 5 with alpha_j <= 4, plus random larger cases.
bad = []
for n in range(0, 6):
    for al in product(range(5), repeat=n):
        E = sum(a * 2 ** j for j, a in enumerate(al))
        if pc(E) > sum(al) or 2 * E > sum(al) * 2 ** n:
            bad.append((n, al))
rng = random.Random(1)
for _ in range(20000):
    n = rng.randint(0, 12)
    al = [rng.randint(0, 40) for _ in range(n)]
    E = sum(a * 2 ** j for j, a in enumerate(al))
    if pc(E) > sum(al) or 2 * E > sum(al) * 2 ** n:
        bad.append((n, al))
report("L-gct-149", not bad, "no counterexample: exhaustive n <= 5, alpha <= 4, plus 20000 random cases")


# L-gct-144: the greedy split (close a block once M * sum would exceed total) -- search for a list where no split works.
def has_split(M, q, l):
    total = sum(l)
    # dynamic programme over (position, blocks used): can the rest be split?
    n = len(l)
    reach = {0}
    for _ in range(M):
        nxt = set()
        for s in reach:
            acc = 0
            nxt.add(s)
            for e in range(s, n):
                acc += l[e]
                if M * acc > total + M * q:
                    break
                nxt.add(e + 1)
        reach = nxt
    return n in reach


bad = []
for M in range(1, 5):
    for q in range(0, 4):
        for n in range(0, 7):
            for l in product(range(q + 1), repeat=n):
                if not has_split(M, q, list(l)):
                    bad.append((M, q, l))
report("L-gct-144", not bad, "no counterexample: exhaustive M <= 4, q <= 3, length <= 6")

# L-pcx-083
ok = all(4 * 4 ** k <= 5 ** k for k in range(7, 400)) and all(16 * 4 ** k <= 9 * 5 ** k for k in range(3, 400))
tight = (4 * 4 ** 6 > 5 ** 6, 16 * 4 ** 2 > 9 * 5 ** 2)
report("L-pcx-083", ok, f"holds for k < 400; thresholds are sharp (fails at k = 6 / k = 2): {tight}")

# L-pcx-087, L-pcx-088: exhaustive for n <= 3 (both are coordinatewise, so n = 1 decides them).
h = lambda a, b: sum(x != y for x, y in zip(a, b))
bad87, bad88 = [], []
for n in range(0, 4):
    for u_, u2, v_, v2 in product(product((0, 1), repeat=n), repeat=4):
        if h(u_, v_) > h(u_, v2) + h(u2, v2) + h(u2, v_):
            bad87.append((u_, u2, v_, v2))
        if (h(u_, v_) + h(u_, v2) + h(u2, v2) + h(u2, v_)) % 2:
            bad88.append((u_, u2, v_, v2))
report("L-pcx-087", not bad87, "exhaustive for n <= 3; the inequality is coordinatewise")
report("L-pcx-088", not bad88, "exhaustive for n <= 3; the parity is coordinatewise")

# L-gct-134: order-4 identity on doubly centred p x q rational matrices (random exact instances).
rng = random.Random(7)
bad = []
for p_, q_ in [(1, 1), (2, 2), (2, 3), (3, 3), (4, 4), (4, 5), (5, 5), (3, 6), (6, 4)]:
    for _ in range(3):
        t = [[F(rng.randint(-5, 5)) for _ in range(q_)] for _ in range(p_)]
        for i in range(p_):  # centre rows, then columns
            m = sum(t[i]) / q_
            t[i] = [x - m for x in t[i]]
        for j in range(q_):
            m = sum(t[i][j] for i in range(p_)) / p_
            for i in range(p_):
                t[i][j] -= m
        lhs = sum(t[f[0]][g[0]] * t[f[1]][g[1]] * t[f[2]][g[2]] * t[f[3]][g[3]]
                  for f in permutations(range(p_), 4) for g in permutations(range(q_), 4))
        p4 = sum(x ** 4 for r in t for x in r)
        R4 = sum(sum(x * x for x in r) ** 2 for r in t)
        C4 = sum(sum(t[i][j] ** 2 for i in range(p_)) ** 2 for j in range(q_))
        Q = sum(t[i][j] * t[i][j2] * t[i2][j] * t[i2][j2]
                for i in range(p_) for i2 in range(p_) for j in range(q_) for j2 in range(q_))
        p2 = sum(x * x for r in t for x in r)
        if lhs != 36 * p4 - 18 * (R4 + C4) + 6 * Q + 3 * p2 ** 2:
            bad.append((p_, q_))
report("L-gct-134", not bad, f"exact on 27 random doubly centred rational matrices up to 6 x 4{'' if not bad else ' FAILS at ' + str(bad[:3])}")

print()
print(f"{sum(ok for ok, _ in results.values())} of {len(results)} statements hold on these checks; "
      f"failing: {[k for k, (ok, _) in results.items() if not ok] or 'none'}")
