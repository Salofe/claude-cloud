"""Where integer factoring actually stands, measured.

- Pollard rho (Brent) and p-1 are run on balanced semiprimes n = p*q of growing
  size. rho costs ~ n^(1/4); it dies on balanced factors past ~2^55-60 each.
- sympy.factorint (trial div + rho + p-1 + a little ECM/Fermat) is timed too; it
  has no number-field sieve, so it also stalls on balanced semiprimes.
- The real state of the art is GNFS, cost L_n[1/3, 1.923]. We extrapolate it to
  RSA-768 (done 2009), RSA-250 (done 2020) and RSA-2048 (never), using the public
  CPU-year figures as anchors.

Nothing here moves toward "factoring is in P": every known algorithm is
super-polynomial, and there is no accepted path to a polynomial one.
"""
import math, time, random, sys
from sympy import nextprime, factorint


def brent_rho(n, budget=5_000_000):
    if n % 2 == 0:
        return 2
    random.seed(n)
    y, c, m = random.randint(1, n - 1), random.randint(1, n - 1), 128
    g = q = 1
    r = 1
    steps = 0
    while g == 1:
        x = y
        for _ in range(r):
            y = (y * y + c) % n
        k = 0
        while k < r and g == 1:
            ys = y
            for _ in range(min(m, r - k)):
                y = (y * y + c) % n
                q = (q * abs(x - y)) % n
                steps += 1
                if steps > budget:
                    return None
            g = math.gcd(q, n)
            k += m
        r *= 2
    if g == n:
        while True:
            ys = (ys * ys + c) % n
            g = math.gcd(abs(x - ys), n)
            if g > 1:
                break
    return g if 1 < g < n else None


def pollard_pm1(n, B=100000):
    a = 2
    for p in _primes_up_to(B):
        pe = p
        while pe * p <= B:
            pe *= p
        a = pow(a, pe, n)
    g = math.gcd(a - 1, n)
    return g if 1 < g < n else None


def _primes_up_to(B):
    sieve = bytearray([1]) * (B + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(B ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(2, B + 1) if sieve[i]]


def semiprime(bits, seed):
    random.seed(seed)
    half = bits // 2
    p = nextprime(random.getrandbits(half) | (1 << (half - 1)))
    q = nextprime(random.getrandbits(bits - half) | (1 << (bits - half - 1)))
    return int(p) * int(q), int(p), int(q)


def L(n, a=1.0 / 3, c=1.923):
    ln = math.log(n)
    return math.exp(c * ln ** a * math.log(ln) ** (1 - a))


if __name__ == "__main__":
    print("=== Pollard rho / p-1 / sympy on balanced semiprimes n = p*q (p,q ~ equal size) ===")
    print("bits | rho time (budget 5M steps) | sympy.factorint time")
    for bits in [40, 50, 60, 70, 80, 90, 100]:
        n, p, q = semiprime(bits, seed=bits)
        t0 = time.time(); r = brent_rho(n); tr = time.time() - t0
        rstr = f"{tr:6.2f}s ok" if r in (p, q) else (f"{tr:6.2f}s gave up" if r is None else f"{tr:6.2f}s ?")
        # sympy with a hard time cap via a step: just time it but cap bits where it stays fast
        if bits <= 80:
            t0 = time.time(); fac = factorint(n); ts = time.time() - t0
            sstr = f"{ts:6.2f}s {'ok' if set(fac) == {p, q} else '?'}"
        else:
            sstr = "(skipped; balanced & slow)"
        print(f" {bits:3d} | {rstr:24s} | {sstr}")

    print()
    print("=== GNFS extrapolation (heuristic op count L_n[1/3,1.923]), anchored to public records ===")
    anchors = {
        "RSA-512  (512 bit, broken 1999)": 512,
        "RSA-768  (768 bit, broken 2009, ~2000 CPU-yr)": 768,
        "RSA-795  (broken 2019)": 795,
        "RSA-829  (RSA-250, broken 2020, ~2700 CPU-yr)": 829,
        "RSA-1024 (never broken publicly)": 1024,
        "RSA-2048 (target of all modern security)": 2048,
    }
    base_bits, base_cpu_years = 829, 2700.0   # RSA-250 anchor
    base = L(2 ** base_bits)
    for name, b in anchors.items():
        ratio = L(2 ** b) / base
        cpu_years = base_cpu_years * ratio
        print(f"  {name:48s}: ~{cpu_years:.3e} CPU-years  (relative to RSA-250)")
    print()
    print("  This crude single-constant L-extrapolation puts RSA-2048 at ~2e11 x the effort of")
    print("  RSA-250 (~6e14 CPU-years). Optimized published estimates are lower (~1e9 core-years)")
    print("  but still far beyond any feasible computation. There is no known sub-GNFS classical")
    print("  method and no accepted path to a polynomial-time algorithm. (Quantum Shor factors in")
    print("  poly time but needs millions of stable logical qubits, which do not exist.)")
