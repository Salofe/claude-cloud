"""Generic birthday-collision cost on real (full 64-round) SHA-256, output
truncated to n bits, via memory-free Pollard-rho. Measures the hash rate and
extrapolates the cost of a full 128-bit (collision) and 256-bit (preimage) wall.
This is the generic bound every hash must meet; it is not a structural attack.
"""
import hashlib, os, time, math


def trunc(v, nbytes, mask):
    return int.from_bytes(hashlib.sha256(v.to_bytes(nbytes, "big")).digest(), "big") & mask


def rho(nbits, cap):
    mask = (1 << nbits) - 1
    nbytes = (nbits + 7) // 8 + 4
    f = lambda v: trunc(v, nbytes, mask)
    start = int.from_bytes(os.urandom(8), "big") & mask
    t = f(start); h = f(f(start)); evals = 3
    while t != h:
        t = f(t); h = f(f(h)); evals += 3
        if evals > cap:
            return None, evals
    # Brent-style recovery of an actual colliding pair
    t = start
    prev_t, prev_h = t, h
    while True:
        nt, nh = f(t), f(h)
        evals += 2
        if nt == nh:
            return (t, h), evals
        t, h = nt, nh


if __name__ == "__main__":
    # measure raw hash rate
    t0 = time.time(); n = 400000
    for i in range(n):
        hashlib.sha256(i.to_bytes(8, "big")).digest()
    rate = n / (time.time() - t0)
    print(f"raw SHA-256 rate in this container (python/hashlib): {rate:,.0f} hashes/sec\n")

    print("n (bits) | collision found in evals | expected ~1.25*2^(n/2) | wall-clock")
    for nb in [24, 32, 40, 48, 50]:
        t0 = time.time()
        pair, evals = rho(nb, cap=int(80 * 2 ** (nb / 2)) + 10_000_000)
        dt = time.time() - t0
        exp = 1.2533 * 2 ** (nb / 2)
        if pair:
            a, b = pair
            nbytes = (nb + 7) // 8 + 4
            da = hashlib.sha256(a.to_bytes(nbytes, "big")).digest()
            db = hashlib.sha256(b.to_bytes(nbytes, "big")).digest()
            mask = (1 << nb) - 1
            ok = (int.from_bytes(da, "big") & mask) == (int.from_bytes(db, "big") & mask) and a != b
            print(f"   {nb:3d}   | {evals:>18,d}   | {exp:>18,.0f}   | {dt:6.1f}s   collision verified: {ok}")
        else:
            print(f"   {nb:3d}   | gave up after {evals:,} evals (> cap) | {exp:>18,.0f} | {dt:6.1f}s")

    print()
    print("=== Extrapolation to the real walls (no structural shortcut known) ===")
    for label, cost in [("collision, full 256-bit output (birthday, 2^128)", 2 ** 128),
                        ("preimage, full 256-bit output (2^256)", 2 ** 256)]:
        secs = cost / rate
        years = secs / (365.25 * 24 * 3600)
        print(f"  {label}: ~{cost:.3e} hashes -> {years:.2e} years at this rate")
    print("  (Even a billion-fold faster machine and a billion machines leaves 2^128 at ~10^13 years.)")
