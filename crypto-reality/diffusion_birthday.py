"""Two honest measurements of SHA-256's strength.

1. Avalanche vs. rounds: flip one input bit, count output bit flips, as a
   function of how many of the 64 rounds we run. Shows how fast one bit of
   difference fills the whole 256-bit state (strict avalanche target: 50%).

2. Generic collision cost: a memory-free Pollard-rho collision search on the
   output truncated to n bits. This is the baseline birthday bound ~2^(n/2)
   that holds for ANY hash regardless of internal weaknesses; it is NOT a
   structural attack. Timing it and extrapolating shows the wall at full width.
"""
import os
import time
import statistics
from sha_ref import sha256, compress, _pad_single_block

MASK = 0xFFFFFFFF


def avalanche(rounds, trials=400):
    frac = []
    for _ in range(trials):
        m = os.urandom(32)
        blk = _pad_single_block(m)
        base = compress(blk, rounds=rounds)
        bit = int.from_bytes(os.urandom(1), "big") % 256  # flip one of the 256 input-word bits
        wi, bi = bit // 32, bit % 32
        blk2 = list(blk)
        blk2[wi] ^= (1 << bi)
        other = compress(blk2, rounds=rounds)
        x = 0
        for u, v in zip(base, other):
            x |= 0  # noop
        diff = sum(bin((u ^ v) & MASK).count("1") for u, v in zip(base, other))
        frac.append(diff / 256.0)
    return statistics.mean(frac)


def rho_collision(nbits, max_evals=None):
    """Find x != y with trunc_n(sha256(x)) == trunc_n(sha256(y)) via Floyd cycle
    detection on f(x) = trunc_n(sha256(x))."""
    mask = (1 << nbits) - 1
    nbytes = (nbits + 7) // 8

    def f(v):
        return int.from_bytes(sha256(v.to_bytes(nbytes + 4, "big")[:16]), "big") & mask

    start = int.from_bytes(os.urandom(nbytes + 2), "big") & ((1 << (8 * (nbytes + 2))) - 1)
    evals = 0
    tortoise = f(start)
    hare = f(f(start))
    evals += 3
    while tortoise != hare:
        tortoise = f(tortoise)
        hare = f(f(hare))
        evals += 3
        if max_evals and evals > max_evals:
            return None, evals
    # find entrance to the cycle -> an actual colliding pair
    tortoise = start
    while tortoise != hare:
        t2, h2 = f(tortoise), f(hare)
        evals += 2
        if t2 == h2 and tortoise != hare:
            return (tortoise, hare), evals
        tortoise, hare = t2, h2
    # tortoise == hare means they met at the cycle start; step both once more to get the pair just before
    return (start, hare), evals


if __name__ == "__main__":
    print("=== 1. Avalanche: mean fraction of the 256 output bits that flip when one input bit flips ===")
    print("    (strict avalanche criterion target = 0.5000)")
    for r in [1, 2, 3, 4, 5, 6, 8, 10, 16, 24, 32, 64]:
        print(f"    rounds={r:3d}   mean flip fraction = {avalanche(r):.4f}")

    print()
    print("=== 2. Generic birthday collision cost on full 64-round SHA-256, output truncated to n bits ===")
    print("    expected hash evaluations ~ sqrt(pi/2) * 2^(n/2) ~ 1.25 * 2^(n/2)")
    import math
    for n in [24, 32, 40, 48, 56]:
        t0 = time.time()
        pair, evals = rho_collision(n)
        dt = time.time() - t0
        a, b = pair
        import hashlib as _h
        exp = 1.2533 * 2 ** (n / 2)
        print(f"    n={n:3d} bits: collision found in {evals:>12,d} evals  (expected ~{exp:,.0f})  [{dt:5.1f}s]")
