"""SHA-256 from scratch, with a configurable number of rounds (0..64).

At rounds=64 this is exactly SHA-256; `verify()` checks it against hashlib on
random inputs. Lower round counts give the reduced-round variants used to study
where the function's mixing becomes strong enough to resist search.

Only single 512-bit-block messages are handled (inputs < 56 bytes), which is all
the experiments need; the full length-padding rule is standard and unchanged.
"""
import hashlib

MASK = 0xFFFFFFFF

K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

H0 = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]


def _rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & MASK


def _schedule(block):
    w = list(block)
    for i in range(16, 64):
        s0 = _rotr(w[i - 15], 7) ^ _rotr(w[i - 15], 18) ^ (w[i - 15] >> 3)
        s1 = _rotr(w[i - 2], 17) ^ _rotr(w[i - 2], 19) ^ (w[i - 2] >> 10)
        w.append((w[i - 16] + s0 + w[i - 7] + s1) & MASK)
    return w


def compress(block, rounds=64, h=None):
    """Compress one 16-word block through `rounds` of the round function."""
    w = _schedule(block)
    a, b, c, d, e, f, g, hh = (h if h is not None else H0)
    for i in range(rounds):
        S1 = _rotr(e, 6) ^ _rotr(e, 11) ^ _rotr(e, 25)
        ch = (e & f) ^ ((~e & MASK) & g)
        t1 = (hh + S1 + ch + K[i] + w[i]) & MASK
        S0 = _rotr(a, 2) ^ _rotr(a, 13) ^ _rotr(a, 22)
        maj = (a & b) ^ (a & c) ^ (b & c)
        t2 = (S0 + maj) & MASK
        hh, g, f, e, d, c, b, a = g, f, e, (d + t1) & MASK, c, b, a, (t1 + t2) & MASK
    base = h if h is not None else H0
    return [(base[j] + v) & MASK for j, v in enumerate([a, b, c, d, e, f, g, hh])]


def _pad_single_block(msg):
    assert len(msg) < 56, "this reduced-round study uses single-block (<56 byte) messages"
    padded = msg + b"\x80" + b"\x00" * (55 - len(msg)) + (len(msg) * 8).to_bytes(8, "big")
    return [int.from_bytes(padded[i:i + 4], "big") for i in range(0, 64, 4)]


def sha256(msg, rounds=64):
    block = _pad_single_block(msg)
    return b"".join(x.to_bytes(4, "big") for x in compress(block, rounds=rounds))


def verify(n=2000):
    import os
    for _ in range(n):
        m = os.urandom(__import__("random").randint(0, 55))
        if sha256(m, rounds=64) != hashlib.sha256(m).digest():
            return False, m
    return True, None


if __name__ == "__main__":
    ok, bad = verify()
    print("64-round output matches hashlib.sha256 on 2000 random messages:", ok)
    print("sha256(b'abc') =", sha256(b"abc").hex())
    print("hashlib        =", hashlib.sha256(b"abc").hexdigest())
