"""Reduced-round SHA-256 preimage via SAT (bit-blasting / Tseitin encoding).

Pick a random single-block message, compute its r-round digest, then hand a SAT
solver the full round structure with all 512 message bits free and the 256 output
bits constrained to that digest. A satisfying assignment IS a preimage of the
r-round hash. Solve time vs r shows where algebraic/search inversion stops
helping relative to the 2^256 brute-force wall.
"""
import sys, time, os
from pysat.solvers import Cadical153
from sha_ref import compress, _pad_single_block, K, H0


class Enc:
    def __init__(self):
        self.n = 2
        self.cl = []
        self.TRUE = 1
        self.FALSE = 2
        self.cl.append([self.TRUE])
        self.cl.append([-self.FALSE])

    def nv(self):
        self.n += 1
        return self.n

    def word(self):
        return [self.nv() for _ in range(32)]

    def const(self, val):
        return [self.TRUE if (val >> b) & 1 else self.FALSE for b in range(32)]

    def xor2(self, a, b):
        z = self.nv()
        self.cl += [[-a, -b, -z], [a, b, -z], [a, -b, z], [-a, b, z]]
        return z

    def and2(self, a, b):
        z = self.nv()
        self.cl += [[-a, -b, z], [a, -z], [b, -z]]
        return z

    def xl(self, lits):
        acc = lits[0]
        for x in lits[1:]:
            acc = self.xor2(acc, x)
        return acc

    def ch(self, e, f, g):
        return [self.xor2(self.and2(e[i], f[i]), self.and2(-e[i], g[i])) for i in range(32)]

    def maj(self, a, b, c):
        return [self.xl([self.and2(a[i], b[i]), self.and2(a[i], c[i]), self.and2(b[i], c[i])]) for i in range(32)]

    def add2(self, a, b):
        out, carry = [], self.FALSE
        for i in range(32):
            s = self.xl([a[i], b[i], carry])
            c = self.xl([self.and2(a[i], b[i]), self.and2(a[i], carry), self.and2(b[i], carry)])
            out.append(s); carry = c
        return out

    def addm(self, words):
        acc = words[0]
        for w in words[1:]:
            acc = self.add2(acc, w)
        return acc

    def eqc(self, word, val):
        for i in range(32):
            self.cl.append([word[i] if (val >> i) & 1 else -word[i]])


def rotr(w, n):
    return [w[(i + n) % 32] for i in range(32)]


def shr(E, w, n):
    return [w[i + n] if i + n < 32 else E.FALSE for i in range(32)]


def encode(E, rounds):
    w = [E.word() for _ in range(16)]
    for i in range(16, rounds):
        s0 = [E.xl([rotr(w[i-15], 7)[j], rotr(w[i-15], 18)[j], shr(E, w[i-15], 3)[j]]) for j in range(32)]
        s1 = [E.xl([rotr(w[i-2], 17)[j], rotr(w[i-2], 19)[j], shr(E, w[i-2], 10)[j]]) for j in range(32)]
        w.append(E.addm([w[i - 16], s0, w[i - 7], s1]))
    H = [E.const(h) for h in H0]
    a, b, c, d, e, f, g, hh = H
    for i in range(rounds):
        S1 = [E.xl([rotr(e, 6)[j], rotr(e, 11)[j], rotr(e, 25)[j]]) for j in range(32)]
        S0 = [E.xl([rotr(a, 2)[j], rotr(a, 13)[j], rotr(a, 22)[j]]) for j in range(32)]
        t1 = E.addm([hh, S1, E.ch(e, f, g), E.const(K[i]), w[i]])
        t2 = E.add2(S0, E.maj(a, b, c))
        hh, g, f, e, d, c, b, a = g, f, e, E.add2(d, t1), c, b, a, E.add2(t1, t2)
    final = [E.add2(x, y) for x, y in zip([a, b, c, d, e, f, g, hh], H)]
    return w, final


def run(rounds):
    E = Enc()
    msg = os.urandom(32)
    blk = _pad_single_block(msg)
    target = compress(blk, rounds=rounds)
    w, final = encode(E, rounds)
    for word, tval in zip(final, target):
        E.eqc(word, tval)
    s = Cadical153(bootstrap_with=E.cl)
    t0 = time.time()
    sat = s.solve()
    dt = time.time() - t0
    out = {"rounds": rounds, "sat": sat, "time": dt, "vars": E.n, "clauses": len(E.cl)}
    if sat:
        model = set(l for l in s.get_model() if l > 0)
        words = [sum((1 << i) for i, lit in enumerate(wi) if lit in model) for wi in w[:16]]
        out["valid"] = (compress(words, rounds=rounds) == target)
    s.delete()
    return out


if __name__ == "__main__":
    rl = [int(x) for x in sys.argv[1:]] or [1, 2, 4, 8, 12, 16, 18, 20, 22, 24]
    print("reduced-round SHA-256 preimage by SAT (512 msg bits free, 256 output bits fixed)")
    print("rounds | SAT  | preimage valid | solve time | vars | clauses")
    for r in rl:
        res = run(r)
        print(f"  {r:4d} | {str(res['sat']):5s}| {str(res.get('valid')):5s}          "
              f"| {res['time']:8.2f}s | {res['vars']:>8,d} | {res['clauses']:>9,d}", flush=True)
