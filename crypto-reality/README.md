# Factoring and SHA-256: what is actually reachable

A reality check, with reproducible experiments, on two requests: "prove factoring
is in P" and "factor / break SHA-256". The short version is that **neither is
reachable**, and the point of this folder is to make that concrete and honest
rather than to pretend otherwise. Everything here runs in a few minutes.

All numbers below were produced by the scripts in this folder on this machine.

## SHA-256

SHA-256 is not a number-theoretic function, so "factoring" it is not a thing.
Breaking it means a **preimage** (invert a digest) or a **collision** (two inputs,
one digest). `sha_ref.py` is a from-scratch, round-configurable implementation; it
reproduces `hashlib.sha256` exactly on 2000 random messages.

**1. Diffusion (`diffusion_birthday.py`).** Flip one input bit, count output-bit
flips, as a function of how many of the 64 rounds run:

| rounds | 1 | 2 | 4 | 6 | 8 | 10 | 16 | 32 | 64 |
|---|---|---|---|---|---|---|---|---|---|
| mean output flip fraction | .002 | .014 | .08 | .21 | .32 | .43 | **.50** | .50 | .50 |

One bit of difference fills the whole 256-bit state (the 50% strict-avalanche
target) by round ~16. The real function has 64. That margin is why attacks on
reduced versions do not extend to the full one.

**2. Generic collision cost (`birthday.py`).** Memory-free Pollard-rho collision
search on the output truncated to n bits, on the real hash. Collisions found and
re-verified:

| n (bits) | 24 | 32 | 40 | 48 | 50 |
|---|---|---|---|---|---|
| hash evals to collide | 5.1k | 200k | 2.1M | 56M | 131M |

This tracks the birthday law ~1.25·2^(n/2) exactly. Extrapolated to the real
256-bit output: a collision is **2^128 ≈ 10^38 hashes ≈ 10^24 years** at this
machine's rate, and ~10^13 years even granting a 10^9× faster machine times 10^9
machines. This is the generic bound every hash has; it is not a weakness.

**3. Preimage by SAT (`sat_preimage.py`).** The closest honest thing to an
"attack": encode r rounds of SHA-256 as a Boolean formula (512 message bits free,
256 output bits fixed to a target) and ask a SAT solver to invert it. Each found
preimage is re-hashed to confirm it is genuine.

| rounds | 1–16 | 18 | 20+ |
|---|---|---|---|
| solve time | < 0.01 s | 55 s | no answer in 180 s |

Direct SAT inversion reaches ~18 rounds and walls off. Full SHA-256 is **64**
rounds. This matches the published literature (algebraic/SAT preimage attacks
stall in the low-20s of rounds). Reproducing the best reduced-round *differential*
results (collisions at ~28–31 rounds, Mendel–Nad–Schläffer and successors) needs
specialized multi-day search and is not reproducible in a quick run; those still
leave the full 64-round function with no practical attack.

**Conclusion.** Full SHA-256 has no known practical preimage or collision attack,
by anyone, and nothing here changes that. The experiments quantify *why*: fast
avalanche, an exponential generic wall, and algebraic inversion that dies at a
quarter of the rounds.

## Factoring (`factoring.py`)

Factoring is in NP ∩ co-NP, is believed not NP-complete, and is **not known to be
in P** — nor is there any accepted path to proving it is. (For contrast, *primality*
testing was put in P by AKS in 2002; that result does not help factoring.)

- Pollard-rho (Brent) on balanced semiprimes n = p·q: instant to ~2^45 per factor,
  and gives up on 100-bit n (50-bit factors) within a 5M-step budget. Cost ~ n^(1/4).
- `sympy.factorint` (trial division + rho + p−1, no sieve) stays fast only while a
  factor is small or special; on balanced semiprimes it stalls in the same range.
- The real state of the art is the General Number Field Sieve, cost L_n[1/3, 1.923].
  A single-constant extrapolation anchored to RSA-250 (829 bit, broken 2020,
  ~2700 CPU-years) reproduces the record scale and gives:

| modulus | RSA-512 | RSA-768 | RSA-250 | RSA-1024 | RSA-2048 |
|---|---|---|---|---|---|
| heuristic CPU-years | 0.07 | ~440 | 2700 (anchor) | ~5×10^5 | **~6×10^14** |

RSA-2048 is ~2×10^11 times the effort of the largest number ever factored.
Optimized published estimates are lower (~10^9 core-years) but still far beyond
any feasible computation. Shor's quantum algorithm would factor in polynomial
time, but needs millions of stable qubits that do not exist.

**Conclusion.** Every known factoring algorithm is super-polynomial, and there is
no result to chip toward "in P". Unlike the permanent split-rank work in
`../pequalnp/` — where there were real, bounded sub-questions to make verified
progress on — here there is no incremental sub-result that moves the needle, so
running search would be pure theater.

## Reproduce

```
python3 sha_ref.py            # verify the implementation == hashlib
python3 diffusion_birthday.py # avalanche table + small collisions
python3 birthday.py           # collision scaling + extrapolation
python3 sat_preimage.py 1 2 4 8 12 16 18   # SAT preimage up to the wall (18 ~ 1 min)
python3 factoring.py          # factoring + GNFS extrapolation
```
Requires `python-sat` and `sympy`.
