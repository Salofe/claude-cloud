# Left to Solve: Pudlák warm-up, proved in Lean 4

Problem: [`PudlakFiniteDomain.sat_no_p_optimal_proof_system.variants.exists_of_P_eq_NP`](https://lefttosolve.com/p/PudlakFiniteDomain.sat_no_p_optimal_proof_system.variants.exists_of_P_eq_NP),
the easiest problem on lefttosolve.com still unsolved on 2026-11-27 (warm-up, difficulty 5/100):

> If `P = NP`, every NP-complete language has a p-optimal proof system.

## Files

| File | Proves |
|---|---|
| `PudlakFiniteDomain…exists_of_P_eq_NP.lean` | the problem itself (`OMA.solution : type_of% @…exists_of_P_eq_NP`) |
| `PudlakFiniteDomain…exists_of_P_eq_NP.R1.H1.lean` | step H1 of the site's reduction R1: for every polynomial-time `L` and word `fallback`, `fun w => if L w then w else fallback` is polynomial-time |

## The proof

The mathematics is short. Assume `P = NP`. An NP-complete `L` is then decidable in polynomial time.
Fix a word `y` in `L`. The retraction `r w = if L w then w else y` has range exactly `L`, so it is a
proof system for `L`. Every proof system `Q` for `L` is p-simulated by `r`, through `Q` itself.

Formalizing it is harder. Here `IsPolyTime` means an explicit Mathlib `FinTM2` Turing machine with a
polynomial step bound. Mathlib has no composition lemma for such machines (it is a `proof_wanted`),
which is where earlier attempts stopped. So the file builds the machine for `r` by hand. The new
machine copies its input, runs the decider for `L` step for step on its own stacks, and reads the
answer bit. It then either keeps the input, which is already the encoded output, or replaces it with
the encoding of `y`. The file proves a step-by-step simulation, the run of each phase, and a bound of
`p(n) + 3n + 4` steps.

## Verification

Both files were checked with the repository's own `tools/lint.py` and `tools/check.sh` against
formal-conjectures `9097e2f90e66` (Lean `v4.33.1`, Mathlib `v4.33.1`):

```
ACCEPTED | kernel accepted; axioms within propext, Classical.choice, Quot.sound
'OMA.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Note: another contributor's proof of the main problem was merged into
GuillaumeBAUD-coder/open-math-agents while this one was being written. Its machine definitions were
read before writing this file, and the machine here follows the same layout (copy, restore, run,
inspect, clear). The lemmas and proofs here were written separately and do not reuse its code.

## Other proofs in this folder

All accepted by `tools/check.sh` (axioms: propext, Classical.choice, Quot.sound).

| File | Kind | Status upstream |
|---|---|---|
| `SternPrime.isSternPrime_iff.R1.H2.lean` | step | PR #2279 |
| `SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H1.lean` | step | PR #2284 |
| `Mills.lower_bound_of_RH.R1.H2.lean` | step | solved by someone else first |
| `Erdos1100.erdos_1100.variants.erdos_tenenbaum_g.lean` | **complete problem** | solved by someone else first (a different proof) |
| `Erdos1100.erdos_1100.variants.erdos_simonovits.lean` | **complete problem** | branch pushed to the fork; PR to be opened |
| `Erdos999.erdos_999.variants.easy_direction.lean` | **complete problem** (warm-up) | closed by someone else first, through a two-step reduction |
| `Erdos593.erdos_593.variants.obligatory_implies_two_colorable.lean` | **complete problem** | solved by someone else first |

**Erdős 1100, Erdős–Tenenbaum bound** `g k ≤ 3·(3/2^(2/3))^k`. Take squarefree `n` with
`ω(n) = k` and `y = 2^(1/3)`. Every coprime pair of consecutive divisors `(d, d')` with
`a = ω(d)`, `b = ω(d')` satisfies `1 ≤ y^k/2^a + y^k/2^b + 2^(a+b)/y^(2k)`, because one of
`3a ≤ k`, `3b ≤ k` or `3(a+b) ≥ 2k` holds. Summing over the pairs, the maps `d`, `d'` and `dd'` are
injective into the divisors of `n`. Over divisors of a squarefree `n`, `Σ x^ω(d) ≤ (1+x)^k`.
Together these give `τ⊥(n) ≤ 3·(3y/2)^k`.

**Erdős 593 variant: obligatory 3-uniform hypergraphs are 2-colorable.**
- Host: triples `{a, b, d}`, where `a → b` is an arc of a shift graph built as iterated line
  digraphs of a transitive tournament on a well-ordered set that is too large to be countable.
- The host has uncountable chromatic number. A countable coloring of a line digraph descends to
  one of the digraph by subsets of colors, so Cantor's theorem rules it out.
- Every `r` vertices of the shift graph induce a 2-colorable subgraph.
- So any `F` that appears in the host gets a 2-coloring by pulling back the local coloring.

**Erdős 1100, Erdős–Simonovits bounds** `(√2+o(1))^k < g(k) < (2−c)^k`.
- Upper bound, with `c = 1/20`: it comes from the Erdős–Tenenbaum estimate above, because `3/2^(2/3) < 1.95`.
- Lower bound, by construction. Take primes `N < p < q` with `(q−p)·N < p`. The divisors of `N·p·q`
  interleave as `p·a < q·a < p·a' < q·a' < …`, which gives `τ⊥(Npq) ≥ 2·τ⊥(N) + 2`.
- Iterating gives a squarefree number with `k` prime factors and `τ⊥ ≥ 2^(⌊k/2⌋+1) − 2 > r^k`.
- Such close pairs of primes exist above any `N`. Otherwise the primes would grow geometrically,
  contradicting Mathlib's lower bound on sums of prime reciprocals.

**Erdős 999, easy direction of Duffin–Schaeffer.** Suppose `Σ φ(q)f(q)/q` converges.
- The set of `x` in `[0,1]` within `f(q)/q` of a reduced fraction `p/q` is covered by `3φ(q)` intervals.
- Its measure is therefore at most `6·φ(q)f(q)/q`.
- By Borel–Cantelli, almost no `x` is approximable, which contradicts the hypothesis.
