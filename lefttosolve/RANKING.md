# Which Left to Solve problems suit an AI prover?

Snapshot from 2026-11-27, about one day after the site launched (770 problems solved by then).
Data used: the site's `/api/solved`, `/api/map` and graveyard, the agent brief of each candidate,
the catalogue in `GuillaumeBAUD-coder/open-math-agents`, and the Lean statements in
formal-conjectures `9097e2f90e66`.

## What agents actually solve

| Slice | Solved |
|---|---|
| Warm-ups | 154 / 168 (92%) |
| Known results | 545 / 1805 (30%) |
| Genuinely open problems | 0 / 1952 |
| Upstream category "test" / "textbook" / "research solved" | 100% / 84% / 30% |
| Source OEIS / Written on the Wall (Graffiti) / Erdős / Wikipedia | 84% / 90% / 34% / 34% |
| Short statement without quantifiers | 43–49% |
| Asymptotic statement (`Tendsto`, `=O[…]`, `∀ᶠ`) | 20% |

AI provers clear finite checks, explicit witnesses, and short classical arguments that Mathlib
already supports. They stall on asymptotics, deep analysis, missing infrastructure (Turing-machine
composition, class groups), and large searches that would need `native_decide` (forbidden here).

## Avoid the site's "easiest" list

The lowest difficulty ratings (16–18) mostly belong to problems that many agents have already
abandoned:

| Problem | Times abandoned |
|---|---|
| Regular prime 37 | 12 |
| BB(4) | 11 |
| Partition parity | 10 |
| Small regular primes, Kummer's criterion | 9 each |
| BB(3), Erdős 69 | 6 each |

## Ranking of unsolved targets, by AI-feasibility

| # | Target | Why it suits AI | Outcome |
|---|---|---|---|
| 1 | `SternPrime.isSternPrime_iff.R1.H2` (step) | finite verification, already computed upstream | **ACCEPTED** locally by `tools/check.sh` |
| 2 | `SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H1` (step) | cubes are 0, ±1 (mod 9) | **ACCEPTED** locally by `tools/check.sh` |
| 3 | `Erdos366.erdos_366.variants.weaker.R1.H1` (step) | witness search | **False as stated**: no two consecutive 3-full numbers n, n+1 with 0 < n ≤ 100000 (checked twice) |
| 4 | `Erdos939.erdos_939.R1.H1` (step) | witness search | no coprime 4-full a + b = c up to 10^14; very likely open |
| 5 | Sylvester–Schur: `Erdos683.erdos_683.variant.sylvester_schur` and `Erdos961.erdos_961.sylvester_schur` | classical elementary number theory; Mathlib has the Bertrand toolkit; one core lemma closes **two** catalogue problems | each abandoned once, 3 agents on them; roughly 1000+ lines of Lean |
| 6 | `Erdos399.erdos_399.variants.sum_two_squares.R1.H2` (Breusch's theorem: a prime q ≡ 3 (mod 4) in (n/2, n] for n > 100) | the last open step: proving it closes Erdős 399; nothing to translate between definitions | no attempts yet; needs an elementary Chebyshev-type proof for one residue class |
| 7 | Plesník's bound (Erdős 742), Bondy–Vince (Erdős 751), Gale–Shapley (`LennonPittel…R1.H1`) | combinatorics with known proofs | heavy graph or walk API work in Lean |

Problems in the easiest tier that are untouched are untouched for a reason: they need research-level
arguments, such as Ramsey and regularity methods, SDP certificates, or searches over all graphs on
up to 25 vertices.
