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
Nothing has been submitted to the site.
