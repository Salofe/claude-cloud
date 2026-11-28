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
| `Erdos1100.erdos_1100.variants.erdos_simonovits.lean` | **complete problem** | **merged and credited to Salofe** ([PR #3267](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3267), 18 points) |
| `Erdos999.erdos_999.variants.easy_direction.lean` | **complete problem** (warm-up) | closed by someone else first, through a two-step reduction |
| `Erdos792.erdos_792.variants.bourgain.lean` | **complete problem** (proved by Fable 5.2) | **merged, credited to Salofe** ([PR #4072](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4072), 17 points) |
| `Erdos174.erdos_174.variants.trapezoid.lean` | **complete problem** (Kříž: isosceles trapezoids are Ramsey, proved by Fable 5.2) | **merged, credited to Salofe** ([PR #4258](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4258), site credit pending) |
| `Erdos321.erdos_321.variants.upper.lean` | **complete problem** (Bleicher–Erdős upper bound for R(N), proved by Fable 5.2) | **merged, credited to Salofe** ([PR #4869](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4869), 19 points) |
| `Arxiv.2606.03696.bondy_conjecture.variants.three.lean` | **complete problem** (Bondy's longest-cycle conjecture for k = 3, proved by Fable 5.2) | solved by someone else first (their PR #5825 merged; ours was [PR #6031](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6031)) |
| `Erdos976.erdos_976.variants.nagell_ricci.lean` | **complete problem** (Nagell–Ricci, proved by Fable 5.2) | another team's PR (#6259) was merged instead; ours was [PR #6147](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6147) |
| `Erdos258.erdos_258.variants.monotone.lean` | **complete problem** (monotone variant, proved by Fable 5.2) | solved by someone else first (their PR #6227 merged; ours was [PR #6499](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6499)) |
| `Erdos377.erdos_377.variants.ae.lean` | **complete problem** (proved by Fable 5.2) | solved by someone else first |
| `Erdos1088.f_isLeast.lean` | **complete problem** (warm-up, proved by Fable 5.2) | solved by someone else first |
| `Sendov.sendov_conjecture.variants.le_eight.lean` | **complete problem** (Sendov's conjecture, degree ≤ 8) | solved by someone else first |
| `OeisA182126.conjecture3.R1.H2.lean` | step | [PR #4113](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4113) (opened automatically) |
| `OeisA67599.conjecture.R1.H2.lean` | step | [PR #4127](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4127) (opened automatically) |
| `OeisA217785.conjecture_3.R1.H1.lean` | step | [PR #4140](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4140) (opened automatically) |
| `Erdos700.erdos_700.parts.ii.R1.H2.lean` | step | [PR #4156](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4156) (opened automatically) |
| `Erdos420.erdos_420.parts.i.R1.H2.lean` | step | [PR #4143](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4143) (opened automatically) |
| `Erdos479.erdos_479.R1.H1.lean` | step | [PR #4151](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4151) (opened automatically) |
| `Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H1.lean` | step | [PR #4163](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4163) (opened automatically) |
| `Erdos828.erdos_828.R1.H1.lean` | step | [PR #4165](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4165) (opened automatically) |
| `Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H1.R1.H2.lean` | step | [PR #4179](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4179) (opened automatically) |
| `Erdos686.erdos_686.R1.H1.lean` | step | [PR #4356](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4356) (opened automatically) |
| `Erdos687.erdos_687.variants.maier_pomerance.R1.H2.lean` | step | [PR #4354](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4354) (opened automatically) |
| `Erdos700.erdos_700.parts.ii.R1.H1.lean` | step | [PR #4373](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4373) (opened automatically) |
| `MeynielConjecture.meyniel_conjecture.R1.H1.lean` | step | [PR #4353](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4353) (opened automatically) |
| `MeynielConjecture.meyniel_conjecture.variants.soft.R1.H1.lean` | step | [PR #4348](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4348) (opened automatically) |
| `FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1.H1.lean` | step | [PR #4349](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4349) (opened automatically) |
| `FlintCooksonHills.flint_hills_series_converges.R1.H2.lean` | step | [PR #4357](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4357) (opened automatically) |
| `FlintCooksonHills.cookson_hills_series_converges.R1.H2.lean` | step | [PR #4367](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4367) (opened automatically) |
| `ScholzConjecture.scholz_conjecture.R1.H1.lean` | step | [PR #4360](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4360) (opened automatically) |
| `WrittenOnTheWallII.GraphConjecture84.conjecture84.R1.H2.lean` | step | [PR #4362](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4362) (opened automatically) |
| `Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H1.lean` | step | [PR #4376](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4376) (opened automatically) |
| `Erdos470.erdos_470.parts.ii.R1.H1.lean` | step | [PR #4383](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4383) (opened automatically) |
| `Erdos20.erdos_20.R1.H1.lean` | step | [PR #4414](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4414) (opened automatically) |
| `Erdos770.erdos_770.parts.iii.R1.H2.lean` | step | [PR #4506](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4506) (opened automatically) |
| `MonochromaticQuantumGraph.eqSystem6_no_solution_ge3.R1.H1.lean` | step | [PR #4363](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4363) (opened automatically) |
| `OeisA224.conjecture.R1.H1.lean` | step | [PR #4372](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4372) (opened automatically) |
| `Erdos1129.erdos_1129.lean` | **complete problem** (Kilgore / de Boor–Pinkus, proved by Fable 5.2, 2460 lines) | solved by someone else first |
| `Erdos944.erdos_944.variants.dirac_conjecture.lean` | **complete problem** (Dirac's conjecture for all k ≥ 4, proved by Fable 5.2) | solved by someone else first |
| `Arxiv.0805.3777.isMaxRank_of_le_min.lean` | **complete problem** (maximal tensor rank, proved by Fable 5.2) | solved by someone else first |
| `Erdos1111.erdos_1111.variants.nguyen_scott_seymour.lean` | **complete problem** (proved by Fable 5.2) | solved by someone else first (by about 15 minutes) |
| `ReconstructionConjecture.reconstruction_conjecture.variants.tree.lean` | **complete problem** (Kelly: trees are reconstructible, proved by Fable 5.2) | solved by someone else first |
| `Arxiv.2605.02731.dean_conjecture.variants.three.lean` | **complete problem** (Chen–Saito: min degree ≥ 3 gives a cycle of length ≡ 0 mod 3, proved by Fable 5.2) | solved by someone else first |
| `OeisA24356.conjecture.R1.H1.lean` | step | [PR #3573](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3573) (opened automatically) |
| `OeisA135508.conjecture.R1.H1.lean` | step | [PR #3570](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3570) (opened automatically) |
| `OeisA108129.conjecture.R1.H1.lean` | step | [PR #3571](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3571) (opened automatically) |
| `Erdos647.erdos_647.R1.H1.lean` | step | [PR #3572](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3572) (opened automatically) |
| `OeisA237578.conjecture_2.R1.H1.lean` | step | [PR #3575](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3575) (opened automatically) |
| `OeisA249609.conjecture.R1.H1.lean` | step | [PR #3576](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3576) (opened automatically) |
| `OeisA234246.conjecture_2.R1.H1.lean` | step | [PR #3685](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3685) (opened automatically) |
| `ErdosMoser.erdos_moser_conjecture.R1.H1.lean` | step | [PR #3693](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3693) (opened automatically) |
| `Erdos406.erdos_406.variants.one_two.R1.H1.lean` | step | [PR #3692](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3692) (opened automatically) |
| `OeisA7406.conjecture.R1.H1.lean` | step | [PR #3697](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3697) (opened automatically) |
| `OeisA2426.conjecture.R1.H1.lean` | step | [PR #3698](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3698) (opened automatically) |
| `Erdos835.johnson_chromaticNumber.R1.H1.lean` | step | [PR #3704](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3704) (opened automatically) |
| `OeisA5258.conjecture.R1.H1.lean` | step | [PR #3703](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3703) (opened automatically) |
| `LennonPittel.lennon_pittel_conjecture.R1.H1.lean` | step | [PR #3711](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3711) (opened automatically) |
| `AgohGiuga.agoh_giuga.variants.giuga.R1.H2.lean` | step | [PR #4751](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4751) (opened automatically) |
| `Green37.green_37_lower_bound.R1.H3.lean` | step | [PR #4774](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4774) (opened automatically) |
| `IrvingLeather.irving_leather_growth_rate.R1.H1.lean` | step | [PR #4759](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4759) (opened automatically) |
| `OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H1.lean` | step | [PR #4783](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4783) (opened automatically) |
| `FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H1.lean` | step | [PR #4779](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4779) (opened automatically) |
| `FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H2.lean` | step | [PR #4785](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4785) (opened automatically) |
| `Erdos535.erdos_535.R1.H3.lean` | step | [PR #4792](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4792) (opened automatically) |
| `Erdos94.erdos_94.variants.regular_ngon.R1.H1.lean` | step | [PR #4796](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4796) (opened automatically) |
| `Erdos535.erdos_535.R1.H2.lean` | step | [PR #4841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4841) (opened automatically) |
| `Erdos78.erdos_78.variants.strongly_explicit.R1.H3.lean` | step | [PR #4891](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4891) (opened automatically) |
| `Erdos470.erdos_470.parts.ii.R2.H1.lean` | step | [PR #4903](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4903) (opened automatically) |
| `WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2.lean` | step | [PR #4892](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4892) (opened automatically) |
| `Erdos835.erdos_835.variants.johnson.R1.H1.R1.H2.lean` | step | [PR #4913](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4913) (opened automatically) |
| `Erdos713.erdos_713.parts.ii.R1.H2.R1.H1.lean` | step | [PR #4912](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4912) (opened automatically) |
| `WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H2.lean` | step | [PR #4923](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4923) (opened automatically) |
| `Kourovka.20.51.kourovka_20_51.R1.H2.lean` | step | [PR #4933](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4933) (opened automatically) |
| `OeisA215926.conjecture_2.R1.H2.lean` | step | [PR #4939](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4939) (opened automatically) |
| `AgohGiuga.agoh_giuga.variants.giuga.R1.H1.lean` | step | [PR #4942](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4942) (opened automatically) |
| `Green37.green_37_lower_bound.R1.H2.lean` | step | [PR #4951](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4951) (opened automatically) |
| `Erdos535.erdos_535.variants.sunflower_strong.R1.H2.lean` | step | [PR #4955](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4955) (opened automatically) |
| `OeisA238568.conjecture_2.R1.H1.lean` | step | [PR #4878](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4878) (opened automatically) |
| `Erdos317.erdos_317.variants.claim2.R1.H1.lean` | step | [PR #4889](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4889) (opened automatically) |
| `Erdos470.erdos_470.parts.ii.R3.H1.lean` | step | [PR #4896](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4896) (opened automatically) |
| `OpenQuantumProblem23.hasSICPOVM_68.R1.H2.lean` | step | [PR #4965](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4965) (opened automatically) |
| `ReconstructionConjecture.edge_reconstruction_conjecture.R1.H2.lean` | step | **merged** ([PR #5208](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5208)) |
| `LennonPittel.lennon_pittel_conjecture.R2.H1.lean` | step | [PR #5260](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5260) (opened automatically) |
| `Erdos104.erdos_104.R1.H2.lean` | step | [PR #5277](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5277) (opened automatically) |
| `Erdos142.erdos_142.variants.lower.R2.H2.lean` | step | [PR #5265](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5265) (opened automatically) |
| `Erdos535.erdos_535.R2.H2.lean` | step | [PR #5264](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5264) (opened automatically) |
| `Erdos142.erdos_142.variants.lower.R1.H2.R2.H2.lean` | step | [PR #5279](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5279) (opened automatically) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H2.lean` | step | [PR #5331](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5331) (opened automatically) |
| `Erdos173.erdos_173.R1.H1.lean` | step | [PR #5304](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5304) (opened automatically) |
| `OeisA108569.conjecture.R1.H2.lean` | step | [PR #5297](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5297) (opened automatically) |
| `Mersenne.squarefree_mersenne_of_prime.R1.H1.lean` | step | [PR #5325](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5325) (opened automatically) |
| `Erdos366.erdos_366.variants.weaker.R2.H2.lean` | step | [PR #5314](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5314) (opened automatically) |
| `Erdos408.erdos_408.parts.ii.R1.H1.lean` | step | [PR #5343](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5343) (opened automatically) |
| `Erdos161.erdos_161.parts.ii.R1.H2.R1.H1.lean` | step | [PR #5377](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5377) (opened automatically) |
| `Erdos40.erdos_40.variants.weaker.R1.H2.R1.H1.lean` | step | [PR #5471](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5471) (opened automatically) |
| `Erdos307.erdos_307.variants.coprime_one_notMem.R1.H1.lean` | step | [PR #5442](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5442) (opened automatically) |
| `Erdos307.erdos_307.variants.coprime_one_notMem.R1.H2.lean` | step | [PR #5435](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5435) (opened automatically) |
| `Erdos261.erdos_261.parts.iii.R1.H3.lean` | step | [PR #5447](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5447) (opened automatically) |
| `Erdos835.erdos_835.variants.johnson.R2.H2.lean` | step | [PR #5460](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5460) (opened automatically) |
| `Erdos835.erdos_835.variants.johnson.R2.H3.lean` | step | [PR #5478](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5478) (opened automatically) |
| `OeisA245212.conjecture.R1.H1.R1.H2.R1.H3.lean` | step | [PR #5481](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5481) (opened automatically) |
| `Erdos261.erdos_261.parts.iii.R1.H2.lean` | step | [PR #5531](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5531) (opened automatically) |
| `OeisA232194.conjecture_2.R1.H1.lean` | step | [PR #5489](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5489) (opened automatically) |
| `Erdos261.erdos_261.parts.ii.R1.H2.lean` | step | [PR #5474](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5474) (opened automatically) |
| `Erdos389.erdos_389.R1.H2.lean` | step | [PR #5490](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5490) (opened automatically) |
| `Erdos824.erdos_824.variants.squarefree.R1.H2.lean` | step | [PR #5504](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5504) (opened automatically) |
| `OeisA7468.conjecture.R1.H1.lean` | step | [PR #5507](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5507) (opened automatically) |
| `Erdos1180.erdos_1180.variants.optimal.R1.H1.lean` | step | [PR #5515](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5515) (opened automatically) |
| `Erdos173.erdos_173.R1.H2.R1.H2.R1.H2.lean` | step | [PR #5520](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5520) (opened automatically) |
| `Green37.green_37_lower_bound.R1.H1.R1.H2.lean` | step | [PR #5537](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5537) (opened automatically) |
| `Green37.green_37_lower_bound.R1.H1.R1.H3.lean` | step | [PR #5526](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5526) (opened automatically) |
| `Erdos94.erdos_94.variants.regular_ngon.R1.H2.lean` | step | [PR #5538](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5538) (opened automatically) |
| `Erdos307.erdos_307.variants.coprime_one_notMem.R2.H2.lean` | step | [PR #5766](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5766) (opened automatically) |
| `Erdos242.erdos_242.R1.H2.lean` | step | [PR #5765](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5765) (opened automatically) |
| `OeisA2326.conjecture2.R1.H1.lean` | step | [PR #5782](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5782) (opened automatically) |
| `Erdos824.erdos_824.variants.squarefree.R1.H1.R1.H2.lean` | step | [PR #5780](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5780) (opened automatically) |
| `Erdos389.erdos_389.R1.H2.R1.H1.lean` | step | [PR #5824](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5824) (opened automatically) |
| `Erdos890.erdos_890.parts.b.R1.H2.lean` | step | [PR #5823](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5823) (opened automatically) |
| `Green3.green_3.R1.H2.R1.H2.R1.H1.lean` | step | [PR #5863](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5863) (opened automatically) |
| `Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H1.lean` | step | [PR #5912](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5912) (opened automatically) |
| `Erdos173.erdos_173.R1.H2.R1.H2.R1.H1.R1.H2.lean` | step | [PR #5889](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5889) (opened automatically) |
| `Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H1.lean` | step | [PR #5893](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5893) (opened automatically) |
| `Erdos242.erdos_242.variants.schinzel_generalization.R1.H2.lean` | step | [PR #5908](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5908) (opened automatically) |
| `OeisA51903.conjecture1.R1.H1.lean` | step | [PR #5906](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5906) (opened automatically) |
| `OeisA69004.conjecture2.variants.without_upper_bound.R1.H3.lean` | step | [PR #5890](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5890) (opened automatically) |
| `Erdos542.erdos_542.variants.only_two.R1.H1.lean` | step | [PR #5918](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5918) (opened automatically) |
| `OeisA1146.conjecture.R1.H2.R1.H1.lean` | step | [PR #5952](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5952) (opened automatically) |
| `PoincareConjecture.poincare_conjecture.R1.H1.R1.H2.R1.H2.R1.H2.R1.H2.lean` | step | [PR #6172](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6172) (opened automatically) |
| `OeisA238585.conjecture_2.R1.H1.lean` | step | [PR #6170](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6170) (opened automatically) |
| `Green75.green_75.variants.pinchasi.R1.H1.lean` | step | [PR #6183](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6183) (opened automatically) |
| `Erdos20.erdos_20.R1.H2.R2.H2.lean` | step | [PR #6198](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6198) (opened automatically) |
| `RiemannHypothesis.lagarias_criterion.R1.H2.R1.H1.R1.H2.lean` | step | [PR #6292](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6292) (opened automatically) |
| `Erdos50.erdos_50_singular.R1.H2.R1.H2.R1.H2.lean` | step | [PR #6047](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6047) (opened automatically) |
| `Erdos103.erdos_103.variants.two_le.R1.H1.lean` | step | [PR #6075](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6075) (opened automatically) |
| `SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes.R1.H2.lean` | step | [PR #6048](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6048) (opened automatically) |
| `RiemannHypothesis.beurling_nyman_criterion.R1.H1.R1.H2.lean` | step | [PR #6218](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6218) (opened automatically) |
| `SnakeInBox.coil_upper_bound.R1.H1.lean` | step | [PR #6162](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6162) (opened automatically) |
| `GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.radius_two.R1.H1.lean` | step | [PR #6098](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6098) (opened automatically) |
| `PoincareConjecture.poincare_conjecture.R1.H2.R1.H1.R1.H2.R1.H2.lean` | step | [PR #6316](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6316) (opened automatically) |
| `InscribedSquare.exists_inscribed_rectangle.R1.H1.lean` | step | [PR #6277](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6277) (opened automatically) |
| `Erdos1013.erdos_1013.variants.lower.R1.H2.lean` | step | [PR #6236](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6236) (opened automatically) |
| `Erdos1013.erdos_1013.variants.lower.R1.H3.lean` | step | [PR #6207](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6207) (opened automatically) |
| `Erdos1013.erdos_1013.variants.lower.R1.H4.lean` | step | [PR #6267](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6267) (opened automatically) |
| `Green91.green_91.R1.H2.lean` | step | [PR #6485](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6485) (opened automatically) |
| `Mills.exists-prime.R1.H2.lean` | step | [PR #6459](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6459) (opened automatically) |
| `Erdos593.erdos_593.variants.obligatory_implies_two_colorable.lean` | **complete problem** | solved by someone else first |
| `Erdos930.erdos_930.variants.consecutive_integers.R1.H4.R1.H2.R1.H1.R1.H3.R1.H4.lean` | step | [PR #6875](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6875) (opened automatically) |
| `Erdos1109.erdos_1109.variants.konyagin_upper.R1.H1.R1.H1.lean` | step | [PR #6335](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6335) (opened automatically) |
| `Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1.H1.lean` | step | [PR #6336](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6336) (opened automatically) |
| `Erdos821.erdos_821.variants.lichtman.R1.H2.lean` | step | [PR #6362](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6362) (opened automatically) |
| `Green68.green_68.variants.voloch.R1.H2.lean` | step | [PR #6386](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6386) (opened automatically) |
| `LatinSquare.growthRateZn.R1.H2.lean` | step | [PR #6405](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6405) (opened automatically) |
| `Green54.green_54_known_case.R1.H2.lean` | step | [PR #6455](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6455) (opened automatically) |
| `Erdos561.erdos_561.R1.H1.lean` | step | [PR #6457](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6457) (opened automatically) |
| `Erdos647.erdos_647.variants.infinite.R1.H2.lean` | step | [PR #6473](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6473) (opened automatically) |
| `Green72.no_k_in_line_big.R1.H2.lean` | step | [PR #6475](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6475) (opened automatically) |
| `Erdos422.erdos_422.variants.well_defined.R1.H1.lean` | step | [PR #6543](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6543) (opened automatically) |
| `OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H2.lean` | step | [PR #6573](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6573) (opened automatically) |
| `OeisA262813.conjecture_2.R1.H1.lean` | step | [PR #6669](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6669) (opened automatically) |
| `AlspachConjecture.alspach_conjecture.variants.long_cycles.R1.H1.lean` | step | [PR #6728](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6728) (opened automatically) |
| `Erdos552.erdos_552.parts.ii.R1.H2.lean` | step | [PR #6745](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6745) (opened automatically) |
| `Erdos208.erdos_208.variants.log_bound.R1.H1.lean` | step | [PR #6756](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6756) (opened automatically) |
| `InscribedSquare.exists_inscribed_rectangle.R1.H2.R1.H1.lean` | step | [PR #6784](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6784) (opened automatically) |
| `Erdos552.erdos_552.parts.ii.R1.H1.lean` | step | [PR #6825](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6825) (opened automatically) |
| `OeisA262446.conjecture_2.R1.H1.lean` | step | [PR #6827](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6827) (opened automatically) |
| `Erdos1042.erdos_1042.variants.universal.R1.H1.R1.H1.lean` | step | [PR #6982](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6982) (opened automatically) |
| `ABC.abc.variants.quality.R1.H1.lean` | step | [PR #6833](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6833) (opened automatically) |
| `Erdos687.erdos_687.variants.iwaniec.R1.H2.lean` | step | [PR #6941](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6941) (opened automatically) |
| `OeisA237720.conjecture_2.R1.H1.lean` | step | [PR #7041](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7041) (opened automatically) |
| `Erdos848.erdos_848.R1.H2.R1.H2.R1.H2.lean` | step | [PR #7073](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7073) (opened automatically) |
| `Erdos913.erdos_913.variants.infinite_many_8p_sq_add_one_primes.R1.H1.lean` | step | [PR #6912](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6912) (opened automatically) |
| `Erdos733.erdos_733.variants.limit_exists.R1.H1.lean` | step | [PR #6988](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6988) (opened automatically) |
| `Erdos456.erdos_456.variants.linniks_theorem.R1.H2.lean` | step | [PR #7098](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7098) (opened automatically) |
| `OeisA262781.conjecture_2.R1.H1.lean` | step | [PR #7172](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7172) (opened automatically) |
| `Erdos436.erdos_436.variants.ge_four.R2.H2.lean` | step | [PR #7286](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7286) (opened automatically) |
| `Erdos500.erdos_500.variants.turan_conjecture.R1.H1.lean` | step | [PR #7287](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7287) (opened automatically) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R3.H1.lean` | step | [PR #7350](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7350) (opened automatically) |
| `PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1.H3.lean` | step | [PR #7488](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7488) (opened automatically) |
| `Erdos69.erdos_69.R2.H2.lean` | step | [PR #7521](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7521) (opened automatically) |
| `Erdos768.erdos_768.R1.H1.R1.H2.lean` | step (hard step, rated 5/10) | [PR #7561](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7561) (opened automatically) |
| `OeisA245212.conjecture.R1.H1.R1.H1.lean` | step (hard step, rated 5/10) | [PR #7563](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7563) (opened automatically) |
| `LennonPittel.lennon_pittel_conjecture.R3.H2.R1.H1.lean` | step (hard step, rated 5/10) | [PR #7564](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7564) (opened automatically) |
| `Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H1.lean` | step (hard step, rated 5/10) | [PR #7570](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7570) (opened automatically) |
| `OeisA69191.conjecture_2.R1.H2.lean` | step (hard step, rated 5/10) | [PR #7584](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7584) (opened automatically) |
| `AgohGiuga.agoh_giuga.R1.H1.lean` | step (hard step, rated 5/10, Kellner equivalence) | [PR #7585](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7585) (opened automatically) |
| `Erdos52.erdos_52.R2.H1.lean` | step (divisor bound, already proved in the reduction) | [PR #7638](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7638) (opened automatically) |
| `OeisA78729.conjecture.R1.H1.lean` | step (a(4) = 0: the product plus one is the square (k^2+5k+5)^2) | [PR #7661](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7661) (opened automatically) |
| `Arxiv.1601.03081.crystals_components_unique.R2.H1.lean` | step (crystal uniqueness when n+1 = 2^A p^B: one of a+1, b+1 is a power of two, then a size argument) | [PR #7858](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7858) (opened automatically) |
| `PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1.H1.lean` | step | [PR #7914](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7914) (opened automatically) |
| `Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1.H3.lean` | step | [PR #7636](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7636) (opened automatically) |
| `Erdos386.erdos_386.variants.two.R1.H1.lean` | step | [PR #7639](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7639) (opened automatically) |
| `Arxiv.2501.03234.conjecture_1_1.R1.H2.R1.H1.lean` | step | [PR #7681](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7681) (opened automatically) |
| `EllipticCurveRank.RatEllipticCurve.goldfeld_conjecture.variants.two_le.R1.H1.R1.H2.lean` | step | [PR #7751](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7751) (opened automatically) |
| `Erdos604.erdos_604.variants.katz_tardos.R1.H2.lean` | step | [PR #7861](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7861) (opened automatically) |
| `Erdos398.erdos_398.R1.H2.lean` | step | [PR #7907](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7907) (opened automatically) |
| `Arxiv.2610.08796.exists_isPolyTime_bayesNash.R1.H1.lean` | step (hard step, rated 4/10: polynomial-time Turing machine composition) | [PR #7934](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7934) (opened automatically) |
| `Erdos713.erdos_713.parts.ii.R1.H1.lean` | step (hard step, rated 4/10) | [PR #7935](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7935) (opened automatically) |
| `Green47.green_47.variants.finite_exceptions.R1.H1.lean` | step | [PR #7853](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7853) (opened automatically) |
| `Erdos789.erdos_789.variants.sq.R1.H1.lean` | step | [PR #7929](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7929) (opened automatically) |
| `Erdos398.erdos_398.R1.H1.lean` | step | [PR #7738](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7738) (opened automatically) |
| `Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.H2.R1.H2.lean` | step | [PR #7868](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7868) (opened automatically) |
| `Erdos458.erdos_458.R1.H1.lean` | step | [PR #7910](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7910) (opened automatically) |
| `Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.H2.R1.H3.lean` | step | [PR #7941](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7941) (opened automatically) |
| `Erdos1210.erdos_1210.variants.er80_correction.R1.H1.lean` | step | [PR #7975](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7975) (opened automatically) |
| `Erdos81.erdos_81.R1.H1.lean` | step | [PR #7986](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7986) (opened automatically) |
| `Erdos36.minimum_overlap.variants.lower.white_2022.R1.H3.lean` | step | [PR #8055](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8055) (opened automatically) |
| `Erdos292.erdos_292.variants.martin.R1.H2.lean` | step | [PR #8065](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8065) (opened automatically) |
| `Erdos560.erdos_560.variants.conlon_fox_wigderson.R1.H1.lean` | step | [PR #8105](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8105) (opened automatically) |
| `Erdos457.erdos_457.variants.one_sub.R1.H1.lean` | step | [PR #8203](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8203) (opened automatically) |
| `Erdos86.erdos_86.R1.H1.lean` | step | [PR #8213](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8213) (opened automatically) |
| `oeis-a000188.lean` | **open problem** (site statement) | [PR #8207](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8207) (opened automatically) |
| `oeis-a092506.lean` | **open problem** (site statement) | [PR #8227](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8227) (opened automatically) |
| `oeis-a000126.lean` | **open problem** (site statement) | [PR #8268](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8268) (opened automatically) |
| `oeis-a068598.lean` | **open problem** (site statement) | [PR #8275](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8275) (opened automatically) |
| `Erdos695.erdos_695.variants.upperBound.R1.H1.lean` | step | [PR #8200](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8200) (opened automatically) |
| `Erdos388.erdos_388.variants.general.R1.H1.lean` | step | [PR #8145](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8145) (opened automatically) |
| `Green92.green_92.variants.chase_lower.R1.H1.R1.H2.R1.H1.lean` | step | [PR #8349](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8349) (opened automatically) |
| `oeis-a184894.lean` | **open problem** (site statement) | [PR #8291](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8291) (opened automatically) |
| `oeis-a196200.lean` | **open problem** (site statement) | [PR #8301](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8301) (opened automatically) |
| `oeis-a189202.lean` | **open problem** (site statement) | [PR #8436](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8436) (opened automatically) |
| `oeis-a256171.lean` | **open problem** (site statement) | [PR #8784](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8784) (opened automatically) |
| `oeis-a261387.lean` | **open problem** (site statement) | [PR #8794](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8794) (opened automatically) |
| `oeis-a000392.lean` | **open problem** (site statement) | [PR #8267](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8267) (opened automatically) |
| `oeis-a000364.lean` | **open problem** (site statement) | [PR #8323](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8323) (opened automatically) |
| `oeis-a000350.lean` | **open problem** (site statement) | **merged** ([PR #8383](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8383)); counts as an open problem solved once the site confirms the statement |
| `oeis-a001045.lean` | **open problem** (site statement) | **merged** ([PR #8389](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8389)); counts as an open problem solved once the site confirms the statement |
| `oeis-a204988.lean` | **open problem** (site statement) | **merged** ([PR #8431](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8431)); counts as an open problem solved once the site confirms the statement |
| `oeis-a001595.lean` | **open problem** (site statement) | [PR #8440](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8440) (opened automatically) |
| `oeis-a000262.lean` | **open problem** (site statement) | **merged** ([PR #8480](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8480)); counts as an open problem solved once the site confirms the statement |
| `oeis-a000579.lean` | **open problem** (site statement) | [PR #8522](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8522) (opened automatically) |
| `erdos-684.lean` | **open problem** (site statement) | [PR #9213](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9213) (opened automatically) |
| `Erdos1191.erdos_1191.parts.ii.R2.H2.lean` | step | [PR #9215](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9215) (opened automatically) |
| `Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H1.lean` | step | [PR #9217](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9217) (opened automatically) |
| `Erdos332.erdos_332.lean` | **complete problem** | [PR #10136](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10136) (opened automatically) |
| `Erdos357.erdos_357.variants.monotone.parts.ii.littleO_version_symm.lean` | **complete problem** | [PR #10206](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10206) (opened automatically) |
| `Erdos535.erdos_535.R2.H1.R1.H2.lean` | step | [PR #10237](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10237) (opened automatically) |
| `arxiv-2606.27961.R1.H1.lean` | step | [PR #10340](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10340) (opened automatically) |
| `oeis-a267872.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof, already accepted locally, follows once it is merged) | [PR #10411](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10411); no merger verdict after 5 h, resubmitted as [PR #15268](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15268); proof adapted to the competing statement #14384 (Mapika): [PR #16803](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16803) |
| `oeis-a188148.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof, already accepted locally, follows once it is merged) | [PR #10451](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10451); no merger verdict after 5 h, resubmitted as [PR #15266](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15266); proof PR [#16644](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16644) |
| `oeis-a273743.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof, already accepted locally, follows once it is merged) | [PR #10472](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10472); no merger verdict after 5 h, resubmitted as [PR #15270](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15270); proof PR [#16645](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16645) |
| `SierpinskiNumber.prime_sierpinski_problem.R1.H1.R1.H1.lean` | step | [PR #10490](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10490) (opened automatically) |
| `oeis-a273384.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof, already accepted locally, follows once it is merged) | [PR #10499](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10499); no merger verdict after 5 h, resubmitted as [PR #15269](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15269); proof PR [#16646](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16646) |
| `oeis-a000166.R1.H1.lean` | step | [PR #10500](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10500) (opened automatically) |
| `oeis-a273766.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof follows once it is merged) | [PR #10521](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10521) (opened automatically); no merger verdict after 5 h, resubmitted as [PR #15272](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15272); proof adapted to the competing statement #13785 (clementtrecourt): [PR #16891](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16891) |
| `oeis-a273408.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof follows once it is merged) | [PR #10524](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10524) (opened automatically); no merger verdict after 5 h, resubmitted as [PR #15273](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15273); proof adapted to the competing statement #13844 (clementtrecourt): [PR #16825](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16825) |
| `Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H2.R1.H1.lean` | step | [PR #10531](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10531) (opened automatically) |
| `oeis-a180486.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof follows once it is merged) | [PR #10542](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10542) (opened automatically); no merger verdict after 5 h, resubmitted as [PR #15275](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15275); proof PR [#16647](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16647) |
| `oeis-a273789.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof follows once it is merged) | [PR #10544](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10544) (opened automatically); no merger verdict after 5 h, resubmitted as [PR #15277](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15277); proof PR [#16648](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16648) |
| `Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H2.R1.H2.lean` | step | [PR #10553](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10553) (opened automatically) |
| `oeis-a119652.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof follows once it is merged) | [PR #10557](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10557) (opened automatically); no merger verdict after 5 h, resubmitted as [PR #15283](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15283); proof PR [#16652](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16652) |
| `oeis-a208139.lean` | **OEIS conjecture, first Lean statement** (statement PR for review; our full Lean proof follows once it is merged) | [PR #10570](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10570) (opened automatically); no merger verdict after 5 h, resubmitted as [PR #15279](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/15279); proof PR [#16651](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16651) |
| `oeis-a162024.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #16674](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16674); proof [PR #16694](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16694) |
| `oeis-a165372.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #16675](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16675); proof [PR #16697](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16697) |
| `oeis-a183897.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #16676](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16676); proof [PR #16699](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16699) |
| `oeis-a184130.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #16677](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16677); proof [PR #16698](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16698) |
| `oeis-a183906.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #16717](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16717); proof [PR #16888](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16888) |
| `oeis-a187164.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #16871](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16871); proof [PR #16889](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16889) |
| `Erdos963.erdos_963.parts.ii.R1.H3.lean` | step | [PR #10673](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10673) (opened automatically) |
| `Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H1.R1.H1.lean` | step | [PR #10777](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10777) (opened automatically) |
| `Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.lean` | step | [PR #10824](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10824) (opened automatically) |
| `Erdos604.erdos_604.variants.average.R2.H2.R1.H1.R1.H2.lean` | step | [PR #10819](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10819) (opened automatically) |
| `erdos-634.R1.H3.R1.H4.R1.H2.lean` | step | [PR #10952](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10952) (opened automatically) |
| `Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H2.R1.H1.lean` | step | [PR #11410](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11410) (opened automatically) |
| `PoincareConjecture.poincare_conjecture.R1.H4.R1.H2.R1.H1.R2.H1.lean` | step | [PR #11192](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11192) (opened automatically) |
| `riemannZeta.distinct_prop_lt.R1.H2.lean` | step | [PR #11284](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11284) (opened automatically) |
| `Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H1.R1.H2.lean` | step | [PR #11395](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11395) (opened automatically) |
| `Erdos423.erdos_423.variants.upper_bound.R1.H2.lean` | step | [PR #11885](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11885) (opened automatically) |
| `PoincareConjecture.poincare_conjecture.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.lean` | step | [PR #12113](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12113) (opened automatically) |
| `erdos-550.lean` | **open problem** (site statement); disproof of the statement as formalized (it bounds only the smallest class, the source needs n large relative to all classes), so reviewers may flag it | [PR #12411](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12411) (opened automatically) |
| `oeis-a390815.lean` | **open problem** (site statement) | [PR #13074](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/13074) (opened automatically) |
| `oeis-a072872.lean` | **open problem** (site statement): **counterexample** to the OEIS conjecture a(n) < prime(n) for n > 47: a(6298) = 77742 > prime(6298) = 62753 (6298 = 2·47·67) | [PR #13111](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/13111) (opened automatically) |
| `oeis-a184540.lean` | **OEIS conjecture, first Lean statement** (statement PR; our proof follows right after) | [PR #16635](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16635) (opened automatically); proof [PR #16695](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16695) |
| `oeis-a188572.lean` | proof queued | branch `oma/oeis-a188572` pushed; PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a226839.lean` | proof queued | branch `oma/oeis-a226839` pushed; PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a084199.lean` | proof queued | branch `oma/oeis-a084199` pushed; PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a176612.lean` | proof queued | branch `oma/oeis-a176612` pushed; PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a082382.lean` | proof queued | branch `oma/oeis-a082382` pushed; PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a089001.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a154145.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a290192.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a085928.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a222139.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a267210.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `mo-81816.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a094076.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a267604.lean` | proof queued | PR waits until GitHub Actions is re-enabled on the fork |
| `oeis-a290835.lean` | proof (statement pending in #15553 by jleguina) | branch `oma/oeis-a290835` pushed; PR queued |
| `oeis-a330910.lean` | proof (statement pending in #15556 by jleguina) | [PR #16719](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16719) (opened automatically) |
| `oeis-a081124.lean` | proof (statement pending in #15526 by Dugongue) | [PR #17175](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17175) (opened automatically) |
| `oeis-a277864.lean` | proof (statement pending in #15530 by jleguina) | [PR #17336](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17336) (opened automatically) |
| `oeis-a327123.lean` | proof (statement pending in #15529 by Volkopat) | [PR #17431](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17431) (opened automatically) |
| `mo-26856.lean` | proof (statement pending in #15725 by AkiRA-COM-FP) | [PR #17168](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17168) (opened automatically) |
| `oeis-a191017.lean` | proof (statement pending in #15724 by xor2k) | [PR #17252](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17252) (opened automatically) |
| `oeis-a267946.lean` | proof (statement pending in #15721 by jleguina) | [PR #17668](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17668) (opened automatically) |
| `oeis-a276752.lean` | proof (statement pending in #15723 by KoaOkano) | [PR #17506](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17506) (opened automatically) |
| `oeis-a345003.lean` | proof (statement pending in #15730 by jleguina) | [PR #17248](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17248) (opened automatically) |
| `oeis-a355414.lean` | proof (statement pending in #15734 by Volkopat) | [PR #17415](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17415) (opened automatically) |
| `oeis-a079278.lean` | proof (statement pending in #15488 by Dugongue) | [PR #18153](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18153) (opened automatically) |
| `oeis-a081669.lean` | proof (statement pending in #15485 by Dugongue) | [PR #18371](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18371) (opened automatically) |
| `oeis-a154150.lean` | proof (statement pending in #15487 by jleguina) | [PR #18486](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18486) (opened automatically) |
| `oeis-a284540.lean` | proof (statement pending in #15491 by clementtrecourt) | [PR #18773](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18773) (opened automatically) |
| `oeis-a195233.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #19012](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19012); proof [PR #19020](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19020) |
| `oeis-a195249.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #19065](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19065); proof [PR #19082](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19082) |
| `opg-distribution-and-upper-bound-of-mimic-numbers.lean` | **open problem** (Open Problem Garden, proved by Fable 5.2; no published proof of this formalization found) | [PR #9085](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9085) |
| `oeis-a074882.lean` | proof (statement pending in #15570 by jleguina) | [PR #16625](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16625) |
| `oeis-a267539.lean` | proof (statement pending in #15747 by alkrssve) | [PR #16663](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16663) |
| `oeis-a071713.lean` | proof (statement pending in #15744 by Dugongue) | [PR #16678](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16678) |
| `mo-428070.lean` | proof (statement pending in #15738 by dwilfand-sys) | [PR #16752](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16752) |
| `opg-a-gold-grabbing-game.lean` | proof (statement pending in #15740 by AkiRA-COM-FP) | [PR #16875](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16875) |
| `oeis-a290834.lean` | proof (statement pending in #15545 by jleguina) | [PR #16936](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16936) |
| `oeis-a222276.lean` | proof (statement pending in #15751 by jleguina) | [PR #16949](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16949) |
| `oeis-a267604.lean` | proof (statement pending in #15753 by alkrssve) | [PR #16983](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16983) |
| `oeis-a290681.lean` | proof (statement pending in #15537 by jleguina) | [PR #16992](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16992) |
| `oeis-a345051.lean` | proof (statement pending in #15742 by jleguina) | [PR #17007](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17007) |
| `oeis-a377112.lean` | proof (statement pending in #15543 by jleguina) | [PR #17011](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17011) |
| `oeis-a084611.lean` | proof (statement pending in #15550 by Dugongue) | [PR #17134](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17134) |
| `mo-134513.lean` | proof (statement pending in #15519 by chuyeow) | [PR #17269](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17269) |
| `oeis-a265428.lean` | proof (statement pending in #15523 by jleguina) | [PR #17433](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17433) |
| `oeis-a130091.lean` | proof (statement pending in #15709 by xor2k) | [PR #17598](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17598) |
| `oeis-a078522.lean` | proof (statement pending in #15511 by Dugongue) | [PR #17600](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17600) |
| `oeis-a079491.lean` | proof (statement pending in #15492 by Dugongue) | [PR #17663](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17663) |
| `oeis-a082207.lean` | proof (statement pending in #15503 by Dugongue) | [PR #17685](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17685) |
| `oeis-a266791.lean` | proof (statement pending in #15500 by jleguina) | [PR #17762](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17762) |
| `oeis-a396102.lean` | proof (statement pending in #15502 by Volkopat) | [PR #17859](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17859) |
| `oeis-a355407.lean` | proof (statement pending in #15704 by Volkopat) | [PR #17861](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17861) |
| `oeis-a228254.lean` | proof (statement pending in #15714 by jleguina) | [PR #17927](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17927) |
| `oeis-a078128.lean` | proof (statement pending in #15496 by Dugongue) | [PR #17969](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17969) |
| `oeis-a267526.lean` | proof (statement pending in #15699 by jleguina) | [PR #18030](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18030) |
| `oeis-a187608.lean` | proof (statement pending in #15510 by jleguina) | [PR #18044](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18044) |
| `opg-funcolidal-products-inside-an-inward-reloid.lean` | proof (statement pending in #15695 by Dugongue) | [PR #18065](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18065) |
| `oeis-a154154.lean` | proof (statement pending in #15493 by jleguina) | [PR #18080](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18080) |
| `oeis-a079278.lean` | proof (statement pending in #15488 by Dugongue) | [PR #18153](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18153) |
| `oeis-a154140.lean` | proof (statement pending in #15707 by jleguina) | [PR #18191](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18191) |
| `oeis-a068129.lean` | **disproof** (statement pending in #15693 by Dugongue; counterexample T = 1: the only triangular numbers with digit sum 1 are 1 and 10) | [PR #18215](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18215) |
| `Erdos713.erdos_713.parts.i.R3.H2.lean` | **Step of an open $500 Erdős problem (713), proved by Fable** — for a forest F with no isolated vertices and at least 2 edges, ex(n,F)/n converges; elementary argument written from scratch (robust patterns, layered blow-up over a bounded hub set, degree cascade, amplification) | [PR #18340](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18340) |
| `oeis-a283641.lean` | proof (statement pending in #15499 by clementtrecourt) | [PR #18360](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18360) |
| `oeis-a081669.lean` | proof (statement pending in #15485 by Dugongue) | [PR #18371](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18371) |
| `oeis-a188556.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #18358](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18358); proof [PR #18374](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18374) |
| `oeis-a188785.lean` | **OEIS conjecture, first Lean statement + proof** | statement [PR #18359](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18359); proof [PR #18375](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18375) |
| `oeis-a188861.lean` | **OEIS conjecture, proof** adapted to the competing statement filed first (statement pending in #17997 by cj-55m; our own statement was not filed) | [PR #18422](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18422) |
| `oeis-a266841.lean` | proof (statement pending in #15689 by jleguina; Rule 69 automaton: explicit rows, closed forms, recurrence and g.f.) | [PR #18435](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18435) |
| `oeis-a078130.lean` | proof (statement pending in #15477 by Dugongue; numbers with exactly one partition into cubes > 1 are finite: two {8,27}-partitions for n >= 405) | [PR #18470](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18470) |
| `oeis-a067567.lean` | proof (statement pending in #15685 by Dugongue; Bala's partition-convolution divisibility and parity: pair k with n - k, k^(2m+1) + (n-k)^(2m+1) is divisible by n) | [PR #18558](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18558) |
| `oeis-a088120.lean` | **disproof** (statement pending in #15686 by Dugongue; part (2) fails at n = 12: 1*3*...*23 + 2 = 316234143227 is prime and beats every d = 1 value) | [PR #18757](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18757) |
| `mo-267651.lean` | proof (statement pending in #15481 by keiichisince1986-bot; via Dirichlet, every progression p + kq with distinct primes p, q has infinitely many primes, so the set of pairs is empty) | [PR #18778](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18778) |
| `oeis-a077866.lean` | proof (statement pending in #15478 by Dugongue; subsets with least two elements summing to the max: bijection with (x, y, T), explicit sum, recurrence) | [PR #18793](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18793) |
| `oeis-a282289.lean` | **disproof** (statement pending in #15483 by EmircanEsen; counterexample to the conjecture a(n) > 0 for n > 27: 340473 is not a sum of four prime powers p^k with k >= 2, checked by a kernel bitset computation) | [PR #18898](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18898) |
| `oeis-a154141.lean` | proof (statement pending in #15480 by jleguina; Pell-type descent for (2k+1)^2 + 63 = 8m^2: two orbits under (k, m) -> (3k+4m+1, 2k+3m+1), Nat.nth identification, recurrence and both g.f.s) | [PR #19016](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19016) |
| `oeis-a087554.lean` | **disproof** (statement pending in #15662 by Dugongue; part (2) fails for n = 2, r = 3: the only S with 6 < S < 8 is 7 and 2*7+1 = 15) | [PR #18918](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18918) |
| `oeis-a110408.lean` | **disproof** (statement pending in #15666 by jleguina; n = 121 is a counterexample: rev 121 = 121, every 121...121 is divisible by 121, so a(121) = 0, but 121 is neither prime nor a multiple of 3) | [PR #18939](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18939) |
| `oeis-a154153.lean` | proof (statement pending in #15667 by jleguina; Pell-type descent for (2k+1)^2 + 223 = 8m^2: solutions (6,7), (8,8) and (k, m) -> (3k+4m+1, 2k+3m+1), Nat.nth identification, recurrence and both g.f.s) | [PR #19047](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19047) |
| `oeis-a285778.lean` | proof (statement pending in #15470 by jleguina; Rule 89 automaton: background outside the box [-t, t]^2, stage 4 entirely OFF, then the plane alternates OFF/ON; closed forms, recurrence and g.f.) | [PR #19029](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19029) |
| `oeis-a207402.lean` | proof (statement pending in #15653 by clementtrecourt; n X 7 arrays split into even (width 4) and odd (width 3) columns, transfer on row pairs with T m x y = sum C(d,i) C(m,i), d the Hamming distance; a(n) = (2C(n+4,4)-5)(2C(n+3,3)-4), recurrence and g.f.) | [PR #19342](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19342) |
| `oeis-a154151.lean` | proof (statement pending in #15655 by jleguina; Pell-type descent for (2k+1)^2 + 199 = 8m^2: solutions (0,5), (18,14) and (k, m) -> (3k+4m+1, 2k+3m+1), Nat.nth identification, recurrence and both g.f.s) | [PR #19441](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19441) |
| `mo-35878.lean` | proof (statement pending in #15468 by AkiRA-COM-FP; residue degree divides dim_k A for a finite-dimensional local k-algebra: strong induction on k-dimension of A-modules, a minimal submodule is simple hence isomorphic to A/m) | [PR #19128](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19128) |
| `oeis-a166587.lean` | proof (statement pending in #15630 by Mapika; Mathar's recurrence for the signed Motzkin g.f.: S^2 = 1 + 2x - 3x^2 gives (1 + 2x - 3x^2) S' = (1 - 3x) S, an order-2 recurrence R(m) = 0, and the conjectured recurrence is n R(n) - (n-2) R(n-1)) | [PR #19528](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19528) |
| `oeis-a087553.lean` | proof (statement pending in #15651 by Dugongue; the statement only excludes 10^(2k) and 9*10^(2k), so 121*100^k = (11*10^k)^2, with digits 1 2 1 0 ... 0, is an infinite family of nontrivial terms) | [PR #19163](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19163) |
| `oeis-a396722.lean` | proof (statement pending in #15643 by Mapika; Lagrange.sum_basis gives p(n) = 1 - basis_0, whose value at 5/2 is a product e(n) with (n+1) e(n+1) = (n - 1/2) e(n); Mathar's recurrence follows by field_simp) | [PR #19248](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19248) |
| `oeis-a208065.lean` | proof (statement pending in #15638 by clementtrecourt; the vertical rule says row i+2 is bitwise below row i, so transfer on row pairs factors as G m u v = D((m+1)/2, u) D(m/2, v) with D counting chains of allowed rows; 2D is quadratic, a(m+2) = S((m+1)/2) S(m/2) with S(k) = 2k^2+12k+10; both closed forms and the g.f.) | [PR #19440](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19440) |
| `oeis-a154148.lean` | proof (statement pending in #15646 by jleguina; Pell-type descent for x^2 + 167 = 8y^2: solutions (11,6), (15,7) and (x, y) -> (3x+8y, x+3y), Nat.nth identification via eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn, recurrence, g.f. and partial fractions) | [PR #19531](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19531) |
| `oeis-a154144.lean` | proof (statement pending in #15637 by jleguina; Pell-type descent for (2k+1)^2 + 103 = 8m^2: solutions (2,4), (8,7) and (k, m) -> (3k+4m+1, 2k+3m+1), Nat.nth identification, recurrence and both g.f.s) | [PR #19652](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19652) |
| `oeis-a088500.lean` | proof (statement pending in #15705 by Dugongue) | [PR #18385](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18385) |
| `oeis-a207389.lean` | proof (statement pending in #15672 by clementtrecourt) | [PR #19037](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19037) |
| `oeis-a077625.lean` | proof (statement pending in #15463 by Dugongue) | [PR #19091](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19091) |
| `oeis-a127710.lean` | proof (statement pending in #15466 by jleguina) | [PR #19212](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19212) |
| `oeis-a077624.lean` | proof (statement pending in #15456 by Dugongue) | [PR #19300](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19300) |
| `oeis-a079665.lean` | proof (statement pending in #15449 by Dugongue) | [PR #19405](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19405) |
| `oeis-a273406.lean` | proof (statement pending in #15446 by jleguina) | [PR #19445](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19445) |
| `oeis-a279053.lean` | proof (statement pending in #15451 by clementtrecourt) | [PR #19482](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19482) |
| `oeis-a076821.lean` | proof (statement pending in #15434 by Dugongue) | [PR #19577](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19577) |
| `oeis-a072780.lean` | proof (statement pending in #15438 by Dugongue) | [PR #19704](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19704) |
| `oeis-a023811.lean` | proof (statement pending in #15454 by Dugongue) | [PR #19745](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19745) |
| `oeis-a072944.lean` | proof (statement pending in #15455 by Dugongue) | [PR #19905](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19905) |
| `oeis-a273405.lean` | proof (statement pending in #15435 by jleguina) | [PR #19956](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19956) |
| `oeis-a207390.lean` | proof (statement pending in #15624 by clementtrecourt; transfer on row pairs over the 31 allowed rows, each of the 961 pair counts is a degree-7 polynomial in the binomial basis, checked by the kernel in 31 chunks; closed form, recurrence and g.f.) | [PR #20104](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20104) |
| `oeis-a154143.lean` | proof (statement pending in #15628 by jleguina; Pell-type descent for (2k+1)^2 + 79 = 8m^2: solutions (3,4), (5,5) and (k, m) -> (3k+4m+1, 2k+3m+1), Nat.nth identification, recurrence and both g.f.s) | [PR #20186](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20186) |
| `oeis-a309291.lean` | proof (statement pending in #15405 by xor2k; for k > 4 a composite p = k! - q in [k, k^2] has a prime factor at most k, which divides k! and hence the prime q > k) | [PR #20377](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20377) |
| `oeis-a187288.lean` | **OEIS conjecture, proof** adapted to the competing statement filed first (statement pending in #16364 by jleguina; our own statement was not filed) | [PR #20088](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20088) |
| `oeis-a187298.lean` | **OEIS conjecture, proof** adapted to the competing statement filed first (statement pending in #16372 by jleguina; our own statement was not filed) | [PR #20054](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20054) |
| `oeis-a187853.lean` | **OEIS conjecture, proof** adapted to the competing statement filed first (statement pending in #17883 by jleguina; our own statement was not filed) | [PR #20582](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20582) |
| `oeis-a283649.lean` | proof (statement pending in #15409 by jleguina; from stage 3 on the plane is all ON except the 3x3 block at the origin, whose center is ON exactly at odd stages, proved by a 7x7 case split on clamped coordinates; closed form, recurrence and g.f.) | [PR #20602](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20602) |
| `oeis-a267209.lean` | proof (statement pending in #15588 by jleguina; closed form of Rule 109 from a single cell: background outside the light cone, two edge diagonals, and inside a 3 x 12 periodic table indexed by stage mod 3 and distance mod 12, proved by induction with finitely many residue checks; middle column has period 3, giving the recurrence and g.f.) | [PR #20569](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20569) |
| `oeis-a316584.lean` | proof (statement pending in #15592 by jleguina; T(p,p) = p^2: in characteristic p, x^p = 1 iff (x - 1)^2 = 0 for 2 x 2 matrices (Cayley-Hamilton), x -> x - 1 is a bijection onto the matrices [[a, b], [c, -a]] with a^2 + bc = 0, and these are counted by a bijection with pairs) | [PR #20678](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20678) |
| `oeis-a207363.lean` | proof (statement pending in #15587 by clementtrecourt; the vertical condition only links rows two apart, so rows of each parity form a decreasing chain of the 6 allowed rows; a(n) = Q((n+1)/2) Q(n/2) with Q k = (k+1)(2k+1), giving both closed forms and the g.f.) | [PR #20764](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20764) |
| `oeis-a085094.lean` | **OEIS conjecture, proof** (statement pending in #15590 by Dugongue; no entry of A085094 is zero: for n = 2^a 5^b m, an explicit palindrome with digits 8 and 9, built by wrapping 9 in blocks 8 9...9 of length phi(m) and its reverse, is congruent to -1 mod n) | [PR #20860](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20860) |
| `oeis-a378575.lean` | proof (statement pending in #15401 by Volkopat; reduce mod 4 through a ring hom, x/(1-x) is a fixed point there since the r-fold self-composition of x/(1-x) is x/(1-rx) and 5 = 1 in ZMod 4; uniqueness by locality of the truncated composition) | [PR #20634](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20634) |
| `mo-243978.lean` | **disproof** (statement pending in #19949 by caa1982; with φ = g f - x g the equation gives φ' = -g and φ(0) = 0, so the mean value theorem turns γ x ≤ g x f x into γ ≤ g(x) - g(c) with 0 < c < x, contradicting continuity of g at 0) | [PR #20631](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20631) |
| `oeis-a261702.lean` | proof (statement pending in #19946 by etaubman; a finite set of positive integers always has an eligible element (1, or twice its maximum), so terms are positive and new; an element eligible from some stage on is chosen within k steps by pigeonhole on [1, k], and induction on ReachesOne gives surjectivity under Collatz) | [PR #20669](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20669) |
| `oeis-a252505.lean` | proof (statement pending in #19944 by esracummings31-blip; the largest 4th-power-free divisor m of n has v_p(m) = min(v_p(n), 3), so the 4th-power-free divisors of n are exactly the divisors of m, compared through factorizations) | [PR #20699](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20699) |
| `oeis-a131853.lean` | proof (statement pending in #19931 by frido22; the ring map Z[i] -> Z/5 sending i to 2 is compatible with the digit recursion, since appending a bit doubles n and multiplies z by i, so n is congruent mod 5 to Re z(n) + 2 Im z(n), proved by strong induction) | [PR #20755](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20755) |
| `oeis-a257106.lean` | proof (statement pending in #19953 by caa1982; sum_bernoulli' gives c(n) = B(n) - (-1)^n n/6; odd n: denominator of (2m+1)/6; even n: von Staudt-Clausen makes the denominator of B(2m) + 1/3 prime to 3, so subtracting (m+1)/3 keeps or removes the factor 3 according to m mod 3) | [PR #20792](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20792) |
| `oeis-a198900.lean` | proof (statement pending in #19925 by KoaOkano; by symmetry the number of extensions from a proper last row depends only on the number of introduced colors, giving a 4-state linear recursion F(n+1,t) = (t+1+t^2) F(n,t) + 2(t+1) F(n,t+1) + F(n,t+2) with solutions 13^n, 13^n, (3^n+13^n)/2 and (2+3^(n+1)+13^n)/6; the recurrence follows from the closed form) | [PR #20822](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20822) |
| `oeis-a183624.lean` | proof (statement pending in #15602 by Mapika; with two columns the row sums alternate s, 4-s, s, ..., the number of rows over 0..2 with sum s is c(s) = 1, 2, 3, 2, 1 with c(4-s) = c(s), so splitting off the first row gives c(s)^(n+1) arrays per first-row sum and a(n) = 2 + 2^(n+2) + 3^(n+1); recurrence and g.f. follow) | [PR #20454](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20454) |
| `oeis-a265431.lean` | proof (statement pending in #15596 by jleguina; Rule 188 is (l xor c) or (l and c and r), and by induction stage n is ON exactly at 0 <= x <= n with x = 0 or x + n not 3 mod 4, so row k has k + floor((2k+1)/4) - floor((k+1)/4) OFF cells, a(n+4) = a(n) + 5n + 12; closed form by induction in steps of 4 and g.f. by coefficients) | [PR #20592](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20592) |
| `oeis-a207110.lean` | proof (statement pending in #15600 by clementtrecourt; transfer recursion over pairs of the 25 valid rows, and a kernel-checked table of Newton coefficients shows each pair has sum_k tab(u,v,k) C(m,k) continuations, so a(n+2) = 625 + 2774 C(n,1) + ... + 18 C(n,7), a degree-7 polynomial also giving a(1) = 25; eighth-difference recurrence and g.f. follow) | [PR #20833](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20833) |
| `oeis-a207846.lean` | proof (statement pending in #19963 by sntntHb; column transfer over the 6 non-constant 3-bit columns, where a column must cover the zeros of the next except for the last pair; the counts satisfy G(k+3) = 2G(k+2) + G(k+1) code by code, giving a(n+2) = 2a(n+1) + a(n) for n >= 2, the g.f. and the closed form in 1 +- sqrt 2) | [PR #20886](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20886) |
| `oeis-a273312.lean` | **disproof** (statement pending in #19914 by longling12; the recurrence clause is stated for n > 2 but fails at n = 4, where it reaches back to a 1 = 13 before the periodic regime: a 4 = 39 while a 3 + a 2 - a 1 = 43, checked by kernel evaluation of the automaton to stage 5) | [PR #20887](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20887) |
| `oeis-a389540.lean` | proof (statement pending in #19930 by Solitude1312; with G = X - A = X^2 K, A(2G) = 2G - 4G^2 K(2G), so halving the equation gives G = X^2 - 2XG + G^2 + 2G^2 K(2G); modulo 2 this is G = X^2 + G^2, and the coefficient of X^n in G^2 is congruent to that of X^(n/2) in G squared (pairing i with n - i), so by strong induction the odd coefficients of G sit exactly at n = 2^k, k >= 1) | [PR #20967](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20967) |

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

**Erdős 792, Bourgain's sum-free bound** (proved by Fable 5.2): every set of `n ≥ 3` positive integers
has a sum-free subset of size at least `(n+2)/3`. The proof uses only dilation-type sets
`{a : ⌊a t / M⌋ ≡ 1 (mod 3)}`, which are always sum-free:
- **Lifting:** shifting `t` by `M` or `2M` leaves the multiples of 3 alone and selects every other element exactly once.
- **Induction:** divide the multiples of 3 by 3 and apply the statement to them.
- **Hard case:** two multiples of 3 of the form `{3v, 6v}`. A carefully chosen pair of nearby ratios makes the split uneven.
