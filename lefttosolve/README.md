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
| `Arxiv.2606.03696.bondy_conjecture.variants.three.lean` | **complete problem** (Bondy's longest-cycle conjecture for k = 3, proved by Fable 5.2) | [PR #6031](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6031) |
| `Erdos976.erdos_976.variants.nagell_ricci.lean` | **complete problem** (Nagell–Ricci, proved by Fable 5.2) | [PR #6147](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6147) |
| `Erdos258.erdos_258.variants.monotone.lean` | **complete problem** (monotone variant, proved by Fable 5.2) | [PR #6499](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6499) |
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
