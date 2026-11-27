import FormalConjectures.ErdosProblems.«357»

/-!
# Erdős Problem 357, weakly monotone variant: an explicit `g` with `h = o(g)`

`Erdos357.h n` is the largest `k` for which there are integers `1 ≤ a₁ ≤ ⋯ ≤ aₖ ≤ n` whose sums over
all blocks of consecutive indices are pairwise distinct.

Answer: `g n = n * log n`.

The one-term blocks already have distinct sums, so the `aᵢ` are pairwise distinct integers of
`[1, n]`, and therefore `h n ≤ n` (`h_le_self`). Hence `h = o(g)` for every `g` with `n = o(g)`
(`isLittleO_h_of_natCast_isLittleO`), and `n * log n` is such a `g`.

Scope: this is the elementary upper bound, not a determination of the growth of `h`. The upper bounds
recorded on erdosproblems.com/357 are all linear in `n`: `(2/3 + o(1)) n` (Hegyvári, Acta Math.
Hungar. 1986, for sequences in any order) and `(2/3 - 1/512) n + log n` (Coppersmith and Phillips
1996, see Erdős problem 867). The lower bound recorded there is `(2 + o(1)) √n`. Whether `g n = n`
works, i.e. whether `h = o(n)`, is open: it is the statement `erdos_357.variants.monotone.parts.i`
of the same upstream file, and for strictly increasing sequences it is the question of Erdős and
Harzheim.
-/

open Filter Asymptotics

namespace OMA.Helpers

/-- Distinct sums over the order-connected index sets force distinct terms, because every singleton
is order connected. -/
theorem injective_of_hasDistinctSums {ι α : Type*} [PartialOrder ι] [AddCommMonoid α] {a : ι → α}
    (ha : Erdos357.HasDistinctSums a) : Function.Injective a := by
  intro i j hij
  have key : ({i} : Finset ι) = {j} :=
    ha (by simp [Set.ordConnected_singleton]) (by simp [Set.ordConnected_singleton])
      (by simpa using hij)
  exact Finset.singleton_injective key

/-- The terms are pairwise distinct integers of `[1, n]`, so there are at most `n` of them. -/
theorem h_le_self (n : ℕ) : Erdos357.h n ≤ n := by
  refine csSup_le' ?_
  rintro k ⟨a, hrange, -, hsums⟩
  have hmaps : Set.MapsTo a (Finset.univ : Finset (Fin k)) (Finset.Icc (1 : ℤ) n) := by
    intro i _
    exact Finset.mem_coe.2 (Finset.mem_Icc.2 (hrange (Set.mem_range_self i)))
  have hcard :=
    Finset.card_le_card_of_injOn a hmaps (injective_of_hasDistinctSums hsums).injOn
  simpa using hcard

/-- Every `g` with `n = o(g)` satisfies `h = o(g)`. -/
theorem isLittleO_h_of_natCast_isLittleO {g : ℕ → ℝ}
    (hg : (fun n : ℕ ↦ (n : ℝ)) =o[atTop] g) :
    (fun n ↦ (Erdos357.h n : ℝ)) =o[atTop] g := by
  refine IsBigO.trans_isLittleO (isBigO_of_le _ fun n ↦ ?_) hg
  simpa using h_le_self n

/-- `n = o(n log n)` along the natural numbers. -/
theorem natCast_isLittleO_mul_log :
    (fun n : ℕ ↦ (n : ℝ)) =o[atTop] fun n : ℕ ↦ (n : ℝ) * Real.log n := by
  have h1 : (fun x : ℝ ↦ x * 1) =o[atTop] fun x : ℝ ↦ x * Real.log x :=
    (isBigO_refl _ _).mul_isLittleO Real.isLittleO_const_log_atTop
  simpa [Function.comp_def] using h1.comp_tendsto tendsto_natCast_atTop_atTop

end OMA.Helpers

noncomputable def OMA.answer : ℕ → ℝ := fun n ↦ (n : ℝ) * Real.log n

theorem OMA.solution : Erdos357.erdos_357.variants.monotone.parts.ii.littleO_version_symm.answer = OMA.answer → type_of% @Erdos357.erdos_357.variants.monotone.parts.ii.littleO_version_symm := by
  intro h
  rw [h]
  exact OMA.Helpers.isLittleO_h_of_natCast_isLittleO OMA.Helpers.natCast_isLittleO_mul_log
