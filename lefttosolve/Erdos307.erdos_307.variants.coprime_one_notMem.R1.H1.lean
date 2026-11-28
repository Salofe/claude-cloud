import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

/-!
# Step H1 of the reduction Erdos307.erdos_307.variants.coprime_one_notMem.R1

Let `A` be a finite set of positive integers and `P = ∏ A`. Every `a ∈ A` divides `P`, so the
natural-number quotient `P / a` is exact and its cast to `ℚ` equals `P * a⁻¹`. Summing over `A`
gives the first identity `P * ∑ a⁻¹ = ∑ (P / a)`.

Inserting a fresh positive `w` replaces `P` by `w * P`. The new cofactor of `w` is
`(w * P) / w = P`, and every old cofactor becomes `(w * P) / a = w * (P / a)` (exact since
`a ∣ P`). Hence the new cofactor sum is `w * ∑ (P / a) + P`, the insertion law.

Only Mathlib and the helper lemmas below are used; no upstream theorem is invoked.
-/

namespace OMA.Helpers

/-- Clearing denominators: the product of `A` times the reciprocal sum of `A` is the sum of the
exact cofactors `(∏ A) / a`. -/
theorem erdos307_cofactorSum_cast (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    (∏ a ∈ A, (a : ℚ)) * (∑ a ∈ A, (a : ℚ)⁻¹) =
      ((∑ a ∈ A, (∏ x ∈ A, x) / a : ℕ) : ℚ) := by
  rw [Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hdvd : a ∣ ∏ x ∈ A, x := Finset.dvd_prod_of_mem (fun x => x) ha
  have hne : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hA a ha).ne'
  rw [Nat.cast_div hdvd hne, Nat.cast_prod, div_eq_mul_inv]

/-- After multiplying the product by `w`, the cofactor of an old member `a` is `w` times its old
cofactor. -/
theorem erdos307_cofactor_mul (A : Finset ℕ) (w a : ℕ) (ha : a ∈ A) :
    w * (∏ x ∈ A, x) / a = w * ((∏ x ∈ A, x) / a) :=
  Nat.mul_div_assoc w (Finset.dvd_prod_of_mem (fun x => x) ha)

/-- Insertion law for the cofactor sum of a fresh positive member `w`. -/
theorem erdos307_cofactorSum_insert (A : Finset ℕ) (w : ℕ) (hw : 0 < w) (hwA : w ∉ A) :
    (∑ a ∈ insert w A, (∏ x ∈ insert w A, x) / a) =
      w * (∑ a ∈ A, (∏ x ∈ A, x) / a) + ∏ x ∈ A, x := by
  have hprod : (∏ x ∈ insert w A, x) = w * ∏ x ∈ A, x := Finset.prod_insert hwA
  have hold : (∑ a ∈ A, (∏ x ∈ insert w A, x) / a) = w * ∑ a ∈ A, (∏ x ∈ A, x) / a := by
    rw [hprod, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a ha => erdos307_cofactor_mul A w a ha
  have hnew : (∏ x ∈ insert w A, x) / w = ∏ x ∈ A, x := by
    rw [hprod, Nat.mul_div_cancel_left _ hw]
  rw [Finset.sum_insert hwA, hold, hnew]
  exact Nat.add_comm _ _

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 := by
  intro A hA
  exact ⟨erdos307_cofactorSum_cast A hA,
    fun w hw hwA => erdos307_cofactorSum_insert A w hw hwA⟩
