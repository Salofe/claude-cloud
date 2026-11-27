import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R2

/-!
# Step H2 of the reduction Erdos307.erdos_307.variants.coprime_one_notMem.R2

For finite sets `P` and `Q` of natural numbers that are all at least two, the cleared-denominator
identity `(∑ cofactors of P) * (∑ cofactors of Q) = (∏ P) * (∏ Q)` holds exactly when
`(∑ 1/a over P) * (∑ 1/b over Q) = 1`.

Proof: over `ℚ`, the cofactor `∏ (P.erase a)` equals `(∏ P) * a⁻¹`, so the sum of cofactors is
`(∏ P)` times the reciprocal sum. Both sides of the natural-number identity are therefore
`(∏ P) * (∏ Q)` times something, namely the product of the reciprocal sums on the left and `1`
on the right, and `(∏ P) * (∏ Q)` is nonzero, so it cancels.

Only Mathlib and the statement of `H2` are used; no upstream theorem.
-/

namespace OMA.Helpers

open Finset

/-- Over `ℚ`, removing a nonzero member `a` from a product of naturals divides it by `a`. -/
theorem erase_prod_cast {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) (ha0 : a ≠ 0) :
    ((∏ x ∈ A.erase a, x : ℕ) : ℚ) = (∏ x ∈ A, (x : ℚ)) * (a : ℚ)⁻¹ := by
  have hq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  rw [Nat.cast_prod, ← mul_prod_erase A (fun x : ℕ => (x : ℚ)) ha, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ hq, one_mul]

/-- The sum of cofactors is the product times the sum of reciprocals. -/
theorem cofactor_sum_cast {A : Finset ℕ} (hA : ∀ a ∈ A, 2 ≤ a) :
    ((∑ a ∈ A, ∏ x ∈ A.erase a, x : ℕ) : ℚ) = (∏ x ∈ A, (x : ℚ)) * ∑ a ∈ A, (a : ℚ)⁻¹ := by
  rw [Nat.cast_sum, mul_sum]
  exact sum_congr rfl fun a ha => erase_prod_cast ha (by have := hA a ha; omega)

/-- A product of naturals that are all at least two is nonzero in `ℚ`. -/
theorem prod_cast_ne_zero {A : Finset ℕ} (hA : ∀ a ∈ A, 2 ≤ a) : (∏ x ∈ A, (x : ℚ)) ≠ 0 :=
  prod_ne_zero_iff.mpr fun a ha => Nat.cast_ne_zero.mpr (by have := hA a ha; omega)

end OMA.Helpers

open OMA.Helpers Finset in
theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R2.H2 := by
  intro P Q hP hQ
  have hM := prod_cast_ne_zero hP
  have hN := prod_cast_ne_zero hQ
  rw [← Nat.cast_inj (R := ℚ), Nat.cast_mul, Nat.cast_mul, cofactor_sum_cast hP,
    cofactor_sum_cast hQ, Nat.cast_prod, Nat.cast_prod,
    show ∀ m u n v : ℚ, m * u * (n * v) = (m * n) * (u * v) from fun m u n v => by ring]
  constructor
  · intro h
    exact mul_left_cancel₀ (mul_ne_zero hM hN) (h.trans (mul_one _).symm)
  · intro h
    rw [h, mul_one]
