import OMAStatements.S_oeis_a166587
import Mathlib

-- Proof: S^2 = 1 + 2x - 3x^2 gives (1 + 2x - 3x^2) S' = (1 - 3x) S; with S = 1 + 3x - 2xG this is
-- R(m) = (m+1) g(m) + (2m-1) g(m-1) - 3(m-2) g(m-2) = 0 for m >= 2, and the conjectured
-- recurrence at n is n R(n) - (n-2) R(n-1).

namespace OMA.Helpers

open PowerSeries

theorem a166587_ofNat_mul (k : ℕ) [k.AtLeastTwo] (n : ℕ) (φ : ℚ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat k) : ℚ⟦X⟧) * φ) = (OfNat.ofNat k : ℚ) * coeff n φ := by
  rw [← map_ofNat (C (R := ℚ)) k, coeff_C_mul]

theorem a166587_deriv_ofNat (k : ℕ) [k.AtLeastTwo] :
    d⁄dX ℚ (no_index (OfNat.ofNat k) : ℚ⟦X⟧) = 0 := by
  have := Derivation.map_natCast (d⁄dX ℚ) (A := ℚ⟦X⟧) k
  exact this

theorem a166587_ode (S : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 2 * X - 3 * X ^ 2) :
    2 * d⁄dX ℚ S + 4 * (X ^ 1 * d⁄dX ℚ S) - 6 * (X ^ 2 * d⁄dX ℚ S)
      = 2 * S - 6 * (X ^ 1 * S) := by
  have h1 : d⁄dX ℚ (S ^ 2) = d⁄dX ℚ (1 + 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) := by rw [hS]
  rw [derivative_pow] at h1
  have hE : d⁄dX ℚ (1 + 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) = 2 - 6 * X := by
    simp [a166587_deriv_ofNat]
    ring
  rw [hE] at h1
  norm_num at h1
  linear_combination S * h1 + (-2 * d⁄dX ℚ S) * hS

theorem a166587_coeff_S (S G : ℚ⟦X⟧) (hG : 2 * X * G = 1 + 3 * X - S) (j : ℕ) :
    coeff (j + 2) S = -2 * coeff (j + 1) G := by
  have hS : S = 1 + 3 * X - 2 * (X * G) := by linear_combination hG
  rw [hS, map_sub, map_add, a166587_ofNat_mul, a166587_ofNat_mul, coeff_one, coeff_X,
    show j + 2 = (j + 1) + 1 by omega, coeff_succ_X_mul]
  simp

theorem a166587_R (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 2 * X - 3 * X ^ 2)
    (hG : 2 * X * G = 1 + 3 * X - S) (k : ℕ) :
    ((k : ℚ) + 3) * coeff (k + 2) G + (2 * (k : ℚ) + 3) * coeff (k + 1) G
      - 3 * (k : ℚ) * coeff k G = 0 := by
  have h := congrArg (coeff (k + 2)) (a166587_ode S hS)
  simp only [map_add, map_sub, a166587_ofNat_mul, coeff_X_pow_mul', coeff_derivative] at h
  simp only [show 1 ≤ k + 2 by omega, show 2 ≤ k + 2 by omega, if_true,
    show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega] at h
  rw [show k + 2 + 1 = (k + 1) + 2 by omega, a166587_coeff_S S G hG (k + 1),
    a166587_coeff_S S G hG k] at h
  rcases k with _ | k
  · push_cast at h ⊢
    linear_combination (-1 / 4 : ℚ) * h
  · rw [show k + 1 + 1 = k + 2 by omega, a166587_coeff_S S G hG k] at h
    push_cast at h ⊢
    linear_combination (-1 / 4 : ℚ) * h

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a166587.main := by
  intro S G hS _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h1 := OMA.Helpers.a166587_R S G hS hG (k + 1)
  have h2 := OMA.Helpers.a166587_R S G hS hG k
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  simp only [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at h1
  push_cast at h1 h2 ⊢
  linear_combination ((k : ℚ) + 3) * h1 - ((k : ℚ) + 1) * h2
