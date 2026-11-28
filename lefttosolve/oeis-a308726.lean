import OMAStatements.S_oeis_a308726
import Mathlib

namespace OMA.Helpers

open PowerSeries

theorem D_mul (f g : ℚ⟦X⟧) : PowerSeries.derivative ℚ (f * g) =
    f * PowerSeries.derivative ℚ g + g * PowerSeries.derivative ℚ f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem D_C (a : ℚ) : PowerSeries.derivative ℚ (C a) = 0 := derivative_C

theorem D_two_mul (f : ℚ⟦X⟧) :
    PowerSeries.derivative ℚ (2 * f) = 2 * PowerSeries.derivative ℚ f := by
  rw [← map_ofNat (C (R := ℚ)) 2, D_mul, D_C, mul_zero, add_zero]

theorem ne_zero_of_c0 {f : ℚ⟦X⟧} (h : coeff 0 f = 1) : f ≠ 0 := by
  intro hf
  rw [hf, map_zero] at h
  exact zero_ne_one h

theorem two_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  rw [← map_ofNat (C (R := ℚ)) 2, coeff_zero_C, map_zero] at this
  norm_num at this

theorem cancel_two {a b : ℚ⟦X⟧} (h : 2 * a = 2 * b) : a = b := by
  have h' : (2 : ℚ⟦X⟧) * (a - b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h2 | h2
  · exact absurd h2 two_ne
  · linear_combination h2

/-- The second-order linear ODE satisfied by `W`. -/
theorem W_ode (T W : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 4 * X) (hT0 : coeff 0 T = 1)
    (hW : W ^ 2 = 2 * T - 1) (hW0 : coeff 0 W = 1) :
    (64 * X ^ 2 - 28 * X + 3) * PowerSeries.derivative ℚ (PowerSeries.derivative ℚ W)
      + (64 * X - 14) * PowerSeries.derivative ℚ W - 4 * W = 0 := by
  set D := PowerSeries.derivative ℚ with hD
  have hDT : 2 * (T * D T) = 2 * (-2) := by
    have h := congrArg D hT
    rw [pow_two, D_mul, map_sub, Derivation.map_one_eq_zero,
      ← map_ofNat (C (R := ℚ)) 4, D_mul, D_C, derivative_X] at h
    rw [map_ofNat] at h
    linear_combination h
  have e2 : T * D T = -2 := cancel_two hDT
  have e3 : D T ^ 2 + T * D (D T) = 0 := by
    have h := congrArg D e2
    rw [D_mul, show (-2 : ℚ⟦X⟧) = C (-2) by rw [map_neg, map_ofNat], D_C] at h
    linear_combination h
  have hDW : 2 * (W * D W) = 2 * D T := by
    have h := congrArg D hW
    rw [pow_two, D_mul, map_sub, Derivation.map_one_eq_zero, D_two_mul] at h
    linear_combination h
  have e5 : W * D W = D T := cancel_two hDW
  have e6 : D W ^ 2 + W * D (D W) = D (D T) := by
    have h := congrArg D e5
    rw [D_mul] at h
    linear_combination h
  set A : ℚ⟦X⟧ := 64 * X ^ 2 - 28 * X + 3 with hA
  set B : ℚ⟦X⟧ := 64 * X - 14 with hB
  have h1 : W * (2 * T - 1) * (A * D (D W) + B * D W - 4 * W) =
      A * (2 * T - 1) * D (D T) - A * D T ^ 2 + B * (2 * T - 1) * D T - 4 * (2 * T - 1) ^ 2 := by
    linear_combination (2 * T - 1) * A * e6 + (2 * T - 1) * B * e5 - 4 * (2 * T - 1) * hW
      + A * D W ^ 2 * hW - A * (W * D W + D T) * e5
  have h2 : T ^ 3 * (A * (2 * T - 1) * D (D T) - A * D T ^ 2 + B * (2 * T - 1) * D T
      - 4 * (2 * T - 1) ^ 2) = 0 := by
    rw [hA, hB]
    linear_combination (T ^ 2 * (2 * T - 1) * (4 * X - 1) * (16 * X - 3)) * e3
      + (-192 * D T * T ^ 2 * X ^ 2 + 84 * D T * T ^ 2 * X - 9 * D T * T ^ 2
        + 64 * D T * T * X ^ 2 - 28 * D T * T * X + 3 * D T * T + 128 * T ^ 3 * X - 28 * T ^ 3
        - 64 * T ^ 2 * X + 14 * T ^ 2 + 384 * T * X ^ 2 - 168 * T * X + 18 * T
        - 128 * X ^ 2 + 56 * X - 6) * e2
      + (-4 * (4 * T ^ 3 - 4 * T ^ 2 + 48 * T * X - 9 * T - 16 * X + 3)) * hT
  have h3 : T ^ 3 * (W * (2 * T - 1)) * (A * D (D W) + B * D W - 4 * W) = 0 := by
    rw [mul_assoc, h1, h2]
  have hTne : T ^ 3 * (W * (2 * T - 1)) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero 3 (ne_zero_of_c0 hT0))
    apply mul_ne_zero (ne_zero_of_c0 hW0)
    apply ne_zero_of_c0
    rw [map_sub, ← map_ofNat (C (R := ℚ)) 2, coeff_C_mul, hT0, coeff_one]
    norm_num
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hTne
  · exact h

end OMA.Helpers

namespace OMA.Helpers

open PowerSeries

theorem U_rec (U : ℚ⟦X⟧) (h : PowerSeries.derivative ℚ U - C 4 * (X * PowerSeries.derivative ℚ U)
    = C 2 * U) (k : ℕ) :
    ((k : ℚ) + 1) * coeff (k + 1) U = (4 * (k : ℚ) + 2) * coeff k U := by
  have hk := congrArg (coeff k) h
  rw [map_sub, coeff_C_mul, coeff_C_mul, coeff_derivative] at hk
  rcases k with _ | k
  · rw [coeff_zero_X_mul] at hk
    push_cast at hk ⊢
    linear_combination hk
  · rw [coeff_succ_X_mul, coeff_derivative] at hk
    push_cast at hk ⊢
    linear_combination hk

theorem W_rec (W : ℚ⟦X⟧)
    (h : C 64 * (X ^ 2 * PowerSeries.derivative ℚ (PowerSeries.derivative ℚ W))
      - C 28 * (X * PowerSeries.derivative ℚ (PowerSeries.derivative ℚ W))
      + C 3 * PowerSeries.derivative ℚ (PowerSeries.derivative ℚ W)
      + C 64 * (X * PowerSeries.derivative ℚ W) - C 14 * PowerSeries.derivative ℚ W
      - C 4 * W = 0) (k : ℕ) :
    3 * ((k : ℚ) + 2) * ((k : ℚ) + 3) * coeff (k + 3) W =
      14 * ((k : ℚ) + 2) * (2 * (k : ℚ) + 3) * coeff (k + 2) W
        - (64 * ((k : ℚ) + 1) ^ 2 - 4) * coeff (k + 1) W := by
  rcases k with _ | k
  · have hk := congrArg (coeff 1) h
    simp only [map_sub, map_add, coeff_C_mul, coeff_derivative, map_zero] at hk
    rw [coeff_X_pow_mul', if_neg (by norm_num), show (1 : ℕ) = 0 + 1 from rfl,
      coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative,
      coeff_derivative] at hk
    push_cast at hk ⊢
    linear_combination hk
  · have hk := congrArg (coeff (k + 2)) h
    simp only [map_sub, map_add, coeff_C_mul, map_zero] at hk
    rw [coeff_X_pow_mul, show k + 2 = (k + 1) + 1 from rfl, coeff_succ_X_mul,
      coeff_succ_X_mul] at hk
    simp only [coeff_derivative] at hk
    push_cast at hk ⊢
    linear_combination hk

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a308726.main := by
  intro T W G hT hT0 hW hW0 hG _hG0 n hn
  set D := PowerSeries.derivative ℚ with hD
  have hode := W_ode T W hT hT0 hW hW0
  rw [← hD] at hode
  -- the inverse of T
  have hTc : constantCoeff T ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hT0]
    norm_num
  set U := T⁻¹ with hU
  have hTU : T * U = 1 := PowerSeries.mul_inv_cancel T hTc
  have hDT : 2 * (T * D T) = 2 * (-2) := by
    have h := congrArg D hT
    rw [pow_two, D_mul, map_sub, Derivation.map_one_eq_zero,
      ← map_ofNat (C (R := ℚ)) 4, D_mul, D_C, derivative_X] at h
    rw [map_ofNat] at h
    linear_combination h
  have e2 : T * D T = -2 := cancel_two hDT
  have hDTU : T * D U + U * D T = 0 := by
    have h := congrArg D hTU
    rw [D_mul, Derivation.map_one_eq_zero] at h
    exact h
  have hUode : D U - C 4 * (X * D U) = C 2 * U := by
    simp only [map_ofNat]
    linear_combination T * hDTU - U * e2 - D U * hT
  have h2XG : C 2 * (X * G) = C 2 + C 2 * (X * U) - U - W := by
    simp only [map_ofNat]
    linear_combination U * hG - (2 * X * G - 2 + W) * hTU
  have hW2 : C 64 * (X ^ 2 * D (D W)) - C 28 * (X * D (D W)) + C 3 * D (D W)
      + C 64 * (X * D W) - C 14 * D W - C 4 * W = 0 := by
    simp only [map_ofNat]
    linear_combination hode
  have ru := U_rec U hUode
  have rw' := W_rec W hW2
  have rg : ∀ k : ℕ, coeff k G = (2 * coeff k U - coeff (k + 1) U - coeff (k + 1) W) / 2 := by
    intro k
    have hk := congrArg (coeff (k + 1)) h2XG
    simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_C] at hk
    rw [if_neg (by omega)] at hk
    linear_combination hk / 2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  rw [rg (m + 5), rg (m + 4), rg (m + 3), rg (m + 2), rg (m + 1), rg m]
  have W6 : coeff (m + 6) W = (14 * (((m : ℚ) + 3) + 2) * (2 * ((m : ℚ) + 3) + 3) * coeff (m + 5) W
      - (64 * (((m : ℚ) + 3) + 1) ^ 2 - 4) * coeff (m + 4) W) / (3 * (((m : ℚ) + 3) + 2) * (((m : ℚ) + 3) + 3)) := by
    have h := rw' (m + 3)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have W5 : coeff (m + 5) W = (14 * (((m : ℚ) + 2) + 2) * (2 * ((m : ℚ) + 2) + 3) * coeff (m + 4) W
      - (64 * (((m : ℚ) + 2) + 1) ^ 2 - 4) * coeff (m + 3) W) / (3 * (((m : ℚ) + 2) + 2) * (((m : ℚ) + 2) + 3)) := by
    have h := rw' (m + 2)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have W4 : coeff (m + 4) W = (14 * (((m : ℚ) + 1) + 2) * (2 * ((m : ℚ) + 1) + 3) * coeff (m + 3) W
      - (64 * (((m : ℚ) + 1) + 1) ^ 2 - 4) * coeff (m + 2) W) / (3 * (((m : ℚ) + 1) + 2) * (((m : ℚ) + 1) + 3)) := by
    have h := rw' (m + 1)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have W3 : coeff (m + 3) W = (14 * ((m : ℚ) + 2) * (2 * (m : ℚ) + 3) * coeff (m + 2) W
      - (64 * ((m : ℚ) + 1) ^ 2 - 4) * coeff (m + 1) W) / (3 * ((m : ℚ) + 2) * ((m : ℚ) + 3)) := by
    have h := rw' (m + 0)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have U6 : coeff (m + 6) U = (4 * ((m : ℚ) + 5) + 2) * coeff (m + 5) U / (((m : ℚ) + 5) + 1) := by
    have h := ru (m + 5)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have U5 : coeff (m + 5) U = (4 * ((m : ℚ) + 4) + 2) * coeff (m + 4) U / (((m : ℚ) + 4) + 1) := by
    have h := ru (m + 4)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have U4 : coeff (m + 4) U = (4 * ((m : ℚ) + 3) + 2) * coeff (m + 3) U / (((m : ℚ) + 3) + 1) := by
    have h := ru (m + 3)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have U3 : coeff (m + 3) U = (4 * ((m : ℚ) + 2) + 2) * coeff (m + 2) U / (((m : ℚ) + 2) + 1) := by
    have h := ru (m + 2)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have U2 : coeff (m + 2) U = (4 * ((m : ℚ) + 1) + 2) * coeff (m + 1) U / (((m : ℚ) + 1) + 1) := by
    have h := ru (m + 1)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  have U1 : coeff (m + 1) U = (4 * (m : ℚ) + 2) * coeff (m) U / ((m : ℚ) + 1) := by
    have h := ru (m)
    push_cast at h
    rw [eq_div_iff (by positivity)]
    linear_combination h
  rw [W6, W5, W4, W3, U6, U5, U4, U3, U2, U1]
  push_cast
  field_simp
  ring
