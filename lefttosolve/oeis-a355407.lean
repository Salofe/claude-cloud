import OMAStatements.S_oeis_a355407
import Mathlib

open PowerSeries

namespace OMA.Helpers

/-- `1 - X + X^2 - ...` times `1 + X` is `1`. -/
theorem a355407_geomAlt : (mk fun n => (-1 : ℚ) ^ n) * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_one]
    simp [pow_succ]

/-- `(1 - X) (1 - 2X) * Sum (2^(n+1) - 1) X^n = 1`. -/
theorem a355407_hH : (1 - X) * (1 - 2 * X) * (mk fun n => (2 : ℚ) ^ (n + 1) - 1) = 1 := by
  have e : ((1 : ℚ⟦X⟧) - X) * (1 - 2 * X) = 1 - C (3 : ℚ) * X + C (2 : ℚ) * X ^ 2 := by
    simp only [map_ofNat]; ring
  rw [e]
  ext n
  rw [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_one]
  rw [show (X : ℚ⟦X⟧) = X ^ 1 from (pow_one _).symm, coeff_X_pow_mul']
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · simp only [coeff_mk, show 1 ≤ n + 2 from by omega, show 2 ≤ n + 2 from by omega, if_true,
      show n + 2 - 1 = n + 1 from by omega, show n + 2 - 2 = n from by omega]
    simp only [show n + 2 ≠ 0 from by omega, if_false]
    ring

/-- The formal logarithm of `(1 - X) / (1 - 2X)` is `Sum_{n >= 1} (2^n - 1)/n X^n`. -/
theorem a355407_logL : logOf ((1 - X) * (1 - 2 * X)⁻¹ : ℚ⟦X⟧) =
    mk fun n => if n = 0 then 0 else ((2 : ℚ) ^ n - 1) / n := by
  have hw : (1 - 2 * X : ℚ⟦X⟧)⁻¹ * (1 - 2 * X) = 1 := PowerSeries.inv_mul_cancel _ (by simp)
  set w := (1 - 2 * X : ℚ⟦X⟧)⁻¹ with hwdef
  have hcw : constantCoeff w = 1 := by simp [w, constantCoeff_inv]
  have hc : constantCoeff ((1 - X) * w - 1) = 0 := by simp [hcw]
  have hs : HasSubst ((1 - X) * w - 1) := HasSubst.of_constantCoeff_zero' hc
  apply derivative.ext
  · rw [logOf_eq, derivative_subst hs, deriv_log]
    have hS : (mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)).subst ((1 - X) * w - 1) *
        ((1 - X) * w) = 1 := by
      have h1 := congrArg (substAlgHom hs) a355407_geomAlt
      rw [map_mul, map_one, map_add, map_one, substAlgHom_X, coe_substAlgHom] at h1
      simpa using h1
    have hdG : d⁄dX ℚ (mk fun n => if n = 0 then 0 else ((2 : ℚ) ^ n - 1) / n) =
        mk fun n => (2 : ℚ) ^ (n + 1) - 1 := by
      ext n
      rw [coeff_derivative, coeff_mk, coeff_mk, if_neg (by omega)]
      push_cast
      field_simp
    have hdf : d⁄dX ℚ ((1 - X) * w - 1) = -w + 2 * (1 - X) * w ^ 2 := by
      have h2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by
        rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm]; exact derivative_C
      simp [w, derivative_inv', h2]
      ring
    rw [hdG, hdf]
    set S := (mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)).subst ((1 - X) * w - 1)
    linear_combination S * ((w + (1 - X) * w * (mk fun n => (2 : ℚ) ^ (n + 1) - 1)) * hw -
      w ^ 2 * a355407_hH) + (mk fun n => (2 : ℚ) ^ (n + 1) - 1) * hS
  · rw [constantCoeff_logOf (by simp [hcw])]
    simp

/-- `((1 - X)^4)⁻¹ = Sum C(3 + n, 3) X^n`. -/
theorem a355407_inv4 : (((1 : ℚ⟦X⟧) - X) ^ 4)⁻¹ = mk fun n => ((Nat.choose (3 + n) 3 : ℕ) : ℚ) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  have h := (invOneSubPow ℚ 4).val_inv
  rw [invOneSubPow_inv_eq_one_sub_pow, invOneSubPow_val_succ_eq_mk_add_choose] at h
  exact h

/-- The coefficients of the e.g.f. as a finite sum. -/
theorem a355407_coeff (n : ℕ) : coeff n OMA.S_oeis_a355407.egf =
    ∑ k ∈ Finset.range (n + 1), (if k = 0 then 0 else ((2 : ℚ) ^ k - 1) / k) *
      ((Nat.choose (3 + (n - k)) 3 : ℕ) : ℚ) := by
  rw [OMA.S_oeis_a355407.egf, a355407_logL, a355407_inv4, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (mk fun n =>
      if n = 0 then (0 : ℚ) else ((2 : ℚ) ^ n - 1) / n) *
      coeff j (mk fun n => ((Nat.choose (3 + n) 3 : ℕ) : ℚ)))]
  simp only [coeff_mk]

/-- The integer value of `a n`. -/
def a355407_z (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else
    ((n.factorial / k : ℕ) : ℤ) * (2 ^ k - 1) * ((Nat.choose (3 + (n - k)) 3 : ℕ) : ℤ)

theorem a355407_a_eq (n : ℕ) : OMA.S_oeis_a355407.a n = (a355407_z n : ℚ) := by
  rw [OMA.S_oeis_a355407.a, a355407_coeff, a355407_z, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Int.cast_mul, Int.cast_natCast, Int.cast_sub,
    Int.cast_pow, Int.cast_ofNat, Int.cast_one]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by simp at hk; omega
  by_cases h0 : k = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast h0
    rw [Nat.cast_div (Nat.dvd_factorial (by omega) hkn) hk0]
    field_simp

theorem a355407_dvd (p : ℕ) (hp : p.Prime) : (p : ℤ) ∣ a355407_z p - (-1) := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, a355407_z, Finset.sum_range_succ]
  have hrest : ∀ k ∈ Finset.range p, (((if k = 0 then 0 else
      ((p.factorial / k : ℕ) : ℤ) * (2 ^ k - 1) * ((Nat.choose (3 + (p - k)) 3 : ℕ) : ℤ)) : ℤ) :
        ZMod p) = 0 := by
    intro k hk
    have hkp : k < p := Finset.mem_range.mp hk
    by_cases h0 : k = 0
    · simp [h0]
    · simp only [h0, if_false]
      have hdiv : p ∣ p.factorial / k := by
        have hk1 : k ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
        rw [← Nat.mul_factorial_pred hp.ne_zero, Nat.mul_div_assoc _ hk1]
        exact dvd_mul_right _ _
      have hz : ((p.factorial / k : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
      simp only [Int.cast_mul, Int.cast_natCast, hz, zero_mul]
  rw [Int.cast_sub, Int.cast_add, Int.cast_sum, Finset.sum_eq_zero hrest, zero_add,
    if_neg hp.ne_zero, Nat.sub_self]
  have hfac : p.factorial / p = (p - 1).factorial := by
    rw [← Nat.mul_factorial_pred hp.ne_zero, Nat.mul_div_cancel_left _ hp.pos]
  rw [hfac]
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one,
    Int.cast_neg, ZMod.wilsons_lemma, ZMod.pow_card]
  norm_num

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a355407.main := by
  intro p hp
  exact ⟨OMA.Helpers.a355407_z p, OMA.Helpers.a355407_a_eq p, OMA.Helpers.a355407_dvd p hp⟩
