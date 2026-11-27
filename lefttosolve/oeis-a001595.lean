import OMAStatements.S_oeis_a001595
import Mathlib

-- Problem: A001595: a(n) = a(n-1) + a(n-2) + 1, with a(0) = a(1) = 1.
-- Upstream: formal-conjectures statements/oeis-a001595.lean:0 (declaration OMA.S_oeis_a001595.main)
-- Credit: @Salofe (the owner of the agent is credited as the solver)

namespace OMA.Helpers

open OMA.S_oeis_a001595 PowerSeries

theorem a001595_gf :
    PowerSeries.mk a * (1 - 2 * (X : PowerSeries ℤ) + X ^ 3) = 1 - X + X ^ 2 := by
  have h2 : (2 : PowerSeries ℤ) = C (2 : ℤ) := by simp
  ext n
  rw [mul_add, mul_sub, mul_one, h2, mul_left_comm]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_one, coeff_X,
    coeff_X_pow]
  match n with
  | 0 => simp [a]
  | 1 => simp [a, coeff_succ_mul_X]
  | 2 => simp [a, coeff_succ_mul_X]
  | n + 3 =>
    have e1 : a (n + 3) = a (n + 2) + a (n + 1) + 1 := rfl
    have e2 : a (n + 2) = a (n + 1) + a n + 1 := rfl
    rw [show n + 3 = (n + 2) + 1 from rfl, coeff_succ_mul_X, coeff_mk]
    simp only [show 3 ≤ n + 2 + 1 by omega, if_true, show n + 2 + 1 - 3 = n by omega,
      show n + 2 + 1 ≠ 0 by omega, show n + 2 + 1 ≠ 1 by omega, show n + 2 + 1 ≠ 2 by omega,
      if_false]
    rw [show n + 2 + 1 = n + 3 from rfl, e1, e2]
    ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a001595.main := by
  refine ⟨a001595_gf, ?_⟩
  have h : ((1 - (PowerSeries.X : PowerSeries ℤ) - PowerSeries.X ^ 2) * (1 - PowerSeries.X)) =
      1 - 2 * (PowerSeries.X : PowerSeries ℤ) + PowerSeries.X ^ 3 := by ring
  rw [h, a001595_gf]
  ring
