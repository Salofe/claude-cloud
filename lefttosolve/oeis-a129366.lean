import OMAStatements.S_oeis_a129366
import Mathlib

/-!
Disproof of the stated recurrence for A129366 (with `a(n) = Sum_{k=0..floor(n/2)} C(n-k)`).

At `n = 6` the values are `a 0, ..., a 6 = 1, 1, 3, 7, 21, 61, 193`, and the coefficients of the
stated relation are `3210, -12690, -4572, 28572, -4440, 17760, -27840`, so the left side equals
`-73968`, not `0`. The Catalan numbers are evaluated through `catalan n = centralBinom n / (n + 1)`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a129366

theorem cat_val (n : ℕ) : catalan n = (2 * n).choose n / (n + 1) := by
  rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]

theorem a0 : a 0 = 1 := by
  simp [a, cat_val]

theorem a1 : a 1 = 1 := by
  simp [a, cat_val]

theorem a2 : a 2 = 3 := by
  simp [a, Finset.sum_range_succ, cat_val, Nat.choose]
  norm_num

theorem a3 : a 3 = 7 := by
  simp [a, Finset.sum_range_succ, cat_val, Nat.choose]
  norm_num

theorem a4 : a 4 = 21 := by
  simp [a, Finset.sum_range_succ, cat_val, Nat.choose]
  norm_num

theorem a5 : a 5 = 61 := by
  simp [a, Finset.sum_range_succ, cat_val, Nat.choose]
  norm_num

theorem a6 : a 6 = 193 := by
  simp [a, Finset.sum_range_succ, cat_val, Nat.choose]
  norm_num

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a129366.main) := by
  intro h
  have h6 := h 6 le_rfl
  norm_num [OMA.Helpers.a0, OMA.Helpers.a1, OMA.Helpers.a2, OMA.Helpers.a3, OMA.Helpers.a4,
    OMA.Helpers.a5, OMA.Helpers.a6] at h6
