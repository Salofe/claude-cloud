import OMAStatements.S_oeis_a267524
import Mathlib

/-!
Proof of the two conjectures of OEIS A267524 (middle column of Rule 139 from a single ON cell).

Rule 139 sends a neighbourhood to ON exactly for 000, 001, 011 and 111. By induction, stage n + 1
is ON everywhere except at the two cells -n and 1 - n. Hence the middle cells are 1, 0, 0 and then
1 forever, a(n + 1) = 10 a(n) + c(n + 1), and both the recurrence and the generating function
follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a267524 PowerSeries

/-- Rule 139 in closed form: the next state is ON exactly for 000, 001, 011 and 111. -/
theorem a267524_rule (l c r : Bool) :
    Nat.testBit 139 (4 * l.toNat + 2 * c.toNat + r.toNat) = ((!l && !c) || (c && r)) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem a267524_rule_decide (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    Nat.testBit 139 (4 * (decide P).toNat + 2 * (decide Q).toNat + (decide R).toNat)
      = decide ((¬ P ∧ ¬ Q) ∨ (Q ∧ R)) := by
  rw [a267524_rule]
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

/-- Stage n + 1: every cell is ON except the two cells -n and 1 - n. -/
theorem a267524_state_succ (n : ℕ) (x : ℤ) :
    state 139 (n + 1) x = decide (x ≠ -(n : ℤ) ∧ x ≠ 1 - (n : ℤ)) := by
  induction n generalizing x with
  | zero =>
    show Nat.testBit 139 (4 * (decide (x - 1 = 0)).toNat + 2 * (decide (x = 0)).toNat
      + (decide (x + 1 = 0)).toNat) = _
    rw [a267524_rule_decide, decide_eq_decide]
    push_cast
    omega
  | succ k ih =>
    show Nat.testBit 139 (4 * (state 139 (k + 1) (x - 1)).toNat + 2 * (state 139 (k + 1) x).toNat
      + (state 139 (k + 1) (x + 1)).toNat) = _
    rw [ih, ih, ih, a267524_rule_decide, decide_eq_decide]
    push_cast
    omega

theorem a267524_c_zero : c 0 = 1 := rfl

theorem a267524_c_one : c 1 = 0 := by
  unfold c
  rw [a267524_state_succ]
  decide

theorem a267524_c_two : c 2 = 0 := by
  unfold c
  rw [a267524_state_succ]
  decide

theorem a267524_c_add_three (n : ℕ) : c (n + 3) = 1 := by
  unfold c
  rw [a267524_state_succ, decide_eq_true (by push_cast; omega)]
  rfl

theorem a267524_a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

theorem a267524_a_zero : a 0 = 1 := rfl

theorem a267524_a_one : a 1 = 10 := by
  rw [a267524_a_succ, a267524_a_zero, a267524_c_one]

theorem a267524_a_two : a 2 = 100 := by
  rw [a267524_a_succ, a267524_a_one, a267524_c_two]

theorem a267524_a_add_three (n : ℕ) : a (n + 3) = 10 * a (n + 2) + 1 := by
  rw [a267524_a_succ, a267524_c_add_three]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a267524.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h4 := OMA.Helpers.a267524_a_add_three (m + 1)
    have h3 := OMA.Helpers.a267524_a_add_three m
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    rw [show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega] at h4
    rw [h4, h3]
    push_cast
    ring
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    have e1 : OMA.S_oeis_a267524.A * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X))
        = OMA.S_oeis_a267524.A - PowerSeries.C (11 : ℚ) * (OMA.S_oeis_a267524.A * PowerSeries.X ^ 1)
          + PowerSeries.C (10 : ℚ) * (OMA.S_oeis_a267524.A * PowerSeries.X ^ 2) := by
      simp only [map_ofNat]
      ring
    have e2 : (1 - PowerSeries.X + PowerSeries.X ^ 3 : PowerSeries ℚ)
        = PowerSeries.X ^ 0 - PowerSeries.X ^ 1 + PowerSeries.X ^ 3 := by ring
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      OMA.S_oeis_a267524.A, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases k with _ | _ | _ | _ | k
    · simp [OMA.Helpers.a267524_a_zero]
    · simp [OMA.Helpers.a267524_a_zero, OMA.Helpers.a267524_a_one]
      norm_num
    · simp [OMA.Helpers.a267524_a_zero, OMA.Helpers.a267524_a_one, OMA.Helpers.a267524_a_two]
      norm_num
    · simp [OMA.Helpers.a267524_a_one, OMA.Helpers.a267524_a_two,
        OMA.Helpers.a267524_a_add_three 0]
      norm_num
    · have h4 := OMA.Helpers.a267524_a_add_three (k + 1)
      have h3 := OMA.Helpers.a267524_a_add_three k
      simp only [show k + 1 + 3 = k + 4 by omega, show k + 1 + 2 = k + 3 by omega] at h4
      simp only [show k + 1 + 1 + 1 + 1 = k + 4 by omega]
      simp only [show ¬ (k + 4 = 0) by omega, show ¬ (k + 4 = 1) by omega,
        show ¬ (k + 4 = 3) by omega, if_true, if_false, show 1 ≤ k + 4 by omega,
        show 2 ≤ k + 4 by omega, show k + 4 - 1 = k + 3 by omega,
        show k + 4 - 2 = k + 2 by omega, h4, h3]
      push_cast
      ring
