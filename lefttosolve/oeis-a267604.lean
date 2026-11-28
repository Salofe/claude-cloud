import OMAStatements.S_oeis_a267604

/-!
Proof of the conjectures of OEIS A267604 (Rule 175 from a single ON cell).

Rule 175 sends a neighbourhood to OFF exactly when the left cell is ON and the right cell is OFF.
By induction, row n + 1 is ON everywhere except at the single cell 1 - n. So the middle column
reads 1, 1, 0, 1, 1, 1, ..., whence a(n + 1) = 2 a(n) + [row (n + 1) 0], a(0) = 1, a(1) = 3 and
a(m + 2) = 7 * 2^m - 1. All four conjectures follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a267604

theorem a267604_rule_eq (l c r : Bool) : rule l c r = (!l || r) := by
  cases l <;> cases c <;> cases r <;> decide

theorem a267604_row_succ (n : ℕ) (i : ℤ) : row (n + 1) i = decide (i ≠ 1 - (n : ℤ)) := by
  induction n generalizing i with
  | zero =>
    show rule (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
    rw [a267604_rule_eq]
    by_cases h1 : i = 1
    · subst h1; decide
    · have e1 : i - 1 ≠ 0 := by omega
      simp [e1, h1]
  | succ k ih =>
    show rule (row (k + 1) (i - 1)) (row (k + 1) i) (row (k + 1) (i + 1)) = _
    rw [a267604_rule_eq, ih, ih, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    push_cast
    constructor <;> intro h <;> omega

theorem a267604_a_succ (n : ℕ) : a (n + 1) = 2 * a n + (if row (n + 1) 0 then 1 else 0) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have e : n + 1 - t = (n - t) + 1 := by omega
  rw [e, pow_succ]
  split_ifs <;> ring

theorem a267604_a_zero : a 0 = 1 := by decide

theorem a267604_a_one : a 1 = 3 := by
  rw [a267604_a_succ, a267604_a_zero, a267604_row_succ]; decide

theorem a267604_a_add_two (m : ℕ) : a (m + 2) = 7 * 2 ^ m - 1 := by
  induction m with
  | zero =>
    rw [a267604_a_succ, a267604_a_one, a267604_row_succ]; decide
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, a267604_a_succ, ih, a267604_row_succ]
    have h : (0 : ℤ) ≠ 1 - ((k + 2 : ℕ) : ℤ) := by push_cast; omega
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [h, ne_eq, not_false_eq_true, decide_true, if_true, pow_succ]
    omega

theorem a267604_aZ (m : ℕ) : (a (m + 2) : ℤ) = 7 * 2 ^ m - 1 := by
  rw [a267604_a_add_two]
  have hp : 1 ≤ 7 * 2 ^ m := by have := @Nat.one_le_two_pow m; omega
  push_cast [hp]
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a267604.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = (m + 1) + 2 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 = (m + 2) + 2 by omega, OMA.Helpers.a267604_aZ, OMA.Helpers.a267604_aZ,
      OMA.Helpers.a267604_aZ]
    ring
  · set f : PowerSeries ℤ := PowerSeries.mk (fun n => (OMA.S_oeis_a267604.a n : ℤ)) with hf
    have e1 : f * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X))
        = f - f * PowerSeries.X ^ 1 - f * PowerSeries.X ^ 1 - f * PowerSeries.X ^ 1
          + f * PowerSeries.X ^ 2 + f * PowerSeries.X ^ 2 := by ring
    have e2 : (1 - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℤ)
        = PowerSeries.X ^ 0 - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by ring
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', hf, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases k with _ | _ | _ | _ | k
    · simp [OMA.Helpers.a267604_a_zero]
    · simp [OMA.Helpers.a267604_a_zero, OMA.Helpers.a267604_a_one]
    · simp [OMA.Helpers.a267604_a_zero, OMA.Helpers.a267604_a_one,
        OMA.Helpers.a267604_a_add_two 0]
    · simp [OMA.Helpers.a267604_a_one, OMA.Helpers.a267604_a_add_two 0,
        OMA.Helpers.a267604_a_add_two 1]
    · have h4 := OMA.Helpers.a267604_aZ (k + 2)
      have h3 := OMA.Helpers.a267604_aZ (k + 1)
      have h2 := OMA.Helpers.a267604_aZ k
      simp only [show k + 1 + 1 + 1 + 1 = k + 2 + 2 by ring, show 1 ≤ k + 2 + 2 by omega,
        show 2 ≤ k + 2 + 2 by omega, if_true, show k + 2 + 2 - 1 = k + 1 + 2 by omega,
        show k + 2 + 2 - 2 = k + 2 by omega, h4, h3, h2]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [OMA.Helpers.a267604_a_add_two]
    simp [OMA.S_oeis_a267604.A086224]
  · intro n
    rcases n with _ | _ | m
    · rw [OMA.Helpers.a267604_a_zero]
      norm_num [Int.ceil_eq_iff]
    · rw [OMA.Helpers.a267604_a_one]
      norm_num [Int.ceil_eq_iff]
    · rw [OMA.Helpers.a267604_aZ]
      have e : (7 / 4 : ℚ) * 2 ^ (m + 1 + 1) - 1 = (((7 * 2 ^ m - 1 : ℤ)) : ℚ) := by
        push_cast; ring
      rw [e, Int.ceil_intCast]
