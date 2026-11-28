import OMAStatements.S_oeis_a267539

/-!
Proof of the conjectures of OEIS A267539 (Rule 143 from a single ON cell).

Rule 143 sends a neighbourhood to ON exactly when the left cell is OFF or both the centre and the
right cell are ON. Row 1 is ON except at the cell 1, and by induction row n + 2 is ON except at
the two cells -n and 1 - n. So the middle column reads 1, 1, 0, 0, 1, 1, 1, ..., whence
a(n + 1) = 2 a(n) + [row (n + 1) 0], a(0), a(1), a(2) = 1, 3, 6 and a(m + 3) = 13 * 2^m - 1.
The recurrence, the generating function and the link with A198274 follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a267539

theorem a267539_rule_eq (l c r : Bool) : rule l c r = (!l || (c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

theorem a267539_row_one (i : ℤ) : row 1 i = decide (i ≠ 1) := by
  show rule (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
  rw [a267539_rule_eq, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_false_iff_not,
    decide_eq_true_eq]
  constructor <;> intro h <;> omega

theorem a267539_row_add_two (n : ℕ) (i : ℤ) :
    row (n + 2) i = decide (i ≠ -(n : ℤ) ∧ i ≠ 1 - (n : ℤ)) := by
  induction n generalizing i with
  | zero =>
    show rule (row 1 (i - 1)) (row 1 i) (row 1 (i + 1)) = _
    rw [a267539_rule_eq, a267539_row_one, a267539_row_one, a267539_row_one, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_false_iff_not,
      decide_eq_true_eq]
    push_cast
    constructor <;> intro h <;> omega
  | succ k ih =>
    show rule (row (k + 2) (i - 1)) (row (k + 2) i) (row (k + 2) (i + 1)) = _
    rw [a267539_rule_eq, ih, ih, ih, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_false_iff_not,
      decide_eq_true_eq]
    push_cast
    constructor <;> intro h <;> omega

theorem a267539_a_succ (n : ℕ) : a (n + 1) = 2 * a n + (if row (n + 1) 0 then 1 else 0) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have e : n + 1 - t = (n - t) + 1 := by omega
  rw [e, pow_succ]
  split_ifs <;> ring

theorem a267539_a_zero : a 0 = 1 := by decide

theorem a267539_a_one : a 1 = 3 := by
  rw [a267539_a_succ, a267539_a_zero, a267539_row_one]; decide

theorem a267539_a_two : a 2 = 6 := by
  rw [a267539_a_succ, a267539_a_one, a267539_row_add_two]; decide

theorem a267539_a_add_three (m : ℕ) : a (m + 3) = 13 * 2 ^ m - 1 := by
  induction m with
  | zero =>
    rw [a267539_a_succ, a267539_a_two, a267539_row_add_two]; decide
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, a267539_a_succ, ih,
      show k + 3 + 1 = (k + 2) + 2 by ring, a267539_row_add_two]
    have h : (0 : ℤ) ≠ -((k + 2 : ℕ) : ℤ) ∧ (0 : ℤ) ≠ 1 - ((k + 2 : ℕ) : ℤ) := by
      push_cast; omega
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [if_pos (decide_eq_true h), pow_succ]
    omega

theorem a267539_aZ (m : ℕ) : (a (m + 3) : ℤ) = 13 * 2 ^ m - 1 := by
  rw [a267539_a_add_three]
  have hp : 1 ≤ 13 * 2 ^ m := by have := @Nat.one_le_two_pow m; omega
  push_cast [hp]
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a267539.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = (m + 1) + 3 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 = (m + 2) + 3 by omega, OMA.Helpers.a267539_aZ, OMA.Helpers.a267539_aZ,
      OMA.Helpers.a267539_aZ]
    ring
  · set f : PowerSeries ℤ := PowerSeries.mk (fun n => (OMA.S_oeis_a267539.a n : ℤ)) with hf
    have e1 : f * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X))
        = f - f * PowerSeries.X ^ 1 - f * PowerSeries.X ^ 1 - f * PowerSeries.X ^ 1
          + f * PowerSeries.X ^ 2 + f * PowerSeries.X ^ 2 := by ring
    have e2 : (1 - PowerSeries.X ^ 2 + PowerSeries.X ^ 4 : PowerSeries ℤ)
        = PowerSeries.X ^ 0 - PowerSeries.X ^ 2 + PowerSeries.X ^ 4 := by ring
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', hf, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases k with _ | _ | _ | _ | _ | k
    · simp [OMA.Helpers.a267539_a_zero]
    · simp [OMA.Helpers.a267539_a_zero, OMA.Helpers.a267539_a_one]
    · simp [OMA.Helpers.a267539_a_zero, OMA.Helpers.a267539_a_one, OMA.Helpers.a267539_a_two]
    · simp [OMA.Helpers.a267539_a_one, OMA.Helpers.a267539_a_two,
        OMA.Helpers.a267539_a_add_three 0]
    · simp [OMA.Helpers.a267539_a_two, OMA.Helpers.a267539_a_add_three 0,
        OMA.Helpers.a267539_a_add_three 1]
    · have h4 := OMA.Helpers.a267539_aZ (k + 2)
      have h3 := OMA.Helpers.a267539_aZ (k + 1)
      have h2 := OMA.Helpers.a267539_aZ k
      simp only [show k + 1 + 1 + 1 + 1 + 1 = k + 2 + 3 by ring, show 1 ≤ k + 2 + 3 by omega,
        show 2 ≤ k + 2 + 3 by omega, if_true, show k + 2 + 3 - 1 = k + 1 + 3 by omega,
        show k + 2 + 3 - 2 = k + 3 by omega, h4, h3, h2]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
  · refine ⟨OMA.Helpers.a267539_a_zero, OMA.Helpers.a267539_a_one, OMA.Helpers.a267539_a_two,
      fun n => ?_⟩
    rw [OMA.Helpers.a267539_a_add_three]
    rfl
