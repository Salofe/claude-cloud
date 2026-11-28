import OMAStatements.S_oeis_a273743

/-!
Proof of the three conjectures of OEIS A273743 (Rule 901, 5-celled von Neumann neighbourhood).

Rule 901 = 1110000101 in binary: a cell with own value c and k ON orthogonal neighbours becomes
ON exactly when c + 2k is one of 0, 2, 7, 8, 9.
* Stage 1: the origin (ON, no ON neighbour) dies, its four neighbours (OFF, one ON neighbour)
  are born, and every other cell (OFF, no ON neighbour) is born: all cells but the origin are ON.
* Stage 2: the origin (OFF, four ON neighbours) is born, its four neighbours (ON, three ON
  neighbours) survive, and every other cell (ON, four ON neighbours) survives: the plane is ON.
* An ON cell with four ON neighbours stays ON, so the plane stays ON from stage 2 on.
Hence a(n) = (2n+1)^2 for n >= 2, while a(0) = 1 and a(1) = 8. The recurrence and the
generating function follow by computing with these values.
-/

namespace OMA.Helpers

open OMA.S_oeis_a273743

/-- Stage 1: every cell is ON except the origin. -/
theorem a273743_state_one (x y : ℤ) : state 1 x y = !decide (x = 0 ∧ y = 0) := by
  show rule (initial x y) (neighbors initial x y) = _
  unfold neighbors initial bit
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    decide
  · rw [decide_eq_false h]
    simp only [decide_eq_true_eq]
    split_ifs <;> first | omega | decide

/-- Stage 2: every cell is ON. -/
theorem a273743_state_two (x y : ℤ) : state 2 x y = true := by
  show rule (state 1 x y) (neighbors (state 1) x y) = true
  unfold neighbors bit
  simp only [a273743_state_one]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    decide
  · rw [decide_eq_false h]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    split_ifs <;> first | omega | decide

/-- From stage 2 on, every cell is ON (an ON cell with four ON neighbours stays ON). -/
theorem a273743_state_add_two (m : ℕ) : ∀ x y : ℤ, state (m + 2) x y = true := by
  induction m with
  | zero => exact a273743_state_two
  | succ m ih =>
    intro x y
    show rule (state (m + 2) x y) (neighbors (state (m + 2)) x y) = true
    simp only [neighbors, ih]
    decide

/-- The closed form: from stage 2 on, the whole (2n+1) x (2n+1) square is ON. -/
theorem a273743_closed (n : ℕ) (hn : 2 ≤ n) : a n = (1 + 2 * n) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  simp only [a273743_state_add_two, bit, if_true, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]
  ring

theorem a273743_zero : a 0 = 1 := by decide

theorem a273743_one : a 1 = 8 := by decide

theorem a273743_two : a 2 = 25 := a273743_closed 2 (by norm_num)

theorem a273743_three : a 3 = 49 := a273743_closed 3 (by norm_num)

theorem a273743_four : a 4 = 81 := a273743_closed 4 (by norm_num)

/-- The recurrence for n > 4: a third difference of a quadratic vanishes. -/
theorem a273743_rec (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 3 * (a (n-1) : ℤ) - 3 * (a (n-2) : ℤ) + (a (n-3) : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  rw [a273743_closed (m + 5) (by omega), a273743_closed (m + 4) (by omega),
    a273743_closed (m + 3) (by omega), a273743_closed (m + 2) (by omega)]
  push_cast
  ring

/-- The generating function, as a product identity in ℤ⟦X⟧, checked coefficient by
coefficient: coefficients 0..4 from a(0..4) = 1, 8, 25, 49, 81, and coefficient k >= 5 from
the closed form. -/
theorem a273743_gf :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      1 + 5 * PowerSeries.X + 4 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3
        + PowerSeries.X ^ 4 := by
  set p : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ)) with hp
  have e1 : p * (1 - PowerSeries.X) ^ 3 =
      p - PowerSeries.C (3 : ℤ) * (p * PowerSeries.X ^ 1)
        + PowerSeries.C (3 : ℤ) * (p * PowerSeries.X ^ 2) - p * PowerSeries.X ^ 3 := by
    rw [map_ofNat]
    ring
  have e2 : (1 + 5 * PowerSeries.X + 4 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3
        + PowerSeries.X ^ 4 : PowerSeries ℤ) =
      1 + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2
        - PowerSeries.C (3 : ℤ) * PowerSeries.X ^ 3
        + PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 4 := by
    simp only [map_ofNat, map_one, pow_one, one_mul]
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;>
      simp [a273743_zero, a273743_one, a273743_two, a273743_three, a273743_four]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    rw [if_pos (show 1 ≤ j + 5 by omega), if_pos (show 2 ≤ j + 5 by omega),
      if_pos (show 3 ≤ j + 5 by omega), if_neg (show ¬ (j + 5 = 0) by omega),
      if_neg (show ¬ (j + 5 = 1) by omega), if_neg (show ¬ (j + 5 = 2) by omega),
      if_neg (show ¬ (j + 5 = 3) by omega), if_neg (show ¬ (j + 5 = 4) by omega)]
    rw [show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
      show j + 5 - 3 = j + 2 by omega]
    rw [a273743_closed (j + 5) (by omega), a273743_closed (j + 4) (by omega),
      a273743_closed (j + 3) (by omega), a273743_closed (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a273743.main := by
  refine ⟨fun n hn => ?_, fun n hn => OMA.Helpers.a273743_rec n hn, OMA.Helpers.a273743_gf⟩
  have h := OMA.Helpers.a273743_closed n (by omega)
  refine ⟨h, ?_⟩
  rw [h]
  unfold OMA.S_oeis_a273743.A016754
  ring
