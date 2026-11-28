import OMAStatements.S_oeis_a273789

/-!
Proof of the three conjectures of OEIS A273789 (Rule 931, 5-celled von Neumann neighbourhood),
including the cross-reference to A273743 (Rule 901, same construction).

A cell with own value c and k ON orthogonal neighbours becomes bit c + 2k of the code.
931 = 1110100011 in binary (bits 0, 1, 5, 7, 8, 9 set) and 901 = 1110000101 in binary
(bits 0, 2, 7, 8, 9 set).
* Both codes have bit 0 set: at stage 1 every cell outside the 3 x 3 square around the origin
  (an OFF cell with no ON neighbour at stage 0) is ON.
* Both codes have bit 9 set: an ON cell with four ON neighbours stays ON.
* For both codes the plane is entirely ON at stage 2: outside the 5 x 5 square around the
  origin a cell and its four neighbours are all ON at stage 1, and the 25 cells inside the
  square are checked by evaluation.
* Hence from stage 2 on the whole plane is ON, so a(n) = A273743(n) = (2n+1)^2 for n >= 2,
  while a(0) = 1 and a(1) = 5. The recurrence and the generating function follow by computing
  with these values.
-/

namespace OMA.Helpers

open OMA.S_oeis_a273789

/-- Outside the 3 x 3 square around the origin, a cell at stage 1 is the image of an OFF cell
with no ON neighbour. -/
theorem a273789_state_one_far (code : ℕ) (x y : ℤ)
    (h : ¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1)) : state code 1 x y = rule code false 0 := by
  have e0 : ¬ (x = 0 ∧ y = 0) := by omega
  have e1 : ¬ (x + 1 = 0 ∧ y = 0) := by omega
  have e2 : ¬ (x - 1 = 0 ∧ y = 0) := by omega
  have e3 : ¬ (x = 0 ∧ y + 1 = 0) := by omega
  have e4 : ¬ (x = 0 ∧ y - 1 = 0) := by omega
  show rule code (initial x y) (neighbors initial x y) = rule code false 0
  simp only [neighbors, initial, e0, e1, e2, e3, e4, decide_false]
  rfl

/-- The plane is entirely ON at stage 2 as soon as bits 0 and 9 of the code are set and the 25
cells of the 5 x 5 square around the origin are ON at stage 2. -/
theorem a273789_state_two (code : ℕ) (h0 : rule code false 0 = true)
    (h9 : rule code true 4 = true)
    (hin : ∀ x y : ℤ, -2 ≤ x → x ≤ 2 → -2 ≤ y → y ≤ 2 → state code 2 x y = true)
    (x y : ℤ) : state code 2 x y = true := by
  by_cases hb : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · exact hin x y hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  · show rule code (state code 1 x y) (neighbors (state code 1) x y) = true
    simp only [neighbors, a273789_state_one_far code x y (by omega),
      a273789_state_one_far code (x + 1) y (by omega),
      a273789_state_one_far code (x - 1) y (by omega),
      a273789_state_one_far code x (y + 1) (by omega),
      a273789_state_one_far code x (y - 1) (by omega), h0]
    exact h9

/-- Once the plane is entirely ON at stage 2, it stays ON when bit 9 of the code is set. -/
theorem a273789_all_on (code : ℕ) (h9 : rule code true 4 = true)
    (h2 : ∀ x y : ℤ, state code 2 x y = true) :
    ∀ n : ℕ, 2 ≤ n → ∀ x y : ℤ, state code n x y = true := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h2
  | succ m _ ih =>
    intro x y
    show rule code (state code m x y) (neighbors (state code m) x y) = true
    simp only [neighbors, ih]
    exact h9

/-- When the plane is entirely ON at stage n, the (2n+1) x (2n+1) square has (2n+1)^2 ON
cells. -/
theorem a273789_onCount_of_all_on (code n : ℕ) (h : ∀ x y : ℤ, state code n x y = true) :
    onCount code n = (1 + 2 * n) ^ 2 := by
  unfold onCount
  rw [Finset.filter_true_of_mem (fun p _ => h _ _), Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  ring

/-- Rule 931: the 25 cells of the 5 x 5 square around the origin are ON at stage 2. -/
theorem a273789_box_931 (x y : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) (h3 : -2 ≤ y) (h4 : y ≤ 2) :
    state 931 2 x y = true := by
  interval_cases x <;> interval_cases y <;> decide

/-- Rule 901: the 25 cells of the 5 x 5 square around the origin are ON at stage 2. -/
theorem a273789_box_901 (x y : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) (h3 : -2 ≤ y) (h4 : y ≤ 2) :
    state 901 2 x y = true := by
  interval_cases x <;> interval_cases y <;> decide

/-- The closed form of A273789 from stage 2 on. -/
theorem a273789_closed (n : ℕ) (hn : 2 ≤ n) : a n = (1 + 2 * n) ^ 2 :=
  a273789_onCount_of_all_on 931 n
    (a273789_all_on 931 (by decide)
      (a273789_state_two 931 (by decide) (by decide) a273789_box_931) n hn)

/-- The closed form of A273743 from stage 2 on. -/
theorem a273789_closed_901 (n : ℕ) (hn : 2 ≤ n) : A273743 n = (1 + 2 * n) ^ 2 :=
  a273789_onCount_of_all_on 901 n
    (a273789_all_on 901 (by decide)
      (a273789_state_two 901 (by decide) (by decide) a273789_box_901) n hn)

theorem a273789_zero : a 0 = 1 := by decide

theorem a273789_one : a 1 = 5 := by decide

theorem a273789_two : a 2 = 25 := a273789_closed 2 (by norm_num)

theorem a273789_three : a 3 = 49 := a273789_closed 3 (by norm_num)

theorem a273789_four : a 4 = 81 := a273789_closed 4 (by norm_num)

/-- The recurrence for n > 4: a third difference of a quadratic vanishes. -/
theorem a273789_rec (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega,
    a273789_closed (m + 5) (by omega), a273789_closed (m + 4) (by omega),
    a273789_closed (m + 3) (by omega), a273789_closed (m + 2) (by omega)]
  push_cast
  ring

/-- The generating function, as a product identity in ℤ⟦X⟧, checked coefficient by
coefficient: coefficients 0..4 from a(0..4) = 1, 5, 25, 49, 81, and coefficient k >= 5 from
the closed form. -/
theorem a273789_gf :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      1 + 2 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3
        + 4 * PowerSeries.X ^ 4 := by
  set p : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ)) with hp
  have e1 : p * (1 - PowerSeries.X) ^ 3 =
      p - PowerSeries.C (3 : ℤ) * (p * PowerSeries.X ^ 1)
        + PowerSeries.C (3 : ℤ) * (p * PowerSeries.X ^ 2) - p * PowerSeries.X ^ 3 := by
    rw [map_ofNat]
    ring
  have e2 : (1 + 2 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3
        + 4 * PowerSeries.X ^ 4 : PowerSeries ℤ) =
      1 + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 1
        + PowerSeries.C (13 : ℤ) * PowerSeries.X ^ 2
        - PowerSeries.C (12 : ℤ) * PowerSeries.X ^ 3
        + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 4 := by
    simp only [map_ofNat, pow_one]
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;>
      simp [a273789_zero, a273789_one, a273789_two, a273789_three, a273789_four]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    rw [if_pos (show 1 ≤ j + 5 by omega), if_pos (show 2 ≤ j + 5 by omega),
      if_pos (show 3 ≤ j + 5 by omega), if_neg (show ¬ (j + 5 = 0) by omega),
      if_neg (show ¬ (j + 5 = 1) by omega), if_neg (show ¬ (j + 5 = 2) by omega),
      if_neg (show ¬ (j + 5 = 3) by omega), if_neg (show ¬ (j + 5 = 4) by omega),
      show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
      show j + 5 - 3 = j + 2 by omega,
      a273789_closed (j + 5) (by omega), a273789_closed (j + 4) (by omega),
      a273789_closed (j + 3) (by omega), a273789_closed (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a273789.main := by
  refine ⟨fun n hn => ⟨OMA.Helpers.a273789_closed n hn,
    (OMA.Helpers.a273789_closed_901 n hn).symm, ?_⟩,
    fun n hn => OMA.Helpers.a273789_rec n hn, OMA.Helpers.a273789_gf⟩
  rw [OMA.Helpers.a273789_closed_901 n hn]
  unfold OMA.S_oeis_a273789.A016754
  ring
