import OMAStatements.S_oeis_a273384

/-!
Proof of the three conjectures of OEIS A273384 (Rule 659 started from a single ON cell).

Rule 659 = 1010010011 in binary: the new value is bit c + 2k, where c is the cell and k the
number of ON orthogonal neighbours. Bits 0 and 9 are set, so the OFF background turns ON at
stage 1 and the all-ON plane is a fixed point. A direct look at the square of radius 3 shows
that stage 3 is ON everywhere; hence stage n is ON everywhere for n ≥ 3 and the count over the
(2n+1) × (2n+1) square is (2n+1)^2. Together with a(0), a(1), a(2) = 1, 5, 17 this gives the
closed form, the recurrence and the generating function.
-/

namespace OMA.Helpers

open OMA.S_oeis_a273384

/-- The value of every cell far from the origin at stage k: OFF at stage 0, ON afterwards. -/
def a273384_bg : ℕ → Bool
  | 0 => false
  | _ + 1 => true

/-- Outside the square of radius k around the origin, stage k agrees with the background. -/
theorem a273384_far : ∀ k : ℕ, ∀ x y : ℤ, ((k : ℤ) < |x| ∨ (k : ℤ) < |y|) →
    state k x y = a273384_bg k := by
  intro k
  induction k with
  | zero =>
    intro x y h
    simp only [state, initial, a273384_bg, decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ k ih =>
    intro x y h
    push_cast at h
    have h1 : state k x y = a273384_bg k := ih x y (by
      rcases h with h | h
      · left; linarith
      · right; linarith)
    have h2 : state k (x + 1) y = a273384_bg k := ih _ _ (by
      rcases h with h | h
      · left; cases abs_cases x <;> cases abs_cases (x + 1) <;> linarith
      · right; linarith)
    have h3 : state k (x - 1) y = a273384_bg k := ih _ _ (by
      rcases h with h | h
      · left; cases abs_cases x <;> cases abs_cases (x - 1) <;> linarith
      · right; linarith)
    have h4 : state k x (y + 1) = a273384_bg k := ih _ _ (by
      rcases h with h | h
      · left; linarith
      · right; cases abs_cases y <;> cases abs_cases (y + 1) <;> linarith)
    have h5 : state k x (y - 1) = a273384_bg k := ih _ _ (by
      rcases h with h | h
      · left; linarith
      · right; cases abs_cases y <;> cases abs_cases (y - 1) <;> linarith)
    show rule (state k x y) (neighbors (state k) x y) = a273384_bg (k + 1)
    simp only [neighbors, h1, h2, h3, h4, h5]
    cases k <;> simp only [a273384_bg] <;> decide

/-- Stage 3 is ON everywhere. -/
theorem a273384_state_three : state 3 = fun _ _ => true := by
  funext x y
  by_cases h : (3 : ℤ) < |x| ∨ (3 : ℤ) < |y|
  · exact a273384_far 3 x y (by exact_mod_cast h)
  · push Not at h
    obtain ⟨hx, hy⟩ := h
    rw [abs_le] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases x <;> interval_cases y <;> decide

/-- The all-ON plane is a fixed point: an ON cell with four ON neighbours stays ON (bit 9). -/
theorem a273384_step_all : step (fun _ _ => true) = fun _ _ => true := by
  funext x y
  show rule true (bit true + bit true + bit true + bit true) = true
  decide

/-- From stage 3 on, every cell is ON. -/
theorem a273384_state_ge : ∀ m : ℕ, 3 ≤ m → state m = fun _ _ => true := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact a273384_state_three
  | succ m hm ih =>
    show step (state m) = _
    rw [ih, a273384_step_all]

theorem a273384_a_ge (n : ℕ) (hn : 3 ≤ n) : a n = (2 * n + 1) ^ 2 := by
  unfold a
  rw [a273384_state_ge n hn]
  simp [bit, Finset.sum_const, Finset.card_range]
  ring

theorem a273384_a_small : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 17 := by
  decide

/-- The generating-function identity for any sequence with the values 1, 5, 17 at 0, 1, 2
and (2n+1)^2 from 3 on (the factor (1-x)^3 kills the quadratic part from degree 6 on). -/
theorem a273384_gf_aux (g : ℕ → ℤ) (h0 : g 0 = 1) (h1 : g 1 = 5) (h2 : g 2 = 17)
    (hz : ∀ n : ℕ, 3 ≤ n → g n = (2 * (n : ℤ) + 1) ^ 2) :
    PowerSeries.mk g * (1 - PowerSeries.X) ^ 3 =
      1 + 2 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 12 * PowerSeries.X ^ 3
        - 20 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 5 := by
  have e1 : PowerSeries.mk g * (1 - PowerSeries.X) ^ 3
      = PowerSeries.mk g - PowerSeries.C (3 : ℤ) * (PowerSeries.mk g * PowerSeries.X ^ 1)
        + PowerSeries.C (3 : ℤ) * (PowerSeries.mk g * PowerSeries.X ^ 2)
        - PowerSeries.mk g * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
    ring
  have e2 : (1 + 2 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 12 * PowerSeries.X ^ 3
      - 20 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 5 : PowerSeries ℤ)
      = PowerSeries.X ^ 0 + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 1
        + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 2 + PowerSeries.C (12 : ℤ) * PowerSeries.X ^ 3
        - PowerSeries.C (20 : ℤ) * PowerSeries.X ^ 4
        + PowerSeries.C (8 : ℤ) * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k
    · simp [h0]
    · simp [h0, h1]
    · simp [h0, h1, h2]
    · simp [h0, h1, h2, hz 3 le_rfl]
    · simp [h1, h2, hz 3 le_rfl, hz 4 (by norm_num)]
    · simp [h2, hz 3 le_rfl, hz 4 (by norm_num), hz 5 (by norm_num)]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    have c1 : 1 ≤ m + 6 := by omega
    have c2 : 2 ≤ m + 6 := by omega
    have c3 : 3 ≤ m + 6 := by omega
    have d0 : m + 6 ≠ 0 := by omega
    have d1 : m + 6 ≠ 1 := by omega
    have d2 : m + 6 ≠ 2 := by omega
    have d3 : m + 6 ≠ 3 := by omega
    have d4 : m + 6 ≠ 4 := by omega
    have d5 : m + 6 ≠ 5 := by omega
    simp only [c1, c2, c3, d0, d1, d2, d3, d4, d5, if_true, if_false]
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega]
    rw [hz (m + 6) (by omega), hz (m + 5) (by omega), hz (m + 4) (by omega),
      hz (m + 3) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a273384.main := by
  have hz : ∀ n : ℕ, 3 ≤ n → (OMA.S_oeis_a273384.a n : ℤ) = (2 * (n : ℤ) + 1) ^ 2 := by
    intro n hn
    rw [OMA.Helpers.a273384_a_ge n hn]
    push_cast
    ring
  obtain ⟨h0, h1, h2⟩ := OMA.Helpers.a273384_a_small
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [OMA.Helpers.a273384_a_ge n (by omega)]
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega]
    rw [hz (m + 6) (by omega), hz (m + 5) (by omega), hz (m + 4) (by omega),
      hz (m + 3) (by omega)]
    push_cast
    ring
  · exact OMA.Helpers.a273384_gf_aux (fun n => (OMA.S_oeis_a273384.a n : ℤ))
      (by simp [h0]) (by simp [h1]) (by simp [h2]) hz
