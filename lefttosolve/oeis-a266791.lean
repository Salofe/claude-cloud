import OMAStatements.S_oeis_a266791
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a266791

/-- The background value far from the origin: OFF at even stages, ON at odd stages. -/
def bg61 : ℕ → Bool
  | 0 => false
  | t + 1 => !bg61 t

theorem far61 : ∀ t : ℕ, ∀ i : ℤ, (t : ℤ) < |i| → state t i = bg61 t := by
  intro t
  induction t with
  | zero =>
    intro i h
    simp only [state, bg61, decide_eq_false_iff_not]
    rintro rfl
    simp at h
  | succ t ih =>
    intro i h
    push_cast at h
    have h1 : state t i = bg61 t := ih i (by linarith)
    have h2 : state t (i - 1) = bg61 t := ih _ (by cases abs_cases i <;> cases abs_cases (i - 1) <;> linarith)
    have h3 : state t (i + 1) = bg61 t := ih _ (by cases abs_cases i <;> cases abs_cases (i + 1) <;> linarith)
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = bg61 (t + 1)
    rw [h1, h2, h3]
    simp only [bg61]
    cases bg61 t <;> decide

/-- The even-stage pattern, as a function of the shifted position. -/
def P61 (d : ℤ) : Bool := decide (d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5)

/-- The odd-stage pattern, as a function of the shifted position. -/
def Q61 (d : ℤ) : Bool := !decide (d + 1 = 0 ∨ d + 1 = 2 ∨ d + 1 = 3 ∨ d + 1 = 4)

theorem stepP61 (d : ℤ) : rule (P61 (d - 1)) (P61 d) (P61 (d + 1)) = Q61 d := by
  by_cases h : -3 ≤ d ∧ d ≤ 7
  · obtain ⟨h1, h2⟩ := h
    interval_cases d <;> decide
  · unfold P61 Q61
    rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_false (by omega),
      decide_eq_false (by omega)]
    decide

theorem stepQ61 (d : ℤ) : rule (Q61 (d - 1)) (Q61 d) (Q61 (d + 1)) = P61 (d + 1) := by
  by_cases h : -3 ≤ d ∧ d ≤ 7
  · obtain ⟨h1, h2⟩ := h
    interval_cases d <;> decide
  · unfold P61 Q61
    rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_false (by omega),
      decide_eq_false (by omega)]
    decide

theorem state6 : ∀ i : ℤ, state 6 i = P61 (i + 3) := by
  intro i
  by_cases h : (6 : ℤ) < |i|
  · rw [far61 6 i (by exact_mod_cast h)]
    unfold P61
    rw [decide_eq_false]
    · rfl
    · rw [lt_abs] at h
      omega
  · push Not at h
    rw [abs_le] at h
    obtain ⟨h1, h2⟩ := h
    interval_cases i <;> decide

theorem pattern61 : ∀ s : ℕ, 3 ≤ s →
    (∀ i : ℤ, state (2 * s) i = P61 (i + s)) ∧ (∀ i : ℤ, state (2 * s + 1) i = Q61 (i + s)) := by
  intro s hs
  have hodd : ∀ s : ℕ, (∀ i : ℤ, state (2 * s) i = P61 (i + s)) →
      (∀ i : ℤ, state (2 * s + 1) i = Q61 (i + s)) := by
    intro s h i
    show rule (state (2 * s) (i - 1)) (state (2 * s) i) (state (2 * s) (i + 1)) = _
    rw [h, h, h, show i - 1 + (s : ℤ) = (i + s) - 1 by ring,
      show i + 1 + (s : ℤ) = (i + s) + 1 by ring]
    exact stepP61 _
  induction s, hs using Nat.le_induction with
  | base =>
    have h : ∀ i : ℤ, state (2 * 3) i = P61 (i + (3 : ℕ)) := by
      intro i; exact state6 i
    exact ⟨h, hodd 3 h⟩
  | succ s hs ih =>
    have h : ∀ i : ℤ, state (2 * (s + 1)) i = P61 (i + ((s + 1 : ℕ) : ℤ)) := by
      intro i
      show rule (state (2 * s + 1) (i - 1)) (state (2 * s + 1) i) (state (2 * s + 1) (i + 1)) = _
      rw [ih.2, ih.2, ih.2, show i - 1 + (s : ℤ) = (i + s) - 1 by ring,
        show i + 1 + (s : ℤ) = (i + s) + 1 by ring, stepQ61]
      push_cast
      ring_nf
    exact ⟨h, hodd (s + 1) h⟩

theorem a_succ61 (n : ℕ) : a (n + 1) = 2 * a n + mid (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simp at hk; omega
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

theorem mid_even61 (s : ℕ) (hs : 6 ≤ s) : mid (2 * s) = 0 := by
  unfold mid
  rw [(pattern61 s (by omega)).1 0]
  unfold P61
  rw [decide_eq_false (by omega)]
  rfl

theorem mid_odd61 (s : ℕ) (hs : 4 ≤ s) : mid (2 * s + 1) = 1 := by
  unfold mid
  rw [(pattern61 s (by omega)).2 0]
  unfold Q61
  rw [decide_eq_false (by omega)]
  rfl

theorem mid_large61 (k : ℕ) (hk : 11 ≤ k) : (mid k : ℚ) = (1 - (-1) ^ k) / 2 := by
  rcases Nat.even_or_odd' k with ⟨s, rfl | rfl⟩
  · rw [mid_even61 s (by omega), pow_mul]
    norm_num
  · rw [mid_odd61 s (by omega), pow_succ, pow_mul]
    norm_num

theorem mid_small61 : mid 0 = 1 ∧ mid 1 = 1 ∧ mid 2 = 1 ∧ mid 3 = 0 ∧ mid 4 = 1 ∧ mid 5 = 0 := by
  decide

theorem mid_mid61 : mid 6 = 1 ∧ mid 7 = 0 ∧ mid 8 = 0 ∧ mid 9 = 1 ∧ mid 10 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold mid; rw [(pattern61 3 le_rfl).1 0]; decide
  · unfold mid; rw [(pattern61 3 le_rfl).2 0]; decide
  · unfold mid; rw [(pattern61 4 (by omega)).1 0]; decide
  · unfold mid; rw [(pattern61 4 (by omega)).2 0]; decide
  · unfold mid; rw [(pattern61 5 (by omega)).1 0]; decide

theorem a_vals61 : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 7 ∧ a 3 = 14 ∧ a 4 = 29 ∧ a 5 = 58 ∧ a 6 = 117 ∧
    a 7 = 234 ∧ a 8 = 468 ∧ a 9 = 937 ∧ a 10 = 1875 := by
  obtain ⟨m0, m1, m2, m3, m4, m5⟩ := mid_small61
  obtain ⟨m6, m7, m8, m9, m10⟩ := mid_mid61
  have h0 : a 0 = 1 := by unfold a; simp [m0]
  have h1 : a 1 = 3 := by rw [a_succ61, h0, m1]
  have h2 : a 2 = 7 := by rw [a_succ61, h1, m2]
  have h3 : a 3 = 14 := by rw [a_succ61, h2, m3]
  have h4 : a 4 = 29 := by rw [a_succ61, h3, m4]
  have h5 : a 5 = 58 := by rw [a_succ61, h4, m5]
  have h6 : a 6 = 117 := by rw [a_succ61, h5, m6]
  have h7 : a 7 = 234 := by rw [a_succ61, h6, m7]
  have h8 : a 8 = 468 := by rw [a_succ61, h7, m8]
  have h9 : a 9 = 937 := by rw [a_succ61, h8, m9]
  have h10 : a 10 = 1875 := by rw [a_succ61, h9, m10]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem closed61 (m : ℕ) :
    (a (m + 10) : ℚ) = (-(-1) ^ (m + 10) + 5627 * 2 ^ (m + 1) - 3) / 6 := by
  induction m with
  | zero =>
    rw [a_vals61.2.2.2.2.2.2.2.2.2.2]
    norm_num
  | succ m ih =>
    rw [show m + 1 + 10 = (m + 10) + 1 by ring, a_succ61]
    push_cast
    rw [ih, mid_large61 _ (by omega)]
    ring

theorem closed61' (n : ℕ) (hn : 9 < n) :
    (a n : ℚ) = (-(-1) ^ n + 5627 * 2 ^ (n - 9) - 3) / 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [closed61, show m + 10 - 9 = m + 1 by omega]

open PowerSeries in
theorem gf61 (g : ℕ → ℚ) (h0 : g 0 = 1) (h1 : g 1 = 3) (h2 : g 2 = 7) (h3 : g 3 = 14)
    (h4 : g 4 = 29) (h5 : g 5 = 58) (h6 : g 6 = 117) (h7 : g 7 = 234) (h8 : g 8 = 468)
    (h9 : g 9 = 937)
    (hz : ∀ n : ℕ, 9 < n → g n = (-(-1) ^ n + 5627 * 2 ^ (n - 9) - 3) / 6) :
    PowerSeries.mk g * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12) := by
  have e1 : PowerSeries.mk g * ((1 - X) * (1 + X) * (1 - 2 * X))
      = PowerSeries.mk g - C (2 : ℚ) * (PowerSeries.mk g * X ^ 1)
        - (PowerSeries.mk g * X ^ 2) + C (2 : ℚ) * (PowerSeries.mk g * X ^ 3) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 : PowerSeries ℚ)
      = X ^ 0 + X ^ 1 - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 := by
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  have z10 := hz 10 (by norm_num)
  have z11 := hz 11 (by norm_num)
  have z12 := hz 12 (by norm_num)
  norm_num at z10 z11 z12
  rcases Nat.lt_or_ge k 13 with hk | hk
  · interval_cases k <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, z10, z11, z12] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 13 := ⟨k - 13, by omega⟩
    have c1 : 1 ≤ m + 13 := by omega
    have c2 : 2 ≤ m + 13 := by omega
    have c3 : 3 ≤ m + 13 := by omega
    simp only [c1, c2, c3, if_true, show m + 13 ≠ 0 by omega, show m + 13 ≠ 1 by omega,
      show m + 13 ≠ 3 by omega, show m + 13 ≠ 8 by omega, show m + 13 ≠ 9 by omega,
      show m + 13 ≠ 10 by omega, show m + 13 ≠ 12 by omega, if_false]
    rw [show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega,
      show m + 13 - 3 = m + 10 by omega]
    rw [hz (m + 13) (by omega), hz (m + 12) (by omega), hz (m + 11) (by omega),
      hz (m + 10) (by omega)]
    rw [show m + 13 - 9 = m + 4 by omega, show m + 12 - 9 = m + 3 by omega,
      show m + 11 - 9 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a266791.main := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := OMA.Helpers.a_vals61
  refine ⟨OMA.Helpers.closed61', ?_⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq]
  · have := OMA.Helpers.gf61 (fun n => (OMA.S_oeis_a266791.a n : ℚ)) (by simp [h0]) (by simp [h1])
      (by simp [h2]) (by simp [h3]) (by simp [h4]) (by simp [h5]) (by simp [h6]) (by simp [h7])
      (by simp [h8]) (by simp [h9]) OMA.Helpers.closed61'
    rw [this]
  · simp
