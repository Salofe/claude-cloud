import OMAStatements.S_oeis_a273405
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a273405 PowerSeries

/-- One synchronous update of the plane. -/
def stp (g : ℤ × ℤ → Bool) (p : ℤ × ℤ) : Bool :=
  rule (g p) ((nbrs p).countP (fun q => g q))

theorem state_succ (t : ℕ) : state (t + 1) = stp (state t) := by
  funext p
  rfl

/-- Odd stages: the OFF cells form the plus |x| + |y| ≤ 1. -/
def Sodd (p : ℤ × ℤ) : Bool :=
  !decide ((p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1) ∨ (p.2 = 0 ∧ -1 ≤ p.1 ∧ p.1 ≤ 1))

/-- Even stages from 2 on: the OFF cells are the four arms |x| + |y| = 1. -/
def Seven (p : ℤ × ℤ) : Bool :=
  !decide ((p.1 = 0 ∧ (p.2 = 1 ∨ p.2 = -1)) ∨ (p.2 = 0 ∧ (p.1 = 1 ∨ p.1 = -1)))

theorem stp_on (g : ℤ × ℤ → Bool) (x y : ℤ) (h0 : g (x, y) = true)
    (h1 : g (x + 1, y) = true) (h2 : g (x - 1, y) = true) (h3 : g (x, y + 1) = true)
    (h4 : g (x, y - 1) = true) : stp g (x, y) = true := by
  simp only [stp, nbrs, List.countP_cons, List.countP_nil, h0, h1, h2, h3, h4]
  decide

theorem stp_off (g : ℤ × ℤ → Bool) (x y : ℤ) (h0 : g (x, y) = false)
    (h1 : g (x + 1, y) = false) (h2 : g (x - 1, y) = false) (h3 : g (x, y + 1) = false)
    (h4 : g (x, y - 1) = false) : stp g (x, y) = true := by
  simp only [stp, nbrs, List.countP_cons, List.countP_nil, h0, h1, h2, h3, h4]
  decide

theorem state0_far (x y : ℤ) (h : x ≤ -1 ∨ 1 ≤ x ∨ y ≤ -1 ∨ 1 ≤ y) :
    state 0 (x, y) = false := by
  simp only [state, decide_eq_false_iff_not, Prod.mk.injEq]
  omega

theorem Sodd_far (x y : ℤ) (h : x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) : Sodd (x, y) = true := by
  simp only [Sodd, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

theorem Seven_far (x y : ℤ) (h : x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) : Seven (x, y) = true := by
  simp only [Seven, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

theorem state_one : state 1 = Sodd := by
  rw [state_succ]
  funext ⟨x, y⟩
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · rw [Sodd_far x y (by omega)]
    exact stp_off _ x y (state0_far _ _ (by omega)) (state0_far _ _ (by omega))
      (state0_far _ _ (by omega)) (state0_far _ _ (by omega)) (state0_far _ _ (by omega))

theorem stp_Sodd : stp Sodd = Seven := by
  funext ⟨x, y⟩
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · rw [Seven_far x y (by omega)]
    exact stp_on _ x y (Sodd_far _ _ (by omega)) (Sodd_far _ _ (by omega))
      (Sodd_far _ _ (by omega)) (Sodd_far _ _ (by omega)) (Sodd_far _ _ (by omega))

theorem stp_Seven : stp Seven = Sodd := by
  funext ⟨x, y⟩
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · rw [Sodd_far x y (by omega)]
    exact stp_on _ x y (Seven_far _ _ (by omega)) (Seven_far _ _ (by omega))
      (Seven_far _ _ (by omega)) (Seven_far _ _ (by omega)) (Seven_far _ _ (by omega))

theorem state_odd_even (m : ℕ) : state (2 * m + 1) = Sodd ∧ state (2 * m + 2) = Seven := by
  induction m with
  | zero => exact ⟨state_one, by rw [state_succ, state_one, stp_Sodd]⟩
  | succ m ih =>
    have e1 : state (2 * (m + 1) + 1) = Sodd := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring, state_succ, ih.2, stp_Seven]
    exact ⟨e1, by rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by ring, state_succ, e1,
      stp_Sodd]⟩

/-- A sum over the window `[-n, n]` of a function supported in `[-1, 1]`. -/
theorem sum_center (h : ℤ → ℕ) (hz : ∀ z : ℤ, (z ≤ -2 ∨ 2 ≤ z) → h z = 0) (n : ℕ)
    (hn : 1 ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), h ((x : ℤ) - n) = h (-1) + h 0 + h 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (m + 1) + 1 = m + 3 + m by ring, Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range m, h ((x : ℤ) - ((m + 1 : ℕ) : ℤ)) = 0 :=
    Finset.sum_eq_zero (fun x hx => hz _ (by simp at hx; push_cast; omega))
  have e2 : ∑ x ∈ Finset.range m, h (((m + 3 + x : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) = 0 :=
    Finset.sum_eq_zero (fun x _ => hz _ (by push_cast; omega))
  rw [e1, e2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
  have q0 : ((m : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) = -1 := by push_cast; ring
  have q1 : ((m + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) = 0 := by ring
  have q2 : ((m + 2 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) = 1 := by push_cast; ring
  rw [q0, q1, q2]

/-- Counting the ON cells of a configuration that is ON outside `[-1, 1]²`. -/
theorem count (g : ℤ × ℤ → Bool)
    (hg : ∀ x y : ℤ, (x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) → g (x, y) = true) (n : ℕ) (hn : 1 ≤ n) :
    (∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
        if g ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0) +
      (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        if g ((i : ℤ) - 1, (j : ℤ) - 1) then 0 else 1) = (2 * n + 1) ^ 2 := by
  set off : ℤ × ℤ → ℕ := fun p => if g p then 0 else 1 with hoff
  have hsplit : ∀ p, (if g p then 1 else 0) + off p = 1 := by
    intro p; simp only [hoff]; cases g p <;> rfl
  have hoff0 : ∀ x y : ℤ, (x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) → off (x, y) = 0 := by
    intro x y hxy; simp only [hoff, hg x y hxy, if_true]
  have hO : ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
      off ((x : ℤ) - n, (y : ℤ) - n) =
      ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, off ((i : ℤ) - 1, (j : ℤ) - 1) := by
    have inner : ∀ x : ℤ, ∑ y ∈ Finset.range (2 * n + 1), off (x, (y : ℤ) - n) =
        off (x, -1) + off (x, 0) + off (x, 1) :=
      fun x => sum_center (fun z => off (x, z)) (fun z hz => hoff0 x z (by omega)) n hn
    simp only [inner]
    rw [sum_center (fun z => off (z, -1) + off (z, 0) + off (z, 1))
      (fun z hz => by rw [hoff0 z (-1) (by omega), hoff0 z 0 (by omega), hoff0 z 1 (by omega)])
      n hn]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    try ring
  have htot : ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
      ((if g ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0) + off ((x : ℤ) - n, (y : ℤ) - n)) =
      (2 * n + 1) ^ 2 := by
    simp only [hsplit, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    ring
  rw [← hO, ← htot]
  simp only [Finset.sum_add_distrib]

theorem a_odd (m : ℕ) : a (2 * m + 1) = (2 * (2 * m + 1) + 1) ^ 2 - 5 := by
  have h := count Sodd Sodd_far (2 * m + 1) (by omega)
  have e : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
      if Sodd ((i : ℤ) - 1, (j : ℤ) - 1) then 0 else 1) = 5 := by decide
  rw [e] at h
  unfold a
  rw [(state_odd_even m).1]
  omega

theorem a_even (m : ℕ) : a (2 * m + 2) = (2 * (2 * m + 2) + 1) ^ 2 - 4 := by
  have h := count Seven Seven_far (2 * m + 2) (by omega)
  have e : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
      if Seven ((i : ℤ) - 1, (j : ℤ) - 1) then 0 else 1) = 4 := by decide
  rw [e] at h
  unfold a
  rw [(state_odd_even m).2]
  omega

/-- The closed form, doubled, in the integers. -/
theorem a_closed (n : ℕ) (hn : 0 < n) :
    2 * (a n : ℤ) = (-1) ^ n + 8 * n + 8 * n ^ 2 - 7 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, a_even j]
    have : 4 ≤ (2 * (2 * j + 2) + 1) ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]
    rw [pow_add, pow_mul]
    norm_num
    ring
  · rw [a_odd m]
    have : 5 ≤ (2 * (2 * m + 1) + 1) ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]
    rw [pow_add, pow_mul]
    norm_num
    ring

theorem a_zero : a 0 = 1 := by decide

end OMA.Helpers

open OMA.Helpers OMA.S_oeis_a273405 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a273405.main := by
  have hq : ∀ n : ℕ, 0 < n → (a n : ℚ) = ((-1) ^ n + 8 * n + 8 * n ^ 2 - 7) / 2 := by
    intro n hn
    have h := a_closed n hn
    have h' := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at h'
    linarith
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · intro n hn he
    rw [hq n hn, he.neg_one_pow]
    ring
  · intro n hn ho
    rw [hq n hn, ho.neg_one_pow]
    ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 3 = k + 2 by omega,
      show k + 5 - 4 = k + 1 by omega]
    have h5 := a_closed (k + 5) (by omega)
    have h4 := a_closed (k + 4) (by omega)
    have h2 := a_closed (k + 2) (by omega)
    have h1 := a_closed (k + 1) (by omega)
    have e5 : 2 * (a (k + 5) : ℤ) = -(-1) ^ k + 8 * (k + 5) + 8 * (k + 5) ^ 2 - 7 := by
      rw [h5]; push_cast; ring
    have e4 : 2 * (a (k + 4) : ℤ) = (-1) ^ k + 8 * (k + 4) + 8 * (k + 4) ^ 2 - 7 := by
      rw [h4]; push_cast; ring
    have e2 : 2 * (a (k + 2) : ℤ) = (-1) ^ k + 8 * (k + 2) + 8 * (k + 2) ^ 2 - 7 := by
      rw [h2]; push_cast; ring
    have e1 : 2 * (a (k + 1) : ℤ) = -(-1) ^ k + 8 * (k + 1) + 8 * (k + 1) ^ 2 - 7 := by
      rw [h1]; push_cast; ring
    nlinarith
  · have hD : constantCoeff ((1 - X) ^ 3 * (1 + X) : ℚ⟦X⟧) ≠ 0 := by
      simp
    rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
    have e1 : A * ((1 - X) ^ 3 * (1 + X)) =
        A - C (2 : ℚ) * (A * X ^ 1) + C (2 : ℚ) * (A * X ^ 3) - A * X ^ 4 := by
      rw [map_ofNat]
      ring
    have e2 : (1 + 2 * X + 13 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4 : ℚ⟦X⟧) =
        1 + C (2 : ℚ) * X ^ 1 + C (13 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3
          - C (4 : ℚ) * X ^ 4 := by
      simp only [map_ofNat, pow_one]
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, coeff_C_mul_X_pow, coeff_one]
    simp only [coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
    by_cases hk : k < 5
    · interval_cases k <;> simp [a_zero, hq 1 (by norm_num), hq 2 (by norm_num),
        hq 3 (by norm_num), hq 4 (by norm_num)] <;> norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
      rw [if_pos (show 1 ≤ j + 5 by omega), if_pos (show 3 ≤ j + 5 by omega),
        if_pos (show 4 ≤ j + 5 by omega)]
      simp only [show j + 5 ≠ 0 by omega, show j + 5 ≠ 1 by omega, show j + 5 ≠ 2 by omega,
        show j + 5 ≠ 3 by omega, show j + 5 ≠ 4 by omega, if_false]
      rw [show j + 5 - 1 = j + 4 by omega, show j + 5 - 3 = j + 2 by omega,
        show j + 5 - 4 = j + 1 by omega]
      rw [hq (j + 5) (by omega), hq (j + 4) (by omega), hq (j + 2) (by omega),
        hq (j + 1) (by omega)]
      push_cast
      ring
