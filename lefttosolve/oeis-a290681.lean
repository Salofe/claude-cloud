import OMAStatements.S_oeis_a290681

/-!
Proof of the three conjectures of OEIS A290681 (the diagonal of Rule 929 started from one ON cell).

Rule 929 = 1110100001 in binary. Writing Z for the origin, N for its four orthogonal neighbours and
M = Z together with N, the first stages are: stage 0 is Z; stage 1 is everything except M (the
background turns ON by bit 0, the origin turns OFF by bit 1, its neighbours stay OFF by bit 2);
stage 2 is everything except N; stage 3 is everything except Z; stage 4 is everything (the origin
has four OFF neighbours and turns ON by bit 8). Everything ON is a fixed point (bit 9). Each step
is checked on the box [-2, 2] x [-2, 2] by evaluation; outside it every cell involved is OFF in the
old configuration's exceptional set, hence ON. So every diagonal cell is ON from stage 4 on, which
gives 9 a(n) + 1 = 10^(n+1) for n >= 4; the recurrence and the generating function follow, with
a(0..3) = 1, 1, 111, 111 for the first coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a290681 PowerSeries

abbrev a290681_Z (x y : ℤ) : Prop := x = 0 ∧ y = 0

abbrev a290681_N (x y : ℤ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)

theorem a290681_s0 (x y : ℤ) : state 0 (x, y) = decide (a290681_Z x y) := by
  simp [state, Prod.ext_iff]

theorem a290681_succ (t : ℕ) (x y : ℤ) :
    state (t + 1) (x, y) = rule (state t (x, y))
      ((if state t (x, y - 1) = true then 1 else 0) + (if state t (x, y + 1) = true then 1 else 0) +
        (if state t (x - 1, y) = true then 1 else 0) + (if state t (x + 1, y) = true then 1 else 0)) := by
  simp only [state, nbrs, List.countP_cons, List.countP_nil, zero_add]

abbrev a290681_M (x y : ℤ) : Prop :=
  (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)

theorem a290681_s1 (x y : ℤ) : state 1 (x, y) = !decide (a290681_M x y) := by
  rw [a290681_succ, a290681_s0, a290681_s0, a290681_s0, a290681_s0, a290681_s0]
  by_cases hb : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    interval_cases x <;> interval_cases y <;> decide
  · rw [decide_eq_false (by omega : ¬ a290681_Z x y), decide_eq_false (by omega : ¬ a290681_Z x (y - 1)), decide_eq_false (by omega : ¬ a290681_Z x (y + 1)), decide_eq_false (by omega : ¬ a290681_Z (x - 1) y), decide_eq_false (by omega : ¬ a290681_Z (x + 1) y), decide_eq_false (by omega : ¬ a290681_M x y)]
    decide

theorem a290681_s2 (x y : ℤ) : state 2 (x, y) = !decide (a290681_N x y) := by
  rw [a290681_succ, a290681_s1, a290681_s1, a290681_s1, a290681_s1, a290681_s1]
  by_cases hb : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    interval_cases x <;> interval_cases y <;> decide
  · rw [decide_eq_false (by omega : ¬ a290681_M x y), decide_eq_false (by omega : ¬ a290681_M x (y - 1)), decide_eq_false (by omega : ¬ a290681_M x (y + 1)), decide_eq_false (by omega : ¬ a290681_M (x - 1) y), decide_eq_false (by omega : ¬ a290681_M (x + 1) y), decide_eq_false (by omega : ¬ a290681_N x y)]
    decide

theorem a290681_s3 (x y : ℤ) : state 3 (x, y) = !decide (a290681_Z x y) := by
  rw [a290681_succ, a290681_s2, a290681_s2, a290681_s2, a290681_s2, a290681_s2]
  by_cases hb : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    interval_cases x <;> interval_cases y <;> decide
  · rw [decide_eq_false (by omega : ¬ a290681_N x y), decide_eq_false (by omega : ¬ a290681_N x (y - 1)), decide_eq_false (by omega : ¬ a290681_N x (y + 1)), decide_eq_false (by omega : ¬ a290681_N (x - 1) y), decide_eq_false (by omega : ¬ a290681_N (x + 1) y), decide_eq_false (by omega : ¬ a290681_Z x y)]
    decide

theorem a290681_s4 (x y : ℤ) : state 4 (x, y) = true := by
  rw [a290681_succ, a290681_s3, a290681_s3, a290681_s3, a290681_s3, a290681_s3]
  by_cases hb : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    interval_cases x <;> interval_cases y <;> decide
  · rw [decide_eq_false (by omega : ¬ a290681_Z x y), decide_eq_false (by omega : ¬ a290681_Z x (y - 1)), decide_eq_false (by omega : ¬ a290681_Z x (y + 1)), decide_eq_false (by omega : ¬ a290681_Z (x - 1) y), decide_eq_false (by omega : ¬ a290681_Z (x + 1) y)]
    decide

theorem a290681_big (n : ℕ) (x y : ℤ) : state (n + 4) (x, y) = true := by
  induction n generalizing x y with
  | zero => exact a290681_s4 x y
  | succ n ih =>
    rw [show n + 1 + 4 = (n + 4) + 1 by omega, a290681_succ, ih, ih, ih, ih, ih]
    decide

theorem a290681_geom (n : ℕ) :
    9 * (∑ k ∈ Finset.range (n + 1), 10 ^ (n - k)) + 1 = 10 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [pow_succ 10 (n + 1)]
    omega

theorem a290681_closedN (n : ℕ) (hn : 4 ≤ n) : 9 * a n + 1 = 10 ^ (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h : a (m + 4) = ∑ k ∈ Finset.range (m + 4 + 1), 10 ^ (m + 4 - k) := by
    unfold a
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [a290681_big, if_pos rfl]
  rw [h, a290681_geom]

theorem a290681_v0 : a 0 = 1 := by
  simp [a, a290681_s0]

theorem a290681_v1 : a 1 = 1 := by
  simp [a, Finset.sum_range_succ, a290681_s1]

theorem a290681_v2 : a 2 = 111 := by
  simp [a, Finset.sum_range_succ, a290681_s2]

theorem a290681_v3 : a 3 = 111 := by
  simp [a, Finset.sum_range_succ, a290681_s3]

theorem a290681_closedQ (n : ℕ) (hn : 4 ≤ n) : 9 * (a n : ℚ) + 1 = 10 ^ (n + 1) := by
  have h := congrArg (fun z : ℕ => (z : ℚ)) (a290681_closedN n hn)
  push_cast at h
  exact h

theorem a290681_gf :
    A * ((1 - X) * (1 - 10 * X)) =
      1 - 10 * X + 110 * X ^ 2 - 1100 * X ^ 3 + 11000 * X ^ 4 - 10000 * X ^ 5 := by
  have e : A * ((1 - X) * (1 - 10 * X)) =
      X ^ 0 * A - C (11 : ℚ) * (X ^ 1 * A) + C (10 : ℚ) * (X ^ 2 * A) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 - 10 * X + 110 * X ^ 2 - 1100 * X ^ 3 + 11000 * X ^ 4 - 10000 * X ^ 5 : ℚ⟦X⟧) =
      C (1 : ℚ) * X ^ 0 - C (10 : ℚ) * X ^ 1 + C (110 : ℚ) * X ^ 2 - C (1100 : ℚ) * X ^ 3
        + C (11000 : ℚ) * X ^ 4 - C (10000 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e, e2]
  ext k
  simp only [map_add, map_sub, coeff_C_mul_X_pow]
  rw [coeff_C_mul, coeff_C_mul]
  simp only [coeff_X_pow_mul', A, coeff_mk]
  by_cases hk : 6 ≤ k
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    simp only [if_pos (show 0 ≤ m + 6 by omega), if_pos (show 1 ≤ m + 6 by omega),
      if_pos (show 2 ≤ m + 6 by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    rw [show m + 6 - 0 = m + 6 by omega, show m + 6 - 1 = m + 5 by omega,
      show m + 6 - 2 = m + 4 by omega]
    have h6 := a290681_closedQ (m + 6) (by omega)
    have h5 := a290681_closedQ (m + 5) (by omega)
    have h4 := a290681_closedQ (m + 4) (by omega)
    have : 9 * ((a (m + 6) : ℚ) - 11 * a (m + 5) + 10 * a (m + 4)) = 0 := by
      rw [show m + 6 + 1 = (m + 4 + 1) + 2 by omega, show m + 5 + 1 = (m + 4 + 1) + 1 by omega,
        pow_add, pow_add] at *
      linear_combination h6 - 11 * h5 + 10 * h4
    linarith
  · have v4 : (a 4 : ℚ) = 11111 := by
      have := a290681_closedQ 4 le_rfl
      norm_num at this
      linarith
    have v5 : (a 5 : ℚ) = 111111 := by
      have := a290681_closedQ 5 (by norm_num)
      norm_num at this
      linarith
    interval_cases k <;> simp [a290681_v0, a290681_v1, a290681_v2, a290681_v3, v4, v5] <;> norm_num

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a290681.main := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    exact OMA.Helpers.a290681_gf
  · intro n hn
    have h := OMA.Helpers.a290681_closedQ n (by omega)
    rw [eq_div_iff (by norm_num : (9 : ℚ) ≠ 0), add_comm 1 n]
    linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega]
    have h6 := OMA.Helpers.a290681_closedN (m + 6) (by omega)
    have h5 := OMA.Helpers.a290681_closedN (m + 5) (by omega)
    have h4 := OMA.Helpers.a290681_closedN (m + 4) (by omega)
    rw [show m + 6 + 1 = (m + 4 + 1) + 2 by omega, pow_add] at h6
    rw [show m + 5 + 1 = (m + 4 + 1) + 1 by omega, pow_add] at h5
    omega
