import OMAStatements.S_oeis_a285778
import Mathlib

/-!
Proof of the conjectures of OEIS A285778 (Rule 89, diagonal of stage n).

Away from the box `[-t, t]²` every cell is in the background state, which alternates OFF/ON.
Inside, a direct evaluation shows that stage 4 is entirely OFF. Rule 89 turns an OFF cell with no
ON neighbour ON and an ON cell with four ON neighbours OFF, so from stage 4 on the plane alternates
between all OFF (even stages) and all ON (odd stages). Hence a(n) = 0 for even n > 3 and
a(n) = 2^(n+1) - 1 for odd n > 3; the recurrence and the generating function follow by comparing
coefficients, using a(0..3) = 1, 1, 4, 7.
-/

namespace OMA.Helpers
open OMA.S_oeis_a285778

theorem a285778_step (t : ℕ) (x y : ℤ) : state (t + 1) (x, y) =
    rule (state t (x, y)) ((if state t (x + 1, y) then 1 else 0) + (if state t (x - 1, y) then 1 else 0)
      + (if state t (x, y + 1) then 1 else 0) + (if state t (x, y - 1) then 1 else 0)) := by
  show rule _ ((nbrs (x, y)).countP _) = _
  simp only [nbrs, List.countP_cons, List.countP_nil]
  congr 1
  omega

/-- The background state at time `t` (the state of every cell far from the origin). -/
def a285778_bg : ℕ → Bool
  | 0 => false
  | t + 1 => rule (a285778_bg t) (if a285778_bg t then 4 else 0)

/-- Cells outside the box `[-t, t]²` are in the background state at time `t`. -/
theorem a285778_far (t : ℕ) (x y : ℤ) (h : x < -t ∨ (t : ℤ) < x ∨ y < -t ∨ (t : ℤ) < y) :
    state t (x, y) = a285778_bg t := by
  induction t generalizing x y with
  | zero =>
    show decide ((x, y) = (0, 0)) = false
    simp only [decide_eq_false_iff_not, Prod.mk.injEq]
    push_cast at h
    omega
  | succ t ih =>
    push_cast at h
    rw [a285778_step, ih x y (by omega), ih (x + 1) y (by omega), ih (x - 1) y (by omega),
      ih x (y + 1) (by omega), ih x (y - 1) (by omega)]
    show _ = rule (a285778_bg t) (if a285778_bg t then 4 else 0)
    cases a285778_bg t <;> rfl

/-- At time 4 every cell is OFF. -/
theorem a285778_state4 (x y : ℤ) : state 4 (x, y) = false := by
  by_cases h : x < -4 ∨ 4 < x ∨ y < -4 ∨ 4 < y
  · rw [a285778_far 4 x y (by push_cast; exact h)]
    rfl
  · have h1 : -4 ≤ x := by omega
    have h2 : x ≤ 4 := by omega
    have h3 : -4 ≤ y := by omega
    have h4 : y ≤ 4 := by omega
    interval_cases x <;> interval_cases y <;> decide +kernel

theorem a285778_late (m : ℕ) (x y : ℤ) :
    state (2 * m + 4) (x, y) = false ∧ state (2 * m + 5) (x, y) = true := by
  induction m generalizing x y with
  | zero =>
    refine ⟨a285778_state4 x y, ?_⟩
    rw [a285778_step]
    simp only [a285778_state4]
    rfl
  | succ m ih =>
    have e1 : 2 * (m + 1) + 4 = (2 * m + 5) + 1 := by ring
    have e2 : 2 * (m + 1) + 5 = (2 * (m + 1) + 4) + 1 := by ring
    have h1 : ∀ u v : ℤ, state (2 * (m + 1) + 4) (u, v) = false := by
      intro u v
      rw [e1, a285778_step]
      simp only [(ih _ _).2]
      rfl
    refine ⟨h1 x y, ?_⟩
    rw [e2, a285778_step]
    simp only [h1]
    rfl

theorem a285778_geom (n : ℕ) : ∑ k ∈ Finset.range (n + 1), 2 ^ (n - k) + 1 = 2 ^ (n + 1) := by
  have := Finset.sum_range_reflect (fun k => 2 ^ k) (n + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this]
  clear this
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem a285778_even (m : ℕ) : a (2 * m + 4) = 0 := by
  unfold a
  apply Finset.sum_eq_zero
  intro k _
  simp [(a285778_late m _ _).1]

theorem a285778_odd (m : ℕ) : a (2 * m + 5) + 1 = 2 ^ (2 * m + 6) := by
  unfold a
  simp only [(a285778_late m _ _).2, if_true]
  exact a285778_geom (2 * m + 5)

theorem a285778_small : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem a285778_even' (n : ℕ) (h3 : 3 < n) (he : Even n) : a n = 0 := by
  obtain ⟨r, hr⟩ := he
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨r - 2, by omega⟩
  exact a285778_even m

theorem a285778_odd' (n : ℕ) (h3 : 3 < n) (ho : Odd n) : a n + 1 = 2 ^ (n + 1) := by
  obtain ⟨r, hr⟩ := ho
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 5 := ⟨r - 2, by omega⟩
  exact a285778_odd m

end OMA.Helpers

open OMA.S_oeis_a285778 OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a285778.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hD : constantCoeff ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) : ℚ⟦X⟧) ≠ 0 := by
      simp
    rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
    have eL : A * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X))
        = A - C (5 : ℚ) * (A * X ^ 2) + C (4 : ℚ) * (A * X ^ 4) := by
      simp only [map_ofNat]
      ring
    have eR : (1 + X - X ^ 2 + 2 * X ^ 3 - 16 * X ^ 4 + 32 * X ^ 5 + 16 * X ^ 6 - 32 * X ^ 7 : ℚ⟦X⟧)
        = 1 + X - X ^ 2 + C (2 : ℚ) * X ^ 3 - C (16 : ℚ) * X ^ 4 + C (32 : ℚ) * X ^ 5
          + C (16 : ℚ) * X ^ 6 - C (32 : ℚ) * X ^ 7 := by
      simp only [map_ofNat]
    rw [eL, eR]
    obtain ⟨h0, h1, h2, h3⟩ := a285778_small
    ext k
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X, A,
      coeff_mk]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp [h0]
    · simp [h1]
    · simp [h2, h0]; norm_num
    · simp [h3, h1]; norm_num
    · simp [a285778_even 0, h2, h0]; norm_num
    · have := a285778_odd 0
      simp [h3, h1]
      norm_num at this
      rw [show a 5 = 63 by omega]
      norm_num
    · simp [a285778_even 1, a285778_even 0, h2]; norm_num
    · have h7 := a285778_odd 1
      have h5 := a285778_odd 0
      norm_num at h7 h5
      simp [show a 7 = 255 by omega, show a 5 = 63 by omega, h3]
      norm_num
    · simp only [show k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = k + 8 by ring]
      simp
      rcases Nat.even_or_odd k with hk | hk
      · obtain ⟨r, hr⟩ := hk
        rw [a285778_even' (k + 8) (by omega) ⟨r + 4, by omega⟩,
          a285778_even' (k + 6) (by omega) ⟨r + 3, by omega⟩,
          a285778_even' (k + 4) (by omega) ⟨r + 2, by omega⟩]
        simp
      · obtain ⟨r, hr⟩ := hk
        have e8 := a285778_odd' (k + 8) (by omega) ⟨r + 4, by omega⟩
        have e6 := a285778_odd' (k + 6) (by omega) ⟨r + 3, by omega⟩
        have e4 := a285778_odd' (k + 4) (by omega) ⟨r + 2, by omega⟩
        have q8 : (a (k + 8) : ℚ) = 2 ^ (k + 9) - 1 := by
          rw [eq_sub_iff_add_eq]; exact_mod_cast e8
        have q6 : (a (k + 6) : ℚ) = 2 ^ (k + 7) - 1 := by
          rw [eq_sub_iff_add_eq]; exact_mod_cast e6
        have q4 : (a (k + 4) : ℚ) = 2 ^ (k + 5) - 1 := by
          rw [eq_sub_iff_add_eq]; exact_mod_cast e4
        rw [q8, q6, q4]
        ring
  · intro n h3 he
    simp [a285778_even' n h3 he]
  · intro n h3 ho
    have := a285778_odd' n h3 ho
    rw [eq_sub_iff_add_eq]
    exact_mod_cast this
  · intro n h7
    rcases Nat.even_or_odd n with he | ho
    · rw [a285778_even' n (by omega) he, a285778_even' (n - 2) (by omega) ?_,
        a285778_even' (n - 4) (by omega) ?_]
      · simp
      · obtain ⟨r, hr⟩ := he; exact ⟨r - 2, by omega⟩
      · obtain ⟨r, hr⟩ := he; exact ⟨r - 1, by omega⟩
    · have e0 := a285778_odd' n (by omega) ho
      have e2 := a285778_odd' (n - 2) (by omega) (by obtain ⟨r, hr⟩ := ho; exact ⟨r - 1, by omega⟩)
      have e4 := a285778_odd' (n - 4) (by omega) (by obtain ⟨r, hr⟩ := ho; exact ⟨r - 2, by omega⟩)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      rw [show m + 8 - 2 = m + 6 by omega] at e2 ⊢
      rw [show m + 8 - 4 = m + 4 by omega] at e4 ⊢
      have q0 : (a (m + 8) : ℤ) = 2 ^ (m + 9) - 1 := by
        rw [eq_sub_iff_add_eq]; exact_mod_cast e0
      have q2 : (a (m + 6) : ℤ) = 2 ^ (m + 7) - 1 := by
        rw [eq_sub_iff_add_eq]; exact_mod_cast e2
      have q4 : (a (m + 4) : ℤ) = 2 ^ (m + 5) - 1 := by
        rw [eq_sub_iff_add_eq]; exact_mod_cast e4
      rw [q0, q2, q4]
      ring
