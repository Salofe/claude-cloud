import OMAStatements.S_oeis_a277864
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a277864 PowerSeries

theorem rule_eq (c : Bool) (k : ℕ) : rule c k = decide (k = 0) := by
  cases k with
  | zero => cases c <;> rfl
  | succ k =>
    unfold rule
    rw [Nat.testBit_eq_false_of_lt]
    · simp
    · calc (3 : ℕ) < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * (k + 1) + cond c 1 0) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem step_true (t : ℕ) (x y : ℤ) : state (t + 1) (x, y) = true ↔
    (state t (x + 1, y) = false ∧ state t (x - 1, y) = false ∧ state t (x, y + 1) = false ∧
      state t (x, y - 1) = false) := by
  show rule _ _ = true ↔ _
  simp [rule_eq, nbrs, List.countP_cons]
  tauto

theorem s0 (x y : ℤ) : state 0 (x, y) = true ↔ (x = 0 ∧ y = 0) := by
  show decide ((x, y) = ((0 : ℤ), (0 : ℤ))) = true ↔ _
  simp

theorem s1 (x y : ℤ) : state 1 (x, y) = false ↔
    ((x + 1 = 0 ∧ y = 0) ∨ (x - 1 = 0 ∧ y = 0) ∨ (x = 0 ∧ y + 1 = 0) ∨ (x = 0 ∧ y - 1 = 0)) := by
  rw [← Bool.not_eq_true, step_true 0 x y]
  simp only [← Bool.not_eq_true, s0]
  tauto

theorem s2 (x y : ℤ) : state 2 (x, y) = true ↔ (x = 0 ∧ y = 0) := by
  rw [step_true 1 x y, s1, s1, s1, s1]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem key (t : ℕ) (p : ℤ × ℤ) :
    state (t + 1) p = rule (state t p) ((nbrs p).countP (fun q => state t q)) := rfl

theorem period (t : ℕ) : state (t + 2) = state t := by
  induction t with
  | zero =>
    funext p
    obtain ⟨x, y⟩ := p
    rw [Bool.eq_iff_iff, s2, s0]
  | succ t ih =>
    funext p
    show state (t + 2 + 1) p = state (t + 1) p
    rw [key (t + 2), key t, ih]

theorem even_state (m : ℕ) : state (2 * m) = state 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [show 2 * (m + 1) = 2 * m + 2 by ring, period, ih]

theorem odd_state (m : ℕ) : state (2 * m + 1) = state 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, period, ih]

theorem a_even (m : ℕ) : a (2 * m) = 1 := by
  unfold a
  rw [even_state, Finset.sum_range_succ, Finset.sum_eq_zero]
  · have : state 0 (((2 * m : ℕ) : ℤ) - ((2 * m : ℕ) : ℤ), 0) = true := by
      rw [s0]; simp
    rw [if_pos this]
    simp
  · intro k hk
    simp only [Finset.mem_range] at hk
    have : state 0 ((k : ℤ) - ((2 * m : ℕ) : ℤ), 0) = false := by
      rw [← Bool.not_eq_true, s0]
      push_cast
      omega
    rw [this]
    simp

theorem geom (N : ℕ) : 9 * ∑ k ∈ Finset.range N, 10 ^ (N + 1 - k) + 100 = 10 ^ (N + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    have e : ∑ k ∈ Finset.range N, 10 ^ (N + 1 + 1 - (k + 1)) =
        ∑ k ∈ Finset.range N, 10 ^ (N + 1 - k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      congr 1
      omega
    rw [e]
    have e2 : N + 1 + 1 - 0 = N + 2 := by omega
    rw [e2, show N + 1 + 2 = (N + 2) + 1 by ring, pow_succ]
    linear_combination ih

theorem a_odd (m : ℕ) : 9 * a (2 * m + 1) + 91 = 10 ^ (2 * m + 2) := by
  unfold a
  rw [odd_state, Finset.sum_range_succ, Finset.sum_range_succ]
  have hlast : state 1 (((2 * m + 1 : ℕ) : ℤ) - ((2 * m + 1 : ℕ) : ℤ), 0) = true := by
    rw [← Bool.not_eq_false, s1]; simp
  have hmid : state 1 (((2 * m : ℕ) : ℤ) - ((2 * m + 1 : ℕ) : ℤ), 0) = false := by
    rw [s1]
    refine Or.inl ⟨?_, rfl⟩
    push_cast
    ring
  rw [if_pos hlast, hmid]
  have hrest : ∑ k ∈ Finset.range (2 * m),
      (if state 1 ((k : ℤ) - ((2 * m + 1 : ℕ) : ℤ), 0) = true then 10 ^ (2 * m + 1 - k) else 0) =
      ∑ k ∈ Finset.range (2 * m), 10 ^ (2 * m + 1 - k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp only [Finset.mem_range] at hk
    have : state 1 ((k : ℤ) - ((2 * m + 1 : ℕ) : ℤ), 0) = true := by
      rw [← Bool.not_eq_false, s1]
      push_cast
      omega
    rw [if_pos this]
  rw [hrest]
  have g := geom (2 * m)
  simp only [Bool.false_eq_true, if_false, Nat.sub_self, pow_zero, add_zero]
  linear_combination g

theorem closed (n : ℕ) :
    (a n : ℚ) = (-41 + 50 * (-1) ^ n - (-2) ^ n * 5 ^ (1 + n) + 2 ^ n * 5 ^ (1 + n)) / 9 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [a_even]
    have he : Even (2 * m) := even_two_mul m
    rw [he.neg_pow, he.neg_pow]
    push_cast
    ring
  · have h := a_odd m
    have h' : (9 : ℚ) * (a (2 * m + 1) : ℚ) + 91 = 10 ^ (2 * m + 2) := by exact_mod_cast h
    have ho : Odd (2 * m + 1) := odd_two_mul_add_one m
    rw [ho.neg_pow, ho.neg_pow, one_pow]
    have e10 : (10 : ℚ) ^ (2 * m + 2) = 2 ^ (2 * m + 1) * 5 ^ (1 + (2 * m + 1)) * 2 := by
      rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      ring
    rw [e10] at h'
    linear_combination h' / 9

theorem rec4 (n : ℕ) : (a (n + 4) : ℚ) - 101 * (a (n + 2) : ℚ) + 100 * (a n : ℚ) = 0 := by
  rw [closed, closed, closed]
  ring

theorem main_proof :
    A = (1 + X - 100 * X ^ 2 + 1000 * X ^ 3) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ ∧
    (∀ n : ℕ,
      (a n : ℚ) = (-41 + 50 * (-1) ^ n - (-2) ^ n * 5 ^ (1 + n) + 2 ^ n * 5 ^ (1 + n)) / 9) := by
  refine ⟨?_, closed⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have hD : ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : ℚ⟦X⟧) =
      1 - C (101 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hN : (1 + X - 100 * X ^ 2 + 1000 * X ^ 3 : ℚ⟦X⟧) =
      X ^ 0 + X ^ 1 - C (100 : ℚ) * X ^ 2 + C (1000 : ℚ) * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_add, map_sub, A]
  rw [mul_comm (PowerSeries.mk _) (C (101 : ℚ) * X ^ 2), mul_comm (PowerSeries.mk _) (C (100 : ℚ) * X ^ 4),
    mul_assoc, mul_assoc]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num [closed]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have r := rec4 m
    simp only [show 2 ≤ m + 4 by omega, show 4 ≤ m + 4 by omega, if_true,
      show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega,
      show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega,
      show m + 4 ≠ 3 by omega, if_false]
    linear_combination r

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a277864.main :=
  OMA.Helpers.main_proof
