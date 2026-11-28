import OMAStatements.S_oeis_a265428
import Mathlib

/-!
Rule 188 from a single ON cell: after `t` steps the ON cells are the origin and the cells
`1 ≤ i ≤ t` with `i + t` not congruent to `3` modulo `4`. Hence `a (n + 4) = a n + 3`, which
gives the closed form, the recurrence and the generating function.
-/

namespace OMA.Helpers
open OMA.S_oeis_a265428

theorem rule_eq (l c r : Bool) : rule l c r = (!l && c || l && (!c || r)) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem state_iff (t : ℕ) (i : ℤ) :
    state t i = true ↔ (i = 0 ∨ (1 ≤ i ∧ i ≤ t ∧ (i + t) % 4 ≠ 3)) := by
  induction t generalizing i with
  | zero =>
    simp only [state, decide_eq_true_eq]
    omega
  | succ t ih =>
    simp only [state, rule_eq, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      ih, Bool.eq_false_iff, ne_eq]
    push_cast
    omega

/-- Indicator of the residues other than `3` modulo `4`. -/
def h (x : ℕ) : ℕ := if x % 4 = 3 then 0 else 1

/-- `H n` counts the ON cells strictly right of the origin in row `n`. -/
def H (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, h (n + 1 + j)

theorem a_eq (n : ℕ) : a n = 1 + H n := by
  unfold a H
  rw [show 2 * n + 1 = n + (n + 1) by ring, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range n, (if state n ((x : ℤ) - n) then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    have : state n ((x : ℤ) - n) = false := by
      rw [Bool.eq_false_iff, ne_eq, state_iff]
      omega
    simp [this]
  rw [h1, zero_add, Finset.sum_range_succ', add_comm]
  congr 1
  · have e : (((n + 0 : ℕ) : ℤ) - n) = 0 := by push_cast; ring
    have : state n 0 = true := by rw [state_iff]; omega
    rw [e, this]; rfl
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have e : (((n + (j + 1) : ℕ) : ℤ) - n) = (j : ℤ) + 1 := by push_cast; ring
    rw [e]
    unfold h
    by_cases hc : (n + 1 + j) % 4 = 3
    · have : state n ((j : ℤ) + 1) = false := by
        rw [Bool.eq_false_iff, ne_eq, state_iff]; omega
      rw [this, if_pos hc]; rfl
    · have : state n ((j : ℤ) + 1) = true := by
        rw [state_iff]; omega
      rw [this, if_neg hc]; rfl

theorem sum_four (c m : ℕ) :
    ∑ j ∈ Finset.range (m + 4), h (c + j) = ∑ j ∈ Finset.range m, h (c + j) + 3 := by
  simp only [show m + 4 = m + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ]
  unfold h
  split_ifs <;> omega

theorem H_add_four (n : ℕ) : H (n + 4) = H n + 3 := by
  unfold H
  rw [show n + 4 + 1 = n + 1 + 4 by ring, sum_four]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold h
  rw [show n + 1 + 4 + j = (n + 1 + j) + 4 by ring, Nat.add_mod_right]

theorem a_add_four (n : ℕ) : a (n + 4) = a n + 3 := by
  rw [a_eq, a_eq, H_add_four]; ring

theorem a_small : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 4 := by
  simp only [a_eq, H, h]
  decide

/-- Barker's closed form, as a function of `n`. -/
noncomputable def F (n : ℕ) : ℂ := (1 / 8) * (6 * (n : ℂ) - 3 * (-1) ^ n +
      (1 - Complex.I) * (-Complex.I) ^ n + (1 + Complex.I) * Complex.I ^ n + 9)

theorem F_add_four (n : ℕ) : F (n + 4) = F n + 3 := by
  unfold F
  have h1 : (-1 : ℂ) ^ 4 = 1 := by norm_num
  have h2 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h3 : (-Complex.I) ^ 4 = 1 := by rw [neg_pow, Complex.I_pow_four]; norm_num
  rw [pow_add, pow_add, pow_add, h1, h2, h3]
  push_cast
  ring

theorem F_small : F 0 = 1 ∧ F 1 = 2 ∧ F 2 = 2 ∧ F 3 = 4 := by
  unfold F
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  refine ⟨?_, ?_, ?_, ?_⟩
  · push_cast; ring
  · push_cast; ring_nf; rw [h2]; ring
  · push_cast; ring_nf; rw [h2]; ring
  · push_cast; ring_nf; rw [Complex.I_pow_four]; ring

theorem closed (n : ℕ) : (a n : ℂ) = F n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with hn | hn
    · obtain ⟨a0, a1, a2, a3⟩ := a_small
      obtain ⟨f0, f1, f2, f3⟩ := F_small
      interval_cases n
      · rw [a0, f0]; norm_num
      · rw [a1, f1]; norm_num
      · rw [a2, f2]; norm_num
      · rw [a3, f3]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [a_add_four, F_add_four, ← ih m (by omega)]
      push_cast; ring

end OMA.Helpers

open OMA.S_oeis_a265428 OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a265428.main := by
  refine ⟨fun n => closed n, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have e1 : m + 5 - 1 = m + 4 := by omega
    have e4 : m + 5 - 4 = m + 1 := by omega
    have e5 : m + 5 - 5 = m := by omega
    rw [e1, e4, e5, show m + 5 = (m + 1) + 4 by ring, a_add_four, a_add_four]
    push_cast; ring
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    obtain ⟨a0, a1, a2, a3⟩ := a_small
    have e1 : (PowerSeries.mk (fun n => (a n : ℚ))) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2))
        = PowerSeries.mk (fun n => (a n : ℚ)) - PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1
          - PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4
          + PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5 := by ring
    have e2 : (1 + X + 2 * X ^ 3 - X ^ 4 : PowerSeries ℚ)
        = X ^ 0 + X ^ 1 + PowerSeries.C (2 : ℚ) * X ^ 3 - X ^ 4 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
    simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge k 5 with hk | hk
    · interval_cases k <;> simp [a0, a1, a2, a3, a_add_four] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
      have c1 : 1 ≤ m + 5 := by omega
      have c4 : 4 ≤ m + 5 := by omega
      have c5 : 5 ≤ m + 5 := by omega
      have d0 : m + 5 ≠ 0 := by omega
      have d1 : m + 5 ≠ 1 := by omega
      have d3 : m + 5 ≠ 3 := by omega
      have d4 : m + 5 ≠ 4 := by omega
      simp only [c1, c4, c5, d0, d1, d3, d4, if_true, if_false]
      rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 4 = m + 1 by omega,
        show m + 5 - 5 = m by omega, show m + 5 = (m + 1) + 4 by ring, a_add_four, a_add_four]
      push_cast; ring
