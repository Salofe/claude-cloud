import OMAStatements.S_oeis_a082382
import Mathlib
namespace OMA.Helpers

open OMA.S_oeis_a082382

theorem a082382_step (n : ℕ) :
    sumSqDigits n = n % 10 * (n % 10) + sumSqDigits (n / 10) := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp [sumSqDigits]
  · unfold sumSqDigits
    rw [Nat.digits_def' (by norm_num) hn]
    simp

/-- The digit square sum of a number below `1000`, written with three digits. -/
def a082382_g3 (n : ℕ) : ℕ :=
  n % 10 * (n % 10) + (n / 10 % 10 * (n / 10 % 10) + n / 10 / 10 % 10 * (n / 10 / 10 % 10))

theorem a082382_sq_le (d : ℕ) : d % 10 * (d % 10) ≤ 81 := by
  have h : d % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have h9 : d % 10 ≤ 9 := by omega
  calc d % 10 * (d % 10) ≤ 9 * 9 := Nat.mul_le_mul h9 h9
    _ = 81 := by norm_num

theorem a082382_eq_g3 (n : ℕ) (h : n < 1000) : sumSqDigits n = a082382_g3 n := by
  rw [a082382_step n, a082382_step (n / 10), a082382_step (n / 10 / 10)]
  have h0 : n / 10 / 10 / 10 = 0 := by omega
  rw [h0]
  simp [a082382_g3, sumSqDigits]

theorem a082382_g3_le (n : ℕ) : a082382_g3 n ≤ 243 := by
  unfold a082382_g3
  have := a082382_sq_le n
  have := a082382_sq_le (n / 10)
  have := a082382_sq_le (n / 10 / 10)
  omega

theorem a082382_iter (k n : ℕ) (h : n < 1000) :
    sumSqDigits^[k] n = a082382_g3^[k] n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, a082382_eq_g3 n h]
    exact ih _ (by have := a082382_g3_le n; omega)

/-- `true` when the `a082382_g3` orbit of `n` hits `1` or `4` within `k` steps. -/
def a082382_reach : ℕ → ℕ → Bool
  | 0, n => n == 1 || n == 4
  | k + 1, n => n == 1 || n == 4 || a082382_reach k (a082382_g3 n)

theorem a082382_reach_sound (k n : ℕ) (h : a082382_reach k n = true) :
    ∃ j, a082382_g3^[j] n = 1 ∨ a082382_g3^[j] n = 4 := by
  induction k generalizing n with
  | zero =>
    simp only [a082382_reach, Bool.or_eq_true, beq_iff_eq] at h
    exact ⟨0, h⟩
  | succ k ih =>
    simp only [a082382_reach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
    · obtain ⟨j, hj⟩ := ih _ h
      exact ⟨j + 1, by rwa [Function.iterate_succ_apply]⟩

theorem a082382_base : ∀ n < 1000, n = 0 ∨ a082382_reach 16 n = true := by
  decide +kernel

theorem a082382_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ sumSqDigits n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [a082382_step n]
    by_cases h : n % 10 = 0
    · have h1 : 1 ≤ n / 10 := by omega
      have := ih (n / 10) (by omega) h1
      omega
    · have h1 : 1 ≤ n % 10 := by omega
      have : 1 ≤ n % 10 * (n % 10) := Nat.mul_le_mul h1 h1
      omega

theorem a082382_lt (n : ℕ) (hn : 1000 ≤ n) : sumSqDigits n < n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [a082382_step n]
    have hd := a082382_sq_le n
    by_cases h : n / 10 < 1000
    · rw [a082382_eq_g3 _ h]
      have := a082382_g3_le (n / 10)
      omega
    · have := ih (n / 10) (by omega) (by omega)
      omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a082382.main := by
  intro n hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 1000
    · rcases a082382_base n h with h0 | hr
      · omega
      · obtain ⟨j, hj⟩ := a082382_reach_sound _ _ hr
        exact ⟨j, by rw [a082382_iter j n h]; exact hj⟩
    · obtain ⟨k, hk⟩ := ih (OMA.S_oeis_a082382.sumSqDigits n)
        (a082382_lt n (by omega)) (a082382_pos n hn)
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
