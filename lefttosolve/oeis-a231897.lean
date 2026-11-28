import OMAStatements.S_oeis_a231897
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a231897

theorem wt_double (k : ℕ) : wt (2 * k) = wt k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · unfold wt
    rw [Nat.digits_def' (by norm_num) (by omega)]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k) / 2 = k := by omega
    rw [h1, h2, List.sum_cons, zero_add]

theorem wt_double_add_one (k : ℕ) : wt (2 * k + 1) = wt k + 1 := by
  unfold wt
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, List.sum_cons, add_comm]

theorem wt_pow_mul (j x : ℕ) : wt (2 ^ j * x) = wt x := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc, wt_double, ih]

theorem wt_mersenne (a : ℕ) : wt (2 ^ a - 1) = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have hp : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have e : 2 ^ (a + 1) - 1 = 2 * (2 ^ a - 1) + 1 := by
      rw [pow_succ]; omega
    rw [e, wt_double_add_one, ih]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a231897.main := by
  intro n
  rcases n with _ | a
  · exact ⟨0, rfl⟩
  · refine ⟨2 ^ (a + 1) - 1, ?_⟩
    have hp : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have key : (2 ^ (a + 1) - 1) ^ 2 = 2 * (2 ^ (a + 1) * (2 ^ a - 1)) + 1 := by
      obtain ⟨s, hs⟩ : ∃ s, 2 ^ a = s + 1 := ⟨2 ^ a - 1, by omega⟩
      rw [pow_succ (2 : ℕ) a, hs]
      have e1 : (s + 1) * 2 - 1 = 2 * s + 1 := by omega
      have e2 : s + 1 - 1 = s := by omega
      rw [e1, e2]; ring
    rw [key, wt_double_add_one, wt_pow_mul, wt_mersenne]
