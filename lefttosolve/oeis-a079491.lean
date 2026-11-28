import OMAStatements.S_oeis_a079491
import Mathlib

namespace OMA.Helpers

def S79491 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * 2 ^ (k * (n - k) + Nat.choose k 2)

theorem choose_two_add (j m : ℕ) :
    Nat.choose (j + m) 2 = Nat.choose j 2 + Nat.choose m 2 + j * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ', ih, Nat.choose_succ_succ' m 1]
    simp
    ring

theorem key79491 (n : ℕ) :
    OMA.S_oeis_a079491.ratSum n * 2 ^ (Nat.choose n 2) = (S79491 n : ℚ) := by
  unfold OMA.S_oeis_a079491.ratSum S79491
  rw [Finset.sum_mul]
  push_cast
  rw [← Finset.sum_range_reflect (fun k => (Nat.choose n k : ℚ) * 2 ^ (k * (n - k) + Nat.choose k 2))]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simp at hk; omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk'
  have h1 : k + m + 1 - 1 - k = m := by omega
  have h2 : k + m - m = k := by omega
  rw [h1, h2, ← Nat.choose_two_right, choose_two_add, Nat.choose_symm_add]
  rw [pow_add, pow_add]
  field_simp
  ring

theorem odd79491 (n : ℕ) (hn : 2 ≤ n) : Odd (S79491 n) := by
  unfold S79491
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.zero_mul, Nat.choose_zero_succ, Nat.add_zero, pow_zero,
    Nat.mul_one]
  apply Even.add_one
  apply Finset.even_sum
  intro k hk
  have hk' : k < n := by simpa using hk
  have hne : (k + 1) * (n - (k + 1)) + Nat.choose (k + 1) 2 ≠ 0 := by
    intro h
    have ha : (k + 1) * (n - (k + 1)) = 0 := by omega
    have hb : Nat.choose (k + 1) 2 = 0 := by omega
    rw [Nat.choose_eq_zero_iff] at hb
    rcases Nat.mul_eq_zero.mp ha with h3 | h3 <;> omega
  apply Even.mul_left
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [he, pow_succ]
  exact Even.mul_left even_two _

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a079491.main := by
  intro n
  have hpos : (0 : ℚ) < 2 ^ (Nat.choose n 2) := by positivity
  have hr : OMA.S_oeis_a079491.ratSum n = ((S79491 n : ℤ) : ℚ) / ((2 ^ (Nat.choose n 2) : ℤ) : ℚ) := by
    push_cast
    rw [eq_div_iff hpos.ne', ← key79491]
  rw [hr, Rat.num_div_eq_of_coprime]
  · rfl
  · positivity
  · simp only [Int.natAbs_natCast, Int.natAbs_pow]
    rcases Nat.lt_or_ge n 2 with h | h
    · have : Nat.choose n 2 = 0 := Nat.choose_eq_zero_iff.mpr h
      rw [this]; simp
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_two_right).mpr (odd79491 n h))
