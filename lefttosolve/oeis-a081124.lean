import OMAStatements.S_oeis_a081124
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a081124

theorem sum_ext (f : ℕ → ℤ) (K L : ℕ) (h : K ≤ L) (hf : ∀ k, K ≤ k → f k = 0) :
    ∑ k ∈ Finset.range L, f k = ∑ k ∈ Finset.range K, f k := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 h) ?_).symm
  intro k hk hk'
  simp only [Finset.mem_range, not_lt] at hk hk'
  exact hf k hk'

theorem sum_even_odd (f : ℕ → ℤ) (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M), f k = ∑ j ∈ Finset.range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- Odd part with bound `M`. -/
def Ob (M n : ℕ) : ℤ := ∑ j ∈ Finset.range M, (Nat.choose n (2 * j + 1) : ℤ) * (Nat.factorial j : ℤ)

/-- Even part with bound `M`. -/
def Eb (M n : ℕ) : ℤ := ∑ j ∈ Finset.range M, (Nat.choose n (2 * j) : ℤ) * (Nat.factorial j : ℤ)

/-- Auxiliary sum. -/
def Tb (M n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range M, (Nat.choose n (2 * j + 1) : ℤ) * (Nat.factorial (j + 1) : ℤ)

theorem a_eq_Ob (n M : ℕ) (hM : n + 1 ≤ M) : a n = Ob M (n + 1) := by
  unfold a Ob
  have h1 : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * (Nat.factorial (k / 2) : ℤ) =
      ∑ k ∈ Finset.range (2 * M), (Nat.choose n k : ℤ) * (Nat.factorial (k / 2) : ℤ) := by
    refine (sum_ext _ _ _ (by omega) ?_).symm
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [h1, sum_even_odd]
  refine Finset.sum_congr rfl ?_
  intro j _
  have e1 : 2 * j / 2 = j := by omega
  have e2 : (2 * j + 1) / 2 = j := by omega
  rw [e1, e2, Nat.choose_succ_succ' n (2 * j)]
  push_cast
  ring

theorem Ob_succ (M n : ℕ) : Ob M (n + 1) = Ob M n + Eb M n := by
  unfold Ob Eb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Nat.choose_succ_succ' n (2 * j)]
  push_cast
  ring

theorem Eb_succ (M n : ℕ) : Eb (M + 1) (n + 1) = Eb (M + 1) n + Tb M n := by
  unfold Eb Tb
  rw [Finset.sum_range_succ', Finset.sum_range_succ', add_assoc, add_comm _ (∑ j ∈ _, _),
    ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.choose_succ_succ' n (2 * j + 1)]
    push_cast
    ring
  · simp

theorem Tb_succ (M n : ℕ) : 2 * Tb M (n + 1) = ((n : ℤ) + 1) * Eb M n + Ob M (n + 1) := by
  unfold Tb Eb Ob
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  have h := Nat.add_one_mul_choose_eq n (2 * j)
  have h' : ((n : ℤ) + 1) * (Nat.choose n (2 * j) : ℤ) =
      (Nat.choose (n + 1) (2 * j + 1) : ℤ) * (2 * j + 1) := by exact_mod_cast h
  rw [Nat.factorial_succ]
  push_cast
  linear_combination -(Nat.factorial j : ℤ) * h'

theorem Eb_ext (M n : ℕ) (h : n < 2 * M) : Eb (M + 1) n = Eb M n := by
  unfold Eb
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt h]
  simp

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a081124.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  set M := m + 10 with hM
  rw [a_eq_Ob (m + 3) M (by omega), a_eq_Ob (m + 2) M (by omega), a_eq_Ob (m + 1) M (by omega),
    a_eq_Ob m M (by omega)]
  have A1 := Ob_succ M (m + 1)
  have A2 := Ob_succ M (m + 2)
  have A3 := Ob_succ M (m + 3)
  have B := Eb_succ M (m + 2)
  have C := Tb_succ M (m + 1)
  rw [Eb_ext M (m + 3) (by omega), Eb_ext M (m + 2) (by omega)] at B
  push_cast at C ⊢
  linear_combination 2 * A3 - 2 * A2 + 2 * B + C - ((m : ℤ) + 2) * A1
