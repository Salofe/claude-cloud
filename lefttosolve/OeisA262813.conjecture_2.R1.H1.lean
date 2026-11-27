import OMAReductions.R_OeisA262813_conjecture_2_R1

/-!
# Step H1 of the reduction OeisA262813.conjecture_2.R1

At each of the seven indices 1, 9, 21, 35, 98, 152 and 306 the count `OeisA262813.a` equals one.

Only the upstream definition `OeisA262813.a` is used. The helper lemma below truncates the three
summation ranges to explicit bounds `X`, `Y`, `Z` beyond which every summand vanishes (because
`x ^ 3`, `y ^ 2` or the triangular number alone already exceeds `n`). The truncated sums are small
and are evaluated by the kernel.
-/

namespace OMA.Helpers

theorem a262813_triangular_mono {a b : ℕ} (h : a ≤ b) : Nat.triangular a ≤ Nat.triangular b := by
  unfold Nat.triangular
  exact Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1))

/-- Truncation of the three sums defining `OeisA262813.a`. -/
theorem a262813_trunc (n X Y Z : ℕ) (hX : X ≤ n + 1) (hY : Y ≤ n + 1) (hZ1 : 1 ≤ Z)
    (hZ : Z ≤ n + 1) (hx : n < X ^ 3) (hy : n < Y ^ 2) (hz : n < Nat.triangular Z) :
    OeisA262813.a n = ∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.Ico 1 Z,
        (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0) := by
  unfold OeisA262813.a
  rw [← Finset.sum_range_add_sum_Ico _ hX]
  have h1 : ∑ x ∈ Finset.Ico X (n + 1), ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.Ico 1 (n + 1),
      (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hxm
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro z _
    have hxX : X ≤ x := (Finset.mem_Ico.mp hxm).1
    have : X ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hxX 3
    have hne : x ^ 3 + y ^ 2 + Nat.triangular z ≠ n := by omega
    simp [hne]
  rw [h1, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_range_add_sum_Ico _ hY]
  have h2 : ∑ y ∈ Finset.Ico Y (n + 1), ∑ z ∈ Finset.Ico 1 (n + 1),
      (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y hym
    apply Finset.sum_eq_zero
    intro z _
    have hyY : Y ≤ y := (Finset.mem_Ico.mp hym).1
    have : Y ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hyY 2
    have hne : x ^ 3 + y ^ 2 + Nat.triangular z ≠ n := by omega
    simp [hne]
  rw [h2, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_Ico_consecutive _ hZ1 hZ]
  have h3 : ∑ z ∈ Finset.Ico Z (n + 1),
      (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro z hzm
    have hzZ : Z ≤ z := (Finset.mem_Ico.mp hzm).1
    have : Nat.triangular Z ≤ Nat.triangular z := a262813_triangular_mono hzZ
    have hne : x ^ 3 + y ^ 2 + Nat.triangular z ≠ n := by omega
    simp [hne]
  rw [h3, Nat.add_zero]

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA262813_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h <;> subst h
  · rw [OMA.Helpers.a262813_trunc 1 2 2 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    decide +kernel
  · rw [OMA.Helpers.a262813_trunc 9 3 4 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    decide +kernel
  · rw [OMA.Helpers.a262813_trunc 21 3 5 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    decide +kernel
  · rw [OMA.Helpers.a262813_trunc 35 4 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    decide +kernel
  · rw [OMA.Helpers.a262813_trunc 98 5 10 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    decide +kernel
  · rw [OMA.Helpers.a262813_trunc 152 6 13 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    decide +kernel
  · rw [OMA.Helpers.a262813_trunc 306 7 18 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    decide +kernel
