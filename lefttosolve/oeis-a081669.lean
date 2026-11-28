import OMAStatements.S_oeis_a081669
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a081669

/-- The summand `C(n, 2m) C(2m, m)`. -/
def Fn (n m : ℕ) : ℕ := Nat.choose n (2 * m) * Nat.choose (2 * m) m

theorem Fn_zero (n : ℕ) : Fn n 0 = 1 := by simp [Fn]

theorem Fn_eq_zero {n m : ℕ} (h : n < 2 * m) : Fn n m = 0 := by
  simp [Fn, Nat.choose_eq_zero_of_lt h]

theorem Fq (k m : ℕ) : (Fn (k + 2 * m) m : ℚ) =
    ((k + 2 * m).factorial : ℚ) / ((k.factorial : ℚ) * (m.factorial : ℚ) * (m.factorial : ℚ)) := by
  have h1 := Nat.cast_choose ℚ (show 2 * m ≤ k + 2 * m by omega)
  have h2 := Nat.cast_choose ℚ (show m ≤ 2 * m by omega)
  rw [show k + 2 * m - 2 * m = k by omega] at h1
  rw [show 2 * m - m = m by omega] at h2
  unfold Fn
  push_cast
  rw [h1, h2]
  have : ((2 * m).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem key (n j : ℕ) :
    ((n + 2 : ℕ) : ℚ) * (Fn (n + 2) (j + 1) : ℚ) + ((n + 1 : ℕ) : ℚ) * (Fn n (j + 1) : ℚ) =
      ((2 * n + 3 : ℕ) : ℚ) * (Fn (n + 1) (j + 1) : ℚ) + 4 * ((n + 1 : ℕ) : ℚ) * (Fn n j : ℚ) := by
  have fk : ∀ k : ℕ, (k.factorial : ℚ) ≠ 0 := fun k => by exact_mod_cast Nat.factorial_ne_zero _
  by_cases h0 : 2 * j + 2 ≤ n
  · obtain ⟨k, hk⟩ : ∃ k, n = k + 2 * (j + 1) := ⟨n - 2 * j - 2, by omega⟩
    have hA : (Fn (n + 2) (j + 1) : ℚ) = ((k + 2 * j + 4).factorial : ℚ) /
        (((k + 2).factorial : ℚ) * ((j + 1).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
      rw [show n + 2 = (k + 2) + 2 * (j + 1) by omega, Fq, show k + 2 + 2 * (j + 1) = k + 2 * j + 4 by omega]
    have hB : (Fn (n + 1) (j + 1) : ℚ) = ((k + 2 * j + 3).factorial : ℚ) /
        (((k + 1).factorial : ℚ) * ((j + 1).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
      rw [show n + 1 = (k + 1) + 2 * (j + 1) by omega, Fq, show k + 1 + 2 * (j + 1) = k + 2 * j + 3 by omega]
    have hC : (Fn n (j + 1) : ℚ) = ((k + 2 * j + 2).factorial : ℚ) /
        ((k.factorial : ℚ) * ((j + 1).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
      rw [hk, Fq, show k + 2 * (j + 1) = k + 2 * j + 2 by omega]
    have hD : (Fn n j : ℚ) = ((k + 2 * j + 2).factorial : ℚ) /
        (((k + 2).factorial : ℚ) * (j.factorial : ℚ) * (j.factorial : ℚ)) := by
      rw [show n = (k + 2) + 2 * j by omega, Fq, show k + 2 + 2 * j = k + 2 * j + 2 by omega]
    rw [hA, hB, hC, hD, hk]
    simp only [Nat.factorial_succ]
    push_cast
    have := fk k
    have := fk j
    have := fk (k + 2 * j)
    field_simp
    ring
  · rcases (show n = 2 * j + 1 ∨ n = 2 * j ∨ n < 2 * j by omega) with h | h | h
    · have hA : (Fn (n + 2) (j + 1) : ℚ) = ((2 * j + 3).factorial : ℚ) /
          ((1 : ℚ) * ((j + 1).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
        rw [show n + 2 = 1 + 2 * (j + 1) by omega, Fq, show 1 + 2 * (j + 1) = 2 * j + 3 by omega]
        simp
      have hB : (Fn (n + 1) (j + 1) : ℚ) = ((2 * j + 2).factorial : ℚ) /
          ((1 : ℚ) * ((j + 1).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
        rw [show n + 1 = 0 + 2 * (j + 1) by omega, Fq, show 0 + 2 * (j + 1) = 2 * j + 2 by omega]
        simp
      have hC : (Fn n (j + 1) : ℚ) = 0 := by rw [Fn_eq_zero (by omega)]; simp
      have hD : (Fn n j : ℚ) = ((2 * j + 1).factorial : ℚ) /
          ((1 : ℚ) * (j.factorial : ℚ) * (j.factorial : ℚ)) := by
        rw [show n = 1 + 2 * j by omega, Fq, show 1 + 2 * j = 2 * j + 1 by omega]
        simp
      rw [hA, hB, hC, hD, h]
      simp only [Nat.factorial_succ]
      push_cast
      have := fk j
      have := fk (2 * j)
      field_simp
      ring
    · have hA : (Fn (n + 2) (j + 1) : ℚ) = ((2 * j + 2).factorial : ℚ) /
          ((1 : ℚ) * ((j + 1).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
        rw [show n + 2 = 0 + 2 * (j + 1) by omega, Fq, show 0 + 2 * (j + 1) = 2 * j + 2 by omega]
        simp
      have hB : (Fn (n + 1) (j + 1) : ℚ) = 0 := by rw [Fn_eq_zero (by omega)]; simp
      have hC : (Fn n (j + 1) : ℚ) = 0 := by rw [Fn_eq_zero (by omega)]; simp
      have hD : (Fn n j : ℚ) = ((2 * j).factorial : ℚ) /
          ((1 : ℚ) * (j.factorial : ℚ) * (j.factorial : ℚ)) := by
        rw [show n = 0 + 2 * j by omega, Fq, show 0 + 2 * j = 2 * j by omega]
        simp
      rw [hA, hB, hC, hD, h]
      simp only [Nat.factorial_succ]
      push_cast
      have := fk j
      have := fk (2 * j)
      field_simp
      ring
    · rw [Fn_eq_zero (by omega), Fn_eq_zero (by omega), Fn_eq_zero (by omega),
        Fn_eq_zero (show n < 2 * j by omega)]
      simp

theorem keyN (n j : ℕ) :
    (n + 2) * Fn (n + 2) (j + 1) + (n + 1) * Fn n (j + 1) =
      (2 * n + 3) * Fn (n + 1) (j + 1) + 4 * (n + 1) * Fn n j := by
  have h := key n j
  exact_mod_cast h

/-- The central trinomial part of `a`. -/
def Tz (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n / 2 + 1), (Nat.choose n (2 * m) : ℤ) * (Nat.choose (2 * m) m : ℤ)

theorem a_eq (n : ℕ) : a n = 2 ^ n + Tz n := rfl

theorem Tz_eq (n M : ℕ) (h : n / 2 + 1 ≤ M) : Tz n = ∑ m ∈ Finset.range M, (Fn n m : ℤ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range d, (Fn n (n / 2 + 1 + x) : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [Fn_eq_zero (by omega)]
    simp
  rw [hz, add_zero]
  unfold Tz Fn
  push_cast
  rfl

theorem TR (n : ℕ) :
    ((n : ℤ) + 2) * Tz (n + 2) = (2 * (n : ℤ) + 3) * Tz (n + 1) + 3 * ((n : ℤ) + 1) * Tz n := by
  rw [Tz_eq (n + 2) (n + 4) (by omega), Tz_eq (n + 1) (n + 4) (by omega)]
  have e1 := Tz_eq n (n + 4) (by omega)
  have e2 := Tz_eq n (n + 3) (by omega)
  have hsum : ∑ m ∈ Finset.range (n + 4), (((n : ℤ) + 2) * (Fn (n + 2) m : ℤ) + ((n : ℤ) + 1) * (Fn n m : ℤ)) =
      ∑ m ∈ Finset.range (n + 4), ((2 * (n : ℤ) + 3) * (Fn (n + 1) m : ℤ)) +
        4 * ((n : ℤ) + 1) * ∑ m ∈ Finset.range (n + 3), (Fn n m : ℤ) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun m => (2 * (n : ℤ) + 3) * (Fn (n + 1) m : ℤ)),
      Finset.mul_sum]
    have hs1 : ∑ j ∈ Finset.range (n + 3),
        (((n : ℤ) + 2) * (Fn (n + 2) (j + 1) : ℤ) + ((n : ℤ) + 1) * (Fn n (j + 1) : ℤ)) =
        ∑ j ∈ Finset.range (n + 3),
        ((2 * (n : ℤ) + 3) * (Fn (n + 1) (j + 1) : ℤ) + 4 * ((n : ℤ) + 1) * (Fn n j : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j _
      have := keyN n j
      have h' : (((n + 2) * Fn (n + 2) (j + 1) + (n + 1) * Fn n (j + 1) : ℕ) : ℤ) =
          (((2 * n + 3) * Fn (n + 1) (j + 1) + 4 * (n + 1) * Fn n j : ℕ) : ℤ) := by
        rw [this]
      push_cast at h'
      linear_combination h'
    simp only [Finset.sum_add_distrib] at hs1 ⊢
    simp only [Fn_zero]
    push_cast
    linear_combination hs1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← e1, ← e2] at hsum
  linear_combination hsum

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a081669.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  simp only [a_eq]
  have h0 := TR k
  have h1 := TR (k + 1)
  have h2 := TR (k + 2)
  push_cast at h0 h1 h2 ⊢
  rw [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring] at h1
  rw [show k + 2 + 1 = k + 3 by ring, show k + 2 + 2 = k + 4 by ring] at h2
  linear_combination h2 - 4 * h1 + 4 * h0
