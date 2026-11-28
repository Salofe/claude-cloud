import OMAStatements.S_oeis_a000262
import Mathlib

namespace OMA.Helpers

open Finset

/-- The summand `k! * C(n,k) * C(n+1,k)`; it is the Lah number `L(n+1, n+1-k)`. -/
def lahT (n k : ℕ) : ℕ := Nat.factorial k * Nat.choose n k * Nat.choose (n + 1) k

theorem lahT_eq (n k : ℕ) : lahT n k = Nat.choose n k * (n + 1).descFactorial k := by
  rw [lahT, Nat.descFactorial_eq_factorial_mul_choose]
  ring

theorem lahT_zero (n : ℕ) : lahT n 0 = 1 := by simp [lahT]

theorem lahT_eq_zero {n k : ℕ} (h : n < k) : lahT n k = 0 := by
  simp [lahT, Nat.choose_eq_zero_of_lt h]

/-- The Lah recurrence for the reversed triangle. -/
theorem lahT_succ_succ (n k : ℕ) :
    (lahT (n + 1) (k + 1) : ℤ) = (2 * (n : ℤ) + 2 - k) * lahT n k + lahT n (k + 1) := by
  rcases Nat.lt_or_ge n k with h | h
  · rw [lahT_eq_zero h, lahT_eq_zero (by omega : n < k + 1), lahT_eq_zero (by omega : n + 1 < k + 1)]
    simp
  · rw [lahT_eq, lahT_eq, lahT_eq, Nat.choose_succ_succ, show n + 1 + 1 = (n + 1) + 1 by rfl,
      Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
    have key := Nat.choose_succ_right_eq n k
    have hk : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := Nat.cast_sub h
    have hk' : ((n + 1 - k : ℕ) : ℤ) = (n : ℤ) + 1 - k := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have key' : (Nat.choose n (k + 1) : ℤ) * (k + 1) = (Nat.choose n k : ℤ) * ((n : ℤ) - k) := by
      rw [← hk]
      exact_mod_cast key
    push_cast
    rw [hk']
    linear_combination ((n + 1).descFactorial k : ℤ) * key'

/-- The reversed Lah vector: `V n j = L(n, n - j)`. -/
def V : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, j => lahT n j

theorem V_zero_right (n : ℕ) : V n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ n => exact lahT_zero n

theorem V_eq_zero {n j : ℕ} (h : n < j) : V n j = 0 := by
  cases n with
  | zero => simp [V]; omega
  | succ n => exact lahT_eq_zero (by omega)

theorem V_succ_succ (n j : ℕ) :
    (V (n + 1) (j + 1) : ℤ) = (2 * (n : ℤ) - j) * V n j + V n (j + 1) := by
  cases n with
  | zero =>
    simp only [V]
    rw [lahT_eq_zero (by omega : 0 < j + 1)]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp
    · simp [show j ≠ 0 by omega]
  | succ m =>
    simp only [V]
    rw [lahT_succ_succ]
    push_cast
    ring

theorem a_eq_sum (n : ℕ) :
    (OMA.S_oeis_a000262.a n : ℤ) = ∑ j ∈ range (n + 1), (V n j : ℤ) := by
  cases n with
  | zero => simp [OMA.S_oeis_a000262.a, V]
  | succ n =>
    rw [Finset.sum_range_succ, show V (n + 1) (n + 1) = 0 from lahT_eq_zero (by omega)]
    simp only [OMA.S_oeis_a000262.a, V, lahT, Nat.cast_sum, Nat.cast_zero, add_zero]

theorem sum_extend (n m : ℕ) (h : n + 1 ≤ m) :
    ∑ j ∈ range m, (V n j : ℤ) = ∑ j ∈ range (n + 1), (V n j : ℤ) := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr h)
  intro j _ hj
  rw [Finset.mem_range, not_lt] at hj
  rw [V_eq_zero (by omega)]
  simp

theorem base (k j : ℕ) : ((k + 1 : ℕ) : ℤ) ∣ (V (k + 1) j : ℤ) - V 0 j := by
  cases j with
  | zero => simp [V_zero_right]
  | succ i =>
    simp only [V, if_neg (Nat.succ_ne_zero i), Nat.cast_zero, sub_zero]
    have : lahT k (i + 1) = Nat.choose k (i + 1) * ((k + 1) * k.descFactorial i) := by
      rw [lahT_eq, Nat.succ_descFactorial_succ]
    rw [this]
    exact Int.natCast_dvd_natCast.mpr ⟨Nat.choose k (i + 1) * k.descFactorial i, by ring⟩

theorem period (k : ℕ) (n : ℕ) : ∀ j : ℕ, ((k + 1 : ℕ) : ℤ) ∣ (V (n + (k + 1)) j : ℤ) - V n j := by
  induction n with
  | zero =>
    intro j
    simpa using base k j
  | succ n ih =>
    intro j
    cases j with
    | zero => simp [V_zero_right]
    | succ i =>
      rw [show n + 1 + (k + 1) = (n + (k + 1)) + 1 by ring, V_succ_succ, V_succ_succ]
      have h1 := ih i
      have h2 := ih (i + 1)
      have e : (2 * ((n + (k + 1) : ℕ) : ℤ) - i) * V (n + (k + 1)) i + V (n + (k + 1)) (i + 1) -
          ((2 * (n : ℤ) - i) * V n i + V n (i + 1)) =
          (2 * ((n + (k + 1) : ℕ) : ℤ) - i) * ((V (n + (k + 1)) i : ℤ) - V n i) +
          2 * ((k + 1 : ℕ) : ℤ) * V n i + ((V (n + (k + 1)) (i + 1) : ℤ) - V n (i + 1)) := by
        push_cast
        ring
      rw [e]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_right h1 _) ⟨2 * (V n i : ℤ), by ring⟩) h2

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a000262.main := by
  intro k hk n
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.modEq_iff_dvd, OMA.Helpers.a_eq_sum, OMA.Helpers.a_eq_sum,
    ← OMA.Helpers.sum_extend n (n + (k + 1) + 1) (by omega), ← Finset.sum_sub_distrib]
  rw [← dvd_neg, ← Finset.sum_neg_distrib]
  apply Finset.dvd_sum
  intro j _
  rw [neg_sub]
  exact OMA.Helpers.period k n j
