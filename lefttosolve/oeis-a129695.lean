import OMAStatements.S_oeis_a129695
import Mathlib

namespace OMA.Helpers

open Finset

/-- The coefficient `C(n,k) * n! / k!`. -/
noncomputable def cc (n k : ℕ) : ℚ := (n.choose k : ℚ) * (n.factorial : ℚ) / (k.factorial : ℚ)

/-- `PP x n = Sum_{k <= n} C(n,k) n!/k! x^k`. -/
noncomputable def PP (x : ℚ) (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), cc n k * x ^ k

theorem cc_zero_right (n : ℕ) : cc n 0 = (n.factorial : ℚ) := by
  simp [cc]

theorem cc_of_lt {n k : ℕ} (h : n < k) : cc n k = 0 := by
  simp [cc, Nat.choose_eq_zero_of_lt h]

theorem cc_formula (k j : ℕ) :
    cc (k + j) k = ((k + j).factorial : ℚ) ^ 2 / ((k.factorial : ℚ) ^ 2 * (j.factorial : ℚ)) := by
  unfold cc
  rw [Nat.cast_choose ℚ (by omega : k ≤ k + j), show k + j - k = j by omega]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (j.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem cc_self (n : ℕ) : cc n n = 1 := by
  have h := cc_formula n 0
  simp only [Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one] at h
  rw [h]
  exact div_self (by positivity)

theorem cc_step (n k : ℕ) :
    cc (n + 2) (k + 1) = (2 * (n : ℚ) + 3) * cc (n + 1) (k + 1) + cc (n + 1) k
      - ((n : ℚ) + 1) ^ 2 * cc n (k + 1) := by
  rcases Nat.lt_or_ge n (k + 1) with h | h
  · rcases Nat.lt_or_ge (n + 1) k with h2 | h2
    · rw [cc_of_lt (by omega : n + 2 < k + 1), cc_of_lt (by omega : n + 1 < k + 1),
        cc_of_lt (by omega : n + 1 < k), cc_of_lt (by omega : n < k + 1)]
      ring
    · rcases (show k = n ∨ k = n + 1 by omega) with rfl | rfl
      · rw [cc_of_lt (show k < k + 1 by omega), cc_self, show k + 2 = k + 1 + 1 from rfl,
          cc_formula (k + 1) 1, cc_formula k 1]
        simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add,
          Nat.cast_one]
        have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
        have h4 : ((k : ℚ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      · rw [cc_of_lt (show n + 1 < n + 1 + 1 by omega), cc_of_lt (show n < n + 1 + 1 by omega),
          show cc (n + 2) (n + 1 + 1) = 1 from cc_self (n + 2), cc_self (n + 1)]
        ring
  · obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by omega⟩
    rw [show k + 1 + j + 2 = (k + 1) + (j + 2) by ring, cc_formula,
      show k + 1 + j + 1 = (k + 1) + (j + 1) by ring, cc_formula,
      show k + 1 + (j + 1) = k + (j + 2) by ring, cc_formula, cc_formula]
    rw [show k + (j + 2) = (k + j + 1) + 1 by ring,
      show k + 1 + (j + 2) = (k + j + 1) + 1 + 1 by ring,
      show k + 1 + j = k + j + 1 by ring]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((k + j).factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h5 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have h6 : ((j : ℚ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

theorem PP_ext (x : ℚ) (n j : ℕ) : ∑ k ∈ range (n + 1 + j), cc n k * x ^ k = PP x n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, sum_range_succ, ih, cc_of_lt (by omega)]
    ring

theorem PP_rec (x : ℚ) (n : ℕ) :
    PP x (n + 2) = (2 * (n : ℚ) + 3 + x) * PP x (n + 1) - ((n : ℚ) + 1) ^ 2 * PP x n := by
  have e1 : PP x (n + 2) = cc (n + 2) 0 + ∑ k ∈ range (n + 2), cc (n + 2) (k + 1) * x ^ (k + 1) := by
    unfold PP
    rw [sum_range_succ']
    ring
  have e2 : PP x (n + 1) = cc (n + 1) 0 + ∑ k ∈ range (n + 2), cc (n + 1) (k + 1) * x ^ (k + 1) := by
    rw [← PP_ext x (n + 1) 1, show n + 1 + 1 + 1 = (n + 2) + 1 by ring, sum_range_succ']
    ring
  have e3 : PP x n = cc n 0 + ∑ k ∈ range (n + 2), cc n (k + 1) * x ^ (k + 1) := by
    rw [← PP_ext x n 2, show n + 1 + 2 = (n + 2) + 1 by ring, sum_range_succ']
    ring
  have e4 : x * PP x (n + 1) = ∑ k ∈ range (n + 2), cc (n + 1) k * x ^ (k + 1) := by
    unfold PP
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  have e5 : ∑ k ∈ range (n + 2), cc (n + 2) (k + 1) * x ^ (k + 1) =
      (2 * (n : ℚ) + 3) * ∑ k ∈ range (n + 2), cc (n + 1) (k + 1) * x ^ (k + 1)
        + ∑ k ∈ range (n + 2), cc (n + 1) k * x ^ (k + 1)
        - ((n : ℚ) + 1) ^ 2 * ∑ k ∈ range (n + 2), cc n (k + 1) * x ^ (k + 1) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    rw [cc_step]
    ring
  have f2 : cc (n + 2) 0 = ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n.factorial : ℚ) := by
    rw [cc_zero_right, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f1 : cc (n + 1) 0 = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
    rw [cc_zero_right, Nat.factorial_succ]
    push_cast
    ring
  have f0 : cc n 0 = (n.factorial : ℚ) := cc_zero_right n
  rw [e1, e5, ← e4]
  rw [e2, e3, f2, f1, f0]
  ring

theorem J_eq : ∀ k : ℕ, (OMA.S_oeis_a129695.J k : ℚ) = (2 ^ k - (-1) ^ k) / 3
  | 0 => by simp [OMA.S_oeis_a129695.J]
  | 1 => by norm_num [OMA.S_oeis_a129695.J]
  | k + 2 => by
    rw [show OMA.S_oeis_a129695.J (k + 2) =
      OMA.S_oeis_a129695.J (k + 1) + 2 * OMA.S_oeis_a129695.J k from rfl]
    push_cast
    rw [J_eq (k + 1), J_eq k]
    ring

theorem a_eq (n : ℕ) : OMA.S_oeis_a129695.a n = (PP 2 n - PP (-1) n) / 3 := by
  unfold OMA.S_oeis_a129695.a PP cc
  rw [← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro k _
  rw [J_eq]
  ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a129695.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  simp only [a_eq]
  have u2 := PP_rec 2 m
  have u3 := PP_rec 2 (m + 1)
  have u4 := PP_rec 2 (m + 2)
  have v2 := PP_rec (-1) m
  have v3 := PP_rec (-1) (m + 1)
  have v4 := PP_rec (-1) (m + 2)
  rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at u3 v3
  rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at u4 v4
  push_cast at u3 u4 v3 v4 ⊢
  rw [u4, v4, u3, v3, u2, v2]
  ring
