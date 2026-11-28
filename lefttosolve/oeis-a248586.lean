import OMAStatements.S_oeis_a248586
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a248586 Finset

/-- The summand. -/
def F (n i : ℕ) : ℤ := (n.choose i : ℤ) * ((2 * i).choose i : ℤ) ^ 2

/-- The telescoping companion. -/
def T (m k : ℕ) : ℤ := (k : ℤ) ^ 3 * ((m + 3).choose k : ℤ) * ((2 * k).choose k : ℤ) ^ 2

theorem a_ext (n N : ℕ) (h : n + 1 ≤ N) : a n = ∑ i ∈ range N, F n i := by
  unfold a F
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hiN hi
    simp only [Finset.mem_range, not_lt] at hiN hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem rel_up (n k : ℕ) :
    ((n : ℤ) + 1) * (n.choose k : ℤ) = ((n : ℤ) + 1 - k) * ((n + 1).choose k : ℤ) := by
  rcases le_or_gt k (n + 1) with h | h
  · have e := Nat.choose_mul_succ_eq n k
    have e' : ((n.choose k * (n + 1) : ℕ) : ℤ) = (((n + 1).choose k * (n + 1 - k) : ℕ) : ℤ) := by
      rw [e]
    push_cast [Nat.cast_sub h] at e'
    linear_combination e'
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt h]
    simp

theorem rel_right (n k : ℕ) :
    ((k : ℤ) + 1) * (n.choose (k + 1) : ℤ) = ((n : ℤ) - k) * (n.choose k : ℤ) := by
  rcases le_or_gt k n with h | h
  · have e := Nat.choose_succ_right_eq n k
    have e' : ((n.choose (k + 1) * (k + 1) : ℕ) : ℤ) = ((n.choose k * (n - k) : ℕ) : ℤ) := by
      rw [e]
    push_cast [Nat.cast_sub h] at e'
    linear_combination e'
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt h]
    simp

theorem rel_central (k : ℕ) :
    ((k : ℤ) + 1) ^ 2 * ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 2 =
      4 * (2 * (k : ℤ) + 1) ^ 2 * ((2 * k).choose k : ℤ) ^ 2 := by
  have e := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at e
  have e' : (((k + 1) * (2 * (k + 1)).choose (k + 1) : ℕ) : ℤ) =
      ((2 * (2 * k + 1) * (2 * k).choose k : ℕ) : ℤ) := by rw [e]
  push_cast at e'
  linear_combination
    (((k : ℤ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℤ) +
      2 * (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ)) * e'

theorem pointwise (m k : ℕ) :
    ((m : ℤ) + 3) * (((m : ℤ) + 3) ^ 2 * F (m + 3) k
      + (-19 * ((m : ℤ) + 3) ^ 2 + 19 * ((m : ℤ) + 3) - 5) * F (m + 2) k
      + 35 * ((m : ℤ) + 2) ^ 2 * F (m + 1) k
      - 17 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * F m k) = T m k - T m (k + 1) := by
  have eY := rel_up (m + 2) k
  have eZ := rel_up (m + 1) k
  have eW := rel_up m k
  have eX1 := rel_right (m + 3) k
  have ec := rel_central k
  push_cast at eY eZ eW eX1
  unfold F T
  push_cast
  set X : ℤ := ((m + 3).choose k : ℤ)
  set Y : ℤ := ((m + 2).choose k : ℤ)
  set Z : ℤ := ((m + 1).choose k : ℤ)
  set W : ℤ := (m.choose k : ℤ)
  set X1 : ℤ := ((m + 3).choose (k + 1) : ℤ)
  set c : ℤ := ((2 * k).choose k : ℤ) ^ 2
  set c1 : ℤ := ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 2
  linear_combination
    ((-19 * ((m : ℤ) + 3) ^ 2 + 19 * ((m : ℤ) + 3) - 5) * c
      + 35 * ((m : ℤ) + 2) * ((m : ℤ) + 2 - k) * c
      - 17 * ((m : ℤ) + 1 - k) * ((m : ℤ) + 2 - k) * c) * eY
    + (35 * ((m : ℤ) + 2) * ((m : ℤ) + 3) * c - 17 * ((m : ℤ) + 3) * ((m : ℤ) + 1 - k) * c) * eZ
    + (-17 * ((m : ℤ) + 3) * ((m : ℤ) + 2) * c) * eW
    + (((k : ℤ) + 1) ^ 2 * c1) * eX1
    + (((m : ℤ) + 3 - k) * X) * ec

end OMA.Helpers

open OMA.Helpers Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a248586.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  rw [a_ext (m + 3) (m + 4) (by omega), a_ext (m + 2) (m + 4) (by omega),
    a_ext (m + 1) (m + 4) (by omega), a_ext m (m + 4) (by omega)]
  have key : ((m : ℤ) + 3) * (((m : ℤ) + 3) ^ 2 * ∑ i ∈ range (m + 4), F (m + 3) i
      + (-19 * ((m : ℤ) + 3) ^ 2 + 19 * ((m : ℤ) + 3) - 5) * ∑ i ∈ range (m + 4), F (m + 2) i
      + 35 * ((m : ℤ) + 2) ^ 2 * ∑ i ∈ range (m + 4), F (m + 1) i
      - 17 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * ∑ i ∈ range (m + 4), F m i) = 0 := by
    have hs : ((m : ℤ) + 3) * (((m : ℤ) + 3) ^ 2 * ∑ i ∈ range (m + 4), F (m + 3) i
        + (-19 * ((m : ℤ) + 3) ^ 2 + 19 * ((m : ℤ) + 3) - 5) * ∑ i ∈ range (m + 4), F (m + 2) i
        + 35 * ((m : ℤ) + 2) ^ 2 * ∑ i ∈ range (m + 4), F (m + 1) i
        - 17 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * ∑ i ∈ range (m + 4), F m i) =
        ∑ i ∈ range (m + 4), (T m i - T m (i + 1)) := by
      rw [← Finset.sum_congr rfl (fun i _ => pointwise m i)]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [hs, Finset.sum_range_sub']
    unfold T
    rw [Nat.choose_eq_zero_of_lt (by omega : m + 3 < m + 4)]
    simp
  have hm : ((m : ℤ) + 3) ≠ 0 := by positivity
  have key' := (mul_eq_zero.mp key).resolve_left hm
  push_cast
  linear_combination key'
