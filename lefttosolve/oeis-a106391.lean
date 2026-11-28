import OMAStatements.S_oeis_a106391
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a106391 Finset

/-- binomial(2j, j+1). -/
def bb (j : ℕ) : ℤ := ((2 * j).choose (j + 1) : ℤ)

/-- Binomial transform of `bb`. -/
def U (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), (n.choose j : ℤ) * bb j

/-- Alternating binomial transform of `bb`. -/
def V (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), (-1) ^ j * (n.choose j : ℤ) * bb j

def TU (m j : ℕ) : ℤ := ((j : ℤ) - 1) * ((j : ℤ) + 1) * ((m + 2).choose j : ℤ) * bb j

def TV (m j : ℕ) : ℤ := ((j : ℤ) - 1) * ((j : ℤ) + 1) * (-1) ^ j * ((m + 2).choose j : ℤ) * bb j

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

theorem rel_b (j : ℕ) :
    (j : ℤ) * ((j : ℤ) + 2) * bb (j + 1) = 2 * ((j : ℤ) + 1) * (2 * (j : ℤ) + 1) * bb j := by
  have h1 := Nat.choose_succ_right_eq (2 * j) j
  have h2 := Nat.choose_succ_right_eq (2 * (j + 1)) (j + 1)
  have h3 := Nat.succ_mul_centralBinom_succ j
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h3
  have e1 : 2 * j - j = j := by omega
  have e2 : 2 * (j + 1) - (j + 1) = j + 1 := by omega
  rw [e1] at h1
  rw [e2] at h2
  have h1' : (((2 * j).choose (j + 1) * (j + 1) : ℕ) : ℤ) = (((2 * j).choose j * j : ℕ) : ℤ) := by
    rw [h1]
  have h2' : (((2 * (j + 1)).choose (j + 1 + 1) * (j + 1 + 1) : ℕ) : ℤ) =
      (((2 * (j + 1)).choose (j + 1) * (j + 1) : ℕ) : ℤ) := by
    rw [h2]
  have h3' : (((j + 1) * (2 * (j + 1)).choose (j + 1) : ℕ) : ℤ) =
      ((2 * (2 * j + 1) * (2 * j).choose j : ℕ) : ℤ) := by
    rw [h3]
  push_cast at h1' h2' h3'
  unfold bb
  linear_combination (j : ℤ) * h2' + (j : ℤ) * h3' - 2 * (2 * (j : ℤ) + 1) * h1'

theorem pointU (m j : ℕ) :
    ((m : ℤ) + 1) * ((m : ℤ) + 3) * (((m + 2).choose j : ℤ) * bb j)
      - 3 * ((m : ℤ) + 2) * (2 * (m : ℤ) + 3) * (((m + 1).choose j : ℤ) * bb j)
      + 5 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * ((m.choose j : ℤ) * bb j) = TU m j - TU m (j + 1) := by
  have eY := rel_up (m + 1) j
  have eZ := rel_up m j
  have eX1 := rel_right (m + 2) j
  have eb := rel_b j
  push_cast at eY eZ eX1
  unfold TU
  push_cast
  linear_combination
    ((-3 * (2 * (m : ℤ) + 3) + 5 * ((m : ℤ) + 1 - j)) * bb j) * eY
    + (5 * ((m : ℤ) + 2) * bb j) * eZ
    + (2 * (2 * (j : ℤ) + 1) * bb j) * eX1
    + (((m + 2).choose (j + 1) : ℤ)) * eb

theorem pointV (m j : ℕ) :
    -((m : ℤ) + 1) * ((m : ℤ) + 3) * ((-1) ^ j * ((m + 2).choose j : ℤ) * bb j)
      - ((m : ℤ) + 2) * (2 * (m : ℤ) + 3) * ((-1) ^ j * ((m + 1).choose j : ℤ) * bb j)
      + 3 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * ((-1) ^ j * (m.choose j : ℤ) * bb j) =
      TV m (j + 1) - TV m j := by
  have eY := rel_up (m + 1) j
  have eZ := rel_up m j
  have eX1 := rel_right (m + 2) j
  have eb := rel_b j
  push_cast at eY eZ eX1
  unfold TV
  push_cast
  linear_combination
    ((-1) ^ j * (-(2 * (m : ℤ) + 3) + 3 * ((m : ℤ) + 1 - j)) * bb j) * eY
    + ((-1) ^ j * 3 * ((m : ℤ) + 2) * bb j) * eZ
    + ((-1) ^ j * 2 * (2 * (j : ℤ) + 1) * bb j) * eX1
    + ((-1) ^ j * ((m + 2).choose (j + 1) : ℤ)) * eb

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a106391 Finset

theorem U_ext (n N : ℕ) (h : n + 1 ≤ N) : U n = ∑ j ∈ range N, (n.choose j : ℤ) * bb j := by
  unfold U
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hiN hi
    simp only [Finset.mem_range, not_lt] at hiN hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem V_ext (n N : ℕ) (h : n + 1 ≤ N) :
    V n = ∑ j ∈ range N, (-1) ^ j * (n.choose j : ℤ) * bb j := by
  unfold V
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hiN hi
    simp only [Finset.mem_range, not_lt] at hiN hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem LU (m : ℕ) :
    ((m : ℤ) + 1) * ((m : ℤ) + 3) * U (m + 2)
      - 3 * ((m : ℤ) + 2) * (2 * (m : ℤ) + 3) * U (m + 1)
      + 5 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * U m = 0 := by
  rw [U_ext (m + 2) (m + 3) (by omega), U_ext (m + 1) (m + 3) (by omega),
    U_ext m (m + 3) (by omega)]
  have hs : ((m : ℤ) + 1) * ((m : ℤ) + 3) * ∑ j ∈ range (m + 3), ((m + 2).choose j : ℤ) * bb j
      - 3 * ((m : ℤ) + 2) * (2 * (m : ℤ) + 3) * ∑ j ∈ range (m + 3), ((m + 1).choose j : ℤ) * bb j
      + 5 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * ∑ j ∈ range (m + 3), (m.choose j : ℤ) * bb j =
      ∑ j ∈ range (m + 3), (TU m j - TU m (j + 1)) := by
    rw [← Finset.sum_congr rfl (fun j _ => pointU m j)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [hs, Finset.sum_range_sub']
  unfold TU bb
  rw [Nat.choose_eq_zero_of_lt (by omega : m + 2 < m + 3)]
  simp

theorem LV (m : ℕ) :
    -((m : ℤ) + 1) * ((m : ℤ) + 3) * V (m + 2)
      - ((m : ℤ) + 2) * (2 * (m : ℤ) + 3) * V (m + 1)
      + 3 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * V m = 0 := by
  rw [V_ext (m + 2) (m + 3) (by omega), V_ext (m + 1) (m + 3) (by omega),
    V_ext m (m + 3) (by omega)]
  have hs : -((m : ℤ) + 1) * ((m : ℤ) + 3) *
        ∑ j ∈ range (m + 3), (-1) ^ j * ((m + 2).choose j : ℤ) * bb j
      - ((m : ℤ) + 2) * (2 * (m : ℤ) + 3) *
        ∑ j ∈ range (m + 3), (-1) ^ j * ((m + 1).choose j : ℤ) * bb j
      + 3 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * ∑ j ∈ range (m + 3), (-1) ^ j * (m.choose j : ℤ) * bb j =
      ∑ j ∈ range (m + 3), (TV m (j + 1) - TV m j) := by
    rw [← Finset.sum_congr rfl (fun j _ => pointV m j)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [hs, Finset.sum_range_sub]
  unfold TV bb
  rw [Nat.choose_eq_zero_of_lt (by omega : m + 2 < m + 3)]
  simp

theorem par_sum (g : ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ range (N + 1), g i * (1 + (-1) ^ i) = 2 * ∑ k ∈ range (N / 2 + 1), g (2 * k) := by
  induction N with
  | zero =>
    simp only [Nat.zero_div, zero_add, Finset.sum_range_one, pow_zero, mul_zero]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd N with ⟨t, ht⟩ | ⟨t, ht⟩
    · have e1 : (N + 1) / 2 = N / 2 := by omega
      have e2 : (-1 : ℤ) ^ (N + 1) = -1 := by
        rw [ht, show t + t + 1 = 2 * t + 1 by omega, pow_succ, pow_mul]; norm_num
      rw [e1, e2]; ring
    · have e1 : (N + 1) / 2 = N / 2 + 1 := by omega
      have e2 : (-1 : ℤ) ^ (N + 1) = 1 := by
        rw [ht, show 2 * t + 1 + 1 = 2 * (t + 1) by omega, pow_mul]; norm_num
      have e3 : 2 * (N / 2 + 1) = N + 1 := by omega
      rw [e1, Finset.sum_range_succ _ (N / 2 + 1), e2, e3]; ring

theorem two_a (n : ℕ) : 2 * a n = U n + (-1) ^ n * V n := by
  have h1 : U n + (-1) ^ n * V n =
      ∑ j ∈ range (n + 1), (n.choose j : ℤ) * bb j * (1 + (-1) ^ n * (-1) ^ j) := by
    unfold U V
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2 : ∑ j ∈ range (n + 1), (n.choose j : ℤ) * bb j * (1 + (-1) ^ n * (-1) ^ j) =
      ∑ i ∈ range (n + 1), (n.choose i : ℤ) * bb (n - i) * (1 + (-1) ^ i) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have e : n + 1 - 1 - i = n - i := by omega
    rw [e, Nat.choose_symm (by omega)]
    have hs : (-1 : ℤ) ^ n * (-1) ^ (n - i) = (-1) ^ i := by
      rw [← pow_add]
      obtain ⟨d, hd⟩ : ∃ d, n = i + d := ⟨n - i, by omega⟩
      subst hd
      rw [show i + d - i = d by omega, show i + d + d = i + 2 * d by ring, pow_add, pow_mul]
      norm_num
    rw [hs]
  rw [h1, h2, par_sum (fun i => (n.choose i : ℤ) * bb (n - i)) n]
  unfold a bb
  rfl

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a106391

theorem R2U (m : ℕ) :
    (-(((m:ℤ) + 4) - 2)*(((m:ℤ) + 4) + 1)*(4*((m:ℤ) + 4)^2 - 16*((m:ℤ) + 4) + 19)) * U (m + 4) + (8*((m:ℤ) + 4)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 14*((m:ℤ) + 4) + 13)) * U (m + 3) + (-2*(28*((m:ℤ) + 4)^4 - 168*((m:ℤ) + 4)^3 + 375*((m:ℤ) + 4)^2 - 401*((m:ℤ) + 4) + 180)) * U (m + 2) + (-8*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^3 - 18*((m:ℤ) + 4)^2 + 27*((m:ℤ) + 4) - 10)) * U (m + 1) + (15*(((m:ℤ) + 4) - 3)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 8*((m:ℤ) + 4) + 7)) * U m = 0 := by
  have h0 := LU (m + 2)
  rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at h0
  push_cast at h0
  have h1 := LU (m + 1)
  rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h1
  push_cast at h1
  have h2 := LU m
  have hD : ((m:ℤ) + 3) * ((-(((m:ℤ) + 4) - 2)*(((m:ℤ) + 4) + 1)*(4*((m:ℤ) + 4)^2 - 16*((m:ℤ) + 4) + 19)) * U (m + 4) + (8*((m:ℤ) + 4)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 14*((m:ℤ) + 4) + 13)) * U (m + 3) + (-2*(28*((m:ℤ) + 4)^4 - 168*((m:ℤ) + 4)^3 + 375*((m:ℤ) + 4)^2 - 401*((m:ℤ) + 4) + 180)) * U (m + 2) + (-8*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^3 - 18*((m:ℤ) + 4)^2 + 27*((m:ℤ) + 4) - 10)) * U (m + 1) + (15*(((m:ℤ) + 4) - 3)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 8*((m:ℤ) + 4) + 7)) * U m) = 0 := by
    linear_combination (-(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 16*((m:ℤ) + 4) + 19)) * h0 + (8*((m:ℤ) + 4)^3 - 36*((m:ℤ) + 4)^2 + 54*((m:ℤ) + 4) - 47) * h1 + (3*(((m:ℤ) + 4) - 1)*(4*((m:ℤ) + 4)^2 - 8*((m:ℤ) + 4) + 7)) * h2
  have hDne : ((m:ℤ) + 3) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hD).resolve_left hDne

theorem R2V (m : ℕ) :
    (-(((m:ℤ) + 4) - 2)*(((m:ℤ) + 4) + 1)*(4*((m:ℤ) + 4)^2 - 16*((m:ℤ) + 4) + 19)) * V (m + 4) + (-8*((m:ℤ) + 4)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 14*((m:ℤ) + 4) + 13)) * V (m + 3) + (-2*(28*((m:ℤ) + 4)^4 - 168*((m:ℤ) + 4)^3 + 375*((m:ℤ) + 4)^2 - 401*((m:ℤ) + 4) + 180)) * V (m + 2) + (8*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^3 - 18*((m:ℤ) + 4)^2 + 27*((m:ℤ) + 4) - 10)) * V (m + 1) + (15*(((m:ℤ) + 4) - 3)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 8*((m:ℤ) + 4) + 7)) * V m = 0 := by
  have h0 := LV (m + 2)
  rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at h0
  push_cast at h0
  have h1 := LV (m + 1)
  rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h1
  push_cast at h1
  have h2 := LV m
  have hD : ((m:ℤ) + 3) * ((-(((m:ℤ) + 4) - 2)*(((m:ℤ) + 4) + 1)*(4*((m:ℤ) + 4)^2 - 16*((m:ℤ) + 4) + 19)) * V (m + 4) + (-8*((m:ℤ) + 4)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 14*((m:ℤ) + 4) + 13)) * V (m + 3) + (-2*(28*((m:ℤ) + 4)^4 - 168*((m:ℤ) + 4)^3 + 375*((m:ℤ) + 4)^2 - 401*((m:ℤ) + 4) + 180)) * V (m + 2) + (8*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^3 - 18*((m:ℤ) + 4)^2 + 27*((m:ℤ) + 4) - 10)) * V (m + 1) + (15*(((m:ℤ) + 4) - 3)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 8*((m:ℤ) + 4) + 7)) * V m) = 0 := by
    linear_combination ((((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 16*((m:ℤ) + 4) + 19)) * h0 + (24*((m:ℤ) + 4)^3 - 108*((m:ℤ) + 4)^2 + 162*((m:ℤ) + 4) - 85) * h1 + (5*(((m:ℤ) + 4) - 1)*(4*((m:ℤ) + 4)^2 - 8*((m:ℤ) + 4) + 7)) * h2
  have hDne : ((m:ℤ) + 3) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hD).resolve_left hDne

theorem R1U (m : ℕ) :
    (-(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) + 1)) * U (m + 6) + (4*((m:ℤ) + 6)*(3*((m:ℤ) + 6) - 7)) * U (m + 5) + (-49*((m:ℤ) + 6)^2 + 193*((m:ℤ) + 6) - 148) * U (m + 4) + (8*(((m:ℤ) + 6) - 4)*(9*((m:ℤ) + 6) - 19)) * U (m + 3) + (5*((m:ℤ) + 6)^2 + 115*((m:ℤ) + 6) - 418) * U (m + 2) + (-12*(((m:ℤ) + 6) - 4)*(7*((m:ℤ) + 6) - 19)) * U (m + 1) + (45*(((m:ℤ) + 6) - 5)*(((m:ℤ) + 6) - 4)) * U m = 0 := by
  have h0 := LU (m + 4)
  rw [show m + 4 + 2 = m + 6 from rfl, show m + 4 + 1 = m + 5 from rfl] at h0
  push_cast at h0
  have h1 := LU (m + 3)
  rw [show m + 3 + 2 = m + 5 from rfl, show m + 3 + 1 = m + 4 from rfl] at h1
  push_cast at h1
  have h2 := LU (m + 2)
  rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at h2
  push_cast at h2
  have h3 := LU (m + 1)
  rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h3
  push_cast at h3
  have h4 := LU m
  have hD : (((m:ℤ) + 3) * ((m:ℤ) + 4) * ((m:ℤ) + 5)) * ((-(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) + 1)) * U (m + 6) + (4*((m:ℤ) + 6)*(3*((m:ℤ) + 6) - 7)) * U (m + 5) + (-49*((m:ℤ) + 6)^2 + 193*((m:ℤ) + 6) - 148) * U (m + 4) + (8*(((m:ℤ) + 6) - 4)*(9*((m:ℤ) + 6) - 19)) * U (m + 3) + (5*((m:ℤ) + 6)^2 + 115*((m:ℤ) + 6) - 418) * U (m + 2) + (-12*(((m:ℤ) + 6) - 4)*(7*((m:ℤ) + 6) - 19)) * U (m + 1) + (45*(((m:ℤ) + 6) - 5)*(((m:ℤ) + 6) - 4)) * U m) = 0 := by
    linear_combination (-(((m:ℤ) + 6) - 3)*(((m:ℤ) + 6) - 2)^2) * h0 + ((((m:ℤ) + 6) - 3)*(6*((m:ℤ) + 6)^2 - 25*((m:ℤ) + 6) + 22)) * h1 + (-(((m:ℤ) + 6) - 1)*(8*((m:ℤ) + 6)^2 - 59*((m:ℤ) + 6) + 98)) * h2 + (-3*(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) - 1)*(2*((m:ℤ) + 6) + 1)) * h3 + (9*(((m:ℤ) + 6) - 3)*(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) - 1)) * h4
  have hDne : (((m:ℤ) + 3) * ((m:ℤ) + 4) * ((m:ℤ) + 5)) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hD).resolve_left hDne

theorem R1V (m : ℕ) :
    (-(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) + 1)) * V (m + 6) + (-4*((m:ℤ) + 6)*(3*((m:ℤ) + 6) - 7)) * V (m + 5) + (-49*((m:ℤ) + 6)^2 + 193*((m:ℤ) + 6) - 148) * V (m + 4) + (-8*(((m:ℤ) + 6) - 4)*(9*((m:ℤ) + 6) - 19)) * V (m + 3) + (5*((m:ℤ) + 6)^2 + 115*((m:ℤ) + 6) - 418) * V (m + 2) + (12*(((m:ℤ) + 6) - 4)*(7*((m:ℤ) + 6) - 19)) * V (m + 1) + (45*(((m:ℤ) + 6) - 5)*(((m:ℤ) + 6) - 4)) * V m = 0 := by
  have h0 := LV (m + 4)
  rw [show m + 4 + 2 = m + 6 from rfl, show m + 4 + 1 = m + 5 from rfl] at h0
  push_cast at h0
  have h1 := LV (m + 3)
  rw [show m + 3 + 2 = m + 5 from rfl, show m + 3 + 1 = m + 4 from rfl] at h1
  push_cast at h1
  have h2 := LV (m + 2)
  rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at h2
  push_cast at h2
  have h3 := LV (m + 1)
  rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h3
  push_cast at h3
  have h4 := LV m
  have hD : (((m:ℤ) + 3) * ((m:ℤ) + 4) * ((m:ℤ) + 5)) * ((-(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) + 1)) * V (m + 6) + (-4*((m:ℤ) + 6)*(3*((m:ℤ) + 6) - 7)) * V (m + 5) + (-49*((m:ℤ) + 6)^2 + 193*((m:ℤ) + 6) - 148) * V (m + 4) + (-8*(((m:ℤ) + 6) - 4)*(9*((m:ℤ) + 6) - 19)) * V (m + 3) + (5*((m:ℤ) + 6)^2 + 115*((m:ℤ) + 6) - 418) * V (m + 2) + (12*(((m:ℤ) + 6) - 4)*(7*((m:ℤ) + 6) - 19)) * V (m + 1) + (45*(((m:ℤ) + 6) - 5)*(((m:ℤ) + 6) - 4)) * V m) = 0 := by
    linear_combination ((((m:ℤ) + 6) - 3)*(((m:ℤ) + 6) - 2)^2) * h0 + ((((m:ℤ) + 6) - 3)*(10*((m:ℤ) + 6)^2 - 35*((m:ℤ) + 6) + 26)) * h1 + ((((m:ℤ) + 6) - 1)*(32*((m:ℤ) + 6)^2 - 171*((m:ℤ) + 6) + 218)) * h2 + ((((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) - 1)*(38*((m:ℤ) + 6) - 121)) * h3 + (15*(((m:ℤ) + 6) - 3)*(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) - 1)) * h4
  have hDne : (((m:ℤ) + 3) * ((m:ℤ) + 4) * ((m:ℤ) + 5)) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hD).resolve_left hDne

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a106391.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega]
    push_cast
    have hU := R1U m
    have hV := R1V m
    have a0 := two_a m
    have a1 := two_a (m + 1)
    have a2 := two_a (m + 2)
    have a3 := two_a (m + 3)
    have a4 := two_a (m + 4)
    have a5 := two_a (m + 5)
    have a6 := two_a (m + 6)
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    rw [mul_zero]
    linear_combination (-(((m:ℤ) + 6) - 2)*(((m:ℤ) + 6) + 1)) * a6 + (4*((m:ℤ) + 6)*(3*((m:ℤ) + 6) - 7)) * a5 + (-49*((m:ℤ) + 6)^2 + 193*((m:ℤ) + 6) - 148) * a4 + (8*(((m:ℤ) + 6) - 4)*(9*((m:ℤ) + 6) - 19)) * a3 + (5*((m:ℤ) + 6)^2 + 115*((m:ℤ) + 6) - 418) * a2 + (-12*(((m:ℤ) + 6) - 4)*(7*((m:ℤ) + 6) - 19)) * a1 + (45*(((m:ℤ) + 6) - 5)*(((m:ℤ) + 6) - 4)) * a0 + hU + (-1) ^ m * hV
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
    push_cast
    have hU := R2U m
    have hV := R2V m
    have a0 := two_a m
    have a1 := two_a (m + 1)
    have a2 := two_a (m + 2)
    have a3 := two_a (m + 3)
    have a4 := two_a (m + 4)
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    rw [mul_zero]
    linear_combination (-(((m:ℤ) + 4) - 2)*(((m:ℤ) + 4) + 1)*(4*((m:ℤ) + 4)^2 - 16*((m:ℤ) + 4) + 19)) * a4 + (8*((m:ℤ) + 4)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 14*((m:ℤ) + 4) + 13)) * a3 + (-2*(28*((m:ℤ) + 4)^4 - 168*((m:ℤ) + 4)^3 + 375*((m:ℤ) + 4)^2 - 401*((m:ℤ) + 4) + 180)) * a2 + (-8*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^3 - 18*((m:ℤ) + 4)^2 + 27*((m:ℤ) + 4) - 10)) * a1 + (15*(((m:ℤ) + 4) - 3)*(((m:ℤ) + 4) - 2)*(4*((m:ℤ) + 4)^2 - 8*((m:ℤ) + 4) + 7)) * a0 + hU + (-1) ^ m * hV

