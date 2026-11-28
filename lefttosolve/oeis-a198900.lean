import OMAStatements.S_oeis_a198900
import Mathlib

namespace OMA.Helpers

open Finset

/-- Number of extensions from a state with `t + 2` introduced colors; it does not depend on
the last row, as long as that row is proper. -/
def a198900F : ℕ → ℕ → ℤ
  | 0, _ => 1
  | n+1, t => (((t+1 : ℕ) : ℤ) + ((t*t : ℕ) : ℤ)) * a198900F n t +
      (if t+2 < 5 then 2 * ((t+1 : ℕ) : ℤ) * a198900F n (t+1) else 0) +
      (if t+3 < 5 then a198900F n (t+2) else 0)

theorem a198900_ext (n : ℕ) : ∀ t a b : ℕ, a ≠ b → a < t+2 → b < t+2 →
    OMA.S_oeis_a198900.extensions 5 n t a b = a198900F n t := by
  induction n with
  | zero => intro t a b _ _ _; rfl
  | succ n ih =>
    intro t a b hab ha hb
    have hbm : b ∈ range (t+2) := mem_range.2 hb
    have ham : a ∈ range (t+2) := mem_range.2 ha
    have h1 : ∑ y ∈ (range (t+2)).erase b, OMA.S_oeis_a198900.extensions 5 n t b y =
        ((t+1 : ℕ) : ℤ) * a198900F n t := by
      rw [sum_congr rfl (fun y hy => ih t b y (Ne.symm (mem_erase.1 hy).1) hb
        (mem_range.1 (mem_erase.1 hy).2))]
      rw [sum_const, card_erase_of_mem hbm, card_range, nsmul_eq_mul]
      simp
    have h2 : ∑ x ∈ ((range (t+2)).erase a).erase b, ∑ y ∈ ((range (t+2)).erase b).erase x,
        OMA.S_oeis_a198900.extensions 5 n t x y = ((t*t : ℕ) : ℤ) * a198900F n t := by
      have hin : ∀ x ∈ ((range (t+2)).erase a).erase b,
          ∑ y ∈ ((range (t+2)).erase b).erase x, OMA.S_oeis_a198900.extensions 5 n t x y =
            (t : ℤ) * a198900F n t := by
        intro x hx
        have hxb : x ≠ b := (mem_erase.1 hx).1
        have hxr : x < t+2 := mem_range.1 (mem_erase.1 (mem_erase.1 hx).2).2
        have hxm : x ∈ (range (t+2)).erase b := mem_erase.2 ⟨hxb, mem_range.2 hxr⟩
        rw [sum_congr rfl (fun y hy => ih t x y (Ne.symm (mem_erase.1 hy).1) hxr
          (mem_range.1 (mem_erase.1 (mem_erase.1 hy).2).2))]
        rw [sum_const, card_erase_of_mem hxm, card_erase_of_mem hbm, card_range, nsmul_eq_mul]
        simp
      rw [sum_congr rfl hin, sum_const, card_erase_of_mem (mem_erase.2 ⟨Ne.symm hab, hbm⟩),
        card_erase_of_mem ham, card_range, nsmul_eq_mul]
      push_cast
      ring
    have h3 : ∑ y ∈ (range (t+2)).erase b, OMA.S_oeis_a198900.extensions 5 n (t+1) (t+2) y =
        ((t+1 : ℕ) : ℤ) * a198900F n (t+1) := by
      rw [sum_congr rfl (fun y hy => ih (t+1) (t+2) y
        (by have := mem_range.1 (mem_erase.1 hy).2; omega) (by omega)
        (by have := mem_range.1 (mem_erase.1 hy).2; omega))]
      rw [sum_const, card_erase_of_mem hbm, card_range, nsmul_eq_mul]
      simp
    have h4 : ∑ x ∈ (range (t+2)).erase a, OMA.S_oeis_a198900.extensions 5 n (t+1) x (t+2) =
        ((t+1 : ℕ) : ℤ) * a198900F n (t+1) := by
      rw [sum_congr rfl (fun x hx => ih (t+1) x (t+2)
        (by have := mem_range.1 (mem_erase.1 hx).2; omega)
        (by have := mem_range.1 (mem_erase.1 hx).2; omega) (by omega))]
      rw [sum_const, card_erase_of_mem ham, card_range, nsmul_eq_mul]
      simp
    have h5 : OMA.S_oeis_a198900.extensions 5 n (t+2) (t+2) (t+3) = a198900F n (t+2) :=
      ih (t+2) (t+2) (t+3) (by omega) (by omega) (by omega)
    rw [OMA.S_oeis_a198900.extensions]
    rw [h1, h2, h3, h4, h5, a198900F]
    split_ifs <;> push_cast <;> ring

theorem a198900_F3 (n : ℕ) : a198900F n 3 = 13 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [a198900F, ih]; norm_num; ring

theorem a198900_F2 (n : ℕ) : a198900F n 2 = 13 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [a198900F, ih, a198900_F3]; norm_num; ring

theorem a198900_F1 (n : ℕ) : 2 * a198900F n 1 = 3 ^ n + 13 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a198900F, a198900_F2, a198900_F3]
    norm_num
    linear_combination 3 * ih

theorem a198900_F0 (n : ℕ) : 6 * a198900F n 0 = 2 + 3 ^ (n+1) + 13 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a198900F, a198900_F2]
    norm_num
    linear_combination ih + 6 * a198900_F1 n

theorem a198900_closed (m : ℕ) :
    78 * OMA.S_oeis_a198900.sequence (m+1) = 26 + 13*3^(m+1) + 13^(m+1) := by
  have h : OMA.S_oeis_a198900.sequence (m+1) = a198900F m 0 :=
    a198900_ext m 0 0 1 (by omega) (by omega) (by omega)
  rw [h]
  linear_combination 13 * a198900_F0 m

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a198900.main := by
  refine ⟨OMA.Helpers.a198900_closed, ?_⟩
  intro n
  have c := OMA.Helpers.a198900_closed
  have s0 : OMA.S_oeis_a198900.sequence 0 = 0 := rfl
  match n with
  | 0 => simp [OMA.S_oeis_a198900.delayed, OMA.S_oeis_a198900.numerator, s0]
  | 1 =>
    have e0 := c 0
    norm_num at e0
    simp [OMA.S_oeis_a198900.delayed, OMA.S_oeis_a198900.numerator, s0]
    omega
  | 2 =>
    have e0 := c 0
    have e1 := c 1
    norm_num at e0 e1
    simp [OMA.S_oeis_a198900.delayed, OMA.S_oeis_a198900.numerator, s0]
    omega
  | 3 =>
    have e0 := c 0
    have e1 := c 1
    have e2 := c 2
    norm_num at e0 e1 e2
    simp [OMA.S_oeis_a198900.delayed, OMA.S_oeis_a198900.numerator, s0]
    omega
  | k+4 =>
    have e0 := c (k+3)
    have e1 := c (k+2)
    have e2 := c (k+1)
    have e3 := c k
    simp only [OMA.S_oeis_a198900.delayed, OMA.S_oeis_a198900.numerator,
      if_pos (show 0 ≤ k+4 by omega), if_pos (show 1 ≤ k+4 by omega),
      if_pos (show 2 ≤ k+4 by omega), if_pos (show 3 ≤ k+4 by omega),
      show k+4-0 = k+3+1 by omega, show k+4-1 = k+2+1 by omega,
      show k+4-2 = k+1+1 by omega, show k+4-3 = k+1 by omega,
      if_neg (show k+4 ≠ 1 by omega), if_neg (show k+4 ≠ 2 by omega),
      if_neg (show k+4 ≠ 3 by omega)]
    have h78 : (78 : ℤ) * (OMA.S_oeis_a198900.sequence (k+3+1) -
        17 * OMA.S_oeis_a198900.sequence (k+2+1) +
        55 * OMA.S_oeis_a198900.sequence (k+1+1) - 39 * OMA.S_oeis_a198900.sequence (k+1)) = 0 := by
      linear_combination e0 - 17 * e1 + 55 * e2 - 39 * e3
    have := mul_eq_zero.1 h78
    rcases this with h | h
    · norm_num at h
    · exact h

