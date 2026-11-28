import OMAStatements.S_oeis_a116408
import Mathlib

namespace OMA.Helpers

open Polynomial

/-- `1 + X + X^2`. -/
noncomputable def qq : ℚ[X] := 1 + X + X ^ 2

/-- The trinomial coefficient: the coefficient of `X^(n+k)` in `(1 + X + X^2)^n`. -/
noncomputable def TT (n k : ℕ) : ℚ := (qq ^ n).coeff (n + k)

theorem coeff_qq_mul (p : ℚ[X]) (m : ℕ) :
    (qq * p).coeff (m + 2) = p.coeff (m + 2) + p.coeff (m + 1) + p.coeff m := by
  unfold qq
  rw [add_mul, add_mul, one_mul, coeff_add, coeff_add,
    show m + 2 = (m + 1) + 1 from rfl, coeff_X_mul, show m + 1 + 1 = m + 2 from rfl,
    coeff_X_pow_mul]

theorem TT_succ (n k : ℕ) : TT (n + 1) (k + 1) = TT n k + TT n (k + 1) + TT n (k + 2) := by
  unfold TT
  rw [pow_succ', show n + 1 + (k + 1) = (n + k) + 2 by ring, coeff_qq_mul,
    show n + k + 2 = n + (k + 2) by ring, show n + k + 1 = n + (k + 1) by ring]
  ring

theorem deriv_qq : derivative qq = 1 + 2 * X := by
  unfold qq
  rw [derivative_add, derivative_add, derivative_one, derivative_X, derivative_X_pow]
  rw [show ((2 : ℕ) : ℚ) = (2 : ℚ) by norm_num, map_ofNat]
  ring

theorem key_poly (n : ℕ) : qq * derivative (qq ^ n) = C (n : ℚ) * (1 + 2 * X) * qq ^ n := by
  rw [derivative_pow, deriv_qq]
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    ring

theorem deriv_rel (n m : ℕ) :
    ((m : ℚ) + 3) * (qq ^ n).coeff (m + 3) + ((m : ℚ) + 2) * (qq ^ n).coeff (m + 2)
      + ((m : ℚ) + 1) * (qq ^ n).coeff (m + 1)
      = (n : ℚ) * ((qq ^ n).coeff (m + 2) + 2 * (qq ^ n).coeff (m + 1)) := by
  have h : (qq * derivative (qq ^ n)).coeff (m + 2)
      = (C (n : ℚ) * (1 + 2 * X) * qq ^ n).coeff (m + 2) := by rw [key_poly]
  rw [coeff_qq_mul, coeff_derivative, coeff_derivative, coeff_derivative] at h
  have e : C (n : ℚ) * (1 + 2 * X) * qq ^ n = C (n : ℚ) * qq ^ n + C (2 * (n : ℚ)) * (X * qq ^ n) := by
    rw [C_mul, map_ofNat]
    ring
  rw [e, coeff_add, coeff_C_mul, coeff_C_mul, show m + 2 = (m + 1) + 1 from rfl, coeff_X_mul] at h
  push_cast at h
  rw [show m + 2 + 1 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h
  linear_combination h

theorem coeff_qq_pow_zero (k : ℕ) : (qq ^ 0).coeff k = if k = 0 then 1 else 0 := by
  simp [coeff_one]

theorem qq_coeff0 : qq.coeff 0 = 1 := by simp [qq]
theorem qq_coeff1 : qq.coeff 1 = 1 := by simp [qq, coeff_X, coeff_one]
theorem qq_coeff2 : qq.coeff 2 = 1 := by simp [qq, coeff_X, coeff_one]

/-- Symmetry `T(n+1,-1) = T(n+1,1)`. -/
theorem qq_symm (n : ℕ) : (qq ^ (n + 1)).coeff n = (qq ^ (n + 1)).coeff (n + 2) := by
  rcases n with _ | n
  · simp [qq_coeff0, qq_coeff2]
  · have h := deriv_rel (n + 2) n
    have hpos : ((n : ℚ) + 3) ≠ 0 := by positivity
    rw [show n + 1 + 1 = n + 2 from rfl, show n + 1 + 2 = n + 3 from rfl]
    push_cast at h
    apply mul_left_cancel₀ hpos
    linear_combination -h

theorem TT_zero_succ (n : ℕ) : TT (n + 1) 0 = TT n 0 + 2 * TT n 1 := by
  rcases n with _ | n
  · simp [TT, qq_coeff1, coeff_one]
  · have h1 := coeff_qq_mul (qq ^ (n + 1)) n
    have h2 := qq_symm n
    show (qq ^ (n + 2)).coeff (n + 2) = (qq ^ (n + 1)).coeff (n + 1)
      + 2 * (qq ^ (n + 1)).coeff (n + 2)
    rw [show qq ^ (n + 2) = qq * qq ^ (n + 1) by ring, h1, ← h2]
    ring

theorem TT_two (n : ℕ) : TT n 2 = ((n : ℚ) * TT n 0 - TT n 1) / ((n : ℚ) + 2) := by
  have hpos : ((n : ℚ) + 2) ≠ 0 := by positivity
  rw [eq_div_iff hpos]
  rcases n with _ | n
  · simp [TT, coeff_one]
  · have h := deriv_rel (n + 1) n
    unfold TT
    rw [show n + 1 + 2 = n + 3 by ring, show n + 1 + 0 = n + 1 by ring,
      show n + 1 + 1 = n + 2 by ring]
    push_cast at h ⊢
    linear_combination h

theorem TT_three (n : ℕ) : TT n 3 = (((n : ℚ) - 1) * TT n 1 - 2 * TT n 2) / ((n : ℚ) + 3) := by
  have hpos : ((n : ℚ) + 3) ≠ 0 := by positivity
  rw [eq_div_iff hpos]
  have h := deriv_rel n n
  unfold TT
  linear_combination h

theorem TT_four (n : ℕ) : TT n 4 = (((n : ℚ) - 2) * TT n 2 - 3 * TT n 3) / ((n : ℚ) + 4) := by
  have hpos : ((n : ℚ) + 4) ≠ 0 := by positivity
  rw [eq_div_iff hpos]
  have h := deriv_rel n (n + 1)
  unfold TT
  rw [show n + 1 + 3 = n + 4 by ring, show n + 1 + 2 = n + 3 by ring,
    show n + 1 + 1 = n + 2 by ring] at h
  push_cast at h
  linear_combination h

end OMA.Helpers

namespace OMA.Helpers

open Polynomial Finset

theorem a_sum (n : ℕ) : OMA.S_oeis_a116408.a n =
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * ((j.factorial : ℚ) * OMA.S_oeis_a116408.b j) := by
  unfold OMA.S_oeis_a116408.a
  rw [mul_comm (PowerSeries.exp ℚ), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_exp, Algebra.algebraMap_self,
    RingHom.id_apply]
  rw [Nat.cast_choose ℚ hk']
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem TT_sum (n v : ℕ) : TT n v =
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (((1 + X ^ 2 : ℚ[X]) ^ j).coeff (j + v)) := by
  unfold TT qq
  rw [show (1 + X + X ^ 2 : ℚ[X]) = (1 + X ^ 2) + X by ring, add_pow, finsetSum_coeff]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [coeff_mul_natCast, show n + v = (j + v) + (n - j) by omega, coeff_mul_X_pow]
  ring

theorem bes_eq (v j : ℕ) : (j.factorial : ℚ) * OMA.S_oeis_a116408.bes v j =
    ((1 + X ^ 2 : ℚ[X]) ^ j).coeff (j + v) := by
  have hexp : ((1 + X ^ 2 : ℚ[X]) ^ j) = expand ℚ 2 ((1 + X) ^ j) := by
    rw [map_pow, map_add, map_one, expand_X]
  rw [hexp, coeff_expand (by norm_num), coeff_one_add_X_pow]
  unfold OMA.S_oeis_a116408.bes
  by_cases h : v ≤ j ∧ (j - v) % 2 = 0
  · rw [if_pos h, if_pos (show 2 ∣ j + v by omega)]
    obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + v := ⟨(j - v) / 2, by omega⟩
    rw [show (2 * i + v - v) / 2 = i by omega, show (2 * i + v + v) / 2 = i + v by omega,
      Nat.cast_choose ℚ (show i + v ≤ 2 * i + v by omega),
      show 2 * i + v - (i + v) = i by omega]
    have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((i + v).factorial : ℚ) ≠ 0 := by positivity
    field_simp
  · rw [if_neg h]
    by_cases h2 : 2 ∣ j + v
    · rw [if_pos h2, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · rw [if_neg h2]
      simp

theorem a_eq (n : ℕ) : OMA.S_oeis_a116408.a n = TT n 2 - TT n 3 + TT n 4 := by
  rw [a_sum, TT_sum, TT_sum, TT_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  unfold OMA.S_oeis_a116408.b
  rw [← bes_eq, ← bes_eq, ← bes_eq]
  ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a116408.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  simp only [a_eq]
  rw [TT_four (m + 4), TT_four (m + 3), TT_four (m + 2), TT_four (m + 1), TT_four m]
  rw [TT_three (m + 4), TT_three (m + 3), TT_three (m + 2), TT_three (m + 1), TT_three m]
  rw [TT_two (m + 4)]
  have s0_3 : TT (m + 4) 0 = TT (m + 3) 0 + 2 * TT (m + 3) 1 := TT_zero_succ (m + 3)
  have s1_3 : TT (m + 4) 1 = TT (m + 3) 0 + TT (m + 3) 1 + TT (m + 3) 2 := TT_succ (m + 3) 0
  have s0_2 : TT (m + 3) 0 = TT (m + 2) 0 + 2 * TT (m + 2) 1 := TT_zero_succ (m + 2)
  have s1_2 : TT (m + 3) 1 = TT (m + 2) 0 + TT (m + 2) 1 + TT (m + 2) 2 := TT_succ (m + 2) 0
  have s0_1 : TT (m + 2) 0 = TT (m + 1) 0 + 2 * TT (m + 1) 1 := TT_zero_succ (m + 1)
  have s1_1 : TT (m + 2) 1 = TT (m + 1) 0 + TT (m + 1) 1 + TT (m + 1) 2 := TT_succ (m + 1) 0
  have s0_0 : TT (m + 1) 0 = TT m 0 + 2 * TT m 1 := TT_zero_succ m
  have s1_0 : TT (m + 1) 1 = TT m 0 + TT m 1 + TT m 2 := TT_succ m 0
  rw [s0_3, s1_3, TT_two (m + 3), s0_2, s1_2, TT_two (m + 2), s0_1, s1_1, TT_two (m + 1),
    s0_0, s1_0, TT_two m]
  push_cast
  have p0 : (m : ℚ) + 2 ≠ 0 := by positivity
  have p1 : (m : ℚ) + 3 ≠ 0 := by positivity
  have p2 : (m : ℚ) + 4 ≠ 0 := by positivity
  have p3 : (m : ℚ) + 1 + 2 ≠ 0 := by positivity
  have p4 : (m : ℚ) + 1 + 3 ≠ 0 := by positivity
  have p5 : (m : ℚ) + 1 + 4 ≠ 0 := by positivity
  have p6 : (m : ℚ) + 2 + 2 ≠ 0 := by positivity
  have p7 : (m : ℚ) + 2 + 3 ≠ 0 := by positivity
  have p8 : (m : ℚ) + 2 + 4 ≠ 0 := by positivity
  have p9 : (m : ℚ) + 3 + 2 ≠ 0 := by positivity
  have p10 : (m : ℚ) + 3 + 3 ≠ 0 := by positivity
  have p11 : (m : ℚ) + 3 + 4 ≠ 0 := by positivity
  have p12 : (m : ℚ) + 4 + 2 ≠ 0 := by positivity
  have p13 : (m : ℚ) + 4 + 3 ≠ 0 := by positivity
  have p14 : (m : ℚ) + 4 + 4 ≠ 0 := by positivity
  field_simp
  ring
