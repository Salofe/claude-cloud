import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1

/-!
# Step H4: overlap of the constant and decaying relative errors

Below y = 50 the constant error already suffices. Above it, the bound
50 y^7 <= exp (4y/5) follows from the Taylor term of order 40.
-/

namespace OMA.Helpers

open Real

theorem big_exp (y : ℝ) (h : 50 ≤ y) : 50 * y ^ 7 ≤ exp ((4/5) * y) := by
  have hy : 0 ≤ y := by linarith
  have e := Real.pow_div_factorial_le_exp (x := (4/5) * y) (by positivity) 40
  refine le_trans ?_ e
  have hy33 : (50:ℝ) ^ 33 ≤ y ^ 33 := pow_le_pow_left₀ (by norm_num) h 33
  have c : (50:ℝ) * (Nat.factorial 40 : ℝ) ≤ (4/5) ^ 40 * 50 ^ 33 := by
    norm_num [Nat.factorial]
  have hf : (0:ℝ) < (Nat.factorial 40 : ℝ) := by exact_mod_cast Nat.factorial_pos 40
  rw [le_div_iff₀ hf, mul_pow]
  calc 50 * y ^ 7 * (Nat.factorial 40 : ℝ) = (50 * (Nat.factorial 40 : ℝ)) * y ^ 7 := by ring
    _ ≤ ((4/5) ^ 40 * y ^ 33) * y ^ 7 :=
        mul_le_mul_of_nonneg_right
          (c.trans (mul_le_mul_of_nonneg_left hy33 (by positivity))) (by positivity)
    _ = (4/5) ^ 40 * y ^ 40 := by ring

end OMA.Helpers

open Real in
theorem OMA.solution :
    OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1.H4 := by
  intro y hy
  rcases le_or_gt y 50 with h | h
  · have h1 : min (1/40000000:ℝ) (10*y^3*exp (-(4/5)*y)) ≤ 1/40000000 := min_le_left _ _
    have hy4 : y ^ 4 ≤ (50:ℝ) ^ 4 := pow_le_pow_left₀ hy h 4
    calc min (1/40000000:ℝ) (10*y^3*exp (-(4/5)*y)) * (5*y^4)
        ≤ 1/40000000 * (5*y^4) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 1 := by nlinarith
  · have h1 : min (1/40000000:ℝ) (10*y^3*exp (-(4/5)*y)) ≤ 10*y^3*exp (-(4/5)*y) :=
      min_le_right _ _
    have key := OMA.Helpers.big_exp y h.le
    have ep : 0 < exp ((4/5) * y) := exp_pos _
    calc min (1/40000000:ℝ) (10*y^3*exp (-(4/5)*y)) * (5*y^4)
        ≤ 10*y^3*exp (-(4/5)*y) * (5*y^4) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 50 * y ^ 7 / exp ((4/5) * y) := by
          rw [neg_mul, Real.exp_neg]; field_simp; ring
      _ ≤ 1 := by rw [div_le_one ep]; exact key
