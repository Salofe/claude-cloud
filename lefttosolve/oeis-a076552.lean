import OMAStatements.S_oeis_a076552
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a076552 PowerSeries Finset

/-- Binomial convolution of exponential generating functions. -/
theorem conv (f g : ℕ → ℚ) (N : ℕ) :
    coeff N (mk (fun n => f n / (n.factorial : ℚ)) * mk (fun n => g n / (n.factorial : ℚ))) =
      (∑ i ∈ range (N + 1), (N.choose i : ℚ) * f i * g (N - i)) / (N.factorial : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (mk (fun n => f n / (n.factorial : ℚ))) *
      coeff j (mk (fun n => g n / (n.factorial : ℚ)))), Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [coeff_mk]
  have h := Nat.choose_mul_factorial_mul_factorial hi'
  have h' : ((N.choose i : ℕ) : ℚ) * (i.factorial : ℚ) * ((N - i).factorial : ℚ) =
      (N.factorial : ℚ) := by exact_mod_cast h
  have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((N - i).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((N.choose i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← h']
  field_simp

/-- The values `e m = E_m(-1/2)`. -/
noncomputable def e (m : ℕ) : ℚ := (eulerPoly m).eval (-(1 / 2 : ℚ))

theorem e_rec (m : ℕ) :
    e m = (-(1 / 2 : ℚ)) ^ m - (1 / 2) * ∑ k ∈ range m, (m.choose k : ℚ) * e k := by
  unfold e
  rw [eulerPoly]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_smul,
    Polynomial.eval_finsetSum, smul_eq_mul]
  congr 2
  rw [Fin.sum_univ_eq_sum_range (fun k => (m.choose k : ℚ) * (eulerPoly k).eval (-(1 / 2 : ℚ))) m]

/-- The exponential generating function of `e`. -/
noncomputable def EG : ℚ⟦X⟧ := mk (fun n => e n / (n.factorial : ℚ))

theorem exp_eq : exp ℚ = mk (fun n => (1 : ℚ) / (n.factorial : ℚ)) := by
  ext n
  simp [coeff_exp]

theorem EG_rel : EG * (exp ℚ + 1) = 2 * rescale (-(1 / 2 : ℚ)) (exp ℚ) := by
  ext m
  rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, coeff_C_mul, coeff_rescale, coeff_exp]
  rw [mul_add, mul_one, map_add, EG, exp_eq, conv]
  simp only [mul_one, coeff_mk]
  have hr := e_rec m
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hf : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith

theorem xy_one : exp ℚ * rescale (-1 : ℚ) (exp ℚ) = 1 := exp_mul_exp_neg_eq_one

theorem x_sq : exp ℚ ^ 2 = rescale (2 : ℚ) (exp ℚ) := by
  rw [exp_pow_eq_rescale_exp]; norm_num

theorem x_four : exp ℚ ^ 4 = rescale (4 : ℚ) (exp ℚ) := by
  rw [exp_pow_eq_rescale_exp]; norm_num

theorem y_sq : rescale (-1 : ℚ) (exp ℚ) ^ 2 = rescale (-2 : ℚ) (exp ℚ) := by
  rw [sq, exp_mul_exp_eq_exp_add]; norm_num

theorem R2 : rescale (2 : ℚ) EG * (1 + exp ℚ ^ 2) = 2 * rescale (-1 : ℚ) (exp ℚ) := by
  have h := congrArg (rescale (2 : ℚ)) EG_rel
  rw [map_mul, map_add, map_one, map_mul, map_ofNat, rescale_rescale] at h
  rw [x_sq, add_comm (1 : ℚ⟦X⟧), h]
  norm_num

theorem R3 : rescale (-2 : ℚ) EG * (1 + rescale (-1 : ℚ) (exp ℚ) ^ 2) = 2 * exp ℚ := by
  have h := congrArg (rescale (-2 : ℚ)) EG_rel
  rw [map_mul, map_add, map_one, map_mul, map_ofNat, rescale_rescale] at h
  rw [y_sq, add_comm (1 : ℚ⟦X⟧), h]
  norm_num

/-- `Bev(4t) = B(4t) + 2t`, the even part of `B(4t)`. -/
noncomputable def Bv : ℚ⟦X⟧ := rescale (4 : ℚ) (bernoulliPowerSeries ℚ) + 2 * X

theorem R1 : Bv * (exp ℚ ^ 4 - 1) = 2 * X * (exp ℚ ^ 4 + 1) := by
  have h := congrArg (rescale (4 : ℚ)) (bernoulliPowerSeries_mul_exp_sub_one ℚ)
  rw [map_mul, map_sub, map_one, rescale_X] at h
  rw [Bv, x_four, add_mul, h, map_ofNat]
  ring

theorem core : (exp ℚ - rescale (-1 : ℚ) (exp ℚ)) * Bv =
    X * (rescale (2 : ℚ) EG + rescale (-2 : ℚ) EG) := by
  set x := exp ℚ with hx
  set y := rescale (-1 : ℚ) (exp ℚ) with hy
  have h4 : x ^ 4 - 1 ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    rw [x_four, map_sub, coeff_rescale, coeff_exp, coeff_one] at this
    norm_num at this
  apply mul_right_cancel₀ h4
  have r1 := R1
  have r2 := R2
  have r3 := R3
  have r4 := xy_one
  rw [← hx] at r1 r2 r3 r4
  rw [← hy] at r2 r3 r4
  linear_combination (x - y) * r1 - X * (x ^ 2 - 1) * r2 - X * x ^ 2 * (x ^ 2 - 1) * r3 +
    (X * rescale (-2 : ℚ) EG * (x ^ 2 - 1) * (1 + x * y) - 2 * X * (x + x ^ 3)) * r4

/-- The numerators of `Bv`. -/
noncomputable def beta (j : ℕ) : ℚ := 4 ^ j * bernoulli j + if j = 1 then 2 else 0

theorem Bv_eq : Bv = mk (fun j => beta j / (j.factorial : ℚ)) := by
  ext j
  rw [Bv, map_add, coeff_rescale, bernoulliPowerSeries, coeff_mk, coeff_mk, beta,
    show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, coeff_C_mul, coeff_X]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs with h
  · subst h; norm_num
  · simp only [add_zero, mul_zero]
    ring

theorem beta_odd (k : ℕ) : beta (2 * k + 1) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [beta, bernoulli_one]
    norm_num
  · rw [beta, bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega), if_neg (by omega)]
    ring

theorem Bv_even : rescale (-1 : ℚ) Bv = Bv := by
  rw [Bv_eq, rescale_mk]
  ext j
  rw [coeff_mk, coeff_mk]
  rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
  · rw [pow_mul]; norm_num
  · rw [beta_odd]; simp

theorem sum_even_odd (f : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ k ∈ range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

theorem key (n : ℕ) :
    ∑ k ∈ range (n + 1), (16 : ℚ) ^ k * bernoulli (2 * k) * ((2 * n + 1).choose (2 * k) : ℚ) =
      (2 * n + 1 : ℚ) * 4 ^ n * e (2 * n) := by
  have hc := congrArg (coeff (2 * n + 1)) core
  rw [coeff_succ_X_mul, map_add, coeff_rescale, coeff_rescale, EG, coeff_mk] at hc
  rw [sub_mul, map_sub] at hc
  have hy : rescale (-1 : ℚ) (exp ℚ) * Bv = rescale (-1 : ℚ) (Bv * exp ℚ) := by
    rw [map_mul, Bv_even, mul_comm]
  rw [hy, coeff_rescale, mul_comm (exp ℚ) Bv, Bv_eq, exp_eq, conv] at hc
  simp only [mul_one] at hc
  have hS : ∑ i ∈ range (2 * n + 1 + 1), ((2 * n + 1).choose i : ℚ) * beta i =
      ∑ k ∈ range (n + 1), (16 : ℚ) ^ k * bernoulli (2 * k) * ((2 * n + 1).choose (2 * k) : ℚ) := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, sum_even_odd]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [beta_odd, beta, if_neg (by omega), pow_mul]
    norm_num
    ring
  rw [hS] at hc
  have hf : ((2 * n + 1).factorial : ℚ) = (2 * n + 1 : ℚ) * ((2 * n).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf] at hc
  have h1 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (2 * n + 1 : ℚ) ≠ 0 := by positivity
  have p1 : (2 : ℚ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  have p2 : (-2 : ℚ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  have p3 : (-1 : ℚ) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [p1, p2, p3] at hc
  field_simp at hc
  linear_combination hc / 2

end OMA.Helpers


open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a076552.main := by
  intro n
  have hk := key n
  unfold OMA.S_oeis_a076552.a
  rw [hk]
  unfold OMA.Helpers.e
  have h2 : (2 * n + 1 : ℚ) ≠ 0 := by positivity
  rw [show (-4 : ℚ) ^ n = (-1) ^ n * 4 ^ n by rw [← mul_pow]; norm_num, pow_succ]
  field_simp
  try ring
