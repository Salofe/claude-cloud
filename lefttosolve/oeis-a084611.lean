import OMAStatements.S_oeis_a084611
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a084611 Polynomial

theorem a084611_unit (z : ℂ) (hz : ‖z‖ = 1) : ‖1 + z - z ^ 2‖ ≤ Real.sqrt 5 := by
  have h1 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at h
    nlinarith
  rw [← Real.sqrt_sq (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Complex.sq_norm, Complex.normSq_apply]
  have e : (1 + z - z ^ 2).re = 1 + z.re - (z.re * z.re - z.im * z.im) := by
    simp [pow_two]
  have f : (1 + z - z ^ 2).im = z.im - (z.re * z.im + z.im * z.re) := by
    simp [pow_two]
  rw [e, f]
  have key : (1 + z.re - (z.re * z.re - z.im * z.im)) * (1 + z.re - (z.re * z.re - z.im * z.im)) +
      (z.im - (z.re * z.im + z.im * z.re)) * (z.im - (z.re * z.im + z.im * z.re)) =
      5 - 4 * z.re ^ 2 := by
    linear_combination (z.re ^ 2 - 2 * z.re + z.im ^ 2 + 4) * h1
  rw [key]
  nlinarith [sq_nonneg z.re]

theorem a084611_deg (n : ℕ) : (P ^ n).natDegree < 2 * n + 1 := by
  have h1 : P.natDegree ≤ 2 := by
    unfold P
    compute_degree
  have h2 := natDegree_pow_le (p := P) (n := n)
  nlinarith

theorem a084611_eval_le (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖aeval z (P ^ n)‖ ≤ Real.sqrt 5 ^ n := by
  rw [map_pow, norm_pow]
  have : aeval z P = 1 + z - z ^ 2 := by simp [P]
  rw [this]
  exact pow_le_pow_left₀ (norm_nonneg _) (a084611_unit z hz) n

theorem a084611_coeff_le (n k : ℕ) (hk : k < 2 * n + 1) :
    |((P ^ n).coeff k : ℝ)| ≤ Real.sqrt 5 ^ n := by
  set N := 2 * n + 1 with hN
  have hN0 : N ≠ 0 := by omega
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN0
  have hωj : ∀ j : ℕ, ‖ω ^ j‖ = 1 := fun j =>
    Complex.norm_eq_one_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow])
      hN0
  have hsum : ∀ m, m < N → ∑ j ∈ Finset.range N, (ω ^ (m + (N - k))) ^ j =
      if m = k then (N : ℂ) else 0 := by
    intro m hm
    split_ifs with h
    · subst h
      rw [show m + (N - m) = N by omega, hω.pow_eq_one]
      simp
    · have hne : ω ^ (m + (N - k)) ≠ 1 := by
        rw [Ne, hω.pow_eq_one_iff_dvd]
        rintro ⟨c, hc⟩
        rcases c with _ | _ | c
        · omega
        · omega
        · have : N * (c + 1 + 1) ≥ N * 2 := Nat.mul_le_mul_left _ (by omega)
          omega
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
        zero_div]
  have hid : ∑ j ∈ Finset.range N, aeval (ω ^ j) (P ^ n) * (ω ^ j) ^ (N - k) =
      (N : ℂ) * ((P ^ n).coeff k : ℂ) := by
    simp_rw [aeval_eq_sum_range' (a084611_deg n), Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (P ^ n).coeff m • (ω ^ j) ^ m * (ω ^ j) ^ (N - k) =
        ((P ^ n).coeff m : ℂ) * (if m = k then (N : ℂ) else 0) := by
      intro m hm
      rw [← hsum m (Finset.mem_range.mp hm), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zsmul_eq_mul, mul_assoc, ← pow_add, ← pow_mul, ← pow_mul, mul_comm j]
    rw [Finset.sum_congr rfl this]
    simp [Finset.mem_range.mpr hk, mul_comm]
  have hle : ‖(N : ℂ) * ((P ^ n).coeff k : ℂ)‖ ≤ N * Real.sqrt 5 ^ n := by
    rw [← hid]
    calc _ ≤ ∑ j ∈ Finset.range N, ‖aeval (ω ^ j) (P ^ n) * (ω ^ j) ^ (N - k)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range N, Real.sqrt 5 ^ n := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul, norm_pow, hωj, one_pow, mul_one]
          exact a084611_eval_le n _ (hωj j)
      _ = N * Real.sqrt 5 ^ n := by simp
  rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast] at hle
  have hNpos : (0 : ℝ) < N := by positivity
  exact le_of_mul_le_mul_left hle hNpos

theorem a084611_a_eq (n : ℕ) :
    (a n : ℝ) = ∑ k ∈ Finset.range (2 * n + 1), |((P ^ n).coeff k : ℝ)| := by
  unfold a
  push_cast
  rw [Finset.sum_subset (supp_subset_range (a084611_deg n))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  · intro x _ hx
    rw [Polynomial.notMem_support_iff.mp hx]
    simp

theorem a084611_upper (n : ℕ) : (a n : ℝ) ≤ (2 * n + 1 : ℕ) * Real.sqrt 5 ^ n := by
  rw [a084611_a_eq]
  calc _ ≤ ∑ k ∈ Finset.range (2 * n + 1), Real.sqrt 5 ^ n :=
        Finset.sum_le_sum fun k hk => a084611_coeff_le n k (Finset.mem_range.mp hk)
    _ = _ := by simp

theorem a084611_lower (n : ℕ) : Real.sqrt 5 ^ n ≤ (a n : ℝ) := by
  have h2 : ‖(2 + Complex.I : ℂ)‖ = Real.sqrt 5 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    norm_num
  have hP : aeval Complex.I P = 2 + Complex.I := by
    simp [P]
    ring
  have : ‖aeval Complex.I (P ^ n)‖ = Real.sqrt 5 ^ n := by
    rw [map_pow, norm_pow, hP, h2]
  rw [← this, a084611_a_eq, aeval_eq_sum_range' (a084611_deg n)]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [zsmul_eq_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_intCast]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a084611.main := by
  have hlim : Filter.Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 1) := by
    have h1 := tendsto_rpow_div_mul_add 2 1 (-1) (by norm_num)
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    refine (h1.comp h2).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp only [Function.comp, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    congr 1
    field_simp
    ring
  have hup : Filter.Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * Real.sqrt 5)
      Filter.atTop (nhds (Real.sqrt 5)) := by
    simpa using hlim.mul_const (Real.sqrt 5)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    calc Real.sqrt 5 = (Real.sqrt 5 ^ n) ^ ((1 : ℝ) / (n : ℝ)) := by
          rw [one_div, Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 5) hn0]
      _ ≤ (OMA.S_oeis_a084611.a n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) :=
          Real.rpow_le_rpow (by positivity) (a084611_lower n) (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    calc (OMA.S_oeis_a084611.a n : ℝ) ^ ((1 : ℝ) / (n : ℝ))
        ≤ (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt 5 ^ n) ^ ((1 : ℝ) / (n : ℝ)) :=
          Real.rpow_le_rpow (by positivity) (a084611_upper n) (by positivity)
      _ = ((2 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * Real.sqrt 5 := by
          rw [Real.mul_rpow (by positivity) (by positivity), one_div,
            Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 5) hn0]
