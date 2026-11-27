import OMAReductions.R_Mills_lower_bound_of_RH_R1

open Real Chebyshev

namespace OMA.MillsH2

/-- `x ^ (1/4) * 4.9 ≤ √x` once `x ≥ 599` (as `4.9 ^ 4 ≤ 599`). -/
theorem quarter_le {x : ℝ} (hx : 599 ≤ x) : x ^ ((1 : ℝ) / 4) * 4.9 ≤ √x := by
  have hx0 : 0 ≤ x := by linarith
  have hq : (4.9 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := by
    have h1 : ((4.9 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = 4.9 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have hsq : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = √x := by
    rw [← Real.rpow_add' hx0 (by norm_num), Real.sqrt_eq_rpow]; norm_num
  have hpos : 0 ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hx0 _
  nlinarith

/-- `x ^ (1/3) * 2.9 ≤ √x` once `x ≥ 599` (as `2.9 ^ 6 ≤ 599`). -/
theorem third_le {x : ℝ} (hx : 599 ≤ x) : x ^ ((1 : ℝ) / 3) * 2.9 ≤ √x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : (2.9 : ℝ) ≤ x ^ ((1 : ℝ) / 6) := by
    have h1 : ((2.9 : ℝ) ^ (6 : ℕ)) ^ ((1 : ℝ) / 6) = 2.9 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have hsplit : x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 6) = √x := by
    rw [← Real.rpow_add' hx0 (by norm_num), Real.sqrt_eq_rpow]; norm_num
  have hpos : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx0 _
  nlinarith

/-- `x ^ (1/6) * 8.4 ≤ √x` once `x ≥ 599` (as `8.4 ^ 3 ≤ 599`). -/
theorem sixth_le {x : ℝ} (hx : 599 ≤ x) : x ^ ((1 : ℝ) / 6) * 8.4 ≤ √x := by
  have hx0 : 0 ≤ x := by linarith
  have ht : (8.4 : ℝ) ≤ x ^ ((1 : ℝ) / 3) := by
    have h1 : ((8.4 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = 8.4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have hsplit : x ^ ((1 : ℝ) / 6) * x ^ ((1 : ℝ) / 3) = √x := by
    rw [← Real.rpow_add' hx0 (by norm_num), Real.sqrt_eq_rpow]; norm_num
  have hpos : 0 ≤ x ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hx0 _
  nlinarith

/-- `log x ≥ 9 log 2 > 6.2383` once `x ≥ 599 ≥ 2 ^ 9`. -/
theorem log_ge {x : ℝ} (hx : 599 ≤ x) : 6.2383 ≤ log x := by
  have h512 : log ((2 : ℝ) ^ 9) ≤ log x :=
    Real.log_le_log (by norm_num) (by norm_num; linarith)
  rw [Real.log_pow] at h512
  have := Real.log_two_gt_d9
  push_cast at h512
  linarith

end OMA.MillsH2

open OMA.MillsH2 in
theorem OMA.solution : OMA.R_Mills_lower_bound_of_RH_R1.H2 := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  -- Costa Pereira, then `ψ (x ^ (1/5)) ≤ ψ (x ^ (1/3))`.
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
  have e2 : x ^ (2 : ℝ)⁻¹ = √x := by rw [Real.sqrt_eq_rpow]; norm_num
  have e3 : x ^ (3 : ℝ)⁻¹ = x ^ ((1 : ℝ) / 3) := by norm_num
  have e5 : x ^ (5 : ℝ)⁻¹ = x ^ ((1 : ℝ) / 5) := by norm_num
  rw [e2, e3, e5] at hCP
  have h53 : ψ (x ^ ((1 : ℝ) / 5)) ≤ ψ (x ^ ((1 : ℝ) / 3)) :=
    psi_mono (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  -- Explicit bounds on the two remaining `ψ` values.
  have hs1 : (1 : ℝ) ≤ √x := by rw [Real.one_le_sqrt]; exact hx1
  have hb1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 3) := Real.one_le_rpow hx1 (by norm_num)
  have hψs := psi_le hs1
  have hψb := psi_le hb1
  -- Rewrite `√√x`, `log √x`, `√(x^(1/3))`, `log (x^(1/3))`.
  have hss : √(√x) = x ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
  have hls : log √x = log x / 2 := Real.log_sqrt hx0.le
  have hsb : √(x ^ ((1 : ℝ) / 3)) = x ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
  have hlb : log (x ^ ((1 : ℝ) / 3)) = log x / 3 := by
    rw [Real.log_rpow hx0]; ring
  rw [hss, hls] at hψs
  rw [hsb, hlb] at hψb
  -- Numeric comparisons with `√x`.
  have q := quarter_le hx
  have t := third_le hx
  have s := sixth_le hx
  have hL := log_ge hx
  have hlog4 : log 4 < 1.3863 := by
    have : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have hlog4p : 0 < log (4 : ℝ) := Real.log_pos (by norm_num)
  have hsx : 0 ≤ √x := Real.sqrt_nonneg x
  have hq0 : 0 ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hx0.le _
  have ht0 : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx0.le _
  have h60 : 0 ≤ x ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hx0.le _
  have hLpos : 0 ≤ log x := by linarith
  -- Assemble: ψ x - θ x ≤ √x (1.6897 log 4 + 0.36282 log x) ≤ √x (log x)^2 / 8.
  have key1 : x ^ ((1 : ℝ) / 4) * 4.9 * log x ≤ √x * log x := mul_le_mul_of_nonneg_right q hLpos
  have key2 : x ^ ((1 : ℝ) / 3) * 2.9 * log 4 ≤ √x * log 4 :=
    mul_le_mul_of_nonneg_right t hlog4p.le
  have key3 : x ^ ((1 : ℝ) / 6) * 8.4 * log x ≤ √x * log x := mul_le_mul_of_nonneg_right s hLpos
  have hsl4 : 0 ≤ √x * log 4 := mul_nonneg hsx hlog4p.le
  have hslx : 0 ≤ √x * log x := mul_nonneg hsx hLpos
  have hLL : 6.2383 * log x ≤ log x * log x := mul_le_mul_of_nonneg_right hL hLpos
  have hquad : 1.6897 * log 4 + 0.36282 * log x ≤ log x ^ 2 / 8 := by
    rw [sq]; linarith
  have hfin : √x * (1.6897 * log 4 + 0.36282 * log x) ≤ √x * (log x ^ 2 / 8) :=
    mul_le_mul_of_nonneg_left hquad hsx
  calc ψ x - θ x
      ≤ ψ √x + ψ (x ^ ((1 : ℝ) / 3)) + ψ (x ^ ((1 : ℝ) / 5)) := hCP
    _ ≤ ψ √x + 2 * ψ (x ^ ((1 : ℝ) / 3)) := by linarith
    _ ≤ (log 4 * √x + 2 * x ^ ((1 : ℝ) / 4) * (log x / 2)) +
          2 * (log 4 * x ^ ((1 : ℝ) / 3) + 2 * x ^ ((1 : ℝ) / 6) * (log x / 3)) := by
        linarith
    _ ≤ √x * (1.6897 * log 4 + 0.36282 * log x) := by
        ring_nf
        ring_nf at key1 key2 key3 hsl4 hslx
        linarith
    _ ≤ √x * (log x ^ 2 / 8) := hfin
    _ = 1 / 8 * (√x * log x ^ 2) := by ring
