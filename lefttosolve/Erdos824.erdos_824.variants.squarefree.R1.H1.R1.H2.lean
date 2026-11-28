import OMAReductions.R_Erdos824_erdos_824_variants_squarefree_R1_H1_R1
import Mathlib

/-! Step H2 of Erdos824.erdos_824.variants.squarefree.R1.H1.R1: with e = min(eta/2, 1/4), the Mathlib bound psi - theta at most 2 sqrt(x) log x and log = o(x^r) give psi(5y) - theta(5y) + y^(1-eta) log(5y) below y^(1-e) for large y. -/

open Filter

namespace OMA.Helpers

/-- For every positive exponent r and constant c, eventually log (5 y) ≤ c y^r. -/
theorem log_five_mul_le {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, Real.log (5 * y) ≤ c * y ^ r := by
  have hb := (isLittleO_log_rpow_atTop hr).bound (show 0 < c / 2 by positivity)
  filter_upwards [hb, eventually_ge_atTop (5 : ℝ)] with y hy hy5
  have hy0 : 0 < y := by linarith
  have hlogy : Real.log 5 ≤ Real.log y := Real.log_le_log (by norm_num) hy5
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hpos : 0 ≤ Real.log y := le_trans hlog5 hlogy
  rw [Real.norm_of_nonneg hpos, Real.norm_of_nonneg (by positivity)] at hy
  rw [Real.log_mul (by norm_num) hy0.ne']
  linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos824_erdos_824_variants_squarefree_R1_H1_R1.H2 := by
  intro η hη
  refine ⟨min (η / 2) (1 / 4), lt_min (by linarith) (by norm_num), ?_⟩
  filter_upwards [OMA.Helpers.log_five_mul_le (r := 1 / 4) (c := 1 / 20) (by norm_num) (by norm_num),
    OMA.Helpers.log_five_mul_le (r := η / 2) (c := 1 / 4) (by linarith) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with y hA hB hy1
  have hy0 : 0 < y := by linarith
  set e := min (η / 2) (1 / 4) with he
  have he1 : e ≤ η / 2 := min_le_left _ _
  have he2 : e ≤ 1 / 4 := min_le_right _ _
  have hlog : 0 ≤ Real.log (5 * y) := Real.log_nonneg (by linarith)
  -- the prime-power part
  have hpt := Chebyshev.psi_sub_theta_le (x := 5 * y) (by linarith)
  have hsq : √(5 * y) ≤ 3 * y ^ (1 / (2 : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow y]
    have h5 : √(5 : ℝ) ≤ 3 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have : 0 ≤ y ^ (1 / (2 : ℝ)) := by positivity
    nlinarith
  have hA' : Chebyshev.psi (5 * y) - Chebyshev.theta (5 * y) ≤ (3 / 10) * y ^ (3 / (4 : ℝ)) := by
    have h34 : y ^ (3 / (4 : ℝ)) = y ^ (1 / (2 : ℝ)) * y ^ (1 / (4 : ℝ)) := by
      rw [← Real.rpow_add hy0]
      norm_num
    have hp1 : 0 ≤ y ^ (1 / (2 : ℝ)) := by positivity
    calc Chebyshev.psi (5 * y) - Chebyshev.theta (5 * y)
        ≤ 2 * √(5 * y) * Real.log (5 * y) := hpt
      _ ≤ 2 * (3 * y ^ (1 / (2 : ℝ))) * ((1 / 20) * y ^ (1 / (4 : ℝ))) := by
          apply mul_le_mul (by linarith) hA hlog (by positivity)
      _ = (3 / 10) * y ^ (3 / (4 : ℝ)) := by rw [h34]; ring
  have hB' : y ^ (1 - η) * Real.log (5 * y) ≤ (1 / 4) * y ^ (1 - η / 2) := by
    have hsplit : y ^ (1 - η / 2) = y ^ (1 - η) * y ^ (η / 2) := by
      rw [← Real.rpow_add hy0]
      ring_nf
    rw [hsplit]
    have : 0 ≤ y ^ (1 - η) := by positivity
    nlinarith
  have hm1 : y ^ (3 / (4 : ℝ)) ≤ y ^ (1 - e) :=
    Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have hm2 : y ^ (1 - η / 2) ≤ y ^ (1 - e) :=
    Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have hpos : 0 < y ^ (1 - e) := by positivity
  linarith
