import OMAReductions.R_LatinSquare_growthRateZn_R1

/-!
# Step H2 of the reduction LatinSquare.growthRateZn.R1

By the logarithmic form of the Stirling sequence,
log n! = log (stirlingSeq n) + (1/2) log (2 n) + n log (n / e),
so the normalized quantity equals log (stirlingSeq n) / n + (log 2 / 2) / n + (3/2) (log n / n) - 1.
The Stirling sequence converges (to the square root of pi), so its logarithm is bounded and the first
term tends to zero; the other two correction terms tend to zero as well.
-/

namespace OMA.Helpers

open Real Filter
open scoped Topology

theorem latin_log_factorial_identity (n : ℕ) (hn : 1 ≤ n) :
    (Real.log (n.factorial : ℝ) - ((n : ℝ) - 1) * Real.log n) / n =
      Real.log (Stirling.stirlingSeq n) / n + (Real.log 2 / 2) / n +
        (3 / 2) * (Real.log n / n) - 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hform := Stirling.log_stirlingSeq_formula n
  have h2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) hn0.ne'
  have hne : Real.log ((n : ℝ) / Real.exp 1) = Real.log n - 1 := by
    rw [Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  rw [hform, h2n, hne]
  field_simp
  ring

end OMA.Helpers

open Real Filter
open scoped Topology

theorem OMA.solution : OMA.R_LatinSquare_growthRateZn_R1.H2 := by
  unfold OMA.R_LatinSquare_growthRateZn_R1.H2
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨a, _, ha⟩ := Stirling.stirlingSeq_has_pos_limit_a
  have hpos : (0 : ℝ) < a := by assumption
  have t1 : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / n) atTop (𝓝 0) :=
    (ha.log hpos.ne').div_atTop hN
  have t2 : Tendsto (fun n : ℕ => (Real.log 2 / 2) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have t3 : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN
    refine h.congr (fun n => ?_)
    simp
  have hsum := ((t1.add t2).add (t3.const_mul (3 / 2))).sub_const 1
  simp only [add_zero, mul_zero, zero_sub] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (OMA.Helpers.latin_log_factorial_identity n hn).symm
