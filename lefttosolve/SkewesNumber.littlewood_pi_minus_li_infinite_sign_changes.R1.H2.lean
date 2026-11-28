import OMAReductions.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1
import Mathlib

/-!
# Step H2 of the reduction SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes.R1

For x at least 3, the difference li(x) - li(floor x) is the integral of 1 / log t over the
interval from floor x to x. On that interval the integrand lies in (0, 1) because t is at
least 3 > e, and the interval has length less than one; this gives both bounds.
-/

namespace OMA.Helpers

/-- The integrand `1 / log t` is continuous on `[2, ∞)`. -/
theorem one_div_log_continuousOn (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc a b) := by
  refine continuousOn_const.div (Real.continuousOn_log.mono fun t ht => ?_) fun t ht => ?_
  · have : 2 ≤ t := le_trans (le_min ha hb) ht.1
    exact Set.mem_compl_singleton_iff.mpr (by linarith)
  · have : 2 ≤ t := le_trans (le_min ha hb) ht.1
    exact (Real.log_pos (by linarith)).ne'

theorem one_div_log_intervalIntegrable (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b :=
  (one_div_log_continuousOn a b ha hb).intervalIntegrable

end OMA.Helpers

theorem OMA.solution : OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1.H2 := by
  intro x hx
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hf3n : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hf3 : (3:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf3n
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hxf : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have key : Real.logIntegral x - Real.logIntegral (⌊x⌋₊ : ℝ) =
      ∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t := by
    unfold Real.logIntegral
    rw [add_sub_add_left_eq_sub]
    refine intervalIntegral.integral_interval_sub_left (OMA.Helpers.one_div_log_intervalIntegrable 2 x (by norm_num) (by linarith))
      (OMA.Helpers.one_div_log_intervalIntegrable 2 _ (by norm_num) (by linarith))
  rw [key]
  have hlog3 : 1 < Real.log 3 := by
    have h := Real.exp_one_lt_d9
    exact (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith)
  have bound : ∀ t ∈ Set.Icc (⌊x⌋₊ : ℝ) x, 0 ≤ 1 / Real.log t ∧ 1 / Real.log t ≤ 1 := by
    intro t ht
    have ht3 : 3 ≤ t := le_trans hf3 ht.1
    have hlt : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht3
    have hpos : 0 < Real.log t := by linarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hpos]
    linarith
  constructor
  · exact intervalIntegral.integral_nonneg hfx (fun t ht => (bound t ht).1)
  · have h1 : (∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t) ≤ ∫ t in (⌊x⌋₊ : ℝ)..x, (1:ℝ) :=
      intervalIntegral.integral_mono_on hfx
        (OMA.Helpers.one_div_log_intervalIntegrable _ x (by linarith) (by linarith))
        intervalIntegrable_const (fun t ht => (bound t ht).2)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
    linarith
