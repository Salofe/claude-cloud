import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H2_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos173.erdos_173.R1.H2.R1.H2.R1

A continuous map f from the complex plane to L2 of an arbitrary measure has a jointly
measurable version. For each n, uniform continuity of f on a compact disc gives a grid mesh 1/m
such that rounding p down to the grid moves f p by less than (1/4)^n whenever the norm of p is
at most n. The rounded approximants are jointly measurable because the grid index ranges over
the countable set of integer pairs. By the Chebyshev inequality the set where the n-th
approximant is at least (1/2)^n away from f p has measure at most (1/4)^n, so by Borel-Cantelli
the approximants converge almost everywhere to f p. The pointwise limit is measurable.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace OMA.Helpers

/-- The grid point with integer coordinates z at mesh 1/m. -/
noncomputable def gridPt (m : ℕ) (z : ℤ × ℤ) : ℂ := ⟨(z.1 : ℝ) / m, (z.2 : ℝ) / m⟩

/-- The integer coordinates of the grid cell containing p. -/
noncomputable def gridCell (m : ℕ) (p : ℂ) : ℤ × ℤ := (⌊p.re * m⌋, ⌊p.im * m⌋)

theorem measurable_gridCell (m : ℕ) : Measurable (gridCell m) :=
  ((Complex.measurable_re.mul_const _).floor).prodMk ((Complex.measurable_im.mul_const _).floor)

theorem floor_div_close (m : ℕ) (hm : 0 < m) (x : ℝ) :
    |(⌊x * m⌋ : ℝ) / m - x| ≤ 1 / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have e : (⌊x * m⌋ : ℝ) / m - x = ((⌊x * m⌋ : ℝ) - x * m) / m := by
    field_simp
  rw [e, abs_div, abs_of_pos hm', div_le_div_iff_of_pos_right hm', abs_le]
  have h1 := Int.floor_le (x * m)
  have h2 := Int.lt_floor_add_one (x * m)
  constructor <;> linarith

theorem dist_gridPt_le (m : ℕ) (hm : 0 < m) (p : ℂ) :
    dist (gridPt m (gridCell m p)) p ≤ 2 / m := by
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a := floor_div_close m hm p.re
  have b := floor_div_close m hm p.im
  simp only [gridPt, gridCell, Complex.sub_re, Complex.sub_im]
  have : (2:ℝ) / m = 1 / m + 1 / m := by ring
  rw [this]
  exact add_le_add a b

/-- Uniform continuity on a compact disc yields a suitable mesh for each n. -/
theorem mesh_choice {E : Type*} [PseudoMetricSpace E] (f : ℂ → E) (hf : Continuous f) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ p : ℂ, ‖p‖ ≤ n →
      dist (f (gridPt m (gridCell m p))) (f p) < ((1:ℝ)/4)^n := by
  have hK : IsCompact (Metric.closedBall (0:ℂ) (n+1)) := isCompact_closedBall _ _
  have hu := hK.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδf⟩ := hu (((1:ℝ)/4)^n) (by positivity)
  have hmin : 0 < min δ 1 := lt_min hδ one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / min δ 1)
  have hmpos : (0:ℝ) < m := lt_trans (by positivity) hm
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have small : 2 / (m:ℝ) < min δ 1 := by
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hmin] at hm
    linarith [mul_comm (m:ℝ) (min δ 1)]
  have hl := min_le_left δ 1
  have hr := min_le_right δ 1
  refine ⟨m, hm0, fun p hp => ?_⟩
  have hd := dist_gridPt_le m hm0 p
  have tri : ‖gridPt m (gridCell m p)‖ ≤ ‖p‖ + dist (gridPt m (gridCell m p)) p := by
    rw [dist_eq_norm]
    have := norm_add_le (gridPt m (gridCell m p) - p) p
    rw [sub_add_cancel] at this
    linarith
  apply hδf
  · rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  · rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  · linarith

/-- A continuous family of L2 classes has a jointly measurable version. -/
theorem measurable_version {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (f : ℂ → Lp ℂ 2 ν)
    (hf : Continuous f) : ∃ F : ℂ × Ω → ℂ, Measurable F ∧
      ∀ p : ℂ, (fun ω => F (p, ω)) =ᵐ[ν] f p := by
  choose m hm0 hm using mesh_choice f hf
  let G : ℕ → ℂ × Ω → ℂ := fun n z => f (gridPt (m n) (gridCell (m n) z.1)) z.2
  have hG : ∀ n, Measurable (G n) := by
    intro n
    have h1 : Measurable (fun w : (ℤ × ℤ) × Ω => f (gridPt (m n) w.1) w.2) :=
      measurable_from_prod_countable_right
        (fun x => (Lp.stronglyMeasurable (f (gridPt (m n) x))).measurable)
    exact h1.comp (((measurable_gridCell (m n)).comp measurable_fst).prodMk measurable_snd)
  refine ⟨fun z => limUnder atTop (fun n => G n z),
    (StronglyMeasurable.limUnder (fun n => (hG n).stronglyMeasurable)).measurable, fun p => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge ‖p‖
  let s : ℕ → Set Ω := fun n => if N ≤ n then
    {ω | ENNReal.ofReal (((1:ℝ)/2)^n) ≤ ‖f (gridPt (m n) (gridCell (m n) p)) ω - f p ω‖ₑ} else ∅
  have hs : ∀ n, ν (s n) ≤ ENNReal.ofReal (((1:ℝ)/4)^n) := by
    intro n
    by_cases hn : N ≤ n
    · simp only [s, if_pos hn]
      set η := ENNReal.ofReal (((1:ℝ)/2)^n) with hη
      have cheb := mul_meas_ge_le_pow_eLpNorm' ν (p := 2) two_ne_zero ENNReal.ofNat_ne_top
        ((Lp.aestronglyMeasurable (f (gridPt (m n) (gridCell (m n) p)))).sub
          (Lp.aestronglyMeasurable (f p))) η
      rw [← Lp.edist_def] at cheb
      have hd := hm n p (hN.trans (by exact_mod_cast hn))
      have he := (edist_lt_ofReal.mpr hd).le
      have hq : ENNReal.ofReal (((1:ℝ)/4)^n) = η^2 := by
        rw [hη, ← ENNReal.ofReal_pow (by positivity), ← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [hq] at he ⊢
      have hη0 : η ≠ 0 := by
        rw [hη, Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      have hηt : η ≠ ⊤ := ENNReal.ofReal_ne_top
      have h2 : η^2 * ν {ω | η ≤ ‖f (gridPt (m n) (gridCell (m n) p)) ω - f p ω‖ₑ} ≤
          η^2 * η^2 := by
        have t2 : (2:ℝ≥0∞).toReal = (2:ℝ) := by norm_num
        rw [t2, ENNReal.rpow_two, ENNReal.rpow_two] at cheb
        calc _ ≤ _ := cheb
          _ ≤ (η^2)^2 := by gcongr
          _ = η^2 * η^2 := sq _
      exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hη0) (ENNReal.pow_ne_top hηt)).mp h2
    · simp [s, hn]
  have hsum : (∑' n, ν (s n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  show limUnder atTop (fun n => G n (p, ω)) = f p ω
  apply Tendsto.limUnder_eq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1:ℝ)/2) (by norm_num) (by norm_num))
  filter_upwards [hω, eventually_ge_atTop N] with n hn hNn
  simp only [s, if_pos hNn, Set.mem_ofPred_eq, not_le] at hn
  rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hn
  exact hn.le

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1.H2 := by
  intro Ω _ ν f hf
  exact OMA.Helpers.measurable_version ν f hf
