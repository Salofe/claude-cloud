import OMAReductions.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1
import Mathlib

/-!
# Step H2 of the reduction RiemannHypothesis.beurling_nyman_criterion.R1.H1.R1

If the constant one is a limit of the constrained sums of fractional parts, so is every
indicator of an initial interval. For `a ≤ 0` the indicator is zero on `(0, 1]`, which is the
empty sum; for `a ≥ 1` it agrees with the constant one on `(0, 1]`. For `0 < a < 1`, replacing
each `θ` by `a * θ` keeps the constraints; the new sum equals the old one at `x / a` on `(0, a]`
and vanishes on `(a, 1]` because there every fractional part is the number itself and the
weights sum to zero. A change of variables then shows that the squared distance to the
indicator of `(0, a]` is `a` times the squared distance to one.

Only upstream definitions are used.
-/

namespace OMA.Helpers
open MeasureTheory Set

/-- The finite combination of fractional parts, as an almost everywhere defined function. -/
theorem coe_fractSum (n : ℕ) (c θ : Fin n → ℝ) :
    (RiemannHypothesis.fractScalarInvSumL2 n c θ : ℝ → ℝ) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      fun x => ∑ ν, c ν * Int.fract (θ ν / x) := by
  unfold RiemannHypothesis.fractScalarInvSumL2
  have key : ∀ s : Finset (Fin n),
      ((∑ ν ∈ s, c ν • (RiemannHypothesis.fractScalarInv_memLp2 (θ ν)).toLp _ :
        Lp ℝ 2 (volume.restrict (Ioc (0:ℝ) 1))) : ℝ → ℝ)
        =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] fun x => ∑ ν ∈ s, c ν * Int.fract (θ ν / x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioc (0:ℝ) 1))] with x hx
      rw [hx]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add _ _).trans ?_
      have h1 := Lp.coeFn_smul (c a) ((RiemannHypothesis.fractScalarInv_memLp2 (θ a)).toLp _)
      have h2 := (RiemannHypothesis.fractScalarInv_memLp2 (θ a)).coeFn_toLp
      filter_upwards [h1, h2, ih] with x hx1 hx2 hx3
      rw [Pi.add_apply, hx1, Pi.smul_apply, hx2, hx3, Finset.sum_insert ha, smul_eq_mul,
        RiemannHypothesis.fractScalarInv]
  exact key Finset.univ

/-- The indicator of a set as an almost everywhere defined function. -/
theorem ind_coe (s : Set ℝ) (hs : MeasurableSet s) :
    (indicatorConstLp 2 hs (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) s) (1:ℝ) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] s.indicator (fun _ => (1:ℝ)) :=
  indicatorConstLp_coeFn

/-- The square of an `L²` norm as the integral of the square of a representative. -/
theorem norm_sq_eq_integral (F : Lp ℝ 2 (volume.restrict (Ioc (0:ℝ) 1))) (φ : ℝ → ℝ)
    (h : (F : ℝ → ℝ) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] φ) :
    ‖F‖ ^ 2 = ∫ x in Ioc (0:ℝ) 1, φ x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]

/-- Dilating the parameters by `a` dilates the approximation of one into an approximation of
the indicator of `(0, a]`, and multiplies the squared distance by `a`. -/
theorem dilation_sq (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) (c θ : Fin n → ℝ)
    (hθ : ∀ ν, θ ν ∈ Ioc (0:ℝ) 1) (hsum : ∑ ν, c ν * θ ν = 0) :
    ‖RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν) -
        indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) (Iic a)) (1:ℝ)‖ ^ 2 =
      a * ‖RiemannHypothesis.fractScalarInvSumL2 n c θ -
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) univ) (1:ℝ)‖ ^ 2 := by
  let ψ : ℝ → ℝ := fun y => ∑ ν, c ν * Int.fract (θ ν / y) - 1
  let φ : ℝ → ℝ := fun x =>
    ∑ ν, c ν * Int.fract (a * θ ν / x) - (Iic a).indicator (fun _ => (1:ℝ)) x
  have hL := norm_sq_eq_integral
    (RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν) -
        indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) (Iic a)) (1:ℝ)) φ (by
    filter_upwards [Lp.coeFn_sub (RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν))
        (indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) (Iic a)) (1:ℝ)),
      coe_fractSum n c (fun ν => a * θ ν), ind_coe (Iic a) measurableSet_Iic] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3])
  have hR := norm_sq_eq_integral
    (RiemannHypothesis.fractScalarInvSumL2 n c θ -
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) univ) (1:ℝ)) ψ (by
    filter_upwards [Lp.coeFn_sub (RiemannHypothesis.fractScalarInvSumL2 n c θ)
        (indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) univ) (1:ℝ)),
      coe_fractSum n c θ, ind_coe univ MeasurableSet.univ] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Set.indicator_univ])
  rw [hL, hR]
  have hzero : ∀ x ∈ Ioc (0:ℝ) 1 \ Ioc 0 a, φ x ^ 2 = 0 := by
    intro x hx
    obtain ⟨⟨hx0, _⟩, hxa⟩ := hx
    have hxa' : a < x := by
      by_contra h
      exact hxa ⟨hx0, not_lt.mp h⟩
    have hind : (Iic a).indicator (fun _ => (1:ℝ)) x = 0 :=
      Set.indicator_of_notMem (fun h => absurd (Set.mem_Iic.mp h) (not_le.mpr hxa')) _
    have hfr : ∀ ν, Int.fract (a * θ ν / x) = a * θ ν / x := by
      intro ν
      rw [Int.fract_eq_self]
      have h := hθ ν
      have hpos : 0 < a * θ ν := mul_pos ha0 h.1
      constructor
      · positivity
      · rw [div_lt_one hx0]
        nlinarith [h.1, h.2]
    have hsum' : ∑ ν, c ν * (a * θ ν / x) = (a / x) * ∑ ν, c ν * θ ν := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    show (∑ ν, c ν * Int.fract (a * θ ν / x) - (Iic a).indicator (fun _ => (1:ℝ)) x) ^ 2 = 0
    rw [hind, sub_zero]
    simp only [hfr]
    rw [hsum', hsum]
    ring
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc_right ha1.le) hzero]
  have hcongr : EqOn (fun x => φ x ^ 2) (fun x => ψ (x / a) ^ 2) (Ioc (0:ℝ) a) := by
    intro x hx
    have hind : (Iic a).indicator (fun _ => (1:ℝ)) x = 1 :=
      Set.indicator_of_mem (Set.mem_Iic.mpr hx.2) _
    have hfr : ∀ ν, Int.fract (a * θ ν / x) = Int.fract (θ ν / (x / a)) := by
      intro ν
      rw [div_div_eq_mul_div]
      ring_nf
    show (∑ ν, c ν * Int.fract (a * θ ν / x) - (Iic a).indicator (fun _ => (1:ℝ)) x) ^ 2 =
      (∑ ν, c ν * Int.fract (θ ν / (x / a)) - 1) ^ 2
    rw [hind]
    simp only [hfr]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
  rw [← intervalIntegral.integral_of_le ha0.le, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_div (fun y => ψ y ^ 2) ha0.ne', zero_div, div_self ha0.ne',
    smul_eq_mul]

end OMA.Helpers

open MeasureTheory Set in
theorem OMA.solution : OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1.H2 := by
  unfold OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1.H2
  dsimp only
  intro hone a
  have hae : ∀ᵐ x ∂(volume.restrict (Ioc (0:ℝ) 1)), x ∈ Ioc (0:ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  rcases le_or_gt a 0 with ha0 | ha0
  · have hz : indicatorConstLp 2 measurableSet_Iic
        (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) (Iic a)) (1:ℝ) = 0 := by
      apply Lp.ext
      filter_upwards [OMA.Helpers.ind_coe (Iic a) measurableSet_Iic,
        Lp.coeFn_zero ℝ 2 (volume.restrict (Ioc (0:ℝ) 1)), hae] with x h1 h2 hx
      rw [h1, h2, Set.indicator_of_notMem]
      · rfl
      · intro hxa
        exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hxa) (lt_of_le_of_lt ha0 hx.1)) (lt_irrefl x)
    rw [hz]
    apply subset_closure
    refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp, ?_⟩
    simp [RiemannHypothesis.fractScalarInvSumL2]
  rcases le_or_gt 1 a with ha1 | ha1
  · have he : indicatorConstLp 2 measurableSet_Iic
        (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) (Iic a)) (1:ℝ) =
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) univ) (1:ℝ) := by
      apply Lp.ext
      filter_upwards [OMA.Helpers.ind_coe (Iic a) measurableSet_Iic,
        OMA.Helpers.ind_coe univ MeasurableSet.univ, hae] with x h1 h2 hx
      rw [h1, h2, Set.indicator_of_mem (Set.mem_Iic.mpr (le_trans hx.2 ha1)),
        Set.indicator_of_mem (Set.mem_univ x)]
    rw [he]
    exact hone
  rw [Metric.mem_closure_iff] at hone ⊢
  intro ε hε
  obtain ⟨b, ⟨n, c, θ, hθ, hsum, rfl⟩, hb⟩ := hone ε hε
  refine ⟨RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν),
    ⟨n, c, fun ν => a * θ ν, ?_, ?_, rfl⟩, ?_⟩
  · intro ν
    have h := hθ ν
    refine ⟨mul_pos ha0 h.1, ?_⟩
    nlinarith [h.1, h.2]
  · have : ∑ ν, c ν * (a * θ ν) = a * ∑ ν, c ν * θ ν := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    rw [this, hsum, mul_zero]
  · have key := OMA.Helpers.dilation_sq a ha0 ha1 n c θ hθ hsum
    rw [dist_eq_norm, norm_sub_rev] at hb ⊢
    set X := ‖RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν) -
        indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) (Iic a)) (1:ℝ)‖ with hX
    set Y := ‖RiemannHypothesis.fractScalarInvSumL2 n c θ -
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0:ℝ) 1)) univ) (1:ℝ)‖ with hY
    have hX0 : 0 ≤ X := norm_nonneg _
    have hY0 : 0 ≤ Y := norm_nonneg _
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_le_mul hcon hcon hε.le hX0, mul_lt_mul'' hb hb hY0 hY0]
