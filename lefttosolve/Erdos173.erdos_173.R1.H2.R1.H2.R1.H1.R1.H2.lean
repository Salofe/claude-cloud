import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1

/-!
# Step H2 of the reduction Erdos173.erdos_173.R1.H2.R1.H2.R1.H1.R1

For a, b, c in [-1, 1] the quadratic form 1 + ab + ac + bc is nonnegative, since twice it equals
(1+a)(1+b)(1+c) + (1-a)(1-b)(1-c). For real-valued L2 vectors on a probability space the real
part of 1 + <A,B> + <A,C> + <B,C> is the integral of this form (L2 inner products are integrals of
pointwise inner products). A nonnegative integrable function with zero integral vanishes almost
everywhere, which is the claim.
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace OMA.Helpers

theorem qform_nonneg {a b c : ℝ} (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) : 0 ≤ 1 + a * b + a * c + b * c := by
  have h1 : 0 ≤ (1 + a) * (1 + b) * (1 + c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : 0 ≤ (1 - a) * (1 - b) * (1 - c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

theorem re_inner_eq (z w : ℂ) : (inner ℂ z w).re = z.re * w.re + z.im * w.im := by
  rw [RCLike.inner_apply']
  simp [Complex.mul_re]

theorem re_inner_L2 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} (X Y : Lp ℂ 2 ν) :
    (inner ℂ X Y).re = ∫ ω, ((X ω).re * (Y ω).re + (X ω).im * (Y ω).im) ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  have h := integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) X Y)
  simp only [RCLike.re_to_complex, re_inner_eq] at h
  exact h.symm

theorem integrable_g {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} (X Y : Lp ℂ 2 ν) :
    Integrable (fun ω => (X ω).re * (Y ω).re + (X ω).im * (Y ω).im) ν := by
  have h := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) X Y).re
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [RCLike.re_to_complex, re_inner_eq]

theorem ae_zero_of_integral {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f1 f2 f3 : Ω → ℝ}
    (i1 : Integrable f1 ν) (i2 : Integrable f2 ν) (i3 : Integrable f3 ν)
    (h : 1 + ∫ ω, f1 ω ∂ν + ∫ ω, f2 ω ∂ν + ∫ ω, f3 ω ∂ν = 0)
    (hnn : ∀ᵐ ω ∂ν, 0 ≤ 1 + f1 ω + f2 ω + f3 ω) :
    ∀ᵐ ω ∂ν, 1 + f1 ω + f2 ω + f3 ω = 0 := by
  have j0 : Integrable (fun _ : Ω => (1 : ℝ)) ν := integrable_const _
  have j1 : Integrable (fun ω => 1 + f1 ω) ν := j0.add i1
  have j2 : Integrable (fun ω => 1 + f1 ω + f2 ω) ν := j1.add i2
  have hint : Integrable (fun ω => 1 + f1 ω + f2 ω + f3 ω) ν := j2.add i3
  have hsum : ∫ ω, (1 + f1 ω + f2 ω + f3 ω) ∂ν = 0 := by
    rw [integral_add (f := fun ω => 1 + f1 ω + f2 ω) (g := f3) j2 i3,
      integral_add (f := fun ω => 1 + f1 ω) (g := f2) j1 i2,
      integral_add (f := fun _ => (1 : ℝ)) (g := f1) j0 i1]
    simpa using h
  have hz := (integral_eq_zero_iff_of_nonneg_ae (f := fun ω => 1 + f1 ω + f2 ω + f3 ω)
    hnn hint).mp hsum
  filter_upwards [hz] with ω hω
  simpa using hω

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro Ω _ ν _ A B C hA hB hC h0
  simp only [Complex.add_re, Complex.one_re, OMA.Helpers.re_inner_L2] at h0
  have hz := OMA.Helpers.ae_zero_of_integral (OMA.Helpers.integrable_g A B)
    (OMA.Helpers.integrable_g A C) (OMA.Helpers.integrable_g B C) h0 (by
      filter_upwards [hA, hB, hC] with ω ha hb hc
      simp only [ha.1, hb.1, hc.1, mul_zero, add_zero]
      exact OMA.Helpers.qform_nonneg ha.2 hb.2 hc.2)
  filter_upwards [hz, hA, hB, hC] with ω h ha hb hc
  simpa [ha.1, hb.1, hc.1] using h
