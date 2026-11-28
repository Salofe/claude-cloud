import OMAReductions.R_Green54_green_54_known_case_R1
import Mathlib

open Set MeasureTheory ProbabilityTheory Green54
open scoped Pointwise ENNReal

theorem OMA.solution : OMA.R_Green54_green_54_known_case_R1.H2 := by
  intro I A r hA hb hr
  have : IsProbabilityMeasure gaussianMeasureInf := by
    unfold gaussianMeasureInf; infer_instance
  have hm : MeasurableSet ((I.restrict : (ℕ → ℝ) → I → ℝ) ⁻¹' A) :=
    (I.continuous_restrict (A := fun _ : ℕ => ℝ)).measurable hA
  have heq : gaussianMeasureInf ((I.restrict : (ℕ → ℝ) → I → ℝ) ⁻¹' A) =
      (Measure.pi fun _ : I ↦ gaussianReal 0 1) A :=
    OMA.R_Green54_green_54_known_case_R1.cylinder_measure I A hA
  rw [← heq] at hr
  obtain ⟨K0, hK0A, hK0, hrK0⟩ := hm.exists_lt_isCompact_of_ne_top (measure_ne_top _ _) hr
  let K : Set (ℕ → ℝ) :=
    (fun p : ℝ × (ℕ → ℝ) => p.1 • p.2) '' (Metric.closedBall (0:ℝ) 1 ×ˢ K0)
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact ((isCompact_closedBall (0:ℝ) 1).prod hK0).image (continuous_fst.smul continuous_snd)
  · rintro a ha _ ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
    refine ⟨(a * t, x), ⟨?_, hx⟩, ?_⟩
    · have ht' : ‖t‖ ≤ 1 := by simpa using ht
      simp only [Metric.mem_closedBall, dist_zero_right, norm_mul]
      exact mul_le_one₀ ha (norm_nonneg _) ht'
    · simp [mul_smul]
  · have hsub : K0 ⊆ K := by
      intro x hx
      exact ⟨(1, x), ⟨by simp, hx⟩, by simp⟩
    exact hrK0.le.trans (measure_mono hsub)
  · rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    have ht' : ‖t‖ ≤ 1 := by simpa using ht
    have hxA : (I.restrict : (ℕ → ℝ) → I → ℝ) x ∈ A := hK0A hx
    have h2 : t • (I.restrict : (ℕ → ℝ) → I → ℝ) x ∈ A := hb t ht' (Set.smul_mem_smul_set hxA)
    exact h2
