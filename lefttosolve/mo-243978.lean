import OMAStatements.S_mo_243978
import Mathlib

/-!
The answer to the question is negative. Put `φ y = g y * f y - y * g y`. The equation
`x g' - (g f)' = 0` gives `φ' = -g` on `[0, 1]`, and `φ 0 = 0` because `f 0 ∈ [0, 0]`.
By the mean value theorem `φ x = -x g c` for some `c ∈ (0, x)`, so `γ x ≤ g x f x` becomes
`γ ≤ g x - g c`. This contradicts the continuity of `g` at `0` for small `x > 0`.
-/

open Set

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_243978.main) := by
  rintro ⟨γ, hγ, g, f, g', h', H⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hφ : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun y => g y * f y - y * g y) (- g x) (Icc 0 1) x := by
    intro x hx
    obtain ⟨-, -, hg, hh, he, -⟩ := H x hx
    have := hh.sub (((hasDerivAt_id' x).hasDerivWithinAt (s := Icc 0 1)).mul hg)
    exact this.congr_deriv (by linarith)
  have hf0 : f 0 = 0 := by
    obtain ⟨-, hf, -⟩ := H 0 h0
    exact le_antisymm hf.2 hf.1
  have hgc : ContinuousWithinAt g (Icc 0 1) 0 := (H 0 h0).2.2.1.continuousWithinAt
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 hgc (γ / 2) (by linarith)
  set x : ℝ := min (δ / 2) 1 with hxdef
  have hxpos : 0 < x := lt_min (by linarith) one_pos
  have hx1 : x ≤ 1 := min_le_right _ _
  have hxδ : x < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsub : Icc 0 x ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (le_refl _) hx1
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun y => g y * f y - y * g y)
    (fun y => - g y) hxpos
    (fun y hy => ((hφ y (hsub hy)).continuousWithinAt).mono hsub)
    (fun y hy => (hφ y (hsub (Ioo_subset_Icc_self hy))).hasDerivAt
      (Icc_mem_nhds (by linarith [hy.1]) (by linarith [hy.2])))
  simp only [hf0, mul_zero, zero_mul, sub_zero] at hceq
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hxpos.le, hx1⟩
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, by linarith [hc.2]⟩
  have hb := (H x hxI).2.2.2.2.2
  have d1 := hδg hxI (by rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]; exact hxδ)
  have d2 := hδg hcI (by rw [Real.dist_eq, sub_zero, abs_of_pos hc.1]; linarith [hc.2])
  rw [Real.dist_eq, abs_lt] at d1 d2
  rw [eq_div_iff hxpos.ne'] at hceq
  nlinarith
