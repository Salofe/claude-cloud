import OMAStatements.S_mo_436948
import Mathlib

/-- Converse of the descent lemma: a two-sided quadratic bound on the first-order Taylor error
forces the gradient to be `L`-Lipschitz (no convexity needed). -/
theorem OMA.solution : type_of% @OMA.S_mo_436948.main := by
  intro n f L _ h
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have key : ∀ w : EuclideanSpace ℝ (Fin n),
      inner ℝ (gradient f x - gradient f y) w ≤ (L : ℝ) * ‖w‖ ^ 2 + (L : ℝ) / 4 * ‖x - y‖ ^ 2 := by
    intro w
    obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin n), e = (1 / 2 : ℝ) • (y - x) := ⟨_, rfl⟩
    have h1 := abs_le.mp (h (x + e + w) x)
    have h2 := abs_le.mp (h (x + e + w) y)
    have h3 := abs_le.mp (h (x + e - w) x)
    have h4 := abs_le.mp (h (x + e - w) y)
    have ey : x + e - y = -e := by
      rw [he]; module
    have r1 : x + e + w - x = e + w := by abel
    have r2 : x + e + w - y = w - e := by
      rw [show x + e + w - y = (x + e - y) + w by abel, ey]; abel
    have r3 : x + e - w - x = e - w := by abel
    have r4 : x + e - w - y = -(e + w) := by
      rw [show x + e - w - y = (x + e - y) - w by abel, ey]; abel
    rw [r1] at h1
    rw [r2] at h2
    rw [r3] at h3
    rw [r4] at h4
    have ne : ‖e‖ ^ 2 = ‖x - y‖ ^ 2 / 4 := by
      rw [he, norm_smul, mul_pow, norm_sub_rev]
      norm_num
      ring
    rw [norm_neg] at h4
    simp only [inner_add_right, inner_sub_right, inner_neg_right] at h1 h2 h3 h4
    rw [norm_add_sq_real] at h1 h4
    rw [norm_sub_sq_real] at h2 h3
    rw [real_inner_comm e w] at h2
    rw [ne] at h1 h2 h3 h4
    rw [inner_sub_left]
    linarith [h1.1, h2.2, h3.2, h4.1]
  by_cases hu : gradient f x - gradient f y = 0
  · rw [hu, norm_zero]; positivity
  have hpos : 0 < ‖gradient f x - gradient f y‖ := norm_pos_iff.mpr hu
  by_cases hL : (L : ℝ) = 0
  · exfalso
    have := key (gradient f x - gradient f y)
    rw [hL, real_inner_self_eq_norm_sq] at this
    nlinarith
  have hLp : 0 < (L : ℝ) := lt_of_le_of_ne L.2 (Ne.symm hL)
  have := key ((1 / (2 * (L : ℝ))) • (gradient f x - gradient f y))
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, mul_pow,
    Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  have hsq : ‖gradient f x - gradient f y‖ ^ 2 ≤ ((L : ℝ) * ‖x - y‖) ^ 2 := by
    field_simp at this
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
