import OMAReductions.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1
import Mathlib

/-!
# Step H2 of the reduction EllipticCurveRank.RatEllipticCurve.goldfeld_conjecture.variants.two_le.R1.H1.R1

The twist of `y^2 = x^3 + A x + B` by `b^2 a` is `y^2 = x^3 + b^4 a^2 A x + b^6 a^3 B`, which is the
image of the twist by `a` under the change of variables `(x, y) ↦ (b^2 x, b^3 y)`. We show that a
scaling `(x, y) ↦ (u^2 x, u^3 y)` between two short Weierstrass curves with `a₄' = u^4 a₄` and
`a₆' = u^6 a₆` maps nonsingular points to nonsingular points, multiplies slopes by `u`, and
therefore commutes with the chord-and-tangent addition. The scalings by `u` and `u⁻¹` are inverse
to each other, which gives the required isomorphism of groups of rational points.
-/

namespace OMA.Helpers

open WeierstrassCurve WeierstrassCurve.Affine

/-- Two short Weierstrass curves over `ℚ` related by the scaling `(x, y) ↦ (u^2 x, u^3 y)`. -/
def ScaleRel (W₁ W₂ : Affine ℚ) (u : ℚ) : Prop :=
  u ≠ 0 ∧ W₁.a₁ = 0 ∧ W₁.a₂ = 0 ∧ W₁.a₃ = 0 ∧ W₂.a₁ = 0 ∧ W₂.a₂ = 0 ∧ W₂.a₃ = 0 ∧
    W₂.a₄ = u ^ 4 * W₁.a₄ ∧ W₂.a₆ = u ^ 6 * W₁.a₆

theorem scale_nonsingular {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) {x y : ℚ}
    (h : W₁.Nonsingular x y) : W₂.Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
  obtain ⟨hu, h1, h2, h3, h1', h2', h3', h4, h6⟩ := hR
  rw [nonsingular_iff', equation_iff'] at h ⊢
  obtain ⟨he, hn⟩ := h
  rw [h1, h2, h3] at he hn
  rw [h1', h2', h3', h4, h6]
  refine ⟨?_, ?_⟩
  · have e : (u ^ 3 * y) ^ 2 + 0 * (u ^ 2 * x) * (u ^ 3 * y) + 0 * (u ^ 3 * y) -
        ((u ^ 2 * x) ^ 3 + 0 * (u ^ 2 * x) ^ 2 + u ^ 4 * W₁.a₄ * (u ^ 2 * x) + u ^ 6 * W₁.a₆) =
        u ^ 6 * (y ^ 2 + 0 * x * y + 0 * y - (x ^ 3 + 0 * x ^ 2 + W₁.a₄ * x + W₁.a₆)) := by ring
    rw [e, he, mul_zero]
  · rcases hn with hn | hn
    · left
      have e : 0 * (u ^ 3 * y) - (3 * (u ^ 2 * x) ^ 2 + 2 * 0 * (u ^ 2 * x) + u ^ 4 * W₁.a₄) =
          u ^ 4 * (0 * y - (3 * x ^ 2 + 2 * 0 * x + W₁.a₄)) := by ring
      rw [e]
      exact mul_ne_zero (pow_ne_zero _ hu) hn
    · right
      have e : 2 * (u ^ 3 * y) + 0 * (u ^ 2 * x) + 0 = u ^ 3 * (2 * y + 0 * x + 0) := by ring
      rw [e]
      exact mul_ne_zero (pow_ne_zero _ hu) hn

/-- The scaling map on points. -/
noncomputable def scalePt {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) :
    W₁.Point → W₂.Point
  | .zero => .zero
  | .some x y h => .some (u ^ 2 * x) (u ^ 3 * y) (scale_nonsingular hR h)

theorem some_congr {W : Affine ℚ} {x y x' y' : ℚ} {h : W.Nonsingular x y}
    {h' : W.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx
  subst hy
  rfl

theorem scale_slope {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) (x₁ x₂ y₁ y₂ : ℚ) :
    W₂.slope (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) = u * W₁.slope x₁ x₂ y₁ y₂ := by
  obtain ⟨hu, h1, h2, h3, h1', h2', h3', h4, h6⟩ := hR
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero _ hu
  by_cases hx : x₁ = x₂
  · have hx' : u ^ 2 * x₁ = u ^ 2 * x₂ := by rw [hx]
    by_cases hy : y₁ = W₁.negY x₂ y₂
    · have hy' : u ^ 3 * y₁ = W₂.negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
        simp only [negY, h1, h3, h1', h3'] at hy ⊢
        rw [hy]
        ring
      rw [slope_of_Y_eq hx' hy', slope_of_Y_eq hx hy, mul_zero]
    · have hy' : u ^ 3 * y₁ ≠ W₂.negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
        intro hc
        apply hy
        simp only [negY, h1, h3, h1', h3'] at hc ⊢
        apply mul_left_cancel₀ hu3
        rw [hc]
        ring
      rw [slope_of_Y_ne hx' hy', slope_of_Y_ne hx hy]
      simp only [negY, h1, h2, h3, h1', h2', h3', h4]
      have e1 : 3 * (u ^ 2 * x₁) ^ 2 + 2 * 0 * (u ^ 2 * x₁) + u ^ 4 * W₁.a₄ - 0 * (u ^ 3 * y₁) =
          u ^ 4 * (3 * x₁ ^ 2 + 2 * 0 * x₁ + W₁.a₄ - 0 * y₁) := by ring
      have e2 : u ^ 3 * y₁ - (-(u ^ 3 * y₁) - 0 * (u ^ 2 * x₁) - 0) =
          u ^ 3 * (y₁ - (-y₁ - 0 * x₁ - 0)) := by ring
      rw [e1, e2, mul_div_mul_comm]
      congr 1
      field_simp
  · have hx' : u ^ 2 * x₁ ≠ u ^ 2 * x₂ := fun hc => hx (mul_left_cancel₀ hu2 hc)
    rw [slope_of_X_ne hx', slope_of_X_ne hx]
    have e1 : u ^ 3 * y₁ - u ^ 3 * y₂ = u ^ 3 * (y₁ - y₂) := by ring
    have e2 : u ^ 2 * x₁ - u ^ 2 * x₂ = u ^ 2 * (x₁ - x₂) := by ring
    rw [e1, e2, mul_div_mul_comm]
    congr 1
    field_simp

theorem scale_add {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) (P Q : W₁.Point) :
    scalePt hR (P + Q) = scalePt hR P + scalePt hR Q := by
  have hR' := hR
  obtain ⟨hu, h1, h2, h3, h1', h2', h3', h4, h6⟩ := hR'
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero _ hu
  rcases P with _ | ⟨x₁, y₁, k₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, k₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₁.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have hx' : u ^ 2 * x₁ = u ^ 2 * x₂ := by rw [hx]
    have hy' : u ^ 3 * y₁ = W₂.negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
      simp only [negY, h1, h3, h1', h3'] at hy ⊢
      rw [hy]
      ring
    rw [Point.add_of_Y_eq hx hy]
    change Point.zero = Point.some _ _ (scale_nonsingular hR k₁) +
      Point.some _ _ (scale_nonsingular hR k₂)
    rw [Point.add_of_Y_eq hx' hy']
    rfl
  · have hxy' : ¬(u ^ 2 * x₁ = u ^ 2 * x₂ ∧ u ^ 3 * y₁ = W₂.negY (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
      rintro ⟨hc1, hc2⟩
      apply hxy
      refine ⟨mul_left_cancel₀ hu2 hc1, ?_⟩
      simp only [negY, h1, h3, h1', h3'] at hc2 ⊢
      apply mul_left_cancel₀ hu3
      rw [hc2]
      ring
    rw [Point.add_some hxy]
    change Point.some _ _ (scale_nonsingular hR (nonsingular_add k₁ k₂ hxy)) =
      Point.some _ _ (scale_nonsingular hR k₁) +
      Point.some _ _ (scale_nonsingular hR k₂)
    rw [Point.add_some hxy']
    have hs := scale_slope hR x₁ x₂ y₁ y₂
    apply some_congr
    · rw [hs]
      simp only [addX, h1, h2, h1', h2']
      ring
    · rw [hs]
      simp only [addY, negAddY, addX, negY, h1, h2, h3, h1', h2', h3']
      ring

theorem scale_inv {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) :
    ScaleRel W₂ W₁ u⁻¹ := by
  obtain ⟨hu, h1, h2, h3, h1', h2', h3', h4, h6⟩ := hR
  refine ⟨inv_ne_zero hu, h1', h2', h3', h1, h2, h3, ?_, ?_⟩
  · rw [h4]
    field_simp
  · rw [h6]
    field_simp

theorem scale_left_inv {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) (P : W₁.Point) :
    scalePt (scale_inv hR) (scalePt hR P) = P := by
  have hu : u ≠ 0 := hR.1
  rcases P with _ | ⟨x, y, k⟩
  · rfl
  · apply some_congr
    · field_simp
    · field_simp

theorem scale_right_inv {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) (P : W₂.Point) :
    scalePt hR (scalePt (scale_inv hR) P) = P := by
  have hu : u ≠ 0 := hR.1
  rcases P with _ | ⟨x, y, k⟩
  · rfl
  · apply some_congr
    · field_simp
    · field_simp

/-- The scaling as an isomorphism of groups of points. -/
noncomputable def scaleEquiv {W₁ W₂ : Affine ℚ} {u : ℚ} (hR : ScaleRel W₁ W₂ u) :
    W₁.Point ≃+ W₂.Point where
  toFun := scalePt hR
  invFun := scalePt (scale_inv hR)
  left_inv := scale_left_inv hR
  right_inv := scale_right_inv hR
  map_add' := scale_add hR

theorem twist_rel (E : EllipticCurveRank.RatEllipticCurve) (a b : ℕ) (hb : 0 < b) :
    ScaleRel (E.quadraticTwist (a : ℤ)) (E.quadraticTwist ((b ^ 2 * a : ℕ) : ℤ)) (b : ℚ) := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨hb', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [EllipticCurveRank.RatEllipticCurve.quadraticTwist]
    push_cast
    ring
  · simp only [EllipticCurveRank.RatEllipticCurve.quadraticTwist]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution :
    OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1.H2 := by
  intro E a b _ hb
  exact ⟨(OMA.Helpers.scaleEquiv (OMA.Helpers.twist_rel E a b hb)).symm⟩
