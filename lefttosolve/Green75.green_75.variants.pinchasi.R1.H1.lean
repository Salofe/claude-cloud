import OMAReductions.R_Green75_green_75_variants_pinchasi_R1
import Mathlib

/-!
# Step H1 of the reduction Green75.green_75.variants.pinchasi.R1

The shear `(x, y) ↦ (x + s y, y)` has determinant one, so it preserves every cross product
`cross p q x` and hence every left count, right count and imbalance. A finite set `X` has only
finitely many bad slopes `s`, namely `(q.1 - p.1) / (p.2 - q.2)` for points `p, q` of `X` with
`p.2 ≠ q.2`; any other `s` makes the first coordinates of the sheared points distinct.

Only the upstream definitions `Green75.cross`, `Green75.leftCount`, `Green75.rightCount` and
`Green75.imbalance` are used.
-/

namespace OMA.Helpers

/-- The shear `(x, y) ↦ (x + s y, y)` as an embedding of the plane. -/
def green75Shear (s : ℝ) : (ℝ × ℝ) ↪ (ℝ × ℝ) :=
  ⟨fun z => (z.1 + s * z.2, z.2), by
    intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext
    · rw [h2] at h1
      linarith
    · exact h2⟩

theorem green75_shear_apply (s : ℝ) (z : ℝ × ℝ) :
    green75Shear s z = (z.1 + s * z.2, z.2) := rfl

/-- A shear preserves the cross product. -/
theorem green75_cross_shear (s : ℝ) (p q x : ℝ × ℝ) :
    Green75.cross (green75Shear s p) (green75Shear s q) (green75Shear s x) =
      Green75.cross p q x := by
  simp only [green75_shear_apply, Green75.cross]
  ring

theorem green75_leftCount_shear (s : ℝ) (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) :
    Green75.leftCount (X.map (green75Shear s)) (green75Shear s p) (green75Shear s q) =
      Green75.leftCount X p q := by
  unfold Green75.leftCount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp only [Function.comp_apply, green75_cross_shear]

theorem green75_rightCount_shear (s : ℝ) (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) :
    Green75.rightCount (X.map (green75Shear s)) (green75Shear s p) (green75Shear s q) =
      Green75.rightCount X p q := by
  unfold Green75.rightCount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp only [Function.comp_apply, green75_cross_shear]

theorem green75_imbalance_shear (s : ℝ) (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) :
    Green75.imbalance (X.map (green75Shear s)) (green75Shear s p) (green75Shear s q) =
      Green75.imbalance X p q := by
  unfold Green75.imbalance
  rw [green75_leftCount_shear, green75_rightCount_shear]

end OMA.Helpers

theorem OMA.solution : OMA.R_Green75_green_75_variants_pinchasi_R1.H1 := by
  classical
  intro X
  let S : Finset ℝ := ((X ×ˢ X).filter (fun pq => pq.1.2 ≠ pq.2.2)).image
    (fun pq => (pq.2.1 - pq.1.1) / (pq.1.2 - pq.2.2))
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset S
  refine ⟨OMA.Helpers.green75Shear s, ?_,
    fun p q => OMA.Helpers.green75_imbalance_shear s X p q⟩
  intro a ha b hb hab
  rw [Finset.coe_map, Set.mem_image] at ha hb
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := hb
  simp only [OMA.Helpers.green75_shear_apply] at hab ⊢
  by_cases h2 : p.2 = q.2
  · have h1 : p.1 = q.1 := by
      rw [h2] at hab
      linarith
    rw [h1, h2]
  · exfalso
    apply hs
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp, hq⟩, h2⟩, ?_⟩
    have hne : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr h2
    show (q.1 - p.1) / (p.2 - q.2) = s
    rw [div_eq_iff hne]
    linear_combination -hab
