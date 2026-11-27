import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1
import Mathlib

/-!
# Step H3 of the reduction PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1

Given charts `c i`, affine maps `b i` and projection fields `Q i` with the stated kernel and
right-inverse properties, the transition `c j ∘ (c i).symm` has an explicit formula on its
domain: with `T z = Q i (b i z) ∘ (b j).contLinear`, which is invertible there, one has
`c j ((c i).symm z) = (T z)⁻¹ (Q i (b i z) (b i z - b j 0))`. This expression is smooth since
`Q i` is smooth along `b i` and inversion of continuous linear equivalences is smooth.
Hence the charts `c` form a smooth atlas.
-/

open Set Geometry
open scoped Manifold ContDiff

namespace OMA.Helpers

theorem transition_smooth {m : ℕ} {M : Type} [TopologicalSpace M]
    (c : M → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (v : M → EuclideanSpace ℝ (Fin m)) (P : M → Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (b : M → EuclideanSpace ℝ (Fin 3) →ᴬ[ℝ] EuclideanSpace ℝ (Fin m))
    (Q : M → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hsm : ∀ i z, z ∈ (c i).target → ContDiffAt ℝ ∞ (Q i) (b i z))
    (hlin : ∀ i y, y ∈ (c i).source → Function.RightInverse (b i).contLinear (Q i (v y)) ∧
      (Q i (v y)).ker = P y ∧ Q i (b i (c i y)) = Q i (v y) ∧ b i (c i y) - v y ∈ P y)
    (i j : M) :
    ContDiffOn ℝ ∞ ((c i).symm ≫ₕ c j) ((c i).symm ≫ₕ c j).source := by
  let T : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun z => (Q i (b i z)).comp (b j).contLinear
  let Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun z => (T z).inverse (Q i (b i z) (b i z - b j 0))
  have key : ∀ z ∈ ((c i).symm ≫ₕ c j).source,
      ∃ e : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3),
        (e : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) = T z ∧
        Φ z = ((c i).symm ≫ₕ c j) z := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hzt, hzj⟩ := hz
    set y := (c i).symm z with hy
    have hyi : y ∈ (c i).source := (c i).map_target hzt
    have hzi : c i y = z := (c i).right_inv hzt
    obtain ⟨-, hki, hQi, hmi⟩ := hlin i y hyi
    obtain ⟨hrj, hkj, -, hmj⟩ := hlin j y hzj
    rw [hzi] at hQi hmi
    have hTz : T z = (Q i (v y)).comp (b j).contLinear := by
      simp only [T, hQi]
    have hinj : (T z).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro u hu
      have h1 : (b j).contLinear u ∈ P y := by
        rw [← hki, LinearMap.mem_ker]
        rw [hTz] at hu
        simpa using hu
      rw [← hkj, LinearMap.mem_ker] at h1
      have := hrj u
      simp only at this
      rw [← this]
      exact h1
    have hsurj : (T z).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      have hi : Function.Injective ((T z : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
          EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :=
        LinearMap.ker_eq_bot.mp hinj
      exact LinearMap.injective_iff_surjective.mp hi
    let e := ContinuousLinearEquiv.ofBijective (T z) hinj hsurj
    refine ⟨e, ContinuousLinearEquiv.coe_ofBijective _ _ _, ?_⟩
    have hw : T z (c j y) = Q i (b i z) (b i z - b j 0) := by
      have hsplit : (b j).contLinear (c j y) = b j (c j y) - b j 0 := by
        have := (b j).contLinear_map_vsub (c j y) 0
        simpa [vsub_eq_sub] using this
      have hdiff : b j (c j y) - b i z ∈ P y := by
        have := Submodule.sub_mem _ hmj hmi
        simpa using this
      rw [← hki, LinearMap.mem_ker] at hdiff
      simp only [ContinuousLinearMap.coe_coe] at hdiff
      have h3 : b i z - b j 0 = (b j (c j y) - b j 0) - (b j (c j y) - b i z) := by abel
      have h2 : Q i (v y) (b i z - b j 0) = Q i (v y) (b j (c j y) - b j 0) := by
        rw [h3, map_sub, hdiff, sub_zero]
      rw [hTz, hQi, h2]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hsplit]
    have hinv : (T z).IsInvertible := ⟨e, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
    simp only [Φ, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rw [← hw, ContinuousLinearMap.IsInvertible.inverse_apply_self hinv]
  intro z hz
  obtain ⟨e, he, -⟩ := key z hz
  have hz' := hz
  rw [OpenPartialHomeomorph.trans_source] at hz'
  have hQ : ContDiffAt ℝ ∞ (fun z => Q i (b i z)) z :=
    (hsm i z hz'.1).comp z
      (b i).contDiff.contDiffAt
  have hT : ContDiffAt ℝ ∞ T z := hQ.clm_comp contDiffAt_const
  have hinv : ContDiffAt ℝ ∞ (fun z => (T z).inverse) z := by
    have := contDiffAt_map_inverse (n := ∞) e
    rw [he] at this
    exact this.comp z hT
  have hrhs : ContDiffAt ℝ ∞ (fun z => Q i (b i z) (b i z - b j 0)) z :=
    hQ.clm_apply (((b i).contDiff.contDiffAt).sub contDiffAt_const)
  have hΦ : ContDiffAt ℝ ∞ Φ z := hinv.clm_apply hrhs
  refine hΦ.contDiffWithinAt.congr (fun z' hz' => ?_) ?_
  · exact ((key z' hz').choose_spec.2).symm
  · exact ((key z hz).choose_spec.2).symm

end OMA.Helpers

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1.H3 := by
  intro m M _
  dsimp only
  intro c v P b Q hyp
  obtain ⟨hcov, hsm, hlin⟩ := hyp
  let atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
    { atlas := range c
      chartAt := fun y => c (hcov y).choose
      mem_chart_source := fun y => (hcov y).choose_spec
      chart_mem_atlas := fun y => mem_range_self _ }
  refine ⟨atlas, ?_⟩
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
    Function.id_comp, Function.comp_id, preimage_id, inter_univ]
  exact OMA.Helpers.transition_smooth c v P b Q hsm hlin i j
