import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1_H1_R1
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst


/-!
# Step H2 of the reduction PoincareConjecture.poincare_conjecture.R1.H2.R1.H1.R1.H2.R1.H1.R1

The map from the pushout of the singular chain complexes of `U` and `V` over `U ∩ V` to the
singular chain complex of `U ∪ V` is a monomorphism.

* A morphism of chain complexes is a monomorphism as soon as every component is one.
* In degree `n`, the chain groups are `sigmaConst.obj ℤ` applied to the sets of singular
  `n`-simplices. This functor preserves pushouts and monomorphisms (Mathlib instances), and
  evaluation at `n` preserves pushouts of chain complexes.
* On simplex sets the square `U ∩ V → U, V → U ∪ V` is a pullback with injective legs, so by
  `Types.mono_of_isPushout_of_isPullback` the induced map out of the pushout of simplex sets
  is injective. Its image under `sigmaConst.obj ℤ` is a monomorphism, and comparing the two
  pushouts of the same span transports this to the chain level.

Only Mathlib is used; no upstream theorem is invoked.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace OMA.Helpers

/-- A monomorphism out of one pushout transports to any other pushout of the same span. -/
theorem poincare_mono_transport {𝒞 : Type*} [Category 𝒞] {W X Y P P' Z : 𝒞} {f : W ⟶ X}
    {g : W ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} {inl' : X ⟶ P'} {inr' : Y ⟶ P'}
    (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') (k : P ⟶ Z) (k' : P' ⟶ Z)
    (hl : CategoryStruct.comp inl k = CategoryStruct.comp inl' k')
    (hr : CategoryStruct.comp inr k = CategoryStruct.comp inr' k') (hk : Mono k') : Mono k := by
  have e : k = CategoryStruct.comp (h.isoIsPushout _ _ h').hom k' := by
    apply h.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom_assoc, hl]
    · rw [IsPushout.inr_isoIsPushout_hom_assoc, hr]
  rw [e]
  exact mono_comp _ _

/-- Degreewise criterion: if on every simplex level the square of simplex sets is a pullback
with injective right and bottom maps, the induced map from the pushout of singular chain
complexes is a monomorphism. -/
theorem poincare_chain_mono {A B D E : TopCat.{0}} (i : A ⟶ B) (j : A ⟶ D) (l : B ⟶ E)
    (r : D ⟶ E)
    (hpb : ∀ m : SimplexCategoryᵒᵖ, IsPullback ((TopCat.toSSet.map i).app m)
      ((TopCat.toSSet.map j).app m) ((TopCat.toSSet.map l).app m) ((TopCat.toSSet.map r).app m))
    (hl : ∀ m : SimplexCategoryᵒᵖ, Mono ((TopCat.toSSet.map l).app m))
    (hr : ∀ m : SimplexCategoryᵒᵖ, Function.Injective ((TopCat.toSSet.map r).app m))
    (w : CategoryStruct.comp
        (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map i)
        (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map l) =
      CategoryStruct.comp
        (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map j)
        (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map r)) :
    Mono (pushout.desc
      (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map l)
      (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map r) w) := by
  set C := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ) with hC
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let F := sigmaConst.obj (AddCommGrpCat.of ℤ)
  let m : SimplexCategoryᵒᵖ := Opposite.op (SimplexCategory.mk n)
  let t := (TopCat.toSSet.map i).app m
  let lT := (TopCat.toSSet.map j).app m
  let rT := (TopCat.toSSet.map l).app m
  let bT := (TopCat.toSSet.map r).app m
  have hPT := IsPushout.of_hasPushout t lT
  have hk : Mono (pushout.desc rT bT (hpb m).w) := by
    have := hl m
    exact Types.mono_of_isPushout_of_isPullback hPT (hpb m) (pushout.inl_desc _ _ _)
      (pushout.inr_desc _ _ _) (fun x y _ _ hxy => hr m hxy)
  have hPF := F.map_isPushout hPT
  have hPC := (HomologicalComplex.eval _ _ n).map_isPushout
    (IsPushout.of_hasPushout (C.map i) (C.map j))
  have hPF' : IsPushout ((HomologicalComplex.eval _ _ n).map (C.map i))
      ((HomologicalComplex.eval _ _ n).map (C.map j)) (F.map (pushout.inl t lT))
      (F.map (pushout.inr t lT)) := hPF
  have hmk : Mono (F.map (pushout.desc rT bT (hpb m).w)) := inferInstance
  exact poincare_mono_transport hPC hPF' ((HomologicalComplex.eval _ _ n).map
      (pushout.desc (C.map l) (C.map r) w)) (F.map (pushout.desc rT bT (hpb m).w))
    ((((HomologicalComplex.eval _ _ n).map_comp _ _).symm.trans
        (congrArg (HomologicalComplex.eval _ _ n).map (pushout.inl_desc _ _ _))).trans
      ((congrArg F.map (pushout.inl_desc rT bT (hpb m).w)).symm.trans (F.map_comp _ _)))
    ((((HomologicalComplex.eval _ _ n).map_comp _ _).symm.trans
        (congrArg (HomologicalComplex.eval _ _ n).map (pushout.inr_desc _ _ _))).trans
      ((congrArg F.map (pushout.inr_desc rT bT (hpb m).w)).symm.trans (F.map_comp _ _)))
    hmk

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro X _ U V C i j l r h
  refine poincare_chain_mono i j l r ?_ ?_ ?_ h
  · intro m
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · intro x y hxy
      obtain ⟨hxy, _⟩ := hxy
      have h1 := congrArg ULift.down hxy
      change CategoryStruct.comp x.down i = CategoryStruct.comp y.down i at h1
      apply ULift.ext
      refine TopCat.ext (fun s => ?_)
      have h2 := congrArg (fun f => (ConcreteCategory.hom f s).1) h1
      exact Subtype.ext h2
    · intro x y hxy
      have h1 := congrArg ULift.down hxy
      change CategoryStruct.comp x.down l = CategoryStruct.comp y.down r at h1
      have hmem : ∀ s, (ConcreteCategory.hom x.down s).1 ∈ U ∩ V := fun s =>
        ⟨(ConcreteCategory.hom x.down s).2, by
          have h2 := congrArg (fun f => (ConcreteCategory.hom f s).1) h1
          change (ConcreteCategory.hom x.down s).1 = (ConcreteCategory.hom y.down s).1 at h2
          rw [h2]
          exact (ConcreteCategory.hom y.down s).2⟩
      refine ⟨ULift.up (TopCat.ofHom ⟨fun s => ⟨(ConcreteCategory.hom x.down s).1, hmem s⟩,
        Continuous.subtype_mk (continuous_subtype_val.comp
          (ConcreteCategory.hom x.down).continuous) _⟩), ?_, ?_⟩
      · apply ULift.ext
        refine TopCat.ext (fun s => ?_)
        rfl
      · apply ULift.ext
        refine TopCat.ext (fun s => ?_)
        have h2 := congrArg (fun f => (ConcreteCategory.hom f s).1) h1
        exact Subtype.ext h2
  · intro m
    rw [mono_iff_injective]
    intro x y hxy
    have h1 := congrArg ULift.down hxy
    change CategoryStruct.comp x.down l = CategoryStruct.comp y.down l at h1
    apply ULift.ext
    refine TopCat.ext (fun s => ?_)
    have h2 := congrArg (fun f => (ConcreteCategory.hom f s).1) h1
    exact Subtype.ext h2
  · intro m x y hxy
    have h1 := congrArg ULift.down hxy
    change CategoryStruct.comp x.down r = CategoryStruct.comp y.down r at h1
    apply ULift.ext
    refine TopCat.ext (fun s => ?_)
    have h2 := congrArg (fun f => (ConcreteCategory.hom f s).1) h1
    exact Subtype.ext h2
