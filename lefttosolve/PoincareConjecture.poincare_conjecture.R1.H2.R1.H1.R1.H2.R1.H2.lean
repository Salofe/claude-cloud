import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1
import Mathlib

namespace OMA.Helpers

open CategoryTheory Limits

/-- A morphism of topological spaces whose underlying map is injective is mono. -/
theorem topMono {A B : TopCat} (f : A ⟶ B) (hf : Function.Injective f) : Mono f :=
  (TopCat.mono_iff_injective f).mpr hf

/-- A lift into a biproduct is mono as soon as its first component is mono. -/
theorem liftMono {A B C : ChainComplex AddCommGrpCat ℕ} (f : A ⟶ B) (g : A ⟶ C) (hf : Mono f) :
    Mono (biprod.lift f g) :=
  mono_of_mono_fac (biprod.lift_fst f g)

end OMA.Helpers

open CategoryTheory Limits

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro X _ U V
  dsimp only
  -- the inclusion of the intersection into the first open set is injective, hence mono
  have hL : Mono (TopCat.ofHom ⟨Set.inclusion (Set.inter_subset_left (s := U) (t := V)),
      continuous_inclusion (Set.inter_subset_left (s := U) (t := V))⟩ :
        TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U) :=
    OMA.Helpers.topMono _ (fun a b h => Set.inclusion_injective Set.inter_subset_left h)
  -- singular chains preserve monomorphisms
  have hI : Mono (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom ⟨Set.inclusion (Set.inter_subset_left (s := U) (t := V)),
        continuous_inclusion (Set.inter_subset_left (s := U) (t := V))⟩ :
          TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U)) :=
    Functor.map_mono _ _
  -- the pushout square gives a right exact sequence; injectivity on the left is `hI`
  exact
    { exact := (IsPushout.of_hasPushout _ _).exact_shortComplex
      mono_f := OMA.Helpers.liftMono _ _ hI
      epi_g := (IsPushout.of_hasPushout _ _).epi_shortComplex_g }
