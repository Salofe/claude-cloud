import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1_H2_R1
import Mathlib.Algebra.Homology.HomologySequenceLemmas

open CategoryTheory Limits

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro K L A i j f w _ _ hiso n
  have hS₁ : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i
      mono_f := show Mono i from inferInstance }
  have hS₂ : (ShortComplex.cokernelSequence j).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact j
      mono_f := show Mono j from inferInstance }
  let φ : ShortComplex.cokernelSequence i ⟶ ShortComplex.cokernelSequence j :=
    { τ₁ := 𝟙 A
      τ₂ := f
      τ₃ := cokernel.map i j (𝟙 A) f (by simp [w])
      comm₁₂ := (Category.id_comp j).trans w.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  have hid : ∀ k, IsIso (HomologicalComplex.homologyMap (𝟙 A) k) := fun k => by
    rw [HomologicalComplex.homologyMap_id]; infer_instance
  have h := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ n
    (@IsIso.epi_of_iso _ _ _ _ _ (hid n))
    (hiso n)
    (fun k _ => hid k)
    (fun k _ => @IsIso.mono_of_iso _ _ _ _ _ (hiso k))
  exact h
