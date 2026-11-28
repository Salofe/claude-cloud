import OMAStatements.S_mo_252065
import Mathlib

namespace OMA.Helpers
open OMA.S_mo_252065 Module

abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem le_two {S T : Submodule ℝ E3} (h : S.IsOrtho T) (hT : 1 ≤ finrank ℝ T) :
    finrank ℝ S ≤ 2 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal T
  have h2 : finrank ℝ S ≤ finrank ℝ Tᗮ := Submodule.finrank_mono (Submodule.isOrtho_iff_le.mp h)
  rw [finrank_euclideanSpace_fin] at h1
  omega

theorem eq_orth {S T : Submodule ℝ E3} (h : S.IsOrtho T) (hS : finrank ℝ S = 2)
    (hT : 1 ≤ finrank ℝ T) : T = Sᗮ := by
  have h1 := Submodule.finrank_add_finrank_orthogonal S
  rw [finrank_euclideanSpace_fin] at h1
  exact Submodule.eq_of_le_of_finrank_le (Submodule.isOrtho_iff_le.mp h.symm) (by omega)

theorem dim_one {A B1 B2 C : Submodule ℝ E3} (hA : 1 ≤ finrank ℝ A) (h1 : 1 ≤ finrank ℝ B1)
    (h2 : 1 ≤ finrank ℝ B2) (hAB1 : A.IsOrtho B1) (hAB2 : A.IsOrtho B2)
    (hC1 : C.IsOrtho B1) (hC2 : ¬ C.IsOrtho B2) : finrank ℝ A = 1 := by
  have hle := le_two hAB1 h1
  by_contra hne
  have h2' : finrank ℝ A = 2 := by omega
  have e1 := eq_orth hAB1 h2' h1
  have e2 := eq_orth hAB2 h2' h2
  exact hC2 (e2 ▸ e1 ▸ hC1)

theorem key : ∀ S T : Fin 4 → Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      (∀ i, 1 ≤ Module.finrank ℝ (S i)) → (∀ j, 1 ≤ Module.finrank ℝ (T j)) →
      (∀ i j, M i j = 0 ↔ (S i).IsOrtho (T j)) →
      (∀ i, Module.finrank ℝ (S i) = 1) ∧ (∀ j, Module.finrank ℝ (T j) = 1) := by
  intro S T hS hT hM
  have o : ∀ i j, M i j = 0 → (S i).IsOrtho (T j) := fun i j h => (hM i j).mp h
  have no : ∀ i j, M i j ≠ 0 → ¬ (S i).IsOrtho (T j) := fun i j h h' => h ((hM i j).mpr h')
  refine ⟨fun i => ?_, fun j => ?_⟩
  · fin_cases i
    · exact dim_one (hS 0) (hT 1) (hT 2) (o 0 1 rfl) (o 0 2 rfl) (o 1 1 rfl) (no 1 2 (by decide))
    · exact dim_one (hS 1) (hT 1) (hT 3) (o 1 1 rfl) (o 1 3 rfl) (o 0 1 rfl) (no 0 3 (by decide))
    · exact dim_one (hS 2) (hT 2) (hT 0) (o 2 2 rfl) (o 2 0 rfl) (o 0 2 rfl) (no 0 0 (by decide))
    · exact dim_one (hS 3) (hT 3) (hT 0) (o 3 3 rfl) (o 3 0 rfl) (o 1 3 rfl) (no 1 0 (by decide))
  · fin_cases j
    · exact dim_one (hT 0) (hS 2) (hS 3) (o 2 0 rfl).symm (o 3 0 rfl).symm (o 2 2 rfl).symm
        (fun h => no 3 2 (by decide) h.symm)
    · exact dim_one (hT 1) (hS 0) (hS 1) (o 0 1 rfl).symm (o 1 1 rfl).symm (o 0 2 rfl).symm
        (fun h => no 1 2 (by decide) h.symm)
    · exact dim_one (hT 2) (hS 2) (hS 0) (o 2 2 rfl).symm (o 0 2 rfl).symm (o 2 0 rfl).symm
        (fun h => no 0 0 (by decide) h.symm)
    · exact dim_one (hT 3) (hS 3) (hS 1) (o 3 3 rfl).symm (o 1 3 rfl).symm (o 3 0 rfl).symm
        (fun h => no 1 0 (by decide) h.symm)

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_252065.main := OMA.Helpers.key
