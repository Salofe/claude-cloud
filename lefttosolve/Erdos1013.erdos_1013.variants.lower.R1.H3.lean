import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1
import Mathlib

namespace OMA.Helpers

/-- A graph on `Fin m` has chromatic number at most `m`. -/
lemma chi_le_size {m χ : ℕ} (G : SimpleGraph (Fin m)) (h : G.chromaticNumber = χ) : χ ≤ m := by
  have hle := G.chromaticNumber_le_card
  rw [h, Fintype.card_fin] at hle
  exact_mod_cast hle

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H3 := by
  intro k _ hex
  have hmem : Erdos1013.h3 k ∈
      {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k} :=
    Nat.sInf_mem hex
  obtain ⟨G, hG, hχ⟩ := hmem
  have hk : k ≤ Erdos1013.h3 k := OMA.Helpers.chi_le_size G hχ
  refine ⟨hk, ?_⟩
  apply le_csSup
  · refine ⟨Erdos1013.h3 k, ?_⟩
    rintro χ ⟨G', -, hG'⟩
    exact OMA.Helpers.chi_le_size G' hG'
  · exact ⟨G, hG, hχ⟩
