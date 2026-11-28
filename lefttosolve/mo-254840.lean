import OMAStatements.S_mo_254840
import Mathlib

namespace OMA.Helpers

/-- Casting an integer sign vector to a rational vector. -/
def qvec {n : ℕ} (a : Fin n → ℤ) : Fin n → ℚ := fun i => (a i : ℚ)

theorem qvec_injective (n : ℕ) : Function.Injective (@qvec n) := by
  intro a b h
  funext i
  have := congrFun h i
  simp only [qvec] at this
  exact_mod_cast this

theorem qvec_dot {n : ℕ} (a b : Fin n → ℤ) :
    dotProduct (qvec a) (qvec b) = ((∑ i, a i * b i : ℤ) : ℚ) := by
  simp [dotProduct, qvec]

theorem signs_card_le (n : ℕ) (S : Finset (Fin n → ℤ))
    (hpm : ∀ a ∈ S, ∀ i, a i = 1 ∨ a i = -1)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∑ i, a i * b i = 0) (hn : 1 ≤ n) :
    S.card ≤ n := by
  classical
  set T : Finset (Fin n → ℚ) := S.image qvec with hTdef
  have hT : T.card = S.card := Finset.card_image_of_injective _ (qvec_injective n)
  have hself : ∀ a ∈ S, dotProduct (qvec a) (qvec a) = (n : ℚ) := by
    intro a ha
    rw [qvec_dot]
    have : ∀ i, a i * a i = 1 := by
      intro i
      rcases hpm a ha i with h | h <;> rw [h] <;> norm_num
    simp [this]
  have hli : LinearIndependent ℚ (fun x => x : T → (Fin n → ℚ)) := by
    rw [linearIndependent_iff']
    intro s g hs j hj
    have h1 := congrArg (fun v => dotProduct v (j : Fin n → ℚ)) hs
    simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct] at h1
    obtain ⟨a, ha, hja⟩ := Finset.mem_image.1 j.2
    rw [Finset.sum_eq_single j] at h1
    · rw [← hja, hself a ha, smul_eq_mul] at h1
      have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      exact (mul_eq_zero.1 h1).resolve_right hn'
    · intro k _ hkj
      obtain ⟨b, hb, hkb⟩ := Finset.mem_image.1 k.2
      have hab : b ≠ a := by
        intro e
        apply hkj
        apply Subtype.ext
        rw [← hkb, ← hja, e]
      rw [← hkb, ← hja, qvec_dot, horth b hb a ha hab]
      simp
    · intro h; exact absurd hj h
  have := hli.finset_card_le_finrank
  rw [Module.finrank_fin_fun] at this
  omega

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_254840.main) := by
  rintro ⟨n, hn, S, hpm, horth, hcard⟩
  have := OMA.Helpers.signs_card_le n S hpm horth hn
  omega
