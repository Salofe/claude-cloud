import OMAReductions.R_OeisA78729_conjecture_R1

namespace OMA.Helpers

theorem a78729_prod_four (k : ℕ) :
    ∏ i ∈ Finset.range 4, (k + i + 1) + 1 = (k ^ 2 + 5 * k + 5) ^ 2 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  ring

theorem a78729_not_prime (k : ℕ) :
    ¬ (∏ i ∈ Finset.range 4, (k + i + 1) + 1).Prime := by
  rw [a78729_prod_four]
  exact Nat.Prime.not_prime_pow (le_refl 2)

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA78729_conjecture_R1.H1 := by
  intro n hn
  subst hn
  unfold OeisA78729.a
  rw [dif_neg]
  rintro ⟨k, _, hk⟩
  exact OMA.Helpers.a78729_not_prime k hk
