import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2

/-!
# Step H2 of the reduction Erdos835.erdos_835.variants.johnson.R2

Let `c` colour the subsets of `2p - 3` points with the `p` colours of `Fin p`, and suppose that every
`(p - 3)`-subset `T` extends to each colour: for every colour `γ` some `y ∉ T` has
`c (insert y T) = γ`. Take `(p - 2)`-sets `A`, `B` meeting in `p - 3` points and put `T = A ∩ B`.
Then `A = insert a T` and `B = insert b T` with `a, b ∉ T`. The map `y ↦ c (insert y T)` sends the
`p` points outside `T` onto the `p` colours, so it is injective there. Hence `c A = c B` would force
`a = b`, that is `A = B`, against `#(A ∩ B) = p - 3 < p - 2 = #A`. Primality of `p` is not needed.

Only Mathlib and the definition `H2` of the reduction are used.
-/

namespace OMA.Helpers

/-- If every colour `γ` is `c (insert y T)` for some `y ∉ T`, and there are no more points outside
`T` than colours, then two points outside `T` that give `T` the same colour are equal. -/
theorem eq_of_color_insert_eq {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (c : Finset α → β) (T : Finset α)
    (hcov : ∀ γ : β, ∃ y : α, y ∉ T ∧ c (insert y T) = γ)
    (hcard : Fintype.card α - T.card ≤ Fintype.card β)
    {a b : α} (ha : a ∉ T) (hb : b ∉ T) (hab : c (insert a T) = c (insert b T)) : a = b := by
  have hinj : Set.InjOn (fun y => c (insert y T)) (Tᶜ : Finset α) := by
    refine Finset.injOn_of_surjOn_of_card_le (t := (Finset.univ : Finset β)) _ ?_ ?_ ?_
    · intro y _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro γ _
      obtain ⟨y, hyT, hy⟩ := hcov γ
      exact ⟨y, Finset.mem_coe.mpr (Finset.mem_compl.mpr hyT), hy⟩
    · rw [Finset.card_compl, Finset.card_univ]
      exact hcard
  exact hinj (Finset.mem_coe.mpr (Finset.mem_compl.mpr ha))
    (Finset.mem_coe.mpr (Finset.mem_compl.mpr hb)) hab

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H2 := by
  intro p _hp hp5 c hcov A B hA hB hAB hc
  obtain ⟨a, haT, hAa⟩ : ∃ a ∉ A ∩ B, insert a (A ∩ B) = A :=
    Finset.exists_eq_insert_iff.mpr ⟨Finset.inter_subset_left, by omega⟩
  obtain ⟨b, hbT, hBb⟩ : ∃ b ∉ A ∩ B, insert b (A ∩ B) = B :=
    Finset.exists_eq_insert_iff.mpr ⟨Finset.inter_subset_right, by omega⟩
  have hcard : Fintype.card (Fin (2 * p - 3)) - (A ∩ B).card ≤ Fintype.card (Fin p) := by
    simp only [Fintype.card_fin]
    omega
  have hab : a = b :=
    OMA.Helpers.eq_of_color_insert_eq c (A ∩ B) (hcov (A ∩ B) hAB) hcard haT hbT
      (by rw [hAa, hBb]; exact hc)
  have hAeqB : A = B := by rw [← hAa, hab, hBb]
  rw [hAeqB, Finset.inter_self] at hAB
  omega
