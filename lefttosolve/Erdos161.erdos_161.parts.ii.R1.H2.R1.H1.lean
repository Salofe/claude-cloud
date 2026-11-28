import OMAReductions.R_Erdos161_erdos_161_parts_ii_R1_H2_R1

/-!
# Step H1 of the reduction Erdos161.erdos_161.parts.ii.R1.H2.R1

Finite hypergraph Ramsey theorem for two colorings of t-subsets, proved by induction on t.
For the inductive step we first build a set on which the color of a (t+1)-subset depends
only on its least element (greedy choice of the least element, then the induction
hypothesis applied to the coloring of t-subsets of the rest), and finish by pigeonhole on
the two colors. The statement is first proved for finite sets of naturals and then
transported to Fin R.
-/

namespace OMA.Helpers


theorem prehom (t : ℕ)
    (ih : ∀ d : ℕ, ∃ R : ℕ, ∀ X : Finset ℕ, R ≤ X.card →
      ∀ col : Finset ℕ → Bool, ∃ S ⊆ X, S.card = d ∧ ∃ b : Bool,
        ∀ e ⊆ S, e.card = t → col e = b) :
    ∀ k : ℕ, ∃ M : ℕ, ∀ X : Finset ℕ, M ≤ X.card → ∀ col : Finset ℕ → Bool,
      ∃ S ⊆ X, S.card = k ∧ ∃ c : ℕ → Bool, ∀ e ⊆ S, e.card = t + 1 →
        ∀ m ∈ e, (∀ x ∈ e, m ≤ x) → col e = c m := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, fun X _ col => ⟨∅, Finset.empty_subset _, rfl, fun _ => true, ?_⟩⟩
    intro e he hc
    rw [Finset.subset_empty.mp he] at hc
    simp at hc
  | succ k ihk =>
    obtain ⟨M, hM⟩ := ihk
    obtain ⟨R, hR⟩ := ih M
    refine ⟨R + 1, fun X hX col => ?_⟩
    have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
    set a := X.min' hXne with ha
    have haX : a ∈ X := X.min'_mem hXne
    have hamin : ∀ x ∈ X, a ≤ x := fun x hx => X.min'_le x hx
    have hX' : R ≤ (X.erase a).card := by
      rw [Finset.card_erase_of_mem haX]; omega
    obtain ⟨Y, hYX, hYc, β, hβ⟩ := hR (X.erase a) hX' (fun T => col (insert a T))
    obtain ⟨S', hS'Y, hS'c, c', hc'⟩ := hM Y (by omega) col
    have haS' : a ∉ S' := fun h => by
      have := hYX (hS'Y h)
      simp at this
    refine ⟨insert a S', ?_, ?_, Function.update c' a β, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haX
      · exact Finset.mem_of_mem_erase (hYX (hS'Y hx))
    · rw [Finset.card_insert_of_notMem haS', hS'c]
    · intro e he hec m hm hmin
      by_cases hae : a ∈ e
      · have hma : m = a := by
          apply le_antisymm (hmin a hae)
          apply hamin
          rcases Finset.mem_insert.mp (he hm) with h | h
          · rw [h]; exact haX
          · exact Finset.mem_of_mem_erase (hYX (hS'Y h))
        subst hma
        rw [Function.update_self]
        have hsub : e.erase a ⊆ Y := by
          intro x hx
          obtain ⟨hxm, hxe⟩ := Finset.mem_erase.mp hx
          rcases Finset.mem_insert.mp (he hxe) with h | h
          · exact absurd h hxm
          · exact hS'Y h
        have hcard : (e.erase a).card = t := by
          rw [Finset.card_erase_of_mem hae, hec]; rfl
        have := hβ (e.erase a) hsub hcard
        simpa [Finset.insert_erase hae] using this
      · have hsub : e ⊆ S' := by
          intro x hx
          rcases Finset.mem_insert.mp (he hx) with h | h
          · exact absurd (h ▸ hx) hae
          · exact h
        have hma : m ≠ a := fun h => hae (h ▸ hm)
        rw [Function.update_of_ne hma]
        exact hc' e hsub hec m hm hmin

theorem ramsey_finset (t : ℕ) : ∀ d : ℕ, ∃ R : ℕ, ∀ X : Finset ℕ, R ≤ X.card →
    ∀ col : Finset ℕ → Bool, ∃ S ⊆ X, S.card = d ∧ ∃ b : Bool,
      ∀ e ⊆ S, e.card = t → col e = b := by
  induction t with
  | zero =>
    intro d
    refine ⟨d, fun X hX col => ?_⟩
    obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hX
    refine ⟨S, hS, hSc, col ∅, fun e _ he => ?_⟩
    rw [Finset.card_eq_zero.mp he]
  | succ t ih =>
    intro d
    obtain ⟨M, hM⟩ := prehom t ih (2 * d)
    refine ⟨M, fun X hX col => ?_⟩
    obtain ⟨S, hSX, hSc, c, hc⟩ := hM X hX col
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => c x = true)
    have key : ∀ b : Bool, d ≤ (S.filter (fun x => c x = b)).card →
        ∃ T ⊆ X, T.card = d ∧ ∃ b : Bool, ∀ e ⊆ T, e.card = t + 1 → col e = b := by
      intro b hb
      obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hb
      refine ⟨T, fun x hx => hSX (Finset.mem_filter.mp (hT hx)).1, hTc, b, ?_⟩
      intro e he hec
      have hne : e.Nonempty := Finset.card_pos.mp (by omega)
      have hm := e.min'_mem hne
      rw [hc e (fun x hx => (Finset.mem_filter.mp (hT (he hx))).1) hec (e.min' hne) hm
        (fun x hx => e.min'_le x hx)]
      exact (Finset.mem_filter.mp (hT (he hm))).2
    by_cases h : d ≤ (S.filter (fun x => c x = true)).card
    · exact key true h
    · apply key false
      have : (S.filter (fun x => ¬ c x = true)) = S.filter (fun x => c x = false) := by
        apply Finset.filter_congr
        intro x _
        simp
      rw [← this]
      omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos161_erdos_161_parts_ii_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos161_erdos_161_parts_ii_R1_H2_R1.H1
  intro t d _ _
  obtain ⟨R0, hR0⟩ := OMA.Helpers.ramsey_finset t d
  refine ⟨max R0 d, le_max_right _ _, fun col => ?_⟩
  let col' : Finset ℕ → Bool := fun e =>
    col (Finset.univ.filter (fun i : Fin (max R0 d) => (i : ℕ) ∈ e))
  obtain ⟨S, hSX, hSc, b, hb⟩ := hR0 (Finset.range (max R0 d)) (by simp) col'
  have hmap : (Finset.univ.filter (fun i : Fin (max R0 d) => (i : ℕ) ∈ S)).map Fin.valEmbedding = S := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, Finset.mem_range.mp (hSX hx)⟩, hx, rfl⟩
  refine ⟨b, Finset.univ.filter (fun i : Fin (max R0 d) => (i : ℕ) ∈ S), ?_, ?_⟩
  · rw [← Finset.card_map Fin.valEmbedding, hmap, hSc]
  · intro e he hec
    have h1 : e.map Fin.valEmbedding ⊆ S := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_filter.mp (he hi)).2
    have h2 := hb (e.map Fin.valEmbedding) h1 (by rw [Finset.card_map, hec])
    have h3 : Finset.univ.filter (fun i : Fin (max R0 d) => (i : ℕ) ∈ e.map Fin.valEmbedding) = e := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Fin.valEmbedding_apply]
      constructor
      · rintro ⟨j, hj, hji⟩
        rwa [← Fin.ext hji]
      · intro hi
        exact ⟨i, hi, rfl⟩
    have h4 : col' (e.map Fin.valEmbedding) = col e := by
      simp only [col']
      rw [h3]
    rw [← h4]
    exact h2
