import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1_H2_R1

/-!
# Step H1: splitting a disconnected graph of minimum degree at least two

Let `S` be the connected component of a vertex `s` of `G`, and `G₁`, `G₂` the subgraphs
induced on `S` and on its complement (renumbered by `Fin`). They are nonempty, smaller than
`G`, contained in `G`, and keep minimum degree at least two since `S` is closed under adjacency.

For the extremal bound, take a host `X` on `n` vertices with more than
`ex(n, G₁) + ex(n, G₂) + q n` edges. It contains a copy of `G₁`; deleting the at most `q n`
edges at its vertices leaves more than `ex(n, G₂)` edges, hence a copy of `G₂`. Every vertex of
`G₂` has a neighbour, so this second copy avoids the vertices of the first one, and the two
copies glue to a copy of `G`.
-/

namespace OMA.Helpers

open SimpleGraph Finset

theorem two_le_degree_of {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (w a b : W) (hab : a ≠ b) (ha : H.Adj w a) (hb : H.Adj w b) : 2 ≤ H.degree w := by
  rw [← card_neighborFinset_eq_degree]
  exact Finset.one_lt_card.mpr
    ⟨a, (mem_neighborFinset _ _ _).mpr ha, b, (mem_neighborFinset _ _ _).mpr hb, hab⟩

theorem exists_two_adj {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (h : 2 ≤ G.degree v) : ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  rw [← card_neighborFinset_eq_degree] at h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  exact ⟨a, b, hab, (mem_neighborFinset _ _ _).mp ha, (mem_neighborFinset _ _ _).mp hb⟩

theorem split_bound {q : ℕ} (G : SimpleGraph (Fin q)) (S : Finset (Fin q))
    (closed : ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S))
    (active : ∀ x, ∃ y, G.Adj x y) (n : ℕ) :
    extremalNumber n G ≤
      extremalNumber n (G.comap (fun u => ((Fintype.equivFin {x // x ∈ S}).symm u).val)) +
      extremalNumber n (G.comap (fun u => ((Fintype.equivFin {x // x ∉ S}).symm u).val)) +
        q * n := by
  classical
  set e1 := Fintype.equivFin {x // x ∈ S}
  set e2 := Fintype.equivFin {x // x ∉ S}
  set G1 := G.comap (fun u => (e1.symm u).val) with hG1
  set G2 := G.comap (fun u => (e2.symm u).val) with hG2
  suffices h : extremalNumber (Fintype.card (Fin n)) G ≤
      extremalNumber n G1 + extremalNumber n G2 + q * n by
    rwa [Fintype.card_fin] at h
  rw [extremalNumber_le_iff]
  intro X _ hfree
  by_contra! hlarge
  have l1 : extremalNumber (Fintype.card (Fin n)) G1 < #X.edgeFinset := by
    rw [Fintype.card_fin]; omega
  obtain ⟨f⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset l1
  let D : Finset (Sym2 (Fin n)) :=
    (univ : Finset (Fin (Fintype.card {x // x ∈ S}))).biUnion (fun v => X.incidenceFinset (f v))
  have hDsub : D ⊆ X.edgeFinset := by
    intro e he
    obtain ⟨v, _, hm⟩ := mem_biUnion.mp he
    exact X.incidenceFinset_subset _ hm
  have hr1 : Fintype.card {x // x ∈ S} ≤ q := by
    have h := Fintype.card_le_of_injective (Subtype.val : {x // x ∈ S} → Fin q)
      Subtype.val_injective
    simpa using h
  have hDcard : D.card ≤ q * n := by
    calc D.card ≤ ∑ v, (X.incidenceFinset (f v)).card := card_biUnion_le
      _ ≤ ∑ _v : Fin (Fintype.card {x // x ∈ S}), n := sum_le_sum fun v _ => by
          rw [card_incidenceFinset_eq_degree]
          simpa using (X.degree_lt_card_verts (f v)).le
      _ = Fintype.card {x // x ∈ S} * n := by simp
      _ ≤ q * n := Nat.mul_le_mul_right _ hr1
  let Y := X.deleteEdges (D : Set (Sym2 (Fin n)))
  have hY : Y.edgeFinset = X.edgeFinset \ D := X.edgeFinset_deleteEdges D
  have l2 : extremalNumber (Fintype.card (Fin n)) G2 < #Y.edgeFinset := by
    rw [hY, card_sdiff_of_subset hDsub, Fintype.card_fin]
    omega
  obtain ⟨g⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset l2
  have apart : ∀ v w, f v ≠ g w := by
    intro v w heq
    obtain ⟨y, hy⟩ := active (e2.symm w).val
    have hy' : y ∉ S := fun hyS => (e2.symm w).property ((closed _ _ hy).mpr hyS)
    have hadj : G2.Adj w (e2 ⟨y, hy'⟩) := by
      show G.Adj (e2.symm w).val (e2.symm (e2 ⟨y, hy'⟩)).val
      simpa using hy
    have hY' := g.toHom.map_rel' hadj
    obtain ⟨hXadj, hnot⟩ := deleteEdges_adj.mp hY'
    apply hnot
    rw [Finset.mem_coe]
    refine mem_biUnion.mpr ⟨v, mem_univ _, ?_⟩
    rw [mem_incidenceFinset, mk'_mem_incidenceSet_iff]
    exact ⟨hXadj, Or.inl heq⟩
  let φ : Fin q → Fin n := fun x => if h : x ∈ S then f (e1 ⟨x, h⟩) else g (e2 ⟨x, h⟩)
  have φinj : Function.Injective φ := by
    intro x y hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simp only [φ, dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (e1.injective (f.injective hxy))
    · simp only [φ, dif_pos hx, dif_neg hy] at hxy
      exact absurd hxy (apart _ _)
    · simp only [φ, dif_neg hx, dif_pos hy] at hxy
      exact absurd hxy.symm (apart _ _)
    · simp only [φ, dif_neg hx, dif_neg hy] at hxy
      exact congrArg Subtype.val (e2.injective (g.injective hxy))
  apply hfree
  refine ⟨⟨⟨φ, ?_⟩, φinj⟩⟩
  intro x y hxy
  by_cases hx : x ∈ S
  · have hy : y ∈ S := (closed x y hxy).mp hx
    have h1 : G1.Adj (e1 ⟨x, hx⟩) (e1 ⟨y, hy⟩) := by
      show G.Adj (e1.symm (e1 ⟨x, hx⟩)).val (e1.symm (e1 ⟨y, hy⟩)).val
      simpa using hxy
    simp only [φ, dif_pos hx, dif_pos hy]
    exact f.toHom.map_rel' h1
  · have hy : y ∉ S := fun hy => hx ((closed x y hxy).mpr hy)
    have h2 : G2.Adj (e2 ⟨x, hx⟩) (e2 ⟨y, hy⟩) := by
      show G.Adj (e2.symm (e2 ⟨x, hx⟩)).val (e2.symm (e2 ⟨y, hy⟩)).val
      simpa using hxy
    simp only [φ, dif_neg hx, dif_neg hy]
    exact (deleteEdges_adj.mp (g.toHom.map_rel' h2)).1

end OMA.Helpers

open SimpleGraph Finset in
theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1.H1 := by
  intro q G hq hdeg hc
  classical
  let s : Fin q := ⟨0, hq⟩
  obtain ⟨t, ht⟩ : ∃ t, ¬ G.Reachable s t := by
    by_contra! h
    exact hc ((connected_iff_exists_forall_reachable G).mpr ⟨s, h⟩)
  let S : Finset (Fin q) := univ.filter (fun x => G.Reachable s x)
  have memS : ∀ x, x ∈ S ↔ G.Reachable s x := by intro x; simp [S]
  have closed : ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S) := by
    intro x y h
    rw [memS, memS]
    exact ⟨fun hx => hx.trans h.reachable, fun hy => hy.trans h.symm.reachable⟩
  have active : ∀ x, ∃ y, G.Adj x y := by
    intro x
    obtain ⟨a, b, _, ha, _⟩ := OMA.Helpers.exists_two_adj G x (hdeg x)
    exact ⟨a, ha⟩
  have hsS : s ∈ S := (memS s).mpr (Reachable.refl s)
  have htS : t ∉ S := fun h => ht ((memS t).mp h)
  refine ⟨Fintype.card {x // x ∈ S}, Fintype.card {x // x ∉ S},
    G.comap (fun u => ((Fintype.equivFin {x // x ∈ S}).symm u).val),
    G.comap (fun u => ((Fintype.equivFin {x // x ∉ S}).symm u).val),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun n => OMA.Helpers.split_bound G S closed active n⟩
  · exact Fintype.card_pos_iff.mpr ⟨⟨s, hsS⟩⟩
  · have h := Fintype.card_lt_of_injective_of_notMem (Subtype.val : {x // x ∈ S} → Fin q)
      Subtype.val_injective (b := t) (fun ⟨y, hy⟩ => htS (hy ▸ y.property))
    simpa using h
  · exact Fintype.card_pos_iff.mpr ⟨⟨t, htS⟩⟩
  · have h := Fintype.card_lt_of_injective_of_notMem (Subtype.val : {x // x ∉ S} → Fin q)
      Subtype.val_injective (b := s) (fun ⟨y, hy⟩ => y.property (hy ▸ hsS))
    simpa using h
  · exact ⟨⟨⟨fun u => ((Fintype.equivFin {x // x ∈ S}).symm u).val, fun h => h⟩,
      Subtype.val_injective.comp (Fintype.equivFin {x // x ∈ S}).symm.injective⟩⟩
  · exact ⟨⟨⟨fun u => ((Fintype.equivFin {x // x ∉ S}).symm u).val, fun h => h⟩,
      Subtype.val_injective.comp (Fintype.equivFin {x // x ∉ S}).symm.injective⟩⟩
  · intro u
    set e1 := Fintype.equivFin {x // x ∈ S}
    obtain ⟨a, b, hab, ha, hb⟩ := OMA.Helpers.exists_two_adj G (e1.symm u).val (hdeg _)
    have haS : a ∈ S := (closed _ _ ha).mp (e1.symm u).property
    have hbS : b ∈ S := (closed _ _ hb).mp (e1.symm u).property
    refine OMA.Helpers.two_le_degree_of _ u (e1 ⟨a, haS⟩) (e1 ⟨b, hbS⟩) ?_ ?_ ?_
    · intro h
      exact hab (congrArg Subtype.val (e1.injective h))
    · show G.Adj (e1.symm u).val (e1.symm (e1 ⟨a, haS⟩)).val
      simpa using ha
    · show G.Adj (e1.symm u).val (e1.symm (e1 ⟨b, hbS⟩)).val
      simpa using hb
  · intro u
    set e2 := Fintype.equivFin {x // x ∉ S}
    obtain ⟨a, b, hab, ha, hb⟩ := OMA.Helpers.exists_two_adj G (e2.symm u).val (hdeg _)
    have haS : a ∉ S := fun h => (e2.symm u).property ((closed _ _ ha).mpr h)
    have hbS : b ∉ S := fun h => (e2.symm u).property ((closed _ _ hb).mpr h)
    refine OMA.Helpers.two_le_degree_of _ u (e2 ⟨a, haS⟩) (e2 ⟨b, hbS⟩) ?_ ?_ ?_
    · intro h
      exact hab (congrArg Subtype.val (e2.injective h))
    · show G.Adj (e2.symm u).val (e2.symm (e2 ⟨a, haS⟩)).val
      simpa using ha
    · show G.Adj (e2.symm u).val (e2.symm (e2 ⟨b, hbS⟩)).val
      simpa using hb
