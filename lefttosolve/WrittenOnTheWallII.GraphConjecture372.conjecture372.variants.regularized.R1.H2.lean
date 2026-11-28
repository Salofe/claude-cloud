import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

/-!
# Step H2: a tree has vertex cover number at most twice its total domination number

Let `D` be a minimum total dominating set of a tree `T` on `n ≥ 2` vertices, and let `F` be the
set of edges with no endpoint in `D`. Each vertex outside `D` has a neighbour in `D`; the edges
to these chosen neighbours are distinct and none of them lies in `F`. Since `T` has `n - 1`
edges, `(n - |D|) + |F| ≤ n - 1`, so `|F| < |D|`. Then `D` together with one endpoint of each
edge of `F` is a vertex cover with at most `2 |D|` vertices.
-/

namespace OMA.Helpers

open SimpleGraph Finset

theorem cover_le_two_tdn {α : Type} [Fintype α] [DecidableEq α] (T : SimpleGraph α)
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber := by
  classical
  have hnt : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  -- a total dominating set exists
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card α, Finset.univ, ⟨?_, Finset.card_univ⟩⟩
    intro v
    obtain ⟨u, hu⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
    exact ⟨u, by simp, hu⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hDdom := hD.isTotalDominating
  have hDcard : D.card = T.totalDominationNumber := hD.card_eq
  -- edges avoiding D
  let F := T.edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ D)
  -- choice of a dominating neighbour
  have hdom : ∀ v : α, ∃ w, w ∈ D ∧ T.Adj v w := fun v => by
    obtain ⟨w, hw, hadj⟩ := hDdom v
    exact ⟨w, by simpa using hw, hadj⟩
  choose d hdD hdadj using hdom
  let g : α → Sym2 α := fun v => s(v, d v)
  have hgF : ∀ v ∈ Dᶜ, g v ∈ T.edgeFinset \ F := by
    intro v _
    refine Finset.mem_sdiff.mpr ⟨T.mem_edgeFinset.mpr (hdadj v), ?_⟩
    intro hF
    have h := (Finset.mem_filter.mp hF).2 (d v) (Sym2.mem_mk_right _ _)
    exact h (hdD v)
  have hginj : Set.InjOn g (Dᶜ : Finset α) := by
    intro v hv v' hv' h
    have hv1 : v ∉ D := Finset.mem_compl.mp hv
    have hv2 : v' ∉ D := Finset.mem_compl.mp hv'
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd (h1 ▸ hdD v') hv1
  have hcount : (Dᶜ).card ≤ (T.edgeFinset \ F).card :=
    Finset.card_le_card_of_injOn g hgF hginj
  have hFsub : F ⊆ T.edgeFinset := Finset.filter_subset _ _
  have hsd : (T.edgeFinset \ F).card + F.card = T.edgeFinset.card := by
    rw [Finset.card_sdiff_of_subset hFsub]
    have := Finset.card_le_card hFsub
    omega
  have htree := hT.card_edgeFinset
  have hcompl : (Dᶜ).card + D.card = Fintype.card α := by
    rw [Finset.card_compl]
    have := Finset.card_le_univ D
    omega
  have hFD : F.card ≤ D.card := by omega
  -- the vertex cover
  let C : Finset α := D ∪ F.image (fun e => e.out.1)
  have hC : T.IsVertexCover (C : Set α) := by
    intro v w hvw
    by_cases hv : v ∈ D
    · left; exact Finset.mem_coe.mpr (Finset.mem_union_left _ hv)
    by_cases hw : w ∈ D
    · right; exact Finset.mem_coe.mpr (Finset.mem_union_left _ hw)
    have he : s(v, w) ∈ F := by
      refine Finset.mem_filter.mpr ⟨T.mem_edgeFinset.mpr hvw, ?_⟩
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · exact hv
      · exact hw
    have hmem : (s(v, w)).out.1 ∈ C :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem (s(v, w))) with h | h
    · left; rw [← h]; exact Finset.mem_coe.mpr hmem
    · right; rw [← h]; exact Finset.mem_coe.mpr hmem
  have hCcard : C.card ≤ 2 * D.card := by
    change (D ∪ F.image (fun e => e.out.1)).card ≤ 2 * D.card
    have h1 := Finset.card_union_le D (F.image (fun e => e.out.1))
    have h2 := Finset.card_image_le (s := F) (f := fun e => e.out.1)
    omega
  have hle : T.vertexCoverNum ≤ ((2 * D.card : ℕ) : ℕ∞) := by
    refine hC.vertexCoverNum_le.trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hCcard
  rw [← hDcard]
  exact ENat.toNat_le_of_le_natCast hle

end OMA.Helpers

theorem OMA.solution :
    OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 := by
  intro α _ _ T hT hcard
  exact OMA.Helpers.cover_le_two_tdn T hT hcard
