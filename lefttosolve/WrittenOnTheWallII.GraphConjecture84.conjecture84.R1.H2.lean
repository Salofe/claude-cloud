import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

/-!
# Conjecture 84 of Written on the Wall II, case of minimum degree at least two

With `2 ≤ δ` we have `2 rad / δ ≤ rad`. Pick a vertex `v` with `dist u v = eccent u ≥ rad`.
A shortest path from `u` to `v` induces a tree on `dist u v + 1` vertices. The tree is built
layer by layer: the vertex at distance `k + 1` has exactly one neighbour among the earlier
vertices (its predecessor), by the triangle inequality. Acyclicity is witnessed by an acyclic
graph `K` on the whole vertex type that contains every induced edge; each layer adds one
pendant edge to `K`.
-/

namespace OMA.Helpers

open SimpleGraph

/-- Any induced tree has at most `largestInducedTreeSize G` vertices. -/
theorem card_le_tree {α : Type} [Fintype α] (G : SimpleGraph α) (s : Finset α)
    (hs : (G.induce (s : Set α)).IsTree) : s.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro n ⟨t, rfl, -⟩
    exact Finset.card_le_univ t
  · exact ⟨s, rfl, hs⟩

/-- A vertex without neighbours reaches only itself. -/
theorem reach_of_isolated {α : Type} (K : SimpleGraph α) (z a : α)
    (hz : ∀ y, ¬ K.Adj z y) (h : K.Reachable z a) : z = a := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons h' _ => exact (hz _ h').elim

/-- A connected induced subgraph whose edges all lie in an acyclic graph is a tree. -/
theorem isTree_of_cover {α : Type} (G K : SimpleGraph α) (s : Set α)
    (hconn : (G.induce s).Connected) (hK : K.IsAcyclic)
    (hGK : ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → K.Adj x y) : (G.induce s).IsTree := by
  refine ⟨hconn, ?_⟩
  refine IsAcyclic.anti (G' := K.induce s) ?_ (hK.induce s)
  intro x y hxy
  exact hGK x x.2 y y.2 hxy

/-- A shortest path from `u` to `z` grows into an induced tree, one layer at a time. -/
theorem layer_tree {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (hc : G.Connected) (u : α) :
    ∀ k : ℕ, ∀ z : α, G.dist u z = k → ∃ s : Finset α, s.card = k + 1 ∧ z ∈ s ∧
      (∀ b ∈ s, b ≠ z → G.dist u b < k) ∧ (∀ b ∈ s, G.dist u b ≤ k) ∧
      (G.induce (s : Set α)).Connected ∧
      ∃ K : SimpleGraph α, K.IsAcyclic ∧ (∀ x y, K.Adj x y → x ∈ s) ∧
        (∀ x ∈ s, ∀ y ∈ s, G.Adj x y → K.Adj x y) := by
  intro k
  induction k with
  | zero =>
    intro z hz
    have hzu : u = z := (hc.dist_eq_zero_iff).mp hz
    subst hzu
    refine ⟨{u}, by simp, by simp, ?_, ?_, ?_, ⊥, isAcyclic_bot, ?_, ?_⟩
    · intro b hb hne
      exact (hne (Finset.mem_singleton.mp hb)).elim
    · intro b hb
      rw [Finset.mem_singleton.mp hb, dist_self]
    · have hs : (({u} : Finset α) : Set α) = {u} := by simp
      rw [hs]
      refine ⟨fun x y => ?_⟩
      have hxy : x = y := Subsingleton.elim x y
      subst hxy
      exact Reachable.refl _
    · intro x y hxy
      exact absurd hxy (by simp)
    · intro x hx y hy hxy
      rw [Finset.mem_singleton] at hx hy
      rw [hx, hy] at hxy
      exact (G.irrefl hxy).elim
  | succ k ih =>
    intro z hz
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist z u
    have hzu' : G.dist z u = k + 1 := by rw [SimpleGraph.dist_comm]; exact hz
    cases p with
    | nil => simp at hz
    | @cons _ w _ hzw q =>
      have hq : q.length = k := by simp at hp; omega
      have hwu : G.dist w u ≤ k := hq ▸ dist_le q
      have hwz1 : G.dist w z = 1 := dist_eq_one_iff_adj.mpr hzw.symm
      have tri : G.dist u z ≤ G.dist u w + G.dist w z := hc.dist_triangle
      have hw : G.dist u w = k := by
        rw [SimpleGraph.dist_comm] at hwu
        omega
      obtain ⟨s, hcard, hws, hlt, hle, hconn, K, hK, hKs, hGK⟩ := ih w hw
      have hzs : z ∉ s := by
        intro hzs
        have := hle z hzs
        omega
      have huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = w := by
        intro b hb hzb
        by_contra hbw
        have h1 := hlt b hb hbw
        have h2 : G.dist b z = 1 := dist_eq_one_iff_adj.mpr hzb.symm
        have h3 : G.dist u z ≤ G.dist u b + G.dist b z := hc.dist_triangle
        omega
      refine ⟨insert z s, ?_, Finset.mem_insert_self z s, ?_, ?_, ?_, K ⊔ edge z w, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hzs, hcard]
      · intro b hb hbz
        rcases Finset.mem_insert.mp hb with h | h
        · exact (hbz h).elim
        · have := hle b h
          omega
      · intro b hb
        rcases Finset.mem_insert.mp hb with h | h
        · rw [h, hz]
        · have := hle b h
          omega
      · have hset : ((insert z s : Finset α) : Set α) = {z} ∪ (s : Set α) := by
          rw [Finset.coe_insert, Set.insert_eq]
        rw [hset]
        refine connected_induce_union ?_ hconn.preconnected (Set.mem_singleton z) hws hzw
        intro x y
        have hxy : x = y := Subsingleton.elim x y
        subst hxy
        exact Reachable.refl _
      · refine IsAcyclic.sup_edge_of_not_reachable ?_ hK
        intro hr
        have hzK : ∀ y, ¬ K.Adj z y := fun y hy => hzs (hKs z y hy)
        have hzw' : z = w := reach_of_isolated K z w hzK hr
        exact hzs (by rw [hzw']; exact hws)
      · intro x y hxy
        rcases (sup_adj _ _ _ _).mp hxy with h | h
        · exact Finset.mem_insert_of_mem (hKs x y h)
        · rw [edge_adj] at h
          rcases h with ⟨⟨hx, -⟩ | ⟨hx, -⟩, -⟩
          · rw [hx]
            exact Finset.mem_insert_self _ _
          · rw [hx]
            exact Finset.mem_insert_of_mem hws
      · intro x hx y hy hxy
        rw [sup_adj, edge_adj]
        rcases Finset.mem_insert.mp hx with hx' | hx'
        · rcases Finset.mem_insert.mp hy with hy' | hy'
          · rw [hx', hy'] at hxy
            exact (G.irrefl hxy).elim
          · right
            rw [hx'] at hxy
            have hyw : y = w := huniq hy' hxy
            exact ⟨Or.inl ⟨hx', hyw⟩, by rw [hx']; exact hxy.ne⟩
        · rcases Finset.mem_insert.mp hy with hy' | hy'
          · right
            rw [hy'] at hxy
            have hxw : x = w := huniq hx' hxy.symm
            exact ⟨Or.inr ⟨hxw, hy'⟩, by rw [hy']; exact hxy.ne⟩
          · left
            exact hGK x hx' y hy' hxy

end OMA.Helpers

open SimpleGraph in
theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2 := by
  intro α _ _ _ G _ hc hδ h2
  classical
  obtain ⟨u⟩ := hc.nonempty
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  have hrad : G.radius ≤ G.edist u v := hv ▸ radius_le_eccent
  have htop : G.edist u v ≠ ⊤ := edist_ne_top_iff_reachable.mpr (hc u v)
  have hr : G.radius.toNat ≤ G.dist u v := ENat.toNat_le_toNat hrad htop
  obtain ⟨s, hcard, -, -, -, hconn, K, hK, -, hGK⟩ :=
    OMA.Helpers.layer_tree G hc u (G.dist u v) v rfl
  have htree : (G.induce (s : Set α)).IsTree :=
    OMA.Helpers.isTree_of_cover G K _ hconn hK (fun x hx y hy h => hGK x hx y hy h)
  have hT : s.card ≤ largestInducedTreeSize G := OMA.Helpers.card_le_tree G s htree
  have hrT : (G.radius.toNat : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
    exact_mod_cast (show G.radius.toNat ≤ largestInducedTreeSize G by omega)
  have hδR : (2 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast h2
  have hδpos : (0 : ℝ) < (G.minDegree : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ (G.radius.toNat : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hδpos]
  nlinarith
