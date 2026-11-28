import FormalConjectures.WrittenOnTheWallII.GraphConjecture189

open SimpleGraph

namespace OMA.Helpers

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A list which is a chain for adjacency is the support of a walk. -/
theorem exists_walk_of_isChain (G : SimpleGraph α) :
    ∀ (l : List α) (a : α), (a :: l).IsChain G.Adj →
      ∃ b : α, ∃ p : G.Walk a b, p.support = a :: l
  | [], a, _ => ⟨a, Walk.nil, rfl⟩
  | c :: l, a, h => by
      rw [List.isChain_cons_cons] at h
      obtain ⟨b, p, hp⟩ := exists_walk_of_isChain G l c h.2
      exact ⟨b, Walk.cons h.1 p, by simp [hp]⟩

/-- Two non-adjacent distinct vertices with a common neighbour are at distance two. -/
theorem dist_eq_two (G : SimpleGraph α) (hc : G.Connected) {x y w : α}
    (hxy : G.Adj x y) (hyw : G.Adj y w) (hne : x ≠ w) (hna : ¬ G.Adj x w) :
    G.dist x w = 2 := by
  have h1 : G.dist x w ≤ 2 := by
    have := SimpleGraph.dist_le (Walk.cons hxy (Walk.cons hyw Walk.nil))
    simpa using this
  have h2 : 1 < G.dist x w := hc.one_lt_dist_of_ne_of_not_adj hne hna
  omega

/-- Key counting lemma: if all neighbours of `x` lie on a path (given as a list) not containing `x`,
and `x` is adjacent neither to an end of the path nor to two consecutive vertices of it, then at
least `deg x + 2` vertices are at even distance from `x`. -/
theorem distEven_ge (G : SimpleGraph α) [DecidableRel G.Adj] (hc : G.Connected)
    (l : List α) (hch : l.IsChain G.Adj) (hnd : l.Nodup)
    (x : α) (hx : x ∉ l) (hN : ∀ y, G.Adj x y → y ∈ l) (hpos : 0 < G.degree x)
    (h0 : ∀ h : 0 < l.length, ¬ G.Adj x l[0])
    (hlast : ∀ h : l.length - 1 < l.length, ¬ G.Adj x l[l.length - 1])
    (hcons : ∀ i (h : i + 1 < l.length), ¬ (G.Adj x l[i] ∧ G.Adj x l[i + 1])) :
    G.degree x + 2 ≤ distEven G x := by
  classical
  set N := G.neighborFinset x with hNdef
  have hNcard : N.card = G.degree x := G.card_neighborFinset_eq_degree x
  have hNne : N.Nonempty := by
    rw [← Finset.card_pos, hNcard]; exact hpos
  have hmemN : ∀ y, y ∈ N ↔ G.Adj x y := fun y => by simp [hNdef]
  -- index facts
  have hidx : ∀ y, y ∈ N → l.idxOf y < l.length := fun y hy =>
    List.idxOf_lt_length_of_mem (hN y ((hmemN y).1 hy))
  have hget : ∀ y (hy : y ∈ N), l[l.idxOf y]'(hidx y hy) = y := fun y hy =>
    List.getElem_idxOf (hidx y hy)
  have hsucc : ∀ y, y ∈ N → l.idxOf y + 1 < l.length := by
    intro y hy
    by_contra hcon
    have hi := hidx y hy
    have hlt : l.length - 1 < l.length := by omega
    have heq : l.idxOf y = l.length - 1 := by omega
    apply hlast hlt
    have : l[l.length - 1]'hlt = y := by
      have := hget y hy
      simp only [heq] at this
      exact this
    rw [this]; exact (hmemN y).1 hy
  -- successor map
  let s : α → α := fun y => l.getD (l.idxOf y + 1) x
  have hs : ∀ y (hy : y ∈ N), s y = l[l.idxOf y + 1]'(hsucc y hy) := by
    intro y hy
    simp only [s]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hsucc y hy)]
    rfl
  have hinj : Set.InjOn s (N : Set α) := by
    intro y hy y' hy' hss
    have hy1 : y ∈ N := hy
    have hy2 : y' ∈ N := hy'
    rw [hs y hy1, hs y' hy2] at hss
    have := (hnd.getElem_inj_iff).1 hss
    have hii : l.idxOf y = l.idxOf y' := by omega
    have e1 := hget y hy1
    have e2 := hget y' hy2
    simp only [hii] at e1
    rw [← e1, e2]
  -- adjacency along the list
  have hchain : ∀ i (h : i + 1 < l.length), G.Adj l[i] l[i + 1] := fun i h => hch.getElem i h
  -- properties of successors
  have hs_mem : ∀ y (hy : y ∈ N), s y ∈ l := by
    intro y hy; rw [hs y hy]; exact List.getElem_mem _
  have hs_dist : ∀ y (hy : y ∈ N), G.dist x (s y) = 2 := by
    intro y hy
    have hxy : G.Adj x y := (hmemN y).1 hy
    have hyw : G.Adj y (s y) := by
      have := hchain (l.idxOf y) (hsucc y hy)
      rw [hget y hy] at this
      rw [hs y hy]; exact this
    have hne : x ≠ s y := fun h => hx (h ▸ hs_mem y hy)
    have hna : ¬ G.Adj x (s y) := by
      intro hadj
      apply hcons (l.idxOf y) (hsucc y hy)
      refine ⟨?_, ?_⟩
      · rw [hget y hy]; exact hxy
      · rw [← hs y hy]; exact hadj
    exact dist_eq_two G hc hxy hyw hne hna
  -- the first neighbour on the list and its predecessor
  obtain ⟨y0, hy0, hmin⟩ := N.exists_min_image (fun y => l.idxOf y) hNne
  have hi0 : l.idxOf y0 < l.length := hidx y0 hy0
  have hi0pos : 0 < l.idxOf y0 := by
    rcases Nat.eq_zero_or_pos (l.idxOf y0) with h | h
    · exfalso
      have hlen : 0 < l.length := by omega
      apply h0 hlen
      have := hget y0 hy0
      simp only [h] at this
      rw [this]; exact (hmemN y0).1 hy0
    · exact h
  have hpred : l.idxOf y0 - 1 < l.length := by omega
  set t := l[l.idxOf y0 - 1]'hpred with htdef
  have ht_mem : t ∈ l := List.getElem_mem _
  have ht_notN : t ∉ N := by
    intro htN
    have h1 := hmin t htN
    have h2 : l.idxOf t = l.idxOf y0 - 1 := by
      have := hget t htN
      have h3 : l[l.idxOf t]'(hidx t htN) = l[l.idxOf y0 - 1]'hpred := by rw [this]
      exact (hnd.getElem_inj_iff).1 h3
    omega
  have ht_dist : G.dist x t = 2 := by
    have hxy : G.Adj x y0 := (hmemN y0).1 hy0
    have hyt : G.Adj y0 t := by
      have hlt : l.idxOf y0 - 1 + 1 < l.length := by omega
      have := hchain (l.idxOf y0 - 1) hlt
      have e : l[l.idxOf y0 - 1 + 1]'hlt = y0 := by
        have := hget y0 hy0
        have hh : l.idxOf y0 - 1 + 1 = l.idxOf y0 := by omega
        simp only [hh]
        exact this
      rw [e] at this
      exact this.symm
    have hne : x ≠ t := fun h => hx (h ▸ ht_mem)
    have hna : ¬ G.Adj x t := fun h => ht_notN ((hmemN t).2 h)
    exact dist_eq_two G hc hxy hyt hne hna
  have ht_notimg : t ∉ N.image s := by
    intro hti
    obtain ⟨y, hy, hyt⟩ := Finset.mem_image.1 hti
    rw [hs y hy] at hyt
    have := (hnd.getElem_inj_iff).1 hyt
    have h1 := hmin y hy
    omega
  have hx_notin : x ∉ insert t (N.image s) := by
    intro hxi
    rcases Finset.mem_insert.1 hxi with h | h
    · exact hx (h ▸ ht_mem)
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 h
      exact hx (hyx ▸ hs_mem y hy)
  -- the set of witnesses
  have hsub : insert x (insert t (N.image s)) ⊆
      Finset.univ.filter (fun w => Even (G.dist x w)) := by
    intro w hw
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.1 hw with h | h
    · subst h; simp
    · rcases Finset.mem_insert.1 h with h | h
      · subst h; rw [ht_dist]; decide
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
        rw [hs_dist y hy]; decide
  have hcard : (insert x (insert t (N.image s))).card = G.degree x + 2 := by
    rw [Finset.card_insert_of_notMem hx_notin, Finset.card_insert_of_notMem ht_notimg,
      Finset.card_image_of_injOn hinj, hNcard]
  unfold distEven
  calc G.degree x + 2 = (insert x (insert t (N.image s))).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Absorption lemma: if every vertex has at most `s + 1` vertices at even distance, then a vertex
`x` of degree at least `s`, all of whose neighbours lie on a path not containing `x`, can be
inserted into the path. Paths are lists which are chains for adjacency. -/
theorem absorb (G : SimpleGraph α) [DecidableRel G.Adj] [Nontrivial α] (hc : G.Connected) (s : ℕ)
    (hσ : ∀ v, distEven G v ≤ 1 + s)
    (l : List α) (hne : l ≠ []) (hch : l.IsChain G.Adj) (hnd : l.Nodup)
    (x : α) (hx : x ∉ l) (hN : ∀ y, G.Adj x y → y ∈ l) (hdeg : s ≤ G.degree x) :
    ∃ l' : List α, l'.IsChain G.Adj ∧ l'.Perm (x :: l) := by
  have hlen : 0 < l.length := List.length_pos_iff.2 hne
  have hlen1 : l.length - 1 < l.length := by omega
  by_cases h0 : G.Adj x l[0]
  · refine ⟨x :: l, ?_, List.Perm.refl _⟩
    cases l with
    | nil => exact absurd rfl hne
    | cons a l0 =>
      refine List.isChain_cons_cons.2 ⟨?_, hch⟩
      simpa using h0
  by_cases hlast : G.Adj x l[l.length - 1]
  · refine ⟨l ++ [x], ?_, ?_⟩
    · refine List.IsChain.append hch (List.isChain_singleton x) ?_
      intro a ha b hb
      have hb' : b = x := by simpa using hb.symm
      subst hb'
      have ha' : a = l[l.length - 1] := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlen1] at ha
        exact (Option.some.inj ha).symm
      rw [ha']; exact hlast.symm
    · exact List.perm_append_singleton x l
  by_cases hcons : ∃ i, ∃ h : i + 1 < l.length, G.Adj x l[i] ∧ G.Adj x l[i + 1]
  · obtain ⟨i, h, hi1, hi2⟩ := hcons
    refine ⟨l.take (i + 1) ++ x :: l.drop (i + 1), ?_, ?_⟩
    · refine List.IsChain.append (hch.take _) ?_ ?_
      · have hd : l.drop (i + 1) = l[i + 1] :: l.drop (i + 1 + 1) := List.drop_eq_getElem_cons h
        rw [hd]
        refine List.isChain_cons_cons.2 ⟨hi2, ?_⟩
        rw [← hd]; exact hch.drop _
      · intro a ha b hb
        have hb' : b = x := by simpa using hb.symm
        subst hb'
        have ha' : a = l[i] := by
          rw [List.getLast?_eq_getElem?] at ha
          have hl : (l.take (i + 1)).length = i + 1 := by
            rw [List.length_take]; omega
          rw [hl] at ha
          have hi : i < l.length := by omega
          simp only [Nat.add_sub_cancel] at ha
          rw [List.getElem?_take] at ha
          simp only [Nat.lt_succ_self, if_true] at ha
          rw [List.getElem?_eq_getElem hi] at ha
          exact (Option.some.inj ha).symm
        rw [ha']; exact hi1.symm
    · have h1 : (l.take (i + 1) ++ x :: l.drop (i + 1)).Perm
          (x :: (l.take (i + 1) ++ l.drop (i + 1))) := List.perm_middle
      rw [List.take_append_drop] at h1
      exact h1
  · exfalso
    have hpos : 0 < G.degree x := hc.preconnected.degree_pos_of_nontrivial x
    have h1 := distEven_ge G hc l hch hnd x hx hN hpos (fun _ => h0) (fun _ => hlast)
      (fun i h hh => hcons ⟨i, h, hh⟩)
    have h2 := hσ x
    omega

/-- Iterated absorption: a path whose complement is an independent set of vertices of degree at
least `s` can be completed to a Hamiltonian path. -/
theorem ham_list (G : SimpleGraph α) [DecidableRel G.Adj] [Nontrivial α] (hc : G.Connected)
    (s : ℕ) (hσ : ∀ v, distEven G v ≤ 1 + s) :
    ∀ (m : ℕ) (l : List α), l ≠ [] → l.IsChain G.Adj → l.Nodup →
      Fintype.card α - l.length = m →
      (∀ x, x ∉ l → s ≤ G.degree x) → (∀ x y, x ∉ l → y ∉ l → ¬ G.Adj x y) →
      ∃ l' : List α, l' ≠ [] ∧ l'.IsChain G.Adj ∧ l'.Nodup ∧ ∀ v, v ∈ l' := by
  intro m
  induction m with
  | zero =>
    intro l hne hch hnd hm hdeg hind
    refine ⟨l, hne, hch, hnd, ?_⟩
    intro v
    by_contra hv
    have h1 : (v :: l).Nodup := List.nodup_cons.2 ⟨hv, hnd⟩
    have h2 := h1.length_le_card
    simp only [List.length_cons] at h2
    omega
  | succ k ih =>
    intro l hne hch hnd hm hdeg hind
    by_cases hall : ∀ v, v ∈ l
    · exact ⟨l, hne, hch, hnd, hall⟩
    · obtain ⟨x, hx⟩ := not_forall.1 hall
      have hN : ∀ y, G.Adj x y → y ∈ l := by
        intro y hxy
        by_contra hy
        exact hind x y hx hy hxy
      obtain ⟨l', hch', hperm⟩ := absorb G hc s hσ l hne hch hnd x hx hN (hdeg x hx)
      have hnd' : l'.Nodup := hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hx, hnd⟩)
      have hlen' : l'.length = l.length + 1 := by
        rw [hperm.length_eq]; simp
      have hne' : l' ≠ [] := by
        intro h; rw [h] at hlen'; simp at hlen'
      have hsub : ∀ v, v ∈ l → v ∈ l' := fun v hv =>
        hperm.mem_iff.2 (List.mem_cons_of_mem _ hv)
      refine ih l' hne' hch' hnd' (by omega) ?_ ?_
      · intro y hy; exact hdeg y (fun h => hy (hsub y h))
      · intro y z hy hz; exact hind y z (fun h => hy (hsub y h)) (fun h => hz (hsub z h))

/-- Reduction of Conjecture 189 to the existence of a dominating path: if the hypothesis of the
conjecture holds and `G` has a path (a list which is a chain for adjacency, without repetitions)
such that every vertex off the path has degree at least the second smallest degree and no two
vertices off the path are adjacent, then `G` has a Hamiltonian path. -/
theorem ham_of_dominating [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hc : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (l : List α) (hne : l ≠ []) (hch : l.IsChain G.Adj) (hnd : l.Nodup)
    (hdeg : ∀ x, x ∉ l → secondSmallestDegree G ≤ G.degree x)
    (hind : ∀ x y, x ∉ l → y ∉ l → ¬ G.Adj x y) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hσ' : ∀ v, distEven G v ≤ 1 + secondSmallestDegree G := fun v =>
    (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))).trans hσ
  obtain ⟨l', hne', hch', hnd', hall⟩ :=
    ham_list G hc (secondSmallestDegree G) hσ' _ l hne hch hnd rfl hdeg hind
  cases l' with
  | nil => exact absurd rfl hne'
  | cons a l0 =>
    obtain ⟨b, p, hp⟩ := exists_walk_of_isChain G l0 a hch'
    refine ⟨a, b, p, ?_⟩
    intro v
    rw [hp]
    exact List.count_eq_one_of_mem hnd' (hall v)

end OMA.Helpers
