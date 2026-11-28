import FormalConjectures.ErdosProblems.«944»

/-!
# Dirac's conjecture: vertex-critical graphs without critical edges, for every `k ≥ 4`

For every `k ≥ 4` we give a finite graph `G` with a certificate `Cert G (k - 1)`: every
vertex-deleted subgraph is `(k - 1)`-colourable, and every map into `k - 1` colours has a
monochromatic edge different from any prescribed pair. Then `G` has chromatic number `k`, every
vertex is critical and no set of at most one pair is critical.

* `k = 4`: a Cayley graph on 60 vertices (group `ZMod 5 ⋊ ZMod 12`). In every 3-colouring of the
  graph minus the vertex `0`, each colour occurs on two neighbours of `0`. This is checked by an
  exhaustive search run in the kernel (the colours of two adjacent vertices are fixed in advance,
  which is no restriction up to a permutation of the colours) and it is transported to the other
  vertices by the left multiplications of the group.
* `k = 6`: the circulant graph on 21 vertices with connection set `±{1, 3, 4, 5, 6}`, checked by
  the same search with 5 colours (the colours of a 4-clique are fixed in advance).
* `k = 5` and `k ≥ 7`: circulant graphs on `4 (k - 1) + 1` vertices in which every 5 vertices span
  at least two edges, glued together at one vertex (a counting argument).
-/

open SimpleGraph Erdos944

namespace OMA.Helpers

universe u

/-- Certificate: every vertex-deleted subgraph is `m`-colourable, and every map into `m` colours
has a monochromatic edge different from any prescribed pair `e`. -/
structure Cert {V : Type u} (G : SimpleGraph V) (m : ℕ) : Prop where
  col : ∀ v : V, ∃ c : V → Fin m, ∀ x y, x ≠ v → y ≠ v → G.Adj x y → c x ≠ c y
  rigid : ∀ (e : Sym2 V) (f : V → Fin m), ∃ x y, G.Adj x y ∧ s(x, y) ≠ e ∧ f x = f y

theorem cert_not_colorable {V : Type u} [Finite V] [Nonempty V] {G : SimpleGraph V} {m : ℕ}
    (h : Cert G m) (E : Set (Sym2 V)) (hE : E.ncard ≤ 1) : ¬ (G.deleteEdges E).Colorable m := by
  rintro ⟨C⟩
  obtain ⟨v0⟩ := ‹Nonempty V›
  have : Nonempty (Sym2 V) := ⟨s(v0, v0)⟩
  obtain ⟨e, he⟩ := (Set.ncard_le_one_iff_subset_singleton (Set.toFinite E)).1 hE
  obtain ⟨x, y, hxy, hne, hf⟩ := h.rigid e C
  refine C.valid ?_ hf
  rw [deleteEdges_adj]
  exact ⟨hxy, fun hmem => hne (he hmem)⟩

theorem cert_colorable {V : Type u} [Nonempty V] {G : SimpleGraph V} {m : ℕ}
    (h : Cert G m) : G.Colorable (m + 1) := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨c, hc⟩ := h.col v
  classical
  refine ⟨Coloring.mk (fun x => if x = v then Fin.last m else (c x).castSucc) ?_⟩
  intro x y hxy
  by_cases hx : x = v
  · by_cases hy : y = v
    · exact absurd hxy (by rw [hx, hy]; exact G.irrefl)
    · simp only [hx, hy, if_true, if_false]
      exact (Fin.castSucc_lt_last _).ne'
  · by_cases hy : y = v
    · simp only [hx, hy, if_true, if_false]
      exact (Fin.castSucc_lt_last _).ne
    · simp only [hx, hy, if_false]
      exact fun h' => hc x y hx hy hxy (Fin.castSucc_injective _ h')

theorem cert_erdos {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V) (m : ℕ)
    (h : Cert G m) : G.IsErdos944 (m + 1) 1 := by
  have hnot : ¬ G.Colorable m := by
    have := cert_not_colorable h ∅ (by simp)
    rwa [deleteEdges_empty] at this
  have hchi : G.chromaticNumber = ((m + 1 : ℕ) : ℕ∞) := by
    rw [Nat.cast_add_one]
    exact chromaticNumber_eq_iff_colorable_not_colorable.2 ⟨cert_colorable h, hnot⟩
  refine ⟨⟨hchi, fun v => ?_⟩, fun E hE => ?_⟩
  · -- vertex criticality
    show ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber
    have htop : (⊤ : G.Subgraph).coe.chromaticNumber = ((m + 1 : ℕ) : ℕ∞) := by
      rw [← hchi]
      exact le_antisymm (chromaticNumber_mono_of_hom Subgraph.topIso.toHom)
        (chromaticNumber_mono_of_hom Subgraph.topIso.symm.toHom)
    rw [htop]
    obtain ⟨c, hc⟩ := h.col v
    have hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable m := by
      refine ⟨Coloring.mk (fun x => c x.1) ?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have hx' : x ≠ v := fun hxv => hx.2 (by simp [hxv])
      have hy' : y ≠ v := fun hyv => hy.2 (by simp [hyv])
      exact hc x y hx' hy' (Subgraph.coe_adj_sub _ _ _ hxy)
    calc ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber ≤ (m : ℕ∞) :=
          chromaticNumber_le_iff_colorable.2 hcol
      _ < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self m
  · -- no critical edge set of size ≤ 1
    by_contra hlt
    have hE1 : E.ncard ≤ 1 := not_lt.1 hlt
    have hnc := cert_not_colorable h E hE1
    have : (G.deleteEdges E).chromaticNumber < ((m + 1 : ℕ) : ℕ∞) := by
      rw [← hchi]; exact hE
    rw [Nat.cast_add_one] at this
    have h2 : (G.deleteEdges E).chromaticNumber ≤ (m : ℕ∞) := Order.le_of_lt_add_one this
    exact hnc (chromaticNumber_le_iff_colorable.1 h2)

/-- Counting certificate. -/
structure Good {V : Type u} [Fintype V] (G : SimpleGraph V) (s m : ℕ) : Prop where
  card : s * m < Fintype.card V
  col : ∀ v : V, ∃ c : V → Fin m, ∀ x y, x ≠ v → y ≠ v → G.Adj x y → c x ≠ c y
  dense : ∀ (X : Finset V) (e : Sym2 V), s < X.card → ∃ x ∈ X, ∃ y ∈ X, G.Adj x y ∧ s(x, y) ≠ e

theorem good_cert {V : Type u} [Fintype V] {G : SimpleGraph V} {s m : ℕ} (h : Good G s m) :
    Cert G m := by
  classical
  refine ⟨h.col, fun e f => ?_⟩
  have hcard : Fintype.card (Fin m) * s < Fintype.card V := by
    rw [Fintype.card_fin, mul_comm]; exact h.card
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hcard
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := h.dense _ e hc
  refine ⟨x, y, hxy, hne, ?_⟩
  rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]


section Glue

variable {V₁ V₂ : Type u}

/-- One-point union of `G₁` and `G₂` (identifying `w₁` with `w₂`), with all other pairs of
vertices from different sides joined. -/
def glue (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (w₁ : V₁) (w₂ : V₂) :
    SimpleGraph (V₁ ⊕ {y : V₂ // y ≠ w₂}) where
  Adj a b := match a, b with
    | Sum.inl x, Sum.inl x' => G₁.Adj x x'
    | Sum.inr y, Sum.inr y' => G₂.Adj y.1 y'.1
    | Sum.inl x, Sum.inr y => x ≠ w₁ ∨ G₂.Adj w₂ y.1
    | Sum.inr y, Sum.inl x => x ≠ w₁ ∨ G₂.Adj w₂ y.1
  symm := ⟨by
    rintro (x | y) (x' | y') h
    · exact G₁.adj_symm h
    · exact h
    · exact h
    · exact G₂.adj_symm h⟩
  loopless := ⟨by
    rintro (x | y) h
    · exact G₁.irrefl h
    · exact G₂.irrefl h⟩

variable {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {w₁ : V₁} {w₂ : V₂}

/-- The copy of `V₂` inside the glued vertex set. -/
def glueR [DecidableEq V₂] (w₁ : V₁) (w₂ : V₂) (y : V₂) : V₁ ⊕ {y : V₂ // y ≠ w₂} :=
  if h : y = w₂ then Sum.inl w₁ else Sum.inr ⟨y, h⟩

theorem glueR_injective [DecidableEq V₂] : Function.Injective (glueR w₁ w₂) := by
  intro y y' h
  unfold glueR at h
  by_cases hy : y = w₂ <;> by_cases hy' : y' = w₂ <;> simp [hy, hy'] at h
  · rw [hy, hy']
  · exact h

theorem glue_adj_glueR [DecidableEq V₂] {y y' : V₂} (h : G₂.Adj y y') :
    (glue G₁ G₂ w₁ w₂).Adj (glueR w₁ w₂ y) (glueR w₁ w₂ y') := by
  unfold glueR
  by_cases hy : y = w₂ <;> by_cases hy' : y' = w₂ <;> simp only [hy, hy', dif_pos, dif_neg, not_false_iff]
  · exact absurd h (by rw [hy, hy']; exact G₂.irrefl)
  · exact Or.inr (hy ▸ h)
  · exact Or.inr (hy' ▸ h.symm)
  · exact h

/-- A set with more than `s` vertices contains two different edges. -/
theorem Good.two_edges {V : Type u} [Fintype V] {G : SimpleGraph V} {s m : ℕ} (h : Good G s m)
    (X : Finset V) (hX : s < X.card) :
    ∃ x ∈ X, ∃ y ∈ X, ∃ x' ∈ X, ∃ y' ∈ X, G.Adj x y ∧ G.Adj x' y' ∧ s(x, y) ≠ s(x', y') := by
  obtain ⟨x0, -⟩ := Finset.card_pos.1 (Nat.zero_lt_of_lt hX)
  obtain ⟨x, hx, y, hy, hxy, -⟩ := h.dense X s(x0, x0) hX
  obtain ⟨x', hx', y', hy', hxy', hne⟩ := h.dense X s(x, y) hX
  exact ⟨x, hx, y, hy, x', hx', y', hy', hxy, hxy', hne.symm⟩

/-- Transport of density along an injective map preserving adjacency. -/
theorem dense_of_map {V W : Type u} [Fintype V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} {s m : ℕ} (h : Good G s m) (j : V → W) (hj : Function.Injective j)
    (hadj : ∀ x y, G.Adj x y → H.Adj (j x) (j y)) (X : Finset W) (e : Sym2 W)
    (hX : s < X.card) (hsub : ∀ a ∈ X, ∃ x, j x = a) :
    ∃ a ∈ X, ∃ b ∈ X, H.Adj a b ∧ s(a, b) ≠ e := by
  classical
  have hcard : (X.preimage j hj.injOn).card = X.card := by
    rw [Finset.card_preimage]
    congr 1
    ext a
    simp only [Finset.mem_filter, Set.mem_range, and_iff_left_iff_imp]
    exact hsub a
  obtain ⟨x, hx, y, hy, x', hx', y', hy', hxy, hxy', hne⟩ :=
    h.two_edges (X.preimage j hj.injOn) (by rw [hcard]; exact hX)
  rw [Finset.mem_preimage] at hx hy hx' hy'
  by_cases he : s(j x, j y) = e
  · refine ⟨j x', hx', j y', hy', hadj _ _ hxy', fun he' => hne ?_⟩
    have h2 : s(j x, j y) = s(j x', j y') := he.trans he'.symm
    have h3 : Sym2.map j s(x, y) = Sym2.map j s(x', y') := by simpa using h2
    exact Sym2.map.injective hj h3
  · exact ⟨j x, hx, j y, hy, hadj _ _ hxy, he⟩

theorem good_glue [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂] {s m₁ m₂ : ℕ}
    (hs : 3 ≤ s) (h₁ : Good G₁ s m₁) (h₂ : Good G₂ s m₂) (w₁ : V₁) (w₂ : V₂) :
    Good (glue G₁ G₂ w₁ w₂) s (m₁ + m₂) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- cardinality
    have hc : Fintype.card {y : V₂ // y ≠ w₂} = Fintype.card V₂ - 1 := by
      rw [Fintype.card_subtype_compl (fun y => y = w₂), Fintype.card_subtype_eq]
    rw [Fintype.card_sum, hc, Nat.mul_add]
    have := h₁.card
    have := h₂.card
    omega
  · -- colourings
    rintro (a | b)
    · obtain ⟨c₁, hc₁⟩ := h₁.col a
      obtain ⟨c₂, hc₂⟩ := h₂.col w₂
      refine ⟨Sum.elim (fun x => Fin.castAdd m₂ (c₁ x)) (fun y => Fin.natAdd m₁ (c₂ y.1)), ?_⟩
      rintro (x | y) (x' | y') hx hx' hadj
      · have hxa : x ≠ a := fun h => hx (by rw [h])
        have hxa' : x' ≠ a := fun h => hx' (by rw [h])
        intro heq
        exact hc₁ x x' hxa hxa' hadj (Fin.castAdd_injective _ _ heq)
      · intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      · intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      · intro heq
        exact hc₂ y.1 y'.1 y.2 y'.2 hadj (Fin.natAdd_injective _ _ heq)
    · obtain ⟨c₁, hc₁⟩ := h₁.col w₁
      obtain ⟨c₂, hc₂⟩ := h₂.col b.1
      have hwb : w₂ ≠ b.1 := fun h => b.2 h.symm
      refine ⟨Sum.elim (fun x => if x = w₁ then Fin.natAdd m₁ (c₂ w₂) else Fin.castAdd m₂ (c₁ x))
        (fun y => Fin.natAdd m₁ (c₂ y.1)), ?_⟩
      rintro (x | y) (x' | y') hx hx' hadj
      · have hadj' : G₁.Adj x x' := hadj
        by_cases hxw : x = w₁ <;> by_cases hxw' : x' = w₁ <;>
          simp only [Sum.elim_inl, hxw, hxw', if_true, if_false]
        · exact absurd hadj' (by rw [hxw, hxw']; exact G₁.irrefl)
        · intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        · intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        · intro heq
          exact hc₁ x x' hxw hxw' hadj' (Fin.castAdd_injective _ _ heq)
      · have hyb : y'.1 ≠ b.1 := fun h => hx' (by rw [Subtype.ext h])
        have hadj' : x ≠ w₁ ∨ G₂.Adj w₂ y'.1 := hadj
        by_cases hxw : x = w₁ <;> simp only [Sum.elim_inl, Sum.elim_inr, hxw, if_true, if_false]
        · rcases hadj' with h | h
          · exact absurd hxw h
          · intro heq
            exact hc₂ w₂ y'.1 hwb hyb h (Fin.natAdd_injective _ _ heq)
        · intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
      · have hyb : y.1 ≠ b.1 := fun h => hx (by rw [Subtype.ext h])
        have hadj' : x' ≠ w₁ ∨ G₂.Adj w₂ y.1 := hadj
        by_cases hxw : x' = w₁ <;> simp only [Sum.elim_inl, Sum.elim_inr, hxw, if_true, if_false]
        · rcases hadj' with h | h
          · exact absurd hxw h
          · intro heq
            exact hc₂ w₂ y.1 hwb hyb h (Fin.natAdd_injective _ _ heq).symm
        · intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
      · have hyb : y.1 ≠ b.1 := fun h => hx (by rw [Subtype.ext h])
        have hyb' : y'.1 ≠ b.1 := fun h => hx' (by rw [Subtype.ext h])
        intro heq
        exact hc₂ y.1 y'.1 hyb hyb' hadj (Fin.natAdd_injective _ _ heq)
  · -- density
    intro X e hX
    by_cases hL : ∀ a ∈ X, ∃ x, (Sum.inl x : V₁ ⊕ {y : V₂ // y ≠ w₂}) = a
    · exact dense_of_map h₁ Sum.inl Sum.inl_injective (fun _ _ h => h) X e hX hL
    by_cases hR : ∀ a ∈ X, ∃ y, glueR w₁ w₂ y = a
    · exact dense_of_map h₂ (glueR w₁ w₂) glueR_injective (fun _ _ h => glue_adj_glueR h) X e hX hR
    -- a vertex of the right side and a vertex of the left side different from `w₁`
    push Not at hL hR
    obtain ⟨b, hbX, hb⟩ := hL
    obtain ⟨a, haX, ha⟩ := hR
    obtain ⟨y, rfl⟩ : ∃ y, Sum.inr y = b := by
      rcases b with x | y
      · exact absurd rfl (hb x)
      · exact ⟨y, rfl⟩
    obtain ⟨x, rfl, hxw⟩ : ∃ x, Sum.inl x = a ∧ x ≠ w₁ := by
      rcases a with x | y'
      · refine ⟨x, rfl, fun h => ha w₂ ?_⟩
        rw [h]; simp [glueR]
      · exact absurd (by simp [glueR, y'.2]) (ha y'.1)
    -- look for a third vertex giving a second cross edge
    by_cases h3 : ∃ c ∈ X, c ≠ Sum.inl x ∧ c ≠ Sum.inr y ∧ c ≠ Sum.inl w₁
    · obtain ⟨c, hcX, hc1, hc2, hc3⟩ := h3
      have hxy : (glue G₁ G₂ w₁ w₂).Adj (Sum.inl x) (Sum.inr y) := Or.inl hxw
      by_cases he : s((Sum.inl x : V₁ ⊕ {y : V₂ // y ≠ w₂}), Sum.inr y) = e
      · rcases c with x' | y'
        · have hx'w : x' ≠ w₁ := fun h => hc3 (by rw [h])
          refine ⟨Sum.inl x', hcX, Sum.inr y, hbX, Or.inl hx'w, fun he' => hc1 ?_⟩
          have h2 := he'.trans he.symm
          simp at h2
          rw [h2]
        · refine ⟨Sum.inl x, haX, Sum.inr y', hcX, Or.inl hxw, fun he' => hc2 ?_⟩
          have h2 := he'.trans he.symm
          simp at h2
          rw [h2]
      · exact ⟨_, haX, _, hbX, hxy, he⟩
    · push Not at h3
      have hsub : X ⊆ {Sum.inl x, Sum.inr y, Sum.inl w₁} := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hcon
        push Not at hcon
        exact hcon.2.2 (h3 c hc hcon.1 hcon.2.1)
      have := (Finset.card_le_card hsub).trans Finset.card_le_three
      omega

end Glue


section Circ

/-- Circulant graph on `Fin n` whose connection set is given by the bits of `mask`. -/
def circ (n : ℕ) [NeZero n] (mask : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (mask.testBit (y - x).val = true ∨ mask.testBit (x - y).val = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance circDec (n : ℕ) [NeZero n] (mask : ℕ) : DecidableRel (circ n mask).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧
    (mask.testBit (y - x).val = true ∨ mask.testBit (x - y).val = true)))

theorem circ_adj_sub {n : ℕ} [NeZero n] (mask : ℕ) (x y v : Fin n) :
    (circ n mask).Adj (x - v) (y - v) ↔ (circ n mask).Adj x y := by
  show (x - v ≠ y - v ∧ _) ↔ (x ≠ y ∧ _)
  rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]
  simp

theorem circ_adj_add {n : ℕ} [NeZero n] (mask : ℕ) (x y v : Fin n) :
    (circ n mask).Adj (x + v) (y + v) ↔ (circ n mask).Adj x y := by
  have := circ_adj_sub mask (x + v) (y + v) v
  simpa using this.symm

/-- `c0` is a proper colouring of the circulant graph minus the vertex `0`. -/
def ColProp (n m mask : ℕ) [NeZero n] (c0 : Fin n → Fin m) : Prop :=
  ∀ x y : Fin n, x ≠ 0 → y ≠ 0 → (circ n mask).Adj x y → c0 x ≠ c0 y

instance colPropDec (n m mask : ℕ) [NeZero n] (c0 : Fin n → Fin m) :
    Decidable (ColProp n m mask c0) := by
  unfold ColProp; infer_instance

/-- Every triangle `{0, a, b}` of the complement has at most one common neighbour in the
complement. -/
def LocProp (n mask : ℕ) [NeZero n] : Prop :=
  ∀ a : Fin n, a ≠ 0 → ¬ (circ n mask).Adj 0 a →
    ∀ b : Fin n, b ≠ 0 → b ≠ a → ¬ (circ n mask).Adj 0 b → ¬ (circ n mask).Adj a b →
    ∀ c : Fin n, c ≠ 0 → c ≠ a → c ≠ b → ¬ (circ n mask).Adj 0 c → ¬ (circ n mask).Adj a c →
      ¬ (circ n mask).Adj b c →
    ∀ d : Fin n, d ≠ 0 → d ≠ a → d ≠ b → ¬ (circ n mask).Adj 0 d → ¬ (circ n mask).Adj a d →
      ¬ (circ n mask).Adj b d → c = d

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance locPropDec (n mask : ℕ) [NeZero n] : Decidable (LocProp n mask) := by
  unfold LocProp; infer_instance

/-- A circulant graph with a `m`-colouring away from `0` and in which every `4`-clique of the
complement is determined by any three of its vertices is a counting certificate. -/
theorem good_circ {n : ℕ} [NeZero n] (mask m : ℕ) (hn : 4 * m < n) (c0 : Fin n → Fin m)
    (hc0 : ColProp n m mask c0) (hloc : LocProp n mask) :
    Good (circ n mask) 4 m := by
  classical
  refine ⟨by rw [Fintype.card_fin]; exact hn, fun v => ⟨fun x => c0 (x - v), ?_⟩, ?_⟩
  · intro x y hx hy hxy
    exact hc0 _ _ (sub_ne_zero.2 hx) (sub_ne_zero.2 hy) ((circ_adj_sub mask x y v).2 hxy)
  · intro X e hX
    induction e using Sym2.ind with
    | _ p q =>
    by_contra hno
    have hno' : ∀ x ∈ X, ∀ y ∈ X, x ≠ p → x ≠ q → ¬ (circ n mask).Adj x y := by
      intro x hx y hy hxp hxq hadj
      refine hno ⟨x, hx, y, hy, hadj, fun he => ?_⟩
      rcases Sym2.eq_iff.1 he with h | h
      · exact hxp h.1
      · exact hxq h.1
    have h3 : 2 < ((X.erase p).erase q).card := by
      have h1 := Finset.pred_card_le_card_erase (s := X) (a := p)
      have h2 := Finset.pred_card_le_card_erase (s := X.erase p) (a := q)
      omega
    obtain ⟨u1, u2, u3, h1, h2, h3', h12, h13, h23⟩ := Finset.two_lt_card_iff.1 h3
    have hu : ∀ u ∈ (X.erase p).erase q, u ∈ X ∧ u ≠ p ∧ u ≠ q := by
      intro u hu
      rw [Finset.mem_erase, Finset.mem_erase] at hu
      exact ⟨hu.2.2, hu.2.1, hu.1⟩
    obtain ⟨hu1X, hu1p, hu1q⟩ := hu u1 h1
    obtain ⟨hu2X, hu2p, hu2q⟩ := hu u2 h2
    obtain ⟨hu3X, hu3p, hu3q⟩ := hu u3 h3'
    have h2' : 1 < (((X.erase u1).erase u2).erase u3).card := by
      have k1 := Finset.pred_card_le_card_erase (s := X) (a := u1)
      have k2 := Finset.pred_card_le_card_erase (s := X.erase u1) (a := u2)
      have k3 := Finset.pred_card_le_card_erase (s := (X.erase u1).erase u2) (a := u3)
      omega
    obtain ⟨c, d, hc, hd, hcd⟩ := Finset.one_lt_card_iff.1 h2'
    have hv : ∀ z ∈ ((X.erase u1).erase u2).erase u3, z ∈ X ∧ z ≠ u1 ∧ z ≠ u2 ∧ z ≠ u3 := by
      intro z hz
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at hz
      exact ⟨hz.2.2.2, hz.2.2.1, hz.2.1, hz.1⟩
    obtain ⟨hcX, hc1, hc2, hc3⟩ := hv c hc
    obtain ⟨hdX, hd1, hd2, hd3⟩ := hv d hd
    have key := hloc (u2 - u1) (sub_ne_zero.2 h12.symm)
      (by rw [← sub_self u1, circ_adj_sub]; exact hno' u1 hu1X u2 hu2X hu1p hu1q)
      (u3 - u1) (sub_ne_zero.2 h13.symm) (fun h => h23 (sub_left_injective h).symm)
      (by rw [← sub_self u1, circ_adj_sub]; exact hno' u1 hu1X u3 hu3X hu1p hu1q)
      (by rw [circ_adj_sub]; exact hno' u2 hu2X u3 hu3X hu2p hu2q)
      (c - u1) (sub_ne_zero.2 hc1) (fun h => hc2 (sub_left_injective h))
      (fun h => hc3 (sub_left_injective h))
      (by rw [← sub_self u1, circ_adj_sub]; exact hno' u1 hu1X c hcX hu1p hu1q)
      (by rw [circ_adj_sub]; exact hno' u2 hu2X c hcX hu2p hu2q)
      (by rw [circ_adj_sub]; exact hno' u3 hu3X c hcX hu3p hu3q)
      (d - u1) (sub_ne_zero.2 hd1) (fun h => hd2 (sub_left_injective h))
      (fun h => hd3 (sub_left_injective h))
      (by rw [← sub_self u1, circ_adj_sub]; exact hno' u1 hu1X d hdX hu1p hu1q)
      (by rw [circ_adj_sub]; exact hno' u2 hu2X d hdX hu2p hu2q)
      (by rw [circ_adj_sub]; exact hno' u3 hu3X d hdX hu3p hu3q)
    exact hcd (sub_left_injective key)

/- The base graphs. -/

def col17 : Fin 17 → Fin 4 := ![0, 0, 0, 1, 1, 0, 0, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3]

theorem good17 : Good (circ 17 36804) 4 4 :=
  good_circ 36804 4 (by norm_num) col17 (by decide +kernel) (by decide +kernel)

def col25 : Fin 25 → Fin 6 := ![0, 0, 0, 1, 1, 0, 0, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3, 4, 4, 5, 5, 4, 4, 5, 5]

theorem good25 : Good (circ 25 9437124) 4 6 :=
  good_circ 9437124 6 (by norm_num) col25 (by decide +kernel) (by decide +kernel)

def col29 : Fin 29 → Fin 7 := ![0, 0, 0, 1, 1, 0, 0, 2, 2, 3, 3, 4, 4, 5, 5, 4, 4, 5, 5, 6, 6, 1, 1, 6, 6, 2, 2, 3, 3]

theorem good29 : Good (circ 29 150070212) 4 7 :=
  good_circ 150070212 7 (by norm_num) col29 (by decide +kernel) (by decide +kernel)

def col37 : Fin 37 → Fin 9 := ![0, 0, 0, 1, 1, 2, 2, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 6, 6, 7, 7, 8, 8]

theorem good37 : Good (circ 37 61203283740) 4 9 :=
  good_circ 61203283740 9 (by norm_num) col37 (by decide +kernel) (by decide +kernel)


end Circ


section Puncture

/-- Balanced puncture at one vertex plus enough symmetries gives a certificate. -/
theorem cert_of_puncture {V : Type u} (G : SimpleGraph V) (p : ℕ) (r : V)
    (htrans : ∀ u : V, ∃ ψ : V → V, Function.Injective ψ ∧ ψ r = u ∧
      ∀ x y, G.Adj x y → G.Adj (ψ x) (ψ y))
    (htrans' : ∀ u : V, ∃ ψ : V → V, Function.Injective ψ ∧ ψ u = r ∧
      ∀ x y, G.Adj x y → G.Adj (ψ x) (ψ y))
    (c0 : V → Fin p) (hc0 : ∀ x y, x ≠ r → y ≠ r → G.Adj x y → c0 x ≠ c0 y)
    (hbal : ∀ f : V → Fin p, (∀ x y, x ≠ r → y ≠ r → G.Adj x y → f x ≠ f y) →
      ∀ c : Fin p, ∃ u w, u ≠ w ∧ G.Adj r u ∧ G.Adj r w ∧ f u = c ∧ f w = c) :
    Cert G p := by
  refine ⟨fun v => ?_, fun e f => ?_⟩
  · obtain ⟨ψ, hinj, hv, hhom⟩ := htrans' v
    refine ⟨fun x => c0 (ψ x), fun x y hx hy hxy => ?_⟩
    exact hc0 _ _ (fun h => hx (hinj (h.trans hv.symm))) (fun h => hy (hinj (h.trans hv.symm)))
      (hhom _ _ hxy)
  · induction e using Sym2.ind with
    | _ a b =>
    obtain ⟨ψ, hinj, ha, hhom⟩ := htrans a
    by_contra hno
    have hno' : ∀ x y, G.Adj x y → s(x, y) ≠ s(a, b) → f x ≠ f y :=
      fun x y hxy hne hf => hno ⟨x, y, hxy, hne, hf⟩
    have hproper : ∀ x y, x ≠ r → y ≠ r → G.Adj x y → f (ψ x) ≠ f (ψ y) := by
      intro x y hx hy hxy
      refine hno' _ _ (hhom _ _ hxy) (fun he => ?_)
      rcases Sym2.eq_iff.1 he with h | h
      · exact hx (hinj (h.1.trans ha.symm))
      · exact hy (hinj (h.2.trans ha.symm))
    obtain ⟨u, w, huw, hru, hrw, hu, hw⟩ := hbal (fun x => f (ψ x)) hproper (f (ψ r))
    have step : ∀ z, G.Adj r z → f (ψ z) = f (ψ r) → ψ z = b := by
      intro z hrz hz
      by_contra hzb
      have hadj : G.Adj a (ψ z) := by
        have := hhom _ _ hrz
        rwa [ha] at this
      refine hno' _ _ hadj (fun he => ?_) (by rw [← ha]; exact hz.symm)
      rcases Sym2.eq_iff.1 he with h | h
      · exact hzb h.2
      · exact hrz.ne (hinj (ha.trans h.2.symm))
    exact huw (hinj ((step u hru hu).trans (step w hrw hw).symm))

/-- Iterates of an adjacency-preserving map preserve adjacency. -/
theorem hom_iterate {V : Type u} (G : SimpleGraph V) (φ : V → V)
    (h : ∀ x y, G.Adj x y → G.Adj (φ x) (φ y)) (k : ℕ) :
    ∀ x y, G.Adj x y → G.Adj (φ^[k] x) (φ^[k] y) := by
  induction k with
  | zero => exact fun _ _ hxy => hxy
  | succ k ih =>
    intro x y hxy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact h _ _ (ih x y hxy)

/-- Leaf test of the search: every colour occurs on both ends of one of the listed pairs. -/
def leaf (p : ℕ) (pairs : List (ℕ × ℕ)) (M : ℕ) : Bool :=
  (List.range p).all fun c =>
    pairs.any fun uw => M.testBit (64 * c + uw.1) && M.testBit (64 * c + uw.2)

/-- `allBelow f p` tests `f c` for every `c < p`. -/
def allBelow (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | c + 1 => f c && allBelow f c

/-- If `allBelow f p` holds then `f c` holds for every `c < p`. -/
theorem allBelow_spec {f : ℕ → Bool} :
    ∀ {p : ℕ}, allBelow f p = true → ∀ c < p, f c = true := by
  intro p
  induction p with
  | zero => exact fun _ c hc => absurd hc (Nat.not_lt_zero c)
  | succ n ih =>
    intro h c hc
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h1 | h1
    · exact ih h.2 c h1
    · rw [h1]; exact h.1

/-- `ifZero n b` is `b` when `n = 0` and `true` otherwise. -/
def ifZero (n : ℕ) (b : Bool) : Bool :=
  match n with
  | 0 => b
  | _ + 1 => true

/-- Exhaustive search over all colourings (with `p` colours) of the vertices listed in the
order, respecting the neighbour masks. Bit `64 * c + v` of the state `M` says that the vertex
`v` has colour `c`. The arithmetic is written with the primitive operations on natural numbers,
which the kernel evaluates directly. -/
def search (p : ℕ) (pairs : List (ℕ × ℕ)) : List (ℕ × ℕ) → ℕ → Bool
  | [], M => leaf p pairs M
  | (v, nb) :: rest, M =>
      allBelow (fun c => ifZero (Nat.land (Nat.shiftLeft nb (Nat.mul 64 c)) M)
        (search p pairs rest (Nat.lor M (Nat.shiftLeft 1 (Nat.add (Nat.mul 64 c) v))))) p

/-- The state in which the vertices of the list have the colours `k`, `k + 1`, ... -/
def preState : List ℕ → ℕ → ℕ → ℕ
  | [], _, M => M
  | v :: rest, k, M => preState rest (k + 1) (M ||| (1 <<< (64 * k + v)))

/-- Giving the vertex `v` its colour keeps the description of the state. -/
theorem inv_update (g : ℕ → ℕ) (done : List ℕ) (M v : ℕ) (hv : v < 64)
    (hM : ∀ c v', v' < 64 → (M.testBit (64 * c + v') = true ↔ v' ∈ done ∧ g v' = c)) :
    ∀ c v', v' < 64 →
      ((M ||| (1 <<< (64 * g v + v))).testBit (64 * c + v') = true ↔ v' ∈ v :: done ∧ g v' = c) := by
  intro c v' hv'
  rw [Nat.testBit_or, Bool.or_eq_true, hM c v' hv', Nat.one_shiftLeft, Nat.testBit_two_pow,
    decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · exact ⟨Or.inr h1, h2⟩
    · have h1 : v' = v := by omega
      have h2 : g v = c := by omega
      exact ⟨Or.inl h1, by rw [h1]; exact h2⟩
  · rintro ⟨h1 | h1, h2⟩
    · right
      rw [h1] at h2 ⊢
      rw [h2]
    · exact Or.inl ⟨h1, h2⟩

/-- If the colouring `g` gives the vertices of `pre` the colours `k`, `k + 1`, ..., and the
state `M` describes `g` on the vertices of `done`, then `preState pre k M` describes `g` on a
larger list of vertices. -/
theorem inv_preState (g : ℕ → ℕ) : ∀ (pre : List ℕ) (k : ℕ) (done : List ℕ) (M : ℕ),
    (∀ i (hi : i < pre.length), pre[i] < 64 ∧ g pre[i] = k + i) →
    (∀ c v, v < 64 → (M.testBit (64 * c + v) = true ↔ v ∈ done ∧ g v = c)) →
    ∃ done' : List ℕ, ∀ c v, v < 64 →
      ((preState pre k M).testBit (64 * c + v) = true ↔ v ∈ done' ∧ g v = c) := by
  intro pre
  induction pre with
  | nil => exact fun k done M _ hM => ⟨done, hM⟩
  | cons v rest ih =>
    intro k done M hpre hM
    obtain ⟨hv, hgv⟩ := hpre 0 (Nat.succ_pos _)
    have hgv' : g v = k := hgv
    refine ih (k + 1) (v :: done) (M ||| (1 <<< (64 * k + v))) (fun i hi => ?_) ?_
    · have := hpre (i + 1) (Nat.succ_lt_succ hi)
      refine ⟨this.1, ?_⟩
      have h2 : g rest[i] = k + (i + 1) := this.2
      omega
    · rw [← hgv']
      exact inv_update g done M v hv hM

/-- Soundness of the search. Let `g` be a colouring respecting the neighbour masks of the
order, and let the state `M` describe `g` on the vertices coloured so far. If the search
succeeds, then every colour occurs (under `g`) on both ends of one of the listed pairs: the
branch of the search following `g` is never cut. -/
theorem search_sound (g : ℕ → ℕ) (p : ℕ) (pairs : List (ℕ × ℕ))
    (hpairs : ∀ uw ∈ pairs, uw.1 < 64 ∧ uw.2 < 64) :
    ∀ (order : List (ℕ × ℕ)) (done : List ℕ) (M : ℕ),
      (∀ vn ∈ order, vn.1 < 64 ∧ vn.2 < 2 ^ 64 ∧ g vn.1 < p ∧
        ∀ i, vn.2.testBit i = true → g vn.1 ≠ g i) →
      (∀ c v, v < 64 → (M.testBit (64 * c + v) = true ↔ v ∈ done ∧ g v = c)) →
      search p pairs order M = true →
      ∀ c < p, ∃ uw ∈ pairs, g uw.1 = c ∧ g uw.2 = c := by
  intro order
  induction order with
  | nil =>
    intro done M _ hM hs c hc
    simp only [search, leaf, List.all_eq_true, List.mem_range, List.any_eq_true,
      Bool.and_eq_true] at hs
    obtain ⟨uw, huw, h1, h2⟩ := hs c hc
    obtain ⟨hlt1, hlt2⟩ := hpairs uw huw
    exact ⟨uw, huw, ((hM c uw.1 hlt1).1 h1).2, ((hM c uw.2 hlt2).1 h2).2⟩
  | cons vn rest ih =>
    intro done M hval hM hs
    obtain ⟨v, nb⟩ := vn
    obtain ⟨hv64, hnb, hgv, hadj⟩ := hval (v, nb) (List.mem_cons_self ..)
    have hs' : ifZero ((nb <<< (64 * g v)) &&& M)
        (search p pairs rest (M ||| (1 <<< (64 * g v + v)))) = true :=
      allBelow_spec hs (g v) hgv
    have hzero : (nb <<< (64 * g v)) &&& M = 0 := by
      by_contra hne'
      obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hne'
      rw [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_shiftLeft, Bool.and_eq_true,
        decide_eq_true_eq] at hj
      obtain ⟨⟨hge, hbit⟩, hMj⟩ := hj
      have hi64 : j - 64 * g v < 64 := by
        by_contra hcon
        have : nb.testBit (j - 64 * g v) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hnb (Nat.pow_le_pow_right (by norm_num)
            (not_lt.1 hcon)))
        rw [this] at hbit
        exact Bool.false_ne_true hbit
      have hj' : j = 64 * g v + (j - 64 * g v) := by omega
      rw [hj'] at hMj
      exact hadj _ hbit ((hM _ _ hi64).1 hMj).2.symm
    rw [hzero] at hs'
    exact ih (v :: done) _ (fun vn hvn => hval vn (List.mem_cons_of_mem _ hvn))
      (inv_update g done M v hv64 hM) hs'

/-- Adjacency of a graph on `Fin n`, as a function on natural numbers. -/
def adjNat {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x y : ℕ) : Bool :=
  if h : x < n ∧ y < n then decide (G.Adj ⟨x, h.1⟩ ⟨y, h.2⟩) else false

/-- The search data only uses genuine edges avoiding the vertex `r`. -/
def OrderOK {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (order : List (ℕ × ℕ)) : Bool :=
  order.all fun vn => decide (vn.1 < n) && decide (vn.1 ≠ r) && decide (vn.2 < 2 ^ 64) &&
    (List.range 64).all fun i => !vn.2.testBit i || (decide (i ≠ r) && adjNat G vn.1 i)

/-- The listed pairs are pairs of distinct neighbours of `r`. -/
def PairsOK {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (pairs : List (ℕ × ℕ)) : Bool :=
  pairs.all fun uw => decide (uw.1 ≠ uw.2) && adjNat G r uw.1 && adjNat G r uw.2

/-- The precoloured vertices are at most `p` pairwise adjacent vertices different from `r`. -/
def PreOK {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r p : ℕ)
    (pre : List ℕ) : Bool :=
  decide (pre.length ≤ p) && (pre.all fun v => decide (v < n) && decide (v ≠ r)) &&
    decide (pre.Pairwise fun x y => adjNat G x y = true)

/-- `adjNat` only holds for (numbers of) adjacent vertices. -/
theorem adjNat_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {x y : ℕ}
    (h : adjNat G x y = true) : ∃ (hx : x < n) (hy : y < n), G.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold adjNat at h
  by_cases hxy : x < n ∧ y < n
  · rw [dif_pos hxy] at h
    exact ⟨hxy.1, hxy.2, of_decide_eq_true h⟩
  · rw [dif_neg hxy] at h
    exact absurd h Bool.false_ne_true

/-- If the search succeeds, starting from the colouring of a clique by distinct colours (which
is no restriction up to a permutation of the colours), then every proper colouring of `G - r`
uses every colour on two different neighbours of `r`. -/
theorem bal_of_search {n : ℕ} (hn : n ≤ 64) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (r : Fin n) (p : ℕ) (pre : List ℕ) (pairs order : List (ℕ × ℕ))
    (hpre : PreOK G r.val p pre = true)
    (hord : OrderOK G r.val order = true) (hpairs : PairsOK G r.val pairs = true)
    (hsearch : search p pairs order (preState pre 0 0) = true)
    (f : Fin n → Fin p) (hf : ∀ x y, x ≠ r → y ≠ r → G.Adj x y → f x ≠ f y) (c : Fin p) :
    ∃ u w, u ≠ w ∧ G.Adj r u ∧ G.Adj r w ∧ f u = c ∧ f w = c := by
  have hpairs' : ∀ uw ∈ pairs, uw.1 ≠ uw.2 ∧ adjNat G r.val uw.1 = true ∧
      adjNat G r.val uw.2 = true := by
    intro uw huw
    have := List.all_eq_true.1 hpairs uw huw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hord' : ∀ vn ∈ order, vn.1 < n ∧ vn.1 ≠ r.val ∧ vn.2 < 2 ^ 64 ∧
      ∀ i < 64, vn.2.testBit i = true → i ≠ r.val ∧ adjNat G vn.1 i = true := by
    intro vn hvn
    have := List.all_eq_true.1 hord vn hvn
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, Bool.not_eq_true'] at this
    refine ⟨this.1.1.1, this.1.1.2, this.1.2, fun i hi hbit => ?_⟩
    rcases this.2 i hi with h | h
    · rw [h] at hbit
      exact absurd hbit Bool.false_ne_true
    · exact h
  -- the precoloured clique
  unfold PreOK at hpre
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hpre
  obtain ⟨⟨hlen, hpre1⟩, hpre2⟩ := hpre
  have hlt : ∀ i (hi : i < pre.length), pre[i] < n ∧ pre[i] ≠ r.val :=
    fun i hi => hpre1 _ (List.getElem_mem hi)
  have hclique := List.pairwise_iff_getElem.1 hpre2
  -- a permutation of the colours which makes the colouring standard on the clique
  have hinj : Function.Injective
      (fun i : Fin pre.length => f ⟨pre[i.val], (hlt i.val i.isLt).1⟩) := by
    intro i j hij
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · obtain ⟨_, _, hG⟩ := adjNat_spec G (hclique i.val j.val i.isLt j.isLt h)
      exact hf _ _ (fun h' => (hlt i.val i.isLt).2 (congrArg Fin.val h'))
        (fun h' => (hlt j.val j.isLt).2 (congrArg Fin.val h')) hG hij
    · obtain ⟨_, _, hG⟩ := adjNat_spec G (hclique j.val i.val j.isLt i.isLt h)
      exact hf _ _ (fun h' => (hlt j.val j.isLt).2 (congrArg Fin.val h'))
        (fun h' => (hlt i.val i.isLt).2 (congrArg Fin.val h')) hG hij.symm
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hinj (Fin.castLE_injective hlen)
  let g : ℕ → ℕ := fun i => if h : i < n then (σ (f ⟨i, h⟩)).val else 0
  have hg : ∀ (i : ℕ) (h : i < n), g i = (σ (f ⟨i, h⟩)).val := fun i h => dif_pos h
  obtain ⟨done, hinv⟩ := inv_preState g pre 0 [] 0
    (fun i hi => by
      refine ⟨lt_of_lt_of_le (hlt i hi).1 hn, ?_⟩
      rw [hg _ (hlt i hi).1, zero_add]
      exact congrArg Fin.val (hσ ⟨i, hi⟩))
    (fun c v _ => by simp)
  obtain ⟨uw, huw, h1, h2⟩ := search_sound g p pairs
    (fun uw huw => by
      obtain ⟨-, ha, hb⟩ := hpairs' uw huw
      obtain ⟨-, h1, -⟩ := adjNat_spec G ha
      obtain ⟨-, h2, -⟩ := adjNat_spec G hb
      exact ⟨lt_of_lt_of_le h1 hn, lt_of_lt_of_le h2 hn⟩)
    order done _
    (fun vn hvn => by
      obtain ⟨hvn1, hvr, hnb, hbits⟩ := hord' vn hvn
      refine ⟨lt_of_lt_of_le hvn1 hn, hnb, ?_, fun i hbit => ?_⟩
      · rw [hg _ hvn1]
        exact (σ (f _)).isLt
      · have hi64 : i < 64 := by
          by_contra hcon
          have : vn.2.testBit i = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hnb (Nat.pow_le_pow_right (by norm_num)
              (not_lt.1 hcon)))
          rw [this] at hbit
          exact Bool.false_ne_true hbit
        obtain ⟨hir, hadj⟩ := hbits i hi64 hbit
        obtain ⟨hx, hy, hG⟩ := adjNat_spec G hadj
        rw [hg _ hx, hg _ hy]
        intro heq
        exact hf ⟨vn.1, hx⟩ ⟨i, hy⟩ (fun h => hvr (congrArg Fin.val h))
          (fun h => hir (congrArg Fin.val h)) hG (σ.injective (Fin.ext heq)))
    hinv hsearch (σ c).val (σ c).isLt
  obtain ⟨hne, ha, hb⟩ := hpairs' uw huw
  obtain ⟨hr1, hu, hGu⟩ := adjNat_spec G ha
  obtain ⟨hr2, hw, hGw⟩ := adjNat_spec G hb
  refine ⟨⟨uw.1, hu⟩, ⟨uw.2, hw⟩, fun h => hne (congrArg Fin.val h), hGu, hGw, ?_, ?_⟩
  · exact σ.injective (Fin.ext (by rw [← hg _ hu]; exact h1))
  · exact σ.injective (Fin.ext (by rw [← hg _ hw]; exact h2))

end Puncture


section Sixty

/-- Adjacency bit masks of the graph on 60 vertices: the vertices `x` and `y` are adjacent if
the bit `y` of the entry number `x` is set. -/
def tbl60 : List ℕ := [36028944188702752, 72057888377405504, 144115743468814464, 288230421785739520, 576460842531291648, 17699560227841, 1314259994626, 2628519989252, 5223753981960, 9382356074512, 287522290696224, 573979429503040, 57243324252288, 80401788043520, 160803576087040, 2858730233267200, 4626744931780608, 9219405003100160, 18438810006200320, 1974722900279296, 154318656015204352, 308637312030408704, 582371726948696064, 47850746309509120, 94610777084264448, 112589991759052816, 225179983518105601, 450359967036211202, 865817036960301060, 614741366332719112, 576460786696716549, 36028865805550090, 72057731611099188, 144115463222198345, 288230926444396690, 1100585372200, 2201170743408, 4402341486785, 8804682973570, 17609365915396, 35218731967552, 70437463935104, 140874927838464, 281749854661120, 563499709321248, 1126999435350016, 2253998838194176, 4507997676388352, 9015995352744960, 18031990704474112, 36063981665255424, 72127963329495040, 144255925618802688, 288511851205099520, 577023702410199040, 1125902633140225, 2251804226093058, 4503608419680260, 9007216839360520, 18014400392724496]

/-- The Cayley graph on `ZMod 5 ⋊ ZMod 12` (labels `5 * a + i`) with connection set
`(1,0), (11,0), (5,1), (7,2), (6,0), (6,3)`, given by its adjacency bit masks. -/
def G60 : SimpleGraph (Fin 60) where
  Adj x y := (tbl60.getD x.val 0).testBit y.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance G60Dec : DecidableRel G60.Adj :=
  fun x y => inferInstanceAs (Decidable ((tbl60.getD x.val 0).testBit y.val = true))

/-- Left multiplication by the group element `(1, 0)`, on labels: `(b, j) ↦ (b + 1, 2 * j)`. -/
def rot60 (x : Fin 60) : Fin 60 :=
  ⟨(5 * ((x.val / 5 + 1) % 12) + (2 * (x.val % 5)) % 5) % 60, Nat.mod_lt _ (by norm_num)⟩

/-- Left multiplication by the group element `(0, 1)`, on labels: `(b, j) ↦ (b, j + 1)`. -/
def shift60 (x : Fin 60) : Fin 60 :=
  ⟨(5 * (x.val / 5) + (x.val % 5 + 1) % 5) % 60, Nat.mod_lt _ (by norm_num)⟩

theorem rot60_hom : ∀ x y : Fin 60, G60.Adj x y → G60.Adj (rot60 x) (rot60 y) := by
  decide +kernel

theorem shift60_hom : ∀ x y : Fin 60, G60.Adj x y → G60.Adj (shift60 x) (shift60 y) := by
  decide +kernel

theorem rot60_injective : Function.Injective rot60 := by
  have h : ∀ x : Fin 60, rot60^[11] (rot60 x) = x := by decide +kernel
  exact Function.LeftInverse.injective h

theorem shift60_injective : Function.Injective shift60 := by
  have h : ∀ x : Fin 60, shift60^[4] (shift60 x) = x := by decide +kernel
  exact Function.LeftInverse.injective h

/-- Left multiplication by the group element with label `u`, which is `(0, 1) ^ i * (1, 0) ^ a`
for `u = 5 * a + i`. -/
def mul60 (u x : Fin 60) : Fin 60 := shift60^[u.val % 5] (rot60^[u.val / 5] x)

/-- Left multiplication by the inverse of the group element with label `u`. -/
def inv60 (u x : Fin 60) : Fin 60 :=
  rot60^[(12 - u.val / 5) % 12] (shift60^[(5 - u.val % 5) % 5] x)

theorem mul60_zero : ∀ u : Fin 60, mul60 u 0 = u := by decide +kernel

theorem inv60_self : ∀ u : Fin 60, inv60 u u = 0 := by decide +kernel

theorem mul60_injective (u : Fin 60) : Function.Injective (mul60 u) :=
  (shift60_injective.iterate _).comp (rot60_injective.iterate _)

theorem inv60_injective (u : Fin 60) : Function.Injective (inv60 u) :=
  (rot60_injective.iterate _).comp (shift60_injective.iterate _)

theorem mul60_hom (u x y : Fin 60) (h : G60.Adj x y) : G60.Adj (mul60 u x) (mul60 u y) :=
  hom_iterate G60 shift60 shift60_hom _ _ _ (hom_iterate G60 rot60 rot60_hom _ _ _ h)

theorem inv60_hom (u x y : Fin 60) (h : G60.Adj x y) : G60.Adj (inv60 u x) (inv60 u y) :=
  hom_iterate G60 rot60 rot60_hom _ _ _ (hom_iterate G60 shift60 shift60_hom _ _ _ h)

/-- A proper colouring of the graph minus the vertex `0`, with 3 colours. -/
def col60 : Fin 60 → Fin 3 := ![0, 0, 1, 0, 2, 1, 1, 0, 2, 1, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2, 2, 0, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 1, 1, 1, 1, 2, 0, 2, 0, 2, 0, 2, 1]

theorem col60_ok : ∀ x y : Fin 60, x ≠ 0 → y ≠ 0 → G60.Adj x y → col60 x ≠ col60 y := by
  decide +kernel

/-- Two adjacent vertices; the search only looks at the colourings which give them the colours
`0` and `1`. -/
def pre60 : List ℕ := [18, 48]

/-- The other vertices different from `0`, in the order in which the search colours them,
each with the bit mask of its neighbours different from `0`. -/
def order60 : List (ℕ × ℕ) := [(43, 281749854661120), (13, 80401788043520), (10, 287522290696224), (40, 35218731967552), (35, 1100585372200), (9, 9382356074512), (39, 17609365915396), (5, 17699560227840), (44, 563499709321248), (15, 2858730233267200), (49, 18031990704474112), (11, 573979429503040), (16, 4626744931780608), (45, 1126999435350016), (41, 70437463935104), (14, 160803576087040), (19, 1974722900279296), (46, 2253998838194176), (12, 57243324252288), (42, 140874927838464), (47, 4507997676388352), (17, 9219405003100160), (8, 5223753981960), (38, 8804682973570), (7, 2628519989252), (37, 4402341486784), (36, 2201170743408), (6, 1314259994626), (1, 72057888377405504), (31, 36028865805550090), (3, 288230421785739520), (33, 144115463222198344), (34, 288230926444396690), (4, 576460842531291648), (32, 72057731611099188), (2, 144115743468814464), (30, 576460786696716548), (25, 112589991759052816), (20, 154318656015204352), (57, 4503608419680260), (52, 144255925618802688), (22, 582371726948696064), (50, 36063981665255424), (27, 450359967036211202), (58, 9007216839360520), (53, 288511851205099520), (23, 47850746309509120), (55, 1125902633140224), (26, 225179983518105600), (56, 2251804226093058), (21, 308637312030408704), (51, 72127963329495040), (54, 577023702410199040), (59, 18014400392724496), (29, 614741366332719112), (28, 865817036960301060), (24, 94610777084264448)]

/-- The pairs of neighbours of the vertex `0`. -/
def pairs60 : List (ℕ × ℕ) := [(5, 26), (5, 30), (5, 33), (5, 37), (5, 55), (26, 30), (26, 33), (26, 37), (26, 55), (30, 33), (30, 37), (30, 55), (33, 37), (33, 55), (37, 55)]

theorem pre60_ok : PreOK G60 0 3 pre60 = true := by decide +kernel

theorem order60_ok : OrderOK G60 0 order60 = true := by decide +kernel

theorem pairs60_ok : PairsOK G60 0 pairs60 = true := by decide +kernel

/-- The exhaustive search (7510 calls): in every proper colouring of the graph minus the vertex
`0` with 3 colours, in which the vertices 18 and 48 have the colours `0` and `1`, every colour
occurs on two neighbours of `0`. -/
theorem search60 : search 3 pairs60 order60 (preState pre60 0 0) = true := by decide +kernel

theorem cert60 : Cert G60 3 :=
  cert_of_puncture G60 3 0
    (fun u => ⟨mul60 u, mul60_injective u, mul60_zero u, mul60_hom u⟩)
    (fun u => ⟨inv60 u, inv60_injective u, inv60_self u, inv60_hom u⟩)
    col60 col60_ok
    (bal_of_search (by norm_num) G60 0 3 pre60 pairs60 order60 pre60_ok order60_ok pairs60_ok
      search60)

end Sixty

section TwentyOne

/-- A proper colouring of the circulant graph on 21 vertices minus the vertex `0`, with 5
colours. -/
def col21 : Fin 21 → Fin 5 := ![0, 1, 3, 1, 3, 2, 4, 2, 4, 0, 1, 0, 1, 3, 2, 3, 2, 4, 0, 4, 0]

theorem col21_ok : ColProp 21 5 1540218 col21 := by decide +kernel

/-- Four pairwise adjacent vertices; the search only looks at the colourings which give them
the colours `0`, `1`, `2`, `3`. -/
def pre21 : List ℕ := [9, 10, 14, 15]

/-- The other vertices different from `0`, in the order in which the search colours them,
each with the bit mask of its neighbours different from `0`. -/
def order21 : List (ℕ × ℕ) := [(11, 251360), (13, 1005440), (8, 31420), (12, 502720), (7, 15710), (6, 7854), (5, 1052502), (4, 1574826), (3, 1835988), (2, 1966570), (18, 716814), (19, 1433630), (1, 983284), (17, 1406982), (16, 1752066), (20, 770108)]

/-- The pairs of neighbours of the vertex `0`. -/
def pairs21 : List (ℕ × ℕ) := [(1, 3), (1, 4), (1, 5), (1, 6), (1, 15), (1, 16), (1, 17), (1, 18), (1, 20), (3, 4), (3, 5), (3, 6), (3, 15), (3, 16), (3, 17), (3, 18), (3, 20), (4, 5), (4, 6), (4, 15), (4, 16), (4, 17), (4, 18), (4, 20), (5, 6), (5, 15), (5, 16), (5, 17), (5, 18), (5, 20), (6, 15), (6, 16), (6, 17), (6, 18), (6, 20), (15, 16), (15, 17), (15, 18), (15, 20), (16, 17), (16, 18), (16, 20), (17, 18), (17, 20), (18, 20)]

theorem pre21_ok : PreOK (circ 21 1540218) 0 5 pre21 = true := by decide +kernel

theorem order21_ok : OrderOK (circ 21 1540218) 0 order21 = true := by decide +kernel

theorem pairs21_ok : PairsOK (circ 21 1540218) 0 pairs21 = true := by decide +kernel

/-- The exhaustive search (187 calls): in every proper colouring of the graph minus the vertex
`0` with 5 colours, in which the vertices 9, 10, 14, 15 have the colours `0`, `1`, `2`, `3`,
every colour occurs on two neighbours of `0`. -/
theorem search21 : search 5 pairs21 order21 (preState pre21 0 0) = true := by decide +kernel

theorem cert21 : Cert (circ 21 1540218) 5 :=
  cert_of_puncture (circ 21 1540218) 5 0
    (fun u => ⟨fun x => x + u, add_left_injective u, zero_add u,
      fun x y h => (circ_adj_add 1540218 x y u).2 h⟩)
    (fun u => ⟨fun x => x - u, sub_left_injective, sub_self u,
      fun x y h => (circ_adj_sub 1540218 x y u).2 h⟩)
    col21 col21_ok
    (bal_of_search (by norm_num) (circ 21 1540218) 0 5 pre21 pairs21 order21 pre21_ok
      order21_ok pairs21_ok search21)

end TwentyOne

section Final

theorem cert_ulift {V : Type} (G : SimpleGraph V) (m : ℕ) (h : Cert G m) :
    Cert (G.comap (ULift.down : ULift.{u} V → V)) m := by
  refine ⟨fun v => ?_, fun e f => ?_⟩
  · obtain ⟨c, hc⟩ := h.col v.down
    refine ⟨fun x => c x.down, fun x y hx hy hxy => ?_⟩
    exact hc _ _ (fun h' => hx (ULift.ext _ _ h')) (fun h' => hy (ULift.ext _ _ h')) hxy
  · obtain ⟨x, y, hxy, hne, hf⟩ := h.rigid (e.map ULift.down) (fun x => f (ULift.up x))
    refine ⟨ULift.up x, ULift.up y, hxy, fun he => hne ?_, hf⟩
    rw [← he]
    rfl

theorem erdos_of_cert {V : Type} [Finite V] [Nonempty V] (G : SimpleGraph V) (m : ℕ)
    (h : Cert G m) : ∃ (W : Type u) (H : SimpleGraph W), H.IsErdos944 (m + 1) 1 :=
  ⟨ULift.{u} V, G.comap ULift.down, cert_erdos _ _ (cert_ulift G m h)⟩

theorem exists_good : ∀ m : ℕ, 6 ≤ m →
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), Good G 4 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h10 : m < 10
    · interval_cases m
      · exact ⟨_, inferInstance, _, good25⟩
      · exact ⟨_, inferInstance, _, good29⟩
      · exact ⟨_, inferInstance, _, good_glue (by norm_num) good17 good17 0 0⟩
      · exact ⟨_, inferInstance, _, good37⟩
    · obtain ⟨V, hV, G, hG⟩ := ih (m - 4) (by omega) (by omega)
      classical
      have hpos : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le _) hG.card
      obtain ⟨w⟩ := Fintype.card_pos_iff.1 hpos
      have := good_glue (by norm_num) hG good17 w 0
      rw [show m - 4 + 4 = m by omega] at this
      exact ⟨_, inferInstance, _, this⟩

end Final

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @Erdos944.erdos_944.variants.dirac_conjecture := by
  intro k hk
  have hcases : k = 4 ∨ k = 6 ∨ k = 5 ∨ 7 ≤ k := by omega
  rcases hcases with rfl | rfl | rfl | h7
  · exact erdos_of_cert G60 3 cert60
  · exact erdos_of_cert (circ 21 1540218) 5 cert21
  · exact erdos_of_cert (circ 17 36804) 4 (good_cert good17)
  · obtain ⟨V, hV, G, hG⟩ := exists_good (k - 1) (by omega)
    have hpos : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le _) hG.card
    have : Nonempty V := Fintype.card_pos_iff.1 hpos
    have := erdos_of_cert G (k - 1) (good_cert hG)
    rwa [show k - 1 + 1 = k by omega] at this
