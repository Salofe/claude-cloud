import OMAReductions.R_Erdos713_erdos_713_parts_i_R3

/-!
# Step H2 of the reduction Erdos713.erdos_713.parts.i.R3

For a graph `F` on `Fin q` without isolated vertices and with `ex(n, F) ≤ q n`, the ratio
`ex(n, F) / n` converges to a positive limit. (Acyclicity, bipartiteness and disconnectedness
are not needed beyond the linear bound, which is a hypothesis of the step.)

The proof is elementary and self-contained; `a n` denotes `ex(n, F)`.

* **Patterns.** Fix a host graph `H` and a nonempty set `X` of hubs. A pattern is a pair `(W, g)`
  with `W ⊆ V(F)` and `g : V(F) → X`; a witness for it embeds `F[W]` outside the hubs so that the
  image of `w ∈ W` is adjacent to `g a` for every neighbour `a ∉ W` of `w` (`IsWit`). A pattern is
  robust if some witness avoids any given set of at most `q` vertices, and `(H, X)` is clean if
  every pattern with a witness is robust.
* **Elimination** (`exists_clean`). If a pattern has a witness but is not robust, all its
  witnesses meet a set `S` of at most `q` vertices; deleting the edges at `S \ X` kills the
  pattern for good, because `F` has no isolated vertex. There are at most `2 ^ q * |X| ^ q`
  patterns, so a clean subgraph is reached after deleting few edges when the non-hub degrees
  are small.
* **Blow-up** (`blow`, `blow_free`). Copy the non-hub part of a clean `F`-free graph into `t + 1`
  layers, all attached to the same hubs. A copy of `F` in the blow-up projects to a map into
  `H` that may have collisions; the part `W` of `F` lying in one layer is a witness of a
  pattern, which is therefore robust, so `W` can be re-embedded away from the rest. Each step
  removes collisions, and in the end `F` embeds in `H`. Hence the blow-up is `F`-free, and it
  has about `t + 1` times as many edges (`card_edgeFinset_blow`).
* **Degree cascade** (`exists_gap`, `exists_clean_sub`). With thresholds `N / c i` for a rapidly
  growing sequence `c`, one of the first `2 q k` degree classes carries a degree sum at most
  `N / k`; deleting its edges leaves at most `2 q c i` hubs of large degree, while all other
  degrees are below `N / c (i + 1)`, which makes the elimination cost at most `N / k`.
* **Amplification** (`amplify`). `a (N (t + 1)) ≥ (t + 1) (a N - 2 N / k - s ^ 2)` with `s`
  depending only on `q` and `k`.
* **Limit** (`tendsto_of_amplify`). `a` is monotone (`extremalNumber_mono`), so the
  amplification inequality forces `liminf a n / n ≥ limsup a n / n`. The limit is at least
  `1 / 3` by the lower bound `n / 2 ≤ a n` of the reduction.
-/

namespace OMA.Helpers

open SimpleGraph Finset
open scoped Classical

/-- `h` is a witness for the pattern `(W, g)` in `H` relative to the hub set `X`: it embeds
`F[W]` outside the hubs, and the image of `w ∈ W` is adjacent to `g a` for every neighbour
`a ∉ W` of `w`. -/
def IsWit {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (H : SimpleGraph V) (X : Finset V)
    (W : Finset (Fin q)) (g h : Fin q → V) : Prop :=
  (∀ w ∈ W, h w ∉ X) ∧ (∀ w ∈ W, ∀ w' ∈ W, h w = h w' → w = w') ∧
    (∀ w ∈ W, ∀ w' ∈ W, F.Adj w w' → H.Adj (h w) (h w')) ∧
    (∀ w ∈ W, ∀ a, a ∉ W → F.Adj w a → H.Adj (h w) (g a))

theorem IsWit.mono {q : ℕ} {V : Type} {F : SimpleGraph (Fin q)} {H H' : SimpleGraph V}
    {X : Finset V} {W : Finset (Fin q)} {g h : Fin q → V} (hle : H' ≤ H)
    (hw : IsWit F H' X W g h) : IsWit F H X W g h :=
  ⟨hw.1, hw.2.1, fun w hw1 w' hw2 hadj => hle (hw.2.2.1 w hw1 w' hw2 hadj),
    fun w hw1 a ha hadj => hle (hw.2.2.2 w hw1 a ha hadj)⟩

/-- A pattern is robust if it has a witness avoiding any given set of at most `q` vertices. -/
def Robust {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (H : SimpleGraph V) (X : Finset V)
    (W : Finset (Fin q)) (g : Fin q → V) : Prop :=
  ∀ S : Finset V, S.card ≤ q → ∃ h, IsWit F H X W g h ∧ ∀ w ∈ W, h w ∉ S

/-- Every pattern with hub values in `X` that has a witness is robust. -/
def Clean {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (H : SimpleGraph V) (X : Finset V) : Prop :=
  ∀ (W : Finset (Fin q)) (g : Fin q → V), (∀ a, g a ∈ X) → (∃ h, IsWit F H X W g h) →
    Robust F H X W g

/-- The patterns with hub values in `X` that have a witness. -/
noncomputable def live {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (H : SimpleGraph V)
    (X : Finset V) : Finset (Finset (Fin q) × (Fin q → V)) :=
  ((univ : Finset (Fin q)).powerset ×ˢ Fintype.piFinset (fun _ : Fin q => X)).filter
    (fun p => ∃ h, IsWit F H X p.1 p.2 h)

theorem mem_live {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (H : SimpleGraph V)
    (X : Finset V) (W : Finset (Fin q)) (g : Fin q → V) :
    (W, g) ∈ live F H X ↔ (∀ a, g a ∈ X) ∧ ∃ h, IsWit F H X W g h := by
  simp [live, Fintype.mem_piFinset]

theorem card_live_le {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (H : SimpleGraph V)
    (X : Finset V) : (live F H X).card ≤ 2 ^ q * X.card ^ q := by
  refine (card_filter_le _ _).trans ?_
  rw [card_product, card_powerset, card_univ, Fintype.card_fin, Fintype.card_piFinset_const]

/-- Delete all edges of `H` at the vertices of `T`. -/
def delAt {V : Type} (H : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ∉ T ∧ b ∉ T
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem delAt_adj {V : Type} (H : SimpleGraph V) (T : Finset V) (a b : V) :
    (delAt H T).Adj a b ↔ H.Adj a b ∧ a ∉ T ∧ b ∉ T := Iff.rfl

theorem delAt_le {V : Type} (H : SimpleGraph V) (T : Finset V) : delAt H T ≤ H :=
  fun _ _ h => h.1

theorem degree_delAt_of_mem {V : Type} [Fintype V] (H : SimpleGraph V) (T : Finset V) (v : V)
    (hv : v ∈ T) : (delAt H T).degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  exact ((mem_neighborFinset _ _ _).mp hw).2.1 hv

theorem card_edgeFinset_le_delAt {V : Type} [Fintype V] (H : SimpleGraph V) (T : Finset V) :
    H.edgeFinset.card ≤ (delAt H T).edgeFinset.card + ∑ v ∈ T, H.degree v := by
  have hsub : H.edgeFinset ⊆
      (delAt H T).edgeFinset ∪ T.biUnion (fun s => H.incidenceFinset s) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      by_cases ha : a ∈ T
      · exact mem_union_right _ (mem_biUnion.2 ⟨a, ha,
          (mem_incidenceFinset _ _ _).2 ⟨he, Sym2.mem_mk_left _ _⟩⟩)
      · by_cases hb : b ∈ T
        · exact mem_union_right _ (mem_biUnion.2 ⟨b, hb,
            (mem_incidenceFinset _ _ _).2 ⟨he, Sym2.mem_mk_right _ _⟩⟩)
        · refine mem_union_left _ ?_
          rw [mem_edgeFinset, mem_edgeSet]
          exact ⟨he, ha, hb⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  refine card_biUnion_le.trans (Finset.sum_le_sum fun s _ => ?_)
  rw [card_incidenceFinset_eq_degree]


/-- Elimination: after deleting the edges at few low-degree vertices, every pattern is dead or
robust. -/
theorem exists_clean {q : ℕ} {V : Type} [Fintype V] (F : SimpleGraph (Fin q))
    (hF : ∀ v, ∃ w, F.Adj v w) (X : Finset V) (D : ℕ) :
    ∀ k : ℕ, ∀ H : SimpleGraph V, (live F H X).card ≤ k → (∀ v, v ∉ X → H.degree v ≤ D) →
      ∃ H' : SimpleGraph V, H' ≤ H ∧ Clean F H' X ∧
        H.edgeFinset.card ≤ H'.edgeFinset.card + k * (q * D) := by
  intro k
  induction k with
  | zero =>
    intro H hk _
    refine ⟨H, le_rfl, ?_, by simp⟩
    intro W g hg hw
    have hmem : (W, g) ∈ live F H X := (mem_live F H X W g).mpr ⟨hg, hw⟩
    have hempty : live F H X = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  | succ k ih =>
    intro H hk hdeg
    by_cases hc : Clean F H X
    · exact ⟨H, le_rfl, hc, Nat.le_add_right _ _⟩
    · unfold Clean at hc
      push Not at hc
      obtain ⟨W, g, hg, hw, hnr⟩ := hc
      unfold Robust at hnr
      push Not at hnr
      obtain ⟨S, hS, hhit⟩ := hnr
      let T : Finset V := S.filter (fun v => v ∉ X)
      have hTcard : T.card ≤ q := (card_filter_le _ _).trans hS
      have hdead : ¬ ∃ h, IsWit F (delAt H T) X W g h := by
        rintro ⟨h, hh⟩
        obtain ⟨w, hwW, hwS⟩ := hhit h (hh.mono (delAt_le H T))
        have hwT : h w ∈ T := mem_filter.mpr ⟨hwS, hh.1 w hwW⟩
        obtain ⟨a, ha⟩ := hF w
        by_cases haW : a ∈ W
        · exact (hh.2.2.1 w hwW a haW ha).2.1 hwT
        · exact (hh.2.2.2 w hwW a haW ha).2.1 hwT
      have hsub : live F (delAt H T) X ⊂ live F H X := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro p hp
          obtain ⟨W', g'⟩ := p
          rw [mem_live] at hp ⊢
          exact ⟨hp.1, hp.2.imp fun h hh => hh.mono (delAt_le H T)⟩
        · intro heq
          have hmem : (W, g) ∈ live F H X := (mem_live F H X W g).mpr ⟨hg, hw⟩
          rw [← heq, mem_live] at hmem
          exact hdead hmem.2
      have hcard : (live F (delAt H T) X).card ≤ k := by
        have := Finset.card_lt_card hsub
        omega
      obtain ⟨H', hle, hclean, hedges⟩ := ih (delAt H T) hcard
        (fun v hv => (degree_le_of_le (delAt_le H T)).trans (hdeg v hv))
      refine ⟨H', hle.trans (delAt_le H T), hclean, ?_⟩
      have h1 := card_edgeFinset_le_delAt H T
      have h2 : ∑ v ∈ T, H.degree v ≤ q * D := by
        calc ∑ v ∈ T, H.degree v ≤ ∑ _v ∈ T, D :=
              Finset.sum_le_sum fun v hv => hdeg v (mem_filter.mp hv).2
          _ = T.card * D := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ q * D := Nat.mul_le_mul_right D hTcard
      have h3 : (k + 1) * (q * D) = k * (q * D) + q * D := by ring
      omega


/-- The blow-up of `H` around the hub set `X`: `t + 1` layers; the hubs live in layer `0`, the
other vertices are copied into every layer; a non-hub vertex is joined to its hub neighbours
and to its non-hub neighbours of the same layer. -/
def blow {V : Type} (H : SimpleGraph V) (X : Finset V) (t : ℕ) : SimpleGraph (V × Fin (t + 1)) where
  Adj a b := H.Adj a.1 b.1 ∧ (a.1 ∈ X → a.2 = 0) ∧ (b.1 ∈ X → b.2 = 0) ∧
    (a.1 ∉ X → b.1 ∉ X → a.2 = b.2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, fun hb ha => (h.2.2.2 ha hb).symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem blow_adj {V : Type} (H : SimpleGraph V) (X : Finset V) (t : ℕ) (a b : V × Fin (t + 1)) :
    (blow H X t).Adj a b ↔ H.Adj a.1 b.1 ∧ (a.1 ∈ X → a.2 = 0) ∧ (b.1 ∈ X → b.2 = 0) ∧
      (a.1 ∉ X → b.1 ∉ X → a.2 = b.2) := Iff.rfl

/-- The pairs of distinct vertices of `F` whose images lie over the same vertex of `H`. -/
noncomputable def coll {q : ℕ} {V : Type} {t : ℕ} (f : Fin q → V × Fin (t + 1)) :
    Finset (Fin q × Fin q) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ (f p.1).1 = (f p.2).1)

theorem mem_coll {q : ℕ} {V : Type} {t : ℕ} (f : Fin q → V × Fin (t + 1)) (a b : Fin q) :
    (a, b) ∈ coll f ↔ a ≠ b ∧ (f a).1 = (f b).1 := by
  simp [coll]

/-- One re-embedding step: a copy of `F` in the blow-up with a collision can be replaced by a
copy with fewer collisions. -/
theorem blow_step {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (hF : ∀ v, ∃ w, F.Adj v w)
    (H : SimpleGraph V) (X : Finset V) (hX : X.Nonempty) (hclean : Clean F H X) (t : ℕ)
    (f : Fin q → V × Fin (t + 1)) (hinj : Function.Injective f)
    (hhom : ∀ a b, F.Adj a b → (blow H X t).Adj (f a) (f b)) (hne : (coll f).Nonempty) :
    ∃ f' : Fin q → V × Fin (t + 1), Function.Injective f' ∧
      (∀ a b, F.Adj a b → (blow H X t).Adj (f' a) (f' b)) ∧ (coll f').card < (coll f).card := by
  obtain ⟨⟨u, v⟩, huv⟩ := hne
  rw [mem_coll] at huv
  obtain ⟨hne, hfst⟩ := huv
  obtain ⟨x0, hx0⟩ := hX
  -- image vertices over hubs are in layer 0
  have hlayer : ∀ a, (f a).1 ∈ X → (f a).2 = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := hF a
    exact (hhom a b hb).2.1 ha
  have huX : (f u).1 ∉ X := by
    intro hu
    have hv : (f v).1 ∈ X := hfst ▸ hu
    exact hne (hinj (Prod.ext hfst ((hlayer u hu).trans (hlayer v hv).symm)))
  let i : Fin (t + 1) := (f u).2
  let W : Finset (Fin q) := univ.filter (fun w => (f w).1 ∉ X ∧ (f w).2 = i)
  have hW : ∀ w, w ∈ W ↔ (f w).1 ∉ X ∧ (f w).2 = i := fun w => by simp [W]
  have huW : u ∈ W := (hW u).mpr ⟨huX, rfl⟩
  let g : Fin q → V := fun a => if (f a).1 ∈ X then (f a).1 else x0
  have hg : ∀ a, g a ∈ X := by
    intro a
    by_cases ha : (f a).1 ∈ X
    · simp only [g, if_pos ha]; exact ha
    · simp only [g, if_neg ha]; exact hx0
  -- a neighbour outside `W` of a vertex of `W` lies over a hub
  have hout : ∀ w ∈ W, ∀ a, a ∉ W → F.Adj w a → (f a).1 ∈ X := by
    intro w hw a ha hadj
    by_contra haX
    have h1 := (hhom w a hadj).2.2.2 ((hW w).mp hw).1 haX
    exact ha ((hW a).mpr ⟨haX, h1.symm.trans ((hW w).mp hw).2⟩)
  have hwit : IsWit F H X W g (fun a => (f a).1) := by
    refine ⟨fun w hw => ((hW w).mp hw).1, ?_, ?_, ?_⟩
    · intro w hw w' hw' heq
      exact hinj (Prod.ext heq (((hW w).mp hw).2.trans ((hW w').mp hw').2.symm))
    · intro w _ w' _ hadj
      exact (hhom w w' hadj).1
    · intro w hw a ha hadj
      have haX := hout w hw a ha hadj
      simp only [g, if_pos haX]
      exact (hhom w a hadj).1
  let S : Finset V := (univ.filter (fun a => a ∉ W)).image (fun a => (f a).1)
  have hS : S.card ≤ q := by
    refine card_image_le.trans ((card_filter_le _ _).trans ?_)
    rw [card_univ, Fintype.card_fin]
  obtain ⟨h, hh, havoid⟩ := hclean W g hg ⟨_, hwit⟩ S hS
  have hmemS : ∀ a, a ∉ W → (f a).1 ∈ S := fun a ha =>
    mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩, rfl⟩
  let f' : Fin q → V × Fin (t + 1) := fun a => if a ∈ W then (h a, i) else f a
  have hf'in : ∀ a, a ∈ W → f' a = (h a, i) := fun a ha => by simp only [f', if_pos ha]
  have hf'out : ∀ a, a ∉ W → f' a = f a := fun a ha => by simp only [f', if_neg ha]
  -- no collision of `f'` involves a vertex of `W`
  have hnocoll : ∀ a b, a ∈ W → a ≠ b → (f' a).1 ≠ (f' b).1 := by
    intro a b ha hab heq
    rw [hf'in a ha] at heq
    by_cases hb : b ∈ W
    · rw [hf'in b hb] at heq
      exact hab (hh.2.1 a ha b hb heq)
    · rw [hf'out b hb] at heq
      have heq' : h a = (f b).1 := heq
      exact havoid a ha (heq' ▸ hmemS b hb)
  have hmixed : ∀ a b, a ∈ W → b ∉ W → F.Adj a b → (blow H X t).Adj (f' a) (f' b) := by
    intro a b ha hb hadj
    have hbX := hout a ha b hb hadj
    rw [hf'in a ha, hf'out b hb]
    have h1 := hh.2.2.2 a ha b hb hadj
    simp only [g, if_pos hbX] at h1
    exact ⟨h1, fun hc => absurd hc (hh.1 a ha), fun _ => hlayer b hbX,
      fun _ hc => absurd hbX hc⟩
  refine ⟨f', ?_, ?_, ?_⟩
  · intro a b heq
    by_contra hab
    by_cases ha : a ∈ W
    · exact hnocoll a b ha hab (congrArg Prod.fst heq)
    · by_cases hb : b ∈ W
      · exact hnocoll b a hb (Ne.symm hab) (congrArg Prod.fst heq).symm
      · rw [hf'out a ha, hf'out b hb] at heq
        exact hab (hinj heq)
  · intro a b hadj
    by_cases ha : a ∈ W
    · by_cases hb : b ∈ W
      · rw [hf'in a ha, hf'in b hb]
        exact ⟨hh.2.2.1 a ha b hb hadj, fun hc => absurd hc (hh.1 a ha),
          fun hc => absurd hc (hh.1 b hb), fun _ _ => rfl⟩
      · exact hmixed a b ha hb hadj
    · by_cases hb : b ∈ W
      · exact (hmixed b a hb ha hadj.symm).symm
      · rw [hf'out a ha, hf'out b hb]
        exact hhom a b hadj
  · apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨a, b⟩ := p
      rw [mem_coll] at hp ⊢
      have ha : a ∉ W := fun ha => hnocoll a b ha hp.1 hp.2
      have hb : b ∉ W := fun hb => hnocoll b a hb hp.1.symm hp.2.symm
      rw [hf'out a ha, hf'out b hb] at hp
      exact hp
    · intro heq
      have hmem : (u, v) ∈ coll f' := by
        rw [heq, mem_coll]
        exact ⟨hne, hfst⟩
      rw [mem_coll] at hmem
      exact hnocoll u v huW hmem.1 hmem.2

/-- The blow-up of a clean `F`-free graph is `F`-free. -/
theorem blow_free {q : ℕ} {V : Type} (F : SimpleGraph (Fin q)) (hF : ∀ v, ∃ w, F.Adj v w)
    (H : SimpleGraph V) (X : Finset V) (hX : X.Nonempty) (hclean : Clean F H X)
    (hfree : F.Free H) (t : ℕ) : F.Free (blow H X t) := by
  have key : ∀ c : ℕ, ∀ f : Fin q → V × Fin (t + 1), Function.Injective f →
      (∀ a b, F.Adj a b → (blow H X t).Adj (f a) (f b)) → (coll f).card ≤ c → F ⊑ H := by
    intro c
    induction c with
    | zero =>
      intro f hinj hhom hc
      have hempty : coll f = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
      refine ⟨⟨⟨fun a => (f a).1, fun {a b} hadj => (hhom a b hadj).1⟩, ?_⟩⟩
      intro a b heq
      by_contra hab
      have hmem : (a, b) ∈ coll f := (mem_coll f a b).mpr ⟨hab, heq⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    | succ c ih =>
      intro f hinj hhom hc
      by_cases hne : (coll f).Nonempty
      · obtain ⟨f', hinj', hhom', hlt⟩ := blow_step F hF H X hX hclean t f hinj hhom hne
        exact ih f' hinj' hhom' (by omega)
      · exact ih f hinj hhom (by
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne]; simp)
  rintro ⟨c⟩
  exact hfree (key _ c c.injective (fun a b hadj => c.toHom.map_adj hadj) le_rfl)


/-- Lift a vertex into layer `i`; hubs go to layer `0`. -/
noncomputable def lift {V : Type} (X : Finset V) (t : ℕ) (i : Fin (t + 1)) (v : V) :
    V × Fin (t + 1) :=
  (v, if v ∈ X then 0 else i)

theorem lift_fst {V : Type} (X : Finset V) (t : ℕ) (i : Fin (t + 1)) (v : V) :
    (lift X t i v).1 = v := rfl

theorem lift_adj {V : Type} (H : SimpleGraph V) (X : Finset V) (t : ℕ) (i : Fin (t + 1))
    (a b : V) (hab : H.Adj a b) : (blow H X t).Adj (lift X t i a) (lift X t i b) := by
  refine ⟨hab, fun ha => ?_, fun hb => ?_, fun ha hb => ?_⟩
  · have ha' : a ∈ X := ha
    simp only [lift, if_pos ha']
  · have hb' : b ∈ X := hb
    simp only [lift, if_pos hb']
  · have ha' : a ∉ X := ha
    have hb' : b ∉ X := hb
    simp only [lift, if_neg ha', if_neg hb']

theorem choose_succ_two_le (s : ℕ) : (s + 1).choose 2 ≤ s * s := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · apply Nat.div_le_of_le_mul
    nlinarith

/-- Every edge with an endpoint outside the hubs is copied into each layer. -/
theorem card_edgeFinset_blow {V : Type} [Fintype V] (H : SimpleGraph V) (X : Finset V) (t : ℕ) :
    (t + 1) * H.edgeFinset.card ≤
      (blow H X t).edgeFinset.card + (t + 1) * (X.card * X.card) := by
  let E0 : Finset (Sym2 V) := H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∉ X)
  have h1 : H.edgeFinset.card ≤ E0.card + X.card * X.card := by
    have hsub : H.edgeFinset ⊆ E0 ∪ X.sym2 := by
      intro e he
      by_cases h : ∃ v ∈ e, v ∉ X
      · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
      · push Not at h
        exact mem_union_right _ (Finset.mem_sym2_iff.mpr h)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
    rw [Finset.card_sym2]
    exact choose_succ_two_le _
  have h2 : E0.card * (t + 1) ≤ (blow H X t).edgeFinset.card := by
    have hcard : (E0 ×ˢ (univ : Finset (Fin (t + 1)))).card = E0.card * (t + 1) := by
      rw [card_product, card_univ, Fintype.card_fin]
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun p => Sym2.map (lift X t p.2) p.1)
    · rintro ⟨e, i⟩ hp
      have he : e ∈ H.edgeFinset := (mem_filter.mp (mem_product.mp hp).1).1
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        simp only [Sym2.map_mk, coe_edgeFinset, mem_edgeSet]
        exact lift_adj H X t i a b he
    · rintro ⟨e, i⟩ hp ⟨e', j⟩ hp' heq
      have heq' : Sym2.map (lift X t i) e = Sym2.map (lift X t j) e' := heq
      have hfst : ∀ (k : Fin (t + 1)) (z : Sym2 V),
          Sym2.map Prod.fst (Sym2.map (lift X t k) z) = z := by
        intro k z
        rw [Sym2.map_map]
        exact congrFun Sym2.map_id' z
      have hee : e = e' := by
        have := congrArg (Sym2.map Prod.fst) heq'
        rwa [hfst, hfst] at this
      subst hee
      obtain ⟨v, hve, hvX⟩ := (mem_filter.mp (mem_product.mp (mem_coe.mp hp)).1).2
      have hmem : lift X t i v ∈ Sym2.map (lift X t j) e := by
        rw [← heq']
        exact Sym2.mem_map.mpr ⟨v, hve, rfl⟩
      obtain ⟨v', _, hv'⟩ := Sym2.mem_map.mp hmem
      have hvv : v' = v := congrArg Prod.fst hv'
      subst hvv
      have hsnd := congrArg Prod.snd hv'
      simp only [lift, if_neg hvX] at hsnd
      rw [hsnd]
  calc (t + 1) * H.edgeFinset.card ≤ (t + 1) * (E0.card + X.card * X.card) :=
        Nat.mul_le_mul_left _ h1
    _ = E0.card * (t + 1) + (t + 1) * (X.card * X.card) := by ring
    _ ≤ (blow H X t).edgeFinset.card + (t + 1) * (X.card * X.card) :=
        Nat.add_le_add_right h2 _


/-- The threshold constants of the degree cascade. -/
def cseq (q k : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => k * q * 2 ^ q * (2 * q * cseq q k i + 1) ^ q

theorem cseq_succ (q k i : ℕ) :
    cseq q k (i + 1) = k * q * 2 ^ q * (2 * q * cseq q k i + 1) ^ q := rfl

theorem cseq_pos (q k : ℕ) (hq : 0 < q) (hk : 0 < k) (i : ℕ) : 0 < cseq q k i := by
  cases i with
  | zero => exact Nat.one_pos
  | succ i =>
    rw [cseq_succ]
    positivity

theorem cseq_mono (q k : ℕ) (hq : 0 < q) (hk : 0 < k) : Monotone (cseq q k) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [cseq_succ]
  have h1 : cseq q k i ≤ 2 * q * cseq q k i + 1 := by nlinarith
  have h2 : 2 * q * cseq q k i + 1 ≤ (2 * q * cseq q k i + 1) ^ q :=
    Nat.le_self_pow hq.ne' _
  have h3 : 1 ≤ k * q * 2 ^ q := Nat.succ_le_of_lt (by positivity)
  calc cseq q k i ≤ (2 * q * cseq q k i + 1) ^ q := h1.trans h2
    _ = 1 * (2 * q * cseq q k i + 1) ^ q := (one_mul _).symm
    _ ≤ k * q * 2 ^ q * (2 * q * cseq q k i + 1) ^ q := Nat.mul_le_mul_right _ h3

/-- Pigeonhole over the degree classes: one of the first `2 q k` classes carries a degree sum
of at most `N / k`. -/
theorem exists_gap {V : Type} [Fintype V] (H : SimpleGraph V) (q k N : ℕ) (hq : 0 < q)
    (hk : 0 < k) (c : ℕ → ℕ) (hc : Monotone c) (he : H.edgeFinset.card ≤ q * N) :
    ∃ i, i < 2 * q * k ∧
      k * (∑ v ∈ univ.filter (fun v => c i * H.degree v < N ∧ N ≤ c (i + 1) * H.degree v),
        H.degree v) ≤ N := by
  by_contra hcon
  push Not at hcon
  let M : ℕ → Finset V := fun i =>
    univ.filter (fun v => c i * H.degree v < N ∧ N ≤ c (i + 1) * H.degree v)
  have hdisj : (↑(range (2 * q * k)) : Set ℕ).PairwiseDisjoint M := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro v hvi hvj
    simp only [M, mem_filter, mem_univ, true_and] at hvi hvj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have h1 : c (i + 1) * H.degree v ≤ c j * H.degree v :=
        Nat.mul_le_mul_right (H.degree v) (hc (Nat.succ_le_of_lt h))
      omega
    · have h1 : c (j + 1) * H.degree v ≤ c i * H.degree v :=
        Nat.mul_le_mul_right (H.degree v) (hc (Nat.succ_le_of_lt h))
      omega
  have hsum : ∑ i ∈ range (2 * q * k), ∑ v ∈ M i, H.degree v ≤ 2 * (q * N) := by
    rw [← Finset.sum_biUnion hdisj]
    calc ∑ v ∈ (range (2 * q * k)).biUnion M, H.degree v ≤ ∑ v, H.degree v :=
          Finset.sum_le_sum_of_subset (subset_univ _)
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
      _ ≤ 2 * (q * N) := Nat.mul_le_mul_left 2 he
  have hlow : ∑ _i ∈ range (2 * q * k), (N + 1) ≤
      ∑ i ∈ range (2 * q * k), k * ∑ v ∈ M i, H.degree v :=
    Finset.sum_le_sum fun i hi => hcon i (mem_range.mp hi)
  rw [← Finset.mul_sum, Finset.sum_const, card_range, smul_eq_mul] at hlow
  have h1 := Nat.mul_le_mul_left k hsum
  have hpos : 0 < 2 * q * k := by positivity
  nlinarith

/-- Structure step: an `F`-sparse graph has a clean subgraph, relative to a bounded hub set,
with almost as many edges. -/
theorem exists_clean_sub {q : ℕ} {V : Type} [Fintype V] [Nonempty V] (F : SimpleGraph (Fin q))
    (hF : ∀ v, ∃ w, F.Adj v w) (hq : 0 < q) (k : ℕ) (hk : 0 < k) (H : SimpleGraph V) (N : ℕ)
    (hN : 0 < N) (he : H.edgeFinset.card ≤ q * N) :
    ∃ (H' : SimpleGraph V) (X : Finset V), H' ≤ H ∧ X.Nonempty ∧ Clean F H' X ∧
      X.card ≤ 2 * q * cseq q k (2 * q * k) + 1 ∧
      k * H.edgeFinset.card ≤ k * H'.edgeFinset.card + 2 * N := by
  obtain ⟨i, hi, hgap⟩ := exists_gap H q k N hq hk (cseq q k) (cseq_mono q k hq hk) he
  obtain ⟨v0⟩ := ‹Nonempty V›
  set c := cseq q k i with hcdef
  set c' := cseq q k (i + 1) with hc'def
  set M : Finset V := univ.filter (fun v => c * H.degree v < N ∧ N ≤ c' * H.degree v) with hM
  let X0 : Finset V := univ.filter (fun v => N ≤ c * H.degree v)
  let X : Finset V := insert v0 X0
  have hc'pos : 0 < c' := cseq_pos q k hq hk (i + 1)
  have hX0card : X0.card ≤ 2 * q * c := by
    have h1 : N * X0.card ≤ ∑ v ∈ X0, c * H.degree v := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun v hv => (mem_filter.mp hv).2
    have h2 : ∑ v ∈ X0, c * H.degree v ≤ c * (2 * (q * N)) := by
      rw [← Finset.mul_sum]
      refine Nat.mul_le_mul_left c ?_
      calc ∑ v ∈ X0, H.degree v ≤ ∑ v, H.degree v :=
            Finset.sum_le_sum_of_subset (subset_univ _)
        _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
        _ ≤ 2 * (q * N) := Nat.mul_le_mul_left 2 he
    have h3 : N * X0.card ≤ N * (2 * q * c) := by
      calc N * X0.card ≤ c * (2 * (q * N)) := h1.trans h2
        _ = N * (2 * q * c) := by ring
    exact Nat.le_of_mul_le_mul_left h3 hN
  have hXcard : X.card ≤ 2 * q * c + 1 := (card_insert_le _ _).trans (by omega)
  have hcle : c ≤ cseq q k (2 * q * k) := cseq_mono q k hq hk hi.le
  let D : ℕ := (N - 1) / c'
  have hdeg1 : ∀ v, v ∉ X → (delAt H M).degree v ≤ D := by
    intro v hv
    by_cases hvM : v ∈ M
    · rw [degree_delAt_of_mem H M v hvM]
      exact Nat.zero_le _
    · have hvX0 : v ∉ X0 := fun h => hv (mem_insert_of_mem h)
      have h1 : ¬ N ≤ c * H.degree v := fun h => hvX0 (mem_filter.mpr ⟨mem_univ _, h⟩)
      have h2 : ¬ (c * H.degree v < N ∧ N ≤ c' * H.degree v) := fun h =>
        hvM (mem_filter.mpr ⟨mem_univ _, h⟩)
      have h3 : c' * H.degree v < N := by
        by_contra h4
        exact h2 ⟨not_le.mp h1, not_lt.mp h4⟩
      have h5 : H.degree v ≤ D := by
        rw [Nat.le_div_iff_mul_le hc'pos]
        rw [mul_comm]
        omega
      exact (degree_le_of_le (delAt_le H M)).trans h5
  obtain ⟨H', hle, hclean, hedges⟩ :=
    exists_clean F hF X D (live F (delAt H M) X).card (delAt H M) le_rfl hdeg1
  refine ⟨H', X, hle.trans (delAt_le H M), ⟨v0, mem_insert_self _ _⟩, hclean,
    hXcard.trans (by nlinarith), ?_⟩
  have hlive := card_live_le F (delAt H M) X
  have hcost : k * ((live F (delAt H M) X).card * (q * D)) ≤ N := by
    have h1 : X.card ^ q ≤ (2 * q * c + 1) ^ q := Nat.pow_le_pow_left hXcard q
    have h2 : (live F (delAt H M) X).card ≤ 2 ^ q * (2 * q * c + 1) ^ q :=
      hlive.trans (Nat.mul_le_mul_left _ h1)
    have h3 : c' * D ≤ N - 1 := Nat.mul_div_le _ _
    have h4 : k * ((live F (delAt H M) X).card * (q * D)) ≤
        k * ((2 ^ q * (2 * q * c + 1) ^ q) * (q * D)) :=
      Nat.mul_le_mul_left k (Nat.mul_le_mul_right _ h2)
    have h5 : k * ((2 ^ q * (2 * q * c + 1) ^ q) * (q * D)) = c' * D := by
      rw [hc'def, cseq_succ]
      ring
    omega
  have hdel := card_edgeFinset_le_delAt H M
  have h6 : k * H.edgeFinset.card ≤
      k * (delAt H M).edgeFinset.card + k * ∑ v ∈ M, H.degree v := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left k hdel
  have h7 : k * (delAt H M).edgeFinset.card ≤
      k * H'.edgeFinset.card + k * ((live F (delAt H M) X).card * (q * D)) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left k hedges
  omega


/-- An extremal graph, with the classical decidability instance. -/
theorem exists_extremal {q : ℕ} (F : SimpleGraph (Fin q)) (hne : F ≠ ⊥) (N : ℕ) :
    ∃ G : SimpleGraph (Fin N), F.Free G ∧ G.edgeFinset.card = extremalNumber N F := by
  obtain ⟨G, inst, hG⟩ := exists_isExtremal_free (V := Fin N) hne
  have h := isExtremal_free_iff.mp hG
  rw [Fintype.card_fin] at h
  refine ⟨G, h.1, ?_⟩
  convert h.2

/-- Amplification: `ex(N (t + 1), F) ≥ (t + 1) (ex(N, F) - 2 N / k - s ^ 2)` with `s` depending
only on `q` and `k`. -/
theorem amplify {q : ℕ} (F : SimpleGraph (Fin q)) (hF : ∀ v, ∃ w, F.Adj v w) (hq : 0 < q)
    (hlin : ∀ n, extremalNumber n F ≤ q * n) (k : ℕ) (hk : 0 < k) (N t : ℕ) (hN : 0 < N) :
    k * ((t + 1) * extremalNumber N F) ≤ k * extremalNumber (N * (t + 1)) F +
      (t + 1) * (k * (2 * q * cseq q k (2 * q * k) + 1) ^ 2 + 2 * N) := by
  have hne : F ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw⟩ := hF ⟨0, hq⟩
    rw [hbot] at hw
    exact hw
  obtain ⟨G, hfree, hcard⟩ := exists_extremal F hne N
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨H', X, hle, hX, hclean, hXcard, hedges⟩ :=
    exists_clean_sub F hF hq k hk G N hN (hcard ▸ hlin N)
  have hfree' : F.Free H' := fun hc => hfree (hc.trans (IsContained.of_le hle))
  have hbfree := blow_free F hF H' X hX hclean hfree' t
  have hb := card_edgeFinset_le_extremalNumber hbfree
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hb
  have hcount := card_edgeFinset_blow H' X t
  have hsq : X.card * X.card ≤ (2 * q * cseq q k (2 * q * k) + 1) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul hXcard hXcard
  rw [← hcard]
  set s := (2 * q * cseq q k (2 * q * k) + 1) ^ 2
  set eG := G.edgeFinset.card
  set eH := H'.edgeFinset.card
  set eB := (blow H' X t).edgeFinset.card
  set aB := extremalNumber (N * (t + 1)) F
  have h1 : k * ((t + 1) * eG) ≤ (t + 1) * (k * eH + 2 * N) := by
    calc k * ((t + 1) * eG) = (t + 1) * (k * eG) := by ring
      _ ≤ (t + 1) * (k * eH + 2 * N) := Nat.mul_le_mul_left _ hedges
  have h2 : k * ((t + 1) * eH) ≤ k * (aB + (t + 1) * s) := by
    refine Nat.mul_le_mul_left k (hcount.trans ?_)
    exact Nat.add_le_add hb (Nat.mul_le_mul_left _ hsq)
  calc k * ((t + 1) * eG) ≤ (t + 1) * (k * eH + 2 * N) := h1
    _ = k * ((t + 1) * eH) + (t + 1) * (2 * N) := by ring
    _ ≤ k * (aB + (t + 1) * s) + (t + 1) * (2 * N) := Nat.add_le_add_right h2 _
    _ = k * aB + (t + 1) * (k * s + 2 * N) := by ring

/-- Adding isolated vertices: the extremal number is monotone in the number of vertices. -/
theorem extremalNumber_mono {q : ℕ} (F : SimpleGraph (Fin q)) (hF : ∀ v, ∃ w, F.Adj v w)
    (hq : 0 < q) {m n : ℕ} (h : m ≤ n) : extremalNumber m F ≤ extremalNumber n F := by
  have hne : F ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw⟩ := hF ⟨0, hq⟩
    rw [hbot] at hw
    exact hw
  obtain ⟨G, hfree, hcard⟩ := exists_extremal F hne m
  rw [← hcard]
  let e : Fin m ↪ Fin n := Fin.castLEEmb h
  have hfree' : F.Free (G.map e) := by
    rintro ⟨c⟩
    have hrange : ∀ a, ∃ u, e u = c a := by
      intro a
      obtain ⟨b, hb⟩ := hF a
      have hadj := c.toHom.map_adj hb
      rw [SimpleGraph.map_adj] at hadj
      obtain ⟨u, v, _, hu, _⟩ := hadj
      exact ⟨u, hu⟩
    choose g hg using hrange
    apply hfree
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro a b hab
      have hadj := c.toHom.map_adj hab
      rw [SimpleGraph.map_adj] at hadj
      obtain ⟨u, v, huv, hu, hv⟩ := hadj
      have hu' : u = g a := e.injective (hu.trans (hg a).symm)
      have hv' : v = g b := e.injective (hv.trans (hg b).symm)
      rw [← hu', ← hv']
      exact huv
    · intro a b hab
      have hab' : g a = g b := hab
      have hc : c a = c b := by rw [← hg a, ← hg b, hab']
      exact c.injective hc
  have hb := card_edgeFinset_le_extremalNumber hfree'
  rw [Fintype.card_fin] at hb
  have hmap : (G.map e).edgeFinset.card = G.edgeFinset.card := by
    convert card_edgeFinset_map e G
  rw [← hmap]
  exact hb


/-- Analytic part: a monotone sequence with linear growth satisfying the amplification
inequality has a limiting density. -/
theorem tendsto_of_amplify (a : ℕ → ℕ) (q : ℕ) (hmono : Monotone a) (hup : ∀ n, a n ≤ q * n)
    (hamp : ∀ k : ℕ, 0 < k → ∃ s : ℕ, ∀ N t : ℕ, 0 < N →
      k * ((t + 1) * a N) ≤ k * a (N * (t + 1)) + (t + 1) * (k * s + 2 * N)) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop (nhds L) := by
  let u : ℕ → ℝ := fun n => (a n : ℝ) / n
  have hu0 : ∀ n, 0 ≤ u n := fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have huq : ∀ n, u n ≤ q := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [u]
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      change (a n : ℝ) / n ≤ q
      rw [div_le_iff₀ hn']
      exact_mod_cast hup n
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := Filter.isBoundedUnder_of ⟨q, huq⟩
  have hbdd' : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u := Filter.isBoundedUnder_of ⟨0, hu0⟩
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u := hbdd'.isCoboundedUnder_le
  have hLq : Filter.limsup u Filter.atTop ≤ q :=
    Filter.limsup_le_of_le hcobdd (Filter.Eventually.of_forall huq)
  refine ⟨Filter.limsup u Filter.atTop, tendsto_order.2
    ⟨fun b hb => ?_, fun b hb => Filter.eventually_lt_of_limsup_lt hb hbdd⟩⟩
  set L := Filter.limsup u Filter.atTop with hLdef
  have hεpos : 0 < (L - b) / 4 := by linarith
  set ε := (L - b) / 4 with hε
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hkpos' : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hkpos : 0 < k := Nat.cast_pos.mp hkpos'
  have hkε : 2 < ε * k := by
    rw [div_lt_iff₀ hεpos] at hk
    linarith
  obtain ⟨s, hs⟩ := hamp k hkpos
  have hfreq : ∃ᶠ N in Filter.atTop, L - ε < u N :=
    Filter.frequently_lt_of_lt_limsup hcobdd (by linarith)
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((s : ℝ) / ε)
  obtain ⟨N, hNu, hNge⟩ := (hfreq.and_eventually (Filter.eventually_ge_atTop (N0 + 1))).exists
  have hNpos : 0 < N := by omega
  have hNpos' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hsN : (s : ℝ) ≤ ε * N := by
    rw [div_lt_iff₀ hεpos] at hN0
    have h1 : (N0 : ℝ) ≤ N := by exact_mod_cast (by omega : N0 ≤ N)
    nlinarith
  have haN : (L - ε) * N ≤ a N := by
    have h : L - ε < (a N : ℝ) / N := hNu
    rw [lt_div_iff₀ hNpos'] at h
    exact h.le
  have key : ∀ t : ℕ, ((t : ℝ) + 1) * N * (L - 3 * ε) ≤ a (N * (t + 1)) := by
    intro t
    have h := hs N t hNpos
    have h' : (k : ℝ) * (((t : ℝ) + 1) * a N) ≤
        k * a (N * (t + 1)) + ((t : ℝ) + 1) * (k * s + 2 * N) := by exact_mod_cast h
    have hT : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have e1 : (k : ℝ) * ((t : ℝ) + 1) * ((L - ε) * N) ≤ k * ((t : ℝ) + 1) * a N :=
      mul_le_mul_of_nonneg_left haN (by positivity)
    have e2 : (k : ℝ) * ((t : ℝ) + 1) * s ≤ k * ((t : ℝ) + 1) * (ε * N) :=
      mul_le_mul_of_nonneg_left hsN (by positivity)
    have e3 : ((t : ℝ) + 1) * N * 2 ≤ ((t : ℝ) + 1) * N * (ε * k) :=
      mul_le_mul_of_nonneg_left hkε.le (by positivity)
    have e4 : (k : ℝ) * (((t : ℝ) + 1) * N * (L - 3 * ε)) ≤ k * a (N * (t + 1)) := by
      linarith
    exact le_of_mul_le_mul_left e4 hkpos'
  obtain ⟨N1, hN1⟩ := exists_nat_gt ((N : ℝ) * q / ε)
  filter_upwards [Filter.eventually_ge_atTop (max N N1)] with n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le hNpos hnN
  have hnpos' : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.div_pos hnN hNpos).ne'
  have h1 : N * (t + 1) ≤ n := by
    rw [← ht]
    exact Nat.mul_div_le n N
  have h2 : n < N * (t + 1) + N := by
    have h3 := Nat.lt_mul_div_succ n hNpos
    rw [ht] at h3
    calc n < N * (t + 1 + 1) := h3
      _ = N * (t + 1) + N := by ring
  have ha : (a (N * (t + 1)) : ℝ) ≤ a n := by exact_mod_cast hmono h1
  have hkey := key t
  change b < (a n : ℝ) / n
  rw [lt_div_iff₀ hnpos']
  have hb4 : b = L - 4 * ε := by
    rw [hε]
    ring
  by_cases hneg : L - 3 * ε ≤ 0
  · have h3 : b * n < 0 := mul_neg_of_neg_of_pos (by linarith) hnpos'
    have h4 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
    linarith
  · push Not at hneg
    have h3 : (n : ℝ) - N ≤ ((t : ℝ) + 1) * N := by
      have h2' : (n : ℝ) < N * ((t : ℝ) + 1) + N := by exact_mod_cast h2
      linarith
    have h4 : ((n : ℝ) - N) * (L - 3 * ε) ≤ ((t : ℝ) + 1) * N * (L - 3 * ε) :=
      mul_le_mul_of_nonneg_right h3 hneg.le
    have h5 : (N : ℝ) * q < n * ε := by
      have h6 : (N : ℝ) * q / ε < n := lt_of_lt_of_le hN1 (by exact_mod_cast hnN1)
      rwa [div_lt_iff₀ hεpos] at h6
    have h6 : (N : ℝ) * (L - 3 * ε) ≤ N * q :=
      mul_le_mul_of_nonneg_left (by linarith) hNpos'.le
    rw [hb4]
    linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R3.H2 := by
  intro q G _ edges noiso _ _ hlin
  have hF : ∀ v, ∃ w, G.Adj v w := fun v => by
    have h := noiso v
    unfold SimpleGraph.IsIsolated at h
    push Not at h
    exact h
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · obtain ⟨e, _⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two edges)
      induction e using Sym2.ind with
      | h a b => exact a.elim0
    · exact hq
  obtain ⟨L, hL⟩ := OMA.Helpers.tendsto_of_amplify (fun n => SimpleGraph.extremalNumber n G) q
    (fun m n h => OMA.Helpers.extremalNumber_mono G hF hq h) hlin
    (fun k hk => ⟨(2 * q * OMA.Helpers.cseq q k (2 * q * k) + 1) ^ 2,
      fun N t hN => OMA.Helpers.amplify G hF hq hlin k hk N t hN⟩)
  refine ⟨L, ?_, hL⟩
  have hle : (1 / 3 : ℝ) ≤ L := ge_of_tendsto hL (by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [le_div_iff₀ hnpos]
    have hlow := OMA.R_Erdos713_erdos_713_parts_i_R3.extremal_linear_lower G edges
      (by omega : 0 < n)
    have hnat : n ≤ 3 * SimpleGraph.extremalNumber n G := by omega
    have hreal : (n : ℝ) ≤ 3 * (SimpleGraph.extremalNumber n G : ℝ) := by exact_mod_cast hnat
    linarith)
  linarith
