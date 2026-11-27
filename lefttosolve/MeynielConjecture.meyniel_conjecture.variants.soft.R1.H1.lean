import OMAReductions.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1

-- Step H1 of reduction MeynielConjecture.meyniel_conjecture.variants.soft.R1: guarding a closed neighbourhood.
-- One cop sits on v and catches the robber as soon as it enters N(v). The robber, starting
-- outside N[v], is then confined to its connected piece K of G - N[v]; the other k cops walk
-- along walks of G to the start positions of a winning k-cop strategy on G.induce K (with a
-- uniform round bound, by finiteness of K) and replay it, lifted to G.
namespace OMA.Helpers

open MeynielConjecture

variable {V : Type}

theorem ccw_succ (G : SimpleGraph V) (k : ℕ) :
    ∀ (m : ℕ) (c : Fin k → V) (r : V), CopsCatchWithin G k m c r →
      CopsCatchWithin G k (m + 1) c r := by
  intro m
  induction m with
  | zero => intro c r h; exact Or.inl h
  | succ m ih =>
    rintro c r (h | ⟨c', hs, h | hall⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c', hs, Or.inl h⟩
    · exact Or.inr ⟨c', hs, Or.inr fun r' hr' => ih c' r' (hall r' hr')⟩

theorem ccw_mono (G : SimpleGraph V) (k : ℕ) {m m' : ℕ} (hm : m ≤ m') (c : Fin k → V) (r : V)
    (h : CopsCatchWithin G k m c r) : CopsCatchWithin G k m' c r := by
  induction m', hm using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ccw_succ G k n c r ih

theorem ccw_guard (G : SimpleGraph V) (k : ℕ) (v : V) (m : ℕ) (c : Fin k → V) (r : V)
    (hr : G.Adj v r) :
    CopsCatchWithin G (k + 1) (m + 1) (Fin.cons v c : Fin (k + 1) → V) r := by
  refine Or.inr ⟨(Fin.cons r c : Fin (k + 1) → V), fun i => ?_, Or.inl ⟨0, by simp⟩⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact Or.inr hr
  · simp only [Fin.cons_succ]; exact Or.inl rfl

theorem ccw_lift (G : SimpleGraph V) (k : ℕ) (v : V) (K : Set V)
    (hcl : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K ∨ G.Adj v y) :
    ∀ (m : ℕ) (c : Fin k → K) (r : K), CopsCatchWithin (G.induce K) k m c r →
      CopsCatchWithin G (k + 1) (m + 1)
        (Fin.cons v (fun i => (c i : V)) : Fin (k + 1) → V) (r : V) := by
  intro m
  induction m with
  | zero =>
    rintro c r ⟨i, hi⟩
    exact Or.inl ⟨i.succ, by simp [hi]⟩
  | succ m ih =>
    rintro c r (⟨i, hi⟩ | ⟨c', hs, h⟩)
    · exact Or.inl ⟨i.succ, by simp [hi]⟩
    · have hs' : ∀ i, Step G ((Fin.cons v (fun i => (c i : V)) : Fin (k + 1) → V) i)
          ((Fin.cons v (fun i => (c' i : V)) : Fin (k + 1) → V) i) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]; exact Or.inl rfl
        · simp only [Fin.cons_succ]
          rcases hs j with h | h
          · exact Or.inl (congrArg Subtype.val h)
          · exact Or.inr h
      rcases h with ⟨i, hi⟩ | hall
      · exact Or.inr ⟨_, hs', Or.inl ⟨i.succ, by simp [hi]⟩⟩
      · refine Or.inr ⟨_, hs', Or.inr fun r' hr' => ?_⟩
        rcases hr' with hr' | hadj
        · subst hr'
          exact ih c' r (hall r (Or.inl rfl))
        · rcases hcl r r.2 r' hadj with hK | hv
          · exact ih c' ⟨r', hK⟩ (hall ⟨r', hK⟩ (Or.inr hadj))
          · exact ccw_guard G k v m _ r' hv

theorem walk_step (G : SimpleGraph V) (n : ℕ) {a b : V} (w : G.Walk a b)
    (hw : w.length ≤ n + 1) : ∃ y, Step G a y ∧ ∃ w' : G.Walk y b, w'.length ≤ n := by
  cases w with
  | nil => exact ⟨_, Or.inl rfl, SimpleGraph.Walk.nil, by simp⟩
  | cons h w' =>
    refine ⟨_, Or.inr h, w', ?_⟩
    simp only [SimpleGraph.Walk.length_cons] at hw
    omega

theorem travel (G : SimpleGraph V) (k : ℕ) (v : V) (K : Set V)
    (hcl : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K ∨ G.Adj v y) (t : Fin k → V) (M : ℕ)
    (hbase : ∀ r ∈ K, CopsCatchWithin G (k + 1) (M + 1) (Fin.cons v t : Fin (k + 1) → V) r) :
    ∀ (n : ℕ) (c : Fin k → V), (∀ i, ∃ w : G.Walk (c i) (t i), w.length ≤ n) →
      ∀ r ∈ K, CopsCatchWithin G (k + 1) (n + M + 1) (Fin.cons v c : Fin (k + 1) → V) r := by
  intro n
  induction n with
  | zero =>
    intro c hc r hr
    have hct : c = t := funext fun i => by
      obtain ⟨w, hw⟩ := hc i
      exact w.eq_of_length_eq_zero (by omega)
    rw [hct, Nat.zero_add]
    exact hbase r hr
  | succ n ih =>
    intro c hc r hr
    have hnext : ∀ i, ∃ y, Step G (c i) y ∧ ∃ w : G.Walk y (t i), w.length ≤ n := by
      intro i
      obtain ⟨w, hw⟩ := hc i
      exact walk_step G n w hw
    choose y hy hyw using hnext
    have hs : ∀ i, Step G ((Fin.cons v c : Fin (k + 1) → V) i)
        ((Fin.cons v y : Fin (k + 1) → V) i) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]; exact Or.inl rfl
      · simp only [Fin.cons_succ]; exact hy j
    have e : n + 1 + M + 1 = (n + M + 1) + 1 := by omega
    rw [e]
    refine Or.inr ⟨_, hs, Or.inr fun r' hr' => ?_⟩
    rcases hr' with hr' | hadj
    · subst hr'
      exact ih y hyw r hr
    · rcases hcl r hr r' hadj with hK | hv
      · exact ih y hyw r' hK
      · exact ccw_guard G k v (n + M) y r' hv

theorem component_exists (G : SimpleGraph V) (R : Set V) (r0 : V) (hr0 : r0 ∈ R) :
    ∃ K : Set V, K ⊆ R ∧ r0 ∈ K ∧ (G.induce K).Connected ∧
      ∀ x ∈ K, ∀ y ∈ R, G.Adj x y → y ∈ K := by
  let S : Set (Set V) := {s | s ⊆ R ∧ r0 ∈ s ∧ (G.induce s).Connected}
  have h0 : {u | u ∈ (SimpleGraph.Walk.nil : G.Walk r0 r0).support} ∈ S := by
    refine ⟨?_, ?_, SimpleGraph.Walk.connected_induce_support _⟩
    · intro u hu
      simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_ofPred_eq] at hu
      rw [hu]
      exact hr0
    · simp
  refine ⟨⋃₀ S, Set.sUnion_subset fun s hs => hs.1, Set.mem_sUnion.mpr ⟨_, h0, by simp⟩, ?_, ?_⟩
  · exact SimpleGraph.induce_sUnion_connected_of_pairwise_not_disjoint ⟨_, h0⟩
      (fun hs ht => ⟨r0, hs.2.1, ht.2.1⟩) (fun hs => hs.2.2)
  · intro x hx y hy hxy
    obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hx
    have hc : (G.induce (s ∪ {x, y})).Connected :=
      SimpleGraph.induce_union_connected hs.2.2.preconnected
        (SimpleGraph.induce_pair_connected_of_adj hxy).preconnected ⟨x, hxs, by simp⟩
    refine Set.mem_sUnion.mpr ⟨s ∪ {x, y}, ⟨?_, Or.inl hs.2.1, hc⟩, by simp⟩
    intro u hu
    rcases hu with hu | hu
    · exact hs.1 hu
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact hs.1 hxs
      · exact hy

theorem meyniel_H1 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ),
    G.Connected →
    (∀ s : Set V, s ⊆ {u | u ≠ v ∧ ¬ G.Adj v u} → (G.induce s).Connected →
      CopsWin (G.induce s) k) →
    CopsWin G (k + 1) := by
  intro V _ G v k hG hyp
  refine ⟨(Fin.cons v (fun _ => v) : Fin (k + 1) → V), fun r => ?_⟩
  by_cases hrv : r = v
  · exact ⟨0, 0, by simp [hrv]⟩
  by_cases hadj : G.Adj v r
  · exact ⟨1, ccw_guard G k v 0 _ r hadj⟩
  obtain ⟨K, hKR, hrK, hKc, hKcl⟩ :=
    component_exists G {u | u ≠ v ∧ ¬ G.Adj v u} r ⟨hrv, hadj⟩
  have hcl : ∀ x ∈ K, ∀ y, G.Adj x y → y ∈ K ∨ G.Adj v y := by
    intro x hx y hxy
    by_cases hyR : y ∈ {u | u ≠ v ∧ ¬ G.Adj v u}
    · exact Or.inl (hKcl x hx y hyR hxy)
    · right
      simp only [Set.mem_ofPred_eq, not_and, not_not] at hyR
      by_cases hyv : y = v
      · subst hyv
        exact absurd hxy.symm (hKR hx).2
      · exact hyR hyv
  obtain ⟨cK, hcK⟩ := hyp K hKR hKc
  choose mf hmf using hcK
  obtain ⟨M, hM⟩ := (Set.finite_range mf).bddAbove
  have hbase : ∀ r ∈ K, CopsCatchWithin G (k + 1) (M + 1)
      (Fin.cons v (fun i => (cK i : V)) : Fin (k + 1) → V) r := by
    intro r hr
    exact ccw_lift G k v K hcl M cK ⟨r, hr⟩
      (ccw_mono _ k (hM (Set.mem_range_self _)) cK _ (hmf ⟨r, hr⟩))
  have hw : ∀ i, Nonempty (G.Walk v (cK i : V)) := fun i => hG.preconnected v (cK i)
  let w : ∀ i, G.Walk v (cK i : V) := fun i => (hw i).some
  obtain ⟨L, hL⟩ := (Set.finite_range fun i => (w i).length).bddAbove
  exact ⟨L + M + 1, travel G k v K hcl _ M hbase L (fun _ => v)
    (fun i => ⟨w i, hL (Set.mem_range_self i)⟩) r hrK⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1.H1 :=
  OMA.Helpers.meyniel_H1
