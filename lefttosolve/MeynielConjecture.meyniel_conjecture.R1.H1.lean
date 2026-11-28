import OMAReductions.R_MeynielConjecture_meyniel_conjecture_R1

/-!
# Step H1 of the reduction MeynielConjecture.meyniel_conjecture.R1: guarding a closed neighbourhood

Let `G` be a connected finite graph and `v` a vertex, and suppose that `k` cops win on every
connected induced subgraph of `G` avoiding the closed neighbourhood `N[v]`. Then `k + 1` cops
win on `G`.

All `k + 1` cops start on `v`, and cop `0` never leaves `v`.
* A robber starting on `v` is caught at once, and a robber starting in `N(v)` is caught in the
  first round by cop `0`.
* Otherwise the robber starts in `R = V \ N[v]`. Let `K` be its connected piece of `G[R]`
  (`component_exists`). Every edge leaving `K` ends in `N(v)`, so a robber that leaves `K`
  steps next to cop `0` and is caught in the following round (`ccw_guard`).
* The other `k` cops walk along walks of `G` from `v` to the start positions of a winning
  `k`-cop strategy on `G[K]` (`walk_step`, `travel`), and then replay that strategy, lifted to
  `G` (`ccw_lift`). As `K` is finite, a single round bound `M` serves every robber start in `K`
  (`ccw_mono`).

Only the upstream definitions `MeynielConjecture.Step`, `MeynielConjecture.CopsCatchWithin`
and `MeynielConjecture.CopsWin` are used (no upstream theorem and no upstream instance).
-/

namespace OMA.Helpers

open MeynielConjecture

variable {V : Type}

/-- One more round never hurts: a catch within `m` rounds is a catch within `m + 1` rounds. -/
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

/-- A catch within `m` rounds is a catch within any `m' ≥ m` rounds. -/
theorem ccw_mono (G : SimpleGraph V) (k : ℕ) {m m' : ℕ} (hm : m ≤ m') (c : Fin k → V) (r : V)
    (h : CopsCatchWithin G k m c r) : CopsCatchWithin G k m' c r := by
  induction m', hm using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ccw_succ G k n c r ih

/-- A cop on `v` catches, in the next round, a robber standing on a neighbour of `v`. -/
theorem ccw_guard (G : SimpleGraph V) (k : ℕ) (v : V) (m : ℕ) (c : Fin k → V) (r : V)
    (hr : G.Adj v r) :
    CopsCatchWithin G (k + 1) (m + 1) (Fin.cons v c : Fin (k + 1) → V) r := by
  refine Or.inr ⟨(Fin.cons r c : Fin (k + 1) → V), fun i => ?_, Or.inl ⟨0, by simp⟩⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact Or.inr hr
  · simp only [Fin.cons_succ]; exact Or.inl rfl

/-- Lifting a strategy from `G.induce K` to `G` with one extra cop parked on `v`: if every edge
leaving `K` ends next to `v`, a catch within `m` rounds on `G.induce K` gives a catch within
`m + 1` rounds on `G`. -/
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

/-- A walk of length at most `n + 1` can be followed for one move (a step or a stay), leaving a
walk of length at most `n`. -/
theorem walk_step (G : SimpleGraph V) (n : ℕ) {a b : V} (w : G.Walk a b)
    (hw : w.length ≤ n + 1) : ∃ y, Step G a y ∧ ∃ w' : G.Walk y b, w'.length ≤ n := by
  cases w with
  | nil => exact ⟨_, Or.inl rfl, SimpleGraph.Walk.nil, by simp⟩
  | cons h w' =>
    refine ⟨_, Or.inr h, w', ?_⟩
    simp only [SimpleGraph.Walk.length_cons] at hw
    omega

/-- The cops walk to the positions `t`: if cop `i` has a walk of length at most `n` to `t i`, and
from `t` (with the guard on `v`) the cops catch any robber in `K` within `M + 1` rounds, then
they catch any robber in `K` within `n + M + 1` rounds. -/
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

/-- The connected piece of `R` containing `r0`: a set `K ⊆ R` containing `r0`, connected as an
induced subgraph, and closed under the edges of `G` inside `R`. -/
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

/-- The guarding lemma: one cop on `v` plus `k` cops winning on every connected piece of
`G - N[v]` win on `G`. -/
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

theorem OMA.solution : OMA.R_MeynielConjecture_meyniel_conjecture_R1.H1 :=
  OMA.Helpers.meyniel_H1
