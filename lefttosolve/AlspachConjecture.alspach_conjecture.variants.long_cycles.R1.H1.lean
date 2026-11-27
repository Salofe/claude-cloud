import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1
import Mathlib

/-!
# Step H1 of the reduction AlspachConjecture.alspach_conjecture.variants.long_cycles.R1

Walecki's theorem: for odd `n = 2k + 1 ≥ 5`, the complete graph on `Fin n` decomposes into `k`
Hamilton cycles.

Construction. The vertex `2k` plays the role of the point at infinity and `0, ..., 2k - 1` are
read modulo `2k`. The `i`-th cycle (`i < k`) is `∞, i, i + 1, i - 1, i + 2, i - 2, ..., i + k, ∞`
(the zig-zag path shifted by `i`). Every edge of the `i`-th cycle has colour `i`, where the colour
of `{a, b}` is `((a + b) mod 2k) / 2` for finite `a, b` and `b mod k` for `{∞, b}`. Hence two
different cycles share no edge. Each cycle has `2k + 1` distinct edges, so the `k` cycles cover
`k (2k + 1) = (2k + 1).choose 2` edges, i.e. every edge of the complete graph, exactly once.

Only upstream definitions (`IsCycleDecomposition`, `lengths`, `SimpleGraph.Cycle`) are used.
-/

namespace OMA.Helpers

open SimpleGraph AlspachConjecture

/-- The walk visiting `f 0, f 1, ..., f m`. -/
def walkTo {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
    (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) : (m : ℕ) → m ≤ N → G.Walk (f 0) (f m)
  | 0, _ => Walk.nil
  | m + 1, hm => (walkTo f N h m (by omega)).concat (h m (by omega))

theorem walkTo_support {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
    (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) (hm : m ≤ N) :
    (walkTo f N h m hm).support = (List.range (m + 1)).map f := by
  induction m with
  | zero => simp [walkTo]
  | succ m ih =>
    rw [walkTo, Walk.support_concat, ih (by omega), List.range_succ (n := m + 1), List.map_append]
    simp

theorem walkTo_edges {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
    (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) (hm : m ≤ N) :
    (walkTo f N h m hm).edges = (List.range m).map (fun t => s(f t, f (t + 1))) := by
  induction m with
  | zero => simp [walkTo]
  | succ m ih =>
    rw [walkTo, Walk.edges_concat, ih (by omega), List.range_succ, List.map_append]
    simp

theorem walkTo_length {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
    (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) (hm : m ≤ N) :
    (walkTo f N h m hm).length = m := by
  induction m with
  | zero => simp [walkTo]
  | succ m ih => rw [walkTo, Walk.length_concat, ih (by omega)]

/-- Walecki's zig-zag: position `t` of the `i`-th Hamilton cycle, the point at infinity being
`2k`. -/
def wal (k i t : ℕ) : ℕ :=
  if 2 * k ≤ t then 2 * k
  else if t % 2 = 1 then i + (t + 1) / 2
  else if t / 2 ≤ i then i - t / 2
  else i + 2 * k - t / 2

theorem wal_lt (k i t : ℕ) (hi : i < k) : wal k i t < 2 * k + 1 := by
  unfold wal
  split_ifs <;> omega

theorem wal_inj (k i t u : ℕ) (hi : i < k) (ht : t ≤ 2 * k) (hu : u ≤ 2 * k)
    (h : wal k i t = wal k i u) : t = u := by
  unfold wal at h
  split_ifs at h <;> omega

/-- The colour of an edge. -/
def col (k a b : ℕ) : ℕ :=
  if a = 2 * k then (if b < k then b else b - k)
  else if b = 2 * k then (if a < k then a else a - k)
  else if a + b < 2 * k then (a + b) / 2
  else (a + b - 2 * k) / 2

theorem col_comm (k a b : ℕ) : col k a b = col k b a := by
  unfold col
  split_ifs <;> omega

theorem col_step (k i t : ℕ) (hi : i < k) (ht : t < 2 * k) :
    col k (wal k i t) (wal k i (t + 1)) = i := by
  unfold col wal
  split_ifs <;> omega

theorem col_close (k i : ℕ) (hi : i < k) :
    col k (wal k i (2 * k)) (wal k i 0) = i := by
  unfold col wal
  split_ifs <;> omega

/-- Vertex `t` of the `i`-th Hamilton cycle. -/
def wv (k : ℕ) (i : Fin k) (t : ℕ) : Fin (2 * k + 1) := ⟨wal k i t, wal_lt k i t i.2⟩

theorem wv_inj (k : ℕ) (i : Fin k) (t u : ℕ) (ht : t ≤ 2 * k) (hu : u ≤ 2 * k)
    (h : wv k i t = wv k i u) : t = u :=
  wal_inj k i t u i.2 ht hu (congrArg Fin.val h)

theorem wv_adj (k : ℕ) (i : Fin k) :
    ∀ t, t < 2 * k → (completeGraph (Fin (2 * k + 1))).Adj (wv k i t) (wv k i (t + 1)) := by
  intro t ht
  rw [completeGraph_eq_top, top_adj]
  intro h
  have := wv_inj k i t (t + 1) (by omega) (by omega) h
  omega

theorem wv_close (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
    (completeGraph (Fin (2 * k + 1))).Adj (wv k i (2 * k)) (wv k i 0) := by
  rw [completeGraph_eq_top, top_adj]
  intro h
  have := wv_inj k i (2 * k) 0 le_rfl (by omega) h
  omega

/-- The Hamilton path of the `i`-th cycle, from `wv k i 0` to the point at infinity. -/
def hpath (k : ℕ) (i : Fin k) :
    (completeGraph (Fin (2 * k + 1))).Walk (wv k i 0) (wv k i (2 * k)) :=
  walkTo (wv k i) (2 * k) (wv_adj k i) (2 * k) le_rfl

/-- The `i`-th Walecki Hamilton cycle. -/
def cyc (k : ℕ) (hk : 1 ≤ k) (i : Fin k) : SimpleGraph.Cycle (completeGraph (Fin (2 * k + 1))) where
  base := wv k i (2 * k)
  walk := Walk.cons (wv_close k hk i) (hpath k i)
  isCycle := by
    rw [Walk.cons_isCycle_iff]
    constructor
    · rw [Walk.isPath_def, hpath, walkTo_support]
      apply List.Nodup.map_on
      · intro x hx y hy hxy
        rw [List.mem_range] at hx hy
        exact wv_inj k i x y (by omega) (by omega) hxy
      · exact List.nodup_range
    · rw [hpath, walkTo_edges, List.mem_map]
      rintro ⟨t, ht, he⟩
      rw [List.mem_range] at ht
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := wv_inj k i t (2 * k) (by omega) le_rfl h1
        omega
      · have h3 := wv_inj k i t 0 (by omega) (by omega) h1
        have h4 := wv_inj k i (t + 1) (2 * k) (by omega) le_rfl h2
        omega

theorem cyc_edges (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
    (cyc k hk i).edges = s(wv k i (2 * k), wv k i 0) ::
      (List.range (2 * k)).map (fun t => s(wv k i t, wv k i (t + 1))) := by
  simp only [SimpleGraph.Cycle.edges, cyc, Walk.edges_cons, hpath, walkTo_edges]

theorem cyc_length (k : ℕ) (hk : 1 ≤ k) (i : Fin k) : (cyc k hk i).length = 2 * k + 1 := by
  simp only [SimpleGraph.Cycle.length, cyc, Walk.length_cons, hpath, walkTo_length]

/-- The colour of an edge, as a function on `Sym2`. -/
def colS (k : ℕ) : Sym2 (Fin (2 * k + 1)) → ℕ :=
  Sym2.lift ⟨fun a b => col k a b, fun a b => col_comm k a b⟩

theorem colS_of_mem (k : ℕ) (hk : 1 ≤ k) (i : Fin k) (e : Sym2 (Fin (2 * k + 1)))
    (he : e ∈ (cyc k hk i).edges) : colS k e = i := by
  rw [cyc_edges, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨t, ht, rfl⟩
  · simp only [colS, Sym2.lift_mk]
    exact col_close k i i.2
  · rw [List.mem_range] at ht
    simp only [colS, Sym2.lift_mk]
    exact col_step k i t i.2 ht

theorem cyc_nodup (k : ℕ) (hk : 1 ≤ k) (i : Fin k) : (cyc k hk i).edges.Nodup :=
  (cyc k hk i).isCycle.edges_nodup

theorem choose_two_odd (k : ℕ) : (2 * k + 1).choose 2 = k * (2 * k + 1) := by
  rw [Nat.choose_two_right, show (2 * k + 1) * (2 * k + 1 - 1) = 2 * (k * (2 * k + 1)) by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]; ring, Nat.mul_div_cancel_left _ (by norm_num)]

end OMA.Helpers

open SimpleGraph AlspachConjecture OMA.Helpers in
theorem OMA.solution : OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1.H1 := by
  intro n hn hn5 m hm hsum
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  have hm' : m = Multiset.replicate k (2 * k + 1) := by
    have h1 : m = Multiset.replicate (Multiset.card m) (2 * k + 1) :=
      Multiset.eq_replicate.mpr ⟨rfl, hm⟩
    have h2 : Multiset.card m = k := by
      rw [h1, Multiset.sum_replicate, smul_eq_mul, choose_two_odd] at hsum
      exact Nat.eq_of_mul_eq_mul_right (by omega) hsum
    rw [h1, h2]
  refine ⟨(Finset.univ : Finset (Fin k)).val.map (cyc k hk), ?_, ?_⟩
  · intro e he
    classical
    -- every edge lies on some cycle, by counting
    have hex : ∃ i, e ∈ (cyc k hk i).edges := by
      let S : Fin k → Finset (Sym2 (Fin (2 * k + 1))) := fun i => (cyc k hk i).edges.toFinset
      have hsub : Finset.univ.biUnion S ⊆ (completeGraph (Fin (2 * k + 1))).edgeFinset := by
        intro x hx
        rw [Finset.mem_biUnion] at hx
        obtain ⟨i, -, hx⟩ := hx
        rw [List.mem_toFinset] at hx
        rw [mem_edgeFinset]
        exact Walk.edges_subset_edgeSet _ hx
      have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint S := by
        intro i _ j _ hij
        rw [Function.onFun, Finset.disjoint_left]
        intro x hxi hxj
        rw [List.mem_toFinset] at hxi hxj
        apply hij
        apply Fin.ext
        rw [← colS_of_mem k hk i x hxi, ← colS_of_mem k hk j x hxj]
      have hcard : (Finset.univ.biUnion S).card = k * (2 * k + 1) := by
        rw [Finset.card_biUnion hdisj]
        have : ∀ i, (S i).card = 2 * k + 1 := by
          intro i
          simp only [S]
          rw [List.toFinset_card_of_nodup (cyc_nodup k hk i), SimpleGraph.Cycle.edges,
            Walk.length_edges]
          exact cyc_length k hk i
        simp [this]
      have hcardE : (completeGraph (Fin (2 * k + 1))).edgeFinset.card = k * (2 * k + 1) := by
        rw [← choose_two_odd]
        convert card_edgeFinset_top_eq_card_choose_two (V := Fin (2 * k + 1)) using 1
        simp
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcardE])
      have he' : e ∈ Finset.univ.biUnion S := by
        rw [heq]
        convert he
      rw [Finset.mem_biUnion] at he'
      obtain ⟨i, -, hi⟩ := he'
      exact ⟨i, List.mem_toFinset.mp hi⟩
    obtain ⟨i0, hi0⟩ := hex
    rw [Multiset.filter_map, Multiset.card_map, Multiset.card_eq_one]
    refine ⟨i0, ?_⟩
    rw [Multiset.Nodup.ext (Multiset.Nodup.filter _ Finset.univ.nodup) (Multiset.nodup_singleton _)]
    intro i
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and,
      Multiset.mem_singleton, Function.comp]
    constructor
    · intro hi
      apply Fin.ext
      rw [← colS_of_mem k hk i e hi, ← colS_of_mem k hk i0 e hi0]
    · rintro rfl
      exact hi0
  · rw [hm', lengths, Multiset.map_map]
    have : (SimpleGraph.Cycle.length ∘ cyc k hk) = fun _ => 2 * k + 1 := by
      funext i
      exact cyc_length k hk i
    rw [this, Multiset.map_const']
    simp
