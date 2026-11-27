import OMAStatements.S_erdos_550
import Mathlib

/-!
Disproof of the formal statement `OMA.S_erdos_550.main`.

The statement lets the class sizes and the tree size be large independently of each
other. Take three classes of sizes `a, a, b` with `a = M + 1`, the star tree on
`M + 2` vertices, and `b` huge. The Ramsey number on the left is at least the number
of vertices `2a + b` of the multipartite graph, while the right-hand side is at most
`2 (R(T, K_{a,a}) - 1) + a`, which does not depend on `b`. Both Ramsey numbers are
finite: a graph with no star `K_{1, M+1}` has maximum degree at most `M`, hence a
greedy independent set of size `N / (M + 1)`.
-/

namespace OMA.Helpers

open SimpleGraph

/-- Greedy independent set in a graph of maximum degree at most `d`. -/
theorem indep_greedy {V : Type} [Fintype V] [DecidableEq V] (C : SimpleGraph V)
    [DecidableRel C.Adj] (d : ℕ) (hd : ∀ v, C.degree v ≤ d) :
    ∀ s : ℕ, ∀ U : Finset V, s * (d + 1) ≤ U.card →
      ∃ I ⊆ U, I.card = s ∧ ∀ x ∈ I, ∀ y ∈ I, ¬ C.Adj x y := by
  intro s
  induction s with
  | zero => intro U _; exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ s ih =>
    intro U hU
    have hpos : 0 < U.card := by
      have : (s + 1) * (d + 1) = s * (d + 1) + d + 1 := by ring
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hcard : s * (d + 1) ≤ ((U.erase v) \ C.neighborFinset v).card := by
      have h1 : (U.erase v).card = U.card - 1 := Finset.card_erase_of_mem hv
      have h2 := Finset.le_card_sdiff (C.neighborFinset v) (U.erase v)
      have h3 : (C.neighborFinset v).card ≤ d := by
        rw [card_neighborFinset_eq_degree]; exact hd v
      have : (s + 1) * (d + 1) = s * (d + 1) + d + 1 := by ring
      omega
    obtain ⟨I, hIU, hIc, hIind⟩ := ih _ hcard
    have hmem : ∀ x ∈ I, x ∈ U ∧ x ≠ v ∧ ¬ C.Adj v x := by
      intro x hx
      have := hIU hx
      simp only [Finset.mem_sdiff, Finset.mem_erase, mem_neighborFinset] at this
      exact ⟨this.1.2, this.1.1, this.2⟩
    have hvI : v ∉ I := fun h => (hmem v h).2.1 rfl
    refine ⟨insert v I, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact (hmem x hx).1
    · rw [Finset.card_insert_of_notMem hvI, hIc]
    · intro x hx y hy
      rcases Finset.mem_insert.mp hx with hxv | hxI <;>
        rcases Finset.mem_insert.mp hy with hyv | hyI
      · rw [hxv, hyv]; exact C.irrefl
      · rw [hxv]; exact (hmem y hyI).2.2
      · rw [hyv]; exact fun hadj => (hmem x hxI).2.2 hadj.symm
      · exact hIind x hxI y hyI

/-- A vertex of degree at least `k + 1` gives a copy of the star on `k + 2` vertices. -/
theorem star_contained {N k : ℕ} (C : SimpleGraph (Fin N)) [DecidableRel C.Adj] (v : Fin N)
    (hv : k + 1 ≤ C.degree v) : (starGraph (0 : Fin (k + 2))).IsContained C := by
  have hcard : k + 1 ≤ (C.neighborFinset v).card := by rwa [card_neighborFinset_eq_degree]
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin (k + 1) ≃ t := (Finset.equivFinOfCardEq htc).symm
  let g : Fin (k + 1) → Fin N := fun i => (e i : Fin N)
  have hg : Function.Injective g := by
    intro i j h
    exact e.injective (Subtype.ext h)
  have hgn : ∀ i, C.Adj v (g i) := by
    intro i
    have := ht (e i).2
    simpa [g] using this
  have hinj : Function.Injective (Fin.cons v g : Fin (k + 2) → Fin N) := by
    refine Fin.cons_injective_iff.mpr ⟨?_, hg⟩
    rintro ⟨i, hi⟩
    have := hgn i
    rw [hi] at this
    exact C.irrefl this
  rw [isContained_iff_exists_le_comap]
  refine ⟨⟨Fin.cons v g, hinj⟩, ?_⟩
  intro x y hxy
  rw [starGraph_adj] at hxy
  simp only [comap_adj, Function.Embedding.coeFn_mk]
  obtain ⟨hne, hx | hy⟩ := hxy
  · subst hx
    cases y using Fin.cases with
    | zero => exact absurd rfl hne
    | succ j => simpa using hgn j
  · subst hy
    cases x using Fin.cases with
    | zero => exact absurd rfl hne
    | succ j => simpa using (hgn j).symm

/-- Every graph on `card β * (k + 1)` vertices contains the star on `k + 2` vertices or
has a complement containing any fixed graph on `β`. -/
theorem star_mem {β : Type} [Fintype β] (H : SimpleGraph β) (k : ℕ) :
    Fintype.card β * (k + 1) ∈ {N : ℕ | ∀ C : SimpleGraph (Fin N),
      (starGraph (0 : Fin (k + 2))).IsContained C ∨ H.IsContained Cᶜ} := by
  intro C
  classical
  by_cases h : ∃ v, k + 1 ≤ C.degree v
  · obtain ⟨v, hv⟩ := h
    exact Or.inl (star_contained C v hv)
  · simp only [not_exists, not_le] at h
    have hd : ∀ v, C.degree v ≤ k := fun v => Nat.lt_succ_iff.mp (h v)
    obtain ⟨I, -, hIc, hI⟩ :=
      indep_greedy C k hd (Fintype.card β) Finset.univ (by simp)
    right
    have e : β ≃ I := Fintype.equivOfCardEq (by simp [hIc])
    rw [isContained_iff_exists_le_comap]
    refine ⟨e.toEmbedding.trans (Function.Embedding.subtype _), ?_⟩
    intro x y hxy
    simp only [comap_adj, compl_adj, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Function.Embedding.coe_subtype]
    refine ⟨?_, hI _ (e x).2 _ (e y).2⟩
    intro hxy'
    exact hxy.ne (e.injective (Subtype.ext hxy'))

theorem ramsey_le {β : Type} [Fintype β] (H : SimpleGraph β) (k : ℕ) :
    OMA.S_erdos_550.graphRamsey (starGraph (0 : Fin (k + 2))) H ≤ Fintype.card β * (k + 1) :=
  Nat.sInf_le (star_mem H k)

theorem card_le_ramsey {β : Type} [Fintype β] (H : SimpleGraph β) (k : ℕ) :
    Fintype.card β ≤ OMA.S_erdos_550.graphRamsey (starGraph (0 : Fin (k + 2))) H := by
  unfold OMA.S_erdos_550.graphRamsey
  apply le_csInf ⟨_, star_mem H k⟩
  intro N hN
  by_contra hlt
  simp only [not_le] at hlt
  rcases hN ⊥ with h | h
  · have hne : (starGraph (0 : Fin (k + 2))) ≠ ⊥ := by
      intro hb
      have h01 : (starGraph (0 : Fin (k + 2))).Adj 0 1 := starGraph_center_adj (by simp)
      rw [hb] at h01
      exact h01
    exact free_bot hne h
  · rw [compl_bot] at h
    obtain ⟨f⟩ := isContained_top_iff.mp h
    have := Fintype.card_le_of_embedding f
    simp only [Fintype.card_fin] at this
    omega

end OMA.Helpers

open SimpleGraph in
theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_550.main) := by
  intro h
  obtain ⟨M, hM⟩ := h 1
  let m : Fin 3 → ℕ := fun i =>
    if i.val = 2 then 2 * ((M + 1 + (M + 1)) * (M + 1)) + (M + 1) + 1 else M + 1
  have hmono : Monotone m := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    have hj3 : j.val < 3 := j.isLt
    simp only [m]
    split_ifs <;> omega
  have key := hM m hmono (by simp [m]) (M + 2) (by omega) (starGraph (0 : Fin (M + 2)))
    (isTree_starGraph _)
  have hup := OMA.Helpers.ramsey_le
    (completeBipartiteGraph (Fin (m 0)) (Fin (m 1))) M
  have hlow := OMA.Helpers.card_le_ramsey (OMA.S_erdos_550.completeMultipartite m) M
  have hcol : (OMA.S_erdos_550.completeMultipartite m).Colorable 3 := by
    have := (SimpleGraph.Coloring.mk (G := OMA.S_erdos_550.completeMultipartite m)
      (fun x => x.1) (fun h => h)).colorable
    simpa using this
  have hchi := hcol.chromaticNumber_le
  generalize (OMA.S_erdos_550.completeMultipartite m).chromaticNumber = χ at key hchi
  generalize OMA.S_erdos_550.graphRamsey (starGraph (0 : Fin (M + 2)))
    (OMA.S_erdos_550.completeMultipartite m) = L at key hlow
  generalize OMA.S_erdos_550.graphRamsey (starGraph (0 : Fin (M + 2)))
    (completeBipartiteGraph (Fin (m 0)) (Fin (m 1))) = R at key hup
  have h1 : χ - 1 ≤ 2 := by
    calc χ - 1 ≤ ((3 : ℕ) : ℕ∞) - 1 := tsub_le_tsub_right hchi 1
      _ = 2 := rfl
  have h2 : (χ - 1) * ((R - 1 : ℕ) : ℕ∞) + (m 0 : ℕ∞) ≤ ((2 * (R - 1) + m 0 : ℕ) : ℕ∞) := by
    push_cast
    gcongr
  have h3 : L ≤ 2 * (R - 1) + m 0 := by exact_mod_cast key.trans h2
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma, Fin.sum_univ_three] at hup hlow
  have hm0 : m 0 = M + 1 := by simp [m]
  have hm1 : m 1 = M + 1 := by simp [m]
  have hm2 : m 2 = 2 * ((M + 1 + (M + 1)) * (M + 1)) + (M + 1) + 1 := by simp [m]
  rw [hm0, hm1] at hup
  rw [hm0, hm1, hm2] at hlow
  rw [hm0] at h3
  generalize (M + 1 + (M + 1)) * (M + 1) = U at hup hlow h3
  omega
