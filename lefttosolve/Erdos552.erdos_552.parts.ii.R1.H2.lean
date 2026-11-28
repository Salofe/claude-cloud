import OMAReductions.R_Erdos552_erdos_552_parts_ii_R1

/-!
# Step H2 of the reduction Erdos552.erdos_552.parts.ii.R1

Let f n be the Ramsey number of the four-cycle versus the star with n leaves.
We show f n ≤ f (n+1) ≤ f n + 2 for every n ≥ 1.

The argument is self-contained and uses only Mathlib and the upstream definition
of graphRamsey.

* A graph without four-cycle has at most one common neighbour for any two distinct
  vertices, hence the sum over the vertices of (degree choose 2) is at most (N choose 2).
  This gives a finite Ramsey number for every star (nonemptiness of the defining set).
* Monotonicity: a star with n+1 leaves contains a star with n leaves.
* Increment: take a graph on f n + 2 vertices with no four-cycle and complement
  degrees at most n. If two vertices u, w have no common neighbour of complement degree n,
  deleting them leaves a graph on f n vertices, which must contain the forbidden
  complement star; adding back u or w gives a star with n+1 leaves. Otherwise a double
  counting shows the graph is d-regular and every pair has exactly one common
  neighbour, with N = d(d-1)+1 and n = d(d-2), so d ≥ 3. Over ZMod p with p a prime
  divisor of d-1, the adjacency matrix A satisfies A*A = J and A*J = J, so A^p = J,
  while trace (A^p) = (trace A)^p = 0 and trace J = N = 1, a contradiction.
-/

namespace OMA.Helpers

open SimpleGraph Finset

/-- Two distinct vertices with two distinct common neighbours span a four-cycle. -/
theorem c4_of_two_common {V : Type*} (G : SimpleGraph V) {a b x y : V}
    (hab : a ≠ b) (hxy : x ≠ y) (hax : G.Adj a x) (hbx : G.Adj b x)
    (hay : G.Adj a y) (hby : G.Adj b y) : (cycleGraph 4).IsContained G := by
  have h1 : a ≠ x := G.ne_of_adj hax
  have h2 : a ≠ y := G.ne_of_adj hay
  have h3 : b ≠ x := G.ne_of_adj hbx
  have h4 : b ≠ y := G.ne_of_adj hby
  let F : Fin 4 → V := ![a, x, b, y]
  have hinj : Function.Injective F := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [F] at h ⊢ <;>
      first
      | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm
      | exact h3 h | exact h3 h.symm | exact h4 h | exact h4 h.symm
      | exact hab h | exact hab h.symm | exact hxy h | exact hxy h.symm
  have hmap : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → G.Adj (F i) (F j) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd h (by decide)
      | (simp only [F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Fin.zero_eta,
          Fin.mk_one, Fin.reduceFinMk]
         first
         | exact hax | exact hax.symm | exact hbx | exact hbx.symm
         | exact hay | exact hay.symm | exact hby | exact hby.symm)
  exact ⟨⟨⟨F, fun {i j} h => hmap i j h⟩, hinj⟩⟩

/-- A vertex with at least m neighbours in the complement gives a complement star. -/
theorem star_of_le_degree {N : ℕ} (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (m : ℕ) (v : Fin N) (hv : m ≤ Hᶜ.degree v) :
    (completeBipartiteGraph (Fin 1) (Fin m)).IsContained Hᶜ := by
  classical
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hv
  let g := t.orderEmbOfFin htc
  have hg : ∀ j, g j ∈ Hᶜ.neighborFinset v := fun j => ht (t.orderEmbOfFin_mem htc j)
  let F : Fin 1 ⊕ Fin m → Fin N := Sum.elim (fun _ => v) (fun j => g j)
  have hinj : Function.Injective F := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (Subsingleton.elim i j)
    · have := hg j
      simp only [F, Sum.elim_inl, Sum.elim_inr] at h
      rw [← h, mem_neighborFinset] at this
      exact absurd this (Hᶜ.loopless.irrefl v)
    · have := hg i
      simp only [F, Sum.elim_inl, Sum.elim_inr] at h
      rw [h, mem_neighborFinset] at this
      exact absurd this (Hᶜ.loopless.irrefl v)
    · simp only [F, Sum.elim_inr] at h
      exact congrArg Sum.inr (g.injective h)
  have hmap : ∀ x y : Fin 1 ⊕ Fin m, (completeBipartiteGraph (Fin 1) (Fin m)).Adj x y →
      Hᶜ.Adj (F x) (F y) := by
    rintro (i | i) (j | j) h
    · simp [completeBipartiteGraph] at h
    · have := hg j
      rw [mem_neighborFinset] at this
      exact this
    · have := hg i
      rw [mem_neighborFinset] at this
      exact this.symm
    · simp [completeBipartiteGraph] at h
  exact ⟨⟨⟨F, fun {x y} h => hmap x y h⟩, hinj⟩⟩

/-- A complement star with m leaves gives a vertex of complement degree at least m. -/
theorem le_degree_of_star {N m : ℕ} (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (h : (completeBipartiteGraph (Fin 1) (Fin m)).IsContained Hᶜ) :
    ∃ v, m ≤ Hᶜ.degree v := by
  classical
  obtain ⟨φ⟩ := h
  refine ⟨φ (Sum.inl 0), ?_⟩
  have hsub : (univ.image fun j : Fin m => φ (Sum.inr j)) ⊆
      Hᶜ.neighborFinset (φ (Sum.inl 0)) := by
    intro x hx
    simp only [mem_image, mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [mem_neighborFinset]
    exact φ.toHom.map_adj (by simp [completeBipartiteGraph])
  have hc : (univ.image fun j : Fin m => φ (Sum.inr j)).card = m := by
    rw [card_image_of_injective (f := fun j : Fin m => φ (Sum.inr j)) univ
      (fun a b h => Sum.inr_injective (φ.injective h))]
    simp
  calc m = _ := hc.symm
    _ ≤ _ := card_le_card hsub

/-- Twice (n choose 2) is n(n-1). -/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    cases k with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [mul_add, ih]
      ring

/-- Counting pairs of neighbours in a graph without four-cycle. -/
theorem sum_choose_le {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (cycleGraph 4).IsContained G) :
    ∑ v, (G.degree v).choose 2 ≤ N.choose 2 := by
  classical
  have hdisj : ((univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun v => (G.neighborFinset v).powersetCard 2) := by
    intro v _ w _ hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs hs'
    rw [mem_powersetCard] at hs hs'
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hs.2
    have ha : a ∈ G.neighborFinset v := hs.1 (by simp)
    have hb : b ∈ G.neighborFinset v := hs.1 (by simp)
    have ha' : a ∈ G.neighborFinset w := hs'.1 (by simp)
    have hb' : b ∈ G.neighborFinset w := hs'.1 (by simp)
    rw [mem_neighborFinset] at ha hb ha' hb'
    exact hG (c4_of_two_common G hab hvw ha.symm hb.symm ha'.symm hb'.symm)
  calc ∑ v, (G.degree v).choose 2
      = ∑ v, ((G.neighborFinset v).powersetCard 2).card := by
        simp [card_powersetCard]
    _ = (univ.biUnion fun v => (G.neighborFinset v).powersetCard 2).card :=
        (card_biUnion hdisj).symm
    _ ≤ (univ.powersetCard 2 : Finset (Finset (Fin N))).card := by
        apply card_le_card
        intro s hs
        simp only [mem_biUnion, mem_univ, true_and, mem_powersetCard] at hs
        obtain ⟨v, -, hv⟩ := hs
        rw [mem_powersetCard]
        exact ⟨subset_univ _, hv⟩
    _ = N.choose 2 := by simp [card_powersetCard]

/-- If every pair of distinct vertices has a common neighbour in T then
(N choose 2) is at most the sum over T of (degree choose 2). -/
theorem choose_le_sum_of_cover {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (T : Finset (Fin N))
    (hcov : ∀ u w, u ≠ w → ∃ x ∈ T, G.Adj u x ∧ G.Adj w x) :
    N.choose 2 ≤ ∑ x ∈ T, (G.degree x).choose 2 := by
  classical
  calc N.choose 2 = (univ.powersetCard 2 : Finset (Finset (Fin N))).card := by
        simp [card_powersetCard]
    _ ≤ (T.biUnion fun x => (G.neighborFinset x).powersetCard 2).card := by
        apply card_le_card
        intro s hs
        rw [mem_powersetCard] at hs
        obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hs.2
        obtain ⟨x, hxT, hax, hbx⟩ := hcov a b hab
        rw [mem_biUnion]
        refine ⟨x, hxT, ?_⟩
        rw [mem_powersetCard]
        refine ⟨?_, card_pair hab⟩
        intro z hz
        rw [mem_insert, mem_singleton] at hz
        rw [mem_neighborFinset]
        rcases hz with rfl | rfl
        · exact hax.symm
        · exact hbx.symm
    _ ≤ ∑ x ∈ T, ((G.neighborFinset x).powersetCard 2).card := card_biUnion_le
    _ = ∑ x ∈ T, (G.degree x).choose 2 := by simp [card_powersetCard]

/-- No d-regular graph with d ≥ 3 on d(d-1)+1 vertices has exactly one common
neighbour for every pair of distinct vertices. -/
theorem no_friendship {N d : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = d)
    (hone : ∀ u w, u ≠ w → ((G.neighborFinset u).filter (fun x => G.Adj x w)).card = 1)
    (hN : N = d * (d - 1) + 1) (hd : 3 ≤ d) : False := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d - 1 ≠ 1 by omega)
  have := Fact.mk hp
  have hd1 : ((d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
  have hdeq : (d : ZMod p) = 1 := by
    have : d = (d - 1) + 1 := by omega
    rw [this, Nat.cast_add, hd1, Nat.cast_one, zero_add]
  have hAA : G.adjMatrix (ZMod p) * G.adjMatrix (ZMod p) = Matrix.of fun _ _ => 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [adjMatrix_mul_self_apply_self, hreg]
      simp [hdeq]
    · rw [adjMatrix_mul_apply]
      simp only [adjMatrix_apply]
      rw [Finset.sum_boole, hone i j hij]
      simp
  have hAJ : G.adjMatrix (ZMod p) * (Matrix.of fun _ _ => (1 : ZMod p)) =
      Matrix.of fun _ _ => 1 := by
    ext i j
    rw [adjMatrix_mul_apply]
    simp only [Matrix.of_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [card_neighborFinset_eq_degree, hreg, hdeq]
  have hpow : ∀ k : ℕ, G.adjMatrix (ZMod p) ^ (k + 2) = Matrix.of fun _ _ => 1 := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_two, hAA]
    | succ k ih => rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ', ih, hAJ]
  have htr : Matrix.trace (G.adjMatrix (ZMod p) ^ p) = 0 := by
    rw [ZMod.trace_pow_card, trace_adjMatrix, zero_pow hp.ne_zero]
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hAp := hpow k
  rw [← hk] at hAp
  rw [hAp] at htr
  have htrJ : Matrix.trace (Matrix.of fun _ _ => (1 : ZMod p) : Matrix (Fin N) (Fin N) (ZMod p))
      = (N : ZMod p) := by
    simp [Matrix.trace]
  rw [htrJ, hN] at htr
  push_cast at htr
  rw [hd1, mul_zero, zero_add] at htr
  exact one_ne_zero htr

/-- Removing a vertex set and keeping a complement neighbour outside the image. -/
theorem compl_degree_comap {N M : ℕ} (C : SimpleGraph (Fin N)) [DecidableRel C.Adj]
    (e : Fin M ↪ Fin N) (v : Fin M) (z : Fin N) (hz : ∀ y, e y ≠ z) (hzv : e v ≠ z)
    (hadj : ¬ C.Adj (e v) z) :
    (C.comap e)ᶜ.degree v + 1 ≤ Cᶜ.degree (e v) := by
  classical
  have hsub : insert z (((C.comap e)ᶜ.neighborFinset v).map e) ⊆ Cᶜ.neighborFinset (e v) := by
    intro x hx
    rw [mem_insert] at hx
    rw [mem_neighborFinset, compl_adj]
    rcases hx with rfl | hx
    · exact ⟨hzv, hadj⟩
    · rw [mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [mem_neighborFinset, compl_adj, comap_adj] at hy
      exact ⟨fun h => hy.1 (e.injective h), hy.2⟩
  have hnot : z ∉ ((C.comap e)ᶜ.neighborFinset v).map e := by
    rw [mem_map]
    rintro ⟨y, -, hy⟩
    exact hz y hy
  have := card_le_card hsub
  rw [card_insert_of_notMem hnot, card_map, card_neighborFinset_eq_degree,
    card_neighborFinset_eq_degree] at this
  exact this

/-- Complement degrees do not decrease when passing to the whole graph. -/
theorem compl_degree_comap_le {N M : ℕ} (C : SimpleGraph (Fin N)) [DecidableRel C.Adj]
    (e : Fin M ↪ Fin N) (v : Fin M) :
    (C.comap e)ᶜ.degree v ≤ Cᶜ.degree (e v) := by
  classical
  have hsub : ((C.comap e)ᶜ.neighborFinset v).map e ⊆ Cᶜ.neighborFinset (e v) := by
    intro x hx
    rw [mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_neighborFinset, compl_adj, comap_adj] at hy
    rw [mem_neighborFinset, compl_adj]
    exact ⟨fun h => hy.1 (e.injective h), hy.2⟩
  have := card_le_card hsub
  rw [card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at this
  exact this

/-- The defining set of the four-cycle versus star Ramsey number. -/
def RS (m : ℕ) : Set ℕ :=
  { N : ℕ | ∀ C : SimpleGraph (Fin N), (cycleGraph 4).IsContained C ∨
      (completeBipartiteGraph (Fin 1) (Fin m)).IsContained Cᶜ }

/-- Degree bound from the absence of a complement star. -/
theorem degree_bound {N m : ℕ} (C : SimpleGraph (Fin N)) [DecidableRel C.Adj]
    (hS : ¬ (completeBipartiteGraph (Fin 1) (Fin (m + 1))).IsContained Cᶜ) (v : Fin N) :
    Cᶜ.degree v ≤ m ∧ N ≤ C.degree v + 1 + m := by
  classical
  have h1 : Cᶜ.degree v ≤ m := by
    by_contra h
    exact hS (star_of_le_degree C (m + 1) v (by omega))
  have h2 := degree_compl C (v := v)
  have h3 := C.degree_lt_card_verts v
  simp only [Fintype.card_fin] at h2 h3
  exact ⟨h1, by omega⟩

/-- Every star has a finite Ramsey number against the four-cycle. -/
theorem mem_RS (m : ℕ) (hm : 1 ≤ m) : 2 * m + 2 ∈ RS m := by
  classical
  intro C
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h4, hS⟩ := hcon
  have hS' : ¬ (completeBipartiteGraph (Fin 1) (Fin ((m - 1) + 1))).IsContained Cᶜ := by
    rw [show m - 1 + 1 = m by omega]
    exact hS
  have hdeg : ∀ v, m + 2 ≤ C.degree v := by
    intro v
    have := (degree_bound C hS' v).2
    omega
  have hsum := sum_choose_le C h4
  have hlow : ∑ _v : Fin (2 * m + 2), (m + 2).choose 2 ≤ ∑ v, (C.degree v).choose 2 :=
    Finset.sum_le_sum fun v _ => Nat.choose_le_choose 2 (hdeg v)
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlow
  have hA := two_mul_choose_two (m + 2)
  have hB := two_mul_choose_two (2 * m + 2)
  have hC : (2 * m + 2) * (2 * ((m + 2).choose 2)) ≤ 2 * (2 * m + 2).choose 2 := by
    have := le_trans hlow hsum
    nlinarith
  rw [hA, hB] at hC
  simp only [show m + 2 - 1 = m + 1 by omega, show 2 * m + 2 - 1 = 2 * m + 1 by omega] at hC
  have hD := Nat.le_of_mul_le_mul_left hC (by omega : 0 < 2 * m + 2)
  nlinarith

theorem RS_nonempty (m : ℕ) (hm : 1 ≤ m) : (RS m).Nonempty := ⟨_, mem_RS m hm⟩

/-- Elements of the defining set exceed the number of leaves. -/
theorem lt_of_mem_RS {m N : ℕ} (h : N ∈ RS m) : m < N := by
  classical
  rcases h ⊥ with h4 | hS
  · obtain ⟨φ⟩ := h4
    have := φ.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
    exact this.elim
  · obtain ⟨v, hv⟩ := le_degree_of_star ⊥ hS
    have := (⊥ᶜ : SimpleGraph (Fin N)).degree_lt_card_verts v
    simp only [Fintype.card_fin] at this
    omega

/-- Monotonicity in the number of leaves. -/
theorem RS_succ_subset {m : ℕ} : RS (m + 1) ⊆ RS m := by
  classical
  intro N h C
  rcases h C with h4 | hS
  · exact Or.inl h4
  · right
    obtain ⟨v, hv⟩ := le_degree_of_star C hS
    exact star_of_le_degree C m v (by omega)

/-- The increment step. -/
theorem add_two_mem_RS (n : ℕ) (hn : 1 ≤ n) : sInf (RS n) + 2 ∈ RS (n + 1) := by
  classical
  set M := sInf (RS n) with hMdef
  have hM : M ∈ RS n := Nat.sInf_mem (RS_nonempty n hn)
  have hMn : n < M := lt_of_mem_RS hM
  intro C
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h4, hS⟩ := hcon
  have hb := degree_bound C hS
  -- a pair of distinct vertices without a common neighbour of complement degree n
  have key : ∃ u w : Fin (M + 2), u ≠ w ∧
      ∀ x, C.Adj u x → C.Adj w x → Cᶜ.degree x < n := by
    by_contra hno
    push_neg at hno
    set d := M + 1 - n with hd
    let T : Finset (Fin (M + 2)) := univ.filter fun x => n ≤ Cᶜ.degree x
    have hTdeg : ∀ x ∈ T, C.degree x = d := by
      intro x hx
      simp only [T, mem_filter, mem_univ, true_and] at hx
      have h1 := (hb x).1
      have h2 := degree_compl C (v := x)
      have h3 := C.degree_lt_card_verts x
      simp only [Fintype.card_fin] at h2 h3
      omega
    have hcov : ∀ u w, u ≠ w → ∃ x ∈ T, C.Adj u x ∧ C.Adj w x := by
      intro u w huw
      obtain ⟨x, hux, hwx, hx⟩ := hno u w huw
      exact ⟨x, by simp [T, hx], hux, hwx⟩
    have hcover := choose_le_sum_of_cover C T hcov
    have hcount := sum_choose_le C h4
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun x => n ≤ Cᶜ.degree x)] at hcount
    have hrest : ∑ x ∈ univ.filter (fun x => ¬ n ≤ Cᶜ.degree x), (C.degree x).choose 2 = 0 := by
      have : ∑ x ∈ T, (C.degree x).choose 2 =
          ∑ x ∈ univ.filter (fun x => n ≤ Cᶜ.degree x), (C.degree x).choose 2 := rfl
      omega
    rw [Finset.sum_eq_zero_iff] at hrest
    have hall : ∀ x, x ∈ T := by
      intro x
      by_contra hxT
      have hx : x ∈ univ.filter (fun x => ¬ n ≤ Cᶜ.degree x) := by
        simp only [T, mem_filter, mem_univ, true_and] at hxT ⊢
        exact hxT
      have h0 := hrest x hx
      rw [Nat.choose_eq_zero_iff] at h0
      have := (hb x).2
      omega
    have hreg : ∀ x, C.degree x = d := fun x => hTdeg x (hall x)
    have hTuniv : T = univ := eq_univ_of_forall hall
    rw [hTuniv] at hcover
    simp only [hreg, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hcover
    have hcount' := sum_choose_le C h4
    simp only [hreg, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hcount'
    have heq : (M + 2) * d.choose 2 = (M + 2).choose 2 := le_antisymm hcount' hcover
    have hA := two_mul_choose_two d
    have hB := two_mul_choose_two (M + 2)
    have heq2 : (M + 2) * (d * (d - 1)) = (M + 2) * (M + 1) := by
      rw [← hA, show M + 1 = M + 2 - 1 by omega, ← hB, ← heq]
      ring
    have heq3 : d * (d - 1) = M + 1 := Nat.eq_of_mul_eq_mul_left (by omega) heq2
    have hd3 : 3 ≤ d := by
      rcases Nat.lt_or_ge d 3 with h | h
      · interval_cases d <;> omega
      · exact h
    have hone : ∀ u w, u ≠ w →
        ((C.neighborFinset u).filter (fun x => C.Adj x w)).card = 1 := by
      intro u w huw
      obtain ⟨x, hux, hwx, -⟩ := hno u w huw
      rw [card_eq_one]
      refine ⟨x, ?_⟩
      ext y
      simp only [mem_filter, mem_neighborFinset, mem_singleton]
      constructor
      · rintro ⟨huy, hyw⟩
        by_contra hyx
        exact h4 (c4_of_two_common C huw hyx huy hyw.symm hux hwx)
      · rintro rfl
        exact ⟨hux, hwx.symm⟩
    exact no_friendship C hreg hone (by omega) hd3
  obtain ⟨u, w, huw, hprop⟩ := key
  let s : Finset (Fin (M + 2)) := (univ.erase u).erase w
  have hs : s.card = M := by
    have hw : w ∈ univ.erase u := mem_erase.mpr ⟨huw.symm, mem_univ w⟩
    rw [card_erase_of_mem hw, card_erase_of_mem (mem_univ u), card_univ, Fintype.card_fin]
    omega
  let e : Fin M ↪ Fin (M + 2) := (s.orderEmbOfFin hs).toEmbedding
  have hes : ∀ y, e y ∈ s := fun y => s.orderEmbOfFin_mem hs y
  have heu : ∀ y, e y ≠ u := by
    intro y h
    have := hes y
    rw [h] at this
    simp [s] at this
  have hew : ∀ y, e y ≠ w := by
    intro y h
    have := hes y
    rw [h] at this
    simp [s] at this
  have hC' : ¬ (cycleGraph 4).IsContained (C.comap e) := by
    intro h
    apply h4
    exact h.trans ⟨⟨⟨e, fun {a b} hab => hab⟩, e.injective⟩⟩
  rcases hM (C.comap e) with h | h
  · exact hC' h
  · obtain ⟨v, hv⟩ := le_degree_of_star (C.comap e) h
    have hge : n ≤ Cᶜ.degree (e v) := le_trans hv (compl_degree_comap_le C e v)
    have hnadj : ¬ C.Adj (e v) u ∨ ¬ C.Adj (e v) w := by
      by_contra hc
      push_neg at hc
      have h1 := hprop (e v) hc.1.symm hc.2.symm
      omega
    rcases hnadj with hu | hw
    · have := compl_degree_comap C e v u heu (heu v) hu
      have := (hb (e v)).1
      omega
    · have := compl_degree_comap C e v w hew (hew v) hw
      have := (hb (e v)).1
      omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R1.H2 := by
  intro n hn
  show sInf (RS n) ≤ sInf (RS (n + 1)) ∧ sInf (RS (n + 1)) ≤ sInf (RS n) + 2
  have hmem : sInf (RS (n + 1)) ∈ RS (n + 1) := Nat.sInf_mem (RS_nonempty (n + 1) (by omega))
  exact ⟨Nat.sInf_le (RS_succ_subset hmem), Nat.sInf_le (add_two_mem_RS n hn)⟩
