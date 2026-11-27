import OMAReductions.R_Erdos552_erdos_552_parts_ii_R1

/-!
# Step H1 of the reduction Erdos552.erdos_552.parts.ii.R1

Parsons: for every prime p the Ramsey number of the four-cycle versus the star with
p^2 leaves equals p^2+p+1.

Only Mathlib and the upstream definition graphRamsey are used.

* Upper bound. In a graph on p^2+p+1 vertices with no four-cycle whose complement has
  no star with p^2 leaves, every degree is at least p+1. Two distinct vertices have at
  most one common neighbour, so the sum of (degree choose 2) is at most (N choose 2),
  which is exactly N (p+1 choose 2). Equality forces a (p+1)-regular graph in which
  every pair of vertices has exactly one common neighbour. Over ZMod q, q a prime
  divisor of p, its adjacency matrix A satisfies A*A = J and A*J = J, so A^q = J,
  whereas trace (A^q) = (trace A)^q = 0 and trace J = N = 1.
* Lower bound. Take the polarity graph of the projective plane over ZMod p (points
  adjacent when orthogonal for the standard dot product) and delete one absolute
  point v0, which exists since every element of ZMod p is a sum of two squares.
  Two distinct points have at most one common neighbour (Mathlib lemma
  eq_or_eq_of_orthogonal), each line has p+1 points, and no absolute point other than
  v0 is orthogonal to v0, so the p^2+p remaining vertices have degree at least p.
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


/-- In the extremal case of the pair count every pair has a common neighbour. -/
theorem common_of_sum_ge {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ (cycleGraph 4).IsContained G)
    (hsum : N.choose 2 ≤ ∑ v, (G.degree v).choose 2) :
    ∀ u w, u ≠ w → ∃ x, G.Adj u x ∧ G.Adj w x := by
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
  have hsub : (univ.biUnion fun v => (G.neighborFinset v).powersetCard 2) ⊆
      (univ.powersetCard 2 : Finset (Finset (Fin N))) := by
    intro s hs
    simp only [mem_biUnion, mem_univ, true_and, mem_powersetCard] at hs
    obtain ⟨v, -, hv⟩ := hs
    rw [mem_powersetCard]
    exact ⟨subset_univ _, hv⟩
  have hcard : (univ.powersetCard 2 : Finset (Finset (Fin N))).card ≤
      (univ.biUnion fun v => (G.neighborFinset v).powersetCard 2).card := by
    rw [card_biUnion hdisj, card_powersetCard, card_univ, Fintype.card_fin]
    simpa [card_powersetCard] using hsum
  have heq := eq_of_subset_of_card_le hsub hcard
  intro u w huw
  have hmem : ({u, w} : Finset (Fin N)) ∈ (univ.powersetCard 2 : Finset (Finset (Fin N))) := by
    rw [mem_powersetCard]
    exact ⟨subset_univ _, card_pair huw⟩
  rw [← heq, mem_biUnion] at hmem
  obtain ⟨x, -, hx⟩ := hmem
  rw [mem_powersetCard] at hx
  have hu : u ∈ G.neighborFinset x := hx.1 (by simp)
  have hw : w ∈ G.neighborFinset x := hx.1 (by simp)
  rw [mem_neighborFinset] at hu hw
  exact ⟨x, hu.symm, hw.symm⟩

/-- In the extremal case of the pair count the graph is regular. -/
theorem regular_of_sum {N d : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hd : 2 ≤ d) (hdeg : ∀ v, d ≤ G.degree v)
    (hsum : ∑ v, (G.degree v).choose 2 ≤ N * d.choose 2) : ∀ v, G.degree v = d := by
  classical
  have hle : ∀ v ∈ (univ : Finset (Fin N)), d.choose 2 ≤ (G.degree v).choose 2 :=
    fun v _ => Nat.choose_le_choose 2 (hdeg v)
  have hconst : ∑ _v : Fin N, d.choose 2 = N * d.choose 2 := by simp
  have heq : ∑ _v : Fin N, d.choose 2 = ∑ v, (G.degree v).choose 2 :=
    le_antisymm (Finset.sum_le_sum hle) (hconst ▸ hsum)
  rw [Finset.sum_eq_sum_iff_of_le hle] at heq
  intro v
  have h1 := heq v (mem_univ v)
  by_contra hne
  have h2 : d + 1 ≤ G.degree v := by have := hdeg v; omega
  have h3 := Nat.choose_le_choose 2 h2
  have h4 : (d + 1).choose 2 = d.choose 1 + d.choose 2 := Nat.choose_succ_succ d 1
  rw [Nat.choose_one_right] at h4
  omega

/-- Upward closure of the defining set. -/
theorem RS_mono {m N M : ℕ} (h : N ∈ RS m) (hNM : N ≤ M) : M ∈ RS m := by
  classical
  intro C
  let e : Fin N ↪ Fin M := Fin.castLEEmb hNM
  rcases h (C.comap e) with h4 | hS
  · left
    exact h4.trans ⟨⟨⟨e, fun {a b} hab => hab⟩, e.injective⟩⟩
  · right
    obtain ⟨v, hv⟩ := le_degree_of_star (C.comap e) hS
    exact star_of_le_degree C m (e v) (le_trans hv (compl_degree_comap_le C e v))

/-- The counting upper bound at a prime square: the extremal graphs would be
friendship graphs of degree p+1, which do not exist. -/
theorem upper_mem (p : ℕ) (hp : p.Prime) : p ^ 2 + p + 1 ∈ RS (p ^ 2) := by
  classical
  have hp2 := hp.two_le
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ 2 := ⟨_, rfl⟩
  have hq1 : 4 ≤ q := by rw [hq]; nlinarith
  rw [← hq]
  intro C
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h4, hS⟩ := hcon
  have hS' : ¬ (completeBipartiteGraph (Fin 1) (Fin ((q - 1) + 1))).IsContained Cᶜ := by
    rw [show q - 1 + 1 = q by omega]
    exact hS
  have hdeg : ∀ v, p + 1 ≤ C.degree v := by
    intro v
    have := (degree_bound C hS' v).2
    omega
  have hA := two_mul_choose_two (p + 1)
  have hB := two_mul_choose_two (q + p + 1)
  rw [show p + 1 - 1 = p by omega] at hA
  rw [show q + p + 1 - 1 = q + p by omega] at hB
  have hid : (q + p + 1).choose 2 = (q + p + 1) * (p + 1).choose 2 := by
    have : 2 * (q + p + 1).choose 2 = 2 * ((q + p + 1) * (p + 1).choose 2) := by
      rw [hB, mul_left_comm, hA, hq]
      ring
    omega
  have hlow : ∑ _v : Fin (q + p + 1), (p + 1).choose 2 ≤ ∑ v, (C.degree v).choose 2 :=
    Finset.sum_le_sum fun v _ => Nat.choose_le_choose 2 (hdeg v)
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlow
  have hup := sum_choose_le C h4
  have hcom := common_of_sum_ge C h4 (by rw [hid]; exact hlow)
  have hreg := regular_of_sum C (by omega) hdeg (by rw [← hid]; exact hup)
  have hone : ∀ u w, u ≠ w →
      ((C.neighborFinset u).filter (fun x => C.Adj x w)).card = 1 := by
    intro u w huw
    obtain ⟨x, hux, hwx⟩ := hcom u w huw
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
  exact no_friendship C hreg hone (by rw [show p + 1 - 1 = p by omega, hq]; ring) (by omega)

section plane

open Projectivization Configuration

/-- Over a field of characteristic p the conic x^2+y^2+z^2 = 0 has a point. -/
theorem exists_absolute (p : ℕ) [Fact p.Prime] :
    ∃ v : Projectivization (ZMod p) (Fin 3 → ZMod p), v.orthogonal v := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have hne : (![a, b, 1] : Fin 3 → ZMod p) ≠ 0 := by
    intro h
    have := congrFun h 2
    simp at this
  refine ⟨mk (ZMod p) ![a, b, 1] hne, ?_⟩
  rw [orthogonal_mk]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one]
  linear_combination hab

/-- The number of points of the projective plane over ZMod p. -/
theorem card_plane (p : ℕ) [Fact p.Prime] [Fintype (Projectivization (ZMod p) (Fin 3 → ZMod p))] :
    Fintype.card (Projectivization (ZMod p) (Fin 3 → ZMod p)) = p ^ 2 + p + 1 := by
  rw [← Nat.card_eq_fintype_card, card_of_finrank (ZMod p) (Fin 3 → ZMod p)
    (Module.finrank_fin_fun (ZMod p)), Nat.card_zmod]
  simp [Finset.sum_range_succ]
  ring

/-- Each line of the projective plane over ZMod p has p+1 points. -/
theorem card_line (p : ℕ) [Fact p.Prime] [Fintype (Projectivization (ZMod p) (Fin 3 → ZMod p))]
    (x : Projectivization (ZMod p) (Fin 3 → ZMod p))
    [DecidablePred fun z : Projectivization (ZMod p) (Fin 3 → ZMod p) => z.orthogonal x] :
    (univ.filter fun z : Projectivization (ZMod p) (Fin 3 → ZMod p) => z.orthogonal x).card = p + 1 := by
  classical
  have h1 := ProjectivePlane.card_points (Projectivization (ZMod p) (Fin 3 → ZMod p))
    (Projectivization (ZMod p) (Fin 3 → ZMod p))
  rw [card_plane] at h1
  have h2 := ProjectivePlane.pointCount_eq (Projectivization (ZMod p) (Fin 3 → ZMod p)) x
  set o := ProjectivePlane.order (Projectivization (ZMod p) (Fin 3 → ZMod p)) (Projectivization (ZMod p) (Fin 3 → ZMod p))
  have ho : o = p := by
    rcases lt_trichotomy o p with h | h | h
    · have : o ^ 2 < p ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
      omega
    · exact h
    · have : p ^ 2 < o ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
      omega
  rw [ho] at h2
  rw [← h2, pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1

/-- The polarity graph of the projective plane with one absolute point removed
has no four-cycle and minimum degree at least p. -/
theorem lower_not_mem (p : ℕ) (hp : p.Prime) : p ^ 2 + p ∉ RS (p ^ 2) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  let P := Projectivization (ZMod p) (Fin 3 → ZMod p)
  let _ : Fintype P := Fintype.ofFinite P
  obtain ⟨v0, hv0⟩ := exists_absolute p
  let s : Finset P := univ.erase v0
  have hs : s.card = p ^ 2 + p := by
    rw [card_erase_of_mem (mem_univ v0), card_univ, card_plane]
    omega
  let eqv := s.equivFinOfCardEq hs
  let ι : Fin (p ^ 2 + p) → P := fun i => (eqv.symm i).val
  have hιinj : Function.Injective ι := by
    intro i j h
    exact eqv.symm.injective (Subtype.val_injective h)
  have hιv0 : ∀ i, ι i ≠ v0 := by
    intro i h
    have := (eqv.symm i).property
    simp only [s, mem_erase] at this
    exact this.1 h
  have hιsurj : ∀ z : P, z ≠ v0 → ∃ i, ι i = z := by
    intro z hz
    refine ⟨eqv ⟨z, by simp [s, hz]⟩, ?_⟩
    simp [ι]
  let G : SimpleGraph (Fin (p ^ 2 + p)) := SimpleGraph.fromRel fun i j => (ι i).orthogonal (ι j)
  have hGadj : ∀ i j, G.Adj i j → (ι i).orthogonal (ι j) := by
    intro i j h
    rcases h.2 with h' | h'
    · exact h'
    · exact orthogonal_comm.mp h'
  have hC4 : ¬ (cycleGraph 4).IsContained G := by
    rintro ⟨φ⟩
    have e01 := hGadj _ _ (φ.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide))
    have e21 := hGadj _ _ (φ.toHom.map_adj (show (cycleGraph 4).Adj 2 1 by decide))
    have e03 := hGadj _ _ (φ.toHom.map_adj (show (cycleGraph 4).Adj 0 3 by decide))
    have e23 := hGadj _ _ (φ.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide))
    rcases ofField.eq_or_eq_of_orthogonal e01 e21 e03 e23 with h | h
    · exact absurd (φ.injective (hιinj h)) (by decide)
    · exact absurd (φ.injective (hιinj h)) (by decide)
  have hdeg : ∀ i, p ≤ G.degree i := by
    intro i
    set x := ι i with hx
    let T : Finset P := univ.filter fun z : P => z.orthogonal x
    have hT : T.card = p + 1 := card_line p x
    have hT' : p ≤ ((T.erase x).erase v0).card := by
      by_cases hxx : x.orthogonal x
      · have hv0T : v0 ∉ T.erase x := by
          intro hmem
          simp only [T, mem_erase, mem_filter, mem_univ, true_and] at hmem
          rcases ofField.eq_or_eq_of_orthogonal hxx hmem.2
              (orthogonal_comm.mp hmem.2) hv0 with h | h
          · exact hιv0 i h
          · exact hιv0 i h
        rw [erase_eq_of_notMem hv0T]
        have hxT : x ∈ T := by simp [T, hxx]
        rw [card_erase_of_mem hxT, hT]
        omega
      · have hxT : x ∉ T := by simp [T, hxx]
        rw [erase_eq_of_notMem hxT]
        have := pred_card_le_card_erase (s := T) (a := v0)
        omega
    have hsub : (T.erase x).erase v0 ⊆ (G.neighborFinset i).image ι := by
      intro z hz
      simp only [T, mem_erase, mem_filter, mem_univ, true_and] at hz
      obtain ⟨hzv0, hzx, hzo⟩ := hz
      obtain ⟨j, rfl⟩ := hιsurj z hzv0
      rw [mem_image]
      refine ⟨j, ?_, rfl⟩
      rw [mem_neighborFinset, fromRel_adj]
      refine ⟨?_, Or.inr hzo⟩
      intro hij
      exact hzx (by rw [hx, hij])
    have := card_le_card hsub
    rw [card_image_of_injective _ hιinj, card_neighborFinset_eq_degree] at this
    omega
  intro hmem
  rcases hmem G with h | h
  · exact hC4 h
  · obtain ⟨v, hv⟩ := le_degree_of_star G h
    have h2 := degree_compl G (v := v)
    have h3 := hdeg v
    simp only [Fintype.card_fin] at h2
    have h4 : 4 ≤ p ^ 2 := by nlinarith
    omega

end plane

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R1.H1 := by
  intro p hp
  show sInf (RS (p ^ 2)) = p ^ 2 + p + 1
  have hmem := upper_mem p hp
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  intro N hN
  by_contra hlt
  exact lower_not_mem p hp (RS_mono hN (by omega))
