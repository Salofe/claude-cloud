import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1

/-!
# Step H1 of the reduction Erdos713.erdos_713.parts.ii.R1

Let `G` be a graph on `Fin (m + 1)` with a vertex `v` of degree at most one, and let
`J = G.comap v.succAbove` be `G` with `v` deleted (a graph on `Fin m`). Then `J` is a subgraph of
`G`, so `ex(n, J) ≤ ex(n, G)`, and for `n ≥ m + 1` we prove `ex(n, G) ≤ ex(n, J) + n * m`.
Let `H` be a `G`-free graph on `Fin n`.

* `v` isolated: a copy of `J` in `H` misses some vertex, and sending `v` there gives a copy of `G`.
  So `H` is `J`-free.
* `v` is a leaf whose neighbour `u` has another neighbour: drop the edges of `H` at vertices of
  degree at most `m` (at most `n * m` edges). In what is left, a copy of `J` sends `u` to a vertex
  of `H`-degree above `m`, which has a neighbour outside the `m` image vertices; sending `v` there
  gives a copy of `G`. So the remaining graph is `J`-free.
* `u v` is an isolated edge of `G`: if `H` contains a copy of `J`, then every edge `a b` of `H`
  meets its image (otherwise move `u` to `a` and send `v` to `b`), so `H` has at most `n * m`
  edges.

If `J` has at least two edges this gives the second alternative of H1 with `r = m`. Otherwise
`J` has at most one edge, it embeds in every graph on `Fin n` (`n ≥ m`) with an edge, so
`ex(n, J) = 0` and `ex(n, G) ≤ n * m`, which is the first alternative.

Only the Mathlib definition `SimpleGraph.extremalNumber` and Mathlib lemmas are used.
-/

namespace OMA.Helpers

open SimpleGraph Finset

/-- Every vertex of `Fin (m + 1)` is `v` or in the image of `v.succAbove`. -/
theorem fin_cases_succAbove {m : ℕ} (v a : Fin (m + 1)) : a = v ∨ ∃ x, v.succAbove x = a := by
  by_cases h : a = v
  · exact Or.inl h
  · exact Or.inr (Fin.exists_succAbove_eq h)

/-- A copy of `G.comap v.succAbove` in `H` extends to a copy of `G` by sending `v` to a vertex `w`
outside its image that is adjacent to the images of all neighbours of `v`. -/
theorem extend_copy {m : ℕ} {W : Type*} {G : SimpleGraph (Fin (m + 1))} {H : SimpleGraph W}
    (v : Fin (m + 1)) (f : Copy (G.comap v.succAbove) H) (w : W)
    (hw : ∀ x, f x ≠ w) (hadj : ∀ x, G.Adj v (v.succAbove x) → H.Adj w (f x)) : G ⊑ H := by
  let g : Fin (m + 1) → W := Fin.insertNth v w (fun x => f x)
  have hgv : g v = w := Fin.insertNth_apply_same _ _ _
  have hgs : ∀ x, g (v.succAbove x) = f x := fun x => Fin.insertNth_apply_succAbove _ _ _ _
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro a b hab
    rcases fin_cases_succAbove v a with ha | ⟨x, hx⟩ <;>
      rcases fin_cases_succAbove v b with hb | ⟨y, hy⟩
    · rw [ha, hb] at hab
      exact (hab.ne rfl).elim
    · rw [ha, ← hy] at hab ⊢
      rw [hgv, hgs]
      exact hadj y hab
    · rw [hb, ← hx] at hab ⊢
      rw [hgv, hgs]
      exact (hadj x hab.symm).symm
    · rw [← hx, ← hy] at hab ⊢
      rw [hgs, hgs]
      exact f.toHom.map_adj hab
  · intro a b hab
    change g a = g b at hab
    rcases fin_cases_succAbove v a with ha | ⟨x, hx⟩ <;>
      rcases fin_cases_succAbove v b with hb | ⟨y, hy⟩
    · rw [ha, hb]
    · rw [ha, ← hy, hgv, hgs] at hab
      exact absurd hab.symm (hw y)
    · rw [hb, ← hx, hgv, hgs] at hab
      exact absurd hab (hw x)
    · rw [← hx, ← hy, hgs, hgs] at hab
      rw [← hx, ← hy, f.injective hab]

/-- If every edge of `H` meets `S`, then `H` has at most `#S * card V` edges. -/
theorem card_edgeFinset_le_of_meets {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V)
    (h : ∀ a b, H.Adj a b → a ∈ S ∨ b ∈ S) : #H.edgeFinset ≤ #S * Fintype.card V := by
  have hsub : H.edgeFinset ⊆ S.biUnion (fun s => H.incidenceFinset s) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rcases h a b he with ha | hb
      · exact mem_biUnion.2 ⟨a, ha, (mem_incidenceFinset _ _ _).2 ⟨he, Sym2.mem_mk_left _ _⟩⟩
      · exact mem_biUnion.2 ⟨b, hb, (mem_incidenceFinset _ _ _).2 ⟨he, Sym2.mem_mk_right _ _⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ fun s _ => ?_)
  rw [card_incidenceFinset_eq_degree]
  exact (H.degree_lt_card_verts s).le

/-- The spanning subgraph of `H` keeping the edges whose endpoints both have degree above `m`. -/
def highPart {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (m : ℕ) :
    SimpleGraph V where
  Adj a b := H.Adj a b ∧ m < H.degree a ∧ m < H.degree b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- Adjacency in `highPart`. -/
theorem highPart_adj {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (m : ℕ)
    (a b : V) : (highPart H m).Adj a b ↔ H.Adj a b ∧ m < H.degree a ∧ m < H.degree b := Iff.rfl

/-- `highPart H m` is a subgraph of `H`. -/
theorem highPart_le {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (m : ℕ) :
    highPart H m ≤ H := fun _ _ h => ((highPart_adj H m _ _).1 h).1

/-- Deleting the edges at vertices of degree at most `m` deletes at most `m * card V` edges. -/
theorem card_edgeFinset_le_highPart {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (m : ℕ) [DecidableRel (highPart H m).Adj] :
    #H.edgeFinset ≤ #(highPart H m).edgeFinset + Fintype.card V * m := by
  let L : Finset V := univ.filter (fun a => H.degree a ≤ m)
  have hsub : H.edgeFinset ⊆
      (highPart H m).edgeFinset ∪ L.biUnion (fun s => H.incidenceFinset s) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      by_cases ha : m < H.degree a
      · by_cases hb : m < H.degree b
        · refine mem_union_left _ ?_
          rw [mem_edgeFinset, mem_edgeSet, highPart_adj]
          exact ⟨he, ha, hb⟩
        · refine mem_union_right _ (mem_biUnion.2 ⟨b, ?_, ?_⟩)
          · simp only [L, mem_filter, mem_univ, true_and]; omega
          · exact (mem_incidenceFinset _ _ _).2 ⟨he, Sym2.mem_mk_right _ _⟩
      · refine mem_union_right _ (mem_biUnion.2 ⟨a, ?_, ?_⟩)
        · simp only [L, mem_filter, mem_univ, true_and]; omega
        · exact (mem_incidenceFinset _ _ _).2 ⟨he, Sym2.mem_mk_left _ _⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  refine (card_biUnion_le_card_mul _ _ _ fun s hs => ?_).trans
    (Nat.mul_le_mul_right _ (card_le_univ _))
  rw [card_incidenceFinset_eq_degree]
  simp only [L, mem_filter, mem_univ, true_and] at hs
  exact hs

/-- A `J`-free graph on `Fin n` has at most `extremalNumber n J` edges. -/
theorem card_le_extremalNumber_of_free {n : ℕ} {W : Type*} (J : SimpleGraph W)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (h : J.Free H) :
    #H.edgeFinset ≤ extremalNumber n J := by
  have := card_edgeFinset_le_extremalNumber h
  simpa using this

/-- A graph on `Fin m` with at most one edge is contained in every graph on `Fin n` (`m ≤ n`) with
an edge, so its extremal number vanishes. -/
theorem extremalNumber_eq_zero_of_card_le_one {m : ℕ} (J : SimpleGraph (Fin m))
    [DecidableRel J.Adj] (hJ : #J.edgeFinset ≤ 1) (n : ℕ) (hn : m ≤ n) :
    extremalNumber n J = 0 := by
  have key : ∀ ⦃H : SimpleGraph (Fin n)⦄ [DecidableRel H.Adj], J.Free H → #H.edgeFinset ≤ 0 := by
    intro H _ hfree
    by_contra hpos
    push Not at hpos
    obtain ⟨e, he⟩ := card_pos.1 hpos
    induction e using Sym2.ind with
    | h x y =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    apply hfree
    by_cases hex : ∃ a b, J.Adj a b
    · obtain ⟨a, b, hab⟩ := hex
      have honly : ∀ c d, J.Adj c d → (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
        intro c d hcd
        have h1 : s(c, d) ∈ J.edgeFinset := by rw [mem_edgeFinset]; exact hcd
        have h2 : s(a, b) ∈ J.edgeFinset := by rw [mem_edgeFinset]; exact hab
        exact Sym2.eq_iff.1 (card_le_one.1 hJ _ h1 _ h2)
      let e : Fin m ↪ Fin n := Fin.castLEEmb hn
      let σ1 : Equiv.Perm (Fin n) := Equiv.swap (e a) x
      let σ2 : Equiv.Perm (Fin n) := Equiv.swap (σ1 (e b)) y
      let g : Fin m → Fin n := fun c => σ2 (σ1 (e c))
      have h1 : σ1 (e a) = x := Equiv.swap_apply_left _ _
      have hne : σ1 (e b) ≠ x := by
        rw [← h1]
        intro h
        exact hab.ne (e.injective (σ1.injective h)).symm
      have hga : g a = x := by
        show σ2 (σ1 (e a)) = x
        rw [h1]
        exact Equiv.swap_apply_of_ne_of_ne hne.symm he.ne
      have hgb : g b = y := Equiv.swap_apply_left _ _
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro c d hcd
        rcases honly c d hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
        · rw [hc, hd, hga, hgb]
          exact he
        · rw [hc, hd, hga, hgb]
          exact he.symm
      · intro c d hcd
        exact e.injective (σ1.injective (σ2.injective hcd))
    · push Not at hex
      refine ⟨⟨⟨Fin.castLEEmb hn, ?_⟩, (Fin.castLEEmb hn).injective⟩⟩
      intro c d hcd
      exact absurd hcd (hex c d)
  have := (extremalNumber_le_iff (V := Fin n) J 0).2 key
  simp only [Fintype.card_fin, nonpos_iff_eq_zero] at this
  exact this

/-- Removing a vertex `v` of degree at most one lowers the extremal number by at most `n * m`. -/
theorem extremalNumber_le_comap_add {m : ℕ} (G : SimpleGraph (Fin (m + 1))) (v : Fin (m + 1))
    (hv : ∀ a b, G.Adj v a → G.Adj v b → a = b) (n : ℕ) (hn : m + 1 ≤ n) :
    extremalNumber n G ≤ extremalNumber n (G.comap v.succAbove) + n * m := by
  classical
  have key : ∀ ⦃H : SimpleGraph (Fin n)⦄ [DecidableRel H.Adj], G.Free H →
      #H.edgeFinset ≤ extremalNumber n (G.comap v.succAbove) + n * m := by
    intro H _ hfree
    by_cases hiso : ∀ a, ¬ G.Adj v a
    · -- `v` is isolated: every copy of `G - v` extends, as there is a spare vertex.
      have hJ : (G.comap v.succAbove).Free H := by
        rintro ⟨f⟩
        obtain ⟨w, hw⟩ : ∃ w, ∀ x, f x ≠ w := by
          by_contra hcon
          push Not at hcon
          have := Fintype.card_le_of_surjective _ hcon
          simp only [Fintype.card_fin] at this
          omega
        exact hfree (extend_copy v f w hw (fun x hx => absurd hx (hiso _)))
      exact (card_le_extremalNumber_of_free _ _ hJ).trans (Nat.le_add_right _ _)
    push Not at hiso
    obtain ⟨u, hu⟩ := hiso
    obtain ⟨x0, rfl⟩ := Fin.exists_succAbove_eq hu.ne.symm
    have honly : ∀ x, G.Adj v (v.succAbove x) → x = x0 := fun x hx =>
      Fin.succAbove_right_injective (hv _ _ hx hu)
    by_cases hdeg : ∃ x1, G.Adj (v.succAbove x0) (v.succAbove x1)
    · -- the neighbour of `v` has another neighbour: keep only the high-degree part of `H`.
      obtain ⟨x1, hx1⟩ := hdeg
      have hJ : (G.comap v.succAbove).Free (highPart H m) := by
        rintro ⟨f⟩
        have hadj01 : (highPart H m).Adj (f x0) (f x1) := f.toHom.map_adj hx1
        have hdegf : m < H.degree (f x0) := ((highPart_adj H m _ _).1 hadj01).2.1
        have hcard : #(univ.image f) < #(H.neighborFinset (f x0)) := by
          calc #(univ.image f) ≤ #(univ : Finset (Fin m)) := card_image_le
            _ = m := by simp
            _ < H.degree (f x0) := hdegf
            _ = #(H.neighborFinset (f x0)) := (card_neighborFinset_eq_degree _ _).symm
        obtain ⟨w, hwN, hwI⟩ := exists_mem_notMem_of_card_lt_card hcard
        let f' : Copy (G.comap v.succAbove) H := (Copy.ofLE _ _ (highPart_le H m)).comp f
        have hf' : ∀ x, f' x = f x := fun x => rfl
        refine hfree (extend_copy v f' w ?_ ?_)
        · intro x hx
          rw [hf'] at hx
          exact hwI (mem_image.2 ⟨x, mem_univ _, hx⟩)
        · intro x hx
          rw [honly x hx, hf']
          exact ((mem_neighborFinset _ _ _).1 hwN).symm
      have h1 := card_edgeFinset_le_highPart H m
      have h2 := card_le_extremalNumber_of_free _ _ hJ
      simp only [Fintype.card_fin] at h1
      omega
    · -- `v u` is an isolated edge: a copy of `G - v` meets every edge of `H`.
      push Not at hdeg
      by_cases hJ : (G.comap v.succAbove).Free H
      · exact (card_le_extremalNumber_of_free _ _ hJ).trans (Nat.le_add_right _ _)
      obtain ⟨f⟩ := not_not.1 hJ
      have hmeet : ∀ a b, H.Adj a b → a ∈ univ.image f ∨ b ∈ univ.image f := by
        intro a b hab
        by_contra hcon
        push Not at hcon
        obtain ⟨ha, hb⟩ := hcon
        let g2 : Fin m → Fin n := fun x => if x = x0 then a else f x
        have hg2hom : ∀ x y, (G.comap v.succAbove).Adj x y → H.Adj (g2 x) (g2 y) := by
          intro x y hxy
          have hx : x ≠ x0 := by
            rintro rfl
            exact hdeg y hxy
          have hy : y ≠ x0 := by
            rintro rfl
            exact hdeg x hxy.symm
          simp only [g2, if_neg hx, if_neg hy]
          exact f.toHom.map_adj hxy
        have hg2inj : Function.Injective g2 := by
          intro x y hxy
          by_cases hx : x = x0 <;> by_cases hy : y = x0
          · rw [hx, hy]
          · simp only [g2, if_pos hx, if_neg hy] at hxy
            exact absurd (mem_image.2 ⟨y, mem_univ _, hxy.symm⟩) ha
          · simp only [g2, if_neg hx, if_pos hy] at hxy
            exact absurd (mem_image.2 ⟨x, mem_univ _, hxy⟩) ha
          · simp only [g2, if_neg hx, if_neg hy] at hxy
            exact f.injective hxy
        let f2 : Copy (G.comap v.succAbove) H := ⟨⟨g2, fun {x y} h => hg2hom x y h⟩, hg2inj⟩
        have hf2 : ∀ x, f2 x = g2 x := fun x => rfl
        refine hfree (extend_copy v f2 b ?_ ?_)
        · intro x
          rw [hf2]
          by_cases hx : x = x0
          · simp only [g2, if_pos hx]
            exact hab.ne
          · simp only [g2, if_neg hx]
            intro h
            exact hb (mem_image.2 ⟨x, mem_univ _, h⟩)
        · intro x hx
          rw [honly x hx, hf2]
          simp only [g2, if_pos rfl]
          exact hab.symm
      have h1 := card_edgeFinset_le_of_meets H (univ.image f) hmeet
      have h2 : #(univ.image f) ≤ m := card_image_le.trans (by simp)
      simp only [Fintype.card_fin] at h1
      calc #H.edgeFinset ≤ #(univ.image f) * n := h1
        _ ≤ m * n := Nat.mul_le_mul_right _ h2
        _ = n * m := Nat.mul_comm _ _
        _ ≤ _ := Nat.le_add_left _ _
  have := (extremalNumber_le_iff (V := Fin n) G
    (extremalNumber n (G.comap v.succAbove) + n * m)).2 key
  simpa using this

end OMA.Helpers

open SimpleGraph Finset Filter Asymptotics

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1.H1 := by
  intro q G hb he hv
  obtain ⟨v, hv⟩ := hv
  cases q with
  | zero => exact v.elim0
  | succ m =>
  classical
  have hvn : ∀ a b, G.Adj v a → G.Adj v b → a = b := by
    have h1 := hv
    rw [← card_neighborFinset_eq_degree] at h1
    have h2 := card_le_one.1 (Nat.le_of_lt_succ h1)
    intro a b ha hb'
    exact h2 a ((mem_neighborFinset _ _ _).2 ha) b ((mem_neighborFinset _ _ _).2 hb')
  have hkey := OMA.Helpers.extremalNumber_le_comap_add G v hvn
  have hle : ∀ n, extremalNumber n (G.comap v.succAbove) ≤ extremalNumber n G := fun n =>
    IsContained.extremalNumber_le ⟨⟨⟨v.succAbove, fun h => h⟩, Fin.succAbove_right_injective⟩⟩
  by_cases hJ : 2 ≤ #(G.comap v.succAbove).edgeFinset
  · right
    refine ⟨m, G.comap v.succAbove, Nat.lt_succ_self m, ?_, ?_, ?_⟩
    · exact Colorable.of_hom ⟨v.succAbove, fun h => h⟩ hb
    · convert hJ
    · refine IsBigO.of_bound (m : ℝ) ?_
      filter_upwards [eventually_ge_atTop (m + 1)] with n hn
      have h1 : (extremalNumber n (G.comap v.succAbove) : ℝ) ≤ extremalNumber n G := by
        exact_mod_cast hle n
      have h2 : (extremalNumber n G : ℝ) ≤ extremalNumber n (G.comap v.succAbove) + n * m := by
        exact_mod_cast hkey n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), abs_le]
      have h3 : (0 : ℝ) ≤ m * n := by positivity
      constructor <;> linarith
  · left
    have h0 := OMA.Helpers.extremalNumber_eq_zero_of_card_le_one (G.comap v.succAbove) (by omega)
    refine IsBigO.of_bound (m : ℝ) ?_
    filter_upwards [eventually_ge_atTop (m + 1)] with n hn
    have h2 := hkey n hn
    rw [h0 n (by omega), Nat.zero_add] at h2
    have h3 : (extremalNumber n G : ℝ) ≤ n * m := by exact_mod_cast h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (extremalNumber n G))]
    linarith
