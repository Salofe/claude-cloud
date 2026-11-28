import FormalConjectures.Arxiv.«2606.03696».BondyLongestCycles
import Mathlib

/-!
# Bondy's conjecture for k = 3 (minimum degree version)

Own proof, organised around lists of vertices instead of walks.

* `IsCyc G L` : a cyclic list (distinct vertices, consecutive ones adjacent, last adjacent to first).
  `cyc_length_le` bounds its length by the circumference, `cyc_of_isCycle` turns the given cycle into one.
* `gap`, `crossing`, `common_nbr` : the three cycle exchanges (all produce a longer cyclic list).
* `three_succ` : for three attachment vertices pairwise joined through the component `H` by lists with at
  least two vertices, the successors `u1 u2 u3` satisfy `deg u1 + deg u2 + deg u3 + |H| ≤ n + 3`
  (shift injection `arc_count` on each of the three arcs).  With 3-connectivity (`good_triple`) this gives
  `|H| + 3 ≤ δ` (`h_bound`).
* `inj_count` : an injection of shifted positions into the cycle; it gives the two counting bounds
  `case_ii` (a longest list of `H` spans `H`) and `case_i` (its two ends have few neighbours in `H`),
  the dichotomy being `posa`.
* `final_contra`, `main_aux` : assembly.
-/

open SimpleGraph

namespace OMA.Helpers

variable {V : Type*}

/-- cyclic list: nodup chain whose last is adjacent to its head -/
def IsCyc (G : SimpleGraph V) (L : List V) : Prop :=
  L.Nodup ∧ L.IsChain G.Adj ∧ ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, G.Adj x y

theorem cyc_length_le [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {L : List V}
    (hL : IsCyc G L) (h3 : 3 ≤ L.length) : L.length ≤ G.circumference := by
  obtain ⟨hnd, hch, hadj⟩ := hL
  have hne : L ≠ [] := by
    intro h; rw [h] at h3; simp at h3
  set p := Walk.ofSupport L hne hch with hp
  have hpath : p.IsPath := by
    rw [Walk.isPath_def, Walk.support_ofSupport]; exact hnd
  have hlen : p.length = L.length - 1 := Walk.length_ofSupport hne hch
  have hadj' : G.Adj (L.getLast hne) (L.head hne) :=
    hadj _ (List.getLast?_eq_some_getLast hne) _ (List.head?_eq_some_head hne)
  have hcyc : (Walk.cons hadj' p).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hpath, fun hmem => ?_⟩
    have h1 : p.length = 1 := by
      apply hpath.length_eq_one_of_mem_edges
      rw [Sym2.eq_swap]; exact hmem
    omega
  have hmem : (Walk.cons hadj' p).length ∈ G.cycleLengths :=
    ⟨_, _, hcyc, rfl⟩
  have hbdd : BddAbove G.cycleLengths := by
    refine ⟨Fintype.card V, ?_⟩
    rintro m ⟨a, w, hw, rfl⟩
    have := hw.isPath_tail.length_lt
    have h2 : w.tail.length + 1 = w.length := by
      apply Walk.length_tail_add_one
      exact hw.not_nil
    omega
  have := le_csSup hbdd hmem
  rw [Walk.length_cons, hlen] at this
  unfold SimpleGraph.circumference
  omega

theorem cyc_of_isCycle {G : SimpleGraph V} {a : V} {C : G.Walk a a} (hC : C.IsCycle) :
    IsCyc G C.support.tail ∧ C.support.tail.length = C.length := by
  have hlen : C.support.tail.length = C.length := by simp [Walk.length_support]
  refine ⟨⟨hC.support_nodup, C.isChain_adj_support.tail, ?_⟩, hlen⟩
  intro x hx y hy
  have h3 := hC.three_le_length
  have hsup : C.support = a :: C.support.tail := (C.cons_tail_support).symm
  have hl : C.support.tail ≠ [] := by
    intro h0; rw [h0] at hlen; simp at hlen; omega
  have hx' : x = a := by
    have h1 : C.support.getLast? = some a := by
      rw [List.getLast?_eq_some_getLast (C.support_ne_nil), C.getLast_support]
    rw [hsup, List.getLast?_cons_of_ne_nil hl] at h1
    rw [h1] at hx
    simpa using hx.symm
  subst hx'
  have hch := C.isChain_adj_support
  rw [hsup] at hch
  exact hch.rel_head? hy

theorem getLast?_app {A B : List V} {b : V} (h : B.getLast? = some b) :
    (A ++ B).getLast? = some b := by
  rw [List.getLast?_append, h]; rfl

theorem head?_app {A B : List V} {a : V} (h : A.head? = some a) :
    (A ++ B).head? = some a := by
  rw [List.head?_append, h]; rfl

theorem chain_app {R : V → V → Prop} {A B : List V} {x y : V} (h1 : A.IsChain R) (h2 : B.IsChain R)
    (ha : A.getLast? = some x) (hb : B.head? = some y) (h : R x y) : (A ++ B).IsChain R := by
  apply h1.append h2
  intro x' hx' y' hy'
  rw [ha] at hx'; rw [hb] at hy'
  obtain rfl : x = x' := by simpa using hx'
  obtain rfl : y = y' := by simpa using hy'
  exact h

theorem chain_rev {G : SimpleGraph V} {l : List V} (hl : l.IsChain G.Adj) :
    l.reverse.IsChain G.Adj := by
  rw [List.isChain_reverse]
  exact hl.imp (fun _ _ h => h.symm)

theorem cyc_mk {G : SimpleGraph V} {L : List V} {x y : V} (hnd : L.Nodup) (hch : L.IsChain G.Adj)
    (hl : L.getLast? = some x) (hh : L.head? = some y) (h : G.Adj x y) : IsCyc G L := by
  refine ⟨hnd, hch, ?_⟩
  intro x' hx' y' hy'
  rw [hl] at hx'; rw [hh] at hy'
  obtain rfl : x = x' := by simpa using hx'
  obtain rfl : y = y' := by simpa using hy'
  exact h

theorem cyc_rotate {G : SimpleGraph V} {X Y : List V} (h : IsCyc G (X ++ Y)) : IsCyc G (Y ++ X) := by
  rcases List.eq_nil_or_concat' X with rfl | ⟨X', b, rfl⟩
  · simpa using h
  rcases Y with _ | ⟨u', Y'⟩
  · simpa using h
  obtain ⟨hnd, hch, hadj⟩ := h
  have hnd' : (u' :: Y' ++ (X' ++ [b])).Nodup := by
    rw [List.nodup_append_comm]; exact hnd
  have hYX : G.Adj ((u' :: Y').getLast (by simp)) ((X' ++ [b]).head (by simp)) := by
    apply hadj
    · exact getLast?_app (List.getLast?_eq_some_getLast (by simp))
    · exact head?_app (List.head?_eq_some_head (by simp))
  rw [List.isChain_append] at hch
  refine cyc_mk hnd' ?_ (getLast?_app (by simp)) (by simp) ?_ (x := b) (y := u')
  · exact chain_app hch.2.1 hch.1 (List.getLast?_eq_some_getLast _) (List.head?_eq_some_head _) hYX
  · exact hch.2.2 b (by simp) u' (by simp)

/-- master contradiction lemma for the crossing configuration -/
theorem crossing {G : SimpleGraph V} {c : ℕ}
    (hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ c)
    {X Y1 Y2 Y3 Q : List V} {u b u' v w a q0 q1 : V}
    (hcyc : IsCyc G (X ++ (Y1 ++ (Y2 ++ Y3)))) (hlen : (X ++ (Y1 ++ (Y2 ++ Y3))).length = c)
    (h3 : 3 ≤ c)
    (hXh : X.head? = some u) (hXl : X.getLast? = some b)
    (hY1h : Y1.head? = some u') (hY1l : Y1.getLast? = some v)
    (hY3h : Y3.head? = some w) (hY3l : Y3.getLast? = some a)
    (hQh : Q.head? = some q0) (hQl : Q.getLast? = some q1)
    (hQnd : Q.Nodup) (hQch : Q.IsChain G.Adj)
    (hQdisj : ∀ z ∈ Q, z ∉ X ++ (Y1 ++ (Y2 ++ Y3)))
    (haq : G.Adj a q0) (hqb : G.Adj q1 b)
    (hk : Y2.length < Q.length)
    (huv : G.Adj u v) (hu'w : G.Adj u' w) : False := by
  obtain ⟨hnd, hch, hadj⟩ := hcyc
  have hnd0 : (Q ++ (X ++ (Y1 ++ (Y2 ++ Y3)))).Nodup :=
    List.nodup_append.2 ⟨hQnd, hnd, fun x hx y hy hxy => hQdisj x hx (hxy ▸ hy)⟩
  have hsub : (Q ++ (X ++ (Y1 ++ Y3))).Sublist (Q ++ (X ++ (Y1 ++ (Y2 ++ Y3)))) :=
    (List.Sublist.refl Q).append ((List.Sublist.refl X).append
      ((List.Sublist.refl Y1).append (List.sublist_append_right Y2 Y3)))
  have hperm : (Q ++ (X.reverse ++ (Y1.reverse ++ Y3))).Perm (Q ++ (X ++ (Y1 ++ Y3))) :=
    List.Perm.append_left Q ((List.reverse_perm X).append
      (List.Perm.append_right Y3 (List.reverse_perm Y1)))
  have hnd1 : (Q ++ (X.reverse ++ (Y1.reverse ++ Y3))).Nodup :=
    hperm.nodup_iff.2 (hnd0.sublist hsub)
  have hchX : X.IsChain G.Adj := hch.left_of_append
  have hchY : (Y1 ++ (Y2 ++ Y3)).IsChain G.Adj := hch.right_of_append
  have hchY1 : Y1.IsChain G.Adj := hchY.left_of_append
  have hchY3 : Y3.IsChain G.Adj := hchY.right_of_append.right_of_append
  have hch1 : (Q ++ (X.reverse ++ (Y1.reverse ++ Y3))).IsChain G.Adj := by
    refine chain_app hQch (chain_app (chain_rev hchX) (chain_app (chain_rev hchY1) hchY3
      (x := u') (y := w) ?_ hY3h hu'w) (x := u) (y := v) ?_ ?_ huv) hQl (y := b) ?_ hqb
    · rw [List.getLast?_reverse]; exact hY1h
    · rw [List.getLast?_reverse]; exact hXh
    · apply head?_app; rw [List.head?_reverse]; exact hY1l
    · apply head?_app; rw [List.head?_reverse]; exact hXl
  have key : IsCyc G (Q ++ (X.reverse ++ (Y1.reverse ++ Y3))) :=
    cyc_mk hnd1 hch1 (getLast?_app (getLast?_app (getLast?_app hY3l))) (head?_app hQh) haq
  have h1 := hmax _ key (by simp at hlen ⊢; omega)
  simp at hlen h1
  omega

/-- gap lemma -/
theorem gap {G : SimpleGraph V} {c : ℕ}
    (hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ c)
    {X Y Q : List V} {b u' a q0 q1 : V}
    (hcyc : IsCyc G (X ++ Y)) (hlen : (X ++ Y).length = c)
    (hXl : X.getLast? = some b)
    (hYh : Y.head? = some u') (hYl : Y.getLast? = some a)
    (hQh : Q.head? = some q0) (hQl : Q.getLast? = some q1)
    (hQnd : Q.Nodup) (hQch : Q.IsChain G.Adj)
    (hQdisj : ∀ z ∈ Q, z ∉ X ++ Y)
    (haq : G.Adj a q0) (hqb : G.Adj q1 b) : Q.length + 1 ≤ X.length := by
  obtain ⟨hnd, hch, hadj⟩ := hcyc
  have hbX : b ∈ X := List.mem_of_getLast? hXl
  have hQne : Q ≠ [] := by rintro rfl; simp at hQh
  have hYne : Y ≠ [] := by rintro rfl; simp at hYh
  have hnd0 : (Q ++ (X ++ Y)).Nodup :=
    List.nodup_append.2 ⟨hQnd, hnd, fun x hx y hy hxy => hQdisj x hx (hxy ▸ hy)⟩
  have hsub : (Q ++ ([b] ++ Y)).Sublist (Q ++ (X ++ Y)) :=
    (List.Sublist.refl Q).append ((List.singleton_sublist.2 hbX).append (List.Sublist.refl Y))
  have hnd1 := hnd0.sublist hsub
  have hbu' : G.Adj b u' := by
    rw [List.isChain_append] at hch
    exact hch.2.2 b hXl u' hYh
  have hch1 : (Q ++ ([b] ++ Y)).IsChain G.Adj := by
    refine chain_app hQch (chain_app (List.isChain_singleton b) hch.right_of_append
      (x := b) (y := u') (by simp) hYh hbu') hQl (y := b) (by simp) hqb
  have key : IsCyc G (Q ++ ([b] ++ Y)) :=
    cyc_mk hnd1 hch1 (getLast?_app (getLast?_app hYl)) (head?_app hQh) haq
  have hQl1 : 1 ≤ Q.length := List.length_pos_of_ne_nil hQne
  have hYl1 : 1 ≤ Y.length := List.length_pos_of_ne_nil hYne
  have h1 := hmax _ key (by simp; omega)
  simp at hlen h1
  omega

/-- common off-cycle neighbour lemma -/
theorem common_nbr {G : SimpleGraph V} {c : ℕ}
    (hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ c)
    {X Y Q : List V} {u b u' a q0 q1 w : V}
    (hcyc : IsCyc G (X ++ Y)) (hlen : (X ++ Y).length = c) (h3 : 3 ≤ c)
    (hXh : X.head? = some u) (hXl : X.getLast? = some b)
    (hYh : Y.head? = some u') (hYl : Y.getLast? = some a)
    (hQh : Q.head? = some q0) (hQl : Q.getLast? = some q1)
    (hQnd : Q.Nodup) (hQch : Q.IsChain G.Adj)
    (hQdisj : ∀ z ∈ Q, z ∉ X ++ Y)
    (haq : G.Adj a q0) (hqb : G.Adj q1 b)
    (hwL : w ∉ X ++ Y) (hwQ : w ∉ Q)
    (huw : G.Adj u w) (hwu' : G.Adj w u') : False := by
  obtain ⟨hnd, hch, hadj⟩ := hcyc
  have hnd0 : (Q ++ w :: (X ++ Y)).Nodup := by
    refine List.nodup_append.2 ⟨hQnd, List.nodup_cons.2 ⟨hwL, hnd⟩, ?_⟩
    intro x hx y hy hxy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hwQ (hxy ▸ hx)
    · exact hQdisj x hx (hxy ▸ hy)
  have hperm : (Q ++ (X.reverse ++ w :: Y)).Perm (Q ++ w :: (X ++ Y)) :=
    List.Perm.append_left Q (List.perm_middle.trans
      (List.Perm.cons w (List.Perm.append_right Y (List.reverse_perm X))))
  have hnd1 := hperm.nodup_iff.2 hnd0
  have hch1 : (Q ++ (X.reverse ++ w :: Y)).IsChain G.Adj := by
    refine chain_app hQch (chain_app (chain_rev hch.left_of_append) ?_
      (x := u) (y := w) ?_ (by simp) huw) hQl (y := b) ?_ hqb
    · exact chain_app (List.isChain_singleton w) hch.right_of_append (x := w) (y := u')
        (by simp) hYh hwu'
    · rw [List.getLast?_reverse]; exact hXh
    · apply head?_app; rw [List.head?_reverse]; exact hXl
  have hYne : Y ≠ [] := by rintro rfl; simp at hYh
  have key : IsCyc G (Q ++ (X.reverse ++ w :: Y)) := by
    refine cyc_mk hnd1 hch1 (getLast?_app (getLast?_app ?_)) (head?_app hQh) haq
    rw [List.getLast?_cons_of_ne_nil hYne]; exact hYl
  have h1 := hmax _ key (by simp at hlen ⊢; omega)
  simp at hlen h1
  omega


/-- path-list inside `H` from `v` to `w` -/
def HP (G : SimpleGraph V) (H : Finset V) (Q : List V) (v w : V) : Prop :=
  Q.Nodup ∧ Q.IsChain G.Adj ∧ Q.head? = some v ∧ Q.getLast? = some w ∧ ∀ z ∈ Q, z ∈ H

theorem HP.rev {G : SimpleGraph V} {H : Finset V} {Q : List V} {v w : V} (h : HP G H Q v w) :
    HP G H Q.reverse w v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨List.nodup_reverse.2 h1, chain_rev h2, ?_, ?_, ?_⟩
  · rw [List.head?_reverse]; exact h4
  · rw [List.getLast?_reverse]; exact h3
  · intro z hz; exact h5 z (List.mem_reverse.1 hz)

theorem HP.single {G : SimpleGraph V} {H : Finset V} {v : V} (hv : v ∈ H) : HP G H [v] v v := by
  refine ⟨List.nodup_singleton v, List.isChain_singleton v, rfl, rfl, ?_⟩
  intro z hz; rw [List.mem_singleton] at hz; rw [hz]; exact hv

theorem HP.length_pos {G : SimpleGraph V} {H : Finset V} {Q : List V} {v w : V} (h : HP G H Q v w) :
    1 ≤ Q.length := by
  obtain ⟨_, _, h3, _, _⟩ := h
  rcases Q with _ | ⟨q, Q⟩
  · simp at h3
  · simp

theorem HP.two_le {G : SimpleGraph V} {H : Finset V} {Q : List V} {v w : V} (h : HP G H Q v w)
    (hvw : v ≠ w) : 2 ≤ Q.length := by
  obtain ⟨_, _, h3, h4, _⟩ := h
  rcases Q with _ | ⟨q, _ | ⟨q', Q⟩⟩
  · simp at h3
  · simp at h3 h4; exact absurd (h3.symm.trans h4) hvw
  · simp

/-- the working context: a longest cyclic list `L` and a closed connected set `H` off `L` -/
structure Ctx (G : SimpleGraph V) (c : ℕ) (L : List V) (H : Finset V) : Prop where
  hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ c
  hcyc : IsCyc G L
  hlen : L.length = c
  h3 : 3 ≤ c
  hHL : ∀ v ∈ H, v ∉ L
  hHcl : ∀ v ∈ H, ∀ w, G.Adj v w → w ∉ L → w ∈ H
  hHconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w

/-- forward distance between two positions on a cycle of length `c` -/
def fwd (c i j : ℕ) : ℕ := if i ≤ j then j - i else j + c - i

section pos
variable [DecidableEq V]

theorem idxOf_mid {s t : List V} {a : V} (h : a ∉ s) : (s ++ a :: t).idxOf a = s.length := by
  rw [List.idxOf_append_of_notMem h]; simp

theorem gap_pos {G : SimpleGraph V} {c : ℕ} {L : List V} {H : Finset V} (ctx : Ctx G c L H)
    {a b : V} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b)
    {Q : List V} {x y : V} (hQ : HP G H Q x y) (hax : G.Adj a x) (hyb : G.Adj y b) :
    Q.length + 1 ≤ fwd c (L.idxOf a) (L.idxOf b) := by
  obtain ⟨hQnd, hQch, hQh, hQl, hQH⟩ := hQ
  have hnd := ctx.hcyc.1
  have hlen := ctx.hlen
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  have has : a ∉ s := by
    intro h
    rw [List.nodup_append] at hnd
    exact hnd.2.2 a h a (by simp) rfl
  have hat : a ∉ t := by
    intro h
    rw [List.nodup_append] at hnd
    have := hnd.2.1
    rw [List.nodup_cons] at this
    exact this.1 h
  have hia : (s ++ a :: t).idxOf a = s.length := idxOf_mid has
  have hQdisj : ∀ L' : List V, (∀ z ∈ L', z ∈ s ++ a :: t) → ∀ z ∈ Q, z ∉ L' := by
    intro L' hL' z hz hzL
    exact ctx.hHL z (hQH z hz) (hL' z hzL)
  rw [List.mem_append, List.mem_cons] at hb
  rcases hb with hb | hb | hb
  · -- b before a
    obtain ⟨s', t', rfl⟩ := List.append_of_mem hb
    have hbs' : b ∉ s' := by
      intro h
      rw [List.append_assoc, List.nodup_append] at hnd
      exact hnd.2.2 b h b (by simp) rfl
    have hib : (s' ++ b :: t' ++ a :: t).idxOf b = s'.length := by
      rw [List.append_assoc]; exact idxOf_mid hbs'
    have hcyc' : IsCyc G ((t ++ (s' ++ [b])) ++ (t' ++ [a])) := by
      have h1 : IsCyc G ((s' ++ [b]) ++ ((t' ++ [a]) ++ t)) := by
        have := ctx.hcyc; simpa using this
      have h2 := cyc_rotate h1
      have h3 : IsCyc G (((t' ++ [a]) ++ t) ++ (s' ++ [b])) := h2
      have h4 : IsCyc G ((t' ++ [a]) ++ (t ++ (s' ++ [b]))) := by simpa using h3
      exact cyc_rotate h4
    have hg := gap ctx.hmax (X := t ++ (s' ++ [b])) (Y := t' ++ [a]) (Q := Q) (b := b)
      (u' := (t' ++ [a]).head (by simp)) (a := a) (q0 := x) (q1 := y) hcyc'
      (by simp at hlen ⊢; omega) (getLast?_app (by simp)) (List.head?_eq_some_head _)
      (getLast?_app (by simp)) hQh hQl hQnd hQch
      (hQdisj _ (by intro z hz; simp at hz ⊢; tauto)) hax hyb
    rw [hia, hib]
    unfold fwd
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen hg ⊢
    split_ifs <;> omega
  · exact absurd hb.symm hab
  · -- b after a
    obtain ⟨s', t', rfl⟩ := List.append_of_mem hb
    have hbs' : b ∉ s' := by
      intro h
      rw [List.nodup_append] at hnd
      have h1 := hnd.2.1
      rw [List.nodup_cons, List.nodup_append] at h1
      exact h1.2.2.2 b h b (by simp) rfl
    have hbs : b ∉ s := by
      intro h
      rw [List.nodup_append] at hnd
      exact hnd.2.2 b h b (by simp) rfl
    have hib : (s ++ a :: (s' ++ b :: t')).idxOf b = s.length + 1 + s'.length := by
      have h1 : s ++ a :: (s' ++ b :: t') = (s ++ a :: s') ++ b :: t' := by simp
      rw [h1, idxOf_mid (by simp; exact ⟨hbs, fun h => hab h.symm, hbs'⟩)]
      simp; omega
    have hcyc' : IsCyc G ((s' ++ [b]) ++ (t' ++ (s ++ [a]))) := by
      have h1 : IsCyc G ((s ++ [a]) ++ ((s' ++ [b]) ++ t')) := by
        have := ctx.hcyc; simpa using this
      have h2 := cyc_rotate h1
      simpa using h2
    have hg := gap ctx.hmax (X := s' ++ [b]) (Y := t' ++ (s ++ [a])) (Q := Q) (b := b)
      (u' := (t' ++ (s ++ [a])).head (by simp)) (a := a) (q0 := x) (q1 := y) hcyc'
      (by simp at hlen ⊢; omega) (getLast?_app (by simp)) (List.head?_eq_some_head _)
      (getLast?_app (getLast?_app (by simp))) hQh hQl hQnd hQch
      (hQdisj _ (by intro z hz; simp at hz ⊢; tauto)) hax hyb
    rw [hia, hib]
    unfold fwd
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen hg ⊢
    split_ifs <;> omega

end pos

theorem fwd_le_of_mod_eq {c i j s s' : ℕ} (hi : i < c) (hj : j < c) (_hij : i ≠ j) (hss : s' ≤ s)
    (h : (i + s) % c = (j + s') % c) : fwd c i j ≤ s - s' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hss
  have h1 : (i + d) % c = j := by
    have h2 : (i + d + s') % c = (j + s') % c := by
      rw [← h]; congr 1; omega
    have h3 : (i + d) ≡ j [MOD c] := Nat.ModEq.add_right_cancel' s' h2
    have h4 : (i + d) % c = j % c := h3
    rw [h4, Nat.mod_eq_of_lt hj]
  unfold fwd
  by_contra hcon
  push Not at hcon
  by_cases hlt : i + d < c
  · rw [Nat.mod_eq_of_lt hlt] at h1
    split_ifs at hcon <;> omega
  · push Not at hlt
    have h5 : (i + d) % c = (i + d - c) % c := Nat.mod_eq_sub_mod hlt
    have h6 : i + d - c < c := by split_ifs at hcon <;> omega
    rw [h5, Nat.mod_eq_of_lt h6] at h1
    split_ifs at hcon <;> omega

theorem inj_count {T : Finset V} {c : ℕ} (pos : V → ℕ) (S : V → Finset ℕ)
    (hpos : ∀ a ∈ T, pos a < c)
    (hposinj : ∀ a ∈ T, ∀ a' ∈ T, pos a = pos a' → a = a')
    (hS : ∀ a ∈ T, ∀ s ∈ S a, s < c)
    (hsep : ∀ a ∈ T, ∀ a' ∈ T, a ≠ a' → ∀ s ∈ S a, ∀ s' ∈ S a', s' ≤ s →
      s - s' < fwd c (pos a) (pos a')) :
    ∑ a ∈ T, (S a).card ≤ c := by
  classical
  have hcard : (T.sigma S).card ≤ (Finset.range c).card := by
    apply Finset.card_le_card_of_injOn (fun p => (pos p.1 + p.2) % c)
    · intro p hp
      have hp' := Finset.mem_sigma.1 hp
      have hc : 0 < c := lt_of_le_of_lt (Nat.zero_le _) (hpos _ hp'.1)
      exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hc))
    · rintro ⟨a, s⟩ hp ⟨a', s'⟩ hp' heq
      have hp1 := Finset.mem_sigma.1 (Finset.mem_coe.1 hp)
      have hp2 := Finset.mem_sigma.1 (Finset.mem_coe.1 hp')
      simp only at hp1 hp2 heq
      by_cases haa : a = a'
      · subst haa
        have h3 : s ≡ s' [MOD c] := Nat.ModEq.add_left_cancel' (pos a) heq
        have h4 : s % c = s' % c := h3
        rw [Nat.mod_eq_of_lt (hS a hp1.1 s hp1.2), Nat.mod_eq_of_lt (hS a hp1.1 s' hp2.2)] at h4
        rw [h4]
      · exfalso
        have hne : pos a ≠ pos a' := fun h => haa (hposinj a hp1.1 a' hp2.1 h)
        rcases le_total s' s with hle | hle
        · have h1 := fwd_le_of_mod_eq (hpos a hp1.1) (hpos a' hp2.1) hne hle heq
          have h2 := hsep a hp1.1 a' hp2.1 haa s hp1.2 s' hp2.2 hle
          omega
        · have h1 := fwd_le_of_mod_eq (hpos a' hp2.1) (hpos a hp1.1) (Ne.symm hne) hle heq.symm
          have h2 := hsep a' hp2.1 a hp1.1 (Ne.symm haa) s' hp2.2 s hp1.2 hle
          omega
  rw [Finset.card_sigma, Finset.card_range] at hcard
  exact hcard


section arc
variable [DecidableEq V]

theorem getElem_of_idxOf_eq {l : List V} {v : V} {i : ℕ} (hi : l.idxOf v = i) (h : i < l.length) :
    l[i] = v := by
  subst hi; exact List.getElem_idxOf h

/-- pure counting on one arc -/
theorem arc_count {G : SimpleGraph V} [DecidableRel G.Adj] {A : List V} {u1 u2 u3 : V}
    (hh : A.head? = some u1)
    (hA : ∀ b (h : b + 1 < A.length), ¬ (G.Adj u3 A[b] ∧ G.Adj u1 A[b+1]))
    (hB : ∀ b (h : b + 1 < A.length), ¬ (G.Adj u2 A[b] ∧ G.Adj u3 A[b+1]))
    (hC : ∀ b (h : b + 2 < A.length), ¬ (G.Adj u2 A[b] ∧ G.Adj u1 A[b+2])) :
    (A.toFinset.filter (G.Adj u1)).card + (A.toFinset.filter (G.Adj u2)).card
      + (A.toFinset.filter (G.Adj u3)).card ≤ A.length + 1 := by
  set F1 := A.toFinset.filter (G.Adj u1) with hF1
  set F2 := A.toFinset.filter (G.Adj u2) with hF2
  set F3 := A.toFinset.filter (G.Adj u3) with hF3
  have hmem : ∀ {F : Finset V} {u : V}, F = A.toFinset.filter (G.Adj u) → ∀ v ∈ F, v ∈ A ∧ G.Adj u v := by
    intro F u hF v hv
    rw [hF, Finset.mem_filter, List.mem_toFinset] at hv
    exact hv
  have hinj : ∀ (k : ℕ) (F : Finset V), (∀ v ∈ F, v ∈ A) →
      Set.InjOn (fun v => A.idxOf v + k) (F : Set V) := by
    intro k F hF v hv w hw h
    have h' : A.idxOf v = A.idxOf w := by simpa using h
    exact (List.idxOf_inj (hF v hv)).1 h'
  set I1 := F1.image (fun v => A.idxOf v + 0) with hI1
  set I3 := F3.image (fun v => A.idxOf v + 1) with hI3
  set I2 := F2.image (fun v => A.idxOf v + 2) with hI2
  have hc1 : I1.card = F1.card := Finset.card_image_of_injOn (hinj 0 F1 (fun v hv => (hmem hF1 v hv).1))
  have hc3 : I3.card = F3.card := Finset.card_image_of_injOn (hinj 1 F3 (fun v hv => (hmem hF3 v hv).1))
  have hc2 : I2.card = F2.card := Finset.card_image_of_injOn (hinj 2 F2 (fun v hv => (hmem hF2 v hv).1))
  have hlt : ∀ v ∈ A, A.idxOf v < A.length := fun v hv => List.idxOf_lt_length_of_mem hv
  have hd13 : Disjoint I1 I3 := by
    rw [Finset.disjoint_left]
    intro i hi1 hi3
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨v', hv', hvv⟩ := Finset.mem_image.1 hi3
    have h1 := hmem hF1 v hv
    have h3 := hmem hF3 v' hv'
    have hb : A.idxOf v' + 1 < A.length := by have := hlt v h1.1; omega
    refine hA (A.idxOf v') hb ⟨?_, ?_⟩
    · rw [getElem_of_idxOf_eq rfl (by omega)]; exact h3.2
    · rw [getElem_of_idxOf_eq (v := v) (by omega) hb]; exact h1.2
  have hd12 : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨v', hv', hvv⟩ := Finset.mem_image.1 hi2
    have h1 := hmem hF1 v hv
    have h2 := hmem hF2 v' hv'
    have hb : A.idxOf v' + 2 < A.length := by have := hlt v h1.1; omega
    refine hC (A.idxOf v') hb ⟨?_, ?_⟩
    · rw [getElem_of_idxOf_eq rfl (by omega)]; exact h2.2
    · rw [getElem_of_idxOf_eq (v := v) (by omega) hb]; exact h1.2
  have hd32 : Disjoint I3 I2 := by
    rw [Finset.disjoint_left]
    intro i hi3 hi2
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi3
    obtain ⟨v', hv', hvv⟩ := Finset.mem_image.1 hi2
    have h3 := hmem hF3 v hv
    have h2 := hmem hF2 v' hv'
    have hb : A.idxOf v' + 1 < A.length := by have := hlt v h3.1; omega
    refine hB (A.idxOf v') hb ⟨?_, ?_⟩
    · rw [getElem_of_idxOf_eq rfl (by omega)]; exact h2.2
    · rw [getElem_of_idxOf_eq (v := v) (by omega) hb]; exact h3.2
  have hsub : I1 ∪ I3 ∪ I2 ⊆ Finset.Icc 1 (A.length + 1) := by
    intro i hi
    rw [Finset.mem_Icc]
    rcases Finset.mem_union.1 hi with hi | hi
    · rcases Finset.mem_union.1 hi with hi | hi
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
        have h1 := hmem hF1 v hv
        have := hlt v h1.1
        have hne : v ≠ u1 := fun h => G.loopless.irrefl u1 (h ▸ h1.2)
        have hpos : A.idxOf v ≠ 0 := by
          intro h0
          rcases A with _ | ⟨x, A'⟩
          · simp at hh
          · simp at hh
            subst hh
            rw [List.idxOf_cons_ne _ (Ne.symm hne)] at h0
            exact Nat.succ_ne_zero _ h0
        omega
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
        have := hlt v (hmem hF3 v hv).1
        omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
      have := hlt v (hmem hF2 v hv).1
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hd12, hd32⟩),
    Finset.card_union_of_disjoint hd13, Nat.card_Icc, hc1, hc2, hc3] at hcard
  omega

end arc



/-- `a` and `a'` are joined through `H` by a path-list with at least `k` vertices -/
def Good (G : SimpleGraph V) (H : Finset V) (k : ℕ) (a a' : V) : Prop :=
  ∃ (Q : List V) (x y : V), HP G H Q x y ∧ k ≤ Q.length ∧ G.Adj a x ∧ G.Adj y a'

theorem Good.symm {G : SimpleGraph V} {H : Finset V} {k : ℕ} {a a' : V} (h : Good G H k a a') :
    Good G H k a' a := by
  obtain ⟨Q, x, y, hQ, hk, hax, hya⟩ := h
  exact ⟨Q.reverse, y, x, hQ.rev, by simpa using hk, hya.symm, hax.symm⟩

theorem Good.mono {G : SimpleGraph V} {H : Finset V} {k k' : ℕ} {a a' : V} (h : Good G H k a a')
    (hk : k' ≤ k) : Good G H k' a a' := by
  obtain ⟨Q, x, y, hQ, hk', hax, hya⟩ := h
  exact ⟨Q, x, y, hQ, le_trans hk hk', hax, hya⟩

section arc2
variable [DecidableEq V]

theorem take_getLast? {l : List V} {b : ℕ} (h : b < l.length) :
    (l.take (b + 1)).getLast? = some l[b] := by
  rw [List.getLast?_take]
  simp [List.getElem?_eq_getElem h]

theorem drop_head? {l : List V} {b : ℕ} (h : b < l.length) :
    (l.drop b).head? = some l[b] := by
  rw [List.head?_drop, List.getElem?_eq_getElem h]

theorem take_head? {l : List V} {b : ℕ} {u : V} (h : l.head? = some u) :
    (l.take (b + 1)).head? = some u := by
  rw [List.head?_take]; simp [h]

theorem drop_getLast? {l : List V} {b : ℕ} {a : V} (hb : b < l.length) (h : l.getLast? = some a) :
    (l.drop b).getLast? = some a := by
  rw [List.getLast?_drop]; simp [h]; omega

/-- the count on the middle arc of a cycle split in three arcs -/
theorem arc_bound {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ} {H : Finset V}
    (hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ c) (h3 : 3 ≤ c)
    {A1 A2 A3 : List V} {a1 a2 a3 u1 u2 u3 : V}
    (hcyc : IsCyc G (A1 ++ (A2 ++ A3))) (hlen : (A1 ++ (A2 ++ A3)).length = c)
    (hHL : ∀ v ∈ H, v ∉ A1 ++ (A2 ++ A3))
    (h1h : A1.head? = some u3) (h1l : A1.getLast? = some a1)
    (h2h : A2.head? = some u1) (h2l : A2.getLast? = some a2)
    (h3h : A3.head? = some u2) (h3l : A3.getLast? = some a3)
    (g31 : Good G H 1 a3 a1) (g23 : Good G H 1 a2 a3) (g21 : Good G H 2 a2 a1) :
    (A2.toFinset.filter (G.Adj u1)).card + (A2.toFinset.filter (G.Adj u2)).card
      + (A2.toFinset.filter (G.Adj u3)).card ≤ A2.length + 1 := by
  have hrot : IsCyc G (A3 ++ (A1 ++ A2)) := by
    have h1 : IsCyc G ((A1 ++ A2) ++ A3) := by simpa using hcyc
    exact cyc_rotate h1
  have hlen' : (A3 ++ (A1 ++ A2)).length = c := by simp at hlen ⊢; omega
  apply arc_count h2h
  · -- rule A
    intro b hb ⟨h3v, h1w⟩
    obtain ⟨Q, x, y, hQ, hk, hax, hya⟩ := g31
    have hsplit : A2 = A2.take (b + 1) ++ A2.drop (b + 1) := (List.take_append_drop _ _).symm
    have hcyc' : IsCyc G (A1 ++ (A2.take (b + 1) ++ ([] ++ (A2.drop (b + 1) ++ A3)))) := by
      have : A1 ++ (A2.take (b + 1) ++ ([] ++ (A2.drop (b + 1) ++ A3))) = A1 ++ (A2 ++ A3) := by
        simp [← List.append_assoc]
      rw [this]; exact hcyc
    refine crossing hmax hcyc' ?_ h3 h1h h1l (take_head? h2h) (take_getLast? (by omega))
      (head?_app (drop_head? hb)) (getLast?_app h3l) hQ.2.2.1 hQ.2.2.2.1 hQ.1 hQ.2.1 ?_ hax hya
      (by simp only [List.length_nil]; omega) h3v h1w
    · simp at hlen ⊢; omega
    · intro z hz hzL
      refine hHL z (hQ.2.2.2.2 z hz) ?_
      simp only [List.nil_append, List.mem_append] at hzL ⊢
      rcases hzL with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_of_mem_take h))
      · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
      · exact Or.inr (Or.inr h)
  · -- rule B
    intro b hb ⟨h2v, h3w⟩
    obtain ⟨Q, x, y, hQ, hk, hax, hya⟩ := g23
    have hcyc' : IsCyc G (A3 ++ ((A1 ++ A2.take (b + 1)) ++ ([] ++ A2.drop (b + 1)))) := by
      have : A3 ++ ((A1 ++ A2.take (b + 1)) ++ ([] ++ A2.drop (b + 1))) = A3 ++ (A1 ++ A2) := by
        simp
      rw [this]; exact hrot
    refine crossing hmax hcyc' ?_ h3 h3h h3l (head?_app h1h) (getLast?_app (take_getLast? (by omega)))
      (drop_head? hb) (drop_getLast? hb h2l) hQ.2.2.1 hQ.2.2.2.1 hQ.1 hQ.2.1 ?_ hax hya
      (by simp only [List.length_nil]; omega) h2v h3w
    · simp at hlen ⊢; omega
    · intro z hz hzL
      refine hHL z (hQ.2.2.2.2 z hz) ?_
      simp only [List.nil_append, List.mem_append] at hzL ⊢
      rcases hzL with h | (h | h) | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_of_mem_take h))
      · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
  · -- rule C
    intro b hb ⟨h2v, h1w⟩
    obtain ⟨Q, x, y, hQ, hk, hax, hya⟩ := g21
    have hd : A2.drop (b + 1) = A2[b + 1] :: A2.drop (b + 2) := List.drop_eq_getElem_cons (by omega)
    have hcyc' : IsCyc G ((A3 ++ A1) ++ (A2.take (b + 1) ++ ([A2[b + 1]] ++ A2.drop (b + 2)))) := by
      have : (A3 ++ A1) ++ (A2.take (b + 1) ++ ([A2[b + 1]] ++ A2.drop (b + 2))) = A3 ++ (A1 ++ A2) := by
        have h1 : [A2[b + 1]] ++ A2.drop (b + 2) = A2.drop (b + 1) := by rw [hd]; rfl
        rw [h1, List.take_append_drop, List.append_assoc]
      rw [this]; exact hrot
    refine crossing hmax hcyc' ?_ h3 (head?_app h3h) (getLast?_app h1l) (take_head? h2h)
      (take_getLast? (by omega)) (drop_head? hb) (drop_getLast? hb h2l) hQ.2.2.1 hQ.2.2.2.1 hQ.1 hQ.2.1
      ?_ hax hya (by simp only [List.length_singleton]; omega) h2v h1w
    · simp at hlen ⊢; omega
    · intro z hz hzL
      refine hHL z (hQ.2.2.2.2 z hz) ?_
      simp only [List.mem_append, List.mem_singleton] at hzL ⊢
      rcases hzL with (h | h) | h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_of_mem_take h))
      · exact Or.inr (Or.inl (h ▸ List.getElem_mem _))
      · exact Or.inr (Or.inl (List.mem_of_mem_drop h))

end arc2


section deg
variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- the successor of an attachment vertex has no neighbour in `H` -/
theorem succ_no_H {G : SimpleGraph V} {c : ℕ} {H : Finset V}
    (hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ c)
    {B D : List V} {u a y : V}
    (hcyc : IsCyc G (B ++ D)) (hlen : (B ++ D).length = c)
    (hHL : ∀ v ∈ H, v ∉ B ++ D)
    (hconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w)
    (hDh : D.head? = some u) (hBl : B.getLast? = some a) (hy : y ∈ H) (hay : G.Adj a y) :
    ∀ w ∈ H, ¬ G.Adj u w := by
  intro w hw huw
  obtain ⟨Q, hQ⟩ := hconn y hy w hw
  rcases D with _ | ⟨u', D'⟩
  · simp at hDh
  obtain rfl : u' = u := by simpa using hDh
  have hBne : B ≠ [] := by rintro rfl; simp at hBl
  have hcyc' : IsCyc G ([u'] ++ (D' ++ B)) := by
    have := cyc_rotate hcyc; simpa using this
  have hg := gap hmax (X := [u']) (Y := D' ++ B) (Q := Q) (b := u')
    (u' := (D' ++ B).head (by simp [hBne])) (a := a) (q0 := y) (q1 := w) hcyc'
    (by simp at hlen ⊢; omega) (by simp) (List.head?_eq_some_head _) (getLast?_app hBl)
    hQ.2.2.1 hQ.2.2.2.1 hQ.1 hQ.2.1 ?_ hay huw.symm
  · have := hQ.length_pos
    simp only [List.length_singleton] at hg
    omega
  · intro z hz hzL
    refine hHL z (hQ.2.2.2.2 z hz) ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hzL ⊢
    tauto

theorem card_filter_append {G : SimpleGraph V} [DecidableRel G.Adj] {A B : List V} (u : V)
    (hnd : (A ++ B).Nodup) :
    ((A ++ B).toFinset.filter (G.Adj u)).card
      = (A.toFinset.filter (G.Adj u)).card + (B.toFinset.filter (G.Adj u)).card := by
  rw [List.toFinset_append, Finset.filter_union, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [Finset.mem_filter, List.mem_toFinset] at hv hv'
  exact (List.nodup_append.1 hnd).2.2 v hv.1 v hv'.1 rfl

/-- the degree sum of three successors -/
theorem three_succ {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ} {H : Finset V}
    (hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ c) (h3 : 3 ≤ c)
    {A1 A2 A3 : List V} {a1 a2 a3 u1 u2 u3 : V}
    (hcyc : IsCyc G (A1 ++ (A2 ++ A3))) (hlen : (A1 ++ (A2 ++ A3)).length = c)
    (hHL : ∀ v ∈ H, v ∉ A1 ++ (A2 ++ A3))
    (hconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w)
    (h1h : A1.head? = some u3) (h1l : A1.getLast? = some a1)
    (h2h : A2.head? = some u1) (h2l : A2.getLast? = some a2)
    (h3h : A3.head? = some u2) (h3l : A3.getLast? = some a3)
    (g12 : Good G H 2 a1 a2) (g23 : Good G H 2 a2 a3) (g31 : Good G H 2 a3 a1) :
    G.degree u1 + G.degree u2 + G.degree u3 + H.card ≤ Fintype.card V + 3 := by
  have hnd := hcyc.1
  have hrot2 : IsCyc G (A2 ++ (A3 ++ A1)) := by
    have := cyc_rotate hcyc; simpa using this
  have hrot3 : IsCyc G (A3 ++ (A1 ++ A2)) := by
    have h1 : IsCyc G ((A1 ++ A2) ++ A3) := by simpa using hcyc
    exact cyc_rotate h1
  have hlen2 : (A2 ++ (A3 ++ A1)).length = c := by simp at hlen ⊢; omega
  have hlen3 : (A3 ++ (A1 ++ A2)).length = c := by simp at hlen ⊢; omega
  have hHL2 : ∀ v ∈ H, v ∉ A2 ++ (A3 ++ A1) := by
    intro v hv hvL; apply hHL v hv; simp only [List.mem_append] at hvL ⊢; tauto
  have hHL3 : ∀ v ∈ H, v ∉ A3 ++ (A1 ++ A2) := by
    intro v hv hvL; apply hHL v hv; simp only [List.mem_append] at hvL ⊢; tauto
  -- arc bounds
  have hb2 := arc_bound hmax h3 hcyc hlen hHL h1h h1l h2h h2l h3h h3l
    (g31.mono (by norm_num)) (g23.mono (by norm_num)) g12.symm
  have hb3 := arc_bound hmax h3 hrot2 hlen2 hHL2 h2h h2l h3h h3l h1h h1l
    (g12.mono (by norm_num)) (g31.mono (by norm_num)) g23.symm
  have hb1 := arc_bound hmax h3 hrot3 hlen3 hHL3 h3h h3l h1h h1l h2h h2l
    (g23.mono (by norm_num)) (g12.mono (by norm_num)) g31.symm
  -- H-neighbours of the attachment vertices
  obtain ⟨Q12, x12, y12, hQ12, hk12, hax12, hya12⟩ := g12
  obtain ⟨Q23, x23, y23, hQ23, hk23, hax23, hya23⟩ := g23
  obtain ⟨Q31, x31, y31, hQ31, hk31, hax31, hya31⟩ := g31
  have hx12 : x12 ∈ H := hQ12.2.2.2.2 _ (List.mem_of_head? hQ12.2.2.1)
  have hx23 : x23 ∈ H := hQ23.2.2.2.2 _ (List.mem_of_head? hQ23.2.2.1)
  have hx31 : x31 ∈ H := hQ31.2.2.2.2 _ (List.mem_of_head? hQ31.2.2.1)
  have hno1 : ∀ w ∈ H, ¬ G.Adj u1 w :=
    succ_no_H hmax hcyc hlen hHL hconn (head?_app h2h) h1l hx12 hax12
  have hno2 : ∀ w ∈ H, ¬ G.Adj u2 w :=
    succ_no_H hmax hrot2 hlen2 hHL2 hconn (head?_app h3h) h2l hx23 hax23
  have hno3 : ∀ w ∈ H, ¬ G.Adj u3 w :=
    succ_no_H hmax hrot3 hlen3 hHL3 hconn (head?_app h1h) h3l hx31 hax31
  -- off-cycle neighbourhoods
  set Lf := (A1 ++ (A2 ++ A3)).toFinset with hLf
  have hLfc : Lf.card = c := by rw [hLf, List.toFinset_card_of_nodup hnd, hlen]
  set O1 := (Finset.univ.filter (G.Adj u1)).filter (fun v => v ∉ Lf) with hO1
  set O2 := (Finset.univ.filter (G.Adj u2)).filter (fun v => v ∉ Lf) with hO2
  set O3 := (Finset.univ.filter (G.Adj u3)).filter (fun v => v ∉ Lf) with hO3
  have hdeg : ∀ u : V, G.degree u = (Lf.filter (G.Adj u)).card
      + ((Finset.univ.filter (G.Adj u)).filter (fun v => v ∉ Lf)).card := by
    intro u
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter,
      ← Finset.card_filter_add_card_filter_not (fun v => v ∈ Lf)]
    congr 2
    ext v; simp [and_comm]
  have hsplit : ∀ u : V, (Lf.filter (G.Adj u)).card = (A1.toFinset.filter (G.Adj u)).card
      + (A2.toFinset.filter (G.Adj u)).card + (A3.toFinset.filter (G.Adj u)).card := by
    intro u
    rw [hLf, card_filter_append u hnd, card_filter_append u (List.nodup_append.1 hnd).2.1]
    omega
  have hmemO : ∀ {u v : V}, v ∈ (Finset.univ.filter (G.Adj u)).filter (fun v => v ∉ Lf) ↔
      G.Adj u v ∧ v ∉ A1 ++ (A2 ++ A3) := by
    intro u v; simp [hLf]
  have hd12 : Disjoint O1 O2 := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [hO1, hmemO] at hw1
    rw [hO2, hmemO] at hw2
    refine common_nbr hmax hrot2 hlen2 h3 h2h h2l (head?_app h3h) (getLast?_app h1l)
      hQ12.2.2.1 hQ12.2.2.2.1 hQ12.1 hQ12.2.1 ?_ hax12 hya12 ?_ ?_ hw1.1 hw2.1.symm
    · intro z hz; exact hHL2 z (hQ12.2.2.2.2 z hz)
    · intro h; apply hw1.2; simp only [List.mem_append] at h ⊢; tauto
    · intro h; exact hno1 w (hQ12.2.2.2.2 w h) hw1.1
  have hd23 : Disjoint O2 O3 := by
    rw [Finset.disjoint_left]
    intro w hw2 hw3
    rw [hO2, hmemO] at hw2
    rw [hO3, hmemO] at hw3
    refine common_nbr hmax hrot3 hlen3 h3 h3h h3l (head?_app h1h) (getLast?_app h2l)
      hQ23.2.2.1 hQ23.2.2.2.1 hQ23.1 hQ23.2.1 ?_ hax23 hya23 ?_ ?_ hw2.1 hw3.1.symm
    · intro z hz; exact hHL3 z (hQ23.2.2.2.2 z hz)
    · intro h; apply hw2.2; simp only [List.mem_append] at h ⊢; tauto
    · intro h; exact hno2 w (hQ23.2.2.2.2 w h) hw2.1
  have hd31 : Disjoint O3 O1 := by
    rw [Finset.disjoint_left]
    intro w hw3 hw1
    rw [hO3, hmemO] at hw3
    rw [hO1, hmemO] at hw1
    refine common_nbr hmax hcyc hlen h3 h1h h1l (head?_app h2h) (getLast?_app h3l)
      hQ31.2.2.1 hQ31.2.2.2.1 hQ31.1 hQ31.2.1 ?_ hax31 hya31 hw3.2 ?_ hw3.1 hw1.1.symm
    · intro z hz; exact hHL z (hQ31.2.2.2.2 z hz)
    · intro h; exact hno3 w (hQ31.2.2.2.2 w h) hw3.1
  have hOsub : O1 ∪ O2 ∪ O3 ∪ (Lf ∪ H) ⊆ Finset.univ := Finset.subset_univ _
  have hdisjO : Disjoint (O1 ∪ O2 ∪ O3) (Lf ∪ H) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    have hwO : (G.Adj u1 w ∨ G.Adj u2 w ∨ G.Adj u3 w) ∧ w ∉ A1 ++ (A2 ++ A3) := by
      rcases Finset.mem_union.1 hw with hw | hw
      · rcases Finset.mem_union.1 hw with hw | hw
        · rw [hO1, hmemO] at hw; exact ⟨Or.inl hw.1, hw.2⟩
        · rw [hO2, hmemO] at hw; exact ⟨Or.inr (Or.inl hw.1), hw.2⟩
      · rw [hO3, hmemO] at hw; exact ⟨Or.inr (Or.inr hw.1), hw.2⟩
    rcases Finset.mem_union.1 hw' with hw' | hw'
    · rw [hLf, List.mem_toFinset] at hw'; exact hwO.2 hw'
    · rcases hwO.1 with h | h | h
      · exact hno1 w hw' h
      · exact hno2 w hw' h
      · exact hno3 w hw' h
  have hdisjLH : Disjoint Lf H := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [hLf, List.mem_toFinset] at hw
    exact hHL w hw' hw
  have hcard := Finset.card_le_card hOsub
  rw [Finset.card_union_of_disjoint hdisjO, Finset.card_union_of_disjoint hdisjLH,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hd31.symm, hd23⟩),
    Finset.card_union_of_disjoint hd12, Finset.card_univ, hLfc] at hcard
  have e1 := hdeg u1
  have e2 := hdeg u2
  have e3 := hdeg u3
  have s1 := hsplit u1
  have s2 := hsplit u2
  have s3 := hsplit u3
  simp only [List.length_append] at hlen
  rw [← hO1] at e1
  rw [← hO2] at e2
  rw [← hO3] at e3
  omega

end deg


/-- three distinct vertices of a cyclic list cut it into three arcs -/
theorem split3 {G : SimpleGraph V} {L : List V} (hcyc : IsCyc G L) {a1 a2 a3 : V}
    (h1 : a1 ∈ L) (h2 : a2 ∈ L) (h3 : a3 ∈ L) (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3) :
    ∃ A1 A2 A3 : List V, IsCyc G (A1 ++ (A2 ++ A3)) ∧ (A1 ++ (A2 ++ A3)).length = L.length ∧
      (∀ z, z ∈ A1 ++ (A2 ++ A3) → z ∈ L) ∧ A1.getLast? = some a1 ∧
      ((A2.getLast? = some a2 ∧ A3.getLast? = some a3) ∨
        (A2.getLast? = some a3 ∧ A3.getLast? = some a2)) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h1
  have hM : IsCyc G ((t ++ s) ++ [a1]) := by
    have h := cyc_rotate hcyc
    have h' : IsCyc G ([a1] ++ (t ++ s)) := by simpa using h
    exact cyc_rotate h'
  have h2' : a2 ∈ t ++ s := by
    simp only [List.mem_append, List.mem_cons] at h2 ⊢
    rcases h2 with h | h | h
    · exact Or.inr h
    · exact absurd h.symm h12
    · exact Or.inl h
  have h3' : a3 ∈ t ++ s := by
    simp only [List.mem_append, List.mem_cons] at h3 ⊢
    rcases h3 with h | h | h
    · exact Or.inr h
    · exact absurd h.symm h13
    · exact Or.inl h
  obtain ⟨m1, m2, hm⟩ := List.append_of_mem h2'
  have hmemts : ∀ z, z ∈ t ++ s → z ∈ s ++ a1 :: t := by
    intro z hz
    simp only [List.mem_append, List.mem_cons] at hz ⊢
    tauto
  rw [hm] at hM h3'
  have hlen0 : (t ++ s).length = (m1 ++ a2 :: m2).length := congrArg List.length hm
  rw [List.mem_append, List.mem_cons] at h3'
  rcases h3' with h | h | h
  · -- a3 before a2
    obtain ⟨m3, m4, rfl⟩ := List.append_of_mem h
    refine ⟨m2 ++ [a1], m3 ++ [a3], m4 ++ [a2], ?_, ?_, ?_, getLast?_app (by simp),
      Or.inr ⟨getLast?_app (by simp), getLast?_app (by simp)⟩⟩
    · have h4 : IsCyc G (((m3 ++ [a3]) ++ (m4 ++ [a2])) ++ (m2 ++ [a1])) := by simpa using hM
      exact cyc_rotate h4
    · simp only [List.length_append, List.length_cons, List.length_nil] at hlen0 ⊢
      omega
    · intro z hz
      have : z ∈ t ++ s ∨ z = a1 := by
        rw [hm]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        tauto
      rcases this with h5 | h5
      · exact hmemts z h5
      · subst h5; simp
  · exact absurd h.symm h23
  · -- a3 after a2
    obtain ⟨m3, m4, rfl⟩ := List.append_of_mem h
    refine ⟨m4 ++ [a1], m1 ++ [a2], m3 ++ [a3], ?_, ?_, ?_, getLast?_app (by simp),
      Or.inl ⟨getLast?_app (by simp), getLast?_app (by simp)⟩⟩
    · have h4 : IsCyc G (((m1 ++ [a2]) ++ (m3 ++ [a3])) ++ (m4 ++ [a1])) := by simpa using hM
      exact cyc_rotate h4
    · simp only [List.length_append, List.length_cons, List.length_nil] at hlen0 ⊢
      omega
    · intro z hz
      have : z ∈ t ++ s ∨ z = a1 := by
        rw [hm]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        tauto
      rcases this with h5 | h5
      · exact hmemts z h5
      · subst h5; simp

theorem good_of_far {G : SimpleGraph V} {H : Finset V}
    (hconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w) {a a' x x' : V} (hx : x ∈ H) (hx' : x' ∈ H)
    (hne : x ≠ x') (hax : G.Adj a x) (ha'x' : G.Adj a' x') : Good G H 2 a a' := by
  obtain ⟨Q, hQ⟩ := hconn x hx x' hx'
  exact ⟨Q, x, x', hQ, hQ.two_le hne, hax, ha'x'.symm⟩

theorem good_of_rich {G : SimpleGraph V} {H : Finset V}
    (hconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w) {a a' x x' y : V} (hx : x ∈ H) (hx' : x' ∈ H)
    (hy : y ∈ H) (hne : x ≠ x') (hax : G.Adj a x) (hax' : G.Adj a x') (ha'y : G.Adj a' y) :
    Good G H 2 a a' := by
  by_cases h : x = y
  · exact good_of_far hconn hx' hy (fun h' => hne (h.trans h'.symm)) hax' ha'y
  · exact good_of_far hconn hx hy h hax ha'y

section triple
variable [DecidableEq V]

/-- a triple of attachment vertices which are pairwise joined through `H` by lists of length ≥ 2 -/
def Triple (G : SimpleGraph V) (L : List V) (H : Finset V) : Prop :=
  ∃ a1 a2 a3 : V, a1 ∈ L ∧ a2 ∈ L ∧ a3 ∈ L ∧ a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3 ∧
    Good G H 2 a1 a2 ∧ Good G H 2 a1 a3 ∧ Good G H 2 a2 a3

theorem rich_triple {G : SimpleGraph V} {L : List V} {H : Finset V}
    (hconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w)
    (hK : ∀ S : Finset V, S.card ≤ 2 → ∃ x ∈ H, ∃ a ∈ L, x ∉ S ∧ a ∉ S ∧ G.Adj a x)
    {a1 a2 x1 x3 x2 : V} (ha1 : a1 ∈ L) (ha2 : a2 ∈ L) (h12 : a1 ≠ a2)
    (hx1 : x1 ∈ H) (hx3 : x3 ∈ H) (hx2 : x2 ∈ H) (h13 : x1 ≠ x3)
    (e1 : G.Adj a1 x1) (e3 : G.Adj a1 x3) (e2 : G.Adj a2 x2) : Triple G L H := by
  obtain ⟨x4, hx4, a4, ha4, hx4S, ha4S, e4⟩ := hK {a1, x2} (Finset.card_le_two)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx4S ha4S
  by_cases h42 : a4 = a2
  · subst h42
    obtain ⟨x5, hx5, a5, ha5, hx5S, ha5S, e5⟩ := hK {a1, a4} (Finset.card_le_two)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx5S ha5S
    exact ⟨a1, a4, a5, ha1, ha2, ha5, h12, Ne.symm ha5S.1, Ne.symm ha5S.2,
      good_of_rich hconn hx1 hx3 hx2 h13 e1 e3 e2,
      good_of_rich hconn hx1 hx3 hx5 h13 e1 e3 e5,
      good_of_rich hconn hx2 hx4 hx5 (Ne.symm hx4S.2) e2 e4 e5⟩
  · exact ⟨a1, a2, a4, ha1, ha2, ha4, h12, Ne.symm ha4S.1, Ne.symm h42,
      good_of_rich hconn hx1 hx3 hx2 h13 e1 e3 e2,
      good_of_rich hconn hx1 hx3 hx4 h13 e1 e3 e4,
      good_of_far hconn hx2 hx4 (Ne.symm hx4S.2) e2 e4⟩

theorem good_triple {G : SimpleGraph V} {L : List V} {H : Finset V}
    (hconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w)
    (hK : ∀ S : Finset V, S.card ≤ 2 → ∃ x ∈ H, ∃ a ∈ L, x ∉ S ∧ a ∉ S ∧ G.Adj a x) :
    Triple G L H := by
  obtain ⟨x1, hx1, a1, ha1, -, -, e1⟩ := hK ∅ (by simp)
  obtain ⟨x2, hx2, a2, ha2, hx2S, ha2S, e2⟩ := hK {x1, a1} (Finset.card_le_two)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx2S ha2S
  obtain ⟨x3, hx3, a3, ha3, hx3S, ha3S, e3⟩ := hK {x1, x2} (Finset.card_le_two)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx3S ha3S
  have h12 : a1 ≠ a2 := Ne.symm ha2S.2
  by_cases h31 : a3 = a1
  · subst h31
    exact rich_triple hconn hK ha1 ha2 h12 hx1 hx3 hx2 (Ne.symm hx3S.1) e1 e3 e2
  by_cases h32 : a3 = a2
  · subst h32
    exact rich_triple hconn hK ha2 ha1 (Ne.symm h12) hx2 hx3 hx1 (Ne.symm hx3S.2) e2 e3 e1
  exact ⟨a1, a2, a3, ha1, ha2, ha3, h12, Ne.symm h31, Ne.symm h32,
    good_of_far hconn hx1 hx2 (Ne.symm hx2S.1) e1 e2,
    good_of_far hconn hx1 hx3 (Ne.symm hx3S.1) e1 e3,
    good_of_far hconn hx2 hx3 (Ne.symm hx3S.2) e2 e3⟩

end triple

section hbound
variable [Fintype V] [DecidableEq V]

/-- Corollary 1: three successors force `H` to be small -/
theorem h_bound {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ} {L : List V} {H : Finset V}
    (ctx : Ctx G c L H)
    (hK : ∀ S : Finset V, S.card ≤ 2 → ∃ x ∈ H, ∃ a ∈ L, x ∉ S ∧ a ∉ S ∧ G.Adj a x) :
    3 * G.minDegree + H.card ≤ Fintype.card V + 3 := by
  obtain ⟨a1, a2, a3, ha1, ha2, ha3, h12, h13, h23, g12, g13, g23⟩ := good_triple ctx.hHconn hK
  obtain ⟨A1, A2, A3, hcyc, hlen, hmem, hl1, hcase⟩ := split3 ctx.hcyc ha1 ha2 ha3 h12 h13 h23
  have hHL : ∀ v ∈ H, v ∉ A1 ++ (A2 ++ A3) := fun v hv hvL => ctx.hHL v hv (hmem v hvL)
  have hlen' : (A1 ++ (A2 ++ A3)).length = c := hlen.trans ctx.hlen
  have hne : ∀ {A : List V} {a : V}, A.getLast? = some a → A ≠ [] := by
    rintro A a h rfl; simp at h
  have hd1 := G.minDegree_le_degree
  rcases hcase with ⟨hl2, hl3⟩ | ⟨hl2, hl3⟩
  · have := three_succ ctx.hmax ctx.h3 hcyc hlen' hHL ctx.hHconn
      (List.head?_eq_some_head (hne hl1)) hl1 (List.head?_eq_some_head (hne hl2)) hl2
      (List.head?_eq_some_head (hne hl3)) hl3 g12 g23 g13.symm
    have e1 := hd1 (A2.head (hne hl2))
    have e2 := hd1 (A3.head (hne hl3))
    have e3 := hd1 (A1.head (hne hl1))
    omega
  · have := three_succ ctx.hmax ctx.h3 hcyc hlen' hHL ctx.hHconn
      (List.head?_eq_some_head (hne hl1)) hl1 (List.head?_eq_some_head (hne hl2)) hl2
      (List.head?_eq_some_head (hne hl3)) hl3 g13 g23.symm g12.symm
    have e1 := hd1 (A2.head (hne hl2))
    have e2 := hd1 (A3.head (hne hl3))
    have e3 := hd1 (A1.head (hne hl1))
    omega

end hbound


/-- a list of distinct vertices of `H` forming a chain -/
def HL (G : SimpleGraph V) (H : Finset V) (Q : List V) : Prop :=
  Q.Nodup ∧ Q.IsChain G.Adj ∧ ∀ z ∈ Q, z ∈ H

theorem chain_cross {R : V → V → Prop} {S : V → Prop} : ∀ (Q : List V) (a b : V), Q.IsChain R →
    Q.head? = some a → Q.getLast? = some b → ¬ S a → S b →
    ∃ q q', q ∈ Q ∧ q' ∈ Q ∧ R q q' ∧ ¬ S q ∧ S q'
  | [], a, b, _, hh, _, _, _ => by simp at hh
  | [a'], a, b, _, hh, hl, hna, hb => by
    simp at hh hl; subst hh; subst hl; exact absurd hb hna
  | a' :: q' :: Q', a, b, hch, hh, hl, hna, hb => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rw [List.isChain_cons_cons] at hch
    by_cases hq : S q'
    · exact ⟨a', q', by simp, by simp, hch.1, hna, hq⟩
    · have hl' : (q' :: Q').getLast? = some b := by
        rw [List.getLast?_cons_of_ne_nil (by simp)] at hl; exact hl
      obtain ⟨q, q'', h1, h2, h3, h4, h5⟩ := chain_cross (q' :: Q') q' b hch.2 (by simp) hl' hq hb
      exact ⟨q, q'', List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3, h4, h5⟩

section longest
variable [DecidableEq V]

theorem HL.length_le {G : SimpleGraph V} {H : Finset V} {Q : List V} (h : HL G H Q) :
    Q.length ≤ H.card := by
  rw [← List.toFinset_card_of_nodup h.1]
  apply Finset.card_le_card
  intro z hz
  exact h.2.2 z (List.mem_toFinset.1 hz)

theorem exists_longest {G : SimpleGraph V} {H : Finset V} {Q0 : List V} (h0 : HL G H Q0) :
    ∃ Q, HL G H Q ∧ Q0.length ≤ Q.length ∧ ∀ Q', HL G H Q' → Q'.length ≤ Q.length := by
  classical
  let P : ℕ → Prop := fun m => ∃ Q, HL G H Q ∧ Q.length = m
  have hP0 : P Q0.length := ⟨Q0, h0, rfl⟩
  obtain ⟨Q, hQ, hQlen⟩ := Nat.findGreatest_spec (P := P) h0.length_le hP0
  refine ⟨Q, hQ, ?_, ?_⟩
  · rw [hQlen]; exact Nat.le_findGreatest h0.length_le hP0
  · intro Q' hQ'
    rw [hQlen]; exact Nat.le_findGreatest hQ'.length_le ⟨Q', hQ', rfl⟩

theorem deg_H [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ} {L : List V}
    {H : Finset V} (ctx : Ctx G c L H) {v : V} (hv : v ∈ H) :
    G.degree v ≤ (H.filter (G.Adj v)).card + (L.toFinset.filter (G.Adj v)).card := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro w hw
  rw [Finset.mem_filter] at hw
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, List.mem_toFinset]
  by_cases hwL : w ∈ L
  · exact Or.inr ⟨hwL, hw.2⟩
  · exact Or.inl ⟨ctx.hHcl v hv w hw.2 hwL, hw.2⟩

theorem dH_lt {G : SimpleGraph V} [DecidableRel G.Adj] {H : Finset V} {v : V} (hv : v ∈ H) :
    (H.filter (G.Adj v)).card + 1 ≤ H.card := by
  have hsub : H.filter (G.Adj v) ⊆ H.erase v := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_erase]
    exact ⟨fun h => G.loopless.irrefl v (h ▸ hw.2), hw.1⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at h1
  have h2 : 0 < H.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

theorem fwd_lt {c i j : ℕ} (hi : i < c) (hj : j < c) : fwd c i j < c := by
  unfold fwd; split_ifs <;> omega

theorem getLast?_append_cons_of_mem {E F : List V} {v b : V} (h : b ∈ F.getLast?) :
    (E ++ v :: F).getLast? = some b := by
  have hF : F ≠ [] := by rintro rfl; simp at h
  apply getLast?_app
  rw [List.getLast?_cons_of_ne_nil hF]
  exact h

/-- Posa: the ends of a longest list in `H` have few neighbours, or the list spans `H` -/
theorem posa {G : SimpleGraph V} [DecidableRel G.Adj] {H : Finset V}
    (hconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w) {Pst : List V} {x y : V}
    (hP : HP G H Pst x y) (hmaxP : ∀ Q', HL G H Q' → Q'.length ≤ Pst.length) :
    (H.filter (G.Adj x)).card + (H.filter (G.Adj y)).card + 1 ≤ Pst.length ∨ ∀ z ∈ H, z ∈ Pst := by
  obtain ⟨hnd, hch, hh, hl, hH⟩ := hP
  have hxP : x ∈ Pst := List.mem_of_head? hh
  have hyP : y ∈ Pst := List.mem_of_getLast? hl
  -- neighbours of the ends lie on the list
  have hxN : ∀ w ∈ H, G.Adj x w → w ∈ Pst := by
    intro w hw hxw
    by_contra hwP
    have hHL : HL G H (w :: Pst) := by
      refine ⟨List.nodup_cons.2 ⟨hwP, hnd⟩, ?_, ?_⟩
      · exact chain_app (List.isChain_singleton w) hch (x := w) (y := x) (by simp) hh hxw.symm
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hw
        · exact hH z hz
    have := hmaxP _ hHL
    simp at this
  have hyN : ∀ w ∈ H, G.Adj y w → w ∈ Pst := by
    intro w hw hyw
    by_contra hwP
    have hHL : HL G H (Pst ++ [w]) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton w, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        exact hwP (hb ▸ hab ▸ ha)
      · exact chain_app hch (List.isChain_singleton w) (x := y) (y := w) hl (by simp) hyw
      · intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hH z hz
        · rw [List.mem_singleton] at hz; rw [hz]; exact hw
    have := hmaxP _ hHL
    simp at this
  set I := (H.filter (G.Adj x)).image (fun w => Pst.idxOf w) with hI
  set J := (H.filter (G.Adj y)).image (fun w => Pst.idxOf w + 1) with hJ
  have hmemx : ∀ w ∈ H.filter (G.Adj x), w ∈ Pst ∧ G.Adj x w := by
    intro w hw; rw [Finset.mem_filter] at hw; exact ⟨hxN w hw.1 hw.2, hw.2⟩
  have hmemy : ∀ w ∈ H.filter (G.Adj y), w ∈ Pst ∧ G.Adj y w := by
    intro w hw; rw [Finset.mem_filter] at hw; exact ⟨hyN w hw.1 hw.2, hw.2⟩
  have hcI : I.card = (H.filter (G.Adj x)).card := by
    apply Finset.card_image_of_injOn
    intro v hv w hw h
    exact (List.idxOf_inj (hmemx v hv).1).1 h
  have hcJ : J.card = (H.filter (G.Adj y)).card := by
    apply Finset.card_image_of_injOn
    intro v hv w hw h
    have h' : Pst.idxOf v = Pst.idxOf w := by simpa using h
    exact (List.idxOf_inj (hmemy v hv).1).1 h'
  have hlt : ∀ v ∈ Pst, Pst.idxOf v < Pst.length := fun v hv => List.idxOf_lt_length_of_mem hv
  have hx0 : Pst.idxOf x = 0 := by
    rcases Pst with _ | ⟨x', P'⟩
    · simp at hh
    · simp at hh; subst hh; simp
  have hylast : Pst.idxOf y + 1 = Pst.length := by
    obtain ⟨P', rfl⟩ : ∃ P', Pst = P' ++ [y] := by
      rcases List.eq_nil_or_concat' Pst with rfl | ⟨P', b, rfl⟩
      · simp at hl
      · simp at hl; subst hl; exact ⟨P', rfl⟩
    have hyP' : y ∉ P' := by
      intro h
      rw [List.nodup_append] at hnd
      exact hnd.2.2 y h y (by simp) rfl
    rw [idxOf_mid hyP']; simp
  by_cases hdisj : Disjoint I J
  · left
    have hsub : I ∪ J ⊆ Finset.Icc 1 (Pst.length - 1) := by
      intro i hi
      rw [Finset.mem_Icc]
      rcases Finset.mem_union.1 hi with hi | hi
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hi
        have h1 := hmemx w hw
        have h2 := hlt w h1.1
        have hne : Pst.idxOf w ≠ 0 := by
          intro h0
          have : Pst.idxOf w = Pst.idxOf x := by rw [h0, hx0]
          have hwx : w = x := (List.idxOf_inj h1.1).1 this
          exact G.loopless.irrefl x (hwx ▸ h1.2)
        omega
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hi
        have h1 := hmemy w hw
        have h2 := hlt w h1.1
        have hne : Pst.idxOf w ≠ Pst.idxOf y := by
          intro h0
          have hwy : w = y := (List.idxOf_inj h1.1).1 h0
          exact G.loopless.irrefl y (hwy ▸ h1.2)
        omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Icc, hcI, hcJ] at hcard
    have := hlt x hxP
    omega
  · right
    rw [Finset.not_disjoint_iff] at hdisj
    obtain ⟨i, hiI, hiJ⟩ := hdisj
    obtain ⟨w1, hw1, hi1⟩ := Finset.mem_image.1 hiI
    obtain ⟨w2, hw2, hi2⟩ := Finset.mem_image.1 hiJ
    have h1 := hmemx w1 hw1
    have h2 := hmemy w2 hw2
    have hi1lt := hlt w1 h1.1
    have hi2lt := hlt w2 h2.1
    by_contra hcon
    push Not at hcon
    obtain ⟨z, hzH, hzP⟩ := hcon
    -- a vertex of H off the list adjacent to the list
    obtain ⟨Q, hQ⟩ := hconn z hzH x (hH x hxP)
    obtain ⟨w0, vj, hw0Q, hvjQ, hadj, hw0P, hvjP⟩ :=
      chain_cross (S := fun v => v ∈ Pst) Q z x hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hzP hxP
    have hw0H : w0 ∈ H := hQ.2.2.2.2 w0 hw0Q
    -- split the list
    have hsplit : Pst.take i ++ Pst.drop i = Pst := List.take_append_drop i Pst
    have hP1l : (Pst.take i).getLast? = some w2 := by
      rw [← hi2, take_getLast? hi2lt, getElem_of_idxOf_eq rfl hi2lt]
    have hP2h : (Pst.drop i).head? = some w1 := by
      have hlt' : i < Pst.length := by omega
      rw [drop_head? hlt', getElem_of_idxOf_eq hi1 hlt']
    have hP1h : (Pst.take i).head? = some x := by
      rw [← hi2]; exact take_head? hh
    have hP2l : (Pst.drop i).getLast? = some y := drop_getLast? (by omega) hl
    have hch1 : (Pst.take i).IsChain G.Adj := hch.take i
    have hch2 : (Pst.drop i).IsChain G.Adj := hch.drop i
    have hlenP : (Pst.take i).length + (Pst.drop i).length = Pst.length := by
      rw [← List.length_append, hsplit]
    rw [← hsplit, List.mem_append] at hvjP
    have hfin : ∀ N : List V, N.Perm Pst → (w0 :: N).IsChain G.Adj → False := by
      intro N hperm hchN
      have hHL : HL G H (w0 :: N) := by
        refine ⟨List.nodup_cons.2 ⟨fun h => hw0P (hperm.mem_iff.1 h), hperm.nodup_iff.2 hnd⟩, hchN, ?_⟩
        intro z' hz'
        rcases List.mem_cons.1 hz' with rfl | hz'
        · exact hw0H
        · exact hH z' (hperm.mem_iff.1 hz')
      have := hmaxP _ hHL
      rw [List.length_cons, hperm.length_eq] at this
      omega
    rcases hvjP with hvj | hvj
    · obtain ⟨E, F, hEF⟩ := List.append_of_mem hvj
      have hE1 : (E ++ [vj]).IsChain G.Adj := by
        have : (Pst.take i) = (E ++ [vj]) ++ F := by rw [hEF]; simp
        rw [this] at hch1; exact hch1.left_of_append
      have hF1 : F.IsChain G.Adj := by
        have : (Pst.take i) = (E ++ [vj]) ++ F := by rw [hEF]; simp
        rw [this] at hch1; exact hch1.right_of_append
      have hEh : (E ++ [vj]).head? = some x := by
        have : (Pst.take i).head? = ((E ++ [vj]) ++ F).head? := by rw [hEF]; simp
        rw [hP1h] at this
        rw [List.head?_append] at this
        rcases h : (E ++ [vj]).head? with _ | e
        · simp at h
        · rw [h] at this; simpa [eq_comm] using this
      apply hfin ((E ++ [vj]).reverse ++ (Pst.drop i ++ F.reverse))
      · have h3 : ((E ++ [vj]).reverse ++ (Pst.drop i ++ F.reverse)).Perm
            ((E ++ [vj]) ++ (F ++ Pst.drop i)) :=
          (List.reverse_perm _).append ((List.Perm.append_left _ (List.reverse_perm F)).trans
            List.perm_append_comm)
        have h4 : (E ++ [vj]) ++ (F ++ Pst.drop i) = Pst := by
          calc (E ++ [vj]) ++ (F ++ Pst.drop i) = (E ++ vj :: F) ++ Pst.drop i := by simp
            _ = Pst.take i ++ Pst.drop i := by rw [hEF]
            _ = Pst := hsplit
        rw [h4] at h3; exact h3
      · have hc3 : (Pst.drop i ++ F.reverse).IsChain G.Adj := by
          apply hch2.append (chain_rev hF1)
          intro a ha b hb
          rw [hP2l] at ha
          obtain rfl : y = a := by simpa using ha
          rw [List.head?_reverse] at hb
          have h5 := getLast?_append_cons_of_mem (E := E) (v := vj) hb
          rw [← hEF, hP1l] at h5
          obtain rfl : w2 = b := by simpa using h5
          exact h2.2
        have hc4 : ((E ++ [vj]).reverse ++ (Pst.drop i ++ F.reverse)).IsChain G.Adj :=
          chain_app (chain_rev hE1) hc3 (x := x) (y := w1)
            (by rw [List.getLast?_reverse]; exact hEh) (head?_app hP2h) h1.2
        exact chain_app (List.isChain_singleton w0) hc4 (x := w0) (y := vj) (by simp)
          (head?_app (by simp)) hadj
    · obtain ⟨E, F, hEF⟩ := List.append_of_mem hvj
      have hE2 : E.IsChain G.Adj := by rw [hEF] at hch2; exact hch2.left_of_append
      have hF2 : (vj :: F).IsChain G.Adj := by rw [hEF] at hch2; exact hch2.right_of_append
      have hFl : (vj :: F).getLast? = some y := by
        have : (Pst.drop i).getLast? = (E ++ vj :: F).getLast? := by rw [hEF]
        rw [hP2l] at this
        rw [List.getLast?_append] at this
        rcases h : (vj :: F).getLast? with _ | e
        · simp at h
        · rw [h] at this; simpa [eq_comm] using this
      apply hfin ((vj :: F) ++ ((Pst.take i).reverse ++ E))
      · have h3 : ((vj :: F) ++ ((Pst.take i).reverse ++ E)).Perm
            (Pst.take i ++ (E ++ vj :: F)) := by
          refine List.perm_append_comm.trans ?_
          rw [List.append_assoc]
          exact List.Perm.append_right _ (List.reverse_perm _)
        rw [← hEF, hsplit] at h3; exact h3
      · have hc3 : ((Pst.take i).reverse ++ E).IsChain G.Adj := by
          apply (chain_rev hch1).append hE2
          intro a ha b hb
          rw [List.getLast?_reverse, hP1h] at ha
          obtain rfl : x = a := by simpa using ha
          have h5 : (Pst.drop i).head? = some b := by
            rw [hEF]; exact head?_app hb
          rw [hP2h] at h5
          obtain rfl : w1 = b := by simpa using h5
          exact h1.2
        have hc4 : ((vj :: F) ++ ((Pst.take i).reverse ++ E)).IsChain G.Adj :=
          chain_app hF2 hc3 (x := y) (y := w2) hFl
            (head?_app (by rw [List.head?_reverse]; exact hP1l)) h2.2
        exact chain_app (List.isChain_singleton w0) hc4 (x := w0) (y := vj) (by simp)
          (by simp) hadj

end longest


section caseii
variable [DecidableEq V]

theorem sub_path {G : SimpleGraph V} {H : Finset V} {Pst : List V} (hHL : HL G H Pst) {z' z : V}
    (hz' : z' ∈ Pst) (hz : z ∈ Pst) (hle : Pst.idxOf z' ≤ Pst.idxOf z) :
    ∃ Q, HP G H Q z' z ∧ Q.length = Pst.idxOf z - Pst.idxOf z' + 1 := by
  obtain ⟨hnd, hch, hH⟩ := hHL
  have hi := List.idxOf_lt_length_of_mem hz'
  have hj := List.idxOf_lt_length_of_mem hz
  set i := Pst.idxOf z' with hi_def
  set j := Pst.idxOf z with hj_def
  have hdl : j - i < (Pst.drop i).length := by rw [List.length_drop]; omega
  refine ⟨(Pst.drop i).take (j - i + 1), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (hnd.sublist (List.drop_sublist i Pst)).sublist (List.take_sublist _ _)
  · exact (hch.drop i).take _
  · rw [take_head? (drop_head? hi), getElem_of_idxOf_eq hi_def.symm hi]
  · rw [take_getLast? hdl, List.getElem_drop]
    have h1 : i + (j - i) = j := by omega
    rw [getElem_of_idxOf_eq (v := z) (by omega) (by omega)]
  · intro w hw
    exact hH w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
  · rw [List.length_take, List.length_drop]; omega

/-- case (ii): the longest list spans `H` -/
theorem case_ii {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ} {L : List V} {H : Finset V}
    (ctx : Ctx G c L H) {Pst : List V} {x y : V} (hP : HP G H Pst x y)
    (hspan : ∀ z ∈ H, z ∈ Pst) (hpc : Pst.length + 2 ≤ c) {s0 : ℕ}
    (hatt : ∀ v ∈ H, s0 ≤ (L.toFinset.filter (G.Adj v)).card) :
    (H.card + 1) * s0 ≤ c := by
  classical
  have hHLP : HL G H Pst := ⟨hP.1, hP.2.1, hP.2.2.2.2⟩
  have hxH : x ∈ H := hP.2.2.2.2 x (List.mem_of_head? hP.2.2.1)
  set T := L.toFinset.filter (fun a => (H.filter (G.Adj a)).Nonempty) with hT
  set K : V → Finset ℕ := fun a => (H.filter (G.Adj a)).image (fun z => Pst.idxOf z) with hK
  set S : V → Finset ℕ := fun a =>
    if h : (K a).Nonempty then insert ((K a).max' h + 1) (K a) else ∅ with hS
  have hKcard : ∀ a, (K a).card = (H.filter (G.Adj a)).card := by
    intro a
    apply Finset.card_image_of_injOn
    intro v hv w hw h
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    exact (List.idxOf_inj (hspan v hv.1)).1 h
  have hKne : ∀ a ∈ T, (K a).Nonempty := by
    intro a ha
    rw [hT, Finset.mem_filter] at ha
    exact ha.2.image _
  have hKmem : ∀ a k, k ∈ K a → ∃ z ∈ H, G.Adj a z ∧ Pst.idxOf z = k := by
    intro a k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hk
    rw [Finset.mem_filter] at hz
    exact ⟨z, hz.1, hz.2, rfl⟩
  have hScard : ∀ a ∈ T, (S a).card = (H.filter (G.Adj a)).card + 1 := by
    intro a ha
    have hne := hKne a ha
    simp only [hS, dif_pos hne]
    rw [Finset.card_insert_of_notMem, hKcard]
    intro hmem
    have := Finset.le_max' (K a) _ hmem
    omega
  have hSmem : ∀ a s, s ∈ S a → (∃ k ∈ K a, s ≤ k + 1) ∧ (∃ l ∈ K a, l ≤ s) := by
    intro a s hs
    by_cases hne : (K a).Nonempty
    · simp only [hS, dif_pos hne, Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · exact ⟨⟨_, Finset.max'_mem _ hne, le_refl _⟩, ⟨_, Finset.max'_mem _ hne, Nat.le_succ _⟩⟩
      · exact ⟨⟨s, hs, Nat.le_succ _⟩, ⟨s, hs, le_refl _⟩⟩
    · simp only [hS, dif_neg hne] at hs
      exact absurd hs (Finset.notMem_empty s)
  have hTL : ∀ a ∈ T, a ∈ L := by
    intro a ha
    rw [hT, Finset.mem_filter, List.mem_toFinset] at ha
    exact ha.1
  have hcount : ∑ a ∈ T, (S a).card ≤ c := by
    apply inj_count (fun a => L.idxOf a) S
    · intro a ha
      rw [← ctx.hlen]; exact List.idxOf_lt_length_of_mem (hTL a ha)
    · intro a ha a' _ h
      exact (List.idxOf_inj (hTL a ha)).1 h
    · intro a _ s hs
      obtain ⟨⟨k, hk, hsk⟩, -⟩ := hSmem a s hs
      obtain ⟨z, hz, -, rfl⟩ := hKmem a k hk
      have := List.idxOf_lt_length_of_mem (hspan z hz)
      omega
    · intro a ha a' ha' hne s hs s' hs' hle
      obtain ⟨⟨k, hk, hsk⟩, -⟩ := hSmem a s hs
      obtain ⟨-, ⟨l, hl, hls⟩⟩ := hSmem a' s' hs'
      obtain ⟨z, hz, haz, rfl⟩ := hKmem a k hk
      obtain ⟨z', hz', haz', rfl⟩ := hKmem a' l hl
      rcases le_total (Pst.idxOf z') (Pst.idxOf z) with hzz | hzz
      · obtain ⟨Q, hQ, hQlen⟩ := sub_path hHLP (hspan z' hz') (hspan z hz) hzz
        have hg := gap_pos ctx (hTL a ha) (hTL a' ha') hne hQ.rev haz haz'.symm
        rw [List.length_reverse, hQlen] at hg
        omega
      · obtain ⟨Q, hQ, hQlen⟩ := sub_path hHLP (hspan z hz) (hspan z' hz') hzz
        have hg := gap_pos ctx (hTL a ha) (hTL a' ha') hne hQ haz haz'.symm
        rw [hQlen] at hg
        omega
  -- double counting
  have hsum1 : ∑ a ∈ T, (S a).card = ∑ a ∈ T, (H.filter (G.Adj a)).card + T.card := by
    rw [Finset.sum_congr rfl hScard, Finset.sum_add_distrib]
    simp
  have hsum2 : ∑ a ∈ T, (H.filter (G.Adj a)).card = ∑ a ∈ L.toFinset, (H.filter (G.Adj a)).card := by
    rw [hT, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : (H.filter (G.Adj a)).Nonempty
    · rw [if_pos h]
    · rw [if_neg h]
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h]; rfl
  have hsum3 : ∑ a ∈ L.toFinset, (H.filter (G.Adj a)).card
      = ∑ z ∈ H, (L.toFinset.filter (G.Adj z)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro a _
    simp [G.adj_comm]
  have hsum4 : H.card * s0 ≤ ∑ z ∈ H, (L.toFinset.filter (G.Adj z)).card := by
    have := Finset.card_nsmul_le_sum H (fun z => (L.toFinset.filter (G.Adj z)).card) s0 hatt
    simpa using this
  have hTcard : s0 ≤ T.card := by
    refine le_trans (hatt x hxH) (Finset.card_le_card ?_)
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [hT, Finset.mem_filter]
    exact ⟨ha.1, ⟨x, Finset.mem_filter.2 ⟨hxH, ha.2.symm⟩⟩⟩
  rw [hsum1, hsum2, hsum3] at hcount
  calc (H.card + 1) * s0 = H.card * s0 + s0 := by ring
    _ ≤ ∑ z ∈ H, (L.toFinset.filter (G.Adj z)).card + T.card := Nat.add_le_add hsum4 hTcard
    _ ≤ c := hcount

end caseii


section casei
variable [DecidableEq V]

theorem fwd_sub {c i j k : ℕ} (hi : i < c) (hj : j < c) (hk : k < c) (_hij : i ≠ j) (_hjk : j ≠ k)
    (h : fwd c i j < fwd c i k) : fwd c j k + fwd c i j = fwd c i k := by
  unfold fwd at h ⊢
  split_ifs at h ⊢ <;> omega

/-- case (i): the ends of the longest list have few neighbours in `H` -/
theorem case_i {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ} {L : List V} {H : Finset V}
    (ctx : Ctx G c L H) {Pst : List V} {x y : V} (hP : HP G H Pst x y) (h3 : 3 ≤ Pst.length)
    (hpc : Pst.length + 2 ≤ c)
    (hx2 : 2 ≤ (L.toFinset.filter (G.Adj x)).card) (hy1 : 1 ≤ (L.toFinset.filter (G.Adj y)).card) :
    2 * ((L.toFinset.filter (G.Adj x)).card + (L.toFinset.filter (G.Adj y)).card) + Pst.length
      ≤ c + 3 := by
  classical
  have hxH : x ∈ H := hP.2.2.2.2 x (List.mem_of_head? hP.2.2.1)
  have hyH : y ∈ H := hP.2.2.2.2 y (List.mem_of_getLast? hP.2.2.2.1)
  set p := Pst.length with hp
  set Tx := L.toFinset.filter (G.Adj x) with hTx
  set Ty := L.toFinset.filter (G.Adj y) with hTy
  set T := Tx ∪ Ty with hT
  set M := Tx ∩ Ty with hM
  have hTxm : ∀ a, a ∈ Tx ↔ a ∈ L ∧ G.Adj x a := by
    intro a; rw [hTx, Finset.mem_filter, List.mem_toFinset]
  have hTym : ∀ a, a ∈ Ty ↔ a ∈ L ∧ G.Adj y a := by
    intro a; rw [hTy, Finset.mem_filter, List.mem_toFinset]
  have hTL : ∀ a ∈ T, a ∈ L := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · exact ((hTxm a).1 h).1
    · exact ((hTym a).1 h).1
  set pos : V → ℕ := fun a => L.idxOf a with hpos
  have hposlt : ∀ a ∈ L, pos a < c := by
    intro a ha; rw [← ctx.hlen]; exact List.idxOf_lt_length_of_mem ha
  have hposinj : ∀ a ∈ L, ∀ a', pos a = pos a' → a = a' := by
    intro a ha a' h; exact (List.idxOf_inj ha).1 h
  -- gaps
  have hxx : ∀ a ∈ Tx, ∀ a' ∈ Tx, a ≠ a' → 2 ≤ fwd c (pos a) (pos a') := by
    intro a ha a' ha' hne
    have := gap_pos ctx ((hTxm a).1 ha).1 ((hTxm a').1 ha').1 hne (HP.single (G := G) hxH)
      ((hTxm a).1 ha).2.symm ((hTxm a').1 ha').2
    simpa using this
  have hyy : ∀ a ∈ Ty, ∀ a' ∈ Ty, a ≠ a' → 2 ≤ fwd c (pos a) (pos a') := by
    intro a ha a' ha' hne
    have := gap_pos ctx ((hTym a).1 ha).1 ((hTym a').1 ha').1 hne (HP.single (G := G) hyH)
      ((hTym a).1 ha).2.symm ((hTym a').1 ha').2
    simpa using this
  have hxy : ∀ a ∈ Tx, ∀ a' ∈ Ty, a ≠ a' → p + 1 ≤ fwd c (pos a) (pos a') := by
    intro a ha a' ha' hne
    exact gap_pos ctx ((hTxm a).1 ha).1 ((hTym a').1 ha').1 hne hP
      ((hTxm a).1 ha).2.symm ((hTym a').1 ha').2
  have hyx : ∀ a ∈ Ty, ∀ a' ∈ Tx, a ≠ a' → p + 1 ≤ fwd c (pos a) (pos a') := by
    intro a ha a' ha' hne
    have := gap_pos ctx ((hTym a).1 ha).1 ((hTxm a').1 ha').1 hne hP.rev
      ((hTym a).1 ha).2.symm ((hTxm a').1 ha').2
    simpa using this
  have hgap2 : ∀ a ∈ T, ∀ a' ∈ T, a ≠ a' → 2 ≤ fwd c (pos a) (pos a') := by
    intro a ha a' ha' hne
    rcases Finset.mem_union.1 ha with h | h <;> rcases Finset.mem_union.1 ha' with h' | h'
    · exact hxx a h a' h' hne
    · have := hxy a h a' h' hne; omega
    · have := hyx a h a' h' hne; omega
    · exact hyy a h a' h' hne
  -- the minimising cross pair
  set Pairs := (Tx ×ˢ Ty).filter (fun q => q.1 ≠ q.2) with hPairs
  have hPne : Pairs.Nonempty := by
    obtain ⟨a', ha'⟩ := Finset.card_pos.1 (by omega : 0 < Ty.card)
    obtain ⟨a, ha, hne⟩ := Finset.exists_mem_ne (by omega : 1 < Tx.card) a'
    exact ⟨(a, a'), by rw [hPairs, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ha, ha'⟩, hne⟩⟩
  obtain ⟨⟨a0, a0'⟩, hmem0, hmin⟩ :=
    Finset.exists_min_image Pairs (fun q => fwd c (pos q.1) (pos q.2)) hPne
  rw [hPairs, Finset.mem_filter, Finset.mem_product] at hmem0
  obtain ⟨⟨ha0, ha0'⟩, hne0⟩ := hmem0
  simp only at ha0 ha0' hne0
  have hD0 := hxy a0 ha0 a0' ha0' hne0
  have hspecial : ∀ a'' ∈ T, a'' ≠ a0 → p + 1 ≤ fwd c (pos a0) (pos a'') := by
    intro a'' ha'' hne
    rcases Finset.mem_union.1 ha'' with h | h
    · by_contra hlt
      push Not at hlt
      have hne' : a'' ≠ a0' := by
        rintro rfl; omega
      have hpair : (a'', a0') ∈ Pairs := by
        rw [hPairs, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨h, ha0'⟩, hne'⟩
      have h1 := hmin (a'', a0') hpair
      simp only at h1
      have hL0 := ((hTxm a0).1 ha0).1
      have hL'' := ((hTxm a'').1 h).1
      have hL0' := ((hTym a0').1 ha0').1
      have h2 := fwd_sub (hposlt a0 hL0) (hposlt a'' hL'') (hposlt a0' hL0')
        (fun e => hne (hposinj a0 hL0 a'' e).symm) (fun e => hne' (hposinj a'' hL'' a0' e))
        (by omega)
      have h3 := hxx a0 ha0 a'' h (Ne.symm hne)
      omega
    · exact hxy a0 ha0 a'' h (Ne.symm hne)
  set f : V → ℕ := fun a => if a ∈ M ∨ a = a0 then p else 1 with hf
  have hcount : ∑ a ∈ T, (Finset.range (f a + 1)).card ≤ c := by
    apply inj_count pos (fun a => Finset.range (f a + 1))
    · intro a ha; exact hposlt a (hTL a ha)
    · intro a ha a' _ h; exact hposinj a (hTL a ha) a' h
    · intro a _ s hs
      rw [Finset.mem_range] at hs
      have : f a ≤ p := by simp only [hf]; split_ifs <;> omega
      omega
    · intro a ha a' ha' hne s hs s' _ _
      rw [Finset.mem_range] at hs
      by_cases hcase : a ∈ M ∨ a = a0
      · have hfa : f a = p := by simp only [hf, if_pos hcase]
        have : p + 1 ≤ fwd c (pos a) (pos a') := by
          rcases hcase with hm | rfl
          · rw [hM, Finset.mem_inter] at hm
            rcases Finset.mem_union.1 ha' with h' | h'
            · exact hyx a hm.2 a' h' hne
            · exact hxy a hm.1 a' h' hne
          · exact hspecial a' ha' (Ne.symm hne)
        omega
      · have hfa : f a = 1 := by simp only [hf, if_neg hcase]
        have := hgap2 a ha a' ha' hne
        omega
  -- evaluate the sum
  set M' := insert a0 M with hM'
  have hM'T : M' ⊆ T := by
    intro a ha
    rw [hM', Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact Finset.mem_union_left _ ha0
    · rw [hM, Finset.mem_inter] at ha
      exact Finset.mem_union_left _ ha.1
  have hsum : ∑ a ∈ T, (Finset.range (f a + 1)).card = 2 * (T \ M').card + (p + 1) * M'.card := by
    rw [← Finset.sum_sdiff hM'T]
    congr 1
    · rw [Finset.sum_congr rfl (g := fun _ => 2)]
      · simp [mul_comm]
      · intro a ha
        rw [Finset.mem_sdiff, hM', Finset.mem_insert] at ha
        have : ¬ (a ∈ M ∨ a = a0) := fun h => ha.2 (h.symm)
        simp only [Finset.card_range, hf, if_neg this]
    · rw [Finset.sum_congr rfl (g := fun _ => p + 1)]
      · simp [mul_comm]
      · intro a ha
        rw [hM', Finset.mem_insert] at ha
        have : a ∈ M ∨ a = a0 := ha.symm
        simp only [Finset.card_range, hf, if_pos this]
  have hcard1 : (T \ M').card = T.card - M'.card := Finset.card_sdiff_of_subset hM'T
  have hcard2 : M'.card ≤ T.card := Finset.card_le_card hM'T
  have hcard3 : T.card + M.card = Tx.card + Ty.card := Finset.card_union_add_card_inter Tx Ty
  have hcard4 : M.card ≤ M'.card := Finset.card_le_card (Finset.subset_insert a0 M)
  have hcard5 : 1 ≤ M'.card := Finset.card_pos.2 ⟨a0, Finset.mem_insert_self a0 M⟩
  rw [hsum, hcard1] at hcount
  obtain ⟨q, hq⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, M'.card = r + 1 := ⟨M'.card - 1, by omega⟩
  rw [hq, hr] at hcount
  have hqr : (q + 3 + 1) * (r + 1) = q * r + q + 4 * r + 4 := by ring
  rw [hqr] at hcount
  have := Nat.zero_le (q * r)
  omega

end casei


section final
variable [Fintype V] [DecidableEq V]

/-- the contradiction once `H` is known to be small -/
theorem final_contra {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ} {L : List V} {H : Finset V}
    (ctx : Ctx G c L H) {d : ℕ} (hd : ∀ v, d ≤ G.degree v)
    (hn : Fintype.card V + 6 ≤ 4 * d) (hh : H.card + 3 ≤ d) (hcn : c + H.card ≤ Fintype.card V)
    {Q0 : List V} (hQ0 : HL G H Q0) (h30 : 3 ≤ Q0.length) : False := by
  obtain ⟨Pst, hPst, hlen0, hmaxP⟩ := exists_longest hQ0
  have hp3 : 3 ≤ Pst.length := le_trans h30 hlen0
  have hne : Pst ≠ [] := by rintro rfl; simp at hp3
  have hP : HP G H Pst (Pst.head hne) (Pst.getLast hne) :=
    ⟨hPst.1, hPst.2.1, List.head?_eq_some_head hne, List.getLast?_eq_some_getLast hne, hPst.2.2⟩
  set x := Pst.head hne with hx
  set y := Pst.getLast hne with hy
  have hxH : x ∈ H := hPst.2.2 x (List.head_mem hne)
  have hyH : y ∈ H := hPst.2.2 y (List.getLast_mem hne)
  have hpH := hPst.length_le
  have hatt : ∀ v ∈ H, d + 1 ≤ H.card + (L.toFinset.filter (G.Adj v)).card := by
    intro v hv
    have h1 := deg_H ctx hv
    have h2 := dH_lt (G := G) hv
    have h3 := hd v
    omega
  have hax := hatt x hxH
  have hay := hatt y hyH
  -- p + 2 ≤ c
  have hpc : Pst.length + 2 ≤ c := by
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < (L.toFinset.filter (G.Adj x)).card)
    obtain ⟨a', ha', hne'⟩ :=
      Finset.exists_mem_ne (by omega : 1 < (L.toFinset.filter (G.Adj y)).card) a
    rw [Finset.mem_filter, List.mem_toFinset] at ha ha'
    have hg := gap_pos ctx ha.1 ha'.1 (Ne.symm hne') hP ha.2.symm ha'.2
    have hlt := fwd_lt (c := c) (i := L.idxOf a) (j := L.idxOf a')
      (by rw [← ctx.hlen]; exact List.idxOf_lt_length_of_mem ha.1)
      (by rw [← ctx.hlen]; exact List.idxOf_lt_length_of_mem ha'.1)
    omega
  rcases posa ctx.hHconn hP hmaxP with h | h
  · have h1 := case_i ctx hP hp3 hpc (by omega) (by omega)
    have h2 := deg_H ctx hxH
    have h3 := deg_H ctx hyH
    have h4 := hd x
    have h5 := hd y
    omega
  · have h1 := case_ii ctx hP h hpc (s0 := d + 1 - H.card) (by intro v hv; have := hatt v hv; omega)
    obtain ⟨h', hh'⟩ : ∃ h', H.card = h' + 3 := ⟨H.card - 3, by omega⟩
    obtain ⟨s', hs'⟩ : ∃ s', d + 1 - H.card = s' + 4 := ⟨d + 1 - H.card - 4, by omega⟩
    rw [hs', hh'] at h1
    have hexp : (h' + 3 + 1) * (s' + 4) = h' * s' + 4 * h' + 4 * s' + 16 := by ring
    rw [hexp] at h1
    have := Nat.zero_le (h' * s')
    omega

open Arxiv.«2606.03696» in
/-- the statement with the degree hypothesis over the naturals -/
theorem main_aux {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsKConnected G 3) (hn : Fintype.card V + 6 ≤ 4 * G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference)
    (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v) (hP : P.IsPath)
    (h3 : 3 ≤ P.support.length) : False := by
  classical
  obtain ⟨hcycL, hlenL⟩ := cyc_of_isCycle hC
  set L := C.support.tail with hL
  have hmax : ∀ L' : List V, IsCyc G L' → 3 ≤ L'.length → L'.length ≤ C.length := by
    intro L' h h3'; rw [hlong]; exact cyc_length_le h h3'
  have h3c : 3 ≤ C.length := hC.three_le_length
  have hsupp : ∀ w, w ∈ C.support → w ∈ L := by
    intro w hw
    rw [← C.cons_tail_support, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact Walk.end_mem_tail_support hC.not_nil
    · exact hw
  have hoff : ∀ w, w ∈ offWalk C ↔ w ∉ C.support := fun w => Iff.rfl
  set H : Finset V := Finset.univ.filter (fun w => ∃ hw : w ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨w, hw⟩)
    with hH
  have hHmem : ∀ w, w ∈ H ↔ ∃ hw : w ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨w, hw⟩ := by
    intro w; rw [hH, Finset.mem_filter]; simp
  have hHL : ∀ w ∈ H, w ∉ L := by
    intro w hw hwL
    obtain ⟨hw', -⟩ := (hHmem w).1 hw
    exact (hoff w).1 hw' (List.mem_of_mem_tail hwL)
  have hHcl : ∀ v ∈ H, ∀ w, G.Adj v w → w ∉ L → w ∈ H := by
    intro v hv w hvw hwL
    obtain ⟨hv', rv⟩ := (hHmem v).1 hv
    have hw' : w ∈ offWalk C := (hoff w).2 (fun h => hwL (hsupp w h))
    have hadj : (G.induce (offWalk C)).Adj ⟨v, hv'⟩ ⟨w, hw'⟩ := hvw
    exact (hHmem w).2 ⟨hw', rv.trans hadj.reachable⟩
  have hlist : ∀ (s t : offWalk C) (p : (G.induce (offWalk C)).Walk s t), p.IsPath → (G.induce (offWalk C)).Reachable u s →
      HP G H (p.support.map Subtype.val) s.1 t.1 := by
    intro s t p hp hs
    refine ⟨hp.support_nodup.map Subtype.val_injective, ?_, ?_, ?_, ?_⟩
    · exact List.isChain_map_of_isChain Subtype.val (fun a b h => h) p.isChain_adj_support
    · rw [List.head?_map, List.head?_eq_some_head p.support_ne_nil, p.head_support]; rfl
    · rw [List.getLast?_map, List.getLast?_eq_some_getLast p.support_ne_nil, p.getLast_support]; rfl
    · intro z hz
      obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hz
      exact (hHmem z'.1).2 ⟨z'.2, hs.trans (p.takeUntil z' hz').reachable⟩
  have hHconn : ∀ v ∈ H, ∀ w ∈ H, ∃ Q, HP G H Q v w := by
    intro v hv w hw
    obtain ⟨hv', rv⟩ := (hHmem v).1 hv
    obtain ⟨hw', rw'⟩ := (hHmem w).1 hw
    obtain ⟨p, hp⟩ := (rv.symm.trans rw').exists_isPath
    exact ⟨_, hlist _ _ p hp rv⟩
  have hQ0 := hlist u v P hP (Reachable.refl u)
  have hQ0L : HL G H (P.support.map Subtype.val) := ⟨hQ0.1, hQ0.2.1, hQ0.2.2.2.2⟩
  have h30 : 3 ≤ (P.support.map Subtype.val).length := by rw [List.length_map]; exact h3
  have hH3 : 3 ≤ H.card := le_trans h30 hQ0L.length_le
  have ctx : Ctx G C.length L H := ⟨hmax, hcycL, hlenL, h3c, hHL, hHcl, hHconn⟩
  have hK : ∀ S : Finset V, S.card ≤ 2 → ∃ x ∈ H, ∃ a ∈ L, x ∉ S ∧ a ∉ S ∧ G.Adj a x := by
    intro S hS
    have hconn := hG.2 S (by omega)
    obtain ⟨x0, hx0H, hx0S⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : S.card < H.card)
    have hLc : L.toFinset.card = C.length := by
      rw [List.toFinset_card_of_nodup hcycL.1, hlenL]
    obtain ⟨c0, hc0L, hc0S⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (by omega : S.card < L.toFinset.card)
    rw [List.mem_toFinset] at hc0L
    have hx0S' : x0 ∈ ((S : Set V)ᶜ) := by simpa using hx0S
    have hc0S' : c0 ∈ ((S : Set V)ᶜ) := by simpa using hc0S
    obtain ⟨p⟩ := hconn.preconnected ⟨x0, hx0S'⟩ ⟨c0, hc0S'⟩
    obtain ⟨dt, -, hd1, hd2⟩ := p.exists_boundary_dart {z | z.1 ∈ H} hx0H
      (fun h => hHL c0 h hc0L)
    have hadj : G.Adj dt.fst.1 dt.snd.1 := dt.adj
    have hsndL : dt.snd.1 ∈ L := by
      by_contra hnL
      exact hd2 (hHcl _ hd1 _ hadj hnL)
    have hfS : dt.fst.1 ∉ S := fun h => dt.fst.2 (Finset.mem_coe.2 h)
    have hsS : dt.snd.1 ∉ S := fun h => dt.snd.2 (Finset.mem_coe.2 h)
    exact ⟨dt.fst.1, hd1, dt.snd.1, hsndL, hfS, hsS, hadj.symm⟩
  have hb := h_bound ctx hK
  have hcn : C.length + H.card ≤ Fintype.card V := by
    have hdisj : Disjoint L.toFinset H := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      exact hHL w hw' (List.mem_toFinset.1 hw)
    have h1 := Finset.card_le_card (Finset.subset_univ (L.toFinset ∪ H))
    rw [Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hcycL.1, hlenL,
      Finset.card_univ] at h1
    exact h1
  exact final_contra ctx (fun v => G.minDegree_le_degree v) hn (by omega) hcn hQ0L h30

end final

end OMA.Helpers

theorem OMA.solution : type_of% @Arxiv.«2606.03696».bondy_conjecture.variants.three := by
  intro V _ _ G _ hG hd a C hC hlong u v P hP
  by_contra hcon
  have h3 : 3 ≤ P.support.length := by omega
  have hn : Fintype.card V + 6 ≤ 4 * G.minDegree := by
    have h4 : ((Fintype.card V : ℝ) + 6) ≤ 4 * (G.minDegree : ℝ) := by
      have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).1 hd
      linarith
    exact_mod_cast h4
  exact OMA.Helpers.main_aux hG hn C hC hlong u v P hP h3
