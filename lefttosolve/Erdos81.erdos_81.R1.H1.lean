import OMAReductions.R_Erdos81_erdos_81_R1
import Mathlib

/-!
# Dirac's simplicial vertex theorem

Every finite chordal graph which is not complete has two nonadjacent simplicial vertices.

We prove the stronger statement: for every finite vertex set `S` and every clique `K ⊆ S`
with `S ≠ K`, the induced graph on `S` has a simplicial vertex outside `K`.
The proof is by strong induction on `S`. Pick `x ∈ K` (or any `x ∈ S` if `K` is empty).
If `x` is adjacent to every other vertex of `S`, delete it. Otherwise, let `R` be the set of
vertices of `S` different from `x` and not adjacent to it, and `C` a minimal nonempty subset
of `R` closed under adjacency inside `R`. The vertices `Z` of `S \ C` adjacent to `C` are all
neighbours of `x`, and they form a clique: a nonadjacent pair would yield, through a shortest
connection inside `R` and back through `x`, an induced cycle of length at least four.
Induction applied to `C ∪ Z` and the clique `Z` gives a vertex of `C`, which is simplicial
in `S` and lies outside `K`.
-/

namespace OMA.Helpers

open SimpleGraph Finset

variable {V : Type*}

/-- A sequence `p 0, …, p L` of consecutive adjacent vertices from `a` to `b`
whose interior lies in `R`. -/
def Wk (G : SimpleGraph V) (R : Set V) (p : ℕ → V) (L : ℕ) (a b : V) : Prop :=
  p 0 = a ∧ p L = b ∧ (∀ k < L, G.Adj (p k) (p (k + 1))) ∧ (∀ k, 0 < k → k < L → p k ∈ R)

lemma wk_shortcut {G : SimpleGraph V} {R : Set V} {p : ℕ → V} {L : ℕ} {a b : V}
    (hW : Wk G R p L a b) (i d : ℕ) (hid : i + d ≤ L)
    (hlink : i + d < L → G.Adj (p i) (p (i + d + 1))) (hend : i + d = L → p i = b) :
    Wk G R (fun k => if k ≤ i then p k else p (k + d)) (L - d) a b := by
  obtain ⟨h0, hL, hadj, hR⟩ := hW
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [h0]
  · dsimp only
    by_cases h : L - d ≤ i
    · rw [if_pos h, show L - d = i by omega]
      exact hend (by omega)
    · rw [if_neg h, show L - d + d = L by omega]
      exact hL
  · intro k hk
    dsimp only
    by_cases h1 : k + 1 ≤ i
    · rw [if_pos (show k ≤ i by omega), if_pos h1]
      exact hadj k (by omega)
    · by_cases h2 : k ≤ i
      · have hki : k = i := by omega
        subst hki
        rw [if_pos h2, if_neg h1, show k + 1 + d = k + d + 1 by omega]
        exact hlink (by omega)
      · rw [if_neg h1, if_neg h2, show k + 1 + d = k + d + 1 by omega]
        exact hadj (k + d) (by omega)
  · intro k hk0 hk
    dsimp only
    by_cases h : k ≤ i
    · rw [if_pos h]
      exact hR k hk0 (by omega)
    · rw [if_neg h]
      exact hR (k + d) (by omega) (by omega)

lemma wk_snoc {G : SimpleGraph V} {R : Set V} {p : ℕ → V} {L : ℕ} {a b c : V}
    (hW : Wk G R p L a b) (hb : 0 < L → b ∈ R) (hbc : G.Adj b c) :
    Wk G R (fun k => if k ≤ L then p k else c) (L + 1) a c := by
  obtain ⟨h0, hL, hadj, hR⟩ := hW
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [h0]
  · simp
  · intro k hk
    dsimp only
    by_cases h1 : k + 1 ≤ L
    · rw [if_pos (show k ≤ L by omega), if_pos h1]
      exact hadj k (by omega)
    · have hkL : k = L := by omega
      subst hkL
      rw [if_pos le_rfl, if_neg h1, hL]
      exact hbc
  · intro k hk0 hk
    dsimp only
    rw [if_pos (show k ≤ L by omega)]
    by_cases h : k < L
    · exact hR k hk0 h
    · have hkL : k = L := by omega
      subst hkL
      rw [hL]
      exact hb hk0

lemma wk_nil (G : SimpleGraph V) (R : Set V) (a : V) : Wk G R (fun _ => a) 0 a a :=
  ⟨rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), fun k _ hk => absurd hk (Nat.not_lt_zero k)⟩

/-- A shortest connection is an induced path. -/
lemma wk_min {G : SimpleGraph V} {R : Set V} {a b : V} (h : ∃ L, ∃ p, Wk G R p L a b) :
    ∃ L, ∃ p, Wk G R p L a b ∧ (∀ i j, i < j → j ≤ L → p i ≠ p j) ∧
      (∀ i j, i + 1 < j → j ≤ L → ¬ G.Adj (p i) (p j)) := by
  classical
  obtain ⟨p, hp⟩ := Nat.find_spec h
  refine ⟨Nat.find h, p, hp, ?_, ?_⟩
  · intro i j hij hjL heq
    have hW := wk_shortcut hp i (j - i) (by omega)
      (fun h1 => by
        rw [show i + (j - i) + 1 = j + 1 by omega, heq]
        exact hp.2.2.1 j (by omega))
      (fun h1 => by
        rw [heq, show j = Nat.find h by omega]
        exact hp.2.1)
    exact Nat.find_min h (show Nat.find h - (j - i) < Nat.find h by omega) ⟨_, hW⟩
  · intro i j hij hjL hadj
    have hW := wk_shortcut hp i (j - i - 1) (by omega)
      (fun _ => by
        rw [show i + (j - i - 1) + 1 = j by omega]
        exact hadj)
      (fun h1 => by omega)
    exact Nat.find_min h (show Nat.find h - (j - i - 1) < Nat.find h by omega) ⟨_, hW⟩

lemma cyc_adj {n : ℕ} (hn : 3 ≤ n) (u v : Fin n) :
    (cycleGraph n).Adj u v ↔
      (u.val + 1 = v.val ∨ v.val + 1 = u.val ∨ (u.val = 0 ∧ v.val + 1 = n) ∨
        (v.val = 0 ∧ u.val + 1 = n)) := by
  rw [cycleGraph_adj']
  have hu := u.isLt
  have hv := v.isLt
  rcases lt_trichotomy u v with h | h | h
  · have h' : u.val < v.val := h
    rw [Fin.coe_sub_iff_lt.2 h, Fin.sub_val_of_le h.le]
    omega
  · subst h
    rw [Fin.sub_val_of_le le_rfl]
    omega
  · have h' : v.val < u.val := h
    rw [Fin.coe_sub_iff_lt.2 h, Fin.sub_val_of_le h.le]
    omega

/-- An induced path whose two ends (and nothing else) are joined to an outside vertex `x`
closes an induced cycle. -/
lemma cycle_of_path {G : SimpleGraph V} {R : Set V} {p : ℕ → V} {L : ℕ} {a b x : V}
    (hW : Wk G R p L a b) (hinj : ∀ i j, i < j → j ≤ L → p i ≠ p j)
    (hind : ∀ i j, i + 1 < j → j ≤ L → ¬ G.Adj (p i) (p j))
    (hL : 2 ≤ L) (hxa : G.Adj x a) (hxb : G.Adj x b) (hxR : ∀ r ∈ R, ¬ G.Adj x r)
    (hxnR : x ∉ R) :
    (cycleGraph (L + 2)).IsIndContained G := by
  classical
  obtain ⟨h0, hLb, hadj, hR⟩ := hW
  have hx_ne : ∀ k ≤ L, p k ≠ x := by
    intro k hk heq
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [h0] at heq
      subst heq
      exact G.irrefl hxa
    · by_cases hkL : k = L
      · subst hkL
        rw [hLb] at heq
        subst heq
        exact G.irrefl hxb
      · exact hxnR (heq ▸ hR k hk0 (by omega))
  let f : Fin (L + 2) → V := fun k => if k.val ≤ L then p k.val else x
  have hf_inj : Function.Injective f := by
    intro u v huv
    have hu := u.isLt
    have hv := v.isLt
    apply Fin.ext
    simp only [f] at huv
    by_cases hu' : u.val ≤ L
    · by_cases hv' : v.val ≤ L
      · rw [if_pos hu', if_pos hv'] at huv
        rcases lt_trichotomy u.val v.val with h | h | h
        · exact absurd huv (hinj _ _ h hv')
        · exact h
        · exact absurd huv.symm (hinj _ _ h hu')
      · rw [if_pos hu', if_neg hv'] at huv
        exact absurd huv (hx_ne _ hu')
    · by_cases hv' : v.val ≤ L
      · rw [if_neg hu', if_pos hv'] at huv
        exact absurd huv.symm (hx_ne _ hv')
      · omega
  have hpadj : ∀ i j, i ≤ L → j ≤ L → (G.Adj (p i) (p j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    constructor
    · intro hij
      rcases lt_trichotomy i j with h | h | h
      · by_contra hc
        exact hind i j (by omega) hj hij
      · subst h
        exact absurd hij G.irrefl
      · by_contra hc
        exact hind j i (by omega) hi hij.symm
    · rintro (h | h)
      · subst h
        exact hadj i (by omega)
      · subst h
        exact (hadj j (by omega)).symm
  have hxadj : ∀ i, i ≤ L → (G.Adj (p i) x ↔ (i = 0 ∨ i = L)) := by
    intro i hi
    constructor
    · intro h
      by_contra hc
      exact hxR _ (hR i (by omega) (by omega)) h.symm
    · rintro (h | h)
      · subst h
        rw [h0]
        exact hxa.symm
      · subst h
        rw [hLb]
        exact hxb.symm
  refine ⟨{ toFun := f, inj' := hf_inj, map_rel_iff' := ?_ }⟩
  intro u v
  have hu := u.isLt
  have hv := v.isLt
  change G.Adj (f u) (f v) ↔ (cycleGraph (L + 2)).Adj u v
  rw [cyc_adj (by omega)]
  simp only [f]
  by_cases hu' : u.val ≤ L
  · by_cases hv' : v.val ≤ L
    · rw [if_pos hu', if_pos hv', hpadj _ _ hu' hv']
      omega
    · rw [if_pos hu', if_neg hv', hxadj _ hu']
      omega
  · by_cases hv' : v.val ≤ L
    · rw [if_neg hu', if_pos hv', G.adj_comm, hxadj _ hv']
      omega
    · rw [if_neg hu', if_neg hv']
      exact iff_of_false G.irrefl (by omega)

/-- Main lemma: a simplicial vertex outside any proper clique. -/
lemma simplicial_outside [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsChordal) :
    ∀ (S K : Finset V), K ⊆ S → G.IsClique (K : Set V) → (∃ w ∈ S, w ∉ K) →
      ∃ y ∈ S, y ∉ K ∧ G.IsClique ((S.filter (fun w => G.Adj y w)) : Set V) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro K hKS hK hw0
  obtain ⟨w0, hw0S, hw0K⟩ := hw0
  obtain ⟨x, hxS, hxK⟩ : ∃ x ∈ S, ∀ k ∈ K, k = x ∨ G.Adj x k := by
    rcases K.eq_empty_or_nonempty with hKe | ⟨x, hx⟩
    · exact ⟨w0, hw0S, by simp [hKe]⟩
    · refine ⟨x, hKS hx, fun k hk => ?_⟩
      by_cases hkx : k = x
      · exact Or.inl hkx
      · exact Or.inr (hK hx hk (Ne.symm hkx))
  set R := S.filter (fun w => w ≠ x ∧ ¬ G.Adj x w) with hRdef
  have hRx : ∀ r ∈ R, r ∈ S ∧ r ≠ x ∧ ¬ G.Adj x r := by
    intro r hr
    exact (Finset.mem_filter.1 hr)
  rcases R.eq_empty_or_nonempty with hRe | hRne
  · -- `x` is adjacent to every other vertex of `S`
    have hall : ∀ w ∈ S, w ≠ x → G.Adj x w := by
      intro w hw hwx
      by_contra hna
      have hwR : w ∈ R := Finset.mem_filter.2 ⟨hw, hwx, hna⟩
      rw [hRe] at hwR
      exact Finset.notMem_empty _ hwR
    by_cases hex : ∃ w ∈ S.erase x, w ∉ K.erase x
    · have hK' : G.IsClique ((K.erase x : Finset V) : Set V) :=
        hK.subset (by
          intro a ha
          exact Finset.mem_of_mem_erase (Finset.mem_coe.1 ha))
      obtain ⟨y, hyS, hyK, hycl⟩ := ih (S.erase x) (Finset.erase_ssubset hxS) (K.erase x)
        (Finset.erase_subset_erase x hKS) hK' hex
      have hyx : y ≠ x := Finset.ne_of_mem_erase hyS
      refine ⟨y, Finset.mem_of_mem_erase hyS, fun h => hyK (Finset.mem_erase.2 ⟨hyx, h⟩), ?_⟩
      intro a ha b hb hab
      have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      by_cases hax : a = x
      · subst hax
        exact hall b hb'.1 (Ne.symm hab)
      · by_cases hbx : b = x
        · subst hbx
          exact (hall a ha'.1 hab).symm
        · exact hycl (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hax, ha'.1⟩, ha'.2⟩))
            (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hbx, hb'.1⟩, hb'.2⟩)) hab
    · push Not at hex
      refine ⟨x, hxS, ?_, ?_⟩
      · intro hxK'
        apply hw0K
        by_cases h : w0 = x
        · rw [h]
          exact hxK'
        · exact Finset.mem_of_mem_erase (hex w0 (Finset.mem_erase.2 ⟨h, hw0S⟩))
      · apply hK.subset
        intro a ha
        have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
        exact Finset.mem_coe.2
          (Finset.mem_of_mem_erase (hex a (Finset.mem_erase.2 ⟨(G.ne_of_adj ha'.2).symm, ha'.1⟩)))
  · -- a minimal nonempty subset `C` of `R` closed under adjacency inside `R`
    obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image
      (R.powerset.filter (fun C => C.Nonempty ∧ ∀ c ∈ C, ∀ w ∈ R, G.Adj c w → w ∈ C))
      Finset.card
      ⟨R, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 subset_rfl, hRne, fun _ _ w hw _ => hw⟩⟩
    obtain ⟨hCR', hCne, hCcl⟩ := Finset.mem_filter.1 hCmem
    have hCR : C ⊆ R := Finset.mem_powerset.1 hCR'
    set Z := S.filter (fun w => w ∉ C ∧ ∃ c ∈ C, G.Adj w c) with hZdef
    have hZ : ∀ z ∈ Z, z ∈ S ∧ z ∉ C ∧ ∃ c ∈ C, G.Adj z c := fun z hz => Finset.mem_filter.1 hz
    have hZx : ∀ z ∈ Z, G.Adj x z := by
      intro z hz
      obtain ⟨hzS, hzC, c, hcC, hzc⟩ := hZ z hz
      obtain ⟨-, hcx, hxc⟩ := hRx c (hCR hcC)
      by_contra hna
      have hzx : z ≠ x := by
        rintro rfl
        exact hxc hzc
      exact hzC (hCcl c hcC z (Finset.mem_filter.2 ⟨hzS, hzx, hna⟩) hzc.symm)
    -- the key step: `Z` is a clique, by chordality
    have hZcl : G.IsClique (Z : Set V) := by
      classical
      intro z1 hz1 z2 hz2 hne
      have hz1' := hZ z1 (Finset.mem_coe.1 hz1)
      have hz2' := hZ z2 (Finset.mem_coe.1 hz2)
      obtain ⟨hz1S, hz1C, c1, hc1C, hz1c1⟩ := hz1'
      obtain ⟨hz2S, hz2C, c2, hc2C, hz2c2⟩ := hz2'
      by_contra hna
      -- every vertex of `C` is reachable from `z1` through `R`
      let D := C.filter (fun w => ∃ L, ∃ p, Wk G (R : Set V) p L z1 w)
      have hDC : D ⊆ C := Finset.filter_subset _ _
      have hDmem : D ∈ R.powerset.filter
          (fun C => C.Nonempty ∧ ∀ c ∈ C, ∀ w ∈ R, G.Adj c w → w ∈ C) := by
        refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hDC.trans hCR), ?_, ?_⟩
        · exact ⟨c1, Finset.mem_filter.2 ⟨hc1C, 0 + 1, _,
            wk_snoc (wk_nil G (R : Set V) z1) (fun h => absurd h (lt_irrefl 0)) hz1c1⟩⟩
        · intro c hc w hwR hcw
          obtain ⟨hcC, L, p, hp⟩ := Finset.mem_filter.1 hc
          exact Finset.mem_filter.2 ⟨hCcl c hcC w hwR hcw, L + 1, _,
            wk_snoc hp (fun _ => Finset.mem_coe.2 (hCR hcC)) hcw⟩
      have hDeq : D = C := Finset.eq_of_subset_of_card_le hDC (hCmin D hDmem)
      have hc2D : c2 ∈ D := by
        rw [hDeq]
        exact hc2C
      obtain ⟨-, L0, p0, hp0⟩ := Finset.mem_filter.1 hc2D
      have hwalk : ∃ L, ∃ p, Wk G (R : Set V) p L z1 z2 :=
        ⟨L0 + 1, _, wk_snoc hp0 (fun _ => Finset.mem_coe.2 (hCR hc2C)) hz2c2.symm⟩
      obtain ⟨L, p, hp, hinj, hind⟩ := wk_min hwalk
      have hL2 : 2 ≤ L := by
        by_contra hlt
        rcases (show L = 0 ∨ L = 1 by omega) with h | h
        · subst h
          exact hne (hp.1.symm.trans hp.2.1)
        · subst h
          have := hp.2.2.1 0 (by omega)
          rw [hp.1, show (0 : ℕ) + 1 = 1 by rfl, hp.2.1] at this
          exact hna this
      have hcyc := cycle_of_path hp hinj hind hL2 (hZx z1 (Finset.mem_coe.1 hz1))
        (hZx z2 (Finset.mem_coe.1 hz2))
        (fun r hr => (hRx r (Finset.mem_coe.1 hr)).2.2)
        (fun hx => (hRx x (Finset.mem_coe.1 hx)).2.1 rfl)
      exact hG (L + 2) (by omega) hcyc
    -- induction on `C ∪ Z`
    have hxC : x ∉ C := fun h => (hRx x (hCR h)).2.1 rfl
    have hxZ : x ∉ Z := fun h => G.irrefl (hZx x h)
    have hsub : C ∪ Z ⊆ S := by
      intro w hw
      rcases Finset.mem_union.1 hw with h | h
      · exact (hRx w (hCR h)).1
      · exact (hZ w h).1
    have hss : C ∪ Z ⊂ S := (Finset.ssubset_iff_of_subset hsub).2
      ⟨x, hxS, fun h => (Finset.mem_union.1 h).elim hxC hxZ⟩
    obtain ⟨c0, hc0⟩ := hCne
    obtain ⟨y, hyS', hyZ, hycl⟩ := ih (C ∪ Z) hss Z Finset.subset_union_right hZcl
      ⟨c0, Finset.mem_union_left _ hc0, fun h => (hZ c0 h).2.1 hc0⟩
    have hyC : y ∈ C := (Finset.mem_union.1 hyS').resolve_right hyZ
    obtain ⟨hyS, hyx, hxy⟩ := hRx y (hCR hyC)
    refine ⟨y, hyS, ?_, ?_⟩
    · intro hyK
      rcases hxK y hyK with h | h
      · exact hyx h
      · exact hxy h
    · apply hycl.subset
      intro w hw
      have hw' := Finset.mem_filter.1 (Finset.mem_coe.1 hw)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨?_, hw'.2⟩)
      by_cases hwC : w ∈ C
      · exact Finset.mem_union_left _ hwC
      · exact Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hw'.1, hwC, y, hyC, hw'.2.symm⟩)

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos81_erdos_81_R1.H1 := by
  intro n G _ hG S hS
  obtain ⟨u, hu, v, hv, huv, hnadj⟩ := hS
  obtain ⟨u', hu'S, -, hu'cl⟩ := OMA.Helpers.simplicial_outside hG S ∅
    (Finset.empty_subset _) (by simp) ⟨u, hu, Finset.notMem_empty u⟩
  have hKcl : G.IsClique ((S.filter (fun w => w = u' ∨ G.Adj u' w)) : Set (Fin n)) := by
    intro a ha b hb hab
    have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
    have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
    rcases ha'.2 with h1 | h1
    · subst h1
      rcases hb'.2 with h2 | h2
      · exact absurd h2.symm hab
      · exact h2
    · rcases hb'.2 with h2 | h2
      · subst h2
        exact h1.symm
      · exact hu'cl (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨ha'.1, h1⟩))
          (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hb'.1, h2⟩)) hab
  by_cases hex : ∃ w ∈ S, w ∉ S.filter (fun w => w = u' ∨ G.Adj u' w)
  · obtain ⟨v', hv'S, hv'K, hv'cl⟩ := OMA.Helpers.simplicial_outside hG S
      (S.filter (fun w => w = u' ∨ G.Adj u' w)) (Finset.filter_subset _ _) hKcl hex
    refine ⟨u', hu'S, v', hv'S, ?_, ?_, hu'cl, hv'cl⟩
    · intro h
      apply hv'K
      exact Finset.mem_filter.2 ⟨hv'S, Or.inl h.symm⟩
    · intro h
      apply hv'K
      exact Finset.mem_filter.2 ⟨hv'S, Or.inr h⟩
  · push Not at hex
    exact absurd (hKcl (Finset.mem_coe.2 (hex u hu)) (Finset.mem_coe.2 (hex v hv)) huv) hnadj
