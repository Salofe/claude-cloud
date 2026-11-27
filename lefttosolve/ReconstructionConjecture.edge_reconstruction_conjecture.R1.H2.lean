import OMAReductions.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1

/-!
# Step H2 of the reduction ReconstructionConjecture.edge_reconstruction_conjecture.R1

Mueller's theorem: if a graph on `n` vertices with `m` edges satisfies `n! < 2 ^ (m - 1)`, then
it is determined up to isomorphism by its deck of edge-deleted subgraphs. The extra hypotheses
of the step (connectivity, no isolated vertex, vertex hypomorphism) are not needed.

The proof is the Lovasz / Nash-Williams counting argument, written from scratch. For finite sets
`S` and `X` of unordered pairs, `erCnt S X` counts the permutations `π` of `V` with
`π(S) ⊆ X`. Let `E(G)` and `E(H)` be the edge sets, both of size `m`.

* Kelly-type lemma: if `|S| < m` then `erCnt S E(G) = erCnt S E(H)`. Indeed, double counting
  gives `∑_{x ∈ E(G)} erCnt S (E(G) - x) = (m - |S|) * erCnt S E(G)`, and the deck isomorphisms
  `G - x ≃ H - σ x` match the summands one by one with those of the same sum for `H`.
* Binomial identity: `∑_π (-1) ^ |{e ∈ E(G) | π e ∈ X}| = ∑_{S ⊆ E(G)} (-2) ^ |S| * erCnt S X`.
* Taking the difference of the identities for `X = E(H)` and `X = E(G)`, only `S = E(G)`
  survives, giving `(-2) ^ m * (erCnt E(G) E(H) - erCnt E(G) E(G))`. If `G` and `H` are not
  isomorphic then `erCnt E(G) E(H) = 0` while `erCnt E(G) E(G) ≥ 1`, and both left-hand sums
  are at most `n!` in absolute value. Hence `2 ^ m ≤ 2 * n!`, contradicting `n! < 2 ^ (m - 1)`.

Only the upstream definitions `EdgeHypomorphic` and `Hypomorphic` (through the statement) and
Mathlib are used.
-/

namespace OMA.Helpers

open Finset

section EdgeRecon

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The number of permutations `π` of `V` mapping every pair of `S` into `X`. -/
def erCnt (S X : Finset (Sym2 V)) : ℕ :=
  (univ.filter (fun π : Equiv.Perm V => ∀ e ∈ S, Sym2.map π e ∈ X)).card

theorem erCnt_double_count (X S : Finset (Sym2 V)) :
    ∑ x ∈ X, erCnt S (X.erase x) = (X.card - S.card) * erCnt S X := by
  unfold erCnt
  have key : ∀ π : Equiv.Perm V,
      (X.filter (fun x => ∀ e ∈ S, Sym2.map π e ∈ X.erase x)).card =
        if (∀ e ∈ S, Sym2.map π e ∈ X) then X.card - S.card else 0 := by
    intro π
    split_ifs with h
    · have hsub : S.image (Sym2.map π) ⊆ X := by
        intro y hy
        obtain ⟨e, he, rfl⟩ := mem_image.1 hy
        exact h e he
      have heq : X.filter (fun x => ∀ e ∈ S, Sym2.map π e ∈ X.erase x) =
          X \ S.image (Sym2.map π) := by
        ext x
        simp only [mem_filter, mem_sdiff, mem_image, mem_erase, not_exists, not_and]
        constructor
        · rintro ⟨hx, hall⟩
          exact ⟨hx, fun e he hex => (hall e he).1 hex⟩
        · rintro ⟨hx, hnot⟩
          exact ⟨hx, fun e he => ⟨fun hex => hnot e he hex, h e he⟩⟩
      rw [heq, card_sdiff_of_subset hsub,
        card_image_of_injective _ (Sym2.map.injective π.injective)]
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro x _ hall
      exact h (fun e he => mem_of_mem_erase (hall e he))
  calc ∑ x ∈ X, (univ.filter (fun π : Equiv.Perm V => ∀ e ∈ S, Sym2.map π e ∈ X.erase x)).card
      = ∑ π : Equiv.Perm V, (X.filter (fun x => ∀ e ∈ S, Sym2.map π e ∈ X.erase x)).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := X) (t := (univ : Finset (Equiv.Perm V)))
          (r := fun x (π : Equiv.Perm V) => ∀ e ∈ S, Sym2.map π e ∈ X.erase x)
    _ = ∑ π : Equiv.Perm V, if (∀ e ∈ S, Sym2.map π e ∈ X) then X.card - S.card else 0 :=
        sum_congr rfl (fun π _ => key π)
    _ = (X.card - S.card) *
          (univ.filter (fun π : Equiv.Perm V => ∀ e ∈ S, Sym2.map π e ∈ X)).card := by
        rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]

theorem erCnt_transfer {G' H' : SimpleGraph V} (τ : G' ≃g H') (X Y S : Finset (Sym2 V))
    (hX : ∀ e, e ∈ X ↔ e ∈ G'.edgeSet) (hY : ∀ e, e ∈ Y ↔ e ∈ H'.edgeSet) :
    erCnt S X = erCnt S Y := by
  unfold erCnt
  refine card_equiv (Equiv.mulLeft (τ.toEquiv : Equiv.Perm V)) (fun π => ?_)
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_mulLeft]
  refine forall₂_congr (fun e _ => ?_)
  rw [hX, hY, Equiv.Perm.coe_mul, ← Sym2.map_map]
  exact (τ.map_mem_edgeSet_iff).symm

theorem erCnt_kelly {G H : SimpleGraph V} (EG EH : Finset (Sym2 V))
    (hEG : ∀ e, e ∈ EG ↔ e ∈ G.edgeSet) (hEH : ∀ e, e ∈ EH ↔ e ∈ H.edgeSet)
    (σ : G.edgeSet ≃ H.edgeSet)
    (hσ : ∀ e : G.edgeSet, Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g
      H.deleteEdges {((σ e : H.edgeSet) : Sym2 V)}))
    (hcard : EG.card = EH.card)
    (S : Finset (Sym2 V)) (hS : S.card < EG.card) : erCnt S EG = erCnt S EH := by
  have hsum : ∑ x ∈ EG, erCnt S (EG.erase x) = ∑ y ∈ EH, erCnt S (EH.erase y) := by
    refine sum_bij (fun x hx => ((σ ⟨x, (hEG x).1 hx⟩ : H.edgeSet) : Sym2 V)) ?_ ?_ ?_ ?_
    · intro x hx
      exact (hEH _).2 (σ _).2
    · intro x₁ hx₁ x₂ hx₂ h
      have := σ.injective (Subtype.ext h)
      exact congrArg Subtype.val this
    · intro y hy
      refine ⟨((σ.symm ⟨y, (hEH y).1 hy⟩ : G.edgeSet) : Sym2 V), (hEG _).2 (σ.symm _).2, ?_⟩
      simp
    · intro x hx
      obtain ⟨τ⟩ := hσ ⟨x, (hEG x).1 hx⟩
      refine erCnt_transfer τ _ _ S ?_ ?_
      · intro e
        simp [SimpleGraph.edgeSet_deleteEdges, hEG, and_comm]
      · intro e
        simp [SimpleGraph.edgeSet_deleteEdges, hEH, and_comm]
  rw [erCnt_double_count, erCnt_double_count, ← hcard] at hsum
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hS) hsum

theorem erCnt_binom (E X : Finset (Sym2 V)) :
    ∑ π : Equiv.Perm V, (-1 : ℤ) ^ (E.filter (fun e => Sym2.map π e ∈ X)).card =
      ∑ S ∈ E.powerset, (-2 : ℤ) ^ S.card * (erCnt S X : ℤ) := by
  unfold erCnt
  simp_rw [natCast_card_filter, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun π _ => ?_)
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  have hps : E.powerset.filter (fun S => ∀ e ∈ S, Sym2.map π e ∈ X) =
      (E.filter (fun e => Sym2.map π e ∈ X)).powerset := by
    ext S
    simp only [mem_filter, mem_powerset, subset_iff]
    constructor
    · rintro ⟨h1, h2⟩ e he
      exact ⟨h1 he, h2 e he⟩
    · intro h
      exact ⟨fun e he => (h he).1, fun e he => (h he).2⟩
  rw [hps]
  have := sum_pow_mul_eq_add_pow (-2 : ℤ) 1 (E.filter (fun e => Sym2.map π e ∈ X))
  simp only [one_pow, mul_one] at this
  rw [this]
  norm_num

theorem erCnt_iso {G H : SimpleGraph V} (EG EH : Finset (Sym2 V))
    (hEG : ∀ e, e ∈ EG ↔ e ∈ G.edgeSet) (hEH : ∀ e, e ∈ EH ↔ e ∈ H.edgeSet)
    (hcard : EG.card = EH.card) (hno : ¬ Nonempty (G ≃g H)) : erCnt EG EH = 0 := by
  unfold erCnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro π _ hπ
  apply hno
  have himg : EG.image (Sym2.map π) = EH := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨e, he, rfl⟩ := mem_image.1 hy
      exact hπ e he
    · rw [card_image_of_injective _ (Sym2.map.injective π.injective), hcard]
  refine ⟨⟨π, ?_⟩⟩
  intro a b
  constructor
  · intro hab
    have hmem : s(π a, π b) ∈ EH := (hEH _).2 hab
    rw [← himg] at hmem
    obtain ⟨e, he, hee⟩ := mem_image.1 hmem
    have : e = s(a, b) := Sym2.map.injective π.injective (by rw [hee, Sym2.map_mk])
    rw [this] at he
    exact (hEG _).1 he
  · intro hab
    have := hπ s(a, b) ((hEG _).2 hab)
    rw [Sym2.map_mk] at this
    exact (hEH _).1 this

theorem erCnt_self_pos (E : Finset (Sym2 V)) : 1 ≤ erCnt E E := by
  unfold erCnt
  apply card_pos.2
  refine ⟨1, mem_filter.2 ⟨mem_univ _, fun e he => ?_⟩⟩
  simpa using he

theorem erCnt_abs_le (E X : Finset (Sym2 V)) :
    |∑ π : Equiv.Perm V, (-1 : ℤ) ^ (E.filter (fun e => Sym2.map π e ∈ X)).card| ≤
      ((Fintype.card V).factorial : ℤ) := by
  calc |∑ π : Equiv.Perm V, (-1 : ℤ) ^ (E.filter (fun e => Sym2.map π e ∈ X)).card|
      ≤ ∑ π : Equiv.Perm V, |(-1 : ℤ) ^ (E.filter (fun e => Sym2.map π e ∈ X)).card| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ _π : Equiv.Perm V, (1 : ℤ) := by simp
    _ = ((Fintype.card V).factorial : ℤ) := by simp [Fintype.card_perm]

end EdgeRecon

end OMA.Helpers

theorem OMA.solution : OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1.H2 := by
  intro V _ G H _ hE hfact _ _ hEH _
  classical
  obtain ⟨σ, hσ⟩ := hEH
  by_contra hno
  have hEG : ∀ e, e ∈ G.edgeFinset ↔ e ∈ G.edgeSet := fun e => SimpleGraph.mem_edgeFinset
  have hEH' : ∀ e, e ∈ H.edgeFinset ↔ e ∈ H.edgeSet := fun e => SimpleGraph.mem_edgeFinset
  have hm : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hcard : G.edgeFinset.card = H.edgeFinset.card := by
    rw [← G.card_edgeSet, ← H.card_edgeSet]
    exact Fintype.card_congr σ
  set EG := G.edgeFinset with hEGdef
  set EH := H.edgeFinset with hEHdef
  set m := EG.card with hmdef
  have hK := OMA.Helpers.erCnt_kelly EG EH hEG hEH' σ hσ hcard
  have h0 := OMA.Helpers.erCnt_iso EG EH hEG hEH' hcard hno
  have h1 := OMA.Helpers.erCnt_self_pos EG
  have hbG := OMA.Helpers.erCnt_binom EG EG
  have hbH := OMA.Helpers.erCnt_binom EG EH
  have hdiff : (∑ π : Equiv.Perm V, (-1 : ℤ) ^ (EG.filter (fun e => Sym2.map π e ∈ EH)).card) -
      (∑ π : Equiv.Perm V, (-1 : ℤ) ^ (EG.filter (fun e => Sym2.map π e ∈ EG)).card) =
      (-2 : ℤ) ^ m * ((OMA.Helpers.erCnt EG EH : ℤ) - OMA.Helpers.erCnt EG EG) := by
    rw [hbG, hbH, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single EG]
    · ring
    · intro S hS hne
      rw [hK S (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1 hS, hne⟩))]
      ring
    · intro h
      exact absurd (Finset.mem_powerset_self EG) h
  have hc : (1 : ℤ) ≤ (OMA.Helpers.erCnt EG EG : ℤ) := by exact_mod_cast h1
  have e1 : |(∑ π : Equiv.Perm V, (-1 : ℤ) ^ (EG.filter (fun e => Sym2.map π e ∈ EH)).card) -
      (∑ π : Equiv.Perm V, (-1 : ℤ) ^ (EG.filter (fun e => Sym2.map π e ∈ EG)).card)| =
      2 ^ m * (OMA.Helpers.erCnt EG EG : ℤ) := by
    rw [hdiff, h0, abs_mul, abs_pow]
    simp
  have e2 := abs_sub (∑ π : Equiv.Perm V, (-1 : ℤ) ^ (EG.filter (fun e => Sym2.map π e ∈ EH)).card)
      (∑ π : Equiv.Perm V, (-1 : ℤ) ^ (EG.filter (fun e => Sym2.map π e ∈ EG)).card)
  have e3 := OMA.Helpers.erCnt_abs_le EG EH
  have e4 := OMA.Helpers.erCnt_abs_le EG EG
  have key : (2 : ℤ) ^ m ≤ 2 * ((Fintype.card V).factorial : ℤ) := by
    have hpos : (0 : ℤ) ≤ 2 ^ m := by positivity
    nlinarith
  have key' : 2 ^ m ≤ 2 * (Fintype.card V).factorial := by exact_mod_cast key
  rw [hm] at hfact hE
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega
