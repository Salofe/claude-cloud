import OMAReductions.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_variants_radius_two_R1
import Mathlib

/-!
# Step H1 of the reduction GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.radius_two.R1

Stars specify chi-bounded classes. A tree of radius one around `c` is a star centred at `c`
(two adjacent leaves would close a triangle with `c`). If a finite graph `G` has no induced copy
of the star, the neighbourhood of every vertex has no independent set of size `|W| - 1` and no
clique of size `ω(G)`, so by an Erdos-Szekeres style Ramsey bound every degree is below
`2 ^ (ω(G) + |W|)`. A greedy colouring then gives `χ(G) ≤ 2 ^ (ω(G) + |W|)`.

Only upstream definitions are used.
-/

namespace OMA.Helpers
open SimpleGraph Finset

/-- An Erdos-Szekeres type Ramsey bound: a finite vertex set with every clique of size below `s`
and every independent set of size below `t` has fewer than `2 ^ (s + t)` vertices. -/
theorem ramsey_pow_two {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (N s t : ℕ), s + t = N → ∀ S : Finset V,
      (∀ K ⊆ S, (∀ x ∈ K, ∀ y ∈ K, x ≠ y → G.Adj x y) → K.card < s) →
      (∀ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card < t) →
      S.card < 2 ^ (s + t) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s t hst S hK hI
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have hs : 1 < s := by
    have h1 := hK {a} (by simpa using ha) (by simp)
    simpa using h1
  have ht : 1 < t := by
    have h1 := hI {a} (by simpa using ha) (by simp)
    simpa using h1
  have hcard : S.card = 1 + ((S.erase a).filter (fun x => G.Adj a x)).card +
      ((S.erase a).filter (fun x => ¬ G.Adj a x)).card := by
    rw [add_assoc, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem ha]
    have := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  have mem_of {p : V → Prop} [DecidablePred p] {x : V}
      (hx : x ∈ (S.erase a).filter p) : x ∈ S ∧ x ≠ a ∧ p x := by
    rw [Finset.mem_filter, Finset.mem_erase] at hx
    exact ⟨hx.1.2, hx.1.1, hx.2⟩
  have h1 : ((S.erase a).filter (fun x => G.Adj a x)).card < 2 ^ ((s - 1) + t) := by
    refine ih ((s - 1) + t) (by omega) (s - 1) t rfl _ ?_ ?_
    · intro K hKs hKc
      have hnot : a ∉ K := fun h => (mem_of (hKs h)).2.1 rfl
      have hbig := hK (insert a K) (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ha
        · exact (mem_of (hKs hx)).1) (by
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxa | hx' <;>
          rcases Finset.mem_insert.mp hy with hya | hy'
        · exact absurd (hxa.trans hya.symm) hxy
        · rw [hxa]; exact (mem_of (hKs hy')).2.2
        · rw [hya]; exact ((mem_of (hKs hx')).2.2).symm
        · exact hKc x hx' y hy' hxy)
      rw [Finset.card_insert_of_notMem hnot] at hbig
      omega
    · intro I hIs hIi
      exact hI I (fun x hx => (mem_of (hIs hx)).1) hIi
  have h2 : ((S.erase a).filter (fun x => ¬ G.Adj a x)).card < 2 ^ (s + (t - 1)) := by
    refine ih (s + (t - 1)) (by omega) s (t - 1) rfl _ ?_ ?_
    · intro K hKs hKc
      exact hK K (fun x hx => (mem_of (hKs hx)).1) hKc
    · intro I hIs hIi
      have hnot : a ∉ I := fun h => (mem_of (hIs h)).2.1 rfl
      have hbig := hI (insert a I) (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ha
        · exact (mem_of (hIs hx)).1) (by
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxa | hx' <;>
          rcases Finset.mem_insert.mp hy with hya | hy'
        · exact absurd (hxa.trans hya.symm) hxy
        · rw [hxa]; exact (mem_of (hIs hy')).2.2
        · rw [hya]; exact fun h => (mem_of (hIs hx')).2.2 h.symm
        · exact hIi x hx' y hy' hxy)
      rw [Finset.card_insert_of_notMem hnot] at hbig
      omega
  have e1 : 2 ^ ((s - 1) + t) = 2 ^ (s + t - 1) := by congr 1; omega
  have e2 : 2 ^ (s + (t - 1)) = 2 ^ (s + t - 1) := by congr 1; omega
  have e3 : 2 ^ (s + t) = 2 * 2 ^ (s + t - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- Greedy colouring: a finite graph whose degrees are at most `D` is `D + 1`-colourable. -/
theorem colorable_of_degree_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, (G.neighborFinset v).card ≤ D) :
    G.Colorable (D + 1) := by
  have key : ∀ S : Finset V, ∃ c : V → Fin (D + 1),
      ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      have hlt : ((G.neighborFinset a).image c).card < (Finset.univ : Finset (Fin (D + 1))).card := by
        calc ((G.neighborFinset a).image c).card ≤ (G.neighborFinset a).card := Finset.card_image_le
          _ ≤ D := hD a
          _ < D + 1 := Nat.lt_succ_self D
          _ = (Finset.univ : Finset (Fin (D + 1))).card := by simp
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨Function.update c a k, ?_⟩
      intro u hu v hv huv
      by_cases hua : u = a
      · subst hua
        have hva : v ≠ u := fun h => huv.ne h.symm
        rw [Function.update_self, Function.update_of_ne hva]
        intro hkv
        apply hk
        rw [hkv]
        exact Finset.mem_image_of_mem c ((G.mem_neighborFinset u v).mpr huv)
      · by_cases hva : v = a
        · subst hva
          rw [Function.update_self, Function.update_of_ne hua]
          intro hkv
          apply hk
          rw [← hkv]
          exact Finset.mem_image_of_mem c ((G.mem_neighborFinset v u).mpr huv.symm)
        · rw [Function.update_of_ne hua, Function.update_of_ne hva]
          exact hc u ((Finset.mem_insert.mp hu).resolve_left hua) v
            ((Finset.mem_insert.mp hv).resolve_left hva) huv
  obtain ⟨c, hc⟩ := key Finset.univ
  exact ⟨Coloring.mk c (fun {u v} h => hc u (Finset.mem_univ _) v (Finset.mem_univ _) h)⟩

/-- A tree in which every vertex is within distance one of `c` is a star centred at `c`. -/
theorem star_adj_iff {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.IsTree)
    (c : W) (hc : ∀ w, T.dist c w ≤ 1) (a b : W) :
    T.Adj a b ↔ (a = c ∧ b ≠ c) ∨ (a ≠ c ∧ b = c) := by
  have adjc : ∀ w, w ≠ c → T.Adj c w := by
    intro w hw
    rw [← SimpleGraph.dist_eq_one_iff_adj]
    have h1 := hc w
    have h0 : T.dist c w ≠ 0 := fun h => hw ((hT.connected.dist_eq_zero_iff.mp h).symm)
    omega
  constructor
  · intro h
    by_cases ha : a = c
    · subst ha
      exact Or.inl ⟨rfl, fun hb => h.ne hb.symm⟩
    · by_cases hb : b = c
      · exact Or.inr ⟨ha, hb⟩
      · exfalso
        have hab : a ≠ b := h.ne
        have hca := adjc a ha
        have hcb := adjc b hb
        apply hT.isAcyclic (Walk.cons hca (Walk.cons h (Walk.cons hcb.symm Walk.nil)))
        rw [Walk.cons_isCycle_iff]
        refine ⟨?_, ?_⟩
        · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
          simp only [Walk.IsPath.nil, Walk.support_cons, Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false, true_and]
          exact ⟨fun h' => hb h', fun h' => h'.elim hab ha⟩
        · simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false,
            Sym2.eq_iff]
          intro h'
          rcases h' with (⟨h1, _⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨_, h1⟩)
          · exact ha h1.symm
          · exact hb h1.symm
          · exact hb h1.symm
          · exact hab h1
  · rintro (⟨rfl, hb⟩ | ⟨ha, rfl⟩)
    · exact adjc b hb
    · exact (adjc a ha).symm

/-- A vertex with `|W| - 1` pairwise non-adjacent neighbours yields an induced copy of a star on
`W` centred at `c`. -/
theorem star_isIndContained {W V : Type} [Fintype W] [DecidableEq W] [DecidableEq V]
    (T : SimpleGraph W) (G : SimpleGraph V) (c : W)
    (hstar : ∀ a b, T.Adj a b ↔ (a = c ∧ b ≠ c) ∨ (a ≠ c ∧ b = c))
    (v : V) (I : Finset V) (hIadj : ∀ x ∈ I, G.Adj v x)
    (hIind : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y)
    (hcard : I.card = Fintype.card W - 1) : T.IsIndContained G := by
  have hcardeq : Fintype.card {w : W // ¬ w = c} = Fintype.card I := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_coe, hcard]
  let e : {w : W // ¬ w = c} ≃ I := Fintype.equivOfCardEq hcardeq
  let f : W → V := fun w => if h : w = c then v else (e ⟨w, h⟩ : V)
  have fc : f c = v := by simp [f]
  have fne : ∀ w (h : ¬ w = c), f w = (e ⟨w, h⟩ : V) := by
    intro w h
    simp [f, h]
  have fmem : ∀ w (h : ¬ w = c), f w ∈ I := fun w h => by rw [fne w h]; exact (e ⟨w, h⟩).2
  have fnev : ∀ w (h : ¬ w = c), f w ≠ v := fun w h hfw =>
    (hIadj _ (fmem w h)).ne (by rw [hfw])
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a = c <;> by_cases hb : b = c
    · rw [ha, hb]
    · exact absurd (by rw [← hab, ha, fc]) (fnev b hb)
    · exact absurd (by rw [hab, hb, fc]) (fnev a ha)
    · rw [fne a ha, fne b hb] at hab
      have := e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
  refine ⟨{ toFun := f, inj' := hinj, map_rel_iff' := ?_ }⟩
  intro a b
  change G.Adj (f a) (f b) ↔ T.Adj a b
  rw [hstar]
  by_cases ha : a = c <;> by_cases hb : b = c
  · subst ha; subst hb
    simp
  · subst ha
    rw [fc]
    simp only [true_and, hb, not_false_eq_true, ne_eq, not_true_eq_false, false_and, or_false]
    exact iff_of_true (hIadj _ (fmem b hb)) trivial
  · subst hb
    rw [fc]
    simp only [ha, false_and, ne_eq, not_false_eq_true, and_self, or_true, iff_true]
    exact (hIadj _ (fmem a ha)).symm
  · simp only [ha, hb, false_and, ne_eq, not_false_eq_true, and_false, or_self, iff_false]
    intro hadj
    have hne : f a ≠ f b := fun h => (hadj.ne h)
    exact hIind _ (fmem a ha) _ (fmem b hb) hne hadj

end OMA.Helpers

open SimpleGraph in
theorem OMA.solution :
    OMA.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_variants_radius_two_R1.H1 := by
  intro W _ _ T _ hT hc
  obtain ⟨c, hc1, -⟩ := hc
  have hstar := OMA.Helpers.star_adj_iff T hT c hc1
  refine ⟨fun k => 2 ^ (k + Fintype.card W), ?_⟩
  intro V _ _ G _ hfree
  have hdeg : ∀ v, (G.neighborFinset v).card ≤ 2 ^ (G.cliqueNum + Fintype.card W) - 1 := by
    intro v
    have hb := OMA.Helpers.ramsey_pow_two G _ G.cliqueNum (Fintype.card W) rfl
      (G.neighborFinset v) ?_ ?_
    · omega
    · intro K hK hKc
      have hv : v ∉ K := fun h => G.irrefl ((G.mem_neighborFinset v v).mp (hK h))
      have hcl : G.IsClique ((insert v K : Finset V) : Set V) := by
        intro x hx y hy hxy
        rw [Finset.coe_insert] at hx hy
        rcases hx with hxa | hx' <;> rcases hy with hya | hy'
        · exact absurd (hxa.trans hya.symm) hxy
        · rw [hxa]; exact (G.mem_neighborFinset _ _).mp (hK hy')
        · rw [hya]; exact ((G.mem_neighborFinset _ _).mp (hK hx')).symm
        · exact hKc x hx' y hy' hxy
      have hle : (insert v K).card ≤ G.cliqueNum := hcl.card_le_cliqueNum
      rw [Finset.card_insert_of_notMem hv] at hle
      omega
    · intro I hI hIi
      by_contra hge
      rw [not_lt] at hge
      obtain ⟨J, hJI, hJc⟩ :=
        Finset.exists_subset_card_eq (show Fintype.card W - 1 ≤ I.card by omega)
      exact hfree (OMA.Helpers.star_isIndContained T G c hstar v J
        (fun x hx => (G.mem_neighborFinset _ _).mp (hI (hJI hx)))
        (fun x hx y hy hxy => hIi x (hJI hx) y (hJI hy) hxy) hJc)
  have hcol := OMA.Helpers.colorable_of_degree_le G _ hdeg
  have hpos : 0 < 2 ^ (G.cliqueNum + Fintype.card W) := by positivity
  rw [Nat.sub_add_cancel hpos] at hcol
  exact hcol.chromaticNumber_le
