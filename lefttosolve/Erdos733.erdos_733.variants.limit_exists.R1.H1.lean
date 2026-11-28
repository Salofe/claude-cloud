import OMAReductions.R_Erdos733_erdos_733_variants_limit_exists_R1
import Mathlib

/-!
# Step H1 of the reduction Erdos733.erdos_733.variants.limit_exists.R1

Two facts about the number of all-lines sequences of n points in the plane.

* Finiteness and positivity: a line with two points of P is determined by any two of them, so
  such lines inject into pairs of points of P. Hence each sequence has length at most n^2 and
  entries at most n, so there are finitely many; there is at least one, from any n points.
* Monotonicity: given a configuration P of n points, pick a point x outside P and off every line
  through two points of P (a finite union of lines and points is Lebesgue-null in the plane).
  The lines of P together with x are the old lines (with unchanged counts) and the n new lines
  through x and a point of P, each with exactly two points. So the sequence X becomes the sorted
  version of X plus n copies of 2, which is injective in X.
-/

open Erdos733 EuclideanGeometry MeasureTheory

namespace OMA.Helpers

theorem e733_pair_isLine {p q : ℝ²} (h : p ≠ q) : IsLine (line[ℝ, p, q]) := by
  unfold IsLine
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr h)

theorem e733_line_eq_pair (ℓ : Line) {p q : ℝ²} (hp : p ∈ ℓ.1) (hq : q ∈ ℓ.1) (h : p ≠ q) :
    line[ℝ, p, q] = ℓ.1 := by
  have hle : line[ℝ, p, q] ≤ ℓ.1 := affineSpan_pair_le_of_mem_of_mem hp hq
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ ⟨p, left_mem_affineSpan_pair ℝ p q⟩ hle
  apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
  have h1 : Module.finrank ℝ (line[ℝ, p, q]).direction = 1 := e733_pair_isLine h
  have h2 : Module.finrank ℝ ℓ.1.direction = 1 := ℓ.2.2
  rw [h1, h2]

theorem e733_two_le_iff (P : Finset ℝ²) (ℓ : Line) :
    2 ≤ lineCount P ℓ ↔ ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ p ∈ ℓ.1 ∧ q ∈ ℓ.1 := by
  classical
  unfold lineCount
  rw [show ∀ c : ℕ, 2 ≤ c ↔ 1 < c from fun c => by omega, Finset.one_lt_card]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [Finset.mem_filter] at ha hb
    exact ⟨a, ha.1, b, hb.1, hab, ha.2, hb.2⟩
  · rintro ⟨a, ha, b, hb, hab, ha', hb'⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, ha'⟩, b, Finset.mem_filter.mpr ⟨hb, hb'⟩, hab⟩

theorem e733_count_insert {P : Finset ℝ²} {x : ℝ²} {ℓ : Line} (hx : x ∉ ℓ.1) :
    lineCount (insert x P) ℓ = lineCount P ℓ := by
  classical
  unfold lineCount
  rw [Finset.filter_insert, if_neg hx]

theorem e733_count_le (P : Finset ℝ²) (ℓ : Line) : lineCount P ℓ ≤ P.card := by
  classical
  unfold lineCount
  exact Finset.card_filter_le _ _

/-- Lines with two points of `P` inject into pairs of points of `P`. -/
theorem e733_lines_inj (P : Finset ℝ²) :
    ∃ f : Line → ℝ² × ℝ², Set.MapsTo f {ℓ | 2 ≤ lineCount P ℓ} (P ×ˢ P : Finset (ℝ² × ℝ²)) ∧
      Set.InjOn f {ℓ | 2 ≤ lineCount P ℓ} := by
  have h : ∀ ℓ ∈ {ℓ : Line | 2 ≤ lineCount P ℓ}, ∃ pq : ℝ² × ℝ², pq.1 ∈ P ∧ pq.2 ∈ P ∧
      pq.1 ≠ pq.2 ∧ pq.1 ∈ ℓ.1 ∧ pq.2 ∈ ℓ.1 := by
    intro ℓ hℓ
    obtain ⟨a, ha, b, hb, hab, ha', hb'⟩ := (e733_two_le_iff P ℓ).mp hℓ
    exact ⟨(a, b), ha, hb, hab, ha', hb'⟩
  choose! f hf using h
  refine ⟨f, fun ℓ hℓ => ?_, fun ℓ hℓ ℓ' hℓ' he => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hf ℓ hℓ
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨h1, h2⟩
  · obtain ⟨-, -, h3, h4, h5⟩ := hf ℓ hℓ
    obtain ⟨-, -, h3', h4', h5'⟩ := hf ℓ' hℓ'
    apply Subtype.ext
    rw [← e733_line_eq_pair ℓ h4 h5 h3, ← e733_line_eq_pair ℓ' h4' h5' h3', he]

theorem e733_lines_finite (P : Finset ℝ²) : {ℓ : Line | 2 ≤ lineCount P ℓ}.Finite := by
  obtain ⟨f, hm, hi⟩ := e733_lines_inj P
  exact Set.Finite.of_injOn hm hi (Finset.finite_toSet _)

theorem e733_card_le (P : Finset ℝ²) (L : Finset Line) (hL : ∀ ℓ ∈ L, 2 ≤ lineCount P ℓ) :
    L.card ≤ P.card * P.card := by
  obtain ⟨f, hm, hi⟩ := e733_lines_inj P
  rw [← Finset.card_product]
  exact Finset.card_le_card_of_injOn f (fun ℓ hℓ => hm (hL ℓ hℓ))
    (fun ℓ hℓ ℓ' hℓ' he => hi (hL ℓ hℓ) (hL ℓ' hℓ') he)

theorem e733_finite (n : ℕ) : (allLinesSequences n).Finite := by
  apply ((List.finite_length_le (Fin (n + 1)) (n * n)).image (List.map Fin.val)).subset
  rintro X ⟨P, hP, L, hL, rfl⟩
  have hmem : ∀ a ∈ lineSizeSequence P L, a < n + 1 := by
    intro a ha
    unfold lineSizeSequence lineSizeMultiset at ha
    rw [Multiset.mem_sort, Multiset.mem_map] at ha
    obtain ⟨ℓ, -, rfl⟩ := ha
    have := e733_count_le P ℓ
    omega
  refine ⟨(lineSizeSequence P L).attach.map (fun a => (⟨a.1, hmem a.1 a.2⟩ : Fin (n + 1))), ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, List.length_map, List.length_attach]
    unfold lineSizeSequence lineSizeMultiset
    rw [Multiset.length_sort, Multiset.card_map, ← hP]
    exact e733_card_le P L (fun ℓ hℓ => (hL ℓ).mp hℓ)
  · simp only [List.map_map]
    exact List.attach_map_subtype_val _

theorem e733_generic (P : Finset ℝ²) (L : Finset Line) :
    ∃ x : ℝ², x ∉ P ∧ ∀ ℓ ∈ L, x ∉ ℓ.1 := by
  have hne : ∀ ℓ : Line, ℓ.1 ≠ ⊤ := by
    intro ℓ h
    have h2 : Module.finrank ℝ ℓ.1.direction = 1 := ℓ.2.2
    rw [h, AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace_fin] at h2
    omega
  have hnull : volume ((⋃ ℓ ∈ (L : Set Line), (ℓ.1 : Set ℝ²)) ∪ (P : Set ℝ²)) = 0 := by
    apply measure_union_null
    · exact (measure_biUnion_null_iff L.countable_toSet).mpr
        (fun ℓ _ => Measure.addHaar_affineSubspace volume ℓ.1 (hne ℓ))
    · exact P.finite_toSet.measure_zero volume
  by_contra hcon
  push Not at hcon
  have huniv : (⋃ ℓ ∈ (L : Set Line), (ℓ.1 : Set ℝ²)) ∪ (P : Set ℝ²) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe, Set.mem_univ, iff_true]
    by_cases hx : x ∈ P
    · exact Or.inr hx
    · obtain ⟨ℓ, hℓ, hxℓ⟩ := hcon x hx
      exact Or.inl ⟨ℓ, hℓ, hxℓ⟩
  rw [huniv] at hnull
  exact (isOpen_univ.measure_ne_zero (μ := (volume : Measure ℝ²)) Set.univ_nonempty) hnull

theorem e733_nonempty (n : ℕ) : (allLinesSequences n).Nonempty := by
  classical
  have : Infinite ℝ² := inferInstance
  obtain ⟨P, hP⟩ := Infinite.exists_subset_card_eq ℝ² n
  exact ⟨_, P, hP, (e733_lines_finite P).toFinset, fun ℓ => by simp, rfl⟩

theorem e733_step (n : ℕ) :
    (allLinesSequences n).ncard ≤ (allLinesSequences (n + 1)).ncard := by
  classical
  let f : List ℕ → List ℕ := fun X => ((X : Multiset ℕ) + Multiset.replicate n 2).sort (· ≤ ·)
  have hsorted : ∀ X ∈ allLinesSequences n, (X : Multiset ℕ).sort (· ≤ ·) = X := by
    rintro X ⟨P, -, L, -, rfl⟩
    unfold lineSizeSequence
    rw [Multiset.sort_eq]
  apply Set.ncard_le_ncard_of_injOn f _ _ (e733_finite (n + 1))
  · rintro X ⟨P, hP, L, hL, rfl⟩
    obtain ⟨x, hxP, hxL⟩ := e733_generic P L
    have hxp : ∀ p ∈ P, x ≠ p := fun p hp h => hxP (h ▸ hp)
    let g : P → Line := fun p => ⟨line[ℝ, x, p.1], ⟨x, left_mem_affineSpan_pair ℝ x p.1⟩,
      e733_pair_isLine (hxp p.1 p.2)⟩
    have hone : ∀ ℓ : Line, x ∈ ℓ.1 → ∀ p ∈ P, ∀ q ∈ P, p ∈ ℓ.1 → q ∈ ℓ.1 → p = q := by
      intro ℓ hx p hp q hq hpl hql
      by_contra hpq
      have hmem : ℓ ∈ L := (hL ℓ).mpr ((e733_two_le_iff P ℓ).mpr ⟨p, hp, q, hq, hpq, hpl, hql⟩)
      exact hxL ℓ hmem hx
    have hginj : Function.Injective g := by
      intro p q hpq
      apply Subtype.ext
      apply hone (g p) (left_mem_affineSpan_pair ℝ x p.1) p.1 p.2 q.1 q.2
        (right_mem_affineSpan_pair ℝ x p.1)
      rw [hpq]
      exact right_mem_affineSpan_pair ℝ x q.1
    let T : Finset Line := P.attach.map ⟨g, hginj⟩
    have hdisj : Disjoint L T := by
      rw [Finset.disjoint_left]
      intro ℓ hℓL hℓT
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hℓT
      exact hxL _ hℓL (left_mem_affineSpan_pair ℝ x p.1)
    have hcountT : ∀ p : P, lineCount (insert x P) (g p) = 2 := by
      intro p
      apply le_antisymm
      · unfold lineCount
        calc _ ≤ ({x, p.1} : Finset ℝ²).card := by
              apply Finset.card_le_card
              intro r hr
              rw [Finset.mem_filter, Finset.mem_insert] at hr
              rcases hr with ⟨rfl | hrP, hrl⟩
              · exact Finset.mem_insert_self _ _
              · rw [hone (g p) (left_mem_affineSpan_pair ℝ x p.1) r hrP p.1 p.2 hrl
                  (right_mem_affineSpan_pair ℝ x p.1)]
                exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          _ ≤ 2 := Finset.card_le_two
      · exact (e733_two_le_iff _ _).mpr ⟨x, Finset.mem_insert_self _ _, p.1,
          Finset.mem_insert_of_mem p.2, hxp p.1 p.2, left_mem_affineSpan_pair ℝ x p.1,
          right_mem_affineSpan_pair ℝ x p.1⟩
    have hm : lineSizeMultiset (insert x P) (L.disjUnion T hdisj) =
        (lineSizeSequence P L : Multiset ℕ) + Multiset.replicate n 2 := by
      unfold lineSizeSequence
      rw [Multiset.sort_eq]
      unfold lineSizeMultiset
      rw [show (L.disjUnion T hdisj).val = L.val + T.val from rfl, Multiset.map_add]
      congr 1
      · apply Multiset.map_congr rfl
        intro ℓ hℓ
        exact e733_count_insert (hxL ℓ (Finset.mem_val.mp hℓ))
      · rw [Finset.map_val, Multiset.map_map]
        have hc : ∀ p ∈ P.attach.val,
            (lineCount (insert x P) ∘ ⇑(⟨g, hginj⟩ : P ↪ Line)) p = (fun _ => 2) p :=
          fun p _ => hcountT p
        rw [Multiset.map_congr rfl hc, Multiset.map_const']
        rw [← hP, ← Finset.card_attach (s := P)]
        rfl
    refine ⟨insert x P, by rw [Finset.card_insert_of_notMem hxP, hP], L.disjUnion T hdisj, ?_, ?_⟩
    · intro ℓ
      rw [Finset.mem_disjUnion]
      constructor
      · rintro (hℓ | hℓ)
        · rw [e733_count_insert (hxL ℓ hℓ)]
          exact (hL ℓ).mp hℓ
        · obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hℓ
          exact (hcountT p).ge
      · intro h2
        by_cases hx : x ∈ ℓ.1
        · right
          obtain ⟨a, ha, b, hb, hab, ha', hb'⟩ := (e733_two_le_iff _ ℓ).mp h2
          have hr : ∃ r ∈ P, r ∈ ℓ.1 := by
            by_cases hax : a = x
            · subst hax
              rcases Finset.mem_insert.mp hb with hbx | hbP
              · exact absurd hbx.symm hab
              · exact ⟨b, hbP, hb'⟩
            · rcases Finset.mem_insert.mp ha with hax' | haP
              · exact absurd hax' hax
              · exact ⟨a, haP, ha'⟩
          obtain ⟨r, hrP, hrl⟩ := hr
          apply Finset.mem_map.mpr
          refine ⟨⟨r, hrP⟩, Finset.mem_attach _ _, ?_⟩
          apply Subtype.ext
          exact e733_line_eq_pair ℓ hx hrl (hxp r hrP)
        · left
          rw [e733_count_insert hx] at h2
          exact (hL ℓ).mpr h2
    · show _ = (lineSizeMultiset (insert x P) (L.disjUnion T hdisj)).sort (· ≤ ·)
      rw [hm]
  · intro X hX Y hY hXY
    have h1 : (X : Multiset ℕ) + Multiset.replicate n 2 = (Y : Multiset ℕ) + Multiset.replicate n 2 := by
      have := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hXY
      simpa only [f, Multiset.sort_eq] using this
    have h2 : (X : Multiset ℕ) = Y := add_right_cancel h1
    rw [← hsorted X hX, ← hsorted Y hY, h2]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos733_erdos_733_variants_limit_exists_R1.H1 :=
  ⟨monotone_nat_of_le_succ e733_step,
    fun n => (Set.ncard_pos (e733_finite n)).mpr (e733_nonempty n)⟩
