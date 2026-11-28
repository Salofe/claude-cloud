import OMAReductions.R_Erdos963_erdos_963_parts_ii_R1

/-!
# Step H3 of the reduction Erdos963.erdos_963.parts.ii.R1

A set `X` of seven integers in which no five-element subset is affinely dissociated (no two
distinct disjoint subsets of equal size with equal sums) is a symmetric configuration
`{x, x ± a, x ± b, x ± (a + b)}` with `0 < a < b`.

Proof. Sort `X` as `x0 < x1 < ... < x6`. A five-element set `y0 < y1 < y2 < y3 < y4` fails to be
affinely dissociated only through two disjoint pairs with equal sums, and as the elements are
sorted this means `p + s = q + r` for one of its five sorted four-element subsets `p < q < r < s`.
So each five-element subset of `X` yields a disjunction of five linear equations in the `xi`.
A case analysis on thirteen of these disjunctions (found by a computer search; every leaf is
closed by linear arithmetic, either as a contradiction with `x0 < ... < x6` or because the
chosen equations already force the conclusion) gives
`x0 + x6 = x1 + x5 = x2 + x4 = 2 x3` and `x0 + x3 = x1 + x2`, which is the symmetric shape
with `x = x3`, `a = x3 - x2`, `b = x3 - x1`.
-/

namespace OMA.Helpers

/-- A sorted quadruple `p < r < s < q` inside a sorted five-element set with `p + q = r + s` is
one of the five sorted four-element subsets with outer sum equal to inner sum. -/
theorem e963_quad {y0 y1 y2 y3 y4 p r s q : ℤ} (h01 : y0 < y1) (h12 : y1 < y2)
    (h23 : y2 < y3) (h34 : y3 < y4)
    (hp : p ∈ ({y0, y1, y2, y3, y4} : Finset ℤ)) (hr : r ∈ ({y0, y1, y2, y3, y4} : Finset ℤ))
    (hs : s ∈ ({y0, y1, y2, y3, y4} : Finset ℤ)) (hq : q ∈ ({y0, y1, y2, y3, y4} : Finset ℤ))
    (hpr : p < r) (hrs : r < s) (hsq : s < q) (he : p + q = r + s) :
    y1 + y4 = y2 + y3 ∨ y0 + y4 = y2 + y3 ∨ y0 + y4 = y1 + y3 ∨ y0 + y4 = y1 + y2 ∨
      y0 + y3 = y1 + y2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hr hs hq
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl <;>
    omega

/-- Five strictly increasing integers form a five-element finset. -/
theorem e963_card5 {y0 y1 y2 y3 y4 : ℤ} (h01 : y0 < y1) (h12 : y1 < y2) (h23 : y2 < y3)
    (h34 : y3 < y4) : ({y0, y1, y2, y3, y4} : Finset ℤ).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_pair (by omega)]

/-- A sorted five-element set that is not affinely dissociated satisfies one of five equations. -/
theorem e963_five {y0 y1 y2 y3 y4 : ℤ} (h01 : y0 < y1) (h12 : y1 < y2) (h23 : y2 < y3)
    (h34 : y3 < y4)
    (h : ¬ ∀ T ⊆ ({y0, y1, y2, y3, y4} : Finset ℤ), ∀ S ⊆ ({y0, y1, y2, y3, y4} : Finset ℤ),
      Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S) :
    y1 + y4 = y2 + y3 ∨ y0 + y4 = y2 + y3 ∨ y0 + y4 = y1 + y3 ∨ y0 + y4 = y1 + y2 ∨
      y0 + y3 = y1 + y2 := by
  by_contra hne
  apply h
  intro T hT S hS hd hc hsum
  have hU := Finset.card_le_card (Finset.union_subset hT hS)
  rw [Finset.card_union_of_disjoint hd, e963_card5 h01 h12 h23 h34] at hU
  obtain hk | hk | hk : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  · rw [Finset.card_eq_zero.mp hk, Finset.card_eq_zero.mp (hc.symm.trans hk)]
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hk
    obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp (hc.symm.trans hk)
    simp only [Finset.sum_singleton, id] at hsum
    rw [hsum]
  · exfalso
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hk
    obtain ⟨r, s, hrs, rfl⟩ := Finset.card_eq_two.mp (hc.symm.trans hk)
    rw [Finset.sum_pair hpq, Finset.sum_pair hrs] at hsum
    simp only [id] at hsum
    have hp' := Finset.disjoint_left.mp hd (Finset.mem_insert_self p {q})
    have hq' := Finset.disjoint_left.mp hd (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp' hq'
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hT hS
    obtain ⟨hp, hq⟩ := hT
    obtain ⟨hr, hs⟩ := hS
    apply hne
    rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hrs with h2 | h2
    · rcases lt_or_gt_of_ne hp'.1 with h3 | h3
      · exact e963_quad h01 h12 h23 h34 hp hr hs hq h3 h2 (by omega) (by omega)
      · exact e963_quad h01 h12 h23 h34 hr hp hq hs h3 h1 (by omega) (by omega)
    · rcases lt_or_gt_of_ne hp'.2 with h3 | h3
      · exact e963_quad h01 h12 h23 h34 hp hs hr hq h3 h2 (by omega) (by omega)
      · exact e963_quad h01 h12 h23 h34 hs hp hq hr h3 h1 (by omega) (by omega)
    · rcases lt_or_gt_of_ne hq'.1 with h3 | h3
      · exact e963_quad h01 h12 h23 h34 hq hr hs hp h3 h2 (by omega) (by omega)
      · exact e963_quad h01 h12 h23 h34 hr hq hp hs h3 h1 (by omega) (by omega)
    · rcases lt_or_gt_of_ne hq'.2 with h3 | h3
      · exact e963_quad h01 h12 h23 h34 hq hs hr hp h3 h2 (by omega) (by omega)
      · exact e963_quad h01 h12 h23 h34 hs hq hp hr h3 h1 (by omega) (by omega)

/-- Five strictly increasing members of `X`, under the hypothesis of the step, satisfy one of the
five equations. -/
theorem e963_from {X : Finset ℤ}
    (hno : ∀ F ⊆ X, F.card = 5 → ¬ ∀ T ⊆ F, ∀ S ⊆ F, Disjoint T S → T.card = S.card →
      T.sum id = S.sum id → T = S)
    {y0 y1 y2 y3 y4 : ℤ} (h01 : y0 < y1) (h12 : y1 < y2) (h23 : y2 < y3) (h34 : y3 < y4)
    (m0 : y0 ∈ X) (m1 : y1 ∈ X) (m2 : y2 ∈ X) (m3 : y3 ∈ X) (m4 : y4 ∈ X) :
    y1 + y4 = y2 + y3 ∨ y0 + y4 = y2 + y3 ∨ y0 + y4 = y1 + y3 ∨ y0 + y4 = y1 + y2 ∨
      y0 + y3 = y1 + y2 := by
  apply e963_five h01 h12 h23 h34
  apply hno _ _ (e963_card5 h01 h12 h23 h34)
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- The case analysis on thirteen of the twenty-one five-element subsets. -/
theorem e963_core (x0 x1 x2 x3 x4 x5 x6 : ℤ) (h0 : x0 < x1) (h1 : x1 < x2) (h2 : x2 < x3)
    (h3 : x3 < x4) (h4 : x4 < x5) (h5 : x5 < x6)
    (d01234 : x1 + x4 = x2 + x3 ∨ x0 + x4 = x2 + x3 ∨ x0 + x4 = x1 + x3 ∨ x0 + x4 = x1 + x2 ∨ x0 + x3 = x1 + x2)
    (d01235 : x1 + x5 = x2 + x3 ∨ x0 + x5 = x2 + x3 ∨ x0 + x5 = x1 + x3 ∨ x0 + x5 = x1 + x2 ∨ x0 + x3 = x1 + x2)
    (d01236 : x1 + x6 = x2 + x3 ∨ x0 + x6 = x2 + x3 ∨ x0 + x6 = x1 + x3 ∨ x0 + x6 = x1 + x2 ∨ x0 + x3 = x1 + x2)
    (d01245 : x1 + x5 = x2 + x4 ∨ x0 + x5 = x2 + x4 ∨ x0 + x5 = x1 + x4 ∨ x0 + x5 = x1 + x2 ∨ x0 + x4 = x1 + x2)
    (d01246 : x1 + x6 = x2 + x4 ∨ x0 + x6 = x2 + x4 ∨ x0 + x6 = x1 + x4 ∨ x0 + x6 = x1 + x2 ∨ x0 + x4 = x1 + x2)
    (d01256 : x1 + x6 = x2 + x5 ∨ x0 + x6 = x2 + x5 ∨ x0 + x6 = x1 + x5 ∨ x0 + x6 = x1 + x2 ∨ x0 + x5 = x1 + x2)
    (d01345 : x1 + x5 = x3 + x4 ∨ x0 + x5 = x3 + x4 ∨ x0 + x5 = x1 + x4 ∨ x0 + x5 = x1 + x3 ∨ x0 + x4 = x1 + x3)
    (d01346 : x1 + x6 = x3 + x4 ∨ x0 + x6 = x3 + x4 ∨ x0 + x6 = x1 + x4 ∨ x0 + x6 = x1 + x3 ∨ x0 + x4 = x1 + x3)
    (d01356 : x1 + x6 = x3 + x5 ∨ x0 + x6 = x3 + x5 ∨ x0 + x6 = x1 + x5 ∨ x0 + x6 = x1 + x3 ∨ x0 + x5 = x1 + x3)
    (d02345 : x2 + x5 = x3 + x4 ∨ x0 + x5 = x3 + x4 ∨ x0 + x5 = x2 + x4 ∨ x0 + x5 = x2 + x3 ∨ x0 + x4 = x2 + x3)
    (d02456 : x2 + x6 = x4 + x5 ∨ x0 + x6 = x4 + x5 ∨ x0 + x6 = x2 + x5 ∨ x0 + x6 = x2 + x4 ∨ x0 + x5 = x2 + x4)
    (d03456 : x3 + x6 = x4 + x5 ∨ x0 + x6 = x4 + x5 ∨ x0 + x6 = x3 + x5 ∨ x0 + x6 = x3 + x4 ∨ x0 + x5 = x3 + x4)
    (d12356 : x2 + x6 = x3 + x5 ∨ x1 + x6 = x3 + x5 ∨ x1 + x6 = x2 + x5 ∨ x1 + x6 = x2 + x3 ∨ x1 + x5 = x2 + x3) :
    x0 + x6 = x3 + x3 ∧ x1 + x5 = x3 + x3 ∧ x2 + x4 = x3 + x3 ∧ x0 + x3 = x1 + x2 := by
  rcases d01234 with e0 | e0 | e0 | e0 | e0
  · rcases d12356 with e1 | e1 | e1 | e1 | e1
    · rcases d01356 with e2 | e2 | e2 | e2 | e2
      · omega
      · omega
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · rcases d01245 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · rcases d01346 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
        · rcases d03456 with e4 | e4 | e4 | e4 | e4
          · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · rcases d01345 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · rcases d02345 with e3 | e3 | e3 | e3 | e3
        · rcases d01236 with e4 | e4 | e4 | e4 | e4
          · omega
          · rcases d02456 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
    · rcases d03456 with e2 | e2 | e2 | e2 | e2
      · omega
      · omega
      · omega
      · rcases d01236 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · omega
        · omega
        · rcases d01246 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · omega
      · rcases d01235 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · omega
        · omega
        · rcases d01245 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · omega
    · rcases d02456 with e2 | e2 | e2 | e2 | e2
      · omega
      · omega
      · omega
      · rcases d01236 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · omega
        · omega
        · rcases d01356 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · omega
          · omega
      · rcases d01235 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · omega
        · omega
        · rcases d01246 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · omega
    · omega
    · omega
  · rcases d01235 with e1 | e1 | e1 | e1 | e1
    · omega
    · omega
    · omega
    · omega
    · rcases d01245 with e2 | e2 | e2 | e2 | e2
      · rcases d01345 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · rcases d01246 with e4 | e4 | e4 | e4 | e4
          · omega
          · rcases d03456 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
        · omega
        · omega
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · rcases d01256 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · rcases d01346 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
        · rcases d01356 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · rcases d03456 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
        · omega
        · omega
        · omega
      · omega
      · omega
  · rcases d01235 with e1 | e1 | e1 | e1 | e1
    · rcases d01245 with e2 | e2 | e2 | e2 | e2
      · omega
      · omega
      · rcases d02345 with e3 | e3 | e3 | e3 | e3
        · rcases d01246 with e4 | e4 | e4 | e4 | e4
          · rcases d02456 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · rcases d01356 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega
    · rcases d01236 with e2 | e2 | e2 | e2 | e2
      · omega
      · omega
      · omega
      · omega
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · omega
        · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · rcases d01256 with e4 | e4 | e4 | e4 | e4
          · rcases d01356 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
    · omega
    · omega
    · rcases d01245 with e2 | e2 | e2 | e2 | e2
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · omega
        · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · rcases d01256 with e4 | e4 | e4 | e4 | e4
          · rcases d01356 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases d01246 with e3 | e3 | e3 | e3 | e3
        · rcases d01256 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · rcases d02456 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
        · rcases d01356 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · omega
          · omega
        · omega
        · omega
        · omega
      · omega
      · omega
  · rcases d01235 with e1 | e1 | e1 | e1 | e1
    · rcases d02345 with e2 | e2 | e2 | e2 | e2
      · rcases d01236 with e3 | e3 | e3 | e3 | e3
        · omega
        · rcases d03456 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
      · omega
    · rcases d01236 with e2 | e2 | e2 | e2 | e2
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases d01236 with e2 | e2 | e2 | e2 | e2
      · rcases d01256 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · rcases d01346 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
      · rcases d02456 with e3 | e3 | e3 | e3 | e3
        · rcases d03456 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · omega
    · omega
  · rcases d01245 with e1 | e1 | e1 | e1 | e1
    · rcases d01246 with e2 | e2 | e2 | e2 | e2
      · omega
      · rcases d03456 with e3 | e3 | e3 | e3 | e3
        · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · omega
        · omega
        · omega
        · omega
      · rcases d01256 with e3 | e3 | e3 | e3 | e3
        · rcases d01356 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · rcases d02345 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega
    · rcases d01246 with e2 | e2 | e2 | e2 | e2
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases d01246 with e2 | e2 | e2 | e2 | e2
      · rcases d01256 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · rcases d01346 with e4 | e4 | e4 | e4 | e4
          · omega
          · omega
          · omega
          · omega
          · rcases d02456 with e5 | e5 | e5 | e5 | e5
            · omega
            · omega
            · omega
            · omega
            · omega
        · omega
        · omega
      · rcases d01356 with e3 | e3 | e3 | e3 | e3
        · omega
        · omega
        · rcases d03456 with e4 | e4 | e4 | e4 | e4
          · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · omega
    · omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos963_erdos_963_parts_ii_R1.H3 := by
  unfold OMA.R_Erdos963_erdos_963_parts_ii_R1.H3
  intro aff X hX hno
  have hno' : ∀ F ⊆ X, F.card = 5 → ¬ ∀ T ⊆ F, ∀ S ⊆ F, Disjoint T S → T.card = S.card →
      T.sum id = S.sum id → T = S := hno
  let f := X.orderEmbOfFin hX
  have hm : ∀ i, f i ∈ X := fun i => X.orderEmbOfFin_mem hX i
  have hlt : ∀ i j : Fin 7, i < j → f i < f j := fun i j h => f.strictMono h
  have o01 := hlt 0 1 (by decide)
  have o12 := hlt 1 2 (by decide)
  have o23 := hlt 2 3 (by decide)
  have o34 := hlt 3 4 (by decide)
  have o45 := hlt 4 5 (by decide)
  have o56 := hlt 5 6 (by decide)
  have d01234 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide))
    (hm 0) (hm 1) (hm 2) (hm 3) (hm 4)
  have d01235 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 5 (by decide))
    (hm 0) (hm 1) (hm 2) (hm 3) (hm 5)
  have d01236 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 6 (by decide))
    (hm 0) (hm 1) (hm 2) (hm 3) (hm 6)
  have d01245 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 4 (by decide)) (hlt 4 5 (by decide))
    (hm 0) (hm 1) (hm 2) (hm 4) (hm 5)
  have d01246 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 4 (by decide)) (hlt 4 6 (by decide))
    (hm 0) (hm 1) (hm 2) (hm 4) (hm 6)
  have d01256 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 5 (by decide)) (hlt 5 6 (by decide))
    (hm 0) (hm 1) (hm 2) (hm 5) (hm 6)
  have d01345 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 3 (by decide)) (hlt 3 4 (by decide)) (hlt 4 5 (by decide))
    (hm 0) (hm 1) (hm 3) (hm 4) (hm 5)
  have d01346 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 3 (by decide)) (hlt 3 4 (by decide)) (hlt 4 6 (by decide))
    (hm 0) (hm 1) (hm 3) (hm 4) (hm 6)
  have d01356 := e963_from hno' (hlt 0 1 (by decide)) (hlt 1 3 (by decide)) (hlt 3 5 (by decide)) (hlt 5 6 (by decide))
    (hm 0) (hm 1) (hm 3) (hm 5) (hm 6)
  have d02345 := e963_from hno' (hlt 0 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide)) (hlt 4 5 (by decide))
    (hm 0) (hm 2) (hm 3) (hm 4) (hm 5)
  have d02456 := e963_from hno' (hlt 0 2 (by decide)) (hlt 2 4 (by decide)) (hlt 4 5 (by decide)) (hlt 5 6 (by decide))
    (hm 0) (hm 2) (hm 4) (hm 5) (hm 6)
  have d03456 := e963_from hno' (hlt 0 3 (by decide)) (hlt 3 4 (by decide)) (hlt 4 5 (by decide)) (hlt 5 6 (by decide))
    (hm 0) (hm 3) (hm 4) (hm 5) (hm 6)
  have d12356 := e963_from hno' (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 5 (by decide)) (hlt 5 6 (by decide))
    (hm 1) (hm 2) (hm 3) (hm 5) (hm 6)
  obtain ⟨e1, e2, e3, e4⟩ := e963_core (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
    o01 o12 o23 o34 o45 o56
    d01234 d01235 d01236 d01245 d01246 d01256 d01345 d01346 d01356 d02345 d02456 d03456 d12356
  have hsub : ({f 0, f 1, f 2, f 3, f 4, f 5, f 6} : Finset ℤ) ⊆ X := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hm _
  have hcard : ({f 0, f 1, f 2, f 3, f 4, f 5, f 6} : Finset ℤ).card = 7 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_pair (by omega)]
  have hXe := Finset.eq_of_subset_of_card_le hsub (by rw [hX, hcard])
  refine ⟨f 3, f 3 - f 2, f 3 - f 1, by omega, by omega, ?_⟩
  rw [← hXe]
  ext t
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor <;> intro h <;> omega
