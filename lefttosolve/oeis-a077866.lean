import OMAStatements.S_oeis_a077866
import Mathlib

namespace OMA.Helpers

open Finset

/-- Good subsets of `{1, ..., n}` written as `{x, y, x + y} ∪ T`. -/
def G (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).biUnion fun x => (Ioc x (n - x)).biUnion fun y =>
    (Ioo y (x + y)).powerset.image fun T => insert x (insert y (insert (x + y) T))

theorem key {x y : ℕ} {T S : Finset ℕ} (hxy : x < y) (hT : T ⊆ Ioo y (x + y))
    (hS : insert x (insert y (insert (x + y) T)) = S) :
    x ∈ S ∧ y ∈ S ∧ (∀ z ∈ S, x ≤ z) ∧ (∀ z ∈ S, z ≠ x → y ≤ z) := by
  subst hS
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro z hz
    simp only [mem_insert] at hz
    rcases hz with rfl | rfl | rfl | hz
    · exact le_refl _
    · omega
    · omega
    · have := hT hz
      simp only [mem_Ioo] at this
      omega
  · intro z hz hzx
    simp only [mem_insert] at hz
    rcases hz with rfl | rfl | rfl | hz
    · exact absurd rfl hzx
    · exact le_refl _
    · omega
    · have := hT hz
      simp only [mem_Ioo] at this
      omega

theorem b_eq_card (n : ℕ) : OMA.S_oeis_a077866.b n = (G n).card := by
  unfold OMA.S_oeis_a077866.b
  congr 1
  ext S
  simp only [mem_filter, mem_powerset, G, mem_biUnion, mem_image, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨hS, x, y, m, hx, hy, hm, hxy, hmin, hsec, hmax, hsum⟩
    subst hsum
    have hx' := hS hx
    have hm' := hS hm
    simp only [mem_Icc] at hx' hm'
    refine ⟨x, ⟨hx'.1, hx'.2⟩, y, ⟨hxy, by omega⟩,
      S.filter (fun z => y < z ∧ z < x + y), ?_, ?_⟩
    · intro z hz
      simp only [mem_filter] at hz
      simp only [mem_Ioo]
      exact hz.2
    · ext z
      simp only [mem_insert, mem_filter]
      constructor
      · rintro (rfl | rfl | rfl | ⟨hz, -⟩)
        · exact hx
        · exact hy
        · exact hm
        · exact hz
      · intro hz
        by_cases h : z = x
        · exact Or.inl h
        · have h3 := hsec z hz h
          have h4 := hmax z hz
          rcases eq_or_lt_of_le h3 with h5 | h5
          · exact Or.inr (Or.inl h5.symm)
          · rcases eq_or_lt_of_le h4 with h6 | h6
            · exact Or.inr (Or.inr (Or.inl h6))
            · exact Or.inr (Or.inr (Or.inr ⟨hz, h5, h6⟩))
  · rintro ⟨x, ⟨hx1, hxn⟩, y, ⟨hxy, hyn⟩, T, hT, hS⟩
    refine ⟨?_, ?_⟩
    · subst hS
      intro z hz
      simp only [mem_insert] at hz
      simp only [mem_Icc]
      rcases hz with rfl | rfl | rfl | hz
      · omega
      · omega
      · omega
      · have := hT hz
        simp only [mem_Ioo] at this
        omega
    · obtain ⟨h1, h2, h3, h4⟩ := key hxy hT hS
      refine ⟨x, y, x + y, h1, h2, ?_, hxy, h3, h4, ?_, rfl⟩
      · rw [← hS]; simp
      · subst hS
        intro z hz
        simp only [mem_insert] at hz
        rcases hz with rfl | rfl | rfl | hz
        · omega
        · omega
        · exact le_refl _
        · have := hT hz
          simp only [mem_Ioo] at this
          omega

theorem card_G (n : ℕ) :
    (G n).card = ∑ x ∈ Icc 1 n, ∑ _y ∈ Ioc x (n - x), 2 ^ (x - 1) := by
  rw [G, card_biUnion]
  · refine sum_congr rfl (fun x hx => ?_)
    rw [card_biUnion]
    · refine sum_congr rfl (fun y hy => ?_)
      simp only [mem_Ioc] at hy
      rw [card_image_of_injOn, card_powerset, Nat.card_Ioo]
      · congr 1
        omega
      · intro T1 hT1 T2 hT2 heq
        simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hT1 hT2
        simp only at heq
        ext z
        constructor
        · intro hz
          have hz' := hT1 hz
          simp only [mem_Ioo] at hz'
          have : z ∈ insert x (insert y (insert (x + y) T2)) := by
            rw [← heq]; simp [hz]
          simp only [mem_insert] at this
          rcases this with h | h | h | h
          · omega
          · omega
          · omega
          · exact h
        · intro hz
          have hz' := hT2 hz
          simp only [mem_Ioo] at hz'
          have : z ∈ insert x (insert y (insert (x + y) T1)) := by
            rw [heq]; simp [hz]
          simp only [mem_insert] at this
          rcases this with h | h | h | h
          · omega
          · omega
          · omega
          · exact h
    · intro y1 hy1 y2 hy2 hne
      simp only [coe_Ioc, Set.mem_Ioc] at hy1 hy2
      rw [Function.onFun, disjoint_left]
      intro S hS1 hS2
      simp only [mem_image, mem_powerset] at hS1 hS2
      obtain ⟨T1, hT1, e1⟩ := hS1
      obtain ⟨T2, hT2, e2⟩ := hS2
      obtain ⟨-, a2, -, a4⟩ := key hy1.1 hT1 e1
      obtain ⟨-, b2, -, b4⟩ := key hy2.1 hT2 e2
      have := a4 y2 b2 (by omega)
      have := b4 y1 a2 (by omega)
      omega
  · intro x1 hx1 x2 hx2 hne
    rw [Function.onFun, disjoint_left]
    intro S hS1 hS2
    simp only [mem_biUnion, mem_image, mem_powerset, mem_Ioc] at hS1 hS2
    obtain ⟨y1, hy1, T1, hT1, e1⟩ := hS1
    obtain ⟨y2, hy2, T2, hT2, e2⟩ := hS2
    obtain ⟨a1, -, a3, -⟩ := key hy1.1 hT1 e1
    obtain ⟨b1, -, b3, -⟩ := key hy2.1 hT2 e2
    have := a3 x2 b1
    have := b3 x1 a1
    omega

/-- Explicit sum: `c n = ∑_{j} 2^j (n + 1 - 2 j)`. -/
def c (n : ℕ) : ℕ := ∑ j ∈ range (n + 3), 2 ^ j * (n + 1 - 2 * j)

theorem b_eq_c (n : ℕ) : OMA.S_oeis_a077866.b (n + 3) = c n := by
  rw [b_eq_card, card_G]
  simp only [sum_const, Nat.card_Ioc, smul_eq_mul]
  have e : Icc 1 (n + 3) = Ico 1 (n + 3 + 1) := by
    ext z; simp only [mem_Icc, mem_Ico]; omega
  rw [e, sum_Ico_eq_sum_range, c]
  have e2 : n + 3 + 1 - 1 = n + 3 := by omega
  rw [e2]
  refine sum_congr rfl (fun j _ => ?_)
  have e3 : 1 + j - 1 = j := by omega
  have e4 : n + 3 - (1 + j) - (1 + j) = n + 1 - 2 * j := by omega
  rw [e3, e4, mul_comm]

theorem c_rec (n : ℕ) : c (n + 2) = 2 * c n + (n + 3) := by
  have h1 : c (n + 2) = ∑ j ∈ range (n + 4), 2 * (2 ^ j * (n + 1 - 2 * j)) + (n + 3) := by
    rw [c, show n + 2 + 3 = (n + 4) + 1 by omega, sum_range_succ']
    congr 1
    · refine sum_congr rfl (fun j _ => ?_)
      rw [pow_succ]
      have : n + 2 + 1 - 2 * (j + 1) = n + 1 - 2 * j := by omega
      rw [this]
      ring
    · simp
  rw [h1, ← mul_sum, c, show n + 4 = (n + 3) + 1 by omega, sum_range_succ]
  have : n + 1 - 2 * (n + 3) = 0 := by omega
  rw [this]
  ring

theorem a_rec (n : ℕ) :
    OMA.S_oeis_a077866.a (n + 2) = 2 * OMA.S_oeis_a077866.a n + (n + 3) ∧
    OMA.S_oeis_a077866.a (n + 3) = 2 * OMA.S_oeis_a077866.a (n + 1) + (n + 4) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    refine ⟨by push_cast; linarith [ih.2], ?_⟩
    have e : OMA.S_oeis_a077866.a (k + 4) = 2 * OMA.S_oeis_a077866.a (k + 3) +
        OMA.S_oeis_a077866.a (k + 2) - 4 * OMA.S_oeis_a077866.a (k + 1) +
        2 * OMA.S_oeis_a077866.a k := rfl
    rw [show k + 1 + 3 = k + 4 by omega, e]
    push_cast
    linarith [ih.1, ih.2]

theorem c_eq_a (n : ℕ) : ((c n : ℕ) : ℤ) = OMA.S_oeis_a077866.a n ∧
    ((c (n + 1) : ℕ) : ℤ) = OMA.S_oeis_a077866.a (n + 1) := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 1 = k + 2 by omega, c_rec, (a_rec k).1]
    push_cast
    rw [ih.1]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a077866.main := by
  refine ⟨?_, ?_, ?_, fun n => ?_⟩
  · rw [OMA.Helpers.b_eq_card, OMA.Helpers.card_G]; decide
  · rw [OMA.Helpers.b_eq_card, OMA.Helpers.card_G]; decide
  · rw [OMA.Helpers.b_eq_card, OMA.Helpers.card_G]; decide
  · rw [OMA.Helpers.b_eq_c]
    exact (OMA.Helpers.c_eq_a n).1
