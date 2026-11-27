import OMAReductions.R_Erdos789_erdos_789_variants_sq_R1
import Mathlib

namespace OMA.Helpers

open Finset

/-- The set of sums of the `j`-element subsets of `B`. -/
def e789lev (B : Finset ℤ) (j : ℕ) : Finset ℤ :=
  (B.powersetCard j).image (fun T => ∑ x ∈ T, x)

/-- A set of `k` integers has at least `j * (k - j) + 1` distinct `j`-subset sums. -/
theorem e789_lev_card (B : Finset ℤ) :
    ∀ j ≤ B.card, j * (B.card - j) + 1 ≤ (e789lev B j).card := by
  induction B using Finset.induction_on_max with
  | empty =>
    intro j hj
    simp only [Finset.card_empty, Nat.le_zero] at hj
    subst hj
    simp [e789lev]
  | insert a s hlt ih =>
    intro j hj
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has] at hj ⊢
    rcases Nat.lt_or_ge s.card j with hjs | hjs
    · have hjeq : j = s.card + 1 := by omega
      have hne : (e789lev (insert a s) j).Nonempty := by
        unfold e789lev
        apply Finset.Nonempty.image
        rw [Finset.powersetCard_nonempty, card_insert_of_notMem has]
        omega
      have hpos := hne.card_pos
      have h0 : s.card + 1 - j = 0 := by omega
      rw [h0, Nat.mul_zero]
      omega
    · have hih := ih j hjs
      have hne : (s.powersetCard j).Nonempty := Finset.powersetCard_nonempty.mpr hjs
      obtain ⟨Tm, hTm, hmax⟩ :=
        Finset.exists_max_image (s.powersetCard j) (fun T => ∑ x ∈ T, x) hne
      rw [Finset.mem_powersetCard] at hTm
      obtain ⟨hTms, hTmc⟩ := hTm
      have hna : ∀ y, a ∉ Tm.erase y := by
        intro y h
        exact lt_irrefl a (hlt a (hTms (Finset.mem_of_mem_erase h)))
      let N : Finset ℤ := Tm.image (fun y => (∑ x ∈ Tm, x) - y + a)
      have hNcard : N.card = j := by
        rw [Finset.card_image_of_injective _ (by intro y y' h; simp only at h; linarith), hTmc]
      have hsub1 : e789lev s j ⊆ e789lev (insert a s) j := by
        unfold e789lev
        apply Finset.image_subset_image
        exact Finset.powersetCard_mono (Finset.subset_insert a s)
      have hsub2 : N ⊆ e789lev (insert a s) j := by
        intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        unfold e789lev
        rw [Finset.mem_image]
        refine ⟨insert a (Tm.erase y), ?_, ?_⟩
        · rw [Finset.mem_powersetCard]
          constructor
          · exact Finset.insert_subset_insert a ((Finset.erase_subset y Tm).trans hTms)
          · rw [Finset.card_insert_of_notMem (hna y), Finset.card_erase_of_mem hy, hTmc]
            have : 0 < j := by
              rw [← hTmc]
              exact Finset.card_pos.mpr ⟨y, hy⟩
            omega
        · rw [Finset.sum_insert (hna y), Finset.sum_erase_eq_sub hy]
          ring
      have hdisj : Disjoint (e789lev s j) N := by
        rw [Finset.disjoint_left]
        intro z hz hzN
        unfold e789lev at hz
        rw [Finset.mem_image] at hz hzN
        obtain ⟨T, hT, rfl⟩ := hz
        obtain ⟨y, hy, hyz⟩ := hzN
        have h1 := hmax T hT
        have h2 := hlt y (hTms hy)
        linarith
      have hcu := Finset.card_union_of_disjoint hdisj
      have hle := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      have harith : j * (s.card + 1 - j) + 1 = j * (s.card - j) + 1 + j := by
        have : s.card + 1 - j = s.card - j + 1 := by omega
        rw [this, Nat.mul_add, Nat.mul_one]
        ring
      rw [harith]
      omega

theorem e789_gauss (k : ℕ) : 2 * ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

theorem e789_sum_closed (k : ℕ) :
    6 * ∑ i ∈ Finset.range k, ((i + 1) * (k - (i + 1)) + 1) = k ^ 3 + 5 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hc : ∀ i ∈ Finset.range k, ((i + 1) * (k + 1 - (i + 1)) + 1) =
        ((i + 1) * (k - (i + 1)) + 1) + (i + 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have : k + 1 - (i + 1) = k - (i + 1) + 1 := by omega
      rw [this]
      ring
    rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
    have hg := e789_gauss k
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    nlinarith [ih, hg]

theorem e789_card_bound (n : ℕ) (B : Finset ℤ) (hB : B ⊆ Finset.Icc (1 : ℤ) n)
    (hsep : ∀ T ⊆ B, ∀ S ⊆ B, S.Nonempty → T.Nonempty →
      ∑ a ∈ T, a = ∑ b ∈ S, b → T.card = S.card) :
    B.card ^ 2 ≤ 6 * n := by
  have hdisj : ∀ x ∈ Finset.range B.card, ∀ y ∈ Finset.range B.card, x ≠ y →
      Disjoint (e789lev B (x + 1)) (e789lev B (y + 1)) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    unfold e789lev at hz1 hz2
    rw [Finset.mem_image] at hz1 hz2
    obtain ⟨T, hT, rfl⟩ := hz1
    obtain ⟨S, hS, hST⟩ := hz2
    rw [Finset.mem_powersetCard] at hT hS
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    have := hsep T hT.1 S hS.1 hSne hTne hST.symm
    omega
  have hcardU := Finset.card_biUnion hdisj
  have hUsub : (Finset.range B.card).biUnion (fun i => e789lev B (i + 1)) ⊆
      Finset.Icc (1 : ℤ) ((B.card : ℤ) * n) := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨i, _, hz⟩ := hz
    unfold e789lev at hz
    rw [Finset.mem_image] at hz
    obtain ⟨T, hT, rfl⟩ := hz
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_Icc]
    have hel : ∀ x ∈ T, 1 ≤ x ∧ x ≤ n := fun x hx => Finset.mem_Icc.mp (hB (hT.1 hx))
    have hTB : T.card ≤ B.card := Finset.card_le_card hT.1
    constructor
    · have h1 : T.card • (1 : ℤ) ≤ ∑ x ∈ T, x :=
        Finset.card_nsmul_le_sum T (fun x => x) 1 (fun x hx => (hel x hx).1)
      rw [nsmul_eq_mul, mul_one, hT.2] at h1
      push_cast at h1
      linarith
    · have h1 : ∑ x ∈ T, x ≤ T.card • (n : ℤ) :=
        Finset.sum_le_card_nsmul T (fun x => x) (n : ℤ) (fun x hx => (hel x hx).2)
      rw [nsmul_eq_mul] at h1
      have h2 : (T.card : ℤ) ≤ B.card := by exact_mod_cast hTB
      have h3 : (0 : ℤ) ≤ n := by positivity
      nlinarith
  have hUcard := Finset.card_le_card hUsub
  have hIcc : (Finset.Icc (1 : ℤ) ((B.card : ℤ) * n)).card = B.card * n := by
    rw [Int.card_Icc]
    have hc : (B.card : ℤ) * n + 1 - 1 = ((B.card * n : ℕ) : ℤ) := by push_cast; ring
    rw [hc]
    omega
  rw [hIcc, hcardU] at hUcard
  have hlow : ∑ i ∈ Finset.range B.card, ((i + 1) * (B.card - (i + 1)) + 1) ≤
      ∑ i ∈ Finset.range B.card, (e789lev B (i + 1)).card := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact e789_lev_card B (i + 1) (by omega)
  have hclosed := e789_sum_closed B.card
  have hmain : B.card * (B.card ^ 2 + 5) ≤ B.card * (6 * n) := by
    have : B.card * (B.card ^ 2 + 5) = B.card ^ 3 + 5 * B.card := by ring
    rw [this, ← hclosed]
    have : B.card * (6 * n) = 6 * (B.card * n) := by ring
    rw [this]
    omega
  rcases Nat.eq_zero_or_pos B.card with h0 | hpos
  · rw [h0]
    simp
  · have := Nat.le_of_mul_le_mul_left hmain hpos
    omega

end OMA.Helpers

open Filter in
theorem OMA.solution : OMA.R_Erdos789_erdos_789_variants_sq_R1.H1 := by
  have key : ∀ n : ℕ, Erdos789.subsetSumThreshold n ^ 2 ≤ 6 * n := by
    intro n
    have hle : Erdos789.subsetSumThreshold n ≤ Nat.sqrt (6 * n) := by
      unfold Erdos789.subsetSumThreshold
      apply csSup_le'
      intro m hm
      rw [Set.mem_ofPred_eq] at hm
      obtain ⟨B, hBA, hmB, hsep⟩ := hm (Finset.Icc (1 : ℤ) n) (by simp)
      have hb := OMA.Helpers.e789_card_bound n B hBA hsep
      rw [Nat.le_sqrt]
      nlinarith
    calc Erdos789.subsetSumThreshold n ^ 2 ≤ Nat.sqrt (6 * n) ^ 2 := Nat.pow_le_pow_left hle 2
      _ ≤ 6 * n := Nat.sqrt_le' _
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards with n
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : ((Erdos789.subsetSumThreshold n : ℕ) : ℝ) ^ 2 ≤ 6 * n := by exact_mod_cast key n
  have h2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have h3 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h4 : (0 : ℝ) ≤ (Erdos789.subsetSumThreshold n : ℝ) := by positivity
  nlinarith [sq_nonneg ((Erdos789.subsetSumThreshold n : ℝ) - 3 * Real.sqrt n)]
