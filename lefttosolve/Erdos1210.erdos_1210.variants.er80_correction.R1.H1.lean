import OMAReductions.R_Erdos1210_erdos_1210_variants_er80_correction_R1

/-!
# Step H1 of the reduction Erdos1210.erdos_1210.variants.er80_correction.R1

Split the primes q in the interval from 2n (exclusive) to m into those below m - n and the rest.

For q below m - n we have q in the interval from n to m - n, and since q is at least 2n + 1,
1/(q - n) is at most 1/q + 2n (1/q - 1/(q + 1)). The second part telescopes over all integers
in the interval and contributes at most 2n/(2n + 1), which is at most 1.

The remaining q lie between m - n and m, so there are at most n + 1 of them, and each satisfies
q - n at least n + 1. Their contribution is therefore at most 1.
-/

namespace OMA.Helpers

open Finset

theorem erdos1210_tele (a b : ℕ) (h : a ≤ b) :
    ∑ q ∈ Ioc a b, (1 / (q : ℝ) - 1 / ((q : ℝ) + 1)) = 1 / ((a : ℝ) + 1) - 1 / ((b : ℝ) + 1) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih]
    push_cast
    ring

theorem erdos1210_point (n : ℕ) (x : ℝ) (hx : 2 * (n : ℝ) + 1 ≤ x) :
    1 / (x - n) ≤ 1 / x + 2 * n * (1 / x - 1 / (x + 1)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hxn : 0 < x - n := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have e : 1 / x + 2 * n * (1 / x - 1 / (x + 1)) = (x + 1 + 2 * n) / (x * (x + 1)) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ hxn (by positivity)]
  nlinarith

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_Erdos1210_erdos_1210_variants_er80_correction_R1.H1 := by
  intro n m hnm
  set S := (Ioc (2 * n) m).filter Nat.Prime with hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun q => q < m - n)]
  have hA : (∑ q ∈ S.filter (fun q => q < m - n), 1 / ((q : ℝ) - n)) ≤
      (∑ q ∈ (Ico n (m - n)).filter Nat.Prime, 1 / (q : ℝ)) + 1 := by
    have h1 : (∑ q ∈ S.filter (fun q => q < m - n), 1 / ((q : ℝ) - n)) ≤
        ∑ q ∈ S.filter (fun q => q < m - n),
          (1 / (q : ℝ) + 2 * n * (1 / (q : ℝ) - 1 / ((q : ℝ) + 1))) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
      apply OMA.Helpers.erdos1210_point
      have : ((2 * n + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'
      push_cast at this
      exact this
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    have h2 : (∑ q ∈ S.filter (fun q => q < m - n), 1 / (q : ℝ)) ≤
        ∑ q ∈ (Ico n (m - n)).filter Nat.Prime, 1 / (q : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro q hq
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        obtain ⟨hq3, hq4⟩ := Finset.mem_filter.mp hq1
        have hq5 := Finset.mem_Ioc.mp hq3
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hq2⟩, hq4⟩
      · intro q _ _
        positivity
    have h3 : (∑ q ∈ S.filter (fun q => q < m - n), (1 / (q : ℝ) - 1 / ((q : ℝ) + 1))) ≤
        ∑ q ∈ Ioc (2 * n) m, (1 / (q : ℝ) - 1 / ((q : ℝ) + 1)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro q hq
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      · intro q hq _
        have hq1 := (Finset.mem_Ioc.mp hq).1
        have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hq0 (by linarith)
    rw [OMA.Helpers.erdos1210_tele _ _ hnm] at h3
    have h4 : 2 * (n : ℝ) * (1 / (((2 * n : ℕ) : ℝ) + 1) - 1 / ((m : ℝ) + 1)) ≤ 1 := by
      push_cast
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hn1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have e1 : 2 * (n : ℝ) * (1 / (2 * (n : ℝ) + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hn1]
        linarith
      have e2 : 0 ≤ 2 * (n : ℝ) * (1 / ((m : ℝ) + 1)) := by positivity
      nlinarith
    have h5 : 2 * (n : ℝ) * (∑ q ∈ S.filter (fun q => q < m - n),
        (1 / (q : ℝ) - 1 / ((q : ℝ) + 1))) ≤ 1 := by
      have hn0 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
      exact (mul_le_mul_of_nonneg_left h3 hn0).trans h4
    linarith
  have hB : (∑ q ∈ S.filter (fun q => ¬ q < m - n), 1 / ((q : ℝ) - n)) ≤ 1 := by
    have h1 : ∀ q ∈ S.filter (fun q => ¬ q < m - n), 1 / ((q : ℝ) - n) ≤ 1 / ((n : ℝ) + 1) := by
      intro q hq
      have hq' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
      have : ((2 * n + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'
      push_cast at this
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    have h3 : (S.filter (fun q => ¬ q < m - n)).card ≤ n + 1 := by
      have hsub : S.filter (fun q => ¬ q < m - n) ⊆ Icc (m - n) m := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        have hq5 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq1).1
        exact Finset.mem_Icc.mpr ⟨by omega, hq5.2⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    rw [nsmul_eq_mul] at h2
    have h4 : ((S.filter (fun q => ¬ q < m - n)).card : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast h3
    have h5 : ((S.filter (fun q => ¬ q < m - n)).card : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      exact h4
    linarith
  linarith
