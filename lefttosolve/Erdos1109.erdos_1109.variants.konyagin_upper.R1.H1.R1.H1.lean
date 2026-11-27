import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1
import Mathlib

namespace OMA.Helpers
open Finset

/-- A nonzero natural number has at most log base 2 of itself distinct prime factors. -/
lemma two_pow_card_primeFactors_le (d : ℕ) (hd : d ≠ 0) :
    2 ^ d.primeFactors.card ≤ d := by
  calc 2 ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ d.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.prod_primeFactors_dvd d)

lemma card_primeFactors_le_log (d N : ℕ) (hd : d ≠ 0) (hdN : d ≤ N) :
    (d.primeFactors.card : ℝ) ≤ 2 * Real.log N := by
  have h := two_pow_card_primeFactors_le d hd
  have h' : ((2:ℝ)) ^ d.primeFactors.card ≤ (N:ℝ) := by exact_mod_cast h.trans hdN
  have hl : Real.log ((2:ℝ) ^ d.primeFactors.card) ≤ Real.log N :=
    Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at hl
  have l2 := Real.log_two_gt_d9
  have k0 : (0:ℝ) ≤ d.primeFactors.card := Nat.cast_nonneg _
  nlinarith

/-- For a pair of elements of `A ⊆ [1, N]`, few primes have squares dividing the difference. -/
lemma pair_count (N X : ℕ) (hN : 1 ≤ N) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) (t : ℕ × ℕ)
    (ht : t ∈ A ×ˢ A) :
    ((((range (X+1)).filter Nat.Prime).filter
      (fun p => t.1 ≠ t.2 ∧ t.1 % (p*p) = t.2 % (p*p))).card : ℝ) ≤ 2 * Real.log N := by
  have logN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  by_cases h : t.1 = t.2
  · have : (((range (X+1)).filter Nat.Prime).filter
        (fun p => t.1 ≠ t.2 ∧ t.1 % (p*p) = t.2 % (p*p))) = ∅ := by
      apply Finset.filter_false_of_mem
      intro p _ hp
      exact hp.1 h
    rw [this]
    simp only [card_empty, Nat.cast_zero]
    linarith
  · obtain ⟨h1, h2⟩ := mem_product.mp ht
    have m1 := mem_Icc.mp (hA h1)
    have m2 := mem_Icc.mp (hA h2)
    set d := Int.natAbs ((t.2:ℤ) - t.1) with hdd
    have hd0 : d ≠ 0 := by omega
    have hdN : d ≤ N := by omega
    have sub : (((range (X+1)).filter Nat.Prime).filter
        (fun p => t.1 ≠ t.2 ∧ t.1 % (p*p) = t.2 % (p*p))) ⊆ d.primeFactors := by
      intro p hp
      obtain ⟨hp1, _, hp3⟩ := mem_filter.mp hp
      have pr : p.Prime := (mem_filter.mp hp1).2
      have hmod : t.1 ≡ t.2 [MOD p*p] := hp3
      have hz : ((p*p:ℕ):ℤ) ∣ (t.2:ℤ) - t.1 := Nat.modEq_iff_dvd.mp hmod
      have hz' : (p:ℤ) ∣ (t.2:ℤ) - t.1 :=
        (Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_right p p)).trans hz
      exact Nat.mem_primeFactors.mpr ⟨pr, Int.natCast_dvd.mp hz', hd0⟩
    calc _ ≤ (d.primeFactors.card : ℝ) := by exact_mod_cast card_le_card sub
      _ ≤ 2 * Real.log N := card_primeFactors_le_log d N hd0 hdN

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1.H1 := by
  intro N X hN A hA
  intro P C
  have hterm : ∀ p ∈ P, ((p*p:ℕ):ℝ) * C p ≤ (X:ℝ)^2 * C p := by
    intro p hp
    have hpX : p ≤ X := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hp).1)
    have hpX' : (p:ℝ) ≤ X := by exact_mod_cast hpX
    have : ((p*p:ℕ):ℝ) ≤ (X:ℝ)^2 := by
      push_cast
      rw [pow_two]
      exact mul_le_mul hpX' hpX' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
  have hswap : ∑ p ∈ P, C p = ∑ t ∈ A ×ˢ A,
      (P.filter (fun p => t.1 ≠ t.2 ∧ t.1 % (p*p) = t.2 % (p*p))).card := by
    simp only [C, card_filter]
    exact Finset.sum_comm
  have hcount : ∀ t ∈ A ×ˢ A,
      ((P.filter (fun p => t.1 ≠ t.2 ∧ t.1 % (p*p) = t.2 % (p*p))).card : ℝ) ≤
        2 * Real.log N :=
    fun t ht => OMA.Helpers.pair_count N X hN A hA t ht
  calc ∑ p ∈ P, ((p*p:ℕ):ℝ) * C p ≤ ∑ p ∈ P, (X:ℝ)^2 * C p := sum_le_sum hterm
    _ = (X:ℝ)^2 * ((∑ p ∈ P, C p : ℕ) : ℝ) := by rw [← mul_sum]; push_cast; rfl
    _ = (X:ℝ)^2 * ∑ t ∈ A ×ˢ A,
        ((P.filter (fun p => t.1 ≠ t.2 ∧ t.1 % (p*p) = t.2 % (p*p))).card : ℝ) := by
      rw [hswap]; push_cast; rfl
    _ ≤ (X:ℝ)^2 * ∑ t ∈ A ×ˢ A, 2 * Real.log N := by
      gcongr with t ht
      exact hcount t ht
    _ = 2*(X:ℝ)^2*Real.log N*(A.card:ℝ)^2 := by
      rw [sum_const, card_product, nsmul_eq_mul]
      push_cast
      ring
