import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1

-- Step H1 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1 (class S).
-- Write N = 1 + q + ... + q^(p-1) and M = 1 + p + ... + p^(q-1), and let r be a prime factor
-- of N with q not dividing r - 1. If N divided M, then r would divide M, so p^q = 1 in ZMod r.
-- r is neither q (N = 1 mod q) nor p (M = 1 mod p), so p is a unit mod r and its order
-- divides the prime q. Order 1 gives M = q mod r, so r = q: impossible. Order q gives
-- q | r - 1 by Fermat: excluded by hypothesis.

namespace OMA.Helpers

open Finset

theorem geom_zero_sum {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, (0 : R) ^ i) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp

theorem geom_one_sum {R : Type*} [CommRing R] (n : ℕ) :
    (∑ i ∈ range n, (1 : R) ^ i) = n := by
  simp

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1.H1 := by
  intro p q hp hq _ _ _ ⟨r, hr, hrN, hqr⟩ hNM
  have := Fact.mk hr
  rw [← Nat.geomSum_eq hq.two_le] at hrN hNM
  rw [← Nat.geomSum_eq hp.two_le] at hNM
  have hrM := hrN.trans hNM
  have hN0 : ((∑ i ∈ range p, q ^ i : ℕ) : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ r).mpr hrN
  have hM0 : ((∑ i ∈ range q, p ^ i : ℕ) : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ r).mpr hrM
  push_cast at hN0 hM0
  have hrq : r ≠ q := by
    rintro rfl
    rw [ZMod.natCast_self, OMA.Helpers.geom_zero_sum p hp.pos] at hN0
    exact one_ne_zero hN0
  have hrp : r ≠ p := by
    rintro rfl
    rw [ZMod.natCast_self, OMA.Helpers.geom_zero_sum q hq.pos] at hM0
    exact one_ne_zero hM0
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp h)
  have hpow : (p : ZMod r) ^ q = 1 := by
    have h := geom_sum_mul (p : ZMod r) q
    rw [hM0, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have hord : orderOf (p : ZMod r) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime hq).mp hord with h1 | hq'
  · have hp1 : (p : ZMod r) = 1 := orderOf_eq_one_iff.mp h1
    rw [hp1, OMA.Helpers.geom_one_sum, ZMod.natCast_eq_zero_iff] at hM0
    exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp hM0)
  · have h := ZMod.orderOf_dvd_card_sub_one hp0
    rw [hq'] at h
    exact hqr h
