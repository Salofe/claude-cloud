import OMAReductions.R_Erdos647_erdos_647_R1

-- Step H1 of reduction Erdos647.erdos_647.R1: d(m) ^ 6 <= 139 ^ 6 * m.
-- Per prime, (k + 1) ^ 6 * p ^ a <= (a + 1) ^ 6 * p ^ k with a the maximising exponent
-- (a = 0 for p >= 64); multiply over the prime factors of m together with the primes below 64.

namespace OMA.Helpers

def ex (p : ℕ) : ℕ :=
  if p = 2 then 8 else if p = 3 then 4 else if p = 5 then 3 else if p ≤ 11 then 2
  else if p < 64 then 1 else 0

def S : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}

lemma gen (p a K : ℕ) (hsmall : ∀ k ≤ K, (k + 1) ^ 6 * p ^ a ≤ (a + 1) ^ 6 * p ^ k)
    (hratio : (K + 2) ^ 6 ≤ p * (K + 1) ^ 6) :
    ∀ k, (k + 1) ^ 6 * p ^ a ≤ (a + 1) ^ 6 * p ^ k := by
  intro k
  rcases le_or_gt k K with h | h
  · exact hsmall k h
  · have hK : K ≤ k := h.le
    clear h
    induction k, hK using Nat.le_induction with
    | base => exact hsmall K le_rfl
    | succ k hk ih =>
      have hlin : (k + 2) * (K + 1) ≤ (k + 1) * (K + 2) := by nlinarith
      have h6 : ((k + 2) * (K + 1)) ^ 6 ≤ ((k + 1) * (K + 2)) ^ 6 := Nat.pow_le_pow_left hlin 6
      rw [mul_pow, mul_pow] at h6
      have hr : (k + 2) ^ 6 ≤ p * (k + 1) ^ 6 := by
        have hpos : 0 < (K + 1) ^ 6 := by positivity
        have : (k + 2) ^ 6 * (K + 1) ^ 6 ≤ (p * (k + 1) ^ 6) * (K + 1) ^ 6 := by
          calc (k + 2) ^ 6 * (K + 1) ^ 6 ≤ (k + 1) ^ 6 * (K + 2) ^ 6 := h6
            _ ≤ (k + 1) ^ 6 * (p * (K + 1) ^ 6) := Nat.mul_le_mul_left _ hratio
            _ = (p * (k + 1) ^ 6) * (K + 1) ^ 6 := by ring
        exact Nat.le_of_mul_le_mul_right this hpos
      have ih' := ih
      calc (k + 1 + 1) ^ 6 * p ^ a = (k + 2) ^ 6 * p ^ a := by ring
        _ ≤ (p * (k + 1) ^ 6) * p ^ a := Nat.mul_le_mul_right _ hr
        _ = p * ((k + 1) ^ 6 * p ^ a) := by ring
        _ ≤ p * ((a + 1) ^ 6 * p ^ k) := Nat.mul_le_mul_left _ ih'
        _ = (a + 1) ^ 6 * p ^ (k + 1) := by ring

lemma local_bound (p : ℕ) (hp : p.Prime) (k : ℕ) :
    (k + 1) ^ 6 * p ^ ex p ≤ (ex p + 1) ^ 6 * p ^ k := by
  rcases lt_or_ge p 64 with h | h
  · interval_cases p <;> norm_num at hp <;>
      exact gen _ _ 8 (fun k hk => by interval_cases k <;> norm_num [ex]) (by norm_num) k
  · have hex : ex p = 0 := by unfold ex; split_ifs <;> omega
    rw [hex]
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    calc (k + 1) ^ 6 * p ^ 0 = (k + 1) ^ 6 := by ring
      _ ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left h1 6
      _ = 64 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ p ^ k := Nat.pow_le_pow_left h k
      _ = (0 + 1) ^ 6 * p ^ k := by ring

lemma ex_eq_zero (p : ℕ) (hp : p.Prime) (hS : p ∉ S) : ex p = 0 := by
  rcases lt_or_ge p 64 with h | h
  · interval_cases p <;> norm_num at hp <;> simp [S] at hS
  · unfold ex; split_ifs <;> omega

lemma numeric : (∏ p ∈ S, (ex p + 1) ^ 6) ≤ 139 ^ 6 * ∏ p ∈ S, p ^ ex p := by
  decide +kernel

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := by
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hTprime : ∀ p ∈ m.primeFactors ∪ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · simp only [S, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hsig : ArithmeticFunction.sigma 0 m ^ 6 = ∏ p ∈ m.primeFactors ∪ S, (m.factorization p + 1) ^ 6 := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm, ← Finset.prod_pow]
    apply Finset.prod_subset Finset.subset_union_left
    intro p _ hp
    have : m.factorization p = 0 := Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    simp [this]
  have hm' : m = ∏ p ∈ m.primeFactors ∪ S, p ^ m.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Finsupp.prod]
    apply Finset.prod_subset (by rw [Nat.support_factorization]; exact Finset.subset_union_left)
    intro p _ hp
    have : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [this]
  have hD : ∏ p ∈ S, p ^ ex p = ∏ p ∈ m.primeFactors ∪ S, p ^ ex p := by
    apply Finset.prod_subset Finset.subset_union_right
    intro p hpT hpS
    simp [ex_eq_zero p (hTprime p hpT) hpS]
  have hN : ∏ p ∈ S, (ex p + 1) ^ 6 = ∏ p ∈ m.primeFactors ∪ S, (ex p + 1) ^ 6 := by
    apply Finset.prod_subset Finset.subset_union_right
    intro p hpT hpS
    simp [ex_eq_zero p (hTprime p hpT) hpS]
  have hterm : (∏ p ∈ m.primeFactors ∪ S, (m.factorization p + 1) ^ 6) * ∏ p ∈ m.primeFactors ∪ S, p ^ ex p ≤
      (∏ p ∈ m.primeFactors ∪ S, (ex p + 1) ^ 6) * ∏ p ∈ m.primeFactors ∪ S, p ^ m.factorization p := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun p hp => local_bound p (hTprime p hp) (m.factorization p)
  have hDpos : 0 < ∏ p ∈ S, p ^ ex p := by
    apply Finset.prod_pos
    intro p hp
    have : 0 < p := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
      omega
    positivity
  rw [← hm', ← hN, ← hD, ← hsig] at hterm
  have := hterm.trans (Nat.mul_le_mul_right m numeric)
  rw [mul_comm (139 ^ 6) _, mul_assoc] at this
  rw [mul_comm] at this
  exact Nat.le_of_mul_le_mul_left this hDpos
