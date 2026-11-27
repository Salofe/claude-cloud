import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1

/-!
# Step H1 of reduction ErdosMoser.erdos_moser_conjecture.R1: the odd-exponent case (Moser)

Write m = n + 1. Pairing i with n - i, every term i ^ k + (n - i) ^ k of 2 S_k(m) is divisible
by i + (n - i) = n because k is odd, so n divides 2 S_k(m) = 2 m ^ k. As n is coprime to
(n + 1) ^ k, n divides 2, so m is 1, 2 or 3; m = 1 and m = 2 are impossible, and m = 3 means
1 + 2 ^ k = 3 ^ k, which forces k = 1.
-/

namespace OMA.Helpers

/-- The power sum, with the vanishing term at 0 added back, as a sum over range. -/
theorem powerSum_succ_eq_sum_range (k n : ℕ) (hk : 0 < k) :
    ErdosMoser.powerSum k (n + 1) = ∑ i ∈ Finset.range (n + 1), i ^ k := by
  unfold ErdosMoser.powerSum
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < n + 1 by omega),
    zero_pow hk.ne', zero_add]

/-- Moser's pairing: for odd k, n divides twice the power sum up to m = n + 1. -/
theorem dvd_two_mul_powerSum (k n : ℕ) (hk : 0 < k) (ho : Odd k) :
    n ∣ 2 * ErdosMoser.powerSum k (n + 1) := by
  rw [powerSum_succ_eq_sum_range k n hk, two_mul]
  nth_rw 2 [← Finset.sum_range_reflect]
  rw [← Finset.sum_add_distrib]
  apply Finset.dvd_sum
  intro i hi
  have hi' : i ≤ n := by
    simp only [Finset.mem_range] at hi
    omega
  have h := ho.nat_add_dvd_pow_add_pow i (n + 1 - 1 - i)
  rwa [show i + (n + 1 - 1 - i) = n by omega] at h

/-- For k at least 2, 1 + 2 ^ k is strictly less than 3 ^ k. -/
theorem one_add_two_pow_lt_three_pow (j : ℕ) : 1 + 2 ^ (j + 2) < 3 ^ (j + 2) := by
  have h1 := Nat.pow_le_pow_left (show 2 ≤ 3 by norm_num) j
  have h2 := Nat.one_le_two_pow (n := j)
  rw [pow_add, pow_add]
  norm_num
  omega

end OMA.Helpers

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1 := by
  intro k m hk hm ho h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hdvd := OMA.Helpers.dvd_two_mul_powerSum k n hk ho
  rw [h] at hdvd
  have hcop : Nat.Coprime n ((n + 1) ^ k) := by
    apply Nat.Coprime.pow_right
    simp
  have h2 : n ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have hn : n ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have hsum := OMA.Helpers.powerSum_succ_eq_sum_range k n hk
  rw [h] at hsum
  interval_cases n
  · -- m = 1: the sum is empty, but 1 ^ k = 1
    simp [zero_pow hk.ne'] at hsum
  · -- m = 2: the sum is 0 ^ k + 1 ^ k = 1, but 2 ^ k is at least 2
    have h22 : 2 ≤ 2 ^ k := Nat.le_self_pow hk.ne' 2
    simp [Finset.sum_range_succ, zero_pow hk.ne'] at hsum
    omega
  · -- m = 3: 3 ^ k = 1 + 2 ^ k forces k = 1
    refine ⟨?_, rfl⟩
    have h' : (2 + 1) ^ k = 1 + 2 ^ k := by
      rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
        zero_pow hk.ne', one_pow, zero_add]
    by_contra hk1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hlt := OMA.Helpers.one_add_two_pow_lt_three_pow j
    norm_num at h'
    omega
