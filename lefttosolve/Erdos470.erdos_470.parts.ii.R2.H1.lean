import OMAReductions.R_Erdos470_erdos_470_parts_ii_R2

/-!
# Step H1 of the reduction Erdos470.erdos_470.parts.ii.R2

Write K = 2^k, N = 2K and n = K p q with distinct primes p, q > N. The sum of the divisors
of n is A = (N - 1)(p + 1)(q + 1) and 2n = B = N p q.

* n is abundant because B < A.
* n is not pseudoperfect: if a set s of proper divisors sums to n, its complement t in the
  proper divisors sums to A - B < q. Splitting the elements of t by divisibility by p and q
  writes this sum as p U + q V + W with W a sum of distinct divisors of K, so W < N < p.
  Since the sum is below q, V = 0, and then (A - B) mod p = W < N, against the hypothesis.
* n is primitive: every proper divisor is 2^i, 2^i p, 2^i q (i <= k) or 2^i p q (i < k),
  and none of these is abundant because p, q > N.

Only the upstream definition Erdos470.PrimitiveWeird and Mathlib definitions are used.
-/

namespace OMA.Helpers

open Finset

/-- The sum of the divisors of a prime `p` is `p + 1`. -/
theorem sigma_prime {p : ℕ} (hp : p.Prime) : ∑ d ∈ p.divisors, d = p + 1 := by
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne, add_comm]

/-- The sum of the divisors of `2 ^ i` is `2 ^ (i + 1) - 1`. -/
theorem sigma_two_pow (i : ℕ) : (∑ d ∈ (2 ^ i).divisors, d) + 1 = 2 ^ (i + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction i with
  | zero => simp
  | succ i ih => rw [Finset.sum_range_succ, pow_succ 2 (i + 1)]; omega

/-- A power of two is coprime to an odd number. -/
theorem coprime_two_pow_of_odd {m : ℕ} (hm : m % 2 = 1) (i : ℕ) : Nat.Coprime (2 ^ i) m := by
  apply Nat.Coprime.pow_left
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  omega

/-- For odd `m`, `2 ^ i * m` is not abundant as soon as
`2 ^ (i + 1) * sigma(m) ≤ 2 ^ (i + 1) * m + sigma(m)`. -/
theorem not_abundant_two_pow_mul {m : ℕ} (i : ℕ) (hm : m % 2 = 1)
    (h : 2 ^ (i + 1) * (∑ d ∈ m.divisors, d) ≤ 2 ^ (i + 1) * m + ∑ d ∈ m.divisors, d) :
    ¬ (2 ^ i * m).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, Nat.Coprime.sum_divisors_mul (coprime_two_pow_of_odd hm i)]
  have h2 := sigma_two_pow i
  intro hlt
  rw [← h2] at h
  rw [pow_succ] at h2
  nlinarith

/-- The divisors of `2 ^ k * p * q` for primes `p` and `q`. -/
theorem dvd_classify {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (k : ℕ)
    (h : d ∣ 2 ^ k * p * q) :
    ∃ i ≤ k, (d = 2 ^ i * 1 ∨ d = 2 ^ i * p ∨ d = 2 ^ i * q ∨ d = 2 ^ i * (p * q)) := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨y1, y2, hy1, hy2, rfl⟩ := Nat.dvd_mul.mp hy
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy1
  refine ⟨i, hi, ?_⟩
  rcases (Nat.dvd_prime hp).mp hy2 with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hz with rfl | rfl
  · left; ring
  · right; right; left; ring
  · right; left; ring
  · right; right; right; ring

/-- Every sum of distinct divisors of `K * p * q` is `p * U + q * V + W` with `W` at most the sum
of the divisors of `K`. -/
theorem subset_sum_decomp {K p q : ℕ} (hK : K ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (t : Finset ℕ) (ht : ∀ d ∈ t, d ∣ K * p * q) :
    ∃ U V W : ℕ, ∑ d ∈ t, d = p * U + q * V + W ∧ W ≤ ∑ d ∈ K.divisors, d := by
  refine ⟨∑ d ∈ t, (if p ∣ d then d / p else 0),
    ∑ d ∈ t, (if p ∣ d then 0 else if q ∣ d then d / q else 0),
    ∑ d ∈ t, (if p ∣ d then 0 else if q ∣ d then 0 else d), ?_, ?_⟩
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h1 : p ∣ d
    · simp [h1, Nat.mul_div_cancel' h1]
    · by_cases h2 : q ∣ d
      · simp [h1, h2, Nat.mul_div_cancel' h2]
      · simp [h1, h2]
  · calc ∑ d ∈ t, (if p ∣ d then 0 else if q ∣ d then 0 else d)
          = ∑ d ∈ t.filter (fun d => ¬ p ∣ d ∧ ¬ q ∣ d), d := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro d _
            by_cases h1 : p ∣ d <;> by_cases h2 : q ∣ d <;> simp [h1, h2]
      _ ≤ ∑ d ∈ K.divisors, d := by
            apply Finset.sum_le_sum_of_subset
            intro d hd
            rw [Finset.mem_filter] at hd
            rw [Nat.mem_divisors]
            refine ⟨?_, hK⟩
            have h := ht d hd.1
            have cq : Nat.Coprime d q :=
              Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hd.2.2)
            have cp : Nat.Coprime d p :=
              Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd.2.1)
            exact cp.dvd_of_dvd_mul_right (cq.dvd_of_dvd_mul_right h)

/-- The criterion of step H1. -/
theorem primitiveWeird_R2 (k p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hNp : 2 ^ (k + 1) < p) (hNq : 2 ^ (k + 1) < q) (hpq : p ≠ q)
    (hpos : 2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1))
    (hlt : (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) < 2 ^ (k + 1) * p * q + q)
    (hmod : 2 ^ (k + 1) ≤
      ((2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q) % p) :
    Erdos470.PrimitiveWeird (2 ^ k * p * q) := by
  obtain ⟨K, hK⟩ : ∃ K, K = 2 ^ k := ⟨_, rfl⟩
  have hX : 2 ^ (k + 1) = 2 * K := by rw [hK, pow_succ]; ring
  have hK1 : 1 ≤ K := by rw [hK]; exact Nat.one_le_two_pow
  rw [hX] at hNp hNq hpos hlt hmod
  rw [← hK]
  have hK0 : K ≠ 0 := by omega
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · omega
    · exact h
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have cKp : Nat.Coprime K p := by rw [hK]; exact coprime_two_pow_of_odd hpodd k
  have cKq : Nat.Coprime K q := by rw [hK]; exact coprime_two_pow_of_odd hqodd k
  have hS2 : (∑ d ∈ K.divisors, d) + 1 = 2 * K := by
    rw [hK, sigma_two_pow k, pow_succ]; ring
  have hS2' : 2 * K - 1 = ∑ d ∈ K.divisors, d := by omega
  rw [hS2'] at hpos hlt hmod
  have hσn : ∑ d ∈ (K * p * q).divisors, d = (∑ d ∈ K.divisors, d) * (p + 1) * (q + 1) := by
    rw [Nat.Coprime.sum_divisors_mul (Nat.Coprime.mul_left cKq cpq),
      Nat.Coprime.sum_divisors_mul cKp, sigma_prime hp, sigma_prime hq]
  have h2n : 2 * K * p * q = 2 * (K * p * q) := by ring
  rw [h2n] at hpos hlt hmod
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [Nat.abundant_iff_sum_divisors, hσn]
    exact hpos
  · -- not pseudoperfect
    rintro ⟨_, s, hs, hsum⟩
    have h1 := Finset.sum_sdiff (f := fun d => d) hs
    have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := K * p * q)
    obtain ⟨U, V, W, hT, hW⟩ := subset_sum_decomp hK0 hp hq ((K * p * q).properDivisors \ s)
      (fun d hd => (Nat.mem_properDivisors.mp (Finset.sdiff_subset hd)).1)
    rw [hσn] at h2
    have hAB : (∑ d ∈ K.divisors, d) * (p + 1) * (q + 1) - 2 * (K * p * q) = p * U + q * V + W := by
      omega
    rw [hAB] at hmod
    have hV : V = 0 := by
      by_contra hV
      have : q ≤ q * V := Nat.le_mul_of_pos_right q (Nat.pos_of_ne_zero hV)
      omega
    subst hV
    have hWp : W < p := by omega
    rw [Nat.mul_zero, Nat.add_zero, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hWp] at hmod
    omega
  · -- primitive
    intro d hd
    rw [Nat.mem_properDivisors] at hd
    obtain ⟨hdvd, hdlt⟩ := hd
    rintro ⟨habund, _⟩
    rw [hK] at hdvd hdlt
    obtain ⟨i, hi, hcases⟩ := dvd_classify hp hq k hdvd
    have hTi : 2 ^ (i + 1) ≤ 2 * K := by
      rw [hK, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases hcases with rfl | rfl | rfl | rfl
    · refine not_abundant_two_pow_mul i (by norm_num) ?_ habund
      simp
    · refine not_abundant_two_pow_mul i hpodd ?_ habund
      rw [sigma_prime hp]
      nlinarith
    · refine not_abundant_two_pow_mul i hqodd ?_ habund
      rw [sigma_prime hq]
      nlinarith
    · have hik : i < k := by
        have h' : 2 ^ i * (p * q) < 2 ^ k * (p * q) := by
          calc 2 ^ i * (p * q) < 2 ^ k * p * q := hdlt
            _ = 2 ^ k * (p * q) := by ring
        have := Nat.lt_of_mul_lt_mul_right h'
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      have hTK : 2 ^ (i + 1) ≤ K := by
        rw [hK]; exact Nat.pow_le_pow_right (by norm_num) hik
      have hpqodd : (p * q) % 2 = 1 := by
        rw [Nat.mul_mod, hpodd, hqodd]
      refine not_abundant_two_pow_mul i hpqodd ?_ habund
      rw [Nat.Coprime.sum_divisors_mul cpq, sigma_prime hp, sigma_prime hq]
      have e1 : 2 ^ (i + 1) * (p + q + 1) ≤ K * (p + q + 1) := Nat.mul_le_mul_right _ hTK
      have e2 : (2 * K + 1) * q ≤ p * q := Nat.mul_le_mul_right _ hNp
      have e3 : K * 1 ≤ K * q := Nat.mul_le_mul_left _ (by omega)
      nlinarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R2.H1 := by
  intro k p q hp hq hNp hNq hpq hpos hlt hmod
  exact OMA.Helpers.primitiveWeird_R2 k p q hp hq hNp hNq hpq hpos hlt hmod
