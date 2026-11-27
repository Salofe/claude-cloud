import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1

/-!
# Step H1 of the reduction Erdos470.erdos_470.parts.ii.R1

Melfi's construction of primitive weird numbers (G. Melfi, J. Number Theory 147 (2015), Theorem 1),
with the size condition a (a + b) < 2^(k+2). Write K = 2^k, p = 4K - a and q = 4K + b (both prime)
and n = K p q.

* Since a (a + b) < 4K and a >= 4 we get a < K, so p > 3K; p and q are odd primes, hence a and b
  are odd and a = b + 4 + 2j for some j.
* The sum of the divisors of n is (2K - 1)(p + 1)(q + 1), and the abundance is
  sigma(n) - 2n = 2K(2j + 1) + (a - 1)(b + 1) > 0, so n is abundant.
* n is not pseudoperfect: if a set s of proper divisors sums to n, its complement t in the proper
  divisors sums to the abundance. Splitting each element of t by divisibility by p and by q writes
  that sum as p U + q V + W, where W is a sum of distinct divisors of K, so W < 2K. With
  h = U + V the sum lies in [p h, q h + 2K - 1]: for h >= j + 1 it exceeds the abundance, for
  h <= j it falls short of it.
* n is primitive: every divisor of n is 2^i, 2^i p, 2^i q or 2^i p q (i <= k, and i < k for a
  proper divisor of the last kind), and none of these is abundant.

Only the upstream definition Erdos470.PrimitiveWeird is used, together with Mathlib's definitions
Nat.Weird, Nat.Abundant and Nat.Pseudoperfect; no upstream theorem is used.
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

/-- The abundance identity: with `p = 4K - a`, `q = 4K + b`, `a = b + 4 + 2j` and
`S2 = 2K - 1`, `S2 (p+1) (q+1) = 2 K p q + 2K(2j+1) + (a-1)(b+1)`. -/
theorem sigma_identity {K a b j p q S2 : ℕ}
    (hpa : p + a = 4 * K) (hqb : q = 4 * K + b) (haj : a = b + 4 + 2 * j)
    (hS2 : S2 + 1 = 2 * K) :
    S2 * (p + 1) * (q + 1) =
      2 * (K * p * q) + (2 * K * (2 * j + 1) + (b + 3 + 2 * j) * (b + 1)) := by
  subst haj
  have e1 : (p : ℤ) = 4 * K - (b + 4 + 2 * j) := by omega
  have e2 : (q : ℤ) = 4 * K + b := by omega
  have e3 : (S2 : ℤ) = 2 * K - 1 := by omega
  have h : ((S2 * (p + 1) * (q + 1) : ℕ) : ℤ) =
      ((2 * (K * p * q) + (2 * K * (2 * j + 1) + (b + 3 + 2 * j) * (b + 1)) : ℕ) : ℤ) := by
    push_cast
    rw [e1, e2, e3]
    ring
  exact_mod_cast h

/-- The abundance `2K(2j+1) + (a-1)(b+1)` is not of the form `p U + q V + W` with `W < 2K`:
for `U + V ≥ j + 1` such a sum is too large, for `U + V ≤ j` it is too small. -/
theorem gap_contra {K a b j p q U V W S2 : ℕ}
    (hpa : p + a = 4 * K) (hqb : q = 4 * K + b) (haj : a = b + 4 + 2 * j)
    (hsize : a * (a + b) < 4 * K) (hW : W ≤ S2) (hS2 : S2 + 1 = 2 * K)
    (hT : p * U + q * V + W = 2 * K * (2 * j + 1) + (b + 3 + 2 * j) * (b + 1)) :
    False := by
  subst haj
  have e1 : (p : ℤ) = 4 * K - (b + 4 + 2 * j) := by omega
  have e2 : (q : ℤ) = 4 * K + b := by omega
  have e3 : (S2 : ℤ) = 2 * K - 1 := by omega
  have hT' : (p : ℤ) * U + q * V + W = 2 * K * (2 * j + 1) + (b + 3 + 2 * j) * (b + 1) := by
    exact_mod_cast hT
  have hsize' : ((b : ℤ) + 4 + 2 * j) * ((b + 4 + 2 * j) + b) < 4 * K := by
    exact_mod_cast hsize
  have hW' : (W : ℤ) ≤ S2 := by exact_mod_cast hW
  rw [e1, e2] at hT'
  have hp0 : (0 : ℤ) ≤ 4 * K - (b + 4 + 2 * j) := by omega
  rcases le_or_gt (j + 1) (U + V) with h | h
  · have h1 : (4 * (K : ℤ) - (b + 4 + 2 * j)) * (j + 1) ≤
        (4 * (K : ℤ) - (b + 4 + 2 * j)) * (U + V) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h) hp0
    have h2 : (4 * (K : ℤ) - (b + 4 + 2 * j)) * V ≤ (4 * K + b) * V :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    have hW0 : (0 : ℤ) ≤ W := by positivity
    have hb0 : (0 : ℤ) ≤ b := by positivity
    linarith
  · have h3 : (4 * (K : ℤ) - (b + 4 + 2 * j)) * U ≤ (4 * K + b) * U :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    have h4 : (4 * (K : ℤ) + b) * (U + V) ≤ (4 * K + b) * j :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : U + V ≤ j)) (by positivity)
    have h5 : (0 : ℤ) ≤ b * j := by positivity
    have h6 : (0 : ℤ) ≤ b * b := by positivity
    linarith

/-- Melfi's theorem with the size condition `a * (a + b) < 2 ^ (k + 2)`. -/
theorem primitiveWeird_main (k a b : ℕ) (hab : b + 3 < a) (hsize : a * (a + b) < 2 ^ (k + 2))
    (hp : (2 ^ (k + 2) - a).Prime) (hq : (2 ^ (k + 2) + b).Prime) :
    Erdos470.PrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b)) := by
  obtain ⟨K, hK⟩ : ∃ K, K = 2 ^ k := ⟨_, rfl⟩
  have hX : 2 ^ (k + 2) = 4 * K := by rw [hK, pow_add]; ring
  rw [hX] at hsize hp hq
  rw [hX, ← hK]
  have ha4 : 4 ≤ a := by omega
  have h4a : 4 * a ≤ a * (a + b) := by nlinarith
  have haK : a < K := by omega
  generalize hpd : 4 * K - a = p at hp ⊢
  generalize hqd : 4 * K + b = q at hq ⊢
  have hpa : p + a = 4 * K := by omega
  have hK0 : K ≠ 0 := by omega
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · omega
    · exact h
  obtain ⟨j, hj⟩ : ∃ j, a = b + 4 + 2 * j := ⟨(a - b - 4) / 2, by omega⟩
  have hpq : p ≠ q := by omega
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have cKp : Nat.Coprime K p := by rw [hK]; exact coprime_two_pow_of_odd hpodd k
  have cKq : Nat.Coprime K q := by rw [hK]; exact coprime_two_pow_of_odd hqodd k
  have hS2 : (∑ d ∈ K.divisors, d) + 1 = 2 * K := by
    rw [hK, sigma_two_pow k, pow_succ]; ring
  have hσn : ∑ d ∈ (K * p * q).divisors, d = (∑ d ∈ K.divisors, d) * (p + 1) * (q + 1) := by
    rw [Nat.Coprime.sum_divisors_mul (Nat.Coprime.mul_left cKq cpq),
      Nat.Coprime.sum_divisors_mul cKp, sigma_prime hp, sigma_prime hq]
  have hid := sigma_identity (S2 := ∑ d ∈ K.divisors, d) hpa hqd.symm hj hS2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [Nat.abundant_iff_sum_divisors, hσn, hid]
    have : 0 < 2 * K * (2 * j + 1) := by positivity
    omega
  · -- not pseudoperfect
    rintro ⟨_, s, hs, hsum⟩
    have h1 := Finset.sum_sdiff (f := fun d => d) hs
    have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := K * p * q)
    obtain ⟨U, V, W, hT, hW⟩ := subset_sum_decomp hK0 hp hq ((K * p * q).properDivisors \ s)
      (fun d hd => (Nat.mem_properDivisors.mp (Finset.sdiff_subset hd)).1)
    apply gap_contra hpa hqd.symm hj hsize hW hS2 (U := U) (V := V)
    rw [hσn, hid] at h2
    omega
  · -- primitive
    intro d hd
    rw [Nat.mem_properDivisors] at hd
    obtain ⟨hdvd, hlt⟩ := hd
    rintro ⟨habund, _⟩
    rw [hK] at hdvd hlt
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
          calc 2 ^ i * (p * q) < 2 ^ k * p * q := hlt
            _ = 2 ^ k * (p * q) := by ring
        have := Nat.lt_of_mul_lt_mul_right h'
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      have hTK : 2 ^ (i + 1) ≤ K := by
        rw [hK]; exact Nat.pow_le_pow_right (by norm_num) hik
      have hpqodd : (p * q) % 2 = 1 := by
        rw [Nat.mul_mod, hpodd, hqodd]
      refine not_abundant_two_pow_mul i hpqodd ?_ habund
      rw [Nat.Coprime.sum_divisors_mul cpq, sigma_prime hp, sigma_prime hq]
      have hp3 : 3 * K + 1 ≤ p := by omega
      have hpq' : p ≤ q := by omega
      have e1 : 2 ^ (i + 1) * (p + q + 1) ≤ K * (p + q + 1) := Nat.mul_le_mul_right _ hTK
      have e2 : (3 * K + 1) * q ≤ p * q := Nat.mul_le_mul_right _ hp3
      have e3 : K * p ≤ K * q := Nat.mul_le_mul_left _ hpq'
      have e4 : K * 1 ≤ K * q := Nat.mul_le_mul_left _ (by omega)
      nlinarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 := by
  intro k a b hab hsize hp hq
  exact OMA.Helpers.primitiveWeird_main k a b hab hsize hp hq
