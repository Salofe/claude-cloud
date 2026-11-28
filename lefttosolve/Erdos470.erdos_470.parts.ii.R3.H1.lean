import OMAReductions.R_Erdos470_erdos_470_parts_ii_R3

/-!
# Step H1 of the reduction Erdos470.erdos_470.parts.ii.R3

Let `M = 2 ^ (k + 1)`, let `p ≠ q` be primes above `M` and put `n = 2 ^ k * p * q`.
If `n` is abundant and the excess `e = (M - 1) (p + 1) (q + 1) - M p q` avoids every block
`[b p + c q, b p + c q + M)` with `b, c < M`, then `n` is a primitive weird number.

Only upstream definitions (`Erdos470.PrimitiveWeird` and the Mathlib notions `Nat.Weird`,
`Nat.Abundant`, `Nat.Pseudoperfect`) are used. The argument:

* `σ(2 ^ k * m) = (2 ^ (k + 1) - 1) σ(m)` for odd `m`, so `σ(n) = (M - 1) (p + 1) (q + 1)` and
  abundance of `n` is exactly the hypothesis.
* If a set `s` of proper divisors sums to `n`, its complement `s'` among the proper divisors
  sums to `e`. Since `e < p q`, no element of `s'` is divisible by `p q`. Splitting `s'` by
  divisibility by `p` and by `q`, each class is a set of numbers `m t` (with `m` one of `1, p, q`)
  whose cofactors `t` are distinct divisors of `2 ^ k`, so its sum is `m` times a number below
  `M`. Hence `e = a + b p + c q` with `a, b, c < M`, which the block condition forbids.
* A proper divisor of `n` divides `2 ^ k p`, `2 ^ k q` or `2 ^ (k - 1) p q`; none of these is
  abundant because `p, q > M`, so (abundance passing to multiples) no proper divisor is abundant,
  let alone weird.
-/

namespace OMA.Helpers

open Finset

/-- The geometric sum `1 + 2 + ... + 2 ^ (k - 1) = 2 ^ k - 1`, in additive form. -/
theorem e470_sum_range_two_pow (k : ℕ) : ∑ i ∈ range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ]; omega

/-- `σ(2 ^ k) = 2 ^ (k + 1) - 1`. -/
theorem e470_sigma_two_pow (k : ℕ) : ∑ d ∈ (2 ^ k).divisors, d = 2 ^ (k + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  have := e470_sum_range_two_pow (k + 1)
  omega

/-- `σ(p) = p + 1` for a prime `p`. -/
theorem e470_sigma_prime {p : ℕ} (hp : p.Prime) : ∑ d ∈ p.divisors, d = p + 1 := by
  rw [Nat.Prime.sum_divisors hp]

/-- A prime other than `2` is coprime to every power of `2`. -/
theorem e470_coprime_two_pow {k p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Nat.Coprime (2 ^ k) p :=
  Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h2))

/-- `σ(2 ^ k p) = (2 ^ (k + 1) - 1) (p + 1)` for an odd prime `p`. -/
theorem e470_sigma_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ∑ d ∈ (2 ^ k * p).divisors, d = (2 ^ (k + 1) - 1) * (p + 1) := by
  rw [Nat.Coprime.sum_divisors_mul (e470_coprime_two_pow hp h2), e470_sigma_two_pow,
    e470_sigma_prime hp]

/-- `σ(2 ^ k p q) = (2 ^ (k + 1) - 1) (p + 1) (q + 1)` for distinct odd primes `p, q`. -/
theorem e470_sigma_two_pow_mul_prime_mul_prime {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h2p : p ≠ 2) (h2q : q ≠ 2) (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ k * p * q).divisors, d = (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime (2 ^ k) (p * q) :=
    Nat.Coprime.mul_right (e470_coprime_two_pow hp h2p) (e470_coprime_two_pow hq h2q)
  have hpq' : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [mul_assoc, Nat.Coprime.sum_divisors_mul hcop, Nat.Coprime.sum_divisors_mul hpq',
    e470_sigma_two_pow, e470_sigma_prime hp, e470_sigma_prime hq]
  ring

/-- `2 ^ k * p` is not abundant when `p` is a prime above `2 ^ (k + 1)`. -/
theorem e470_not_abundant_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (h : 2 ^ (k + 1) < p) :
    ¬ (2 ^ k * p).Abundant := by
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hM : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [Nat.abundant_iff_sum_divisors, e470_sigma_two_pow_mul_prime hp (by omega)]
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ k = t + 1 := ⟨2 ^ k - 1, by omega⟩
  have h1 : 2 ^ (k + 1) - 1 = 2 * t + 1 := by omega
  rw [h1, ht]
  have h2 : 2 * t + 2 < p := by omega
  intro hlt
  nlinarith

/-- `2 ^ j * p * q` is not abundant when `p` and `q` are distinct primes above `2 ^ (j + 2)`. -/
theorem e470_not_abundant_two_pow_mul_pq {j p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : 2 ^ (j + 2) < p) (h2 : 2 ^ (j + 2) < q) : ¬ (2 ^ j * p * q).Abundant := by
  have hN : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hM : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
  have hM1 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [Nat.abundant_iff_sum_divisors,
    e470_sigma_two_pow_mul_prime_mul_prime hp hq (by omega) (by omega) hpq]
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ j = t + 1 := ⟨2 ^ j - 1, by omega⟩
  have h3 : 2 ^ (j + 1) - 1 = 2 * t + 1 := by omega
  rw [h3, ht]
  have hp' : 4 * t + 5 ≤ p := by omega
  have hq' : 4 * t + 5 ≤ q := by omega
  have e1 : (4 * t + 5) * q ≤ p * q := Nat.mul_le_mul_right q hp'
  have e2 : (4 * t + 5) * p ≤ q * p := Nat.mul_le_mul_right p hq'
  intro hlt
  nlinarith

/-- A proper divisor of `2 ^ k * p * q` is never weird. -/
theorem e470_proper_not_weird {k p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpM : 2 ^ (k + 1) < p) (hqM : 2 ^ (k + 1) < q) (hpq : p ≠ q)
    (hd : d ∈ (2 ^ k * p * q).properDivisors) : ¬ d.Weird := by
  rintro ⟨hab, -⟩
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨hdvd, hlt⟩ := hd
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  by_cases hpd : p ∣ d
  · by_cases hqd : q ∣ d
    · have hpqd : p * q ∣ d :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr hpq) hpd hqd
      obtain ⟨t, rfl⟩ := hpqd
      have ht : t ∣ 2 ^ k := by
        have h' : p * q * t ∣ p * q * 2 ^ k := by
          rwa [show 2 ^ k * p * q = p * q * 2 ^ k by ring] at hdvd
        exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h'
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ht
      have hik : i < k := by
        rcases lt_or_eq_of_le hi with h | h
        · exact h
        · subst h
          exfalso
          rw [show 2 ^ i * p * q = p * q * 2 ^ i by ring] at hlt
          exact lt_irrefl _ hlt
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hdj : p * q * 2 ^ i ∣ 2 ^ j * p * q := by
        have hij : 2 ^ i ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
        rw [show 2 ^ j * p * q = p * q * 2 ^ j by ring]
        exact Nat.mul_dvd_mul_left (p * q) hij
      exact e470_not_abundant_two_pow_mul_pq hp hq hpq hpM hqM
        (Nat.Abundant.of_dvd hab hdj (by positivity))
    · have hcop : Nat.Coprime d q :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
      have h' : d ∣ 2 ^ k * p := hcop.dvd_of_dvd_mul_right hdvd
      exact e470_not_abundant_two_pow_mul_prime hp hpM (Nat.Abundant.of_dvd hab h' (by positivity))
  · have hcop : Nat.Coprime d p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
    have h' : d ∣ 2 ^ k * q := by
      rw [show 2 ^ k * p * q = (2 ^ k * q) * p by ring] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
    exact e470_not_abundant_two_pow_mul_prime hq hqM (Nat.Abundant.of_dvd hab h' (by positivity))

/-- A finite set of multiples `m * t` with `t ∣ 2 ^ k` sums to `m * b` with `b < 2 ^ (k + 1)`. -/
theorem e470_class_bound (k m : ℕ) (S : Finset ℕ)
    (hS : ∀ d ∈ S, m ∣ d ∧ d / m ∣ 2 ^ k) :
    ∃ b, ∑ d ∈ S, d = m * b ∧ b + 1 ≤ 2 ^ (k + 1) := by
  refine ⟨∑ d ∈ S, d / m, ?_, ?_⟩
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact (Nat.mul_div_cancel' (hS d hd).1).symm
  · have hinj : Set.InjOn (fun d => d / m) (S : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := Nat.mul_div_cancel' (hS x hx).1
      have h2 := Nat.mul_div_cancel' (hS y hy).1
      simp only at hxy
      rw [← h1, ← h2, hxy]
    rw [← Finset.sum_image (f := fun x => x) hinj]
    have hsub : S.image (fun d => d / m) ⊆ (2 ^ k).divisors := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      rw [Nat.mem_divisors]
      exact ⟨(hS d hd).2, by positivity⟩
    have h3 := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
    rw [e470_sigma_two_pow] at h3
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega

/-- The core: `2 ^ k * p * q` is not pseudoperfect under the block condition. -/
theorem e470_not_pseudoperfect {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpM : 2 ^ (k + 1) < p) (hqM : 2 ^ (k + 1) < q) (hpq : p ≠ q)
    (hab : 2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1))
    (hblock : ∀ b c : ℕ, b < 2 ^ (k + 1) → c < 2 ^ (k + 1) →
      ¬ (b * p + c * q ≤ (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q ∧
        (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q < b * p + c * q + 2 ^ (k + 1))) :
    ¬ (2 ^ k * p * q).Pseudoperfect := by
  rintro ⟨hpos, s, hs, hsum⟩
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  have h2M : 2 ≤ 2 ^ (k + 1) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega
  have hsig := e470_sigma_two_pow_mul_prime_mul_prime (k := k) hp hq (by omega) (by omega) hpq
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsig
  have hsd := Finset.sum_sdiff (f := fun x => x) hs
  have h2n : 2 * (2 ^ k * p * q) = 2 ^ (k + 1) * p * q := by ring
  set E := (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q with hE
  set s' := (2 ^ k * p * q).properDivisors \ s with hs'
  have hs'sum : ∑ d ∈ s', d = E := by omega
  -- `E < p * q`
  have hEpq : E < p * q := by
    obtain ⟨u, hu⟩ : ∃ u, 2 ^ (k + 1) = u + 1 := ⟨2 ^ (k + 1) - 1, by omega⟩
    have hu1 : 2 ^ (k + 1) - 1 = u := by omega
    have hp' : u + 2 ≤ p := by omega
    have hq' : u + 2 ≤ q := by omega
    have e1 : (u + 2) * q ≤ p * q := Nat.mul_le_mul_right q hp'
    have e2 : (u + 2) * p ≤ q * p := Nat.mul_le_mul_right p hq'
    have key : u * (p + 1) * (q + 1) < (u + 2) * p * q := by nlinarith
    have hab' : (u + 1) * p * q < u * (p + 1) * (q + 1) := by rw [hu1, hu] at hab; exact hab
    have hsplit : (u + 2) * p * q = (u + 1) * p * q + p * q := by ring
    rw [hE, hu1, hu]
    omega
  -- every element of `s'` is a divisor of `n` below `p * q`
  have hmem : ∀ d ∈ s', d ∣ 2 ^ k * p * q ∧ 0 < d ∧ d < p * q := by
    intro d hd
    have hd' := Finset.mem_sdiff.mp hd
    have hdp := Nat.mem_properDivisors.mp hd'.1
    refine ⟨hdp.1, Nat.pos_of_dvd_of_pos hdp.1 (by positivity), ?_⟩
    have := Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hd
    omega
  have hnotpq : ∀ d ∈ s', p ∣ d → q ∣ d → False := by
    intro d hd hpd hqd
    have hpqd : p * q ∣ d :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr hpq) hpd hqd
    have := Nat.le_of_dvd (hmem d hd).2.1 hpqd
    have := (hmem d hd).2.2
    omega
  have hsplit1 := Finset.sum_filter_add_sum_filter_not s' (fun d => p ∣ d) (fun d => d)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (s'.filter (fun d => ¬ p ∣ d))
    (fun d => q ∣ d) (fun d => d)
  obtain ⟨b, hb, hbM⟩ := e470_class_bound k p (s'.filter (fun d => p ∣ d)) (by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hd, hpd⟩ := hd
    refine ⟨hpd, ?_⟩
    have hqd : ¬ q ∣ d := fun hqd => hnotpq d hd hpd hqd
    obtain ⟨t, rfl⟩ := hpd
    rw [Nat.mul_div_cancel_left t hp0]
    have h1 : p * t ∣ p * (2 ^ k * q) := by
      rw [show p * (2 ^ k * q) = 2 ^ k * p * q by ring]; exact (hmem _ hd).1
    have h2 : t ∣ 2 ^ k * q := Nat.dvd_of_mul_dvd_mul_left hp0 h1
    have hqt : ¬ q ∣ t := fun h => hqd (Dvd.dvd.mul_left h p)
    have hcop : Nat.Coprime t q := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqt)
    exact hcop.dvd_of_dvd_mul_right h2)
  obtain ⟨c, hc, hcM⟩ := e470_class_bound k q
    ((s'.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d)) (by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_filter] at hd
    obtain ⟨⟨hd, hpd⟩, hqd⟩ := hd
    refine ⟨hqd, ?_⟩
    obtain ⟨t, rfl⟩ := hqd
    rw [Nat.mul_div_cancel_left t hq0]
    have h1 : q * t ∣ q * (2 ^ k * p) := by
      rw [show q * (2 ^ k * p) = 2 ^ k * p * q by ring]; exact (hmem _ hd).1
    have h2 : t ∣ 2 ^ k * p := Nat.dvd_of_mul_dvd_mul_left hq0 h1
    have hpt : ¬ p ∣ t := fun h => hpd (Dvd.dvd.mul_left h q)
    have hcop : Nat.Coprime t p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpt)
    exact hcop.dvd_of_dvd_mul_right h2)
  obtain ⟨a, ha, haM⟩ := e470_class_bound k 1
    ((s'.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d)) (by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_filter] at hd
    obtain ⟨⟨hd, hpd⟩, hqd⟩ := hd
    refine ⟨one_dvd d, ?_⟩
    rw [Nat.div_one]
    have hcq : Nat.Coprime d q := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
    have hcp : Nat.Coprime d p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
    have h1 : d ∣ 2 ^ k * p := hcq.dvd_of_dvd_mul_right (hmem d hd).1
    exact hcp.dvd_of_dvd_mul_right h1)
  have htot : E = p * b + (q * c + 1 * a) := by
    rw [← hs'sum, ← hsplit1, ← hsplit2, hb, hc, ha]
  apply hblock b c (by omega) (by omega)
  constructor
  · rw [htot]; nlinarith
  · rw [htot]; nlinarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R3.H1 := by
  intro k p q hp hq hpM hqM hpq hab hblock
  refine ⟨⟨?_, OMA.Helpers.e470_not_pseudoperfect hp hq hpM hqM hpq hab hblock⟩, ?_⟩
  · have h2M : 2 ≤ 2 ^ (k + 1) := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]; omega
    rw [Nat.abundant_iff_sum_divisors,
      OMA.Helpers.e470_sigma_two_pow_mul_prime_mul_prime hp hq (by omega) (by omega) hpq]
    have h2n : 2 * (2 ^ k * p * q) = 2 ^ (k + 1) * p * q := by ring
    rw [h2n]
    exact hab
  · intro d hd
    exact OMA.Helpers.e470_proper_not_weird hp hq hpM hqM hpq hd
