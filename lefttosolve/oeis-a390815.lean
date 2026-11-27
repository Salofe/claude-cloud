import OMAStatements.S_oeis_a390815
import Mathlib

-- Problem: A390815: Denominators > 1 of ratio n!/sigma(n).
-- Proof: if n is not a prime power, sigma(n) divides n! (multiplicativity and
-- i! j! | (i+j)!); if n = p^k then sigma(n) < 2n, so sigma(n) either divides n! or is
-- a prime > n, and for k odd (1+p) divides sigma(n), forcing k even.


namespace OMA.Helpers

open ArithmeticFunction

theorem geom_succ (p k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), p ^ i = p * (∑ i ∈ Finset.range (k + 1), p ^ i) + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

theorem geom_lt_two (p : ℕ) (hp : 2 ≤ p) :
    ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), p ^ i < 2 * p ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := geom_lt_two p hp k
    rw [geom_succ, pow_succ]
    nlinarith

theorem geom_lt_three (p : ℕ) (hp : 3 ≤ p) :
    ∀ k : ℕ, 2 * ∑ i ∈ Finset.range (k + 1), p ^ i < 3 * p ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := geom_lt_three p hp k
    rw [geom_succ, pow_succ]
    nlinarith

theorem geom_odd (p : ℕ) :
    ∀ j : ℕ, ∑ i ∈ Finset.range (2 * j + 2), p ^ i =
      (1 + p) * ∑ i ∈ Finset.range (j + 1), p ^ (2 * i)
  | 0 => by simp [Finset.sum_range_succ]
  | j + 1 => by
    have e1 : ∑ i ∈ Finset.range (2 * (j + 1) + 2), p ^ i =
        ∑ i ∈ Finset.range (2 * j + 2), p ^ i + p ^ (2 * j + 2) + p ^ (2 * j + 2 + 1) := by
      rw [show 2 * (j + 1) + 2 = 2 * j + 2 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have e2 : ∑ i ∈ Finset.range (j + 1 + 1), p ^ (2 * i) =
        ∑ i ∈ Finset.range (j + 1), p ^ (2 * i) + p ^ (2 * (j + 1)) :=
      Finset.sum_range_succ _ _
    rw [e1, e2, geom_odd p j]
    ring

theorem sigma_pp_lt {n : ℕ} (h : IsPrimePow n) : sigma 1 n < 2 * n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 h
  rw [sigma_one_apply_prime_pow hp]
  exact geom_lt_two p hp.two_le k

theorem sigma_pp_odd {n : ℕ} (h : IsPrimePow n) (hodd : ¬ 2 ∣ n) :
    2 * sigma 1 n < 3 * n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 h
  rw [sigma_one_apply_prime_pow hp]
  have h3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · subst h2
      exact absurd (dvd_pow_self 2 (by omega)) hodd
    · have := hp.two_le
      rcases h2 with ⟨r, hr⟩
      omega
  exact geom_lt_three p h3 k

theorem sigma_pos' {n : ℕ} (hn : 0 < n) : 0 < sigma 1 n := by
  rw [sigma_pos_iff]; exact hn

theorem dvd_fact_self {a : ℕ} (ha : 0 < a) : a ∣ a.factorial :=
  Nat.dvd_factorial ha le_rfl

theorem mul_dvd_fact {a b x y n : ℕ} (ha : a ∣ x.factorial) (hb : b ∣ y.factorial)
    (h : x + y ≤ n) : a * b ∣ n.factorial :=
  ((mul_dvd_mul ha hb).trans (Nat.factorial_mul_factorial_dvd_factorial_add x y)).trans
    (Nat.factorial_dvd_factorial h)

theorem pair_bound {q m : ℕ} (hq : IsPrimePow q) (hm : IsPrimePow m) (hc : Nat.Coprime q m)
    (h23 : ¬ (q = 2 ∧ m = 3)) (h32 : ¬ (q = 3 ∧ m = 2)) :
    sigma 1 q + sigma 1 m ≤ q * m := by
  have hq2 : 2 ≤ q := hq.two_le
  have hm2 : 2 ≤ m := hm.two_le
  have sq := sigma_pp_lt hq
  have sm := sigma_pp_lt hm
  have hne : q ≠ m := by
    rintro rfl
    rw [Nat.coprime_self] at hc
    omega
  by_cases hq' : q = 2
  · subst hq'
    have hodd : ¬ 2 ∣ m := by
      intro h2
      have := Nat.Coprime.coprime_dvd_right h2 hc
      norm_num at this
    have so := sigma_pp_odd hm hodd
    have : m ≠ 4 := by rintro rfl; exact hodd (by norm_num)
    have : m ≠ 3 := fun h => h23 ⟨rfl, h⟩
    omega
  by_cases hm' : m = 2
  · subst hm'
    have hodd : ¬ 2 ∣ q := by
      intro h2
      have := Nat.Coprime.coprime_dvd_left h2 hc
      norm_num at this
    have so := sigma_pp_odd hq hodd
    have : q ≠ 4 := by rintro rfl; exact hodd (by norm_num)
    have : q ≠ 3 := fun h => h32 ⟨h, rfl⟩
    omega
  have hq3 : 3 ≤ q := by omega
  have hm3 : 3 ≤ m := by omega
  rcases Nat.lt_or_ge q 4 with h4 | h4
  · have : q = 3 := by omega
    subst this
    have : 4 ≤ m := by omega
    nlinarith
  · nlinarith

theorem sigma_dvd_of_not_pp : ∀ n : ℕ, 2 ≤ n → ¬ IsPrimePow n → sigma 1 n ∣ n.factorial := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hnp
  have hn0 : n ≠ 0 := by omega
  have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
  set p := Nat.minFac n with hpdef
  have hk : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
  have hnqm : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
  generalize n / p ^ n.factorization p = m at hnqm hcop
  generalize hkk : n.factorization p = k at hnqm hcop hk
  have hqpp : IsPrimePow (p ^ k) := (isPrimePow_nat_iff _).2 ⟨p, k, hp, hk, rfl⟩
  generalize p ^ k = q at hnqm hcop hqpp
  have hq2 : 2 ≤ q := hqpp.two_le
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnqm
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hnqm
    exact hnp (hnqm ▸ hqpp)
  have hm2 : 2 ≤ m := by omega
  have hmn : m < n := by nlinarith
  have hsig : sigma 1 n = sigma 1 q * sigma 1 m := by
    rw [← hnqm]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have sq := sigma_pp_lt hqpp
  have sq0 : 0 < sigma 1 q := sigma_pos' (by omega)
  have sm0 : 0 < sigma 1 m := sigma_pos' (by omega)
  by_cases hmpp : IsPrimePow m
  · by_cases h6 : (q = 2 ∧ m = 3) ∨ (q = 3 ∧ m = 2)
    · have : n = 6 := by
        rcases h6 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← hnqm, h1, h2]
      subst this
      decide
    · push Not at h6
      have hb := pair_bound hqpp hmpp hcop (fun h => absurd h.2 (h6.1 h.1))
        (fun h => absurd h.2 (h6.2 h.1))
      rw [hsig]
      exact mul_dvd_fact (dvd_fact_self sq0) (dvd_fact_self sm0) (hnqm ▸ hb)
  · have ihm := ih m hmn hm2 hmpp
    have hm3 : 3 ≤ m := by
      by_contra h
      have : m = 2 := by omega
      exact hmpp (this ▸ Nat.prime_two.isPrimePow)
    rw [hsig]
    refine mul_dvd_fact (dvd_fact_self sq0) ihm ?_
    rw [← hnqm]
    nlinarith

theorem lemX (n s : ℕ) (hn : 8 ≤ n) (hs : 0 < s) (hs2 : s < 2 * n) :
    s ∣ n.factorial ∨ (s.Prime ∧ n < s) := by
  by_cases hp : s.Prime
  · by_cases h : s ≤ n
    · left; exact Nat.dvd_factorial hs h
    · right; exact ⟨hp, by omega⟩
  · left
    rcases Nat.lt_or_ge s 2 with h1 | h1
    · have : s = 1 := by omega
      subst this; exact one_dvd _
    have hsq := Nat.minFac_sq_le_self hs hp
    have ha2 : 2 ≤ s.minFac := (Nat.minFac_prime (by omega)).two_le
    obtain ⟨b, hb⟩ := Nat.minFac_dvd s
    set a := s.minFac with ha
    have hab : a ≤ b := by nlinarith
    have hbn : b < n := by nlinarith
    rcases Nat.lt_or_ge a b with h | h
    · have h1 : a ∣ (b - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
      have h2 : b.factorial = b * (b - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
      have : s ∣ b.factorial := by
        rw [hb, h2, mul_comm b]
        exact Nat.mul_dvd_mul_right h1 b
      exact this.trans (Nat.factorial_dvd_factorial (by omega))
    · have hab' : a = b := le_antisymm hab h
      have h2a : 2 * a ≤ n := by
        by_contra hc
        push Not at hc
        have : (n + 1) * (n + 1) ≤ (2 * a) * (2 * a) := Nat.mul_le_mul hc hc
        nlinarith
      have h1 : a ∣ (2 * a - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
      have h2 : (2 * a).factorial = (2 * a) * (2 * a - 1).factorial :=
        (Nat.mul_factorial_pred (by omega)).symm
      have : s ∣ (2 * a).factorial := by
        rw [hb, ← hab', h2]
        exact mul_dvd_mul (dvd_mul_left a 2) h1
      exact this.trans (Nat.factorial_dvd_factorial h2a)

/-- For a prime power `n = p ^ k` with `k` odd and `n ≥ 8`, the divisor sum is not prime. -/
theorem sigma_pp_prime_even {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (h8 : 8 ≤ p ^ k)
    (hs : (sigma 1 (p ^ k)).Prime) : Even k := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨j, rfl⟩ := hodd
  rw [sigma_one_apply_prime_pow hp, show 2 * j + 1 + 1 = 2 * j + 2 by ring, geom_odd] at hs
  have hp2 := hp.two_le
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp at hs h8
    -- hs : (1 + p).Prime, p prime, p ≥ 8
    rcases hp.eq_two_or_odd' with h2 | ⟨r, hr⟩
    · omega
    · have : 2 ∣ 1 + p := ⟨r + 1, by omega⟩
      rcases (Nat.Prime.eq_one_or_self_of_dvd hs 2 this) with h | h <;> omega
  · have hT : 2 ≤ ∑ i ∈ Finset.range (j + 1), p ^ (2 * i) := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      have : 1 ≤ p ^ (2 * (j' + 1)) := Nat.one_le_pow _ _ (by omega)
      simp
      omega
    rcases (Nat.Prime.eq_one_or_self_of_dvd hs (1 + p) (dvd_mul_right _ _)) with h | h
    · omega
    · have : (1 + p) * 1 < (1 + p) * ∑ i ∈ Finset.range (j + 1), p ^ (2 * i) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega

theorem small_a (n : ℕ) (h1 : 0 < n) (h8 : n < 8) :
    1 < OMA.S_oeis_a390815.reducedDen n → (OMA.S_oeis_a390815.reducedDen n).Prime := by
  interval_cases n <;> decide

theorem small_b (n : ℕ) (h4 : 4 ≤ n) (h8 : n < 8) (hnd : ¬ sigma 1 n ∣ n.factorial) :
    ∃ k : ℕ, n = k ^ 2 := by
  interval_cases n
  · exact ⟨2, rfl⟩
  all_goals exact absurd (by decide) hnd

end OMA.Helpers

open OMA.Helpers ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a390815.main := by
  -- common reduction: if sigma n does not divide n! and n ≥ 8, then n = p^k with sigma n prime > n
  have key : ∀ n : ℕ, 8 ≤ n → ¬ sigma 1 n ∣ n.factorial →
      IsPrimePow n ∧ (sigma 1 n).Prime ∧ n < sigma 1 n := by
    intro n hn hnd
    have hpp : IsPrimePow n := by
      by_contra h
      exact hnd (sigma_dvd_of_not_pp n (by omega) h)
    have := lemX n (sigma 1 n) hn (sigma_pos' (by omega)) (sigma_pp_lt hpp)
    rcases this with h | h
    · exact absurd h hnd
    · exact ⟨hpp, h⟩
  refine ⟨fun n hn hden => ?_, fun n hn hnd => ?_⟩
  · rcases Nat.lt_or_ge n 8 with h8 | h8
    · exact small_a n hn h8 hden
    · unfold OMA.S_oeis_a390815.reducedDen at hden ⊢
      by_cases hd : sigma 1 n ∣ n.factorial
      · rw [Nat.gcd_eq_left hd, Nat.div_self (sigma_pos' hn)] at hden
        omega
      · obtain ⟨_, hpr, hlt⟩ := key n h8 hd
        have hcop : Nat.gcd (sigma 1 n) n.factorial = 1 := by
          apply (Nat.Prime.coprime_iff_not_dvd hpr).2
          rw [hpr.dvd_factorial]
          omega
        rw [hcop, Nat.div_one]
        exact hpr
  · rcases Nat.lt_or_ge n 8 with h8 | h8
    · exact small_b n hn h8 hnd
    · obtain ⟨hpp, hpr, _⟩ := key n h8 hnd
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      obtain ⟨j, rfl⟩ := sigma_pp_prime_even hp hk h8 hpr
      exact ⟨p ^ j, by ring⟩
