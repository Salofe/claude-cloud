import OMAStatements.S_oeis_a345003
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a345003

theorem rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

theorem rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos (fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos)

theorem a048250_eq {n : ℕ} (hn : n ≠ 0) :
    (a048250 n : ℚ) = ∏ p ∈ n.primeFactors, (1 + (p : ℚ)) := by
  rw [Finset.prod_one_add]
  unfold a048250
  rw [Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  rfl

theorem psi_mul_rad {n : ℕ} (hn : n ≠ 0) :
    psi n * (rad n : ℚ) = (n : ℚ) * (a048250 n : ℚ) := by
  rw [a048250_eq hn]
  unfold psi rad
  push_cast
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  field_simp
  ring

theorem key {n : ℕ} (hn : 0 < n) :
    a344998 n = a344999 n ↔ ((deriv n : ℚ) = psi n ∨ (sigma n : ℚ) = 2 * n) := by
  have hr : (rad n : ℚ) ≠ 0 := by exact_mod_cast (rad_pos n).ne'
  have hN : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : ((a003557 n : ℕ) : ℚ) = n / rad n := by
    unfold a003557; rw [Nat.cast_div (rad_dvd n) hr]
  have h2 : (a048250 n : ℚ) = psi n * rad n / n := by
    rw [psi_mul_rad hn.ne']; field_simp
  unfold a344998 a344999 a342001 a344753 a345001
  rw [h1, h2]
  have e : (deriv n : ℚ) / (n / rad n) * (sigma n + psi n - 2 * n) -
      psi n * rad n / n * (sigma n + deriv n - 2 * n) =
      (rad n / n) * (((deriv n : ℚ) - psi n) * (sigma n - 2 * n)) := by
    field_simp; ring
  constructor
  · intro h
    have h0 : (rad n / n : ℚ) * (((deriv n : ℚ) - psi n) * (sigma n - 2 * n)) = 0 := by
      rw [← e, h, sub_self]
    rcases mul_eq_zero.1 h0 with h3 | h3
    · exact absurd h3 (div_ne_zero hr hN)
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact Or.inl (sub_eq_zero.1 h4)
      · exact Or.inr (sub_eq_zero.1 h4)
  · intro h
    have h0 : (rad n / n : ℚ) * (((deriv n : ℚ) - psi n) * (sigma n - 2 * n)) = 0 := by
      rcases h with h | h <;> simp [h]
    rw [← e] at h0
    exact sub_eq_zero.1 h0

theorem psi_eq_nat {n : ℕ} (hn : n ≠ 0) :
    psi n = ((∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1) : ℕ) : ℚ) := by
  have hN : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact_mod_cast h.symm
  unfold psi
  rw [hN, ← Finset.prod_mul_distrib]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hv : 1 ≤ n.factorization p :=
    (hp'.dvd_iff_one_le_factorization hn).1 (Nat.dvd_of_mem_primeFactors hp)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hv).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  field_simp

theorem sigma_prod {n : ℕ} (hn : n ≠ 0) :
    sigma n = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
  unfold sigma
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      ArithmeticFunction.isMultiplicative_sigma hn,
    Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  exact ArithmeticFunction.sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)

theorem geom_zmod2 {p v : ℕ} (hp : Odd p) :
    ((∑ i ∈ Finset.range (v + 1), p ^ i : ℕ) : ZMod 2) = ((v + 1 : ℕ) : ZMod 2) := by
  have h : (p : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.2 hp
  push_cast
  simp [h]

theorem geom_even {p v : ℕ} (hp : Odd p) (hv : Odd v) :
    2 ∣ ∑ i ∈ Finset.range (v + 1), p ^ i := by
  rw [← even_iff_two_dvd, ← ZMod.natCast_eq_zero_iff_even, geom_zmod2 hp,
    ZMod.natCast_eq_zero_iff_even]
  exact hv.add_one

theorem odd_perfect_omega {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) :
    ((∑ p ∈ n.primeFactors, n.factorization p : ℕ) : ZMod 2) = 1 := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hs : sigma n = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).1 hperf
  have hprod := sigma_prod hn0
  have hpodd : ∀ p ∈ n.primeFactors, Odd p :=
    fun p hp => hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hex : ∃ p ∈ n.primeFactors, Odd (n.factorization p) := by
    by_contra hcon
    push Not at hcon
    have h1 : ((sigma n : ℕ) : ZMod 2) = 1 := by
      rw [hprod, Nat.cast_prod]
      apply Finset.prod_eq_one
      intro p hp
      rw [geom_zmod2 (hpodd p hp), Nat.cast_add, Nat.cast_one,
        (ZMod.natCast_eq_zero_iff_even.2 (Nat.not_odd_iff_even.1 (hcon p hp))), zero_add]
    rw [hs] at h1
    push_cast at h1
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul] at h1
    exact zero_ne_one h1
  obtain ⟨p0, hp0, hv0⟩ := hex
  have huniq : ∀ q ∈ n.primeFactors, Odd (n.factorization q) → q = p0 := by
    intro q hq hvq
    by_contra hne
    have hsub : ({q, p0} : Finset ℕ) ⊆ n.primeFactors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hq
      · exact hp0
    have hd := Finset.prod_dvd_prod_of_subset _ _
      (fun p => ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) hsub
    rw [Finset.prod_pair hne, ← hprod, hs] at hd
    have h4 : 2 * 2 ∣ 2 * n :=
      (mul_dvd_mul (geom_even (hpodd q hq) hvq) (geom_even (hpodd p0 hp0) hv0)).trans hd
    have h2 : 2 ∣ n := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [Nat.cast_sum, Finset.sum_eq_single_of_mem p0 hp0]
  · exact ZMod.natCast_eq_one_iff_odd.2 hv0
  · intro q hq hne
    apply ZMod.natCast_eq_zero_iff_even.2
    by_contra hcon
    exact hne (huniq q hq (Nat.not_even_iff_odd.1 hcon))

theorem deriv_zmod2 {n : ℕ} (hodd : Odd n) :
    ((S_oeis_a345003.deriv n : ℕ) : ZMod 2) = ((∑ p ∈ n.primeFactors, n.factorization p : ℕ) : ZMod 2) := by
  unfold S_oeis_a345003.deriv
  rw [Nat.cast_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have h : ((n / p : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.2
    (hodd.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
  rw [Nat.cast_mul, h, mul_one]

theorem not_odd_case {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) : (S_oeis_a345003.deriv n : ℚ) ≠ psi n := by
  intro h
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hom := odd_perfect_omega hodd hperf
  have hne : n.primeFactors.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty, Nat.cast_zero] at hom
    exact zero_ne_one hom
  obtain ⟨p, hp⟩ := hne
  rw [psi_eq_nat hn0] at h
  have h' : S_oeis_a345003.deriv n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1) :=
    by exact_mod_cast h
  have hpo : Odd p := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have he : 2 ∣ S_oeis_a345003.deriv n := by
    rw [h']
    exact (Dvd.dvd.mul_left (even_iff_two_dvd.1 hpo.add_one) _).trans (Finset.dvd_prod_of_mem _ hp)
  have h0 : ((S_oeis_a345003.deriv n : ℕ) : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.2 (even_iff_two_dvd.2 he)
  rw [deriv_zmod2 hodd, hom] at h0
  exact one_ne_zero h0

theorem sum_two_pow (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem even_perfect_form {n : ℕ} (hev : Even n) (hperf : Nat.Perfect n) :
    ∃ k q : ℕ, 1 ≤ k ∧ q.Prime ∧ Odd q ∧ n = 2 ^ k * q := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hs : sigma n = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).1 hperf
  have hnm : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime 2 (n / 2 ^ n.factorization 2) := Nat.coprime_ordCompl Nat.prime_two hn0
  have hk : 1 ≤ n.factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization hn0).1 (even_iff_two_dvd.1 hev)
  generalize n.factorization 2 = k at hnm hcop hk
  generalize n / 2 ^ k = m at hnm hcop
  have hmodd : Odd m := Nat.coprime_two_left.1 hcop
  have hm0 : m ≠ 0 := by rintro rfl; simp at hnm; exact hn0 hnm.symm
  have hsig : sigma n = (2 ^ (k + 1) - 1) * sigma m := by
    rw [← hnm]
    unfold sigma
    rw [Nat.Coprime.sum_divisors_mul (Nat.Coprime.pow_left k hcop),
      Nat.sum_divisors_prime_pow Nat.prime_two]
    congr 1
    have := sum_two_pow (k + 1)
    omega
  have hpow : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ (k + 1) = M + 1 := ⟨2 ^ (k + 1) - 1, by omega⟩
  rw [hM, Nat.add_sub_cancel] at hsig
  have hM3 : 3 ≤ M := by omega
  have heq : M * sigma m = (M + 1) * m := by
    rw [← hsig, hs, ← hnm, ← hM]; ring
  have hdvd : M ∣ m := by
    have hc : Nat.Coprime M (M + 1) := Nat.coprime_self_add_right.2 (Nat.coprime_one_right M)
    exact hc.dvd_of_dvd_mul_left ⟨sigma m, heq.symm⟩
  obtain ⟨c, hc⟩ := hdvd
  have hsm : sigma m = m + c := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < M by omega)
    rw [heq, hc]; ring
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hm0 hc
  have hc1 : c = 1 := by
    by_contra hne
    have hcm : c < m := by rw [hc]; nlinarith [Nat.pos_of_ne_zero hc0]
    have h1c : 1 < c := by omega
    have hsub : ({1, c, m} : Finset ℕ) ⊆ m.divisors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl | rfl
      · exact ⟨one_dvd _, hm0⟩
      · exact ⟨⟨M, by rw [hc, mul_comm]⟩, hm0⟩
      · exact ⟨dvd_refl _, hm0⟩
    have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_singleton] at hle
    unfold sigma at hsm
    omega
  have hprime : m.Prime := by
    rw [← Nat.sum_properDivisors_eq_one_iff_prime]
    have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
    unfold sigma at hsm
    omega
  exact ⟨k, m, hk, hprime, hmodd, hnm.symm⟩

theorem not_even_case {n : ℕ} (hev : Even n) (hperf : Nat.Perfect n) :
    (S_oeis_a345003.deriv n : ℚ) ≠ psi n := by
  obtain ⟨k, q, hk, hq, hqo, rfl⟩ := even_perfect_form hev hperf
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hq2 : q ≠ 2 := by rintro rfl; exact absurd hqo (by decide)
  have h2q : (2 : ℕ) ≠ q := fun h => hq2 h.symm
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hpf : (2 ^ (j + 1) * q).primeFactors = {2, q} := by
    rw [Nat.primeFactors_mul (by positivity) hq.ne_zero,
      Nat.primeFactors_prime_pow (by omega) Nat.prime_two, hq.primeFactors]
    rfl
  have hf2 : (2 ^ (j + 1) * q).factorization 2 = j + 1 := by
    rw [Nat.factorization_mul (by positivity) hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq
        Nat.prime_two hq).1 h).symm)]
    simp
  have hfq : (2 ^ (j + 1) * q).factorization q = 1 := by
    rw [Nat.factorization_mul (by positivity) hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq
        hq Nat.prime_two).1 h))]
    simp
  have hd2 : 2 ^ (j + 1) * q / 2 = 2 ^ j * q :=
    Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
  have hdq : 2 ^ (j + 1) * q / q = 2 ^ (j + 1) := Nat.mul_div_cancel _ hq.pos
  unfold S_oeis_a345003.deriv psi
  rw [hpf, Finset.sum_pair h2q, Finset.prod_pair h2q, hf2, hfq, hd2, hdq]
  intro h
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h' : (2 : ℚ) ^ j * (((j : ℚ) + 1) * q + 2 - 3 * (q + 1)) = 0 := by
    push_cast at h
    field_simp at h
    linear_combination (1 / 2 : ℚ) * h
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd h0 (by positivity)
  · have hn : ((j + 1) * q + 2 : ℕ) = 3 * (q + 1) := by
      have : ((j : ℚ) + 1) * q + 2 = 3 * (q + 1) := by linarith
      exact_mod_cast this
    rcases Nat.lt_or_ge j 3 with hj | hj
    · interval_cases j <;> omega
    · nlinarith

theorem disj {n : ℕ} (hperf : Nat.Perfect n) : (S_oeis_a345003.deriv n : ℚ) ≠ psi n := by
  rcases Nat.even_or_odd n with h | h
  · exact not_even_case h hperf
  · exact not_odd_case h hperf

end OMA.Helpers

open OMA.S_oeis_a345003 OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a345003.main := by
  constructor
  · ext k
    simp only [A345003, A000396, A301939, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hk, h⟩
      rcases (key hk).1 h with h1 | h1
      · exact Or.inr ⟨hk, h1⟩
      · left
        rw [Nat.perfect_iff_sum_divisors_eq_two_mul hk]
        exact_mod_cast h1
    · rintro (h | ⟨hk, h⟩)
      · refine ⟨h.2, (key h.2).2 (Or.inr ?_)⟩
        have := (Nat.perfect_iff_sum_divisors_eq_two_mul h.2).1 h
        exact_mod_cast this
      · exact ⟨hk, (key hk).2 (Or.inl h)⟩
  · rw [Set.disjoint_left]
    rintro n hn ⟨_, h⟩
    exact disj hn h
