import OMAStatements.S_oeis_a345051
import Mathlib

open OMA.S_oeis_a345051

namespace OMA.Helpers

theorem rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem totient_eq (n : ℕ) : Nat.totient n = a003557 n * a173557 n := by
  have h := Nat.totient_mul_prod_primeFactors n
  have hd : rad n ∣ n := Nat.prod_primeFactors_dvd n
  have hr := rad_pos n
  unfold a003557 a173557
  apply Nat.eq_of_mul_eq_mul_right hr
  calc Nat.totient n * rad n = n * ∏ p ∈ n.primeFactors, (p - 1) := h
    _ = (n / rad n * rad n) * ∏ p ∈ n.primeFactors, (p - 1) := by rw [Nat.div_mul_cancel hd]
    _ = _ := by ring

theorem a003557_pos {n : ℕ} (hn : 0 < n) : 0 < a003557 n :=
  Nat.div_pos (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)) (rad_pos n)

theorem key {n : ℕ} (hn : 0 < n) :
    a345048 n = a345049 n ↔ (deriv n = Nat.totient n ∨ sigma n = 2 * n) := by
  have hA : (a003557 n : ℚ) ≠ 0 := by exact_mod_cast (a003557_pos hn).ne'
  have ht : (Nat.totient n : ℚ) = (a003557 n : ℚ) * (a173557 n : ℚ) := by
    exact_mod_cast totient_eq n
  have hdiff : a345048 n - a345049 n =
      ((deriv n : ℚ) - Nat.totient n) * ((sigma n : ℚ) - 2 * n) / (a003557 n : ℚ) := by
    unfold a345048 a345049 a342001 a051709 a345001
    rw [ht]
    field_simp
    ring
  rw [← sub_eq_zero, hdiff, div_eq_zero_iff, or_iff_left hA, mul_eq_zero, sub_eq_zero,
    sub_eq_zero]
  constructor
  · rintro (h | h)
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · rintro (h | h)
    · left; exact_mod_cast h
    · right; exact_mod_cast h

theorem sigma_eq_prod (n : ℕ) (hn : n ≠ 0) : sigma n =
    ∏ p ∈ n.primeFactors, ArithmeticFunction.sigma 1 (p ^ n.factorization p) := by
  unfold sigma
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      ArithmeticFunction.isMultiplicative_sigma hn, Finsupp.prod, Nat.support_factorization]

theorem sigma_pp_mod (p a : ℕ) (hp : p.Prime) (hodd : p % 2 = 1) :
    ArithmeticFunction.sigma 1 (p ^ a) % 2 = (a + 1) % 2 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Finset.sum_nat_mod]
  have h : ∀ i ∈ Finset.range (a + 1), p ^ i % 2 = 1 := fun i _ => by
    simp [Nat.pow_mod, hodd]
  rw [Finset.sum_congr rfl h]
  simp

theorem odd_sum_exp {n : ℕ} (hn0 : 0 < n) (hodd : n % 2 = 1) (hs : sigma n = 2 * n) :
    (∑ p ∈ n.primeFactors, n.factorization p) % 2 = 1 := by
  have hprod : ∏ p ∈ n.primeFactors, ArithmeticFunction.sigma 1 (p ^ n.factorization p) =
      2 * n := (sigma_eq_prod n hn0.ne').symm.trans hs
  have hg0 : ∀ p ∈ n.primeFactors, ArithmeticFunction.sigma 1 (p ^ n.factorization p) ≠ 0 :=
    fun p hp => (ArithmeticFunction.sigma_pos 1 _
      (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'
  have hf : (∏ p ∈ n.primeFactors, ArithmeticFunction.sigma 1 (p ^ n.factorization p)).factorization 2
      = ∑ p ∈ n.primeFactors,
        (ArithmeticFunction.sigma 1 (p ^ n.factorization p)).factorization 2 := by
    rw [Nat.factorization_prod hg0, Finsupp.finsetSum_apply]
  have h2n : (2 * n).factorization 2 = 1 := by
    rw [Nat.factorization_mul two_ne_zero hn0.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by omega)]
  rw [hprod, h2n] at hf
  have hpodd : ∀ p ∈ n.primeFactors, p % 2 = 1 := by
    intro p hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · exact absurd (dvd_trans (Nat.dvd_of_mod_eq_zero h0) hpd) (by omega)
    · exact h1
  have hT : ∀ p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1),
      1 ≤ (ArithmeticFunction.sigma 1 (p ^ n.factorization p)).factorization 2 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hm := sigma_pp_mod p (n.factorization p) (Nat.prime_of_mem_primeFactors hp.1)
      (hpodd p hp.1)
    apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two (hg0 p hp.1)
    omega
  have hcard : (n.primeFactors.filter (fun p => n.factorization p % 2 = 1)).card ≤ 1 := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1), 1
        ≤ ∑ p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1),
          (ArithmeticFunction.sigma 1 (p ^ n.factorization p)).factorization 2 :=
          Finset.sum_le_sum hT
      _ ≤ ∑ p ∈ n.primeFactors,
          (ArithmeticFunction.sigma 1 (p ^ n.factorization p)).factorization 2 :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = 1 := hf.symm
  have hne : (n.primeFactors.filter (fun p => n.factorization p % 2 = 1)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hz : ∀ p ∈ n.primeFactors,
        (ArithmeticFunction.sigma 1 (p ^ n.factorization p)).factorization 2 = 0 := by
      intro p hp
      have hev : ¬ n.factorization p % 2 = 1 := by
        intro hc
        have : p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1) :=
          Finset.mem_filter.mpr ⟨hp, hc⟩
        rw [h] at this
        exact Finset.notMem_empty p this
      have hm := sigma_pp_mod p (n.factorization p) (Nat.prime_of_mem_primeFactors hp)
        (hpodd p hp)
      apply Nat.factorization_eq_zero_of_not_dvd
      omega
    rw [Finset.sum_eq_zero hz] at hf
    exact one_ne_zero hf
  obtain ⟨p0, hp0⟩ := Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hne))
  have hp0m : p0 ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1) := by
    rw [hp0]; exact Finset.mem_singleton_self p0
  rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p => n.factorization p % 2 = 1),
    hp0, Finset.sum_singleton]
  have h2 : (∑ p ∈ n.primeFactors.filter (fun p => ¬ n.factorization p % 2 = 1),
      n.factorization p) % 2 = 0 := by
    rw [Finset.sum_nat_mod, Finset.sum_eq_zero]
    · rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    omega
  have h1 := (Finset.mem_filter.mp hp0m).2
  omega

theorem deriv_odd {n : ℕ} (hodd : n % 2 = 1) :
    deriv n % 2 = (∑ p ∈ n.primeFactors, n.factorization p) % 2 := by
  unfold S_oeis_a345051.deriv
  rw [Finset.sum_nat_mod, Finset.sum_nat_mod n.primeFactors 2 (fun p => n.factorization p)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hq : (n / p) % 2 = 1 := by
    have hd : n / p ∣ n := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    rcases Nat.mod_two_eq_zero_or_one (n / p) with h | h
    · exact absurd (dvd_trans (Nat.dvd_of_mod_eq_zero h) hd) (by omega)
    · exact h
  rw [Nat.mul_mod, hq, mul_one, Nat.mod_mod]

theorem even_case {n : ℕ} (hn0 : 0 < n) (heven : n % 2 = 0) (hs : sigma n = 2 * n) :
    Nat.totient n < deriv n := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨k, hk⟩ | ⟨q, hq, hqd, hqodd⟩
  · exfalso
    subst hk
    unfold sigma at hs
    rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, Finset.sum_range_succ'] at hs
    have h0 : (∑ i ∈ Finset.range k, 2 ^ (i + 1)) % 2 = 0 := by
      rw [Finset.sum_nat_mod, Finset.sum_eq_zero]
      · rfl
      intro i _
      rw [pow_succ, Nat.mul_mod_left]
    omega
  · have h2 : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by omega, hn0.ne'⟩
    have hqP : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqd, hn0.ne'⟩
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.mpr even_two) hqodd
    have hsub : ({2, q} : Finset ℕ) ⊆ n.primeFactors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h2
      · exact hqP
    have hle : n.factorization 2 * (n / 2) + n.factorization q * (n / q) ≤ deriv n := by
      unfold S_oeis_a345051.deriv
      rw [← Finset.sum_pair (f := fun p => n.factorization p * (n / p)) hq2.symm]
      exact Finset.sum_le_sum_of_subset hsub
    have ha2 : 1 ≤ n.factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0.ne' (by omega)
    have haq : 1 ≤ n.factorization q := hq.factorization_pos_of_dvd hn0.ne' hqd
    have hnq : 1 ≤ n / q := Nat.div_pos (Nat.le_of_dvd hn0 hqd) hq.pos
    have e1 : n / 2 ≤ n.factorization 2 * (n / 2) := Nat.le_mul_of_pos_left _ ha2
    have e2 : 1 ≤ n.factorization q * (n / q) := Nat.mul_pos haq hnq
    have ht : 2 * Nat.totient n ≤ n := by
      have h := Nat.totient_mul_prod_primeFactors n
      rw [← Finset.mul_prod_erase _ _ h2, ← Finset.mul_prod_erase _ (fun p => p - 1) h2] at h
      have hP : 0 < ∏ p ∈ n.primeFactors.erase 2, p := Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).pos
      have hle' : ∏ p ∈ n.primeFactors.erase 2, (p - 1) ≤ ∏ p ∈ n.primeFactors.erase 2, p :=
        Finset.prod_le_prod' fun p _ => Nat.sub_le p 1
      have hm : 2 * Nat.totient n * (∏ p ∈ n.primeFactors.erase 2, p) ≤
          n * (∏ p ∈ n.primeFactors.erase 2, p) := by
        calc 2 * Nat.totient n * (∏ p ∈ n.primeFactors.erase 2, p)
            = Nat.totient n * (2 * ∏ p ∈ n.primeFactors.erase 2, p) := by ring
          _ = n * ((2 - 1) * ∏ p ∈ n.primeFactors.erase 2, (p - 1)) := h
          _ ≤ n * (∏ p ∈ n.primeFactors.erase 2, p) := by
            rw [show (2 : ℕ) - 1 = 1 from rfl, one_mul]
            exact Nat.mul_le_mul_left n hle'
      exact Nat.le_of_mul_le_mul_right hm hP
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a345051.main := by
  refine ⟨?_, ?_⟩
  · ext k
    simp only [A345051, A000396, A166374, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hk, h⟩
      rcases (OMA.Helpers.key hk).mp h with h | h
      · right; exact ⟨hk, h⟩
      · left; exact (Nat.perfect_iff_sum_divisors_eq_two_mul hk).mpr h
    · rintro (h | ⟨hk, h⟩)
      · have hk : 0 < k := h.2
        exact ⟨hk, (OMA.Helpers.key hk).mpr
          (Or.inr ((Nat.perfect_iff_sum_divisors_eq_two_mul hk).mp h))⟩
      · exact ⟨hk, (OMA.Helpers.key hk).mpr (Or.inl h)⟩
  · rw [Set.disjoint_left]
    rintro n hp ⟨hn0, hd⟩
    have hs : sigma n = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul hn0).mp hp
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have := OMA.Helpers.even_case hn0 he hs
      omega
    · have h1 := OMA.Helpers.odd_sum_exp hn0 ho hs
      have h2 := OMA.Helpers.deriv_odd ho
      have hn2 : 2 < n := by
        rcases (show n = 1 ∨ 2 < n by omega) with h | h
        · subst h
          simp [sigma] at hs
        · exact h
      have := Nat.totient_even hn2
      rw [Nat.even_iff] at this
      omega
