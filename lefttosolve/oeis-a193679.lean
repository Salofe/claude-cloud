import OMAStatements.S_oeis_a193679
import Mathlib

namespace OMA.Helpers

open Finset

theorem sum_totient_pow (q e : ℕ) (hq : q.Prime) :
    ∑ j ∈ range (e + 1), Nat.totient (q ^ j) = q ^ e := by
  rw [← Nat.sum_divisors_prime_pow hq]
  exact Nat.sum_totient _

theorem key (q f m : ℕ) (hq : q.Prime) (hcop : Nat.Coprime q m) :
    (q - 1) * ∑ j ∈ range (f + 1), Nat.totient (q ^ (f + 1) * m / q ^ (j + 1)) =
      Nat.totient (q ^ (f + 1) * m) := by
  have hterm : ∀ j ∈ range (f + 1), Nat.totient (q ^ (f + 1) * m / q ^ (j + 1)) =
      Nat.totient (q ^ (f - j)) * Nat.totient m := by
    intro j hj
    have hj' : j < f + 1 := mem_range.1 hj
    have h1 : q ^ (f + 1) = q ^ (f - j) * q ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    have h2 : q ^ (f + 1) * m / q ^ (j + 1) = q ^ (f - j) * m := by
      rw [h1, show q ^ (f - j) * q ^ (j + 1) * m = q ^ (f - j) * m * q ^ (j + 1) by ring]
      exact Nat.mul_div_cancel _ (pow_pos hq.pos _)
    rw [h2, Nat.totient_mul (Nat.Coprime.pow_left _ hcop)]
  rw [sum_congr rfl hterm, ← sum_mul]
  have hrefl := sum_range_reflect (fun j => Nat.totient (q ^ j)) (f + 1)
  simp only [show f + 1 - 1 = f by omega] at hrefl
  rw [hrefl, sum_totient_pow q f hq, Nat.totient_mul (Nat.Coprime.pow_left _ hcop),
    Nat.totient_prime_pow hq (by omega)]
  simp only [Nat.add_sub_cancel]
  ring

theorem prime_of_lt {n q j : ℕ} (hj : j < n.factorization q) : q.Prime := by
  have : q ∈ n.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.2 (by omega)
  exact Nat.prime_of_mem_primeFactors this

theorem fact_expM (n q d : ℕ) (hn : n ≠ 0) (hd : d ∣ n) :
    (OMA.S_oeis_a193679.expMangoldt d).factorization q =
      if d ∈ (range (n.factorization q)).image (fun j => q ^ (j + 1)) then 1 else 0 := by
  unfold OMA.S_oeis_a193679.expMangoldt
  by_cases h : IsPrimePow d
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
    rw [if_pos h, hp.pow_minFac hk.ne', hp.factorization, Finsupp.single_apply]
    have hkle : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).1 hd
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, if_pos]
      exact mem_image.2 ⟨k - 1, mem_range.2 (by omega), by congr 1; omega⟩
    · rw [if_neg hpq, if_neg]
      intro hm
      obtain ⟨j, hj, hjeq⟩ := mem_image.1 hm
      have hqp : q.Prime := prime_of_lt (mem_range.1 hj)
      have h1 : q ∣ p ^ k := hjeq ▸ dvd_pow_self q (Nat.succ_ne_zero j)
      have h2 := (Nat.prime_dvd_prime_iff_eq hqp hp).1 (hqp.dvd_of_dvd_pow h1)
      exact hpq h2.symm
  · rw [if_neg h, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, if_neg]
    intro hm
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hm
    have hqp : q.Prime := prime_of_lt (mem_range.1 hj)
    exact h ((isPrimePow_nat_iff _).2 ⟨q, j + 1, hqp, by omega, rfl⟩)

end OMA.Helpers

open Finset OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a193679.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hEne : ∀ d, OMA.S_oeis_a193679.expMangoldt d ≠ 0 := by
    intro d
    unfold OMA.S_oeis_a193679.expMangoldt
    split_ifs
    · exact (Nat.minFac_pos d).ne'
    · exact one_ne_zero
  unfold OMA.S_oeis_a193679.a
  apply Nat.eq_of_factorization_eq
  · exact prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  · exact prod_ne_zero_iff.2 fun d _ => pow_ne_zero _ (hEne d)
  intro q
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
    Nat.factorization_prod (fun d _ => pow_ne_zero _ (hEne d))]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul]
  have hL : ∑ p ∈ n.primeFactors, Nat.totient n / (p - 1) * p.factorization q =
      ∑ p ∈ n.primeFactors, if p = q then Nat.totient n / (p - 1) else 0 := by
    apply sum_congr rfl
    intro p hp
    rw [(Nat.prime_of_mem_primeFactors hp).factorization, Finsupp.single_apply]
    split_ifs <;> simp
  have hR : ∑ d ∈ n.divisors, Nat.totient (n / d) *
        (OMA.S_oeis_a193679.expMangoldt d).factorization q =
      ∑ d ∈ n.divisors, if d ∈ (range (n.factorization q)).image (fun j => q ^ (j + 1))
        then Nat.totient (n / d) else 0 := by
    apply sum_congr rfl
    intro d hd
    rw [fact_expM n q d hn0 (Nat.dvd_of_mem_divisors hd)]
    split_ifs <;> simp
  rw [hL, hR, sum_ite_eq', sum_ite_mem]
  by_cases hq : q ∈ n.primeFactors
  · rw [if_pos hq]
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq
    have hsub : (range (n.factorization q)).image (fun j => q ^ (j + 1)) ⊆ n.divisors := by
      intro d hd
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hd
      exact Nat.mem_divisors.2 ⟨(hqp.pow_dvd_iff_le_factorization hn0).2 (by
        have := mem_range.1 hj; omega), hn0⟩
    rw [inter_eq_right.2 hsub, sum_image (fun i _ j _ hij =>
      Nat.succ_injective (Nat.pow_right_injective hqp.two_le hij))]
    have he : 0 < n.factorization q := hqp.factorization_pos_of_dvd hn0 hqn
    obtain ⟨f, hf⟩ : ∃ f, n.factorization q = f + 1 := ⟨n.factorization q - 1, by omega⟩
    have hnm : q ^ (f + 1) * (n / q ^ n.factorization q) = n := by
      rw [← hf]; exact Nat.ordProj_mul_ordCompl_eq_self n q
    have hcop : Nat.Coprime q (n / q ^ n.factorization q) := Nat.coprime_ordCompl hqp hn0
    have hk := key q f _ hqp hcop
    rw [hnm] at hk
    rw [hf]
    apply Nat.div_eq_of_eq_mul_left (by have := hqp.two_le; omega)
    rw [← hk, mul_comm]
  · rw [if_neg hq]
    have : n.factorization q = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hq
    rw [this]
    simp
