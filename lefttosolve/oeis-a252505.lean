import OMAStatements.S_oeis_a252505
import Mathlib

/-!
`m = a058035 n` has `v_p(m) = min (v_p(n)) 3` for every `p`. Hence for `n ≥ 1` a number `d`
divides `n` and has no prime with `p ^ 4 ∣ d` exactly when `v_p(d) ≤ min (v_p(n)) 3` for all
`p`, i.e. when `d ∣ m`; the two sets being counted coincide.
-/

namespace OMA.Helpers

open OMA.S_oeis_a252505

theorem a058035_ne_zero (n : ℕ) : a058035 n ≠ 0 := by
  unfold a058035
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem a058035_fact (n q : ℕ) : (a058035 n).factorization q = min (n.factorization q) 3 := by
  unfold a058035
  rw [Nat.factorization_prod
    (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
    Finsupp.finsetSum_apply]
  have h : ∀ p ∈ n.primeFactors, (p ^ min (n.factorization p) 3).factorization q =
      if p = q then min (n.factorization q) 3 else 0 := by
    intro p hp
    rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow, Finsupp.single_apply]
    split_ifs with e
    · rw [e]
    · rfl
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hq
  · rfl
  · have : n.factorization q = 0 := by
      by_contra hc
      exact hq (Nat.support_factorization n ▸ Finsupp.mem_support_iff.2 hc)
    rw [this]
    rfl

end OMA.Helpers

open OMA.Helpers OMA.S_oeis_a252505 in
theorem OMA.solution : type_of% @OMA.S_oeis_a252505.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hm0 := a058035_ne_zero n
  unfold a
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdn, -⟩, hd4⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hdn)
    refine ⟨?_, hm0⟩
    rw [← Nat.factorization_le_iff_dvd hd0 hm0, Finsupp.le_def]
    intro q
    rw [a058035_fact]
    refine le_min (Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hd0 hn0).2 hdn) q) ?_
    by_contra hq
    push Not at hq
    have hqd : q ∈ d.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.2 (by omega)
    exact hd4 q hqd ((Nat.Prime.pow_dvd_iff_le_factorization
      (Nat.prime_of_mem_primeFactors hqd) hd0).2 (by omega))
  · rintro ⟨hdm, -⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hm0 (Nat.eq_zero_of_zero_dvd hdm)
    have hmn : a058035 n ∣ n := by
      rw [← Nat.factorization_le_iff_dvd hm0 hn0, Finsupp.le_def]
      intro q
      rw [a058035_fact]
      exact min_le_left _ _
    refine ⟨⟨hdm.trans hmn, hn0⟩, ?_⟩
    intro p hp h4
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (Nat.prime_of_mem_primeFactors hp) hd0).1 h4
    have h2 := Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hd0 hm0).2 hdm) p
    rw [a058035_fact] at h2
    have := min_le_right (n.factorization p) 3
    omega
