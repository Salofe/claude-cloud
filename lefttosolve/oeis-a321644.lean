import OMAStatements.S_oeis_a321644
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a321644

theorem twinLow_odd_a321644 {p : ℕ} (hp : p ∈ lowerTwins) : Odd p := by
  rcases hp.1.eq_two_or_odd' with h | h
  · exfalso; have := hp.2; rw [h] at this; norm_num at this
  · exact h

theorem terms_finite_a321644 (h : lowerTwins.Finite) : terms.Finite := by
  have ht : twinPrimes.Finite := h.union (h.image _)
  refine (Set.finite_Iic (∏ q ∈ ht.toFinset, q)).subset ?_
  intro n hn
  obtain ⟨hsqf, -, hn1, -, hq⟩ := hn
  have hpfsub : n.primeFactors ⊆ ht.toFinset := by
    intro q hq'
    rw [Set.Finite.mem_toFinset]
    exact hq q (Nat.prime_of_mem_primeFactors hq') (Nat.dvd_of_mem_primeFactors hq')
  have hdvd : n ∣ ∏ q ∈ ht.toFinset, q := by
    rw [← Nat.prod_primeFactors_of_squarefree hsqf]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hpfsub
  have hpos : 0 < ∏ q ∈ ht.toFinset, q := by
    apply Finset.prod_pos
    intro q hq'
    rw [Set.Finite.mem_toFinset] at hq'
    rcases hq' with hq' | ⟨r, hr, hr'⟩
    · exact hq'.1.pos
    · rw [← hr']; exact Nat.succ_pos _
  exact Nat.le_of_dvd hpos hdvd

theorem terms_infinite_a321644 (h : lowerTwins.Infinite) : terms.Infinite := by
  have hinj : Set.InjOn (fun p : ℕ => p * (p + 2)) lowerTwins := by
    intro a _ b _ hab
    simp only at hab
    by_contra hab_ne
    rcases Nat.lt_or_gt_of_ne hab_ne with hcmp | hcmp
    · have : a * (a + 2) < b * (b + 2) := Nat.mul_lt_mul'' hcmp (by omega)
      omega
    · have : b * (b + 2) < a * (a + 2) := Nat.mul_lt_mul'' hcmp (by omega)
      omega
  refine Set.Infinite.mono ?_ (h.image hinj)
  rintro _ ⟨p, hp, rfl⟩
  have hp1 := hp.1
  have hp2 := hp.2
  have hodd := twinLow_odd_a321644 hp
  have hp3 : 3 ≤ p := by
    rcases hodd with ⟨k, hk⟩
    have := hp1.two_le
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.squarefree_mul_iff]
    refine ⟨?_, hp1.squarefree, hp2.squarefree⟩
    rw [Nat.coprime_primes hp1 hp2]
    omega
  · exact hodd.mul (hodd.add_even even_two)
  · nlinarith
  · exact Nat.not_prime_mul (by omega) (by omega)
  · intro q hq hqd
    rcases (Nat.Prime.dvd_mul hq).1 hqd with hd | hd
    · left
      rw [(Nat.prime_dvd_prime_iff_eq hq hp1).1 hd]
      exact hp
    · right
      exact ⟨p, hp, ((Nat.prime_dvd_prime_iff_eq hq hp2).1 hd).symm⟩

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a321644.main := by
  constructor
  · intro h
    by_contra h'
    exact h (OMA.Helpers.terms_finite_a321644 (Set.not_infinite.mp h'))
  · exact OMA.Helpers.terms_infinite_a321644
