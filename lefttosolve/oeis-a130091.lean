import OMAStatements.S_oeis_a130091
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a130091

theorem fact_eq_one {k p : ℕ} (hp : p.Prime) (hk : k ≠ 0) (h1 : p ∣ k) (h2 : ¬ p ^ 2 ∣ k) :
    k.factorization p = 1 := by
  have a : 1 ≤ k.factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization hk, pow_one]
    exact h1
  have b : ¬ 2 ≤ k.factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization hk]
    exact h2
  omega

theorem not_inSeq_of_mod {k : ℕ} (h : k % 36 = 6 ∨ k % 36 = 30) : ¬ InSeq k := by
  rintro ⟨hk, hinj⟩
  have hk0 : k ≠ 0 := by omega
  have h2 : k.factorization 2 = 1 :=
    fact_eq_one Nat.prime_two hk0 (by omega) (by norm_num; omega)
  have h3 : k.factorization 3 = 1 :=
    fact_eq_one Nat.prime_three hk0 (by omega) (by norm_num; omega)
  have m2 : (2 : ℕ) ∈ (k.primeFactors : Set ℕ) := by
    rw [Finset.mem_coe, Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, by omega, hk0⟩
  have m3 : (3 : ℕ) ∈ (k.primeFactors : Set ℕ) := by
    rw [Finset.mem_coe, Nat.mem_primeFactors]
    exact ⟨Nat.prime_three, by omega, hk0⟩
  have := hinj m2 m3 (by rw [h2, h3])
  omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a130091.main := by
  refine ⟨fun n hn => not_inSeq_of_mod (by omega), fun n => not_inSeq_of_mod (by omega), ?_⟩
  rintro ⟨m, hm⟩
  have key : ∃ i, i < 24 ∧ ((m + i) % 36 = 6 ∨ (m + i) % 36 = 30) := by
    by_cases h1 : m % 36 ≤ 6
    · exact ⟨6 - m % 36, by omega, by omega⟩
    · by_cases h2 : m % 36 ≤ 30
      · exact ⟨30 - m % 36, by omega, by omega⟩
      · exact ⟨42 - m % 36, by omega, by omega⟩
  obtain ⟨i, hi, hmod⟩ := key
  exact not_inSeq_of_mod hmod (hm i hi)
