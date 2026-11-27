import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1

/-!
# Step H1 of the reduction Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1

Let `D` be the product of the primes in `P` and `N` the sum of the cofactors `D / p`.
For each `p` in `P`, every cofactor except `D / p` is divisible by `p`, so the local
congruence gives `p ∣ N + 1`. The primes are distinct, so `D ∣ N + 1`.
Multiplying the reciprocal sum bound by `D` gives `N < D`, hence `D = N + 1`.
-/

namespace OMA.Helpers

open Finset

/-- The product of the primes divides one plus the sum of the cofactors. -/
theorem erdos313_prod_dvd (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hcong : ∀ p ∈ P, p ∣ (∏ q ∈ P.erase p, q) + 1) :
    (∏ p ∈ P, p) ∣ (∑ p ∈ P, ∏ q ∈ P.erase p, q) + 1 := by
  apply Finset.prod_primes_dvd _ (fun p hm => (hp p hm).prime)
  intro p hm
  rw [← Finset.add_sum_erase P _ hm, add_right_comm]
  apply dvd_add (hcong p hm)
  apply Finset.dvd_sum
  intro q hq
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hq).symm, hm⟩

/-- The reciprocal sum bound gives that the cofactor sum is below the product. -/
theorem erdos313_sum_lt (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hsum : (∑ p ∈ P, (1 : ℚ) / p) < 1) :
    (∑ p ∈ P, ∏ q ∈ P.erase p, q) < ∏ p ∈ P, p := by
  have hD : (0 : ℚ) < ((∏ p ∈ P, p : ℕ) : ℚ) := by
    exact_mod_cast Finset.prod_pos fun p hm => (hp p hm).pos
  have key : (∑ p ∈ P, (1 : ℚ) / p) * ((∏ p ∈ P, p : ℕ) : ℚ) =
      ((∑ p ∈ P, ∏ q ∈ P.erase p, q : ℕ) : ℚ) := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hm
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hp p hm).ne_zero
    rw [← Finset.mul_prod_erase P (fun q : ℕ => (q : ℚ)) hm]
    field_simp
  have hlt := mul_lt_mul_of_pos_right hsum hD
  rw [key, one_mul] at hlt
  exact_mod_cast hlt

end OMA.Helpers

theorem OMA.solution :
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1.H1 := by
  intro P _ hp hcong hsum
  have hdiv := OMA.Helpers.erdos313_prod_dvd P hp hcong
  have hlt := OMA.Helpers.erdos313_sum_lt P hp hsum
  have hle := Nat.le_of_dvd (Nat.succ_pos _) hdiv
  omega
