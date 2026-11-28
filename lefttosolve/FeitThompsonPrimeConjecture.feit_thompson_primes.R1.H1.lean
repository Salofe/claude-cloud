import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

/-!
# Step H1 of the reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1

If p < q are primes with q mod p = 1, then N = (q^p - 1)/(q - 1) is the geometric sum of q^i
for i < p, so N is congruent to p, hence to 0, modulo p. Meanwhile M = (p^q - 1)/(p - 1) is the
geometric sum of p^i for i < q, so M is congruent to 1 modulo p. A divisibility N | M would give
0 | 1 in ZMod p, which is impossible since p is prime.
-/

namespace OMA.Helpers

open Finset

/-- The geometric sum of `q` with `p` terms vanishes in `ZMod p` when `q % p = 1`. -/
theorem feit_first_sum_zero (p q : ℕ) (hq : q % p = 1) :
    (((∑ i ∈ range p, q ^ i : ℕ)) : ZMod p) = 0 := by
  have h1 : (q : ZMod p) = 1 := by
    rw [← ZMod.natCast_mod q p, hq, Nat.cast_one]
  push_cast
  simp [h1]

/-- The geometric sum of `p` with at least one term equals one in `ZMod p`. -/
theorem feit_second_sum_one (p q : ℕ) (hq : 0 < q) :
    (((∑ i ∈ range q, p ^ i : ℕ)) : ZMod p) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  push_cast
  rw [sum_range_succ']
  simp

end OMA.Helpers

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1 := by
  intro p q hp hq hpq hmod hdvd
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  rw [← Nat.geomSum_eq hq2 p, ← Nat.geomSum_eq hp2 q] at hdvd
  have hcast := Nat.cast_dvd_cast (α := ZMod p) hdvd
  rw [OMA.Helpers.feit_first_sum_zero p q hmod, OMA.Helpers.feit_second_sum_one p q (by omega)] at hcast
  have : Fact p.Prime := ⟨hp⟩
  exact one_ne_zero (zero_dvd_iff.mp hcast)
