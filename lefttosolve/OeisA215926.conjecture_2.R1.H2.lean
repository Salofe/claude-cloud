import OMAReductions.R_OeisA215926_conjecture_2_R1

/-!
# Step H2 of the reduction OeisA215926.conjecture_2.R1

For an odd prime q with q < 2 * 2 ^ j, the number 2 ^ j * q is perfect or abundant.
The divisor sum is multiplicative on the coprime factors 2 ^ j and q, giving
(2 ^ (j+1) - 1) * (q + 1), and this is at least 2 * 2 ^ j * q exactly when q + 1 is at
most 2 ^ (j+1).
-/

namespace OMA.Helpers

theorem geom_two_add_one (j : ℕ) : (∑ i ∈ Finset.range (j + 1), 2 ^ i) + 1 = 2 * 2 ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [pow_succ]
    omega

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hq2 hlt
  have hpos : 0 < 2 ^ j * q := Nat.mul_pos (by positivity) hq.pos
  have hcop : Nat.Coprime (2 ^ j) q :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega))
  have key : 2 * (2 ^ j * q) ≤ ∑ d ∈ (2 ^ j * q).divisors, d := by
    rw [Nat.Coprime.sum_divisors_mul hcop, Nat.sum_divisors_prime_pow Nat.prime_two,
      Nat.Prime.sum_divisors hq]
    have hs := OMA.Helpers.geom_two_add_one j
    set s := ∑ i ∈ Finset.range (j + 1), 2 ^ i with hsdef
    set X := 2 ^ j with hX
    have h1 : s * q + q = 2 * X * q := by rw [← hs]; ring
    have h2 : s * (q + 1) = s * q + s := by ring
    have h3 : 2 * (X * q) = 2 * X * q := by ring
    rw [h2, h3]
    omega
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors]
  omega
