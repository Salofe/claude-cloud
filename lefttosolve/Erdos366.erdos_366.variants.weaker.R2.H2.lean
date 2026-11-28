import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R2

/-!
# Step H2 of the reduction Erdos366.erdos_366.variants.weaker.R2

For all positive a, b, c the number a^3 b^4 c^5 is 3-full. A prime p dividing the product
divides one of a, b, c (p is prime), so p^3 divides a^3, or b^4 (as p^3 divides p^4), or c^5
(as p^3 divides p^5), and therefore divides the whole product.

Only the upstream definition `Nat.Full` is used (no upstream theorem), together with Mathlib.
-/

namespace OMA.Helpers

/-- If a prime `p` divides `a ^ 3 * b ^ 4 * c ^ 5`, then so does `p ^ 3`. -/
theorem erdos366_prime_cube_dvd {p a b c : ℕ} (hp : p.Prime)
    (h : p ∣ a ^ 3 * b ^ 4 * c ^ 5) : p ^ 3 ∣ a ^ 3 * b ^ 4 * c ^ 5 := by
  rcases hp.dvd_mul.mp h with hab | hc
  · rcases hp.dvd_mul.mp hab with ha | hb
    · -- `p ∣ a`, hence `p ^ 3 ∣ a ^ 3`
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow ha) 3) _) _
    · -- `p ∣ b`, hence `p ^ 3 ∣ b ^ 4`
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd_of_le (hp.dvd_of_dvd_pow hb) (by norm_num)) _) _
  · -- `p ∣ c`, hence `p ^ 3 ∣ c ^ 5`
    exact dvd_mul_of_dvd_right
      (pow_dvd_pow_of_dvd_of_le (hp.dvd_of_dvd_pow hc) (by norm_num)) _

/-- Every number of the form `a ^ 3 * b ^ 4 * c ^ 5` is `3`-full (no positivity needed). -/
theorem erdos366_full_three (a b c : ℕ) : Nat.Full 3 (a ^ 3 * b ^ 4 * c ^ 5) := by
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  exact erdos366_prime_cube_dvd hp'.1 hp'.2.1

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R2.H2 :=
  fun a b c _ _ _ => OMA.Helpers.erdos366_full_three a b c
