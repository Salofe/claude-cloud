import OMAReductions.R_Erdos458_erdos_458_R1

/-!
# Step H1 of the reduction Erdos458.erdos_458.R1

The logarithm of the least common multiple of 1, ..., n is the Chebyshev function psi at n,
which is the sum of the von Mangoldt function over the integers 1, ..., n. Subtracting the
two partial sums leaves the sum over the half-open interval from a to b.
-/

namespace OMA.Helpers

open Finset ArithmeticFunction

theorem erdos458_log_lcm_eq_sum (n : ℕ) :
    Real.log (Erdos458.lcm_upto n : ℝ) = ∑ k ∈ Ioc 0 n, vonMangoldt k := by
  have h1 : Erdos458.lcm_upto n = Nat.lcmUpto n := rfl
  rw [h1, ← Chebyshev.psi_eq_log_lcmUpto, Chebyshev.psi, Nat.floor_natCast]

end OMA.Helpers

open Finset ArithmeticFunction in
theorem OMA.solution : OMA.R_Erdos458_erdos_458_R1.H1 := by
  intro a b hab
  rw [OMA.Helpers.erdos458_log_lcm_eq_sum, OMA.Helpers.erdos458_log_lcm_eq_sum,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring
