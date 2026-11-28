import OMAReductions.R_Erdos457_erdos_457_variants_one_sub_R1

/-!
# Step H1 of the reduction Erdos457.erdos_457.variants.one_sub.R1

The block product of n+1, ..., n+k is the rising factorial of n+1 of length k,
which equals k! times the binomial coefficient (n+k choose k).
-/

namespace OMA.Helpers

/-- The block product over Icc 1 k is a rising factorial, by induction on k. -/
theorem block_prod_eq_rising (n k : ℕ) :
    (∏ i ∈ Finset.Icc 1 k, (n + i)) = (n + 1).ascFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]
    ring

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos457_erdos_457_variants_one_sub_R1.H1 := by
  intro n k
  rw [OMA.Helpers.block_prod_eq_rising, Nat.ascFactorial_eq_factorial_mul_choose]
