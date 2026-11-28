import OMAReductions.R_OeisA24356_conjecture_R1

/-!
# Step H1 of reduction OeisA24356.conjecture.R1: `OeisA24356.a 4 = 0`

`OeisA24356.a 4` is the determinant of the `4 × 4` Hankel matrix `M i j = p (i + j)`, where
`p k = Nat.nth Nat.Prime k`. We locate `p 0, ..., p 6 = 2, 3, 5, 7, 11, 13, 17` by counting the
primes below each of them, check that `M` sends the nonzero vector `(6, -3, -2, 1)` to zero (row `i`
reads `6 p i - 3 p (i + 1) - 2 p (i + 2) + p (i + 3) = 0`), and conclude with the fact that a square
matrix over the integral domain `ℤ` with a nonzero kernel vector is singular.
-/

namespace OMA.Helpers

/-- A prime `n` is the `k`-th prime (counting from `0`) when exactly `k` primes lie below it. -/
theorem nth_prime_eq_of_count {n k : ℕ} (hn : n.Prime) (hk : Nat.count Nat.Prime n = k) :
    Nat.nth Nat.Prime k = n := by
  rw [← hk]
  exact Nat.nth_count hn

/-- The first seven primes `2, 3, 5, 7, 11, 13, 17`, each located by counting the primes below it. -/
theorem nth_prime_table :
    Nat.nth Nat.Prime 0 = 2 ∧ Nat.nth Nat.Prime 1 = 3 ∧ Nat.nth Nat.Prime 2 = 5 ∧
      Nat.nth Nat.Prime 3 = 7 ∧ Nat.nth Nat.Prime 4 = 11 ∧ Nat.nth Nat.Prime 5 = 13 ∧
      Nat.nth Nat.Prime 6 = 17 :=
  ⟨nth_prime_eq_of_count (by norm_num) (by decide), nth_prime_eq_of_count (by norm_num) (by decide),
    nth_prime_eq_of_count (by norm_num) (by decide), nth_prime_eq_of_count (by norm_num) (by decide),
    nth_prime_eq_of_count (by norm_num) (by decide), nth_prime_eq_of_count (by norm_num) (by decide),
    nth_prime_eq_of_count (by norm_num) (by decide)⟩

/-- The Hankel matrix of the primes sends `(6, -3, -2, 1)` to zero. -/
theorem hankel_kernel :
    Matrix.mulVec (Matrix.of fun (i j : Fin 4) ↦ (Nat.nth Nat.Prime (i.val + j.val) : ℤ))
      ![6, -3, -2, 1] = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := nth_prime_table
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0, h1, h2, h3, h4, h5, h6]

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := by
  unfold OMA.R_OeisA24356_conjecture_R1.H1 OeisA24356.a
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨![6, -3, -2, 1], fun hv ↦ ?_, OMA.Helpers.hankel_kernel⟩
  have h3 := congrFun hv 3
  simp at h3
