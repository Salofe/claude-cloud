import OMAReductions.R_OeisA238585_conjecture_2_R1

/-!
# Step H1 of the reduction OeisA238585.conjecture_2.R1

At each of the twelve indices 4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44 the count a n equals one.

The primes Nat.nth Nat.Prime k for k at most 43 are located by counting the primes below each of
them (a kernel computation), and each a n is then expanded into its finitely many summands, whose
primality conditions are settled by norm_num.
Only the upstream definition OeisA238585.a is used.
-/

namespace OMA.Helpers

/-- A prime n is the k-th prime (from 0) when exactly k primes lie below it. -/
theorem nth_prime_of_count {n k : ℕ} (hn : n.Prime) (hk : Nat.count Nat.Prime n = k) :
    Nat.nth Nat.Prime k = n := by
  rw [← hk]
  exact Nat.nth_count hn

theorem nthPrime_0 : Nat.nth Nat.Prime 0 = 2 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_1 : Nat.nth Nat.Prime 1 = 3 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_2 : Nat.nth Nat.Prime 2 = 5 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_3 : Nat.nth Nat.Prime 3 = 7 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_4 : Nat.nth Nat.Prime 4 = 11 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_5 : Nat.nth Nat.Prime 5 = 13 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_6 : Nat.nth Nat.Prime 6 = 17 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_7 : Nat.nth Nat.Prime 7 = 19 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_8 : Nat.nth Nat.Prime 8 = 23 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_9 : Nat.nth Nat.Prime 9 = 29 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_10 : Nat.nth Nat.Prime 10 = 31 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_11 : Nat.nth Nat.Prime 11 = 37 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_12 : Nat.nth Nat.Prime 12 = 41 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_13 : Nat.nth Nat.Prime 13 = 43 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_14 : Nat.nth Nat.Prime 14 = 47 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_15 : Nat.nth Nat.Prime 15 = 53 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_16 : Nat.nth Nat.Prime 16 = 59 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_17 : Nat.nth Nat.Prime 17 = 61 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_18 : Nat.nth Nat.Prime 18 = 67 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_19 : Nat.nth Nat.Prime 19 = 71 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_20 : Nat.nth Nat.Prime 20 = 73 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_21 : Nat.nth Nat.Prime 21 = 79 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_22 : Nat.nth Nat.Prime 22 = 83 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_23 : Nat.nth Nat.Prime 23 = 89 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_24 : Nat.nth Nat.Prime 24 = 97 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_25 : Nat.nth Nat.Prime 25 = 101 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_26 : Nat.nth Nat.Prime 26 = 103 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_27 : Nat.nth Nat.Prime 27 = 107 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_28 : Nat.nth Nat.Prime 28 = 109 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_29 : Nat.nth Nat.Prime 29 = 113 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_30 : Nat.nth Nat.Prime 30 = 127 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_31 : Nat.nth Nat.Prime 31 = 131 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_32 : Nat.nth Nat.Prime 32 = 137 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_33 : Nat.nth Nat.Prime 33 = 139 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_34 : Nat.nth Nat.Prime 34 = 149 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_35 : Nat.nth Nat.Prime 35 = 151 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_36 : Nat.nth Nat.Prime 36 = 157 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_37 : Nat.nth Nat.Prime 37 = 163 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_38 : Nat.nth Nat.Prime 38 = 167 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_39 : Nat.nth Nat.Prime 39 = 173 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_40 : Nat.nth Nat.Prime 40 = 179 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_41 : Nat.nth Nat.Prime 41 = 181 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_42 : Nat.nth Nat.Prime 42 = 191 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

theorem nthPrime_43 : Nat.nth Nat.Prime 43 = 193 :=
  nth_prime_of_count (by norm_num) (by decide +kernel)

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA238585_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [OeisA238585.a, Finset.sum_Ico_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [OMA.Helpers.nthPrime_0, OMA.Helpers.nthPrime_1, OMA.Helpers.nthPrime_2,
      OMA.Helpers.nthPrime_3, OMA.Helpers.nthPrime_4, OMA.Helpers.nthPrime_5,
      OMA.Helpers.nthPrime_6, OMA.Helpers.nthPrime_7, OMA.Helpers.nthPrime_8,
      OMA.Helpers.nthPrime_9, OMA.Helpers.nthPrime_10, OMA.Helpers.nthPrime_11,
      OMA.Helpers.nthPrime_12, OMA.Helpers.nthPrime_13, OMA.Helpers.nthPrime_14,
      OMA.Helpers.nthPrime_15, OMA.Helpers.nthPrime_16, OMA.Helpers.nthPrime_17,
      OMA.Helpers.nthPrime_18, OMA.Helpers.nthPrime_19, OMA.Helpers.nthPrime_20,
      OMA.Helpers.nthPrime_21, OMA.Helpers.nthPrime_22, OMA.Helpers.nthPrime_23,
      OMA.Helpers.nthPrime_24, OMA.Helpers.nthPrime_25, OMA.Helpers.nthPrime_26,
      OMA.Helpers.nthPrime_27, OMA.Helpers.nthPrime_28, OMA.Helpers.nthPrime_29,
      OMA.Helpers.nthPrime_30, OMA.Helpers.nthPrime_31, OMA.Helpers.nthPrime_32,
      OMA.Helpers.nthPrime_33, OMA.Helpers.nthPrime_34, OMA.Helpers.nthPrime_35,
      OMA.Helpers.nthPrime_36, OMA.Helpers.nthPrime_37, OMA.Helpers.nthPrime_38,
      OMA.Helpers.nthPrime_39, OMA.Helpers.nthPrime_40, OMA.Helpers.nthPrime_41,
      OMA.Helpers.nthPrime_42, OMA.Helpers.nthPrime_43]
