import OMAReductions.R_OeisA232194_conjecture_2_R1

/-!
# Step H1 of the reduction OeisA232194.conjecture_2.R1

`OeisA232194.a n` counts the `x` with `1 ≤ x < n` such that, for `y = n - x`, both
`n * x + y` and `n * y - x` are prime.  The step asks for `a n = 1` at the five indices
`3, 4, 6, 20, 24`.  At each of them exactly one `x` qualifies:

* `n = 3`:  `x = 1`,  giving the primes `5` and `5`;
* `n = 4`:  `x = 1`,  giving `7` and `11`;
* `n = 6`:  `x = 1`,  giving `11` and `29`;
* `n = 20`: `x = 9`,  giving `191` and `211`;
* `n = 24`: `x = 19`, giving `461` and `101`.

Every number tested is below `600`.  The definition of `a` decides primality with the
instance `Nat.decidablePrime` (trial division by each `2 ≤ m < p`), which unfolds by
structural recursion only, so the kernel evaluates each of the five sums directly with
`decide +kernel`.  The main theorem splits the membership hypothesis into the five cases.
-/

namespace OMA.Helpers

/-- At `n = 3` only `x = 1` qualifies (`5` and `5`). -/
theorem a232194_three : OeisA232194.a 3 = 1 := by decide +kernel

/-- At `n = 4` only `x = 1` qualifies (`7` and `11`). -/
theorem a232194_four : OeisA232194.a 4 = 1 := by decide +kernel

/-- At `n = 6` only `x = 1` qualifies (`11` and `29`). -/
theorem a232194_six : OeisA232194.a 6 = 1 := by decide +kernel

/-- At `n = 20` only `x = 9` qualifies (`191` and `211`). -/
theorem a232194_twenty : OeisA232194.a 20 = 1 := by decide +kernel

/-- At `n = 24` only `x = 19` qualifies (`461` and `101`). -/
theorem a232194_twentyfour : OeisA232194.a 24 = 1 := by decide +kernel

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  fin_cases hn
  exacts [OMA.Helpers.a232194_three, OMA.Helpers.a232194_four, OMA.Helpers.a232194_six,
    OMA.Helpers.a232194_twenty, OMA.Helpers.a232194_twentyfour]
