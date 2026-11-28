import OMAReductions.R_OeisA234246_conjecture_2_R1

/-!
# Step H1 of reduction OeisA234246.conjecture_2.R1

At each of the nine indices 4, 5, 8, 9, 12, 13, 24, 33, 49 the count `a n` (the number of
`0 < k < n` with `k * φ(n - k) + 1` a perfect square) is exactly one.

This is a finite computation: totients and perfect-square tests over the `k < n` for nine
values of `n`, carried out by the kernel directly on the upstream definition of `a`.
-/

theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  unfold OMA.R_OeisA234246_conjecture_2_R1.H1
  decide +kernel
