import OMAReductions.R_Erdos52_erdos_52_R2

/-!
# Step H1 of the reduction Erdos52.erdos_52.R2

H1 is the uniform divisor bound d(n) ≤ C n^η. The reduction file already proves it as
`divisor_bound` from Mathlib alone (multiplicativity of the divisor count through
`Nat.card_divisors`, and the per-prime estimate a + 1 ≤ cost(p) (p^a)^η with cost(p) = 1
for the primes p with p^η ≥ 2). No upstream theorem is used.
-/

theorem OMA.solution : OMA.R_Erdos52_erdos_52_R2.H1 :=
  OMA.R_Erdos52_erdos_52_R2.divisor_bound
