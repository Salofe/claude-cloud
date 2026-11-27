import OMAReductions.R_OeisA237578_conjecture_2_R1

/-!
# Step H1 of reduction OeisA237578.conjecture_2.R1: a 5 = a 8 = a 13 = 1

Here `a n` counts the `k` with `0 < k < n` and `primeCounting (k * n)` prime.
By hand: for `n = 5` only `k = 1` works (`pi 5 = 3`); for `n = 8` only `k = 4` (`pi 32 = 11`);
for `n = 13` only `k = 10` (`pi 130 = 31`). Each value is a closed finite computation,
checked by the kernel.
-/

namespace OMA.Helpers

theorem a_five : OeisA237578.a 5 = 1 := by decide +kernel

theorem a_eight : OeisA237578.a 8 = 1 := by decide +kernel

theorem a_thirteen : OeisA237578.a 13 = 1 := by decide +kernel

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · exact OMA.Helpers.a_five
  · exact OMA.Helpers.a_eight
  · exact OMA.Helpers.a_thirteen
