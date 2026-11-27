import OMAReductions.R_OeisA237720_conjecture_2_R1

/-!
# Step H1 of the reduction OeisA237720.conjecture_2.R1

At each of the thirteen listed indices the count is evaluated by kernel computation.
-/

theorem OMA.solution : OMA.R_OeisA237720_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl | ⟨h1, h2⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · interval_cases n <;> decide +kernel
