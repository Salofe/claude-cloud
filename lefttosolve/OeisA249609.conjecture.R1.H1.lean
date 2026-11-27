import OMAReductions.R_OeisA249609_conjecture_R1

-- Step H1 of reduction OeisA249609.conjecture.R1: rows 0, 1, 2, 7, 8 of Pascal's triangle
-- contain no evil entry C(n, m) with 1 <= m <= n, so a n = 0 for each of these five indices.
-- Row 7 is 7, 21, 35, 35, 21, 7, 1 and row 8 is 8, 28, 56, 70, 56, 28, 8, 1; in binary these
-- have 3, 3, 3, 3, 3, 3, 1 and 1, 3, 3, 3, 3, 3, 1, 1 one bits, all odd. Rows 0, 1, 2 are
-- (empty), 1 and 2, 1. Each case is a direct kernel computation.

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
