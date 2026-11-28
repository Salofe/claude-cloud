import OMAStatements.S_oeis_a324017
import Mathlib

/-- The third conjunct fails: `j` is not required to be a least residue. With `m = 2`, `n = 1`
the tower is `1`, which is congruent to `9` modulo `8`, but `a 3 1 = 1`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a324017.main) := by
  intro h
  have h3 := h.2.2 2 1 9 (by norm_num) (by norm_num) (by decide)
  revert h3
  decide
