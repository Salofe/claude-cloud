import OMAStatements.S_oeis_a071713
import Mathlib

/-- The bound fails: `(1, 2, -2)` are distinct nonzero integers with `1 + 32 - 32 = 1`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071713.main) := by
  intro h
  have := h 1 2 (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this
