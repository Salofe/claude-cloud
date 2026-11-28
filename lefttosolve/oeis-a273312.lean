import OMAStatements.S_oeis_a273312
import Mathlib

namespace OMA.Helpers

/-- Direct evaluation of the automaton: the counts at stages 1 to 5 are 4, 17, 40, 73, 112, so
a 1 = 13, a 2 = 23, a 3 = 33 and a 4 = 39, while the recurrence would need a 4 = 43. -/
theorem a273312_defect : OMA.S_oeis_a273312.a 4 - OMA.S_oeis_a273312.a 3 -
    OMA.S_oeis_a273312.a 2 + OMA.S_oeis_a273312.a 1 = -4 := by
  decide +kernel

end OMA.Helpers

/-- The fourth clause fails at n = 4, where it reaches back to a 1, before the periodic regime. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a273312.main) := by
  intro h
  have h4 := h.2.2.2.1 4 (by norm_num)
  have hv := OMA.Helpers.a273312_defect
  norm_num at h4
  omega
