import OMAStatements.S_oeis_a087554
import Mathlib

/-!
Part (2) fails for n = 2, r = 3: the only S with 6 < S < 8 is S = 7, and 2 * 7 + 1 = 15 = 3 * 5.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087554.main) := by
  intro h
  obtain ⟨S, h1, h2, h3⟩ := h.2 2 3 (by norm_num) (by norm_num)
  have hS : S = 7 := by omega
  subst hS
  norm_num at h3
