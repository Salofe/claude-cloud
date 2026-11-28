import OMAStatements.S_oeis_a357958
import Mathlib

/-!
Disproof of the product version of the A357958 congruences: the second congruence fails for
p = 3 and r = 2, since 3^9 does not divide u(9) - u(3) (the 3-adic valuation is 8).
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a357958.main) := by
  intro h
  have h2 := h.2 3 2 Nat.prime_three le_rfl le_rfl
  revert h2
  decide +kernel
