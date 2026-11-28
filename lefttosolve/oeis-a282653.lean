import OMAStatements.S_oeis_a282653
import Mathlib

/-!
Disproof. The recurrence clause is stated for every n > 5, but the generating function in the
same statement has numerator terms in x^7 and x^11, so the order-6 recurrence only takes over
for n > 11. Already at n = 7 it fails: evaluating the automaton gives a 7 = 100010 while
a 5 = a 3 = a 1 = 10, so 100 * a 5 + a 3 - 100 * a 1 = 10.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282653.main) := by
  intro h
  have key : OMA.S_oeis_a282653.a 7 ≠
      100 * OMA.S_oeis_a282653.a 5 + OMA.S_oeis_a282653.a 3 - 100 * OMA.S_oeis_a282653.a 1 := by
    decide +kernel
  exact key (h.1 7 (by norm_num))
