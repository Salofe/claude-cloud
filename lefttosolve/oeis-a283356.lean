import OMAStatements.S_oeis_a283356
import Mathlib

/-!
Disproof. The last clause asks for a n = 10 a (n - 1) + a (n - 2) - 10 a (n - 3) for every
n > 5, but the generating function in the same statement has a numerator term in x^7, so this
recurrence fails at n = 7: evaluating the automaton gives a 4 = 10001, a 5 = 11101,
a 6 = 110001 and a 7 = 1111101, while 10 * 110001 + 11101 - 10 * 10001 = 1011101.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283356.main) := by
  intro h
  have key : OMA.S_oeis_a283356.a 7 ≠
      10 * OMA.S_oeis_a283356.a 6 + OMA.S_oeis_a283356.a 5 - 10 * OMA.S_oeis_a283356.a 4 := by
    decide +kernel
  exact key (h.2.2.2 7 (by norm_num))
