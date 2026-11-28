import OMAStatements.S_oeis_a034863
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a034863.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega]
  simp only [OMA.S_oeis_a034863.a, Nat.factorial_succ]
  push_cast
  ring
