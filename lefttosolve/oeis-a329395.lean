import OMAStatements.S_oeis_a329395
import Mathlib

/-!
# A329395: the stated equivalence fails at n = 166

166 is 10100110 in binary, so the trimmed word is 0100110. Its Lyndon factorization is
01 · 0011 · 0 and the complemented word 1011001 factors as 1 · 011 · 001, so both counts are 3.
The composition read from the one bits is [2, 3, 1, 2], which is not a palindrome.
-/

namespace OMA.Helpers

open OMA.S_oeis_a329395

theorem a329395_digits : Nat.digits 2 166 = [0, 1, 1, 0, 0, 1, 0, 1] := by norm_num

end OMA.Helpers

open OMA.S_oeis_a329395 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a329395.main) := by
  intro h
  have key := (h 166 (by norm_num)).mp ⟨[[0, 1], [0, 0, 1, 1], [0]], [[1], [0, 1, 1], [0, 0, 1]],
    by rw [trimmed, OMA.Helpers.a329395_digits]; decide,
    by rw [trimmed, OMA.Helpers.a329395_digits]; decide, rfl⟩
  rw [composition, OMA.Helpers.a329395_digits] at key
  revert key
  decide
