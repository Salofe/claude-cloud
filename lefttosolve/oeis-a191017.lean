import OMAStatements.S_oeis_a191017
import Mathlib

/-!
`kron14 a` only depends on `a` modulo `56`: the factor `χ₈` depends on `a` modulo `8` and the
Jacobi symbol `(a|7)` on `a` modulo `7`. So the claim reduces to a table of the `56` residues,
which holds for every natural number (primality is not needed).
-/

namespace OMA.Helpers

open OMA.S_oeis_a191017

theorem kron14_mod (p : ℕ) : kron14 p = kron14 ((p % 56 : ℕ) : ℤ) := by
  unfold kron14
  congr 1
  · congr 1
    have h8 : (8 : ℕ) ∣ 56 := by norm_num
    rw [Int.cast_natCast, Int.cast_natCast]
    rw [← ZMod.natCast_mod p 8, ← ZMod.natCast_mod (p % 56) 8, Nat.mod_mod_of_dvd p h8]
  · apply jacobiSym.mod_left'
    push_cast
    omega

theorem kron14_table : ∀ r : ℕ, r < 56 → (kron14 (r : ℤ) = 1 ↔ r ∈ S) := by
  intro r hr
  interval_cases r <;> simp only [kron14, S, ZMod.χ₈_int_eq_if_mod_eight] <;> norm_num

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a191017.main := by
  intro p _
  rw [OMA.Helpers.kron14_mod]
  exact OMA.Helpers.kron14_table _ (Nat.mod_lt _ (by norm_num))
