import OMAStatements.S_mo_26856
import Mathlib

/-!
Every associated prime of a finite module lies in its support: an associated prime contains the
annihilator, and for a finite module the support is exactly the set of primes containing the
annihilator.
-/

theorem OMA.solution : type_of% @OMA.S_mo_26856.main := by
  intro R M _ _ _ _ _ _ _ p x _ _ _ q _ hq
  rw [Module.mem_support_iff_of_finite, ← Submodule.annihilator_top]
  exact IsAssociatedPrime.annihilator_le hq
