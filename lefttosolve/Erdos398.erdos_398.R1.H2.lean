import OMAReductions.R_Erdos398_erdos_398_R1
import Mathlib.Data.Nat.Sqrt

/-!
# Step H2 of the reduction Erdos398.erdos_398.R1

For n below 128, n! + 1 is a perfect square exactly when n is 4, 5 or 7.

A natural number k is a square iff `Nat.sqrt k * Nat.sqrt k = k` (Mathlib lemma
`Nat.exists_mul_self`). For each n below 128 other than 4, 5 and 7 the kernel evaluates
`Nat.sqrt (n! + 1)` and checks that its square differs from n! + 1. Conversely
4! + 1 = 5 ^ 2, 5! + 1 = 11 ^ 2 and 7! + 1 = 71 ^ 2.
-/

namespace OMA.Helpers

/-- Finite check: for every n below 128, either n is 4, 5 or 7, or n! + 1 is not a square
(its integer square root does not square back to it). -/
theorem erdos398_small_table : ∀ n < 128, (n = 4 ∨ n = 5 ∨ n = 7) ∨
    Nat.sqrt (Nat.factorial n + 1) * Nat.sqrt (Nat.factorial n + 1) ≠ Nat.factorial n + 1 := by
  decide +kernel

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H2 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm⟩
    rcases OMA.Helpers.erdos398_small_table n hn with h | h
    · exact h
    · exact absurd ((Nat.exists_mul_self _).mp ⟨m, by rw [hm, sq]⟩) h
  · rintro (rfl | rfl | rfl)
    · exact ⟨5, by decide +kernel⟩
    · exact ⟨11, by decide +kernel⟩
    · exact ⟨71, by decide +kernel⟩
