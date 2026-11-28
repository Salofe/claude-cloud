import OMAStatements.S_oeis_a100691
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a100691

theorem neg_eq (n : ℕ) : ∀ p : Bool, tails n (-1) p = tails n 1 p := by
  induction n with
  | zero => intro p; rfl
  | succ n ih =>
    intro p
    cases p <;> simp [tails, ih]; ring

theorem tA (n : ℕ) : tails (n+1) 0 false = tails n 0 false + 2 * tails n 1 true := by
  simp [tails, neg_eq]; ring

theorem tB (n : ℕ) : tails (n+1) 1 false = tails n 0 false + tails n 1 false + tails n 1 true := by
  simp [tails, neg_eq]; ring

theorem tC (n : ℕ) : tails (n+1) 1 true = tails n 1 false := by
  simp [tails, neg_eq]

theorem rec3 (n : ℕ) : words (n+3) = 2 * words (n+2) + words n := by
  unfold words
  rw [tA (n+2), tA (n+1), tA n, tC (n+1), tC n, tB n]
  omega

theorem key : ∀ m : ℕ, walks (m+1) + 3 = words (m+3)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | m+4 => by
    have h1 : walks (m+4) + 3 = words (m+6) := key (m+3)
    have h2 : walks (m+2) + 3 = words (m+4) := key (m+1)
    have hw : walks (m+4+1) = 2 * walks (m+4) + walks (m+2) + 6 := rfl
    have hr : words (m+7) = 2 * words (m+6) + words (m+4) := rec3 (m+4)
    rw [hw, show m+4+3 = m+7 from rfl]
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a100691.main := OMA.Helpers.key
