import OMAStatements.S_oeis_a288668
import Mathlib

/-!
Proof of the length formula for the binary replacement word of A288668.

Call a word `u` splitting when `rewrite (u ++ v) = rewrite u ++ rewrite v` for every `v`, i.e.
the left-to-right parse of `u` never looks past its end. Splitting words are closed under
concatenation, and the words `word 0 = 00`, `word 1 = 0110`, `word 2 = 01000` are splitting
(direct computation). By strong induction one gets simultaneously that every `word n` is
splitting and that `word (n + 3) = word n ++ word n ++ word (n + 1)`: applying `rewrite` to the
decomposition of `word (n + 3)` and splitting it gives the decomposition of `word (n + 4)`.
Taking lengths, `|word (n + 3)| = 2 |word n| + |word (n + 1)|`, which is the recurrence of
`reference`, and the initial values `2, 4, 5` agree.
-/

namespace OMA.Helpers

open OMA.S_oeis_a288668

/-- The parse of `u` is self-contained. -/
def Spl (u : List Bool) : Prop := ∀ v, rewrite (u ++ v) = rewrite u ++ rewrite v

theorem spl_append {u w : List Bool} (hu : Spl u) (hw : Spl w) : Spl (u ++ w) := by
  intro v
  rw [List.append_assoc, hu, hw, hu w, List.append_assoc]

theorem word_succ (n : ℕ) : word (n + 1) = rewrite (word n) := by
  rw [word]

theorem word0 : word 0 = [false, false] := by
  rw [word]

theorem word1 : word 1 = [false, true, true, false] := by
  rw [word_succ, word0]
  simp [rewrite]

theorem word2 : word 2 = [false, true, false, false, false] := by
  rw [word_succ, word1]
  simp [rewrite]

theorem word3 : word 3 = [false, false, false, false, false, true, true, false] := by
  rw [word_succ, word2]
  simp [rewrite]

theorem spl0 : Spl (word 0) := by
  intro v
  rw [word0]
  simp [rewrite]

theorem spl1 : Spl (word 1) := by
  intro v
  rw [word1]
  simp [rewrite]

theorem spl2 : Spl (word 2) := by
  intro v
  rw [word2]
  simp [rewrite]

theorem key (n : ℕ) : Spl (word n) ∧ word (n + 3) = word n ++ word n ++ word (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    refine ⟨?_, ?_⟩
    · match n, ih with
      | 0, _ => exact spl0
      | 1, _ => exact spl1
      | 2, _ => exact spl2
      | m + 3, ih =>
        rw [(ih m (by omega)).2]
        exact spl_append (spl_append (ih m (by omega)).1 (ih m (by omega)).1)
          (ih (m + 1) (by omega)).1
    · match n, ih with
      | 0, _ => rw [word3, word0, word1]; rfl
      | m + 1, ih =>
        have h := (ih m (by omega)).2
        have hs := (ih m (by omega)).1
        rw [word_succ (m + 1 + 2), show m + 1 + 2 = m + 3 by omega, h, List.append_assoc, hs,
          hs, ← word_succ, ← word_succ, List.append_assoc]

theorem len (n : ℕ) : (word n).length = reference n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [word0]; rfl
    | 1, _ => rw [word1]; rfl
    | 2, _ => rw [word2]; rfl
    | m + 3, ih =>
      rw [(key m).2, List.length_append, List.length_append, ih m (by omega),
        ih (m + 1) (by omega), reference]
      ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a288668.main := OMA.Helpers.len
