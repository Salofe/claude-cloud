import OMAStatements.S_oeis_a289131
import Mathlib

/-!
Proof of the length formula for the binary replacement word of A289131.

Call a word `u` splitting when `rewrite (u ++ v) = rewrite u ++ rewrite v` for every `v`.
Splitting words are closed under concatenation. Write `X m = (01)^m`, `Y m = (110)^m`,
`Z m = (011)^m`, `W m = (1010)^m`; then `rewrite (X m ++ v) = Z m ++ rewrite v` and
`rewrite (Y m ++ v) = W m ++ rewrite v`, so `X m`, `Y m` and `00` are splitting.

With `M 0 = 1`, `M (k + 1) = 2 M k + 1` (so `M k = 2^(k+1) - 1`), induction on `k` shows that
`word (2k+1)` is splitting and
* `word (2k+2) = word (2k+1) ++ X (M k) ++ 0`,
* `word (2k+3) = word (2k+1) ++ X (M k) ++ 00 ++ Y (M k)`.
The step uses the splitting of `word (2k+1)` and `word (2k+3)` together with the rotations
`Z m ++ 0 :: r = 0 :: (Y m ++ r)` and `X (2m+1) ++ 0 :: r = 010 ++ W m ++ r`.
Taking lengths, `|word (2k+1)| = 10 * 2^k - 6 - 3k` and `|word (2k+2)| = 14 * 2^k - 7 - 3k`,
and these closed forms satisfy the recurrence of `reference` with the right initial values.
-/

namespace OMA.Helpers

open OMA.S_oeis_a289131

/-- The parse of `u` is self-contained. -/
def Spl (u : List Bool) : Prop := ∀ v, rewrite (u ++ v) = rewrite u ++ rewrite v

theorem spl_append {u w : List Bool} (hu : Spl u) (hw : Spl w) : Spl (u ++ w) := by
  intro v
  rw [List.append_assoc, hu, hw, hu w, List.append_assoc]

/-- `(01)^m` -/
def X : ℕ → List Bool
  | 0 => []
  | m + 1 => false :: true :: X m

/-- `(110)^m` -/
def Y : ℕ → List Bool
  | 0 => []
  | m + 1 => true :: true :: false :: Y m

/-- `(011)^m` -/
def Z : ℕ → List Bool
  | 0 => []
  | m + 1 => false :: true :: true :: Z m

/-- `(1010)^m` -/
def W : ℕ → List Bool
  | 0 => []
  | m + 1 => true :: false :: true :: false :: W m

theorem rw_nil : rewrite [] = [] := by
  simp [rewrite]

theorem rwX (m : ℕ) (v : List Bool) : rewrite (X m ++ v) = Z m ++ rewrite v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [X, Z, List.cons_append]
    rw [rewrite, ih]
    rfl

theorem rwY (m : ℕ) (v : List Bool) : rewrite (Y m ++ v) = W m ++ rewrite v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Y, W, List.cons_append]
    rw [rewrite, rewrite, ih]
    rfl

theorem rwX' (m : ℕ) : rewrite (X m) = Z m := by
  simpa [rw_nil] using rwX m []

theorem rwY' (m : ℕ) : rewrite (Y m) = W m := by
  simpa [rw_nil] using rwY m []

theorem splX (m : ℕ) : Spl (X m) := by
  intro v
  rw [rwX, rwX']

theorem splY (m : ℕ) : Spl (Y m) := by
  intro v
  rw [rwY, rwY']

theorem rw00 (v : List Bool) : rewrite (false :: false :: v) =
    false :: false :: true :: false :: rewrite v := by
  rw [rewrite]
  rfl

theorem spl00 : Spl [false, false] := by
  intro v
  simp only [List.cons_append, List.nil_append]
  rw [rw00, rw00, rw_nil]
  rfl

theorem rw0 : rewrite [false] = [false] := by
  simp [rewrite]

theorem zf (m : ℕ) (r : List Bool) : Z m ++ false :: r = false :: (Y m ++ r) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Z, Y, List.cons_append, ih]

theorem xw0 (m : ℕ) (r : List Bool) : X (2 * m) ++ false :: r = false :: (W m ++ r) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    simp only [X, W, List.cons_append, ih]

theorem xw (m : ℕ) (r : List Bool) :
    X (2 * m + 1) ++ false :: r = false :: true :: false :: (W m ++ r) := by
  simp only [X, List.cons_append, xw0]

/-- `M k = 2^(k+1) - 1`. -/
def M : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * M k + 1

theorem word_succ (n : ℕ) : word (n + 1) = rewrite (word n) := by
  rw [word]

theorem word0 : word 0 = [false, false] := by
  rw [word]

theorem word1 : word 1 = [false, false, true, false] := by
  rw [word_succ, word0, rw00, rw_nil]

theorem word2 : word 2 = [false, false, true, false, false, true, false] := by
  rw [word_succ, word1, rw00]
  simp [rewrite]

theorem word3 : word 3 = [false, false, true, false, false, true, false, false, true, true,
    false] := by
  rw [word_succ, word2, rw00]
  simp [rewrite]

theorem spl1 : Spl (word 1) := by
  intro v
  rw [word1]
  simp only [List.cons_append, List.nil_append]
  rw [rw00, rw00]
  simp [rewrite]

theorem key (k : ℕ) : Spl (word (2 * k + 1)) ∧
    word (2 * k + 2) = word (2 * k + 1) ++ (X (M k) ++ [false]) ∧
    word (2 * k + 3) = word (2 * k + 1) ++ (X (M k) ++ (false :: false :: Y (M k))) := by
  induction k with
  | zero =>
    refine ⟨spl1, ?_, ?_⟩
    · rw [word2, word1]
      rfl
    · rw [word3, word1]
      rfl
  | succ k ih =>
    obtain ⟨hs, h2, h3⟩ := ih
    have e1 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    have e2 : 2 * (k + 1) + 2 = 2 * k + 3 + 1 := by ring
    have e3 : 2 * (k + 1) + 3 = 2 * k + 3 + 1 + 1 := by ring
    have hs3 : Spl (word (2 * k + 3)) := by
      rw [h3]
      refine spl_append hs (spl_append (splX _) ?_)
      have : false :: false :: Y (M k) = [false, false] ++ Y (M k) := rfl
      rw [this]
      exact spl_append spl00 (splY _)
    have h4 : word (2 * k + 3 + 1) = word (2 * k + 3) ++ (X (M (k + 1)) ++ [false]) := by
      rw [word_succ, h3, hs, ← word_succ, h2, rwX, rw00, rwY']
      simp only [M, xw, List.append_assoc, List.cons_append, List.nil_append, zf, List.append_nil]
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]
      exact hs3
    · rw [e1, e2]
      exact h4
    · rw [e1, e3, word_succ (2 * k + 3 + 1), h4, hs3, ← word_succ, h4, rwX, rw0]
      simp only [List.append_assoc, List.cons_append, List.nil_append, zf, List.append_nil]

theorem M_eq (k : ℕ) : (M k : ℤ) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [M]
    push_cast
    rw [ih]
    ring

theorem lenX (m : ℕ) : (X m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [X, List.length_cons, ih]
    ring

theorem lenY (m : ℕ) : (Y m).length = 3 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Y, List.length_cons, ih]
    ring

theorem lenOdd (k : ℕ) : ((word (2 * k + 1)).length : ℤ) = 10 * 2 ^ k - 6 - 3 * k := by
  induction k with
  | zero => rw [word1]; rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, (key k).2.2]
    simp only [List.length_append, List.length_cons, lenX, lenY]
    push_cast
    rw [ih, M_eq]
    ring

theorem lenEven (k : ℕ) : ((word (2 * k + 2)).length : ℤ) = 14 * 2 ^ k - 7 - 3 * k := by
  rw [(key k).2.1]
  simp only [List.length_append, List.length_cons, List.length_nil, lenX]
  push_cast
  rw [lenOdd, M_eq]
  ring

theorem len (n : ℕ) : ((word n).length : ℤ) = reference n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [word0]; rfl
    | 1, _ => rw [word1]; rfl
    | 2, _ => rw [word2]; rfl
    | 3, _ => rw [word3]; rfl
    | 4, _ =>
      rw [show (4 : ℕ) = 2 * 1 + 2 by rfl, lenEven]
      rfl
    | 5, _ =>
      rw [show (5 : ℕ) = 2 * 2 + 1 by rfl, lenOdd]
      rfl
    | m + 6, ih =>
      rw [reference, ← ih (m + 5) (by omega), ← ih (m + 4) (by omega), ← ih (m + 3) (by omega),
        ← ih (m + 2) (by omega), ← ih (m + 1) (by omega)]
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
      · rw [show 2 * k + 6 = 2 * (k + 2) + 2 by ring, show 2 * k + 5 = 2 * (k + 2) + 1 by ring,
          show 2 * k + 4 = 2 * (k + 1) + 2 by ring, show 2 * k + 3 = 2 * (k + 1) + 1 by ring,
          show 2 * k + 2 = 2 * k + 2 by ring, lenEven, lenOdd, lenEven, lenOdd, lenEven, lenOdd]
        push_cast
        ring
      · rw [show 2 * k + 1 + 6 = 2 * (k + 3) + 1 by ring,
          show 2 * k + 1 + 5 = 2 * (k + 2) + 2 by ring,
          show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by ring,
          show 2 * k + 1 + 3 = 2 * (k + 1) + 2 by ring,
          show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring,
          show 2 * k + 1 + 1 = 2 * k + 2 by ring, lenEven, lenOdd, lenEven, lenOdd, lenEven,
          lenOdd]
        push_cast
        ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a289131.main := OMA.Helpers.len
