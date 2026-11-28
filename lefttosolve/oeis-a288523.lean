import OMAStatements.S_oeis_a288523
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a288523

/-- Encoding of a token `1 0^j` (with `j` in `1..3`). -/
def tk (j : ℕ) : List Bool :=
  if j = 1 then [true, false] else if j = 2 then [true, false, false]
  else [true, false, false, false]

/-- Image of a token under one replacement pass. -/
def im (j : ℕ) : List Bool :=
  if j = 1 then [false, true, false] else if j = 2 then [false, true, false, false]
  else [false, true, false, false, true, false, true]

/-- Token substitution. -/
def sg (j : ℕ) : List ℕ := if j = 1 then [2] else if j = 2 then [3] else [2, 1, 1]

/-- Token list of `word (m + 1)`. -/
def Ls : ℕ → List ℕ
  | 0 => []
  | m + 1 => (if m % 2 = 0 then [] else [1, 1]) ++ (Ls m).flatMap sg

theorem rw_tk (j : ℕ) (w : List Bool) :
    OMA.S_oeis_a288523.rewrite (tk j ++ true :: w) = im j ++ OMA.S_oeis_a288523.rewrite (true :: w) := by
  unfold tk im
  split_ifs <;> simp [OMA.S_oeis_a288523.rewrite]

theorem head_true (L : List ℕ) (w : List Bool) : ∃ v, L.flatMap tk ++ true :: w = true :: v := by
  cases L with
  | nil => exact ⟨w, rfl⟩
  | cons j L =>
    have hu : ∃ u, tk j = true :: u := by
      unfold tk
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := hu
    exact ⟨u ++ L.flatMap tk ++ true :: w, by rw [List.flatMap_cons, hu]; simp⟩

theorem rw_flat (L : List ℕ) (w : List Bool) :
    OMA.S_oeis_a288523.rewrite (L.flatMap tk ++ true :: w) =
      L.flatMap im ++ OMA.S_oeis_a288523.rewrite (true :: w) := by
  induction L with
  | nil => simp
  | cons j L ih =>
    obtain ⟨v, hv⟩ := head_true L w
    rw [List.flatMap_cons, List.append_assoc, hv, rw_tk, ← hv, ih, List.flatMap_cons,
      List.append_assoc]

theorem shift (L : List ℕ) (X : List Bool) :
    L.flatMap im ++ false :: X = false :: ((L.flatMap sg).flatMap tk ++ X) := by
  induction L generalizing X with
  | nil => simp
  | cons j L ih =>
    rw [List.flatMap_cons, List.append_assoc, ih, List.flatMap_cons, List.flatMap_append,
      List.append_assoc]
    unfold im sg
    split_ifs <;> simp [tk]

theorem word_eq (m : ℕ) : word (m + 1) =
    List.replicate (if m % 2 = 0 then 1 else 2) false ++ (Ls m).flatMap tk ++ [true, false, true] := by
  induction m with
  | zero => simp [word, Ls, OMA.S_oeis_a288523.rewrite]
  | succ m ih =>
    have h101 : OMA.S_oeis_a288523.rewrite [true, false, true] = [false, true, false, true] := by
      simp [OMA.S_oeis_a288523.rewrite]
    obtain ⟨v, hv⟩ := head_true (Ls m) [false, true]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have h1 : (m + 1) % 2 = 1 := by omega
      rw [word, ih]
      simp only [h, h1, if_true, List.replicate_one, Ls, List.nil_append, List.singleton_append,
        List.append_assoc]
      simp only [one_ne_zero, if_false, List.replicate_succ, List.replicate_zero]
      rw [List.cons_append, hv]
      simp only [OMA.S_oeis_a288523.rewrite]
      rw [← hv, rw_flat, h101, shift]
      simp
    · have h1 : (m + 1) % 2 = 0 := by omega
      rw [word, ih]
      simp only [h, h1, if_true, one_ne_zero, if_false, Ls, List.replicate_succ,
        List.replicate_zero, List.append_assoc]
      simp only [List.cons_append, List.nil_append, OMA.S_oeis_a288523.rewrite]
      rw [rw_flat, h101, shift]
      simp [tk]

/-- Weighted sum over a token list. -/
def W (g : ℕ → ℤ) (L : List ℕ) : ℤ := (L.map g).sum

/-- Token counts of `Ls m`. -/
def cc : ℕ → ℤ × ℤ × ℤ
  | 0 => (0, 0, 0)
  | m + 1 => ((if m % 2 = 0 then 0 else 2) + 2 * (cc m).2.2, (cc m).1 + (cc m).2.2, (cc m).2.1)

theorem W_flat (g : ℕ → ℤ) (L : List ℕ) : W g (L.flatMap sg) = W (fun j => W g (sg j)) L := by
  induction L with
  | nil => simp [W]
  | cons j L ih =>
    simp only [W] at ih ⊢
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem W_Ls (m : ℕ) : ∀ g : ℕ → ℤ, W g (Ls m) = g 1 * (cc m).1 + g 2 * (cc m).2.1 + g 3 * (cc m).2.2 := by
  induction m with
  | zero => intro g; simp [W, Ls, cc]
  | succ m ih =>
    intro g
    have e : W g (Ls (m + 1)) = W g (if m % 2 = 0 then [] else [1, 1]) + W g ((Ls m).flatMap sg) := by
      simp only [Ls, W, List.map_append, List.sum_append]
    rw [e, W_flat, ih]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · simp [h, W, sg, cc]; ring
    · simp [h, W, sg, cc]; ring

/-- Length of `word (m + 1)`. -/
def ell (m : ℕ) : ℤ := (if m % 2 = 0 then 1 else 2) + 2 * (cc m).1 + 3 * (cc m).2.1 + 4 * (cc m).2.2 + 3

theorem len_word (m : ℕ) : ((word (m + 1)).length : ℤ) = ell m := by
  have : (((Ls m).map (fun j => (tk j).length)).sum : ℤ) = W (fun j => ((tk j).length : ℤ)) (Ls m) := by
    simp only [W]
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  rw [word_eq, List.length_append, List.length_append, List.length_replicate, List.length_flatMap,
    Nat.cast_add, Nat.cast_add, this, W_Ls]
  unfold ell
  split_ifs <;> simp [tk] <;> ring

theorem ell_rec (m : ℕ) : ell (m + 4) = ell (m + 3) + ell (m + 2) + ell (m + 1) - 2 * ell m := by
  simp only [ell, cc]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h1 : (m + 1) % 2 = 1 := by omega
    have h2 : (m + 2) % 2 = 0 := by omega
    have h3 : (m + 3) % 2 = 1 := by omega
    have h4 : (m + 4) % 2 = 0 := by omega
    simp only [h, h1, h2, h3, h4]
    simp
    ring
  · have h1 : (m + 1) % 2 = 0 := by omega
    have h2 : (m + 2) % 2 = 1 := by omega
    have h3 : (m + 3) % 2 = 0 := by omega
    have h4 : (m + 4) % 2 = 1 := by omega
    simp only [h, h1, h2, h3, h4]
    simp
    ring

theorem ell_ref (m : ℕ) : ell m = reference (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | k + 4, ih =>
      rw [ell_rec, ih k (by omega), ih (k + 1) (by omega), ih (k + 2) (by omega),
        ih (k + 3) (by omega)]
      rw [show k + 4 + 1 = k + 5 from rfl, reference]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a288523.main := by
  intro n
  cases n with
  | zero => rfl
  | succ m => rw [OMA.Helpers.len_word, OMA.Helpers.ell_ref]
