import OMAStatements.S_oeis_a085928
import Mathlib

/-!
Disproof of the finiteness conjecture of OEIS A085928 as formalized. If a(m+1) = 0 then
a(m+2) = |10 a(m) - rev(10 a(m))|, and rev(10 x) < 10 x for x > 0, so two consecutive terms
(from index 1 on) are never both 0. Hence infinitely many terms are nonzero.
-/

namespace OMA.Helpers

open OMA.S_oeis_a085928

theorem a085928_ofDigits_digits10 (x : ℕ) : Nat.ofDigits 10 (digits10 x) = x := by
  unfold digits10
  split_ifs with h
  · subst h; rfl
  · exact Nat.ofDigits_digits 10 x

/-- Concatenating 0 after x multiplies x by 10. -/
theorem a085928_concat_zero (x : ℕ) : concat10 x 0 = 10 * x := by
  unfold concat10
  have h0 : digits10 0 = [0] := by simp [digits10]
  rw [h0, List.singleton_append, Nat.ofDigits_cons, a085928_ofDigits_digits10]
  ring

/-- For x ≠ 0, the reversal of 10 x is smaller than 10 x (its last digit 0 moves to the front). -/
theorem a085928_rev_lt (x : ℕ) (hx : x ≠ 0) : rev10 (10 * x) < 10 * x := by
  unfold rev10
  have h10 : 10 * x ≠ 0 := by omega
  have hd : digits10 (10 * x) = 0 :: Nat.digits 10 x := by
    unfold digits10
    rw [if_neg h10]
    exact Nat.digits_base_mul (by norm_num) (Nat.pos_of_ne_zero hx)
  rw [hd, List.reverse_cons, Nat.ofDigits_append]
  have hz : Nat.ofDigits 10 [0] = 0 := rfl
  rw [hz, mul_zero, add_zero]
  have h1 : Nat.ofDigits 10 (Nat.digits 10 x).reverse < 10 ^ (Nat.digits 10 x).reverse.length :=
    Nat.ofDigits_lt_base_pow_length (by norm_num) (fun d hd =>
      Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd))
  have h2 : 10 ^ (Nat.digits 10 x).length ≤ 10 * x :=
    Nat.base_pow_length_digits_le 10 x (by norm_num) hx
  rw [List.length_reverse] at h1
  omega

/-- If the second argument is 0, the next term vanishes only when the first one does. -/
theorem a085928_step_zero (k : ℕ) (h1 : a (k + 2) = 0) (h2 : a (k + 3) = 0) : a (k + 1) = 0 := by
  by_contra hx
  have e : a (k + 3) = Int.natAbs ((concat10 (a (k + 1)) (a (k + 2)) : ℤ)
      - (rev10 (concat10 (a (k + 1)) (a (k + 2))) : ℤ)) := rfl
  rw [h1, a085928_concat_zero] at e
  have hlt := a085928_rev_lt (a (k + 1)) hx
  rw [h2] at e
  omega

/-- Two consecutive terms from index 1 on are never both 0. -/
theorem a085928_not_both (n : ℕ) : a (n + 1) ≠ 0 ∨ a (n + 2) ≠ 0 := by
  induction n with
  | zero => left; decide
  | succ k ih =>
    by_contra h
    simp only [ne_eq, not_or, not_not] at h
    obtain ⟨h1, h2⟩ := h
    have h0 := a085928_step_zero k h1 h2
    rcases ih with ih | ih
    · exact ih h0
    · exact ih h1

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a085928.main) := by
  intro h
  apply Set.infinite_of_forall_exists_gt (s := {n : ℕ | 1 ≤ n ∧ OMA.S_oeis_a085928.a n ≠ 0}) _ h
  intro m
  rcases OMA.Helpers.a085928_not_both m with hm | hm
  · exact ⟨m + 1, ⟨by omega, hm⟩, by omega⟩
  · exact ⟨m + 2, ⟨by omega, hm⟩, by omega⟩
