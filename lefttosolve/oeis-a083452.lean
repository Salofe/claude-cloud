import OMAStatements.S_oeis_a083452
import Mathlib

namespace OMA.Helpers

/-- `rep d k = 1 + 10^d + ... + 10^(d(k-1))`. -/
def rep (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + 10 ^ d * rep d k

theorem ofDigits_rep (n k : ℕ) :
    Nat.ofDigits 10 (List.flatten (List.replicate k (Nat.digits 10 n))) =
      n * rep (Nat.digits 10 n).length k := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, ih, Nat.ofDigits_digits]
    simp only [rep]
    ring

theorem rep_ge (d n : ℕ) (hn : n ≤ 10 ^ d) (k : ℕ) : n ^ k ≤ rep d (k + 1) := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    show n ^ (k + 1) ≤ 1 + 10 ^ d * rep d (k + 1)
    rw [pow_succ]
    have : n ^ k * n ≤ rep d (k + 1) * 10 ^ d := Nat.mul_le_mul ih hn
    nlinarith

theorem rep_gt (d n : ℕ) (hn : n ≤ 10 ^ d) (k : ℕ) : n ^ (k + 1) < rep d (k + 2) := by
  show n ^ (k + 1) < 1 + 10 ^ d * rep d (k + 1)
  rw [pow_succ]
  have : n ^ k * n ≤ rep d (k + 1) * 10 ^ d := Nat.mul_le_mul (rep_ge d n hn k) hn
  nlinarith

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a083452.main := by
  intro n hn
  unfold OMA.S_oeis_a083452.a OMA.S_oeis_a083452.concatRep
  rw [ofDigits_rep]
  set d := (Nat.digits 10 n).length
  have hlt : n < 10 ^ d := Nat.lt_base_pow_length_digits (by norm_num)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hgt := rep_gt d (k + 2) hlt.le k
  have hpow : ((k + 2 : ℕ) : ℤ) ^ (k + 2) = ((k + 2 : ℕ) : ℤ) * ((k + 2 : ℕ) : ℤ) ^ (k + 1) := by
    ring
  rw [hpow]
  push_cast
  rw [← mul_sub, Int.mul_ediv_cancel_left _ (by positivity)]
  have : ((k + 2 : ℕ) : ℤ) ^ (k + 1) < (rep d (k + 2) : ℤ) := by exact_mod_cast hgt
  push_cast at this
  linarith
