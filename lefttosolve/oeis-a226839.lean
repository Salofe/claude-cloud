import OMAStatements.S_oeis_a226839
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a226839

theorem three_dvd_div (m : ℕ) (hm : 2 ≤ m) : 3 ∣ (tri m).factorial / m.factorial := by
  have hle : m ≤ tri m := by
    unfold tri
    have : 2 * m ≤ m * (m + 1) := by nlinarith
    omega
  have hd : (tri m).factorial / m.factorial = (tri m).descFactorial (tri m - m) := by
    rw [Nat.descFactorial_eq_div (Nat.sub_le _ _), Nat.sub_sub_self hle]
  rw [hd]
  rcases Nat.lt_or_ge m 3 with h | h
  · have h2 : m = 2 := by omega
    subst h2
    decide
  · have h3 : 3 ≤ tri m - m := by
      unfold tri
      have : 2 * m + 6 ≤ m * (m + 1) := by nlinarith
      omega
    exact (Nat.dvd_factorial (by norm_num) h3).trans (Nat.factorial_dvd_descFactorial _ _)

theorem step (n : ℕ) : a (n + 1) ≡ a n [MOD 3] := by
  rw [a, Fin.sum_univ_succ]
  have h0 : (if tri ((0 : Fin (n + 1)).1 + 1) ≤ n + 1 then
      ((tri ((0 : Fin (n + 1)).1 + 1)).factorial / ((0 : Fin (n + 1)).1 + 1).factorial) *
        Nat.choose n (tri ((0 : Fin (n + 1)).1 + 1) - 1) * a (n + 1 - tri ((0 : Fin (n + 1)).1 + 1))
      else 0) = a n := by
    simp [tri]
  rw [h0]
  have hrest : 3 ∣ ∑ i : Fin n, (if tri ((Fin.succ i).1 + 1) ≤ n + 1 then
      ((tri ((Fin.succ i).1 + 1)).factorial / ((Fin.succ i).1 + 1).factorial) *
        Nat.choose n (tri ((Fin.succ i).1 + 1) - 1) * a (n + 1 - tri ((Fin.succ i).1 + 1))
      else 0) := by
    apply Finset.dvd_sum
    intro i _
    split_ifs
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (three_dvd_div _ (by simp)) _) _
    · exact dvd_zero 3
  obtain ⟨c, hc⟩ := hrest
  rw [hc]
  unfold Nat.ModEq
  omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a226839.main := by
  intro n
  induction n with
  | zero => rw [OMA.S_oeis_a226839.a.eq_1]
  | succ n ih => exact (OMA.Helpers.step n).trans ih
