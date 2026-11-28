import OMAStatements.S_oeis_a061100
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a061100

theorem dsum_lt (m : ℕ) (h : 10 ≤ m) : (Nat.digits 10 m).sum < m := by
  rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
  have := Nat.digit_sum_le 10 (m / 10)
  omega

theorem dsum_pos (m : ℕ) (h : m ≠ 0) : 0 < (Nat.digits 10 m).sum := by
  have h1 := Nat.getLast_digit_ne_zero 10 h
  have h2 := List.le_sum_of_mem (List.getLast_mem ((Nat.digits_ne_nil_iff_ne_zero (b := 10)).mpr h))
  omega

theorem dr_spec (m : ℕ) :
    digitalRoot m % 9 = m % 9 ∧ digitalRoot m < 10 ∧ (m ≠ 0 → digitalRoot m ≠ 0) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [digitalRoot]
    split_ifs with h
    · exact ⟨rfl, h, id⟩
    · have hs := dsum_lt m (by omega)
      obtain ⟨h1, h2, h3⟩ := ih _ hs
      have hmod := Nat.modEq_nine_digits_sum m
      unfold Nat.ModEq at hmod
      have hp := dsum_pos m (by omega)
      exact ⟨by omega, h2, fun _ => h3 (by omega)⟩

theorem dr_eq (m : ℕ) : digitalRoot m = 4 ↔ m % 9 = 4 := by
  obtain ⟨h1, h2, h3⟩ := dr_spec m
  constructor
  · intro h
    omega
  · intro h
    have := h3 (by omega)
    omega

theorem sq_mod (r : ℕ) : r * r % 9 = 4 ↔ r % 9 = 2 ∨ r % 9 = 7 := by
  rw [Nat.mul_mod]
  have h := Nat.mod_lt r (show 9 > 0 by norm_num)
  generalize r % 9 = t at h ⊢
  interval_cases t <;> simp

/-- The square roots of the terms, in increasing order. -/
def x (k : ℕ) : ℕ := 9 * (k / 2) + 2 + 5 * (k % 2)

def f (k : ℕ) : ℕ := x k * x k

theorem x_mono : StrictMono x := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold x
  omega

theorem f_mono : StrictMono f := fun i j h => by
  have := x_mono h
  unfold f
  exact Nat.mul_self_lt_mul_self this

theorem P_iff (m : ℕ) : P m ↔ ∃ k, f k = m := by
  unfold P
  constructor
  · rintro ⟨⟨r, rfl⟩, h⟩
    rw [dr_eq, sq_mod] at h
    refine ⟨2 * (r / 9) + (if r % 9 = 2 then 0 else 1), ?_⟩
    unfold f x
    have : 9 * ((2 * (r / 9) + if r % 9 = 2 then 0 else 1) / 2) + 2 +
        5 * ((2 * (r / 9) + if r % 9 = 2 then 0 else 1) % 2) = r := by
      split_ifs <;> omega
    rw [this]
  · rintro ⟨k, rfl⟩
    refine ⟨⟨x k, rfl⟩, ?_⟩
    unfold f
    rw [dr_eq, sq_mod]
    unfold x
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> omega

theorem nth_eq (n : ℕ) : Nat.nth P n = f n := by
  have hinf : (Set.ofPred P).Infinite :=
    Set.infinite_of_injective_forall_mem f_mono.injective (fun k => (P_iff _).2 ⟨k, rfl⟩)
  have hall : ∀ n, ∀ hfin : (Set.ofPred P).Finite, n < hfin.toFinset.card :=
    fun n hfin => absurd hfin hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ (f_mono.strictMonoOn _)
    (hall n)).symm
  · intro y hy
    obtain ⟨k, hk⟩ := (P_iff y).1 hy
    exact ⟨k, hall k, hk⟩
  · intro k _
    exact (P_iff _).2 ⟨k, rfl⟩

theorem sol : ∀ n : ℕ, 1 ≤ n →
    (Even n → a n = (9 * n - 4) ^ 2 / 4) ∧ (Odd n → a n = (9 * n - 5) ^ 2 / 4) := by
  intro n hn
  unfold a
  rw [nth_eq]
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show i + 1 + (i + 1) - 1 = 2 * i + 1 by omega,
      show 9 * (i + 1 + (i + 1)) - 4 = 2 * (9 * i + 7) by omega,
      show (2 * (9 * i + 7)) ^ 2 = 4 * ((9 * i + 7) * (9 * i + 7)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
    unfold f x
    congr 1 <;> omega
  · rintro ⟨i, rfl⟩
    rw [show 2 * i + 1 - 1 = 2 * i by omega,
      show 9 * (2 * i + 1) - 5 = 2 * (9 * i + 2) by omega,
      show (2 * (9 * i + 2)) ^ 2 = 4 * ((9 * i + 2) * (9 * i + 2)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
    unfold f x
    congr 1 <;> omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a061100.main := OMA.Helpers.sol
