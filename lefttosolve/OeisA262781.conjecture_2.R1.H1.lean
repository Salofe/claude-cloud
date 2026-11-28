import OMAReductions.R_OeisA262781_conjecture_2_R1
import Mathlib

/-!
# Step H1 of the reduction OeisA262781.conjecture_2.R1

At each of the eighteen listed indices `n`, the count `OeisA262781.a n` equals one.

The defining triple sum runs over `x, y, z ≤ n`.  Using `φ (y ^ 2) = y * φ y` and `φ y ≥ 2`
for `y ≥ 3`, only `x < X` and `y, z < Y` can contribute, for explicit small `X` and `Y`.
The resulting short sum is evaluated by the kernel.
-/

namespace OMA.Helpers

open Finset

/-- `φ (y ^ 2) = y * φ y`. -/
theorem a262781_totient_sq (y : ℕ) : Nat.totient (y ^ 2) = y * Nat.totient y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  · have h := Nat.totient_gcd_mul_totient_mul y y
    rw [Nat.gcd_self] at h
    have hp : 0 < Nat.totient y := Nat.totient_pos.2 hy
    rw [sq]
    apply Nat.eq_of_mul_eq_mul_left hp
    rw [h]
    ring

/-- `φ y ≥ 2` for `y ≥ 3`. -/
theorem a262781_two_le_totient {y : ℕ} (hy : 3 ≤ y) : 2 ≤ Nat.totient y := by
  obtain ⟨k, hk⟩ := Nat.totient_even (by omega : 2 < y)
  have hp : 0 < Nat.totient y := Nat.totient_pos.2 (by omega)
  omega

/-- The summand of `OeisA262781.a`, with `φ (y ^ 2)` written as `y * φ y`. -/
def a262781Term (n x y z : ℕ) : ℕ :=
  if (y.Prime ∨ z.Prime) ∧ x ^ 2 + y * Nat.totient y + z * Nat.totient z = n then 1 else 0

/-- The triple sum with the ranges cut down to `x < X` and `y, z < Y`. -/
def a262781Bounded (n X Y : ℕ) : ℕ :=
  ∑ x ∈ range X, ∑ y ∈ Ico 1 Y, ∑ z ∈ Ico y Y, a262781Term n x y z

theorem a262781_eq_bounded (n X Y : ℕ) (hXn : X ≤ n + 1) (hYn : Y ≤ n + 1)
    (hX : n < X ^ 2) (h3 : 3 ≤ Y)
    (hY : ∀ y ∈ Ico Y (n / 2 + 1), n < y * Nat.totient y) :
    OeisA262781.a n = a262781Bounded n X Y := by
  have hbig : ∀ y, Y ≤ y → n < y * Nat.totient y := by
    intro y hy
    by_cases hle : y ≤ n / 2
    · exact hY y (mem_Ico.2 ⟨hy, by omega⟩)
    · have h2 : 2 ≤ Nat.totient y := a262781_two_le_totient (by omega)
      have hm : y * 2 ≤ y * Nat.totient y := Nat.mul_le_mul_left y h2
      omega
  have hv : ∀ x y z, (X ≤ x ∨ Y ≤ y ∨ Y ≤ z) → a262781Term n x y z = 0 := by
    intro x y z h
    unfold a262781Term
    rw [if_neg]
    rintro ⟨_, heq⟩
    rcases h with h | h | h
    · have : X ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left h 2
      omega
    · have := hbig y h
      omega
    · have := hbig z h
      omega
  calc OeisA262781.a n
      = ∑ x ∈ range (n + 1), ∑ y ∈ Ico 1 (n + 1), ∑ z ∈ Ico y (n + 1),
          a262781Term n x y z := by
        unfold OeisA262781.a a262781Term
        simp only [a262781_totient_sq]
    _ = ∑ x ∈ range X, ∑ y ∈ Ico 1 (n + 1), ∑ z ∈ Ico y (n + 1),
          a262781Term n x y z := by
        symm
        apply sum_subset (range_subset_range.2 hXn)
        intro x _ hx
        apply sum_eq_zero
        intro y _
        apply sum_eq_zero
        intro z _
        apply hv
        left
        simpa using hx
    _ = ∑ x ∈ range X, ∑ y ∈ Ico 1 Y, ∑ z ∈ Ico y (n + 1), a262781Term n x y z := by
        apply sum_congr rfl
        intro x _
        symm
        apply sum_subset (Ico_subset_Ico_right hYn)
        intro y hy1 hy2
        apply sum_eq_zero
        intro z _
        apply hv
        right
        left
        simp only [mem_Ico] at hy1 hy2
        omega
    _ = a262781Bounded n X Y := by
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro y _
        symm
        apply sum_subset (Ico_subset_Ico_right hYn)
        intro z hz1 hz2
        apply hv
        right
        right
        simp only [mem_Ico] at hz1 hz2
        omega

end OMA.Helpers

set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_OeisA262781_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · rw [OMA.Helpers.a262781_eq_bounded 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 5 3 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 9 4 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 10 4 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 17 5 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 20 5 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 24 5 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 25 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 31 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 36 7 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 45 7 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 73 9 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 80 9 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 101 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 136 12 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 145 13 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 388 20 31 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
  · rw [OMA.Helpers.a262781_eq_bounded 649 26 43 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)]
    decide +kernel
