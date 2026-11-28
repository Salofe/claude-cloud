import OMAStatements.S_oeis_a375439
import Mathlib

namespace OMA.Helpers

open PowerSeries

theorem a375439_rel (A : PowerSeries ℤ) (h : OMA.S_oeis_a375439.IsA375439 A) (n : ℕ) :
    3 * coeff n A = 3 * ((if n = 1 then 1 else 0) + (if n = 2 then 1 else 0)) +
      2 * coeff n (A ^ 3) + (if 3 ∣ n then coeff (n / 3) A else 0) := by
  have h2 := congrArg (coeff n) h.2
  have e3 : (3 : PowerSeries ℤ) = C (3 : ℤ) := by simp
  have e2 : (2 : PowerSeries ℤ) = C (2 : ℤ) := by simp
  rw [e3, e2] at h2
  simp only [map_add, coeff_C_mul, coeff_X, coeff_X_pow, OMA.S_oeis_a375439.psSubPow, coeff_mk] at h2
  rw [h2]

def a375439Odd (n : ℕ) : Prop := ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

theorem a375439Odd_zero : ¬ a375439Odd 0 := by
  rintro ⟨k, h | h⟩ <;> have := pow_pos (by norm_num : (0:ℕ) < 3) k <;> omega

theorem a375439Odd_dvd (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) : a375439Odd n ↔ a375439Odd (n / 3) := by
  obtain ⟨m, rfl⟩ := h3
  rw [Nat.mul_div_cancel_left m (by norm_num)]
  constructor
  · rintro ⟨k, h | h⟩
    · cases k with
      | zero => omega
      | succ k => exact ⟨k, Or.inl (by rw [pow_succ] at h; omega)⟩
    · cases k with
      | zero => omega
      | succ k => exact ⟨k, Or.inr (by rw [pow_succ] at h; omega)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k + 1, Or.inl (by rw [pow_succ]; omega)⟩
    · exact ⟨k + 1, Or.inr (by rw [pow_succ]; omega)⟩

theorem a375439Odd_ndvd (n : ℕ) (h3 : ¬ 3 ∣ n) : a375439Odd n ↔ (n = 1 ∨ n = 2) := by
  constructor
  · rintro ⟨k, h | h⟩
    · cases k with
      | zero => simp at h; omega
      | succ k => exact absurd ⟨3 ^ k, by rw [h, pow_succ]; ring⟩ h3
    · cases k with
      | zero => simp at h; omega
      | succ k => exact absurd ⟨2 * 3 ^ k, by rw [h, pow_succ]; ring⟩ h3
  · rintro (h | h)
    · exact ⟨0, Or.inl (by simp [h])⟩
    · exact ⟨0, Or.inr (by simp [h])⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a375439.main := by
  intro A hA n
  change PowerSeries.coeff n A % 2 = 1 ↔ a375439Odd n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hr := a375439_rel A hA n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hA.1]
      simp [a375439Odd_zero]
    · by_cases h3 : 3 ∣ n
      · rw [a375439Odd_dvd n hpos h3, ← ih (n / 3) (by omega)]
        have h1 : n ≠ 1 := by rintro rfl; norm_num at h3
        have h2 : n ≠ 2 := by rintro rfl; norm_num at h3
        simp only [h1, h2, h3, if_false, if_true] at hr
        omega
      · rw [a375439Odd_ndvd n h3]
        simp only [h3, if_false] at hr
        by_cases h1 : n = 1
        · subst h1; simp at hr; omega
        · by_cases h2 : n = 2
          · subst h2; simp at hr; omega
          · simp only [h1, h2, if_false] at hr; omega
