import OMAStatements.S_oeis_a077625
import Mathlib

namespace OMA.Helpers

/-- For `n ≥ 2`, `2 ^ n - 1 ≡ 3 (mod 4)` is not a square; for `n = 1` it is `1 = 1 * 1`. -/
theorem a077625_aux : ∀ n : ℕ, 1 ≤ n → (IsSquare (2 ^ n - 1) ↔ n = 1) := by
  intro n hn
  constructor
  · rintro ⟨r, hr⟩
    by_contra hne
    have h2 : 2 ≤ n := by omega
    have h4 : 4 ∣ 2 ^ n := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact Nat.pow_dvd_pow 2 h2
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hmod : (2 ^ n - 1) % 4 = 3 := by omega
    rw [hr] at hmod
    have : r * r % 4 = (r % 4) * (r % 4) % 4 := Nat.mul_mod r r 4
    have hr4 : r % 4 < 4 := Nat.mod_lt r (by norm_num)
    interval_cases h : r % 4 <;> omega
  · rintro rfl
    exact ⟨1, by norm_num⟩

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a077625.main :=
  OMA.Helpers.a077625_aux
