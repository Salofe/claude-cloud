import OMAStatements.S_oeis_a077624
import Mathlib


namespace OMA.Helpers

theorem sq_two_pow_succ {n m : ℕ} (h : 2 ^ n + 1 = m * m) : n = 3 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at h
    · exact h0
  have hprod : (m - 1) * (m + 1) = 2 ^ n := by
    obtain ⟨c, rfl⟩ : ∃ c, m = c + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  have h1 : m - 1 ∣ 2 ^ n := Dvd.intro _ hprod
  have h2 : m + 1 ∣ 2 ^ n := Dvd.intro_left _ hprod
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hij : 2 ^ i = 2 ^ j + 2 := by omega
  have hji : j < i := by
    by_contra hc
    have : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases j with _ | _ | j
  · -- m = 2
    have hm2 : m = 2 := by simp at hj'; omega
    subst hm2
    exfalso
    have : 2 ^ n = 3 := by omega
    have h3 : (2 : ℕ) ∣ 2 ^ n := by
      rcases n with _ | n
      · simp at this
      · exact Dvd.intro_left _ (pow_succ 2 n).symm
    omega
  · have hm3 : m = 3 := by simp at hj'; omega
    subst hm3
    have : 2 ^ n = 2 ^ 3 := by omega
    exact Nat.pow_right_injective le_rfl this
  · exfalso
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
    rw [pow_add, pow_add] at hij
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a077624.main := by
  intro n
  constructor
  · rintro ⟨m, hm⟩
    exact OMA.Helpers.sq_two_pow_succ hm
  · rintro rfl
    exact ⟨3, by norm_num⟩
