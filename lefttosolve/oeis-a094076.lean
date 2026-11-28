import OMAStatements.S_oeis_a094076
import Mathlib

namespace OMA.Helpers

theorem a094076_mod (k : ℕ) :
    (271129 + 2 ^ k) % 5592405 = (271129 + 2 ^ (k % 24)) % 5592405 := by
  have hk : 2 ^ k = (2 ^ 24) ^ (k / 24) * 2 ^ (k % 24) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h1 : (2 ^ 24) ^ (k / 24) % 5592405 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [hk, Nat.add_mod, Nat.mul_mod, h1, one_mul, Nat.mod_mod, ← Nat.add_mod]

theorem a094076_cover (k : ℕ) :
    ∃ q : ℕ, 1 < q ∧ q ≤ 241 ∧ q ∣ 5592405 ∧ (271129 + 2 ^ (k % 24)) % 5592405 % q = 0 := by
  have hr : k % 24 < 24 := Nat.mod_lt _ (by norm_num)
  generalize k % 24 = r at hr ⊢
  interval_cases r
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨241, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `271129 + 2 ^ k` is never prime: it always has a divisor in `{3, 5, 7, 13, 17, 241}`. -/
theorem a094076_not_prime (k : ℕ) : ¬ (271129 + 2 ^ k).Prime := by
  intro hp
  obtain ⟨q, hq1, hq241, hqM, hq0⟩ := a094076_cover k
  rw [← a094076_mod, Nat.mod_mod_of_dvd _ hqM] at hq0
  have hqd : q ∣ 271129 + 2 ^ k := Nat.dvd_of_mod_eq_zero hq0
  rcases hp.eq_one_or_self_of_dvd q hqd with h | h
  · omega
  · generalize 2 ^ k = t at h
    omega

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a094076.main) := by
  intro h
  obtain ⟨k, hk⟩ := h 271129 (by norm_num)
  exact OMA.Helpers.a094076_not_prime k hk
