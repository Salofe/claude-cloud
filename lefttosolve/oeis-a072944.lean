import OMAStatements.S_oeis_a072944
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a072944 Filter Topology

theorem phi_pow (b : ℕ) : Nat.totient (2 ^ (b + 1)) = 2 ^ b := by
  rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp

theorem phi_three (b : ℕ) : Nat.totient (3 * 2 ^ (b + 1)) = 2 * 2 ^ b := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right _ (by norm_num)), phi_pow,
    Nat.totient_prime Nat.prime_three]

theorem phi_five (b : ℕ) : Nat.totient (5 * 2 ^ (b + 1)) = 4 * 2 ^ b := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right _ (by norm_num)), phi_pow,
    Nat.totient_prime (by norm_num : Nat.Prime 5)]

/-- Starting from `2 ^ (b + 2)` the orbit runs through `2 ^ m`, `3 * 2 ^ (m - 1)`,
`5 * 2 ^ (m - 1)` and then `2 ^ (m + 2)`. -/
theorem orbit (b j : ℕ) :
    f (2 ^ (b + 2)) (3 * j) = 2 ^ (b + 2 * j + 2) ∧
    f (2 ^ (b + 2)) (3 * j + 1) = 3 * 2 ^ (b + 2 * j + 1) ∧
    f (2 ^ (b + 2)) (3 * j + 2) = 5 * 2 ^ (b + 2 * j + 1) := by
  induction j with
  | zero =>
    have e0 : f (2 ^ (b + 2)) 0 = 2 ^ (b + 2) := rfl
    have e1 : f (2 ^ (b + 2)) 1 = 3 * 2 ^ (b + 1) := by
      show 2 * f (2 ^ (b + 2)) 0 - Nat.totient (f (2 ^ (b + 2)) 0) = _
      rw [e0, phi_pow, pow_succ 2 (b + 1), pow_succ 2 b]
      omega
    have e2 : f (2 ^ (b + 2)) 2 = 5 * 2 ^ (b + 1) := by
      show 2 * f (2 ^ (b + 2)) 1 - Nat.totient (f (2 ^ (b + 2)) 1) = _
      rw [e1, phi_three, pow_succ 2 b]
      omega
    simpa using ⟨e0, e1, e2⟩
  | succ j ih =>
    obtain ⟨_, _, h2⟩ := ih
    have e0 : f (2 ^ (b + 2)) (3 * (j + 1)) = 2 ^ (b + 2 * (j + 1) + 2) := by
      rw [show 3 * (j + 1) = (3 * j + 2) + 1 by ring]
      show 2 * f (2 ^ (b + 2)) (3 * j + 2) - Nat.totient (f (2 ^ (b + 2)) (3 * j + 2)) = _
      rw [h2, show b + 2 * j + 1 = (b + 2 * j) + 1 by ring, phi_five,
        show b + 2 * (j + 1) + 2 = (b + 2 * j) + 4 by ring, pow_succ 2 (b + 2 * j),
        pow_add 2 (b + 2 * j) 4]
      omega
    have e1 : f (2 ^ (b + 2)) (3 * (j + 1) + 1) = 3 * 2 ^ (b + 2 * (j + 1) + 1) := by
      show 2 * f (2 ^ (b + 2)) (3 * (j + 1)) - Nat.totient (f (2 ^ (b + 2)) (3 * (j + 1))) = _
      rw [e0, show b + 2 * (j + 1) + 2 = (b + 2 * (j + 1) + 1) + 1 by ring, phi_pow,
        pow_succ 2 (b + 2 * (j + 1) + 1)]
      omega
    have e2 : f (2 ^ (b + 2)) (3 * (j + 1) + 2) = 5 * 2 ^ (b + 2 * (j + 1) + 1) := by
      show 2 * f (2 ^ (b + 2)) (3 * (j + 1) + 1) -
        Nat.totient (f (2 ^ (b + 2)) (3 * (j + 1) + 1)) = _
      rw [e1, show b + 2 * (j + 1) + 1 = (b + 2 * (j + 1)) + 1 by ring, phi_three,
        pow_succ 2 (b + 2 * (j + 1))]
      omega
    exact ⟨e0, e1, e2⟩

theorem orbit_step (b i : ℕ) : f (2 ^ (b + 2)) (i + 3) = 4 * f (2 ^ (b + 2)) i := by
  obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, i = 3 * j ∨ i = 3 * j + 1 ∨ i = 3 * j + 2 :=
    ⟨i / 3, by omega⟩
  · rw [show 3 * j + 3 = 3 * (j + 1) by ring, (orbit b (j + 1)).1, (orbit b j).1,
      show b + 2 * (j + 1) + 2 = (b + 2 * j + 2) + 2 by ring, pow_add]
    ring
  · rw [show 3 * j + 1 + 3 = 3 * (j + 1) + 1 by ring, (orbit b (j + 1)).2.1, (orbit b j).2.1,
      show b + 2 * (j + 1) + 1 = (b + 2 * j + 1) + 2 by ring, pow_add]
    ring
  · rw [show 3 * j + 2 + 3 = 3 * (j + 1) + 2 by ring, (orbit b (j + 1)).2.2, (orbit b j).2.2,
      show b + 2 * (j + 1) + 1 = (b + 2 * j + 1) + 2 by ring, pow_add]
    ring

theorem N_pow_le (b : ℕ) : N (2 ^ (b + 2)) ≤ 4 := by
  apply Nat.sInf_le
  refine ⟨le_refl 4, fun n hn => ?_⟩
  rw [show n - 1 = (n - 4) + 3 by omega]
  exact orbit_step b (n - 4)

end OMA.Helpers

open Filter Topology in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a072944.main) := by
  rintro ⟨C, hC1, _, hT⟩
  have hC : 0 < C := by linarith
  have hsub : Tendsto (fun b : ℕ => 2 ^ (b + 2)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)).comp (tendsto_add_atTop_nat 2)
  have h1 := hT.comp hsub
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : Tendsto ((fun x : ℕ => (OMA.S_oeis_a072944.N x : ℝ) / (C * Real.log (x : ℝ))) ∘
      (fun b : ℕ => 2 ^ (b + 2))) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun b => ?_) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (4 / (C * Real.log 2)))
    · simp only [Function.comp]
      push_cast
      rw [Real.log_pow]
      positivity
    · filter_upwards [Filter.eventually_ge_atTop 1] with b hb
      simp only [Function.comp]
      push_cast
      rw [Real.log_pow]
      have hN : (OMA.S_oeis_a072944.N (2 ^ (b + 2)) : ℝ) ≤ 4 := by
        exact_mod_cast OMA.Helpers.N_pow_le b
      have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have hpos : 0 < C * (((b + 2 : ℕ) : ℝ) * Real.log 2) := by positivity
      rw [div_le_div_iff₀ hpos (by linarith), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      push_cast
      have hNn : (0 : ℝ) ≤ (OMA.S_oeis_a072944.N (2 ^ (b + 2)) : ℝ) := by positivity
      have hlog : 0 < C * Real.log 2 := by positivity
      nlinarith [mul_pos hlog (show (0 : ℝ) < b by linarith)]
  exact one_ne_zero (tendsto_nhds_unique h1 h0)
