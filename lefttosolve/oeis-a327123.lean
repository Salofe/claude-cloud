import OMAStatements.S_oeis_a327123
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a327123

/-- The nonprincipal character mod 4, as a real number. -/
noncomputable def chi (m : ℕ) : ℝ := if m % 2 = 1 then (-1 : ℝ) ^ ((m - 1) / 2) else 0

theorem sin_eq (m : ℕ) : Real.sin ((m : ℝ) * Real.pi / 2) = chi m := by
  have hm : m = 4 * (m / 4) + m % 4 := (Nat.div_add_mod m 4).symm
  set q := m / 4 with hq
  have hr : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have harg : (m : ℝ) * Real.pi / 2 = ((m % 4 : ℕ) : ℝ) * Real.pi / 2 + (q : ℕ) * (2 * Real.pi) := by
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi]
  unfold chi
  interval_cases h : m % 4
  · have h2 : m % 2 = 0 := by omega
    simp [h2]
  · have h2 : m % 2 = 1 := by omega
    have h3 : (m - 1) / 2 = 2 * q := by omega
    rw [if_pos h2, h3, pow_mul]
    norm_num
  · have h2 : m % 2 = 0 := by omega
    rw [show ((2 : ℕ) : ℝ) * Real.pi / 2 = Real.pi by push_cast; ring, Real.sin_pi]
    simp [h2]
  · have h2 : m % 2 = 1 := by omega
    have h3 : (m - 1) / 2 = 2 * q + 1 := by omega
    rw [show ((3 : ℕ) : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi by push_cast; ring,
      Real.sin_add_pi, Real.sin_pi_div_two, if_pos h2, h3, pow_succ, pow_mul]
    norm_num

theorem Icc_to_range (n : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, g k = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem gcd_sum (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd k n) =
      ∑ d ∈ n.divisors, f d * (Nat.totient (n / d) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [Icc_to_range]
  have h1 : ∑ k ∈ Finset.range n, f (Nat.gcd (k + 1) n) =
      ∑ k ∈ Finset.range n, f (Nat.gcd n k) := by
    have e1 := Finset.sum_range_succ' (fun k => f (Nat.gcd n k)) n
    have e2 := Finset.sum_range_succ (fun k => f (Nat.gcd n k)) n
    simp only [Nat.gcd_zero_right, Nat.gcd_self] at e1 e2
    have e3 : ∑ k ∈ Finset.range n, f (Nat.gcd (k + 1) n) =
        ∑ k ∈ Finset.range n, f (Nat.gcd n (k + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Nat.gcd_comm]
    rw [e3]
    linarith
  rw [h1]
  have hmaps : ∀ k ∈ Finset.range n, Nat.gcd n k ∈ n.divisors := by
    intro k _
    exact Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n k, hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps f]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.sum_const, nsmul_eq_mul, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
  ring

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    (a n : ℝ) = ∑ k ∈ Finset.Icc 1 n, Real.sin ((Nat.gcd k n : ℝ) * Real.pi / 2) := by
  intro n hn
  have hs : ∀ k, Real.sin ((Nat.gcd k n : ℝ) * Real.pi / 2) = chi (Nat.gcd k n) :=
    fun k => sin_eq _
  simp only [hs]
  rw [gcd_sum n chi]
  rw [← Nat.sum_div_divisors n (fun d => chi d * (Nat.totient (n / d) : ℝ))]
  unfold a
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hk) (by omega)]
  unfold chi
  split_ifs <;> simp

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a327123.main :=
  OMA.Helpers.main_proof
