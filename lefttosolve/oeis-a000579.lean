import OMAStatements.S_oeis_a000579
import Mathlib

-- Problem: A000579: Figurate numbers or binomial coefficients C(n,6).
-- Upstream: formal-conjectures statements/oeis-a000579.lean:0 (declaration OMA.S_oeis_a000579.main)
-- Credit: @Salofe (the owner of the agent is credited as the solver)

namespace OMA.Helpers

/-- Convolution identity: `sum_{l <= t} l * C(t - l, r) = C(t + 1, r + 2)`. -/
theorem a000579_conv (t r : ℕ) :
    ∑ l ∈ Finset.range (t + 1), l * Nat.choose (t - l) r = Nat.choose (t + 1) (r + 2) := by
  induction t generalizing r with
  | zero =>
    rw [Finset.sum_range_one, zero_mul, Nat.choose_eq_zero_of_lt (by omega)]
  | succ t ih =>
    cases r with
    | zero =>
      simp only [Nat.choose_zero_right, mul_one]
      show _ = Nat.choose (t + 1 + 1) 2
      rw [Finset.sum_range_id, Nat.choose_two_right]
    | succ r =>
      rw [Finset.sum_range_succ, Nat.sub_self, Nat.choose_zero_succ, mul_zero, add_zero]
      have h : ∀ l ∈ Finset.range (t + 1), l * Nat.choose (t + 1 - l) (r + 1) =
          l * Nat.choose (t - l) r + l * Nat.choose (t - l) (r + 1) := by
        intro l hl
        rw [Finset.mem_range] at hl
        rw [show t + 1 - l = (t - l) + 1 by omega, Nat.choose_succ_succ', mul_add]
      rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih r, ih (r + 1)]
      show _ = Nat.choose (t + 1 + 1) ((r + 2) + 1)
      rw [Nat.choose_succ_succ' (t + 1) (r + 2)]

/-- The convolution identity over any range long enough, for `k ≥ 2`. -/
theorem a000579_conv' (t k N : ℕ) (hk : 2 ≤ k) (h : t ≤ N + 1) :
    ∑ l ∈ Finset.range N, l * Nat.choose (t - l) k = Nat.choose (t + 1) (k + 2) := by
  have hz : ∀ l, t ≤ l + 1 → l * Nat.choose (t - l) k = 0 := by
    intro l hl
    rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  rw [← a000579_conv t k]
  rcases le_total N (t + 1) with hN | hN
  · apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
    intro l hl hl'
    rw [Finset.mem_range] at hl
    rw [Finset.mem_range] at hl'
    exact hz l (by omega)
  · symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
    intro l hl hl'
    rw [Finset.mem_range] at hl
    rw [Finset.mem_range] at hl'
    exact hz l (by omega)

/-- The innermost sum. -/
theorem a000579_inner (n c : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (if c + m ≤ n then m else 0) = Nat.choose (n + 1 - c) 2 := by
  rw [← Finset.sum_filter]
  have e : (Finset.range (n + 1)).filter (fun m => c + m ≤ n) = Finset.range (n + 1 - c) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [e, Finset.sum_range_id, Nat.choose_two_right]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a000579.main := by
  intro n
  unfold OMA.S_oeis_a000579.weightedTripleSimplexSum
  have step1 : ∀ k ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (n + 1),
      ∑ m ∈ Finset.range (n + 1), (if k + l + m ≤ n then k * l * m else 0) =
        k * (l * Nat.choose ((n + 1 - k) - l) 2) := by
    intro k _ l _
    have h : ∀ m ∈ Finset.range (n + 1), (if k + l + m ≤ n then k * l * m else 0) =
        k * l * (if k + l + m ≤ n then m else 0) := by
      intro m _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, a000579_inner, Nat.sub_sub, mul_assoc]
  rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (step1 k hk))]
  simp_rw [← Finset.mul_sum]
  have step2 : ∀ k ∈ Finset.range (n + 1),
      k * ∑ l ∈ Finset.range (n + 1), l * Nat.choose ((n + 1 - k) - l) 2 =
        k * Nat.choose ((n + 2) - k) 4 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [a000579_conv' (n + 1 - k) 2 (n + 1) le_rfl (by omega),
      show n + 1 - k + 1 = n + 2 - k by omega]
  rw [Finset.sum_congr rfl step2, a000579_conv' (n + 2) 4 (n + 1) (by norm_num) (by omega)]
