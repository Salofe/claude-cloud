import OMAStatements.S_oeis_a076821
import Mathlib

namespace OMA.Helpers

theorem amgm (t g : ℝ) (ht : 0 ≤ t) (hg : 0 < g) : 3 * t ^ 2 ≤ 2 * t ^ 3 * g + 1 / g ^ 2 := by
  have h1 : 3 * t ^ 2 * g ^ 2 ≤ 2 * t ^ 3 * g ^ 3 + 1 := by
    have hu : 0 ≤ t * g := mul_nonneg ht hg.le
    nlinarith [mul_nonneg (sq_nonneg (t * g - 1)) (by linarith : (0:ℝ) ≤ 2 * (t * g) + 1)]
  have hg2 : 0 < g ^ 2 := by positivity
  have : 2 * t ^ 3 * g + 1 / g ^ 2 = (2 * t ^ 3 * g ^ 3 + 1) / g ^ 2 := by
    field_simp
  rw [this, le_div_iff₀ hg2]
  exact h1

theorem key_bound (hS : Summable (fun n : ℕ =>
      (1 : ℝ) / (((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) ^ 2))) (N : ℕ) :
    (N : ℝ) ^ 3 ≤ (∑' n : ℕ,
      (1 : ℝ) / (((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) ^ 2)) *
        (Nat.nth Nat.Prime N : ℝ) ^ 2 := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hmono := Nat.nth_strictMono hinf
  set P := Nat.nth Nat.Prime with hP
  set g : ℕ → ℝ := fun n => ((P (n + 1) - P n : ℕ) : ℝ) with hgdef
  set S := ∑' n : ℕ, (1 : ℝ) / (g n) ^ 2 with hSdef
  have hg : ∀ n, g n = (P (n + 1) : ℝ) - P n := fun n => by
    simp only [hgdef]
    rw [Nat.cast_sub (hmono (Nat.lt_succ_self n)).le]
  have hgpos : ∀ n, 0 < g n := fun n => by
    rw [hg n]
    have : P n < P (n + 1) := hmono (Nat.lt_succ_self n)
    have : (P n : ℝ) < P (n + 1) := by exact_mod_cast this
    linarith
  have hPN : (0 : ℝ) < P N := by exact_mod_cast (Nat.nth_mem_of_infinite hinf N).pos
  have hsum : ∑ n ∈ Finset.range N, g n ≤ P N := by
    rw [Finset.sum_congr rfl (fun n _ => hg n), Finset.sum_range_sub (fun n => (P n : ℝ))]
    have : (0 : ℝ) ≤ P 0 := by positivity
    linarith
  set t : ℝ := (N : ℝ) / P N with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 : ∑ n ∈ Finset.range N, 3 * t ^ 2 ≤
      ∑ n ∈ Finset.range N, (2 * t ^ 3 * g n + 1 / (g n) ^ 2) :=
    Finset.sum_le_sum (fun n _ => amgm t (g n) ht0 (hgpos n))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at h1
  have h2 : ∑ n ∈ Finset.range N, 1 / (g n) ^ 2 ≤ S :=
    hS.sum_le_tsum _ (fun _ _ => by positivity)
  have h3 : 2 * t ^ 3 * ∑ n ∈ Finset.range N, g n ≤ 2 * t ^ 3 * P N := by
    have : 0 ≤ 2 * t ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left hsum this
  have h4 : (N : ℝ) * (3 * t ^ 2) ≤ 2 * t ^ 3 * P N + S := by linarith
  have e1 : (N : ℝ) * (3 * t ^ 2) = 3 * ((N : ℝ) ^ 3 / (P N) ^ 2) := by
    rw [ht]; field_simp
  have e2 : 2 * t ^ 3 * P N = 2 * ((N : ℝ) ^ 3 / (P N) ^ 2) := by
    rw [ht]; field_simp
  rw [e1, e2] at h4
  have h5 : (N : ℝ) ^ 3 / (P N) ^ 2 ≤ S := by linarith
  rwa [div_le_iff₀ (by positivity)] at h5

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a076821.main := by
  intro hS
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  set P := Nat.nth Nat.Prime with hP
  set S := ∑' n : ℕ,
      (1 : ℝ) / (((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) ^ 2) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun _ => by positivity)
  -- summability of 1 / P n
  have hsum1 : Summable (fun n : ℕ => (1 : ℝ) / P (n + 1)) := by
    have hb : Summable (fun n : ℕ => Real.sqrt S * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
      apply Summable.mul_left
      exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num))
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
    have hk := key_bound hS (n + 1)
    have hPN : (0 : ℝ) < P (n + 1) := by
      exact_mod_cast (Nat.nth_mem_of_infinite hinf (n + 1)).pos
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hr : (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
    have hrpos : 0 < ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hN _
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)]
    rw [mul_pow, Real.sq_sqrt hS0, inv_pow, hr, div_pow, one_pow]
    rw [div_le_iff₀ (by positivity)]
    rw [mul_comm] at hk
    calc (1 : ℝ) = ((n + 1 : ℕ) : ℝ) ^ 3 * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹ := by field_simp
      _ ≤ (P (n + 1) : ℝ) ^ 2 * S * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hk (by positivity)
      _ = S * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹ * (P (n + 1) : ℝ) ^ 2 := by ring
  have hsum2 : Summable (fun n : ℕ => (1 : ℝ) / P n) := (summable_nat_add_iff 1).mp hsum1
  apply not_summable_one_div_on_primes
  have hinj : Function.Injective P := Nat.nth_injective hinf
  rw [← hinj.summable_iff]
  · convert hsum2 using 1
    funext n
    simp only [Function.comp_apply]
    rw [Set.indicator_of_mem]
    exact Nat.nth_mem_of_infinite hinf n
  · intro x hx
    rw [Nat.range_nth_of_infinite hinf] at hx
    exact Set.indicator_of_notMem hx _
