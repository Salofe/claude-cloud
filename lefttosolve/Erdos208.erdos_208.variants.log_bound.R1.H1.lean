import OMAReductions.R_Erdos208_erdos_208_variants_log_bound_R1
import Mathlib

open Finset

namespace OMA.Helpers

/-- At most `N / m + 1` multiples of `m` lie in an interval of length `N`. -/
theorem erdos208_count_dvd_Ioc (x N m : ℕ) (hm : 0 < m) :
    ((Ioc x (x + N)).filter (fun y => m ∣ y)).card ≤ N / m + 1 := by
  have hU : Ioc 0 x ∪ Ioc x (x + N) = Ioc 0 (x + N) :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.le_add_right _ _)
  have hD : Disjoint (Ioc 0 x) (Ioc x (x + N)) := Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have h1 : ((Ioc 0 (x + N)).filter (fun y => m ∣ y)).card =
      ((Ioc 0 x).filter (fun y => m ∣ y)).card +
        ((Ioc x (x + N)).filter (fun y => m ∣ y)).card := by
    rw [← hU, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hD)]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at h1
  have a1 := Nat.div_mul_le_self (x + N) m
  have a2 : x < x / m * m + m := Nat.lt_div_mul_add hm
  have a3 : N < N / m * m + m := Nat.lt_div_mul_add hm
  have h2 : (x + N) / m < x / m + N / m + 2 := by
    by_contra h
    push_neg at h
    have h4 := Nat.mul_le_mul_right m h
    nlinarith
  omega

/-- `∑_{d=2}^{L} 1/d² ≤ 3/4 - 1/L`. -/
theorem erdos208_sum_inv_sq (L : ℕ) (hL : 2 ≤ L) :
    ∑ d ∈ Icc 2 L, (1 : ℝ) / ((d : ℝ) * d) ≤ 3 / 4 - 1 / L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have key : 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ 1 / n - 1 / (n + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos208_erdos_208_variants_log_bound_R1.H1 := by
  intro x L
  rcases Nat.lt_or_ge L 2 with hL | hL
  · have hE : Icc 2 L = ∅ := Finset.Icc_eq_empty (by omega)
    simp [hE]
  have hsub : (Ioc x (x + 8 * L)).filter (fun y => ∃ d ∈ Icc 2 L, d * d ∣ y) ⊆
      (Icc 2 L).biUnion (fun d => (Ioc x (x + 8 * L)).filter (fun y => d * d ∣ y)) := by
    intro y hy
    simp only [mem_filter, mem_biUnion] at hy ⊢
    obtain ⟨hy, d, hd, hdy⟩ := hy
    exact ⟨d, hd, hy, hdy⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∑ d ∈ Icc 2 L, ((Ioc x (x + 8 * L)).filter (fun y => d * d ∣ y)).card ≤
      ∑ d ∈ Icc 2 L, (8 * L / (d * d) + 1) := by
    apply sum_le_sum
    intro d hd
    have hd2 := (mem_Icc.mp hd).1
    exact erdos208_count_dvd_Ioc x (8 * L) (d * d) (by positivity)
  have h3 : ((∑ d ∈ Icc 2 L, (8 * L / (d * d) + 1) : ℕ) : ℝ) ≤ 7 * L := by
    rw [Nat.cast_sum]
    have hS := erdos208_sum_inv_sq L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    calc ∑ d ∈ Icc 2 L, (((8 * L / (d * d) + 1 : ℕ)) : ℝ)
        ≤ ∑ d ∈ Icc 2 L, ((8 * L : ℝ) * (1 / ((d : ℝ) * d)) + 1) := by
          apply sum_le_sum
          intro d _
          have hc : (((8 * L / (d * d) : ℕ)) : ℝ) ≤ ((8 * L : ℕ) : ℝ) / ((d * d : ℕ) : ℝ) :=
            Nat.cast_div_le
          push_cast at hc ⊢
          rw [mul_one_div]
          linarith
      _ = (8 * L : ℝ) * ∑ d ∈ Icc 2 L, (1 / ((d : ℝ) * d)) + ((L + 1 - 2 : ℕ) : ℝ) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      _ ≤ (8 * L : ℝ) * (3 / 4 - 1 / L) + L := by
          have hc : ((L + 1 - 2 : ℕ) : ℝ) ≤ L := by exact_mod_cast (by omega : L + 1 - 2 ≤ L)
          have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 8 * L)
          linarith
      _ ≤ 7 * L := by
          have : (8 * L : ℝ) * (1 / L) = 8 := by field_simp
          nlinarith
  have h4 : ∑ d ∈ Icc 2 L, (8 * L / (d * d) + 1) ≤ 7 * L := by exact_mod_cast h3
  exact h1.trans (h2.trans h4)
