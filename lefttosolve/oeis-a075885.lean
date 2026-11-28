import OMAStatements.S_oeis_a075885
import Mathlib

/-!
Proof that a(n)^(1/n) tends to the Luroth geometric-mean constant L for OEIS A075885.

All factors floor(n/j) with j <= n are at least 1, so the terms of a(n) increase and
P(n) <= a(n) <= (n+1) P(n) with P(n) the product of floor(n/j) over j <= n. Writing
log floor(n/j) as a telescoping sum of log(i+1) - log(i) and exchanging the two sums gives
log P(n) / n = sum over i of (floor(n/(i+1)) / n) (log(i+1) - log i), which tends by
dominated convergence (Tannery) to the sum of (log(i+1) - log i)/(i+1); summation by parts
identifies this sum with the series defining log L.
-/

namespace OMA.Helpers

open OMA.S_oeis_a075885 Filter Topology

/-- The full product `∏_{j ≤ n} ⌊n/j⌋`, the largest term of `a n`. -/
def a075885_P (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 n, (n / j)

theorem a075885_prod_le (n k : ℕ) (hk : k ≤ n) :
    ∏ j ∈ Finset.Icc 1 k, (n / j) ≤ a075885_P n := by
  unfold a075885_P
  refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
  · exact Finset.Icc_subset_Icc le_rfl hk
  · intro j hj _
    rw [Finset.mem_Icc] at hj
    exact Nat.div_pos (by omega) (by omega : 0 < j)

theorem a075885_P_pos (n : ℕ) : 1 ≤ a075885_P n := by
  unfold a075885_P
  apply Finset.one_le_prod'
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact Nat.div_pos (by omega) (by omega : 0 < j)

theorem a075885_P_le_a (n : ℕ) : a075885_P n ≤ a n := by
  unfold a
  exact Finset.single_le_sum (f := fun k => ∏ j ∈ Finset.Icc 1 k, (n / j))
    (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ n)

theorem a075885_a_le (n : ℕ) : a n ≤ (n + 1) * a075885_P n := by
  unfold a
  calc ∑ k ∈ Finset.range (n + 1), ∏ j ∈ Finset.Icc 1 k, (n / j)
      ≤ ∑ k ∈ Finset.range (n + 1), a075885_P n := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        exact a075885_prod_le n k (by omega)
    _ = (n + 1) * a075885_P n := by simp

/-- The increments of the logarithm: `log (i + 1) - log i` (with `log 0 = 0`). -/
noncomputable def a075885_d (i : ℕ) : ℝ := Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)

theorem a075885_log_eq (K : ℕ) : Real.log (K : ℝ) = ∑ i ∈ Finset.range K, a075885_d i := by
  unfold a075885_d
  have := Finset.sum_range_sub (fun i : ℕ => Real.log (i : ℝ)) K
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.log_zero, sub_zero] at this
  exact this.symm

theorem a075885_logP (n : ℕ) :
    Real.log (a075885_P n : ℝ) = ∑ i ∈ Finset.range n, ((n / (i + 1) : ℕ) : ℝ) * a075885_d i := by
  unfold a075885_P
  rw [Nat.cast_prod, Real.log_prod]
  · simp_rw [a075885_log_eq]
    rw [Finset.sum_comm' (t' := Finset.range n) (s' := fun i => Finset.Icc 1 (n / (i + 1)))]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    · intro j i
      simp only [Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hj1, hjn⟩, hi⟩
        have h1 : i + 1 ≤ n / j := hi
        rw [Nat.le_div_iff_mul_le (by omega)] at h1
        refine ⟨⟨hj1, ?_⟩, ?_⟩
        · rw [Nat.le_div_iff_mul_le (Nat.succ_pos i)]
          nlinarith
        · nlinarith
      · rintro ⟨⟨hj1, hji⟩, hi⟩
        rw [Nat.le_div_iff_mul_le (by omega)] at hji
        refine ⟨⟨hj1, by nlinarith⟩, ?_⟩
        show i + 1 ≤ n / j
        rw [Nat.le_div_iff_mul_le (show 0 < j by omega)]
        nlinarith
  · intro j hj
    rw [Finset.mem_Icc] at hj
    have : 0 < n / j := Nat.div_pos (by omega) (by omega)
    exact_mod_cast this.ne'

/-- The terms of the series for `log P(n) / n`. -/
noncomputable def a075885_F (n i : ℕ) : ℝ := ((n / (i + 1) : ℕ) : ℝ) / n * a075885_d i

theorem a075885_tsum_F (n : ℕ) : Real.log (a075885_P n : ℝ) / n = ∑' i, a075885_F n i := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · rw [a075885_logP, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    unfold a075885_F
    ring
  · intro i hi
    rw [Finset.mem_range, not_lt] at hi
    unfold a075885_F
    rw [Nat.div_eq_of_lt (by omega)]
    simp

theorem a075885_d_nonneg (i : ℕ) : 0 ≤ a075885_d i := by
  unfold a075885_d
  obtain rfl | hipos := Nat.eq_zero_or_pos i
  · simp
  · have h0 : (0 : ℝ) < i := Nat.cast_pos.mpr hipos
    have := Real.log_le_log h0 (show (i : ℝ) ≤ (i : ℝ) + 1 by linarith)
    linarith

theorem a075885_d_le (i : ℕ) (hi : 1 ≤ i) : a075885_d i ≤ 1 / (i : ℝ) := by
  unfold a075885_d
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  rw [← Real.log_div (by positivity) hi'.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((i : ℝ) + 1) / i by positivity)
  have e : ((i : ℝ) + 1) / i - 1 = 1 / i := by field_simp; ring
  linarith

theorem a075885_bound_summable : Summable (fun i : ℕ => a075885_d i / ((i : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => div_nonneg (a075885_d_nonneg i) (by positivity))
    (fun i => ?_) (Real.summable_one_div_nat_pow.mpr one_lt_two)
  obtain rfl | hipos := Nat.eq_zero_or_pos i
  · simp [a075885_d]
  · have hi' : (0 : ℝ) < i := Nat.cast_pos.mpr hipos
    have h1 := a075885_d_le i hipos
    calc a075885_d i / ((i : ℝ) + 1) ≤ (1 / (i : ℝ)) / ((i : ℝ) + 1) := by gcongr
      _ ≤ 1 / (i : ℝ) ^ 2 := by
        rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
        nlinarith

theorem a075885_floor_le (n i : ℕ) : ((n / (i + 1) : ℕ) : ℝ) / n ≤ 1 / ((i : ℝ) + 1) := by
  obtain rfl | hnpos := Nat.eq_zero_or_pos n
  · simp only [Nat.zero_div, Nat.cast_zero, div_zero]
    positivity
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    rw [div_le_iff₀ hnR]
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := i + 1)
    push_cast at this
    calc ((n / (i + 1) : ℕ) : ℝ) ≤ n / ((i : ℝ) + 1) := this
      _ = 1 / ((i : ℝ) + 1) * n := by ring

theorem a075885_F_tendsto (i : ℕ) :
    Tendsto (fun n => a075885_F n i) atTop (𝓝 (a075885_d i / ((i : ℝ) + 1))) := by
  have key : Tendsto (fun n : ℕ => ((n / (i + 1) : ℕ) : ℝ) / n) atTop (𝓝 (1 / ((i : ℝ) + 1))) := by
    have hlow : Tendsto (fun n : ℕ => 1 / ((i : ℝ) + 1) - 1 / (n : ℝ)) atTop
        (𝓝 (1 / ((i : ℝ) + 1))) := by
      simpa using (tendsto_const_nhds (x := 1 / ((i : ℝ) + 1))).sub tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn0
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
      have hdm := Nat.div_add_mod n (i + 1)
      have hlt := Nat.mod_lt n (show i + 1 > 0 by omega)
      have e : (n : ℝ) = ((i : ℝ) + 1) * ((n / (i + 1) : ℕ) : ℝ) + ((n % (i + 1) : ℕ) : ℝ) := by
        have := congrArg (fun m : ℕ => (m : ℝ)) hdm
        push_cast at this
        linarith
      have hlt' : ((n % (i + 1) : ℕ) : ℝ) < (i : ℝ) + 1 := by exact_mod_cast hlt
      rw [le_div_iff₀ hnR]
      have e2 : (1 / ((i : ℝ) + 1) - 1 / n) * n = n / ((i : ℝ) + 1) - 1 := by
        field_simp
      rw [e2, div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      nlinarith
    · exact Eventually.of_forall (fun n => a075885_floor_le n i)
  have e : a075885_d i / ((i : ℝ) + 1) = 1 / ((i : ℝ) + 1) * a075885_d i := by ring
  rw [e]
  exact key.mul_const (a075885_d i)

theorem a075885_F_bound (n i : ℕ) : ‖a075885_F n i‖ ≤ a075885_d i / ((i : ℝ) + 1) := by
  unfold a075885_F
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)) (a075885_d_nonneg i))]
  have e : a075885_d i / ((i : ℝ) + 1) = 1 / ((i : ℝ) + 1) * a075885_d i := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (a075885_floor_le n i) (a075885_d_nonneg i)

theorem a075885_logP_tendsto :
    Tendsto (fun n : ℕ => Real.log (a075885_P n : ℝ) / n) atTop
      (𝓝 (∑' i, a075885_d i / ((i : ℝ) + 1))) := by
  have h : (fun n : ℕ => Real.log (a075885_P n : ℝ) / n) = fun n => ∑' i, a075885_F n i :=
    funext a075885_tsum_F
  rw [h]
  exact tendsto_tsum_of_dominated_convergence a075885_bound_summable a075885_F_tendsto
    (Eventually.of_forall (fun n i => a075885_F_bound n i))

theorem a075885_partial (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), a075885_d i / ((i : ℝ) + 1) =
      ∑ i ∈ Finset.range M, Real.log ((i : ℝ) + 1) / (((i : ℝ) + 1) * ((i : ℝ) + 2))
        + Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp [a075885_d]
  | succ M ih =>
    rw [Finset.sum_range_succ _ (M + 1), ih, Finset.sum_range_succ _ M]
    unfold a075885_d
    push_cast
    field_simp
    ring

theorem a075885_sum_eq :
    ∑' i, a075885_d i / ((i : ℝ) + 1) =
      ∑' n : ℕ, Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  have h1 : Tendsto (fun M => ∑ i ∈ Finset.range M, a075885_d i / ((i : ℝ) + 1)) atTop
      (𝓝 (∑' i, a075885_d i / ((i : ℝ) + 1))) :=
    a075885_bound_summable.hasSum.tendsto_sum_nat
  have h2 := h1.comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1)) atTop (𝓝 0) := by
    have hg : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hg
    refine this.congr (fun M => ?_)
    simp
  have h4 : Tendsto (fun M => ∑ i ∈ Finset.range M,
      Real.log ((i : ℝ) + 1) / (((i : ℝ) + 1) * ((i : ℝ) + 2))) atTop
      (𝓝 (∑' i, a075885_d i / ((i : ℝ) + 1))) := by
    have := h2.sub h3
    rw [sub_zero] at this
    refine this.congr (fun M => ?_)
    simp only [Function.comp]
    rw [a075885_partial M]
    ring
  have hnn : ∀ i : ℕ, 0 ≤ Real.log ((i : ℝ) + 1) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := fun i =>
    div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])) (by positivity)
  have hs := (hasSum_iff_tendsto_nat_of_nonneg hnn _).mpr h4
  push_cast
  exact hs.tsum_eq.symm

end OMA.Helpers

open OMA.S_oeis_a075885 Filter Topology OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a075885.main := by
  have hP := a075885_logP_tendsto
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have hg : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hg
    refine this.congr (fun n => ?_)
    simp
  have hA : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / n) atTop
      (𝓝 (∑' i, a075885_d i / ((i : ℝ) + 1))) := by
    have hup := hP.add hlog
    rw [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hP hup ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n _hn0
      have h1 : (1 : ℝ) ≤ a075885_P n := by exact_mod_cast a075885_P_pos n
      have h2 : (a075885_P n : ℝ) ≤ a n := by exact_mod_cast a075885_P_le_a n
      exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) h2) (Nat.cast_nonneg n)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n _hn0
      have h1 : (1 : ℝ) ≤ a075885_P n := by exact_mod_cast a075885_P_pos n
      have h2 : (a075885_P n : ℝ) ≤ a n := by exact_mod_cast a075885_P_le_a n
      have h3 : (a n : ℝ) ≤ (a075885_P n : ℝ) * ((n : ℝ) + 1) := by
        have := a075885_a_le n
        have h : ((a n : ℕ) : ℝ) ≤ (((n + 1) * a075885_P n : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h
        linarith
      rw [← add_div, ← Real.log_mul (by positivity) (by positivity)]
      exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) h3) (Nat.cast_nonneg n)
  have hexp := (Real.continuous_exp.tendsto _).comp hA
  have hL : L = Real.exp (∑' i, a075885_d i / ((i : ℝ) + 1)) := by
    unfold L
    rw [a075885_sum_eq]
  rw [hL]
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n _hn0
  have hapos : (0 : ℝ) < a n := by
    have := lt_of_lt_of_le (a075885_P_pos n) (a075885_P_le_a n)
    exact_mod_cast this
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos hapos]
  congr 1
  ring
