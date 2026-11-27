import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1
import Mathlib

open Filter

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H4 := by
  intro ε hε
  have hδpos : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
  refine ⟨min (ε / 2) 1, hδpos, ?_⟩
  set δ : ℝ := min (ε / 2) 1 with hδdef
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  set A : ℝ := (2 + δ) ^ 2 with hAdef
  have hA4 : 4 ≤ A := by nlinarith
  have hAε : A * (1 - ε) ≤ 4 := by
    rcases le_or_gt 1 ε with h | h
    · nlinarith
    · nlinarith
  set L : ℝ := Real.log (2 * A) with hLdef
  have hlogk : ∀ᶠ k : ℕ in atTop, L / (2 * ε) ≤ Real.log k :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlogk, eventually_ge_atTop 1] with k hk hk1 n hn
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hlogk0 : 0 ≤ Real.log k := Real.log_nonneg hk1'
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have h0 : Real.log (n : ℝ) = 0 := by
      interval_cases n <;> simp
    rw [h0, Real.sqrt_zero, div_zero] at hn
    linarith
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogn : 1 / 2 ≤ Real.log n := by
    have h0 := Real.log_two_gt_d9
    have h1 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2'
    linarith
  have hlogpos : 0 < Real.log n := by linarith
  have hsq : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.2 hlogpos
  have h1 : (k : ℝ) * Real.sqrt (Real.log n) ≤ (2 + δ) * Real.sqrt n := by
    rwa [le_div_iff₀ hsq] at hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h2 : (k : ℝ) ^ 2 * Real.log n ≤ A * n := by
    have hm := mul_self_le_mul_self (by positivity) h1
    have e1 : ((k : ℝ) * Real.sqrt (Real.log n)) * ((k : ℝ) * Real.sqrt (Real.log n))
        = (k : ℝ) ^ 2 * Real.log n := by
      rw [show ((k : ℝ) * Real.sqrt (Real.log n)) * ((k : ℝ) * Real.sqrt (Real.log n))
          = (k : ℝ) ^ 2 * (Real.sqrt (Real.log n) * Real.sqrt (Real.log n)) by ring,
        Real.mul_self_sqrt hlogpos.le]
    have e2 : ((2 + δ) * Real.sqrt n) * ((2 + δ) * Real.sqrt n) = A * n := by
      rw [show ((2 + δ) * Real.sqrt n) * ((2 + δ) * Real.sqrt n)
          = (2 + δ) ^ 2 * (Real.sqrt n * Real.sqrt n) by ring, Real.mul_self_sqrt hn0]
    rw [e1, e2] at hm
    exact hm
  have hk2 : 0 ≤ (k : ℝ) ^ 2 := by positivity
  have h3 : (k : ℝ) ^ 2 ≤ 2 * A * n := by nlinarith
  have h4 : 2 * Real.log k - L ≤ Real.log n := by
    have hkpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have h5 := Real.log_le_log hkpos h3
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at h5
    push_cast at h5
    linarith
  have hkey : L ≤ (2 - A * (1 / 2 - ε)) * Real.log k := by
    have h6 : 2 * ε ≤ 2 - A * (1 / 2 - ε) := by nlinarith
    have h' : L ≤ 2 * ε * Real.log k := by
      rw [div_le_iff₀ (by positivity)] at hk
      linarith
    nlinarith
  have hAn : A * ((1 / 2 - ε) * (k : ℝ) ^ 2 * Real.log k) ≤ A * n := by
    have h7 : (k : ℝ) ^ 2 * (2 * Real.log k - L) ≤ (k : ℝ) ^ 2 * Real.log n :=
      mul_le_mul_of_nonneg_left h4 hk2
    have h8 : (k : ℝ) ^ 2 * (A * (1 / 2 - ε) * Real.log k)
        ≤ (k : ℝ) ^ 2 * (2 * Real.log k - L) :=
      mul_le_mul_of_nonneg_left (by linarith) hk2
    nlinarith
  exact le_of_mul_le_mul_left hAn (by linarith)
