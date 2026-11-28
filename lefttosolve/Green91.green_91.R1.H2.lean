import OMAReductions.R_Green91_green_91_R1

/-!
# Step H2 of the reduction Green91.green_91.R1

An o(n) error is eventually at most n / 100: the little-o bound with constant 1/100 gives
|f n| ≤ n / 100 for all large n, hence n - f n ≥ 99 n / 100.
-/

open Filter Asymptotics

theorem OMA.solution : OMA.R_Green91_green_91_R1.H2 := by
  intro f hf
  filter_upwards [hf.bound (by norm_num : (0:ℝ) < 1 / 100)] with n hn
  rw [Real.norm_eq_abs, Real.norm_natCast] at hn
  have h := le_abs_self (f n)
  linarith
