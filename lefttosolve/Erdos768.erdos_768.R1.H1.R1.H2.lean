import OMAReductions.R_Erdos768_erdos_768_R1_H1_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos768.erdos_768.R1.H1.R1

Assuming the prime number theorem with error term
`ψ x - x = O(x exp (-c (log x) ^ (1/10)))`, the number `N` of primes in `(e ^ (u - δ), e ^ u]`
satisfies `N / ((1 - e ^ (-δ)) e ^ u / u) → 1` whenever `u → ∞` and `u ^ (-2) ≤ δ ≤ 1`.

Write `X = e ^ u`, `Y = e ^ (u - δ)`. Then `θ X - θ Y` is the sum of `log p` over these primes,
and each `log p` lies in `(u - δ, u]`, so `N (u - δ) ≤ θ X - θ Y ≤ N u`. Since
`(1 - e ^ (-δ)) X = X - Y`, the ratio is `N u / (X - Y)`, which lies between
`Q = (θ X - θ Y) / (X - Y)` and `Q u / (u - δ)`.
From `1 - e ^ (-δ) ≥ δ / 2 ≥ 1 / (2 u ^ 2)` we get `X - Y ≥ X / (2 u ^ 2)`, hence
`|Q - 1| ≤ 2 |g u| + 8 |g (u - δ)|` with `g w = w ^ 2 (θ (e ^ w) - e ^ w) / e ^ w`.
The function `g` tends to `0`: the hypothesis gives `w ^ 2 (ψ (e ^ w) - e ^ w) / e ^ w → 0`
(via `w ^ 2 exp (-c w ^ (1/10)) → 0`, substituting `t = w ^ (1/10)`), and Mathlib's bound
`ψ x - θ x ≤ 2 √x log x` gives `w ^ 2 (ψ - θ) (e ^ w) / e ^ w ≤ 2 w ^ 3 e ^ (-w/2) → 0`.
Finally `u / (u - δ) → 1`, and the squeeze theorem concludes.

Only Mathlib and the reduction's own definitions are used.
-/

open Filter Asymptotics

namespace OMA.Helpers

/-- `w ^ 2 * exp (-c * w ^ (1/10)) → 0`, by the substitution `t = w ^ (1/10)`. -/
theorem e768_sq_mul_exp_neg_rpow (c : ℝ) (hc : 0 < c) :
    Tendsto (fun w : ℝ => w ^ 2 * Real.exp (-c * w ^ ((1 : ℝ) / 10))) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ (20 : ℝ) * Real.exp (-c * t)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 20 c hc
  have h2 : Tendsto (fun w : ℝ => w ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h3 := h1.comp h2
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hw]
  norm_num

/-- The error term hypothesis, rescaled: `w ^ 2 * (ψ (e ^ w) - e ^ w) / e ^ w → 0`. -/
theorem e768_psi_err (c : ℝ) (hc : 0 < c)
    (h : (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    Tendsto (fun w : ℝ => w ^ 2 * (Chebyshev.psi (Real.exp w) - Real.exp w) / Real.exp w)
      atTop (nhds 0) := by
  have h1 := h.comp_tendsto Real.tendsto_exp_atTop
  have h2 := (isBigO_refl (fun w : ℝ => w ^ 2 / Real.exp w) atTop).mul h1
  have h3 : (fun w : ℝ => w ^ 2 * (Chebyshev.psi (Real.exp w) - Real.exp w) / Real.exp w)
      =O[atTop] (fun w : ℝ => w ^ 2 * Real.exp (-c * w ^ ((1 : ℝ) / 10))) := by
    refine h2.congr (fun w => ?_) (fun w => ?_)
    · simp only [Function.comp_apply, Pi.sub_apply, id]
      ring
    · simp only [Function.comp_apply, Real.log_exp]
      field_simp
  exact h3.trans_tendsto (e768_sq_mul_exp_neg_rpow c hc)

/-- `w ^ 2 * (ψ (e ^ w) - θ (e ^ w)) / e ^ w → 0`, from `ψ x - θ x ≤ 2 √x log x`. -/
theorem e768_psi_sub_theta :
    Tendsto (fun w : ℝ => w ^ 2 * (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w))
      / Real.exp w) atTop (nhds 0) := by
  have hlim : Tendsto (fun w : ℝ => 2 * (w ^ (3 : ℝ) * Real.exp (-(1 / 2) * w))) atTop
      (nhds 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 (1 / 2) (by norm_num)).const_mul 2
    simpa using this
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with w
    have h0 := Chebyshev.theta_le_psi (Real.exp w)
    have h1 : 0 ≤ Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w) := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
    have h1 : 1 ≤ Real.exp w := Real.one_le_exp hw
    have h2 := Chebyshev.psi_sub_theta_le h1
    rw [Real.log_exp, ← Real.exp_half] at h2
    have h3 : Real.exp (-(1 / 2) * w) * Real.exp w = Real.exp (w / 2) := by
      rw [← Real.exp_add]
      ring_nf
    have h4 : w ^ (3 : ℝ) = w ^ 3 := by norm_num
    rw [div_le_iff₀ (Real.exp_pos w), h4]
    calc w ^ 2 * (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w))
        ≤ w ^ 2 * (2 * Real.exp (w / 2) * w) := by gcongr
      _ = 2 * (w ^ 3 * Real.exp (-(1 / 2) * w)) * Real.exp w := by
        rw [← h3]
        ring

/-- `w ^ 2 * (θ (e ^ w) - e ^ w) / e ^ w → 0`. -/
theorem e768_theta_err (c : ℝ) (hc : 0 < c)
    (h : (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    Tendsto (fun w : ℝ => w ^ 2 * (Chebyshev.theta (Real.exp w) - Real.exp w) / Real.exp w)
      atTop (nhds 0) := by
  have := (e768_psi_err c hc h).sub e768_psi_sub_theta
  rw [sub_zero] at this
  refine this.congr (fun w => ?_)
  ring

/-- `θ X - θ Y` is the sum of `log p` over the primes `p` with `Y < p ≤ X`. -/
theorem e768_sum_eq (X Y : ℝ) (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    ∑ p ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ Y < (p : ℝ)), Real.log p
      = Chebyshev.theta X - Chebyshev.theta Y := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime) (fun p : ℕ => Y < (p : ℝ)) (fun p => Real.log p)
  rw [eq_sub_iff_add_eq]
  unfold Chebyshev.theta
  rw [← hsplit]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨⟨by omega, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨by omega, h2⟩, h3, h4⟩
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, not_lt]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨⟨h1, le_trans h2 (Nat.floor_mono hYX)⟩, h3⟩, ?_⟩
      exact le_trans (Nat.cast_le.mpr h2) (Nat.floor_le hY)
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, Nat.le_floor h4⟩, h3⟩

/-- A sum of `log p` over a finite set is sandwiched by the cardinality times the extreme values. -/
theorem e768_card_le (S : Finset ℕ) (a b : ℝ)
    (h : ∀ p ∈ S, a ≤ Real.log p ∧ Real.log p ≤ b) :
    (S.card : ℝ) * a ≤ ∑ p ∈ S, Real.log p ∧ ∑ p ∈ S, Real.log p ≤ (S.card : ℝ) * b := by
  constructor
  · have := Finset.card_nsmul_le_sum S (fun p => Real.log p) a (fun p hp => (h p hp).1)
    rwa [nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul S (fun p => Real.log p) b (fun p hp => (h p hp).2)
    rwa [nsmul_eq_mul] at this

/-- The number `N` of primes in `(e ^ (u - δ), e ^ u]` satisfies
`N (u - δ) ≤ θ (e ^ u) - θ (e ^ (u - δ)) ≤ N u`. -/
theorem e768_count_bounds (u δ : ℝ) (hδ : 0 ≤ δ) :
    (((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
        (fun p => Nat.Prime p ∧ Real.exp (u - δ) < (p : ℝ))).card : ℝ) * (u - δ)
      ≤ Chebyshev.theta (Real.exp u) - Chebyshev.theta (Real.exp (u - δ)) ∧
    Chebyshev.theta (Real.exp u) - Chebyshev.theta (Real.exp (u - δ))
      ≤ (((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
        (fun p => Nat.Prime p ∧ Real.exp (u - δ) < (p : ℝ))).card : ℝ) * u := by
  have hYX : Real.exp (u - δ) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
  rw [← e768_sum_eq (Real.exp u) (Real.exp (u - δ)) (Real.exp_pos _).le hYX]
  apply e768_card_le
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨_, hpX⟩, _, hYp⟩ := hp
  have hp0 : (0 : ℝ) < p := lt_trans (Real.exp_pos _) hYp
  have hpX' : (p : ℝ) ≤ Real.exp u := (Nat.le_floor_iff (Real.exp_pos u).le).mp hpX
  constructor
  · have := Real.log_lt_log (Real.exp_pos _) hYp
    rw [Real.log_exp] at this
    exact this.le
  · have := Real.log_le_log hp0 hpX'
    rwa [Real.log_exp] at this

/-- The elementary inequalities for one index: with `X = e ^ u`, `Y = e ^ (u - δ)` and
`Q = (tX - tY) / (X - Y)`, the ratio `N / ((1 - e ^ (-δ)) X / u)` lies between `Q` and
`Q u / (u - δ)`, and `|Q - 1|` is controlled by the relative errors of `tX` and `tY`. -/
theorem e768_pointwise (u δ N tX tY : ℝ) (hu : 2 ≤ u) (hδ1 : u⁻¹ ^ 2 ≤ δ) (hδ2 : δ ≤ 1)
    (hN1 : N * (u - δ) ≤ tX - tY) (hN2 : tX - tY ≤ N * u) :
    (tX - tY) / (Real.exp u - Real.exp (u - δ)) ≤ N / ((1 - Real.exp (-δ)) * Real.exp u / u) ∧
    N / ((1 - Real.exp (-δ)) * Real.exp u / u)
      ≤ (tX - tY) / (Real.exp u - Real.exp (u - δ)) * (u / (u - δ)) ∧
    |(tX - tY) / (Real.exp u - Real.exp (u - δ)) - 1|
      ≤ 2 * |u ^ 2 * (tX - Real.exp u) / Real.exp u|
        + 8 * |(u - δ) ^ 2 * (tY - Real.exp (u - δ)) / Real.exp (u - δ)| := by
  have hu0 : 0 < u := by linarith
  have hδ0 : 0 ≤ δ := le_trans (sq_nonneg _) hδ1
  have hud : 0 < u - δ := by linarith
  have hX : 0 < Real.exp u := Real.exp_pos u
  have hY : 0 < Real.exp (u - δ) := Real.exp_pos _
  have hYX : Real.exp (u - δ) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
  have hYK : Real.exp (u - δ) = Real.exp u * Real.exp (-δ) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hK : δ / 2 ≤ 1 - Real.exp (-δ) := by
    have h1 : δ + 1 ≤ Real.exp δ := Real.add_one_le_exp δ
    have h2 : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-δ) := Real.exp_pos _
    nlinarith
  have hu2 : 1 ≤ u ^ 2 * δ := by
    have h := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg u)
    rw [inv_pow, inv_mul_cancel₀ (by positivity)] at h
    linarith
  have hK1 : 1 ≤ 2 * u ^ 2 * (1 - Real.exp (-δ)) := by nlinarith
  have hKpos : 0 < 1 - Real.exp (-δ) := by nlinarith
  have hD : Real.exp u - Real.exp (u - δ) = (1 - Real.exp (-δ)) * Real.exp u := by
    rw [hYK]; ring
  have hDpos : 0 < Real.exp u - Real.exp (u - δ) := by rw [hD]; positivity
  have hR : N / ((1 - Real.exp (-δ)) * Real.exp u / u)
      = N * u / (Real.exp u - Real.exp (u - δ)) := by
    rw [hD, div_div_eq_mul_div]
  rw [hR]
  refine ⟨?_, ?_, ?_⟩
  · gcongr
  · rw [div_mul_div_comm, div_le_div_iff₀ hDpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hN1 (le_of_lt (mul_pos hu0 hDpos))]
  · have hsplit : (tX - tY) / (Real.exp u - Real.exp (u - δ)) - 1
        = (tX - Real.exp u) / (Real.exp u - Real.exp (u - δ))
          - (tY - Real.exp (u - δ)) / (Real.exp u - Real.exp (u - δ)) := by
      field_simp
      ring
    rw [hsplit]
    refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
    · rw [abs_div, abs_div, abs_mul, abs_of_pos hDpos, abs_of_pos hX,
        abs_of_nonneg (sq_nonneg u), div_le_iff₀ hDpos, hD]
      calc |tX - Real.exp u| = 1 * |tX - Real.exp u| := by ring
        _ ≤ (2 * u ^ 2 * (1 - Real.exp (-δ))) * |tX - Real.exp u| := by gcongr
        _ = 2 * (u ^ 2 * |tX - Real.exp u| / Real.exp u)
              * ((1 - Real.exp (-δ)) * Real.exp u) := by
          field_simp
    · rw [abs_div, abs_div, abs_mul, abs_of_pos hDpos, abs_of_pos hY,
        abs_of_nonneg (sq_nonneg (u - δ)), div_le_iff₀ hDpos, hD]
      have h5 : u ^ 2 ≤ 4 * (u - δ) ^ 2 := by nlinarith
      have h6 : 1 ≤ 8 * (u - δ) ^ 2 * (1 - Real.exp (-δ)) := by nlinarith
      have h7 : 1 ≤ Real.exp u / Real.exp (u - δ) := (one_le_div hY).mpr hYX
      calc |tY - Real.exp (u - δ)| = 1 * 1 * |tY - Real.exp (u - δ)| := by ring
        _ ≤ (8 * (u - δ) ^ 2 * (1 - Real.exp (-δ))) * (Real.exp u / Real.exp (u - δ))
              * |tY - Real.exp (u - δ)| := by gcongr
        _ = 8 * ((u - δ) ^ 2 * |tY - Real.exp (u - δ)| / Real.exp (u - δ))
              * ((1 - Real.exp (-δ)) * Real.exp u) := by
          field_simp

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos768_erdos_768_R1_H1_R1.H2 := by
  rintro ⟨c, hc, hO⟩ u δ hu hδ
  have hg := e768_theta_err c hc hO
  have hb : Tendsto (fun n => u n - δ n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-1) hu)
    filter_upwards [hδ] with n hn
    linarith [hn.2]
  have hga := hg.comp hu
  have hgb := hg.comp hb
  have hev : ∀ᶠ n in atTop, 2 ≤ u n ∧ (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1 := by
    filter_upwards [hδ, hu.eventually_ge_atTop 2] with n hn h2
    exact ⟨h2, hn.1, hn.2⟩
  have hQ : Tendsto (fun n => (Chebyshev.theta (Real.exp (u n))
      - Chebyshev.theta (Real.exp (u n - δ n))) / (Real.exp (u n) - Real.exp (u n - δ n)))
      atTop (nhds 1) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hbound : Tendsto (fun n => 2 * |(u n) ^ 2 * (Chebyshev.theta (Real.exp (u n))
        - Real.exp (u n)) / Real.exp (u n)| + 8 * |(u n - δ n) ^ 2
        * (Chebyshev.theta (Real.exp (u n - δ n)) - Real.exp (u n - δ n))
        / Real.exp (u n - δ n)|) atTop (nhds 0) := by
      have := (hga.abs.const_mul 2).add (hgb.abs.const_mul 8)
      simpa using this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev] with n hn
    obtain ⟨h1, h2, h3⟩ := hn
    have hδ0 : 0 ≤ δ n := le_trans (sq_nonneg _) h2
    obtain ⟨hN1, hN2⟩ := e768_count_bounds (u n) (δ n) hδ0
    rw [Real.norm_eq_abs]
    exact (e768_pointwise (u n) (δ n) _ _ _ h1 h2 h3 hN1 hN2).2.2
  have hr : Tendsto (fun n => u n / (u n - δ n)) atTop (nhds 1) := by
    have h0 : Tendsto (fun n => δ n / (u n - δ n)) atTop (nhds 0) := by
      refine squeeze_zero' ?_ ?_ hb.inv_tendsto_atTop
      · filter_upwards [hδ, hb.eventually_gt_atTop 0] with n hn hpos
        have : 0 ≤ δ n := le_trans (sq_nonneg _) hn.1
        positivity
      · filter_upwards [hδ, hb.eventually_gt_atTop 0] with n hn hpos
        simp only [Pi.inv_apply]
        rw [div_le_iff₀ hpos, inv_mul_cancel₀ hpos.ne']
        exact hn.2
    have h1 := h0.const_add 1
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hb.eventually_gt_atTop 0] with n hpos
    field_simp
    ring
  have hQr := hQ.mul hr
  rw [mul_one] at hQr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hQ hQr ?_ ?_
  · filter_upwards [hev] with n hn
    obtain ⟨h1, h2, h3⟩ := hn
    have hδ0 : 0 ≤ δ n := le_trans (sq_nonneg _) h2
    obtain ⟨hN1, hN2⟩ := e768_count_bounds (u n) (δ n) hδ0
    exact (e768_pointwise (u n) (δ n) _ _ _ h1 h2 h3 hN1 hN2).1
  · filter_upwards [hev] with n hn
    obtain ⟨h1, h2, h3⟩ := hn
    have hδ0 : 0 ≤ δ n := le_trans (sq_nonneg _) h2
    obtain ⟨hN1, hN2⟩ := e768_count_bounds (u n) (δ n) hδ0
    exact (e768_pointwise (u n) (δ n) _ _ _ h1 h2 h3 hN1 hN2).2.1
