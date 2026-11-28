import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1
import Mathlib

/-!
# Step H2 of the reduction RiemannHypothesis.lagarias_criterion.R1.H2.R1.H1.R1

For `0 < b < 1/2` and `ε > 0`, eventually in `x` (with `P = ⌊x⌋₊` and `n = lcmUpto P`):

  `-log (e^γ log θ(x) ∏_{p ≤ P} (1 - 1/p)) - ε x^(-b) ≤ log (σ(n)/n) - γ - log log log n`.

Proof (own formalization, only Mathlib is used):

* `n = ∏_{p ≤ P} p^k_p` with `k_p = Nat.log p P`, and by multiplicativity of `σ 1` and the
  geometric sum, `σ(n)/n · ∏_{p ≤ P} (1 - 1/p) = ∏_{p ≤ P} (1 - t_p)` with `t_p = p^-(k_p+1)`.
* Since `p^(k_p+1) > P ≥ x - 1` and `k_p ≥ 1`, one has `√x ≤ p^k_p`, hence `t_p ≤ 1/(p √x)`, and
  `t_p ≤ 1/4`. With `-log(1-t) ≤ 2t` and the harmonic bound `H_P ≤ 1 + log P`, the logarithm of
  the product is at least `-2 (1 + log x)/√x`.
* `log n = ψ(x)`, `θ(x) ≤ ψ(x) ≤ θ(x) + 2 √x log x` (Mathlib's Chebyshev bounds), and eventually
  `θ(x) ≥ x/4` (from `Chebyshev.theta_ge'` and `log x = o(√x)`). Then
  `log log ψ - log log θ ≤ (ψ - θ)/(θ log θ) ≤ 8 log x/√x`.
* Finally `ε x^(-b) = ε x^(1/2-b)/√x` and eventually `2 + 10 log x ≤ ε x^(1/2-b)`
  (since `log x = o(x^(1/2-b))`), which absorbs both losses.
-/

namespace OMA.Helpers

open Real Filter
open scoped ArithmeticFunction.sigma

/-- The divisor sum of `lcmUpto P` as a product over the primes up to `P`. -/
theorem sigma_lcmUpto (P : ℕ) :
    σ 1 (Nat.lcmUpto P) =
      ∏ p ∈ Nat.primesLE P, ∑ i ∈ Finset.range (Nat.log p P + 1), p ^ i := by
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
    (Nat.lcmUpto_ne_zero P), Nat.primeFactors_lcmUpto]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.factorization_lcmUpto P (Nat.prime_of_mem_primesLE hp)]
  simp

/-- Product formula for the abundancy of `lcmUpto P` times the Mertens product. -/
theorem abundancy_mul_mertens (P : ℕ) :
    ((σ 1 (Nat.lcmUpto P) : ℝ) / (Nat.lcmUpto P : ℝ)) * ∏ p ∈ Nat.primesLE P, (1 - 1/(p:ℝ)) =
      ∏ p ∈ Nat.primesLE P, (1 - 1/(p:ℝ)^(Nat.log p P + 1)) := by
  have hn : (Nat.lcmUpto P : ℝ) = ∏ p ∈ Nat.primesLE P, (p:ℝ) ^ (Nat.log p P) := by
    conv_lhs => rw [Nat.lcmUpto_eq_prod_pow_log]
    push_cast
    rfl
  rw [sigma_lcmUpto, hn]
  push_cast
  rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
  have hgeom := geom_sum_mul (p:ℝ) (Nat.log p P + 1)
  have hp0 : (p:ℝ) ≠ 0 := by positivity
  field_simp
  rw [hgeom]
  ring

/-- `-log (1 - t) ≤ 2 t` for `0 ≤ t ≤ 1/2`. -/
theorem neg_log_one_sub_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1/2) : -log (1 - t) ≤ 2 * t := by
  have hpos : 0 < 1 - t := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (1 - t)⁻¹ ≤ 1 + 2 * t := by
    rw [inv_le_iff_one_le_mul₀' hpos]
    nlinarith
  linarith

/-- `log b - log a ≤ (b - a) / a`. -/
theorem log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : log b - log a ≤ (b - a) / a := by
  rw [← Real.log_div hb.ne' ha.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hb ha)
  calc log (b / a) ≤ b / a - 1 := this
    _ = (b - a) / a := by field_simp

/-- The local factor bound: `p ^ (k+1) ≥ p * √x` and `p ^ (k+1) ≥ 4`. -/
theorem local_bound (P p : ℕ) (hp : p ∈ Nat.primesLE P) (x : ℝ) (hx0 : 0 < x)
    (hxP : x < P + 1) :
    1/(p:ℝ)^(Nat.log p P + 1) ≤ 1/(p:ℝ) * (1/√x) ∧ 1/(p:ℝ)^(Nat.log p P + 1) ≤ 1/4 := by
  have hp1 : 1 < p := Nat.one_lt_of_mem_primesLE hp
  have hpP : p ≤ P := Nat.le_of_mem_primesLE hp
  have hk : 1 ≤ Nat.log p P := Nat.log_pos hp1 hpP
  have hA : P < p ^ (Nat.log p P + 1) := Nat.lt_pow_succ_log_self hp1 P
  have hB : p ^ (Nat.log p P + 1) ≤ p ^ (2 * Nat.log p P) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hC : p ^ 2 ≤ p ^ (Nat.log p P + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
  have hxR : x ≤ ((p:ℝ) ^ (Nat.log p P)) ^ 2 := by
    have h1 : (P:ℝ) + 1 ≤ (p:ℝ) ^ (Nat.log p P + 1) := by exact_mod_cast hA
    have h2 : (p:ℝ) ^ (Nat.log p P + 1) ≤ (p:ℝ) ^ (2 * Nat.log p P) := by exact_mod_cast hB
    rw [← pow_mul, mul_comm]
    linarith
  have hsq : √x ≤ (p:ℝ) ^ (Nat.log p P) := (Real.sqrt_le_left (by positivity)).mpr hxR
  constructor
  · have hxpos : 0 < √x := Real.sqrt_pos.mpr hx0
    rw [one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    calc (p:ℝ) * √x ≤ (p:ℝ) * (p:ℝ) ^ (Nat.log p P) :=
          mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ p)
      _ = (p:ℝ) ^ (Nat.log p P + 1) := by ring
  · have hC' : (4:ℝ) ≤ (p:ℝ) ^ (Nat.log p P + 1) := by
      have : ((p ^ 2 : ℕ) : ℝ) ≤ ((p ^ (Nat.log p P + 1) : ℕ) : ℝ) := by exact_mod_cast hC
      push_cast at this
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

/-- Lower bound for the logarithm of the product of the local factors. -/
theorem log_local_prod_ge (P : ℕ) (x : ℝ) (hx1 : 1 ≤ x) (hPx : (P:ℝ) ≤ x) (hxP : x < P + 1) :
    -2 * ((1 + log x) * (1/√x)) ≤
      log (∏ p ∈ Nat.primesLE P, (1 - 1/(p:ℝ)^(Nat.log p P + 1))) := by
  have hx0 : 0 < x := by linarith
  rw [Real.log_prod (fun p hp => by
    have := (local_bound P p hp x hx0 hxP).2
    linarith)]
  have hterm : ∀ p ∈ Nat.primesLE P,
      -2 * (1/(p:ℝ) * (1/√x)) ≤ log (1 - 1/(p:ℝ)^(Nat.log p P + 1)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := local_bound P p hp x hx0 hxP
    have h0 : 0 ≤ 1/(p:ℝ)^(Nat.log p P + 1) := by positivity
    have := neg_log_one_sub_le h0 (by linarith)
    linarith
  have hsum := Finset.sum_le_sum hterm
  have hfac : ∑ p ∈ Nat.primesLE P, -2 * (1/(p:ℝ) * (1/√x)) =
      -2 * ((∑ p ∈ Nat.primesLE P, 1/(p:ℝ)) * (1/√x)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hfac] at hsum
  have hsub : ∑ p ∈ Nat.primesLE P, 1/(p:ℝ) ≤ ∑ i ∈ Finset.Icc 1 P, (i:ℝ)⁻¹ := by
    simp only [one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_Icc]
      exact ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
    · intro i _ _
      positivity
  have hH : ∑ i ∈ Finset.Icc 1 P, (i:ℝ)⁻¹ ≤ 1 + log P := by
    have := harmonic_le_one_add_log P
    simpa [harmonic_eq_sum_Icc] using this
  have hlogP : log P ≤ log x := by
    rcases Nat.eq_zero_or_pos P with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg hx1
    · exact Real.log_le_log (by exact_mod_cast h) hPx
  have hsx : 0 ≤ 1/√x := by positivity
  have : (∑ p ∈ Nat.primesLE P, 1/(p:ℝ)) * (1/√x) ≤ (1 + log x) * (1/√x) :=
    mul_le_mul_of_nonneg_right (by linarith) hsx
  linarith

/-- The gap between the iterated logarithms of `ψ` and `θ`. -/
theorem loglog_gap {θ ψ x : ℝ} (hx : 1 ≤ x) (hθ : x/4 ≤ θ) (hθ1 : 1 ≤ log θ) (hψθ : θ ≤ ψ)
    (hgap : ψ - θ ≤ 2 * √x * log x) :
    log (log ψ) - log (log θ) ≤ 8 * (log x * (1/√x)) := by
  have hx0 : 0 < x := by linarith
  have hθ0 : 0 < θ := by linarith
  have hψ0 : 0 < ψ := by linarith
  have hlψ : log θ ≤ log ψ := Real.log_le_log hθ0 hψθ
  have h1 := log_sub_log_le (by linarith : 0 < log θ) (by linarith : 0 < log ψ)
  have h2 := log_sub_log_le hθ0 hψ0
  have h3 : (log ψ - log θ) / log θ ≤ log ψ - log θ := div_le_self (by linarith) hθ1
  have hlx : 0 ≤ log x := Real.log_nonneg hx
  have h4 : (ψ - θ) / θ ≤ (2 * √x * log x) / (x/4) :=
    div_le_div₀ (by positivity) hgap (by positivity) hθ
  have h5 : (2 * √x * log x) / (x/4) = 8 * (log x * (1/√x)) := by
    have hs := Real.mul_self_sqrt hx0.le
    have hsp : 0 < √x := Real.sqrt_pos.mpr hx0
    field_simp
    rw [Real.sq_sqrt hx0.le]
    ring
  linarith

/-- The pointwise inequality, for a real `x ≥ 16` with `θ x ≥ x / 4` and
`2 + 10 log x ≤ ε x ^ (1/2 - b)`. -/
theorem pointwise (b ε x : ℝ) (hx : 16 ≤ x) (hθ : x/4 ≤ Chebyshev.theta x)
    (hE : 2 + 10 * log x ≤ ε * x ^ (1/2 - b)) :
    -(log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ)))) - ε*x^(-b) ≤
    log ((σ 1 (Nat.lcmUpto ⌊x⌋₊) : ℝ)/(Nat.lcmUpto ⌊x⌋₊)) - eulerMascheroniConstant -
      log (log (log (Nat.lcmUpto ⌊x⌋₊ : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have hPx : (⌊x⌋₊:ℝ) ≤ x := Nat.floor_le hx0.le
  have hxP : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hψ : log (Nat.lcmUpto ⌊x⌋₊ : ℝ) = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  rw [hψ]
  have hψθ : Chebyshev.theta x ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
  have hgap : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * √x * log x :=
    Chebyshev.psi_sub_theta_le (by linarith)
  have hθ4 : 4 ≤ Chebyshev.theta x := by linarith
  have hθ1 : 1 ≤ log (Chebyshev.theta x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hM : 0 < ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  have hS : 0 < (σ 1 (Nat.lcmUpto ⌊x⌋₊) : ℝ)/(Nat.lcmUpto ⌊x⌋₊) := by
    apply div_pos
    · exact_mod_cast ArithmeticFunction.sigma_pos 1 _ (Nat.lcmUpto_ne_zero _)
    · exact_mod_cast Nat.lcmUpto_pos _
  have hQ := log_local_prod_ge ⌊x⌋₊ x (by linarith) hPx hxP
  rw [← abundancy_mul_mertens, Real.log_mul hS.ne' hM.ne'] at hQ
  have hlog : log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) =
      eulerMascheroniConstant + log (log (Chebyshev.theta x)) +
        log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) := by
    rw [Real.log_mul (by positivity) hM.ne', Real.log_mul (by positivity) (by linarith),
      Real.log_exp]
  rw [hlog]
  have hG := loglog_gap (by linarith) hθ hθ1 hψθ hgap
  have hpow : ε * x ^ (1/2 - b) * (1/√x) = ε * x ^ (-b) := by
    have hsp : 0 < √x := Real.sqrt_pos.mpr hx0
    rw [Real.sqrt_eq_rpow, sub_eq_add_neg, Real.rpow_add hx0]
    field_simp
  have hE' : (2 + 10 * log x) * (1/√x) ≤ ε * x ^ (-b) := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_right hE (by positivity)
  linarith

end OMA.Helpers

open Real Filter
open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1.H2 := by
  intro b hb0 hb1 ε hε
  have ha : 0 < 1/2 - b := by linarith
  have E1 : ∀ᶠ x : ℝ in atTop, 2 + 10 * log x ≤ ε * x ^ (1/2 - b) := by
    have hlo := (isLittleO_log_rpow_atTop ha).def (c := ε/20) (by positivity)
    have htend := (tendsto_rpow_atTop ha).eventually_ge_atTop (4/ε)
    filter_upwards [hlo, htend, eventually_ge_atTop (1:ℝ)] with x hlx hT hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      at hlx
    have hl : log x ≤ ε/20 * x^(1/2-b) := (le_abs_self _).trans hlx
    have h2 : 2 ≤ ε / 2 * x^(1/2-b) := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : (0:ℝ) ≤ ε/2)
      calc (2:ℝ) = ε/2 * (4/ε) := by field_simp; norm_num
        _ ≤ _ := this
    linarith
  have E2 : ∀ᶠ x : ℝ in atTop, x / 4 ≤ Chebyshev.theta x := by
    have hlo := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).def
      (c := 1/20) (by norm_num)
    filter_upwards [hlo, eventually_ge_atTop (16:ℝ)] with x hlx hx
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg x)] at hlx
    have hl : log x ≤ 1/20 * √x := (le_abs_self _).trans hlx
    have hth := Chebyshev.theta_ge' (x := x) (by linarith)
    have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
    have hs1 : √x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
    have hlog2 : log (x + 2) ≤ log 2 + log x := by
      rw [← Real.log_mul (by norm_num) hx0.ne']
      exact Real.log_le_log (by linarith) (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hlogx0 : 0 ≤ log x := Real.log_nonneg (by linarith)
    have hprod : √x * log x ≤ √x * (1/20 * √x) :=
      mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg x)
    have hprod2 : (x - 1) * 0.6931471803 ≤ (x - 1) * log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by linarith)
    nlinarith
  filter_upwards [E1, E2, eventually_ge_atTop (16:ℝ)] with x h1 h2 h3
  exact OMA.Helpers.pointwise b ε x h3 h2 h1
