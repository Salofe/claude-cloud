import OMAStatements.S_oeis_a088500
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a088500 MeasureTheory Set

/-- The integrand `(2x)_n (1 - t)^(-(2x + n)) e^(-x)`, written with `exp` and `log`. -/
noncomputable def a088500_F (n : ℕ) (t x : ℝ) : ℝ :=
  pochhammer (2 * x) n * Real.exp (-(2 * x + n) * Real.log (1 - t)) * Real.exp (-x)

/-- The dominating function. -/
noncomputable def a088500_B (n : ℕ) (x : ℝ) : ℝ :=
  7 ^ n * n.factorial * Real.exp (2 * n / 7) * Real.exp (-(3 / 7) * x)

theorem a088500_poch_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pochhammer (2 * x) n :=
  Finset.prod_nonneg fun k _ => by positivity

theorem a088500_poch_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : pochhammer (2 * x) n ≤ (2 * x + n) ^ n := by
  unfold pochhammer
  calc ∏ k ∈ Finset.range n, (2 * x + (k : ℝ)) ≤ ∏ _k ∈ Finset.range n, (2 * x + (n : ℝ)) := by
        apply Finset.prod_le_prod
        · intro k _; positivity
        · intro k hk
          have : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
          linarith
    _ = (2 * x + n) ^ n := by rw [Finset.prod_const, Finset.card_range]

theorem a088500_bound (n : ℕ) {t x : ℝ} (ht : t ≤ 1 / 8) (hx : 0 ≤ x) :
    ‖a088500_F n t x‖ ≤ a088500_B n x := by
  have hP := a088500_poch_nonneg n hx
  have hF : 0 ≤ a088500_F n t x := by unfold a088500_F; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hF]
  have h1t : (7 : ℝ) / 8 ≤ 1 - t := by linarith
  have hlog : -(1 / 7 : ℝ) ≤ Real.log (1 - t) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - t by linarith)
    have hinv : (1 - t)⁻¹ ≤ 8 / 7 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hy : 0 ≤ 2 * x + n := by positivity
  have hE : Real.exp (-(2 * x + n) * Real.log (1 - t)) ≤ Real.exp ((2 * x + n) / 7) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : (2 * x + n) ^ n ≤ 7 ^ n * n.factorial * Real.exp ((2 * x + n) / 7) := by
    have h := Real.pow_div_factorial_le_exp ((2 * x + n) / 7) (by positivity) n
    rw [div_le_iff₀ (by positivity), div_pow] at h
    have h7 : (0 : ℝ) < 7 ^ n := by positivity
    rw [div_le_iff₀ h7] at h
    calc (2 * x + n) ^ n ≤ Real.exp ((2 * x + n) / 7) * n.factorial * 7 ^ n := h
      _ = 7 ^ n * n.factorial * Real.exp ((2 * x + n) / 7) := by ring
  unfold a088500_F a088500_B
  calc pochhammer (2 * x) n * Real.exp (-(2 * x + n) * Real.log (1 - t)) * Real.exp (-x)
      ≤ (7 ^ n * n.factorial * Real.exp ((2 * x + n) / 7)) * Real.exp ((2 * x + n) / 7) *
          Real.exp (-x) := by
        gcongr
        exact (a088500_poch_le n hx).trans hpow
    _ = 7 ^ n * n.factorial * Real.exp (2 * n / 7) * Real.exp (-(3 / 7) * x) := by
        rw [mul_assoc (7 ^ n * (n.factorial : ℝ)), mul_assoc (7 ^ n * (n.factorial : ℝ)),
          ← Real.exp_add, ← Real.exp_add, mul_assoc (7 ^ n * (n.factorial : ℝ)), ← Real.exp_add]
        congr 2
        ring

theorem a088500_F_cont (n : ℕ) (t : ℝ) : Continuous (a088500_F n t) := by
  unfold a088500_F pochhammer
  fun_prop

theorem a088500_hasDeriv (n : ℕ) (x : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun s => a088500_F n s x) (a088500_F (n + 1) t x) t := by
  have h1 : (1 - t) ≠ 0 := by linarith
  have hL : HasDerivAt (fun s => Real.log (1 - s)) ((-1) / (1 - t)) t := by
    have := ((hasDerivAt_id t).const_sub 1).log h1
    simpa using this
  have hE := ((hL.const_mul (-(2 * x + n))).exp).const_mul (pochhammer (2 * x) n) |>.mul_const
    (Real.exp (-x))
  have hsplit : Real.exp (-(2 * x + ((n + 1 : ℕ) : ℝ)) * Real.log (1 - t)) =
      Real.exp (-(2 * x + n) * Real.log (1 - t)) * (1 - t)⁻¹ := by
    rw [show -(2 * x + ((n + 1 : ℕ) : ℝ)) * Real.log (1 - t) =
      -(2 * x + n) * Real.log (1 - t) + -Real.log (1 - t) by push_cast; ring, Real.exp_add,
      Real.exp_neg, Real.exp_log (by linarith)]
  have key : pochhammer (2 * x) n * (Real.exp (-(2 * x + n) * Real.log (1 - t)) *
      (-(2 * x + n) * ((-1) / (1 - t)))) * Real.exp (-x) = a088500_F (n + 1) t x := by
    unfold a088500_F
    rw [hsplit]
    unfold pochhammer
    rw [Finset.prod_range_succ]
    field_simp
  exact hE.congr_deriv key


theorem a088500_B_int (n : ℕ) : Integrable (a088500_B n) (volume.restrict (Ioi 0)) := by
  unfold a088500_B
  exact (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 3 / 7)).const_mul _

theorem a088500_F_int (n : ℕ) {t : ℝ} (ht : t ≤ 1 / 8) :
    Integrable (a088500_F n t) (volume.restrict (Ioi 0)) := by
  refine (a088500_B_int n).mono' (a088500_F_cont n t).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall fun x hx => a088500_bound n ht (le_of_lt hx)

/-- The parametric integral. -/
noncomputable def a088500_h (n : ℕ) (t : ℝ) : ℝ := ∫ x in Ioi 0, a088500_F n t x

theorem a088500_h_deriv (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)) :
    HasDerivAt (a088500_h n) (a088500_h (n + 1) t) t := by
  have hs : Ioo (-(1 / 8) : ℝ) (1 / 8) ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := a088500_F n) (F' := a088500_F (n + 1)) (bound := a088500_B (n + 1)) hs
    (Filter.Eventually.of_forall fun s => (a088500_F_cont n s).aestronglyMeasurable)
    (a088500_F_int n ht.2.le) (a088500_F_cont (n + 1) t).aestronglyMeasurable
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall fun x hx s hsm =>
        a088500_bound (n + 1) hsm.2.le (le_of_lt hx))
    (a088500_B_int (n + 1))
    (Filter.Eventually.of_forall fun x s hsm => a088500_hasDeriv n x (by linarith [hsm.2]))
  exact this.2

theorem a088500_h_zero {t : ℝ} (ht : t ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)) :
    a088500_h 0 t = egf t := by
  have hlog : -(1 / 7 : ℝ) ≤ Real.log (1 - t) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - t by linarith [ht.2])
    have hinv : (1 - t)⁻¹ ≤ 8 / 7 := by
      rw [inv_le_comm₀ (by linarith [ht.2]) (by norm_num)]; linarith [ht.2]
    linarith
  have hpos : 0 < 1 + 2 * Real.log (1 - t) := by linarith
  have e : a088500_F 0 t = fun x => Real.exp (-(1 + 2 * Real.log (1 - t)) * x) := by
    funext x
    unfold a088500_F pochhammer
    rw [Finset.prod_range_zero, one_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold a088500_h
  rw [e, integral_exp_mul_Ioi (by linarith) 0, egf]
  simp only [mul_zero, Real.exp_zero]
  field_simp

theorem a088500_iter (n : ℕ) : ∀ t ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
    iteratedDeriv n egf t = a088500_h n t := by
  induction n with
  | zero =>
    intro t ht
    rw [iteratedDeriv_zero, a088500_h_zero ht]
  | succ n ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n egf =ᶠ[nhds t] a088500_h n :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun y hy => ih y hy
    rw [hev.deriv_eq, (a088500_h_deriv n ht).deriv]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a088500.main := by
  intro n
  rw [OMA.S_oeis_a088500.a, OMA.Helpers.a088500_iter n 0 (by norm_num), OMA.Helpers.a088500_h]
  congr 1
  funext x
  unfold OMA.Helpers.a088500_F
  rw [sub_zero, Real.log_one, mul_zero, Real.exp_zero, mul_one, Real.exp_neg, div_eq_mul_inv]
