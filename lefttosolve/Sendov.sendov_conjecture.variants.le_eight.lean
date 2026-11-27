import FormalConjectures.Wikipedia.Sendov

/-!
Sendov conjecture for polynomials of degree at most 8.

Self-contained formalization following the mathematics of the elementary proof of
Sendov conjecture by L. Mazur, as digested and simplified by T. Tao in the blog post
A digestion of the proof of Sendov conjecture (What is new, 12 August 2026):
polar identity and polar inequality, origin identities, defect lemma, origin inequality.
For degree at most 5 the polar inequality alone suffices; for degrees 6, 7, 8 the two
inequalities are combined at the test point x = (1 + 3a)/4 and the resulting one-variable
polynomial inequalities are certified with explicit Bernstein expansions.
The a = 1 case uses the Meir-Sharma identity, the a = 0 case the value of the derivative at 0.
-/

open Polynomial Finset

namespace OMA.Helpers.SendovLE8

lemma bern_aux (μ d : ℝ) (k : ℕ) (hμ : 0 ≤ μ) (hd : 0 ≤ μ + d) :
    μ ^ (k + 1) + (k + 1) * μ ^ k * d ≤ (μ + d) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ μ ^ k * d ^ 2 := mul_nonneg (pow_nonneg hμ k) (sq_nonneg d)
    have h2 : (μ + d) * (μ ^ (k + 1) + (k + 1) * μ ^ k * d) ≤ (μ + d) * (μ + d) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left ih hd
    have h3 : (μ + d) * (μ ^ (k + 1) + (k + 1) * μ ^ k * d)
        = μ ^ (k + 1 + 1) + ((k + 1 : ℕ) + 1 : ℝ) * μ ^ (k + 1) * d + (k + 1) * (μ ^ k * d ^ 2) := by
      push_cast; ring
    have h4 : (μ + d) * (μ + d) ^ (k + 1) = (μ + d) ^ (k + 1 + 1) := by ring
    nlinarith

lemma sum_prod_erase_insert {ι : Type*} [DecidableEq ι] (k : ι) (s : Finset ι) (hk : k ∉ s)
    (f r : ι → ℝ) :
    ∑ i ∈ insert k s, f i * ∏ j ∈ (insert k s).erase i, r j
      = f k * ∏ j ∈ s, r j + r k * ∑ i ∈ s, f i * ∏ j ∈ s.erase i, r j := by
  rw [sum_insert hk, erase_insert hk, mul_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hki : k ≠ i := fun h => hk (h ▸ hi)
  rw [erase_insert_of_ne hki, prod_insert (fun h => hk (mem_of_mem_erase h))]
  ring

lemma amgm {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ∏ i ∈ s, r i ≤ ((∑ i ∈ s, r i) / #s) ^ #s := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hrk : 0 ≤ r k := hr k (mem_insert_self k s)
    have hrs : ∀ i ∈ s, 0 ≤ r i := fun i hi => hr i (mem_insert_of_mem hi)
    have ih := ih hrs
    rw [prod_insert hk, sum_insert hk, card_insert_of_notMem hk]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp
    have hpos : 0 < #s := card_pos.mpr hs
    set N := #s with hN
    set S := ∑ i ∈ s, r i with hS
    have hS0 : 0 ≤ S := sum_nonneg hrs
    have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
    set μ := S / N with hμ
    have hμ0 : 0 ≤ μ := div_nonneg hS0 hNr.le
    have key := bern_aux μ ((r k - μ) / (N + 1)) N hμ0 (by
      have : μ + (r k - μ) / (N + 1) = (N * μ + r k) / (N + 1) := by field_simp; ring
      rw [this]; positivity)
    have e1 : μ + (r k - μ) / (N + 1) = (r k + S) / ((N + 1 : ℕ) : ℝ) := by
      rw [hμ]; push_cast; field_simp; ring
    have e2 : μ ^ (N + 1) + (N + 1) * μ ^ N * ((r k - μ) / (N + 1)) = μ ^ N * r k := by
      field_simp; ring
    rw [e1, e2] at key
    calc r k * ∏ i ∈ s, r i ≤ r k * μ ^ N := mul_le_mul_of_nonneg_left ih hrk
      _ = μ ^ N * r k := by ring
      _ ≤ _ := key

lemma maclaurin {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ∑ i ∈ s, ∏ j ∈ s.erase i, r j ≤ #s * ((∑ i ∈ s, r i) / #s) ^ (#s - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hrk : 0 ≤ r k := hr k (mem_insert_self k s)
    have hrs : ∀ i ∈ s, 0 ≤ r i := fun i hi => hr i (mem_insert_of_mem hi)
    have ih := ih hrs
    have hsplit := sum_prod_erase_insert k s hk (fun _ => (1 : ℝ)) r
    simp only [one_mul] at hsplit
    rw [hsplit, sum_insert hk, card_insert_of_notMem hk, Nat.add_sub_cancel]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp
    have hP := amgm s r hrs
    obtain ⟨M, hM⟩ : ∃ M, #s = M + 1 := ⟨#s - 1, by have := card_pos.mpr hs; omega⟩
    rw [hM] at ih hP ⊢
    simp only [Nat.add_sub_cancel] at ih
    set S := ∑ i ∈ s, r i with hS
    have hS0 : 0 ≤ S := sum_nonneg hrs
    have hNr : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    set μ := S / ((M + 1 : ℕ) : ℝ) with hμ
    have hμ0 : 0 ≤ μ := div_nonneg hS0 hNr.le
    have key := bern_aux μ ((r k - μ) / (M + 2)) M hμ0 (by
      have : μ + (r k - μ) / (M + 2) = ((M + 1) * μ + r k) / (M + 2) := by field_simp; ring
      rw [this]; positivity)
    have e1 : μ + (r k - μ) / (M + 2) = (r k + S) / (((M + 1 + 1 : ℕ)) : ℝ) := by
      rw [hμ]; push_cast; field_simp; ring
    rw [e1] at key
    have hP' : ∏ i ∈ s, r i ≤ μ * μ ^ M := by
      rw [← pow_succ']
      exact hP
    calc ∏ i ∈ s, r i + r k * ∑ i ∈ s, ∏ j ∈ s.erase i, r j
        ≤ μ * μ ^ M + r k * (((M + 1 : ℕ) : ℝ) * μ ^ M) := by gcongr
      _ = (M + 2) * (μ ^ (M + 1) + (M + 1) * μ ^ M * ((r k - μ) / (M + 2))) := by
        push_cast; field_simp; ring
      _ ≤ (M + 2) * ((r k + S) / (((M + 1 + 1 : ℕ)) : ℝ)) ^ (M + 1) := by
        gcongr
      _ = _ := by push_cast; ring

lemma defect {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ) (hr0 : ∀ i ∈ s, 0 ≤ r i)
    (hr1 : ∀ i ∈ s, r i ≤ 1) :
    ∑ i ∈ s, (1 - r i ^ 2) * ∏ j ∈ s.erase i, r j ≤ 1 - (∏ i ∈ s, r i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hrk0 : 0 ≤ r k := hr0 k (mem_insert_self k s)
    have hrk1 : r k ≤ 1 := hr1 k (mem_insert_self k s)
    have hrs0 : ∀ i ∈ s, 0 ≤ r i := fun i hi => hr0 i (mem_insert_of_mem hi)
    have hrs1 : ∀ i ∈ s, r i ≤ 1 := fun i hi => hr1 i (mem_insert_of_mem hi)
    have ih := ih hrs0 hrs1
    rw [sum_prod_erase_insert k s hk, prod_insert hk]
    set P := ∏ i ∈ s, r i
    have hP0 : 0 ≤ P := prod_nonneg hrs0
    have hP1 : P ≤ 1 := prod_le_one hrs0 hrs1
    have h1 : r k * ∑ i ∈ s, (1 - r i ^ 2) * ∏ j ∈ s.erase i, r j ≤ r k * (1 - P ^ 2) :=
      mul_le_mul_of_nonneg_left ih hrk0
    have h2 : 0 ≤ (1 - r k) * (1 - P) * (1 - r k * P) := by
      have : 0 ≤ 1 - r k * P := by nlinarith
      have : 0 ≤ (1 - r k) * (1 - P) := mul_nonneg (by linarith) (by linarith)
      positivity
    nlinarith

lemma poly_ftc (P : ℂ[X]) (u v : ℂ) :
    P.eval v - P.eval u = (v - u) * ∫ t in (0:ℝ)..1, (derivative P).eval (u + t * (v - u)) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => P.eval (u + (s : ℂ) * (v - u)))
      ((derivative P).eval (u + t * (v - u)) * (v - u)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => u + (s : ℂ) * (v - u)) (v - u) t := by
      have := ((hasDerivAt_id t).ofReal_comp).mul_const (v - u)
      simpa using this.const_add u
    exact (P.hasDerivAt (u + (t : ℂ) * (v - u))).comp t h1
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hd t) (by
      apply Continuous.intervalIntegrable
      exact ((Polynomial.continuous _).comp (by fun_prop)).mul continuous_const)
  rw [intervalIntegral.integral_mul_const] at hint
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero] at hint
  have e : u + (v - u) = v := by ring
  rw [e] at hint
  rw [← hint]
  ring

lemma eval_prod_X_sub_C {m : ℕ} (z : Fin m → ℂ) (y : ℂ) :
    (∏ i, (X - C (z i))).eval y = ∏ i, (y - z i) := by
  simp [eval_prod]

lemma deriv_prod_X_sub_C {m : ℕ} (z : Fin m → ℂ) :
    derivative (∏ i, (X - C (z i))) = ∑ i, ∏ j ∈ univ.erase i, (X - C (z j)) := by
  rw [derivative_prod_finset]
  simp

lemma eval_deriv_prod_X_sub_C {m : ℕ} (z : Fin m → ℂ) (y : ℂ) :
    (derivative (∏ i, (X - C (z i)))).eval y = ∑ i, ∏ j ∈ univ.erase i, (y - z j) := by
  rw [deriv_prod_X_sub_C]
  simp [eval_finsetSum, eval_prod]

section core
variable {m : ℕ} {a : ℝ} {z ζ : Fin m → ℂ}

/-- the basic relation -/
lemma rel1 (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) :
    (∏ i, (X - C (z i))) + (X - C (a : ℂ)) * derivative (∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i)) := by
  rw [← hder, derivative_mul]
  simp

lemma eval_g_at_a (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) :
    ∏ i, ((a : ℂ) - z i) = ((m : ℂ) + 1) * ∏ i, ((a : ℂ) - ζ i) := by
  have := congrArg (Polynomial.eval (a : ℂ)) (rel1 hder)
  simpa [eval_prod] using this

lemma eval_at_zero (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) :
    ∏ i, (-z i) - (a : ℂ) * ∑ i, ∏ j ∈ univ.erase i, (-z j)
      = ((m : ℂ) + 1) * ∏ i, (-ζ i) := by
  have := congrArg (Polynomial.eval (0 : ℂ)) (rel1 hder)
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_prod_X_sub_C,
    eval_deriv_prod_X_sub_C, zero_sub] at this
  rw [← this]
  ring

lemma g_eval_integral (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) (v : ℂ) (hv : v ≠ (a : ℂ)) :
    ∏ i, (v - z i) = ((m : ℂ) + 1) *
      ∫ t in (0:ℝ)..1, ∏ i, ((a : ℂ) - ζ i + t * (v - a)) := by
  have h := poly_ftc ((X - C (a : ℂ)) * ∏ i, (X - C (z i))) (a : ℂ) v
  rw [hder] at h
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero, eval_prod] at h
  have hv' : v - (a : ℂ) ≠ 0 := sub_ne_zero.mpr hv
  rw [intervalIntegral.integral_const_mul] at h
  have h2 : (∫ t in (0:ℝ)..1, ∏ i, ((a : ℂ) + t * (v - a) - ζ i))
      = ∫ t in (0:ℝ)..1, ∏ i, ((a : ℂ) - ζ i + t * (v - a)) := by
    congr 1; ext t; congr 1; ext i; ring
  rw [← h2]
  exact mul_left_cancel₀ hv' h

lemma centroid (hm : 0 < m) (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) :
    (m : ℂ) * ((a : ℂ) + ∑ i, z i) = ((m : ℂ) + 1) * ∑ i, ζ i := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hc := congrArg (fun p => Polynomial.coeff p k) hder
  rw [coeff_derivative, coeff_C_mul] at hc
  have hz := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin (k+1))) z (by simp)
  have hζ := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin (k+1))) ζ (by simp)
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel] at hz hζ
  have hmon : (∏ i, (X - C (z i))).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)
  have hdeg : (∏ i, (X - C (z i))).natDegree = k + 1 := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)]
    simp
  have hlead : (∏ i, (X - C (z i))).coeff (k + 1) = 1 := by
    have h := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at h
  rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, hz, hlead, hζ] at hc
  push_cast at hc ⊢
  linear_combination -hc

lemma second_deriv_at_a (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) :
    2 * ∑ i, ∏ j ∈ univ.erase i, ((a : ℂ) - z j)
      = ((m : ℂ) + 1) * ∑ i, ∏ j ∈ univ.erase i, ((a : ℂ) - ζ j) := by
  have h := congrArg derivative (rel1 hder)
  rw [derivative_add, derivative_mul, derivative_C_mul] at h
  have := congrArg (Polynomial.eval (a : ℂ)) h
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero,
    derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_deriv_prod_X_sub_C] at this
  rw [← this]
  ring

end core

lemma norm_sub_le_norm_one_sub_mul (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ) - z‖ ≤ ‖1 - (a : ℂ) * z‖ := by
  have hz2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  have h1 : ‖(a:ℂ) - z‖ ^ 2 ≤ ‖1 - (a:ℂ) * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, zero_mul, sub_zero, zero_sub]
    nlinarith [mul_nonneg (sub_nonneg.2 (pow_le_one₀ ha0 ha1 : a ^ 2 ≤ 1)) (sub_nonneg.2 hz2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

lemma polar_main {m : ℕ} {a : ℝ} {z ζ : Fin m → ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hζ : ∀ i, 1 < ‖(a : ℂ) - ζ i‖)
    (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) :
    1 ≤ ∫ t in (0:ℝ)..1, ∏ i, ‖(a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * ((a : ℂ) - ζ i)⁻¹‖ := by
  set w : Fin m → ℂ := fun i => (a : ℂ) - ζ i with hw
  have hwpos : ∀ i, 0 < ‖w i‖ := fun i => lt_trans one_pos (hζ i)
  have hw0 : ∀ i, w i ≠ 0 := fun i => norm_pos_iff.mp (hwpos i)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hv : ((a : ℂ)⁻¹) ≠ (a : ℂ) := by
    intro h
    have h2 : (a : ℂ) * (a : ℂ)⁻¹ = 1 := mul_inv_cancel₀ haC
    rw [h] at h2
    have h3 : a * a = 1 := by exact_mod_cast h2
    nlinarith
  have h1 := g_eval_integral hder ((a : ℂ)⁻¹) hv
  have h2 := eval_g_at_a hder
  have hn : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hnC : ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 := by
    have : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  -- pointwise identity
  have hpt : ∀ t : ℝ, a ^ m * ‖∏ i, (w i + (t : ℂ) * ((a : ℂ)⁻¹ - a))‖
      = (∏ i, ‖w i‖) * ∏ i, ‖(a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * (w i)⁻¹‖ := by
    intro t
    rw [norm_prod, ← prod_mul_distrib]
    have : a ^ m = ∏ _i : Fin m, a := by simp
    rw [this, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    have e : (a : ℂ) * (w i + (t : ℂ) * ((a : ℂ)⁻¹ - a))
        = w i * ((a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * (w i)⁻¹) := by
      have hwi := hw0 i
      push_cast
      field_simp
    have := congrArg norm e
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0] at this
    exact this
  -- the main chain
  have hchain : ((m : ℝ) + 1) * ∏ i, ‖w i‖ ≤
      ((m : ℝ) + 1) * ((∏ i, ‖w i‖) *
        ∫ t in (0:ℝ)..1, ∏ i, ‖(a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * (w i)⁻¹‖) := by
    calc ((m : ℝ) + 1) * ∏ i, ‖w i‖ = ‖∏ i, ((a : ℂ) - z i)‖ := by
          rw [h2, norm_mul, hnC, norm_prod]
      _ = ∏ i, ‖(a : ℂ) - z i‖ := norm_prod _ _
      _ ≤ ∏ i, ‖1 - (a : ℂ) * z i‖ :=
          prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => norm_sub_le_norm_one_sub_mul a ha0.le ha1.le (z i) (hz i))
      _ = a ^ m * ‖∏ i, ((a : ℂ)⁻¹ - z i)‖ := by
          rw [norm_prod]
          have : a ^ m = ∏ _i : Fin m, a := by simp
          rw [this, ← prod_mul_distrib]
          refine prod_congr rfl fun i _ => ?_
          have e : (1 - (a : ℂ) * z i) = (a : ℂ) * ((a : ℂ)⁻¹ - z i) := by
            field_simp
          rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
      _ = a ^ m * (((m : ℝ) + 1) *
            ‖∫ t in (0:ℝ)..1, ∏ i, (w i + (t : ℂ) * ((a : ℂ)⁻¹ - a))‖) := by
          rw [h1, norm_mul, hnC]
      _ ≤ a ^ m * (((m : ℝ) + 1) *
            ∫ t in (0:ℝ)..1, ‖∏ i, (w i + (t : ℂ) * ((a : ℂ)⁻¹ - a))‖) := by
          gcongr
          exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ = ((m : ℝ) + 1) *
            ∫ t in (0:ℝ)..1, a ^ m * ‖∏ i, (w i + (t : ℂ) * ((a : ℂ)⁻¹ - a))‖ := by
          rw [intervalIntegral.integral_const_mul]; ring
      _ = ((m : ℝ) + 1) * ∫ t in (0:ℝ)..1, (∏ i, ‖w i‖) *
            ∏ i, ‖(a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * (w i)⁻¹‖ := by
          congr 1
          exact intervalIntegral.integral_congr fun t _ => hpt t
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hW : 0 < ((m : ℝ) + 1) * ∏ i, ‖w i‖ := mul_pos hn (prod_pos fun i _ => hwpos i)
  have := hchain
  rw [← mul_assoc] at this
  have h3 : (((m : ℝ) + 1) * ∏ i, ‖w i‖) * 1 ≤ (((m : ℝ) + 1) * ∏ i, ‖w i‖) *
      ∫ t in (0:ℝ)..1, ∏ i, ‖(a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * (w i)⁻¹‖ := by
    rw [mul_one]; exact this
  exact le_of_mul_le_mul_left h3 hW

lemma polar_amgm {m : ℕ} (hm : 0 < m) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (q : Fin m → ℂ) (hq : ∀ i, ‖q i‖ ≤ 1) :
    (∏ i, ‖(a : ℂ) + (c : ℂ) * q i‖) ^ 2 ≤
      (a ^ 2 + 2 * a * c * ((∑ i, (q i).re) / m) + c ^ 2) ^ m := by
  rw [← prod_pow]
  have hr : ∀ i ∈ (univ : Finset (Fin m)), 0 ≤ ‖(a : ℂ) + (c : ℂ) * q i‖ ^ 2 :=
    fun i _ => sq_nonneg _
  have h1 := amgm univ (fun i => ‖(a : ℂ) + (c : ℂ) * q i‖ ^ 2) hr
  simp only [card_univ, Fintype.card_fin] at h1
  refine h1.trans ?_
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  apply pow_le_pow_left₀ (div_nonneg (sum_nonneg fun i _ => sq_nonneg _) hmr.le)
  rw [div_le_iff₀ hmr]
  have hpt : ∀ i, ‖(a : ℂ) + (c : ℂ) * q i‖ ^ 2 ≤ a ^ 2 + 2 * a * c * (q i).re + c ^ 2 := by
    intro i
    have hq2 : (q i).re ^ 2 + (q i).im ^ 2 ≤ 1 := by
      have h := Complex.sq_norm (q i)
      rw [Complex.normSq_apply] at h
      nlinarith [norm_nonneg (q i), hq i]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, zero_mul, sub_zero, zero_add]
    nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.2 hq2)]
  calc ∑ i, ‖(a : ℂ) + (c : ℂ) * q i‖ ^ 2 ≤ ∑ i, (a ^ 2 + 2 * a * c * (q i).re + c ^ 2) :=
        sum_le_sum fun i _ => hpt i
    _ = (a ^ 2 + 2 * a * c * ((∑ i, (q i).re) / m) + c ^ 2) * m := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

lemma polar_triangle {m : ℕ} (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (q : Fin m → ℂ) (hq : ∀ i, ‖q i‖ ≤ 1) :
    ∏ i, ‖(a : ℂ) + (c : ℂ) * q i‖ ≤ (a + c) ^ m := by
  have : (a + c) ^ m = ∏ _i : Fin m, (a + c) := by simp
  rw [this]
  refine prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  calc ‖(a : ℂ) + (c : ℂ) * q i‖ ≤ ‖(a : ℂ)‖ + ‖(c : ℂ) * q i‖ := norm_add_le _ _
    _ = a + c * ‖q i‖ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hc]
    _ ≤ a + c := by nlinarith [hq i]

/-- the function `F(t) = ∏ (1 - t a q_i)` -/
noncomputable def Ff {m : ℕ} (a : ℝ) (q : Fin m → ℂ) (t : ℝ) : ℂ :=
  ∏ i, (1 - (t : ℂ) * ((a : ℂ) * q i))

/-- its derivative -/
noncomputable def Fd {m : ℕ} (a : ℝ) (q : Fin m → ℂ) (t : ℝ) : ℂ :=
  ∑ i, (∏ j ∈ univ.erase i, (1 - (t : ℂ) * ((a : ℂ) * q j))) * (-((a : ℂ) * q i))

/-- the function `ψ(t) = (mean |1 - t a q_j|)^(m-1)` -/
noncomputable def psi {m : ℕ} (a : ℝ) (q : Fin m → ℂ) (t : ℝ) : ℝ :=
  ((∑ j, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖) / m) ^ (m - 1)

lemma Ff_hasDerivAt {m : ℕ} (a : ℝ) (q : Fin m → ℂ) (t : ℝ) :
    HasDerivAt (Ff a q) (Fd a q t) t := by
  have h : ∀ i ∈ (univ : Finset (Fin m)), HasDerivAt (fun s : ℝ => 1 - (s : ℂ) * ((a : ℂ) * q i))
      (-((a : ℂ) * q i)) t := by
    intro i _
    have := (((hasDerivAt_id t).ofReal_comp).mul_const ((a : ℂ) * q i)).const_sub 1
    simpa using this
  have := HasDerivAt.fun_finsetProd h
  unfold Ff Fd
  simpa [smul_eq_mul] using this

lemma Ff_continuous {m : ℕ} (a : ℝ) (q : Fin m → ℂ) : Continuous (Ff a q) := by
  unfold Ff; fun_prop

lemma Fd_continuous {m : ℕ} (a : ℝ) (q : Fin m → ℂ) : Continuous (Fd a q) := by
  unfold Fd; fun_prop

lemma psi_continuous {m : ℕ} (a : ℝ) (q : Fin m → ℂ) : Continuous (psi a q) := by
  unfold psi; fun_prop

lemma Ff_zero {m : ℕ} (a : ℝ) (q : Fin m → ℂ) : Ff a q 0 = 1 := by
  simp [Ff]

lemma D_identity {m : ℕ} (a : ℝ) (q : Fin m → ℂ) (t : ℝ) :
    Fd a q t + (a : ℂ) * (∑ i, q i) * Ff a q t
      = ∑ i, (∏ j ∈ univ.erase i, (1 - (t : ℂ) * ((a : ℂ) * q j))) *
          (-((a : ℂ) * q i) * ((t : ℂ) * ((a : ℂ) * q i))) := by
  unfold Fd Ff
  rw [mul_sum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_prod_erase univ (fun j => 1 - (t : ℂ) * ((a : ℂ) * q j)) (mem_univ i)]
  ring

lemma D_norm_le {m : ℕ} (a : ℝ) (ha : 0 ≤ a) (q : Fin m → ℂ) (hq : ∀ i, ‖q i‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖Fd a q t + (a : ℂ) * (∑ i, q i) * Ff a q t‖ ≤ a ^ 2 * t * m * psi a q t := by
  rw [D_identity]
  have hr : ∀ j ∈ (univ : Finset (Fin m)), 0 ≤ ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖ :=
    fun j _ => norm_nonneg _
  have hmac := maclaurin univ (fun j => ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖) hr
  simp only [card_univ, Fintype.card_fin] at hmac
  calc ‖∑ i, (∏ j ∈ univ.erase i, (1 - (t : ℂ) * ((a : ℂ) * q j))) *
          (-((a : ℂ) * q i) * ((t : ℂ) * ((a : ℂ) * q i)))‖
      ≤ ∑ i, ‖(∏ j ∈ univ.erase i, (1 - (t : ℂ) * ((a : ℂ) * q j))) *
          (-((a : ℂ) * q i) * ((t : ℂ) * ((a : ℂ) * q i)))‖ := norm_sum_le _ _
    _ ≤ ∑ i, (∏ j ∈ univ.erase i, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖) * (a ^ 2 * t) := by
        refine sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_prod]
        refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun j _ => norm_nonneg _)
        rw [norm_mul, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg ht]
        have h1 := hq i
        have h2 := norm_nonneg (q i)
        have : a * ‖q i‖ * (t * (a * ‖q i‖)) = a ^ 2 * t * (‖q i‖ * ‖q i‖) := by ring
        rw [this]
        have h3 : ‖q i‖ * ‖q i‖ ≤ 1 := by nlinarith
        have h4 : 0 ≤ a ^ 2 * t := by positivity
        nlinarith
    _ = (∑ i, ∏ j ∈ univ.erase i, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖) * (a ^ 2 * t) := by
        rw [sum_mul]
    _ ≤ (m * ((∑ j, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖) / m) ^ (m - 1)) * (a ^ 2 * t) := by
        gcongr
    _ = a ^ 2 * t * m * psi a q t := by unfold psi; ring

lemma F_bound {m : ℕ} (a : ℝ) (ha : 0 ≤ a) (q : Fin m → ℂ) (hq : ∀ i, ‖q i‖ ≤ 1) :
    ‖Ff a q 1 - 1 + (a : ℂ) * (∑ i, q i) * ∫ t in (0:ℝ)..1, Ff a q t‖
      ≤ a ^ 2 * m * ∫ t in (0:ℝ)..1, t * psi a q t := by
  have hFTC : ∫ t in (0:ℝ)..1, Fd a q t = Ff a q 1 - Ff a q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => Ff_hasDerivAt a q t)
      ((Fd_continuous a q).intervalIntegrable 0 1)
  have hsum : ∫ t in (0:ℝ)..1, (Fd a q t + (a : ℂ) * (∑ i, q i) * Ff a q t)
      = Ff a q 1 - 1 + (a : ℂ) * (∑ i, q i) * ∫ t in (0:ℝ)..1, Ff a q t := by
    rw [intervalIntegral.integral_add ((Fd_continuous a q).intervalIntegrable 0 1)
      (((Ff_continuous a q).const_smul ((a : ℂ) * (∑ i, q i))).intervalIntegrable 0 1 |>.congr
        (by intro t _; simp [smul_eq_mul])), hFTC, Ff_zero, intervalIntegral.integral_const_mul]
  rw [← hsum]
  calc ‖∫ t in (0:ℝ)..1, (Fd a q t + (a : ℂ) * (∑ i, q i) * Ff a q t)‖
      ≤ ∫ t in (0:ℝ)..1, ‖Fd a q t + (a : ℂ) * (∑ i, q i) * Ff a q t‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0:ℝ)..1, a ^ 2 * m * (t * psi a q t) := by
        apply intervalIntegral.integral_mono_on zero_le_one
        · apply Continuous.intervalIntegrable
          exact ((Fd_continuous a q).add (continuous_const.mul (Ff_continuous a q))).norm
        · apply Continuous.intervalIntegrable
          exact continuous_const.mul (continuous_id.mul (psi_continuous a q))
        · intro t ht
          have := D_norm_le a ha q hq t ht.1
          calc _ ≤ a ^ 2 * t * m * psi a q t := this
            _ = _ := by ring
    _ = a ^ 2 * m * ∫ t in (0:ℝ)..1, t * psi a q t := by
        rw [intervalIntegral.integral_const_mul]

lemma psi_sq_le {m : ℕ} (hm : 0 < m) (a : ℝ) (q : Fin m → ℂ) (hq : ∀ i, ‖q i‖ ≤ 1) (t : ℝ) :
    psi a q t ^ 2 ≤ (1 - 2 * a * ((∑ i, (q i).re) / m) * t + a ^ 2 * t ^ 2) ^ (m - 1) := by
  unfold psi
  rw [← pow_mul, mul_comm, pow_mul]
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  apply pow_le_pow_left₀ (sq_nonneg _)
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin m)))
    (f := fun j => ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖)
  simp only [card_univ, Fintype.card_fin] at hcs
  have hpt : ∀ j, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖ ^ 2 ≤ 1 - 2 * a * t * (q j).re + a ^ 2 * t ^ 2 := by
    intro j
    have hq2 : (q j).re ^ 2 + (q j).im ^ 2 ≤ 1 := by
      have h := Complex.sq_norm (q j)
      rw [Complex.normSq_apply] at h
      nlinarith [norm_nonneg (q j), hq j]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero,
      zero_sub, add_zero]
    nlinarith [mul_nonneg (sq_nonneg (a * t)) (sub_nonneg.2 hq2)]
  have hsum : ∑ j, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖ ^ 2
      ≤ m * (1 - 2 * a * ((∑ i, (q i).re) / m) * t + a ^ 2 * t ^ 2) := by
    calc ∑ j, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖ ^ 2
        ≤ ∑ j, (1 - 2 * a * t * (q j).re + a ^ 2 * t ^ 2) := sum_le_sum fun j _ => hpt j
      _ = m * (1 - 2 * a * ((∑ i, (q i).re) / m) * t + a ^ 2 * t ^ 2) := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc (∑ j, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖) ^ 2
      ≤ m * ∑ j, ‖1 - (t : ℂ) * ((a : ℂ) * q j)‖ ^ 2 := hcs
    _ ≤ m * (m * (1 - 2 * a * ((∑ i, (q i).re) / m) * t + a ^ 2 * t ^ 2)) := by gcongr
    _ = _ := by ring

lemma two_family_defect (A B DA DB : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hDA : DA ≤ 1 - A ^ 2) (hDB : DB ≤ 1 - B ^ 2) :
    B * DA + A * DB ≤ 1 - (A * B) ^ 2 := by
  have h1 : B * DA ≤ B * (1 - A ^ 2) := mul_le_mul_of_nonneg_left hDA hB0
  have h2 : A * DB ≤ A * (1 - B ^ 2) := mul_le_mul_of_nonneg_left hDB hA0
  have h3 : 0 ≤ (1 - A) * (1 - B) * (1 - A * B) := by
    have : 0 ≤ 1 - A * B := by nlinarith
    have : 0 ≤ (1 - A) * (1 - B) := mul_nonneg (by linarith) (by linarith)
    positivity
  nlinarith

lemma defect_norm {m : ℕ} (y : Fin m → ℂ) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ∑ i, (1 - ‖y i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖y j‖ ≤ 1 - ‖∏ i, y i‖ ^ 2 := by
  rw [norm_prod]
  exact defect univ (fun i => ‖y i‖) (fun i _ => norm_nonneg _) (fun i _ => hy i)

lemma termA_eq {m : ℕ} (y : Fin m → ℂ) (Qp : ℂ) (i : Fin m) :
    Qp * ∏ j ∈ univ.erase i, y j - Qp * (∏ j, y j) * (starRingEnd ℂ) (y i)
      = Qp * (∏ j ∈ univ.erase i, y j) * (((1 - ‖y i‖ ^ 2 : ℝ)) : ℂ) := by
  rw [← mul_prod_erase univ y (mem_univ i)]
  have h : y i * (starRingEnd ℂ) (y i) = (‖y i‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  push_cast
  linear_combination (-(Qp * ∏ j ∈ univ.erase i, y j)) * h

lemma termB_norm {m : ℕ} (q : Fin m → ℂ) (hq0 : ∀ i, q i ≠ 0) (Y : ℂ) (i : Fin m)
    (hqi1 : ‖q i‖ ≤ 1) :
    ‖Y * (∏ j, q j) * ((starRingEnd ℂ) ((q i)⁻¹) - q i)‖
      = ‖Y‖ * (∏ j ∈ univ.erase i, ‖q j‖) * (1 - ‖q i‖ ^ 2) := by
  have hqi := hq0 i
  have hcq : (starRingEnd ℂ) (q i) ≠ 0 := by simpa using hqi
  rw [← mul_prod_erase univ q (mem_univ i)]
  have e : q i * ((starRingEnd ℂ) ((q i)⁻¹) - q i)
      = (q i / (starRingEnd ℂ) (q i)) * (((1 - ‖q i‖ ^ 2 : ℝ)) : ℂ) := by
    have h : q i * (starRingEnd ℂ) (q i) = (‖q i‖ : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [map_inv₀]
    push_cast
    rw [← h]
    field_simp
  have hn1 : ‖q i / (starRingEnd ℂ) (q i)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hqi)]
  calc ‖Y * (q i * ∏ j ∈ univ.erase i, q j) * ((starRingEnd ℂ) ((q i)⁻¹) - q i)‖
      = ‖Y * (∏ j ∈ univ.erase i, q j) * (q i * ((starRingEnd ℂ) ((q i)⁻¹) - q i))‖ := by
        ring_nf
    _ = ‖Y‖ * (∏ j ∈ univ.erase i, ‖q j‖) * |1 - ‖q i‖ ^ 2| := by
        rw [e, norm_mul, norm_mul, norm_mul, hn1, norm_prod, Complex.norm_real, Real.norm_eq_abs]
        ring
    _ = _ := by
        rw [abs_of_nonneg]
        nlinarith [norm_nonneg (q i)]

lemma errN_bound {m : ℕ} (a : ℝ) (y q : Fin m → ℂ) (hy : ∀ i, ‖y i‖ ≤ 1)
    (hq : ∀ i, ‖q i‖ ≤ 1) (hq0 : ∀ i, q i ≠ 0)
    (hC : ((m : ℂ) + 1) * ∑ i, (q i)⁻¹ = (m : ℂ) ^ 2 * a + m * ∑ i, y i) :
    ‖(m : ℂ) * (∏ i, q i) * (∑ i, ∏ j ∈ univ.erase i, y j)
      + (m : ℂ) ^ 2 * a * ((∏ i, q i) * ∏ i, y i)
      - ((m : ℂ) + 1) * ((∏ i, q i) * ∏ i, y i) * ∑ i, q i‖
    ≤ ((m : ℝ) + 1) * (1 - ‖(∏ i, q i) * ∏ i, y i‖ ^ 2) := by
  set Qp := ∏ i, q i with hQp
  set Y := ∏ i, y i with hY
  have hCc : ((m : ℂ) + 1) * ∑ i, (starRingEnd ℂ) ((q i)⁻¹)
      = (m : ℂ) ^ 2 * a + m * ∑ i, (starRingEnd ℂ) (y i) := by
    have := congrArg (starRingEnd ℂ) hC
    simpa [map_sum, map_add, map_mul, map_pow, Complex.conj_ofReal, map_natCast] using this
  have hrepr : (m : ℂ) * Qp * (∑ i, ∏ j ∈ univ.erase i, y j) + (m : ℂ) ^ 2 * a * (Qp * Y)
      - ((m : ℂ) + 1) * (Qp * Y) * ∑ i, q i
      = ∑ i, ((m : ℂ) * (Qp * ∏ j ∈ univ.erase i, y j - Qp * Y * (starRingEnd ℂ) (y i))
          + ((m : ℂ) + 1) * (Y * Qp * ((starRingEnd ℂ) ((q i)⁻¹) - q i))) := by
    simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib]
    linear_combination (-(Qp * Y)) * hCc
  rw [hrepr]
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hDy := defect_norm y hy
  have hDq := defect_norm q hq
  have hQ0 : 0 ≤ ‖Qp‖ := norm_nonneg _
  have hY0 : 0 ≤ ‖Y‖ := norm_nonneg _
  have hQ1 : ‖Qp‖ ≤ 1 := by
    rw [hQp, norm_prod]; exact prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hq i)
  have hY1 : ‖Y‖ ≤ 1 := by
    rw [hY, norm_prod]; exact prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hy i)
  have hDy0 : 0 ≤ ∑ i, (1 - ‖y i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖y j‖ := by
    refine sum_nonneg fun i _ => mul_nonneg ?_ (prod_nonneg fun j _ => norm_nonneg _)
    nlinarith [hy i, norm_nonneg (y i)]
  calc ‖∑ i, ((m : ℂ) * (Qp * ∏ j ∈ univ.erase i, y j - Qp * Y * (starRingEnd ℂ) (y i))
          + ((m : ℂ) + 1) * (Y * Qp * ((starRingEnd ℂ) ((q i)⁻¹) - q i)))‖
      ≤ ∑ i, ‖(m : ℂ) * (Qp * ∏ j ∈ univ.erase i, y j - Qp * Y * (starRingEnd ℂ) (y i))
          + ((m : ℂ) + 1) * (Y * Qp * ((starRingEnd ℂ) ((q i)⁻¹) - q i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((m : ℝ) * (‖Qp‖ * ((1 - ‖y i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖y j‖))
          + ((m : ℝ) + 1) * (‖Y‖ * ((1 - ‖q i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖q j‖))) := by
        refine sum_le_sum fun i _ => (norm_add_le _ _).trans (le_of_eq ?_)
        have hyi : 0 ≤ 1 - ‖y i‖ ^ 2 := by nlinarith [hy i, norm_nonneg (y i)]
        congr 1
        · rw [termA_eq, norm_mul, norm_mul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hyi, Complex.norm_natCast]
          simp only [norm_prod]
          ring
        · rw [norm_mul, termB_norm q hq0 Y i (hq i)]
          have : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
            have e : (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
            rw [e, Complex.norm_natCast]; push_cast; ring
          rw [this]
          ring
    _ = (m : ℝ) * (‖Qp‖ * ∑ i, (1 - ‖y i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖y j‖)
          + ((m : ℝ) + 1) * (‖Y‖ * ∑ i, (1 - ‖q i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖q j‖) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
    _ ≤ ((m : ℝ) + 1) * (‖Qp‖ * ∑ i, (1 - ‖y i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖y j‖)
          + ((m : ℝ) + 1) * (‖Y‖ * ∑ i, (1 - ‖q i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖q j‖) := by
        gcongr
        linarith
    _ = ((m : ℝ) + 1) * (‖Qp‖ * ∑ i, (1 - ‖y i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖y j‖
          + ‖Y‖ * ∑ i, (1 - ‖q i‖ ^ 2) * ∏ j ∈ univ.erase i, ‖q j‖) := by ring
    _ ≤ ((m : ℝ) + 1) * (1 - ‖Qp * Y‖ ^ 2) := by
        gcongr
        rw [norm_mul, mul_comm ‖Qp‖ ‖Y‖]
        exact two_family_defect ‖Y‖ ‖Qp‖ _ _ hY0 hY1 hQ0 hQ1 hDy hDq

lemma quad_aux (M a : ℝ) (hM : 4 ≤ M) : 2 * a * (M + 1) ≤ M + M ^ 2 * a ^ 2 - a * M := by
  have h1 : 0 ≤ (2 * M ^ 2 * a - (3 * M + 2)) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 4 * M ^ 3 - (3 * M + 2) ^ 2 := by nlinarith
  have h3 : 0 < M ^ 2 := by positivity
  nlinarith

lemma V_bounds {m : ℕ} (hm : 4 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (Sq : ℂ)
    (hSqn : ‖Sq‖ ≤ m) :
    2 * a * ((m : ℝ) + 1) ≤ ‖(((m : ℝ) * (1 + (m : ℝ) * a ^ 2) : ℝ) : ℂ) - (a : ℂ) * Sq‖ ∧
    ‖(((m : ℝ) * (1 + (m : ℝ) * a ^ 2) : ℝ) : ℂ) - (a : ℂ) * Sq‖
      ≤ (m : ℝ) * (1 + (m : ℝ) * a ^ 2) - a * Sq.re + (1 - (Sq.re / m) ^ 2) / 2 := by
  set V : ℂ := (((m : ℝ) * (1 + (m : ℝ) * a ^ 2) : ℝ) : ℂ) - (a : ℂ) * Sq with hV
  have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hSq2 : Sq.re ^ 2 + Sq.im ^ 2 ≤ (m : ℝ) ^ 2 := by
    have h := Complex.sq_norm Sq
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg Sq]
  have hre_le : Sq.re ≤ m := by nlinarith [sq_nonneg Sq.im]
  have hVre : V.re = m * (1 + m * a ^ 2) - a * Sq.re := by
    rw [hV, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hVim : V.im = -(a * Sq.im) := by
    rw [hV, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_sub]
  have hVre_lo : (m : ℝ) ^ 2 * a ^ 2 ≤ V.re := by
    rw [hVre]
    have : a * Sq.re ≤ a * m := mul_le_mul_of_nonneg_left hre_le ha0.le
    have : a * m ≤ m := by nlinarith
    nlinarith
  constructor
  · have h1 : V.re ≤ ‖V‖ := Complex.re_le_norm V
    have h2 := quad_aux (m : ℝ) a hmr
    have h3 : (m : ℝ) + m ^ 2 * a ^ 2 - a * m ≤ V.re := by
      rw [hVre]
      have : a * Sq.re ≤ a * m := mul_le_mul_of_nonneg_left hre_le ha0.le
      nlinarith
    linarith
  · set x := Sq.re / m with hx
    have hSqx : Sq.re = m * x := by rw [hx]; field_simp
    have hx2 : x ^ 2 ≤ 1 := by
      have h4 : (m : ℝ) ^ 2 * x ^ 2 ≤ (m : ℝ) ^ 2 * 1 := by
        have : (m * x) ^ 2 ≤ (m : ℝ) ^ 2 := by rw [← hSqx]; nlinarith [sq_nonneg Sq.im]
        nlinarith
      exact le_of_mul_le_mul_left h4 (by positivity)
    have hIm : (a * Sq.im) ^ 2 ≤ (m : ℝ) ^ 2 * a ^ 2 * (1 - x ^ 2) := by
      have h5 : Sq.im ^ 2 ≤ (m : ℝ) ^ 2 * (1 - x ^ 2) := by
        have := hSq2; rw [hSqx] at this; nlinarith
      have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg a)
      nlinarith
    have hnormsq : ‖V‖ ^ 2 = V.re ^ 2 + V.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hpos : 0 ≤ V.re + (1 - x ^ 2) / 2 := by
      have : 0 ≤ (m : ℝ) ^ 2 * a ^ 2 := by positivity
      linarith
    rw [← hVre]
    apply (pow_le_pow_iff_left₀ (norm_nonneg V) hpos two_ne_zero).mp
    rw [hnormsq, hVim]
    have h7 : 0 ≤ (1 - x ^ 2) * (V.re - (m : ℝ) ^ 2 * a ^ 2) :=
      mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hVre_lo)
    have e : (V.re + (1 - x ^ 2) / 2) ^ 2 = V.re ^ 2 + V.re * (1 - x ^ 2) + ((1 - x ^ 2) / 2) ^ 2 := by
      ring
    rw [e]
    nlinarith [sq_nonneg ((1 - x ^ 2) / 2)]

lemma origin_alg {m : ℕ} (hm : 4 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (y q : Fin m → ℂ) (hy : ∀ i, ‖y i‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ 1) (hq0 : ∀ i, q i ≠ 0)
    (IF F1 : ℂ) (K : ℝ)
    (hO1 : (∏ i, q i) * (∏ i, y i) = ((m : ℂ) + 1) * IF)
    (hO2 : (∏ i, q i) * ((∏ i, y i) - (a : ℂ) * ∑ i, ∏ j ∈ univ.erase i, y j)
      = ((m : ℂ) + 1) * F1)
    (hC : ((m : ℂ) + 1) * ∑ i, (q i)⁻¹ = (m : ℂ) ^ 2 * a + m * ∑ i, y i)
    (hFb : ‖F1 - 1 + (a : ℂ) * (∑ i, q i) * IF‖ ≤ K) :
    (m : ℝ) * (1 - a ^ 2) + a * ((∑ i, (q i).re) / m) ≤
      (1 - ((∑ i, (q i).re) / m) ^ 2) / (2 * m) + ((m : ℝ) + 1) * K := by
  have hErr := errN_bound a y q hy hq hq0 hC
  set Qp := ∏ i, q i with hQp
  set Y := ∏ i, y i with hY
  set E := ∑ i, ∏ j ∈ univ.erase i, y j with hE
  set Sq := ∑ i, q i with hSq
  set ErrN := (m : ℂ) * Qp * E + (m : ℂ) ^ 2 * a * (Qp * Y) - ((m : ℂ) + 1) * (Qp * Y) * Sq
    with hErrN
  have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hSqn : ‖Sq‖ ≤ m := by
    calc ‖Sq‖ ≤ ∑ i, ‖q i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, (1 : ℝ) := sum_le_sum fun i _ => hq i
      _ = m := by simp
  have hSqre : Sq.re = ∑ i, (q i).re := by rw [hSq, Complex.re_sum]
  obtain ⟨hV_lo, hV_hi⟩ := V_bounds hm a ha0 ha1 Sq hSqn
  set V : ℂ := (((m : ℝ) * (1 + (m : ℝ) * a ^ 2) : ℝ) : ℂ) - (a : ℂ) * Sq with hV
  have hkey : (m : ℂ) * ((m : ℂ) + 1) * (F1 + a * Sq * IF) = (Qp * Y) * V - a * ErrN := by
    rw [hV, hErrN]
    push_cast
    linear_combination (-(m : ℂ)) * hO2 + (-(a * m * Sq)) * hO1
  rw [hSqre] at hV_hi
  have hJ0 : 0 ≤ ‖Qp * Y‖ := norm_nonneg _
  have hJ1 : ‖Qp * Y‖ ≤ 1 := by
    rw [norm_mul, hQp, hY, norm_prod, norm_prod]
    exact mul_le_one₀ (prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hq i))
      (prod_nonneg fun i _ => norm_nonneg _)
      (prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hy i))
  have hstep1 : 1 ≤ ‖F1 + a * Sq * IF‖ + K := by
    have e : (1 : ℂ) = (F1 + a * Sq * IF) - (F1 - 1 + a * Sq * IF) := by ring
    have := norm_sub_le (F1 + a * Sq * IF) (F1 - 1 + a * Sq * IF)
    rw [← e, norm_one] at this
    linarith
  have hstep2 : (m : ℝ) * ((m : ℝ) + 1) * ‖F1 + a * Sq * IF‖
      ≤ ‖Qp * Y‖ * ‖V‖ + a * (((m : ℝ) + 1) * (1 - ‖Qp * Y‖ ^ 2)) := by
    have hnm : ‖(m : ℂ) * ((m : ℂ) + 1)‖ = (m : ℝ) * ((m : ℝ) + 1) := by
      have e : (m : ℂ) * ((m : ℂ) + 1) = (((m : ℝ) * ((m : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (m : ℝ) * ((m : ℝ) + 1) * ‖F1 + a * Sq * IF‖
        = ‖(m : ℂ) * ((m : ℂ) + 1) * (F1 + a * Sq * IF)‖ := by rw [norm_mul, hnm]
      _ = ‖(Qp * Y) * V - a * ErrN‖ := by rw [hkey]
      _ ≤ ‖(Qp * Y) * V‖ + ‖(a : ℂ) * ErrN‖ := norm_sub_le _ _
      _ = ‖Qp * Y‖ * ‖V‖ + a * ‖ErrN‖ := by
          rw [norm_mul (Qp * Y) V, norm_mul (a : ℂ) ErrN, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ha0]
      _ ≤ ‖Qp * Y‖ * ‖V‖ + a * (((m : ℝ) + 1) * (1 - ‖Qp * Y‖ ^ 2)) := by
          gcongr
  have hstep3 : ‖Qp * Y‖ * ‖V‖ + a * (((m : ℝ) + 1) * (1 - ‖Qp * Y‖ ^ 2)) ≤ ‖V‖ := by
    set j := ‖Qp * Y‖
    set A := ‖V‖
    have hanj : a * ((m : ℝ) + 1) * j ≤ a * ((m : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonneg_left hJ1 (by positivity)
    have h1 : a * ((m : ℝ) + 1) * (1 + j) ≤ A := by linarith
    have h2 : 0 ≤ (1 - j) * (A - a * ((m : ℝ) + 1) * (1 + j)) :=
      mul_nonneg (sub_nonneg.2 hJ1) (sub_nonneg.2 h1)
    have e : (1 - j) * (A - a * ((m : ℝ) + 1) * (1 + j))
        = A - (j * A + a * (((m : ℝ) + 1) * (1 - j ^ 2))) := by ring
    linarith
  have hfin : (m : ℝ) * ((m : ℝ) + 1) ≤ (m : ℝ) * (1 + (m : ℝ) * a ^ 2)
      - a * ∑ i, (q i).re + (1 - ((∑ i, (q i).re) / m) ^ 2) / 2
      + (m : ℝ) * ((m : ℝ) + 1) * K := by
    have := mul_le_mul_of_nonneg_left hstep1 (by positivity : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 1))
    linarith
  set x := (∑ i, (q i).re) / m with hx
  have hsx : ∑ i, (q i).re = m * x := by rw [hx]; field_simp
  rw [hsx] at hfin
  have hgoal : (m : ℝ) * ((m : ℝ) * (1 - a ^ 2) + a * x) ≤
      (m : ℝ) * ((1 - x ^ 2) / (2 * m) + ((m : ℝ) + 1) * K) := by
    have e1 : (m : ℝ) * ((1 - x ^ 2) / (2 * m) + ((m : ℝ) + 1) * K)
        = (1 - x ^ 2) / 2 + (m : ℝ) * ((m : ℝ) + 1) * K := by field_simp
    have e2 : (m : ℝ) * ((m : ℝ) * (1 - a ^ 2) + a * x)
        = (m : ℝ) * ((m : ℝ) + 1) - (m : ℝ) * (1 + (m : ℝ) * a ^ 2) + a * (m * x) := by ring
    rw [e1, e2]
    linarith
  exact le_of_mul_le_mul_left hgoal hmpos

lemma integral_sum_pow (N : ℕ) (c : ℕ → ℝ) :
    ∫ t in (0:ℝ)..1, ∑ k ∈ range N, c k * t ^ k = ∑ k ∈ range N, c k / ((k : ℝ) + 1) := by
  rw [intervalIntegral.integral_finsetSum (f := fun k t => c k * t ^ k)
    (fun k _ => (continuous_const.mul (continuous_pow k)).intervalIntegrable 0 1)]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    sub_zero]
  ring

lemma int_P5 (A B C : ℝ) :
    ∫ t in (0:ℝ)..1, (A + B * t + C * t ^ 2) ^ 2 * (1 + (A + B * t + C * t ^ 2)) / 2 = A^3/2 + 3*A^2*B/4 + A^2*C/2 + A^2/2 + A*B^2/2 + 3*A*B*C/4 + A*B/2 + 3*A*C^2/10 + A*C/3 + B^3/8 + 3*B^2*C/10 + B^2/6 + B*C^2/4 + B*C/4 + C^3/14 + C^2/10 := by
  have h : ∀ t : ℝ, (A + B * t + C * t ^ 2) ^ 2 * (1 + (A + B * t + C * t ^ 2)) / 2 = ∑ k ∈ range 7, [(A^3/2 + A^2/2), (3*A^2*B/2 + A*B), (3*A^2*C/2 + 3*A*B^2/2 + A*C + B^2/2), (3*A*B*C + B^3/2 + B*C), (3*A*C^2/2 + 3*B^2*C/2 + C^2/2), (3*B*C^2/2), (C^3/2)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_P6 (A B C : ℝ) :
    ∫ t in (0:ℝ)..1, (A + B * t + C * t ^ 2) ^ 3 = A^3 + 3*A^2*B/2 + A^2*C + A*B^2 + 3*A*B*C/2 + 3*A*C^2/5 + B^3/4 + 3*B^2*C/5 + B*C^2/2 + C^3/7 := by
  have h : ∀ t : ℝ, (A + B * t + C * t ^ 2) ^ 3 = ∑ k ∈ range 7, [(A^3), (3*A^2*B), (3*A^2*C + 3*A*B^2), (6*A*B*C + B^3), (3*A*C^2 + 3*B^2*C), (3*B*C^2), (C^3)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_P7 (A B C : ℝ) :
    ∫ t in (0:ℝ)..1, (A + B * t + C * t ^ 2) ^ 3 * (1 + (A + B * t + C * t ^ 2)) / 2 = A^4/2 + A^3*B + 2*A^3*C/3 + A^3/2 + A^2*B^2 + 3*A^2*B*C/2 + 3*A^2*B/4 + 3*A^2*C^2/5 + A^2*C/2 + A*B^3/2 + 6*A*B^2*C/5 + A*B^2/2 + A*B*C^2 + 3*A*B*C/4 + 2*A*C^3/7 + 3*A*C^2/10 + B^4/10 + B^3*C/3 + B^3/8 + 3*B^2*C^2/7 + 3*B^2*C/10 + B*C^3/4 + B*C^2/4 + C^4/18 + C^3/14 := by
  have h : ∀ t : ℝ, (A + B * t + C * t ^ 2) ^ 3 * (1 + (A + B * t + C * t ^ 2)) / 2 = ∑ k ∈ range 9, [(A^4/2 + A^3/2), (2*A^3*B + 3*A^2*B/2), (2*A^3*C + 3*A^2*B^2 + 3*A^2*C/2 + 3*A*B^2/2), (6*A^2*B*C + 2*A*B^3 + 3*A*B*C + B^3/2), (3*A^2*C^2 + 6*A*B^2*C + 3*A*C^2/2 + B^4/2 + 3*B^2*C/2), (6*A*B*C^2 + 2*B^3*C + 3*B*C^2/2), (2*A*C^3 + 3*B^2*C^2 + C^3/2), (2*B*C^3), (C^4/2)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_O5 (B C : ℝ) :
    ∫ t in (0:ℝ)..1, t * (1 + B * t + C * t ^ 2) ^ 2 = B^2/4 + 2*B*C/5 + 2*B/3 + C^2/6 + C/2 + 1/2 := by
  have h : ∀ t : ℝ, t * (1 + B * t + C * t ^ 2) ^ 2 = ∑ k ∈ range 6, [(0), (1), (2*B), (B^2 + 2*C), (2*B*C), (C^2)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_O7 (B C : ℝ) :
    ∫ t in (0:ℝ)..1, t * (1 + B * t + C * t ^ 2) ^ 3 = B^3/5 + B^2*C/2 + 3*B^2/4 + 3*B*C^2/7 + 6*B*C/5 + B + C^3/8 + C^2/2 + 3*C/4 + 1/2 := by
  have h : ∀ t : ℝ, t * (1 + B * t + C * t ^ 2) ^ 3 = ∑ k ∈ range 8, [(0), (1), (3*B), (3*B^2 + 3*C), (B^3 + 6*B*C), (3*B^2*C + 3*C^2), (3*B*C^2), (C^3)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_O6 (D E : ℝ) :
    ∫ t in (0:ℝ)..1, t * ((1 + D * t) ^ 5 + 5 / 2 * (1 + D * t) ^ 3 * (E * t ^ 2) + 15 / 8 * (E * t ^ 2) ^ 2) = D^5/7 + 5*D^4/6 + 5*D^3*E/14 + 2*D^3 + 5*D^2*E/4 + 5*D^2/2 + 3*D*E/2 + 5*D/3 + 5*E^2/16 + 5*E/8 + 1/2 := by
  have h : ∀ t : ℝ, t * ((1 + D * t) ^ 5 + 5 / 2 * (1 + D * t) ^ 3 * (E * t ^ 2) + 15 / 8 * (E * t ^ 2) ^ 2) = ∑ k ∈ range 7, [(0), (1), (5*D), (10*D^2 + 5*E/2), (10*D^3 + 15*D*E/2), (5*D^4 + 15*D^2*E/2 + 15*E^2/8), (D^5 + 5*D^3*E/2)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_S1 (A B : ℝ) :
    ∫ t in (0:ℝ)..1, (A + B * t) ^ 1 = A + B/2 := by
  have h : ∀ t : ℝ, (A + B * t) ^ 1 = ∑ k ∈ range 2, [(A), (B)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_S2 (A B : ℝ) :
    ∫ t in (0:ℝ)..1, (A + B * t) ^ 2 = A^2 + A*B + B^2/3 := by
  have h : ∀ t : ℝ, (A + B * t) ^ 2 = ∑ k ∈ range 3, [(A^2), (2*A*B), (B^2)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_S3 (A B : ℝ) :
    ∫ t in (0:ℝ)..1, (A + B * t) ^ 3 = A^3 + 3*A^2*B/2 + A*B^2 + B^3/4 := by
  have h : ∀ t : ℝ, (A + B * t) ^ 3 = ∑ k ∈ range 4, [(A^3), (3*A^2*B), (3*A*B^2), (B^3)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

lemma int_S4 (A B : ℝ) :
    ∫ t in (0:ℝ)..1, (A + B * t) ^ 4 = A^4 + 2*A^3*B + 2*A^2*B^2 + A*B^3 + B^4/5 := by
  have h : ∀ t : ℝ, (A + B * t) ^ 4 = ∑ k ∈ range 5, [(A^4), (4*A^3*B), (6*A^2*B^2), (4*A*B^3), (B^4)].getD k 0 * t ^ k := by
    intro t; simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring
  simp_rw [h]
  rw [integral_sum_pow]
  simp only [sum_range_succ, sum_range_zero]; norm_num <;> ring

noncomputable def Qf (a x t : ℝ) : ℝ := a ^ 2 + 2 * a * (t * (1 - a ^ 2)) * x + (t * (1 - a ^ 2)) ^ 2

noncomputable def Bf (a x t : ℝ) : ℝ := 1 - 2 * a * x * t + a ^ 2 * t ^ 2

noncomputable def B6f (a x t : ℝ) : ℝ :=
  (1 - a * x * t) ^ 5 + 5 / 2 * (1 - a * x * t) ^ 3 * (a ^ 2 * t ^ 2 * (1 - x ^ 2))
    + 15 / 8 * (a ^ 2 * t ^ 2 * (1 - x ^ 2)) ^ 2

noncomputable def SP5 (e a : ℝ) : ℝ :=
  (11/4) * e ^ 0 * a ^ 10 + (235/8) * e ^ 1 * a ^ 9 + (642/5) * e ^ 2 * a ^ 8 + (3087/10) * e ^ 3 * a ^ 7 + (130929/280) * e ^ 4 * a ^ 6 + (266867/560) * e ^ 5 * a ^ 5 + (375201/1120) * e ^ 6 * a ^ 4 + (361717/2240) * e ^ 7 * a ^ 3 + (7177/140) * e ^ 8 * a ^ 2 + (1357/140) * e ^ 9 * a ^ 1 + (29/35) * e ^ 10 * a ^ 0

lemma SP5_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SP5 e a := by
  unfold SP5; positivity

noncomputable def SP6 (e a : ℝ) : ℝ :=
  (5/2) * e ^ 0 * a ^ 10 + (117/4) * e ^ 1 * a ^ 9 + 134 * e ^ 2 * a ^ 8 + (3261/10) * e ^ 3 * a ^ 7 + (17257/35) * e ^ 4 * a ^ 6 + (139957/280) * e ^ 5 * a ^ 5 + (195833/560) * e ^ 6 * a ^ 4 + (188117/1120) * e ^ 7 * a ^ 3 + (1489/28) * e ^ 8 * a ^ 2 + (281/28) * e ^ 9 * a ^ 1 + (6/7) * e ^ 10 * a ^ 0

lemma SP6_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SP6 e a := by
  unfold SP6; positivity

noncomputable def SP7 (e a : ℝ) : ℝ :=
  (19/12) * e ^ 0 * a ^ 14 + (731/24) * e ^ 1 * a ^ 13 + (697/3) * e ^ 2 * a ^ 12 + (29449/30) * e ^ 3 * a ^ 11 + (278456/105) * e ^ 4 * a ^ 10 + (8354921/1680) * e ^ 5 * a ^ 9 + (68519533/10080) * e ^ 6 * a ^ 8 + (28070317/4032) * e ^ 7 * a ^ 7 + (13632973/2520) * e ^ 8 * a ^ 6 + (32152483/10080) * e ^ 9 * a ^ 5 + (3550807/2520) * e ^ 10 * a ^ 4 + (9134213/20160) * e ^ 11 * a ^ 3 + (50585/504) * e ^ 12 * a ^ 2 + (3457/252) * e ^ 13 * a ^ 1 + (55/63) * e ^ 14 * a ^ 0

lemma SP7_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SP7 e a := by
  unfold SP7; positivity

noncomputable def SO5 (e a : ℝ) : ℝ :=
  (51/10) * e ^ 0 * a ^ 5 + (709/160) * e ^ 1 * a ^ 4 + (1369/40) * e ^ 2 * a ^ 3 + (4467/80) * e ^ 3 * a ^ 2 + (1189/40) * e ^ 4 * a ^ 1 + (157/32) * e ^ 5 * a ^ 0

lemma SO5_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SO5 e a := by
  unfold SO5; positivity

noncomputable def SO6 (e a : ℝ) : ℝ :=
  (15/2) * e ^ 0 * a ^ 11 + (345/8) * e ^ 1 * a ^ 10 + (27051/128) * e ^ 2 * a ^ 9 + (1249659/2048) * e ^ 3 * a ^ 8 + (655425/512) * e ^ 4 * a ^ 7 + (4225571/2048) * e ^ 5 * a ^ 6 + (155247/64) * e ^ 6 * a ^ 5 + (126555/64) * e ^ 7 * a ^ 4 + (4295/4) * e ^ 8 * a ^ 3 + (23535/64) * e ^ 9 * a ^ 2 + (2283/32) * e ^ 10 * a ^ 1 + (379/64) * e ^ 11 * a ^ 0

lemma SO6_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SO6 e a := by
  unfold SO6; positivity

noncomputable def SO7 (e a : ℝ) : ℝ :=
  (341/35) * e ^ 0 * a ^ 7 + (62373/1120) * e ^ 1 * a ^ 6 + (10275/112) * e ^ 2 * a ^ 5 + (34351/224) * e ^ 3 * a ^ 4 + (12141/56) * e ^ 4 * a ^ 3 + (36255/224) * e ^ 5 * a ^ 2 + (6243/112) * e ^ 6 * a ^ 1 + (1553/224) * e ^ 7 * a ^ 0

lemma SO7_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SO7 e a := by
  unfold SO7; positivity

noncomputable def SS1 (e a : ℝ) : ℝ :=
  (1/2) * e ^ 0 * a ^ 0

lemma SS1_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SS1 e a := by
  unfold SS1; positivity

noncomputable def SS2 (e a : ℝ) : ℝ :=
  (2/3) * e ^ 0 * a ^ 2 + (5/3) * e ^ 1 * a ^ 1 + (2/3) * e ^ 2 * a ^ 0

lemma SS2_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SS2 e a := by
  unfold SS2; positivity

noncomputable def SS3 (e a : ℝ) : ℝ :=
  (1/2) * e ^ 0 * a ^ 4 + 3 * e ^ 1 * a ^ 3 + (11/2) * e ^ 2 * a ^ 2 + (7/2) * e ^ 3 * a ^ 1 + (3/4) * e ^ 4 * a ^ 0

lemma SS3_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SS3 e a := by
  unfold SS3; positivity

noncomputable def SS4 (e a : ℝ) : ℝ :=
  2 * e ^ 0 * a ^ 5 + (49/5) * e ^ 1 * a ^ 4 + (88/5) * e ^ 2 * a ^ 3 + (71/5) * e ^ 3 * a ^ 2 + (27/5) * e ^ 4 * a ^ 1 + (4/5) * e ^ 5 * a ^ 0

lemma SS4_pos (e a : ℝ) (he : 0 < e) (ha : 0 < a) : 0 < SS4 e a := by
  unfold SS4; positivity

lemma num_P5 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0:ℝ)..1, Qf a ((1 + 3 * a) / 4) t ^ 2 * (1 + Qf a ((1 + 3 * a) / 4) t) / 2 < 1 := by
  have e : ∀ t, Qf a ((1 + 3 * a) / 4) t ^ 2 * (1 + Qf a ((1 + 3 * a) / 4) t) / 2
      = (a ^ 2 + (2 * a * (1 - a ^ 2) * ((1 + 3 * a) / 4)) * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^ 2 *
        (1 + (a ^ 2 + (2 * a * (1 - a ^ 2) * ((1 + 3 * a) / 4)) * t + (1 - a ^ 2) ^ 2 * t ^ 2)) / 2 := by
    intro t; unfold Qf; ring
  have h : ∫ t in (0:ℝ)..1, Qf a ((1 + 3 * a) / 4) t ^ 2 * (1 + Qf a ((1 + 3 * a) / 4) t) / 2
      = 1 - (1 - a) ^ 2 * SP5 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_P5]
    unfold SP5; ring
  rw [h]
  have h1 := SP5_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) ^ 2 * SP5 (1 - a) a := mul_pos (pow_pos (by linarith) 2) h1
  linarith

lemma num_P6 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0:ℝ)..1, Qf a ((1 + 3 * a) / 4) t ^ 3 < 1 := by
  have e : ∀ t, Qf a ((1 + 3 * a) / 4) t ^ 3
      = (a ^ 2 + (2 * a * (1 - a ^ 2) * ((1 + 3 * a) / 4)) * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^ 3 := by
    intro t; unfold Qf; ring
  have h : ∫ t in (0:ℝ)..1, Qf a ((1 + 3 * a) / 4) t ^ 3 = 1 - (1 - a) ^ 2 * SP6 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_P6]
    unfold SP6; ring
  rw [h]
  have h1 := SP6_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) ^ 2 * SP6 (1 - a) a := mul_pos (pow_pos (by linarith) 2) h1
  linarith

lemma num_P7 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0:ℝ)..1, Qf a ((1 + 3 * a) / 4) t ^ 3 * (1 + Qf a ((1 + 3 * a) / 4) t) / 2 < 1 := by
  have e : ∀ t, Qf a ((1 + 3 * a) / 4) t ^ 3 * (1 + Qf a ((1 + 3 * a) / 4) t) / 2
      = (a ^ 2 + (2 * a * (1 - a ^ 2) * ((1 + 3 * a) / 4)) * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^ 3 *
        (1 + (a ^ 2 + (2 * a * (1 - a ^ 2) * ((1 + 3 * a) / 4)) * t + (1 - a ^ 2) ^ 2 * t ^ 2)) / 2 := by
    intro t; unfold Qf; ring
  have h : ∫ t in (0:ℝ)..1, Qf a ((1 + 3 * a) / 4) t ^ 3 * (1 + Qf a ((1 + 3 * a) / 4) t) / 2
      = 1 - (1 - a) ^ 2 * SP7 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_P7]
    unfold SP7; ring
  rw [h]
  have h1 := SP7_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) ^ 2 * SP7 (1 - a) a := mul_pos (pow_pos (by linarith) 2) h1
  linarith

lemma num_O5 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (1 - ((1 + 3 * a) / 4) ^ 2) / (2 * 5) + (5 + 1) * (a ^ 2 * 5 *
      ∫ t in (0:ℝ)..1, t * Bf a ((1 + 3 * a) / 4) t ^ 2) < 5 * (1 - a ^ 2) + a * ((1 + 3 * a) / 4) := by
  have e : ∀ t, t * Bf a ((1 + 3 * a) / 4) t ^ 2
      = t * (1 + (-2 * a * ((1 + 3 * a) / 4)) * t + a ^ 2 * t ^ 2) ^ 2 := by
    intro t; unfold Bf; ring
  have h : (1 - ((1 + 3 * a) / 4) ^ 2) / (2 * 5) + (5 + 1) * (a ^ 2 * 5 *
      ∫ t in (0:ℝ)..1, t * Bf a ((1 + 3 * a) / 4) t ^ 2)
      = 5 * (1 - a ^ 2) + a * ((1 + 3 * a) / 4) - (1 - a) * SO5 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_O5]
    unfold SO5; ring
  rw [h]
  have h1 := SO5_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) * SO5 (1 - a) a := mul_pos (by linarith) h1
  linarith

lemma num_O6 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (1 - ((1 + 3 * a) / 4) ^ 2) / (2 * 6) + (6 + 1) * (a ^ 2 * 6 *
      ∫ t in (0:ℝ)..1, t * B6f a ((1 + 3 * a) / 4) t) < 6 * (1 - a ^ 2) + a * ((1 + 3 * a) / 4) := by
  have e : ∀ t, t * B6f a ((1 + 3 * a) / 4) t
      = t * ((1 + (-(a * ((1 + 3 * a) / 4))) * t) ^ 5 + 5 / 2 * (1 + (-(a * ((1 + 3 * a) / 4))) * t) ^ 3 *
          ((a ^ 2 * (1 - ((1 + 3 * a) / 4) ^ 2)) * t ^ 2)
          + 15 / 8 * ((a ^ 2 * (1 - ((1 + 3 * a) / 4) ^ 2)) * t ^ 2) ^ 2) := by
    intro t; unfold B6f; ring
  have h : (1 - ((1 + 3 * a) / 4) ^ 2) / (2 * 6) + (6 + 1) * (a ^ 2 * 6 *
      ∫ t in (0:ℝ)..1, t * B6f a ((1 + 3 * a) / 4) t)
      = 6 * (1 - a ^ 2) + a * ((1 + 3 * a) / 4) - (1 - a) * SO6 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_O6]
    unfold SO6; ring
  rw [h]
  have h1 := SO6_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) * SO6 (1 - a) a := mul_pos (by linarith) h1
  linarith

lemma num_O7 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (1 - ((1 + 3 * a) / 4) ^ 2) / (2 * 7) + (7 + 1) * (a ^ 2 * 7 *
      ∫ t in (0:ℝ)..1, t * Bf a ((1 + 3 * a) / 4) t ^ 3) < 7 * (1 - a ^ 2) + a * ((1 + 3 * a) / 4) := by
  have e : ∀ t, t * Bf a ((1 + 3 * a) / 4) t ^ 3
      = t * (1 + (-2 * a * ((1 + 3 * a) / 4)) * t + a ^ 2 * t ^ 2) ^ 3 := by
    intro t; unfold Bf; ring
  have h : (1 - ((1 + 3 * a) / 4) ^ 2) / (2 * 7) + (7 + 1) * (a ^ 2 * 7 *
      ∫ t in (0:ℝ)..1, t * Bf a ((1 + 3 * a) / 4) t ^ 3)
      = 7 * (1 - a ^ 2) + a * ((1 + 3 * a) / 4) - (1 - a) * SO7 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_O7]
    unfold SO7; ring
  rw [h]
  have h1 := SO7_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) * SO7 (1 - a) a := mul_pos (by linarith) h1
  linarith

lemma num_S1 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 1 < 1 := by
  have e : ∀ t : ℝ, (a + t * (1 - a ^ 2)) ^ 1 = (a + (1 - a ^ 2) * t) ^ 1 := by intro t; ring
  have h : ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 1 = 1 - (1 - a) ^ 2 * SS1 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_S1]
    unfold SS1; ring
  rw [h]
  have h1 := SS1_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) ^ 2 * SS1 (1 - a) a := mul_pos (pow_pos (by linarith) 2) h1
  linarith

lemma num_S2 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 2 < 1 := by
  have e : ∀ t : ℝ, (a + t * (1 - a ^ 2)) ^ 2 = (a + (1 - a ^ 2) * t) ^ 2 := by intro t; ring
  have h : ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 2 = 1 - (1 - a) ^ 2 * SS2 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_S2]
    unfold SS2; ring
  rw [h]
  have h1 := SS2_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) ^ 2 * SS2 (1 - a) a := mul_pos (pow_pos (by linarith) 2) h1
  linarith

lemma num_S3 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 3 < 1 := by
  have e : ∀ t : ℝ, (a + t * (1 - a ^ 2)) ^ 3 = (a + (1 - a ^ 2) * t) ^ 3 := by intro t; ring
  have h : ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 3 = 1 - (1 - a) ^ 2 * SS3 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_S3]
    unfold SS3; ring
  rw [h]
  have h1 := SS3_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) ^ 2 * SS3 (1 - a) a := mul_pos (pow_pos (by linarith) 2) h1
  linarith

lemma num_S4 (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 4 < 1 := by
  have e : ∀ t : ℝ, (a + t * (1 - a ^ 2)) ^ 4 = (a + (1 - a ^ 2) * t) ^ 4 := by intro t; ring
  have h : ∫ t in (0:ℝ)..1, (a + t * (1 - a ^ 2)) ^ 4 = 1 - (1 - a) ^ 3 * SS4 (1 - a) a := by
    rw [intervalIntegral.integral_congr (fun t _ => e t), int_S4]
    unfold SS4; ring
  rw [h]
  have h1 := SS4_pos (1 - a) a (by linarith) ha0
  have h2 : 0 < (1 - a) ^ 3 * SS4 (1 - a) a := mul_pos (pow_pos (by linarith) 3) h1
  linarith

lemma Qf_mono (a x y t : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) (hxy : x ≤ y) :
    Qf a x t ≤ Qf a y t := by
  unfold Qf
  have h1 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have h2 : 0 ≤ 2 * a * (t * (1 - a ^ 2)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hxy h2]

lemma Qf_nonneg (a x t : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) (hx : -1 ≤ x) :
    0 ≤ Qf a x t := by
  unfold Qf
  have h1 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have h2 : 0 ≤ 2 * a * (t * (1 - a ^ 2)) := by positivity
  have h3 : 0 ≤ 2 * a * (t * (1 - a ^ 2)) * (x + 1) := mul_nonneg h2 (by linarith)
  nlinarith [sq_nonneg (a - t * (1 - a ^ 2))]

lemma Bf_anti (a x y t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hxy : x ≤ y) : Bf a y t ≤ Bf a x t := by
  unfold Bf
  have h2 : 0 ≤ 2 * a * t := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hxy h2]

lemma Bf_nonneg (a x t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hx : x ≤ 1) : 0 ≤ Bf a x t := by
  unfold Bf
  have h2 : 0 ≤ 2 * a * t * (1 - x) := mul_nonneg (by positivity) (by linarith)
  nlinarith [sq_nonneg (1 - a * t)]

lemma le_of_sq_le_sq_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v :=
  (pow_le_pow_iff_left₀ hu hv two_ne_zero).mp h

lemma taylor6 (L s : ℝ) (hL : 0 ≤ L) (hLs : L ≤ s) (hs1 : s ≤ 1) :
    s ^ 5 ≤ L ^ 5 + 5 / 2 * L ^ 3 * (s ^ 2 - L ^ 2) + 15 / 8 * (s ^ 2 - L ^ 2) ^ 2 := by
  have hd : 0 ≤ s - L := by linarith
  have hw : 0 ≤ 1 - s := by linarith
  have e : L ^ 5 + 5 / 2 * L ^ 3 * (s ^ 2 - L ^ 2) + 15 / 8 * (s ^ 2 - L ^ 2) ^ 2 - s ^ 5
      = (s - L) ^ 2 / 2 * (10 * L ^ 2 * (s - L) + 15 * L ^ 2 * (1 - s) + 35 / 4 * L * (s - L) ^ 2
        + 15 * L * (s - L) * (1 - s) + 7 / 4 * (s - L) ^ 3 + 15 / 4 * (s - L) ^ 2 * (1 - s)) := by
    ring
  have hpos : 0 ≤ (s - L) ^ 2 / 2 * (10 * L ^ 2 * (s - L) + 15 * L ^ 2 * (1 - s)
      + 35 / 4 * L * (s - L) ^ 2 + 15 * L * (s - L) * (1 - s) + 7 / 4 * (s - L) ^ 3
      + 15 / 4 * (s - L) ^ 2 * (1 - s)) := by
    have t1 : 0 ≤ 10 * L ^ 2 * (s - L) := by positivity
    have t2 : 0 ≤ 15 * L ^ 2 * (1 - s) := by positivity
    have t3 : 0 ≤ 35 / 4 * L * (s - L) ^ 2 := by positivity
    have t4 : 0 ≤ 15 * L * (s - L) * (1 - s) := by positivity
    have t5 : 0 ≤ 7 / 4 * (s - L) ^ 3 := by positivity
    have t6 : 0 ≤ 15 / 4 * (s - L) ^ 2 * (1 - s) := by positivity
    have : 0 ≤ (s - L) ^ 2 / 2 := by positivity
    apply mul_nonneg this
    linarith
  linarith

lemma psi6_bound (a xs x t ψ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxs : xs ≤ x) (hx1 : x ≤ 1) (hxs0 : a / 2 ≤ xs) (hxs1 : xs ≤ 1) (hψ0 : 0 ≤ ψ)
    (hψ : ψ ^ 2 ≤ Bf a x t ^ 5) : ψ ≤ B6f a xs t := by
  set L := 1 - a * xs * t with hL
  set δ := a ^ 2 * t ^ 2 * (1 - xs ^ 2) with hδ
  have hxs00 : 0 ≤ xs := by linarith
  have hat : a * t ≤ 1 := by nlinarith
  have hL0 : 0 ≤ L := by
    have : a * xs * t ≤ 1 := by
      have h1 : a * xs * t ≤ a * 1 * t := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxs1 ha0.le) ht0
      nlinarith
    linarith
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ 1 - xs ^ 2 := by nlinarith
    positivity
  have hβ : Bf a xs t = L ^ 2 + δ := by rw [hL, hδ]; unfold Bf; ring
  have hβ1 : Bf a xs t ≤ 1 := by
    unfold Bf
    have : a * t * (a * t - 2 * xs) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      nlinarith
    nlinarith
  have hβx : Bf a x t ≤ Bf a xs t := Bf_anti a xs x t ha0.le ht0 hxs
  have hβx0 : 0 ≤ Bf a x t := Bf_nonneg a x t ha0.le ht0 hx1
  set s := Real.sqrt (Bf a xs t) with hs
  have hs2 : s ^ 2 = Bf a xs t := Real.sq_sqrt (le_trans hβx0 hβx)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sqrt_le_one.mpr hβ1
  have hLs : L ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    rw [hβ]; linarith
  have hT := taylor6 L s hL0 hLs hs1
  have hB6 : B6f a xs t = L ^ 5 + 5 / 2 * L ^ 3 * (s ^ 2 - L ^ 2) + 15 / 8 * (s ^ 2 - L ^ 2) ^ 2 := by
    have : s ^ 2 - L ^ 2 = δ := by rw [hs2, hβ]; ring
    rw [this, hL, hδ]; unfold B6f; ring
  have hψs : ψ ≤ s ^ 5 := by
    apply le_of_sq_le_sq_nonneg hψ0 (by positivity)
    calc ψ ^ 2 ≤ Bf a x t ^ 5 := hψ
      _ ≤ Bf a xs t ^ 5 := pow_le_pow_left₀ hβx0 hβx 5
      _ = (s ^ 5) ^ 2 := by rw [← hs2]; ring
  rw [hB6]
  linarith

lemma final_generic (m : ℝ) (hm : 0 < m) (a x xs : ℝ) (ha0 : 0 < a) (hxs0 : 0 ≤ xs)
    (φ ψ Φ Ψ : ℝ → ℝ) (hφc : Continuous φ) (hψc : Continuous ψ) (hΦc : Continuous Φ)
    (hΨc : Continuous Ψ)
    (hP : 1 ≤ ∫ t in (0:ℝ)..1, φ t)
    (hO : m * (1 - a ^ 2) + a * x ≤
      (1 - x ^ 2) / (2 * m) + (m + 1) * (a ^ 2 * m * ∫ t in (0:ℝ)..1, t * ψ t))
    (h1 : x ≤ xs → ∀ t ∈ Set.Icc (0:ℝ) 1, φ t ≤ Φ t)
    (h2 : xs ≤ x → ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ≤ Ψ t)
    (hnP : ∫ t in (0:ℝ)..1, Φ t < 1)
    (hnO : (1 - xs ^ 2) / (2 * m) + (m + 1) * (a ^ 2 * m * ∫ t in (0:ℝ)..1, t * Ψ t)
      < m * (1 - a ^ 2) + a * xs) : False := by
  rcases le_total x xs with hle | hle
  · have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
      (hφc.intervalIntegrable 0 1)
      (hΦc.intervalIntegrable 0 1) (h1 hle)
    linarith
  · have hI : ∫ t in (0:ℝ)..1, t * ψ t ≤ ∫ t in (0:ℝ)..1, t * Ψ t :=
      intervalIntegral.integral_mono_on zero_le_one
        ((continuous_id.mul hψc).intervalIntegrable 0 1)
        ((continuous_id.mul hΨc).intervalIntegrable 0 1)
        (fun t ht => mul_le_mul_of_nonneg_left (h2 hle t ht) ht.1)
    have hx2 : xs ^ 2 ≤ x ^ 2 := by nlinarith
    have h3 : (1 - x ^ 2) / (2 * m) ≤ (1 - xs ^ 2) / (2 * m) := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have h4 : a * xs ≤ a * x := mul_le_mul_of_nonneg_left hle ha0.le
    have h5 : (m + 1) * (a ^ 2 * m * ∫ t in (0:ℝ)..1, t * ψ t)
        ≤ (m + 1) * (a ^ 2 * m * ∫ t in (0:ℝ)..1, t * Ψ t) := by
      have : 0 ≤ a ^ 2 * m := by positivity
      have h6 := mul_le_mul_of_nonneg_left hI this
      have : 0 ≤ m + 1 := by linarith
      exact mul_le_mul_of_nonneg_left h6 this
    linarith

lemma final_m5 (a x : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hx : -1 ≤ x) (hx1 : x ≤ 1)
    (φ ψ : ℝ → ℝ) (hφc : Continuous φ) (hψc : Continuous ψ) (hφ0 : ∀ t, 0 ≤ φ t)
    (hφ : ∀ t ∈ Set.Icc (0:ℝ) 1, φ t ^ 2 ≤ Qf a x t ^ 5) (hψ0 : ∀ t, 0 ≤ ψ t)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ^ 2 ≤ Bf a x t ^ 4)
    (hP : 1 ≤ ∫ t in (0:ℝ)..1, φ t)
    (hO : 5 * (1 - a ^ 2) + a * x ≤
      (1 - x ^ 2) / (2 * 5) + (5 + 1) * (a ^ 2 * 5 * ∫ t in (0:ℝ)..1, t * ψ t)) : False := by
  set xs := (1 + 3 * a) / 4 with hxs
  refine final_generic 5 (by norm_num) a x xs ha0 (by positivity) φ ψ
    (fun t => Qf a xs t ^ 2 * (1 + Qf a xs t) / 2) (fun t => Bf a xs t ^ 2)
    hφc hψc (by unfold Qf; fun_prop) (by unfold Bf; fun_prop) hP hO ?_ ?_ (num_P5 a ha0 ha1)
    (num_O5 a ha0 ha1)
  · intro hle t ht
    have hQ0 : 0 ≤ Qf a x t := Qf_nonneg a x t ha0.le ha1.le ht.1 hx
    have hQ : Qf a x t ≤ Qf a xs t := Qf_mono a x xs t ha0.le ha1.le ht.1 hle
    have hQs0 : 0 ≤ Qf a xs t := le_trans hQ0 hQ
    apply le_of_sq_le_sq_nonneg (hφ0 t) (by positivity)
    calc φ t ^ 2 ≤ Qf a x t ^ 5 := hφ t ht
      _ ≤ Qf a xs t ^ 5 := pow_le_pow_left₀ hQ0 hQ 5
      _ ≤ (Qf a xs t ^ 2 * (1 + Qf a xs t) / 2) ^ 2 := by
          nlinarith [mul_nonneg (pow_nonneg hQs0 4) (sq_nonneg (1 - Qf a xs t))]
  · intro hle t ht
    have hB0 : 0 ≤ Bf a x t := Bf_nonneg a x t ha0.le ht.1 hx1
    have hB : Bf a x t ≤ Bf a xs t := Bf_anti a xs x t ha0.le ht.1 hle
    apply le_of_sq_le_sq_nonneg (hψ0 t) (by positivity)
    calc ψ t ^ 2 ≤ Bf a x t ^ 4 := hψ t ht
      _ ≤ Bf a xs t ^ 4 := pow_le_pow_left₀ hB0 hB 4
      _ = (Bf a xs t ^ 2) ^ 2 := by ring

lemma final_m6 (a x : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hx : -1 ≤ x) (hx1 : x ≤ 1)
    (φ ψ : ℝ → ℝ) (hφc : Continuous φ) (hψc : Continuous ψ) (hφ0 : ∀ t, 0 ≤ φ t)
    (hφ : ∀ t ∈ Set.Icc (0:ℝ) 1, φ t ^ 2 ≤ Qf a x t ^ 6) (hψ0 : ∀ t, 0 ≤ ψ t)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ^ 2 ≤ Bf a x t ^ 5)
    (hP : 1 ≤ ∫ t in (0:ℝ)..1, φ t)
    (hO : 6 * (1 - a ^ 2) + a * x ≤
      (1 - x ^ 2) / (2 * 6) + (6 + 1) * (a ^ 2 * 6 * ∫ t in (0:ℝ)..1, t * ψ t)) : False := by
  set xs := (1 + 3 * a) / 4 with hxs
  refine final_generic 6 (by norm_num) a x xs ha0 (by positivity) φ ψ
    (fun t => Qf a xs t ^ 3) (fun t => B6f a xs t)
    hφc hψc (by unfold Qf; fun_prop) (by unfold B6f; fun_prop) hP hO ?_ ?_ (num_P6 a ha0 ha1)
    (num_O6 a ha0 ha1)
  · intro hle t ht
    have hQ0 : 0 ≤ Qf a x t := Qf_nonneg a x t ha0.le ha1.le ht.1 hx
    have hQ : Qf a x t ≤ Qf a xs t := Qf_mono a x xs t ha0.le ha1.le ht.1 hle
    have hQs0 : 0 ≤ Qf a xs t := le_trans hQ0 hQ
    apply le_of_sq_le_sq_nonneg (hφ0 t) (by positivity)
    calc φ t ^ 2 ≤ Qf a x t ^ 6 := hφ t ht
      _ ≤ Qf a xs t ^ 6 := pow_le_pow_left₀ hQ0 hQ 6
      _ = (Qf a xs t ^ 3) ^ 2 := by ring
  · intro hle t ht
    exact psi6_bound a xs x t (ψ t) ha0 ha1 ht.1 ht.2 hle hx1 (by rw [hxs]; linarith)
      (by rw [hxs]; linarith) (hψ0 t) (hψ t ht)

lemma final_m7 (a x : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hx : -1 ≤ x) (hx1 : x ≤ 1)
    (φ ψ : ℝ → ℝ) (hφc : Continuous φ) (hψc : Continuous ψ) (hφ0 : ∀ t, 0 ≤ φ t)
    (hφ : ∀ t ∈ Set.Icc (0:ℝ) 1, φ t ^ 2 ≤ Qf a x t ^ 7) (hψ0 : ∀ t, 0 ≤ ψ t)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ^ 2 ≤ Bf a x t ^ 6)
    (hP : 1 ≤ ∫ t in (0:ℝ)..1, φ t)
    (hO : 7 * (1 - a ^ 2) + a * x ≤
      (1 - x ^ 2) / (2 * 7) + (7 + 1) * (a ^ 2 * 7 * ∫ t in (0:ℝ)..1, t * ψ t)) : False := by
  set xs := (1 + 3 * a) / 4 with hxs
  refine final_generic 7 (by norm_num) a x xs ha0 (by positivity) φ ψ
    (fun t => Qf a xs t ^ 3 * (1 + Qf a xs t) / 2) (fun t => Bf a xs t ^ 3)
    hφc hψc (by unfold Qf; fun_prop) (by unfold Bf; fun_prop) hP hO ?_ ?_ (num_P7 a ha0 ha1)
    (num_O7 a ha0 ha1)
  · intro hle t ht
    have hQ0 : 0 ≤ Qf a x t := Qf_nonneg a x t ha0.le ha1.le ht.1 hx
    have hQ : Qf a x t ≤ Qf a xs t := Qf_mono a x xs t ha0.le ha1.le ht.1 hle
    have hQs0 : 0 ≤ Qf a xs t := le_trans hQ0 hQ
    apply le_of_sq_le_sq_nonneg (hφ0 t) (by positivity)
    calc φ t ^ 2 ≤ Qf a x t ^ 7 := hφ t ht
      _ ≤ Qf a xs t ^ 7 := pow_le_pow_left₀ hQ0 hQ 7
      _ ≤ (Qf a xs t ^ 3 * (1 + Qf a xs t) / 2) ^ 2 := by
          nlinarith [mul_nonneg (pow_nonneg hQs0 6) (sq_nonneg (1 - Qf a xs t))]
  · intro hle t ht
    have hB0 : 0 ≤ Bf a x t := Bf_nonneg a x t ha0.le ht.1 hx1
    have hB : Bf a x t ≤ Bf a xs t := Bf_anti a xs x t ha0.le ht.1 hle
    apply le_of_sq_le_sq_nonneg (hψ0 t) (pow_nonneg (le_trans hB0 hB) 3)
    calc ψ t ^ 2 ≤ Bf a x t ^ 6 := hψ t ht
      _ ≤ Bf a xs t ^ 6 := pow_le_pow_left₀ hB0 hB 6
      _ = (Bf a xs t ^ 3) ^ 2 := by ring

lemma final_small (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (φ : ℝ → ℝ) (hφc : Continuous φ)
    (hφ : ∀ t ∈ Set.Icc (0:ℝ) 1, φ t ≤ (a + t * (1 - a ^ 2)) ^ m)
    (hP : 1 ≤ ∫ t in (0:ℝ)..1, φ t) : False := by
  have hle := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
    (hφc.intervalIntegrable 0 1)
    ((by fun_prop : Continuous fun t : ℝ => (a + t * (1 - a ^ 2)) ^ m).intervalIntegrable 0 1) hφ
  interval_cases m
  · linarith [num_S1 a ha0 ha1]
  · linarith [num_S2 a ha0 ha1]
  · linarith [num_S3 a ha0 ha1]
  · linarith [num_S4 a ha0 ha1]

lemma core_interior {m : ℕ} (hm1 : 1 ≤ m) (hm7 : m ≤ 7) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {z ζ : Fin m → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) (hζ : ∀ i, 1 < ‖(a : ℂ) - ζ i‖)
    (hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) : False := by
  set q : Fin m → ℂ := fun i => ((a : ℂ) - ζ i)⁻¹ with hqdef
  have hw0 : ∀ i, (a : ℂ) - ζ i ≠ 0 := by
    intro i h
    have := hζ i
    rw [h, norm_zero] at this
    linarith
  have hq0 : ∀ i, q i ≠ 0 := fun i => inv_ne_zero (hw0 i)
  have hq : ∀ i, ‖q i‖ ≤ 1 := by
    intro i
    simp only [hqdef, norm_inv]
    exact inv_le_one_of_one_le₀ (le_of_lt (hζ i))
  have hqw : ∀ i, q i * ((a : ℂ) - ζ i) = 1 := fun i => inv_mul_cancel₀ (hw0 i)
  have hP : 1 ≤ ∫ t in (0:ℝ)..1, ∏ i, ‖(a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * q i‖ :=
    polar_main ha0 ha1 hz hζ hder
  set φ : ℝ → ℝ := fun t => ∏ i, ‖(a : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * q i‖ with hφdef
  have hφc : Continuous φ := by rw [hφdef]; fun_prop
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => prod_nonneg fun i _ => norm_nonneg _
  have hmpos : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hc : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ t * (1 - a ^ 2) := fun t ht =>
    mul_nonneg ht.1 (by nlinarith)
  rcases (show m ≤ 4 ∨ 5 ≤ m by omega) with hsmall | hbig
  · exact final_small m hm1 hsmall a ha0 ha1 φ hφc
      (fun t ht => polar_triangle a (t * (1 - a ^ 2)) ha0.le (hc t ht) q hq) hP
  -- the origin part
  set x := (∑ i, (q i).re) / m with hxdef
  have hxb : -1 ≤ x ∧ x ≤ 1 := by
    have h1 : |∑ i, (q i).re| ≤ m := by
      calc |∑ i, (q i).re| ≤ ∑ i, |(q i).re| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin m, (1 : ℝ) := sum_le_sum fun i _ =>
            (Complex.abs_re_le_norm (q i)).trans (hq i)
        _ = m := by simp
    rw [abs_le] at h1
    constructor
    · rw [hxdef, le_div_iff₀ hmr]; linarith
    · rw [hxdef, div_le_iff₀ hmr]; linarith
  set y : Fin m → ℂ := fun i => -z i with hydef
  have hy : ∀ i, ‖y i‖ ≤ 1 := fun i => by simp only [hydef, norm_neg]; exact hz i
  have haC : (0 : ℂ) ≠ (a : ℂ) := by exact_mod_cast ha0.ne
  -- first origin identity
  have hO1 : (∏ i, q i) * (∏ i, y i) = ((m : ℂ) + 1) * ∫ t in (0:ℝ)..1, Ff a q t := by
    have h := g_eval_integral hder 0 haC
    have e1 : ∏ i, ((0 : ℂ) - z i) = ∏ i, y i := by
      refine prod_congr rfl fun i _ => ?_; simp [hydef]
    rw [e1] at h
    rw [h, mul_left_comm, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Ff]
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    have := hqw i
    linear_combination this
  -- second origin identity
  have hO2 : (∏ i, q i) * ((∏ i, y i) - (a : ℂ) * ∑ i, ∏ j ∈ univ.erase i, y j)
      = ((m : ℂ) + 1) * Ff a q 1 := by
    have h := eval_at_zero hder
    have e1 : ∏ i, (-z i) - (a : ℂ) * ∑ i, ∏ j ∈ univ.erase i, (-z j)
        = (∏ i, y i) - (a : ℂ) * ∑ i, ∏ j ∈ univ.erase i, y j := rfl
    rw [← e1, h, mul_left_comm]
    congr 1
    simp only [Ff]
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    have := hqw i
    push_cast
    linear_combination this
  -- centroid in the needed form
  have hC : ((m : ℂ) + 1) * ∑ i, (q i)⁻¹ = (m : ℂ) ^ 2 * a + m * ∑ i, y i := by
    have h := centroid hmpos hder
    have e1 : ∑ i, (q i)⁻¹ = ∑ i, ((a : ℂ) - ζ i) := by
      refine sum_congr rfl fun i _ => ?_; simp [hqdef]
    have e2 : ∑ i, y i = -∑ i, z i := by simp [hydef]
    rw [e1, e2, sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    linear_combination h
  have hFb := F_bound a ha0.le q hq
  have hO := origin_alg (by omega) a ha0 ha1.le y q hy hq hq0 _ _ _ hO1 hO2 hC hFb
  rw [← hxdef] at hO
  -- the bounds on φ and ψ
  have hφ : ∀ t ∈ Set.Icc (0:ℝ) 1, φ t ^ 2 ≤ Qf a x t ^ m := by
    intro t ht
    have := polar_amgm hmpos a (t * (1 - a ^ 2)) ha0.le (hc t ht) q hq
    rw [hφdef, hxdef]; unfold Qf; exact this
  have hψ0 : ∀ t, 0 ≤ psi a q t := by
    intro t; unfold psi
    exact pow_nonneg (div_nonneg (sum_nonneg fun j _ => norm_nonneg _) hmr.le) _
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, psi a q t ^ 2 ≤ Bf a x t ^ (m - 1) := by
    intro t _
    have := psi_sq_le hmpos a q hq t
    rw [hxdef]; unfold Bf; exact this
  have hψc : Continuous (psi a q) := psi_continuous a q
  obtain rfl | rfl | rfl : m = 5 ∨ m = 6 ∨ m = 7 := by omega
  · exact final_m5 a x ha0 ha1 hxb.1 hxb.2 φ (psi a q) hφc hψc hφ0 hφ hψ0 hψ hP
      (by push_cast at hO; linarith)
  · exact final_m6 a x ha0 ha1 hxb.1 hxb.2 φ (psi a q) hφc hψc hφ0 hφ hψ0 hψ hP
      (by push_cast at hO; linarith)
  · exact final_m7 a x ha0 ha1 hxb.1 hxb.2 φ (psi a q) hφc hψc hφ0 hφ hψ0 hψ hP
      (by push_cast at hO; linarith)

lemma core_zero {m : ℕ} (hm1 : 1 ≤ m) {z ζ : Fin m → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1)
    (hζ : ∀ i, 1 < ‖((0 : ℝ) : ℂ) - ζ i‖)
    (hder : derivative ((X - C ((0 : ℝ) : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) : False := by
  have h := eval_at_zero hder
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at h
  have h1 : ‖∏ i, (-z i)‖ ≤ 1 := by
    rw [norm_prod]
    exact prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by rw [norm_neg]; exact hz i)
  have h2 : (m : ℝ) + 1 ≤ ‖((m : ℂ) + 1) * ∏ i, (-ζ i)‖ := by
    rw [norm_mul, norm_prod]
    have e : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
      have e' : (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [e', Complex.norm_natCast]; push_cast; ring
    rw [e]
    have h3 : 1 ≤ ∏ i, ‖-ζ i‖ := by
      have := prod_le_prod (s := (univ : Finset (Fin m))) (f := fun _ => (1 : ℝ))
        (g := fun i => ‖-ζ i‖) (fun i _ => zero_le_one) (fun i _ => by
          have := hζ i
          simp only [Complex.ofReal_zero, zero_sub] at this
          exact this.le)
      simpa using this
    nlinarith
  rw [h] at h1
  have : (2 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  linarith

lemma re_inv_one_sub_ge (z : ℂ) (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) : 1 / 2 ≤ ((1 - z)⁻¹).re := by
  have hz2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  have hne : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hN : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hne
  rw [Complex.inv_re, le_div_iff₀ hN]
  rw [Complex.normSq_apply] at hN ⊢
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub] at hN ⊢
  nlinarith

lemma sum_prod_erase_eq {m : ℕ} (v : Fin m → ℂ) (hv : ∀ i, v i ≠ 0) :
    ∑ i, ∏ j ∈ univ.erase i, v j = (∏ i, v i) * ∑ i, (v i)⁻¹ := by
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_prod_erase univ v (mem_univ i)]
  field_simp [hv i]

lemma core_one {m : ℕ} (hm1 : 1 ≤ m) {z ζ : Fin m → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1)
    (hζ : ∀ i, 1 < ‖((1 : ℝ) : ℂ) - ζ i‖)
    (hder : derivative ((X - C ((1 : ℝ) : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i))) : False := by
  have h2 := second_deriv_at_a hder
  have h1 := eval_g_at_a hder
  simp only [Complex.ofReal_one] at h1 h2 hζ
  have hw0 : ∀ i, (1 : ℂ) - ζ i ≠ 0 := by
    intro i h
    have := hζ i
    rw [h, norm_zero] at this
    linarith
  have hn0 : ((m : ℂ) + 1) ≠ 0 := by
    have : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero m
  have hW0 : ∏ i, ((1 : ℂ) - ζ i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hw0 i
  have hG0 : ∏ i, ((1 : ℂ) - z i) ≠ 0 := by rw [h1]; exact mul_ne_zero hn0 hW0
  have hz0 : ∀ i, (1 : ℂ) - z i ≠ 0 := fun i => (prod_ne_zero_iff.mp hG0) i (mem_univ i)
  rw [sum_prod_erase_eq _ hz0, sum_prod_erase_eq _ hw0, h1] at h2
  -- h2 : 2 * (n * W * Σ 1/(1-z)) = n * (W * Σ 1/(1-ζ))
  have key : ∑ i, ((1 : ℂ) - ζ i)⁻¹ = 2 * ∑ i, ((1 : ℂ) - z i)⁻¹ := by
    have := h2
    have hnW : ((m : ℂ) + 1) * ∏ i, ((1 : ℂ) - ζ i) ≠ 0 := mul_ne_zero hn0 hW0
    apply mul_left_cancel₀ hnW
    linear_combination -this
  have hre := congrArg Complex.re key
  rw [Complex.re_sum, Complex.mul_re, Complex.re_sum, Complex.im_sum] at hre
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have hlt : ∑ i, (((1 : ℂ) - ζ i)⁻¹).re < ∑ _i : Fin m, (1 : ℝ) := by
    apply sum_lt_sum_of_nonempty
    · exact univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
    · intro i _
      calc (((1 : ℂ) - ζ i)⁻¹).re ≤ ‖((1 : ℂ) - ζ i)⁻¹‖ := Complex.re_le_norm _
        _ = ‖(1 : ℂ) - ζ i‖⁻¹ := norm_inv _
        _ < 1 := inv_lt_one_of_one_lt₀ (hζ i)
  have hge : ∑ _i : Fin m, (1 / 2 : ℝ) ≤ ∑ i, (((1 : ℂ) - z i)⁻¹).re := by
    apply sum_le_sum
    intro i _
    exact re_inv_one_sub_ge (z i) (hz i) (fun h => hz0 i (by rw [h]; ring))
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt hge
  linarith

lemma multiset_enum : ∀ (m : ℕ) (s : Multiset ℂ), Multiset.card s = m →
    ∃ v : Fin m → ℂ, (∀ i, v i ∈ s) ∧ (s.map fun r => X - C r).prod = ∏ i, (X - C (v i))
  | 0, s, hs => by
    have : s = 0 := Multiset.card_eq_zero.mp hs
    subst this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩
  | k + 1, s, hs => by
    obtain ⟨a, ha⟩ : ∃ a, a ∈ s := Multiset.card_pos_iff_exists_mem.mp (by omega)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    have ht : Multiset.card t = k := by simpa using hs
    obtain ⟨v, hv1, hv2⟩ := multiset_enum k t ht
    refine ⟨Fin.cons a v, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro j
        simp only [Fin.cons_succ]
        exact Multiset.mem_cons_of_mem (hv1 j)
    · rw [Multiset.map_cons, Multiset.prod_cons, hv2, Fin.prod_univ_succ]
      simp

theorem core_poly (p : ℂ[X]) (n : ℕ) (hn2 : 2 ≤ n) (hn8 : n ≤ 8) (hdeg : p.natDegree = n)
    (hroots : ∀ w, p.IsRoot w → ‖w‖ ≤ 1) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : p.IsRoot (a : ℂ)) : ∃ ζ, (derivative p).IsRoot ζ ∧ ‖ζ - a‖ ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have hp0 : p ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm7 : m ≤ 7 := by omega
  have hcard : Multiset.card p.roots = p.natDegree :=
    (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hmem : (a : ℂ) ∈ p.roots := (mem_roots hp0).mpr ha
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hmem
  have hscard : Multiset.card s = m := by
    have := hcard
    rw [hs, Multiset.card_cons, hdeg] at this
    omega
  obtain ⟨z, hz1, hz2⟩ := multiset_enum m s hscard
  have hdp0 : derivative p ≠ 0 := by
    intro h
    rw [derivative_eq_zero] at h
    omega
  have hdeg' : (derivative p).natDegree = m := by
    rw [natDegree_derivative, hdeg]; omega
  have hcard' : Multiset.card (derivative p).roots = m := by
    rw [← hdeg']
    exact (IsAlgClosed.splits (derivative p)).natDegree_eq_card_roots.symm
  obtain ⟨ζ, hζ1, hζ2⟩ := multiset_enum m (derivative p).roots hcard'
  have hpf : p = C p.leadingCoeff * ((X - C (a : ℂ)) * ∏ i, (X - C (z i))) := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [hs, Multiset.map_cons, Multiset.prod_cons, hz2]
  have hdpf : derivative p = C (derivative p).leadingCoeff * ∏ i, (X - C (ζ i)) := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (hcard'.trans hdeg'.symm)]
    rw [hζ2]
  have hlead : (derivative p).leadingCoeff = p.leadingCoeff * ((m : ℂ) + 1) := by
    rw [leadingCoeff_derivative, hdeg]; push_cast; ring
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hder : derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i)))
      = C ((m : ℂ) + 1) * ∏ i, (X - C (ζ i)) := by
    have h1 : derivative p
        = C p.leadingCoeff * derivative ((X - C (a : ℂ)) * ∏ i, (X - C (z i))) := by
      conv_lhs => rw [hpf]
      rw [derivative_C_mul]
    rw [hdpf, hlead, C_mul, mul_assoc] at h1
    exact (mul_left_cancel₀ (C_ne_zero.mpr hc0) h1).symm
  have hz : ∀ i, ‖z i‖ ≤ 1 := by
    intro i
    apply hroots
    have : z i ∈ p.roots := by rw [hs]; exact Multiset.mem_cons_of_mem (hz1 i)
    exact (mem_roots hp0).mp this
  have hζ : ∀ i, 1 < ‖(a : ℂ) - ζ i‖ := by
    intro i
    have h1 : (derivative p).IsRoot (ζ i) := (mem_roots hdp0).mp (hζ1 i)
    have h2 := hcon _ h1
    rwa [← norm_neg, neg_sub]
  rcases eq_or_lt_of_le ha0 with h0 | h0
  · subst h0
    exact core_zero hm1 hz hζ hder
  rcases eq_or_lt_of_le ha1 with h1 | h1
  · subst h1
    exact core_one hm1 hz hζ hder
  exact core_interior hm1 hm7 h0 h1 hz hζ hder

theorem sendov_le8 (n : ℕ) (hn : n ∈ Set.Icc 2 8) : Sendov.Nat.SatisfiesSendovConjecture n := by
  intro f hf hdeg z hz
  obtain ⟨hdeg2, hroots⟩ := hf
  have hf0 : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg2; omega
  have hzroot : f.IsRoot z := by
    have := (mem_rootSet.mp hz).2
    simpa [aeval_def] using this
  have hroots' : ∀ w, f.IsRoot w → ‖w‖ ≤ 1 := by
    intro w hw
    have hw' : w ∈ f.rootSet ℂ := mem_rootSet.mpr ⟨hf0, by simpa [aeval_def] using hw⟩
    have := hroots hw'
    simpa [mem_closedBall_zero_iff] using this
  set u : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ) with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr h)]
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  have huz : u * (‖z‖ : ℂ) = z := by
    rw [hu]
    split_ifs with h
    · simp [h]
    · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      field_simp
  set g := f.comp (C u * X) with hg
  have hgeval : ∀ w, g.eval w = f.eval (u * w) := by
    intro w; simp [hg, eval_comp]
  have hgdeg : g.natDegree = n := by
    rw [hg, natDegree_comp, natDegree_C_mul_X u hu0, hdeg, mul_one]
  have hgroots : ∀ w, g.IsRoot w → ‖w‖ ≤ 1 := by
    intro w hw
    have h1 : f.IsRoot (u * w) := by
      have := hw.eq_zero
      rw [hgeval] at this
      exact this
    have h2 := hroots' _ h1
    rwa [norm_mul, hu1, one_mul] at h2
  have hga : g.IsRoot ((‖z‖ : ℝ) : ℂ) := by
    show g.eval _ = 0
    rw [hgeval, huz]
    exact hzroot
  obtain ⟨ζ', hζ'1, hζ'2⟩ := core_poly g n hn.1 hn.2 hgdeg hgroots ‖z‖ (norm_nonneg z)
    (hroots' z hzroot) hga
  have hgder : derivative g = C u * (derivative f).comp (C u * X) := by
    rw [hg, derivative_comp, derivative_C_mul_X]
  have hfζ : (derivative f).IsRoot (u * ζ') := by
    have h1 := hζ'1.eq_zero
    rw [hgder, eval_mul, eval_C, eval_comp] at h1
    simp only [eval_mul, eval_C, eval_X] at h1
    exact (mul_eq_zero.mp h1).resolve_left hu0
  have hdf0 : derivative f ≠ 0 := by
    intro h
    rw [derivative_eq_zero] at h
    omega
  have hmem : u * ζ' ∈ (derivative f).rootSet ℂ :=
    mem_rootSet.mpr ⟨hdf0, by simpa [aeval_def] using hfζ⟩
  calc Metric.infDist z ((derivative f).rootSet ℂ) ≤ dist z (u * ζ') :=
        Metric.infDist_le_dist_of_mem hmem
    _ = ‖z - u * ζ'‖ := dist_eq_norm _ _
    _ = ‖u * ζ' - u * (‖z‖ : ℂ)‖ := by rw [huz, norm_sub_rev]
    _ = ‖ζ' - (‖z‖ : ℂ)‖ := by rw [← mul_sub, norm_mul, hu1, one_mul]
    _ ≤ 1 := hζ'2

end OMA.Helpers.SendovLE8

theorem OMA.solution : type_of% @Sendov.sendov_conjecture.variants.le_eight := by
  intro n hn
  exact OMA.Helpers.SendovLE8.sendov_le8 n hn
