import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1

/-!
# Step H3 of the reduction Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.H2.R1

Write psi(y) = fract(y) - 1/2 and F(y) = B2(fract y) = fract(y) ^ 2 - fract(y) + 1/6, the
periodic second Bernoulli function. The summand is floor(x) - x + 1/2 = -psi(x).

1. Pointwise sandwich (0 < d < 1): F(y + d) - F(y) is at most 2 d psi(y) + d ^ 2, and
   F(y) - F(y + d) is at most -2 d psi(y + d) + d ^ 2. Summing over the points gives
   |sum psi| at most K / d + n d / 2 whenever every shifted sum of F is bounded by K.
2. Fourier bound: pi ^ 2 F(y) is the sum over n of cos(2 pi n y) / n ^ 2 (Mathlib's Fourier
   series of the Bernoulli polynomials). For 1 at most n at most H the cosine sum over the
   points is bounded by the exponential sum hypothesis, and for larger n by the number of
   points times the tail of the series of 1 / n ^ 2, which is at most 2 / (H + 1).
3. With n at most N ^ 504 points, H = N ^ 20 and d = N ^ (-6) the bound is far below
   1000 N ^ 498.
-/

open Finset

namespace OMA.Helpers

/-- The additive character x to exp(2 pi i x). -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The periodic second Bernoulli function. -/
noncomputable def FF (y : ℝ) : ℝ := Int.fract y ^ 2 - Int.fract y + 6⁻¹

theorem ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem ee_re (y : ℝ) : (ee y).re = Real.cos (2 * Real.pi * y) := by
  unfold ee
  exact Complex.exp_ofReal_mul_I_re _

theorem FF_step (y δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    FF (y + δ) - FF y ≤ 2 * δ * (Int.fract y - 1 / 2) + δ ^ 2 ∧
      FF y - FF (y + δ) ≤ -(2 * δ * (Int.fract (y + δ) - 1 / 2)) + δ ^ 2 := by
  obtain ⟨z, hz⟩ := Int.fract_add y δ
  have hfδ : Int.fract δ = δ := Int.fract_eq_self.mpr ⟨hδ.le, hδ1⟩
  rw [hfδ] at hz
  have f0 := Int.fract_nonneg y
  have f1 := Int.fract_lt_one y
  have g0 := Int.fract_nonneg (y + δ)
  have g1 := Int.fract_lt_one (y + δ)
  have hz1 : ((-2 : ℤ) : ℝ) < z := by push_cast; linarith
  have hz2 : (z : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
  have hz1' : (-2 : ℤ) < z := by exact_mod_cast hz1
  have hz2' : z < 1 := by exact_mod_cast hz2
  have hcases : z = 0 ∨ z = -1 := by omega
  unfold FF
  rcases hcases with rfl | rfl
  · have hg : Int.fract (y + δ) = Int.fract y + δ := by push_cast at hz; linarith
    rw [hg]
    constructor <;> nlinarith
  · have hg : Int.fract (y + δ) = Int.fract y + δ - 1 := by push_cast at hz; linarith
    rw [hg]
    rw [hg] at g0
    constructor <;> nlinarith

theorem sum_psi_bound {ι : Type*} (S : Finset ι) (x : ι → ℝ) (K δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hK : ∀ s : ℝ, |∑ i ∈ S, FF (x i + s)| ≤ K) :
    |∑ i ∈ S, (Int.fract (x i) - 1 / 2)| ≤ K / δ + S.card * δ / 2 := by
  have h1 : ∑ i ∈ S, (FF (x i + δ) - FF (x i)) ≤
      ∑ i ∈ S, (2 * δ * (Int.fract (x i) - 1 / 2) + δ ^ 2) :=
    sum_le_sum (fun i _ => (FF_step (x i) δ hδ hδ1).1)
  have h2 : ∑ i ∈ S, (FF (x i + -δ) - FF (x i)) ≤
      ∑ i ∈ S, (-(2 * δ * (Int.fract (x i) - 1 / 2)) + δ ^ 2) := by
    refine sum_le_sum (fun i _ => ?_)
    have h := (FF_step (x i + -δ) δ hδ hδ1).2
    rw [neg_add_cancel_right] at h
    exact h
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at h1
  rw [sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum, sum_const,
    nsmul_eq_mul] at h2
  have k1 := abs_le.mp (hK δ)
  have k2 := abs_le.mp (hK (-δ))
  have k0 := abs_le.mp (hK 0)
  simp only [add_zero] at k0
  set T := ∑ i ∈ S, (Int.fract (x i) - 1 / 2)
  set c : ℝ := (S.card : ℝ)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have e1 : K / δ + c * δ / 2 = (2 * K + c * δ ^ 2) / (2 * δ) := by
    rw [div_add_div _ _ hδ.ne' two_ne_zero, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e1]
  have h2δ : 0 < 2 * δ := by linarith
  rw [abs_le]
  constructor
  · rw [neg_le, le_div_iff₀ h2δ]
    nlinarith
  · rw [le_div_iff₀ h2δ]
    nlinarith

theorem fourier_FF (y : ℝ) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * y))
      (Real.pi ^ 2 * FF y) := by
  have hx : Int.fract y ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval (Int.fract y) =
      Int.fract y ^ 2 - Int.fract y + 6⁻¹ := bernoulliFun_two _
  rw [hb] at h
  convert h using 1
  · funext n
    have hc : Real.cos (2 * Real.pi * n * y) = Real.cos (2 * Real.pi * n * Int.fract y) := by
      rw [← Int.self_sub_floor, show 2 * Real.pi * n * (y - ⌊y⌋) =
        2 * Real.pi * n * y - (((n : ℤ) * ⌊y⌋ : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring,
        Real.cos_sub_int_mul_two_pi]
    rw [hc]
  · unfold FF
    have hf : (((2 * 1).factorial : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hf]
    ring

theorem gH_sum_le (H K : ℕ) :
    ∑ n ∈ range K, (if H < n then ((n : ℝ) ^ 2)⁻¹ else 0) ≤ 2 / ((H : ℝ) + 1) := by
  rw [← sum_filter]
  refine le_trans ?_ (sum_Ioo_inv_sq_le H K)
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [mem_filter, mem_range] at hn
    rw [mem_Ioo]
    exact ⟨hn.2, hn.1⟩
  · intro i _ _
    positivity

theorem fourier_bound {ι : Type*} (S : Finset ι) (x : ι → ℝ) (H : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hyp : ∀ n : ℕ, 1 ≤ n → n ≤ H → ‖∑ i ∈ S, ee ((n : ℝ) * x i)‖ ≤ A) (s : ℝ) :
    |∑ i ∈ S, FF (x i + s)| ≤ (2 * A + 2 * S.card / ((H : ℝ) + 1)) / Real.pi ^ 2 := by
  have hsum : HasSum (fun n : ℕ => ∑ i ∈ S, 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * (x i + s)))
      (∑ i ∈ S, Real.pi ^ 2 * FF (x i + s)) := hasSum_sum (fun i _ => fourier_FF (x i + s))
  let g : ℕ → ℕ → ℝ := fun H n => if H < n then ((n : ℝ) ^ 2)⁻¹ else 0
  have hg0 : ∀ H n, 0 ≤ g H n := by
    intro H n
    simp only [g]
    split_ifs <;> positivity
  let w : ℕ → ℝ := fun n => A * g 0 n + S.card * g H n
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    add_nonneg (mul_nonneg hA (hg0 0 n)) (mul_nonneg (Nat.cast_nonneg _) (hg0 H n))
  have hwsum : ∀ K, ∑ n ∈ range K, w n ≤ 2 * A + 2 * S.card / ((H : ℝ) + 1) := by
    intro K
    simp only [w]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have a1 := gH_sum_le 0 K
    have a2 := gH_sum_le H K
    simp only [Nat.cast_zero, zero_add, div_one] at a1
    have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have b1 := mul_le_mul_of_nonneg_left a1 hA
    have b2 := mul_le_mul_of_nonneg_left a2 hc
    have e2 : (S.card : ℝ) * (2 / ((H : ℝ) + 1)) = 2 * S.card / ((H : ℝ) + 1) := by ring
    linarith
  have hws : Summable w := summable_of_sum_range_le hw0 hwsum
  have hwt : ∑' n, w n ≤ 2 * A + 2 * S.card / ((H : ℝ) + 1) :=
    Real.tsum_le_of_sum_range_le hw0 hwsum
  have hterm : ∀ n : ℕ,
      |∑ i ∈ S, 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * (x i + s))| ≤ w n := by
    intro n
    rw [← mul_sum]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        div_zero, zero_mul, abs_zero]
      exact hw0 0
    · set C := ∑ i ∈ S, Real.cos (2 * Real.pi * n * (x i + s))
      have hnr : (0 : ℝ) < (n : ℝ) ^ 2 := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      have hC1 : |C| ≤ S.card := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i ∈ S, |Real.cos (2 * Real.pi * n * (x i + s))| ≤ ∑ _i ∈ S, (1 : ℝ) :=
              sum_le_sum (fun i _ => Real.abs_cos_le_one _)
          _ = S.card := by rw [sum_const, nsmul_eq_mul, mul_one]
      have habs : |1 / (n : ℝ) ^ 2 * C| = ((n : ℝ) ^ 2)⁻¹ * |C| := by
        rw [abs_mul, one_div, abs_of_pos (inv_pos.mpr hnr)]
      rw [habs]
      have hg00 : g 0 n = ((n : ℝ) ^ 2)⁻¹ := by
        simp only [g]
        rw [if_pos hn]
      by_cases hnH : n ≤ H
      · have hC2 : |C| ≤ A := by
          have e1 : C = (∑ i ∈ S, ee ((n : ℝ) * (x i + s))).re := by
            rw [Complex.re_sum]
            refine sum_congr rfl (fun i _ => ?_)
            rw [ee_re]
            congr 1
            ring
          have e2 : ∑ i ∈ S, ee ((n : ℝ) * (x i + s)) =
              ee ((n : ℝ) * s) * ∑ i ∈ S, ee ((n : ℝ) * x i) := by
            rw [mul_sum]
            refine sum_congr rfl (fun i _ => ?_)
            rw [← ee_add]
            congr 1
            ring
          rw [e1, e2]
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, norm_ee, one_mul]
          exact hyp n hn hnH
        have hgH : 0 ≤ g H n := hg0 H n
        calc ((n : ℝ) ^ 2)⁻¹ * |C| ≤ ((n : ℝ) ^ 2)⁻¹ * A :=
              mul_le_mul_of_nonneg_left hC2 (inv_pos.mpr hnr).le
          _ = A * g 0 n := by rw [hg00, mul_comm]
          _ ≤ A * g 0 n + S.card * g H n := by
              have : (0 : ℝ) ≤ S.card * g H n := mul_nonneg (Nat.cast_nonneg _) hgH
              linarith
      · have hgHn : g H n = ((n : ℝ) ^ 2)⁻¹ := by
          simp only [g]
          rw [if_pos (by omega)]
        calc ((n : ℝ) ^ 2)⁻¹ * |C| ≤ ((n : ℝ) ^ 2)⁻¹ * S.card :=
              mul_le_mul_of_nonneg_left hC1 (inv_pos.mpr hnr).le
          _ = S.card * g H n := by rw [hgHn, mul_comm]
          _ ≤ A * g 0 n + S.card * g H n := by
              have : (0 : ℝ) ≤ A * g 0 n := mul_nonneg hA (hg0 0 n)
              linarith
  have up : ∑ i ∈ S, Real.pi ^ 2 * FF (x i + s) ≤ ∑' n, w n :=
    hasSum_le (fun n => (abs_le.mp (hterm n)).2) hsum hws.hasSum
  have lo : -(∑' n, w n) ≤ ∑ i ∈ S, Real.pi ^ 2 * FF (x i + s) :=
    hasSum_le (fun n => (abs_le.mp (hterm n)).1) hws.hasSum.neg hsum
  rw [← mul_sum] at up lo
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hab : |Real.pi ^ 2 * ∑ i ∈ S, FF (x i + s)| ≤ ∑' n, w n := abs_le.mpr ⟨lo, up⟩
  rw [abs_mul, abs_of_pos hπ] at hab
  rw [le_div_iff₀ hπ]
  linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.H3 := by
  intro N t hN J P u e hyp
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hn0 : (0 : ℝ) < N := by linarith
  let x : ℕ × ℕ → ℝ := fun w => u w.1 w.2
  have hsummand : ∀ w ∈ P ×ˢ P, (((t / (w.1 * w.2) : ℕ) : ℝ) - u w.1 w.2) + 1 / 2 =
      -(Int.fract (x w) - 1 / 2) := by
    intro w _
    have hx0 : 0 ≤ x w := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h1 : (((t / (w.1 * w.2) : ℕ) : ℝ)) = ((⌊x w⌋ : ℤ) : ℝ) := by
      rw [← natCast_floor_eq_intCast_floor hx0]
      congr 1
      exact (Nat.floor_div_eq_div t (w.1 * w.2)).symm
    rw [h1, ← Int.self_sub_floor]
    ring
  rw [sum_congr rfl hsummand, sum_neg_distrib, abs_neg]
  have hA : ∀ n : ℕ, 1 ≤ n → n ≤ N ^ 20 →
      ‖∑ w ∈ P ×ˢ P, OMA.Helpers.ee ((n : ℝ) * x w)‖ ≤ 10 * (N : ℝ) ^ 484 := hyp
  have hA0 : (0 : ℝ) ≤ 10 * (N : ℝ) ^ 484 := by positivity
  have hK := OMA.Helpers.fourier_bound (P ×ˢ P) x (N ^ 20) (10 * (N : ℝ) ^ 484) hA0 hA
  have hδ : (0 : ℝ) < ((N : ℝ) ^ 6)⁻¹ := by positivity
  have hN6 : (1 : ℝ) < (N : ℝ) ^ 6 := one_lt_pow₀ (by linarith) (by norm_num)
  have hδ1 : ((N : ℝ) ^ 6)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN6
  have hD := OMA.Helpers.sum_psi_bound (P ×ˢ P) x _ _ hδ hδ1 hK
  refine hD.trans ?_
  -- numerical bound
  have hPcard : P.card ≤ N ^ 252 := by
    calc P.card ≤ J.card := card_filter_le _ _
      _ = N ^ 252 - N ^ 251 := Nat.card_Ioc _ _
      _ ≤ N ^ 252 := Nat.sub_le _ _
  have hScard : ((P ×ˢ P).card : ℝ) ≤ (N : ℝ) ^ 504 := by
    have h : (P ×ˢ P).card ≤ N ^ 504 := by
      rw [card_product]
      calc P.card * P.card ≤ N ^ 252 * N ^ 252 := Nat.mul_le_mul hPcard hPcard
        _ = N ^ 504 := by rw [← pow_add]
    exact_mod_cast h
  have hS0 : (0 : ℝ) ≤ ((P ×ˢ P).card : ℝ) := Nat.cast_nonneg _
  set c : ℝ := ((P ×ˢ P).card : ℝ)
  have hpi : (2 : ℝ) ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hH : (((N ^ 20 : ℕ) : ℝ) + 1) = (N : ℝ) ^ 20 + 1 := by push_cast; ring
  rw [hH]
  have hN20 : (0 : ℝ) < (N : ℝ) ^ 20 + 1 := by positivity
  -- c / (N^20 + 1) ≤ N^484
  have q1 : c / ((N : ℝ) ^ 20 + 1) ≤ (N : ℝ) ^ 484 := by
    rw [div_le_iff₀ hN20]
    have e : (N : ℝ) ^ 484 * ((N : ℝ) ^ 20 + 1) = (N : ℝ) ^ 504 + (N : ℝ) ^ 484 := by ring
    rw [e]
    have : (0 : ℝ) ≤ (N : ℝ) ^ 484 := by positivity
    linarith
  -- the Fourier constant K
  have q2 : (2 * (10 * (N : ℝ) ^ 484) + 2 * c / ((N : ℝ) ^ 20 + 1)) / Real.pi ^ 2 ≤
      11 * (N : ℝ) ^ 484 := by
    rw [div_le_iff₀ (by positivity)]
    have e : 2 * c / ((N : ℝ) ^ 20 + 1) = 2 * (c / ((N : ℝ) ^ 20 + 1)) := by ring
    rw [e]
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ 484 := by positivity
    have hq : 0 ≤ c / ((N : ℝ) ^ 20 + 1) := div_nonneg hS0 hN20.le
    nlinarith
  set K := (2 * (10 * (N : ℝ) ^ 484) + 2 * c / ((N : ℝ) ^ 20 + 1)) / Real.pi ^ 2
  have q3 : K / ((N : ℝ) ^ 6)⁻¹ ≤ 11 * (N : ℝ) ^ 490 := by
    rw [div_inv_eq_mul]
    have e : 11 * (N : ℝ) ^ 490 = 11 * (N : ℝ) ^ 484 * (N : ℝ) ^ 6 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right q2 (by positivity)
  have q4 : c * ((N : ℝ) ^ 6)⁻¹ / 2 ≤ (N : ℝ) ^ 498 := by
    have e : (N : ℝ) ^ 504 * ((N : ℝ) ^ 6)⁻¹ = (N : ℝ) ^ 498 := by
      rw [show (N : ℝ) ^ 504 = (N : ℝ) ^ 498 * (N : ℝ) ^ 6 by ring, mul_assoc,
        mul_inv_cancel₀ (by positivity), mul_one]
    have h1 : c * ((N : ℝ) ^ 6)⁻¹ ≤ (N : ℝ) ^ 504 * ((N : ℝ) ^ 6)⁻¹ :=
      mul_le_mul_of_nonneg_right hScard hδ.le
    rw [e] at h1
    have : (0 : ℝ) ≤ (N : ℝ) ^ 498 := by positivity
    linarith
  have q5 : (N : ℝ) ^ 490 ≤ (N : ℝ) ^ 498 := pow_le_pow_right₀ hn1 (by norm_num)
  have q6 : (0 : ℝ) ≤ (N : ℝ) ^ 498 := by positivity
  linarith
