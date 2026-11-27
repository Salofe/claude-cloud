import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2

/-!
# Step H1 of the reduction PoincareConjecture.poincare_conjecture.R1.H4.R1.H2.R1.H1.R2

The scalar comparison: write `Φ w t = w t * (4 t + 1) ^ (-3/4) + 2 π (4 t + 1) ^ (1/4)`.
On each piece `[t i, t (i+1)]` the function `Φ (w i)` is continuous and its lower right Dini
derivative is at most `0`, so it is nonincreasing there (Mathlib's comparison principle
`image_le_of_liminf_slope_right_le_deriv_boundary` against a constant barrier). At the junction
times the width only drops, and the factor `(4 t + 1) ^ (-3/4)` is positive, so `Φ` only drops.
Chaining the pieces gives `Φ (w n) (t n) ≤ Φ (w 0) 0 = w 0 0 + 2 π`. Since `w n (t n) ≥ 0`, this
gives `2 π (4 t n + 1) ^ (1/4) ≤ w 0 0 + 2 π`; raising to the fourth power gives the bound.
-/

namespace OMA.Helpers

open Set Filter Topology

/-- A function continuous on `[a, b]` whose lower right Dini derivative is at most `0` on
`[a, b)` satisfies `f b ≤ f a`. -/
theorem dini_antitone_endpoint (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ r > 0, ∃ᶠ y in 𝓝[>] x, (y - x)⁻¹ * (f y - f x) < r) :
    f b ≤ f a := by
  have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := f) (a := a) (b := b) hf
    (B := fun _ => f a) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const x _ (f a))
    (fun x hx r hr => by
      have := hd x hx r hr
      simpa only [slope, vsub_eq_sub, smul_eq_mul] using this)
  exact key ⟨hab, le_rfl⟩

/-- The power `(4 t + 1) ^ p` is continuous on any set of nonnegative reals. -/
theorem continuousOn_four_mul_add_one_rpow (s : Set ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (p : ℝ) :
    ContinuousOn (fun x : ℝ => (4 * x + 1) ^ p) s := by
  apply ContinuousOn.rpow_const
  · exact (continuousOn_const.mul continuousOn_id).add continuousOn_const
  · intro x hx
    left
    have := hs x hx
    exact ne_of_gt (by linarith)

/-- The quantity `Φ` of the reduction, written as a named function. -/
noncomputable def phi (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t * (4 * t + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * t + 1) ^ (1 / 4 : ℝ)

end OMA.Helpers

open Set Filter Topology

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2.H1 := by
  intro n t w ht0 hmono hcont hdini hjump hw0 hwn
  let Φ := OMA.Helpers.phi
  have htnn : ∀ i, 0 ≤ t i := fun i => by
    have := hmono (Nat.zero_le i)
    rw [ht0] at this
    exact this
  have hΦcont : ∀ i < n, ContinuousOn (Φ (w i)) (Icc (t i) (t (i + 1))) := by
    intro i hi
    have hnn : ∀ x ∈ Icc (t i) (t (i + 1)), 0 ≤ x := fun x hx => le_trans (htnn i) hx.1
    exact ((hcont i hi).mul
      (OMA.Helpers.continuousOn_four_mul_add_one_rpow _ hnn _)).add
      (continuousOn_const.mul (OMA.Helpers.continuousOn_four_mul_add_one_rpow _ hnn _))
  have key : ∀ k, k ≤ n → Φ (w k) (t k) ≤ Φ (w 0) 0 := by
    intro k
    induction k with
    | zero => intro _; rw [ht0]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : Φ (w k) (t (k + 1)) ≤ Φ (w k) (t k) :=
        OMA.Helpers.dini_antitone_endpoint _ _ _ (hmono (Nat.le_succ k))
          (hΦcont k (by omega)) (hdini k (by omega))
      have h3 : Φ (w (k + 1)) (t (k + 1)) ≤ Φ (w k) (t (k + 1)) := by
        have hj := hjump k (by omega)
        have hpos : 0 < (4 * t (k + 1) + 1) ^ (-(3 / 4) : ℝ) := by
          apply Real.rpow_pos_of_pos
          have := htnn (k + 1)
          linarith
        show w (k + 1) (t (k + 1)) * (4 * t (k + 1) + 1) ^ (-(3 / 4) : ℝ) +
            2 * Real.pi * (4 * t (k + 1) + 1) ^ (1 / 4 : ℝ) ≤
          w k (t (k + 1)) * (4 * t (k + 1) + 1) ^ (-(3 / 4) : ℝ) +
            2 * Real.pi * (4 * t (k + 1) + 1) ^ (1 / 4 : ℝ)
        have := mul_le_mul_of_nonneg_right hj hpos.le
        linarith
      linarith
  have hn := key n le_rfl
  have hT := htnn n
  have hbase : 0 < 4 * t n + 1 := by linarith
  have hΦ0 : Φ (w 0) 0 = w 0 0 + 2 * Real.pi := by
    show w 0 0 * (4 * 0 + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * 0 + 1) ^ (1 / 4 : ℝ) = _
    norm_num
  have hΦn : 2 * Real.pi * (4 * t n + 1) ^ (1 / 4 : ℝ) ≤ Φ (w n) (t n) := by
    show _ ≤ w n (t n) * (4 * t n + 1) ^ (-(3 / 4) : ℝ) +
      2 * Real.pi * (4 * t n + 1) ^ (1 / 4 : ℝ)
    have : 0 ≤ w n (t n) * (4 * t n + 1) ^ (-(3 / 4) : ℝ) :=
      mul_nonneg hwn (Real.rpow_nonneg hbase.le _)
    linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  set c : ℝ := 1 + w 0 0 / (2 * Real.pi) with hc
  have hroot : (4 * t n + 1) ^ (1 / 4 : ℝ) ≤ c := by
    have h : 2 * Real.pi * (4 * t n + 1) ^ (1 / 4 : ℝ) ≤ 2 * Real.pi * c := by
      rw [hc, mul_add, mul_div_cancel₀ _ hpi.ne', mul_one]
      linarith
    exact le_of_mul_le_mul_left h hpi
  have hrootnn : 0 ≤ (4 * t n + 1) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hbase.le _
  have hfour : ((4 * t n + 1) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = 4 * t n + 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hle : 4 * t n + 1 ≤ c ^ 4 := by
    rw [← hfour]
    exact pow_le_pow_left₀ hrootnn hroot 4
  linarith
