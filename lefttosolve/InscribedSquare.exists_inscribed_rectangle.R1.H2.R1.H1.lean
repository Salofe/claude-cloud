import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1
import Mathlib

/-!
# Step H1 of the reduction InscribedSquare.exists_inscribed_rectangle.R1.H2.R1

The capped strip (a Moebius band whose boundary circle is coned off) is the real projective
plane. We parametrize it from the sphere through the Veronese map `v ↦ v vᵀ`, which identifies
exactly antipodal points of the sphere.

* The band point `(s, t)` is sent to the spherical point with longitude `π s` and latitude
  `π (2 t - 1) / 4`; the cap point `((s, t), u)` (with `t ∈ {0, 1}`) to longitude `π s` and
  latitude `π (2 t - 1) (1 / 2 - u / 4)`. The seam of the band and the cone vertex go to
  antipodal points, so this map `Ψ` (followed by the Veronese map) descends to the quotient.
* Two parameters with the same image are glued (a direct case analysis with injectivity of
  `sin` on `[-π/2, π/2]` and of `cos` on `[0, π]`), and every point of the sphere is hit up to
  sign (spherical coordinates via `Complex.arg` and `Real.arcsin`).
* The quotient is compact and the image is Hausdorff, so the induced continuous bijection is a
  homeomorphism; the parametrization is its inverse composed with the Veronese map.

Only upstream definitions are used, together with Mathlib and the helper lemmas below.
-/

open scoped unitInterval
open Real Set

namespace OMA.Helpers

/-- Spherical coordinates with longitude `θ` and latitude `φ`. -/
noncomputable def sphP (θ φ : ℝ) : Fin 3 → ℝ := ![cos φ * cos θ, cos φ * sin θ, sin φ]

/-- The Veronese map `v ↦ v vᵀ`, which identifies exactly the pairs `v, -v` of nonzero vectors. -/
def ver (v : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => v i * v j

theorem continuous_ver : Continuous ver := by
  unfold ver
  fun_prop

theorem ver_neg (v : Fin 3 → ℝ) : ver (-v) = ver v := by
  funext i j
  simp [ver]

theorem ver_eq {v w : Fin 3 → ℝ} (hv : v ≠ 0) (h : ver v = ver w) : v = w ∨ v = -w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  have hii := congrFun (congrFun h i) i
  simp only [ver] at hii
  have hf : (v i - w i) * (v i + w i) = 0 := by linear_combination hii
  rcases mul_eq_zero.mp hf with h1 | h1
  · left
    funext j
    have hij := congrFun (congrFun h i) j
    simp only [ver] at hij
    have e : w i = v i := by linarith
    rw [e] at hij
    exact mul_left_cancel₀ hi hij
  · right
    funext j
    have hij := congrFun (congrFun h i) j
    simp only [ver] at hij
    have e : w i = - v i := by linarith
    rw [e] at hij
    have h2 : v i * v j = v i * (-w j) := by rw [hij]; ring
    simpa using mul_left_cancel₀ hi h2

theorem sphP_sq (θ φ : ℝ) :
    sphP θ φ 0 ^ 2 + sphP θ φ 1 ^ 2 + sphP θ φ 2 ^ 2 = 1 := by
  simp only [sphP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (cos φ ^ 2) * (sin_sq_add_cos_sq θ) + sin_sq_add_cos_sq φ

theorem sphP_ne_zero (θ φ : ℝ) : sphP θ φ ≠ 0 := by
  intro h
  have e := sphP_sq θ φ
  rw [h] at e
  simp at e

theorem sphP_pi_neg (ψ : ℝ) : sphP π (-ψ) = - sphP 0 ψ := by
  funext i
  fin_cases i <;> simp [sphP]

theorem seam_ver (c : ℝ) (p q : I × I)
    (h : p = q ∨ (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = σ p.2) ∨ (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = σ q.2)) :
    ver (sphP (π * p.1) (π * ((2 * p.2 - 1) * c))) =
      ver (sphP (π * q.1) (π * ((2 * q.2 - 1) * c))) := by
  rcases h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rfl
  · rw [h1, h2, h3, unitInterval.coe_symm_eq]
    have e : π * ((2 * (1 - (p.2 : ℝ)) - 1) * c) = -(π * ((2 * p.2 - 1) * c)) := by ring
    rw [e]
    simp only [Icc.coe_zero, Icc.coe_one, mul_zero, mul_one]
    rw [sphP_pi_neg, ver_neg]
  · rw [h1, h2, h3, unitInterval.coe_symm_eq]
    have e : π * ((2 * (1 - (q.2 : ℝ)) - 1) * c) = -(π * ((2 * q.2 - 1) * c)) := by ring
    rw [e]
    simp only [Icc.coe_zero, Icc.coe_one, mul_zero, mul_one]
    rw [sphP_pi_neg, ver_neg]

theorem pole_ver (θ : ℝ) (t : I) (ht : t = 0 ∨ t = 1) :
    ver (sphP θ (π * ((2 * t - 1) * (1 / 2)))) = ver ![0, 0, 1] := by
  rcases ht with rfl | rfl
  · have e : sphP θ (π * ((2 * ((0 : I) : ℝ) - 1) * (1 / 2))) = -![0, 0, 1] := by
      have e2 : π * ((2 * ((0 : I) : ℝ) - 1) * (1 / 2)) = -(π / 2) := by simp; ring
      rw [e2]
      funext i
      fin_cases i <;> simp [sphP]
    rw [e, ver_neg]
  · have e : sphP θ (π * ((2 * ((1 : I) : ℝ) - 1) * (1 / 2))) = ![0, 0, 1] := by
      have e2 : π * ((2 * ((1 : I) : ℝ) - 1) * (1 / 2)) = π / 2 := by simp; ring
      rw [e2]
      funext i
      fin_cases i <;> simp [sphP]
    rw [e]

theorem sph_cases {θ θ' φ φ' : ℝ} (hθ : θ ∈ Icc 0 π) (hθ' : θ' ∈ Icc 0 π)
    (hφ : φ ∈ Icc (-(π / 2)) (π / 2)) (hφ' : φ' ∈ Icc (-(π / 2)) (π / 2))
    (h : sphP θ φ = sphP θ' φ' ∨ sphP θ φ = -sphP θ' φ') :
    (φ = φ' ∧ (cos φ = 0 ∨ θ = θ')) ∨
      (φ = -φ' ∧ (cos φ = 0 ∨ (θ = 0 ∧ θ' = π) ∨ (θ = π ∧ θ' = 0))) := by
  rcases h with h | h
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [sphP] at h0 h1 h2
    have e : φ = φ' := injOn_sin hφ hφ' h2
    subst e
    left
    refine ⟨rfl, ?_⟩
    by_cases hc : cos φ = 0
    · exact Or.inl hc
    · exact Or.inr (injOn_cos hθ hθ' (mul_left_cancel₀ hc h0))
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [sphP] at h0 h1 h2
    have hφ'' : -φ' ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hφ'.2], by linarith [hφ'.1]⟩
    have e : φ = -φ' := injOn_sin hφ hφ'' (by rw [sin_neg]; exact h2)
    subst e
    right
    refine ⟨rfl, ?_⟩
    by_cases hc : cos (-φ') = 0
    · exact Or.inl hc
    · right
      rw [cos_neg] at hc
      have hcos : cos θ = - cos θ' := by
        apply mul_left_cancel₀ hc
        rw [cos_neg] at h0
        linarith
      have hsin : sin θ = - sin θ' := by
        apply mul_left_cancel₀ hc
        rw [cos_neg] at h1
        linarith
      have s1 := sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      have s2 := sin_nonneg_of_nonneg_of_le_pi hθ'.1 hθ'.2
      have hs : sin θ = 0 := by linarith
      have hc2 : (cos θ - 1) * (cos θ + 1) = 0 := by
        linear_combination (sin_sq_add_cos_sq θ) - sin θ * hs
      have h0m : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, pi_pos.le⟩
      have hpm : π ∈ Icc 0 π := ⟨pi_pos.le, le_rfl⟩
      rcases mul_eq_zero.mp hc2 with k | k
      · left
        constructor
        · exact injOn_cos hθ h0m (by rw [cos_zero]; linarith)
        · exact injOn_cos hθ' hpm (by rw [cos_pi]; linarith)
      · right
        constructor
        · exact injOn_cos hθ hpm (by rw [cos_pi]; linarith)
        · exact injOn_cos hθ' h0m (by rw [cos_zero]; linarith)

theorem theta_mem (s : I) : π * (s : ℝ) ∈ Icc 0 π :=
  ⟨mul_nonneg pi_pos.le s.2.1, by nlinarith [s.2.2, pi_pos]⟩

theorem lat_mem {x : ℝ} (h1 : -(1 / 2) ≤ x) (h2 : x ≤ 1 / 2) : π * x ∈ Icc (-(π / 2)) (π / 2) :=
  ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩

theorem cos_ne_zero_of {x : ℝ} (h1 : -(1 / 2) < x) (h2 : x < 1 / 2) : cos (π * x) ≠ 0 :=
  (cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩).ne'

theorem pi_mul_inj {a b : ℝ} (h : π * a = π * b) : a = b := mul_left_cancel₀ pi_ne_zero h

theorem lat_bound (t u : I) : -(1 / 2) ≤ (2 * (t : ℝ) - 1) * (1 / 2 - u / 4) ∧
    (2 * (t : ℝ) - 1) * (1 / 2 - u / 4) ≤ 1 / 2 := by
  have := t.2.1; have := t.2.2; have := u.2.1; have := u.2.2
  constructor <;> nlinarith

theorem coe_I_eq {a b : I} (h : (a : ℝ) = b) : a = b := Subtype.ext h

theorem zero_of_pi {s : I} (h : π * (s : ℝ) = 0) : s = 0 :=
  Subtype.ext (pi_mul_inj (by rw [h]; simp))

theorem one_of_pi {s : I} (h : π * (s : ℝ) = π) : s = 1 :=
  Subtype.ext (pi_mul_inj (by rw [h]; simp))

/-- The common parametrization of the band (left) and the cap (right). -/
abbrev Bd := {p : I × I // p.2 = 0 ∨ p.2 = 1}

noncomputable def psiL (p : I × I) : Fin 3 → ℝ :=
  sphP (π * p.1) (π * ((2 * (p.2 : ℝ) - 1) * (1 / 4)))

noncomputable def psiR (w : Bd × I) : Fin 3 → ℝ :=
  sphP (π * w.1.val.1) (π * ((2 * (w.1.val.2 : ℝ) - 1) * (1 / 2 - (w.2 : ℝ) / 4)))

noncomputable def psi0 : (I × I) ⊕ (Bd × I) → Fin 3 → ℝ := Sum.elim psiL psiR

theorem continuous_sphP : Continuous (fun x : ℝ × ℝ => sphP x.1 x.2) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [sphP] <;> fun_prop

theorem continuous_sphP' {X : Type} [TopologicalSpace X] {f g : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => sphP (f x) (g x) :=
  continuous_sphP.comp (hf.prodMk hg)

theorem continuous_psiL : Continuous psiL := by
  have c1 : Continuous fun p : I × I => (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have c2 : Continuous fun p : I × I => (p.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  unfold psiL
  exact continuous_sphP' (continuous_const.mul c1)
    (continuous_const.mul (((continuous_const.mul c2).sub continuous_const).mul continuous_const))

theorem continuous_psiR : Continuous psiR := by
  have c0 : Continuous fun w : Bd × I => w.1.val :=
    continuous_subtype_val.comp continuous_fst
  have c1 : Continuous fun w : Bd × I => (w.1.val.1 : ℝ) :=
    continuous_subtype_val.comp (continuous_fst.comp c0)
  have c2 : Continuous fun w : Bd × I => (w.1.val.2 : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp c0)
  have c3 : Continuous fun w : Bd × I => (w.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  unfold psiR
  exact continuous_sphP' (continuous_const.mul c1)
    (continuous_const.mul (((continuous_const.mul c2).sub continuous_const).mul
      (continuous_const.sub (c3.div_const 4))))

theorem continuous_psi0 : Continuous psi0 := continuous_psiL.sumElim continuous_psiR

theorem inj_ll (p q : I × I) (h : ver (psi0 (Sum.inl p)) = ver (psi0 (Sum.inl q))) :
    p = q ∨ (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = σ p.2) ∨ (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = σ q.2) := by
  have hp := p.2.2; have hq := q.2.2
  have hc : cos (π * ((2 * (p.2 : ℝ) - 1) * (1 / 4))) ≠ 0 :=
    cos_ne_zero_of (by linarith [hp.1, hp.2]) (by linarith [hp.1, hp.2])
  rcases sph_cases (theta_mem p.1) (theta_mem q.1)
    (lat_mem (by linarith [hp.1, hp.2]) (by linarith [hp.1, hp.2]))
    (lat_mem (by linarith [hq.1, hq.2]) (by linarith [hq.1, hq.2]))
    (ver_eq (sphP_ne_zero _ _) h) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases e2 with e2 | e2
    · exact absurd e2 hc
    left
    have a1 := pi_mul_inj e2
    have a2 := pi_mul_inj e1
    exact Prod.ext (Subtype.ext a1) (Subtype.ext (by linarith))
  · have a2 : π * ((2 * (p.2 : ℝ) - 1) * (1 / 4)) = π * (-((2 * (q.2 : ℝ) - 1) * (1 / 4))) := by
      rw [e1]; ring
    have a2 := pi_mul_inj a2
    rcases e2 with e2 | ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact absurd e2 hc
    · right; left
      refine ⟨zero_of_pi e3, one_of_pi e4, Subtype.ext ?_⟩
      rw [unitInterval.coe_symm_eq]; linarith
    · right; right
      refine ⟨one_of_pi e3, zero_of_pi e4, Subtype.ext ?_⟩
      rw [unitInterval.coe_symm_eq]; linarith

theorem u_one (p : I × I) (w : Bd × I) (h : ver (psi0 (Sum.inl p)) = ver (psi0 (Sum.inr w))) :
    w.2 = 1 := by
  obtain ⟨hp0, hp1⟩ := p.2.2
  obtain ⟨hu0, hu1⟩ := w.2.2
  have hb := lat_bound w.1.val.2 w.2
  have key : (w.2 : ℝ) = 1 := by
    rcases sph_cases (theta_mem p.1) (theta_mem w.1.val.1)
      (lat_mem (by linarith) (by linarith)) (lat_mem hb.1 hb.2)
      (ver_eq (sphP_ne_zero _ _) h) with ⟨e1, -⟩ | ⟨e1, -⟩
    · have a := pi_mul_inj e1
      rcases w.1.2 with ht | ht <;> rw [ht] at a <;> simp at a <;> linarith
    · have a : π * ((2 * (p.2 : ℝ) - 1) * (1 / 4)) =
          π * (-((2 * (w.1.val.2 : ℝ) - 1) * (1 / 2 - w.2 / 4))) := by rw [e1]; ring
      have a := pi_mul_inj a
      rcases w.1.2 with ht | ht <;> rw [ht] at a <;> simp at a <;> linarith
  exact coe_I_eq (key.trans Icc.coe_one.symm)

theorem inj_rr (v w : Bd × I) (h : ver (psi0 (Sum.inr v)) = ver (psi0 (Sum.inr w))) :
    v = w ∨ (v.2 = w.2 ∧ (v.2 = 0 ∨ (v.1.val = w.1.val ∨
      (v.1.val.1 = 0 ∧ w.1.val.1 = 1 ∧ w.1.val.2 = σ v.1.val.2) ∨
      (v.1.val.1 = 1 ∧ w.1.val.1 = 0 ∧ v.1.val.2 = σ w.1.val.2)))) := by
  obtain ⟨hu0, hu1⟩ := v.2.2
  obtain ⟨hu0', hu1'⟩ := w.2.2
  have hb := lat_bound v.1.val.2 v.2
  have hb' := lat_bound w.1.val.2 w.2
  rcases sph_cases (theta_mem v.1.val.1) (theta_mem w.1.val.1)
    (lat_mem hb.1 hb.2) (lat_mem hb'.1 hb'.2)
    (ver_eq (sphP_ne_zero _ _) h) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have a := pi_mul_inj e1
    have huu : (v.2 : ℝ) = w.2 := by
      rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
        simp only [Icc.coe_zero, Icc.coe_one] at a <;> linarith
    have hvw2 : v.2 = w.2 := Subtype.ext huu
    by_cases hz : (v.2 : ℝ) = 0
    · right
      exact ⟨hvw2, Or.inl (Subtype.ext hz)⟩
    · have hpos : 0 < (v.2 : ℝ) := lt_of_le_of_ne hu0 (Ne.symm hz)
      have htt : (v.1.val.2 : ℝ) = w.1.val.2 := by
        rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
          rw [ht, ht'] <;> simp only [Icc.coe_zero, Icc.coe_one] at a ⊢ <;> linarith
      have hc : cos (π * ((2 * (v.1.val.2 : ℝ) - 1) * (1 / 2 - v.2 / 4))) ≠ 0 := by
        rcases v.1.2 with ht | ht <;> rw [ht] <;> simp <;>
          exact cos_ne_zero_of (by linarith) (by linarith)
      rcases e2 with e2 | e2
      · exact absurd e2 hc
      left
      have a1 := pi_mul_inj e2
      exact Prod.ext (Subtype.ext (Prod.ext (Subtype.ext a1) (Subtype.ext htt))) hvw2
  · have a : π * ((2 * (v.1.val.2 : ℝ) - 1) * (1 / 2 - v.2 / 4)) =
        π * (-((2 * (w.1.val.2 : ℝ) - 1) * (1 / 2 - w.2 / 4))) := by rw [e1]; ring
    have a := pi_mul_inj a
    have huu : (v.2 : ℝ) = w.2 := by
      rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
        simp only [Icc.coe_zero, Icc.coe_one] at a <;> linarith
    have hvw2 : v.2 = w.2 := Subtype.ext huu
    right
    refine ⟨hvw2, ?_⟩
    by_cases hz : (v.2 : ℝ) = 0
    · exact Or.inl (Subtype.ext hz)
    · right
      right
      have hpos : 0 < (v.2 : ℝ) := lt_of_le_of_ne hu0 (Ne.symm hz)
      have htt : (w.1.val.2 : ℝ) = 1 - v.1.val.2 := by
        rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
          rw [ht, ht'] <;> simp only [Icc.coe_zero, Icc.coe_one] at a ⊢ <;> linarith
      have hc : cos (π * ((2 * (v.1.val.2 : ℝ) - 1) * (1 / 2 - v.2 / 4))) ≠ 0 := by
        rcases v.1.2 with ht | ht <;> rw [ht] <;> simp <;>
          exact cos_ne_zero_of (by linarith) (by linarith)
      rcases e2 with e2 | ⟨e3, e4⟩ | ⟨e3, e4⟩
      · exact absurd e2 hc
      · left
        refine ⟨zero_of_pi e3, one_of_pi e4, Subtype.ext ?_⟩
        rw [unitInterval.coe_symm_eq]; linarith
      · right
        refine ⟨one_of_pi e3, zero_of_pi e4, Subtype.ext ?_⟩
        rw [unitInterval.coe_symm_eq]; linarith

theorem resp_lr (p : I × I) (w : Bd × I) (hw : w.2 = 1)
    (h : p = w.1.val ∨ (p.1 = 0 ∧ w.1.val.1 = 1 ∧ w.1.val.2 = σ p.2) ∨
      (p.1 = 1 ∧ w.1.val.1 = 0 ∧ p.2 = σ w.1.val.2)) :
    ver (psi0 (Sum.inl p)) = ver (psi0 (Sum.inr w)) := by
  have e : psi0 (Sum.inr w) = psiL w.1.val := by
    simp only [psi0, Sum.elim_inr, psiR, psiL, hw, Icc.coe_one]
    norm_num
  rw [e]
  exact seam_ver (1 / 4) p w.1.val h

theorem resp_rr (v w : Bd × I) (h1 : v.2 = w.2)
    (h2 : v.2 = 0 ∨ (v.1.val = w.1.val ∨
      (v.1.val.1 = 0 ∧ w.1.val.1 = 1 ∧ w.1.val.2 = σ v.1.val.2) ∨
      (v.1.val.1 = 1 ∧ w.1.val.1 = 0 ∧ v.1.val.2 = σ w.1.val.2))) :
    ver (psi0 (Sum.inr v)) = ver (psi0 (Sum.inr w)) := by
  rcases h2 with h0 | hs
  · have hw0 : w.2 = 0 := h1 ▸ h0
    simp only [psi0, Sum.elim_inr, psiR, h0, hw0, Icc.coe_zero, zero_div, sub_zero]
    rw [pole_ver _ _ v.1.2, pole_ver _ _ w.1.2]
  · simp only [psi0, Sum.elim_inr, psiR]
    rw [← h1]
    exact seam_ver _ _ _ hs

theorem surj_param (s x : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx0 : -(1 / 2) ≤ x) (hx1 : x ≤ 1 / 2) :
    ∃ a, psi0 a = sphP (π * s) (π * x) := by
  by_cases hlo : x < -(1 / 4)
  · refine ⟨Sum.inr (⟨((⟨s, hs0, hs1⟩ : I), 0), Or.inl rfl⟩,
      ⟨4 * x + 2, by linarith, by linarith⟩), ?_⟩
    show sphP (π * s) (π * ((2 * ((0 : I) : ℝ) - 1) * (1 / 2 - (4 * x + 2) / 4))) = _
    rw [Icc.coe_zero]
    congr 2
    ring
  by_cases hhi : 1 / 4 < x
  · refine ⟨Sum.inr (⟨((⟨s, hs0, hs1⟩ : I), 1), Or.inr rfl⟩,
      ⟨2 - 4 * x, by linarith, by linarith⟩), ?_⟩
    show sphP (π * s) (π * ((2 * ((1 : I) : ℝ) - 1) * (1 / 2 - (2 - 4 * x) / 4))) = _
    rw [Icc.coe_one]
    congr 2
    ring
  · refine ⟨Sum.inl (⟨s, hs0, hs1⟩, ⟨2 * x + 1 / 2, by linarith, by linarith⟩), ?_⟩
    show sphP (π * s) (π * ((2 * (2 * x + 1 / 2) - 1) * (1 / 4))) = _
    congr 2
    ring

theorem surj_upper (v : Fin 3 → ℝ) (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) (h1 : 0 ≤ v 1) :
    ∃ a, psi0 a = v := by
  let z : ℂ := ⟨v 0, v 1⟩
  have hθ0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr h1
  have hθ1 : Complex.arg z ≤ π := Complex.arg_le_pi z
  have hv2 : -1 ≤ v 2 ∧ v 2 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hφ0 := neg_pi_div_two_le_arcsin (v 2)
  have hφ1 := arcsin_le_pi_div_two (v 2)
  have hnorm : ‖z‖ = cos (arcsin (v 2)) := by
    rw [cos_arcsin, Complex.norm_def, Complex.normSq_mk]
    congr 1
    linarith
  obtain ⟨a, ha⟩ := surj_param (Complex.arg z / π) (arcsin (v 2) / π)
    (div_nonneg hθ0 pi_pos.le) (by rw [div_le_one pi_pos]; exact hθ1)
    (by rw [le_div_iff₀ pi_pos]; linarith) (by rw [div_le_iff₀ pi_pos]; linarith)
  refine ⟨a, ha.trans ?_⟩
  have q1 : π * (Complex.arg z / π) = Complex.arg z := by field_simp
  have q2 : π * (arcsin (v 2) / π) = arcsin (v 2) := by field_simp
  rw [q1, q2]
  have e0 : cos (arcsin (v 2)) * cos (Complex.arg z) = v 0 := by
    rw [← hnorm, Complex.norm_mul_cos_arg]
  have e1 : cos (arcsin (v 2)) * sin (Complex.arg z) = v 1 := by
    rw [← hnorm, Complex.norm_mul_sin_arg]
  have e2 : sin (arcsin (v 2)) = v 2 := sin_arcsin hv2.1 hv2.2
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

theorem surj (v : Fin 3 → ℝ) (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    ∃ a, ver (psi0 a) = ver v := by
  by_cases h1 : 0 ≤ v 1
  · obtain ⟨a, ha⟩ := surj_upper v hv h1
    exact ⟨a, by rw [ha]⟩
  · replace h1 : v 1 < 0 := lt_of_not_ge h1
    obtain ⟨a, ha⟩ := surj_upper (-v) (by simp only [Pi.neg_apply, neg_sq]; exact hv)
      (by simp only [Pi.neg_apply]; linarith)
    exact ⟨a, by rw [ha, ver_neg]⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1.H1 := by
  unfold OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1.H1
  intro B seam glue
  let Ψ : (I × I) ⊕ (B × I) → Fin 3 → Fin 3 → ℝ := fun a => ver (psi0 a)
  have hΨc : Continuous Ψ := continuous_ver.comp continuous_psi0
  have hresp : ∀ a b, glue a b → Ψ a = Ψ b := by
    rintro (p | v) (q | w) h
    · exact seam_ver (1 / 4) p q h
    · exact resp_lr p w h.1 h.2
    · exact (resp_lr q v h.1 h.2).symm
    · exact resp_rr v w h.1 h.2
  have hll : ∀ p q, Ψ (Sum.inl p) = Ψ (Sum.inl q) →
      Quot.mk glue (Sum.inl p) = Quot.mk glue (Sum.inl q) :=
    fun p q h => Quot.sound (inj_ll p q h)
  have hrl : ∀ w : B × I, w.2 = 1 → Quot.mk glue (Sum.inr w) = Quot.mk glue (Sum.inl w.1.val) :=
    fun w hw => (Quot.sound (show glue (Sum.inl w.1.val) (Sum.inr w) from ⟨hw, Or.inl rfl⟩)).symm
  have hΨrl : ∀ w : B × I, w.2 = 1 → Ψ (Sum.inr w) = Ψ (Sum.inl w.1.val) :=
    fun w hw => (hresp _ _ (show glue (Sum.inl w.1.val) (Sum.inr w) from ⟨hw, Or.inl rfl⟩)).symm
  have hinj : ∀ a b, Ψ a = Ψ b → Quot.mk glue a = Quot.mk glue b := by
    rintro (p | v) (q | w) h
    · exact hll p q h
    · have hw := u_one p w h
      rw [hrl w hw]
      exact hll p _ (h.trans (hΨrl w hw))
    · have hv := u_one q v h.symm
      rw [hrl v hv]
      exact hll _ q ((hΨrl v hv).symm.trans h)
    · rcases inj_rr v w h with rfl | h'
      · rfl
      · exact Quot.sound h'
  have hcB : IsCompact {p : I × I | p.2 = 0 ∨ p.2 = 1} :=
    ((isClosed_eq continuous_snd continuous_const).union
      (isClosed_eq continuous_snd continuous_const)).isCompact
  have : CompactSpace B := isCompact_iff_compactSpace.mp hcB
  let F : Quot glue → Set.range Ψ :=
    Quot.lift (fun a => ⟨Ψ a, a, rfl⟩) (fun a b h => Subtype.ext (hresp a b h))
  have hFc : Continuous F := continuous_quot_lift _ (hΨc.subtype_mk _)
  have hFi : Function.Injective F := by
    rintro ⟨a⟩ ⟨b⟩ h
    exact hinj a b (congrArg Subtype.val h)
  have hFs : Function.Surjective F := by
    rintro ⟨_, a, rfl⟩
    exact ⟨Quot.mk _ a, rfl⟩
  let e : Quot glue ≃ₜ Set.range Ψ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩) hFc
  have hsq : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (x.val 0) ^ 2 + (x.val 1) ^ 2 + (x.val 2) ^ 2 = 1 := by
    intro x
    have h1 : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have h2 := EuclideanSpace.real_norm_sq_eq x.val
    rw [h1, Fin.sum_univ_three] at h2
    linarith
  have hne : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (fun i => x.val i) ≠ 0 := by
    intro x h0
    have h := hsq x
    have a0 := congrFun h0 0
    have a1 := congrFun h0 1
    have a2 := congrFun h0 2
    simp only [Pi.zero_apply] at a0 a1 a2
    rw [a0, a1, a2] at h
    norm_num at h
  have hmem : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ver (fun i => x.val i) ∈ Set.range Ψ := fun x => surj _ (hsq x)
  refine ⟨fun x => e.symm ⟨ver (fun i => x.val i), hmem x⟩, ?_, ?_⟩
  · apply e.symm.continuous.comp
    apply Continuous.subtype_mk
    apply continuous_ver.comp
    exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  · intro x y
    constructor
    · intro h
      have h2 := congrArg Subtype.val (e.symm.injective h)
      rcases ver_eq (hne x) h2 with h3 | h3
      · left
        apply Subtype.ext
        ext i
        exact congrFun h3 i
      · right
        ext i
        simpa using congrFun h3 i
    · rintro (rfl | h)
      · rfl
      · have h4 : (fun i => x.val i) = -(fun i => y.val i) := by
          funext i
          simp [h]
        have h5 : ver (fun i => x.val i) = ver (fun i => y.val i) := by
          rw [h4, ver_neg]
        show e.symm _ = e.symm _
        congr 1
        exact Subtype.ext h5
