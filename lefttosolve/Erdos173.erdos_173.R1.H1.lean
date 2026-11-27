import OMAReductions.R_Erdos173_erdos_173_R1

/-!
# Step H1 of the reduction Erdos173.erdos_173.R1

Let x, y, z be an equilateral triangle of side |AB| all of one colour k, where A, B, C are the
vertices of T with no monochromatic copy. Identify the plane with the complex numbers, put
u = y - x, z = x + u w and z0 = (C - A) / (B - A), so that |w| = |1 - w| = 1. A copy of T is
any triple P, P + s, P + s z0 with |s| = |AB|. The six copies

* (x, y, P1) with P1 = x + u z0,
* (z, x, P6) with P6 = x + u w (1 - z0),
* (z, y, P10) with P10 = x + u w + u (1 - w) z0,
* (P18, P10, P1) with P18 = x + u (1 - w) z0,
* (P10, P50, P6) with P50 = x + u (1 - w) (z0 - 1),
* (P18, P50, x)

force P1, P6, P10 to have the other colour, then P18 and P50 to have colour k, and the last
copy is monochromatic. Only the upstream definition `Erdos173.HasMonochromaticCopy` is used.
-/

namespace OMA.Helpers

open EuclideanGeometry
open scoped Congruent

/-- A triple congruent to an affinely independent triple is affinely independent. -/
theorem e173_affInd_of_congr {t t' : Fin 3 → EuclideanSpace ℝ (Fin 2)} (h : t' ≅ t)
    (ht : AffineIndependent ℝ t) : AffineIndependent ℝ t' := by
  have e1 : t = ![t 0, t 1, t 2] := by
    funext m; fin_cases m <;> rfl
  have e2 : t' = ![t' 0, t' 1, t' 2] := by
    funext m; fin_cases m <;> rfl
  rw [e1, affineIndependent_iff_not_collinear_set] at ht
  rw [e2, affineIndependent_iff_not_collinear_set]
  intro hcol
  apply ht
  rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi] at hcol ⊢
  have hang := EuclideanGeometry.angle_eq_of_congruent h 0 1 2
  rcases hcol with h01 | h21 | ha | ha
  · left
    have hd := h.dist_eq 0 1
    rw [h01, dist_self] at hd
    exact dist_eq_zero.mp hd.symm
  · right; left
    have hd := h.dist_eq 2 1
    rw [h21, dist_self] at hd
    exact dist_eq_zero.mp hd.symm
  · right; right; left
    rw [← hang]; exact ha
  · right; right; right
    rw [← hang]; exact ha

theorem e173_fin3_cover : ∀ i j l m : Fin 3, i ≠ j → i ≠ l → j ≠ l →
    m = i ∨ m = j ∨ m = l := by decide

theorem e173_fin3_third : ∀ i j : Fin 3, i ≠ j → ∃ l : Fin 3, i ≠ l ∧ j ≠ l := by decide

/-- Three points at the side lengths of T, in the order of the labels i, j, l, are not of one
colour. -/
theorem e173_no_mono (c : EuclideanSpace ℝ (Fin 2) → Fin 2)
    (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (hT : ¬ Erdos173.HasMonochromaticCopy c T) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (p q r : EuclideanSpace ℝ (Fin 2))
    (h1 : dist p q = dist (T.points i) (T.points j))
    (h2 : dist p r = dist (T.points i) (T.points l))
    (h3 : dist q r = dist (T.points j) (T.points l)) :
    ¬ (c p = c q ∧ c q = c r) := by
  rintro ⟨hpq, hqr⟩
  classical
  let f : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun m => if m = i then p else if m = j then q else r
  have fi : f i = p := by simp [f]
  have fj : f j = q := by simp [f, hij.symm]
  have fl : f l = r := by simp [f, hil.symm, hjl.symm]
  have hcov := e173_fin3_cover i j l
  have hcong : f ≅ T.points := by
    rw [congruent_iff_dist_eq]
    intro m n
    rcases hcov m hij hil hjl with hm | hm | hm <;>
      rcases hcov n hij hil hjl with hn | hn | hn <;>
      rw [hm, hn] <;> simp only [fi, fj, fl, dist_self] <;>
      first
      | rfl
      | exact h1
      | exact h2
      | exact h3
      | (rw [dist_comm, h1, dist_comm])
      | (rw [dist_comm, h2, dist_comm])
      | (rw [dist_comm, h3, dist_comm])
  have haff : AffineIndependent ℝ f := e173_affInd_of_congr hcong T.independent
  apply hT
  refine ⟨⟨f, haff⟩, hcong, c p, fun m => ?_⟩
  rcases hcov m hij hil hjl with hm | hm | hm
  · show c (f m) = c p
    rw [hm, fi]
  · show c (f m) = c p
    rw [hm, fj, hpq]
  · show c (f m) = c p
    rw [hm, fl, hpq, hqr]

/-- Distances of a copy P, P + s, P + s z0 in the complex plane. -/
theorem e173_copy_dist (A B C P Q R s : ℂ) (hAB : A ≠ B) (hs : ‖s‖ = ‖B - A‖)
    (hQ : Q = P + s) (hR : R = P + s * ((C - A) / (B - A))) :
    dist P Q = dist A B ∧ dist P R = dist A C ∧ dist Q R = dist B C := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hnBA : ‖B - A‖ ≠ 0 := norm_ne_zero_iff.mpr hBA
  subst hQ hR
  simp only [Complex.dist_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [show P - (P + s) = -s by ring, norm_neg, hs, norm_sub_rev]
  · rw [show P - (P + s * ((C - A) / (B - A))) = -(s * ((C - A) / (B - A))) by ring, norm_neg,
      norm_mul, norm_div, hs, norm_sub_rev A C]
    field_simp
  · rw [show P + s - (P + s * ((C - A) / (B - A))) = -(s * ((C - B) / (B - A))) by
      field_simp; ring, norm_neg, norm_mul, norm_div, hs, norm_sub_rev B C]
    field_simp

theorem e173_fin2_eq : ∀ a b k : Fin 2, a ≠ k → b ≠ k → a = b := by decide

theorem e173_fin2_comb (x y z p1 p6 p10 p18 p50 : Fin 2) (h0 : x = y ∧ y = z)
    (h1 : ¬ (x = y ∧ y = p1)) (h2 : ¬ (z = x ∧ x = p6)) (h3 : ¬ (z = y ∧ y = p10))
    (h4 : ¬ (p18 = p10 ∧ p10 = p1)) (h5 : ¬ (p10 = p50 ∧ p50 = p6))
    (h6 : ¬ (p18 = p50 ∧ p50 = x)) : False := by
  obtain ⟨hxy, hyz⟩ := h0
  have n1 : p1 ≠ x := fun h => h1 ⟨hxy, hxy.symm.trans h.symm⟩
  have n6 : p6 ≠ x := fun h => h2 ⟨(hxy.trans hyz).symm, h.symm⟩
  have n10 : p10 ≠ x := fun h => h3 ⟨hyz.symm, hxy.symm.trans h.symm⟩
  have e1 : p10 = p1 := e173_fin2_eq p10 p1 x n10 n1
  have n18 : p18 ≠ p10 := fun h => h4 ⟨h, e1⟩
  have e2 : p6 = p10 := e173_fin2_eq p6 p10 x n6 n10
  have n50 : p50 ≠ p10 := fun h => h5 ⟨h.symm, h.trans e2.symm⟩
  have k18 : p18 = x := by
    by_contra hc
    exact n18 (e173_fin2_eq p18 p10 x hc n10)
  have k50 : p50 = x := by
    by_contra hc
    exact n50 (e173_fin2_eq p50 p10 x hc n10)
  exact h6 ⟨k18.trans k50.symm, k50⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1.H1 := by
  intro c T hT i j hij v hv hmono
  obtain ⟨l, hil, hjl⟩ := e173_fin3_third i j hij
  obtain ⟨k, hk⟩ := hmono
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hd : ∀ a b : EuclideanSpace ℝ (Fin 2), dist (e a) (e b) = dist a b := fun a b =>
    e.dist_map a b
  have hback : ∀ a : EuclideanSpace ℝ (Fin 2), e.symm (e a) = a := fun a => e.symm_apply_apply a
  set A := e (T.points i) with hA
  set B := e (T.points j) with hB
  set C := e (T.points l) with hC
  have hAB : A ≠ B := by
    intro h
    have := e.injective h
    exact hij (T.independent.injective this)
  set z0 := (C - A) / (B - A) with hz0
  set x := e (v 0) with hx
  set y := e (v 1) with hy
  set z := e (v 2) with hz
  set u := y - x with hu
  have hnu : ‖u‖ = ‖B - A‖ := by
    have h01 := hv 0 1 (by decide)
    rw [← hd, ← hd] at h01
    rw [hu, ← Complex.dist_eq, dist_comm, h01, Complex.dist_eq, norm_sub_rev]
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnu
    exact hBA (norm_eq_zero.mp hnu.symm)
  set w := (z - x) / u with hw
  have hzw : z = x + u * w := by rw [hw]; field_simp; ring
  have hyu : y = x + u := by rw [hu]; ring
  have hnw : ‖w‖ = 1 := by
    have h02 := hv 0 2 (by decide)
    rw [← hd, ← hd] at h02
    have h1 : ‖z - x‖ = ‖u‖ := by
      rw [← Complex.dist_eq, dist_comm, h02, hnu, Complex.dist_eq, norm_sub_rev]
    rw [hw, norm_div, h1, div_self (norm_ne_zero_iff.mpr hu0)]
  have hn1w : ‖1 - w‖ = 1 := by
    have h12 := hv 1 2 (by decide)
    rw [← hd, ← hd] at h12
    have h1 : ‖z - y‖ = ‖u‖ := by
      rw [← Complex.dist_eq, dist_comm, h12, hnu, Complex.dist_eq, norm_sub_rev]
    have h2 : z - y = -(u * (1 - w)) := by rw [hzw, hyu]; ring
    rw [h2, norm_neg, norm_mul] at h1
    have h3 : ‖u‖ * ‖1 - w‖ = ‖u‖ * 1 := by rw [h1, mul_one]
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hu0) h3
  -- the six copies
  have copy : ∀ P Q R s : ℂ, ‖s‖ = ‖B - A‖ → Q = P + s → R = P + s * z0 →
      ¬ (c (e.symm P) = c (e.symm Q) ∧ c (e.symm Q) = c (e.symm R)) := by
    intro P Q R s hs hQ hR
    obtain ⟨d1, d2, d3⟩ := e173_copy_dist A B C P Q R s hAB hs hQ hR
    apply e173_no_mono c T hT i j l hij hil hjl
    · rw [← hd, ← hd]; simpa [e, hA, hB] using d1
    · rw [← hd, ← hd]; simpa [e, hA, hC] using d2
    · rw [← hd, ← hd]; simpa [e, hB, hC] using d3
  have hs1 : ‖u‖ = ‖B - A‖ := hnu
  have hs2 : ‖-(u * w)‖ = ‖B - A‖ := by rw [norm_neg, norm_mul, hnw, mul_one, hnu]
  have hs3 : ‖u * (1 - w)‖ = ‖B - A‖ := by rw [norm_mul, hn1w, mul_one, hnu]
  have hs4 : ‖u * w‖ = ‖B - A‖ := by rw [norm_mul, hnw, mul_one, hnu]
  have hs5 : ‖-u‖ = ‖B - A‖ := by rw [norm_neg, hnu]
  have hs6 : ‖-(u * (1 - w))‖ = ‖B - A‖ := by rw [norm_neg, hs3]
  have c1 := copy x y (x + u * z0) u hs1 hyu rfl
  have c2 := copy z x (x + u * w * (1 - z0)) (-(u * w)) hs2 (by rw [hzw]; try ring)
    (by rw [hzw]; try ring)
  have c3 := copy z y (x + u * w + u * (1 - w) * z0) (u * (1 - w)) hs3
    (by rw [hzw, hyu]; try ring) (by rw [hzw]; try ring)
  have c4 := copy (x + u * (1 - w) * z0) (x + u * w + u * (1 - w) * z0) (x + u * z0) (u * w)
    hs4 (by ring) (by ring)
  have c5 := copy (x + u * w + u * (1 - w) * z0) (x + u * (1 - w) * (z0 - 1))
    (x + u * w * (1 - z0)) (-u) hs5 (by ring) (by ring)
  have c6 := copy (x + u * (1 - w) * z0) (x + u * (1 - w) * (z0 - 1)) x (-(u * (1 - w)))
    hs6 (by ring) (by ring)
  have k0 : c (e.symm x) = k := by rw [hx, hback]; exact hk 0
  have k1 : c (e.symm y) = k := by rw [hy, hback]; exact hk 1
  have k2 : c (e.symm z) = k := by rw [hz, hback]; exact hk 2
  exact e173_fin2_comb _ _ _ _ _ _ _ _ ⟨k0.trans k1.symm, k1.trans k2.symm⟩ c1 c2 c3 c4 c5 c6
