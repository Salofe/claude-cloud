import OMAReductions.R_Erdos604_erdos_604_variants_average_R2_H2_R1_H1_R1

/-!
# Step H2 of the reduction Erdos604.erdos_604.variants.average.R2.H2.R1.H1.R1

Cyclic arcs on the circles of `L`. Identify the plane with `ℂ` through the orthonormal basis
`1, I`, and measure the angle of a point `p` around a center `c` by `Complex.arg`. On each circle
`(c, r)` of `L`, an arc joins two points `x, y` of `A` on the circle when the angle of `x` is
smaller than the angle of `y` and no point of `A` on the circle has an angle strictly between
them; it is parametrized by the angles from `ang x` to `ang y` (an interval inside `(-π, π]`), so
it is injective and meets `A` only at its endpoints.

* Every point of `A` on a circle, except the one of largest angle, starts such an arc, so the
  incidences are at most the number of arcs plus `L.card`.
* Arcs are thinned to one per unordered endpoint pair; a pair lies on at most two circles of `L`
  and determines the arc on each, so at most half of the arcs are discarded.
* Two distinct arcs on the same circle meet only in `A`. Two distinct circles meet in at most two
  points (Mathlib, two spheres in the plane), so counting the pairs of arcs through each
  intersection point bounds the total intersection count by `2 * L.card ^ 2`.
-/

open scoped EuclideanGeometry

namespace OMA.Helpers

open Complex

noncomputable def eC : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr

noncomputable def ang (c p : EuclideanSpace ℝ (Fin 2)) : ℝ := Complex.arg (eC.symm p - eC.symm c)

noncomputable def pt (c : EuclideanSpace ℝ (Fin 2)) (r θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  eC (eC.symm c + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))

lemma dist_pt (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (θ : ℝ) (hr : 0 < r) :
    dist (pt c r θ) c = r := by
  rw [← eC.symm.dist_map, pt, LinearIsometryEquiv.symm_apply_apply, dist_eq_norm,
    add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]

lemma pt_ang {c p : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (h : dist p c = r) :
    pt c r (ang c p) = p := by
  have hn : ‖eC.symm p - eC.symm c‖ = r := by rw [← dist_eq_norm, eC.symm.dist_map, h]
  unfold pt ang
  rw [← hn, Complex.norm_mul_exp_arg_mul_I, add_sub_cancel, LinearIsometryEquiv.apply_symm_apply]

lemma ang_pt (c : EuclideanSpace ℝ (Fin 2)) {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    ang c (pt c r θ) = θ := by
  unfold ang pt
  rw [LinearIsometryEquiv.symm_apply_apply, add_sub_cancel_left, arg_real_mul _ hr, exp_mul_I,
    arg_cos_add_sin_mul_I hθ]

lemma ang_mem (c p : EuclideanSpace ℝ (Fin 2)) : ang c p ∈ Set.Ioc (-Real.pi) Real.pi :=
  ⟨neg_pi_lt_arg _, arg_le_pi _⟩

noncomputable def arc (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    C(unitInterval, EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun t => pt c r (ang c x + (t:ℝ) * (ang c y - ang c x)), by unfold pt; fun_prop⟩

lemma arc_apply (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) (t : unitInterval) :
    arc c r x y t = pt c r (ang c x + (t:ℝ) * (ang c y - ang c x)) := rfl

lemma dist_arc (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (x y : EuclideanSpace ℝ (Fin 2)) (hr : 0 < r)
    (t : unitInterval) : dist (arc c r x y t) c = r := dist_pt c _ hr

lemma ang_arc (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (x y : EuclideanSpace ℝ (Fin 2)) (hr : 0 < r)
    (hlt : ang c x < ang c y) (t : unitInterval) :
    ang c (arc c r x y t) = ang c x + (t:ℝ) * (ang c y - ang c x) := by
  rw [arc_apply]
  apply ang_pt c hr
  have h0 : (0:ℝ) ≤ t := t.2.1
  have h1 : (t:ℝ) ≤ 1 := t.2.2
  have hx := ang_mem c x
  have hy := ang_mem c y
  constructor
  · nlinarith [hx.1]
  · nlinarith [hy.2]

lemma arc_zero (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (y : EuclideanSpace ℝ (Fin 2)) (hx : dist x c = r) : arc c r x y 0 = x := by
  rw [arc_apply]
  simp only [Set.Icc.coe_zero, zero_mul, add_zero]
  exact pt_ang hx

lemma arc_one (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (x : EuclideanSpace ℝ (Fin 2))
    {y : EuclideanSpace ℝ (Fin 2)} (hy : dist y c = r) : arc c r x y 1 = y := by
  rw [arc_apply]
  simp only [Set.Icc.coe_one, one_mul, add_sub_cancel]
  exact pt_ang hy

lemma arc_injective (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (x y : EuclideanSpace ℝ (Fin 2))
    (hr : 0 < r) (hlt : ang c x < ang c y) : Function.Injective (arc c r x y) := by
  intro s t hst
  have h := congrArg (ang c) hst
  rw [ang_arc c x y hr hlt, ang_arc c x y hr hlt] at h
  have hne : ang c y - ang c x ≠ 0 := by linarith
  have : (s:ℝ) = t := by
    have := mul_right_cancel₀ hne (by linarith : (s:ℝ) * (ang c y - ang c x) = t * (ang c y - ang c x))
    exact this
  exact Subtype.ext this


def Good (A : Finset (EuclideanSpace ℝ (Fin 2))) (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (x y : EuclideanSpace ℝ (Fin 2)) : Prop :=
  dist x c = r ∧ dist y c = r ∧ ang c x < ang c y ∧
    ∀ z ∈ A, dist z c = r → ¬ (ang c x < ang c z ∧ ang c z < ang c y)

lemma arc_not_mem {A : Finset (EuclideanSpace ℝ (Fin 2))} {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {x y : EuclideanSpace ℝ (Fin 2)} (hr : 0 < r) (hg : Good A c r x y) (t : unitInterval)
    (h0 : 0 < (t:ℝ)) (h1 : (t:ℝ) < 1) : arc c r x y t ∉ A := by
  intro hA
  have ha := ang_arc c x y hr hg.2.2.1 t
  have hd := hg.2.2.1
  apply hg.2.2.2 _ hA (dist_arc c x y hr t)
  rw [ha]
  constructor <;> nlinarith

/-- A point of an arc outside `A` has angle strictly inside the arc. -/
lemma ang_strict {A : Finset (EuclideanSpace ℝ (Fin 2))} {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {x y p : EuclideanSpace ℝ (Fin 2)} (hr : 0 < r) (hg : Good A c r x y) (hxA : x ∈ A)
    (hyA : y ∈ A) (hp : p ∈ Set.range (arc c r x y)) (hpA : p ∉ A) :
    dist p c = r ∧ ang c x < ang c p ∧ ang c p < ang c y := by
  obtain ⟨t, rfl⟩ := hp
  have ha := ang_arc c x y hr hg.2.2.1 t
  have hd := hg.2.2.1
  have h0 : (0:ℝ) ≤ t := t.2.1
  have h1 : (t:ℝ) ≤ 1 := t.2.2
  refine ⟨dist_arc c x y hr t, ?_, ?_⟩
  · rcases lt_or_eq_of_le (show ang c x ≤ ang c (arc c r x y t) by rw [ha]; nlinarith) with h | h
    · exact h
    · exfalso
      apply hpA
      have : arc c r x y t = x := by
        rw [← pt_ang (dist_arc c x y hr t), ← h, pt_ang hg.1]
      rw [this]; exact hxA
  · rcases lt_or_eq_of_le (show ang c (arc c r x y t) ≤ ang c y by rw [ha]; nlinarith) with h | h
    · exact h
    · exfalso
      apply hpA
      have : arc c r x y t = y := by
        rw [← pt_ang (dist_arc c x y hr t), h, pt_ang hg.2.1]
      rw [this]; exact hyA

lemma arc_same {A : Finset (EuclideanSpace ℝ (Fin 2))} {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {x y x' y' p : EuclideanSpace ℝ (Fin 2)} (hr : 0 < r) (hg : Good A c r x y)
    (hg' : Good A c r x' y') (hxA : x ∈ A) (hyA : y ∈ A) (hxA' : x' ∈ A) (hyA' : y' ∈ A)
    (hp : p ∈ Set.range (arc c r x y)) (hp' : p ∈ Set.range (arc c r x' y')) (hpA : p ∉ A) :
    x = x' ∧ y = y' := by
  obtain ⟨-, h1, h2⟩ := ang_strict hr hg hxA hyA hp hpA
  obtain ⟨-, h1', h2'⟩ := ang_strict hr hg' hxA' hyA' hp' hpA
  constructor
  · rcases lt_trichotomy (ang c x) (ang c x') with h | h | h
    · exact absurd ⟨h, by linarith⟩ (hg.2.2.2 x' hxA' hg'.1)
    · rw [← pt_ang hg.1, h, pt_ang hg'.1]
    · exact absurd ⟨h, by linarith⟩ (hg'.2.2.2 x hxA hg.1)
  · rcases lt_trichotomy (ang c y) (ang c y') with h | h | h
    · exact absurd ⟨by linarith, h⟩ (hg'.2.2.2 y hyA hg.2.1)
    · rw [← pt_ang hg.2.1, h, pt_ang hg'.2.1]
    · exact absurd ⟨by linarith, h⟩ (hg.2.2.2 y' hyA' hg'.2.1)

lemma two_circles {c c' : EuclideanSpace ℝ (Fin 2) × ℝ} (hcc : c ≠ c')
    {p₁ p₂ p : EuclideanSpace ℝ (Fin 2)} (hp : p₁ ≠ p₂)
    (h1 : dist p₁ c.1 = c.2) (h2 : dist p₂ c.1 = c.2) (h3 : dist p c.1 = c.2)
    (h1' : dist p₁ c'.1 = c'.2) (h2' : dist p₂ c'.1 = c'.2) (h3' : dist p c'.1 = c'.2) :
    p = p₁ ∨ p = p₂ := by
  have hs : (⟨c.1, c.2⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) ≠ ⟨c'.1, c'.2⟩ := by
    intro h
    apply hcc
    have := congrArg EuclideanGeometry.Sphere.center h
    have h' := congrArg EuclideanGeometry.Sphere.radius h
    exact Prod.ext this h'
  exact EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two finrank_euclideanSpace_fin
    hs hp (EuclideanGeometry.mem_sphere.2 h1) (EuclideanGeometry.mem_sphere.2 h2)
    (EuclideanGeometry.mem_sphere.2 h3) (EuclideanGeometry.mem_sphere.2 h1')
    (EuclideanGeometry.mem_sphere.2 h2') (EuclideanGeometry.mem_sphere.2 h3')

lemma two_circles_finite {c c' : EuclideanSpace ℝ (Fin 2) × ℝ} (hcc : c ≠ c') :
    {p : EuclideanSpace ℝ (Fin 2) | dist p c.1 = c.2 ∧ dist p c'.1 = c'.2}.Finite := by
  by_cases h : ∃ p₁ p₂ : EuclideanSpace ℝ (Fin 2), p₁ ≠ p₂ ∧ (dist p₁ c.1 = c.2 ∧ dist p₁ c'.1 = c'.2)
      ∧ (dist p₂ c.1 = c.2 ∧ dist p₂ c'.1 = c'.2)
  · obtain ⟨p₁, p₂, hne, h1, h2⟩ := h
    apply (Set.toFinite ({p₁, p₂} : Set (EuclideanSpace ℝ (Fin 2)))).subset
    intro p hp
    rcases two_circles hcc hne h1.1 h2.1 hp.1 h1.2 h2.2 hp.2 with h | h
    · simp [h]
    · simp [h]
  · apply Set.Subsingleton.finite
    intro p₁ hp₁ p₂ hp₂
    by_contra hne
    exact h ⟨p₁, p₂, hne, hp₁, hp₂⟩

lemma two_circles_card {c c' : EuclideanSpace ℝ (Fin 2) × ℝ} (hcc : c ≠ c')
    (F : Finset (EuclideanSpace ℝ (Fin 2)))
    (hF : ∀ p ∈ F, dist p c.1 = c.2 ∧ dist p c'.1 = c'.2) : F.card ≤ 2 := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.1 hlt
  rcases two_circles hcc hab (hF a ha).1 (hF b hb).1 (hF d hd).1 (hF a ha).2 (hF b hb).2
    (hF d hd).2 with h | h
  · exact had h.symm
  · exact hbd h.symm


lemma pair_cases {u v x y : EuclideanSpace ℝ (Fin 2)} (h : ({u, v} : Finset (EuclideanSpace ℝ (Fin 2))) = {x, y})
    (huv : u ≠ v) : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  have hu : u ∈ ({x, y} : Finset (EuclideanSpace ℝ (Fin 2))) := by rw [← h]; simp
  have hv : v ∈ ({x, y} : Finset (EuclideanSpace ℝ (Fin 2))) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact absurd (hu.trans hv.symm) huv
  · exact Or.inl ⟨hu, hv⟩
  · exact Or.inr ⟨hu, hv⟩
  · exact absurd (hu.trans hv.symm) huv

end OMA.Helpers

open Finset
open scoped EuclideanGeometry Classical

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1_H1_R1.H2 := by
  intro A L hpos hmult
  let Arc : Finset ((ℝ² × ℝ) × ℝ² × ℝ²) :=
    (L ×ˢ (A ×ˢ A)).filter (fun a => OMA.Helpers.Good A a.1.1 a.1.2 a.2.1 a.2.2)
  have memArc : ∀ a, a ∈ Arc ↔ (a.1 ∈ L ∧ a.2.1 ∈ A ∧ a.2.2 ∈ A) ∧
      OMA.Helpers.Good A a.1.1 a.1.2 a.2.1 a.2.2 := by
    intro a
    simp only [Arc, Finset.mem_filter, Finset.mem_product]
  let pr : (ℝ² × ℝ) × ℝ² × ℝ² → Finset ℝ² := fun a => {a.2.1, a.2.2}
  let Q := Arc.image pr
  have hrep : ∀ q ∈ Q, ∃ a, a ∈ Arc ∧ pr a = q := fun q hq => Finset.mem_image.1 hq
  choose! rep hrepA hrepq using hrep
  let idx : ℕ → Finset ℝ² := fun i =>
    if h : i < Q.card then (Q.equivFin.symm ⟨i, h⟩ : Finset ℝ²) else ∅
  have idx_mem : ∀ i, i < Q.card → idx i ∈ Q := by
    intro i hi
    simp only [idx, dif_pos hi]
    exact (Q.equivFin.symm ⟨i, hi⟩).2
  have idx_inj : ∀ i j, i < Q.card → j < Q.card → idx i = idx j → i = j := by
    intro i j hi hj h
    simp only [idx, dif_pos hi, dif_pos hj] at h
    have := Q.equivFin.symm.injective (Subtype.ext h)
    exact congrArg Fin.val this
  let a : ℕ → (ℝ² × ℝ) × ℝ² × ℝ² := fun i => rep (idx i)
  have ha : ∀ i, i < Q.card → a i ∈ Arc := fun i hi => hrepA _ (idx_mem i hi)
  have hpa : ∀ i, i < Q.card → pr (a i) = idx i := fun i hi => hrepq _ (idx_mem i hi)
  let γ : ℕ → C(unitInterval, ℝ²) := fun i =>
    OMA.Helpers.arc (a i).1.1 (a i).1.2 (a i).2.1 (a i).2.2
  have same : ∀ i j, i < Q.card → j < Q.card → (a i).1 = (a j).1 → ∀ p,
      p ∈ Set.range (γ i) → p ∈ Set.range (γ j) → p ∉ A → i = j := by
    intro i j hi hj hc p hp hp' hpA
    obtain ⟨⟨hL, hx, hy⟩, hg⟩ := (memArc _).1 (ha i hi)
    obtain ⟨⟨hL', hx', hy'⟩, hg'⟩ := (memArc _).1 (ha j hj)
    have hp'' : p ∈ Set.range (OMA.Helpers.arc (a i).1.1 (a i).1.2 (a j).2.1 (a j).2.2) := by
      rw [hc]; exact hp'
    rw [← hc] at hg'
    obtain ⟨hxx, hyy⟩ := OMA.Helpers.arc_same (hpos _ hL) hg hg' hx hy hx' hy' hp hp'' hpA
    have haij : a i = a j := Prod.ext hc (Prod.ext hxx hyy)
    apply idx_inj i j hi hj
    rw [← hpa i hi, ← hpa j hj, haij]
  have hrange : ∀ i, i < Q.card → ∀ p ∈ Set.range (γ i), dist p (a i).1.1 = (a i).1.2 := by
    intro i hi p hp
    obtain ⟨t, rfl⟩ := hp
    obtain ⟨⟨hL, -, -⟩, -⟩ := (memArc _).1 (ha i hi)
    exact OMA.Helpers.dist_arc _ _ _ (hpos _ hL) t
  have hZ : {p : ℝ² | ∃ c ∈ L, ∃ c' ∈ L, c ≠ c' ∧ dist p c.1 = c.2 ∧ dist p c'.1 = c'.2}.Finite := by
    apply (Set.Finite.biUnion ((L ×ˢ L).filter (fun cc => cc.1 ≠ cc.2)).finite_toSet
      (fun cc hcc => OMA.Helpers.two_circles_finite (Finset.mem_filter.1 hcc).2)).subset
    rintro p ⟨c, hc, c', hc', hne, h1, h2⟩
    exact Set.mem_biUnion (x := (c, c')) (by simp [hc, hc', hne]) ⟨h1, h2⟩
  have hT : ∀ i ∈ Finset.range Q.card, ∀ j ∈ Finset.range Q.card, i ≠ j →
      (Set.range (γ i) ∩ Set.range (γ j)) \ (A : Set ℝ²) ⊆
        {p : ℝ² | ∃ c ∈ L, ∃ c' ∈ L, c ≠ c' ∧ dist p c.1 = c.2 ∧ dist p c'.1 = c'.2} := by
    intro i hi j hj hij p hp
    rw [Finset.mem_range] at hi hj
    obtain ⟨⟨hp1, hp2⟩, hpA⟩ := hp
    obtain ⟨⟨hL, -, -⟩, -⟩ := (memArc _).1 (ha i hi)
    obtain ⟨⟨hL', -, -⟩, -⟩ := (memArc _).1 (ha j hj)
    exact ⟨(a i).1, hL, (a j).1, hL', fun hc => hij (same i j hi hj hc p hp1 hp2 hpA),
      hrange i hi p hp1, hrange j hj p hp2⟩
  refine ⟨Finset.range Q.card, γ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨⟨hL, hx, hy⟩, hg⟩ := (memArc _).1 (ha i hi)
    have hr := hpos _ hL
    refine ⟨OMA.Helpers.arc_injective _ _ _ hr hg.2.2.1, ?_, ?_, ?_, ⟨(a i).1.1, (a i).1.2, hr,
      fun t => OMA.Helpers.dist_arc _ _ _ hr t⟩⟩
    · show OMA.Helpers.arc _ _ _ _ 0 ∈ A
      rw [OMA.Helpers.arc_zero _ _ hg.1]; exact hx
    · show OMA.Helpers.arc _ _ _ _ 1 ∈ A
      rw [OMA.Helpers.arc_one _ _ hg.2.1]; exact hy
    · intro t h0 h1
      exact OMA.Helpers.arc_not_mem hr hg t h0 h1
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    apply idx_inj i j hi hj
    rw [← hpa i hi, ← hpa j hj]
    obtain ⟨⟨-, -, -⟩, hg⟩ := (memArc _).1 (ha i hi)
    obtain ⟨⟨-, -, -⟩, hg'⟩ := (memArc _).1 (ha j hj)
    have e1 : γ i 0 = (a i).2.1 := OMA.Helpers.arc_zero _ _ hg.1
    have e2 : γ i 1 = (a i).2.2 := OMA.Helpers.arc_one _ _ hg.2.1
    have e3 : γ j 0 = (a j).2.1 := OMA.Helpers.arc_zero _ _ hg'.1
    have e4 : γ j 1 = (a j).2.2 := OMA.Helpers.arc_one _ _ hg'.2.1
    simp only [e1, e2, e3, e4] at hij
    exact hij
  · intro i hi j hj hij
    exact hZ.subset (hT i hi j hj hij)
  · rw [Finset.card_range]
    have hArcQ : Arc.card ≤ 2 * Q.card := by
      apply Finset.card_le_mul_card_image Arc 2
      intro q hq
      obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨⟨hL0, hx0, hy0⟩, hg0⟩ := (memArc a0).1 ha0
      have hxy : a0.2.1 ≠ a0.2.2 := by
        intro h; have := hg0.2.2.1; rw [h] at this; exact lt_irrefl _ this
      refine le_trans ?_ (hmult _ hx0 _ hy0 hxy)
      apply Finset.card_le_card_of_injOn (fun b => b.1)
      · intro b hb
        rw [Finset.mem_coe, Finset.mem_filter] at hb
        obtain ⟨hbA, hbq⟩ := hb
        obtain ⟨⟨hLb, -, -⟩, hgb⟩ := (memArc b).1 hbA
        have hne : b.2.1 ≠ b.2.2 := by
          intro h; have := hgb.2.2.1; rw [h] at this; exact lt_irrefl _ this
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨hLb, ?_⟩
        rcases OMA.Helpers.pair_cases hbq hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact ⟨hgb.1, hgb.2.1⟩
        · rw [← h1, ← h2]; exact ⟨hgb.2.1, hgb.1⟩
      · intro b hb b' hb' hbb'
        rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
        obtain ⟨hbA, hbq⟩ := hb
        obtain ⟨hbA', hbq'⟩ := hb'
        obtain ⟨-, hgb⟩ := (memArc b).1 hbA
        obtain ⟨-, hgb'⟩ := (memArc b').1 hbA'
        have hbb : b.1 = b'.1 := hbb'
        have hne : b.2.1 ≠ b.2.2 := by
          intro h; have := hgb.2.2.1; rw [h] at this; exact lt_irrefl _ this
        have hne' : b'.2.1 ≠ b'.2.2 := by
          intro h; have := hgb'.2.2.1; rw [h] at this; exact lt_irrefl _ this
        have hA := hgb.2.2.1
        have hB := hgb'.2.2.1
        rw [hbb] at hA
        rcases OMA.Helpers.pair_cases hbq hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases OMA.Helpers.pair_cases hbq' hne' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact Prod.ext hbb (Prod.ext (h1.trans h1'.symm) (h2.trans h2'.symm))
        · rw [h1, h2] at hA; rw [h1', h2'] at hB; linarith
        · rw [h1, h2] at hA; rw [h1', h2'] at hB; linarith
        · exact Prod.ext hbb (Prod.ext (h1.trans h1'.symm) (h2.trans h2'.symm))
    have hinc : ((L ×ˢ A).filter fun cp => dist cp.2 cp.1.1 = cp.1.2).card ≤ Arc.card + L.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := L)
          (fun cp hcp => (Finset.mem_product.1 (Finset.mem_filter.1 hcp).1).1),
        Finset.card_eq_sum_card_fiberwise (s := Arc) (f := Prod.fst) (t := L)
          (fun b hb => ((memArc b).1 hb).1.1),
        Finset.card_eq_sum_ones L, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro c hc
      by_cases hK : (A.filter fun p => dist p c.1 = c.2).Nonempty
      · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ (fun p => OMA.Helpers.ang c.1 p) hK
        rw [Finset.mem_filter] at hm
        calc _ ≤ #(insert (c, m) ((Arc.filter (fun b => b.1 = c)).image
                (fun b => (b.1, b.2.1)))) := by
              apply Finset.card_le_card
              intro cp hcp
              simp only [Finset.mem_filter, Finset.mem_product] at hcp
              obtain ⟨⟨⟨-, hxA⟩, hxd⟩, hc1⟩ := hcp
              rw [Finset.mem_insert, Finset.mem_image]
              have hcpe : cp = (c, cp.2) := Prod.ext hc1 rfl
              rw [hc1] at hxd
              by_cases hxm : cp.2 = m
              · left; rw [hcpe, hxm]
              · right
                have hlt : OMA.Helpers.ang c.1 cp.2 < OMA.Helpers.ang c.1 m := by
                  rcases lt_or_eq_of_le (hmax cp.2 (Finset.mem_filter.2 ⟨hxA, hxd⟩)) with h | h
                  · exact h
                  · exfalso; apply hxm
                    rw [← OMA.Helpers.pt_ang hxd, h, OMA.Helpers.pt_ang hm.2]
                obtain ⟨y, hy, hymin⟩ := Finset.exists_min_image
                  ((A.filter fun p => dist p c.1 = c.2).filter
                    fun z => OMA.Helpers.ang c.1 cp.2 < OMA.Helpers.ang c.1 z)
                  (fun p => OMA.Helpers.ang c.1 p)
                  ⟨m, Finset.mem_filter.2 ⟨Finset.mem_filter.2 hm, hlt⟩⟩
                rw [Finset.mem_filter, Finset.mem_filter] at hy
                refine ⟨(c, cp.2, y), ?_, hcpe.symm⟩
                rw [Finset.mem_filter, memArc]
                refine ⟨⟨⟨hc, hxA, hy.1.1⟩, hxd, hy.1.2, hy.2, ?_⟩, rfl⟩
                intro z hz hzd hzz
                have := hymin z (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hz, hzd⟩, hzz.1⟩)
                linarith [hzz.2]
          _ ≤ #((Arc.filter (fun b => b.1 = c)).image (fun b => (b.1, b.2.1))) + 1 :=
              Finset.card_insert_le _ _
          _ ≤ #(Arc.filter (fun b => b.1 = c)) + 1 := by
              gcongr; exact Finset.card_image_le
      · have hE : ((L ×ˢ A).filter fun cp => dist cp.2 cp.1.1 = cp.1.2).filter
            (fun cp => cp.1 = c) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro cp hcp
          simp only [Finset.mem_filter, Finset.mem_product] at hcp
          obtain ⟨⟨⟨-, hxA⟩, hxd⟩, hc1⟩ := hcp
          rw [hc1] at hxd
          exact hK ⟨cp.2, Finset.mem_filter.2 ⟨hxA, hxd⟩⟩
        rw [hE, Finset.card_empty]; omega
    omega
  · let F := hZ.toFinset
    let R : ((_ : ℕ) × ℕ) → ℝ² → Prop := fun x p =>
      p ∈ (Set.range (γ x.1) ∩ Set.range (γ x.2)) \ (A : Set ℝ²)
    let R' : (ℝ² × ℝ) × (ℝ² × ℝ) → ℝ² → Prop := fun cc p =>
      cc.1 ≠ cc.2 ∧ dist p cc.1.1 = cc.1.2 ∧ dist p cc.2.1 = cc.2.2
    have hcardT : ∀ i ∈ Finset.range Q.card, ∀ j ∈ (Finset.range Q.card).erase i,
        ((Set.range (γ i) ∩ Set.range (γ j)) \ (A : Set ℝ²)).ncard =
          #(F.filter (fun p => R ⟨i, j⟩ p)) := by
      intro i hi j hj
      have hsub := hT i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
      rw [← Set.ncard_coe_finset]
      congr 1
      ext p
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, F, Set.Finite.mem_toFinset, R]
      exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hcardT i hi j hj))]
    rw [Finset.sum_sigma' (Finset.range Q.card) (fun i => (Finset.range Q.card).erase i)
      (fun i j => #(F.filter (fun p => R ⟨i, j⟩ p)))]
    calc ∑ x ∈ (Finset.range Q.card).sigma (fun i => (Finset.range Q.card).erase i),
          #(F.filter (fun p => R ⟨x.1, x.2⟩ p))
        = ∑ x ∈ (Finset.range Q.card).sigma (fun i => (Finset.range Q.card).erase i),
            ∑ p ∈ F, if R x p then 1 else 0 := by simp only [Finset.card_filter]
      _ = ∑ p ∈ F, ∑ x ∈ (Finset.range Q.card).sigma (fun i => (Finset.range Q.card).erase i),
            if R x p then 1 else 0 := Finset.sum_comm
      _ = ∑ p ∈ F, #(((Finset.range Q.card).sigma (fun i => (Finset.range Q.card).erase i)).filter
            (fun x => R x p)) := by simp only [Finset.card_filter]
      _ ≤ ∑ p ∈ F, #((L ×ˢ L).filter (fun cc => R' cc p)) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.card_le_card_of_injOn (fun x => ((a x.1).1, (a x.2).1))
          · intro x hx
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma] at hx
            obtain ⟨⟨hx1, hx2⟩, hR⟩ := hx
            have hx12 := (Finset.ne_of_mem_erase hx2).symm
            have hx2' := Finset.mem_of_mem_erase hx2
            rw [Finset.mem_range] at hx1 hx2'
            obtain ⟨⟨hp1, hp2⟩, hpA⟩ := hR
            obtain ⟨⟨hL, -, -⟩, -⟩ := (memArc _).1 (ha x.1 hx1)
            obtain ⟨⟨hL', -, -⟩, -⟩ := (memArc _).1 (ha x.2 hx2')
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨hL, hL'⟩, fun hc => hx12 (same _ _ hx1 hx2' hc p hp1 hp2 hpA),
              hrange _ hx1 p hp1, hrange _ hx2' p hp2⟩
          · intro x hx y hy hxy
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma] at hx hy
            obtain ⟨⟨hx1, hx2⟩, ⟨hpx1, hpx2⟩, hpA⟩ := hx
            obtain ⟨⟨hy1, hy2⟩, ⟨hpy1, hpy2⟩, -⟩ := hy
            have hx2' := Finset.mem_of_mem_erase hx2
            have hy2' := Finset.mem_of_mem_erase hy2
            rw [Finset.mem_range] at hx1 hx2' hy1 hy2'
            simp only [Prod.mk.injEq] at hxy
            have e1 := same _ _ hx1 hy1 hxy.1 p hpx1 hpy1 hpA
            have e2 := same _ _ hx2' hy2' hxy.2 p hpx2 hpy2 hpA
            exact Sigma.ext e1 (heq_of_eq e2)
      _ = ∑ cc ∈ L ×ˢ L, #(F.filter (fun p => R' cc p)) := by
          simp only [Finset.card_filter]; exact Finset.sum_comm
      _ ≤ ∑ cc ∈ L ×ˢ L, 2 := by
          apply Finset.sum_le_sum
          intro cc hcc
          by_cases hcc' : cc.1 = cc.2
          · have hE : F.filter (fun p => R' cc p) = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro p hp
              exact (Finset.mem_filter.1 hp).2.1 hcc'
            rw [hE, Finset.card_empty]; omega
          · apply OMA.Helpers.two_circles_card hcc'
            intro p hp
            exact (Finset.mem_filter.1 hp).2.2
      _ = 2 * L.card ^ 2 := by
          rw [Finset.sum_const, Finset.card_product, smul_eq_mul]; ring
