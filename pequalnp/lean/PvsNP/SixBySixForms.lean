import PvsNP.SixBySix

/-!
# The 6 × 6 middle layer with genuinely trilinear factors

`SixBySix.lean` proves that the `6 × 6` permanent is, up to an error of size `lam`, a sum of
seventeen split products, but its predicate `IsSplit3` allows the two factors to be arbitrary
functions of three rows. Here the factors are required to be trilinear forms given by explicit
coefficient tensors:

* `triForm c u v w = ∑ p q r, c p q r * u p * v q * w r`;
* `IsTriSplit t`: for some splitting of the six rows into `a, b, c` and `d, e, f`, `t` is a
  `triForm` of rows `a, b, c` times a `triForm` of rows `d, e, f`;
* `IsTriSplitOn a b c d e f t`: the same with the splitting `abc|def` prescribed.

The definitions and the Laplace count are stated over any commutative ring, the border bound
over any field.

Main statements:

* `triForm_perm3C`, `triForm_twoOneC`, `triForm_sqC`: the factors `perm3 p q r`, `twoOne p q`
  and `sq lam` of `SixBySix.lean` are `triForm`s of explicit tensors (sums of indicator tensors),
  and `triForm_smul` gives their scalar multiples;
* `permanent_add_eq_seventeen_triSplit`: for `lam ≠ 0`, `permanent A + lam * rest A` is a sum
  of seventeen functions, each `IsTriSplit`;
* `permanent_add_eq_ten_add_seven_triSplit`: the same, recording the splittings: one term for
  each of the ten splittings three against three, and seven more for `012|345`;
* `permanent_eq_twenty_triSplitOn`, `permanent_eq_twenty_triSplit`: the permanent is a sum of
  twenty functions that are all split products for the same splitting `012|345` (Laplace
  expansion along rows `0, 1, 2`, `permanent_fin_six_laplace_rows`);
* `tendsto_seventeen_triSplit`: over `ℝ`, the seventeen split products converge to the
  permanent as `lam → 0`.

Tools for other constructions: `IsTriForm` (being a `triForm`) is closed under sums and scalar
multiples and contains the monomials, and `isTriSplit_mk` turns a split product `mk …` of
`SixBySix.lean` with `IsTriForm` factors into an `IsTriSplit` one. `triForm_single` and
`triForm_injective` show the coefficient tensor is determined by the form, and
`triForm_add_left`, `triForm_smul_left` (and `_mid`, `_right`) are linearity in each argument.
-/

namespace PvsNP

open Matrix

section Ring

variable {R : Type*} [CommRing R]

/-! ### Trilinear forms with a coefficient tensor -/

/-- The trilinear form with coefficient tensor `c`, evaluated on the vectors `u, v, w`. -/
def triForm (c : Fin 6 → Fin 6 → Fin 6 → R) (u v w : Fin 6 → R) : R :=
  ∑ p, ∑ q, ∑ r, c p q r * u p * v q * w r

/-- `triForm` is additive in the coefficient tensor. -/
theorem triForm_add (c c' : Fin 6 → Fin 6 → Fin 6 → R) (u v w : Fin 6 → R) :
    triForm (c + c') u v w = triForm c u v w + triForm c' u v w := by
  simp only [triForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `triForm` is homogeneous in the coefficient tensor. -/
theorem triForm_smul (k : R) (c : Fin 6 → Fin 6 → Fin 6 → R) (u v w : Fin 6 → R) :
    triForm (k • c) u v w = k * triForm c u v w := by
  simp only [triForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem triForm_zero (u v w : Fin 6 → R) :
    triForm (0 : Fin 6 → Fin 6 → Fin 6 → R) u v w = 0 := by
  simp [triForm]

/-- `triForm c` is additive in its first argument. -/
theorem triForm_add_left (c : Fin 6 → Fin 6 → Fin 6 → R) (u u' v w : Fin 6 → R) :
    triForm c (u + u') v w = triForm c u v w + triForm c u' v w := by
  simp only [triForm, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- `triForm c` is homogeneous in its first argument. -/
theorem triForm_smul_left (c : Fin 6 → Fin 6 → Fin 6 → R) (k : R) (u v w : Fin 6 → R) :
    triForm c (k • u) v w = k * triForm c u v w := by
  simp only [triForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  ring

/-- `triForm c` is additive in its second argument. -/
theorem triForm_add_mid (c : Fin 6 → Fin 6 → Fin 6 → R) (u v v' w : Fin 6 → R) :
    triForm c u (v + v') w = triForm c u v w + triForm c u v' w := by
  simp only [triForm, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- `triForm c` is homogeneous in its second argument. -/
theorem triForm_smul_mid (c : Fin 6 → Fin 6 → Fin 6 → R) (k : R) (u v w : Fin 6 → R) :
    triForm c u (k • v) w = k * triForm c u v w := by
  simp only [triForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  ring

/-- `triForm c` is additive in its third argument. -/
theorem triForm_add_right (c : Fin 6 → Fin 6 → Fin 6 → R) (u v w w' : Fin 6 → R) :
    triForm c u v (w + w') = triForm c u v w + triForm c u v w' := by
  simp only [triForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- `triForm c` is homogeneous in its third argument. -/
theorem triForm_smul_right (c : Fin 6 → Fin 6 → Fin 6 → R) (k : R) (u v w : Fin 6 → R) :
    triForm c u v (k • w) = k * triForm c u v w := by
  simp only [triForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  ring

/-- The indicator tensor of the index triple `(p, q, r)`. -/
def mono (p q r : Fin 6) : Fin 6 → Fin 6 → Fin 6 → R :=
  fun p' q' r' => if p' = p then (if q' = q then (if r' = r then 1 else 0) else 0) else 0

/-- A monomial `u p * v q * w r` is the `triForm` of an indicator tensor. -/
theorem triForm_mono (p q r : Fin 6) (u v w : Fin 6 → R) :
    triForm (mono p q r) u v w = u p * v q * w r := by
  unfold triForm
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, Finset.sum_eq_single r]
  · simp [mono]
  · intro r' _ h
    simp [mono, h]
  · simp
  · intro q' _ h
    simp [mono, h]
  · simp
  · intro p' _ h
    simp [mono, h]
  · simp

/-- The coefficient tensor is recovered by evaluating the form on basis vectors, so it is
determined by the form. -/
theorem triForm_single (c : Fin 6 → Fin 6 → Fin 6 → R) (p q r : Fin 6) :
    triForm c (Pi.single p 1) (Pi.single q 1) (Pi.single r 1) = c p q r := by
  unfold triForm
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, Finset.sum_eq_single r]
  · simp
  · intro r' _ h
    simp [h]
  · simp
  · intro q' _ h
    simp [h]
  · simp
  · intro p' _ h
    simp [h]
  · simp

/-- Two coefficient tensors giving the same form are equal. -/
theorem triForm_injective {c c' : Fin 6 → Fin 6 → Fin 6 → R}
    (h : ∀ u v w, triForm c u v w = triForm c' u v w) : c = c' := by
  funext p q r
  rw [← triForm_single c p q r, ← triForm_single c' p q r, h]

/-! ### The factors of `SixBySix.lean` as trilinear forms -/

/-- Coefficient tensor of `perm3 p q r`: the six index triples that permute `(p, q, r)`. -/
def perm3C (p q r : Fin 6) : Fin 6 → Fin 6 → Fin 6 → R :=
  mono p q r + mono p r q + mono q p r + mono q r p + mono r p q + mono r q p

/-- Coefficient tensor of `twoOne p q`: the three index triples using `p` twice and `q` once. -/
def twoOneC (p q : Fin 6) : Fin 6 → Fin 6 → Fin 6 → R :=
  mono p p q + mono p q p + mono q p p

/-- Coefficient tensor of `sq lam`. -/
def sqC (lam : R) : Fin 6 → Fin 6 → Fin 6 → R :=
  perm3C 0 1 2 + lam • perm3C 3 4 5

theorem triForm_perm3C (p q r : Fin 6) (u v w : Fin 6 → R) :
    triForm (perm3C p q r) u v w = perm3 p q r u v w := by
  simp only [perm3C, triForm_add, triForm_mono, perm3]

theorem triForm_twoOneC (p q : Fin 6) (u v w : Fin 6 → R) :
    triForm (twoOneC p q) u v w = twoOne p q u v w := by
  simp only [twoOneC, triForm_add, triForm_mono, twoOne]

theorem triForm_sqC (lam : R) (u v w : Fin 6 → R) :
    triForm (sqC lam) u v w = sq lam u v w := by
  simp only [sqC, triForm_add, triForm_smul, triForm_perm3C, sq]

/-- Scalar multiples of `perm3 p q r` are trilinear forms. -/
theorem triForm_smul_perm3C (k : R) (p q r : Fin 6) (u v w : Fin 6 → R) :
    triForm (k • perm3C p q r) u v w = k * perm3 p q r u v w := by
  rw [triForm_smul, triForm_perm3C]

/-- Scalar multiples of `twoOne p q` are trilinear forms. -/
theorem triForm_smul_twoOneC (k : R) (p q : Fin 6) (u v w : Fin 6 → R) :
    triForm (k • twoOneC p q) u v w = k * twoOne p q u v w := by
  rw [triForm_smul, triForm_twoOneC]

/-- Scalar multiples of `sq lam` are trilinear forms. -/
theorem triForm_smul_sqC (k lam : R) (u v w : Fin 6 → R) :
    triForm (k • sqC lam) u v w = k * sq lam u v w := by
  rw [triForm_smul, triForm_sqC]

/-! ### The predicate "is a trilinear form" and its closure properties -/

/-- `F` is a trilinear form: it is `triForm c` for some coefficient tensor `c`. -/
def IsTriForm (F : (Fin 6 → R) → (Fin 6 → R) → (Fin 6 → R) → R) : Prop :=
  ∃ c : Fin 6 → Fin 6 → Fin 6 → R, ∀ u v w, F u v w = triForm c u v w

theorem isTriForm_triForm (c : Fin 6 → Fin 6 → Fin 6 → R) : IsTriForm (triForm c) :=
  ⟨c, fun _ _ _ => rfl⟩

theorem IsTriForm.add {F G : (Fin 6 → R) → (Fin 6 → R) → (Fin 6 → R) → R}
    (hF : IsTriForm F) (hG : IsTriForm G) : IsTriForm fun u v w => F u v w + G u v w := by
  obtain ⟨cF, hF⟩ := hF
  obtain ⟨cG, hG⟩ := hG
  exact ⟨cF + cG, fun u v w => by simp only [triForm_add, hF, hG]⟩

theorem IsTriForm.const_mul (k : R) {F : (Fin 6 → R) → (Fin 6 → R) → (Fin 6 → R) → R}
    (hF : IsTriForm F) : IsTriForm fun u v w => k * F u v w := by
  obtain ⟨cF, hF⟩ := hF
  exact ⟨k • cF, fun u v w => by simp only [triForm_smul, hF]⟩

/-- A monomial `u p * v q * w r` is a trilinear form. -/
theorem isTriForm_monomial (p q r : Fin 6) :
    IsTriForm fun u v w : Fin 6 → R => u p * v q * w r :=
  ⟨mono p q r, fun u v w => (triForm_mono p q r u v w).symm⟩

theorem isTriForm_perm3 (p q r : Fin 6) : IsTriForm (perm3 (R := R) p q r) :=
  ⟨perm3C p q r, fun u v w => (triForm_perm3C p q r u v w).symm⟩

theorem isTriForm_twoOne (p q : Fin 6) : IsTriForm (twoOne (R := R) p q) :=
  ⟨twoOneC p q, fun u v w => (triForm_twoOneC p q u v w).symm⟩

theorem isTriForm_sq (lam : R) : IsTriForm (sq lam) :=
  ⟨sqC lam, fun u v w => (triForm_sqC lam u v w).symm⟩

/-! ### Split products with trilinear factors -/

/-- The split product with coefficient tensors `cF` (rows `a, b, c`) and `cG` (rows
`d, e, f`). -/
def triMk (a b c d e f : Fin 6) (cF cG : Fin 6 → Fin 6 → Fin 6 → R) :
    Matrix (Fin 6) (Fin 6) R → R :=
  fun A => triForm cF (A a) (A b) (A c) * triForm cG (A d) (A e) (A f)

/-- `t` is a split product for the given splitting `abc|def` of the rows: a trilinear form in
rows `a, b, c` times a trilinear form in rows `d, e, f`. -/
def IsTriSplitOn (a b c d e f : Fin 6) (t : Matrix (Fin 6) (Fin 6) R → R) : Prop :=
  ∃ cF cG : Fin 6 → Fin 6 → Fin 6 → R,
    ∀ A, t A = triForm cF (A a) (A b) (A c) * triForm cG (A d) (A e) (A f)

/-- `t` is a split product with trilinear factors: for some splitting of the six rows into
`a, b, c` and `d, e, f`, it is a trilinear form in the first three rows times a trilinear form
in the last three. -/
def IsTriSplit (t : Matrix (Fin 6) (Fin 6) R → R) : Prop :=
  ∃ a b c d e f : Fin 6, [a, b, c, d, e, f].Nodup ∧
    ∃ cF cG : Fin 6 → Fin 6 → Fin 6 → R,
      ∀ A, t A = triForm cF (A a) (A b) (A c) * triForm cG (A d) (A e) (A f)

theorem isTriSplitOn_triMk (a b c d e f : Fin 6) (cF cG : Fin 6 → Fin 6 → Fin 6 → R) :
    IsTriSplitOn a b c d e f (triMk a b c d e f cF cG) :=
  ⟨cF, cG, fun _ => rfl⟩

theorem IsTriSplitOn.isTriSplit {a b c d e f : Fin 6} {t : Matrix (Fin 6) (Fin 6) R → R}
    (h : [a, b, c, d, e, f].Nodup) (ht : IsTriSplitOn a b c d e f t) : IsTriSplit t :=
  ⟨a, b, c, d, e, f, h, ht⟩

theorem isTriSplit_iff (t : Matrix (Fin 6) (Fin 6) R → R) :
    IsTriSplit t ↔
      ∃ a b c d e f : Fin 6, [a, b, c, d, e, f].Nodup ∧ IsTriSplitOn a b c d e f t :=
  Iff.rfl

theorem isTriSplit_triMk (a b c d e f : Fin 6) (h : [a, b, c, d, e, f].Nodup)
    (cF cG : Fin 6 → Fin 6 → Fin 6 → R) : IsTriSplit (triMk a b c d e f cF cG) :=
  ⟨a, b, c, d, e, f, h, cF, cG, fun _ => rfl⟩

/-! ### Laplace expansion along rows `0, 1, 2`: twenty split products, one splitting -/

/-- The `6 × 6` permanent via Laplace expansion along the first three rows: a sum over the
twenty ways of choosing which three columns they use. -/
theorem permanent_fin_six_laplace_rows (A : Matrix (Fin 6) (Fin 6) R) :
    A.permanent =
      perm3 0 1 2 (A 0) (A 1) (A 2) * perm3 3 4 5 (A 3) (A 4) (A 5)
      + perm3 0 1 3 (A 0) (A 1) (A 2) * perm3 2 4 5 (A 3) (A 4) (A 5)
      + perm3 0 1 4 (A 0) (A 1) (A 2) * perm3 2 3 5 (A 3) (A 4) (A 5)
      + perm3 0 1 5 (A 0) (A 1) (A 2) * perm3 2 3 4 (A 3) (A 4) (A 5)
      + perm3 0 2 3 (A 0) (A 1) (A 2) * perm3 1 4 5 (A 3) (A 4) (A 5)
      + perm3 0 2 4 (A 0) (A 1) (A 2) * perm3 1 3 5 (A 3) (A 4) (A 5)
      + perm3 0 2 5 (A 0) (A 1) (A 2) * perm3 1 3 4 (A 3) (A 4) (A 5)
      + perm3 0 3 4 (A 0) (A 1) (A 2) * perm3 1 2 5 (A 3) (A 4) (A 5)
      + perm3 0 3 5 (A 0) (A 1) (A 2) * perm3 1 2 4 (A 3) (A 4) (A 5)
      + perm3 0 4 5 (A 0) (A 1) (A 2) * perm3 1 2 3 (A 3) (A 4) (A 5)
      + perm3 1 2 3 (A 0) (A 1) (A 2) * perm3 0 4 5 (A 3) (A 4) (A 5)
      + perm3 1 2 4 (A 0) (A 1) (A 2) * perm3 0 3 5 (A 3) (A 4) (A 5)
      + perm3 1 2 5 (A 0) (A 1) (A 2) * perm3 0 3 4 (A 3) (A 4) (A 5)
      + perm3 1 3 4 (A 0) (A 1) (A 2) * perm3 0 2 5 (A 3) (A 4) (A 5)
      + perm3 1 3 5 (A 0) (A 1) (A 2) * perm3 0 2 4 (A 3) (A 4) (A 5)
      + perm3 1 4 5 (A 0) (A 1) (A 2) * perm3 0 2 3 (A 3) (A 4) (A 5)
      + perm3 2 3 4 (A 0) (A 1) (A 2) * perm3 0 1 5 (A 3) (A 4) (A 5)
      + perm3 2 3 5 (A 0) (A 1) (A 2) * perm3 0 1 4 (A 3) (A 4) (A 5)
      + perm3 2 4 5 (A 0) (A 1) (A 2) * perm3 0 1 3 (A 3) (A 4) (A 5)
      + perm3 3 4 5 (A 0) (A 1) (A 2) * perm3 0 1 2 (A 3) (A 4) (A 5) := by
  rw [← Matrix.permanent_transpose, permanent_fin_six_laplace]
  simp only [perm3, Matrix.transpose_apply]
  ring

/-- The twenty split products of the Laplace expansion along rows `0, 1, 2`. -/
def laplaceTerms : List (Matrix (Fin 6) (Fin 6) R → R) :=
  [triMk 0 1 2 3 4 5 (perm3C 0 1 2) (perm3C 3 4 5),
   triMk 0 1 2 3 4 5 (perm3C 0 1 3) (perm3C 2 4 5),
   triMk 0 1 2 3 4 5 (perm3C 0 1 4) (perm3C 2 3 5),
   triMk 0 1 2 3 4 5 (perm3C 0 1 5) (perm3C 2 3 4),
   triMk 0 1 2 3 4 5 (perm3C 0 2 3) (perm3C 1 4 5),
   triMk 0 1 2 3 4 5 (perm3C 0 2 4) (perm3C 1 3 5),
   triMk 0 1 2 3 4 5 (perm3C 0 2 5) (perm3C 1 3 4),
   triMk 0 1 2 3 4 5 (perm3C 0 3 4) (perm3C 1 2 5),
   triMk 0 1 2 3 4 5 (perm3C 0 3 5) (perm3C 1 2 4),
   triMk 0 1 2 3 4 5 (perm3C 0 4 5) (perm3C 1 2 3),
   triMk 0 1 2 3 4 5 (perm3C 1 2 3) (perm3C 0 4 5),
   triMk 0 1 2 3 4 5 (perm3C 1 2 4) (perm3C 0 3 5),
   triMk 0 1 2 3 4 5 (perm3C 1 2 5) (perm3C 0 3 4),
   triMk 0 1 2 3 4 5 (perm3C 1 3 4) (perm3C 0 2 5),
   triMk 0 1 2 3 4 5 (perm3C 1 3 5) (perm3C 0 2 4),
   triMk 0 1 2 3 4 5 (perm3C 1 4 5) (perm3C 0 2 3),
   triMk 0 1 2 3 4 5 (perm3C 2 3 4) (perm3C 0 1 5),
   triMk 0 1 2 3 4 5 (perm3C 2 3 5) (perm3C 0 1 4),
   triMk 0 1 2 3 4 5 (perm3C 2 4 5) (perm3C 0 1 3),
   triMk 0 1 2 3 4 5 (perm3C 3 4 5) (perm3C 0 1 2)]

theorem laplaceTerms_length : (laplaceTerms (R := R)).length = 20 := rfl

theorem laplaceTerms_isTriSplitOn :
    ∀ t ∈ laplaceTerms (R := R), IsTriSplitOn 0 1 2 3 4 5 t := by
  intro t ht
  simp only [laplaceTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact isTriSplitOn_triMk _ _ _ _ _ _ _ _

theorem laplaceTerms_sum (A : Matrix (Fin 6) (Fin 6) R) :
    A.permanent = ((laplaceTerms (R := R)).map fun t => t A).sum := by
  rw [permanent_fin_six_laplace_rows]
  simp only [laplaceTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, triMk,
    triForm_perm3C]
  ring

/-- **Laplace count in the language of trilinear split products.** The `6 × 6` permanent is a
sum of twenty split products that all use the same splitting `012|345` of the rows. -/
theorem permanent_eq_twenty_triSplitOn :
    ∃ ts : List (Matrix (Fin 6) (Fin 6) R → R), ts.length = 20 ∧
      (∀ t ∈ ts, IsTriSplitOn 0 1 2 3 4 5 t) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) R, A.permanent = (ts.map fun t => t A).sum :=
  ⟨laplaceTerms, laplaceTerms_length, laplaceTerms_isTriSplitOn, laplaceTerms_sum⟩

/-- The same statement with the predicate `IsTriSplit` used in the border bound. -/
theorem permanent_eq_twenty_triSplit :
    ∃ ts : List (Matrix (Fin 6) (Fin 6) R → R), ts.length = 20 ∧
      (∀ t ∈ ts, IsTriSplit t) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) R, A.permanent = (ts.map fun t => t A).sum :=
  ⟨laplaceTerms, laplaceTerms_length,
    fun t ht => (laplaceTerms_isTriSplitOn t ht).isTriSplit (by decide), laplaceTerms_sum⟩

end Ring

section Field

variable {K : Type*} [Field K]

/-- A split product with trilinear factors is in particular a split product in the permissive
sense of `SixBySix.lean`. -/
theorem IsTriSplit.isSplit3 {t : Matrix (Fin 6) (Fin 6) K → K} (h : IsTriSplit t) :
    IsSplit3 t := by
  obtain ⟨a, b, c, d, e, f, hnd, cF, cG, hA⟩ := h
  exact ⟨a, b, c, d, e, f, hnd, triForm cF, triForm cG, funext hA⟩

/-- The split product `mk a b c d e f F G` of `SixBySix.lean` has trilinear factors as soon as
`F` and `G` are trilinear forms. -/
theorem isTriSplit_mk {a b c d e f : Fin 6} (h : [a, b, c, d, e, f].Nodup)
    {F G : (Fin 6 → K) → (Fin 6 → K) → (Fin 6 → K) → K} (hF : IsTriForm F) (hG : IsTriForm G) :
    IsTriSplit (mk a b c d e f F G) := by
  obtain ⟨cF, hF⟩ := hF
  obtain ⟨cG, hG⟩ := hG
  refine ⟨a, b, c, d, e, f, h, cF, cG, fun A => ?_⟩
  show F (A a) (A b) (A c) * G (A d) (A e) (A f) = _
  rw [hF, hG]

/-- `IsTriSplit` is `IsSplit3` with both factors required to be trilinear forms. -/
theorem isTriSplit_iff_mk (t : Matrix (Fin 6) (Fin 6) K → K) :
    IsTriSplit t ↔ ∃ a b c d e f : Fin 6, [a, b, c, d, e, f].Nodup ∧
      ∃ F G : (Fin 6 → K) → (Fin 6 → K) → (Fin 6 → K) → K,
        IsTriForm F ∧ IsTriForm G ∧ t = mk a b c d e f F G := by
  constructor
  · rintro ⟨a, b, c, d, e, f, hnd, cF, cG, hA⟩
    exact ⟨a, b, c, d, e, f, hnd, triForm cF, triForm cG, isTriForm_triForm cF,
      isTriForm_triForm cG, funext hA⟩
  · rintro ⟨a, b, c, d, e, f, hnd, F, G, hF, hG, rfl⟩
    exact isTriSplit_mk hnd hF hG

/-! ### The border bound: seventeen split products with trilinear factors -/

/-- The ten splittings of the six rows three against three, written with row `0` on the left
(so no two of them are complementary). -/
def splittings : List (Fin 6 × Fin 6 × Fin 6 × Fin 6 × Fin 6 × Fin 6) :=
  [(0, 1, 2, 3, 4, 5), (0, 1, 3, 2, 4, 5), (0, 1, 4, 2, 3, 5), (0, 1, 5, 2, 3, 4),
   (0, 2, 3, 1, 4, 5), (0, 2, 4, 1, 3, 5), (0, 2, 5, 1, 3, 4), (0, 3, 4, 1, 2, 5),
   (0, 3, 5, 1, 2, 4), (0, 4, 5, 1, 2, 3)]

/-- Each entry of `splittings` lists the six rows without repetition, and row `0` comes first. -/
theorem splittings_nodup :
    ∀ s ∈ splittings, [s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2].Nodup ∧
      s.1 = 0 := by
  decide

/-- The ten left-hand row sets are pairwise different. -/
theorem splittings_left_nodup :
    (splittings.map fun s => ({s.1, s.2.1, s.2.2.1} : Finset (Fin 6))).Nodup := by
  decide

/-- The ten squares, one for each splitting of the rows three against three, divided by
`lam`. -/
def squareTerms (lam : K) : List (Matrix (Fin 6) (Fin 6) K → K) :=
  [triMk 0 1 2 3 4 5 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 1 3 2 4 5 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 1 4 2 3 5 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 1 5 2 3 4 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 2 3 1 4 5 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 2 4 1 3 5 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 2 5 1 3 4 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 3 4 1 2 5 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 3 5 1 2 4 (lam⁻¹ • sqC lam) (sqC lam),
   triMk 0 4 5 1 2 3 (lam⁻¹ • sqC lam) (sqC lam)]

/-- The seven correction terms, all for the splitting `012|345`. -/
def garbageTerms (lam : K) : List (Matrix (Fin 6) (Fin 6) K → K) :=
  [triMk 0 1 2 3 4 5 ((-4 * lam⁻¹) • perm3C 0 1 2) (perm3C 0 1 2),
   triMk 0 1 2 3 4 5 ((-4 * lam⁻¹) • twoOneC 0 2) (twoOneC 1 2),
   triMk 0 1 2 3 4 5 ((-4 * lam⁻¹) • twoOneC 0 1) (twoOneC 2 1),
   triMk 0 1 2 3 4 5 ((-4 * lam⁻¹) • twoOneC 1 2) (twoOneC 0 2),
   triMk 0 1 2 3 4 5 ((-4 * lam⁻¹) • twoOneC 1 0) (twoOneC 2 0),
   triMk 0 1 2 3 4 5 ((-4 * lam⁻¹) • twoOneC 2 1) (twoOneC 0 1),
   triMk 0 1 2 3 4 5 ((-4 * lam⁻¹) • twoOneC 2 0) (twoOneC 1 0)]

/-- The seventeen split products: ten squares and seven corrections. -/
def seventeenTerms (lam : K) : List (Matrix (Fin 6) (Fin 6) K → K) :=
  squareTerms lam ++ garbageTerms lam

theorem squareTerms_length (lam : K) : (squareTerms lam).length = 10 := rfl

theorem garbageTerms_length (lam : K) : (garbageTerms lam).length = 7 := rfl

theorem seventeenTerms_length (lam : K) : (seventeenTerms lam).length = 17 := rfl

theorem squareTerms_isTriSplit (lam : K) : ∀ t ∈ squareTerms lam, IsTriSplit t := by
  intro t ht
  simp only [squareTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact isTriSplit_triMk _ _ _ _ _ _ (by decide) _ _

/-- The ten squares use the ten splittings of `splittings`, one each. -/
theorem squareTerms_splittings (lam : K) :
    List.Forall₂
      (fun s t => IsTriSplitOn s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 t)
      splittings (squareTerms lam) := by
  unfold splittings squareTerms
  repeat first
    | exact List.Forall₂.nil
    | refine List.Forall₂.cons (isTriSplitOn_triMk _ _ _ _ _ _ _ _) ?_

/-- The seven correction terms all use the splitting `012|345`. -/
theorem garbageTerms_isTriSplitOn (lam : K) :
    ∀ t ∈ garbageTerms lam, IsTriSplitOn 0 1 2 3 4 5 t := by
  intro t ht
  simp only [garbageTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact isTriSplitOn_triMk _ _ _ _ _ _ _ _

theorem seventeenTerms_isTriSplit (lam : K) : ∀ t ∈ seventeenTerms lam, IsTriSplit t := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact squareTerms_isTriSplit lam t h
  · exact (garbageTerms_isTriSplitOn lam t h).isTriSplit (by decide)

/-- For nonzero `lam` the seventeen split products sum to `permanent A + lam * rest A`. -/
theorem seventeenTerms_sum (lam : K) (hlam : lam ≠ 0) (A : Matrix (Fin 6) (Fin 6) K) :
    A.permanent + lam * rest A = ((seventeenTerms lam).map fun t => t A).sum := by
  have h := six_squares_identity A lam
  simp only [squares, garbage] at h
  simp only [seventeenTerms, squareTerms, garbageTerms, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, triMk, triForm_smul,
    triForm_sqC, triForm_perm3C, triForm_twoOneC]
  field_simp
  linear_combination h

/-- **Border bound for the 6 × 6 permanent, with trilinear factors.** For every nonzero `lam`,
the permanent plus `lam * rest A` is a sum of seventeen split products, each a trilinear form
in three of the rows times a trilinear form in the other three. Laplace expansion
(`permanent_eq_twenty_triSplit`) uses twenty. -/
theorem permanent_add_eq_seventeen_triSplit (lam : K) (hlam : lam ≠ 0) :
    ∃ ts : List (Matrix (Fin 6) (Fin 6) K → K), ts.length = 17 ∧ (∀ t ∈ ts, IsTriSplit t) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) K,
        A.permanent + lam * rest A = (ts.map fun t => t A).sum :=
  ⟨seventeenTerms lam, seventeenTerms_length lam, seventeenTerms_isTriSplit lam,
    seventeenTerms_sum lam hlam⟩

/-- **Which splittings are used.** The seventeen split products are ten squares, one for each
of the ten splittings of the rows three against three, and seven further products that all use
the splitting `012|345`. -/
theorem permanent_add_eq_ten_add_seven_triSplit (lam : K) (hlam : lam ≠ 0) :
    ∃ ss gs : List (Matrix (Fin 6) (Fin 6) K → K),
      List.Forall₂
        (fun s t => IsTriSplitOn s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 t)
        splittings ss ∧
      gs.length = 7 ∧ (∀ g ∈ gs, IsTriSplitOn 0 1 2 3 4 5 g) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) K,
        A.permanent + lam * rest A = (ss.map fun t => t A).sum + (gs.map fun t => t A).sum := by
  refine ⟨squareTerms lam, garbageTerms lam, squareTerms_splittings lam, garbageTerms_length lam,
    garbageTerms_isTriSplitOn lam, fun A => ?_⟩
  rw [seventeenTerms_sum lam hlam A, seventeenTerms, List.map_append, List.sum_append]

end Field

/-- **The limit.** Over `ℝ` there is a family, indexed by `lam`, of seventeen split products
with trilinear factors whose sum converges to the `6 × 6` permanent as `lam → 0`. -/
theorem tendsto_seventeen_triSplit :
    ∃ ts : ℝ → List (Matrix (Fin 6) (Fin 6) ℝ → ℝ),
      (∀ lam : ℝ, (ts lam).length = 17 ∧ ∀ t ∈ ts lam, IsTriSplit t) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) ℝ,
        Filter.Tendsto (fun lam : ℝ => ((ts lam).map fun t => t A).sum)
          (nhdsWithin 0 {0}ᶜ) (nhds A.permanent) := by
  refine ⟨seventeenTerms, fun lam => ⟨seventeenTerms_length lam, seventeenTerms_isTriSplit lam⟩,
    fun A => ?_⟩
  have hc : Continuous fun lam : ℝ => A.permanent + lam * rest A := by fun_prop
  have h0 := hc.tendsto 0
  simp only [zero_mul, add_zero] at h0
  refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam hl
  exact seventeenTerms_sum lam hl A

end PvsNP
