import PvsNP.SplitRank

/-!
# The `4 × 4` determinant: mixed split rank exactly three

For the standard symplectic form `w(x, y) = x₀ y₁ - x₁ y₀ + x₂ y₃ - x₃ y₂` on `K⁴` the
determinant of a `4 × 4` matrix with rows `r₀, r₁, r₂, r₃` is the Pfaffian of the Gram matrix
`(w(r_a, r_b))`:

`det = w(r₀, r₁) w(r₂, r₃) - w(r₀, r₂) w(r₁, r₃) + w(r₀, r₃) w(r₁, r₂)`.

Each of the three terms is a bilinear form in two rows times a bilinear form in the other two
rows, one term for each of the three pairings `01|23`, `02|13`, `03|12`.

## Main statements (any field `K`)

* `det_eq_three_sympPair`: the identity above.
* `mixedSplit_det_four`: `MixedSplitLE 2 3 det`: in the language of `PvsNP.SplitRank` the
  determinant is a sum of three split products for two rows against two. Laplace expansion
  along two fixed rows uses six terms, and six is optimal when all terms use the same pairing.
* `not_mixedSplit_det_four_two`: `¬ MixedSplitLE 2 2 det`: two split products are not enough,
  whatever row sets they use.
* `mixedSplit_det_four_iff`: `MixedSplitLE 2 n det ↔ 3 ≤ n`.

**Contrast with the permanent.** For the `4 × 4` permanent the corresponding values are larger:
it is a limit of sums of five split products and not of four
(`borderMixedSplit_perm_four_iff` in `PvsNP.SplitRank`, over `ℝ` and `ℂ`), and it is not an
exact sum of five (paper proof in `notes/exact_five_terms_4x4.md`, formalised in the
`FourByFourExact` files), so its exact value is six, the Laplace value. For the determinant
Laplace expansion is therefore NOT optimal, already at `4 × 4`: three terms instead of six.

The identity is the case `n = 4` of the theorem of Lampert and Moshkovitz that the partition
rank of `det₄` is `3` (arXiv:2509.06294), where the alternating form with all coefficients
above the diagonal equal to `1` is used in place of `w`. The lower bound here is the special
case of theirs in which both factors have two rows; the proof is the kernel argument described
at `not_mixedSplit_det_four_two`. See `notes/determinant.md` for the general Pfaffian
construction (for even `k`, `det_{2k}` is a sum of `C(3k/2, k/2)` products for `k` rows against
`k`; for all `k ≥ 2` it is a sum of `2k - 1` products for two rows against `2k - 2`).
-/

namespace PvsNP

open Matrix

section DetFour

variable {K : Type*} [Field K]

/-- The standard symplectic form on `K⁴` applied to rows `a` and `b` of the matrix `A`:
`w(r_a, r_b) = A a 0 * A b 1 - A a 1 * A b 0 + A a 2 * A b 3 - A a 3 * A b 2`. -/
def sympPair (A : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) : K :=
  A a 0 * A b 1 - A a 1 * A b 0 + A a 2 * A b 3 - A a 3 * A b 2

/-- The coefficient table of the standard symplectic form. -/
def sympTable : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

/-- `sympPair` is the bilinear form in rows `a`, `b` with coefficient table `sympTable`. -/
theorem rowForm_sympTable (A : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) :
    rowForm sympTable a b A = sympPair A a b := by
  simp [rowForm, sympTable, sympPair, Fin.sum_univ_four]
  ring

/-- The `4 × 4` determinant written out: the sum over the `24` permutations. -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) K) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2
      - A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1
      + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1
      - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2
      + A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0
      - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0
      + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1
      - A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0
      + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0
      - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1
      + A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0
      - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, Matrix.submatrix]
  ring

/-- **Pfaffian identity at `4 × 4`.** The determinant is the Pfaffian of the Gram matrix of
the rows for the standard symplectic form: three products, one for each pairing of the rows. -/
theorem det_eq_three_sympPair (A : Matrix (Fin 4) (Fin 4) K) :
    A.det = sympPair A 0 1 * sympPair A 2 3 - sympPair A 0 2 * sympPair A 1 3
      + sympPair A 0 3 * sympPair A 1 2 := by
  rw [det_fin_four]
  simp only [sympPair]
  ring

/-- A product of two symplectic pairings on complementary pairs of rows, times a constant, is
a split product in the sense of `FiveTerm.lean`. -/
theorem isSplit_sympPair (s : K) (a b c d : Fin 4) :
    IsSplit a b c d (fun A : Matrix (Fin 4) (Fin 4) K => s * (sympPair A a b * sympPair A c d)) :=
  ⟨s • sympTable, sympTable, fun A => by
    have h : rowForm (s • sympTable) a b A = s * rowForm sympTable a b A := by
      simp [rowForm, Finset.mul_sum, mul_assoc]
    simp only [h, rowForm_sympTable, mul_assoc]⟩

/-- **The `4 × 4` determinant has mixed split rank at most three** (two rows against two), over
every field: it is the sum of three split products, one for each of the pairings `01|23`,
`02|13`, `03|12`. Laplace expansion along two rows uses six. For the permanent the
corresponding value is five in the limit and six exactly (see the header of this file). -/
theorem mixedSplit_det_four :
    MixedSplitLE 2 3 (fun A : Matrix (Fin 4) (Fin 4) K => A.det) := by
  have s₁ := MixedSplitLE.of_isSplitProduct (K := K) (k := 2) (S := {0, 1}) (by decide)
    ((isSplit_sympPair (1 : K) 0 1 2 3).isSplitProduct (by decide))
  have s₂ := MixedSplitLE.of_isSplitProduct (K := K) (k := 2) (S := {0, 2}) (by decide)
    ((isSplit_sympPair (-1 : K) 0 2 1 3).isSplitProduct (by decide))
  have s₃ := MixedSplitLE.of_isSplitProduct (K := K) (k := 2) (S := {0, 3}) (by decide)
    ((isSplit_sympPair (1 : K) 0 3 1 2).isSplitProduct (by decide))
  refine ((s₁.add s₂).add s₃).congr fun A => ?_
  rw [det_eq_three_sympPair]
  ring

end DetFour

/-! ### Lower bound: two split products are not enough -/

namespace DetFour

variable {K : Type*} [Field K]

/-- The determinant of the matrix with rows `e₀, x, y, z`: the `3 × 3` determinant of the
coordinates `1, 2, 3` of `x, y, z`. -/
def D3 (x y z : Fin 4 → K) : K :=
  x 1 * (y 2 * z 3 - y 3 * z 2) - x 2 * (y 1 * z 3 - y 3 * z 1) + x 3 * (y 1 * z 2 - y 2 * z 1)

/-- The linear form with coefficient vector `a`. -/
def lin4 (a x : Fin 4 → K) : K := a 0 * x 0 + a 1 * x 1 + a 2 * x 2 + a 3 * x 3

/-- The bilinear form with coefficient table `G`, as a function of two vectors. -/
def bil4 (G : Matrix (Fin 4) (Fin 4) K) (y z : Fin 4 → K) : K := ∑ p, ∑ q, G p q * y p * z q

/-- The matrix with rows `e₀, u, v, w`. -/
def e0Rows (u v w : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K := Matrix.of ![![1, 0, 0, 0], u, v, w]

theorem D3_vec (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : K) :
    D3 ![x0, x1, x2, x3] ![y0, y1, y2, y3] ![z0, z1, z2, z3] =
      x1 * (y2 * z3 - y3 * z2) - x2 * (y1 * z3 - y3 * z1) + x3 * (y1 * z2 - y2 * z1) := rfl

theorem lin4_vec (a : Fin 4 → K) (x0 x1 x2 x3 : K) :
    lin4 a ![x0, x1, x2, x3] = a 0 * x0 + a 1 * x1 + a 2 * x2 + a 3 * x3 := rfl

theorem D3_cyc (x y z : Fin 4 → K) : D3 z x y = D3 x y z := by simp only [D3]; ring

theorem D3_cyc' (x y z : Fin 4 → K) : D3 y z x = D3 x y z := by simp only [D3]; ring

theorem D3_swap23 (x y z : Fin 4 → K) : D3 x z y = -D3 x y z := by simp only [D3]; ring

theorem D3_swap12 (x y z : Fin 4 → K) : D3 y x z = -D3 x y z := by simp only [D3]; ring

theorem det_rowsMat (u v w : Fin 4 → K) : (e0Rows u v w).det = D3 u v w := by
  rw [det_fin_four]
  simp [e0Rows, D3]
  ring

theorem rowForm_zero_one (F : Matrix (Fin 4) (Fin 4) K) (u v w : Fin 4 → K) :
    rowForm F 0 1 (e0Rows u v w) = lin4 (F 0) u := by
  simp [rowForm, e0Rows, lin4, Fin.sum_univ_four]

theorem rowForm_zero_two (F : Matrix (Fin 4) (Fin 4) K) (u v w : Fin 4 → K) :
    rowForm F 0 2 (e0Rows u v w) = lin4 (F 0) v := by
  simp [rowForm, e0Rows, lin4, Fin.sum_univ_four]

theorem rowForm_zero_three (F : Matrix (Fin 4) (Fin 4) K) (u v w : Fin 4 → K) :
    rowForm F 0 3 (e0Rows u v w) = lin4 (F 0) w := by
  simp [rowForm, e0Rows, lin4, Fin.sum_univ_four]

theorem rowForm_two_three (G : Matrix (Fin 4) (Fin 4) K) (u v w : Fin 4 → K) :
    rowForm G 2 3 (e0Rows u v w) = bil4 G v w := rfl

theorem rowForm_one_three (G : Matrix (Fin 4) (Fin 4) K) (u v w : Fin 4 → K) :
    rowForm G 1 3 (e0Rows u v w) = bil4 G u w := rfl

theorem rowForm_one_two (G : Matrix (Fin 4) (Fin 4) K) (u v w : Fin 4 → K) :
    rowForm G 1 2 (e0Rows u v w) = bil4 G u v := rfl

/-- **Two slices in different directions.** The `3 × 3` determinant `D3 x y z` is not of the
form (linear form in `x`) · (function of `y, z`) + (linear form in `y`) · (function of `x, z`):
choosing `x` and `y` in the kernels of the two linear forms makes the right side vanish, and
the kernels are too large for the determinant to vanish there. Any field. -/
theorem no_mixed (a a' : Fin 4 → K) (g1 g2 : (Fin 4 → K) → (Fin 4 → K) → K)
    (h : ∀ x y z, D3 x y z = lin4 a x * g1 y z + lin4 a' y * g2 x z) : False := by
  have H : ∀ x y z, lin4 a x = 0 → lin4 a' y = 0 → D3 x y z = 0 := fun x y z hx hy => by
    rw [h, hx, hy]; ring
  have h00 : a 0 * a' 0 = 0 := by
    have := H ![-a 1, a 0, 0, 0] ![-a' 2, 0, a' 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h01 : a 0 * a' 1 = 0 := by
    have := H ![-a 1, a 0, 0, 0] ![0, -a' 2, a' 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h02 : a 0 * a' 2 = 0 := by
    have := H ![-a 1, a 0, 0, 0] ![0, 0, -a' 3, a' 2] ![0, 0, 1, 0]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have h03 : a 0 * a' 3 = 0 := by
    have := H ![-a 1, a 0, 0, 0] ![0, 0, -a' 3, a' 2] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have h10 : a 1 * a' 0 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![-a' 1, a' 0, 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have h11 : a 1 * a' 1 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, -a' 3, 0, a' 1] ![0, 1, 0, 0]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h12 : a 1 * a' 2 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, 0, -a' 3, a' 2] ![0, 1, 0, 0]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h13 : a 1 * a' 3 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, -a' 3, 0, a' 1] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h20 : a 2 * a' 0 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![-a' 2, 0, a' 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have h21 : a 2 * a' 1 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, -a' 3, 0, a' 1] ![0, 0, 1, 0]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h22 : a 2 * a' 2 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, 0, -a' 3, a' 2] ![0, 0, 1, 0]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h23 : a 2 * a' 3 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, 0, -a' 3, a' 2] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h30 : a 3 * a' 0 = 0 := by
    have := H ![0, -a 3, 0, a 1] ![-a' 2, 0, a' 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have h31 : a 3 * a' 1 = 0 := by
    have := H ![0, -a 3, 0, a 1] ![0, -a' 2, a' 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have h32 : a 3 * a' 2 = 0 := by
    have := H ![0, -a 3, 0, a 1] ![0, 0, -a' 3, a' 2] ![0, 0, 1, 0]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h33 : a 3 * a' 3 = 0 := by
    have := H ![0, -a 3, 0, a 1] ![0, 0, -a' 3, a' 2] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have h1 := h ![0, 1, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
  rw [D3_vec, lin4_vec, lin4_vec] at h1
  by_cases ha : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0
  · obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
    have Hy : ∀ x y z, lin4 a' y = 0 → D3 x y z = 0 := fun x y z hy =>
      H x y z (by simp [lin4, ha0, ha1, ha2, ha3]) hy
    have hb0 : a' 0 = 0 := by
      have := Hy ![0, 0, 1, 0] ![-a' 1, a' 0, 0, 0] ![0, 0, 0, 1] (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (-1) * this
    have hb1 : a' 1 = 0 := by
      have := Hy ![0, 1, 0, 0] ![0, -a' 2, a' 1, 0] ![0, 0, 0, 1] (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (1) * this
    have hb2 : a' 2 = 0 := by
      have := Hy ![0, 0, 1, 0] ![0, -a' 2, a' 1, 0] ![0, 0, 0, 1] (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (1) * this
    have hb3 : a' 3 = 0 := by
      have := Hy ![0, 0, 1, 0] ![0, -a' 3, 0, a' 1] ![0, 0, 0, 1] (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (1) * this
    norm_num [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at h1
  · have hb0 : a' 0 = 0 := by
      by_contra hne
      exact ha ⟨(mul_eq_zero.mp h00).resolve_right hne, (mul_eq_zero.mp h10).resolve_right hne,
        (mul_eq_zero.mp h20).resolve_right hne, (mul_eq_zero.mp h30).resolve_right hne⟩
    have hb1 : a' 1 = 0 := by
      by_contra hne
      exact ha ⟨(mul_eq_zero.mp h01).resolve_right hne, (mul_eq_zero.mp h11).resolve_right hne,
        (mul_eq_zero.mp h21).resolve_right hne, (mul_eq_zero.mp h31).resolve_right hne⟩
    have hb2 : a' 2 = 0 := by
      by_contra hne
      exact ha ⟨(mul_eq_zero.mp h02).resolve_right hne, (mul_eq_zero.mp h12).resolve_right hne,
        (mul_eq_zero.mp h22).resolve_right hne, (mul_eq_zero.mp h32).resolve_right hne⟩
    have hb3 : a' 3 = 0 := by
      by_contra hne
      exact ha ⟨(mul_eq_zero.mp h03).resolve_right hne, (mul_eq_zero.mp h13).resolve_right hne,
        (mul_eq_zero.mp h23).resolve_right hne, (mul_eq_zero.mp h33).resolve_right hne⟩
    have Hx : ∀ x y z, lin4 a x = 0 → D3 x y z = 0 := fun x y z hx =>
      H x y z hx (by simp [lin4, hb0, hb1, hb2, hb3])
    have ha0 : a 0 = 0 := by
      have := Hx ![-a 1, a 0, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
        (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (1) * this
    have ha1 : a 1 = 0 := by
      have := Hx ![0, -a 2, a 1, 0] ![0, 1, 0, 0] ![0, 0, 0, 1]
        (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (-1) * this
    have ha2 : a 2 = 0 := by
      have := Hx ![0, -a 2, a 1, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
        (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (-1) * this
    have ha3 : a 3 = 0 := by
      have := Hx ![0, -a 3, 0, a 1] ![0, 0, 1, 0] ![0, 0, 0, 1]
        (by rw [lin4_vec]; ring)
      rw [D3_vec] at this
      linear_combination (-1) * this
    exact ha ⟨ha0, ha1, ha2, ha3⟩

/-- **Two slices in the same direction.** `D3 x y z` is not of the form
(linear form in `x`) · (function of `y, z`) + (another linear form in `x`) · (function of
`y, z`). Any field. -/
theorem no_same (a a' : Fin 4 → K) (g1 g2 : (Fin 4 → K) → (Fin 4 → K) → K)
    (h : ∀ x y z, D3 x y z = lin4 a x * g1 y z + lin4 a' x * g2 y z) : False := by
  have H : ∀ x y z, lin4 a x = 0 → lin4 a' x = 0 → D3 x y z = 0 := fun x y z hx hy => by
    rw [h, hx, hy]; ring
  have m01 : a 0 * a' 1 - a 1 * a' 0 = 0 := by
    have := H ![a 1*a' 2 - a 2*a' 1, -a 0*a' 2 + a 2*a' 0, a 0*a' 1 - a 1*a' 0, 0] ![0, 1, 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have m02 : a 0 * a' 2 - a 2 * a' 0 = 0 := by
    have := H ![a 1*a' 2 - a 2*a' 1, -a 0*a' 2 + a 2*a' 0, a 0*a' 1 - a 1*a' 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have m03 : a 0 * a' 3 - a 3 * a' 0 = 0 := by
    have := H ![a 1*a' 3 - a 3*a' 1, -a 0*a' 3 + a 3*a' 0, 0, a 0*a' 1 - a 1*a' 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have m12 : a 1 * a' 2 - a 2 * a' 1 = 0 := by
    have := H ![0, a 2*a' 3 - a 3*a' 2, -a 1*a' 3 + a 3*a' 1, a 1*a' 2 - a 2*a' 1] ![0, 1, 0, 0] ![0, 0, 1, 0]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have m13 : a 1 * a' 3 - a 3 * a' 1 = 0 := by
    have := H ![0, a 2*a' 3 - a 3*a' 2, -a 1*a' 3 + a 3*a' 1, a 1*a' 2 - a 2*a' 1] ![0, 1, 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have m23 : a 2 * a' 3 - a 3 * a' 2 = 0 := by
    have := H ![0, a 2*a' 3 - a 3*a' 2, -a 1*a' 3 + a 3*a' 1, a 1*a' 2 - a 2*a' 1] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this

  have ha0 : a 0 = 0 := by
    have := H ![-a 1, a 0, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; linear_combination (1) * m01)
    rw [D3_vec] at this
    linear_combination (1) * this
  have ha1 : a 1 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, 1, 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; linear_combination (1) * m12)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have ha2 : a 2 = 0 := by
    have := H ![0, -a 2, a 1, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; linear_combination (1) * m12)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have ha3 : a 3 = 0 := by
    have := H ![0, -a 3, 0, a 1] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; ring) (by rw [lin4_vec]; linear_combination (1) * m13)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have hb0 : a' 0 = 0 := by
    have := H ![-a' 1, a' 0, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; linear_combination (-1) * m01) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (1) * this
  have hb1 : a' 1 = 0 := by
    have := H ![0, -a' 2, a' 1, 0] ![0, 1, 0, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; linear_combination (-1) * m12) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have hb2 : a' 2 = 0 := by
    have := H ![0, -a' 2, a' 1, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; linear_combination (-1) * m12) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have hb3 : a' 3 = 0 := by
    have := H ![0, -a' 3, 0, a' 1] ![0, 0, 1, 0] ![0, 0, 0, 1]
      (by rw [lin4_vec]; linear_combination (-1) * m13) (by rw [lin4_vec]; ring)
    rw [D3_vec] at this
    linear_combination (-1) * this
  have h1 := h ![0, 1, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
  rw [D3_vec, lin4_vec, lin4_vec] at h1
  norm_num [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at h1

end DetFour

section Lower

variable {K : Type*} [Field K]

open DetFour

/-- **The `4 × 4` determinant is not a sum of two split products** (two rows against two,
row sets free in each term), over any field. With `mixedSplit_det_four`: the mixed split rank
of `det₄` for two rows against two is exactly `3`. (For all shapes of row sets this is the
theorem `prk(det₄) = 3` of Lampert and Moshkovitz.)

Proof: put `e₀` in row `0`. Each term becomes a linear form in one of the other three rows
times a function of the remaining two, and `no_mixed`, `no_same` exclude all nine
combinations of pairings. -/
theorem not_mixedSplit_det_four_two :
    ¬ MixedSplitLE 2 2 (fun A : Matrix (Fin 4) (Fin 4) K => A.det) := by
  rintro ⟨S, t, hS, ht, hsum⟩
  have hsum' : ∀ A : Matrix (Fin 4) (Fin 4) K, A.det = t 0 A + t 1 A := fun A =>
    (hsum A).trans (Fin.sum_univ_two _)
  have key : ∀ u v w : Fin 4 → K, D3 u v w = t 0 (e0Rows u v w) + t 1 (e0Rows u v w) :=
    fun u v w => by rw [← det_rowsMat, hsum']
  rcases (ht 0).isSplit_of_card_two (hS 0) with ⟨F1, G1, h1⟩ | ⟨F1, G1, h1⟩ | ⟨F1, G1, h1⟩ <;>
  rcases (ht 1).isSplit_of_card_two (hS 1) with ⟨F2, G2, h2⟩ | ⟨F2, G2, h2⟩ | ⟨F2, G2, h2⟩ <;>
  simp only [h1, h2, rowForm_zero_one, rowForm_zero_two, rowForm_zero_three, rowForm_two_three,
    rowForm_one_three, rowForm_one_two] at key
  · -- 01|23, 01|23
    exact no_same (F1 0) (F2 0) (bil4 G1) (bil4 G2) key
  · -- 01|23, 02|13
    exact no_mixed (F1 0) (F2 0) (bil4 G1) (bil4 G2) key
  · -- 01|23, 03|12
    exact no_mixed (F1 0) (F2 0) (fun y z => -bil4 G1 z y) (fun x z => -bil4 G2 x z)
      fun x y z => by linear_combination (D3_swap23 x y z) - key x z y
  · -- 02|13, 01|23
    exact no_mixed (F2 0) (F1 0) (bil4 G2) (bil4 G1) fun x y z => by rw [key x y z]; ring
  · -- 02|13, 02|13
    exact no_same (F1 0) (F2 0) (fun y z => -bil4 G1 y z) (fun y z => -bil4 G2 y z)
      fun x y z => by linear_combination (D3_swap12 x y z) - key y x z
  · -- 02|13, 03|12
    exact no_mixed (F1 0) (F2 0) (fun y z => bil4 G1 z y) (fun x z => bil4 G2 z x)
      fun x y z => by rw [← D3_cyc x y z, key z x y]
  · -- 03|12, 01|23
    exact no_mixed (F2 0) (F1 0) (fun y z => -bil4 G2 z y) (fun x z => -bil4 G1 x z)
      fun x y z => by linear_combination (D3_swap23 x y z) - key x z y
  · -- 03|12, 02|13
    exact no_mixed (F2 0) (F1 0) (fun y z => bil4 G2 z y) (fun x z => bil4 G1 z x)
      fun x y z => by rw [← D3_cyc x y z, key z x y]; ring
  · -- 03|12, 03|12
    exact no_same (F1 0) (F2 0) (bil4 G1) (bil4 G2) fun x y z => by rw [← D3_cyc' x y z, key y z x]

/-- **The mixed split rank of the `4 × 4` determinant is exactly `3`** (two rows against two),
over any field. For the permanent the corresponding statement has `6` in place of `3`
(and `5` for limits). -/
theorem mixedSplit_det_four_iff (n : ℕ) :
    MixedSplitLE 2 n (fun A : Matrix (Fin 4) (Fin 4) K => A.det) ↔ 3 ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact not_mixedSplit_det_four_two (h.mono (by omega) (by simp))
  · intro hn
    exact mixedSplit_det_four.mono hn (by simp)

end Lower

end PvsNP
