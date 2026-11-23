import PvsNP.SplitRank

/-!
# The `4 × 4` determinant is a sum of three split products

For the standard symplectic form `w(x, y) = x₀ y₁ - x₁ y₀ + x₂ y₃ - x₃ y₂` on `K⁴` the
determinant of a `4 × 4` matrix with rows `r₀, r₁, r₂, r₃` is the Pfaffian of the Gram matrix
`(w(r_a, r_b))`:

`det = w(r₀, r₁) w(r₂, r₃) - w(r₀, r₂) w(r₁, r₃) + w(r₀, r₃) w(r₁, r₂)`.

Each of the three terms is a bilinear form in two rows times a bilinear form in the other two
rows, one term for each of the three pairings `01|23`, `02|13`, `03|12`. So in the language of
`PvsNP.SplitRank` the determinant has mixed split rank at most `3` for two rows against two,
over every field (`mixedSplit_det_four`), while Laplace expansion along two fixed rows uses six
terms and is optimal for a fixed pairing.

**Contrast with the permanent.** For the `4 × 4` permanent the corresponding values are larger:
it is a limit of sums of five split products and not of four
(`borderMixedSplit_perm_four_iff` in `PvsNP.SplitRank`, over `ℝ` and `ℂ`), and it is not an
exact sum of five (paper proof in `notes/exact_five_terms_4x4.md`, formalised in the
`FourByFourExact` files), so its exact value is six, the Laplace value. For the determinant
Laplace expansion is therefore NOT optimal, already at `4 × 4`.

The identity is the case `n = 4` of the theorem of Lampert and Moshkovitz that the partition
rank of `det₄` is `3` (arXiv:2509.06294); see `notes/determinant.md` for the general
Pfaffian construction.
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

end PvsNP
