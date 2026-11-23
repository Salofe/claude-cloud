import PvsNP.PermanentLaplace

/-!
# The 4 × 4 permanent is a limit of sums of five split products

Rows `0, 1, 2, 3` of a `4 × 4` matrix `A`. A *split product* is a product of a form that is
bilinear in two of the rows with a form that is bilinear in the other two. Laplace expansion
along rows `{0, 1}` writes the permanent as a sum of `6 = 4.choose 2` split products, all
using the same pairing of the rows `01|23`.

Mixing the three pairings `01|23`, `02|13`, `03|12` does better in the limit: for every
`lam`, `lam * permanent A` equals five split products plus `lam ^ 2` times a sixth one. So
`permanent A` minus a remainder of size `lam` is a sum of five split products, and the
remainder vanishes as `lam → 0`.
-/

namespace PvsNP

open Matrix

variable {R : Type*} [CommRing R]

/-- The symmetric form on columns `p, q`, evaluated on rows `a, b`: the `2 × 2` permanent. -/
def symPair (A : Matrix (Fin 4) (Fin 4) R) (p q a b : Fin 4) : R :=
  A a p * A b q + A a q * A b p

/-- The alternating form on columns `p, q`, evaluated on rows `a, b`: the `2 × 2` determinant. -/
def altPair (A : Matrix (Fin 4) (Fin 4) R) (p q a b : Fin 4) : R :=
  A a p * A b q - A a q * A b p

/-- The `4 × 4` permanent written out. -/
theorem permanent_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.permanent =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 + A 3 2 * A 2 3) + A 2 1 * (A 1 2 * A 3 3 + A 3 2 * A 1 3)
        + A 3 1 * (A 1 2 * A 2 3 + A 2 2 * A 1 3))
      + A 1 0 * (A 0 1 * (A 2 2 * A 3 3 + A 3 2 * A 2 3) + A 2 1 * (A 0 2 * A 3 3 + A 3 2 * A 0 3)
        + A 3 1 * (A 0 2 * A 2 3 + A 2 2 * A 0 3))
      + A 2 0 * (A 0 1 * (A 1 2 * A 3 3 + A 3 2 * A 1 3) + A 1 1 * (A 0 2 * A 3 3 + A 3 2 * A 0 3)
        + A 3 1 * (A 0 2 * A 1 3 + A 1 2 * A 0 3))
      + A 3 0 * (A 0 1 * (A 1 2 * A 2 3 + A 2 2 * A 1 3) + A 1 1 * (A 0 2 * A 2 3 + A 2 2 * A 0 3)
        + A 2 1 * (A 0 2 * A 1 3 + A 1 2 * A 0 3)) := by
  simp [permanent_succ_column_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **Five-term identity.** For every `lam`, `lam` times the `4 × 4` permanent is a sum of five
split products (two for the pairing `01|23` scaled by `lam`, one more for `01|23`, one for
`02|13`, one for `03|12`) plus `lam ^ 2` times a sixth split product. -/
theorem five_term_identity (A : Matrix (Fin 4) (Fin 4) R) (lam : R) :
    lam * A.permanent =
      lam * (symPair A 0 1 0 1 * symPair A 2 3 2 3 + symPair A 2 3 0 1 * symPair A 0 1 2 3)
      + altPair A 0 1 0 1 * altPair A 0 1 2 3
      + (symPair A 0 1 0 2 + lam * symPair A 2 3 0 2) * (symPair A 0 1 1 3 + lam * symPair A 2 3 1 3)
      - (symPair A 0 1 0 3 - lam * symPair A 2 3 0 3) * (symPair A 0 1 1 2 - lam * symPair A 2 3 1 2)
      + lam ^ 2 * (altPair A 2 3 0 1 * altPair A 2 3 2 3) := by
  rw [permanent_fin_four]
  simp only [symPair, altPair]
  ring

section Field

variable {K : Type*} [Field K]

/-- The bilinear form in rows `a` and `b` of the matrix with coefficient table `c`. -/
def rowForm (c : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) (A : Matrix (Fin 4) (Fin 4) K) : K :=
  ∑ p, ∑ q, c p q * A a p * A b q

/-- `f` is a split product for the pairing `ab|cd` of the rows: a bilinear form in rows `a, b`
times a bilinear form in rows `c, d`. -/
def IsSplit (a b c d : Fin 4) (f : Matrix (Fin 4) (Fin 4) K → K) : Prop :=
  ∃ F G : Matrix (Fin 4) (Fin 4) K, ∀ A, f A = rowForm F a b A * rowForm G c d A

/-- **Border bound.** For every nonzero `lam`, the `4 × 4` permanent minus `lam` times the
product of two `2 × 2` minors is a sum of five split products: three for the pairing
`01|23`, one for `02|13` and one for `03|12`. Laplace expansion uses six. -/
theorem permanent_sub_eq_five_split (lam : K) (hlam : lam ≠ 0) :
    ∃ t₁ t₂ t₃ t₄ t₅ : Matrix (Fin 4) (Fin 4) K → K,
      IsSplit 0 1 2 3 t₁ ∧ IsSplit 0 1 2 3 t₂ ∧ IsSplit 0 1 2 3 t₃ ∧
      IsSplit 0 2 1 3 t₄ ∧ IsSplit 0 3 1 2 t₅ ∧
      ∀ A : Matrix (Fin 4) (Fin 4) K,
        A.permanent - lam * (altPair A 2 3 0 1 * altPair A 2 3 2 3) =
          t₁ A + t₂ A + t₃ A + t₄ A + t₅ A := by
  refine ⟨fun A => symPair A 0 1 0 1 * symPair A 2 3 2 3,
    fun A => symPair A 2 3 0 1 * symPair A 0 1 2 3,
    fun A => lam⁻¹ * altPair A 0 1 0 1 * altPair A 0 1 2 3,
    fun A => lam⁻¹ * (symPair A 0 1 0 2 + lam * symPair A 2 3 0 2)
      * (symPair A 0 1 1 3 + lam * symPair A 2 3 1 3),
    fun A => -lam⁻¹ * (symPair A 0 1 0 3 - lam * symPair A 2 3 0 3)
      * (symPair A 0 1 1 2 - lam * symPair A 2 3 1 2),
    ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0], ?_⟩,
    ⟨!![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ?_⟩,
    ⟨!![0, lam⁻¹, 0, 0; -lam⁻¹, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ?_⟩,
    ⟨!![0, lam⁻¹, 0, 0; lam⁻¹, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, lam; 0, 0, lam, 0], ?_⟩,
    ⟨!![0, -lam⁻¹, 0, 0; -lam⁻¹, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -lam; 0, 0, -lam, 0], ?_⟩, ?_⟩
  · intro A
    simp [rowForm, symPair, Fin.sum_univ_four]
  · intro A
    simp [rowForm, symPair, Fin.sum_univ_four]
  · intro A
    simp [rowForm, altPair, Fin.sum_univ_four]
    ring
  · intro A
    simp [rowForm, symPair, Fin.sum_univ_four]
    field_simp
    ring
  · intro A
    simp [rowForm, symPair, Fin.sum_univ_four]
    field_simp
    ring
  · intro A
    have h := five_term_identity A lam
    simp only [symPair, altPair] at h ⊢
    field_simp
    linear_combination h

end Field

/-- The error term of `permanent_sub_eq_five_split` vanishes as `lam → 0` (continuity of a
polynomial of degree one in `lam`). See `tendsto_five_split_strong` for the statement about the
five split products themselves. -/
theorem tendsto_five_split (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Filter.Tendsto (fun lam : ℝ => A.permanent - lam * (altPair A 2 3 0 1 * altPair A 2 3 2 3))
      (nhdsWithin 0 {0}ᶜ) (nhds A.permanent) := by
  have hc : Continuous fun lam : ℝ =>
      A.permanent - lam * (altPair A 2 3 0 1 * altPair A 2 3 2 3) := by fun_prop
  have h0 := hc.tendsto 0
  simp only [zero_mul, sub_zero] at h0
  exact h0.mono_left nhdsWithin_le_nhds

/-- **The limit, as a statement about the five split products.** There is a family, indexed by `lam`, of five
split products (three for `01|23`, one for `02|13`, one for `03|12`) whose sum converges to the
permanent as `lam → 0`. -/
theorem tendsto_five_split_strong :
    ∃ t : ℝ → Fin 5 → Matrix (Fin 4) (Fin 4) ℝ → ℝ,
      (∀ lam : ℝ, lam ≠ 0 → IsSplit 0 1 2 3 (t lam 0) ∧ IsSplit 0 1 2 3 (t lam 1) ∧
        IsSplit 0 1 2 3 (t lam 2) ∧ IsSplit 0 2 1 3 (t lam 3) ∧ IsSplit 0 3 1 2 (t lam 4)) ∧
      ∀ A : Matrix (Fin 4) (Fin 4) ℝ,
        Filter.Tendsto (fun lam : ℝ => ∑ i, t lam i A) (nhdsWithin 0 {0}ᶜ) (nhds A.permanent) := by
  classical
  have h := fun (lam : ℝ) (hlam : lam ≠ 0) => permanent_sub_eq_five_split lam hlam
  choose t₁ t₂ t₃ t₄ t₅ h₁ h₂ h₃ h₄ h₅ hsum using h
  refine ⟨fun lam => if hl : lam ≠ 0 then
      ![t₁ lam hl, t₂ lam hl, t₃ lam hl, t₄ lam hl, t₅ lam hl] else fun _ _ => 0, ?_, ?_⟩
  · intro lam hl
    simp only [dite_eq_left hl]
    exact ⟨h₁ lam hl, h₂ lam hl, h₃ lam hl, h₄ lam hl, h₅ lam hl⟩
  · intro A
    refine (tendsto_five_split A).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with lam hl
    have hl' : lam ≠ 0 := hl
    simp only [dite_eq_left hl', Fin.sum_univ_five]
    rw [hsum lam hl' A]
    rfl

end PvsNP
