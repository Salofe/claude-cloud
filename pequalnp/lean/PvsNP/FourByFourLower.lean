import PvsNP.FiveTerm

/-!
# Lower bounds for mixed split decompositions of the `4 × 4` permanent

A *split product* is a bilinear form in two rows of a `4 × 4` matrix times a bilinear form in
the other two rows; the two pairs of rows form one of the three pairings `01|23`, `02|13`,
`03|12`. Laplace expansion writes the permanent with six split products of one pairing, and
`PvsNP.FiveTerm` shows that sums of *five* split products (three pairings mixed) converge to
the permanent. This file proves that this is optimal.

## Main results

* `five_le_card_of_permanent_eq_sum_split`, `permanent_ne_sum_four_isSplit`: over a field of
  characteristic zero the permanent is **not a sum of four split products**, whatever pairings
  the terms use.
* `not_tendsto_sum_split_four`, `not_tendsto_sum_four_isSplit`,
  `not_tendsto_sum_four_isSplit_complex`: over `ℝ` and over `ℂ`, the permanent is **not a
  limit of sums of four split products** (pairings and factors may vary along the sequence).
  So the border value of the mixed split rank of the `4 × 4` permanent is exactly five.
* `gamma_not_split`, `twoBlock_no_211`, `twoBlock_five_le`: the same lower bound inside the
  *two-block model* (each factor is a form on columns `{0,1}` plus a form on columns `{2,3}`;
  the weight-(2,0) part must cancel and the weight-(1,1) part must be the permanent), by a
  direct computation with `2 × 2 × 2 × 2` tensors. This is a special case of the limit
  theorem, kept because its proof is elementary and independent.

## The idea

Put the all-ones vector in row `0`. The permanent becomes
`E3 w x y = ∑_{i, j, k distinct} w i * x j * y k` in the other three rows, and every split
product becomes a *slice*: a linear form in one of `w, x, y` (the row paired with row `0`)
times a bilinear form in the other two. Hence a sum of split products with `a`, `b`, `c`
terms of the three pairings vanishes on `U₁ × U₂ × U₃` for subspaces of codimension at most
`a`, `b`, `c`: the common kernels of those linear forms. The key lemmas (`slice_211`,
`slice_220`, `slice_310`, combined in `slicePt_of_le`) say that `E3` does not vanish on such
a product when `a + b + c ≤ 4` and `a, b, c ≤ 3`. Behind them: the symmetric matrix
`B_u = E3 u · ·` has zero diagonal and entries `u_c + u_d`; it has rank `≤ 1` only for `u = 0`
and rank `≤ 2` only on ten lines (`thin_C`, `thin_KB`, `kb_one` are the versions used here,
valid over every field of characteristic zero). The remaining case, four terms of the same
pairing, is excluded by the rank of the flattening (`no_rank_four_01`, `det_sum_rank_one`).

For limits, "vanishes on a product of subspaces of given codimensions" is a closed condition
because Grassmannians are compact: `Csl`, `isClosed_Csl` (subspaces are given by orthonormal
families of covectors, `IsFrame`, produced by Gram–Schmidt, `gram_schmidt3`), and "four
terms of the same pairing" is excluded for large `n` by a `5 × 5` minor (`detJ`).
-/

namespace PvsNP

open Matrix

section TwoBlock

/-! ### The two-block model

Columns are split into the blocks `{0,1}` and `{2,3}`, and every factor of every term is a
form on the first block plus a form on the second block. Grading by the number of rows that
use the first block, the weight-(2,0) part of the sum must cancel and the weight-(1,1) part
must be the permanent (the weight-(0,2) part is free: rescaling the second block by `lam`
and dividing by `lam` turns such data into a limit decomposition). On each block the
permanent of two rows is the symmetric form `s` with coefficient table `ne2`.

A pairing with a single term contributes a nonzero multiple `c` of `s ⊗ s` to the weight-(2,0)
part (`single_term_block`), so with one term per pairing that part is
`Γ(c) = c₁ s(01)s(23) + c₂ s(02)s(13) + c₃ s(03)s(12)` with all `c_i ≠ 0`. -/

variable {K : Type*} [Field K]

/-- Coefficient table of the symmetric form `s = x₀ y₁ + x₁ y₀` on a block of two columns. -/
def ne2 (a b : Fin 2) : K := if a = b then 0 else 1

/-- `Γ(c) = c₁ s(01) s(23) + c₂ s(02) s(13) + c₃ s(03) s(12)` as a tensor in `(K²)^{⊗4}`. -/
def gammaT (c₁ c₂ c₃ : K) (a b c d : Fin 2) : K :=
  c₁ * (ne2 a b * ne2 c d) + c₂ * (ne2 a c * ne2 b d) + c₃ * (ne2 a d * ne2 b c)

/-- If `Γ(c)` is a split product for the pairing `01|23`, then `c₂ + c₃ = 0` and `c₁ c₂ = 0`:
compare coefficients (the flattening must have rank one). -/
theorem gamma_split_01 (h2 : (2 : K) ≠ 0) (c₁ c₂ c₃ : K) (F G : Fin 2 → Fin 2 → K)
    (h : ∀ a b c d, gammaT c₁ c₂ c₃ a b c d = F a b * G c d) :
    c₂ + c₃ = 0 ∧ c₁ * c₂ = 0 := by
  have e0011 := h 0 0 1 1
  have e1100 := h 1 1 0 0
  have e0000 := h 0 0 0 0
  have e1111 := h 1 1 1 1
  have e0101 := h 0 1 0 1
  have e1010 := h 1 0 1 0
  have e0110 := h 0 1 1 0
  have e1001 := h 1 0 0 1
  simp only [gammaT, ne2] at e0011 e1100 e0000 e1111 e0101 e1010 e0110 e1001
  norm_num at e0011 e1100 e0000 e1111 e0101 e1010 e0110 e1001
  have ha : (c₂ + c₃) ^ 2 = 0 := by
    have : (c₂ + c₃) ^ 2 = (F 0 0 * G 0 0) * (F 1 1 * G 1 1) := by
      linear_combination (c₂ + c₃) * e0011 + (F 0 0 * G 1 1) * e1100
    rw [this]
    rcases e0000 with h0 | h0 <;> simp [h0]
  have ha' : c₂ + c₃ = 0 := by simpa using ha
  refine ⟨ha', ?_⟩
  have hb : (c₁ + c₃) ^ 2 = (c₁ + c₂) ^ 2 := by
    linear_combination (c₁ + c₃) * e0101 + (F 0 1 * G 0 1) * e1010 - (c₁ + c₂) * e0110
      - (F 0 1 * G 1 0) * e1001
  have h4 : (2 : K) * 2 * (c₁ * c₂) = 0 := by
    have hc3 : c₃ = -c₂ := by linear_combination ha'
    rw [hc3] at hb
    linear_combination -hb
  simpa [h2] using h4

/-- The same for the pairing `02|13`. -/
theorem gamma_split_02 (h2 : (2 : K) ≠ 0) (c₁ c₂ c₃ : K) (F G : Fin 2 → Fin 2 → K)
    (h : ∀ a b c d, gammaT c₁ c₂ c₃ a b c d = F a c * G b d) :
    c₁ + c₃ = 0 ∧ c₂ * c₁ = 0 := by
  apply gamma_split_01 h2 c₂ c₁ c₃ F G
  intro a b c d
  rw [← h a c b d]
  simp only [gammaT, ne2]
  have : (if c = b then (0:K) else 1) = if b = c then 0 else 1 := by simp [eq_comm]
  rw [this]; ring

/-- The same for the pairing `03|12`. -/
theorem gamma_split_03 (h2 : (2 : K) ≠ 0) (c₁ c₂ c₃ : K) (F G : Fin 2 → Fin 2 → K)
    (h : ∀ a b c d, gammaT c₁ c₂ c₃ a b c d = F a d * G b c) :
    c₂ + c₁ = 0 ∧ c₃ * c₂ = 0 := by
  apply gamma_split_01 h2 c₃ c₂ c₁ F (fun c d => G d c)
  intro a b c d
  rw [← h a d c b]
  simp only [gammaT, ne2]
  have e1 : (if d = c then (0:K) else 1) = if c = d then 0 else 1 := by simp [eq_comm]
  have e2 : (if d = b then (0:K) else 1) = if b = d then 0 else 1 := by simp [eq_comm]
  have e3 : (if c = b then (0:K) else 1) = if b = c then 0 else 1 := by simp [eq_comm]
  rw [e1, e2, e3]; ring

/-- **No single split product cancels `Γ(c)`.** For nonzero `c₁, c₂, c₃` there is no split
product `F ⊗ G`, of any of the three pairings, with `Γ(c) + F ⊗ G = 0`. -/
theorem gamma_not_split (h2 : (2 : K) ≠ 0) (c₁ c₂ c₃ : K) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hc₃ : c₃ ≠ 0) (F G : Fin 2 → Fin 2 → K) :
    ¬ ((∀ a b c d, gammaT c₁ c₂ c₃ a b c d + F a b * G c d = 0) ∨
       (∀ a b c d, gammaT c₁ c₂ c₃ a b c d + F a c * G b d = 0) ∨
       (∀ a b c d, gammaT c₁ c₂ c₃ a b c d + F a d * G b c = 0)) := by
  rintro (h | h | h)
  · have := (gamma_split_01 h2 c₁ c₂ c₃ (fun a b => -F a b) G
      (fun a b c d => by linear_combination h a b c d)).2
    exact (mul_ne_zero hc₁ hc₂) this
  · have := (gamma_split_02 h2 c₁ c₂ c₃ (fun a b => -F a b) G
      (fun a b c d => by linear_combination h a b c d)).2
    exact (mul_ne_zero hc₂ hc₁) this
  · have := (gamma_split_03 h2 c₁ c₂ c₃ (fun a b => -F a b) G
      (fun a b c d => by linear_combination h a b c d)).2
    exact (mul_ne_zero hc₃ hc₂) this

/-- Core of the pattern (2,1,1): two terms of the pairing `01|23` cannot have weight-(1,1)
parts `s ⊗ s` (twice) and a weight-(2,0) part cancelling `c₂ s(02)s(13) + c₃ s(03)s(12)` with
`c₂, c₃ ≠ 0`. (A Gram determinant forces `c₃ = -c₂`; then Cauchy–Binet in dimension two gives
`4 c₂² = 0`.) -/
theorem twoBlock_core [CharZero K] (F1 F2 G1 G2 : Fin 2 → Fin 2 → Fin 2 → K) (c₂ c₃ : K)
    (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (h11 : ∀ a b c d, F1 0 a b * G2 0 c d + F1 1 a b * G2 1 c d = ne2 a b * ne2 c d)
    (h11' : ∀ a b c d, F2 0 a b * G1 0 c d + F2 1 a b * G1 1 c d = ne2 a b * ne2 c d)
    (h20 : ∀ a b c d, F1 0 a b * G1 0 c d + F1 1 a b * G1 1 c d
      + c₂ * (ne2 a c * ne2 b d) + c₃ * (ne2 a d * ne2 b c) = 0) : False := by
  have a1 := h20 0 0 1 1
  have a2 := h20 0 0 0 1
  have a3 := h20 0 0 0 0
  have a4 := h20 0 1 1 1
  have a5 := h20 0 1 0 1
  have a6 := h20 0 1 0 0
  have a7 := h20 1 1 1 1
  have a8 := h20 1 1 0 1
  have a9 := h20 1 1 0 0
  have b1 := h20 0 1 1 0
  have b2 := h20 1 0 0 1
  have b3 := h20 1 0 1 0
  have d1 := h11 0 1 0 1
  have d2 := h11 1 0 0 1
  have d3 := h11' 0 1 0 1
  have d4 := h11' 0 1 1 0
  simp only [ne2] at a1 a2 a3 a4 a5 a6 a7 a8 a9 b1 b2 b3 d1 d2 d3 d4
  norm_num at a1 a2 a3 a4 a5 a6 a7 a8 a9 b1 b2 b3 d1 d2 d3 d4
  grind


lemma ne2_comm (a b : Fin 2) : (ne2 a b : K) = ne2 b a := by
  simp [ne2, eq_comm]

/-- A pairing with a single term in the two-block model: the term is forced up to scalars,
and its weight-(2,0) part is a nonzero multiple of `s ⊗ s`. -/
lemma single_term_block (P Q P' Q' : Fin 2 → Fin 2 → K)
    (h : ∀ a b c d, P a b * Q' c d = ne2 a b * ne2 c d)
    (h' : ∀ a b c d, P' a b * Q c d = ne2 a b * ne2 c d) :
    P 0 1 * Q 0 1 ≠ 0 ∧ ∀ a b c d, P a b * Q c d = P 0 1 * Q 0 1 * (ne2 a b * ne2 c d) := by
  have a1 := h 0 1 0 1
  have a2 := h 0 0 0 1
  have a3 := h 1 1 0 1
  have a4 := h 1 0 0 1
  have b1 := h' 0 1 0 1
  have b2 := h' 0 1 0 0
  have b3 := h' 0 1 1 1
  have b4 := h' 0 1 1 0
  simp only [ne2] at a1 a2 a3 a4 b1 b2 b3 b4
  norm_num at a1 a2 a3 a4 b1 b2 b3 b4
  have hQ' : Q' 0 1 ≠ 0 := fun h0 => by simp [h0] at a1
  have hP' : P' 0 1 ≠ 0 := fun h0 => by simp [h0] at b1
  have hP : P 0 1 ≠ 0 := fun h0 => by simp [h0] at a1
  have hQ : Q 0 1 ≠ 0 := fun h0 => by simp [h0] at b1
  have p00 : P 0 0 = 0 := by simpa [hQ'] using a2
  have p11 : P 1 1 = 0 := by simpa [hQ'] using a3
  have p10 : P 1 0 = P 0 1 := mul_right_cancel₀ hQ' (a4.trans a1.symm)
  have q00 : Q 0 0 = 0 := by simpa [hP'] using b2
  have q11 : Q 1 1 = 0 := by simpa [hP'] using b3
  have q10 : Q 1 0 = Q 0 1 := mul_left_cancel₀ hP' (b4.trans b1.symm)
  refine ⟨mul_ne_zero hP hQ, fun a b c d => ?_⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [ne2, p00, p11, p10, q00, q11, q10]

/-- **The two-block model with pattern (2,1,1).** Two terms for the pairing `01|23`, one for
`02|13`, one for `03|12`: the weight-(1,1) part cannot be the permanent while the weight-(2,0)
part cancels. -/
theorem twoBlock_no_211 [CharZero K] (F1 F2 G1 G2 : Fin 2 → Fin 2 → Fin 2 → K)
    (P1 P2 Q1 Q2 R1 R2 S1 S2 : Fin 2 → Fin 2 → K)
    (h01 : ∀ a b c d, F1 0 a b * G2 0 c d + F1 1 a b * G2 1 c d = ne2 a b * ne2 c d)
    (h01' : ∀ a b c d, F2 0 a b * G1 0 c d + F2 1 a b * G1 1 c d = ne2 a b * ne2 c d)
    (h02 : ∀ a b c d, P1 a c * Q2 b d = ne2 a c * ne2 b d)
    (h02' : ∀ a b c d, P2 a c * Q1 b d = ne2 a c * ne2 b d)
    (h03 : ∀ a b c d, R1 a d * S2 b c = ne2 a d * ne2 b c)
    (h03' : ∀ a b c d, R2 a d * S1 b c = ne2 a d * ne2 b c)
    (h20 : ∀ a b c d, F1 0 a b * G1 0 c d + F1 1 a b * G1 1 c d + P1 a c * Q1 b d
      + R1 a d * S1 b c = 0) : False := by
  obtain ⟨hc₂, e₂⟩ := single_term_block P1 Q1 P2 Q2 (fun a b c d => h02 a c b d)
    (fun a b c d => h02' a c b d)
  obtain ⟨hc₃, e₃⟩ := single_term_block R1 S1 R2 S2 (fun a b c d => h03 a c d b)
    (fun a b c d => h03' a c d b)
  refine twoBlock_core F1 F2 G1 G2 (P1 0 1 * Q1 0 1) (R1 0 1 * S1 0 1) hc₂ hc₃ h01 h01' ?_
  intro a b c d
  have := h20 a b c d
  rw [e₂ a c b d, e₃ a d b c] at this
  exact this

/-- **The two-block model needs five terms at `4 × 4`.** With `n₁`, `n₂`, `n₃` terms of the
pairings `01|23`, `02|13`, `03|12` (tables `A1/A2`, `B1/B2`: the two blocks of the two factors
of a term of the first pairing, and so on), if the weight-(1,1) part is the permanent and the
weight-(2,0) part cancels, then `n₁ + n₂ + n₃ ≥ 5`. -/
theorem twoBlock_five_le [CharZero K] (n₁ n₂ n₃ : ℕ)
    (A1 A2 B1 B2 : Fin n₁ → Fin 2 → Fin 2 → K) (C1 C2 D1 D2 : Fin n₂ → Fin 2 → Fin 2 → K)
    (E1 E2 H1 H2 : Fin n₃ → Fin 2 → Fin 2 → K)
    (h01 : ∀ a b c d, ∑ v, A1 v a b * B2 v c d = ne2 a b * ne2 c d)
    (h01' : ∀ a b c d, ∑ v, A2 v a b * B1 v c d = ne2 a b * ne2 c d)
    (h02 : ∀ a b c d, ∑ v, C1 v a c * D2 v b d = ne2 a c * ne2 b d)
    (h02' : ∀ a b c d, ∑ v, C2 v a c * D1 v b d = ne2 a c * ne2 b d)
    (h03 : ∀ a b c d, ∑ v, E1 v a d * H2 v b c = ne2 a d * ne2 b c)
    (h03' : ∀ a b c d, ∑ v, E2 v a d * H1 v b c = ne2 a d * ne2 b c)
    (h20 : ∀ a b c d, ∑ v, A1 v a b * B1 v c d + ∑ v, C1 v a c * D1 v b d
      + ∑ v, E1 v a d * H1 v b c = 0) :
    5 ≤ n₁ + n₂ + n₃ := by
  have p1 : 1 ≤ n₁ := by
    by_contra h
    obtain rfl : n₁ = 0 := by omega
    have := h01 0 1 0 1
    simp [ne2] at this
  have p2 : 1 ≤ n₂ := by
    by_contra h
    obtain rfl : n₂ = 0 := by omega
    have := h02 0 0 1 1
    simp [ne2] at this
  have p3 : 1 ≤ n₃ := by
    by_contra h
    obtain rfl : n₃ = 0 := by omega
    have := h03 0 0 1 1
    simp [ne2] at this
  by_contra hlt
  push Not at hlt
  have hcases : (n₁ ≤ 2 ∧ n₂ = 1 ∧ n₃ = 1) ∨ (n₁ = 1 ∧ n₂ = 2 ∧ n₃ = 1) ∨
      (n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 2) := by omega
  rcases hcases with ⟨h1, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · interval_cases n₁
    · -- (1,1,1): pad the pairing 01 with a zero term
      refine twoBlock_no_211 ![A1 0, 0] ![A2 0, 0] ![B1 0, 0] ![B2 0, 0]
        (C1 0) (C2 0) (D1 0) (D2 0) (E1 0) (E2 0) (H1 0) (H2 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro a b c d; simpa using h01 a b c d
      · intro a b c d; simpa using h01' a b c d
      · intro a b c d; simpa using h02 a b c d
      · intro a b c d; simpa using h02' a b c d
      · intro a b c d; simpa using h03 a b c d
      · intro a b c d; simpa using h03' a b c d
      · intro a b c d; simpa using h20 a b c d
    · refine twoBlock_no_211 A1 A2 B1 B2
        (C1 0) (C2 0) (D1 0) (D2 0) (E1 0) (E2 0) (H1 0) (H2 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro a b c d; simpa [Fin.sum_univ_two] using h01 a b c d
      · intro a b c d; simpa [Fin.sum_univ_two] using h01' a b c d
      · intro a b c d; simpa using h02 a b c d
      · intro a b c d; simpa using h02' a b c d
      · intro a b c d; simpa using h03 a b c d
      · intro a b c d; simpa using h03' a b c d
      · intro a b c d; simpa [Fin.sum_univ_two] using h20 a b c d
  · -- (1,2,1): exchange the roles of rows 1 and 2
    refine twoBlock_no_211 C1 C2 D1 D2 (A1 0) (A2 0) (B1 0) (B2 0)
      (E1 0) (E2 0) (fun b c => H1 0 c b) (fun b c => H2 0 c b) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro a b c d; simpa [Fin.sum_univ_two] using h02 a c b d
    · intro a b c d; simpa [Fin.sum_univ_two] using h02' a c b d
    · intro a b c d; simpa using h01 a c b d
    · intro a b c d; simpa using h01' a c b d
    · intro a b c d; rw [ne2_comm b c]; simpa using h03 a c b d
    · intro a b c d; rw [ne2_comm b c]; simpa using h03' a c b d
    · intro a b c d
      have := h20 a c b d
      simp [Fin.sum_univ_two] at this ⊢
      linear_combination this
  · -- (1,1,2): exchange the roles of rows 1 and 3
    refine twoBlock_no_211 E1 E2 (fun v c d => H1 v d c) (fun v c d => H2 v d c)
      (C1 0) (C2 0) (fun b d => D1 0 d b) (fun b d => D2 0 d b)
      (A1 0) (A2 0) (fun b c => B1 0 c b) (fun b c => B2 0 c b) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro a b c d; rw [ne2_comm c d]; simpa [Fin.sum_univ_two] using h03 a d c b
    · intro a b c d; rw [ne2_comm c d]; simpa [Fin.sum_univ_two] using h03' a d c b
    · intro a b c d; rw [ne2_comm b d]; simpa using h02 a d c b
    · intro a b c d; rw [ne2_comm b d]; simpa using h02' a d c b
    · intro a b c d; rw [ne2_comm b c]; simpa using h01 a d c b
    · intro a b c d; rw [ne2_comm b c]; simpa using h01' a d c b
    · intro a b c d
      have := h20 a d c b
      simp [Fin.sum_univ_two] at this ⊢
      linear_combination this

end TwoBlock

section Slice

variable {K : Type*} [Field K]

set_option linter.unusedSectionVars false

/-- `E3 u x y = ∑ u i * x j * y k` over triples of distinct column indices. -/
def E3 (u x y : Fin 4 → K) : K :=
  ∑ i, ∑ j, ∑ k, if i ≠ j ∧ i ≠ k ∧ j ≠ k then u i * x j * y k else 0

lemma E3_comp (σ : Equiv.Perm (Fin 4)) (u x y : Fin 4 → K) :
    E3 (u ∘ σ) (x ∘ σ) (y ∘ σ) = E3 u x y := by
  simp only [E3, Function.comp]
  refine Fintype.sum_equiv σ _ _ fun i => ?_
  refine Fintype.sum_equiv σ _ _ fun j => ?_
  refine Fintype.sum_equiv σ _ _ fun k => ?_
  simp [σ.injective.ne_iff]

lemma E3_eq (u x y : Fin 4 → K) :
    E3 u x y = (u 2 + u 3) * (x 0 * y 1 + x 1 * y 0) + (u 1 + u 3) * (x 0 * y 2 + x 2 * y 0)
      + (u 1 + u 2) * (x 0 * y 3 + x 3 * y 0) + (u 0 + u 3) * (x 1 * y 2 + x 2 * y 1)
      + (u 0 + u 2) * (x 1 * y 3 + x 3 * y 1) + (u 0 + u 1) * (x 2 * y 3 + x 3 * y 2) := by
  simp [E3, Fin.sum_univ_four]
  ring

lemma E3_swap12 (u x y : Fin 4 → K) : E3 x u y = E3 u x y := by
  simp only [E3_eq]; ring

lemma E3_swap23 (u x y : Fin 4 → K) : E3 u y x = E3 u x y := by
  simp only [E3_eq]; ring

/-- The vector with the four given coordinates. -/
def vec4 (a b c d : K) : Fin 4 → K := ![a, b, c, d]

@[simp] lemma vec4_zero (a b c d : K) : vec4 a b c d 0 = a := rfl
@[simp] lemma vec4_one (a b c d : K) : vec4 a b c d 1 = b := rfl
@[simp] lemma vec4_two (a b c d : K) : vec4 a b c d 2 = c := rfl
@[simp] lemma vec4_three (a b c d : K) : vec4 a b c d 3 = d := rfl

/-- The pairing of a covector with a vector. -/
def dot4 (f x : Fin 4 → K) : K := ∑ i, f i * x i

lemma dot4_eq (f x : Fin 4 → K) : dot4 f x = f 0 * x 0 + f 1 * x 1 + f 2 * x 2 + f 3 * x 3 := by
  simp [dot4, Fin.sum_univ_four]

lemma dot4_comp (σ : Equiv.Perm (Fin 4)) (f x : Fin 4 → K) :
    dot4 (f ∘ σ) (x ∘ σ) = dot4 f x :=
  Fintype.sum_equiv σ _ _ fun _ => rfl

@[simp] lemma dot4_zero_left (x : Fin 4 → K) : dot4 0 x = 0 := by simp [dot4]

/-- `u ↦ E3 u · ·` vanishes on `(ker φ₁ ∩ ker φ₂) × ker ψ`. -/
def Vanish3 (φ₁ φ₂ ψ u : Fin 4 → K) : Prop :=
  ∀ x y : Fin 4 → K, dot4 φ₁ x = 0 → dot4 φ₂ x = 0 → dot4 ψ y = 0 → E3 u x y = 0

lemma Vanish3.scalar {φ₁ φ₂ ψ u : Fin 4 → K} (h : Vanish3 φ₁ φ₂ ψ u)
    (x0 x1 x2 x3 y0 y1 y2 y3 : K)
    (hx : φ₁ 0 * x0 + φ₁ 1 * x1 + φ₁ 2 * x2 + φ₁ 3 * x3 = 0)
    (hx' : φ₂ 0 * x0 + φ₂ 1 * x1 + φ₂ 2 * x2 + φ₂ 3 * x3 = 0)
    (hy : ψ 0 * y0 + ψ 1 * y1 + ψ 2 * y2 + ψ 3 * y3 = 0) :
    (u 2 + u 3) * (x0 * y1 + x1 * y0) + (u 1 + u 3) * (x0 * y2 + x2 * y0)
      + (u 1 + u 2) * (x0 * y3 + x3 * y0) + (u 0 + u 3) * (x1 * y2 + x2 * y1)
      + (u 0 + u 2) * (x1 * y3 + x3 * y1) + (u 0 + u 1) * (x2 * y3 + x3 * y2) = 0 := by
  have := h (vec4 x0 x1 x2 x3) (vec4 y0 y1 y2 y3) (by simpa [dot4_eq] using hx)
    (by simpa [dot4_eq] using hx') (by simpa [dot4_eq] using hy)
  rw [E3_eq] at this
  simpa using this

lemma Vanish3.relabel {φ₁ φ₂ ψ u : Fin 4 → K} (σ : Equiv.Perm (Fin 4))
    (h : Vanish3 φ₁ φ₂ ψ u) : Vanish3 (φ₁ ∘ σ) (φ₂ ∘ σ) (ψ ∘ σ) (u ∘ σ) := by
  intro x y hx hx' hy
  have e : ∀ z : Fin 4 → K, (z ∘ σ.symm) ∘ σ = z := fun z => by
    funext i; simp
  have := h (x ∘ σ.symm) (y ∘ σ.symm)
    (by rw [← dot4_comp σ, e]; exact hx) (by rw [← dot4_comp σ, e]; exact hx')
    (by rw [← dot4_comp σ, e]; exact hy)
  rw [← E3_comp σ, e, e] at this
  exact this

lemma eq_zero_of_comp_perm {u : Fin 4 → K} (σ : Equiv.Perm (Fin 4)) (h : u ∘ σ = 0) : u = 0 := by
  funext i
  have := congrFun h (σ.symm i)
  simpa using this

/-- `Thin3 φ₁ φ₂ ψ`: the space of `u` with `Vanish3 φ₁ φ₂ ψ u` meets some hyperplane only in `0`
(so it has dimension at most one). -/
def Thin3 (φ₁ φ₂ ψ : Fin 4 → K) : Prop :=
  ∃ h : Fin 4 → K, ∀ u : Fin 4 → K, dot4 h u = 0 → Vanish3 φ₁ φ₂ ψ u → u = 0

lemma Thin3.relabel {φ₁ φ₂ ψ : Fin 4 → K} (σ : Equiv.Perm (Fin 4))
    (h : Thin3 (φ₁ ∘ σ) (φ₂ ∘ σ) (ψ ∘ σ)) : Thin3 φ₁ φ₂ ψ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g ∘ σ.symm, fun u hu hV => eq_zero_of_comp_perm σ (hg (u ∘ σ) ?_ (hV.relabel σ))⟩
  have e : (g ∘ σ.symm) ∘ σ = g := by funext i; simp
  rw [← dot4_comp σ, e] at hu
  exact hu

lemma eq_zero_of_coords {u : Fin 4 → K} (h : u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0 ∧ u 3 = 0) : u = 0 := by
  funext i
  fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

lemma exists_perm_01 (p q : Fin 4) (hne : p ≠ q) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = p ∧ σ 1 = q := by
  refine ⟨Equiv.swap 0 p * Equiv.swap 1 (Equiv.swap 0 p q), ?_, ?_⟩
  · fin_cases p <;> fin_cases q <;> first | exact absurd rfl hne | decide
  · fin_cases p <;> fin_cases q <;> first | exact absurd rfl hne | decide

lemma Vanish3.mono {φ₁ φ₂ ψ φ₁' φ₂' ψ' u : Fin 4 → K} (h : Vanish3 φ₁ φ₂ ψ u)
    (h1 : ∀ x, dot4 φ₁' x = 0 → dot4 φ₂' x = 0 → dot4 φ₁ x = 0 ∧ dot4 φ₂ x = 0)
    (h2 : ∀ y, dot4 ψ' y = 0 → dot4 ψ y = 0) : Vanish3 φ₁' φ₂' ψ' u :=
  fun x y hx hx' hy => h x y (h1 x hx hx').1 (h1 x hx hx').2 (h2 y hy)

/-- Three linear equations in four unknowns have a nonzero solution. -/
lemma exists_common_zero (f g h : Fin 4 → K) :
    ∃ u : Fin 4 → K, u ≠ 0 ∧ dot4 f u = 0 ∧ dot4 g u = 0 ∧ dot4 h u = 0 := by
  let M : Matrix (Fin 4) (Fin 4) K := Matrix.of ![f, g, h, 0]
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 3 (fun j => by simp [M])
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · have := congrFun hMv 0
    simpa [M, Matrix.mulVec, dotProduct, dot4] using this
  · have := congrFun hMv 1
    simpa [M, Matrix.mulVec, dotProduct, dot4] using this
  · have := congrFun hMv 2
    simpa [M, Matrix.mulVec, dotProduct, dot4] using this

variable [CharZero K]

/-- Case A1. -/
lemma kc_A1 (φ ψ : Fin 4 → K) (h0 : φ 0 ≠ 0) (h0' : ψ 0 ≠ 0)
    (hd : φ 1 * ψ 0 - ψ 1 * φ 0 ≠ 0) (u : Fin 4 → K) (hu : u 2 + u 3 = 0)
    (hV : Vanish3 φ φ ψ u) : u = 0 := by
  have E12 := hV.scalar (-φ 1) (φ 0) 0 0 (-ψ 2) 0 (ψ 0) 0 (by ring) (by ring) (by ring)
  have E21 := hV.scalar (-φ 2) 0 (φ 0) 0 (-ψ 1) (ψ 0) 0 0 (by ring) (by ring) (by ring)
  have E13 := hV.scalar (-φ 1) (φ 0) 0 0 (-ψ 3) 0 0 (ψ 0) (by ring) (by ring) (by ring)
  have E31 := hV.scalar (-φ 3) 0 0 (φ 0) (-ψ 1) (ψ 0) 0 0 (by ring) (by ring) (by ring)
  have E23 := hV.scalar (-φ 2) 0 (φ 0) 0 (-ψ 3) 0 0 (ψ 0) (by ring) (by ring) (by ring)
  exact eq_zero_of_coords (by grind)

lemma kc_A2_norm (a1 a2 a3 u0 u1 u2 u3 : K)
    (h1 : a1 * (u2 + u3) = 0) (h2 : a2 * (u1 + u3) = 0) (h3 : a3 * (u1 + u2) = 0)
    (e12 : u0 + u3 = a2 * (u2 + u3) + a1 * (u1 + u3))
    (e13 : u0 + u2 = a3 * (u2 + u3) + a1 * (u1 + u2))
    (e23 : u0 + u1 = a3 * (u1 + u3) + a2 * (u1 + u2))
    (hh : u0 + a2 * u1 + a3 * u2 + a1 * u3 = 0) : u0 = 0 ∧ u1 = 0 ∧ u2 = 0 ∧ u3 = 0 := by
  grind

/-- Case A2. -/
lemma kc_A2 (φ ψ : Fin 4 → K) (h0 : φ 0 ≠ 0) (h0' : ψ 0 ≠ 0)
    (hd1 : φ 1 * ψ 0 = ψ 1 * φ 0) (hd2 : φ 2 * ψ 0 = ψ 2 * φ 0) (hd3 : φ 3 * ψ 0 = ψ 3 * φ 0)
    (u : Fin 4 → K) (hu : φ 0 * u 0 + φ 2 * u 1 + φ 3 * u 2 + φ 1 * u 3 = 0)
    (hV : Vanish3 φ φ ψ u) : u = 0 := by
  have E11 := hV.scalar (-φ 1) (φ 0) 0 0 (-ψ 1) (ψ 0) 0 0 (by ring) (by ring) (by ring)
  have E22 := hV.scalar (-φ 2) 0 (φ 0) 0 (-ψ 2) 0 (ψ 0) 0 (by ring) (by ring) (by ring)
  have E33 := hV.scalar (-φ 3) 0 0 (φ 0) (-ψ 3) 0 0 (ψ 0) (by ring) (by ring) (by ring)
  have E12 := hV.scalar (-φ 1) (φ 0) 0 0 (-ψ 2) 0 (ψ 0) 0 (by ring) (by ring) (by ring)
  have E13 := hV.scalar (-φ 1) (φ 0) 0 0 (-ψ 3) 0 0 (ψ 0) (by ring) (by ring) (by ring)
  have E23 := hV.scalar (-φ 2) 0 (φ 0) 0 (-ψ 3) 0 0 (ψ 0) (by ring) (by ring) (by ring)
  have t1 : φ 1 * (u 2 + u 3) = 0 := by
    have : ψ 0 * (φ 1 * (u 2 + u 3)) = 0 := by
      linear_combination (-1 / 2 : K) * E11 + (1 / 2 : K) * (u 2 + u 3) * hd1
    exact (mul_eq_zero.mp this).resolve_left h0'
  have t2 : φ 2 * (u 1 + u 3) = 0 := by
    have : ψ 0 * (φ 2 * (u 1 + u 3)) = 0 := by
      linear_combination (-1 / 2 : K) * E22 + (1 / 2 : K) * (u 1 + u 3) * hd2
    exact (mul_eq_zero.mp this).resolve_left h0'
  have t3 : φ 3 * (u 1 + u 2) = 0 := by
    have : ψ 0 * (φ 3 * (u 1 + u 2)) = 0 := by
      linear_combination (-1 / 2 : K) * E33 + (1 / 2 : K) * (u 1 + u 2) * hd3
    exact (mul_eq_zero.mp this).resolve_left h0'
  have e12 : φ 0 * (u 0 + u 3) - φ 2 * (u 2 + u 3) - φ 1 * (u 1 + u 3) = 0 := by
    have : ψ 0 * (φ 0 * (u 0 + u 3) - φ 2 * (u 2 + u 3) - φ 1 * (u 1 + u 3)) = 0 := by
      linear_combination E12 - (u 2 + u 3) * hd2
    exact (mul_eq_zero.mp this).resolve_left h0'
  have e13 : φ 0 * (u 0 + u 2) - φ 3 * (u 2 + u 3) - φ 1 * (u 1 + u 2) = 0 := by
    have : ψ 0 * (φ 0 * (u 0 + u 2) - φ 3 * (u 2 + u 3) - φ 1 * (u 1 + u 2)) = 0 := by
      linear_combination E13 - (u 2 + u 3) * hd3
    exact (mul_eq_zero.mp this).resolve_left h0'
  have e23 : φ 0 * (u 0 + u 1) - φ 3 * (u 1 + u 3) - φ 2 * (u 1 + u 2) = 0 := by
    have : ψ 0 * (φ 0 * (u 0 + u 1) - φ 3 * (u 1 + u 3) - φ 2 * (u 1 + u 2)) = 0 := by
      linear_combination E23 - (u 1 + u 3) * hd3
    exact (mul_eq_zero.mp this).resolve_left h0'
  exact eq_zero_of_coords
    (kc_A2_norm (φ 1 / φ 0) (φ 2 / φ 0) (φ 3 / φ 0) (u 0) (u 1) (u 2) (u 3)
    (by rw [div_mul_eq_mul_div, t1, zero_div]) (by rw [div_mul_eq_mul_div, t2, zero_div])
    (by rw [div_mul_eq_mul_div, t3, zero_div])
    (by field_simp; linear_combination e12) (by field_simp; linear_combination e13)
    (by field_simp; linear_combination e23) (by field_simp; linear_combination hu))

/-- Case B. -/
lemma kc_B (φ ψ : Fin 4 → K) (h0 : φ 0 ≠ 0) (h1 : ψ 1 ≠ 0) (h01 : φ 1 = 0) (h10 : ψ 0 = 0)
    (u : Fin 4 → K) (hV : Vanish3 φ φ ψ u) : u = 0 := by
  have e1 := hV.scalar 0 1 0 0 1 0 0 0 (by rw [h01]; ring) (by rw [h01]; ring) (by rw [h10]; ring)
  have e2 := hV.scalar 0 1 0 0 0 (-ψ 2) (ψ 1) 0 (by rw [h01]; ring) (by rw [h01]; ring) (by ring)
  have e3 := hV.scalar 0 1 0 0 0 (-ψ 3) 0 (ψ 1) (by rw [h01]; ring) (by rw [h01]; ring) (by ring)
  have e4 := hV.scalar (-φ 2) 0 (φ 0) 0 1 0 0 0 (by ring) (by ring) (by rw [h10]; ring)
  have e5 := hV.scalar (-φ 3) 0 0 (φ 0) 1 0 0 0 (by ring) (by ring) (by rw [h10]; ring)
  have e6 := hV.scalar (-φ 2) 0 (φ 0) 0 0 (-ψ 3) 0 (ψ 1) (by ring) (by ring) (by ring)
  exact eq_zero_of_coords (by grind)

/-- Supports of `φ` and `ψ` meet. -/
lemma thin_A (φ ψ : Fin 4 → K) (h0 : φ 0 ≠ 0) (h0' : ψ 0 ≠ 0) : Thin3 φ φ ψ := by
  by_cases hd : φ 1 * ψ 0 = ψ 1 * φ 0 ∧ φ 2 * ψ 0 = ψ 2 * φ 0 ∧ φ 3 * ψ 0 = ψ 3 * φ 0
  · exact ⟨vec4 (φ 0) (φ 2) (φ 3) (φ 1), fun u hu hV =>
      kc_A2 φ ψ h0 h0' hd.1 hd.2.1 hd.2.2 u (by simpa [dot4_eq] using hu) hV⟩
  · have : ∃ i : Fin 4, i ≠ 0 ∧ φ i * ψ 0 - ψ i * φ 0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hd ⟨sub_eq_zero.mp (hcon 1 (by decide)), sub_eq_zero.mp (hcon 2 (by decide)),
        sub_eq_zero.mp (hcon 3 (by decide))⟩
    obtain ⟨i, hi0, hi⟩ := this
    apply Thin3.relabel (Equiv.swap 1 i)
    have e0 : Equiv.swap 1 i 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hi0)
    refine ⟨vec4 0 0 1 1, fun u hu hV => kc_A1 _ _ ?_ ?_ ?_ u (by simpa [dot4_eq] using hu) hV⟩
    · simpa [e0] using h0
    · simpa [e0] using h0'
    · simpa [e0] using hi

/-- Supports of `φ` and `ψ` are disjoint. -/
lemma thin_B (φ ψ : Fin 4 → K) (p q : Fin 4) (hp : φ p ≠ 0) (hq : ψ q ≠ 0) (hpq : φ q = 0)
    (hqp : ψ p = 0) : Thin3 φ φ ψ := by
  have hne : p ≠ q := fun h => hp (h ▸ hpq)
  obtain ⟨σ, h0, h1⟩ := exists_perm_01 p q hne
  apply Thin3.relabel σ
  exact ⟨0, fun u _ hV => kc_B _ _ (by simpa [h0] using hp) (by simpa [h1] using hq)
    (by simpa [h1] using hpq) (by simpa [h0] using hqp) u hV⟩

lemma thin_ne (φ ψ : Fin 4 → K) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) : Thin3 φ φ ψ := by
  by_cases h : ∃ p, φ p ≠ 0 ∧ ψ p ≠ 0
  · obtain ⟨p, hp, hp'⟩ := h
    apply Thin3.relabel (Equiv.swap 0 p)
    exact thin_A _ _ (by simpa using hp) (by simpa using hp')
  · push Not at h
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hφ
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hψ
    exact thin_B φ ψ p q hp hq (by by_contra hc; exact hq (h q hc)) (h p hp)

/-- **Key lemma for the shape (2,1,1).** For all covectors `φ, ψ`, the space of `u` such that
`E3 u · ·` vanishes on `ker φ × ker ψ` has dimension at most one. -/
theorem thin_C (φ ψ : Fin 4 → K) : Thin3 φ φ ψ := by
  have key : ∀ θ : Fin 4 → K, ∃ θ' : Fin 4 → K, θ' ≠ 0 ∧ ∀ x, dot4 θ' x = 0 → dot4 θ x = 0 := by
    intro θ
    by_cases hθ : θ = 0
    · refine ⟨Pi.single 0 1, ?_, fun x _ => by simp [hθ]⟩
      intro h
      have := congrFun h 0
      simp at this
    · exact ⟨θ, hθ, fun x hx => hx⟩
  obtain ⟨φ', hφ', h1⟩ := key φ
  obtain ⟨ψ', hψ', h2⟩ := key ψ
  obtain ⟨h, hh⟩ := thin_ne φ' ψ' hφ' hψ'
  exact ⟨h, fun u hu hV => hh u hu (hV.mono (fun x hx _ => ⟨h1 x hx, h1 x hx⟩) h2)⟩

/-! ### Shapes (2,2,0) and (3,1,0) -/

lemma kb_one0 (φ : Fin 4 → K) (h0 : φ 0 ≠ 0) (u : Fin 4 → K) (hV : Vanish3 φ φ 0 u) : u = 0 := by
  have e1 := hV.scalar (-φ 1) (φ 0) 0 0 1 0 0 0 (by ring) (by ring) (by simp)
  have e2 := hV.scalar (-φ 2) 0 (φ 0) 0 1 0 0 0 (by ring) (by ring) (by simp)
  have e3 := hV.scalar (-φ 3) 0 0 (φ 0) 1 0 0 0 (by ring) (by ring) (by simp)
  have e4 := hV.scalar (-φ 1) (φ 0) 0 0 0 0 1 0 (by ring) (by ring) (by simp)
  have e5 := hV.scalar (-φ 1) (φ 0) 0 0 0 0 0 1 (by ring) (by ring) (by simp)
  have e6 := hV.scalar (-φ 2) 0 (φ 0) 0 0 0 0 1 (by ring) (by ring) (by simp)
  exact eq_zero_of_coords (by grind)

/-- **Key lemma for the shape (3,1,0).** If `E3 u · ·` vanishes on `ker φ × K⁴` then `u = 0`. -/
lemma kb_one (φ : Fin 4 → K) (u : Fin 4 → K) (hV : Vanish3 φ φ 0 u) : u = 0 := by
  by_cases hφ : φ = 0
  · subst hφ
    have e1 := hV.scalar 1 0 0 0 0 1 0 0 (by simp) (by simp) (by simp)
    have e2 := hV.scalar 1 0 0 0 0 0 1 0 (by simp) (by simp) (by simp)
    have e3 := hV.scalar 1 0 0 0 0 0 0 1 (by simp) (by simp) (by simp)
    have e4 := hV.scalar 0 1 0 0 0 0 1 0 (by simp) (by simp) (by simp)
    have e5 := hV.scalar 0 1 0 0 0 0 0 1 (by simp) (by simp) (by simp)
    have e6 := hV.scalar 0 0 1 0 0 0 0 1 (by simp) (by simp) (by simp)
    exact eq_zero_of_coords (by grind)
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp hφ
    have := hV.relabel (Equiv.swap 0 p)
    exact eq_zero_of_comp_perm (Equiv.swap 0 p) (kb_one0 _ (by simpa using hp) _ this)

lemma kb_zero (φ₁ φ₂ : Fin 4 → K) (hω : ∀ i j, φ₁ i * φ₂ j = φ₁ j * φ₂ i) (u : Fin 4 → K)
    (hV : Vanish3 φ₁ φ₂ 0 u) : u = 0 := by
  by_cases h1 : φ₁ = 0
  · refine kb_one φ₂ u (hV.mono (fun x hx _ => ⟨by simp [h1], hx⟩) (fun y hy => hy))
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp h1
    refine kb_one φ₁ u (hV.mono (fun x hx _ => ⟨hx, ?_⟩) (fun y hy => hy))
    have : φ₁ p * dot4 φ₂ x = φ₂ p * dot4 φ₁ x := by
      simp only [dot4, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      linear_combination x i * hω p i
    rw [hx, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hp

lemma kb_base (φ₁ φ₂ : Fin 4 → K) (hω : φ₁ 0 * φ₂ 1 - φ₁ 1 * φ₂ 0 ≠ 0) (u : Fin 4 → K)
    (hu : u 2 + u 3 = 0) (hV : Vanish3 φ₁ φ₂ 0 u) : u = 0 := by
  have hx2 := hV.scalar (φ₁ 1 * φ₂ 2 - φ₁ 2 * φ₂ 1) (-(φ₁ 0 * φ₂ 2 - φ₁ 2 * φ₂ 0))
    (φ₁ 0 * φ₂ 1 - φ₁ 1 * φ₂ 0) 0
  have hx3 := hV.scalar (φ₁ 1 * φ₂ 3 - φ₁ 3 * φ₂ 1) (-(φ₁ 0 * φ₂ 3 - φ₁ 3 * φ₂ 0)) 0
    (φ₁ 0 * φ₂ 1 - φ₁ 1 * φ₂ 0)
  have a0 := hx2 1 0 0 0 (by ring) (by ring) (by simp)
  have a1 := hx2 0 1 0 0 (by ring) (by ring) (by simp)
  have a2 := hx2 0 0 1 0 (by ring) (by ring) (by simp)
  have a3 := hx2 0 0 0 1 (by ring) (by ring) (by simp)
  have b0 := hx3 1 0 0 0 (by ring) (by ring) (by simp)
  have b1 := hx3 0 1 0 0 (by ring) (by ring) (by simp)
  have b2 := hx3 0 0 1 0 (by ring) (by ring) (by simp)
  have b3 := hx3 0 0 0 1 (by ring) (by ring) (by simp)
  clear hx2 hx3 hV
  generalize φ₁ 0 * φ₂ 1 - φ₁ 1 * φ₂ 0 = w01 at *
  generalize φ₁ 0 * φ₂ 2 - φ₁ 2 * φ₂ 0 = w02 at *
  generalize φ₁ 1 * φ₂ 2 - φ₁ 2 * φ₂ 1 = w12 at *
  generalize φ₁ 0 * φ₂ 3 - φ₁ 3 * φ₂ 0 = w03 at *
  generalize φ₁ 1 * φ₂ 3 - φ₁ 3 * φ₂ 1 = w13 at *
  exact eq_zero_of_coords (by grind)

/-- **Key lemma for the shape (2,2,0).** For all covectors `φ₁, φ₂`, the space of `u` such that
`E3 u · ·` vanishes on `(ker φ₁ ∩ ker φ₂) × K⁴` has dimension at most one. -/
theorem thin_KB (φ₁ φ₂ : Fin 4 → K) : Thin3 φ₁ φ₂ 0 := by
  by_cases hω : ∀ i j, φ₁ i * φ₂ j = φ₁ j * φ₂ i
  · exact ⟨0, fun u _ hV => kb_zero φ₁ φ₂ hω u hV⟩
  · push Not at hω
    obtain ⟨p, q, hpq⟩ := hω
    have hne : p ≠ q := fun h => hpq (by rw [h])
    obtain ⟨σ, h0, h1⟩ := exists_perm_01 p q hne
    apply Thin3.relabel σ
    refine ⟨vec4 0 0 1 1, fun u hu hV => kb_base _ _ ?_ u (by simpa [dot4_eq] using hu) hV⟩
    simpa [h0, h1, sub_eq_zero] using hpq

/-! ### Points where `E3` does not vanish -/

theorem slice_211 (f₁ f₂ φ ψ : Fin 4 → K) :
    ∃ w x y : Fin 4 → K, dot4 f₁ w = 0 ∧ dot4 f₂ w = 0 ∧ dot4 φ x = 0 ∧ dot4 ψ y = 0 ∧
      E3 w x y ≠ 0 := by
  obtain ⟨h, hh⟩ := thin_C φ ψ
  obtain ⟨w, hw, h1, h2, h3⟩ := exists_common_zero f₁ f₂ h
  by_contra hcon
  push Not at hcon
  exact hw (hh w h3 fun x y hx _ hy => hcon w x y h1 h2 hx hy)

theorem slice_220 (f₁ f₂ φ₁ φ₂ : Fin 4 → K) :
    ∃ w x y : Fin 4 → K, dot4 f₁ w = 0 ∧ dot4 f₂ w = 0 ∧ dot4 φ₁ x = 0 ∧ dot4 φ₂ x = 0 ∧
      E3 w x y ≠ 0 := by
  obtain ⟨h, hh⟩ := thin_KB φ₁ φ₂
  obtain ⟨w, hw, h1, h2, h3⟩ := exists_common_zero f₁ f₂ h
  by_contra hcon
  push Not at hcon
  exact hw (hh w h3 fun x y hx hx' _ => hcon w x y h1 h2 hx hx')

theorem slice_310 (f₁ f₂ f₃ φ : Fin 4 → K) :
    ∃ w x y : Fin 4 → K, dot4 f₁ w = 0 ∧ dot4 f₂ w = 0 ∧ dot4 f₃ w = 0 ∧ dot4 φ x = 0 ∧
      E3 w x y ≠ 0 := by
  obtain ⟨w, hw, h1, h2, h3⟩ := exists_common_zero f₁ f₂ f₃
  by_contra hcon
  push Not at hcon
  exact hw (kb_one φ w fun x y hx _ _ => hcon w x y h1 h2 h3 hx)

end Slice

section Rank

variable {K : Type*} [Field K]


lemma rowForm_transpose (G : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4)
    (A : Matrix (Fin 4) (Fin 4) K) : rowForm Gᵀ a b A = rowForm G b a A := by
  simp only [rowForm, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The matrix whose rows are the standard basis vectors `e_{j 0}, …, e_{j 3}`. -/
def selMat (j : Fin 4 → Fin 4) : Matrix (Fin 4) (Fin 4) K :=
  fun i p => if p = j i then 1 else 0

lemma rowForm_selMat (F : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) (j : Fin 4 → Fin 4) :
    rowForm F a b (selMat j) = F (j a) (j b) := by
  simp [rowForm, selMat]

/-- Four split products of the same pairing `01|23` cannot add up to the permanent: the
flattening has rank six. -/
theorem no_rank_four_01 (n : ℕ) (hn : n ≤ 4) (F G : Fin n → Matrix (Fin 4) (Fin 4) K)
    (h : ∀ A : Matrix (Fin 4) (Fin 4) K,
      A.permanent = ∑ v, rowForm (F v) 0 1 A * rowForm (G v) 2 3 A) : False := by
  let a : Fin 5 → Fin 4 := ![0, 0, 0, 1, 1]
  let b : Fin 5 → Fin 4 := ![1, 2, 3, 2, 3]
  let c : Fin 5 → Fin 4 := ![2, 1, 1, 0, 0]
  let d : Fin 5 → Fin 4 := ![3, 3, 2, 3, 2]
  have hperm : ∀ k k' : Fin 5, (selMat ![a k, b k, c k', d k'] : Matrix (Fin 4) (Fin 4) K).permanent
      = if k = k' then 1 else 0 := by
    intro k k'
    fin_cases k <;> fin_cases k' <;> simp [a, b, c, d, permanent_fin_four, selMat]
  let M : Matrix (Fin 5) (Fin 5) K := fun i k => if hi : (i : ℕ) < n then F ⟨i, hi⟩ (a k) (b k) else 0
  have h4 : ¬ ((4 : Fin 5) : ℕ) < n := by
    have : ((4 : Fin 5) : ℕ) = 4 := rfl
    omega
  have hdet : M.det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero 4
    intro k
    simp only [M, h4, ↓reduceDIte]
  obtain ⟨lam, hlam, hM⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hv : ∀ v : Fin n, ∑ k, F v (a k) (b k) * lam k = 0 := by
    intro v
    have := congrFun hM ⟨v, by omega⟩
    simpa [M, Matrix.mulVec, dotProduct, v.isLt] using this
  apply hlam
  funext k'
  have e1 : lam k' = ∑ k, lam k * (selMat ![a k, b k, c k', d k'] : Matrix (Fin 4) (Fin 4) K).permanent := by
    simp [hperm]
  rw [e1]
  simp only [h, rowForm_selMat]
  have e2 : ∀ k : Fin 5, lam k * ∑ v : Fin n, F v (![a k, b k, c k', d k'] 0) (![a k, b k, c k', d k'] 1)
      * G v (![a k, b k, c k', d k'] 2) (![a k, b k, c k', d k'] 3)
      = ∑ v : Fin n, G v (c k') (d k') * (F v (a k) (b k) * lam k) := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp
    ring
  simp only [e2]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hv, mul_zero, Finset.sum_const_zero, Pi.zero_apply]

theorem no_rank_four_02 (n : ℕ) (hn : n ≤ 4) (F G : Fin n → Matrix (Fin 4) (Fin 4) K)
    (h : ∀ A : Matrix (Fin 4) (Fin 4) K,
      A.permanent = ∑ v, rowForm (F v) 0 2 A * rowForm (G v) 1 3 A) : False := by
  apply no_rank_four_01 n hn F G
  intro A
  have := h (A.submatrix (Equiv.swap 1 2) id)
  rw [Matrix.permanent_permute_cols] at this
  have e0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have e3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  simpa [rowForm, e0, e3] using this

theorem no_rank_four_03 (n : ℕ) (hn : n ≤ 4) (F G : Fin n → Matrix (Fin 4) (Fin 4) K)
    (h : ∀ A : Matrix (Fin 4) (Fin 4) K,
      A.permanent = ∑ v, rowForm (F v) 0 3 A * rowForm (G v) 1 2 A) : False := by
  apply no_rank_four_01 n hn F (fun v => (G v)ᵀ)
  intro A
  have := h (A.submatrix (Equiv.swap 1 3) id)
  rw [Matrix.permanent_permute_cols] at this
  have e0 : Equiv.swap (1 : Fin 4) 3 0 = 0 := by decide
  have e2 : Equiv.swap (1 : Fin 4) 3 2 = 2 := by decide
  simp only [rowForm_transpose]
  simpa [rowForm, e0, e2] using this

end Rank

section Main

variable {K : Type*} [Field K]

/-- `SlicePt K a b c`: for any `a` covectors on the first argument, `b` on the second and `c`
on the third, `E3` does not vanish identically on the product of their common kernels. -/
def SlicePt (K : Type*) [Field K] (a b c : ℕ) : Prop :=
  ∀ g₁ g₂ g₃ : ℕ → Fin 4 → K, ∃ w x y : Fin 4 → K, (∀ i < a, dot4 (g₁ i) w = 0) ∧
    (∀ i < b, dot4 (g₂ i) x = 0) ∧ (∀ i < c, dot4 (g₃ i) y = 0) ∧ E3 w x y ≠ 0

lemma SlicePt.swap12 {a b c : ℕ} (h : SlicePt K a b c) : SlicePt K b a c := fun g₁ g₂ g₃ => by
  obtain ⟨w, x, y, h1, h2, h3, hE⟩ := h g₂ g₁ g₃
  exact ⟨x, w, y, h2, h1, h3, by rwa [E3_swap12]⟩

lemma SlicePt.swap23 {a b c : ℕ} (h : SlicePt K a b c) : SlicePt K a c b := fun g₁ g₂ g₃ => by
  obtain ⟨w, x, y, h1, h2, h3, hE⟩ := h g₁ g₃ g₂
  exact ⟨w, y, x, h1, h3, h2, by rwa [E3_swap23]⟩

lemma SlicePt.mono {a b c a' b' c' : ℕ} (h : SlicePt K a b c) (ha : a' ≤ a) (hb : b' ≤ b)
    (hc : c' ≤ c) : SlicePt K a' b' c' := fun g₁ g₂ g₃ => by
  obtain ⟨w, x, y, h1, h2, h3, hE⟩ := h g₁ g₂ g₃
  exact ⟨w, x, y, fun i hi => h1 i (by omega), fun i hi => h2 i (by omega),
    fun i hi => h3 i (by omega), hE⟩

variable [CharZero K]

lemma slicePt_211 : SlicePt K 2 1 1 := fun g₁ g₂ g₃ => by
  obtain ⟨w, x, y, h1, h2, h3, h4, hE⟩ := slice_211 (g₁ 0) (g₁ 1) (g₂ 0) (g₃ 0)
  refine ⟨w, x, y, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hE⟩
  · interval_cases i <;> assumption
  · interval_cases i; assumption
  · interval_cases i; assumption

lemma slicePt_220 : SlicePt K 2 2 0 := fun g₁ g₂ g₃ => by
  obtain ⟨w, x, y, h1, h2, h3, h4, hE⟩ := slice_220 (g₁ 0) (g₁ 1) (g₂ 0) (g₂ 1)
  refine ⟨w, x, y, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hE⟩
  · interval_cases i <;> assumption
  · interval_cases i <;> assumption
  · omega

lemma slicePt_310 : SlicePt K 3 1 0 := fun g₁ g₂ g₃ => by
  obtain ⟨w, x, y, h1, h2, h3, h4, hE⟩ := slice_310 (g₁ 0) (g₁ 1) (g₁ 2) (g₂ 0)
  refine ⟨w, x, y, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hE⟩
  · interval_cases i <;> assumption
  · interval_cases i; assumption
  · omega

/-- `E3` has no slice decomposition with at most four slices unless they all cut the same
argument. -/
theorem slicePt_of_le (a b c : ℕ) (h : a + b + c ≤ 4) (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) :
    SlicePt K a b c := by
  have hcases : (a ≤ 2 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (a ≤ 1 ∧ b ≤ 2 ∧ c ≤ 1) ∨ (a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 2) ∨
      (a ≤ 2 ∧ b ≤ 2 ∧ c ≤ 0) ∨ (a ≤ 2 ∧ b ≤ 0 ∧ c ≤ 2) ∨ (a ≤ 0 ∧ b ≤ 2 ∧ c ≤ 2) ∨
      (a ≤ 3 ∧ b ≤ 1 ∧ c ≤ 0) ∨ (a ≤ 3 ∧ b ≤ 0 ∧ c ≤ 1) ∨ (a ≤ 1 ∧ b ≤ 3 ∧ c ≤ 0) ∨
      (a ≤ 0 ∧ b ≤ 3 ∧ c ≤ 1) ∨ (a ≤ 1 ∧ b ≤ 0 ∧ c ≤ 3) ∨ (a ≤ 0 ∧ b ≤ 1 ∧ c ≤ 3) := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h
  · exact slicePt_211.mono h.1 h.2.1 h.2.2
  · exact slicePt_211.swap12.mono h.1 h.2.1 h.2.2
  · exact slicePt_211.swap12.swap23.mono h.1 h.2.1 h.2.2
  · exact slicePt_220.mono h.1 h.2.1 h.2.2
  · exact slicePt_220.swap23.mono h.1 h.2.1 h.2.2
  · exact slicePt_220.swap23.swap12.mono h.1 h.2.1 h.2.2
  · exact slicePt_310.mono h.1 h.2.1 h.2.2
  · exact slicePt_310.swap23.mono h.1 h.2.1 h.2.2
  · exact slicePt_310.swap12.mono h.1 h.2.1 h.2.2
  · exact slicePt_310.swap23.swap12.mono h.1 h.2.1 h.2.2
  · exact slicePt_310.swap12.swap23.mono h.1 h.2.1 h.2.2
  · exact slicePt_310.swap23.swap12.swap23.mono h.1 h.2.1 h.2.2

omit [CharZero K] in
/-- A finite family of covectors can be listed as a sequence, padded with zeros. -/
lemma exists_pad_covectors {ι : Type*} (S : Finset ι) (f : ι → Fin 4 → K) :
    ∃ g : ℕ → Fin 4 → K, (∀ z : Fin 4 → K, (∀ i < S.card, dot4 (g i) z = 0) →
      ∀ v ∈ S, dot4 (f v) z = 0) ∧ ∀ i, S.card ≤ i → g i = 0 := by
  refine ⟨fun i => if hi : i < S.card then f (S.equivFin.symm ⟨i, hi⟩) else 0,
    fun z hz v hv => ?_, fun i hi => ?_⟩
  · have := hz (S.equivFin ⟨v, hv⟩).val (S.equivFin ⟨v, hv⟩).isLt
    simpa using this
  · have : ¬ i < S.card := by omega
    simp [this]

/-- The matrix with rows `(1,1,1,1), w, x, y`. -/
def rowsMat (w x y : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K := Matrix.of ![fun _ => 1, w, x, y]

omit [CharZero K] in
lemma permanent_rowsMat (w x y : Fin 4 → K) : (rowsMat w x y).permanent = E3 w x y := by
  rw [permanent_fin_four, E3_eq]
  simp [rowsMat]
  ring

/-- Column sums of a coefficient table: the covector `F(1, ·)`. -/
def colSum (F : Matrix (Fin 4) (Fin 4) K) : Fin 4 → K := fun q => ∑ p, F p q

omit [CharZero K] in
lemma rowForm_rowsMat (F : Matrix (Fin 4) (Fin 4) K) (w x y : Fin 4 → K) :
    rowForm F 0 1 (rowsMat w x y) = dot4 (colSum F) w ∧
    rowForm F 0 2 (rowsMat w x y) = dot4 (colSum F) x ∧
    rowForm F 0 3 (rowsMat w x y) = dot4 (colSum F) y := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [rowForm, dot4, colSum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [rowsMat]

/-- The split product of pairing `π` (`0` for `01|23`, `1` for `02|13`, `2` for `03|12`) with
coefficient tables `F` (for the pair of rows containing row `0`) and `G`. -/
def splitTerm (π : Fin 3) (F G : Matrix (Fin 4) (Fin 4) K) (A : Matrix (Fin 4) (Fin 4) K) : K :=
  (![rowForm F 0 1 A * rowForm G 2 3 A, rowForm F 0 2 A * rowForm G 1 3 A,
    rowForm F 0 3 A * rowForm G 1 2 A] : Fin 3 → K) π

/-- **The `4 × 4` permanent is not a sum of four split products**, whatever pairings the terms
use: any family of split products (bilinear form in two rows times bilinear form in the other
two, each term with its own pairing `01|23`, `02|13` or `03|12`) that adds up to the permanent
has at least five members. -/
theorem five_le_card_of_permanent_eq_sum_split {ι : Type*} [Fintype ι] (π : ι → Fin 3)
    (F G : ι → Matrix (Fin 4) (Fin 4) K)
    (h : ∀ A : Matrix (Fin 4) (Fin 4) K, A.permanent = ∑ v, splitTerm (π v) (F v) (G v) A) :
    5 ≤ Fintype.card ι := by
  classical
  by_contra hlt
  push Not at hlt
  let S : Fin 3 → Finset ι := fun j => Finset.univ.filter fun v => π v = j
  have hc : (S 0).card + (S 1).card + (S 2).card = Fintype.card ι := by
    have := Finset.card_eq_sum_card_fiberwise (f := π) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [Fin.sum_univ_three] at this
    rw [← Finset.card_univ, this]
  by_cases hbig : ∃ j, 4 ≤ (S j).card
  · obtain ⟨j, hj⟩ := hbig
    have hSj : S j = Finset.univ := by
      apply Finset.eq_univ_of_card
      have := Finset.card_le_univ (S j)
      omega
    have hall : ∀ v, π v = j := by
      intro v
      have : v ∈ S j := by rw [hSj]; exact Finset.mem_univ v
      simpa [S] using this
    let e := Fintype.equivFin ι
    have h' : ∀ A : Matrix (Fin 4) (Fin 4) K, A.permanent =
        ∑ i : Fin (Fintype.card ι), splitTerm j (F (e.symm i)) (G (e.symm i)) A := by
      intro A
      rw [h A, ← e.symm.sum_comp]
      simp [hall]
    fin_cases j
    · exact no_rank_four_01 _ (by omega) _ _ h'
    · exact no_rank_four_02 _ (by omega) _ _ h'
    · exact no_rank_four_03 _ (by omega) _ _ h'
  · push Not at hbig
    have hpt := slicePt_of_le (K := K) (S 0).card (S 1).card (S 2).card (by omega)
      (by have := hbig 0; omega) (by have := hbig 1; omega) (by have := hbig 2; omega)
    obtain ⟨g₀, hg₀, -⟩ := exists_pad_covectors (S 0) (fun v => colSum (F v))
    obtain ⟨g₁, hg₁, -⟩ := exists_pad_covectors (S 1) (fun v => colSum (F v))
    obtain ⟨g₂, hg₂, -⟩ := exists_pad_covectors (S 2) (fun v => colSum (F v))
    obtain ⟨w, x, y, hw, hx, hy, hE⟩ := hpt g₀ g₁ g₂
    apply hE
    rw [← permanent_rowsMat, h]
    refine Finset.sum_eq_zero fun v _ => ?_
    have h0 := hg₀ w hw v
    have h1 := hg₁ x hx v
    have h2 := hg₂ y hy v
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1 h2
    obtain ⟨hr0, hr1, hr2⟩ := rowForm_rowsMat (F v) w x y
    obtain ⟨j, hj⟩ : ∃ j, π v = j := ⟨_, rfl⟩
    rw [hj] at h0 h1 h2 ⊢
    fin_cases j
    · simp [splitTerm, hr0, h0]
    · simp [splitTerm, hr1, h1]
    · simp [splitTerm, hr2, h2]

end Main


noncomputable section Limit

open Filter Topology

/-! ### Limits of sums of four split products (over `ℝ` or `ℂ`) -/

variable {𝕜 : Type*} [RCLike 𝕜]

lemma dot4_smul_left (s : 𝕜) (a z : Fin 4 → 𝕜) : dot4 (s • a) z = s * dot4 a z := by
  simp only [dot4_eq, Pi.smul_apply, smul_eq_mul]; ring

lemma dot4_smul_right (s : 𝕜) (a z : Fin 4 → 𝕜) : dot4 a (s • z) = s * dot4 a z := by
  simp only [dot4_eq, Pi.smul_apply, smul_eq_mul]; ring

lemma dot4_sub_left (a b z : Fin 4 → 𝕜) : dot4 (a - b) z = dot4 a z - dot4 b z := by
  simp only [dot4_eq, Pi.sub_apply]; ring

lemma dot4_sub_right (a x y : Fin 4 → 𝕜) : dot4 a (x - y) = dot4 a x - dot4 a y := by
  simp only [dot4_eq, Pi.sub_apply]; ring

lemma dot4_zero_right (a : Fin 4 → 𝕜) : dot4 a 0 = 0 := by simp [dot4]

lemma dot4_star_symm (a b : Fin 4 → 𝕜) : dot4 b (star a) = star (dot4 a (star b)) := by
  simp only [dot4_eq, Pi.star_apply, star_add, star_mul', star_star]; ring

/-- Squared Hermitian norm of a vector of `𝕜⁴`. -/
def N2 (b : Fin 4 → 𝕜) : ℝ := ‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2 + ‖b 3‖ ^ 2

lemma dot4_star_self (b : Fin 4 → 𝕜) : dot4 b (star b) = (N2 b : 𝕜) := by
  simp only [dot4_eq, Pi.star_apply, RCLike.star_def, RCLike.mul_conj, N2]
  push_cast
  ring

lemma N2_eq_zero {b : Fin 4 → 𝕜} (h : N2 b = 0) : b = 0 := by
  unfold N2 at h
  have h0 := sq_nonneg ‖b 0‖
  have h1 := sq_nonneg ‖b 1‖
  have h2 := sq_nonneg ‖b 2‖
  have h3 := sq_nonneg ‖b 3‖
  refine eq_zero_of_coords ⟨?_, ?_, ?_, ?_⟩ <;>
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (by linarith))

lemma N2_smul (c : 𝕜) (r : Fin 4 → 𝕜) : N2 (c • r) = ‖c‖ ^ 2 * N2 r := by
  simp only [N2, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]; ring

/-- Normalise a vector (the zero vector stays zero). -/
lemma exists_unit_or_zero (r : Fin 4 → 𝕜) :
    ∃ (b : Fin 4 → 𝕜) (s t : 𝕜), b = s • r ∧ r = t • b ∧ (N2 b = 0 ∨ N2 b = 1) := by
  by_cases hr : r = 0
  · exact ⟨0, 0, 0, by simp, by simp [hr], Or.inl (by simp [N2])⟩
  · have h0 : 0 ≤ N2 r := by unfold N2; positivity
    have hpos : 0 < N2 r := lt_of_le_of_ne h0 (fun h => hr (N2_eq_zero h.symm))
    have hN : 0 < Real.sqrt (N2 r) := Real.sqrt_pos.mpr hpos
    have hN2 : Real.sqrt (N2 r) * Real.sqrt (N2 r) = N2 r := Real.mul_self_sqrt h0
    refine ⟨(((Real.sqrt (N2 r))⁻¹ : ℝ) : 𝕜) • r, (((Real.sqrt (N2 r))⁻¹ : ℝ) : 𝕜),
      ((Real.sqrt (N2 r) : ℝ) : 𝕜), rfl, ?_, Or.inr ?_⟩
    · rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hN.ne', RCLike.ofReal_one, one_smul]
    · rw [N2_smul, RCLike.norm_ofReal, sq_abs]
      have e : ((Real.sqrt (N2 r))⁻¹) ^ 2 * (Real.sqrt (N2 r) * Real.sqrt (N2 r)) = 1 := by
        field_simp
      rw [hN2] at e
      exact e

/-- Gram–Schmidt for three covectors, allowing zero vectors in the output. -/
lemma gram_schmidt3 (g₀ g₁ g₂ : Fin 4 → 𝕜) : ∃ b₀ b₁ b₂ : Fin 4 → 𝕜,
    dot4 b₀ (star b₁) = 0 ∧ dot4 b₀ (star b₂) = 0 ∧ dot4 b₁ (star b₂) = 0 ∧
    (N2 b₀ = 0 ∨ N2 b₀ = 1) ∧ (N2 b₁ = 0 ∨ N2 b₁ = 1) ∧ (N2 b₂ = 0 ∨ N2 b₂ = 1) ∧
    (g₀ = 0 → b₀ = 0) ∧ (g₁ = 0 → b₁ = 0) ∧ (g₂ = 0 → b₂ = 0) ∧
    ∀ z, dot4 b₀ z = 0 → dot4 b₁ z = 0 → dot4 b₂ z = 0 →
      dot4 g₀ z = 0 ∧ dot4 g₁ z = 0 ∧ dot4 g₂ z = 0 := by
  have key : ∀ b : Fin 4 → 𝕜, (N2 b = 0 ∨ N2 b = 1) →
      ∀ z, dot4 z (star b) * (1 - (N2 b : 𝕜)) = 0 := by
    intro b hb z
    rcases hb with h | h
    · rw [N2_eq_zero h, star_zero, dot4_zero_right]; ring
    · rw [h]; simp
  obtain ⟨b₀, s₀, t₀, hb₀, hr₀, hn₀⟩ := exists_unit_or_zero g₀
  obtain ⟨b₁, s₁, t₁, hb₁, hr₁, hn₁⟩ := exists_unit_or_zero (g₁ - dot4 g₁ (star b₀) • b₀)
  have o₁ : dot4 (g₁ - dot4 g₁ (star b₀) • b₀) (star b₀) = 0 := by
    rw [dot4_sub_left, dot4_smul_left, dot4_star_self]
    linear_combination key b₀ hn₀ g₁
  have h10 : dot4 b₁ (star b₀) = 0 := by
    rw [hb₁, dot4_smul_left, o₁, mul_zero]
  have h01 : dot4 b₀ (star b₁) = 0 := by rw [dot4_star_symm, h10, star_zero]
  obtain ⟨b₂, s₂, t₂, hb₂, hr₂, hn₂⟩ :=
    exists_unit_or_zero (g₂ - dot4 g₂ (star b₀) • b₀ - dot4 g₂ (star b₁) • b₁)
  have o₂ : dot4 (g₂ - dot4 g₂ (star b₀) • b₀ - dot4 g₂ (star b₁) • b₁) (star b₀) = 0 := by
    rw [dot4_sub_left, dot4_sub_left, dot4_smul_left, dot4_smul_left, dot4_star_self, h10]
    linear_combination key b₀ hn₀ g₂
  have o₂' : dot4 (g₂ - dot4 g₂ (star b₀) • b₀ - dot4 g₂ (star b₁) • b₁) (star b₁) = 0 := by
    rw [dot4_sub_left, dot4_sub_left, dot4_smul_left, dot4_smul_left, dot4_star_self, h01]
    linear_combination key b₁ hn₁ g₂
  have h20 : dot4 b₂ (star b₀) = 0 := by
    rw [hb₂, dot4_smul_left, o₂, mul_zero]
  have h21 : dot4 b₂ (star b₁) = 0 := by
    rw [hb₂, dot4_smul_left, o₂', mul_zero]
  have h02 : dot4 b₀ (star b₂) = 0 := by rw [dot4_star_symm, h20, star_zero]
  have h12 : dot4 b₁ (star b₂) = 0 := by rw [dot4_star_symm, h21, star_zero]
  refine ⟨b₀, b₁, b₂, h01, h02, h12, hn₀, hn₁, hn₂, ?_, ?_, ?_, ?_⟩
  · intro h; rw [hb₀, h, smul_zero]
  · intro h
    have : g₁ - dot4 g₁ (star b₀) • b₀ = 0 := by
      rw [h]; simp [dot4]
    rw [hb₁, this, smul_zero]
  · intro h
    have : g₂ - dot4 g₂ (star b₀) • b₀ - dot4 g₂ (star b₁) • b₁ = 0 := by
      rw [h]; simp [dot4]
    rw [hb₂, this, smul_zero]
  · intro z z0 z1 z2
    have e0 : dot4 g₀ z = 0 := by rw [hr₀, dot4_smul_left, z0, mul_zero]
    have e1 : dot4 (g₁ - dot4 g₁ (star b₀) • b₀) z = 0 := by
      rw [hr₁, dot4_smul_left, z1, mul_zero]
    have e2 : dot4 (g₂ - dot4 g₂ (star b₀) • b₀ - dot4 g₂ (star b₁) • b₁) z = 0 := by
      rw [hr₂, dot4_smul_left, z2, mul_zero]
    rw [dot4_sub_left, dot4_smul_left, z0] at e1
    rw [dot4_sub_left, dot4_sub_left, dot4_smul_left, dot4_smul_left, z0, z1] at e2
    exact ⟨e0, by linear_combination e1, by linear_combination e2⟩

/-- Three covectors, pairwise orthogonal for the Hermitian form, each zero or of norm one,
those of index `≥ a` zero. -/
def IsFrame (a : ℕ) (b : Fin 3 → Fin 4 → 𝕜) : Prop :=
  (dot4 (b 0) (star (b 1)) = 0 ∧ dot4 (b 0) (star (b 2)) = 0 ∧ dot4 (b 1) (star (b 2)) = 0) ∧
  (∀ i, N2 (b i) = 0 ∨ N2 (b i) = 1) ∧ ∀ i : Fin 3, a ≤ (i : ℕ) → b i = 0

/-- Projection onto the common kernel of the covectors of a frame. -/
def prj (b : Fin 3 → Fin 4 → 𝕜) (x : Fin 4 → 𝕜) : Fin 4 → 𝕜 :=
  x - dot4 (b 0) x • star (b 0) - dot4 (b 1) x • star (b 1) - dot4 (b 2) x • star (b 2)

lemma dot4_prj {a : ℕ} {b : Fin 3 → Fin 4 → 𝕜} (hb : IsFrame a b) (x : Fin 4 → 𝕜) (i : Fin 3) :
    dot4 (b i) (prj b x) = 0 := by
  obtain ⟨⟨h01, h02, h12⟩, hn, -⟩ := hb
  have key : ∀ i, dot4 (b i) x * (1 - (N2 (b i) : 𝕜)) = 0 := by
    intro i
    rcases hn i with h | h
    · rw [N2_eq_zero h]; simp [dot4]
    · rw [h]; simp
  have h10 : dot4 (b 1) (star (b 0)) = 0 := by rw [dot4_star_symm, h01, star_zero]
  have h20 : dot4 (b 2) (star (b 0)) = 0 := by rw [dot4_star_symm, h02, star_zero]
  have h21 : dot4 (b 2) (star (b 1)) = 0 := by rw [dot4_star_symm, h12, star_zero]
  fin_cases i
  · simp only [prj, dot4_sub_right, dot4_smul_right, Fin.zero_eta, dot4_star_self, h01, h02]
    linear_combination key 0
  · simp only [prj, dot4_sub_right, dot4_smul_right, Fin.mk_one, dot4_star_self, h10, h12]
    linear_combination key 1
  · simp only [prj, dot4_sub_right, dot4_smul_right, Fin.reduceFinMk, dot4_star_self, h20, h21]
    linear_combination key 2

lemma prj_eq_self {b : Fin 3 → Fin 4 → 𝕜} {x : Fin 4 → 𝕜} (h : ∀ i, dot4 (b i) x = 0) :
    prj b x = x := by
  simp [prj, h]

lemma isCompact_frames (a : ℕ) : IsCompact {b : Fin 3 → Fin 4 → 𝕜 | IsFrame a b} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have hc : ∀ i j : Fin 3, Continuous fun b : Fin 3 → Fin 4 → 𝕜 => dot4 (b i) (star (b j)) := by
      intro i j
      simp only [dot4_eq, Pi.star_apply]
      fun_prop
    have hN : ∀ i : Fin 3, Continuous fun b : Fin 3 → Fin 4 → 𝕜 => N2 (b i) := by
      intro i
      simp only [N2]
      fun_prop
    have h3 : ∀ i : Fin 3, IsClosed {b : Fin 3 → Fin 4 → 𝕜 | a ≤ (i : ℕ) → b i = 0} := by
      intro i
      by_cases h : a ≤ (i : ℕ)
      · simp only [h, forall_true_left]
        exact isClosed_eq (continuous_apply i) continuous_const
      · simp [h]
    have h2 : ∀ i : Fin 3, IsClosed {b : Fin 3 → Fin 4 → 𝕜 |
        N2 (b i) = 0 ∨ N2 (b i) = 1} := fun i =>
      (isClosed_eq (hN i) continuous_const).union (isClosed_eq (hN i) continuous_const)
    have : {b : Fin 3 → Fin 4 → 𝕜 | IsFrame a b} =
        ({b | dot4 (b 0) (star (b 1)) = 0} ∩ {b | dot4 (b 0) (star (b 2)) = 0} ∩
          {b | dot4 (b 1) (star (b 2)) = 0}) ∩
        (⋂ i : Fin 3, {b | N2 (b i) = 0 ∨ N2 (b i) = 1}) ∩
        (⋂ i : Fin 3, {b | a ≤ (i : ℕ) → b i = 0}) := by
      ext b
      simp [IsFrame, and_assoc]
    rw [this]
    exact ((((isClosed_eq (hc 0 1) continuous_const).inter (isClosed_eq (hc 0 2) continuous_const)).inter
      (isClosed_eq (hc 1 2) continuous_const)).inter (isClosed_iInter h2)).inter (isClosed_iInter h3)
  · refine (Metric.isBounded_closedBall (x := (0 : Fin 3 → Fin 4 → 𝕜)) (r := 1)).subset ?_
    intro b hb
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun l => ?_
    have hle : N2 (b i) ≤ 1 := by
      rcases hb.2.1 i with h | h
      · rw [h]; norm_num
      · rw [h]
    unfold N2 at hle
    have h0 := sq_nonneg ‖b i 0‖
    have h1 := sq_nonneg ‖b i 1‖
    have h2 := sq_nonneg ‖b i 2‖
    have h3 := sq_nonneg ‖b i 3‖
    have key : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ 1 → t ≤ 1 := fun t ht h => by nlinarith
    apply key _ (norm_nonneg _)
    fin_cases l
    · show ‖b i 0‖ ^ 2 ≤ 1
      linarith
    · show ‖b i 1‖ ^ 2 ≤ 1
      linarith
    · show ‖b i 2‖ ^ 2 ≤ 1
      linarith
    · show ‖b i 3‖ ^ 2 ≤ 1
      linarith

/-- Coefficient tensors of trilinear forms in three vectors of `𝕜⁴`. -/
abbrev T3 (𝕜 : Type*) := Fin 4 → Fin 4 → Fin 4 → 𝕜

/-- The trilinear form with coefficient tensor `c`. -/
def tri (c : T3 𝕜) (w x y : Fin 4 → 𝕜) : 𝕜 := ∑ i, ∑ j, ∑ k, c i j k * (w i * x j * y k)

/-- Trilinear forms vanishing on a product of three subspaces, the common kernels of at most
`a₁`, `a₂`, `a₃` covectors. Compactness of the Grassmannians makes this a closed condition. -/
def Csl (a₁ a₂ a₃ : ℕ) : Set (T3 𝕜) :=
  {c | ∃ b₁ b₂ b₃ : Fin 3 → Fin 4 → 𝕜, IsFrame a₁ b₁ ∧ IsFrame a₂ b₂ ∧ IsFrame a₃ b₃ ∧
    ∀ w x y, tri c (prj b₁ w) (prj b₂ x) (prj b₃ y) = 0}

lemma isClosed_Csl (a₁ a₂ a₃ : ℕ) : IsClosed (Csl a₁ a₂ a₃ : Set (T3 𝕜)) := by
  apply IsSeqClosed.isClosed
  intro c c₀ hc hlim
  choose b₁ b₂ b₃ h₁ h₂ h₃ hv using hc
  have hK := (isCompact_frames (𝕜 := 𝕜) a₁).prod
    ((isCompact_frames (𝕜 := 𝕜) a₂).prod (isCompact_frames (𝕜 := 𝕜) a₃))
  obtain ⟨p, hp, φ, hφ, hpl⟩ := hK.tendsto_subseq (x := fun n => (b₁ n, b₂ n, b₃ n))
    (fun n => ⟨h₁ n, h₂ n, h₃ n⟩)
  refine ⟨p.1, p.2.1, p.2.2, hp.1, hp.2.1, hp.2.2, fun w x y => ?_⟩
  have hcont : Continuous fun q : T3 𝕜 × ((Fin 3 → Fin 4 → 𝕜) × (Fin 3 → Fin 4 → 𝕜) ×
      (Fin 3 → Fin 4 → 𝕜)) => tri q.1 (prj q.2.1 w) (prj q.2.2.1 x) (prj q.2.2.2 y) := by
    simp only [tri, prj, dot4_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
    fun_prop
  have hlim2 : Tendsto (fun n => (c (φ n), (b₁ (φ n), b₂ (φ n), b₃ (φ n)))) atTop (𝓝 (c₀, p)) :=
    (hlim.comp hφ.tendsto_atTop).prodMk_nhds hpl
  have h3 := (hcont.tendsto (c₀, p)).comp hlim2
  refine tendsto_nhds_unique h3 ?_
  have : ((fun q : T3 𝕜 × ((Fin 3 → Fin 4 → 𝕜) × (Fin 3 → Fin 4 → 𝕜) × (Fin 3 → Fin 4 → 𝕜)) =>
      tri q.1 (prj q.2.1 w) (prj q.2.2.1 x) (prj q.2.2.2 y)) ∘
      fun n => (c (φ n), (b₁ (φ n), b₂ (φ n), b₃ (φ n)))) = fun _ => 0 := by
    funext n
    exact hv (φ n) w x y
  rw [this]
  exact tendsto_const_nhds

/-- Coefficient tensor of `E3`. -/
def cE : T3 𝕜 := fun i j k => if i ≠ j ∧ i ≠ k ∧ j ≠ k then 1 else 0

lemma tri_cE (w x y : Fin 4 → 𝕜) : tri cE w x y = E3 w x y := by
  simp only [tri, cE, E3, ite_mul, one_mul, zero_mul]

/-- `E3` is not in any of the closed sets `Csl a₁ a₂ a₃` with `a₁ + a₂ + a₃ ≤ 4`. -/
lemma cE_not_mem (a₁ a₂ a₃ : ℕ) (h : a₁ + a₂ + a₃ ≤ 4) (h₁ : a₁ ≤ 3) (h₂ : a₂ ≤ 3)
    (h₃ : a₃ ≤ 3) : (cE : T3 𝕜) ∉ Csl a₁ a₂ a₃ := by
  rintro ⟨b₁, b₂, b₃, f₁, f₂, f₃, hv⟩
  have ext : ∀ b : Fin 3 → Fin 4 → 𝕜, ∃ g : ℕ → Fin 4 → 𝕜, ∀ i : Fin 3, g i = b i := fun b =>
    ⟨fun i => if h : i < 3 then b ⟨i, h⟩ else 0, fun i => by simp⟩
  obtain ⟨g₁, e₁⟩ := ext b₁
  obtain ⟨g₂, e₂⟩ := ext b₂
  obtain ⟨g₃, e₃⟩ := ext b₃
  obtain ⟨w, x, y, hw, hx, hy, hE⟩ := slicePt_of_le (K := 𝕜) a₁ a₂ a₃ h h₁ h₂ h₃ g₁ g₂ g₃
  have kw : ∀ i : Fin 3, dot4 (b₁ i) w = 0 := by
    intro i
    by_cases hi : (i : ℕ) < a₁
    · rw [← e₁ i]; exact hw i hi
    · rw [f₁.2.2 i (by omega)]; simp
  have kx : ∀ i : Fin 3, dot4 (b₂ i) x = 0 := by
    intro i
    by_cases hi : (i : ℕ) < a₂
    · rw [← e₂ i]; exact hx i hi
    · rw [f₂.2.2 i (by omega)]; simp
  have ky : ∀ i : Fin 3, dot4 (b₃ i) y = 0 := by
    intro i
    by_cases hi : (i : ℕ) < a₃
    · rw [← e₃ i]; exact hy i hi
    · rw [f₃.2.2 i (by omega)]; simp
  have := hv w x y
  rw [prj_eq_self kw, prj_eq_self kx, prj_eq_self ky, tri_cE] at this
  exact hE this

/-! #### From decompositions to the closed sets -/

/-- Coefficient tensor of a function of matrices along `rowsMat`. -/
def coef (D : Matrix (Fin 4) (Fin 4) 𝕜 → 𝕜) : T3 𝕜 := fun i j k =>
  D (rowsMat (Pi.single i 1) (Pi.single j 1) (Pi.single k 1))

lemma splitTerm_rowsMat (π : Fin 3) (F G : Matrix (Fin 4) (Fin 4) 𝕜) (w x y : Fin 4 → 𝕜) :
    splitTerm π F G (rowsMat w x y) = tri (coef (splitTerm π F G)) w x y := by
  fin_cases π <;>
  · simp [splitTerm, tri, coef, rowForm, rowsMat, Fin.sum_univ_four, Pi.single_apply]
    ring

lemma tri_add (c c' : T3 𝕜) (w x y : Fin 4 → 𝕜) :
    tri (fun i j k => c i j k + c' i j k) w x y = tri c w x y + tri c' w x y := by
  simp only [tri, add_mul, Finset.sum_add_distrib]

lemma tri_sum {ι : Type*} (s : Finset ι) (c : ι → T3 𝕜) (w x y : Fin 4 → 𝕜) :
    tri (fun i j k => ∑ v ∈ s, c v i j k) w x y = ∑ v ∈ s, tri (c v) w x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tri]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [tri_add (c a) (fun i j k => ∑ v ∈ s, c v i j k), ih]

lemma sum_split_rowsMat {ι : Type*} [Fintype ι] (π : ι → Fin 3)
    (F G : ι → Matrix (Fin 4) (Fin 4) 𝕜) (w x y : Fin 4 → 𝕜) :
    ∑ v, splitTerm (π v) (F v) (G v) (rowsMat w x y) =
      tri (coef fun A => ∑ v, splitTerm (π v) (F v) (G v) A) w x y := by
  have : coef (fun A => ∑ v, splitTerm (π v) (F v) (G v) A) =
      fun i j k => ∑ v ∈ Finset.univ, coef (splitTerm (π v) (F v) (G v)) i j k := rfl
  rw [this, tri_sum]
  exact Finset.sum_congr rfl fun v _ => splitTerm_rowsMat _ _ _ _ _ _

lemma exists_frame {ι : Type*} (S : Finset ι) (f : ι → Fin 4 → 𝕜) :
    ∃ b : Fin 3 → Fin 4 → 𝕜, IsFrame S.card b ∧
      (S.card ≤ 3 → ∀ z, (∀ i, dot4 (b i) z = 0) → ∀ v ∈ S, dot4 (f v) z = 0) := by
  obtain ⟨g, hg, hz⟩ := exists_pad_covectors S f
  obtain ⟨p0, p1, p2, o01, o02, o12, n0, n1, n2, z0, z1, z2, hker⟩ :=
    gram_schmidt3 (g 0) (g 1) (g 2)
  refine ⟨![p0, p1, p2], ⟨⟨o01, o02, o12⟩, ?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · exact n0
    · exact n1
    · exact n2
  · intro i hi
    fin_cases i
    · exact z0 (hz 0 hi)
    · exact z1 (hz 1 hi)
    · exact z2 (hz 2 hi)
  · intro hS z hb v hv
    obtain ⟨e0, e1, e2⟩ := hker z (hb 0) (hb 1) (hb 2)
    refine hg z (fun i hi => ?_) v hv
    have : i < 3 := by omega
    interval_cases i
    · exact e0
    · exact e1
    · exact e2

/-- Index data of the `5 × 5` minor of the flattening used for the rank argument. -/
def pa : Fin 5 → Fin 4 := ![0, 0, 0, 1, 1]
/-- See `pa`. -/
def pb : Fin 5 → Fin 4 := ![1, 2, 3, 2, 3]
/-- See `pa`. -/
def pc : Fin 5 → Fin 4 := ![2, 1, 1, 0, 0]
/-- See `pa`. -/
def pd : Fin 5 → Fin 4 := ![3, 3, 2, 3, 2]

/-- Rows `e_a, e_b` in the first pair and `e_c, e_d` in the second pair of the pairing `j`. -/
def idxMat (j : Fin 3) (k k' : Fin 5) : Fin 4 → Fin 4 :=
  (![![pa k, pb k, pc k', pd k'], ![pa k, pc k', pb k, pd k'], ![pa k, pc k', pd k', pb k]] :
    Fin 3 → Fin 4 → Fin 4) j

lemma splitTerm_selMat (j : Fin 3) (F G : Matrix (Fin 4) (Fin 4) 𝕜) (k k' : Fin 5) :
    splitTerm j F G (selMat (idxMat j k k')) = F (pa k) (pb k) * G (pc k') (pd k') := by
  fin_cases j <;> simp [splitTerm, idxMat, rowForm_selMat]

lemma permanent_selMat_idx (j : Fin 3) (k k' : Fin 5) :
    (selMat (idxMat j k k') : Matrix (Fin 4) (Fin 4) 𝕜).permanent = if k = k' then 1 else 0 := by
  fin_cases j <;> fin_cases k <;> fin_cases k' <;>
    simp [idxMat, pa, pb, pc, pd, permanent_fin_four, selMat]

/-- A `5 × 5` matrix that is a sum of at most four rank-one matrices has determinant zero. -/
lemma det_sum_rank_one {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4) (P Q : ι → Fin 5 → 𝕜) :
    Matrix.det (Matrix.of fun k k' : Fin 5 => ∑ v, P v k * Q v k') = 0 := by
  let e := Fintype.equivFin ι
  let M : Matrix (Fin 5) (Fin 5) 𝕜 := fun i k =>
    if hi : (i : ℕ) < Fintype.card ι then P (e.symm ⟨i, hi⟩) k else 0
  have h4 : ¬ ((4 : Fin 5) : ℕ) < Fintype.card ι := by
    have : ((4 : Fin 5) : ℕ) = 4 := rfl
    omega
  have hdet : M.det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero 4
    intro k
    simp only [M, h4, ↓reduceDIte]
  obtain ⟨lam, hlam, hM⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hv : ∀ v : ι, ∑ k, P v k * lam k = 0 := by
    intro v
    have := congrFun hM ⟨e v, by have := (e v).isLt; omega⟩
    simpa [M, Matrix.mulVec, dotProduct] using this
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨lam, hlam, ?_⟩
  funext k'
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun v _ => ?_
  have : ∑ k, lam k * (P v k * Q v k') = (∑ k, P v k * lam k) * Q v k' := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, hv, zero_mul]

/-- The `5 × 5` minor of the flattening of `D` for the pairing `j`. -/
def detJ (j : Fin 3) (D : Matrix (Fin 4) (Fin 4) 𝕜 → 𝕜) : 𝕜 :=
  Matrix.det (Matrix.of fun k k' : Fin 5 => D (selMat (idxMat j k k')))

lemma detJ_eq_zero {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4) (j : Fin 3)
    (F G : ι → Matrix (Fin 4) (Fin 4) 𝕜) :
    detJ j (fun A => ∑ v, splitTerm j (F v) (G v) A) = 0 := by
  simp only [detJ, splitTerm_selMat]
  exact det_sum_rank_one hι _ _

lemma tendsto_detJ (j : Fin 3) (D : ℕ → Matrix (Fin 4) (Fin 4) 𝕜 → 𝕜)
    (h : ∀ A : Matrix (Fin 4) (Fin 4) 𝕜, Tendsto (fun n => D n A) atTop (𝓝 A.permanent)) :
    Tendsto (fun n => detJ j (D n)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => (Matrix.of fun k k' : Fin 5 => D n (selMat (idxMat j k k')) :
      Matrix (Fin 5) (Fin 5) 𝕜)) atTop (𝓝 (1 : Matrix (Fin 5) (Fin 5) 𝕜)) := by
    refine tendsto_pi_nhds.mpr fun k => tendsto_pi_nhds.mpr fun k' => ?_
    have := h (selMat (idxMat j k k'))
    rw [permanent_selMat_idx] at this
    simpa [Matrix.one_apply] using this
  have h2 := (continuous_id.matrix_det.tendsto (1 : Matrix (Fin 5) (Fin 5) 𝕜)).comp h1
  simpa [detJ, Function.comp_def] using h2

/-- A sum of at most four split products whose three `5 × 5` minors do not vanish (so the terms
do not all have the same pairing) lies in one of the closed sets `Csl`. -/
lemma coef_mem_Csl {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4) (π : ι → Fin 3)
    (F G : ι → Matrix (Fin 4) (Fin 4) 𝕜)
    (hdet : ∀ j, detJ j (fun A => ∑ v, splitTerm (π v) (F v) (G v) A) ≠ 0) :
    ∃ a₁ a₂ a₃ : ℕ, a₁ + a₂ + a₃ ≤ 4 ∧ a₁ ≤ 3 ∧ a₂ ≤ 3 ∧ a₃ ≤ 3 ∧
      coef (fun A => ∑ v, splitTerm (π v) (F v) (G v) A) ∈ Csl a₁ a₂ a₃ := by
  classical
  let S : Fin 3 → Finset ι := fun j => Finset.univ.filter fun v => π v = j
  have hc : (S 0).card + (S 1).card + (S 2).card = Fintype.card ι := by
    have := Finset.card_eq_sum_card_fiberwise (f := π) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [Fin.sum_univ_three] at this
    rw [← Finset.card_univ, this]
  have hsmall : ∀ j, (S j).card ≤ 3 := by
    intro j
    by_contra hj
    have hSj : S j = Finset.univ := by
      apply Finset.eq_univ_of_card
      have := Finset.card_le_univ (S j)
      omega
    have hall : ∀ v, π v = j := by
      intro v
      have : v ∈ S j := by rw [hSj]; exact Finset.mem_univ v
      simpa [S] using this
    apply hdet j
    have : (fun A : Matrix (Fin 4) (Fin 4) 𝕜 => ∑ v, splitTerm (π v) (F v) (G v) A) =
        fun A => ∑ v, splitTerm j (F v) (G v) A := by
      funext A
      exact Finset.sum_congr rfl fun v _ => by rw [hall v]
    rw [this]
    exact detJ_eq_zero hι j F G
  obtain ⟨b₁, f₁, k₁⟩ := exists_frame (S 0) (fun v => colSum (F v))
  obtain ⟨b₂, f₂, k₂⟩ := exists_frame (S 1) (fun v => colSum (F v))
  obtain ⟨b₃, f₃, k₃⟩ := exists_frame (S 2) (fun v => colSum (F v))
  refine ⟨(S 0).card, (S 1).card, (S 2).card, by omega, hsmall 0, hsmall 1, hsmall 2,
    b₁, b₂, b₃, f₁, f₂, f₃, fun w x y => ?_⟩
  rw [← sum_split_rowsMat]
  refine Finset.sum_eq_zero fun v _ => ?_
  have h0 := k₁ (hsmall 0) (prj b₁ w) (fun i => dot4_prj f₁ w i) v
  have h1 := k₂ (hsmall 1) (prj b₂ x) (fun i => dot4_prj f₂ x i) v
  have h2 := k₃ (hsmall 2) (prj b₃ y) (fun i => dot4_prj f₃ y i) v
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1 h2
  obtain ⟨hr0, hr1, hr2⟩ := rowForm_rowsMat (F v) (prj b₁ w) (prj b₂ x) (prj b₃ y)
  obtain ⟨j, hj⟩ : ∃ j, π v = j := ⟨_, rfl⟩
  rw [hj] at h0 h1 h2 ⊢
  fin_cases j
  · simp [splitTerm, hr0, h0]
  · simp [splitTerm, hr1, h1]
  · simp [splitTerm, hr2, h2]

lemma E3_single (i j k : Fin 4) :
    E3 (Pi.single i 1 : Fin 4 → 𝕜) (Pi.single j 1) (Pi.single k 1) = cE i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [E3_eq, cE]

/-- **The `4 × 4` permanent is not a limit of sums of four split products** (over `ℝ` or `ℂ`):
no sequence of sums of at most four split products, with arbitrary and varying pairings,
converges pointwise to the permanent. -/
theorem not_tendsto_sum_split_four {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4)
    (π : ℕ → ι → Fin 3) (F G : ℕ → ι → Matrix (Fin 4) (Fin 4) 𝕜) :
    ¬ ∀ A : Matrix (Fin 4) (Fin 4) 𝕜,
      Tendsto (fun n => ∑ v, splitTerm (π n v) (F n v) (G n v) A) atTop (𝓝 A.permanent) := by
  intro h
  let I := {a : Fin 4 × Fin 4 × Fin 4 // (a.1 : ℕ) + a.2.1 + a.2.2 ≤ 4}
  have hclosed : IsClosed (⋃ a : I, (Csl a.1.1 a.1.2.1 a.1.2.2 : Set (T3 𝕜))) :=
    isClosed_iUnion_of_finite fun a => isClosed_Csl _ _ _
  have hcoef : Tendsto (fun n => coef fun A => ∑ v, splitTerm (π n v) (F n v) (G n v) A)
      atTop (𝓝 (cE : T3 𝕜)) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun k => ?_
    have := h (rowsMat (Pi.single i 1) (Pi.single j 1) (Pi.single k 1))
    rw [permanent_rowsMat, E3_single] at this
    exact this
  have hev : ∀ᶠ n in atTop, (coef fun A => ∑ v, splitTerm (π n v) (F n v) (G n v) A) ∈
      ⋃ a : I, (Csl a.1.1 a.1.2.1 a.1.2.2 : Set (T3 𝕜)) := by
    have hd : ∀ j : Fin 3, ∀ᶠ n in atTop,
        detJ j (fun A => ∑ v, splitTerm (π n v) (F n v) (G n v) A) ≠ 0 := fun j =>
      (tendsto_detJ j (fun n A => ∑ v, splitTerm (π n v) (F n v) (G n v) A) h).eventually_ne
        one_ne_zero
    filter_upwards [hd 0, hd 1, hd 2] with n h0 h1 h2
    have hall : ∀ j, detJ j (fun A => ∑ v, splitTerm (π n v) (F n v) (G n v) A) ≠ 0 := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    obtain ⟨a₁, a₂, a₃, hs, l₁, l₂, l₃, hmem⟩ := coef_mem_Csl hι (π n) (F n) (G n) hall
    exact Set.mem_iUnion.mpr ⟨⟨(⟨a₁, by omega⟩, ⟨a₂, by omega⟩, ⟨a₃, by omega⟩), hs⟩, hmem⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hclosed.mem_of_tendsto hcoef hev)
  exact cE_not_mem _ _ _ a.2 (by omega) (by omega) (by omega) ha

omit [RCLike 𝕜] in
/-- Every split product in the sense of `IsSplit` (file `FiveTerm`) is a `splitTerm`. -/
lemma exists_splitTerm_of_isSplit {K : Type*} [Field K] {t : Matrix (Fin 4) (Fin 4) K → K}
    (ht : IsSplit 0 1 2 3 t ∨ IsSplit 0 2 1 3 t ∨ IsSplit 0 3 1 2 t) :
    ∃ (p : Fin 3) (F G : Matrix (Fin 4) (Fin 4) K), ∀ A, t A = splitTerm p F G A := by
  rcases ht with ⟨F, G, h⟩ | ⟨F, G, h⟩ | ⟨F, G, h⟩
  · exact ⟨0, F, G, fun A => by simpa [splitTerm] using h A⟩
  · exact ⟨1, F, G, fun A => by simpa [splitTerm] using h A⟩
  · exact ⟨2, F, G, fun A => by simpa [splitTerm] using h A⟩

omit [RCLike 𝕜] in
/-- **Exact lower bound, in the language of `FiveTerm`.** Over a field of characteristic zero
the `4 × 4` permanent is not a sum of four split products, whatever pairings they use. -/
theorem permanent_ne_sum_four_isSplit {K : Type*} [Field K] [CharZero K]
    (t : Fin 4 → Matrix (Fin 4) (Fin 4) K → K)
    (ht : ∀ v, IsSplit 0 1 2 3 (t v) ∨ IsSplit 0 2 1 3 (t v) ∨ IsSplit 0 3 1 2 (t v)) :
    ¬ ∀ A : Matrix (Fin 4) (Fin 4) K, A.permanent = ∑ v, t v A := by
  intro h
  choose p F G hpFG using fun v => exists_splitTerm_of_isSplit (ht v)
  have := five_le_card_of_permanent_eq_sum_split p F G (fun A => by rw [h A]; simp [hpFG])
  simp at this

/-- **Border lower bound, in the language of `FiveTerm`.** Over `ℝ` or `ℂ`, no sequence of sums
of four split products (pairings and factors may change along the sequence) converges
pointwise to the `4 × 4` permanent. Together with `tendsto_five_split_strong` (five split
products do converge to it) this says that five is the least number of split products whose
sums approximate the permanent. -/
theorem not_tendsto_sum_four_isSplit (t : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) 𝕜 → 𝕜)
    (ht : ∀ n v, IsSplit 0 1 2 3 (t n v) ∨ IsSplit 0 2 1 3 (t n v) ∨ IsSplit 0 3 1 2 (t n v)) :
    ¬ ∀ A : Matrix (Fin 4) (Fin 4) 𝕜,
      Tendsto (fun n => ∑ v, t n v A) atTop (𝓝 A.permanent) := by
  intro h
  choose p F G hpFG using fun n v => exists_splitTerm_of_isSplit (ht n v)
  refine not_tendsto_sum_split_four (ι := Fin 4) (by simp) p F G fun A => ?_
  have := h A
  simpa [hpFG] using this

/-- The border lower bound over the complex numbers. -/
theorem not_tendsto_sum_four_isSplit_complex (t : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ → ℂ)
    (ht : ∀ n v, IsSplit 0 1 2 3 (t n v) ∨ IsSplit 0 2 1 3 (t n v) ∨ IsSplit 0 3 1 2 (t n v)) :
    ¬ ∀ A : Matrix (Fin 4) (Fin 4) ℂ,
      Tendsto (fun n => ∑ v, t n v A) atTop (𝓝 A.permanent) :=
  not_tendsto_sum_four_isSplit t ht

end Limit

end PvsNP
