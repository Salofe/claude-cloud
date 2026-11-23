import PvsNP.SplitRank

/-!
# The `4 × 4` permanent is not an exact sum of five split products: basic tools

This file contains the general tools used by `PvsNP.FourByFourExact`: bilinear forms given by
coefficient tables (`bil`), the permanent as a function of four rows (`perm4`), decompositions
with a prescribed number of terms on each of the three pairings (`Dec4`, `HasDec`), their
symmetries (row permutations, relabelling of the columns), a rank argument for flattenings
(`rank_contra`), a kernel lemma for sums of rank-one forms (`kernel_of_minor`), a chart lemma
for the common kernel of two covectors (`exists_chart`), and a principle for polynomial
conditions on the torus (`poly_union`).
-/

namespace PvsNP

open Matrix

section Base

variable {K : Type*} [Field K]

/-- The bilinear form with coefficient table `M`. -/
def bil (M : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K) : K := ∑ p, ∑ q, M p q * x p * y q

lemma rowForm_eq_bil (M : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4)
    (A : Matrix (Fin 4) (Fin 4) K) : rowForm M a b A = bil M (A a) (A b) := rfl

lemma bil_transpose (M : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K) :
    bil Mᵀ x y = bil M y x := by
  simp only [bil, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

@[simp] lemma bil_zero (x y : Fin 4 → K) : bil (0 : Matrix (Fin 4) (Fin 4) K) x y = 0 := by
  simp [bil]

/-- The covector `bil M x ·`. -/
def colf (M : Matrix (Fin 4) (Fin 4) K) (x : Fin 4 → K) : Fin 4 → K := fun q => ∑ p, M p q * x p

lemma bil_eq_dot (M : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K) :
    bil M x y = dot4 (colf M x) y := by
  simp only [bil, dot4, colf, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma bil_single (M : Matrix (Fin 4) (Fin 4) K) (p q : Fin 4) :
    bil M (Pi.single p 1) (Pi.single q 1) = M p q := by
  simp [bil, Pi.single_apply]

lemma bil_eq (M : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K) :
    bil M x y = M 0 0 * x 0 * y 0 + M 0 1 * x 0 * y 1 + M 0 2 * x 0 * y 2 + M 0 3 * x 0 * y 3
      + (M 1 0 * x 1 * y 0 + M 1 1 * x 1 * y 1 + M 1 2 * x 1 * y 2 + M 1 3 * x 1 * y 3)
      + (M 2 0 * x 2 * y 0 + M 2 1 * x 2 * y 1 + M 2 2 * x 2 * y 2 + M 2 3 * x 2 * y 3)
      + (M 3 0 * x 3 * y 0 + M 3 1 * x 3 * y 1 + M 3 2 * x 3 * y 2 + M 3 3 * x 3 * y 3) := by
  simp only [bil, Fin.sum_univ_four]

/-- The permanent of the matrix with rows `r0, r1, r2, r3`. -/
def perm4 (r0 r1 r2 r3 : Fin 4 → K) : K := (Matrix.of ![r0, r1, r2, r3]).permanent

lemma permanent_eq_perm4 (A : Matrix (Fin 4) (Fin 4) K) :
    A.permanent = perm4 (A 0) (A 1) (A 2) (A 3) := by
  have : A = Matrix.of ![A 0, A 1, A 2, A 3] := by
    ext i j
    fin_cases i <;> rfl
  rw [perm4, ← this]

/-- The permanent written with the entries `l a * u b + l b * u a` of the slice matrix. -/
lemma perm4_eq (l u x y : Fin 4 → K) :
    perm4 l u x y = (l 2 * u 3 + l 3 * u 2) * (x 0 * y 1 + x 1 * y 0)
      + (l 1 * u 3 + l 3 * u 1) * (x 0 * y 2 + x 2 * y 0)
      + (l 1 * u 2 + l 2 * u 1) * (x 0 * y 3 + x 3 * y 0)
      + (l 0 * u 3 + l 3 * u 0) * (x 1 * y 2 + x 2 * y 1)
      + (l 0 * u 2 + l 2 * u 0) * (x 1 * y 3 + x 3 * y 1)
      + (l 0 * u 1 + l 1 * u 0) * (x 2 * y 3 + x 3 * y 2) := by
  rw [perm4, permanent_fin_four]
  simp
  ring

lemma perm4_swap12 (r0 r1 r2 r3 : Fin 4 → K) : perm4 r0 r2 r1 r3 = perm4 r0 r1 r2 r3 := by
  simp only [perm4_eq]; ring

lemma perm4_swap23 (r0 r1 r2 r3 : Fin 4 → K) : perm4 r0 r1 r3 r2 = perm4 r0 r1 r2 r3 := by
  simp only [perm4_eq]; ring

lemma perm4_swap01 (r0 r1 r2 r3 : Fin 4 → K) : perm4 r1 r0 r2 r3 = perm4 r0 r1 r2 r3 := by
  simp only [perm4_eq]; ring

lemma perm4_swap0213 (r0 r1 r2 r3 : Fin 4 → K) : perm4 r2 r3 r0 r1 = perm4 r0 r1 r2 r3 := by
  simp only [perm4_eq]; ring

lemma perm4_one (w x y : Fin 4 → K) : perm4 (fun _ => 1) w x y = E3 w x y := by
  simp only [perm4_eq, E3_eq]; ring

/-- Scaling the columns by `l` multiplies the permanent by the product of the `l i`. -/
lemma perm4_scale (l w x y : Fin 4 → K) :
    perm4 l (l * w) (l * x) (l * y) = l 0 * l 1 * l 2 * l 3 * E3 w x y := by
  simp only [perm4_eq, E3_eq, Pi.mul_apply]; ring

lemma perm4_comp (σ : Equiv.Perm (Fin 4)) (r0 r1 r2 r3 : Fin 4 → K) :
    perm4 (r0 ∘ σ) (r1 ∘ σ) (r2 ∘ σ) (r3 ∘ σ) = perm4 r0 r1 r2 r3 := by
  have : (Matrix.of ![r0 ∘ σ, r1 ∘ σ, r2 ∘ σ, r3 ∘ σ] : Matrix (Fin 4) (Fin 4) K)
      = (Matrix.of ![r0, r1, r2, r3]).submatrix id σ := by
    ext i j
    fin_cases i <;> rfl
  rw [perm4, this, Matrix.permanent_permute_rows, perm4]

lemma bil_submatrix (σ : Equiv.Perm (Fin 4)) (M : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K) :
    bil (M.submatrix σ σ) (x ∘ σ) (y ∘ σ) = bil M x y := by
  simp only [bil, Matrix.submatrix_apply, Function.comp]
  refine Fintype.sum_equiv σ _ _ fun p => ?_
  exact Fintype.sum_equiv σ _ _ fun q => rfl

lemma injective_vec4_iff (a b c d : Fin 4) :
    Function.Injective ![a, b, c, d] ↔ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · exact absurd (h (a₁ := 0) (a₂ := 1) (by simpa using e)) (by decide)
    · exact absurd (h (a₁ := 0) (a₂ := 2) (by simpa using e)) (by decide)
    · exact absurd (h (a₁ := 0) (a₂ := 3) (by simpa using e)) (by decide)
    · exact absurd (h (a₁ := 1) (a₂ := 2) (by simpa using e)) (by decide)
    · exact absurd (h (a₁ := 1) (a₂ := 3) (by simpa using e)) (by decide)
    · exact absurd (h (a₁ := 2) (a₂ := 3) (by simpa using e)) (by decide)
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; first | exact absurd hij h1 | exact absurd hij h2 | exact absurd hij h3 | exact absurd hij h4 | exact absurd hij h5 | exact absurd hij h6 | exact absurd hij.symm h1 | exact absurd hij.symm h2 | exact absurd hij.symm h3 | exact absurd hij.symm h4 | exact absurd hij.symm h5 | exact absurd hij.symm h6)

/-- The coefficient of the permanent at the column indices `a, b, c, d`. -/
lemma perm4_single (a b c d : Fin 4) :
    perm4 (Pi.single a (1 : K)) (Pi.single b 1) (Pi.single c 1) (Pi.single d 1)
      = if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then 1 else 0 := by
  have e : (Matrix.of ![Pi.single a (1 : K), Pi.single b 1, Pi.single c 1, Pi.single d 1] :
      Matrix (Fin 4) (Fin 4) K) = Matrix.of fun i => (Pi.single (![a, b, c, d] i) 1 : Fin 4 → K) := by
    ext i j
    fin_cases i <;> rfl
  rw [perm4, e]
  by_cases h : Function.Injective ![a, b, c, d]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((injective_vec4_iff a b c d).mp h))]
    have hb : Function.Bijective ![a, b, c, d] := Finite.injective_iff_bijective.mp h
    exact permanent_single_perm (Equiv.ofBijective _ hb)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h ((injective_vec4_iff a b c d).mpr h'))]
    exact permanent_single_of_not_injective _ h

/-! ### Decompositions with a prescribed pattern -/

/-- `Dec4 F0 G0 F1 G1 F2 G2`: the permanent is the sum of the split products
`F0 v (r0, r1) * G0 v (r2, r3)` (pairing `01|23`), `F1 v (r0, r2) * G1 v (r1, r3)` (pairing
`02|13`) and `F2 v (r0, r3) * G2 v (r1, r2)` (pairing `03|12`). -/
def Dec4 {n0 n1 n2 : ℕ} (F0 G0 : Fin n0 → Matrix (Fin 4) (Fin 4) K)
    (F1 G1 : Fin n1 → Matrix (Fin 4) (Fin 4) K) (F2 G2 : Fin n2 → Matrix (Fin 4) (Fin 4) K) :
    Prop :=
  ∀ r0 r1 r2 r3 : Fin 4 → K, perm4 r0 r1 r2 r3 = ∑ v, bil (F0 v) r0 r1 * bil (G0 v) r2 r3
    + ∑ v, bil (F1 v) r0 r2 * bil (G1 v) r1 r3 + ∑ v, bil (F2 v) r0 r3 * bil (G2 v) r1 r2

/-- The permanent is a sum of `n0`, `n1`, `n2` split products of the pairings `01|23`, `02|13`,
`03|12`. -/
def HasDec (K : Type*) [Field K] (n0 n1 n2 : ℕ) : Prop :=
  ∃ (F0 G0 : Fin n0 → Matrix (Fin 4) (Fin 4) K) (F1 G1 : Fin n1 → Matrix (Fin 4) (Fin 4) K)
    (F2 G2 : Fin n2 → Matrix (Fin 4) (Fin 4) K), Dec4 F0 G0 F1 G1 F2 G2

section Sym

variable {n0 n1 n2 : ℕ} {F0 G0 : Fin n0 → Matrix (Fin 4) (Fin 4) K}
  {F1 G1 : Fin n1 → Matrix (Fin 4) (Fin 4) K} {F2 G2 : Fin n2 → Matrix (Fin 4) (Fin 4) K}

/-- Exchange the rows `1` and `2`. -/
lemma Dec4.swap12 (h : Dec4 F0 G0 F1 G1 F2 G2) :
    Dec4 F1 G1 F0 G0 F2 (fun v => (G2 v)ᵀ) := by
  intro r0 r1 r2 r3
  have := h r0 r2 r1 r3
  rw [perm4_swap12] at this
  simp only [bil_transpose]
  linear_combination this

/-- Exchange the rows `2` and `3`. -/
lemma Dec4.swap23 (h : Dec4 F0 G0 F1 G1 F2 G2) :
    Dec4 F0 (fun v => (G0 v)ᵀ) F2 G2 F1 G1 := by
  intro r0 r1 r2 r3
  have := h r0 r1 r3 r2
  rw [perm4_swap23] at this
  simp only [bil_transpose]
  linear_combination this

/-- Exchange the rows `0, 1` and the rows `2, 3`. -/
lemma Dec4.swap0123 (h : Dec4 F0 G0 F1 G1 F2 G2) :
    Dec4 (fun v => (F0 v)ᵀ) (fun v => (G0 v)ᵀ) G1 F1 G2 F2 := by
  intro r0 r1 r2 r3
  have := h r1 r0 r3 r2
  rw [perm4_swap01, perm4_swap23] at this
  simp only [bil_transpose]
  rw [this]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun v _ => mul_comm _ _

/-- Exchange the rows `0, 2` and the rows `1, 3`. -/
lemma Dec4.swap0213 (h : Dec4 F0 G0 F1 G1 F2 G2) :
    Dec4 G0 F0 (fun v => (F1 v)ᵀ) (fun v => (G1 v)ᵀ) (fun v => (G2 v)ᵀ) (fun v => (F2 v)ᵀ) := by
  intro r0 r1 r2 r3
  have := h r2 r3 r0 r1
  rw [perm4_swap0213] at this
  simp only [bil_transpose]
  rw [this]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun v _ => mul_comm _ _

/-- Relabel the columns by a permutation. -/
lemma Dec4.relabel (σ : Equiv.Perm (Fin 4)) (h : Dec4 F0 G0 F1 G1 F2 G2) :
    Dec4 (fun v => (F0 v).submatrix σ σ) (fun v => (G0 v).submatrix σ σ)
      (fun v => (F1 v).submatrix σ σ) (fun v => (G1 v).submatrix σ σ)
      (fun v => (F2 v).submatrix σ σ) (fun v => (G2 v).submatrix σ σ) := by
  intro r0 r1 r2 r3
  have e : ∀ z : Fin 4 → K, (z ∘ σ.symm) ∘ σ = z := fun z => by
    funext i; simp
  have := h (r0 ∘ σ.symm) (r1 ∘ σ.symm) (r2 ∘ σ.symm) (r3 ∘ σ.symm)
  rw [← perm4_comp σ, e, e, e, e] at this
  rw [this]
  have b : ∀ (M : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K),
      bil M (x ∘ σ.symm) (y ∘ σ.symm) = bil (M.submatrix σ σ) x y := fun M x y => by
    rw [← bil_submatrix σ M, e, e]
  simp only [b]

/-- The coefficient identities of a decomposition. -/
lemma Dec4.coeff (h : Dec4 F0 G0 F1 G1 F2 G2) (a b c d : Fin 4) :
    (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : K) else 0)
      = ∑ v, F0 v a b * G0 v c d + ∑ v, F1 v a c * G1 v b d + ∑ v, F2 v a d * G2 v b c := by
  have := h (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) (Pi.single d 1)
  rw [perm4_single] at this
  simpa only [bil_single] using this

end Sym

lemma HasDec.swap12 {n0 n1 n2 : ℕ} (h : HasDec K n0 n1 n2) : HasDec K n1 n0 n2 := by
  obtain ⟨F0, G0, F1, G1, F2, G2, h⟩ := h
  exact ⟨_, _, _, _, _, _, h.swap12⟩

lemma HasDec.swap23 {n0 n1 n2 : ℕ} (h : HasDec K n0 n1 n2) : HasDec K n0 n2 n1 := by
  obtain ⟨F0, G0, F1, G1, F2, G2, h⟩ := h
  exact ⟨_, _, _, _, _, _, h.swap23⟩

/-- A sum of `n` split products (in the sense of `MixedSplitLE`) that equals the permanent
gives a decomposition with some pattern `n0 + n1 + n2 = n`. -/
theorem exists_hasDec_of_mixedSplit {n : ℕ}
    (h : MixedSplitLE 2 n (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent)) :
    ∃ n0 n1 n2 : ℕ, n0 + n1 + n2 = n ∧ HasDec K n0 n1 n2 := by
  classical
  obtain ⟨S, t, hS, ht, hsum⟩ := h
  choose p F G hpFG using fun v =>
    exists_splitTerm_of_isSplit ((ht v).isSplit_of_card_two (hS v))
  let e : ∀ j : Fin 3, {v // p v = j} ≃ Fin (Fintype.card {v // p v = j}) :=
    fun j => Fintype.equivFin _
  refine ⟨Fintype.card {v // p v = 0}, Fintype.card {v // p v = 1}, Fintype.card {v // p v = 2},
    ?_, fun w => F ((e 0).symm w), fun w => G ((e 0).symm w), fun w => F ((e 1).symm w),
    fun w => G ((e 1).symm w), fun w => F ((e 2).symm w), fun w => G ((e 2).symm w), ?_⟩
  · have := Fintype.sum_fiberwise p (fun _ => (1 : ℕ))
    simpa [Fin.sum_univ_three] using this
  · intro r0 r1 r2 r3
    have hA := hsum (Matrix.of ![r0, r1, r2, r3])
    simp only [hpFG] at hA
    rw [← Fintype.sum_fiberwise p, Fin.sum_univ_three] at hA
    rw [perm4, hA]
    congr 1
    · congr 1
      · rw [← (e 0).symm.sum_comp]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [((e 0).symm w).2]
        rfl
      · rw [← (e 1).symm.sum_comp]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [((e 1).symm w).2]
        rfl
    · rw [← (e 2).symm.sum_comp]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [((e 2).symm w).2]
      rfl

/-! ### Linear algebra tools -/

/-- A square matrix that is a sum of fewer rank-one matrices than its size has determinant
zero. -/
lemma det_sum_rank_one_lt {n : ℕ} {ι : Type*} [Fintype ι] (hι : Fintype.card ι < n)
    (P Q : ι → Fin n → K) :
    Matrix.det (Matrix.of fun k k' : Fin n => ∑ v, P v k * Q v k') = 0 := by
  classical
  by_contra hdet
  let A : Matrix (Fin n) ι K := Matrix.of fun k v => P v k
  let B : Matrix ι (Fin n) K := Matrix.of fun v k' => Q v k'
  have hAB : (Matrix.of fun k k' : Fin n => ∑ v, P v k * Q v k') = A * B := by
    ext k k'
    simp [A, B, Matrix.mul_apply]
  rw [hAB] at hdet
  have hu : IsUnit (A * B) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have h1 := Matrix.rank_of_isUnit (A * B) hu
  have h2 := Matrix.rank_mul_le_left A B
  have h3 := Matrix.rank_le_card_width A
  rw [Fintype.card_fin] at h1
  omega

/-- The identity matrix of size `n` is not a sum of fewer than `n` rank-one matrices. -/
lemma rank_contra {n : ℕ} {ι : Type*} [Fintype ι] (hι : Fintype.card ι < n)
    (P Q : ι → Fin n → K)
    (h : ∀ k k' : Fin n, (if k = k' then (1 : K) else 0) = ∑ v, P v k * Q v k') : False := by
  have := det_sum_rank_one_lt hι P Q
  have e : (Matrix.of fun k k' : Fin n => ∑ v, P v k * Q v k') = 1 := by
    ext k k'
    rw [Matrix.of_apply, ← h, Matrix.one_apply]
  rw [e, Matrix.det_one] at this
  exact one_ne_zero this

/-- **Kernel lemma.** If a form `B` is a sum of `r` rank-one forms `α t ⊗ β t` and has a
nonzero `r × r` minor, then every `α t` vanishes on the left kernel of `B` and every `β t`
vanishes on the right kernel. -/
lemma kernel_of_minor {r : ℕ} (B : (Fin 4 → K) → (Fin 4 → K) → K)
    (α β : Fin r → (Fin 4 → K) → K) (hB : ∀ x y, B x y = ∑ t, α t x * β t y)
    (p q : Fin r → Fin 4 → K) (hdet : Matrix.det (Matrix.of fun i j => B (p i) (q j)) ≠ 0)
    (z : Fin 4 → K) :
    ((∀ y, B z y = 0) → ∀ t, α t z = 0) ∧ ((∀ x, B x z = 0) → ∀ t, β t z = 0) := by
  let A : Matrix (Fin r) (Fin r) K := Matrix.of fun i t => α t (p i)
  let Bm : Matrix (Fin r) (Fin r) K := Matrix.of fun t j => β t (q j)
  have hAB : (Matrix.of fun i j => B (p i) (q j)) = A * Bm := by
    ext i j
    simp [A, Bm, Matrix.mul_apply, hB]
  rw [hAB, Matrix.det_mul] at hdet
  have hA : A.det ≠ 0 := left_ne_zero_of_mul hdet
  have hBm : Bm.det ≠ 0 := right_ne_zero_of_mul hdet
  constructor
  · intro hz
    have : (fun t => α t z) ᵥ* Bm = 0 := by
      funext j
      simp only [Matrix.vecMul, dotProduct, Bm, Matrix.of_apply, Pi.zero_apply]
      rw [← hB]
      exact hz _
    intro t
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hBm this) t
  · intro hz
    have : A *ᵥ (fun t => β t z) = 0 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Pi.zero_apply]
      rw [← hB]
      exact hz _
    intro t
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA this) t

/-- The vector `e_i + a e_k + b e_m`. -/
def chartVec (i k m : Fin 4) (a b : K) : Fin 4 → K :=
  Pi.single i 1 + a • Pi.single k 1 + b • Pi.single m 1

lemma dot4_chartVec (c : Fin 4 → K) (i k m : Fin 4) (a b : K) :
    dot4 c (chartVec i k m a b) = c i + a * c k + b * c m := by
  simp [dot4, chartVec, mul_add, Finset.sum_add_distrib, Pi.single_apply]
  ring

lemma exists_compl_two : ∀ k m : Fin 4, k ≠ m →
    ∃ i j : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m := by
  decide

lemma exists_compl_one : ∀ m : Fin 4,
    ∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m := by
  decide

/-- **Chart lemma.** The common kernel of two covectors contains two vectors in echelon form
`e_i + a e_k + b e_m`, `e_j + c e_k + d e_m` for some labelling `i, j, k, m` of the
coordinates. -/
lemma exists_chart (c1 c2 : Fin 4 → K) :
    ∃ i j k m : Fin 4, (i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m) ∧ ∃ a b c d : K,
      dot4 c1 (chartVec i k m a b) = 0 ∧ dot4 c2 (chartVec i k m a b) = 0 ∧
      dot4 c1 (chartVec j k m c d) = 0 ∧ dot4 c2 (chartVec j k m c d) = 0 := by
  by_cases h : ∃ k m, c1 k * c2 m - c1 m * c2 k ≠ 0
  · obtain ⟨k, m, hΔ⟩ := h
    have hkm : k ≠ m := by
      rintro rfl
      exact hΔ (by ring)
    obtain ⟨i, j, hd⟩ := exists_compl_two k m hkm
    obtain ⟨Δ, hΔ'⟩ : ∃ Δ, Δ = c1 k * c2 m - c1 m * c2 k := ⟨_, rfl⟩
    rw [← hΔ'] at hΔ
    refine ⟨i, j, k, m, hd, -(c1 i * c2 m - c1 m * c2 i) / Δ, -(c1 k * c2 i - c1 i * c2 k) / Δ,
      -(c1 j * c2 m - c1 m * c2 j) / Δ, -(c1 k * c2 j - c1 j * c2 k) / Δ, ?_, ?_, ?_, ?_⟩ <;>
    · rw [dot4_chartVec]
      field_simp
      rw [hΔ']
      ring
  · push Not at h
    have single : ∀ c c' : Fin 4 → K, (∀ k m, c k * c' m - c m * c' k = 0) → ∀ m, c m ≠ 0 →
        ∃ i j k m : Fin 4, (i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m) ∧ ∃ a b c₀ d : K,
          dot4 c (chartVec i k m a b) = 0 ∧ dot4 c' (chartVec i k m a b) = 0 ∧
          dot4 c (chartVec j k m c₀ d) = 0 ∧ dot4 c' (chartVec j k m c₀ d) = 0 := by
      intro c c' hcc m hm
      obtain ⟨i, j, k, hd⟩ := exists_compl_one m
      refine ⟨i, j, k, m, hd, 0, -c i / c m, 0, -c j / c m, ?_, ?_, ?_, ?_⟩
      · rw [dot4_chartVec]
        field_simp
        ring
      · rw [dot4_chartVec]
        field_simp
        linear_combination hcc m i
      · rw [dot4_chartVec]
        field_simp
        ring
      · rw [dot4_chartVec]
        field_simp
        linear_combination hcc m j
    by_cases h1 : ∃ m, c1 m ≠ 0
    · obtain ⟨m, hm⟩ := h1
      exact single c1 c2 h m hm
    · by_cases h2 : ∃ m, c2 m ≠ 0
      · obtain ⟨m, hm⟩ := h2
        obtain ⟨i, j, k, m, hd, a, b, c, d, e1, e2, e3, e4⟩ :=
          single c2 c1 (fun k m => by linear_combination -(h k m)) m hm
        exact ⟨i, j, k, m, hd, a, b, c, d, e2, e1, e4, e3⟩
      · push Not at h1 h2
        refine ⟨0, 1, 2, 3, by decide, 0, 0, 0, 0, ?_, ?_, ?_, ?_⟩ <;>
        · rw [dot4_chartVec]
          simp [h1, h2]

lemma all_four {i j k m : Fin 4} (hd : i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m)
    (x : Fin 4) : x = i ∨ x = j ∨ x = k ∨ x = m := by
  revert i j k m x
  decide

/-! ### Polynomial conditions on the torus -/

/-- A polynomial function of four variables. -/
def IsPoly (f : (Fin 4 → K) → K) : Prop :=
  ∃ p : MvPolynomial (Fin 4) K, ∀ l, MvPolynomial.eval l p = f l

lemma IsPoly.const (c : K) : IsPoly (fun _ : Fin 4 → K => c) :=
  ⟨MvPolynomial.C c, fun l => by simp⟩

lemma IsPoly.coord (i : Fin 4) : IsPoly (fun l : Fin 4 → K => l i) :=
  ⟨MvPolynomial.X i, fun l => by simp⟩

lemma IsPoly.add {f g : (Fin 4 → K) → K} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (fun l => f l + g l) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun l => by simp [hp, hq]⟩

lemma IsPoly.mul {f g : (Fin 4 → K) → K} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (fun l => f l * g l) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun l => by simp [hp, hq]⟩

lemma IsPoly.sub {f g : (Fin 4 → K) → K} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (fun l => f l - g l) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun l => by simp [hp, hq]⟩

lemma IsPoly.sum {ι : Type*} (s : Finset ι) (f : ι → (Fin 4 → K) → K) (hf : ∀ i, IsPoly (f i)) :
    IsPoly (fun l => ∑ i ∈ s, f i l) := by
  choose p hp using hf
  exact ⟨∑ i ∈ s, p i, fun l => by simp [hp]⟩

lemma IsPoly.bil (M : Matrix (Fin 4) (Fin 4) K) (x y : (Fin 4 → K) → Fin 4 → K)
    (hx : ∀ p, IsPoly (fun l => x l p)) (hy : ∀ q, IsPoly (fun l => y l q)) :
    IsPoly (fun l => bil M (x l) (y l)) := by
  unfold PvsNP.bil
  exact IsPoly.sum _ _ fun p => IsPoly.sum _ _ fun q =>
    ((IsPoly.const (M p q)).mul (hx p)).mul (hy q)

/-- `l ↦ bil M l (l * w)` is a polynomial function. -/
lemma IsPoly.bil_mul (M : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → K) :
    IsPoly (fun l => PvsNP.bil M l (l * w)) :=
  IsPoly.bil M (fun l => l) (fun l => l * w) (fun p => IsPoly.coord p)
    (fun q => (IsPoly.coord q).mul (IsPoly.const (w q)))

/-- **Finitely many polynomial conditions on the torus.** If at every point `l` with all
coordinates nonzero one of finitely many systems of polynomial equations holds, then one of the
systems holds identically. -/
theorem poly_union [Infinite K] {ι : Type*} [Fintype ι] {J : Type*} (C : ι → Prop)
    (f : ι → J → (Fin 4 → K) → K) (hf : ∀ n j, IsPoly (f n j))
    (h : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) → ∃ n, C n ∧ ∀ j, f n j l = 0) :
    ∃ n, C n ∧ ∀ j l, f n j l = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have key : ∀ n, ∃ g : MvPolynomial (Fin 4) K, g ≠ 0 ∧
      ∀ l, MvPolynomial.eval l g ≠ 0 → C n → ∃ j, f n j l ≠ 0 := by
    intro n
    by_cases hC : C n
    · obtain ⟨j, l0, hl0⟩ := hcon n hC
      obtain ⟨p, hp⟩ := hf n j
      refine ⟨p, ?_, fun l hl _ => ⟨j, by rwa [← hp l]⟩⟩
      rintro rfl
      apply hl0
      rw [← hp l0]
      simp
    · exact ⟨1, one_ne_zero, fun l _ hC' => absurd hC' hC⟩
  choose g hg0 hg using key
  have hQ : (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) * ∏ n, g n ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero i)
      (Finset.prod_ne_zero_iff.mpr fun n _ => hg0 n)
  have : ∃ l, MvPolynomial.eval l
      ((∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) * ∏ n, g n) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hQ (MvPolynomial.funext fun l => by rw [hall l]; simp)
  obtain ⟨l, hl⟩ := this
  rw [map_mul, MvPolynomial.eval_prod, MvPolynomial.eval_prod] at hl
  have h1 := left_ne_zero_of_mul hl
  have h2 := right_ne_zero_of_mul hl
  rw [Finset.prod_ne_zero_iff] at h1 h2
  obtain ⟨n, hC, hn⟩ := h l (fun i => by simpa using h1 i (Finset.mem_univ i))
  obtain ⟨j, hj⟩ := hg n l (h2 n (Finset.mem_univ n)) hC
  exact hj (hn j)

/-- A polynomial function that vanishes on the torus vanishes everywhere. -/
theorem torus_ext [Infinite K] {f : (Fin 4 → K) → K} (hf : IsPoly f)
    (h : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) → f l = 0) : ∀ l, f l = 0 := by
  obtain ⟨-, -, h'⟩ := poly_union (ι := Unit) (J := Unit) (fun _ => True) (fun _ _ => f)
    (fun _ _ => hf) (fun l hl => ⟨(), trivial, fun _ => h l hl⟩)
  exact h' ()

end Base

end PvsNP
