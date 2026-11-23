import PvsNP.FiveTerm

/-!
# Lower bounds for mixed split decompositions of the `4 × 4` permanent

PLACEHOLDER
-/

namespace PvsNP

open Matrix

section TwoBlock

variable {K : Type*} [Field K]

/-- Coefficient table of the symmetric form `s = x₀ y₁ + x₁ y₀` on a block of two columns. -/
def ne2 (a b : Fin 2) : K := if a = b then 0 else 1

/-- `Γ(c) = c₁ s(01) s(23) + c₂ s(02) s(13) + c₃ s(03) s(12)` as a tensor in `(K²)^{⊗4}`. -/
def gammaT (c₁ c₂ c₃ : K) (a b c d : Fin 2) : K :=
  c₁ * (ne2 a b * ne2 c d) + c₂ * (ne2 a c * ne2 b d) + c₃ * (ne2 a d * ne2 b c)

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

theorem gamma_split_02 (h2 : (2 : K) ≠ 0) (c₁ c₂ c₃ : K) (F G : Fin 2 → Fin 2 → K)
    (h : ∀ a b c d, gammaT c₁ c₂ c₃ a b c d = F a c * G b d) :
    c₁ + c₃ = 0 ∧ c₂ * c₁ = 0 := by
  apply gamma_split_01 h2 c₂ c₁ c₃ F G
  intro a b c d
  rw [← h a c b d]
  simp only [gammaT, ne2]
  have : (if c = b then (0:K) else 1) = if b = c then 0 else 1 := by simp [eq_comm]
  rw [this]; ring

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

/-- T1 -/
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

/-- core of the (2,1,1) case -/
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

/-- **The two-block model needs five terms at `4 × 4`.** -/
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

end PvsNP
