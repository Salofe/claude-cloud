import PvsNP.FourByFourExactPencil

/-!
# Exact five-term bound, patterns `(3,2,0)` and `(2,2,1)`

Both patterns contain a pairing with exactly two terms. By `Dec4.pencil_cases` the two forms of
that pairing either have two vanishing columns or lie in `span(alt_ab, s_cd)`.

* `no_dec_320`: in both cases a `4 × 4` minor of a flattening contradicts the three terms of
  the other pairing.
* `no_dec_221`: the first case is impossible (`no221_C`); in the second case the kernel lemma
  forces the other forms into a space `InN` (`n221_N`), and two coefficients of the permanent
  give `1 = 0` or `1 = -1` (`no221_S`).
-/

namespace PvsNP

open Matrix

section PatternsB

variable {K : Type*} [Field K]

/-! ### Pattern `(3,2,0)` -/

/-- Index data for `no230_C`. -/
def qa : Fin 4 → Fin 4 := ![2, 1, 1, 0]
/-- See `qa`. -/
def qb : Fin 4 → Fin 4 := ![3, 3, 2, 3]
/-- See `qa`. -/
def qc : Fin 4 → Fin 4 := ![0, 0, 0, 1]
/-- See `qa`. -/
def qd : Fin 4 → Fin 4 := ![1, 2, 3, 2]

lemma idxC : ∀ k k' : Fin 4, (qa k ≠ qc k' ∧ qa k ≠ qb k ∧ qa k ≠ qd k' ∧ qc k' ≠ qb k ∧
    qc k' ≠ qd k' ∧ qb k ≠ qd k') ↔ k = k' := by
  decide

lemma qc_cases : ∀ k' : Fin 4, qc k' = 0 ∨ qc k' = 1 := by decide

lemma no230_C {F0 G0 : Fin 2 → Matrix (Fin 4) (Fin 4) K} {F1 G1 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F2 G2 : Fin 0 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hC : ∀ v p, F0 v p 0 = 0 ∧ F0 v p 1 = 0) : False := by
  refine rank_contra (n := 4) (ι := Fin 3) (by simp) (fun v k => F1 v (qa k) (qb k))
    (fun v k' => G1 v (qc k') (qd k')) fun k k' => ?_
  have := h.coeff (qa k) (qc k') (qb k) (qd k')
  have hz : ∀ v, F0 v (qa k) (qc k') = 0 := by
    intro v
    rcases qc_cases k' with e | e <;> rw [e]
    · exact (hC v _).1
    · exact (hC v _).2
  simp only [hz, zero_mul, Finset.sum_const_zero, zero_add, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero] at this
  rw [← this]
  simp only [idxC k k']

/-- Index data for `no230_S`. -/
def sa : Fin 4 → Fin 4 := ![0, 0, 1, 1]
/-- See `sa`. -/
def sb : Fin 4 → Fin 4 := ![2, 3, 2, 3]
/-- See `sa`. -/
def sc : Fin 4 → Fin 4 := ![3, 2, 3, 2]
/-- See `sa`. -/
def sd : Fin 4 → Fin 4 := ![1, 1, 0, 0]

lemma idxS : ∀ k k' : Fin 4, (sa k ≠ sc k' ∧ sa k ≠ sb k ∧ sa k ≠ sd k' ∧ sc k' ≠ sb k ∧
    sc k' ≠ sd k' ∧ sb k ≠ sd k') ↔ k = k' := by
  decide

lemma sa_sc_cases : ∀ k k' : Fin 4, (sa k = 0 ∨ sa k = 1) ∧ (sc k' = 2 ∨ sc k' = 3) := by decide

lemma no230_S {F0 G0 : Fin 2 → Matrix (Fin 4) (Fin 4) K} {F1 G1 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F2 G2 : Fin 0 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hS : ∀ v, InPair 0 1 2 3 (F0 v)) : False := by
  refine rank_contra (n := 4) (ι := Fin 3) (by simp) (fun v k => F1 v (sa k) (sb k))
    (fun v k' => G1 v (sc k') (sd k')) fun k k' => ?_
  have := h.coeff (sa k) (sc k') (sb k) (sd k')
  have hz : ∀ v, F0 v (sa k) (sc k') = 0 := by
    intro v
    obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, -, -, -, -⟩ := hS v
    obtain ⟨e1 | e1, e2 | e2⟩ := sa_sc_cases k k' <;> rw [e1, e2] <;> assumption
  simp only [hz, zero_mul, Finset.sum_const_zero, zero_add, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero] at this
  rw [← this]
  simp only [idxS k k']

theorem no_dec_230 [CharZero K] : ¬ HasDec K 2 3 0 := by
  rintro ⟨F0, G0, F1, G1, F2, G2, h⟩
  obtain ⟨σ, hC | hS⟩ := h.pencil_cases (by norm_num)
  · exact no230_C (h.relabel σ) hC
  · exact no230_S (h.relabel σ) hS

/-- **Pattern `(3,2,0)`.** -/
theorem no_dec_320 [CharZero K] : ¬ HasDec K 3 2 0 := fun h => no_dec_230 h.swap12

/-! ### Pattern `(2,2,1)` -/

lemma eq_zero_of_rank_one {x y x' y' B : K} (h1 : x * y' = B) (h2 : x' * y = B)
    (h3 : x * y = 0) : B = 0 := by
  have : B * B = 0 := by
    calc B * B = (x * y') * (x' * y) := by rw [h1, h2]
      _ = (x * y) * (x' * y') := by ring
      _ = 0 := by rw [h3, zero_mul]
  exact mul_self_eq_zero.mp this

/-- The two forms of a doubled pairing cannot both have two vanishing columns. -/
lemma no221_C {F0 G0 F1 G1 : Fin 2 → Matrix (Fin 4) (Fin 4) K}
    {F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hC : ∀ v p, F0 v p 0 = 0 ∧ F0 v p 1 = 0) : False := by
  obtain ⟨u, hu, h1, h2, h3⟩ := exists_common_zero (colf (G1 0) ![1, 1, 0, 0])
    (colf (G1 1) ![1, 1, 0, 0]) (Pi.single 0 1)
  rw [← bil_eq_dot] at h1 h2
  have hu0 : u 0 = 0 := by simpa [dot4_eq, Pi.single_apply] using h3
  have hF : ∀ v (r0 : Fin 4 → K), bil (F0 v) r0 ![1, 1, 0, 0] = 0 := by
    intro v r0
    rw [bil_eq]
    simp [(hC v _).1, (hC v _).2]
  have hB : ∀ r0 r2 : Fin 4 → K,
      perm4 r0 ![1, 1, 0, 0] r2 u = bil (F2 0) r0 u * bil (G2 0) ![1, 1, 0, 0] r2 := by
    intro r0 r2
    rw [h r0 ![1, 1, 0, 0] r2 u]
    simp [Fin.sum_univ_two, hF, h1, h2]
  have key : ∀ x y : Fin 4 → K, perm4 x ![1, 1, 0, 0] x u = 0 →
      perm4 x ![1, 1, 0, 0] y u = 0 := by
    intro x y hx
    refine eq_zero_of_rank_one (x := bil (F2 0) x u) (y' := bil (G2 0) ![1, 1, 0, 0] y)
      (x' := bil (F2 0) y u) (y := bil (G2 0) ![1, 1, 0, 0] x) (hB x y).symm ?_ ?_
    · rw [← hB y x]
      simp only [perm4_eq]
      ring
    · rw [← hB x x]
      exact hx
  have e3 : u 3 = 0 := by
    have := key (Pi.single 0 1) (Pi.single 2 1) (by simp [perm4_eq])
    simpa [perm4_eq, Pi.single_apply] using this
  have e2 : u 2 = 0 := by
    have := key (Pi.single 0 1) (Pi.single 3 1) (by simp [perm4_eq])
    simpa [perm4_eq, Pi.single_apply] using this
  have e1 : u 1 = 0 := by
    have := key (Pi.single 2 1) (Pi.single 3 1) (by simp [perm4_eq])
    simpa [perm4_eq, Pi.single_apply, hu0] using this
  exact hu (funext fun i => by fin_cases i <;> simp [hu0, e1, e2, e3])

/-- `InN M`: `M (l, l_0 e_0 - l_1 e_1) = 0` for all `l`; the columns `0, 1` of `M` are those of
a multiple of `s_01`. -/
def InN (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  M 0 0 = 0 ∧ M 1 1 = 0 ∧ M 1 0 = M 0 1 ∧ M 2 0 = 0 ∧ M 3 0 = 0 ∧ M 2 1 = 0 ∧ M 3 1 = 0

lemma inN_of_cv (M : Matrix (Fin 4) (Fin 4) K) (h : ∀ l, cv M l 0 - cv M l 1 = 0) : InN M := by
  obtain ⟨A1, A2, A3, A4⟩ := quad2 M (x := 0) (y := 1) (by decide) 1 (-1) (fun l => by
    linear_combination h l)
  have A2' := A4 2 (by decide) (by decide)
  have A3' := A4 3 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination A1
  · linear_combination -A2
  · linear_combination A3
  · linear_combination A2'.1
  · linear_combination A3'.1
  · linear_combination -A2'.2
  · linear_combination -A3'.2

lemma inN_of_kernel [CharZero K] (M : Matrix (Fin 4) (Fin 4) K)
    (h : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) → bil M l (l * ![1, -1, 0, 0]) = 0) : InN M := by
  have : Infinite K := CharZero.infinite K
  have h' := torus_ext (IsPoly.bil_mul M ![1, -1, 0, 0]) h
  refine inN_of_cv M fun l => ?_
  have := h' l
  rw [← dot4_cv] at this
  have e : dot4 (cv M l) ![1, -1, 0, 0] = cv M l 0 - cv M l 1 := by
    simp [dot4_eq]
    ring
  rw [e] at this
  exact this

/-- **Kernel step.** If the pencil of the pairing `01|23` lies in `span(alt_01, s_23)`, all
the forms `F1 v` and `F2 0` satisfy `InN`. -/
lemma n221_N [CharZero K] {F0 G0 F1 G1 : Fin 2 → Matrix (Fin 4) (Fin 4) K}
    {F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hS : ∀ v, InPair 0 1 2 3 (F0 v)) : (∀ v, InN (F1 v)) ∧ InN (F2 0) := by
  have key : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) →
      (∀ v, bil (F1 v) l (l * ![1, -1, 0, 0]) = 0) ∧ bil (F2 0) l (l * ![1, -1, 0, 0]) = 0 := by
    intro l hl
    have hF : ∀ v, bil (F0 v) l (l * ![1, 1, 0, 0]) = 0 := by
      intro v
      obtain ⟨h1, h2, -, -, h5, -, -, -, -, -, h11, h12, h13, h14⟩ := hS v
      rw [← dot4_cv]
      simp [dot4_eq, cv, colf, Fin.sum_univ_four]
      linear_combination (l 0 * l 0) * h1 + (l 1 * l 0) * h5 + (l 2 * l 0) * h11
        + (l 3 * l 0) * h13 + (l 1 * l 1) * h2 + (l 2 * l 1) * h12 + (l 3 * l 1) * h14
    have hB : ∀ x y, perm4 l (l * ![1, 1, 0, 0]) x y
        = ∑ t : Fin 3, (![bil (F1 0) l, bil (F1 1) l, bil (G2 0) (l * ![1, 1, 0, 0])] :
            Fin 3 → (Fin 4 → K) → K) t x *
          (![bil (G1 0) (l * ![1, 1, 0, 0]), bil (G1 1) (l * ![1, 1, 0, 0]), bil (F2 0) l] :
            Fin 3 → (Fin 4 → K) → K) t y := by
      intro x y
      rw [h l _ x y, Fin.sum_univ_two, hF 0, hF 1, Fin.sum_univ_two, Fin.sum_univ_three]
      simp
      ring
    have hk := scaled_kernel l hl ![1, 1, 0, 0] _ _ hB
      ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
      (by
        rw [Matrix.det_fin_three]
        simp [E3_eq]) ![1, -1, 0, 0] (fun y => by
        simp [E3_eq])
    refine ⟨fun v => ?_, (hk 2).2⟩
    fin_cases v
    · exact (hk 0).1
    · exact (hk 1).1
  exact ⟨fun v => inN_of_kernel _ fun l hl => (key l hl).1 v,
    inN_of_kernel _ fun l hl => (key l hl).2⟩

lemma D4_cases01 : ∀ a b c d : Fin 4, D4 a b c d →
    ((a = 0 ∨ b = 0) ∧ (c = 1 ∨ d = 1)) ∨ ((a = 1 ∨ b = 1) ∧ (c = 0 ∨ d = 0)) ∨
    ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∨ ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) := by
  decide

/-- Two forms in `span(alt_ab, s_cd)` whose entries `(0,1)` and `(1,0)` agree: either these
entries vanish, or the entries `(2,3)` and `(3,2)` are opposite. -/
lemma inPair_dichotomy [CharZero K] {a b c d : Fin 4} (hd : D4 a b c d)
    (M : Fin 2 → Matrix (Fin 4) (Fin 4) K) (hS : ∀ v, InPair a b c d (M v))
    (hsym : ∀ v, M v 1 0 = M v 0 1) :
    (∀ v, M v 0 1 = 0) ∨ (∀ v, M v 3 2 = -M v 2 3) := by
  rcases D4_cases01 a b c d hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h | h
  · left
    intro v
    obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, -, -, -, -⟩ := hS v
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> assumption
  · left
    intro v
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, h12, h13, h14⟩ := hS v
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> assumption
  · left
    intro v
    obtain ⟨-, -, -, -, h5, -, -, -, -, -, -, -, -, -⟩ := hS v
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    have hv := hsym v
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : (2 : K) * M v 0 1 = 0 := by linear_combination h5 - hv
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : K) * M v 0 1 = 0 := by linear_combination h5 - hv
      exact (mul_eq_zero.mp this).resolve_left h2
  · right
    intro v
    obtain ⟨-, -, -, -, h5, -, -, -, -, -, -, -, -, -⟩ := hS v
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h5
    · linear_combination h5

/-- The pencil of a doubled pairing cannot lie in `span(alt_01, s_23)`. -/
lemma no221_S [CharZero K] {F0 G0 F1 G1 : Fin 2 → Matrix (Fin 4) (Fin 4) K}
    {F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hS : ∀ v, InPair 0 1 2 3 (F0 v)) : False := by
  obtain ⟨hN1, hN2⟩ := n221_N h hS
  obtain ⟨hN3, hN4⟩ := n221_N h.swap0123 (fun v => (hS v).transpose)
  have h12 := h.swap12
  rcases weakS F1 (fun l hl w h0 h1 => h12.pencil_sigma (by norm_num) l hl w h0 h1) with
    ⟨i, j, hij, hC⟩ | ⟨a, b, c, d, hd, hS1⟩
  · obtain ⟨σ, h0, h1⟩ := exists_perm_01 i j hij
    exact no221_C (h12.relabel σ) (fun v p => by
      simp only [Matrix.submatrix_apply, h0, h1]
      exact hC v (σ p))
  · have E1 : (1 : K) = F0 0 0 2 * G0 0 1 3 + F0 1 0 2 * G0 1 1 3
        + (F1 0 0 1 * G1 0 2 3 + F1 1 0 1 * G1 1 2 3) + F2 0 0 3 * G2 0 2 1 := by
      simpa [Fin.sum_univ_two] using h.coeff 0 2 1 3
    have E2 : (1 : K) = F0 0 2 0 * G0 0 3 1 + F0 1 2 0 * G0 1 3 1
        + (F1 0 2 3 * G1 0 0 1 + F1 1 2 3 * G1 1 0 1) + F2 0 2 1 * G2 0 0 3 := by
      simpa [Fin.sum_univ_two] using h.coeff 2 0 3 1
    have E3 : (1 : K) = F0 0 3 0 * G0 0 2 1 + F0 1 3 0 * G0 1 2 1
        + (F1 0 3 2 * G1 0 0 1 + F1 1 3 2 * G1 1 0 1) + F2 0 3 1 * G2 0 0 2 := by
      simpa [Fin.sum_univ_two] using h.coeff 3 0 2 1
    obtain ⟨-, -, -, -, -, -, a7, -, -, -, a11, -, a13, -⟩ := hS 0
    obtain ⟨-, -, -, -, -, -, b7, -, -, -, b11, -, b13, -⟩ := hS 1
    obtain ⟨-, -, -, -, -, f21, f31⟩ := hN2
    obtain ⟨-, -, -, -, -, g21, -⟩ := hN4
    rcases inPair_dichotomy hd F1 hS1 (fun v => (hN1 v).2.2.1) with hz | ha
    · have : (1 : K) = 0 := by
        linear_combination E1 + G0 0 1 3 * a7 + G0 1 1 3 * b7 + G1 0 2 3 * hz 0 + G1 1 2 3 * hz 1
          + F2 0 0 3 * g21
      exact one_ne_zero this
    · have : (2 : K) = 0 := by
        linear_combination E2 + E3 + G0 0 3 1 * a11 + G0 1 3 1 * b11 + G0 0 2 1 * a13
          + G0 1 2 1 * b13 + G1 0 0 1 * ha 0 + G1 1 0 1 * ha 1 + G2 0 0 3 * f21 + G2 0 0 2 * f31
      exact two_ne_zero this

/-- **Pattern `(2,2,1)`.** -/
theorem no_dec_221 [CharZero K] : ¬ HasDec K 2 2 1 := by
  rintro ⟨F0, G0, F1, G1, F2, G2, h⟩
  obtain ⟨σ, hC | hS⟩ := h.pencil_cases (by norm_num)
  · exact no221_C (h.relabel σ) hC
  · exact no221_S (h.relabel σ) hS

end PatternsB

end PvsNP
