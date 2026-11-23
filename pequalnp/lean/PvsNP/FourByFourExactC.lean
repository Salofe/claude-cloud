import PvsNP.FourByFourExactB

/-!
# Exact five-term bound, pattern `(3,1,1)`

The pairing `01|23` carries three terms. For `l` with nonzero coordinates there is `u ≠ 0` with
`F0 v (l, u) = 0` for the three forms, and then the slice matrix `B^l_u` has rank at most two.
This happens only at the ten nodes (`node_of_rank2`), so one node works for all `l`
(`triple_type`). At a node the slice matrix has rank exactly two and the kernel lemma puts the
two single forms `F1 0`, `F2 0` in `span(alt_ab, s_cd)` (pair node) or in the forms supported
on one column (star node): `Dec4.triple_cases`. The same analysis for the rows `2, 3` and a few
coefficients of the permanent give a contradiction: `no_dec_311`.
-/

namespace PvsNP

open Matrix

section PatternC

variable {K : Type*} [Field K]

/-- The `3 × 3` minor of `A` with rows `p` and columns `q`. -/
def minor3 (A : Matrix (Fin 4) (Fin 4) K) (p q : Fin 3 → Fin 4) : K :=
  A (p 0) (q 0) * A (p 1) (q 1) * A (p 2) (q 2) - A (p 0) (q 0) * A (p 1) (q 2) * A (p 2) (q 1)
    - A (p 0) (q 1) * A (p 1) (q 0) * A (p 2) (q 2) + A (p 0) (q 1) * A (p 1) (q 2) * A (p 2) (q 0)
    + A (p 0) (q 2) * A (p 1) (q 0) * A (p 2) (q 1) - A (p 0) (q 2) * A (p 1) (q 1) * A (p 2) (q 0)

lemma minor3_eq_det (A : Matrix (Fin 4) (Fin 4) K) (p q : Fin 3 → Fin 4) :
    minor3 A p q = (A.submatrix p q).det := by
  rw [Matrix.det_fin_three]
  rfl

/-- If a nonzero multiple of `B_w` is a sum of two rank-one matrices, all `3 × 3` minors of
`B_w` vanish. -/
lemma minors_of_rank2 (w : Fin 4 → K) (c : K) (hc : c ≠ 0) (P Q : Fin 2 → Fin 4 → K)
    (h : ∀ i j : Fin 4, c * E3 w (Pi.single i 1) (Pi.single j 1) = ∑ t, P t i * Q t j)
    (p q : Fin 3 → Fin 4) : minor3 (Bmat w) p q = 0 := by
  have hdet := det_sum_rank_one_lt (n := 3) (ι := Fin 2) (by simp) (fun t i => P t (p i))
    (fun t j => Q t (q j))
  have e : (Matrix.of fun i j : Fin 3 => ∑ t, P t (p i) * Q t (q j))
      = c • (Bmat w).submatrix p q := by
    ext i j
    rw [Matrix.of_apply, ← h, Matrix.smul_apply, Matrix.submatrix_apply, Bmat_apply, smul_eq_mul]
  rw [e, Matrix.det_smul, Fintype.card_fin] at hdet
  rw [minor3_eq_det]
  exact (mul_eq_zero.mp hdet).resolve_left (pow_ne_zero 3 hc)

/-- **The ten nodes.** If all `3 × 3` minors of the slice matrix `B_w` vanish, then `w` is a
multiple of `e_a - e_b` or of `e_a - e_b - e_c - e_d` for some labelling of the coordinates. -/
lemma node_of_rank2 [CharZero K] (w : Fin 4 → K)
    (hm : ∀ p q : Fin 3 → Fin 4, minor3 (Bmat w) p q = 0) :
    ∃ a b c d : Fin 4, D4 a b c d ∧ ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨
      (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) := by
  have p0 : (w 0 + w 1) * (w 0 + w 2) * (w 0 + w 3) = 0 := by
    have m : 0 * 0 * 0 - 0 * (w 0 + w 1) * (w 0 + w 1) - (w 0 + w 3) * (w 0 + w 3) * 0 + (w 0 + w 3) * (w 0 + w 1) * (w 0 + w 2) + (w 0 + w 2) * (w 0 + w 3) * (w 0 + w 1) - (w 0 + w 2) * 0 * (w 0 + w 2) = 0 :=
      hm ![1, 2, 3] ![1, 2, 3]
    linear_combination (1 / 2 : K) * m
  have p1 : (w 0 + w 1) * (w 1 + w 2) * (w 1 + w 3) = 0 := by
    have m : 0 * 0 * 0 - 0 * (w 0 + w 1) * (w 0 + w 1) - (w 1 + w 3) * (w 1 + w 3) * 0 + (w 1 + w 3) * (w 0 + w 1) * (w 1 + w 2) + (w 1 + w 2) * (w 1 + w 3) * (w 0 + w 1) - (w 1 + w 2) * 0 * (w 1 + w 2) = 0 :=
      hm ![0, 2, 3] ![0, 2, 3]
    linear_combination (1 / 2 : K) * m
  have p2 : (w 0 + w 2) * (w 1 + w 2) * (w 2 + w 3) = 0 := by
    have m : 0 * 0 * 0 - 0 * (w 0 + w 2) * (w 0 + w 2) - (w 2 + w 3) * (w 2 + w 3) * 0 + (w 2 + w 3) * (w 0 + w 2) * (w 1 + w 2) + (w 1 + w 2) * (w 2 + w 3) * (w 0 + w 2) - (w 1 + w 2) * 0 * (w 1 + w 2) = 0 :=
      hm ![0, 1, 3] ![0, 1, 3]
    linear_combination (1 / 2 : K) * m
  have p3 : (w 0 + w 3) * (w 1 + w 3) * (w 2 + w 3) = 0 := by
    have m : 0 * 0 * 0 - 0 * (w 0 + w 3) * (w 0 + w 3) - (w 2 + w 3) * (w 2 + w 3) * 0 + (w 2 + w 3) * (w 0 + w 3) * (w 1 + w 3) + (w 1 + w 3) * (w 2 + w 3) * (w 0 + w 3) - (w 1 + w 3) * 0 * (w 1 + w 3) = 0 :=
      hm ![0, 1, 2] ![0, 1, 2]
    linear_combination (1 / 2 : K) * m
  have M01 : w 0 + w 1 = 0 → w 2 + w 3 = 0 →
      (w 2 = 0 ∧ w 3 = 0) ∨ (w 0 = 0 ∧ w 1 = 0) := by
    intro h1 h2
    have m1 : 0 * (w 0 + w 3) * (w 0 + w 1) - 0 * (w 0 + w 2) * 0 - (w 1 + w 3) * (w 2 + w 3) * (w 0 + w 1) + (w 1 + w 3) * (w 0 + w 2) * (w 1 + w 3) + (w 1 + w 2) * (w 2 + w 3) * 0 - (w 1 + w 2) * (w 0 + w 3) * (w 1 + w 3) = 0 :=
      hm ![0, 1, 2] ![0, 2, 3]
    have m2 : 0 * (w 0 + w 3) * 0 - 0 * (w 0 + w 2) * (w 0 + w 1) - (w 1 + w 3) * (w 2 + w 3) * 0 + (w 1 + w 3) * (w 0 + w 2) * (w 1 + w 2) + (w 1 + w 2) * (w 2 + w 3) * (w 0 + w 1) - (w 1 + w 2) * (w 0 + w 3) * (w 1 + w 2) = 0 :=
      hm ![0, 1, 3] ![0, 2, 3]
    have e1 : w 1 = -w 0 := by linear_combination h1
    have e2 : w 3 = -w 2 := by linear_combination h2
    rw [e1, e2] at m1 m2
    have k : w 0 * w 0 * w 2 = 0 := by
      linear_combination (1/8 : K) * m1 + (1/8 : K) * m2
    rcases mul_eq_zero.mp k with h | h
    · have h0 : w 0 = 0 := mul_self_eq_zero.mp h
      exact Or.inr ⟨h0, by rw [e1, h0, neg_zero]⟩
    · exact Or.inl ⟨h, by rw [e2, h, neg_zero]⟩
  have M02 : w 0 + w 2 = 0 → w 1 + w 3 = 0 →
      (w 1 = 0 ∧ w 3 = 0) ∨ (w 0 = 0 ∧ w 2 = 0) := by
    intro h1 h2
    have m1 : 0 * (w 0 + w 3) * (w 0 + w 2) - 0 * (w 0 + w 1) * 0 - (w 2 + w 3) * (w 1 + w 3) * (w 0 + w 2) + (w 2 + w 3) * (w 0 + w 1) * (w 2 + w 3) + (w 1 + w 2) * (w 1 + w 3) * 0 - (w 1 + w 2) * (w 0 + w 3) * (w 2 + w 3) = 0 :=
      hm ![0, 2, 1] ![0, 1, 3]
    have m2 : 0 * (w 0 + w 3) * 0 - 0 * (w 0 + w 1) * (w 0 + w 2) - (w 2 + w 3) * (w 1 + w 3) * 0 + (w 2 + w 3) * (w 0 + w 1) * (w 1 + w 2) + (w 1 + w 2) * (w 1 + w 3) * (w 0 + w 2) - (w 1 + w 2) * (w 0 + w 3) * (w 1 + w 2) = 0 :=
      hm ![0, 2, 3] ![0, 1, 3]
    have e1 : w 2 = -w 0 := by linear_combination h1
    have e2 : w 3 = -w 1 := by linear_combination h2
    rw [e1, e2] at m1 m2
    have k : w 0 * w 0 * w 1 = 0 := by
      linear_combination (1/8 : K) * m1 + (1/8 : K) * m2
    rcases mul_eq_zero.mp k with h | h
    · have h0 : w 0 = 0 := mul_self_eq_zero.mp h
      exact Or.inr ⟨h0, by rw [e1, h0, neg_zero]⟩
    · exact Or.inl ⟨h, by rw [e2, h, neg_zero]⟩
  have M03 : w 0 + w 3 = 0 → w 1 + w 2 = 0 →
      (w 1 = 0 ∧ w 2 = 0) ∨ (w 0 = 0 ∧ w 3 = 0) := by
    intro h1 h2
    have m1 : 0 * (w 0 + w 2) * (w 0 + w 3) - 0 * (w 0 + w 1) * 0 - (w 2 + w 3) * (w 1 + w 2) * (w 0 + w 3) + (w 2 + w 3) * (w 0 + w 1) * (w 2 + w 3) + (w 1 + w 3) * (w 1 + w 2) * 0 - (w 1 + w 3) * (w 0 + w 2) * (w 2 + w 3) = 0 :=
      hm ![0, 3, 1] ![0, 1, 2]
    have m2 : 0 * (w 0 + w 2) * 0 - 0 * (w 0 + w 1) * (w 0 + w 3) - (w 2 + w 3) * (w 1 + w 2) * 0 + (w 2 + w 3) * (w 0 + w 1) * (w 1 + w 3) + (w 1 + w 3) * (w 1 + w 2) * (w 0 + w 3) - (w 1 + w 3) * (w 0 + w 2) * (w 1 + w 3) = 0 :=
      hm ![0, 3, 2] ![0, 1, 2]
    have e1 : w 3 = -w 0 := by linear_combination h1
    have e2 : w 2 = -w 1 := by linear_combination h2
    rw [e1, e2] at m1 m2
    have k : w 0 * w 0 * w 1 = 0 := by
      linear_combination (1/8 : K) * m1 + (1/8 : K) * m2
    rcases mul_eq_zero.mp k with h | h
    · have h0 : w 0 = 0 := mul_self_eq_zero.mp h
      exact Or.inr ⟨h0, by rw [e1, h0, neg_zero]⟩
    · exact Or.inl ⟨h, by rw [e2, h, neg_zero]⟩
  have h0 : w 0 + w 1 = 0 ∨ w 0 + w 2 = 0 ∨ w 0 + w 3 = 0 := by
    rcases mul_eq_zero.mp p0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have h1 : w 0 + w 1 = 0 ∨ w 1 + w 2 = 0 ∨ w 1 + w 3 = 0 := by
    rcases mul_eq_zero.mp p1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have h2 : w 0 + w 2 = 0 ∨ w 1 + w 2 = 0 ∨ w 2 + w 3 = 0 := by
    rcases mul_eq_zero.mp p2 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have h3 : w 0 + w 3 = 0 ∨ w 1 + w 3 = 0 ∨ w 2 + w 3 = 0 := by
    rcases mul_eq_zero.mp p3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have S0 : w 0 + w 1 = 0 → w 0 + w 2 = 0 → w 0 + w 3 = 0 → ∃ a b c d : Fin 4, D4 a b c d ∧
      ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨ (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) :=
    fun a b c => ⟨0, 1, 2, 3, by decide, Or.inr ⟨a, b, c⟩⟩
  have S1 : w 0 + w 1 = 0 → w 1 + w 2 = 0 → w 1 + w 3 = 0 → ∃ a b c d : Fin 4, D4 a b c d ∧
      ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨ (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) :=
    fun a b c => ⟨1, 0, 2, 3, by decide, Or.inr ⟨by linear_combination a, b, c⟩⟩
  have S2 : w 0 + w 2 = 0 → w 1 + w 2 = 0 → w 2 + w 3 = 0 → ∃ a b c d : Fin 4, D4 a b c d ∧
      ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨ (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) :=
    fun a b c => ⟨2, 0, 1, 3, by decide,
      Or.inr ⟨by linear_combination a, by linear_combination b, c⟩⟩
  have S3 : w 0 + w 3 = 0 → w 1 + w 3 = 0 → w 2 + w 3 = 0 → ∃ a b c d : Fin 4, D4 a b c d ∧
      ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨ (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) :=
    fun a b c => ⟨3, 0, 1, 2, by decide,
      Or.inr ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩⟩
  have N01 : w 0 + w 1 = 0 → w 2 + w 3 = 0 → ∃ a b c d : Fin 4, D4 a b c d ∧
      ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨ (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) := by
    intro a b
    rcases M01 a b with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact ⟨0, 1, 2, 3, by decide, Or.inl ⟨a, h, h'⟩⟩
    · exact ⟨2, 3, 0, 1, by decide, Or.inl ⟨b, h, h'⟩⟩
  have N02 : w 0 + w 2 = 0 → w 1 + w 3 = 0 → ∃ a b c d : Fin 4, D4 a b c d ∧
      ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨ (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) := by
    intro a b
    rcases M02 a b with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact ⟨0, 2, 1, 3, by decide, Or.inl ⟨a, h, h'⟩⟩
    · exact ⟨1, 3, 0, 2, by decide, Or.inl ⟨b, h, h'⟩⟩
  have N03 : w 0 + w 3 = 0 → w 1 + w 2 = 0 → ∃ a b c d : Fin 4, D4 a b c d ∧
      ((w a + w b = 0 ∧ w c = 0 ∧ w d = 0) ∨ (w a + w b = 0 ∧ w a + w c = 0 ∧ w a + w d = 0)) := by
    intro a b
    rcases M03 a b with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact ⟨0, 3, 1, 2, by decide, Or.inl ⟨a, h, h'⟩⟩
    · exact ⟨1, 2, 0, 3, by decide, Or.inl ⟨b, h, h'⟩⟩
  rcases h0 with z01 | z02 | z03
  · rcases h2 with z02 | z12 | z23
    · rcases h3 with z03 | z13 | z23
      · exact S0 z01 z02 z03
      · exact N02 z02 z13
      · exact N01 z01 z23
    · rcases h3 with z03 | z13 | z23
      · exact N03 z03 z12
      · exact S1 z01 z12 z13
      · exact N01 z01 z23
    · exact N01 z01 z23
  · rcases h1 with z01 | z12 | z13
    · rcases h3 with z03 | z13 | z23
      · exact S0 z01 z02 z03
      · exact N02 z02 z13
      · exact N01 z01 z23
    · rcases h3 with z03 | z13 | z23
      · exact N03 z03 z12
      · exact N02 z02 z13
      · exact S2 z02 z12 z23
    · exact N02 z02 z13
  · rcases h1 with z01 | z12 | z13
    · rcases h2 with z02 | z12 | z23
      · exact S0 z01 z02 z03
      · exact N03 z03 z12
      · exact N01 z01 z23
    · exact N03 z03 z12
    · rcases h2 with z02 | z12 | z23
      · exact N02 z02 z13
      · exact N03 z03 z12
      · exact S3 z03 z13 z23

/-- The equation of a node: `nodeEq (tag, a, b, c, d) c' = 0` says that the covector `c'`
vanishes at `e_a - e_b` (`tag = 0`) or at `e_a - e_b - e_c - e_d` (`tag = 1`). -/
def nodeEq (n : Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4) (c : Fin 4 → K) : K :=
  (![c n.2.1 - c n.2.2.1, c n.2.1 - c n.2.2.1 - c n.2.2.2.1 - c n.2.2.2.2] : Fin 2 → K) n.1

lemma isPoly_nodeEq (n : Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4)
    (Φ : Matrix (Fin 4) (Fin 4) K) : IsPoly (fun l => nodeEq n (cv Φ l)) := by
  obtain ⟨tag, a, b, c, d⟩ := n
  fin_cases tag
  · exact (isPoly_cv Φ a).sub (isPoly_cv Φ b)
  · exact (((isPoly_cv Φ a).sub (isPoly_cv Φ b)).sub (isPoly_cv Φ c)).sub (isPoly_cv Φ d)

lemma sum_D4 {a b c d : Fin 4} (hd : D4 a b c d) (f : Fin 4 → K) :
    ∑ x, f x = f a + f b + f c + f d := by
  obtain ⟨σ, h0, h1, h2, h3⟩ := exists_perm_of_D4 hd
  rw [← Equiv.sum_comp σ f, Fin.sum_univ_four, h0, h1, h2, h3]

/-- **Type of a triple.** Let `Φ 0, Φ 1, Φ 2` be three forms such that, for every `l` with
nonzero coordinates, all `3 × 3` minors of `B_w` vanish whenever `Φ v (l, l * w) = 0` for the
three `v`. Then there is one node `n` with `Φ v (l, l * n) = 0` for all `l` and `v`. -/
theorem triple_type [CharZero K] (Φ : Fin 3 → Matrix (Fin 4) (Fin 4) K)
    (H : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) → ∀ w : Fin 4 → K, (∀ v, bil (Φ v) l (l * w) = 0) →
      ∀ p q : Fin 3 → Fin 4, minor3 (Bmat w) p q = 0) :
    ∃ n : Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4, D4 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2 ∧
      ∀ (v : Fin 3) (l : Fin 4 → K), nodeEq n (cv (Φ v) l) = 0 := by
  have : Infinite K := CharZero.infinite K
  refine poly_union
    (fun n : Fin 2 × Fin 4 × Fin 4 × Fin 4 × Fin 4 => D4 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2)
    (fun n (v : Fin 3) l => nodeEq n (cv (Φ v) l)) (fun n v => isPoly_nodeEq n (Φ v))
    (fun l hl => ?_)
  obtain ⟨w, hw, h0, h1, h2⟩ := exists_common_zero (cv (Φ 0) l) (cv (Φ 1) l) (cv (Φ 2) l)
  have hv : ∀ v, dot4 (cv (Φ v) l) w = 0 := by
    intro v
    fin_cases v <;> assumption
  obtain ⟨a, b, c, d, hd, hnode⟩ :=
    node_of_rank2 w (H l hl w fun v => by rw [← dot4_cv]; exact hv v)
  have hsum : ∀ v, cv (Φ v) l a * w a + cv (Φ v) l b * w b + cv (Φ v) l c * w c
      + cv (Φ v) l d * w d = 0 := by
    intro v
    have := hv v
    rw [dot4, sum_D4 hd] at this
    exact this
  have hwa : w a ≠ 0 := by
    intro ha
    apply hw
    funext x
    rw [Pi.zero_apply]
    rcases hnode with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · have eb : w b = 0 := by linear_combination e1 - ha
      rcases all_four hd x with hx | hx | hx | hx <;> rw [hx] <;> assumption
    · have eb : w b = 0 := by linear_combination e1 - ha
      have ec : w c = 0 := by linear_combination e2 - ha
      have ed : w d = 0 := by linear_combination e3 - ha
      rcases all_four hd x with hx | hx | hx | hx <;> rw [hx] <;> assumption
  rcases hnode with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · refine ⟨(0, a, b, c, d), hd, fun v => ?_⟩
    show cv (Φ v) l a - cv (Φ v) l b = 0
    have : w a * (cv (Φ v) l a - cv (Φ v) l b) = 0 := by
      linear_combination hsum v - cv (Φ v) l b * e1 - cv (Φ v) l c * e2 - cv (Φ v) l d * e3
    exact (mul_eq_zero.mp this).resolve_left hwa
  · refine ⟨(1, a, b, c, d), hd, fun v => ?_⟩
    show cv (Φ v) l a - cv (Φ v) l b - cv (Φ v) l c - cv (Φ v) l d = 0
    have : w a * (cv (Φ v) l a - cv (Φ v) l b - cv (Φ v) l c - cv (Φ v) l d) = 0 := by
      linear_combination hsum v - cv (Φ v) l b * e1 - cv (Φ v) l c * e2 - cv (Φ v) l d * e3
    exact (mul_eq_zero.mp this).resolve_left hwa

/-! ### The structure of a decomposition of pattern `(3,1,1)` -/

/-- **Slices of a triple.** In a decomposition of pattern `(3,1,1)`, the three forms of the
pairing `01|23` satisfy the hypothesis of `triple_type`. -/
lemma Dec4.triple_minors {F0 G0 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F1 G1 F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) (w : Fin 4 → K) (hw : ∀ v, bil (F0 v) l (l * w) = 0)
    (p q : Fin 3 → Fin 4) : minor3 (Bmat w) p q = 0 := by
  refine minors_of_rank2 w (l 0 * l 1 * l 2 * l 3) (torus_prod_ne_zero hl)
    ![fun i => bil (F1 0) l (l * Pi.single i 1), fun i => bil (G2 0) (l * w) (l * Pi.single i 1)]
    ![fun j => bil (G1 0) (l * w) (l * Pi.single j 1), fun j => bil (F2 0) l (l * Pi.single j 1)]
    (fun i j => ?_) p q
  rw [← perm4_scale, h l (l * w) (l * Pi.single i 1) (l * Pi.single j 1), Fin.sum_univ_three,
    hw 0, hw 1, hw 2, Fin.sum_univ_two]
  simp
  ring

/-- **Kernel step at a node.** If the three forms `F0 v` vanish at `(l, l * n)` for all `l`,
the slice matrix `B_n` has rank two and `z` is in its kernel, then `F1 0` and `F2 0` vanish at
`(l, l * z)` for all `l`. -/
lemma kernel311 [CharZero K] {F0 G0 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F1 G1 F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (n : Fin 4 → K) (hn : ∀ v l, bil (F0 v) l (l * n) = 0) (p q : Fin 2 → Fin 4 → K)
    (hdet : Matrix.det (Matrix.of fun i j => E3 n (p i) (q j)) ≠ 0) (z : Fin 4 → K)
    (hz : ∀ y, E3 n z y = 0) (l : Fin 4 → K) :
    bil (F1 0) l (l * z) = 0 ∧ bil (F2 0) l (l * z) = 0 := by
  have : Infinite K := CharZero.infinite K
  have key : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) →
      bil (F1 0) l (l * z) = 0 ∧ bil (F2 0) l (l * z) = 0 := by
    intro l hl
    have hB : ∀ x y, perm4 l (l * n) x y
        = ∑ t : Fin 2, (![bil (F1 0) l, bil (G2 0) (l * n)] : Fin 2 → (Fin 4 → K) → K) t x *
          (![bil (G1 0) (l * n), bil (F2 0) l] : Fin 2 → (Fin 4 → K) → K) t y := by
      intro x y
      rw [h l _ x y, Fin.sum_univ_three, hn 0, hn 1, hn 2, Fin.sum_univ_two]
      simp
      ring
    have hk := scaled_kernel l hl n _ _ hB p q hdet z hz
    exact ⟨(hk 0).1, (hk 1).2⟩
  exact ⟨torus_ext (IsPoly.bil_mul (F1 0) z) (fun l hl => (key l hl).1) l,
    torus_ext (IsPoly.bil_mul (F2 0) z) (fun l hl => (key l hl).2) l⟩

lemma inPair_of_cv (M : Matrix (Fin 4) (Fin 4) K) (h1 : ∀ l, cv M l 0 + cv M l 1 = 0)
    (h2 : ∀ l, cv M l 2 - cv M l 3 = 0) : InPair 0 1 2 3 M := by
  obtain ⟨A1, A2, A3, A4⟩ := quad2 M (x := 0) (y := 1) (by decide) 1 1 (fun l => by
    linear_combination h1 l)
  obtain ⟨B1, B2, B3, B4⟩ := quad2 M (x := 2) (y := 3) (by decide) 1 (-1) (fun l => by
    linear_combination h2 l)
  have A2' := A4 2 (by decide) (by decide)
  have A3' := A4 3 (by decide) (by decide)
  have B0 := B4 0 (by decide) (by decide)
  have B1' := B4 1 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination A1
  · linear_combination A2
  · linear_combination B1
  · linear_combination -B2
  · linear_combination A3
  · linear_combination B3
  · linear_combination B0.1
  · linear_combination -B0.2
  · linear_combination B1'.1
  · linear_combination -B1'.2
  · linear_combination A2'.1
  · linear_combination A2'.2
  · linear_combination A3'.1
  · linear_combination A3'.2

lemma cols_of_cv (M : Matrix (Fin 4) (Fin 4) K) (h1 : ∀ l, cv M l 1 - cv M l 3 = 0)
    (h2 : ∀ l, cv M l 2 - cv M l 3 = 0) : ∀ p q, q ≠ 0 → M p q = 0 := by
  obtain ⟨A1, A2, A3, A4⟩ := quad2 M (x := 1) (y := 3) (by decide) 1 (-1) (fun l => by
    linear_combination h1 l)
  obtain ⟨B1, B2, B3, B4⟩ := quad2 M (x := 2) (y := 3) (by decide) 1 (-1) (fun l => by
    linear_combination h2 l)
  have A0 := A4 0 (by decide) (by decide)
  have A2' := A4 2 (by decide) (by decide)
  have B0 := B4 0 (by decide) (by decide)
  have B1' := B4 1 (by decide) (by decide)
  intro p q hq
  fin_cases q
  · exact absurd rfl hq
  · fin_cases p
    · show M 0 1 = 0
      linear_combination A0.1
    · show M 1 1 = 0
      linear_combination A1
    · show M 2 1 = 0
      linear_combination A2'.1
    · show M 3 1 = 0
      linear_combination A3 - B1'.2
  · fin_cases p
    · show M 0 2 = 0
      linear_combination B0.1
    · show M 1 2 = 0
      linear_combination B1'.1
    · show M 2 2 = 0
      linear_combination B1
    · show M 3 2 = 0
      linear_combination B3 - A2'.2
  · fin_cases p
    · show M 0 3 = 0
      linear_combination -A0.2
    · show M 1 3 = 0
      linear_combination -B1'.2
    · show M 2 3 = 0
      linear_combination -A2'.2
    · show M 3 3 = 0
      linear_combination -A2

/-- Pair node `e_0 - e_1`. -/
lemma std_pair [CharZero K] {F0 G0 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F1 G1 F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hn : ∀ v l, cv (F0 v) l 0 - cv (F0 v) l 1 = 0) :
    (∀ v, InN (F0 v)) ∧ InPair 0 1 2 3 (F1 0) ∧ InPair 0 1 2 3 (F2 0) := by
  have hn' : ∀ v l, bil (F0 v) l (l * ![1, -1, 0, 0]) = 0 := by
    intro v l
    rw [← dot4_cv]
    have e : dot4 (cv (F0 v) l) ![1, -1, 0, 0] = cv (F0 v) l 0 - cv (F0 v) l 1 := by
      simp [dot4_eq]
      ring
    rw [e]
    exact hn v l
  have hdet : Matrix.det (Matrix.of fun i j : Fin 2 =>
      E3 (![1, -1, 0, 0] : Fin 4 → K) ((![![1, 0, 0, 0], ![0, 0, 1, 0]] : Fin 2 → Fin 4 → K) i)
        ((![![1, 0, 0, 0], ![0, 0, 1, 0]] : Fin 2 → Fin 4 → K) j)) ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [E3_eq]
  have k1 := kernel311 h ![1, -1, 0, 0] hn' _ _ hdet ![1, 1, 0, 0] (fun y => by simp [E3_eq])
  have k2 := kernel311 h ![1, -1, 0, 0] hn' _ _ hdet ![0, 0, 1, -1] (fun y => by
    simp [E3_eq])
  have c1 : ∀ (M : Matrix (Fin 4) (Fin 4) K) l,
      bil M l (l * ![1, 1, 0, 0]) = cv M l 0 + cv M l 1 := by
    intro M l
    rw [← dot4_cv]
    simp [dot4_eq]
  have c2 : ∀ (M : Matrix (Fin 4) (Fin 4) K) l,
      bil M l (l * ![0, 0, 1, -1]) = cv M l 2 - cv M l 3 := by
    intro M l
    rw [← dot4_cv]
    simp [dot4_eq]
    ring
  exact ⟨fun v => inN_of_cv _ (hn v),
    inPair_of_cv _ (fun l => by rw [← c1]; exact (k1 l).1) (fun l => by rw [← c2]; exact (k2 l).1),
    inPair_of_cv _ (fun l => by rw [← c1]; exact (k1 l).2) (fun l => by rw [← c2]; exact (k2 l).2)⟩

/-- Star node `e_0 - e_1 - e_2 - e_3`. -/
lemma std_star [CharZero K] {F0 G0 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F1 G1 F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hn : ∀ v l, cv (F0 v) l 0 - cv (F0 v) l 1 - cv (F0 v) l 2 - cv (F0 v) l 3 = 0) :
    (∀ p q, q ≠ 0 → F1 0 p q = 0) ∧ (∀ p q, q ≠ 0 → F2 0 p q = 0) := by
  have hn' : ∀ v l, bil (F0 v) l (l * ![1, -1, -1, -1]) = 0 := by
    intro v l
    rw [← dot4_cv]
    have e : dot4 (cv (F0 v) l) ![1, -1, -1, -1]
        = cv (F0 v) l 0 - cv (F0 v) l 1 - cv (F0 v) l 2 - cv (F0 v) l 3 := by
      simp [dot4_eq]
      ring
    rw [e]
    exact hn v l
  have hdet : Matrix.det (Matrix.of fun i j : Fin 2 =>
      E3 (![1, -1, -1, -1] : Fin 4 → K) ((![![1, 0, 0, 0], ![0, 1, 0, 0]] : Fin 2 → Fin 4 → K) i)
        ((![![1, 0, 0, 0], ![0, 1, 0, 0]] : Fin 2 → Fin 4 → K) j)) ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [E3_eq]
  have k1 := kernel311 h ![1, -1, -1, -1] hn' _ _ hdet ![0, 1, 0, -1] (fun y => by
    simp [E3_eq])
  have k2 := kernel311 h ![1, -1, -1, -1] hn' _ _ hdet ![0, 0, 1, -1] (fun y => by
    simp [E3_eq])
  have c1 : ∀ (M : Matrix (Fin 4) (Fin 4) K) l,
      bil M l (l * ![0, 1, 0, -1]) = cv M l 1 - cv M l 3 := by
    intro M l
    rw [← dot4_cv]
    simp [dot4_eq]
    ring
  have c2 : ∀ (M : Matrix (Fin 4) (Fin 4) K) l,
      bil M l (l * ![0, 0, 1, -1]) = cv M l 2 - cv M l 3 := by
    intro M l
    rw [← dot4_cv]
    simp [dot4_eq]
    ring
  exact ⟨cols_of_cv _ (fun l => by rw [← c1]; exact (k1 l).1) (fun l => by rw [← c2]; exact (k2 l).1),
    cols_of_cv _ (fun l => by rw [← c1]; exact (k1 l).2) (fun l => by rw [← c2]; exact (k2 l).2)⟩

lemma cv_submatrix (σ : Equiv.Perm (Fin 4)) (M : Matrix (Fin 4) (Fin 4) K) (l : Fin 4 → K)
    (q : Fin 4) : cv (M.submatrix σ σ) l q = cv M (l ∘ σ.symm) (σ q) := by
  simp only [cv, colf, Matrix.submatrix_apply, Function.comp, Equiv.symm_apply_apply]
  congr 1
  exact Fintype.sum_equiv σ _ _ fun p => by simp

/-- **Structure of a decomposition of pattern `(3,1,1)`.** After a relabelling of the columns,
either the three forms `F0 v` satisfy `InN` and the two single forms `F1 0`, `F2 0` lie in
`span(alt_01, s_23)`, or the two single forms are supported on column `0`. -/
theorem Dec4.triple_cases [CharZero K] {F0 G0 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F1 G1 F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2) :
    ∃ σ : Equiv.Perm (Fin 4),
      ((∀ v, InN ((F0 v).submatrix σ σ)) ∧ InPair 0 1 2 3 ((F1 0).submatrix σ σ) ∧
        InPair 0 1 2 3 ((F2 0).submatrix σ σ)) ∨
      ((∀ p q, q ≠ 0 → (F1 0).submatrix σ σ p q = 0) ∧
        (∀ p q, q ≠ 0 → (F2 0).submatrix σ σ p q = 0)) := by
  obtain ⟨⟨tag, a, b, c, d⟩, hd, hn⟩ :=
    triple_type F0 (fun l hl w hw => h.triple_minors l hl w hw)
  obtain ⟨σ, h0, h1, h2, h3⟩ := exists_perm_of_D4 hd
  refine ⟨σ, ?_⟩
  fin_cases tag
  · left
    refine std_pair (h.relabel σ) (fun v l => ?_)
    rw [cv_submatrix, cv_submatrix, h0, h1]
    exact hn v (l ∘ σ.symm)
  · right
    refine std_star (h.relabel σ) (fun v l => ?_)
    rw [cv_submatrix, cv_submatrix, cv_submatrix, cv_submatrix, h0, h1, h2, h3]
    exact hn v (l ∘ σ.symm)

/-! ### The contradiction -/

lemma D4_cases23 : ∀ a b c d : Fin 4, D4 a b c d →
    ((a = 2 ∨ b = 2) ∧ (c = 3 ∨ d = 3)) ∨ ((a = 3 ∨ b = 3) ∧ (c = 2 ∨ d = 2)) ∨
    ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) ∨
    (((c = 2 ∧ d = 3) ∨ (c = 3 ∧ d = 2)) ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))) := by
  decide

/-- If `X ∈ span(alt_01, s_23)` has `X 2 3 ≠ 0` and also lies in `span(alt_ab, s_cd)`, then
`{a, b} = {0, 1}`; so forms whose entries `(c, a), (d, a), (c, b), (d, b)` vanish have vanishing
entries `(2, 0)` and `(2, 1)`. -/
lemma pair_finish [CharZero K] {a b c d : Fin 4} (hd : D4 a b c d)
    (X : Matrix (Fin 4) (Fin 4) K) (hX : InPair 0 1 2 3 X) (hXg : InPair a b c d X)
    (hX23 : X 2 3 ≠ 0) (G : Fin 3 → Matrix (Fin 4) (Fin 4) K)
    (hG : ∀ v, G v c a = 0 ∧ G v d a = 0 ∧ G v c b = 0 ∧ G v d b = 0) :
    ∀ v, G v 2 0 = 0 ∧ G v 2 1 = 0 := by
  obtain ⟨-, -, -, -, -, x6, -, -, -, -, -, -, -, -⟩ := hX
  obtain ⟨-, -, -, -, h5, -, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hXg
  rcases D4_cases23 a b c d hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h | ⟨h1, h2⟩
  · exfalso
    apply hX23
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> assumption
  · exfalso
    apply hX23
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> assumption
  · exfalso
    apply hX23
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : (2 : K) * X 2 3 = 0 := by linear_combination h5 - x6
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : K) * X 2 3 = 0 := by linear_combination h5 - x6
      exact (mul_eq_zero.mp this).resolve_left h2
  · intro v
    obtain ⟨g1, g2, g3, g4⟩ := hG v
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨by assumption, by assumption⟩

/-- A decomposition of pattern `(3,1,1)` cannot be of pair type. -/
lemma no311_pair [CharZero K] {F0 G0 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F1 G1 F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hN : ∀ v, InN (F0 v)) (hX : InPair 0 1 2 3 (F1 0)) (hX' : InPair 0 1 2 3 (F2 0)) :
    False := by
  have A1 : (1 : K) = F0 0 2 0 * G0 0 3 1 + F0 1 2 0 * G0 1 3 1 + F0 2 2 0 * G0 2 3 1
      + F1 0 2 3 * G1 0 0 1 + F2 0 2 1 * G2 0 0 3 := by
    simpa [Fin.sum_univ_three] using h.coeff 2 0 3 1
  have B1 : (1 : K) = F0 0 1 3 * G0 0 2 0 + F0 1 1 3 * G0 1 2 0 + F0 2 1 3 * G0 2 2 0
      + F1 0 1 2 * G1 0 3 0 + F2 0 1 0 * G2 0 3 2 := by
    simpa [Fin.sum_univ_three] using h.coeff 1 3 2 0
  have B2 : (1 : K) = F0 0 0 3 * G0 0 2 1 + F0 1 0 3 * G0 1 2 1 + F0 2 0 3 * G0 2 2 1
      + F1 0 0 2 * G1 0 3 1 + F2 0 0 1 * G2 0 3 2 := by
    simpa [Fin.sum_univ_three] using h.coeff 0 3 2 1
  have n0 := (hN 0).2.2.2.1
  have n1 := (hN 1).2.2.2.1
  have n2 := (hN 2).2.2.2.1
  obtain ⟨-, -, -, -, -, x6, x7, -, x9, -, -, -, -, -⟩ := id hX
  obtain ⟨-, -, -, -, y5, -, -, -, -, -, -, y12, -, -⟩ := hX'
  have hX23 : F1 0 2 3 ≠ 0 := by
    intro h0
    have : (1 : K) = 0 := by
      linear_combination A1 + G0 0 3 1 * n0 + G0 1 3 1 * n1 + G0 2 3 1 * n2 + G1 0 0 1 * h0
        + G2 0 0 3 * y12
    exact one_ne_zero this
  have hG : ∀ v, G0 v 2 0 = 0 ∧ G0 v 2 1 = 0 := by
    obtain ⟨σ, ⟨hG, hXt, -⟩ | ⟨hr, -⟩⟩ := h.swap0213.triple_cases
    · have hd : D4 (σ 0) (σ 1) (σ 2) (σ 3) :=
        ⟨σ.injective.ne (by decide), σ.injective.ne (by decide), σ.injective.ne (by decide),
          σ.injective.ne (by decide), σ.injective.ne (by decide), σ.injective.ne (by decide)⟩
      have hXt' : InPair (σ 0) (σ 1) (σ 2) (σ 3) (F1 0)ᵀ := hXt
      have hXg : InPair (σ 0) (σ 1) (σ 2) (σ 3) (F1 0) := by
        have := hXt'.transpose
        rwa [Matrix.transpose_transpose] at this
      refine pair_finish hd (F1 0) hX hXg hX23 G0 (fun v => ?_)
      obtain ⟨-, -, -, g1, g2, g3, g4⟩ := hG v
      exact ⟨g1, g2, g3, g4⟩
    · exfalso
      have r : ∀ x y, x ≠ σ 0 → F1 0 x y = 0 := by
        intro x y hx
        have := hr (σ.symm y) (σ.symm x) (by
          intro e
          apply hx
          rw [← e]
          simp)
        simpa using this
      by_cases h2 : (2 : Fin 4) = σ 0
      · have h3 : (3 : Fin 4) ≠ σ 0 := by
          rw [← h2]
          decide
        apply hX23
        rw [← x6]
        exact r 3 2 h3
      · exact hX23 (r 2 3 h2)
  have : (2 : K) = 0 := by
    linear_combination B1 + B2 + F0 0 1 3 * (hG 0).1 + F0 1 1 3 * (hG 1).1 + F0 2 1 3 * (hG 2).1
      + F0 0 0 3 * (hG 0).2 + F0 1 0 3 * (hG 1).2 + F0 2 0 3 * (hG 2).2 + G1 0 3 0 * x9
      + G1 0 3 1 * x7 + G2 0 3 2 * y5
  exact two_ne_zero this

/-- Index data for `no311_star`: four pairs `(rowA a k, rowB a k)` with `rowA a k ≠ a`. -/
def rowA (a : Fin 4) : Fin 4 → Fin 4 :=
  ![if a = 0 then 1 else 0, if a = 0 then 2 else 0, if a = 0 then 3 else 0, if a = 1 then 2 else 1]
/-- See `rowA`. -/
def rowB (a : Fin 4) : Fin 4 → Fin 4 :=
  ![if a = 0 then 0 else 1, if a = 0 then 0 else 2, if a = 0 then 0 else 3, if a = 1 then 1 else 2]
/-- See `rowA`. -/
def colC : Fin 4 → Fin 4 := ![2, 1, 1, 0]
/-- See `rowA`. -/
def colD : Fin 4 → Fin 4 := ![3, 3, 2, 3]

lemma idxStar : ∀ a k k' : Fin 4, (rowA a k ≠ rowB a k ∧ rowA a k ≠ colC k' ∧ rowA a k ≠ colD k' ∧
    rowB a k ≠ colC k' ∧ rowB a k ≠ colD k' ∧ colC k' ≠ colD k') ↔ k = k' := by
  decide

lemma rowA_ne : ∀ a k : Fin 4, rowA a k ≠ a := by decide

lemma colD_ne : ∀ k : Fin 4, colD k ≠ 0 := by decide

/-- A decomposition of pattern `(3,1,1)` whose single forms `F1 0`, `F2 0` are supported on
column `0`, and whose form `F1 0` is supported on one row, does not exist: both single terms
vanish on a `4 × 4` identity minor of the flattening. -/
lemma no311_star {F0 G0 : Fin 3 → Matrix (Fin 4) (Fin 4) K}
    {F1 G1 F2 G2 : Fin 1 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (hc2 : ∀ p q, q ≠ 0 → F2 0 p q = 0) (a : Fin 4) (hr : ∀ x y, x ≠ a → F1 0 x y = 0) :
    False := by
  refine rank_contra (n := 4) (ι := Fin 3) (by simp) (fun v k => F0 v (rowA a k) (rowB a k))
    (fun v k' => G0 v (colC k') (colD k')) fun k k' => ?_
  have := h.coeff (rowA a k) (rowB a k) (colC k') (colD k')
  rw [Fin.sum_univ_one, Fin.sum_univ_one, hr _ _ (rowA_ne a k), hc2 _ _ (colD_ne k'), zero_mul,
    zero_mul, add_zero, add_zero] at this
  rw [← this]
  simp only [idxStar a k k']

/-- **Pattern `(3,1,1)`.** -/
theorem no_dec_311 [CharZero K] : ¬ HasDec K 3 1 1 := by
  rintro ⟨F0, G0, F1, G1, F2, G2, h⟩
  obtain ⟨σ, ⟨hN, hX, hX'⟩ | ⟨-, hc2⟩⟩ := h.triple_cases
  · exact no311_pair (h.relabel σ) hN hX hX'
  · have h1 := h.relabel σ
    obtain ⟨τ, ⟨hN, hX, hX'⟩ | ⟨hr, -⟩⟩ := h1.swap0213.triple_cases
    · exact no311_pair (h1.swap0213.relabel τ) hN hX hX'
    · refine no311_star h1 hc2 (τ 0) (fun x y hx => ?_)
      have := hr (τ.symm y) (τ.symm x) (by
        intro e
        apply hx
        rw [← e]
        simp)
      simpa using this

end PatternC

end PvsNP
