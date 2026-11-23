import PvsNP.FourByFourExactBase

/-!
# Exact five-term bound, patterns `(5,0,0)` and `(4,1,0)`

* `no_dec_500`: five split products of the same pairing do not add up to the `4 × 4`
  permanent (the flattening has rank six).
* `no_dec_410`: four split products of one pairing and one of another do not add up to the
  permanent. Rows `0` and `2` are restricted to planes `L0`, `L2` on which the single term
  vanishes; on these planes the permanent still has rank at least five.
-/

namespace PvsNP

open Matrix

section PatternsA

variable {K : Type*} [Field K]

/-- Index data of the `6 × 6` minor of the flattening `01|23`. -/
def pa6 : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
/-- See `pa6`. -/
def pb6 : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]
/-- See `pa6`. -/
def pc6 : Fin 6 → Fin 4 := ![2, 1, 1, 0, 0, 0]
/-- See `pa6`. -/
def pd6 : Fin 6 → Fin 4 := ![3, 3, 2, 3, 2, 1]

lemma idx6 : ∀ k k' : Fin 6, (pa6 k ≠ pb6 k ∧ pa6 k ≠ pc6 k' ∧ pa6 k ≠ pd6 k' ∧ pb6 k ≠ pc6 k' ∧
    pb6 k ≠ pd6 k' ∧ pc6 k' ≠ pd6 k') ↔ k = k' := by
  decide

/-- **Pattern `(5,0,0)`.** -/
theorem no_dec_500 : ¬ HasDec K 5 0 0 := by
  rintro ⟨F0, G0, F1, G1, F2, G2, h⟩
  refine rank_contra (n := 6) (ι := Fin 5) (by simp) (fun v k => F0 v (pa6 k) (pb6 k))
    (fun v k' => G0 v (pc6 k') (pd6 k')) fun k k' => ?_
  have := h.coeff (pa6 k) (pb6 k) (pc6 k') (pd6 k')
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at this
  rw [← this]
  simp only [idx6 k k']

/-- The symmetric form `x_c y_d + x_d y_c` for the `t`-th pair `c < d`. -/
def spair (t : Fin 6) (x y : Fin 4 → K) : K := x (pa6 t) * y (pb6 t) + x (pb6 t) * y (pa6 t)

/-- The symmetric forms with zero diagonal that vanish on a plane in chart form are determined
by one coefficient; so six of them cannot be combinations of four forms on that plane. -/
lemma sym0_chart_contra {i j k m : Fin 4}
    (hd : i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m) (a b c d : K)
    (cc : Fin 6 → Fin 4 → K) (g : Fin 4 → (Fin 4 → K) → (Fin 4 → K) → K)
    (hp : ∀ t y, spair t (chartVec i k m a b) y = ∑ v, cc t v * g v (chartVec i k m a b) y)
    (hq : ∀ t y, spair t (chartVec j k m c d) y = ∑ v, cc t v * g v (chartVec j k m c d) y) :
    False := by
  classical
  let M : Matrix (Fin 6) (Fin 6) K := fun t s =>
    if hs : (s : ℕ) < 4 then cc t ⟨s, hs⟩
    else if (s : ℕ) = 4 then spair t (Pi.single k 1) (Pi.single m 1) else 0
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_column_eq_zero 5 (fun t => by simp [M])
  obtain ⟨lam, hlam, hM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hv : ∀ v : Fin 4, ∑ t, lam t * cc t v = 0 := by
    intro v
    have := congrFun hM ⟨v, by omega⟩
    simpa [M, Matrix.vecMul, dotProduct, v.isLt] using this
  have hkm : ∑ t, lam t * spair t (Pi.single k 1) (Pi.single m 1) = 0 := by
    have := congrFun hM 4
    simpa [M, Matrix.vecMul, dotProduct] using this
  have hL : ∀ x : Fin 4 → K, (∀ t y, spair t x y = ∑ v, cc t v * g v x y) →
      ∀ y, ∑ t, lam t * spair t x y = 0 := by
    intro x hx y
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v _ => ?_
    have : ∑ t, lam t * (cc t v * g v x y) = (∑ t, lam t * cc t v) * g v x y := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [this, hv, zero_mul]
  have hLp := hL _ hp
  have hLq := hL _ hq
  obtain ⟨Lm, hLm⟩ : ∃ Lm : Fin 4 → Fin 4 → K,
      Lm = fun x y => ∑ t, lam t * spair t (Pi.single x 1) (Pi.single y 1) := ⟨_, rfl⟩
  have hsym : ∀ x y, Lm x y = Lm y x := by
    intro x y
    simp only [hLm, spair]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hdiag : ∀ x, Lm x x = 0 := by
    intro x
    fin_cases x <;> simp [hLm, spair, pa6, pb6, Fin.sum_univ_six, Pi.single_apply]
  have hlin : ∀ (i' k' m' : Fin 4) (a' b' : K) (y : Fin 4),
      ∑ t, lam t * spair t (chartVec i' k' m' a' b') (Pi.single y 1)
        = Lm i' y + a' * Lm k' y + b' * Lm m' y := by
    intro i' k' m' a' b' y
    simp only [hLm, spair, chartVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hlam' : ∀ t, lam t = Lm (pa6 t) (pb6 t) := by
    intro t
    fin_cases t <;> simp [hLm, spair, pa6, pb6, Fin.sum_univ_six, Pi.single_apply]
  have ekm : Lm k m = 0 := by rw [hLm]; exact hkm
  clear_value M
  clear hLm hkm hM hdet hv hL hp hq
  have emk : Lm m k = 0 := by rw [hsym]; exact ekm
  have eik : Lm i k = 0 := by
    have := hLp (Pi.single k 1)
    rw [hlin] at this
    linear_combination this - a * hdiag k - b * emk
  have eim : Lm i m = 0 := by
    have := hLp (Pi.single m 1)
    rw [hlin] at this
    linear_combination this - a * ekm - b * hdiag m
  have ejk : Lm j k = 0 := by
    have := hLq (Pi.single k 1)
    rw [hlin] at this
    linear_combination this - c * hdiag k - d * emk
  have ejm : Lm j m = 0 := by
    have := hLq (Pi.single m 1)
    rw [hlin] at this
    linear_combination this - c * ekm - d * hdiag m
  have ekj : Lm k j = 0 := by rw [hsym]; exact ejk
  have emj : Lm m j = 0 := by rw [hsym]; exact ejm
  have eij : Lm i j = 0 := by
    have := hLp (Pi.single j 1)
    rw [hlin] at this
    linear_combination this - a * ekj - b * emj
  have eji : Lm j i = 0 := by rw [hsym]; exact eij
  have eki : Lm k i = 0 := by rw [hsym]; exact eik
  have emi : Lm m i = 0 := by rw [hsym]; exact eim
  have hall : ∀ x y, Lm x y = 0 := by
    intro x y
    rcases all_four hd x with hx | hx | hx | hx <;>
    rcases all_four hd y with hy | hy | hy | hy <;> rw [hx, hy] <;>
    first
      | exact hdiag _ | exact eij | exact eik | exact eim | exact ejk | exact ejm | exact ekm
      | exact eji | exact eki | exact emi | exact ekj | exact emj | exact emk
  apply hlam
  funext t
  rw [hlam' t, hall]
  rfl

/-- The rows `l` of the six pairs `(l, u)`, `l` in the plane `L0 = span(e_0, e_1 + e_2 + e_3)`,
whose slice forms are the six forms `spair`. -/
def lv6 : Fin 6 → Fin 4 → K :=
  ![![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]]

/-- See `lv6`. -/
def uv6 : Fin 6 → Fin 4 → K :=
  ![![0, -1 / 2, 1 / 2, 1 / 2], ![0, 1 / 2, -1 / 2, 1 / 2], ![0, 1 / 2, 1 / 2, -1 / 2],
    ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0]]

lemma perm4_lv6_uv6 [CharZero K] (t : Fin 6) (x y : Fin 4 → K) :
    perm4 (lv6 t) (uv6 t) x y = spair t x y := by
  fin_cases t <;> simp [lv6, uv6, perm4_eq, spair, pa6, pb6] <;> ring

/-- **Pattern `(4,1,0)`.** -/
theorem no_dec_410 [CharZero K] : ¬ HasDec K 4 1 0 := by
  rintro ⟨F0, G0, F1, G1, F2, G2, h⟩
  obtain ⟨i, j, k, m, hd, a, b, c, d, e1, e2, e3, e4⟩ :=
    exists_chart (colf (F1 0) ![0, 1, 1, 1]) (colf (F1 0) ![1, 0, 0, 0])
  rw [← bil_eq_dot] at e1 e2 e3 e4
  have hX : ∀ (t : Fin 6), bil (F1 0) (lv6 t) (chartVec i k m a b) = 0 ∧
      bil (F1 0) (lv6 t) (chartVec j k m c d) = 0 := by
    intro t
    fin_cases t
    · exact ⟨e1, e3⟩
    · exact ⟨e1, e3⟩
    · exact ⟨e1, e3⟩
    · exact ⟨e2, e4⟩
    · exact ⟨e2, e4⟩
    · exact ⟨e2, e4⟩
  refine sym0_chart_contra hd a b c d (fun t v => bil (F0 v) (lv6 t) (uv6 t))
    (fun v x y => bil (G0 v) x y) (fun t y => ?_) (fun t y => ?_)
  · have := h (lv6 t) (uv6 t) (chartVec i k m a b) y
    rw [perm4_lv6_uv6] at this
    simpa [(hX t).1] using this
  · have := h (lv6 t) (uv6 t) (chartVec j k m c d) y
    rw [perm4_lv6_uv6] at this
    simpa [(hX t).2] using this

end PatternsA

end PvsNP
