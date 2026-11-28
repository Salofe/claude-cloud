import OMAStatements.S_oeis_a200887

/-!
Proof of Barker's conjectures for A200887 (0..n arrays x(0..3) of 4 elements without any interior
element greater than both neighbors).

An array fails to qualify exactly when it has a peak at position 1 (`x 0 < x 1` and `x 2 < x 1`)
or a peak at position 2 (`x 1 < x 2` and `x 3 < x 2`), and these cannot both happen, since one
needs `x 2 < x 1` and the other `x 1 < x 2`. So the indicator of a qualifying array is
`1 - [peak at 1] - [peak at 2]` (`hsplit` in `a_eq`). Listing an array as a 4-tuple with the peak
position first (`tupA`, `tupB`), each kind of peak is counted by the same sum (`count_peak`): the
peak value `v` in `0..n`, two smaller neighbours in `v * v` ways (`sum_lt`), and the remaining
entry free in `n + 1` ways. With `Sum_{v ≤ n} v^2 = n (n + 1) (2n + 1) / 6` (`sum_sq`) this gives,
for every `n`,
  a(n) = (n + 1)^4 - 2 (n + 1) n (n + 1) (2n + 1) / 6 = (1 + n)^2 (3 + 5n + n^2) / 3
(`a_formula`). The recurrence and the generating function follow by comparing coefficients: the
fifth difference of a polynomial of degree 4 vanishes.
-/

namespace OMA.Helpers

open OMA.S_oeis_a200887 Finset

/-- Arrays as 4-tuples listed with the entry x(1) first: `(x1, x0, x2, x3)`. -/
def tupA (n : ℕ) : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃ (Fin 4 → Fin (n + 1)) where
  toFun p := ![p.2.1, p.1, p.2.2.1, p.2.2.2]
  invFun x := (x 1, x 0, x 2, x 3)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Arrays as 4-tuples listed with the entry x(2) first: `(x2, x1, x3, x0)`. -/
def tupB (n : ℕ) : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃ (Fin 4 → Fin (n + 1)) where
  toFun p := ![p.2.2.2, p.2.1, p.1, p.2.2.1]
  invFun x := (x 2, x 1, x 3, x 0)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- The number of entries `q` in `0..n` below `v` is `v`. -/
theorem sum_lt (n : ℕ) (v : Fin (n + 1)) :
    ∑ q : Fin (n + 1), (if q < v then (1 : ℚ) else 0) = ((v : ℕ) : ℚ) := by
  rw [sum_boole, filter_gt_eq_Iio, Fin.card_Iio]

/-- The tuples `(v, q, r, s)` with `q < v` and `r < v` number `(n + 1) * Sum_{v ≤ n} v^2`. -/
theorem count_peak (n : ℕ) :
    ∑ p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1),
      (if p.2.1 < p.1 ∧ p.2.2.1 < p.1 then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 := by
  simp only [Fintype.sum_prod_type]
  have h : ∀ v : Fin (n + 1), ∑ q : Fin (n + 1), ∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      (if q < v ∧ r < v then (1 : ℚ) else 0) = ((n : ℚ) + 1) * ((v : ℕ) : ℚ) ^ 2 := by
    intro v
    have h1 : ((n : ℚ) + 1) * ((v : ℕ) : ℚ) ^ 2 =
        (∑ q : Fin (n + 1), (if q < v then (1 : ℚ) else 0)) *
          (∑ r : Fin (n + 1), (if r < v then (1 : ℚ) else 0)) * (∑ s : Fin (n + 1), (1 : ℚ)) := by
      rw [sum_lt]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [h1, sum_mul_sum, sum_mul]
    refine sum_congr rfl (fun q _ => ?_)
    rw [sum_mul]
    refine sum_congr rfl (fun r _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun s _ => ?_)
    by_cases hq : q < v <;> by_cases hr : r < v <;> simp [hq, hr]
  rw [sum_congr rfl (fun v _ => h v), ← mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => (i : ℚ) ^ 2) (n + 1)

theorem sum_sq (n : ℕ) :
    ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 = (n : ℚ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem a_eq (n : ℕ) : (a n : ℚ) =
    ((n : ℚ) + 1) ^ 4 - 2 * (((n : ℚ) + 1) * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2) := by
  have hA : ∑ x : Fin 4 → Fin (n + 1), (if x 0 < x 1 ∧ x 2 < x 1 then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 := by
    rw [← (tupA n).sum_comp]
    exact count_peak n
  have hB : ∑ x : Fin 4 → Fin (n + 1), (if x 1 < x 2 ∧ x 3 < x 2 then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 := by
    rw [← (tupB n).sum_comp]
    exact count_peak n
  have hsplit : ∀ x : Fin 4 → Fin (n + 1), (if NoPeak x then (1 : ℚ) else 0) =
      1 - (if x 0 < x 1 ∧ x 2 < x 1 then 1 else 0) - (if x 1 < x 2 ∧ x 3 < x 2 then 1 else 0) := by
    intro x
    unfold NoPeak
    by_cases h1 : x 0 < x 1 ∧ x 2 < x 1
    · have h2 : ¬ (x 1 < x 2 ∧ x 3 < x 2) := fun h => lt_asymm h1.2 h.1
      simp [h1, h2]
    · by_cases h2 : x 1 < x 2 ∧ x 3 < x 2
      · simp [h1, h2]
      · simp [h1, h2]
  have hcard : (a n : ℚ) = ∑ x : Fin 4 → Fin (n + 1), (if NoPeak x then (1 : ℚ) else 0) := by
    unfold a
    rw [natCast_card_filter]
  rw [hcard, sum_congr rfl (fun x _ => hsplit x), sum_sub_distrib, sum_sub_distrib, hA, hB]
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem a_formula (n : ℕ) : (a n : ℚ) = (1 + n) ^ 2 * (3 + 5 * n + n ^ 2) / 3 := by
  rw [a_eq, sum_sq]
  ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have hQ : (a n : ℚ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4)
      + a (n - 5) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega]
    rw [a_formula (k + 6), a_formula (k + 5), a_formula (k + 4), a_formula (k + 3),
      a_formula (k + 2), a_formula (k + 1)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 : PowerSeries ℚ) =
      X * (12 - 9 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) with hA
  have key : A * (1 - X) ^ 5 =
      A * X ^ 0 - C (5 : ℚ) * (A * X ^ 1) + C (10 : ℚ) * (A * X ^ 2) - C (10 : ℚ) * (A * X ^ 3) +
        C (5 : ℚ) * (A * X ^ 4) - A * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℚ) * (12 - 9 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) =
      C (12 : ℚ) * X ^ 1 - C (9 : ℚ) * X ^ 2 + C (9 : ℚ) * X ^ 3 - C (5 : ℚ) * X ^ 4 +
        C (1 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [a_formula]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 < 1) by omega, show ¬ (j + 5 < 1) by omega, show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false]
    rw [a_formula (j + 6), a_formula (j + 5), a_formula (j + 4), a_formula (j + 3),
      a_formula (j + 2), a_formula (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a200887.main :=
  ⟨OMA.Helpers.gen_fun, fun n _ => OMA.Helpers.a_formula n, OMA.Helpers.recurrence⟩
