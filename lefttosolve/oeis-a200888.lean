import OMAStatements.S_oeis_a200888

/-!
Proof of Barker's conjectures for A200888 (0..n arrays x(0..4) of 5 elements without any interior
element greater than both neighbors).

An array fails to qualify when it has a peak at position 1 (`x 0 < x 1` and `x 2 < x 1`), at
position 2 (`x 1 < x 2` and `x 3 < x 2`) or at position 3 (`x 2 < x 3` and `x 4 < x 3`). Peaks at
two adjacent positions are impossible (a peak at 1 needs `x 2 < x 1`, a peak at 2 needs
`x 1 < x 2`, and likewise for 2 and 3), but peaks at 1 and 3 can occur together. So, by
inclusion-exclusion, the indicator of a qualifying array is
`1 - [peak at 1] - [peak at 2] - [peak at 3] + [peaks at 1 and 3]` (`hsplit` in `a_eq`).
Listing an array as a 5-tuple with the peak position first (`tup1`, `tup2`, `tup3`), each kind of
single peak is counted by the same sum (`count_peak`): the peak value `v` in `0..n`, two smaller
neighbours in `v * v` ways, and the two remaining entries free, so `(n + 1)^2 Sum_{v ≤ n} v^2`.
Peaks at 1 and 3 share the neighbour `x 2 = t` (`tup13`); given `t`, each peak contributes
`Sum_{t < u ≤ n} u = (n (n + 1) - t (t + 1)) / 2` choices (`count_half`, `sum_above`), so they
number `Sum_{t ≤ n} ((n (n + 1) - t (t + 1)) / 2)^2` (`count_double`). Summing these polynomials
(`sum_sq`, `sum_sq_above`) gives, for every n,
  a(n) = (2/15) n^5 + (11/6) n^4 + (35/6) n^3 + (23/3) n^2 + (68/15) n + 1
(`a_formula`). The recurrence and the generating function follow by comparing coefficients: the
sixth difference of a polynomial of degree 5 vanishes.
-/

namespace OMA.Helpers

open OMA.S_oeis_a200888 Finset

/-- Arrays as 5-tuples listed with the entry x(1) first: `(x1, x0, x2, x3, x4)`. -/
def tup1 (n : ℕ) :
    Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃ (Fin 5 → Fin (n + 1)) where
  toFun p := ![p.2.1, p.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  invFun x := (x 1, x 0, x 2, x 3, x 4)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Arrays as 5-tuples listed with the entry x(2) first: `(x2, x1, x3, x0, x4)`. -/
def tup2 (n : ℕ) :
    Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃ (Fin 5 → Fin (n + 1)) where
  toFun p := ![p.2.2.2.1, p.2.1, p.1, p.2.2.1, p.2.2.2.2]
  invFun x := (x 2, x 1, x 3, x 0, x 4)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Arrays as 5-tuples listed with the entry x(3) first: `(x3, x2, x4, x0, x1)`. -/
def tup3 (n : ℕ) :
    Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃ (Fin 5 → Fin (n + 1)) where
  toFun p := ![p.2.2.2.1, p.2.2.2.2, p.2.1, p.1, p.2.2.1]
  invFun x := (x 3, x 2, x 4, x 0, x 1)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Arrays as 5-tuples listed with the entry x(2) first, then `x1, x0, x3, x4`. -/
def tup13 (n : ℕ) :
    Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃ (Fin 5 → Fin (n + 1)) where
  toFun p := ![p.2.2.1, p.2.1, p.1, p.2.2.2.1, p.2.2.2.2]
  invFun x := (x 2, x 1, x 0, x 3, x 4)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- The number of entries `q` in `0..n` below `v` is `v`. -/
theorem sum_lt (n : ℕ) (v : Fin (n + 1)) :
    ∑ q : Fin (n + 1), (if q < v then (1 : ℚ) else 0) = ((v : ℕ) : ℚ) := by
  rw [sum_boole, filter_gt_eq_Iio, Fin.card_Iio]

/-- The tuples `(v, q, r, s, t)` with `q < v` and `r < v` number `(n + 1)^2 * Sum_{v ≤ n} v^2`. -/
theorem count_peak (n : ℕ) :
    ∑ p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1),
      (if p.2.1 < p.1 ∧ p.2.2.1 < p.1 then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) ^ 2 * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 := by
  simp only [Fintype.sum_prod_type]
  have h : ∀ v : Fin (n + 1), ∑ q : Fin (n + 1), ∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ∑ t : Fin (n + 1), (if q < v ∧ r < v then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) ^ 2 * ((v : ℕ) : ℚ) ^ 2 := by
    intro v
    have h1 : ((n : ℚ) + 1) ^ 2 * ((v : ℕ) : ℚ) ^ 2 =
        (∑ q : Fin (n + 1), (if q < v then (1 : ℚ) else 0)) *
          ((∑ r : Fin (n + 1), (if r < v then (1 : ℚ) else 0)) *
            ((∑ s : Fin (n + 1), (1 : ℚ)) * (∑ t : Fin (n + 1), (1 : ℚ)))) := by
      rw [sum_lt]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [h1]
    simp only [sum_mul]
    simp only [mul_sum]
    refine sum_congr rfl (fun q _ => sum_congr rfl (fun r _ => sum_congr rfl
      (fun s _ => sum_congr rfl (fun t _ => ?_))))
    by_cases hq : q < v <;> by_cases hr : r < v <;> simp [hq, hr]
  rw [sum_congr rfl (fun v _ => h v), ← mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => (i : ℚ) ^ 2) (n + 1)

/-- For a fixed `t`, the pairs `(u, q)` with `t < u` and `q < u` number `Sum_{t < u ≤ n} u`. -/
theorem count_half (n : ℕ) (t : Fin (n + 1)) :
    ∑ u : Fin (n + 1), ∑ q : Fin (n + 1), (if t < u ∧ q < u then (1 : ℚ) else 0) =
      ∑ u ∈ range (n + 1), (if (t : ℕ) < u then (u : ℚ) else 0) := by
  have h : ∀ u : Fin (n + 1), ∑ q : Fin (n + 1), (if t < u ∧ q < u then (1 : ℚ) else 0) =
      if (t : ℕ) < (u : ℕ) then ((u : ℕ) : ℚ) else 0 := by
    intro u
    by_cases htu : t < u
    · have htu' : (t : ℕ) < (u : ℕ) := htu
      simp only [htu, true_and, htu', if_true]
      exact sum_lt n u
    · have htu' : ¬ (t : ℕ) < (u : ℕ) := htu
      simp [htu, htu']
  rw [sum_congr rfl (fun u _ => h u)]
  exact Fin.sum_univ_eq_sum_range (fun i => if (t : ℕ) < i then (i : ℚ) else 0) (n + 1)

/-- The tuples `(t, u, q, w, r)` with `t, q < u` and `t, r < w` number
`Sum_{t ≤ n} (Sum_{t < u ≤ n} u)^2`. -/
theorem count_double (n : ℕ) :
    ∑ p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1),
      (if (p.1 < p.2.1 ∧ p.2.2.1 < p.2.1) ∧ (p.1 < p.2.2.2.1 ∧ p.2.2.2.2 < p.2.2.2.1)
        then (1 : ℚ) else 0) =
      ∑ t ∈ range (n + 1), (∑ u ∈ range (n + 1), (if t < u then (u : ℚ) else 0)) ^ 2 := by
  simp only [Fintype.sum_prod_type]
  have h : ∀ t : Fin (n + 1), ∑ u : Fin (n + 1), ∑ q : Fin (n + 1), ∑ w : Fin (n + 1),
      ∑ r : Fin (n + 1),
        (if (t < u ∧ q < u) ∧ (t < w ∧ r < w) then (1 : ℚ) else 0) =
      (∑ u ∈ range (n + 1), (if (t : ℕ) < u then (u : ℚ) else 0)) ^ 2 := by
    intro t
    rw [sq, ← count_half n t]
    simp only [sum_mul]
    simp only [mul_sum]
    refine sum_congr rfl (fun u _ => sum_congr rfl (fun q _ => sum_congr rfl
      (fun w _ => sum_congr rfl (fun r _ => ?_))))
    rw [ite_zero_mul_ite_zero, one_mul]
  rw [sum_congr rfl (fun t _ => h t)]
  exact Fin.sum_univ_eq_sum_range
    (fun i => (∑ u ∈ range (n + 1), (if i < u then (u : ℚ) else 0)) ^ 2) (n + 1)

theorem a_eq (n : ℕ) : (a n : ℚ) =
    ((n : ℚ) + 1) ^ 5 - 3 * (((n : ℚ) + 1) ^ 2 * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2) +
      ∑ t ∈ range (n + 1), (∑ u ∈ range (n + 1), (if t < u then (u : ℚ) else 0)) ^ 2 := by
  have h1 : ∑ x : Fin 5 → Fin (n + 1), (if x 0 < x 1 ∧ x 2 < x 1 then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) ^ 2 * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 := by
    rw [← (tup1 n).sum_comp]
    exact count_peak n
  have h2 : ∑ x : Fin 5 → Fin (n + 1), (if x 1 < x 2 ∧ x 3 < x 2 then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) ^ 2 * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 := by
    rw [← (tup2 n).sum_comp]
    exact count_peak n
  have h3 : ∑ x : Fin 5 → Fin (n + 1), (if x 2 < x 3 ∧ x 4 < x 3 then (1 : ℚ) else 0) =
      ((n : ℚ) + 1) ^ 2 * ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 := by
    rw [← (tup3 n).sum_comp]
    exact count_peak n
  have h13 : ∑ x : Fin 5 → Fin (n + 1),
      (if (x 2 < x 1 ∧ x 0 < x 1) ∧ (x 2 < x 3 ∧ x 4 < x 3) then (1 : ℚ) else 0) =
      ∑ t ∈ range (n + 1), (∑ u ∈ range (n + 1), (if t < u then (u : ℚ) else 0)) ^ 2 := by
    rw [← (tup13 n).sum_comp]
    exact count_double n
  have hsplit : ∀ x : Fin 5 → Fin (n + 1), (if NoPeak x then (1 : ℚ) else 0) =
      1 - (if x 0 < x 1 ∧ x 2 < x 1 then 1 else 0) - (if x 1 < x 2 ∧ x 3 < x 2 then 1 else 0)
        - (if x 2 < x 3 ∧ x 4 < x 3 then 1 else 0)
        + (if (x 2 < x 1 ∧ x 0 < x 1) ∧ (x 2 < x 3 ∧ x 4 < x 3) then 1 else 0) := by
    intro x
    have hN : NoPeak x ↔
        ¬ (x 0 < x 1 ∧ x 2 < x 1) ∧ ¬ (x 1 < x 2 ∧ x 3 < x 2) ∧ ¬ (x 2 < x 3 ∧ x 4 < x 3) :=
      Iff.rfl
    by_cases p1 : x 0 < x 1 ∧ x 2 < x 1
    · have p2 : ¬ (x 1 < x 2 ∧ x 3 < x 2) := fun h => lt_asymm p1.2 h.1
      by_cases p3 : x 2 < x 3 ∧ x 4 < x 3
      · have p13 : (x 2 < x 1 ∧ x 0 < x 1) ∧ (x 2 < x 3 ∧ x 4 < x 3) := ⟨⟨p1.2, p1.1⟩, p3⟩
        have hn : ¬ NoPeak x := fun h => (hN.1 h).1 p1
        rw [if_neg hn, if_pos p1, if_neg p2, if_pos p3, if_pos p13]
        norm_num
      · have p13 : ¬ ((x 2 < x 1 ∧ x 0 < x 1) ∧ (x 2 < x 3 ∧ x 4 < x 3)) := fun h => p3 h.2
        have hn : ¬ NoPeak x := fun h => (hN.1 h).1 p1
        rw [if_neg hn, if_pos p1, if_neg p2, if_neg p3, if_neg p13]
        norm_num
    · have p13 : ¬ ((x 2 < x 1 ∧ x 0 < x 1) ∧ (x 2 < x 3 ∧ x 4 < x 3)) :=
        fun h => p1 ⟨h.1.2, h.1.1⟩
      by_cases p2 : x 1 < x 2 ∧ x 3 < x 2
      · have p3 : ¬ (x 2 < x 3 ∧ x 4 < x 3) := fun h => lt_asymm p2.2 h.1
        have hn : ¬ NoPeak x := fun h => (hN.1 h).2.1 p2
        rw [if_neg hn, if_neg p1, if_pos p2, if_neg p3, if_neg p13]
        norm_num
      · by_cases p3 : x 2 < x 3 ∧ x 4 < x 3
        · have hn : ¬ NoPeak x := fun h => (hN.1 h).2.2 p3
          rw [if_neg hn, if_neg p1, if_neg p2, if_pos p3, if_neg p13]
          norm_num
        · have hn : NoPeak x := hN.2 ⟨p1, p2, p3⟩
          rw [if_pos hn, if_neg p1, if_neg p2, if_neg p3, if_neg p13]
          norm_num
  have hcard : (a n : ℚ) = ∑ x : Fin 5 → Fin (n + 1), (if NoPeak x then (1 : ℚ) else 0) := by
    unfold a
    rw [natCast_card_filter]
  rw [hcard, sum_congr rfl (fun x _ => hsplit x), sum_add_distrib, sum_sub_distrib,
    sum_sub_distrib, sum_sub_distrib, h1, h2, h3, h13]
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem sum_sq (n : ℕ) :
    ∑ v ∈ range (n + 1), (v : ℚ) ^ 2 = (n : ℚ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- `Sum_{t < u ≤ m} u = (m (m + 1) - t (t + 1)) / 2` for `t ≤ m`. -/
theorem sum_above (m : ℕ) : ∀ t : ℕ, t ≤ m →
    ∑ u ∈ range (m + 1), (if t < u then (u : ℚ) else 0) =
      ((m : ℚ) * (m + 1) - (t : ℚ) * (t + 1)) / 2 := by
  induction m with
  | zero =>
    intro t ht
    have ht0 : t = 0 := by omega
    subst ht0
    simp
  | succ k ih =>
    intro t ht
    rcases Nat.lt_or_ge t (k + 1) with htk | htk
    · rw [sum_range_succ, ih t (by omega), if_pos htk]
      push_cast
      ring
    · have hteq : t = k + 1 := by omega
      subst hteq
      rw [sum_eq_zero]
      · ring
      · intro u hu
        rw [mem_range] at hu
        rw [if_neg (by omega)]

/-- `Sum_{t < k} ((c - t (t + 1)) / 2)^2` in closed form. -/
theorem sum_sq_above (c : ℚ) (k : ℕ) :
    ∑ t ∈ range k, ((c - (t : ℚ) * (t + 1)) / 2) ^ 2 =
      (k * c ^ 2 - 2 * c * ((k - 1) * k * (k + 1) / 3) +
        (k - 1) * k * (k + 1) * (3 * k ^ 2 - 2) / 15) / 4 := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem a_formula (n : ℕ) : (a n : ℚ) =
    2 / 15 * n ^ 5 + 11 / 6 * n ^ 4 + 35 / 6 * n ^ 3 + 23 / 3 * n ^ 2 + 68 / 15 * n + 1 := by
  have hD : ∑ t ∈ range (n + 1), (∑ u ∈ range (n + 1), (if t < u then (u : ℚ) else 0)) ^ 2 =
      ∑ t ∈ range (n + 1), (((n : ℚ) * (n + 1) - (t : ℚ) * (t + 1)) / 2) ^ 2 := by
    refine sum_congr rfl (fun t ht => ?_)
    rw [sum_above n t (by rw [mem_range] at ht; omega)]
  rw [a_eq, hD, sum_sq, sum_sq_above]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  have hQ : (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega]
    rw [a_formula (k + 7), a_formula (k + 6), a_formula (k + 5), a_formula (k + 4),
      a_formula (k + 3), a_formula (k + 2), a_formula (k + 1)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (21 - 5 * X + 11 * X ^ 2 - 16 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have key : A * (1 - X) ^ 6 =
      A * X ^ 0 - C (6 : ℚ) * (A * X ^ 1) + C (15 : ℚ) * (A * X ^ 2) - C (20 : ℚ) * (A * X ^ 3) +
        C (15 : ℚ) * (A * X ^ 4) - C (6 : ℚ) * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℚ) * (21 - 5 * X + 11 * X ^ 2 - 16 * X ^ 3 + 6 * X ^ 4 - X ^ 5) =
      C (21 : ℚ) * X ^ 1 - C (5 : ℚ) * X ^ 2 + C (11 : ℚ) * X ^ 3 - C (16 : ℚ) * X ^ 4 +
        C (6 : ℚ) * X ^ 5 - C (1 : ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [a_formula]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega, if_true, if_false]
    rw [a_formula (j + 7), a_formula (j + 6), a_formula (j + 5), a_formula (j + 4),
      a_formula (j + 3), a_formula (j + 2), a_formula (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a200888.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
