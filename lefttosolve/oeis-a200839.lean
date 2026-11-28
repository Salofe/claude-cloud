import OMAStatements.S_oeis_a200839

/-!
Proof of Barker's conjectures for A200839 (arrays x(0..3) with entries in 0..n without two
consecutive increases or two consecutive decreases).

Write `Ok3 a b c` for: neither `a < b < c` nor `a > b > c`. An array `(s, u, v, t)` is good iff
`Ok3 s u v` and `Ok3 u v t` (`good_iff`), so `a n` is a four-fold sum of products of indicators,
which we order with the third entry `v` outermost (`a_eq`). For fixed `u, v` the number of
`s ∈ 0..n` with `Ok3 s u v` is `g n u v`, equal to `n + 1 - u`, `n + 1` or `u + 1` according as
`u < v`, `u = v` or `u > v` (`g_lt`, `g_eq`, `g_gt`); by reversal (`Ok3_symm`) the number of `t`
with `Ok3 u v t` is `g n v u`, and `s`, `t` are chosen independently (`inner_eq`). So the arrays
with third entry `v` number `Sum_u g n u v * g n v u`. Splitting the sum over `u ∈ 0..n` at `v`
(`split3`) and summing the arithmetic progressions gives the closed form `Q n v` (`inner_closed`),
a polynomial in `n` and `v`; summing it over `v ≤ n` (`sum_Q`) gives, for every `n`,
  a(n) = (5/12) n^4 + (19/6) n^3 + (79/12) n^2 + (29/6) n + 1   (`closedQ`),
i.e. 12 a(n) = 5n^4 + 38n^3 + 79n^2 + 58n + 12. The recurrence and the generating function follow
by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a200839 Finset

/-- No two consecutive increases and no two consecutive decreases at `a, b, c`. -/
def Ok3 (a b c : ℕ) : Prop := ¬ (a < b ∧ b < c) ∧ ¬ (a > b ∧ b > c)

instance decOk3 (a b c : ℕ) : Decidable (Ok3 a b c) := by
  unfold Ok3
  infer_instance

theorem Ok3_symm (a b c : ℕ) : Ok3 a b c ↔ Ok3 c b a := by
  unfold Ok3
  omega

theorem good_iff {n : ℕ} (x : Fin 4 → Fin (n + 1)) :
    Good x ↔ Ok3 (x 0) (x 1) (x 2) ∧ Ok3 (x 1) (x 2) (x 3) := by
  unfold Good Ok3
  simp only [Fin.lt_def, gt_iff_lt]
  constructor
  · intro h
    exact ⟨h 0 1 2 rfl rfl, h 1 2 3 rfl rfl⟩
  · rintro ⟨h1, h2⟩ ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk
    simp only at hij hjk
    subst hij hjk
    have hi2 : i < 2 := by omega
    interval_cases i
    · exact h1
    · exact h2

/-- The array with entries `s, u, v, t`, listed as `(v, u, s, t)`. -/
def tup (n : ℕ) : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃
    (Fin 4 → Fin (n + 1)) where
  toFun p := ![p.2.2.1, p.2.1, p.1, p.2.2.2]
  invFun x := (x 2, x 1, x 0, x 3)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

theorem ite2 (A B : Prop) [Decidable A] [Decidable B] :
    (if A ∧ B then (1 : ℚ) else 0) = (if A then 1 else 0) * (if B then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

theorem a_eq (n : ℕ) : (a n : ℚ) =
    ∑ v ∈ range (n + 1), ∑ u ∈ range (n + 1), ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
      (if Ok3 s u v then (1 : ℚ) else 0) * (if Ok3 u v t then 1 else 0) := by
  classical
  have h1 : (a n : ℚ) = ∑ x : Fin 4 → Fin (n + 1), if Good x then (1 : ℚ) else 0 := by
    unfold a
    rw [Fintype.card_subtype, Finset.natCast_card_filter]
  rw [h1, ← (tup n).sum_comp]
  simp only [Fintype.sum_prod_type, Finset.sum_range]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [← ite2]
  refine if_congr ?_ rfl rfl
  rw [good_iff]
  rfl

/-- Splitting a sum over `0..v+k` into the parts below `v`, at `v`, and above `v`. -/
theorem split3 (f : ℕ → ℚ) (v k : ℕ) :
    ∑ u ∈ range (v + k + 1), f u = ∑ u ∈ range v, f u + f v + ∑ j ∈ range k, f (v + 1 + j) := by
  rw [show v + k + 1 = v + 1 + k by ring, Finset.sum_range_add, Finset.sum_range_succ]

theorem sum_sub (c : ℚ) (m : ℕ) : ∑ i ∈ range m, (c - i) = m * c - m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_add (c : ℚ) (m : ℕ) : ∑ i ∈ range m, (c + i) = m * c + m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `g n u v`: the number of `s ∈ 0..n` with `Ok3 s u v`. -/
def g (n u v : ℕ) : ℚ := ∑ s ∈ range (n + 1), if Ok3 s u v then 1 else 0

theorem g_lt {n u v : ℕ} (huv : u < v) (hv : v ≤ n) : g n u v = n + 1 - u := by
  obtain ⟨k, rfl⟩ : ∃ k, n = u + k := ⟨n - u, by omega⟩
  unfold g
  rw [split3]
  have h1 : ∑ s ∈ range u, (if Ok3 s u v then (1 : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun s hs => if_neg (by have := mem_range.1 hs; unfold Ok3; omega)
  have h3 : ∑ j ∈ range k, (if Ok3 (u + 1 + j) u v then (1 : ℚ) else 0) = k := by
    rw [Finset.sum_congr rfl fun j _ => if_pos (by unfold Ok3; omega)]
    simp
  rw [h1, h3, if_pos (by unfold Ok3; omega)]
  push_cast
  ring

theorem g_eq (n v : ℕ) : g n v v = n + 1 := by
  unfold g
  rw [Finset.sum_congr rfl fun s _ => if_pos (by unfold Ok3; omega)]
  simp

theorem g_gt {n u v : ℕ} (hvu : v < u) (hu : u ≤ n) : g n u v = u + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = u + k := ⟨n - u, by omega⟩
  unfold g
  rw [split3]
  have h1 : ∑ s ∈ range u, (if Ok3 s u v then (1 : ℚ) else 0) = u := by
    rw [Finset.sum_congr rfl fun s hs =>
      if_pos (by have := mem_range.1 hs; unfold Ok3; omega)]
    simp
  have h3 : ∑ j ∈ range k, (if Ok3 (u + 1 + j) u v then (1 : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (by unfold Ok3; omega)
  rw [h1, h3, if_pos (by unfold Ok3; omega)]
  ring

/-- For fixed inner entries `u, v`, the outer entries `s` and `t` are chosen independently. -/
theorem inner_eq (n u v : ℕ) :
    ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
      (if Ok3 s u v then (1 : ℚ) else 0) * (if Ok3 u v t then 1 else 0) = g n u v * g n v u := by
  have ht : ∑ t ∈ range (n + 1), (if Ok3 u v t then (1 : ℚ) else 0) = g n v u := by
    unfold g
    exact Finset.sum_congr rfl fun t _ => if_congr (Ok3_symm u v t) rfl rfl
  rw [Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm, ht, ← Finset.sum_mul]
  rfl

/-- `Slt n v`: the sum of `n + 1 - u` over `u < v`. -/
def Slt (n v : ℕ) : ℚ := (v : ℚ) * ((n : ℚ) + 1) - (v : ℚ) * ((v : ℚ) - 1) / 2

/-- `Sgt n v`: the sum of `u + 1` over `v < u ≤ n`. -/
def Sgt (n v : ℕ) : ℚ :=
  ((n : ℚ) - v) * ((v : ℚ) + 2) + ((n : ℚ) - v) * ((n : ℚ) - v - 1) / 2

/-- The number of good arrays with third entry `v`, in closed form. -/
def Q (n v : ℕ) : ℚ :=
  ((v : ℚ) + 1) * Slt n v + ((n : ℚ) + 1) ^ 2 + ((n : ℚ) + 1 - v) * Sgt n v

theorem inner_closed {n v : ℕ} (hv : v ≤ n) :
    ∑ u ∈ range (n + 1), g n u v * g n v u = Q n v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = v + k := ⟨n - v, by omega⟩
  rw [split3]
  have h1 : ∑ u ∈ range v, g (v + k) u v * g (v + k) v u =
      ∑ u ∈ range v, ((((v + k : ℕ) : ℚ) + 1 - u) * ((v : ℚ) + 1)) :=
    Finset.sum_congr rfl fun u hu => by
      rw [g_lt (mem_range.1 hu) (by omega), g_gt (mem_range.1 hu) (by omega)]
  have h3 : ∑ j ∈ range k, g (v + k) (v + 1 + j) v * g (v + k) v (v + 1 + j) =
      ∑ j ∈ range k, ((((v : ℚ) + 2) + j) * (((v + k : ℕ) : ℚ) + 1 - v)) :=
    Finset.sum_congr rfl fun j hj => by
      rw [g_gt (by omega) (by have := mem_range.1 hj; omega),
        g_lt (by omega) (by have := mem_range.1 hj; omega)]
      push_cast
      ring
  rw [h1, h3, g_eq, ← Finset.sum_mul, ← Finset.sum_mul, sum_sub, sum_add]
  unfold Q Slt Sgt
  push_cast
  ring

/-- The partial sums of `Q n v` over `v < m`. -/
def PSum (n m : ℕ) : ℚ :=
  (m : ℚ) ^ 3 * n / 6 + 2 * (m : ℚ) ^ 3 / 3 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 / 4 -
    5 * (m : ℚ) ^ 2 * n / 4 - (m : ℚ) ^ 2 + (m : ℚ) * (n : ℚ) ^ 3 / 2 +
    13 * (m : ℚ) * (n : ℚ) ^ 2 / 4 + 55 * (m : ℚ) * n / 12 + 4 * (m : ℚ) / 3

theorem sum_Q (n m : ℕ) : ∑ v ∈ range m, Q n v = PSum n m := by
  induction m with
  | zero => simp [PSum]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold Q Slt Sgt PSum
    push_cast
    ring

theorem closedQ (n : ℕ) : (a n : ℚ) =
    5 / 12 * (n : ℚ) ^ 4 + 19 / 6 * (n : ℚ) ^ 3 + 79 / 12 * (n : ℚ) ^ 2 + 29 / 6 * n + 1 := by
  rw [a_eq, Finset.sum_congr rfl fun v hv =>
    (Finset.sum_congr rfl fun u _ => inner_eq n u v).trans
      (inner_closed (by have := mem_range.1 hv; omega)), sum_Q]
  unfold PSum
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
      a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  have h : ((a (m + 6) : ℤ) : ℚ) =
      ((5 * a (m + 5) - 10 * a (m + 4) + 10 * a (m + 3) - 5 * a (m + 2) + a (m + 1) : ℤ) :
        ℚ) := by
    push_cast
    simp only [closedQ]
    push_cast
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (16 - 11 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 5 * (PowerSeries.mk F * X ^ 1) +
        C 10 * (PowerSeries.mk F * X ^ 2) - C 10 * (PowerSeries.mk F * X ^ 3) +
        C 5 * (PowerSeries.mk F * X ^ 4) - C 1 * (PowerSeries.mk F * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (16 - 11 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) =
      C 16 * X ^ 1 - C 11 * X ^ 2 + C 9 * X ^ 3 - C 5 * X ^ 4 + C 1 * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega,
      show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ (j + 6), closedQ (j + 5), closedQ (j + 4), closedQ (j + 3), closedQ (j + 2),
      closedQ (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a200839.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
