import OMAStatements.S_oeis_a207656

/-!
Proof of Barker's conjectures for A207656 (n X 3 binary arrays avoiding `0 0 0` and `1 1 1`
horizontally and `0 0 1` and `1 0 0` vertically).

Read the array row by row. The horizontal condition only involves one row (`ROK`), and the
vertical condition only involves three consecutive rows (`V`). Removing the first row
(`cons_iff`) gives a transfer recursion: if `T m x y` counts the arrays with `m + 2` rows whose
first two rows are `x, y`, then `T 0 x y = [ROK x ∧ ROK y]`,
`T (m + 1) x y = Sum_z [ROK x ∧ V x y z] T m y z`, and `a (m + 2) = Sum_{x, y} T m x y`.

Rows are coded by the numbers 0, ..., 7 (bit `j` of the code is the entry of column `j`). On
codes the two conditions become Boolean tests (`okr`, `Vt`), checked once against `ROK` and `V`
on all codes, and `G` is the same recursion on codes. The recursion is linear, so the identity
`G (m + 3) + G (m + 1) + G m = 3 G (m + 2)` (entrywise), checked for `m = 0` by a finite
computation, propagates to every `m` by induction. Summing over the pairs of codes gives
`a (m + 5) = 3 a (m + 4) - a (m + 3) - a (m + 2)`, and `a 1, ..., a 4 = 6, 36, 84, 198`.
The generating function follows by comparing coefficients, since
`(1 - x) (1 - 2x - x^2) = 1 - 3x + x^2 + x^3`. The closed form `f n` satisfies the same
recurrence (both `1 + √2` and `1 - √2` are roots of `x^2 - 2x - 1`, and
`x^3 - 3x^2 + x + 1 = (x - 1)(x^2 - 2x - 1)`) and `f 2, f 3, f 4 = 36, 84, 198`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207656 Finset

/-- A row of the array. -/
abbrev Row := Fin 3 → Bool

/-- The horizontal condition on a row. -/
def ROK (r : Row) : Prop := Avoids [(false, false, false), (true, true, true)] (r 0) (r 1) (r 2)

instance decROK (r : Row) : Decidable (ROK r) := by
  unfold ROK Avoids
  infer_instance

/-- The vertical condition on three consecutive rows. -/
def V (x y z : Row) : Prop := ∀ j : Fin 3, Avoids [(false, false, true), (true, false, false)]
  (x j) (y j) (z j)

instance decV (x y z : Row) : Decidable (V x y z) := by
  unfold V Avoids
  infer_instance

theorem rowcond_iff (r : Row) :
    (∀ j : ℕ, ∀ h : j + 2 < 3, Avoids [(false, false, false), (true, true, true)]
      (r ⟨j, by omega⟩) (r ⟨j + 1, by omega⟩) (r ⟨j + 2, h⟩)) ↔ ROK r := by
  constructor
  · intro h
    exact h 0 (by omega)
  · intro h j hj
    obtain rfl : j = 0 := by omega
    exact h

theorem cons_iff {m : ℕ} (x : Row) (B : Fin (m + 2) → Row) :
    IsCounted (m + 3) (Fin.cons x B : Fin (m + 3) → Row) ↔
      ROK x ∧ V x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) ∧ IsCounted (m + 2) B := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(rowcond_iff x).1 (h1 0), fun j => by have h := h2 0 (by omega) j; exact h,
      fun i => h1 i.succ, fun i hi j => h2 (i + 1) (by omega) j⟩
  · rintro ⟨hx, hv, h1, h2⟩
    refine ⟨fun i => ?_, fun i hi j => ?_⟩
    · rcases i with ⟨_ | i, hi⟩
      · exact (rowcond_iff x).2 hx
      · exact h1 ⟨i, by omega⟩
    · cases i with
      | zero => exact hv j
      | succ i => exact h2 i (by omega) j

theorem two_iff (x y : Row) (B : Fin 0 → Row) :
    IsCounted 2 (Fin.cons x (Fin.cons y B) : Fin 2 → Row) ↔ ROK x ∧ ROK y := by
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨(rowcond_iff x).1 (h1 0), (rowcond_iff y).1 (h1 1)⟩
  · rintro ⟨hx, hy⟩
    refine ⟨fun i => ?_, fun i hi => absurd hi (by omega)⟩
    rcases i with ⟨_ | _ | i, hi⟩
    · exact (rowcond_iff x).2 hx
    · exact (rowcond_iff y).2 hy
    · omega

theorem one_iff (A : Fin 1 → Row) : IsCounted 1 A ↔ ROK (A 0) := by
  constructor
  · rintro ⟨h1, -⟩
    exact (rowcond_iff _).1 (h1 0)
  · intro h
    refine ⟨fun i => ?_, fun i hi => absurd hi (by omega)⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (rowcond_iff _).2 h

/-- The number of arrays with `m + 2` rows whose first two rows are `x, y`. -/
noncomputable def T (m : ℕ) (x y : Row) : ℕ := by
  classical
  exact ∑ B : Fin m → Row,
    if IsCounted (m + 2) (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) then 1 else 0

theorem T_zero (x y : Row) : T 0 x y = if ROK x ∧ ROK y then 1 else 0 := by
  classical
  unfold T
  rw [Fintype.sum_unique]
  exact if_congr (two_iff x y _) rfl rfl

theorem T_succ (m : ℕ) (x y : Row) :
    T (m + 1) x y = ∑ z : Row, if ROK x ∧ V x y z then T m y z else 0 := by
  classical
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if IsCounted (m + 3) (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) :
      Fin (m + 3) → Row) then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : ROK x ∧ V x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [cons_iff]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [cons_iff]
    exact fun h => hv ⟨h.1, h.2.1⟩

open Classical in
theorem a_eq_sum (n : ℕ) : a n = ∑ A : Fin n → Row, if IsCounted n A then 1 else 0 := by
  classical
  unfold a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

theorem a_eq (n : ℕ) : a (n + 2) = ∑ x : Row, ∑ y : Row, T n x y := by
  classical
  rw [a_eq_sum, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if IsCounted (n + 2) (Fin.cons p.1 p.2 : Fin (n + 2) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if IsCounted (n + 2) (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row)
      then 1 else 0) (fun A => by simp), Fintype.sum_prod_type]
  rfl

theorem a_one_eq : a 1 = ∑ x : Row, if ROK x then 1 else 0 := by
  classical
  rw [a_eq_sum]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) Row) _ _
    (fun A => if_congr (one_iff A) rfl rfl)

/-- The row with code `u`: the entry of column `j` is bit `j` of `u`. -/
def row (u : Fin 8) : Row := fun j => Nat.testBit u.val j.val

theorem row_injective : Function.Injective row := by
  decide +kernel

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- `ROK` on codes. -/
def okr (u : Fin 8) : Bool := !(u.val == 0) && !(u.val == 7)

/-- `V` on codes: no column has a `0` in the middle row and different entries above and below. -/
def Vt (u v w : Fin 8) : Bool := (u.val ^^^ w.val) &&& (7 - v.val) == 0

theorem okr_iff : ∀ u : Fin 8, ROK (row u) ↔ okr u = true := by
  decide +kernel

theorem Vt_iff : ∀ u v w : Fin 8, (ROK (row u) ∧ V (row u) (row v) (row w)) ↔
    (okr u && Vt u v w) = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 8 → Fin 8 → ℕ
  | 0, u, v => if okr u && okr v then 1 else 0
  | m + 1, u, v => ∑ w : Fin 8, if okr u && Vt u v w then G m v w else 0

theorem T_eq_G (m : ℕ) : ∀ u v : Fin 8, T m (row u) (row v) = G m u v := by
  induction m with
  | zero =>
    intro u v
    rw [T_zero]
    simp only [G]
    refine if_congr ?_ rfl rfl
    rw [okr_iff, okr_iff, Bool.and_eq_true]
  | succ m ih =>
    intro u v
    rw [T_succ, ← row_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    exact if_congr (Vt_iff u v w) rfl rfl

theorem a_eq_G (n : ℕ) : a (n + 2) = ∑ u : Fin 8, ∑ v : Fin 8, G n u v := by
  rw [a_eq, ← row_bijective.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← row_bijective.sum_comp]
  exact Finset.sum_congr rfl fun v _ => T_eq_G n u v

theorem G_succ (k : ℕ) (u v : Fin 8) :
    G (k + 1) u v = ∑ w : Fin 8, if okr u && Vt u v w then G k v w else 0 := rfl

theorem G_base : ∀ u v : Fin 8, G 3 u v + G 1 u v + G 0 u v = 3 * G 2 u v := by
  decide +kernel

theorem G_rec (m : ℕ) : ∀ u v : Fin 8, G (m + 3) u v + G (m + 1) u v + G m u v =
    3 * G (m + 2) u v := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u v
    show G ((m + 3) + 1) u v + G ((m + 1) + 1) u v + G (m + 1) u v = 3 * G ((m + 2) + 1) u v
    rw [G_succ (m + 3), G_succ (m + 1), G_succ m, G_succ (m + 2), ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih v w
    · rfl

theorem a_rec (m : ℕ) : a (m + 5) + a (m + 3) + a (m + 2) = 3 * a (m + 4) := by
  rw [show m + 5 = (m + 3) + 2 by omega, show m + 4 = (m + 2) + 2 by omega,
    show m + 3 = (m + 1) + 2 by omega, a_eq_G, a_eq_G, a_eq_G, a_eq_G, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => G_rec m u v

theorem a_one : a 1 = 6 := by
  rw [a_one_eq, ← row_bijective.sum_comp]
  rw [Finset.sum_congr rfl fun u _ => if_congr (okr_iff u) rfl rfl]
  decide +kernel

theorem a_two : a 2 = 36 := by
  rw [a_eq_G]
  decide +kernel

theorem a_three : a 3 = 84 := by
  rw [a_eq_G]
  decide +kernel

theorem a_four : a 4 = 198 := by
  rw [a_eq_G]
  decide +kernel

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2)) =
      6 * PowerSeries.X * (1 + 3 * PowerSeries.X - 3 * PowerSeries.X ^ 2 -
        2 * PowerSeries.X ^ 3) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * ((1 - X) * (1 - 2 * X - X ^ 2)) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 3 * (PowerSeries.mk F * X ^ 1) +
        C 1 * (PowerSeries.mk F * X ^ 2) + C 1 * (PowerSeries.mk F * X ^ 3) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (6 : ℚ⟦X⟧) * X * (1 + 3 * X - 3 * X ^ 2 - 2 * X ^ 3) =
      C 6 * X ^ 1 + C 18 * X ^ 2 - C 18 * X ^ 3 - C 12 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hF, a_one, a_two, a_three, a_four]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    have hr : ((a (j + 5) + a (j + 3) + a (j + 2) : ℕ) : ℚ) = ((3 * a (j + 4) : ℕ) : ℚ) := by
      rw [a_rec j]
    push_cast at hr
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      if_true, if_false, hF]
    linarith

/-- The closed form of the statement. -/
noncomputable def f (n : ℕ) : ℝ :=
  3 / 2 * (2 + (1 - 2 * Real.sqrt 2) * (1 - Real.sqrt 2) ^ n +
    (1 + Real.sqrt 2) ^ n * (1 + 2 * Real.sqrt 2))

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem f_rec (n : ℕ) : f (n + 3) = 3 * f (n + 2) - f (n + 1) - f n := by
  unfold f
  have hs := sqrt_two_sq
  set s := Real.sqrt 2
  linear_combination (3 / 2 * ((1 - 2 * s) * (1 - s) ^ n * (-s) + (1 + 2 * s) * (1 + s) ^ n * s)) * hs

theorem f_zero : f 0 = 6 := by
  unfold f
  ring

theorem f_one : f 1 = 18 := by
  unfold f
  have hs := sqrt_two_sq
  set s := Real.sqrt 2
  linear_combination 6 * hs

theorem f_two : f 2 = 36 := by
  unfold f
  have hs := sqrt_two_sq
  set s := Real.sqrt 2
  linear_combination 15 * hs

theorem f_three : f 3 = 84 := by
  rw [f_rec 0, f_two, f_one, f_zero]
  norm_num

theorem f_four : f 4 = 198 := by
  rw [f_rec 1, f_three, f_two, f_one]
  norm_num

theorem closed_aux (m : ℕ) :
    (a (m + 2) : ℝ) = f (m + 2) ∧ (a (m + 3) : ℝ) = f (m + 3) ∧ (a (m + 4) : ℝ) = f (m + 4) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a_two, f_two]
      norm_num
    · rw [a_three, f_three]
      norm_num
    · rw [a_four, f_four]
      norm_num
  | succ m ih =>
    obtain ⟨h2, h3, h4⟩ := ih
    refine ⟨h3, h4, ?_⟩
    have hr : ((a (m + 5) + a (m + 3) + a (m + 2) : ℕ) : ℝ) = ((3 * a (m + 4) : ℕ) : ℝ) := by
      rw [a_rec m]
    push_cast at hr
    have hf := f_rec (m + 2)
    rw [show m + 1 + 4 = m + 5 by omega, show m + 2 + 3 = m + 5 by omega,
      show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega] at *
    linarith

theorem closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℝ) = 3 / 2 * (2 + (1 - 2 * Real.sqrt 2) *
    (1 - Real.sqrt 2) ^ n + (1 + Real.sqrt 2) ^ n * (1 + 2 * Real.sqrt 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact (closed_aux m).1

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207656.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed⟩
