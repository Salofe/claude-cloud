import OMAStatements.S_oeis_a207449
import Mathlib

/-!
Proof of the conjectures for A207449 (n X 4 binary arrays avoiding 0 0 0 and 0 0 1 horizontally
and 0 0 1 and 1 0 1 vertically).

An array is good iff every row satisfies the horizontal condition `Hr` and every three
consecutive rows satisfy the vertical condition `Vr` (`avoids_iff`). Removing the first row
gives a transfer recursion `T` on pairs of consecutive rows. Rows are coded by 0..15 and the
recursion becomes `G` on codes. For every pair of codes, `G m u v` is a polynomial of degree at
most 3 in `m`, one of six polynomials indexed by a type table; this is proved by induction with a
finite check per pair (`step_facts`). Summing gives `a n = 10 n (n^2 + n - 1)` for `n >= 1`, and
the recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207449 Finset

/-- A row of the array. -/
abbrev Row := Fin 4 → Fin 2

/-- Entry `j` of a row (`0` outside). -/
def gr (r : Row) (j : ℕ) : ℕ := if h : j < 4 then (r ⟨j, h⟩ : ℕ) else 0

/-- The horizontal condition on one row. -/
def Hr (r : Row) : Prop :=
  ∀ j < 2, (gr r j, gr r (j + 1), gr r (j + 2)) ≠ (0, 0, 0) ∧
    (gr r j, gr r (j + 1), gr r (j + 2)) ≠ (0, 0, 1)

/-- The vertical condition on three consecutive rows. -/
def Vr (p q r : Row) : Prop :=
  ∀ j < 4, (gr p j, gr q j, gr r j) ≠ (0, 0, 1) ∧ (gr p j, gr q j, gr r j) ≠ (1, 0, 1)

instance decHr (r : Row) : Decidable (Hr r) := by unfold Hr; infer_instance

instance decVr (p q r : Row) : Decidable (Vr p q r) := by unfold Vr; infer_instance

/-- Every row satisfies `Hr` and every three consecutive rows satisfy `Vr`. -/
def Good' {m : ℕ} (A : Fin m → Row) : Prop :=
  (∀ i : Fin m, Hr (A i)) ∧
    ∀ (i : ℕ) (h : i + 2 < m), Vr (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem get_eq {m : ℕ} (x : Fin m → Row) (i j : ℕ) :
    OMA.S_oeis_a207449.get x i j = if h : i < m then gr (x ⟨i, h⟩) j else 0 := by
  unfold OMA.S_oeis_a207449.get gr
  by_cases hi : i < m <;> by_cases hj : j < 4 <;> simp [hi, hj]

theorem avoids_iff {m : ℕ} (x : Fin m → Row) : avoids x = true ↔ Good' x := by
  unfold avoids Good' Hr Vr
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hj => ?_, fun i hi j hj => ?_⟩
    · have := h1 i.1 i.2 j (by omega)
      simpa only [get_eq, dif_pos i.2] using this
    · have := h2 i (by omega) j hj
      simpa only [get_eq, dif_pos (show i < m by omega), dif_pos (show i + 1 < m by omega),
        dif_pos hi] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · have := h1 ⟨i, hi⟩ j (by omega)
      simpa only [get_eq, dif_pos hi] using this
    · have := h2 i (by omega) j hj
      simpa only [get_eq, dif_pos (show i < m by omega), dif_pos (show i + 1 < m by omega),
        dif_pos (show i + 2 < m by omega)] using this

theorem good_cons {m : ℕ} (x : Row) (B : Fin (m + 2) → Row) :
    Good' (Fin.cons x B : Fin (m + 3) → Row) ↔
      Hr x ∧ Vr x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) ∧ Good' B := by
  constructor
  · rintro ⟨h1, h2⟩
    have h0 := h2 0 (by omega)
    exact ⟨h1 0, h0, fun i => h1 i.succ, fun i hi => h2 (i + 1) (by omega)⟩
  · rintro ⟨hx, hv, h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact hx
      · simpa using h1 j
    · cases i with
      | zero => exact hv
      | succ i => exact h2 i (by omega)

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
noncomputable def T (m : ℕ) (x y : Row) : ℕ := by
  classical
  exact ∑ B : Fin m → Row,
    if Good' (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) then 1 else 0

theorem T_zero (x y : Row) : T 0 x y = if Hr x ∧ Hr y then 1 else 0 := by
  classical
  unfold T
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, _⟩
    exact ⟨h1 0, h1 1⟩
  · rintro ⟨hx, hy⟩
    refine ⟨fun i => ?_, fun i hi => by omega⟩
    refine Fin.cases hx (fun j => ?_) i
    refine Fin.cases ?_ (fun k => k.elim0) j
    exact hy

theorem T_succ (m : ℕ) (x y : Row) :
    T (m + 1) x y = ∑ z : Row, if Hr x ∧ Vr x y z then T m y z else 0 := by
  classical
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good' (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : Hr x ∧ Vr x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons]
    exact fun h => hv ⟨h.1, h.2.1⟩

theorem a_eq (n : ℕ) : a (n + 2) = ((∑ x : Row, ∑ y : Row, T n x y : ℕ) : ℤ) := by
  classical
  have h1 : ((Finset.univ : Finset (Fin (n + 2) → Fin 4 → Fin 2)).filter
      (fun x => avoids x)).card = ∑ A : Fin (n + 2) → Row, if Good' A then 1 else 0 := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (avoids_iff A) rfl rfl
  have h2 : (∑ A : Fin (n + 2) → Row, if Good' A then 1 else 0) =
      ∑ x : Row, ∑ y : Row, T n x y := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun p => if Good' (Fin.cons p.1 p.2 : Fin (n + 2) → Row) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun p => if Good' (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  unfold a
  rw [h1, h2]

/-- The row with code `c`: the bits of `c`, most significant first. -/
def row (c : Fin 16) : Row := fun j => ⟨c.val / 2 ^ (3 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective : Function.Injective row := by
  decide

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- `Hr` on codes. -/
def Ht (u : Fin 16) : Bool := decide (Hr (row u))

/-- `Hr` and `Vr` on codes. -/
def Vt (u v w : Fin 16) : Bool := decide (Hr (row u)) && decide (Vr (row u) (row v) (row w))

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 16 → Fin 16 → ℕ
  | 0, u, v => if Ht u && Ht v then 1 else 0
  | m + 1, u, v => ∑ w : Fin 16, if Vt u v w then G m v w else 0

theorem T_eq_G (m : ℕ) : ∀ u v : Fin 16, T m (row u) (row v) = G m u v := by
  induction m with
  | zero =>
    intro u v
    rw [T_zero]
    simp only [G, Ht, Bool.and_eq_true, decide_eq_true_eq]
  | succ m ih =>
    intro u v
    rw [T_succ, ← row_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    refine if_congr ?_ rfl rfl
    simp only [Vt, Bool.and_eq_true, decide_eq_true_eq]

theorem a_eq_G (n : ℕ) : a (n + 2) = ((∑ u : Fin 16, ∑ v : Fin 16, G n u v : ℕ) : ℤ) := by
  have h : ∑ x : Row, ∑ y : Row, T n x y = ∑ u : Fin 16, ∑ v : Fin 16, G n u v := by
    rw [← row_bijective.sum_comp]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← row_bijective.sum_comp]
    exact Finset.sum_congr rfl fun v _ => T_eq_G n u v
  rw [a_eq, h]

/-- The types of the pairs of codes. -/
def tbl : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5, 0, 0, 0, 0, 1, 2, 2, 3, 0, 0, 1, 2, 2, 3, 4, 5]

/-- The type of the pair of codes `(u, v)` of two consecutive rows. -/
def typ (u v : Fin 16) : ℕ := tbl.getD (16 * u.val + v.val) 0

/-- Coefficient of `n ^ 3`. -/
def c3 (t : ℕ) : ℤ := if t = 5 then 1 else 0

/-- Coefficient of `n ^ 2`. -/
def c2 (t : ℕ) : ℤ := if t = 3 then 1 else if t = 4 then 1 else if t = 5 then 4 else 0

/-- Coefficient of `n`. -/
def c1 (t : ℕ) : ℤ :=
  if t = 2 then 1 else if t = 3 then 2 else if t = 4 then 3 else if t = 5 then 4 else 0

/-- Constant coefficient. -/
def c0 (t : ℕ) : ℤ := if t = 0 then 0 else 1

/-- The number of continuations by `n` rows of a pair of type `t`. -/
def P (t : ℕ) (n : ℤ) : ℤ := c3 t * n ^ 3 + c2 t * n ^ 2 + c1 t * n + c0 t

theorem step_facts : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt u v w then c3 (typ v w) else 0) = c3 (typ u v) ∧
    (∑ w : Fin 16, if Vt u v w then c2 (typ v w) else 0) = 3 * c3 (typ u v) + c2 (typ u v) ∧
    (∑ w : Fin 16, if Vt u v w then c1 (typ v w) else 0) =
      3 * c3 (typ u v) + 2 * c2 (typ u v) + c1 (typ u v) ∧
    (∑ w : Fin 16, if Vt u v w then c0 (typ v w) else 0) =
      c3 (typ u v) + c2 (typ u v) + c1 (typ u v) + c0 (typ u v) := by
  decide +kernel

theorem base_facts : ∀ u v : Fin 16, (G 0 u v : ℤ) = P (typ u v) 0 := by
  decide +kernel

theorem G_closed (n : ℕ) : ∀ u v : Fin 16, (G n u v : ℤ) = P (typ u v) n := by
  induction n with
  | zero => exact base_facts
  | succ n ih =>
    intro u v
    have hsum : (G (n + 1) u v : ℤ) =
        ∑ w : Fin 16, if Vt u v w then P (typ v w) n else 0 := by
      rw [G]
      push_cast
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs
      · exact ih v w
      · simp
    rw [hsum]
    have hP : ∀ w : Fin 16, (if Vt u v w then P (typ v w) n else 0) =
        (if Vt u v w then c3 (typ v w) else 0) * (n : ℤ) ^ 3 +
        (if Vt u v w then c2 (typ v w) else 0) * (n : ℤ) ^ 2 +
        (if Vt u v w then c1 (typ v w) else 0) * (n : ℤ) +
        (if Vt u v w then c0 (typ v w) else 0) := by
      intro w
      split_ifs <;> simp [P]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := step_facts u v
    rw [h3, h2, h1, h0]
    unfold P
    push_cast
    ring

theorem sum_facts :
    (∑ u : Fin 16, ∑ v : Fin 16, c3 (typ u v)) = 10 ∧
    (∑ u : Fin 16, ∑ v : Fin 16, c2 (typ u v)) = 70 ∧
    (∑ u : Fin 16, ∑ v : Fin 16, c1 (typ u v)) = 150 ∧
    (∑ u : Fin 16, ∑ v : Fin 16, c0 (typ u v)) = 100 := by
  decide +kernel

theorem a_one : a 1 = 10 := by
  decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = 10 * (n : ℤ) * ((n : ℤ) ^ 2 + n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_eq_G]
    push_cast
    simp only [G_closed m]
    simp only [P, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := sum_facts
    rw [h3, h2, h1, h0]
    ring

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = 10 * (n : ℚ) * ((n : ℚ) ^ 2 + n - 1) := by
  have h : ((a n : ℤ) : ℚ) = ((10 * (n : ℤ) * ((n : ℤ) ^ 2 + n - 1) : ℤ) : ℚ) := by
    rw [closed n hn]
  push_cast at h
  exact h

theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℚ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
    closedQ (n - 3) (by omega), closedQ (n - 4) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega]
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 4 : PowerSeries ℚ) =
      10 * X * (1 + 6 * X - X ^ 2) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 4 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 4 * (PowerSeries.mk F * X ^ 1) +
        C 6 * (PowerSeries.mk F * X ^ 2) - C 4 * (PowerSeries.mk F * X ^ 3) +
        C 1 * (PowerSeries.mk F * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (10 * X * (1 + 6 * X - X ^ 2) : ℚ⟦X⟧) =
      C 10 * X ^ 1 + C 60 * X ^ 2 - C 10 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 < 1) by omega, show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    rw [closedQ (j + 5) (by omega), closedQ (j + 4) (by omega), closedQ (j + 3) (by omega),
      closedQ (j + 2) (by omega), closedQ (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207449.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
