import OMAStatements.S_oeis_a207389

/-!
Proof of the conjectured generating function and recurrence of A207389 (n X 6 binary arrays
avoiding 0 0 1 and 0 1 0 horizontally and 0 0 1 and 1 1 0 vertically).

Read the array row by row. The horizontal condition is a condition `RowOK` on each row and the
vertical condition is a condition `ColOK` on each three consecutive rows, so `avoids` is the
conjunction of these (`avoids_iff`). Removing the first row (`good_cons`) gives a transfer
recursion: if `T m x y` counts the ways to continue the rows `x, y` by `m` more rows, then
`T (m + 1) x y = Sum_z [RowOK x and ColOK x y z] T m y z`, and `a (m + 2) = Sum_{x, y} T m x y`.

Exactly 21 rows of length 6 satisfy `RowOK`; they are listed by their codes (bit `j` of the code
is the entry of column `j`) in `codes`, and `H` is the transfer recursion on pairs of indices of
valid rows. For every pair `(p, q)`, `360 * H m p q` is a polynomial `P (typ p q) m` of degree at
most 6 in `m`, one of 36 explicit polynomials (`typ`, `cf`). This is proved by induction on `m`;
the step reduces to seven identities between coefficients for each pair (a finite check).
Summing over the 441 pairs gives `360 a(n) = Q(n - 2)` for `n ≥ 2` with an explicit sextic `Q`;
this also holds for `n = 1` since `a 1 = 21`. The recurrence and the generating function follow by
comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207389 Finset

/-- A row of the array. -/
abbrev Row := Fin 6 → Fin 2

/-- Entry `j` of a row as a natural number (`0` outside the row). -/
def g (x : Row) (j : ℕ) : ℕ := if h : j < 6 then (x ⟨j, h⟩ : ℕ) else 0

/-- The horizontal condition on one row. -/
def RowOK (x : Row) : Prop :=
  ∀ j < 4, (g x j, g x (j + 1), g x (j + 2)) ≠ (0, 0, 1) ∧
    (g x j, g x (j + 1), g x (j + 2)) ≠ (0, 1, 0)

/-- The vertical condition on three consecutive rows. -/
def ColOK (x y z : Row) : Prop :=
  ∀ j < 6, (g x j, g y j, g z j) ≠ (0, 0, 1) ∧ (g x j, g y j, g z j) ≠ (1, 1, 0)

instance decRowOK (x : Row) : Decidable (RowOK x) := by
  unfold RowOK
  infer_instance

instance decColOK (x y z : Row) : Decidable (ColOK x y z) := by
  unfold ColOK
  infer_instance

/-- Every row satisfies `RowOK` and every three consecutive rows satisfy `ColOK`. -/
def Good {m : ℕ} (A : Fin m → Row) : Prop :=
  (∀ i : Fin m, RowOK (A i)) ∧
    ∀ (i : ℕ) (h : i + 2 < m), ColOK (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem get_eq {r : ℕ} (x : Fin r → Row) (i j : ℕ) (hi : i < r) :
    OMA.S_oeis_a207389.get x i j = g (x ⟨i, hi⟩) j := by
  unfold OMA.S_oeis_a207389.get g
  by_cases hj : j < 6
  · rw [dif_pos ⟨hi, hj⟩, dif_pos hj]
  · rw [dif_neg (fun h => hj h.2), dif_neg hj]

theorem avoids_iff {r : ℕ} (x : Fin r → Row) : avoids x = true ↔ Good x := by
  unfold avoids Good
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hj => ?_, fun i hi j hj => ?_⟩
    · have h := h1 i.val i.isLt j (by omega)
      rw [get_eq x i.val j i.isLt, get_eq x i.val (j + 1) i.isLt,
        get_eq x i.val (j + 2) i.isLt] at h
      exact h
    · have h := h2 i (by omega) j hj
      rw [get_eq x i j (by omega), get_eq x (i + 1) j (by omega), get_eq x (i + 2) j hi] at h
      exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [get_eq x i j hi, get_eq x i (j + 1) hi, get_eq x i (j + 2) hi]
      exact h1 ⟨i, hi⟩ j (by omega)
    · rw [get_eq x i j (by omega), get_eq x (i + 1) j (by omega),
        get_eq x (i + 2) j (by omega)]
      exact h2 i (by omega) j hj

theorem good_cons {m : ℕ} (x : Row) (A : Fin (m + 2) → Row) :
    Good (Fin.cons x A : Fin (m + 3) → Row) ↔
      RowOK x ∧ ColOK x (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) ∧ Good A := by
  constructor
  · rintro ⟨h1, h2⟩
    have h0 := h1 (⟨0, by omega⟩ : Fin (m + 3))
    have hc := h2 0 (by omega)
    refine ⟨h0, hc, fun i => h1 i.succ, fun i hi => ?_⟩
    have h3 := h2 (i + 1) (by omega)
    exact h3
  · rintro ⟨hx, hc, h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · rcases i with ⟨_ | k, hk⟩
      · exact hx
      · exact h1 ⟨k, by omega⟩
    · cases i with
      | zero => exact hc
      | succ i =>
        have h3 := h2 i (by omega)
        exact h3

/-- The number of `m`-row arrays satisfying `Good`. -/
noncomputable def cnt (m : ℕ) : ℕ := by
  classical
  exact ∑ A : Fin m → Row, if Good A then 1 else 0

theorem a_eq_cnt (n : ℕ) : a n = (cnt n : ℤ) := by
  classical
  unfold a cnt
  congr 1
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun A _ => if_congr (avoids_iff A) rfl rfl

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
noncomputable def T (m : ℕ) (x y : Row) : ℕ := by
  classical
  exact ∑ B : Fin m → Row, if Good (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) then 1 else 0

theorem T_zero (x y : Row) : T 0 x y = if RowOK x ∧ RowOK y then 1 else 0 := by
  classical
  unfold T
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, -⟩
    have h0 := h1 (⟨0, by omega⟩ : Fin 2)
    have h1' := h1 (⟨1, by omega⟩ : Fin 2)
    exact ⟨h0, h1'⟩
  · rintro ⟨hx, hy⟩
    refine ⟨fun i => ?_, fun i hi => by omega⟩
    rcases i with ⟨_ | _ | k, hk⟩
    · exact hx
    · exact hy
    · omega

theorem T_succ (m : ℕ) (x y : Row) :
    T (m + 1) x y = ∑ z : Row, if RowOK x ∧ ColOK x y z then T m y z else 0 := by
  classical
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : RowOK x ∧ ColOK x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons]
    exact fun h => hv ⟨h.1, h.2.1⟩

theorem T_bad_left (m : ℕ) (y z : Row) (hy : ¬ RowOK y) : T m y z = 0 := by
  classical
  unfold T
  refine Finset.sum_eq_zero fun B _ => if_neg fun h => hy ?_
  have h0 := h.1 (⟨0, by omega⟩ : Fin (m + 2))
  exact h0

theorem T_bad_right (m : ℕ) (y z : Row) (hz : ¬ RowOK z) : T m y z = 0 := by
  classical
  unfold T
  refine Finset.sum_eq_zero fun B _ => if_neg fun h => hz ?_
  have h0 := h.1 (⟨1, by omega⟩ : Fin (m + 2))
  exact h0

theorem cnt_eq (m : ℕ) : cnt (m + 2) = ∑ x : Row, ∑ y : Row, T m x y := by
  classical
  unfold cnt
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good (Fin.cons p.1 p.2 : Fin (m + 2) → Row) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good (Fin.cons x (Fin.cons p.1 p.2) : Fin (m + 2) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

/-- The codes of the 21 rows satisfying `RowOK` (bit `j` of a code is the entry of column `j`). -/
def codes : List ℕ := [0, 1, 3, 6, 7, 13, 14, 15, 27, 29, 30, 31, 45, 46, 47, 54, 55, 59, 61, 62, 63]

/-- The valid row with index `c`. -/
def vr (c : Fin 21) : Row := fun j => ⟨codes.getD c.val 0 / 2 ^ j.val % 2, Nat.mod_lt _ (by norm_num)⟩

theorem vr_injective : Function.Injective vr := by
  decide +kernel

theorem vr_ok : ∀ c : Fin 21, RowOK (vr c) := by
  decide +kernel

theorem vr_complete : ∀ x : Row, RowOK x → ∃ c : Fin 21, vr c = x := by
  decide +kernel

theorem sum_valid {M : Type*} [AddCommMonoid M] (f : Row → M) :
    (∑ x : Row, if RowOK x then f x else 0) = ∑ c : Fin 21, f (vr c) := by
  rw [← Finset.sum_filter]
  have himg : (Finset.univ.filter RowOK) = Finset.univ.image vr := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · exact vr_complete x
    · rintro ⟨c, rfl⟩
      exact vr_ok c
  rw [himg, Finset.sum_image vr_injective.injOn]

/-- `ColOK` on indices of valid rows. -/
def cb (p q w : Fin 21) : Bool := decide (ColOK (vr p) (vr q) (vr w))

/-- The transfer recursion on indices of valid rows. -/
def H : ℕ → Fin 21 → Fin 21 → ℕ
  | 0, _, _ => 1
  | m + 1, p, q => ∑ w : Fin 21, if cb p q w then H m q w else 0

theorem T_eq_H (m : ℕ) : ∀ p q : Fin 21, T m (vr p) (vr q) = H m p q := by
  induction m with
  | zero =>
    intro p q
    rw [T_zero, if_pos ⟨vr_ok p, vr_ok q⟩]
    rfl
  | succ m ih =>
    intro p q
    rw [T_succ]
    have h1 : ∀ z : Row, (if RowOK (vr p) ∧ ColOK (vr p) (vr q) z then T m (vr q) z else 0) =
        if RowOK z then (if ColOK (vr p) (vr q) z then T m (vr q) z else 0) else 0 := by
      intro z
      by_cases hz : RowOK z
      · rw [if_pos hz]
        exact if_congr ⟨fun h => h.2, fun h => ⟨vr_ok p, h⟩⟩ rfl rfl
      · rw [if_neg hz, T_bad_right m _ _ hz]
        simp
    rw [Finset.sum_congr rfl fun z _ => h1 z, sum_valid]
    simp only [H]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih q w]
    exact if_congr (by simp [cb]) rfl rfl

theorem cnt_eq_H (m : ℕ) : cnt (m + 2) = ∑ p : Fin 21, ∑ q : Fin 21, H m p q := by
  rw [cnt_eq]
  have e1 : ∀ x : Row, (∑ y : Row, T m x y) = ∑ q : Fin 21, T m x (vr q) := by
    intro x
    rw [← sum_valid]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : RowOK y
    · rw [if_pos hy]
    · rw [if_neg hy, T_bad_right m x y hy]
  have e2 : (∑ x : Row, ∑ q : Fin 21, T m x (vr q)) =
      ∑ p : Fin 21, ∑ q : Fin 21, T m (vr p) (vr q) := by
    rw [← sum_valid (fun x => ∑ q : Fin 21, T m x (vr q))]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : RowOK x
    · rw [if_pos hx]
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun q _ => T_bad_left m x _ hx
  rw [Finset.sum_congr rfl fun x _ => e1 x, e2]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => T_eq_H m p q

theorem cnt_one : cnt 1 = 21 := by
  classical
  unfold cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Row) _ (fun x => if RowOK x then 1 else 0)
    (fun A => ?_)]
  · rw [sum_valid]
    simp
  · refine if_congr ⟨fun h => h.1 default, fun h => ⟨fun i => ?_, fun i hi => by omega⟩⟩ rfl rfl
    rw [Subsingleton.elim i default]
    exact h

/-- The type of each pair of indices of valid rows. -/
def typs : List (List ℕ) := [[0, 1, 2, 1, 3, 2, 2, 4, 5, 5, 5, 6, 5, 5, 7, 2, 8, 9, 10, 11, 12], [1, 0, 1, 3, 2, 1, 13, 3, 2, 2, 14, 4, 2, 15, 8, 11, 5, 5, 16, 17, 18], [2, 1, 0, 2, 1, 3, 16, 2, 1, 13, 19, 3, 11, 20, 5, 16, 2, 2, 21, 22, 23], [1, 3, 2, 0, 1, 16, 1, 24, 19, 25, 2, 26, 25, 2, 26, 1, 24, 27, 28, 29, 30], [3, 2, 1, 1, 0, 2, 24, 1, 3, 16, 26, 2, 16, 26, 2, 24, 1, 31, 32, 30, 29], [2, 1, 3, 16, 2, 0, 2, 1, 16, 1, 26, 24, 1, 26, 24, 28, 32, 33, 24, 34, 35], [2, 13, 16, 1, 24, 2, 0, 1, 16, 26, 1, 24, 26, 1, 24, 29, 30, 33, 34, 24, 35], [4, 3, 2, 24, 1, 1, 1, 0, 2, 24, 24, 1, 24, 24, 1, 30, 29, 26, 35, 35, 24], [5, 2, 1, 19, 3, 16, 16, 2, 0, 2, 2, 1, 33, 33, 26, 25, 16, 1, 26, 26, 24], [5, 2, 13, 25, 16, 1, 26, 24, 2, 0, 2, 1, 24, 34, 35, 25, 16, 26, 1, 26, 24], [5, 14, 19, 2, 26, 26, 1, 24, 2, 2, 0, 1, 34, 24, 35, 2, 26, 26, 26, 1, 24], [6, 4, 3, 26, 2, 24, 24, 1, 1, 1, 1, 0, 35, 35, 24, 26, 2, 24, 24, 24, 1], [5, 2, 11, 25, 16, 1, 26, 24, 33, 24, 34, 35, 0, 2, 1, 25, 16, 16, 1, 26, 24], [5, 15, 20, 2, 26, 26, 1, 24, 33, 34, 24, 35, 2, 0, 1, 2, 26, 16, 26, 1, 24], [7, 8, 5, 26, 2, 24, 24, 1, 26, 35, 35, 24, 1, 1, 0, 26, 2, 2, 24, 24, 1], [2, 11, 16, 1, 24, 28, 29, 30, 25, 25, 2, 26, 25, 2, 26, 0, 1, 16, 16, 1, 24], [8, 5, 2, 24, 1, 32, 30, 29, 16, 16, 26, 2, 16, 26, 2, 1, 0, 2, 2, 24, 1], [9, 5, 2, 27, 31, 33, 33, 26, 1, 26, 26, 24, 16, 16, 2, 16, 2, 0, 2, 2, 1], [10, 16, 21, 28, 32, 24, 34, 35, 26, 1, 26, 24, 1, 26, 24, 16, 2, 2, 0, 2, 1], [11, 17, 22, 29, 30, 34, 24, 35, 26, 26, 1, 24, 26, 1, 24, 1, 24, 2, 2, 0, 1], [12, 18, 23, 30, 29, 35, 35, 24, 24, 24, 24, 1, 24, 24, 1, 24, 1, 1, 1, 1, 0]]

/-- The coefficients (constant term first) of the 36 polynomials `P t`. -/
def cfs : List (List ℤ) := [[360, 0, 0, 0, 0, 0, 0], [360, 360, 0, 0, 0, 0, 0], [360, 540, 180, 0, 0, 0, 0], [360, 840, 540, 60, 0, 0, 0], [360, 1110, 1065, 330, 15, 0, 0], [360, 660, 360, 60, 0, 0, 0], [360, 1362, 1665, 795, 135, 3, 0], [360, 1272, 1500, 705, 120, 3, 0], [360, 990, 885, 270, 15, 0, 0], [360, 750, 525, 150, 15, 0, 0], [360, 840, 690, 240, 30, 0, 0], [360, 960, 870, 300, 30, 0, 0], [360, 1746, 2809, 1965, 610, 69, 1], [360, 1080, 1050, 360, 30, 0, 0], [360, 1296, 1620, 855, 180, 9, 0], [360, 1206, 1455, 765, 165, 9, 0], [360, 780, 540, 120, 0, 0, 0], [360, 1608, 2656, 2055, 760, 117, 4], [360, 1464, 1950, 1050, 210, 6, 0], [360, 1050, 1035, 390, 45, 0, 0], [360, 930, 855, 330, 45, 0, 0], [360, 1392, 1890, 1110, 270, 18, 0], [360, 1446, 2025, 1230, 315, 24, 0], [360, 1200, 1230, 420, 30, 0, 0], [360, 720, 360, 0, 0, 0, 0], [360, 990, 1005, 450, 75, 0, 0], [360, 900, 720, 180, 0, 0, 0], [360, 1422, 1995, 1245, 345, 33, 0], [360, 1416, 2070, 1410, 450, 54, 0], [360, 960, 720, 120, 0, 0, 0], [360, 1320, 1680, 840, 120, 0, 0], [360, 1170, 1215, 450, 45, 0, 0], [360, 1200, 1350, 600, 90, 0, 0], [360, 1140, 1320, 660, 120, 0, 0], [360, 1260, 1620, 900, 180, 0, 0], [360, 1080, 1080, 360, 0, 0, 0]]

/-- The type of the pair `(p, q)`. -/
def typ (p q : Fin 21) : ℕ := (typs.getD p.val []).getD q.val 0

/-- Coefficient of `m ^ k` in `P t m`. -/
def cf (t k : ℕ) : ℤ := (cfs.getD t []).getD k 0

/-- `360` times the number of continuations by `m` rows of a pair of type `t`. -/
def P (t : ℕ) (m : ℤ) : ℤ :=
  cf t 0 + cf t 1 * m + cf t 2 * m ^ 2 + cf t 3 * m ^ 3 + cf t 4 * m ^ 4 + cf t 5 * m ^ 5 +
    cf t 6 * m ^ 6

/-- The sum, over the continuations `w` of the pair `(p, q)`, of the coefficient `k` of the type
of `(q, w)`. -/
def S (p q : Fin 21) (k : ℕ) : ℤ := ∑ w : Fin 21, if cb p q w then cf (typ q w) k else 0

theorem step6 : ∀ p q : Fin 21, S p q 6 = cf (typ p q) 6 := by
  decide +kernel

theorem step5 : ∀ p q : Fin 21, S p q 5 = 6 * cf (typ p q) 6 + cf (typ p q) 5 := by
  decide +kernel

theorem step4 : ∀ p q : Fin 21,
    S p q 4 = 15 * cf (typ p q) 6 + 5 * cf (typ p q) 5 + cf (typ p q) 4 := by
  decide +kernel

theorem step3 : ∀ p q : Fin 21,
    S p q 3 = 20 * cf (typ p q) 6 + 10 * cf (typ p q) 5 + 4 * cf (typ p q) 4 + cf (typ p q) 3 := by
  decide +kernel

theorem step2 : ∀ p q : Fin 21,
    S p q 2 = 15 * cf (typ p q) 6 + 10 * cf (typ p q) 5 + 6 * cf (typ p q) 4 +
      3 * cf (typ p q) 3 + cf (typ p q) 2 := by
  decide +kernel

theorem step1 : ∀ p q : Fin 21,
    S p q 1 = 6 * cf (typ p q) 6 + 5 * cf (typ p q) 5 + 4 * cf (typ p q) 4 +
      3 * cf (typ p q) 3 + 2 * cf (typ p q) 2 + cf (typ p q) 1 := by
  decide +kernel

theorem step0 : ∀ p q : Fin 21,
    S p q 0 = cf (typ p q) 6 + cf (typ p q) 5 + cf (typ p q) 4 + cf (typ p q) 3 +
      cf (typ p q) 2 + cf (typ p q) 1 + cf (typ p q) 0 := by
  decide +kernel

theorem base_facts : ∀ p q : Fin 21, cf (typ p q) 0 = 360 := by
  decide +kernel

theorem H_closed (m : ℕ) : ∀ p q : Fin 21, 360 * (H m p q : ℤ) = P (typ p q) m := by
  induction m with
  | zero =>
    intro p q
    simp only [H, P, base_facts p q]
    push_cast
    ring
  | succ m ih =>
    intro p q
    have hsum : 360 * (H (m + 1) p q : ℤ) =
        ∑ w : Fin 21, if cb p q w then P (typ q w) m else 0 := by
      rw [H]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs
      · exact ih q w
      · simp
    rw [hsum]
    have hP : ∀ w : Fin 21, (if cb p q w then P (typ q w) m else 0) =
        (if cb p q w then cf (typ q w) 0 else 0) +
        (if cb p q w then cf (typ q w) 1 else 0) * (m : ℤ) +
        (if cb p q w then cf (typ q w) 2 else 0) * (m : ℤ) ^ 2 +
        (if cb p q w then cf (typ q w) 3 else 0) * (m : ℤ) ^ 3 +
        (if cb p q w then cf (typ q w) 4 else 0) * (m : ℤ) ^ 4 +
        (if cb p q w then cf (typ q w) 5 else 0) * (m : ℤ) ^ 5 +
        (if cb p q w then cf (typ q w) 6 else 0) * (m : ℤ) ^ 6 := by
      intro w
      split_ifs <;> simp [P]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    have e : ∀ k : ℕ, (∑ w : Fin 21, if cb p q w then cf (typ q w) k else 0) = S p q k :=
      fun k => rfl
    rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, step0, step1, step2, step3, step4, step5, step6]
    unfold P
    push_cast
    ring

theorem sum_facts :
    (∑ p : Fin 21, ∑ q : Fin 21, cf (typ p q) 0) = 158760 ∧
    (∑ p : Fin 21, ∑ q : Fin 21, cf (typ p q) 1) = 325092 ∧
    (∑ p : Fin 21, ∑ q : Fin 21, cf (typ p q) 2) = 246850 ∧
    (∑ p : Fin 21, ∑ q : Fin 21, cf (typ p q) 3) = 85590 ∧
    (∑ p : Fin 21, ∑ q : Fin 21, cf (typ p q) 4) = 13420 ∧
    (∑ p : Fin 21, ∑ q : Fin 21, cf (typ p q) 5) = 798 ∧
    (∑ p : Fin 21, ∑ q : Fin 21, cf (typ p q) 6) = 10 := by
  decide +kernel

/-- `360 a(m + 2)` as a polynomial in `m`. -/
def Q (m : ℚ) : ℚ :=
  158760 + 325092 * m + 246850 * m ^ 2 + 85590 * m ^ 3 + 13420 * m ^ 4 + 798 * m ^ 5 +
    10 * m ^ 6

theorem closed_two (m : ℕ) : 360 * (a (m + 2) : ℚ) = Q m := by
  have h : 360 * (a (m + 2) : ℤ) =
      ∑ p : Fin 21, ∑ q : Fin 21, P (typ p q) m := by
    rw [a_eq_cnt, cnt_eq_H]
    push_cast
    simp only [Finset.mul_sum, H_closed m]
  have h2 : (∑ p : Fin 21, ∑ q : Fin 21, P (typ p q) m) =
      158760 + 325092 * (m : ℤ) + 246850 * (m : ℤ) ^ 2 + 85590 * (m : ℤ) ^ 3 +
        13420 * (m : ℤ) ^ 4 + 798 * (m : ℤ) ^ 5 + 10 * (m : ℤ) ^ 6 := by
    simp only [P, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := sum_facts
    rw [h0, h1, h2, h3, h4, h5, h6]
  rw [h2] at h
  have h3 : ((360 * (a (m + 2) : ℤ) : ℤ) : ℚ) = ((158760 + 325092 * (m : ℤ) +
      246850 * (m : ℤ) ^ 2 + 85590 * (m : ℤ) ^ 3 + 13420 * (m : ℤ) ^ 4 + 798 * (m : ℤ) ^ 5 +
      10 * (m : ℤ) ^ 6 : ℤ) : ℚ) := by
    rw [h]
  push_cast at h3
  rw [h3, Q]

theorem closedQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = Q ((n : ℚ) - 2) / 360 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_eq_cnt, cnt_one, Q]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have := closed_two m
    push_cast
    rw [show (m : ℚ) + 2 - 2 = m by ring]
    linarith

theorem recurrence (n : ℕ) (hn : 8 ≤ n) :
    (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
    closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega),
    closedQ (n - 6) (by omega), closedQ (n - 7) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega]
  unfold Q
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) =
      X * (21 + 294 * X - 339 * X ^ 2 - 62 * X ^ 3 + 139 * X ^ 4 - 36 * X ^ 5 + 3 * X ^ 6) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  have key : PowerSeries.mk F * ((1 - X) ^ 7 : PowerSeries ℚ) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 7 * (PowerSeries.mk F * X ^ 1) +
        C 21 * (PowerSeries.mk F * X ^ 2) - C 35 * (PowerSeries.mk F * X ^ 3) +
        C 35 * (PowerSeries.mk F * X ^ 4) - C 21 * (PowerSeries.mk F * X ^ 5) +
        C 7 * (PowerSeries.mk F * X ^ 6) - C 1 * (PowerSeries.mk F * X ^ 7) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℚ) *
      (21 + 294 * X - 339 * X ^ 2 - 62 * X ^ 3 + 139 * X ^ 4 - 36 * X ^ 5 + 3 * X ^ 6) =
      C 21 * X ^ 1 + C 294 * X ^ 2 - C 339 * X ^ 3 - C 62 * X ^ 4 + C 139 * X ^ 5 -
        C 36 * X ^ 6 + C 3 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 8
  · interval_cases k <;> norm_num [hF, closedQ, Q]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    simp only [show 0 ≤ j + 8 by omega, show 1 ≤ j + 8 by omega, show 2 ≤ j + 8 by omega,
      show 3 ≤ j + 8 by omega, show 4 ≤ j + 8 by omega, show 5 ≤ j + 8 by omega,
      show 6 ≤ j + 8 by omega, show 7 ≤ j + 8 by omega,
      show j + 8 - 0 = j + 8 by omega, show j + 8 - 1 = j + 7 by omega,
      show j + 8 - 2 = j + 6 by omega, show j + 8 - 3 = j + 5 by omega,
      show j + 8 - 4 = j + 4 by omega, show j + 8 - 5 = j + 3 by omega,
      show j + 8 - 6 = j + 2 by omega, show j + 8 - 7 = j + 1 by omega,
      show ¬ (j + 8 = 1) by omega, show ¬ (j + 8 = 2) by omega, show ¬ (j + 8 = 3) by omega,
      show ¬ (j + 8 = 4) by omega, show ¬ (j + 8 = 5) by omega, show ¬ (j + 8 = 6) by omega,
      show ¬ (j + 8 = 7) by omega,
      show ¬ (j + 8 < 1) by omega, show ¬ (j + 7 < 1) by omega, show ¬ (j + 6 < 1) by omega,
      show ¬ (j + 5 < 1) by omega, show ¬ (j + 4 < 1) by omega, show ¬ (j + 3 < 1) by omega,
      show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    rw [closedQ (j + 8) (by omega), closedQ (j + 7) (by omega), closedQ (j + 6) (by omega),
      closedQ (j + 5) (by omega), closedQ (j + 4) (by omega), closedQ (j + 3) (by omega),
      closedQ (j + 2) (by omega), closedQ (j + 1) (by omega)]
    push_cast
    unfold Q
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207389.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
