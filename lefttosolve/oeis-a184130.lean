import OMAStatements.S_oeis_a184130

/-!
Proof of Barker's closed form and g.f., and of Hardin's recurrence and degree-8 polynomial
remark, for A184130 (n X 2 0..2 arrays whose rows and columns are in lexicographically
nondecreasing order).

A row `r` is coded by `code r = 3 * r 0 + r 1` (from 0 to 8), and two rows compare
lexicographically exactly as their codes do. Split an array with `n + 1` rows into its first row
`r` and the remaining rows `B`:
* its rows are sorted iff every row of `B` has code at least `code r` and the rows of `B` are
  sorted;
* its columns are sorted iff `r 0 < r 1`, or `r 0 = r 1` and the columns of `B` are sorted (a
  column is compared by its top entry first, then by the rest).
Let `F n t` (resp. `G n t`) count the `n`-row arrays with sorted rows (resp. sorted rows and
columns) all of whose rows have code at least `t`. Rows with `r 0 < r 1` have codes 1, 2, 5 and
rows with `r 0 = r 1` have codes 0, 4, 8, so
  `F (n + 1) t = Sum_{t ≤ s ≤ 8} F n s`,
  `G (n + 1) t = Sum_{t ≤ s ≤ 8, s ∈ {1, 2, 5}} F n s + Sum_{t ≤ s ≤ 8, s ∈ {0, 4, 8}} G n s`.
By induction on `n`, `F n t = C(n + 8 - t, 8 - t)` for `1 ≤ t ≤ 8` (as explicit polynomials),
`G n 8 = 1`, `G n 4 = C(n + 3, 4) + n + 1`, and `G n 0` is Barker's polynomial. Since `a n = G n 0`,
this is Barker's closed form (for every `n`); the g.f. follows by comparing coefficients
(a polynomial of degree 8 has vanishing ninth difference), the recurrence by substituting the
closed form, and the polynomial of degree 8 is the closed form itself.
-/

namespace OMA.Helpers

open OMA.S_oeis_a184130 Finset

/-- A row of the array: two entries in {0, 1, 2}. -/
abbrev R := Fin 2 → Fin 3

/-- The row read as a number in base 3, left entry most significant. -/
def code (r : R) : ℕ := 3 * (r 0 : ℕ) + (r 1 : ℕ)

theorem lex_lt_iff {m : ℕ} (x y : Fin m → Fin 3) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

theorem lex_cons_lt {m : ℕ} (x y : Fin 3) (u v : Fin m → Fin 3) :
    toLex (Fin.cons x u : Fin (m + 1) → Fin 3) < toLex (Fin.cons y v : Fin (m + 1) → Fin 3) ↔
      x < y ∨ (x = y ∧ toLex u < toLex v) := by
  rw [lex_lt_iff, lex_lt_iff]
  constructor
  · rintro ⟨i, hi, hlt⟩
    cases i using Fin.cases with
    | zero => exact Or.inl (by simpa using hlt)
    | succ k =>
      refine Or.inr ⟨by simpa using hi 0 (Fin.succ_pos k), k, fun j hj => ?_, by simpa using hlt⟩
      simpa using hi j.succ (Fin.succ_lt_succ_iff.mpr hj)
  · rintro (h | ⟨rfl, k, hk, hlt⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by simpa using h⟩
    · refine ⟨k.succ, fun j hj => ?_, by simpa using hlt⟩
      cases j using Fin.cases with
      | zero => simp
      | succ j => simpa using hk j (Fin.succ_lt_succ_iff.mp hj)

theorem lex_le_iff {m : ℕ} (x y : Fin m → Fin 3) :
    toLex x ≤ toLex y ↔ toLex x < toLex y ∨ x = y := by
  rw [← toLex_inj]
  exact le_iff_lt_or_eq

theorem lex_cons_le {m : ℕ} (x y : Fin 3) (u v : Fin m → Fin 3) :
    toLex (Fin.cons x u : Fin (m + 1) → Fin 3) ≤ toLex (Fin.cons y v : Fin (m + 1) → Fin 3) ↔
      x < y ∨ (x = y ∧ toLex u ≤ toLex v) := by
  rw [lex_le_iff, lex_cons_lt, lex_le_iff, Fin.cons_inj]
  tauto

theorem code_inj {r s : R} (h : code r = code s) : r = s := by
  unfold code at h
  have h0 := (r 1).isLt
  have h1 := (s 1).isLt
  funext j
  fin_cases j
  · exact Fin.ext (by simp; omega)
  · exact Fin.ext (by simp; omega)

theorem row_lt_iff (r s : R) : toLex r < toLex s ↔ code r < code s := by
  rw [lex_lt_iff, Fin.exists_fin_two]
  simp only [Fin.forall_fin_two, Fin.lt_def, Fin.ext_iff]
  unfold code
  have h0 := (r 1).isLt
  have h1 := (s 1).isLt
  simp
  omega

theorem row_le_iff (r s : R) : toLex r ≤ toLex s ↔ code r ≤ code s := by
  rw [lex_le_iff, row_lt_iff, Nat.le_iff_lt_or_eq]
  constructor
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (code_inj h)

theorem mono_cons {β : Type*} [Preorder β] {n : ℕ} (x : β) (f : Fin n → β) :
    Monotone (Fin.cons x f : Fin (n + 1) → β) ↔ (∀ i, x ≤ f i) ∧ Monotone f := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · simpa using h (Fin.zero_le i.succ)
    · simpa using h (Fin.succ_le_succ_iff.mpr hij)
  · rintro ⟨h1, h2⟩ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j => simpa using h1 j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => simpa using h2 (Fin.succ_le_succ_iff.mp hij)

/-- The rows of `B` are in lexicographically nondecreasing order. -/
def RS {n : ℕ} (B : Fin n → R) : Prop := Monotone (fun i => toLex (B i))

/-- The two columns of `B` are in lexicographically nondecreasing order. -/
def CS {n : ℕ} (B : Fin n → R) : Prop := toLex (fun i => B i 0) ≤ toLex (fun i => B i 1)

theorem RS_cons {n : ℕ} (r : R) (B : Fin n → R) :
    RS (Fin.cons r B : Fin (n + 1) → R) ↔ (∀ i, code r ≤ code (B i)) ∧ RS B := by
  unfold RS
  have h : (fun i => toLex ((Fin.cons r B : Fin (n + 1) → R) i)) =
      (Fin.cons (toLex r) (fun i => toLex (B i)) : Fin (n + 1) → Lex R) := by
    funext i
    cases i using Fin.cases <;> simp
  rw [h, mono_cons]
  simp only [row_le_iff]

theorem CS_cons {n : ℕ} (r : R) (B : Fin n → R) :
    CS (Fin.cons r B : Fin (n + 1) → R) ↔ r 0 < r 1 ∨ (r 0 = r 1 ∧ CS B) := by
  unfold CS
  have h0 : (fun i => (Fin.cons r B : Fin (n + 1) → R) i 0) =
      (Fin.cons (r 0) (fun i => B i 0) : Fin (n + 1) → Fin 3) := by
    funext i
    cases i using Fin.cases <;> simp
  have h1 : (fun i => (Fin.cons r B : Fin (n + 1) → R) i 1) =
      (Fin.cons (r 1) (fun i => B i 1) : Fin (n + 1) → Fin 3) := by
    funext i
    cases i using Fin.cases <;> simp
  rw [h0, h1, lex_cons_le]

theorem cols_iff {n : ℕ} (A : Fin n → R) :
    Monotone (fun j => toLex (fun i => A i j)) ↔ CS A := by
  rw [Fin.monotone_iff_le_succ, Fin.forall_fin_one]
  rfl

/-- Arrays with sorted rows, all of code at least `t`. -/
noncomputable def F (n t : ℕ) : ℕ := by
  classical
  exact ∑ B : Fin n → R, if RS B ∧ ∀ i, t ≤ code (B i) then 1 else 0

/-- Arrays with sorted rows and sorted columns, all rows of code at least `t`. -/
noncomputable def G (n t : ℕ) : ℕ := by
  classical
  exact ∑ B : Fin n → R, if RS B ∧ CS B ∧ ∀ i, t ≤ code (B i) then 1 else 0

theorem RS_zero (B : Fin 0 → R) : RS B := fun i => Fin.elim0 i

theorem CS_zero (B : Fin 0 → R) : CS B := by
  unfold CS
  rw [show (fun i => B i 0) = (fun i => B i 1) from funext fun i => Fin.elim0 i]

theorem F_zero (t : ℕ) : F 0 t = 1 := by
  unfold F
  simp [RS_zero]

theorem G_zero (t : ℕ) : G 0 t = 1 := by
  unfold G
  simp [RS_zero, CS_zero]

theorem F_succ (n t : ℕ) : F (n + 1) t = ∑ r : R, if t ≤ code r then F n (code r) else 0 := by
  classical
  unfold F
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => R).symm _
    (fun x => if RS (Fin.cons x.1 x.2 : Fin (n + 1) → R) ∧
      ∀ i, t ≤ code ((Fin.cons x.1 x.2 : Fin (n + 1) → R) i) then 1 else 0) (fun B => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : t ≤ code r
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [RS_cons, Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨⟨h1, h2⟩, h, fun i => le_trans h (h1 i)⟩
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun B _ => ?_
    rw [if_neg]
    rw [Fin.forall_fin_succ]
    simp only [Fin.cons_zero]
    tauto

theorem G_succ (n t : ℕ) : G (n + 1) t = ∑ r : R, if t ≤ code r then
    (if r 0 < r 1 then F n (code r) else if r 0 = r 1 then G n (code r) else 0) else 0 := by
  classical
  unfold G
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => R).symm _
    (fun x => if RS (Fin.cons x.1 x.2 : Fin (n + 1) → R) ∧
      CS (Fin.cons x.1 x.2 : Fin (n + 1) → R) ∧
      ∀ i, t ≤ code ((Fin.cons x.1 x.2 : Fin (n + 1) → R) i) then 1 else 0) (fun B => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : t ≤ code r
  · rw [if_pos h]
    by_cases h01 : r 0 < r 1
    · rw [if_pos h01]
      unfold F
      refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
      rw [RS_cons, CS_cons, Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      constructor
      · rintro ⟨⟨h1, h2⟩, -, -, -⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨⟨h1, h2⟩, Or.inl h01, h, fun i => le_trans h (h1 i)⟩
    · rw [if_neg h01]
      by_cases he : r 0 = r 1
      · rw [if_pos he]
        refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
        rw [RS_cons, CS_cons, Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, -, -⟩
          exact ⟨h2, h3.resolve_left h01 |>.2, h1⟩
        · rintro ⟨h2, h3, h1⟩
          exact ⟨⟨h1, h2⟩, Or.inr ⟨he, h3⟩, h, fun i => le_trans h (h1 i)⟩
      · rw [if_neg he]
        refine Finset.sum_eq_zero fun B _ => ?_
        rw [if_neg]
        rw [CS_cons]
        tauto
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun B _ => ?_
    rw [if_neg]
    rw [Fin.forall_fin_succ]
    simp only [Fin.cons_zero]
    tauto

theorem image_code : (Finset.univ : Finset R).image code = range 9 := by decide

theorem sum_R {M : Type*} [AddCommMonoid M] (φ : ℕ → M) :
    ∑ r : R, φ (code r) = ∑ s ∈ range 9, φ s := by
  rw [← image_code, Finset.sum_image (fun r _ s _ h => code_inj h)]

/-- Rows `r` with `r 0 < r 1` have codes 1, 2, 5. -/
def good (s : ℕ) : Prop := s = 1 ∨ s = 2 ∨ s = 5

/-- Rows `r` with `r 0 = r 1` have codes 0, 4, 8. -/
def tie (s : ℕ) : Prop := s = 0 ∨ s = 4 ∨ s = 8

instance (s : ℕ) : Decidable (good s) := by unfold good; infer_instance
instance (s : ℕ) : Decidable (tie s) := by unfold tie; infer_instance

theorem kind : ∀ r : R, (r 0 < r 1 ↔ good (code r)) ∧ (r 0 = r 1 ↔ tie (code r)) := by
  decide

theorem F_succ' (n t : ℕ) : F (n + 1) t = ∑ s ∈ range 9, if t ≤ s then F n s else 0 := by
  rw [F_succ, sum_R (fun s => if t ≤ s then F n s else 0)]

theorem G_succ' (n t : ℕ) : G (n + 1) t = ∑ s ∈ range 9, if t ≤ s then
    (if good s then F n s else if tie s then G n s else 0) else 0 := by
  rw [G_succ, ← sum_R (fun s => if t ≤ s then
    (if good s then F n s else if tie s then G n s else 0) else 0)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have := kind r
  simp only [this.1, this.2]

theorem F_closed (n : ℕ) :
    (F n 8 : ℚ) = 1 ∧
    (F n 7 : ℚ) = n + 1 ∧
    (F n 6 : ℚ) = (n + 1) * (n + 2) / 2 ∧
    (F n 5 : ℚ) = (n + 1) * (n + 2) * (n + 3) / 6 ∧
    (F n 4 : ℚ) = (n + 1) * (n + 2) * (n + 3) * (n + 4) / 24 ∧
    (F n 3 : ℚ) = (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) / 120 ∧
    (F n 2 : ℚ) = (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) / 720 ∧
    (F n 1 : ℚ) = (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) / 5040 := by
  induction n with
  | zero => simp only [F_zero]; norm_num
  | succ n ih =>
    obtain ⟨h8, h7, h6, h5, h4, h3, h2, h1⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [F_succ']
      norm_num [Finset.sum_range_succ, h8, h7, h6, h5, h4, h3, h2, h1]
      try ring

theorem G8 (n : ℕ) : G n 8 = 1 := by
  induction n with
  | zero => exact G_zero 8
  | succ n ih =>
    rw [G_succ']
    simp [Finset.sum_range_succ, good, tie, ih]

theorem G4 (n : ℕ) : (G n 4 : ℚ) = n * (n + 1) * (n + 2) * (n + 3) / 24 + n + 1 := by
  induction n with
  | zero => simp [G_zero]
  | succ n ih =>
    rw [G_succ']
    simp [Finset.sum_range_succ, good, tie, G8]
    rw [ih, (F_closed n).2.2.2.1]
    ring

theorem G0 (n : ℕ) : (G n 0 : ℚ) = (40320 + 79344 * (n : ℚ) + 64140 * (n : ℚ) ^ 2
        + 37884 * (n : ℚ) ^ 3 + 16009 * (n : ℚ) ^ 4 + 3696 * (n : ℚ) ^ 5 + 490 * (n : ℚ) ^ 6
        + 36 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) / 40320 := by
  induction n with
  | zero => simp [G_zero]
  | succ n ih =>
    rw [G_succ']
    simp [Finset.sum_range_succ, good, tie, G8]
    obtain ⟨-, -, -, h5, -, -, h2, h1⟩ := F_closed n
    rw [ih, G4, h5, h2, h1]
    ring

theorem a_eq (n : ℕ) : a n = G n 0 := by
  classical
  unfold a G
  rw [Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
  unfold RowsColsSorted
  rw [cols_iff]
  simp [RS]

theorem closed (n : ℕ) : (a n : ℚ) = (40320 + 79344 * (n : ℚ) + 64140 * (n : ℚ) ^ 2
        + 37884 * (n : ℚ) ^ 3 + 16009 * (n : ℚ) ^ 4 + 3696 * (n : ℚ) ^ 5 + 490 * (n : ℚ) ^ 6
        + 36 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) / 40320 := by
  rw [a_eq, G0]

theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3)
        - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8)
        + a (n - 9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
    show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
    show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
    show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega,
    show m + 10 - 9 = m + 1 by omega]
  have h : ((a (m + 10) : ℤ) : ℚ) = ((9 * a (m + 9) - 36 * a (m + 8) + 84 * a (m + 7)
      - 126 * a (m + 6) + 126 * a (m + 5) - 84 * a (m + 4) + 36 * a (m + 3) - 9 * a (m + 2)
      + a (m + 1) : ℤ) : ℚ) := by
    push_cast
    simp only [closed]
    push_cast
    ring
  exact_mod_cast h

open Polynomial in
theorem poly : ∃ P : Polynomial ℚ, P.natDegree = 8 ∧
    ∀ n : ℕ, 1 ≤ n → P.eval (n : ℚ) = (a n : ℚ) := by
  refine ⟨C (1 / 40320 : ℚ) * (X ^ 8 + C 36 * X ^ 7 + C 490 * X ^ 6 + C 3696 * X ^ 5
    + C 16009 * X ^ 4 + C 37884 * X ^ 3 + C 64140 * X ^ 2 + C 79344 * X + C 40320), ?_, ?_⟩
  · compute_degree!
  · intro n _
    rw [closed]
    simp only [eval_mul, eval_add, eval_pow, eval_C, eval_X]
    ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
        X * (2 - X) * (3 - 11 * X + 28 * X ^ 2 - 42 * X ^ 3 + 39 * X ^ 4 - 22 * X ^ 5
          + 7 * X ^ 6 - X ^ 7) := by
  set P : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hP
  have key : PowerSeries.mk P * (1 - X) ^ 9 =
      C 1 * (PowerSeries.mk P * X ^ 0) - C 9 * (PowerSeries.mk P * X ^ 1) +
        C 36 * (PowerSeries.mk P * X ^ 2) - C 84 * (PowerSeries.mk P * X ^ 3) +
        C 126 * (PowerSeries.mk P * X ^ 4) - C 126 * (PowerSeries.mk P * X ^ 5) +
        C 84 * (PowerSeries.mk P * X ^ 6) - C 36 * (PowerSeries.mk P * X ^ 7) +
        C 9 * (PowerSeries.mk P * X ^ 8) - C 1 * (PowerSeries.mk P * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (2 - X) * (3 - 11 * X + 28 * X ^ 2 - 42 * X ^ 3 + 39 * X ^ 4
      - 22 * X ^ 5 + 7 * X ^ 6 - X ^ 7) =
      C 6 * X ^ 1 - C 25 * X ^ 2 + C 67 * X ^ 3 - C 112 * X ^ 4 + C 120 * X ^ 5
        - C 83 * X ^ 6 + C 36 * X ^ 7 - C 9 * X ^ 8 + C 1 * X ^ 9 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hP, closed]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    simp only [show 0 ≤ j + 10 by omega, show 1 ≤ j + 10 by omega, show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega, show 4 ≤ j + 10 by omega, show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega, show 7 ≤ j + 10 by omega, show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega,
      show j + 10 - 0 = j + 10 by omega, show j + 10 - 1 = j + 9 by omega,
      show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega,
      show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega,
      show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega,
      show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega,
      show ¬ (j + 10 = 1) by omega, show ¬ (j + 10 = 2) by omega, show ¬ (j + 10 = 3) by omega,
      show ¬ (j + 10 = 4) by omega, show ¬ (j + 10 = 5) by omega, show ¬ (j + 10 = 6) by omega,
      show ¬ (j + 10 = 7) by omega, show ¬ (j + 10 = 8) by omega, show ¬ (j + 10 = 9) by omega,
      show ¬ (j + 10 = 0) by omega, show ¬ (j + 9 = 0) by omega, show ¬ (j + 8 = 0) by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega, if_true, if_false, hP, closed]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a184130.main :=
  ⟨fun n _ => OMA.Helpers.closed n, OMA.Helpers.gen_fun, OMA.Helpers.recurrence,
    OMA.Helpers.poly⟩
