import OMAStatements.S_oeis_a207109
import Mathlib

/-!
Proof of the conjectured generating function and recurrence for A207109 (n X 6 binary arrays
avoiding 0 0 0 and 0 1 1 horizontally and 0 0 1 and 1 1 0 vertically).

A row is allowed iff every `0` among its first four entries is followed by two different entries
(`H`); there are 18 such rows. Three consecutive rows `x, y, z` are compatible iff in every
column where `x` and `y` agree, `z` agrees too (`V`). Removing the first row gives a transfer
recursion: `T m x y` counts the continuations of the rows `x, y` by `m` more rows, with
`T 0 x y = 1` and `T (m + 1) x y = Sum_{z allowed, V x y z} T m y z`.

Indexing the 18 allowed rows by `Fin 18` (`e`), `G m i k = T m (e i) (e k)`. For each pair,
`G m i k` is a polynomial in `m` of degree at most 6, given by its coefficients in the binomial
basis `choose m d` (`Pc`, read from a table of the coefficient vectors that occur). This is
proved by induction on `m`: `choose (m + 1) d = choose m d + choose m (d - 1)` turns the
induction step into finitely many identities between coefficients, checked by the kernel row by
row. Summing over the pairs gives the closed form
`360 a(n) = 7 n^6 + 231 n^5 + 3175 n^4 + 9345 n^3 - 1022 n^2 - 7416 n + 2160` for `n >= 2`, and
also for `n = 1` since `a 1 = 18`. The recurrence and the generating function follow by comparing
coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207109 Finset

/-- A row of the array. -/
abbrev Row := Fin 6 → Fin 2

/-- The horizontal condition on a row: a `0` (not among the last two entries) is followed by two
different entries (this is the same as avoiding `0 0 0` and `0 1 1`). -/
def H (z : Row) : Prop :=
  ∀ j : Fin 4, z ⟨j, by omega⟩ = 0 → z ⟨j + 1, by omega⟩ ≠ z ⟨j + 2, by omega⟩

instance decH (z : Row) : Decidable (H z) := by
  unfold H
  infer_instance

/-- The vertical condition on three consecutive rows: in each column, two equal entries are
followed by the same entry (this is the same as avoiding `0 0 1` and `1 1 0`). -/
def V (x y z : Row) : Prop := ∀ j : Fin 6, x j = y j → z j = y j

instance decV (x y z : Row) : Decidable (V x y z) := by
  unfold V
  infer_instance

/-- Every row satisfies `H`. -/
def AllH {m : ℕ} (A : Fin m → Row) : Prop := ∀ i, H (A i)

/-- Every three consecutive rows satisfy `V`. -/
def Chain {m : ℕ} (A : Fin m → Row) : Prop :=
  ∀ (i : ℕ) (h : i + 2 < m), V (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

noncomputable instance decAllH {m : ℕ} (A : Fin m → Row) : Decidable (AllH A) :=
  Classical.dec _

noncomputable instance decChain {m : ℕ} (A : Fin m → Row) : Decidable (Chain A) :=
  Classical.dec _

theorem tri_h (a b c : Fin 2) :
    ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 0, 0) ∧ ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 1, 1) ↔
      (a = 0 → b ≠ c) := by
  revert a b c
  decide

theorem tri_v (a b c : Fin 2) :
    ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 0, 1) ∧ ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (1, 1, 0) ↔
      (a = b → c = b) := by
  revert a b c
  decide

theorem get_eq {m : ℕ} (A : Fin m → Row) (i j : ℕ) (hi : i < m) (hj : j < 6) :
    OMA.S_oeis_a207109.get A i j = (A ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by
  unfold OMA.S_oeis_a207109.get
  rw [dif_pos ⟨hi, hj⟩]

theorem avoids_iff {m : ℕ} (A : Fin m → Row) : avoids A = true ↔ AllH A ∧ Chain A := by
  unfold avoids
  rw [decide_eq_true_iff]
  apply and_congr
  · constructor
    · intro h i j
      have := h i.val i.isLt j.val (by omega)
      rw [get_eq A i j i.isLt (by omega), get_eq A i (j + 1) i.isLt (by omega),
        get_eq A i (j + 2) i.isLt (by omega)] at this
      exact (tri_h _ _ _).1 this
    · intro h i hi j hj
      rw [get_eq A i j hi (by omega), get_eq A i (j + 1) hi (by omega),
        get_eq A i (j + 2) hi (by omega)]
      exact (tri_h _ _ _).2 (h ⟨i, hi⟩ ⟨j, by omega⟩)
  · constructor
    · intro h i hi j
      have := h i (by omega) j.val j.isLt
      rw [get_eq A i j (by omega) j.isLt, get_eq A (i + 1) j (by omega) j.isLt,
        get_eq A (i + 2) j hi j.isLt] at this
      exact (tri_v _ _ _).1 this
    · intro h i hi j hj
      rw [get_eq A i j (by omega) hj, get_eq A (i + 1) j (by omega) hj,
        get_eq A (i + 2) j (by omega) hj]
      exact (tri_v _ _ _).2 (h i (by omega) ⟨j, hj⟩)
theorem chain_cons {m : ℕ} (x : Row) (B : Fin (m + 2) → Row) :
    Chain (Fin.cons x B : Fin (m + 3) → Row) ↔
      V x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) ∧ Chain B := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

theorem allH_cons {m : ℕ} (x : Row) (B : Fin m → Row) :
    AllH (Fin.cons x B : Fin (m + 1) → Row) ↔ H x ∧ AllH B := by
  unfold AllH
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The number of ways to continue the rows `x, y` by `m` more rows satisfying `H`, so that
every three consecutive rows satisfy `V`. -/
noncomputable def T (m : ℕ) (x y : Row) : ℕ := by
  classical
  exact ∑ B : Fin m → Row,
    if AllH B ∧ Chain (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) then 1 else 0

theorem T_zero (x y : Row) : T 0 x y = 1 := by
  classical
  unfold T
  rw [Fintype.sum_unique, if_pos]
  exact ⟨fun i => i.elim0, fun i hi => by omega⟩

theorem T_succ (m : ℕ) (x y : Row) :
    T (m + 1) x y = ∑ z : Row, if H z ∧ V x y z then T m y z else 0 := by
  classical
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if AllH (Fin.cons p.1 p.2 : Fin (m + 1) → Row) ∧
      Chain (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : H z ∧ V x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chain_cons, allH_cons]
    exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h => ⟨⟨hv.1, h.1⟩, hv.2, h.2⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chain_cons, allH_cons]
    exact fun h => hv ⟨h.1.1, h.2.1⟩

/-- The count of the statement, as a natural number. -/
noncomputable def aN (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 6 → Fin 2)).filter (fun x => avoids x)).card

theorem a_eq_aN (n : ℕ) : a n = (aN n : ℤ) := rfl

theorem aN_sum (n : ℕ) : aN n = ∑ A : Fin n → Row, if AllH A ∧ Chain A then 1 else 0 := by
  classical
  unfold aN
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun A _ => if_congr (avoids_iff A) rfl rfl

theorem aN_eq (n : ℕ) :
    aN (n + 2) = ∑ x : Row, ∑ y : Row, if H x ∧ H y then T n x y else 0 := by
  classical
  rw [aN_sum, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if AllH (Fin.cons p.1 p.2 : Fin (n + 2) → Row) ∧
      Chain (Fin.cons p.1 p.2 : Fin (n + 2) → Row) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if AllH (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row) ∧
      Chain (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : H x ∧ H y
  · rw [if_pos hxy]
    unfold T
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [allH_cons, allH_cons]
    exact ⟨fun h => ⟨h.1.2.2, h.2⟩, fun h => ⟨⟨hxy.1, hxy.2, h.1⟩, h.2⟩⟩
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [allH_cons, allH_cons]
    exact fun h => hxy ⟨h.1.1, h.1.2.1⟩

theorem aN_one : aN 1 = ∑ x : Row, if H x then 1 else 0 := by
  classical
  rw [aN_sum, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if AllH (Fin.cons p.1 p.2 : Fin 1 → Row) ∧
      Chain (Fin.cons p.1 p.2 : Fin 1 → Row) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  rw [allH_cons]
  exact ⟨fun h => h.1.1, fun h => ⟨⟨h, fun i => i.elim0⟩, fun i hi => by omega⟩⟩

end OMA.Helpers
namespace OMA.Helpers

open OMA.S_oeis_a207109 Finset

/-- The row with code `c`: bit `5 - j` of `c` in column `j`. -/
def row (c : Fin 64) : Row := fun j => ⟨c.val / 2 ^ (5 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The code of a row. -/
def code (z : Row) : ℕ := ∑ j : Fin 6, (z j : ℕ) * 2 ^ (5 - j.val)

theorem code_row : ∀ c : Fin 64, code (row c) = c := by
  decide +kernel

theorem row_injective : Function.Injective row := fun a b h =>
  Fin.ext (by rw [← code_row a, ← code_row b, h])

theorem row_surjective : Function.Surjective row :=
  ((Fintype.bijective_iff_injective_and_card row).2 ⟨row_injective, by simp⟩).2
/-- The codes of the 18 rows satisfying `H`. -/
def vc : Fin 18 → Fin 64 := ![9, 10, 18, 20, 21, 36, 37, 41, 42, 50, 52, 53, 57, 58, 60, 61, 62, 63]
/-- The binomial-basis coefficient vectors that occur (30 of them). -/
def polys : Fin 30 → Fin 7 → ℕ := ![
  ![1, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 0],
  ![1, 2, 1, 0, 0, 0, 0],
  ![1, 3, 2, 0, 0, 0, 0],
  ![1, 3, 3, 1, 0, 0, 0],
  ![1, 4, 4, 1, 0, 0, 0],
  ![1, 4, 5, 2, 0, 0, 0],
  ![1, 4, 6, 4, 1, 0, 0],
  ![1, 5, 6, 2, 0, 0, 0],
  ![1, 5, 7, 3, 0, 0, 0],
  ![1, 6, 9, 5, 1, 0, 0],
  ![1, 6, 10, 6, 1, 0, 0],
  ![1, 6, 12, 10, 3, 0, 0],
  ![1, 7, 13, 9, 2, 0, 0],
  ![1, 7, 14, 11, 3, 0, 0],
  ![1, 7, 15, 13, 4, 0, 0],
  ![1, 7, 16, 15, 5, 0, 0],
  ![1, 8, 15, 10, 2, 0, 0],
  ![1, 8, 16, 12, 3, 0, 0],
  ![1, 9, 19, 16, 6, 1, 0],
  ![1, 9, 20, 18, 7, 1, 0],
  ![1, 9, 23, 25, 12, 2, 0],
  ![1, 10, 24, 24, 11, 2, 0],
  ![1, 10, 27, 31, 16, 3, 0],
  ![1, 11, 30, 33, 15, 2, 0],
  ![1, 11, 32, 39, 21, 4, 0],
  ![1, 12, 32, 34, 16, 3, 0],
  ![1, 12, 34, 39, 20, 4, 0],
  ![1, 17, 59, 84, 58, 20, 3],
  ![1, 17, 61, 92, 69, 26, 4]]
/-- Which coefficient vector belongs to the pair of rows `(e i, e k)`. -/
def pid : Fin 18 → Fin 18 → Fin 30 := ![
  ![0, 1, 2, 2, 1, 4, 2, 1, 3, 14, 22, 10, 2, 9, 7, 4, 21, 7],
  ![1, 0, 1, 2, 5, 2, 9, 3, 1, 5, 19, 28, 9, 2, 7, 21, 4, 7],
  ![2, 1, 0, 1, 2, 6, 16, 13, 5, 1, 3, 9, 4, 2, 11, 24, 4, 7],
  ![2, 2, 1, 0, 1, 2, 9, 23, 20, 3, 1, 3, 12, 11, 2, 9, 4, 15],
  ![1, 5, 2, 1, 0, 9, 2, 10, 29, 9, 3, 1, 4, 25, 9, 2, 15, 4],
  ![4, 2, 6, 2, 9, 0, 1, 2, 1, 2, 1, 3, 14, 10, 2, 9, 4, 15],
  ![2, 9, 16, 9, 2, 1, 0, 1, 3, 6, 3, 1, 5, 27, 9, 2, 15, 4],
  ![1, 3, 13, 23, 10, 2, 1, 0, 1, 6, 13, 5, 1, 3, 4, 2, 13, 4],
  ![3, 1, 5, 20, 29, 1, 3, 1, 0, 2, 10, 26, 3, 1, 4, 13, 2, 4],
  ![14, 5, 1, 3, 9, 2, 6, 6, 2, 0, 1, 2, 2, 1, 5, 17, 2, 4],
  ![22, 19, 3, 1, 3, 1, 3, 13, 10, 1, 0, 1, 6, 5, 1, 3, 2, 9],
  ![10, 28, 9, 3, 1, 3, 1, 5, 26, 2, 1, 0, 2, 18, 3, 1, 9, 2],
  ![2, 9, 4, 12, 4, 14, 5, 1, 3, 2, 6, 2, 0, 1, 2, 1, 8, 2],
  ![9, 2, 2, 11, 25, 10, 27, 3, 1, 1, 5, 18, 1, 0, 2, 8, 1, 2],
  ![7, 7, 11, 2, 9, 2, 9, 4, 4, 5, 1, 3, 2, 2, 0, 1, 1, 3],
  ![4, 21, 24, 9, 2, 9, 2, 2, 13, 17, 3, 1, 1, 8, 1, 0, 3, 1],
  ![21, 4, 4, 4, 15, 4, 15, 13, 2, 2, 2, 9, 8, 1, 1, 3, 0, 1],
  ![7, 7, 7, 15, 4, 15, 4, 4, 4, 4, 9, 2, 2, 2, 3, 1, 1, 0]]

/-- The rows satisfying `H`. -/
def e (i : Fin 18) : Row := row (vc i)

theorem vc_injective : Function.Injective vc := by
  decide +kernel

theorem H_row : ∀ c : Fin 64, H (row c) ↔ ∃ i : Fin 18, vc i = c := by
  decide +kernel

theorem H_iff (z : Row) : H z ↔ ∃ i, e i = z := by
  obtain ⟨c, rfl⟩ := row_surjective z
  rw [H_row]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, by rw [e, hi]⟩, fun ⟨i, hi⟩ => ⟨i, row_injective hi⟩⟩

theorem e_injective : Function.Injective e := row_injective.comp vc_injective

theorem sum_H (f : Row → ℕ) : (∑ z : Row, if H z then f z else 0) = ∑ i : Fin 18, f (e i) := by
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter fun z => H z) = Finset.univ.image e := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact H_iff z
  rw [hs, Finset.sum_image (fun i _ k _ h => e_injective h)]

/-- The transfer recursion on indices of rows satisfying `H`. -/
def G : ℕ → Fin 18 → Fin 18 → ℕ
  | 0, _, _ => 1
  | m + 1, i, k => ∑ l : Fin 18, if V (e i) (e k) (e l) then G m k l else 0

theorem T_eq_G (m : ℕ) : ∀ i k : Fin 18, T m (e i) (e k) = G m i k := by
  induction m with
  | zero => intro i k; rw [T_zero]; rfl
  | succ m ih =>
    intro i k
    rw [T_succ]
    simp only [ite_and]
    rw [sum_H (fun z => if V (e i) (e k) z then T m (e k) z else 0)]
    simp only [G]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ih k l]

/-- The binomial-basis coefficients of `G · i k`. -/
def Pc (i k : Fin 18) : Fin 7 → ℕ := polys (pid i k)

/-- Evaluation in the binomial basis. -/
def ev (c : Fin 7 → ℕ) (m : ℕ) : ℕ := ∑ d : Fin 7, c d * m.choose d

/-- The next coefficient. -/
def nx (c : Fin 7 → ℕ) (d : Fin 7) : ℕ := if h : d.val + 1 < 7 then c ⟨d.val + 1, h⟩ else 0

theorem ev_succ (c : Fin 7 → ℕ) (m : ℕ) :
    ev c (m + 1) = ∑ d : Fin 7, (c d + nx c d) * m.choose d := by
  simp only [ev, nx, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [Nat.choose_succ_succ]
  ring

theorem base_check : ∀ i k : Fin 18, Pc i k 0 = 1 := by
  decide +kernel

/-- The induction step for the pairs `(e i, e k)` with `i` fixed, coefficient by coefficient. -/
def SC (i : Fin 18) : Prop :=
  ∀ k : Fin 18, ∀ d : Fin 7,
    (∑ l : Fin 18, if V (e i) (e k) (e l) then Pc k l d else 0) = Pc i k d + nx (Pc i k) d

instance decSC (i : Fin 18) : Decidable (SC i) := by
  unfold SC
  infer_instance

theorem sc0 : SC 0 := by
  decide +kernel

theorem sc1 : SC 1 := by
  decide +kernel

theorem sc2 : SC 2 := by
  decide +kernel

theorem sc3 : SC 3 := by
  decide +kernel

theorem sc4 : SC 4 := by
  decide +kernel

theorem sc5 : SC 5 := by
  decide +kernel

theorem sc6 : SC 6 := by
  decide +kernel

theorem sc7 : SC 7 := by
  decide +kernel

theorem sc8 : SC 8 := by
  decide +kernel

theorem sc9 : SC 9 := by
  decide +kernel

theorem sc10 : SC 10 := by
  decide +kernel

theorem sc11 : SC 11 := by
  decide +kernel

theorem sc12 : SC 12 := by
  decide +kernel

theorem sc13 : SC 13 := by
  decide +kernel

theorem sc14 : SC 14 := by
  decide +kernel

theorem sc15 : SC 15 := by
  decide +kernel

theorem sc16 : SC 16 := by
  decide +kernel

theorem sc17 : SC 17 := by
  decide +kernel

theorem step_check (i : Fin 18) : SC i := by
  fin_cases i
  exacts [sc0, sc1, sc2, sc3, sc4, sc5, sc6, sc7, sc8, sc9, sc10, sc11, sc12, sc13, sc14, sc15, sc16, sc17]

end OMA.Helpers
namespace OMA.Helpers

open OMA.S_oeis_a207109 Finset

theorem G_eq (m : ℕ) : ∀ i k : Fin 18, G m i k = ev (Pc i k) m := by
  induction m with
  | zero =>
    intro i k
    simp [G, ev, Fin.sum_univ_succ, base_check]
  | succ m ih =>
    intro i k
    rw [ev_succ]
    have h1 : ∀ d : Fin 7, Pc i k d + nx (Pc i k) d =
        ∑ l : Fin 18, if V (e i) (e k) (e l) then Pc k l d else 0 :=
      fun d => (step_check i k d).symm
    simp only [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [G, ih]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rfl
    · simp

/-- The coefficients of `a (n + 2)` in the binomial basis. -/
def Sv : Fin 7 → ℕ := ![324, 1180, 1850, 1484, 634, 140, 14]

theorem sum_check : ∀ d : Fin 7, (∑ i : Fin 18, ∑ k : Fin 18, Pc i k d) = Sv d := by
  decide +kernel

theorem aN_two (n : ℕ) : aN (n + 2) = ∑ d : Fin 7, Sv d * n.choose d := by
  rw [aN_eq]
  have h1 : ∀ x : Row, (∑ y : Row, if H x ∧ H y then T n x y else 0) =
      if H x then ∑ y : Row, (if H y then T n x y else 0) else 0 := by
    intro x
    by_cases hx : H x
    · simp only [hx, true_and, if_true]
    · simp only [hx, false_and, if_false, Finset.sum_const_zero]
  simp only [h1]
  rw [sum_H]
  simp only [sum_H, T_eq_G, G_eq, ev]
  simp only [← sum_check, Finset.sum_mul]
  calc (∑ i : Fin 18, ∑ k : Fin 18, ∑ d : Fin 7, Pc i k d * n.choose d)
      = ∑ i : Fin 18, ∑ d : Fin 7, ∑ k : Fin 18, Pc i k d * n.choose d :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ d : Fin 7, ∑ i : Fin 18, ∑ k : Fin 18, Pc i k d * n.choose d := Finset.sum_comm

theorem aN_one' : aN 1 = 18 := by
  rw [aN_one, sum_H (fun _ => 1)]
  simp

theorem chq (m d : ℕ) :
    (m.choose d : ℚ) = (descPochhammer ℚ d).eval (m : ℚ) / (d.factorial : ℚ) :=
  Nat.cast_choose_eq_descPochhammer_div ℚ m d

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    360 * (aN n : ℚ) = 7 * (n : ℚ) ^ 6 + 231 * n ^ 5 + 3175 * n ^ 4 + 9345 * n ^ 3 - 1022 * n ^ 2 - 7416 * n + 2160 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [aN_one']
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [aN_two]
    push_cast
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, chq]
    simp [Sv, descPochhammer_succ_eval, Nat.factorial]
    ring

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (7 * (n : ℚ) ^ 6 + 231 * n ^ 5 + 3175 * n ^ 4 + 9345 * n ^ 3 - 1022 * n ^ 2 - 7416 * n + 2160) / 360 := by
  rw [a_eq_aN, ← closed n hn]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 8 ≤ n) :
    (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega), closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega), closedQ (n - 6) (by omega), closedQ (n - 7) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega]
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) =
      2 * X * (9 + 99 * X - 193 * X ^ 2 + 90 * X ^ 3 + 17 * X ^ 4 - 18 * X ^ 5 + 3 * X ^ 6) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 7 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 7 * (PowerSeries.mk F * X ^ 1) + C 21 * (PowerSeries.mk F * X ^ 2) - C 35 * (PowerSeries.mk F * X ^ 3) + C 35 * (PowerSeries.mk F * X ^ 4) - C 21 * (PowerSeries.mk F * X ^ 5) + C 7 * (PowerSeries.mk F * X ^ 6) - C 1 * (PowerSeries.mk F * X ^ 7) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (9 + 99 * X - 193 * X ^ 2 + 90 * X ^ 3 + 17 * X ^ 4 - 18 * X ^ 5 + 3 * X ^ 6) : ℚ⟦X⟧) =
      C 18 * X ^ 1 + C 198 * X ^ 2 - C 386 * X ^ 3 + C 180 * X ^ 4 + C 34 * X ^ 5 - C 36 * X ^ 6 + C 6 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 8
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    have r := recurrence (j + 8) (by omega)
    simp only [show j + 8 - 1 = j + 7 by omega, show j + 8 - 2 = j + 6 by omega, show j + 8 - 3 = j + 5 by omega, show j + 8 - 4 = j + 4 by omega, show j + 8 - 5 = j + 3 by omega, show j + 8 - 6 = j + 2 by omega, show j + 8 - 7 = j + 1 by omega] at r
    simp only [show 0 ≤ j + 8 by omega, show 1 ≤ j + 8 by omega, show 2 ≤ j + 8 by omega, show 3 ≤ j + 8 by omega, show 4 ≤ j + 8 by omega, show 5 ≤ j + 8 by omega, show 6 ≤ j + 8 by omega, show 7 ≤ j + 8 by omega,
      show j + 8 - 0 = j + 8 by omega, show j + 8 - 1 = j + 7 by omega, show j + 8 - 2 = j + 6 by omega, show j + 8 - 3 = j + 5 by omega, show j + 8 - 4 = j + 4 by omega, show j + 8 - 5 = j + 3 by omega, show j + 8 - 6 = j + 2 by omega, show j + 8 - 7 = j + 1 by omega,
      show ¬ (j + 8 = 1) by omega, show ¬ (j + 8 = 2) by omega, show ¬ (j + 8 = 3) by omega, show ¬ (j + 8 = 4) by omega, show ¬ (j + 8 = 5) by omega, show ¬ (j + 8 = 6) by omega, show ¬ (j + 8 = 7) by omega,
      show ¬ (j + 8 < 1) by omega, show ¬ (j + 7 < 1) by omega, show ¬ (j + 6 < 1) by omega, show ¬ (j + 5 < 1) by omega, show ¬ (j + 4 < 1) by omega, show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207109.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
