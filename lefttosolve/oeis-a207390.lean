import OMAStatements.S_oeis_a207390
import Mathlib

/-!
Proof of the conjectured generating function and recurrence for A207390 (n X 7 binary arrays
avoiding 0 0 1 and 0 1 0 horizontally and 0 0 1 and 1 1 0 vertically).

A row is allowed iff every `0` among its first five entries is followed by two equal entries
(`H`); there are 31 such rows. Three consecutive rows `x, y, z` are compatible iff in every
column where `x` and `y` agree, `z` agrees too (`V`). Removing the first row gives a transfer
recursion: `T m x y` counts the continuations of the rows `x, y` by `m` more rows, with
`T 0 x y = 1` and `T (m + 1) x y = Sum_{z allowed, V x y z} T m y z`.

Indexing the 31 allowed rows by `Fin 31` (`e`), `G m i k = T m (e i) (e k)`. For each of the
961 pairs, `G m i k` is a polynomial in `m` of degree at most 7, given by its coefficients in the
binomial basis `choose m d` (`Pc`, read from a table of the 66 coefficient vectors that occur).
This is proved by induction on `m`: `choose (m + 1) d = choose m d + choose m (d - 1)` turns the
induction step into finitely many identities between coefficients, checked by the kernel in 31
chunks (`sc0`, ..., `sc30`). Summing over the pairs gives the closed form
`5040 a(n) = 24 n^7 + 2884 n^6 + 49644 n^5 + 201460 n^4 + 73836 n^3 - 194264 n^2 + 7536 n + 15120`
for `n ≥ 2`, and also for `n = 1` since `a 1 = 31`. The recurrence and the generating function
follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207390 Finset

/-- A row of the array. -/
abbrev Row := Fin 7 → Fin 2

/-- The horizontal condition on a row: a `0` is followed by two equal entries (this is the
same as avoiding `0 0 1` and `0 1 0`). -/
def H (z : Row) : Prop :=
  ∀ j : Fin 5, z ⟨j, by omega⟩ = 0 → z ⟨j + 1, by omega⟩ = z ⟨j + 2, by omega⟩

instance decH (z : Row) : Decidable (H z) := by
  unfold H
  infer_instance

/-- The vertical condition on three consecutive rows: in each column, two equal entries are
followed by the same entry (this is the same as avoiding `0 0 1` and `1 1 0`). -/
def V (x y z : Row) : Prop := ∀ j : Fin 7, x j = y j → z j = y j

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
    ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 0, 1) ∧ ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 1, 0) ↔
      (a = 0 → b = c) := by
  revert a b c
  decide

theorem tri_v (a b c : Fin 2) :
    ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 0, 1) ∧ ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (1, 1, 0) ↔
      (a = b → c = b) := by
  revert a b c
  decide

theorem get_eq {m : ℕ} (A : Fin m → Row) (i j : ℕ) (hi : i < m) (hj : j < 7) :
    OMA.S_oeis_a207390.get A i j = (A ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by
  unfold OMA.S_oeis_a207390.get
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
  ((Finset.univ : Finset (Fin n → Fin 7 → Fin 2)).filter (fun x => avoids x)).card

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

open OMA.S_oeis_a207390 Finset

/-- The row with code `c`: bit `6 - j` of `c` in column `j`. -/
def row (c : Fin 128) : Row := fun j => ⟨c.val / 2 ^ (6 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The code of a row. -/
def code (z : Row) : ℕ := ∑ j : Fin 7, (z j : ℕ) * 2 ^ (6 - j.val)

theorem code_row : ∀ c : Fin 128, code (row c) = c := by
  decide +kernel

theorem row_injective : Function.Injective row := fun a b h =>
  Fin.ext (by rw [← code_row a, ← code_row b, h])

theorem row_surjective : Function.Surjective row :=
  ((Fintype.bijective_iff_injective_and_card row).2 ⟨row_injective, by simp⟩).2

/-- The codes of the 31 rows satisfying `H`. -/
def vc : Fin 31 → Fin 128 := ![0, 48, 54, 55, 56, 59, 60, 61, 62, 63, 64, 88, 91, 92, 93, 94, 95, 96, 108, 109, 110, 111, 112, 118, 119, 120, 123, 124, 125, 126, 127]

/-- The binomial-basis coefficient vectors that occur (66 of them). -/
def polys : Fin 66 → Fin 8 → ℕ := ![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0],
  ![1, 2, 1, 0, 0, 0, 0, 0],
  ![1, 3, 2, 0, 0, 0, 0, 0],
  ![1, 3, 3, 1, 0, 0, 0, 0],
  ![1, 4, 4, 1, 0, 0, 0, 0],
  ![1, 4, 5, 2, 0, 0, 0, 0],
  ![1, 4, 6, 4, 1, 0, 0, 0],
  ![1, 5, 6, 2, 0, 0, 0, 0],
  ![1, 5, 7, 3, 0, 0, 0, 0],
  ![1, 5, 8, 5, 1, 0, 0, 0],
  ![1, 5, 9, 7, 2, 0, 0, 0],
  ![1, 6, 10, 6, 1, 0, 0, 0],
  ![1, 6, 11, 8, 2, 0, 0, 0],
  ![1, 6, 12, 10, 3, 0, 0, 0],
  ![1, 6, 14, 16, 9, 2, 0, 0],
  ![1, 7, 12, 6, 0, 0, 0, 0],
  ![1, 7, 12, 7, 1, 0, 0, 0],
  ![1, 7, 13, 9, 2, 0, 0, 0],
  ![1, 7, 14, 11, 3, 0, 0, 0],
  ![1, 7, 15, 13, 4, 0, 0, 0],
  ![1, 7, 16, 15, 5, 0, 0, 0],
  ![1, 7, 17, 19, 10, 2, 0, 0],
  ![1, 8, 15, 10, 2, 0, 0, 0],
  ![1, 8, 16, 12, 3, 0, 0, 0],
  ![1, 8, 19, 18, 6, 0, 0, 0],
  ![1, 8, 19, 19, 8, 1, 0, 0],
  ![1, 8, 21, 25, 14, 3, 0, 0],
  ![1, 9, 20, 16, 4, 0, 0, 0],
  ![1, 9, 21, 19, 6, 0, 0, 0],
  ![1, 9, 23, 23, 8, 0, 0, 0],
  ![1, 9, 23, 25, 12, 2, 0, 0],
  ![1, 10, 25, 25, 10, 1, 0, 0],
  ![1, 10, 28, 33, 17, 3, 0, 0],
  ![1, 10, 29, 36, 20, 4, 0, 0],
  ![1, 10, 31, 43, 28, 7, 0, 0],
  ![1, 10, 33, 49, 34, 9, 0, 0],
  ![1, 11, 28, 26, 8, 0, 0, 0],
  ![1, 11, 28, 28, 11, 1, 0, 0],
  ![1, 11, 31, 33, 12, 0, 0, 0],
  ![1, 11, 31, 36, 18, 3, 0, 0],
  ![1, 12, 36, 44, 23, 4, 0, 0],
  ![1, 12, 38, 51, 31, 7, 0, 0],
  ![1, 12, 40, 57, 37, 9, 0, 0],
  ![1, 12, 45, 74, 56, 16, 0, 0],
  ![1, 13, 37, 41, 18, 2, 0, 0],
  ![1, 13, 41, 53, 30, 6, 0, 0],
  ![1, 14, 46, 62, 37, 8, 0, 0],
  ![1, 14, 48, 69, 45, 11, 0, 0],
  ![1, 15, 51, 74, 51, 15, 1, 0],
  ![1, 15, 57, 91, 66, 18, 0, 0],
  ![1, 15, 58, 98, 81, 31, 4, 0],
  ![1, 15, 62, 108, 85, 25, 0, 0],
  ![1, 17, 60, 87, 58, 16, 1, 0],
  ![1, 17, 61, 85, 50, 10, 0, 0],
  ![1, 17, 64, 96, 63, 15, 0, 0],
  ![1, 17, 67, 107, 76, 20, 0, 0],
  ![1, 17, 68, 115, 93, 34, 4, 0],
  ![1, 20, 78, 124, 91, 28, 2, 0],
  ![1, 20, 89, 165, 146, 59, 8, 0],
  ![1, 22, 101, 192, 174, 72, 10, 0],
  ![1, 22, 109, 230, 240, 122, 24, 0],
  ![1, 23, 118, 256, 273, 141, 28, 0],
  ![1, 23, 123, 282, 322, 181, 40, 0],
  ![1, 30, 153, 323, 338, 177, 40, 2],
  ![1, 30, 177, 436, 540, 346, 104, 10]]

/-- Which coefficient vector belongs to the pair of rows `(e i, e k)`. -/
def pid : Fin 31 → Fin 31 → Fin 66 := ![
  ![0, 1, 2, 4, 2, 4, 4, 7, 10, 31, 1, 2, 4, 4, 7, 7, 22, 2, 4, 7, 7, 15, 5, 12, 26, 17, 32, 38, 49, 53, 64],
  ![1, 0, 1, 2, 1, 2, 2, 4, 5, 23, 5, 6, 21, 21, 36, 43, 62, 2, 19, 35, 42, 61, 1, 3, 9, 3, 9, 9, 20, 28, 54],
  ![2, 1, 0, 1, 5, 6, 2, 9, 1, 3, 13, 43, 44, 21, 52, 6, 30, 6, 21, 52, 6, 30, 3, 1, 3, 28, 30, 9, 39, 3, 16],
  ![4, 2, 1, 0, 24, 2, 9, 2, 3, 1, 27, 63, 21, 52, 21, 30, 6, 14, 52, 21, 30, 6, 9, 3, 1, 55, 9, 39, 9, 16, 3],
  ![2, 1, 5, 24, 0, 1, 1, 2, 2, 8, 18, 2, 9, 9, 25, 25, 56, 6, 6, 21, 21, 50, 3, 28, 55, 1, 3, 3, 9, 9, 37],
  ![4, 2, 6, 2, 1, 0, 8, 2, 2, 1, 33, 9, 2, 56, 25, 25, 9, 14, 50, 21, 21, 6, 9, 30, 9, 3, 1, 37, 9, 9, 3],
  ![4, 2, 2, 9, 1, 8, 0, 1, 1, 3, 40, 9, 56, 2, 9, 9, 39, 19, 2, 9, 9, 39, 9, 9, 39, 3, 37, 1, 3, 3, 16],
  ![7, 4, 9, 2, 2, 2, 1, 0, 3, 1, 51, 25, 25, 9, 2, 39, 9, 34, 9, 2, 39, 9, 20, 39, 9, 9, 9, 3, 1, 16, 3],
  ![10, 5, 1, 3, 2, 2, 1, 3, 0, 1, 57, 25, 25, 9, 39, 2, 9, 41, 9, 39, 2, 9, 28, 3, 16, 9, 9, 3, 16, 1, 3],
  ![31, 23, 3, 1, 8, 1, 3, 1, 1, 0, 65, 56, 9, 39, 9, 9, 2, 60, 39, 9, 9, 2, 54, 16, 3, 37, 3, 16, 3, 3, 1],
  ![1, 5, 13, 27, 18, 33, 40, 51, 57, 65, 0, 1, 2, 2, 4, 4, 13, 1, 2, 4, 4, 11, 2, 4, 7, 5, 12, 17, 32, 38, 58],
  ![2, 6, 43, 63, 2, 9, 9, 25, 25, 56, 1, 0, 1, 1, 2, 2, 8, 5, 6, 21, 21, 50, 2, 19, 48, 1, 3, 3, 9, 9, 37],
  ![4, 21, 44, 21, 9, 2, 56, 25, 25, 9, 2, 1, 0, 8, 2, 2, 1, 13, 50, 21, 21, 6, 6, 21, 6, 3, 1, 37, 9, 9, 3],
  ![4, 21, 21, 52, 9, 56, 2, 9, 9, 39, 2, 1, 8, 0, 1, 1, 3, 18, 2, 9, 9, 39, 6, 6, 30, 3, 37, 1, 3, 3, 16],
  ![7, 36, 52, 21, 25, 25, 9, 2, 39, 9, 4, 2, 2, 1, 0, 3, 1, 33, 9, 2, 39, 9, 14, 30, 6, 9, 9, 3, 1, 16, 3],
  ![7, 43, 6, 30, 25, 25, 9, 39, 2, 9, 4, 2, 2, 1, 3, 0, 1, 40, 9, 39, 2, 9, 19, 2, 9, 9, 9, 3, 16, 1, 3],
  ![22, 62, 30, 6, 56, 9, 39, 9, 9, 2, 13, 8, 1, 3, 1, 1, 0, 59, 39, 9, 9, 2, 47, 9, 2, 37, 3, 16, 3, 3, 1],
  ![2, 2, 6, 14, 6, 14, 19, 34, 41, 60, 1, 5, 13, 18, 33, 40, 59, 0, 1, 2, 2, 6, 1, 2, 4, 2, 4, 5, 12, 17, 45],
  ![4, 19, 21, 52, 6, 50, 2, 9, 9, 39, 2, 6, 50, 2, 9, 9, 39, 1, 0, 1, 1, 3, 5, 6, 30, 2, 29, 1, 3, 3, 16],
  ![7, 35, 52, 21, 21, 21, 9, 2, 39, 9, 4, 21, 21, 9, 2, 39, 9, 2, 1, 0, 3, 1, 13, 30, 6, 6, 6, 3, 1, 16, 3],
  ![7, 42, 6, 30, 21, 21, 9, 39, 2, 9, 4, 21, 21, 9, 39, 2, 9, 2, 1, 3, 0, 1, 18, 2, 9, 6, 6, 3, 16, 1, 3],
  ![15, 61, 30, 6, 50, 6, 39, 9, 9, 2, 11, 50, 6, 39, 9, 9, 2, 6, 3, 1, 1, 0, 46, 9, 2, 29, 2, 16, 3, 3, 1],
  ![5, 1, 3, 9, 3, 9, 9, 20, 28, 54, 2, 2, 6, 6, 14, 19, 47, 1, 5, 13, 18, 46, 0, 1, 2, 1, 2, 2, 4, 5, 23],
  ![12, 3, 1, 3, 28, 30, 9, 39, 3, 16, 4, 19, 21, 6, 30, 2, 9, 2, 6, 30, 2, 9, 1, 0, 1, 5, 6, 2, 9, 1, 3],
  ![26, 9, 3, 1, 55, 9, 39, 9, 16, 3, 7, 48, 6, 30, 6, 9, 2, 4, 30, 6, 9, 2, 2, 1, 0, 24, 2, 9, 2, 3, 1],
  ![17, 3, 28, 55, 1, 3, 3, 9, 9, 37, 5, 1, 3, 3, 9, 9, 37, 2, 2, 6, 6, 29, 1, 5, 24, 0, 1, 1, 2, 2, 8],
  ![32, 9, 30, 9, 3, 1, 37, 9, 9, 3, 12, 3, 1, 37, 9, 9, 3, 4, 29, 6, 6, 2, 2, 6, 2, 1, 0, 8, 2, 2, 1],
  ![38, 9, 9, 39, 3, 37, 1, 3, 3, 16, 17, 3, 37, 1, 3, 3, 16, 5, 1, 3, 3, 16, 2, 2, 9, 1, 8, 0, 1, 1, 3],
  ![49, 20, 39, 9, 9, 9, 3, 1, 16, 3, 32, 9, 9, 3, 1, 16, 3, 12, 3, 1, 16, 3, 4, 9, 2, 2, 2, 1, 0, 3, 1],
  ![53, 28, 3, 16, 9, 9, 3, 16, 1, 3, 38, 9, 9, 3, 16, 1, 3, 17, 3, 16, 1, 3, 5, 1, 3, 2, 2, 1, 3, 0, 1],
  ![64, 54, 16, 3, 37, 3, 16, 3, 3, 1, 58, 37, 3, 16, 3, 3, 1, 45, 16, 3, 3, 1, 23, 3, 1, 8, 1, 3, 1, 1, 0]]

/-- The rows satisfying `H`. -/
def e (i : Fin 31) : Row := row (vc i)

theorem vc_injective : Function.Injective vc := by
  decide +kernel

theorem H_row : ∀ c : Fin 128, H (row c) ↔ ∃ i : Fin 31, vc i = c := by
  decide +kernel

theorem H_iff (z : Row) : H z ↔ ∃ i, e i = z := by
  obtain ⟨c, rfl⟩ := row_surjective z
  rw [H_row]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, by rw [e, hi]⟩, fun ⟨i, hi⟩ => ⟨i, row_injective hi⟩⟩

theorem e_injective : Function.Injective e := row_injective.comp vc_injective

theorem sum_H (f : Row → ℕ) : (∑ z : Row, if H z then f z else 0) = ∑ i : Fin 31, f (e i) := by
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter fun z => H z) = Finset.univ.image e := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact H_iff z
  rw [hs, Finset.sum_image (fun i _ k _ h => e_injective h)]

/-- The transfer recursion on indices of rows satisfying `H`. -/
def G : ℕ → Fin 31 → Fin 31 → ℕ
  | 0, _, _ => 1
  | m + 1, i, k => ∑ l : Fin 31, if V (e i) (e k) (e l) then G m k l else 0

theorem T_eq_G (m : ℕ) : ∀ i k : Fin 31, T m (e i) (e k) = G m i k := by
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
def Pc (i k : Fin 31) : Fin 8 → ℕ := polys (pid i k)

/-- Evaluation in the binomial basis. -/
def ev (c : Fin 8 → ℕ) (m : ℕ) : ℕ := ∑ d : Fin 8, c d * m.choose d

/-- The next coefficient. -/
def nx (c : Fin 8 → ℕ) (d : Fin 8) : ℕ := if h : d.val + 1 < 8 then c ⟨d.val + 1, h⟩ else 0

theorem ev_succ (c : Fin 8 → ℕ) (m : ℕ) :
    ev c (m + 1) = ∑ d : Fin 8, (c d + nx c d) * m.choose d := by
  simp only [ev, nx, Fin.sum_univ_eight]
  simp [Nat.choose_succ_succ]
  ring

theorem base_check : ∀ i k : Fin 31, Pc i k 0 = 1 := by
  decide +kernel

/-- The induction step for the pairs `(e i, e k)` with `i` fixed, coefficient by coefficient. -/
def SC (i : Fin 31) : Prop :=
  ∀ k : Fin 31, ∀ d : Fin 8,
    (∑ l : Fin 31, if V (e i) (e k) (e l) then Pc k l d else 0) = Pc i k d + nx (Pc i k) d

instance decSC (i : Fin 31) : Decidable (SC i) := by
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

theorem sc18 : SC 18 := by
  decide +kernel

theorem sc19 : SC 19 := by
  decide +kernel

theorem sc20 : SC 20 := by
  decide +kernel

theorem sc21 : SC 21 := by
  decide +kernel

theorem sc22 : SC 22 := by
  decide +kernel

theorem sc23 : SC 23 := by
  decide +kernel

theorem sc24 : SC 24 := by
  decide +kernel

theorem sc25 : SC 25 := by
  decide +kernel

theorem sc26 : SC 26 := by
  decide +kernel

theorem sc27 : SC 27 := by
  decide +kernel

theorem sc28 : SC 28 := by
  decide +kernel

theorem sc29 : SC 29 := by
  decide +kernel

theorem sc30 : SC 30 := by
  decide +kernel

theorem step_check (i : Fin 31) : SC i := by
  fin_cases i
  exacts [sc0, sc1, sc2, sc3, sc4, sc5, sc6, sc7, sc8, sc9, sc10, sc11, sc12, sc13, sc14, sc15, sc16, sc17, sc18, sc19, sc20, sc21, sc22, sc23, sc24, sc25, sc26, sc27, sc28, sc29, sc30]

end OMA.Helpers
namespace OMA.Helpers

open OMA.S_oeis_a207390 Finset

theorem G_eq (m : ℕ) : ∀ i k : Fin 31, G m i k = ev (Pc i k) m := by
  induction m with
  | zero =>
    intro i k
    simp [G, ev, Fin.sum_univ_eight, base_check]
  | succ m ih =>
    intro i k
    rw [ev_succ]
    have h1 : ∀ d : Fin 8, Pc i k d + nx (Pc i k) d =
        ∑ l : Fin 31, if V (e i) (e k) (e l) then Pc k l d else 0 :=
      fun d => (step_check i k d).symm
    simp only [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [G, ih]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rfl
    · simp

/-- The coefficients of `a (n + 2)` in the binomial basis. -/
def Sv : Fin 8 → ℕ := ![961, 5154, 11802, 14126, 9324, 3284, 532, 24]

theorem sum_check : ∀ d : Fin 8, (∑ i : Fin 31, ∑ k : Fin 31, Pc i k d) = Sv d := by
  decide +kernel

theorem aN_two (n : ℕ) : aN (n + 2) = ∑ d : Fin 8, Sv d * n.choose d := by
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
  calc (∑ i : Fin 31, ∑ k : Fin 31, ∑ d : Fin 8, Pc i k d * n.choose d)
      = ∑ i : Fin 31, ∑ d : Fin 8, ∑ k : Fin 31, Pc i k d * n.choose d :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ d : Fin 8, ∑ i : Fin 31, ∑ k : Fin 31, Pc i k d * n.choose d := Finset.sum_comm

theorem aN_one' : aN 1 = 31 := by
  rw [aN_one, sum_H (fun _ => 1)]
  simp

theorem chq (m d : ℕ) :
    (m.choose d : ℚ) = (descPochhammer ℚ d).eval (m : ℚ) / (d.factorial : ℚ) :=
  Nat.cast_choose_eq_descPochhammer_div ℚ m d

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    5040 * (aN n : ℚ) = 24 * (n : ℚ) ^ 7 + 2884 * n ^ 6 + 49644 * n ^ 5 + 201460 * n ^ 4 +
      73836 * n ^ 3 - 194264 * n ^ 2 + 7536 * n + 15120 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [aN_one']
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [aN_two]
    push_cast
    simp only [Fin.sum_univ_eight, chq]
    simp [Sv, descPochhammer_succ_eval, Nat.factorial]
    ring

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (24 * (n : ℚ) ^ 7 + 2884 * n ^ 6 + 49644 * n ^ 5 + 201460 * n ^ 4 +
      73836 * n ^ 3 - 194264 * n ^ 2 + 7536 * n + 15120) / 5040 := by
  rw [a_eq_aN, ← closed n hn]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
    closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega),
    closedQ (n - 6) (by omega), closedQ (n - 7) (by omega), closedQ (n - 8) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
    show 8 ≤ n by omega]
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) =
      X * (31 + 713 * X - 705 * X ^ 2 - 677 * X ^ 3 + 961 * X ^ 4 - 341 * X ^ 5 + 45 * X ^ 6 -
        3 * X ^ 7) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 8 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 8 * (PowerSeries.mk F * X ^ 1) +
        C 28 * (PowerSeries.mk F * X ^ 2) - C 56 * (PowerSeries.mk F * X ^ 3) +
        C 70 * (PowerSeries.mk F * X ^ 4) - C 56 * (PowerSeries.mk F * X ^ 5) +
        C 28 * (PowerSeries.mk F * X ^ 6) - C 8 * (PowerSeries.mk F * X ^ 7) +
        C 1 * (PowerSeries.mk F * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (31 + 713 * X - 705 * X ^ 2 - 677 * X ^ 3 + 961 * X ^ 4 -
      341 * X ^ 5 + 45 * X ^ 6 - 3 * X ^ 7) =
      C 31 * X ^ 1 + C 713 * X ^ 2 - C 705 * X ^ 3 - C 677 * X ^ 4 + C 961 * X ^ 5 -
        C 341 * X ^ 6 + C 45 * X ^ 7 - C 3 * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have r := recurrence (j + 9) (by omega)
    simp only [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega,
      show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega,
      show j + 9 - 5 = j + 4 by omega, show j + 9 - 6 = j + 3 by omega,
      show j + 9 - 7 = j + 2 by omega, show j + 9 - 8 = j + 1 by omega] at r
    simp only [show 0 ≤ j + 9 by omega, show 1 ≤ j + 9 by omega, show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega, show 4 ≤ j + 9 by omega, show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega, show 7 ≤ j + 9 by omega, show 8 ≤ j + 9 by omega,
      show j + 9 - 0 = j + 9 by omega, show j + 9 - 1 = j + 8 by omega,
      show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega,
      show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega,
      show ¬ (j + 9 < 1) by omega, show ¬ (j + 8 < 1) by omega, show ¬ (j + 7 < 1) by omega,
      show ¬ (j + 6 < 1) by omega, show ¬ (j + 5 < 1) by omega, show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207390.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
