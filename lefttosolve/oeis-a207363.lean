import OMAStatements.S_oeis_a207363
import Mathlib

/-!
Proof of the three conjectures of OEIS A207363 (n X 3 binary arrays avoiding 0 0 0 and 0 1 1
horizontally and 0 0 1 and 0 1 1 vertically).

A row is allowed iff it is not 0 0 0 or 0 1 1 (6 rows). The vertical condition says that a 0 in
row i forces a 0 in row i + 2 of the same column, so it only links rows two apart: the rows of
each parity form a chain z_1 >= z_2 >= ... of allowed rows (columnwise). Removing the first row
gives a transfer recursion T, and T m x y = D ((m+1)/2) x * D (m/2) y, where D k x counts chains
of length k below x. On allowed rows D k x = alpha + beta k + gamma k^2 (three finite identities
checked by the kernel), and summing over the first row gives D (k+1) (1 1 1) = (k+2)(2k+3). Hence
a(n) = Q((n+1)/2) Q(n/2) with Q k = (k+1)(2k+1), which gives both closed forms; the generating
function follows from the order-8 recurrence they satisfy.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207363 Finset

/-- A row of the array. -/
abbrev Row := Fin 3 → Fin 2

/-- The horizontal condition: the row is not `0 0 0` and not `0 1 1`. -/
def H (z : Row) : Prop := z 0 = 0 → z 1 ≠ z 2

instance decH (z : Row) : Decidable (H z) := by
  unfold H
  infer_instance

/-- `z` lies below `x`: every column where `x` is `0` is `0` in `z`. -/
def Le (x z : Row) : Prop := ∀ j : Fin 3, x j = 0 → z j = 0

instance decLe (x z : Row) : Decidable (Le x z) := by
  unfold Le
  infer_instance

/-- The vertical condition on three consecutive rows (avoiding `0 0 1` and `0 1 1`). -/
def V (x _y z : Row) : Prop := Le x z

instance decV (x y z : Row) : Decidable (V x y z) := decLe x z

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
    ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 0, 1) ∧ ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 1, 1) ↔
      (a = 0 → c = 0) := by
  revert a b c
  decide

theorem get_eq {m : ℕ} (A : Fin m → Row) (i j : ℕ) (hi : i < m) (hj : j < 3) :
    OMA.S_oeis_a207363.get A i j = (A ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by
  unfold OMA.S_oeis_a207363.get
  rw [dif_pos ⟨hi, hj⟩]

theorem avoids_iff {m : ℕ} (A : Fin m → Row) : avoids A = true ↔ AllH A ∧ Chain A := by
  unfold avoids
  rw [decide_eq_true_iff]
  apply and_congr
  · constructor
    · intro h i
      have := h i.val i.isLt 0 (by omega)
      rw [get_eq A i 0 i.isLt (by omega), get_eq A i (0 + 1) i.isLt (by omega),
        get_eq A i (0 + 2) i.isLt (by omega)] at this
      exact (tri_h _ _ _).1 this
    · intro h i hi j hj
      obtain rfl : j = 0 := by omega
      rw [get_eq A i 0 hi (by omega), get_eq A i (0 + 1) hi (by omega),
        get_eq A i (0 + 2) hi (by omega)]
      exact (tri_h _ _ _).2 (h ⟨i, hi⟩)
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

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
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
  ((Finset.univ : Finset (Fin n → Fin 3 → Fin 2)).filter (fun x => avoids x)).card

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

/-- `D k x`: the number of chains `z_1, ..., z_k` of allowed rows with `z_1` below `x` and each
`z_(i+1)` below `z_i`. -/
def D : ℕ → Row → ℕ
  | 0, _ => 1
  | k + 1, x => ∑ z : Row, if H z ∧ Le x z then D k z else 0

theorem T_eq (m : ℕ) : ∀ x y : Row, T m x y = D ((m + 1) / 2) x * D (m / 2) y := by
  induction m with
  | zero => intro x y; rw [T_zero]; rfl
  | succ m ih =>
    intro x y
    rw [T_succ, show (m + 1 + 1) / 2 = m / 2 + 1 by omega, D, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ih y z]
    unfold V
    split_ifs
    · ring
    · simp

/-- The top row `1 1 1`. -/
def top : Row := fun _ => 1

theorem le_top (z : Row) : Le top z := fun j h => by simp [top] at h

theorem sum_H (k : ℕ) : (∑ x : Row, if H x then D k x else 0) = D (k + 1) top := by
  rw [D]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [le_top, and_true]

/-- Closed form of `D` on allowed rows: `α + β k + γ k^2`. -/
def α (_x : Row) : ℕ := 1

def β (x : Row) : ℕ := if x = ![1, 1, 1] then 3 else if x = ![1, 0, 1] ∨ x = ![1, 1, 0] then 2 else 0

def γ (x : Row) : ℕ := if x = ![1, 1, 1] then 2 else 0

theorem S1 : ∀ x : Row, H x → (∑ z : Row, if H z ∧ Le x z then α z else 0) = α x + β x + γ x := by
  decide +kernel

theorem S2 : ∀ x : Row, H x → (∑ z : Row, if H z ∧ Le x z then β z else 0) = β x + 2 * γ x := by
  decide +kernel

theorem S3 : ∀ x : Row, H x → (∑ z : Row, if H z ∧ Le x z then γ z else 0) = γ x := by
  decide +kernel

theorem D_closed (k : ℕ) : ∀ x : Row, H x → D k x = α x + β x * k + γ x * k ^ 2 := by
  induction k with
  | zero => intro x _; simp [D, α]
  | succ k ih =>
    intro x hx
    rw [D]
    have e : ∀ z : Row, (if H z ∧ Le x z then D k z else 0) =
        (if H z ∧ Le x z then α z else 0) + (if H z ∧ Le x z then β z else 0) * k +
          (if H z ∧ Le x z then γ z else 0) * k ^ 2 := by
      intro z
      by_cases hz : H z ∧ Le x z
      · simp only [if_pos hz]; exact ih z hz.1
      · simp only [if_neg hz]; ring
    rw [Finset.sum_congr rfl fun z _ => e z, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, S1 x hx, S2 x hx, S3 x hx]
    ring

theorem H_top : H top := fun h => by simp [top] at h

theorem top_eq : top = ![1, 1, 1] := by
  funext j
  fin_cases j <;> rfl

/-- `Q k = (k + 1) (2 k + 1)`, the number of chains of length `k` of allowed rows. -/
def Q (k : ℕ) : ℕ := (k + 1) * (2 * k + 1)

theorem D_top (k : ℕ) : D k top = Q k := by
  rw [D_closed k top H_top, top_eq, Q]
  simp only [α, β, γ, if_true]
  ring

theorem aN_formula (n : ℕ) (hn : 1 ≤ n) : aN n = Q ((n + 1) / 2) * Q (n / 2) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [aN_one]
    decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [aN_eq, show (m + 2 + 1) / 2 = (m + 1) / 2 + 1 by omega,
      show (m + 2) / 2 = m / 2 + 1 by omega, ← D_top, ← D_top, ← sum_H, ← sum_H,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [T_eq]
    by_cases hx : H x <;> by_cases hy : H y <;> simp [hx, hy]

theorem aQ_even (m : ℕ) (hm : 1 ≤ m) :
    (a (2 * m) : ℚ) = ((m : ℚ) + 1) ^ 2 * (2 * m + 1) ^ 2 := by
  rw [a_eq_aN, aN_formula _ (by omega), show (2 * m + 1) / 2 = m by omega,
    show 2 * m / 2 = m by omega, Q]
  push_cast
  ring

theorem aQ_odd (m : ℕ) :
    (a (2 * m + 1) : ℚ) = ((m : ℚ) + 2) * (2 * m + 3) * ((m : ℚ) + 1) * (2 * m + 1) := by
  rw [a_eq_aN, aN_formula _ (by omega), show (2 * m + 1 + 1) / 2 = m + 1 by omega,
    show (2 * m + 1) / 2 = m by omega, Q, Q]
  push_cast
  ring

theorem closed_even (n : ℕ) (hn : 1 ≤ n) (he : Even n) :
    (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 + 13 * (n : ℚ) ^ 2 + 12 * (n : ℚ) + 4) / 4 := by
  obtain ⟨m, rfl⟩ := he
  rw [show m + m = 2 * m by ring, aQ_even m (by omega)]
  push_cast
  ring

theorem closed_odd (n : ℕ) (ho : Odd n) :
    (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 + 11 * (n : ℚ) ^ 2 + 6 * (n : ℚ)) / 4 := by
  obtain ⟨m, rfl⟩ := ho
  rw [aQ_odd m]
  push_cast
  ring

/-- The linear recurrence behind the generating function. -/
theorem rec9 (j : ℕ) :
    (a (j + 9) : ℚ) - 2 * a (j + 8) - 2 * a (j + 7) + 6 * a (j + 6) - 6 * a (j + 4) +
      2 * a (j + 3) + 2 * a (j + 2) - a (j + 1) = 0 := by
  rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [show i + i + 9 = 2 * (i + 4) + 1 by ring, show i + i + 8 = 2 * (i + 4) by ring,
      show i + i + 7 = 2 * (i + 3) + 1 by ring, show i + i + 6 = 2 * (i + 3) by ring,
      show i + i + 4 = 2 * (i + 2) by ring, show i + i + 3 = 2 * (i + 1) + 1 by ring,
      show i + i + 2 = 2 * (i + 1) by ring, show i + i + 1 = 2 * i + 1 by ring,
      aQ_odd, aQ_even _ (by omega), aQ_odd, aQ_even _ (by omega), aQ_even _ (by omega), aQ_odd,
      aQ_even _ (by omega), aQ_odd]
    push_cast
    ring
  · rw [show 2 * i + 1 + 9 = 2 * (i + 5) by ring, show 2 * i + 1 + 8 = 2 * (i + 4) + 1 by ring,
      show 2 * i + 1 + 7 = 2 * (i + 4) by ring, show 2 * i + 1 + 6 = 2 * (i + 3) + 1 by ring,
      show 2 * i + 1 + 4 = 2 * (i + 2) + 1 by ring, show 2 * i + 1 + 3 = 2 * (i + 2) by ring,
      show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, show 2 * i + 1 + 1 = 2 * (i + 1) by ring,
      aQ_even _ (by omega), aQ_odd, aQ_even _ (by omega), aQ_odd, aQ_odd, aQ_even _ (by omega),
      aQ_odd, aQ_even _ (by omega)]
    push_cast
    ring

theorem a1 : (a 1 : ℚ) = 6 := by rw [show 1 = 2 * 0 + 1 by rfl, aQ_odd]; norm_num
theorem a2 : (a 2 : ℚ) = 36 := by rw [show 2 = 2 * 1 by rfl, aQ_even 1 le_rfl]; norm_num
theorem a3 : (a 3 : ℚ) = 90 := by rw [show 3 = 2 * 1 + 1 by rfl, aQ_odd]; norm_num
theorem a4 : (a 4 : ℚ) = 225 := by rw [show 4 = 2 * 2 by rfl, aQ_even 2 (by norm_num)]; norm_num
theorem a5 : (a 5 : ℚ) = 420 := by rw [show 5 = 2 * 2 + 1 by rfl, aQ_odd]; norm_num
theorem a6 : (a 6 : ℚ) = 784 := by rw [show 6 = 2 * 3 by rfl, aQ_even 3 (by norm_num)]; norm_num
theorem a7 : (a 7 : ℚ) = 1260 := by rw [show 7 = 2 * 3 + 1 by rfl, aQ_odd]; norm_num
theorem a8 : (a 8 : ℚ) = 2025 := by rw [show 8 = 2 * 4 by rfl, aQ_even 4 (by norm_num)]; norm_num

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) =
      X * (6 + 24 * X + 6 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  have key : PowerSeries.mk F * ((1 - X) ^ 5 * (1 + X) ^ 3) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 2 * (PowerSeries.mk F * X ^ 1) -
        C 2 * (PowerSeries.mk F * X ^ 2) + C 6 * (PowerSeries.mk F * X ^ 3) -
        C 6 * (PowerSeries.mk F * X ^ 5) + C 2 * (PowerSeries.mk F * X ^ 6) +
        C 2 * (PowerSeries.mk F * X ^ 7) - C 1 * (PowerSeries.mk F * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (6 + 24 * X + 6 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 -
      2 * X ^ 6 + X ^ 7) =
      C 6 * X ^ 1 + C 24 * X ^ 2 + C 6 * X ^ 3 + C 9 * X ^ 4 + C 6 * X ^ 5 -
        C 2 * X ^ 6 - C 2 * X ^ 7 + C 1 * X ^ 8 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [hF, a1, a2, a3, a4, a5, a6, a7, a8]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have r := rec9 j
    simp only [show 0 ≤ j + 9 by omega, show 1 ≤ j + 9 by omega, show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega, show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega, show 7 ≤ j + 9 by omega, show 8 ≤ j + 9 by omega,
      show j + 9 - 0 = j + 9 by omega, show j + 9 - 1 = j + 8 by omega,
      show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega,
      show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega,
      show ¬ (j + 9 < 1) by omega, show ¬ (j + 8 < 1) by omega, show ¬ (j + 7 < 1) by omega,
      show ¬ (j + 6 < 1) by omega, show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207363.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed_even, fun n _ ho => OMA.Helpers.closed_odd n ho⟩
