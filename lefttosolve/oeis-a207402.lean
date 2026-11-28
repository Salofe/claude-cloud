import OMAStatements.S_oeis_a207402
import Mathlib

/-!
Proof of the g.f. and the recurrence conjectured in A207402 (n X 7 0..1 arrays avoiding 0 0 1 and
0 1 1 horizontally and 0 0 1 and 1 1 0 vertically).

Splitting. A row avoids `0 0 1` and `0 1 1` iff `x j = 0 → x (j + 2) = 0`, so the entries in the
columns 0, 2, 4, 6 and those in the columns 1, 3, 5 each form a row `1 .. 1 0 .. 0`. The column
condition is entrywise, so an array is valid iff its even part (width 4) and its odd part (width 3)
are both valid for "rows of the form `1 .. 1 0 .. 0`, columns avoiding `0 0 1` and `1 1 0`"
(`avoids_iff`), and `a n = E 4 n * E 3 n` (`a_eq`).

Transfer. A column avoids `0 0 1` and `1 1 0` iff `u = v → w = v` for any three consecutive
entries, a condition on three consecutive rows, so removing the first row gives a transfer
recursion for the number `T m x y` of continuations of the rows `x, y` by `m` rows. By induction,
`T m x y = Sum_{i ≤ 4} C(d, i) * C(m, i)` when `x, y` are both of the form `1 .. 1 0 .. 0`, with
`d` their Hamming distance (and `0` otherwise); the induction step is a finite check of five
coefficient identities per pair of rows (`step4`, `step3`). Summing over the pairs,
`E 4 (m + 2) = 25 + 40 m + 30 C(m, 2) + 12 C(m, 3) + 2 C(m, 4)` and
`E 3 (m + 2) = 16 + 20 m + 10 C(m, 2) + 2 C(m, 3)`, that is
`E 4 n = (n + 1)(n + 2)(n + 3)(n + 4)/12 - 5` and `E 3 n = (n + 1)(n + 2)(n + 3)/3 - 4` for `n ≥ 1`.
So `a n` is a polynomial of degree 7 in `n` for `n ≥ 1`; the recurrence and the g.f. follow by
comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207402 Finset

/-- A row of width `k`. -/
abbrev Rw (k : ℕ) := Fin k → Fin 2

/-- A weakly decreasing row `1 .. 1 0 .. 0`. -/
def Dec {k : ℕ} (r : Rw k) : Prop :=
  ∀ j : Fin k, ∀ h : j.val + 1 < k, r j = 0 → r ⟨j.val + 1, h⟩ = 0

instance decDec {k : ℕ} (r : Rw k) : Decidable (Dec r) := by
  unfold Dec
  infer_instance

/-- Three consecutive entries of a column avoid `0 0 1` and `1 1 0`. -/
def CT (u v w : Fin 2) : Prop := u = v → w = v

instance decCT (u v w : Fin 2) : Decidable (CT u v w) := by
  unfold CT
  infer_instance

/-- The column condition on three consecutive rows. -/
def CA {k : ℕ} (x y z : Rw k) : Prop := ∀ j, CT (x j) (y j) (z j)

instance decCA {k : ℕ} (x y z : Rw k) : Decidable (CA x y z) := by
  unfold CA
  infer_instance

/-- Every row is weakly decreasing and every three consecutive rows satisfy `CA`. -/
def Chain {k m : ℕ} (A : Fin m → Rw k) : Prop :=
  (∀ i, Dec (A i)) ∧
    ∀ i : Fin m, ∀ h : i.val + 2 < m, CA (A i) (A ⟨i.val + 1, by omega⟩) (A ⟨i.val + 2, h⟩)

instance decChain {k m : ℕ} (A : Fin m → Rw k) : Decidable (Chain A) := by
  unfold Chain
  infer_instance

theorem chain_cons {k m : ℕ} (x : Rw k) (B : Fin (m + 2) → Rw k) :
    Chain (Fin.cons x B : Fin (m + 3) → Rw k) ↔ Dec x ∧ CA x (B 0) (B 1) ∧ Chain B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0, h2 0 (by simp), fun i => h1 i.succ,
      fun i hi => h2 i.succ (by simp only [Fin.val_succ]; omega)⟩
  · rintro ⟨hx, hc, h1, h2⟩
    refine ⟨fun i => Fin.cases hx h1 i, fun i hi => ?_⟩
    cases i using Fin.cases with
    | zero => exact hc
    | succ i => exact h2 i (by simp only [Fin.val_succ] at hi; omega)

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
def T {k : ℕ} (m : ℕ) (x y : Rw k) : ℕ :=
  ∑ B : Fin m → Rw k, if Chain (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Rw k) then 1 else 0

theorem T_zero {k : ℕ} (x y : Rw k) : T 0 x y = if Dec x ∧ Dec y then 1 else 0 := by
  unfold T
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0, h1 1⟩
  · rintro ⟨hx, hy⟩
    refine ⟨fun i => ?_, fun i hi => absurd hi (by omega)⟩
    fin_cases i
    · exact hx
    · exact hy

theorem T_succ {k : ℕ} (m : ℕ) (x y : Rw k) :
    T (m + 1) x y = ∑ z : Rw k, if Dec x ∧ CA x y z then T m y z else 0 := by
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Rw k).symm _
    (fun p => if Chain (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Rw k)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : Dec x ∧ CA x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chain_cons]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chain_cons]
    exact fun h => hv ⟨h.1, h.2.1⟩

/-- The number of `n`-row arrays of width `k` satisfying `Chain`. -/
def E (k n : ℕ) : ℕ := ∑ A : Fin n → Rw k, if Chain A then 1 else 0

theorem E_eq {k : ℕ} (m : ℕ) : E k (m + 2) = ∑ x : Rw k, ∑ y : Rw k, T m x y := by
  unfold E
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Rw k).symm _
    (fun p => if Chain (Fin.cons p.1 p.2 : Fin (m + 2) → Rw k) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Rw k).symm _
    (fun p => if Chain (Fin.cons x (Fin.cons p.1 p.2) : Fin (m + 2) → Rw k) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

/-- The Hamming distance of two rows. -/
def hd {k : ℕ} (x y : Rw k) : ℕ := (univ.filter (fun j => x j ≠ y j)).card

/-- The coefficient of `m.choose i` in `T m x y`. -/
def cf {k : ℕ} (x y : Rw k) (i : ℕ) : ℕ := if Dec x ∧ Dec y then (hd x y).choose i else 0

/-- The transfer step, coefficient by coefficient. -/
def StepFacts {k : ℕ} (x y : Rw k) : Prop :=
  (∑ z : Rw k, if Dec x ∧ CA x y z then cf y z 0 else 0) = cf x y 0 + cf x y 1 ∧
  (∑ z : Rw k, if Dec x ∧ CA x y z then cf y z 1 else 0) = cf x y 1 + cf x y 2 ∧
  (∑ z : Rw k, if Dec x ∧ CA x y z then cf y z 2 else 0) = cf x y 2 + cf x y 3 ∧
  (∑ z : Rw k, if Dec x ∧ CA x y z then cf y z 3 else 0) = cf x y 3 + cf x y 4 ∧
  (∑ z : Rw k, if Dec x ∧ CA x y z then cf y z 4 else 0) = cf x y 4

theorem step4 : ∀ x y : Rw 4, StepFacts x y := by
  unfold StepFacts
  decide +kernel


theorem step3 : ∀ x y : Rw 3, StepFacts x y := by
  unfold StepFacts
  decide +kernel

/-- The closed form of `T m x y` in the binomial basis. -/
def Fm {k : ℕ} (x y : Rw k) (m : ℕ) : ℕ :=
  cf x y 0 + cf x y 1 * m.choose 1 + cf x y 2 * m.choose 2 + cf x y 3 * m.choose 3 +
    cf x y 4 * m.choose 4

theorem T_closed {k : ℕ} (hs : ∀ x y : Rw k, StepFacts x y) (m : ℕ) :
    ∀ x y : Rw k, T m x y = Fm x y m := by
  induction m with
  | zero =>
    intro x y
    rw [T_zero]
    simp [Fm, cf]
  | succ m ih =>
    intro x y
    rw [T_succ]
    have hP : ∀ z : Rw k, (if Dec x ∧ CA x y z then T m y z else 0) =
        (if Dec x ∧ CA x y z then cf y z 0 else 0) +
        (if Dec x ∧ CA x y z then cf y z 1 else 0) * m.choose 1 +
        (if Dec x ∧ CA x y z then cf y z 2 else 0) * m.choose 2 +
        (if Dec x ∧ CA x y z then cf y z 3 else 0) * m.choose 3 +
        (if Dec x ∧ CA x y z then cf y z 4 else 0) * m.choose 4 := by
      intro z
      split_ifs
      · rw [ih y z]
        rfl
      · simp
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h0, h1, h2, h3, h4⟩ := hs x y
    rw [h0, h1, h2, h3, h4]
    have e1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ m 0
    have e2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    have e3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    have e4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ m 3
    simp only [Fm, e1, e2, e3, e4, Nat.choose_zero_right]
    ring

theorem sum4 :
    (∑ x : Rw 4, ∑ y : Rw 4, cf x y 0) = 25 ∧ (∑ x : Rw 4, ∑ y : Rw 4, cf x y 1) = 40 ∧
    (∑ x : Rw 4, ∑ y : Rw 4, cf x y 2) = 30 ∧ (∑ x : Rw 4, ∑ y : Rw 4, cf x y 3) = 12 ∧
    (∑ x : Rw 4, ∑ y : Rw 4, cf x y 4) = 2 := by
  decide +kernel

theorem sum3 :
    (∑ x : Rw 3, ∑ y : Rw 3, cf x y 0) = 16 ∧ (∑ x : Rw 3, ∑ y : Rw 3, cf x y 1) = 20 ∧
    (∑ x : Rw 3, ∑ y : Rw 3, cf x y 2) = 10 ∧ (∑ x : Rw 3, ∑ y : Rw 3, cf x y 3) = 2 ∧
    (∑ x : Rw 3, ∑ y : Rw 3, cf x y 4) = 0 := by
  decide +kernel

theorem E4_closed (m : ℕ) : E 4 (m + 2) =
    25 + 40 * m.choose 1 + 30 * m.choose 2 + 12 * m.choose 3 + 2 * m.choose 4 := by
  rw [E_eq]
  simp only [T_closed step4 m, Fm, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h0, h1, h2, h3, h4⟩ := sum4
  rw [h0, h1, h2, h3, h4]

theorem E3_closed (m : ℕ) : E 3 (m + 2) =
    16 + 20 * m.choose 1 + 10 * m.choose 2 + 2 * m.choose 3 + 0 * m.choose 4 := by
  rw [E_eq]
  simp only [T_closed step3 m, Fm, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h0, h1, h2, h3, h4⟩ := sum3
  rw [h0, h1, h2, h3, h4]

theorem E4_one : E 4 1 = 5 := by decide +kernel

theorem E3_one : E 3 1 = 4 := by decide +kernel

theorem ch2 (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 1, Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

theorem ch3 (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 2, Nat.cast_add, ih, ch2]
    push_cast
    ring

theorem ch4 (m : ℕ) : (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 3, Nat.cast_add, ih, ch3]
    push_cast
    ring

theorem E4Q (n : ℕ) (hn : 1 ≤ n) :
    (E 4 n : ℚ) = (n + 1) * (n + 2) * (n + 3) * (n + 4) / 12 - 5 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [E4_one]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [E4_closed]
    push_cast
    rw [ch2, ch3, ch4, Nat.choose_one_right]
    ring

theorem E3Q (n : ℕ) (hn : 1 ≤ n) :
    (E 3 n : ℚ) = (n + 1) * (n + 2) * (n + 3) / 3 - 4 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [E3_one]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [E3_closed]
    push_cast
    rw [ch2, ch3, ch4, Nat.choose_one_right]
    ring


/-- The entries of a 7-row in the columns 0, 2, 4, 6. -/
def ev (r : Fin 7 → Fin 2) : Rw 4 := ![r 0, r 2, r 4, r 6]

/-- The entries of a 7-row in the columns 1, 3, 5. -/
def od (r : Fin 7 → Fin 2) : Rw 3 := ![r 1, r 3, r 5]

/-- Interleave a 4-row and a 3-row into a 7-row. -/
def mrg (u : Rw 4) (v : Rw 3) : Fin 7 → Fin 2 := ![u 0, v 0, u 1, v 1, u 2, v 2, u 3]

/-- Split an array into its even and odd columns. -/
def splitA (n : ℕ) : (Fin n → Fin 7 → Fin 2) ≃ (Fin n → Rw 4) × (Fin n → Rw 3) where
  toFun A := (fun i => ev (A i), fun i => od (A i))
  invFun p := fun i => mrg (p.1 i) (p.2 i)
  left_inv A := by
    funext i c
    fin_cases c <;> rfl
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> funext i j <;> fin_cases j <;> rfl

/-- Entry `j` of a 7-row as a natural number (`0` outside the row). -/
def gr (r : Fin 7 → Fin 2) (j : ℕ) : ℕ := if h : j < 7 then (r ⟨j, h⟩ : ℕ) else 0

theorem get_eq {n : ℕ} (x : Fin n → Fin 7 → Fin 2) (i j : ℕ) (hi : i < n) :
    S_oeis_a207402.get x i j = gr (x ⟨i, hi⟩) j := by
  unfold S_oeis_a207402.get gr
  by_cases hj : j < 7
  · rw [dif_pos ⟨hi, hj⟩, dif_pos hj]
  · rw [dif_neg (fun h => hj h.2), dif_neg hj]

theorem row_iff : ∀ r : Fin 7 → Fin 2,
    (∀ j < 7 - 2, (gr r j, gr r (j + 1), gr r (j + 2)) ≠ (0, 0, 1) ∧
      (gr r j, gr r (j + 1), gr r (j + 2)) ≠ (0, 1, 1)) ↔ Dec (ev r) ∧ Dec (od r) := by
  decide +kernel

theorem ent_iff : ∀ u v w : Fin 2, (((u : ℕ), (v : ℕ), (w : ℕ)) ≠ (0, 0, 1) ∧
    ((u : ℕ), (v : ℕ), (w : ℕ)) ≠ (1, 1, 0)) ↔ CT u v w := by
  decide

theorem col_iff (r s t : Fin 7 → Fin 2) :
    (∀ j < 7, (gr r j, gr s j, gr t j) ≠ (0, 0, 1) ∧ (gr r j, gr s j, gr t j) ≠ (1, 1, 0)) ↔
      CA (ev r) (ev s) (ev t) ∧ CA (od r) (od s) (od t) := by
  have h1 : (∀ j < 7, (gr r j, gr s j, gr t j) ≠ (0, 0, 1) ∧
      (gr r j, gr s j, gr t j) ≠ (1, 1, 0)) ↔ ∀ j : Fin 7, CT (r j) (s j) (t j) := by
    constructor
    · intro h j
      have := h j.val j.isLt
      simp only [gr, dif_pos j.isLt, Fin.eta] at this
      exact (ent_iff _ _ _).1 this
    · intro h j hj
      simp only [gr, dif_pos hj]
      exact (ent_iff _ _ _).2 (h ⟨j, hj⟩)
  rw [h1]
  unfold CA
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · fin_cases j
      exacts [h 0, h 2, h 4, h 6]
    · fin_cases j
      exacts [h 1, h 3, h 5]
  · rintro ⟨he, ho⟩ j
    fin_cases j
    exacts [he 0, ho 0, he 1, ho 1, he 2, ho 2, he 3]

theorem avoids_iff {n : ℕ} (x : Fin n → Fin 7 → Fin 2) :
    avoids x = true ↔ Chain (fun i => ev (x i)) ∧ Chain (fun i => od (x i)) := by
  unfold avoids
  rw [decide_eq_true_iff]
  have hrow : (∀ i < n, ∀ j < 7 - 2,
      (S_oeis_a207402.get x i j, S_oeis_a207402.get x i (j + 1),
        S_oeis_a207402.get x i (j + 2)) ≠ (0, 0, 1) ∧
      (S_oeis_a207402.get x i j, S_oeis_a207402.get x i (j + 1),
        S_oeis_a207402.get x i (j + 2)) ≠ (0, 1, 1)) ↔
      ∀ i : Fin n, Dec (ev (x i)) ∧ Dec (od (x i)) := by
    constructor
    · intro h i
      have := h i.val i.isLt
      simp only [get_eq x _ _ i.isLt, Fin.eta] at this
      exact (row_iff _).1 this
    · intro h i hi
      simp only [get_eq x _ _ hi]
      exact (row_iff _).2 (h ⟨i, hi⟩)
  have hcol : (∀ i < n - 2, ∀ j < 7,
      (S_oeis_a207402.get x i j, S_oeis_a207402.get x (i + 1) j,
        S_oeis_a207402.get x (i + 2) j) ≠ (0, 0, 1) ∧
      (S_oeis_a207402.get x i j, S_oeis_a207402.get x (i + 1) j,
        S_oeis_a207402.get x (i + 2) j) ≠ (1, 1, 0)) ↔
      ∀ i : Fin n, ∀ h : i.val + 2 < n,
        CA (ev (x i)) (ev (x ⟨i.val + 1, by omega⟩)) (ev (x ⟨i.val + 2, h⟩)) ∧
        CA (od (x i)) (od (x ⟨i.val + 1, by omega⟩)) (od (x ⟨i.val + 2, h⟩)) := by
    constructor
    · intro hc i hi
      have := hc i.val (by omega)
      simp only [get_eq x i.val _ i.isLt, get_eq x (i.val + 1) _ (by omega),
        get_eq x (i.val + 2) _ hi, Fin.eta] at this
      exact (col_iff _ _ _).1 this
    · intro hc i hi
      simp only [get_eq x i _ (by omega), get_eq x (i + 1) _ (by omega),
        get_eq x (i + 2) _ (by omega)]
      exact (col_iff _ _ _).2 (hc ⟨i, by omega⟩ (by simp only; omega))
  rw [hrow, hcol]
  unfold Chain
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun i => (h1 i).1, fun i hi => (h2 i hi).1⟩,
      ⟨fun i => (h1 i).2, fun i hi => (h2 i hi).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun i => ⟨h1 i, h3 i⟩, fun i hi => ⟨h2 i hi, h4 i hi⟩⟩

theorem a_eq (n : ℕ) : a n = (E 4 n : ℤ) * (E 3 n : ℤ) := by
  have h : ((Finset.univ : Finset (Fin n → Fin 7 → Fin 2)).filter (fun x => avoids x)).card =
      ((univ.filter (fun A : Fin n → Rw 4 => Chain A)) ×ˢ
        (univ.filter (fun A : Fin n → Rw 3 => Chain A))).card := by
    refine Finset.card_equiv (splitA n) fun A => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    exact avoids_iff A
  have hE : ∀ k, E k n = (univ.filter (fun A : Fin n → Rw k => Chain A)).card := by
    intro k
    unfold E
    rw [Finset.card_filter]
  unfold a
  rw [h, Finset.card_product, hE, hE]
  push_cast
  rfl

/-- The closed form of `a n` for `n ≥ 1`. -/
def P (n : ℚ) : ℚ :=
  ((n + 1) * (n + 2) * (n + 3) * (n + 4) / 12 - 5) * ((n + 1) * (n + 2) * (n + 3) / 3 - 4)

theorem aQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = P n := by
  rw [a_eq]
  push_cast
  rw [E4Q n hn, E3Q n hn]
  rfl

theorem recurrence (n : ℕ) (hn : 9 ≤ n) : (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) +
    56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) -
      a (n - 8) := by
  rw [aQ n (by omega), aQ (n - 1) (by omega), aQ (n - 2) (by omega), aQ (n - 3) (by omega),
    aQ (n - 4) (by omega), aQ (n - 5) (by omega), aQ (n - 6) (by omega), aQ (n - 7) (by omega),
    aQ (n - 8) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
    show 8 ≤ n by omega]
  unfold P
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) =
      2 * X * (10 + 120 * X - 150 * X ^ 2 + 135 * X ^ 3 - 42 * X ^ 4 - 14 * X ^ 5 +
        14 * X ^ 6 - 3 * X ^ 7) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  have hFv : ∀ m : ℕ, F (m + 1) = P (m + 1) := by
    intro m
    simp only [hF, show ¬ (m + 1 < 1) by omega, if_false]
    rw [aQ (m + 1) (by omega)]
    push_cast
    rfl
  have key : PowerSeries.mk F * (1 - X) ^ 8 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 8 * (PowerSeries.mk F * X ^ 1) +
      C 28 * (PowerSeries.mk F * X ^ 2) - C 56 * (PowerSeries.mk F * X ^ 3) +
      C 70 * (PowerSeries.mk F * X ^ 4) - C 56 * (PowerSeries.mk F * X ^ 5) +
      C 28 * (PowerSeries.mk F * X ^ 6) - C 8 * (PowerSeries.mk F * X ^ 7) +
      C 1 * (PowerSeries.mk F * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (10 + 120 * X - 150 * X ^ 2 + 135 * X ^ 3 - 42 * X ^ 4 - 14 * X ^ 5 +
        14 * X ^ 6 - 3 * X ^ 7) : ℚ⟦X⟧) =
      C 20 * X ^ 1 + C 240 * X ^ 2 - C 300 * X ^ 3 + C 270 * X ^ 4 - C 84 * X ^ 5 -
        C 28 * X ^ 6 + C 28 * X ^ 7 - C 6 * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [hF, aQ, P]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    simp only [show 0 ≤ j + 9 by omega, show 1 ≤ j + 9 by omega, show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega, show 4 ≤ j + 9 by omega, show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega, show 7 ≤ j + 9 by omega, show 8 ≤ j + 9 by omega,
      show j + 9 - 0 = (j + 8) + 1 by omega, show j + 9 - 1 = (j + 7) + 1 by omega,
      show j + 9 - 2 = (j + 6) + 1 by omega, show j + 9 - 3 = (j + 5) + 1 by omega,
      show j + 9 - 4 = (j + 4) + 1 by omega, show j + 9 - 5 = (j + 3) + 1 by omega,
      show j + 9 - 6 = (j + 2) + 1 by omega, show j + 9 - 7 = (j + 1) + 1 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega, if_true, if_false, hFv]
    unfold P
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207402.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
