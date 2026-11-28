import OMAStatements.S_oeis_a202330

/-!
Proof of Barker's conjectures for A202330 ((n+1) X 4 binary arrays whose consecutive windows of
two bits, read as binary numbers, are nondecreasing in every row and column).

With `win p q = 2p + q`, the column condition `win p q ≤ win q r` on three consecutive entries
`p, q, r` of a column only involves three consecutive rows. So an array is good iff its first two
rows are good and every three consecutive rows `x, y, z` satisfy `V x y z`: the row `z` is good
and the column condition holds between `x, y, z` in each column (`good_cons_iff`). Removing the
first row (`chain_cons`) gives a transfer recursion: if `T m x y` counts the ways to continue the
rows `x, y` by `m` more rows, then `T 0 x y = 1`, `T (m + 1) x y = Sum_{z with V x y z} T m y z`,
and `a (m + 1) = Sum_{x, y good} T m x y` (`a_eq`).

Only six rows are good: 0000, 0001, 0010, 0011, 0111, 1111 (`rowOK_iff`), coded 0, ..., 5 by
`vrow`, so the sums over good rows become sums over `Fin 6` (`sum_rows`). On codes, the column
condition is a Boolean test `Ct`, and `G` is the transfer recursion on codes (`T_eq_G`, `a_eq_G`).

Group the 36 pairs of codes `(u, v)` of two consecutive rows into types (`typ`): type 0 for the
pairs with no continuation (u ≠ 0, u ≠ v, and not both u < v and v ≥ 3); otherwise the type is
1, 2, 2, 3, 4, 5 according as v = 0, 1, 2, 3, 4, 5. For `n ≥ 2`, 24 times the number of
continuations by `n` rows of a pair of type `t` is `P t n`, where
  `P 1 n = 2 n^4 + 24 n^3 + 82 n^2 + 108 n + 96`, `P 2 n = 4 n^3 + 36 n^2 + 80 n + 48`,
  `P 3 n = 12 n^2 + 60 n + 48`, `P 4 n = 24 n + 48`, `P 5 n = 24`, `P 0 n = 0`.
This is proved by induction from `n = 2` (a finite check, `base_facts`); the induction step is a
finite check of five identities between coefficients for each pair (`step_facts`). Summing over
the 36 pairs gives `24 a(m + 1) = 2 m^4 + 40 m^3 + 274 m^2 + 788 m + 864` for `m ≥ 2`, that is
`12 a(n) = n^4 + 16 n^3 + 83 n^2 + 176 n + 156` for `n ≥ 3`, and also for `n = 1, 2` since
`a 1 = 36` and `a 2 = 82`. The recurrence and the generating function follow by comparing
coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a202330 Finset

/-- A row of the array. -/
abbrev Row := Fin 4 → Bool

/-- The window condition of a row of length 4, written out. -/
theorem windowsMono_four (v : Row) :
    WindowsMono v ↔ win (v 0) (v 1) ≤ win (v 1) (v 2) ∧ win (v 1) (v 2) ≤ win (v 2) (v 3) := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ i hi
    have hi2 : i < 2 := by omega
    interval_cases i
    · exact h0
    · exact h1

instance decRowOK (v : Row) : Decidable (WindowsMono v) :=
  decidable_of_iff _ (windowsMono_four v).symm

/-- The column condition on three consecutive rows `x, y, z`. -/
def ColOK (x y z : Row) : Prop := ∀ j : Fin 4, win (x j) (y j) ≤ win (y j) (z j)

instance decColOK (x y z : Row) : Decidable (ColOK x y z) := by
  unfold ColOK
  infer_instance

/-- The conditions brought by a new row `z` below the rows `x, y`. -/
def V (x y z : Row) : Prop := WindowsMono z ∧ ColOK x y z

instance decV (x y z : Row) : Decidable (V x y z) := by
  unfold V
  infer_instance

/-- Every three consecutive rows of `A` satisfy `V`. -/
def Chain {m : ℕ} (A : Fin m → Row) : Prop :=
  ∀ (i : ℕ) (h : i + 2 < m), V (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem good_cons_iff {m : ℕ} (x y : Row) (B : Fin m → Row) :
    Good (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) ↔
      WindowsMono x ∧ WindowsMono y ∧ Chain (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) := by
  constructor
  · rintro ⟨hr, hc⟩
    refine ⟨by simpa using hr 0, by simpa using hr 1, fun i hi => ⟨hr _, fun j => hc j i hi⟩⟩
  · rintro ⟨hx, hy, hch⟩
    refine ⟨fun r => ?_, fun j i hi => (hch i hi).2 j⟩
    rcases r with ⟨_ | _ | k, hk⟩
    · exact hx
    · exact hy
    · exact (hch k (by omega)).1

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

/-- The number of ways to continue the rows `x, y` by `m` more rows so that every three
consecutive rows satisfy `V`. -/
noncomputable def T (m : ℕ) (x y : Row) : ℕ := by
  classical
  exact ∑ B : Fin m → Row,
    if Chain (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) then 1 else 0

theorem T_zero (x y : Row) : T 0 x y = 1 := by
  classical
  unfold T
  rw [Fintype.sum_unique, if_pos]
  intro i hi
  omega

theorem T_succ (m : ℕ) (x y : Row) :
    T (m + 1) x y = ∑ z : Row, if V x y z then T m y z else 0 := by
  classical
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : V x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chain_cons]
    exact and_iff_right hv
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chain_cons]
    exact fun h => hv h.1

theorem a_eq (m : ℕ) :
    a (m + 1) = ∑ x : Row, ∑ y : Row, if WindowsMono x ∧ WindowsMono y then T m x y else 0 := by
  classical
  have h1 : a (m + 1) = ∑ A : Fin (m + 2) → Row, if Good A then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good (Fin.cons p.1 p.2 : Fin (m + 2) → Row) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good (Fin.cons x (Fin.cons p.1 p.2) : Fin (m + 2) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : WindowsMono x ∧ WindowsMono y
  · rw [if_pos hxy]
    unfold T
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons_iff]
    exact ⟨fun h => h.2.2, fun h => ⟨hxy.1, hxy.2, h⟩⟩
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons_iff]
    exact fun h => hxy ⟨h.1, h.2.1⟩

/-- The six rows whose windows are nondecreasing: 0000, 0001, 0010, 0011, 0111, 1111. -/
def vrow : Fin 6 → Row :=
  ![![false, false, false, false], ![false, false, false, true], ![false, false, true, false],
    ![false, false, true, true], ![false, true, true, true], ![true, true, true, true]]

theorem vrow_injective : Function.Injective vrow := by
  decide

theorem rowOK_iff : ∀ z : Row, WindowsMono z ↔ ∃ k, vrow k = z := by
  intro z
  rw [windowsMono_four]
  revert z
  decide

theorem sum_rows {M : Type*} [AddCommMonoid M] (g : Row → M) :
    ∑ z : Row, (if WindowsMono z then g z else 0) = ∑ k : Fin 6, g (vrow k) := by
  symm
  refine Fintype.sum_of_injective vrow vrow_injective _ _ (fun z hz => ?_) (fun k => ?_)
  · rw [if_neg]
    rw [rowOK_iff]
    exact hz
  · rw [if_pos ((rowOK_iff _).2 ⟨k, rfl⟩)]

/-- The column test on codes of valid rows. -/
def Ct (u v w : Fin 6) : Bool := decide (ColOK (vrow u) (vrow v) (vrow w))

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 6 → Fin 6 → ℕ
  | 0, _, _ => 1
  | m + 1, u, v => ∑ w : Fin 6, if Ct u v w then G m v w else 0

theorem T_eq_G (m : ℕ) : ∀ u v : Fin 6, T m (vrow u) (vrow v) = G m u v := by
  induction m with
  | zero => intro u v; rw [T_zero]; rfl
  | succ m ih =>
    intro u v
    rw [T_succ]
    simp only [V, ite_and]
    rw [sum_rows]
    simp only [G]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    exact if_congr (by simp [Ct]) rfl rfl

theorem a_eq_G (m : ℕ) : a (m + 1) = ∑ u : Fin 6, ∑ v : Fin 6, G m u v := by
  rw [a_eq]
  simp only [ite_and]
  have : ∀ x : Row, (∑ y : Row, if WindowsMono x then (if WindowsMono y then T m x y else 0)
      else 0) = if WindowsMono x then ∑ y : Row, (if WindowsMono y then T m x y else 0) else 0 := by
    intro x
    split_ifs <;> simp
  simp only [this]
  rw [sum_rows]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sum_rows]
  exact Finset.sum_congr rfl fun v _ => T_eq_G m u v

/-- The type of the pair of codes `(u, v)` of two consecutive rows: 0 if the pair has no
continuation, otherwise 1, 2, 2, 3, 4, 5 according as `v` is 0, 1, 2, 3, 4, 5. A pair has a
continuation iff `u` is 0, or `u = v`, or `u < v` and `v ≥ 3`. -/
def typ (u v : Fin 6) : ℕ :=
  if u.val = 0 ∨ u.val = v.val ∨ (3 ≤ v.val ∧ u.val < v.val) then
    (if v.val = 0 then 1 else if v.val ≤ 2 then 2 else v.val)
  else 0

/-- Coefficient of `n ^ 4` in `P t n`. -/
def c4 (t : ℕ) : ℤ := if t = 1 then 2 else 0

/-- Coefficient of `n ^ 3` in `P t n`. -/
def c3 (t : ℕ) : ℤ := if t = 1 then 24 else if t = 2 then 4 else 0

/-- Coefficient of `n ^ 2` in `P t n`. -/
def c2 (t : ℕ) : ℤ := if t = 1 then 82 else if t = 2 then 36 else if t = 3 then 12 else 0

/-- Coefficient of `n` in `P t n`. -/
def c1 (t : ℕ) : ℤ :=
  if t = 1 then 108 else if t = 2 then 80 else if t = 3 then 60 else if t = 4 then 24 else 0

/-- Constant coefficient of `P t n`. -/
def c0 (t : ℕ) : ℤ :=
  if t = 1 then 96 else if t = 2 then 48 else if t = 3 then 48 else if t = 4 then 48
  else if t = 5 then 24 else 0

/-- 24 times the number of continuations by `n ≥ 2` rows of a pair of type `t`. -/
def P (t : ℕ) (n : ℤ) : ℤ := c4 t * n ^ 4 + c3 t * n ^ 3 + c2 t * n ^ 2 + c1 t * n + c0 t

/-- The induction step of `G_closed`, coefficient by coefficient. -/
theorem step_facts : ∀ u v : Fin 6,
    (∑ w : Fin 6, if Ct u v w then c4 (typ v w) else 0) = c4 (typ u v) ∧
    (∑ w : Fin 6, if Ct u v w then c3 (typ v w) else 0) = 4 * c4 (typ u v) + c3 (typ u v) ∧
    (∑ w : Fin 6, if Ct u v w then c2 (typ v w) else 0) =
      6 * c4 (typ u v) + 3 * c3 (typ u v) + c2 (typ u v) ∧
    (∑ w : Fin 6, if Ct u v w then c1 (typ v w) else 0) =
      4 * c4 (typ u v) + 3 * c3 (typ u v) + 2 * c2 (typ u v) + c1 (typ u v) ∧
    (∑ w : Fin 6, if Ct u v w then c0 (typ v w) else 0) =
      c4 (typ u v) + c3 (typ u v) + c2 (typ u v) + c1 (typ u v) + c0 (typ u v) := by
  decide +kernel

theorem base_facts : ∀ u v : Fin 6, 24 * (G 2 u v : ℤ) = P (typ u v) 2 := by
  decide +kernel

theorem G_closed (n : ℕ) (hn : 2 ≤ n) :
    ∀ u v : Fin 6, 24 * (G n u v : ℤ) = P (typ u v) n := by
  induction n, hn using Nat.le_induction with
  | base => exact base_facts
  | succ n hn ih =>
    intro u v
    have hsum : 24 * (G (n + 1) u v : ℤ) =
        ∑ w : Fin 6, if Ct u v w then P (typ v w) n else 0 := by
      rw [G]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs
      · exact ih v w
      · simp
    rw [hsum]
    have hP : ∀ w : Fin 6, (if Ct u v w then P (typ v w) n else 0) =
        (if Ct u v w then c4 (typ v w) else 0) * (n : ℤ) ^ 4 +
        (if Ct u v w then c3 (typ v w) else 0) * (n : ℤ) ^ 3 +
        (if Ct u v w then c2 (typ v w) else 0) * (n : ℤ) ^ 2 +
        (if Ct u v w then c1 (typ v w) else 0) * (n : ℤ) +
        (if Ct u v w then c0 (typ v w) else 0) := by
      intro w
      split_ifs <;> simp [P]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h4, h3, h2, h1, h0⟩ := step_facts u v
    rw [h4, h3, h2, h1, h0]
    unfold P
    push_cast
    ring

theorem sum_facts :
    (∑ u : Fin 6, ∑ v : Fin 6, c4 (typ u v)) = 2 ∧
    (∑ u : Fin 6, ∑ v : Fin 6, c3 (typ u v)) = 40 ∧
    (∑ u : Fin 6, ∑ v : Fin 6, c2 (typ u v)) = 274 ∧
    (∑ u : Fin 6, ∑ v : Fin 6, c1 (typ u v)) = 788 ∧
    (∑ u : Fin 6, ∑ v : Fin 6, c0 (typ u v)) = 864 := by
  decide +kernel

theorem a_one : a 1 = 36 := by
  rw [a_eq_G 0]
  decide +kernel

theorem a_two : a 2 = 82 := by
  rw [a_eq_G 1]
  decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    12 * (a n : ℤ) = (n : ℤ) ^ 4 + 16 * n ^ 3 + 83 * n ^ 2 + 176 * n + 156 := by
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h
  · rw [a_one]
    norm_num
  · rw [a_two]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 2 ≤ m := by omega
    have key : 24 * (a (m + 1) : ℤ) = ∑ u : Fin 6, ∑ v : Fin 6, P (typ u v) m := by
      rw [a_eq_G]
      push_cast
      simp only [Finset.mul_sum, G_closed m hm]
    have hs : ∑ u : Fin 6, ∑ v : Fin 6, P (typ u v) (m : ℤ) =
        2 * (m : ℤ) ^ 4 + 40 * m ^ 3 + 274 * m ^ 2 + 788 * m + 864 := by
      simp only [P, Finset.sum_add_distrib, ← Finset.sum_mul]
      obtain ⟨h4, h3, h2, h1, h0⟩ := sum_facts
      rw [h4, h3, h2, h1, h0]
    have h2 : 2 * (12 * (a (m + 1) : ℤ)) =
        2 * (((m + 1 : ℕ) : ℤ) ^ 4 + 16 * ((m + 1 : ℕ) : ℤ) ^ 3 + 83 * ((m + 1 : ℕ) : ℤ) ^ 2 +
          176 * ((m + 1 : ℕ) : ℤ) + 156) := by
      rw [← mul_assoc, show (2 : ℤ) * 12 = 24 by norm_num, key, hs]
      push_cast
      ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = ((n : ℚ) ^ 4 + 16 * n ^ 3 + 83 * n ^ 2 + 176 * n + 156) / 12 := by
  have h : ((12 * (a n : ℤ) : ℤ) : ℚ) =
      (((n : ℤ) ^ 4 + 16 * n ^ 3 + 83 * n ^ 2 + 176 * n + 156 : ℤ) : ℚ) := by
    rw [closed n hn]
  push_cast at h
  linarith

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have hQ : (a n : ℚ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4)
      + a (n - 5) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega]
    rw [closedQ (k + 6) (by omega), closedQ (k + 5) (by omega), closedQ (k + 4) (by omega),
      closedQ (k + 3) (by omega), closedQ (k + 2) (by omega), closedQ (k + 1) (by omega)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 : PowerSeries ℚ) =
      X * (36 - 98 * X + 112 * X ^ 2 - 61 * X ^ 3 + 13 * X ^ 4) := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) with hA
  have key : A * (1 - X) ^ 5 =
      A * X ^ 0 - C (5 : ℚ) * (A * X ^ 1) + C (10 : ℚ) * (A * X ^ 2) - C (10 : ℚ) * (A * X ^ 3) +
        C (5 : ℚ) * (A * X ^ 4) - A * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℚ) * (36 - 98 * X + 112 * X ^ 2 - 61 * X ^ 3 + 13 * X ^ 4) =
      C (36 : ℚ) * X ^ 1 - C (98 : ℚ) * X ^ 2 + C (112 : ℚ) * X ^ 3 - C (61 : ℚ) * X ^ 4 +
        C (13 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 < 1) by omega, show ¬ (j + 5 < 1) by omega, show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false]
    rw [closedQ (j + 6) (by omega), closedQ (j + 5) (by omega), closedQ (j + 4) (by omega),
      closedQ (j + 3) (by omega), closedQ (j + 2) (by omega), closedQ (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a202330.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
