import OMAStatements.S_oeis_a188556

/-!
Proof of Barker's conjectures for A188556 (5 X n binary arrays without the pattern 0 1
horizontally, vertically, diagonally or antidiagonally).

Read the array column by column. The vertical condition only involves one column (`ColOK`), and
the horizontal, diagonal and antidiagonal conditions only involve two adjacent columns
(`PairOK`). So an array is valid iff its sequence of columns is a `Chain` (`valid_iff`), and
removing the first column (`chain_cons`) gives a transfer recursion: if `N m c` counts the ways
to continue the column `c` by `m` more columns, then `N 0 c = [ColOK c]`,
`N (m + 1) c = Sum_d [ColOK c ∧ PairOK c d] N m d`, and `a (m + 1) = Sum_c N m c` (`a_succ`).

Columns are coded by the numbers 0, ..., 31 (bit `i` of the code is the entry of row `i`). On
codes the two conditions become Boolean tests on bits (`okc`, `okt`), checked once against
`ColOK` and `PairOK` on all codes. `G` is the same recursion on codes.

The columns satisfying `ColOK` are the staircases 1^k 0^(5-k) (codes 0, 1, 3, 7, 15, 31), and a
staircase of height `k` can only be followed by the staircases of heights `k` and `k - 1`. With
`typ u = k + 1` for the staircase of height `k` and `typ u = 0` for the other codes,
`120 G m u = P (typ u) m`, where `P (k + 1) m = 120 * Sum_{d <= k} C(m, d)` is an explicit
polynomial of degree `k` in `m` and `P 0 = 0`. This is proved by induction on `m`; the step
reduces to six identities between coefficients for each code (`step_facts`, a finite check).
Summing over the 32 codes gives `120 a(m + 1) = m^5 + 35 m^3 + 120 m^2 + 444 m + 720`
(`closed`). The recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a188556 Finset

/-- A column of the array, read from top to bottom. -/
abbrev Col := Fin 5 → Bool

/-- The vertical condition inside a column. -/
def ColOK (c : Col) : Prop :=
  ∀ (i : Fin 5) (hi : i.val + 1 < 5), ¬ (c i = false ∧ c ⟨i.val + 1, hi⟩ = true)

/-- The horizontal, diagonal and antidiagonal conditions between a column `c` and the column `d`
just to its right. -/
def PairOK (c d : Col) : Prop :=
  (∀ i : Fin 5, ¬ (c i = false ∧ d i = true)) ∧
  (∀ (i : Fin 5) (hi : i.val + 1 < 5), ¬ (c i = false ∧ d ⟨i.val + 1, hi⟩ = true)) ∧
  (∀ (i : Fin 5) (hi : i.val + 1 < 5), ¬ (d i = false ∧ c ⟨i.val + 1, hi⟩ = true))

instance decColOK (c : Col) : Decidable (ColOK c) := by
  unfold ColOK
  infer_instance

instance decPairOK (c d : Col) : Decidable (PairOK c d) := by
  unfold PairOK
  infer_instance

/-- A sequence of columns, each satisfying `ColOK`, adjacent ones satisfying `PairOK`. -/
def Chain {m : ℕ} (G : Fin m → Col) : Prop :=
  (∀ j, ColOK (G j)) ∧ ∀ (j : ℕ) (hj : j + 1 < m), PairOK (G ⟨j, by omega⟩) (G ⟨j + 1, hj⟩)

theorem valid_iff {m : ℕ} (g : Grid m) : Valid g ↔ Chain (fun j i => g i j) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun j i hi => h2 i j hi, fun j hj =>
      ⟨fun i => h1 i ⟨j, by omega⟩ hj, fun i hi => h3 i ⟨j, by omega⟩ hi hj,
        fun i hi => h4 i ⟨j, by omega⟩ hi hj⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hj => (h2 j.val hj).1 i, fun i j hi => h1 j i hi,
      fun i j hi hj => (h2 j.val hj).2.1 i hi, fun i j hi hj => (h2 j.val hj).2.2 i hi⟩

theorem chain_one (G : Fin 1 → Col) : Chain G ↔ ColOK (G 0) := by
  constructor
  · intro h
    exact h.1 0
  · intro h
    refine ⟨fun j => ?_, fun j hj => absurd hj (by omega)⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact h

theorem chain_cons {m : ℕ} (c : Col) (G : Fin (m + 1) → Col) :
    Chain (Fin.cons c G : Fin (m + 2) → Col) ↔
      ColOK c ∧ PairOK c (G ⟨0, by omega⟩) ∧ Chain G := by
  constructor
  · rintro ⟨h1, h2⟩
    have hc := h1 0
    have hp := h2 0 (by omega)
    exact ⟨hc, hp, fun j => h1 j.succ, fun j hj => h2 (j + 1) (by omega)⟩
  · rintro ⟨hc, hp, h1, h2⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · rcases j with ⟨_ | j, hj⟩
      · exact hc
      · exact h1 ⟨j, by omega⟩
    · cases j with
      | zero => exact hp
      | succ j => exact h2 j (by omega)

/-- The number of ways to continue the column `c` by `m` more columns into a `Chain`. -/
noncomputable def N (m : ℕ) (c : Col) : ℕ := by
  classical
  exact ∑ G : Fin m → Col, if Chain (Fin.cons c G : Fin (m + 1) → Col) then 1 else 0

theorem N_zero (c : Col) : N 0 c = if ColOK c then 1 else 0 := by
  classical
  unfold N
  rw [Fintype.sum_unique]
  exact if_congr (chain_one _) rfl rfl

theorem N_succ (m : ℕ) (c : Col) :
    N (m + 1) c = ∑ d : Col, if ColOK c ∧ PairOK c d then N m d else 0 := by
  classical
  unfold N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col).symm _
    (fun p => if Chain (Fin.cons c (Fin.cons p.1 p.2) : Fin (m + 2) → Col) then 1 else 0)
    (fun G => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hv : ColOK c ∧ PairOK c d
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun G _ => if_congr ?_ rfl rfl
    rw [chain_cons]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun G _ => if_neg ?_
    rw [chain_cons]
    exact fun h => hv ⟨h.1, h.2.1⟩

theorem a_succ (m : ℕ) : a (m + 1) = ∑ c : Col, (N m c : ℤ) := by
  classical
  have h1 : (Finset.univ.filter (fun g : Grid (m + 1) => Valid g)).card =
      ∑ G : Fin (m + 1) → Col, if Chain G then 1 else 0 := by
    rw [Finset.card_filter]
    exact Fintype.sum_equiv (Equiv.piComm fun (_ : Fin 5) (_ : Fin (m + 1)) => Bool) _ _
      (fun g => if_congr (valid_iff g) rfl rfl)
  have h2 : (∑ G : Fin (m + 1) → Col, if Chain G then 1 else 0) = ∑ c : Col, N m c := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col).symm _
      (fun p => if Chain (Fin.cons p.1 p.2 : Fin (m + 1) → Col) then 1 else 0)
      (fun G => by simp), Fintype.sum_prod_type]
    rfl
  rw [a, h1, h2]
  push_cast
  rfl

/-- The column with code `u`: the entry of row `i` is bit `i` of `u`. -/
def col (u : Fin 32) : Col := fun i => Nat.testBit u.val i.val

theorem col_injective : Function.Injective col := by
  decide +kernel

theorem col_bijective : Function.Bijective col := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨col_injective, by simp⟩

/-- `ColOK` on codes. -/
def okc (u : Fin 32) : Bool := (u.val >>> 1) &&& u.val == u.val >>> 1

/-- `ColOK (col u) ∧ PairOK (col u) (col v)` on codes. -/
def okt (u v : Fin 32) : Bool :=
  okc u && (v.val &&& u.val == v.val) && ((v.val >>> 1) &&& u.val == v.val >>> 1) &&
    ((u.val >>> 1) &&& v.val == u.val >>> 1)

theorem okc_iff : ∀ u : Fin 32, ColOK (col u) ↔ okc u = true := by
  decide +kernel

theorem okt_iff : ∀ u v : Fin 32, (ColOK (col u) ∧ PairOK (col u) (col v)) ↔ okt u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 32 → ℕ
  | 0, u => if okc u then 1 else 0
  | m + 1, u => ∑ v : Fin 32, if okt u v then G m v else 0

theorem N_eq_G (m : ℕ) : ∀ u : Fin 32, N m (col u) = G m u := by
  induction m with
  | zero =>
    intro u
    rw [N_zero]
    simp only [G]
    exact if_congr (okc_iff u) rfl rfl
  | succ m ih =>
    intro u
    rw [N_succ, ← col_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (okt_iff u v) rfl rfl

/-- The type of a code: `k + 1` for the staircase column `1^k 0^(5-k)` (code `2^k - 1`), and `0`
for every other column. -/
def typ (u : Fin 32) : ℕ :=
  if u.val = 0 then 1 else if u.val = 1 then 2 else if u.val = 3 then 3 else
  if u.val = 7 then 4 else if u.val = 15 then 5 else if u.val = 31 then 6 else 0

/-- Coefficient of `m ^ 5` in `P t m`. -/
def c5 (t : ℕ) : ℤ := if t = 6 then 1 else 0

/-- Coefficient of `m ^ 4` in `P t m`. -/
def c4 (t : ℕ) : ℤ := if t = 5 then 5 else if t = 6 then -5 else 0

/-- Coefficient of `m ^ 3` in `P t m`. -/
def c3 (t : ℕ) : ℤ := if t = 4 then 20 else if t = 5 then -10 else if t = 6 then 25 else 0

/-- Coefficient of `m ^ 2` in `P t m`. -/
def c2 (t : ℕ) : ℤ := if t = 3 then 60 else if t = 5 then 55 else if t = 6 then 5 else 0

/-- Coefficient of `m` in `P t m`. -/
def c1 (t : ℕ) : ℤ :=
  if t = 2 then 120 else if t = 3 then 60 else if t = 4 then 100 else if t = 5 then 70 else
  if t = 6 then 94 else 0

/-- Constant coefficient of `P t m`. -/
def c0 (t : ℕ) : ℤ := if t = 0 then 0 else 120

/-- `120` times the number of continuations by `m` columns of a column of type `t`: for
`t = k + 1`, `P t m = 120 * Sum_{d <= k} C(m, d)`. -/
def P (t : ℕ) (m : ℤ) : ℤ :=
  c5 t * m ^ 5 + c4 t * m ^ 4 + c3 t * m ^ 3 + c2 t * m ^ 2 + c1 t * m + c0 t

theorem base_facts : ∀ u : Fin 32, 120 * (G 0 u : ℤ) = c0 (typ u) := by
  decide +kernel

/-- The induction step of `G_closed`, coefficient by coefficient. -/
theorem step_facts : ∀ u : Fin 32,
    (∑ v : Fin 32, if okt u v then c5 (typ v) else 0) = c5 (typ u) ∧
    (∑ v : Fin 32, if okt u v then c4 (typ v) else 0) = 5 * c5 (typ u) + c4 (typ u) ∧
    (∑ v : Fin 32, if okt u v then c3 (typ v) else 0) =
      10 * c5 (typ u) + 4 * c4 (typ u) + c3 (typ u) ∧
    (∑ v : Fin 32, if okt u v then c2 (typ v) else 0) =
      10 * c5 (typ u) + 6 * c4 (typ u) + 3 * c3 (typ u) + c2 (typ u) ∧
    (∑ v : Fin 32, if okt u v then c1 (typ v) else 0) =
      5 * c5 (typ u) + 4 * c4 (typ u) + 3 * c3 (typ u) + 2 * c2 (typ u) + c1 (typ u) ∧
    (∑ v : Fin 32, if okt u v then c0 (typ v) else 0) =
      c5 (typ u) + c4 (typ u) + c3 (typ u) + c2 (typ u) + c1 (typ u) + c0 (typ u) := by
  decide +kernel

theorem G_closed (m : ℕ) : ∀ u : Fin 32, 120 * (G m u : ℤ) = P (typ u) m := by
  induction m with
  | zero =>
    intro u
    rw [base_facts u]
    simp [P]
  | succ m ih =>
    intro u
    have hsum : 120 * (G (m + 1) u : ℤ) =
        ∑ v : Fin 32, if okt u v then P (typ v) m else 0 := by
      rw [G]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih v
      · simp
    rw [hsum]
    have hP : ∀ v : Fin 32, (if okt u v then P (typ v) m else 0) =
        (if okt u v then c5 (typ v) else 0) * (m : ℤ) ^ 5 +
        (if okt u v then c4 (typ v) else 0) * (m : ℤ) ^ 4 +
        (if okt u v then c3 (typ v) else 0) * (m : ℤ) ^ 3 +
        (if okt u v then c2 (typ v) else 0) * (m : ℤ) ^ 2 +
        (if okt u v then c1 (typ v) else 0) * (m : ℤ) +
        (if okt u v then c0 (typ v) else 0) := by
      intro v
      split_ifs <;> simp [P]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h5, h4, h3, h2, h1, h0⟩ := step_facts u
    rw [h5, h4, h3, h2, h1, h0]
    unfold P
    push_cast
    ring

theorem sum_facts :
    (∑ u : Fin 32, c5 (typ u)) = 1 ∧ (∑ u : Fin 32, c4 (typ u)) = 0 ∧
    (∑ u : Fin 32, c3 (typ u)) = 35 ∧ (∑ u : Fin 32, c2 (typ u)) = 120 ∧
    (∑ u : Fin 32, c1 (typ u)) = 444 ∧ (∑ u : Fin 32, c0 (typ u)) = 720 := by
  decide +kernel

theorem closed (m : ℕ) :
    120 * a (m + 1) = (m : ℤ) ^ 5 + 35 * m ^ 3 + 120 * m ^ 2 + 444 * m + 720 := by
  have h : a (m + 1) = ∑ u : Fin 32, (G m u : ℤ) := by
    rw [a_succ, ← col_bijective.sum_comp]
    exact Finset.sum_congr rfl fun u _ => by rw [N_eq_G]
  rw [h, Finset.mul_sum]
  simp only [G_closed m]
  simp only [P, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h5, h4, h3, h2, h1, h0⟩ := sum_facts
  rw [h5, h4, h3, h2, h1, h0]
  ring

/-- `120 a(n)` as a polynomial in `n`, for every `n ≥ 1`. -/
theorem closed_n (n : ℕ) (hn : 1 ≤ n) :
    120 * a n = (n : ℤ) ^ 5 - 5 * n ^ 4 + 45 * n ^ 3 + 5 * n ^ 2 + 314 * n + 360 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [closed m]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  have h0 := closed_n n (by omega)
  have h1 := closed_n (n - 1) (by omega)
  have h2 := closed_n (n - 2) (by omega)
  have h3 := closed_n (n - 3) (by omega)
  have h4 := closed_n (n - 4) (by omega)
  have h5 := closed_n (n - 5) (by omega)
  have h6 := closed_n (n - 6) (by omega)
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega] at h1 h2 h3 h4 h5 h6
  linarith

theorem a_vals :
    a 0 = 0 ∧ a 1 = 6 ∧ a 2 = 11 ∧ a 3 = 20 ∧ a 4 = 36 ∧ a 5 = 64 ∧ a 6 = 112 := by
  have h1 := closed 0
  have h2 := closed 1
  have h3 := closed 2
  have h4 := closed 3
  have h5 := closed 4
  have h6 := closed 5
  norm_num at h1 h2 h3 h4 h5 h6
  exact ⟨rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk a * (1 - X) ^ 6 =
      X * (6 - 25 * X + 44 * X ^ 2 - 39 * X ^ 3 + 18 * X ^ 4 - 3 * X ^ 5) := by
  have key : PowerSeries.mk a * (1 - X) ^ 6 =
      C 1 * (PowerSeries.mk a * X ^ 0) - C 6 * (PowerSeries.mk a * X ^ 1) +
        C 15 * (PowerSeries.mk a * X ^ 2) - C 20 * (PowerSeries.mk a * X ^ 3) +
        C 15 * (PowerSeries.mk a * X ^ 4) - C 6 * (PowerSeries.mk a * X ^ 5) +
        C 1 * (PowerSeries.mk a * X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (6 - 25 * X + 44 * X ^ 2 - 39 * X ^ 3 + 18 * X ^ 4 - 3 * X ^ 5) =
      C 6 * X ^ 1 - C 25 * X ^ 2 + C 44 * X ^ 3 - C 39 * X ^ 4 + C 18 * X ^ 5 -
        C 3 * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := a_vals
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [v0, v1, v2, v3, v4, v5, v6]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    have hr := recurrence (j + 7) (by omega)
    simp only [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      if_true, if_false]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a188556.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
