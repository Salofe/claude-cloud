import OMAStatements.S_oeis_a207846
import Mathlib

/-!
Read the array column by column. A row avoids `0 0 0` and `0 0 1` exactly when it has no `0 0`
starting before the last two positions, and a column of height 3 avoids `0 0 0` and `1 1 1`
exactly when it is not constant. So an array is a sequence of non-constant columns in which
every column except the last two has no row with `0` in it and in the next column (`Chain`).
Removing the first column gives a transfer recursion `N` (`N_zero`, `N_one`, `N_two`), which on
3-bit column codes is `G`. The two kinds of good columns (one `1`, two `1`s) satisfy
`G (k + 3) = 2 G (k + 2) + G (k + 1)` code by code (a finite check at `k = 0` and an induction),
so `a (k + 4) = 2 a (k + 3) + a (k + 2)`, with `a 1 = 6`, `a 2 = 36`, `a 3 = 72`. The generating
function follows by comparing coefficients, and the closed form by induction, since
`1 - sqrt 2` and `1 + sqrt 2` are the roots of `x ^ 2 = 2 x + 1`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207846 Finset

/-- A column of the array, read from top to bottom. -/
abbrev Col := Fin 3 → Bool

/-- The vertical condition on a column. -/
def ColOK (c : Col) : Prop := (c 0, c 1, c 2) ∉ [(false, false, false), (true, true, true)]

instance decColOK (c : Col) : Decidable (ColOK c) := by
  unfold ColOK
  infer_instance

/-- The horizontal condition between a column and the next one (no row reads `0 0`). -/
def Compat (c d : Col) : Prop := ∀ i : Fin 3, ¬ (c i = false ∧ d i = false)

instance decCompat (c d : Col) : Decidable (Compat c d) := by
  unfold Compat
  infer_instance

/-- Columns are good, and each column except the last two is compatible with the next one. -/
def Chain {m : ℕ} (T : Fin m → Col) : Prop :=
  (∀ j, ColOK (T j)) ∧
    ∀ (j : ℕ) (h : j + 2 < m), Compat (T ⟨j, by omega⟩) (T ⟨j + 1, by omega⟩)

theorem row_avoid (x y z : Bool) :
    Avoids [(false, false, false), (false, false, true)] x y z ↔ ¬ (x = false ∧ y = false) := by
  unfold Avoids
  cases x <;> cases y <;> cases z <;> decide

theorem counted_iff (n : ℕ) (A : Fin 3 → Fin n → Bool) :
    IsCounted n A ↔ Chain (fun j i => A i j) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => h2 0 (by norm_num) j, fun j h i => (row_avoid _ _ _).1 (h1 i j h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j h => (row_avoid _ _ _).2 (h2 j h i), fun i h j => ?_⟩
    obtain rfl : i = 0 := by omega
    exact h1 j

theorem chain_cons0 (c : Col) (T : Fin 0 → Col) :
    Chain (Fin.cons c T : Fin 1 → Col) ↔ ColOK c := by
  constructor
  · intro h
    exact h.1 0
  · intro h
    refine ⟨fun j => ?_, fun j hj => absurd hj (by omega)⟩
    rw [Fin.fin_one_eq_zero j]
    exact h

theorem chain_cons1 (c : Col) (T : Fin 1 → Col) :
    Chain (Fin.cons c T : Fin 2 → Col) ↔ ColOK c ∧ ColOK (T 0) := by
  constructor
  · intro h
    exact ⟨h.1 0, h.1 1⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun j => ?_, fun j hj => absurd hj (by omega)⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · exact h0
    · rw [Fin.cons_succ, Fin.fin_one_eq_zero i]
      exact h1

theorem chain_cons2 {m : ℕ} (c : Col) (T : Fin (m + 2) → Col) :
    Chain (Fin.cons c T : Fin (m + 3) → Col) ↔
      ColOK c ∧ Compat c (T ⟨0, by omega⟩) ∧ Chain T := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 0, by simpa using h2 0 (by omega), fun j => by simpa using h1 j.succ,
      fun j hj => h2 (j + 1) (by omega)⟩
  · rintro ⟨h0, hc, h1, h2⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · exact h0
      · rw [Fin.cons_succ]
        exact h1 i
    · cases j with
      | zero => exact hc
      | succ j => exact h2 j (by omega)

/-- The number of ways to continue the column `c` by `m` more columns into a `Chain`. -/
noncomputable def N (m : ℕ) (c : Col) : ℕ := by
  classical
  exact ∑ T : Fin m → Col, if Chain (Fin.cons c T : Fin (m + 1) → Col) then 1 else 0

theorem N_zero (c : Col) : N 0 c = if ColOK c then 1 else 0 := by
  classical
  unfold N
  rw [Fintype.sum_unique]
  exact if_congr (chain_cons0 _ _) rfl rfl

theorem N_one (c : Col) :
    N 1 c = if ColOK c then ∑ d : Col, (if ColOK d then 1 else 0) else 0 := by
  classical
  unfold N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col).symm _
    (fun p => if Chain (Fin.cons c (Fin.cons p.1 p.2) : Fin 2 → Col) then 1 else 0)
    (fun T => by simp), Fintype.sum_prod_type]
  by_cases hc : ColOK c
  · rw [if_pos hc]
    refine sum_congr rfl fun d _ => ?_
    rw [Fintype.sum_unique]
    exact if_congr ((chain_cons1 _ _).trans (by simp [hc])) rfl rfl
  · rw [if_neg hc]
    refine sum_eq_zero fun d _ => sum_eq_zero fun T _ => if_neg ?_
    rw [chain_cons1]
    exact fun h => hc h.1

theorem N_two (m : ℕ) (c : Col) :
    N (m + 2) c = if ColOK c then ∑ d : Col, (if Compat c d then N (m + 1) d else 0) else 0 := by
  classical
  unfold N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col).symm _
    (fun p => if Chain (Fin.cons c (Fin.cons p.1 p.2) : Fin (m + 3) → Col) then 1 else 0)
    (fun T => by simp), Fintype.sum_prod_type]
  by_cases hc : ColOK c
  · rw [if_pos hc]
    refine sum_congr rfl fun d _ => ?_
    by_cases hd : Compat c d
    · rw [if_pos hd]
      refine sum_congr rfl fun T _ => if_congr ?_ rfl rfl
      rw [chain_cons2]
      simp [hc, hd]
    · rw [if_neg hd]
      refine sum_eq_zero fun T _ => if_neg ?_
      rw [chain_cons2]
      exact fun h => hd (by simpa using h.2.1)
  · rw [if_neg hc]
    refine sum_eq_zero fun d _ => sum_eq_zero fun T _ => if_neg ?_
    rw [chain_cons2]
    exact fun h => hc h.1

theorem a_succ (m : ℕ) : a (m + 1) = ∑ c : Col, N m c := by
  classical
  have e := Nat.card_congr (Equiv.subtypeEquiv (Equiv.piComm fun (_ : Fin 3) (_ : Fin (m + 1)) => Bool)
    (fun A => counted_iff (m + 1) A))
  rw [a, e, Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter]
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col).symm _
    (fun p => if Chain (Fin.cons p.1 p.2 : Fin (m + 1) → Col) then 1 else 0)
    (fun T => by simp), Fintype.sum_prod_type]
  rfl

/-- The column with code `u`: the entry of row `i` is bit `i` of `u`. -/
def col (u : Fin 8) : Col := fun i => Nat.testBit u.val i.val

theorem col_injective : Function.Injective col := by
  decide +kernel

theorem col_bijective : Function.Bijective col := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨col_injective, by simp⟩

def okc (u : Fin 8) : Bool := u.val != 0 && u.val != 7

def ok (u v : Fin 8) : Bool := (u.val ||| v.val) == 7

theorem okc_iff : ∀ u : Fin 8, ColOK (col u) ↔ okc u = true := by
  decide +kernel

theorem ok_iff : ∀ u v : Fin 8, Compat (col u) (col v) ↔ ok u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 8 → ℕ
  | 0, u => if okc u then 1 else 0
  | 1, u => if okc u then 6 else 0
  | m + 2, u => if okc u then ∑ v : Fin 8, (if ok u v then G (m + 1) v else 0) else 0

theorem sum_okc : (∑ v : Fin 8, if okc v then 1 else 0) = 6 := by
  decide +kernel

theorem N_eq_G : ∀ (m : ℕ) (u : Fin 8), N m (col u) = G m u
  | 0, u => by
    rw [N_zero]
    exact if_congr (okc_iff u) rfl rfl
  | 1, u => by
    rw [N_one, ← col_bijective.sum_comp]
    simp only [G]
    refine if_congr (okc_iff u) ?_ rfl
    rw [← sum_okc]
    exact sum_congr rfl fun v _ => if_congr (okc_iff v) rfl rfl
  | m + 2, u => by
    rw [N_two, ← col_bijective.sum_comp]
    simp only [G]
    refine if_congr (okc_iff u) (sum_congr rfl fun v _ => ?_) rfl
    rw [N_eq_G (m + 1) v]
    exact if_congr (ok_iff u v) rfl rfl

theorem a_eq_G (m : ℕ) : a (m + 1) = ∑ u : Fin 8, G m u := by
  rw [a_succ, ← col_bijective.sum_comp]
  exact sum_congr rfl fun u _ => N_eq_G m u

theorem G_base : ∀ u : Fin 8, G 3 u = 2 * G 2 u + G 1 u := by
  decide +kernel

theorem G_rec : ∀ (k : ℕ) (u : Fin 8), G (k + 3) u = 2 * G (k + 2) u + G (k + 1) u
  | 0, u => G_base u
  | k + 1, u => by
    have ih := G_rec k
    show (if okc u then ∑ v : Fin 8, (if ok u v then G (k + 3) v else 0) else 0) =
      2 * (if okc u then ∑ v : Fin 8, (if ok u v then G (k + 2) v else 0) else 0) +
        (if okc u then ∑ v : Fin 8, (if ok u v then G (k + 1) v else 0) else 0)
    split_ifs with h
    · rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun v _ => ?_
      rw [ih v]
      split_ifs <;> ring
    · rfl

theorem a_vals : a 1 = 6 ∧ a 2 = 36 ∧ a 3 = 72 := by
  refine ⟨(a_eq_G 0).trans (by decide +kernel), (a_eq_G 1).trans (by decide +kernel),
    (a_eq_G 2).trans (by decide +kernel)⟩

theorem a_rec (k : ℕ) : a (k + 4) = 2 * a (k + 3) + a (k + 2) := by
  rw [a_eq_G (k + 3), a_eq_G (k + 2), a_eq_G (k + 1), mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun u _ => G_rec k u

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) =
      6 * PowerSeries.X * (1 + 4 * PowerSeries.X - PowerSeries.X ^ 2) := by
  set f : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hf
  have key : PowerSeries.mk f * (1 - 2 * X - X ^ 2) =
      C 1 * (PowerSeries.mk f * X ^ 0) - C 2 * (PowerSeries.mk f * X ^ 1) -
        C 1 * (PowerSeries.mk f * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (6 : ℚ⟦X⟧) * X * (1 + 4 * X - X ^ 2) =
      C 6 * X ^ 1 + C 24 * X ^ 2 - C 6 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3⟩ := a_vals
  by_cases hk : k < 4
  · interval_cases k <;> simp [hf, v1, v2, v3] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    have hr := a_rec j
    have hr' : (a (j + 4) : ℚ) = 2 * a (j + 3) + a (j + 2) := by exact_mod_cast hr
    simp only [show 0 ≤ j + 4 by omega, show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega,
      show j + 4 - 0 = j + 4 by omega, show j + 4 - 1 = j + 3 by omega,
      show j + 4 - 2 = j + 2 by omega,
      show ¬ (j + 4 = 1) by omega, show ¬ (j + 4 = 2) by omega, show ¬ (j + 4 = 3) by omega,
      if_true, if_false, hf, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega]
    linarith

/-- The closed form of the entry. -/
noncomputable def r (n : ℕ) : ℝ := 9 * (Real.sqrt 2 * ((1 - Real.sqrt 2) ^ n * (1 + Real.sqrt 2) +
      (-1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ n))

theorem r_rec (n : ℕ) : r (n + 2) = 2 * r (n + 1) + r n := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold r
  linear_combination (9 * Real.sqrt 2 * ((1 - Real.sqrt 2) ^ n * (1 + Real.sqrt 2) +
      (-1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ n)) * hs

theorem r_three : r 3 = 72 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold r
  linear_combination (36 * Real.sqrt 2 ^ 2 + 36) * hs

theorem r_four : r 4 = 180 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold r
  linear_combination (18 * Real.sqrt 2 ^ 4 + 72 * Real.sqrt 2 ^ 2 + 90) * hs

theorem closed_pair (k : ℕ) : (a (k + 3) : ℝ) = r (k + 3) ∧ (a (k + 4) : ℝ) = r (k + 4) := by
  induction k with
  | zero =>
    obtain ⟨v1, v2, v3⟩ := a_vals
    have h4 : a 4 = 180 := by rw [a_rec 0, v3, v2]
    refine ⟨?_, ?_⟩
    · rw [v3, r_three]
      norm_num
    · rw [h4, r_four]
      norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 4 = (k + 3) + 2 by omega, r_rec, a_rec (k + 1)]
    push_cast
    rw [show k + 1 + 3 = k + 4 by omega, show k + 1 + 2 = k + 3 by omega, ih.1, ih.2]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207846.main := by
  refine ⟨OMA.Helpers.gen_fun, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  exact (OMA.Helpers.closed_pair k).1
