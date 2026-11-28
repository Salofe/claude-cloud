import OMAStatements.S_oeis_a251269
import Mathlib

/-!
Proof of Barker's conjectures for A251269.

Write `u` for a column of the array (entries `u 0, u 1, u 2`). The condition on the 2 X 2 block
of rows `i, i + 1` and columns `j, j + 1` says that the sum of the two entries of these rows is
weakly increasing from column `j` to column `j + 1`. Reading the array column by column gives a
transfer recursion on the 8 possible columns (`N`, `G`). For each column code `u`, three times
the number of continuations by `m` further columns is `A u * 2 ^ m + B0 u + B1 u m + B2 u m^2 +
B3 u m^3` (explicit tables, `G_closed`). Summing gives the closed form, then the g.f.
-/

namespace OMA.Helpers

open OMA.S_oeis_a251269 Finset

/-- A column of the array. -/
abbrev Col251269 := Fin 3 → Fin 2

/-- The condition between the column `u` and the column `v` just to its right. -/
def Compat251269 (u v : Col251269) : Prop :=
  ∀ i i' : Fin 3, i'.val = i.val + 1 →
    ¬ (((v i').val : ℤ) - (u i).val < ((u i').val : ℤ) - (v i).val)

instance decCompat251269 (u v : Col251269) : Decidable (Compat251269 u v) := by
  unfold Compat251269
  infer_instance

/-- Each column of `A` is compatible with the next one. -/
def Chain251269 {m : ℕ} (A : Fin m → Col251269) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 < m), Compat251269 (A ⟨j, by omega⟩) (A ⟨j + 1, hj⟩)

theorem valid_iff251269 {n : ℕ} (x : Fin 3 → Fin (n + 1) → Fin 2) :
    (∀ i i' : Fin 3, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val)) ↔
    Chain251269 (fun j i => x i j) := by
  constructor
  · intro h j hj i i' hi
    exact h i i' hi ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
  · intro h i i' hi j j' hj
    obtain ⟨j, hjl⟩ := j
    obtain ⟨j', hjl'⟩ := j'
    simp only at hj
    subst hj
    exact h j hjl' i i' hi

theorem chain_one251269 (A : Fin 1 → Col251269) : Chain251269 A :=
  fun j hj => absurd hj (by omega)

theorem chain_cons251269 {m : ℕ} (r : Col251269) (A : Fin (m + 1) → Col251269) :
    Chain251269 (Fin.cons r A : Fin (m + 2) → Col251269) ↔
      Compat251269 r (A ⟨0, by omega⟩) ∧ Chain251269 A := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The number of ways to continue the column `r` by `m` more columns into a chain. -/
noncomputable def N251269 (m : ℕ) (r : Col251269) : ℕ := by
  classical
  exact ∑ A : Fin m → Col251269,
    if Chain251269 (Fin.cons r A : Fin (m + 1) → Col251269) then 1 else 0

theorem N_zero251269 (r : Col251269) : N251269 0 r = 1 := by
  classical
  unfold N251269
  rw [Fintype.sum_unique, if_pos (chain_one251269 _)]

theorem N_succ251269 (m : ℕ) (r : Col251269) :
    N251269 (m + 1) r = ∑ s : Col251269, if Compat251269 r s then N251269 m s else 0 := by
  classical
  unfold N251269
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col251269).symm _
    (fun p => if Chain251269 (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Col251269)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : Compat251269 r s
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [chain_cons251269]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [chain_cons251269]
    exact fun h => hc h.1

theorem a_eq_N251269 (n : ℕ) : (a n : ℤ) = ∑ r : Col251269, (N251269 n r : ℤ) := by
  classical
  have h1 : a n = ∑ x : Fin 3 → Fin (n + 1) → Fin 2,
      if Chain251269 (fun j i => x i j) then 1 else 0 := by
    rw [a, Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr (valid_iff251269 x) rfl rfl
  have h2 : (∑ x : Fin 3 → Fin (n + 1) → Fin 2,
      if Chain251269 (fun j i => x i j) then 1 else 0) =
      ∑ A : Fin (n + 1) → Col251269, if Chain251269 A then 1 else 0 :=
    Fintype.sum_equiv (Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 1)) => Fin 2)) _ _
      (fun x => rfl)
  have h3 : (∑ A : Fin (n + 1) → Col251269, if Chain251269 A then 1 else 0) =
      ∑ r : Col251269, N251269 n r := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col251269).symm _
      (fun p => if Chain251269 (Fin.cons p.1 p.2 : Fin (n + 1) → Col251269) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  rw [h1, h2, h3]
  push_cast
  rfl

/-- The column with code `u`: the entry of row `i` is bit `i` of `u`. -/
def col251269 (u : Fin 8) : Col251269 := fun i => if Nat.testBit u.val i.val then 1 else 0

theorem col_injective251269 : Function.Injective col251269 := by
  decide +kernel

theorem col_bijective251269 : Function.Bijective col251269 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨col_injective251269, by simp⟩

/-- Sum of the entries of rows 0 and 1 of the column with code `u`. -/
def k1_251269 (u : ℕ) : ℕ := u % 2 + u / 2 % 2

/-- Sum of the entries of rows 1 and 2 of the column with code `u`. -/
def k2_251269 (u : ℕ) : ℕ := u / 2 % 2 + u / 4 % 2

/-- `Compat` on codes. -/
def ok251269 (u v : Fin 8) : Bool :=
  Nat.ble (k1_251269 u.val) (k1_251269 v.val) && Nat.ble (k2_251269 u.val) (k2_251269 v.val)

theorem ok_iff251269 : ∀ u v : Fin 8,
    Compat251269 (col251269 u) (col251269 v) ↔ ok251269 u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G251269 : ℕ → Fin 8 → ℕ
  | 0, _ => 1
  | m + 1, u => ∑ v : Fin 8, if ok251269 u v then G251269 m v else 0

theorem N_eq_G251269 (m : ℕ) : ∀ u : Fin 8, N251269 m (col251269 u) = G251269 m u := by
  induction m with
  | zero => intro u; rw [N_zero251269]; rfl
  | succ m ih =>
    intro u
    rw [N_succ251269, ← col_bijective251269.sum_comp]
    simp only [G251269]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok_iff251269 u v) rfl rfl

theorem a_eq_G251269 (n : ℕ) : (a n : ℤ) = ∑ u : Fin 8, (G251269 n u : ℤ) := by
  rw [a_eq_N251269, ← col_bijective251269.sum_comp]
  exact Finset.sum_congr rfl fun u _ => by rw [N_eq_G251269]

/-- Coefficient of `2 ^ m` in `3 * G m u`. -/
def tA251269 (u : Fin 8) : ℤ :=
  match u.val with
  | 0 => 108 | 1 => 36 | 2 => 18 | 4 => 36 | 5 => 18 | _ => 0

/-- Constant term of `3 * G m u`. -/
def tB0_251269 (u : Fin 8) : ℤ :=
  match u.val with
  | 0 => -105 | 1 => -33 | 2 => -15 | 4 => -33 | 5 => -15 | _ => 3

/-- Coefficient of `m` in `3 * G m u`. -/
def tB1_251269 (u : Fin 8) : ℤ :=
  match u.val with
  | 0 => -67 | 1 => -18 | 2 => -6 | 3 => 3 | 4 => -18 | 5 => -6 | 6 => 3 | _ => 0

/-- Coefficient of `m ^ 2` in `3 * G m u`. -/
def tB2_251269 (u : Fin 8) : ℤ :=
  match u.val with
  | 0 => -18 | 1 => -3 | 4 => -3 | _ => 0

/-- Coefficient of `m ^ 3` in `3 * G m u`. -/
def tB3_251269 (u : Fin 8) : ℤ :=
  match u.val with
  | 0 => -2 | _ => 0

theorem base_facts251269 : ∀ u : Fin 8, tA251269 u + tB0_251269 u = 3 := by
  decide +kernel

theorem step_facts251269 : ∀ u : Fin 8,
    (∑ v : Fin 8, if ok251269 u v then tA251269 v else 0) = 2 * tA251269 u ∧
    (∑ v : Fin 8, if ok251269 u v then tB3_251269 v else 0) = tB3_251269 u ∧
    (∑ v : Fin 8, if ok251269 u v then tB2_251269 v else 0) =
      tB2_251269 u + 3 * tB3_251269 u ∧
    (∑ v : Fin 8, if ok251269 u v then tB1_251269 v else 0) =
      tB1_251269 u + 2 * tB2_251269 u + 3 * tB3_251269 u ∧
    (∑ v : Fin 8, if ok251269 u v then tB0_251269 v else 0) =
      tB0_251269 u + tB1_251269 u + tB2_251269 u + tB3_251269 u := by
  decide +kernel

theorem G_closed251269 (m : ℕ) : ∀ u : Fin 8, 3 * (G251269 m u : ℤ) =
    tA251269 u * 2 ^ m + tB0_251269 u + tB1_251269 u * m + tB2_251269 u * m ^ 2 +
      tB3_251269 u * m ^ 3 := by
  induction m with
  | zero =>
    intro u
    have h := base_facts251269 u
    simp only [G251269, Nat.cast_one, Nat.cast_zero, pow_zero]
    linarith
  | succ m ih =>
    intro u
    have hsum : 3 * (G251269 (m + 1) u : ℤ) = ∑ v : Fin 8, if ok251269 u v then
        tA251269 v * 2 ^ m + tB0_251269 v + tB1_251269 v * m + tB2_251269 v * m ^ 2 +
          tB3_251269 v * m ^ 3 else 0 := by
      rw [G251269]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih v
      · rfl
    rw [hsum]
    have hP : ∀ v : Fin 8, (if ok251269 u v then
        tA251269 v * 2 ^ m + tB0_251269 v + tB1_251269 v * m + tB2_251269 v * m ^ 2 +
          tB3_251269 v * m ^ 3 else 0) =
        (if ok251269 u v then tA251269 v else 0) * 2 ^ m +
        (if ok251269 u v then tB0_251269 v else 0) +
        (if ok251269 u v then tB1_251269 v else 0) * (m : ℤ) +
        (if ok251269 u v then tB2_251269 v else 0) * (m : ℤ) ^ 2 +
        (if ok251269 u v then tB3_251269 v else 0) * (m : ℤ) ^ 3 := by
      intro v
      split_ifs <;> simp
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨hA, h3, h2, h1, h0⟩ := step_facts251269 u
    rw [hA, h3, h2, h1, h0]
    push_cast
    ring

theorem sum_facts251269 : (∑ u : Fin 8, tA251269 u) = 216 ∧
    (∑ u : Fin 8, tB0_251269 u) = -192 ∧ (∑ u : Fin 8, tB1_251269 u) = -109 ∧
    (∑ u : Fin 8, tB2_251269 u) = -24 ∧ (∑ u : Fin 8, tB3_251269 u) = -2 := by
  decide +kernel

theorem closed3_251269 (n : ℕ) :
    3 * (a n : ℤ) = 216 * 2 ^ n - 192 - 109 * n - 24 * n ^ 2 - 2 * n ^ 3 := by
  rw [a_eq_G251269, Finset.mul_sum]
  simp only [G_closed251269 n]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨hA, h0, h1, h2, h3⟩ := sum_facts251269
  rw [hA, h0, h1, h2, h3]
  ring

theorem closed251269 (n : ℕ) : (a n : ℚ) =
    8 * (9 * 2 ^ n - 8) - (109 * n) / 3 - 8 * n ^ 2 - (2 * n ^ 3) / 3 := by
  have h := closed3_251269 n
  have hq : ((3 * (a n : ℤ) : ℤ) : ℚ) =
      ((216 * 2 ^ n - 192 - 109 * n - 24 * n ^ 2 - 2 * n ^ 3 : ℤ) : ℚ) := by rw [h]
  push_cast at hq
  linarith

/-- The sequence of the g.f. -/
noncomputable def b251269 (n : ℕ) : ℚ := if n = 0 then 0 else (a n : ℚ)

/-- The closed form, as a function on all of ℕ. -/
noncomputable def f251269 (n : ℕ) : ℚ :=
  8 * (9 * 2 ^ n - 8) - (109 * n) / 3 - 8 * n ^ 2 - (2 * n ^ 3) / 3

theorem b_eq251269 (n : ℕ) (hn : 1 ≤ n) : b251269 n = f251269 n := by
  rw [b251269, if_neg (by omega), closed251269]
  rfl

open PowerSeries in
theorem gen_fun251269 : PowerSeries.mk b251269 * ((1 - X) ^ 4 * (1 - 2 * X)) =
    X * (35 - 96 * X + 119 * X ^ 2 - 70 * X ^ 3 + 16 * X ^ 4) := by
  have key : PowerSeries.mk b251269 * ((1 - X) ^ 4 * (1 - 2 * X)) =
      C 1 * (PowerSeries.mk b251269 * X ^ 0) - C 6 * (PowerSeries.mk b251269 * X ^ 1) +
      C 14 * (PowerSeries.mk b251269 * X ^ 2) - C 16 * (PowerSeries.mk b251269 * X ^ 3) +
      C 9 * (PowerSeries.mk b251269 * X ^ 4) - C 2 * (PowerSeries.mk b251269 * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (35 - 96 * X + 119 * X ^ 2 - 70 * X ^ 3 + 16 * X ^ 4) =
      C 35 * X ^ 1 - C 96 * X ^ 2 + C 119 * X ^ 3 - C 70 * X ^ 4 + C 16 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have v0 : b251269 0 = 0 := by rw [b251269, if_pos rfl]
  have v1 : b251269 1 = 35 := by rw [b_eq251269 1 le_rfl, f251269]; norm_num
  have v2 : b251269 2 = 114 := by rw [b_eq251269 2 (by norm_num), f251269]; norm_num
  have v3 : b251269 3 = 313 := by rw [b_eq251269 3 (by norm_num), f251269]; norm_num
  have v4 : b251269 4 = 772 := by rw [b_eq251269 4 (by norm_num), f251269]; norm_num
  have v5 : b251269 5 = 1775 := by rw [b_eq251269 5 (by norm_num), f251269]; norm_num
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [v0, v1, v2, v3, v4, v5]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega, if_true, if_false]
    rw [b_eq251269 (j + 6) (by omega), b_eq251269 (j + 5) (by omega),
      b_eq251269 (j + 4) (by omega), b_eq251269 (j + 3) (by omega),
      b_eq251269 (j + 2) (by omega), b_eq251269 (j + 1) (by omega)]
    simp only [f251269]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a251269.main :=
  ⟨OMA.Helpers.gen_fun251269, fun n _ => OMA.Helpers.closed251269 n⟩
