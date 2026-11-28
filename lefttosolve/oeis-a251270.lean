import OMAStatements.S_oeis_a251270
import Mathlib

/-!
Proof of Barker's conjectures for A251270 (4 X (n+1) binary arrays with no 2 X 2 subblock having
x11 - x00 less than x10 - x01).

For rows i, i + 1 and columns j, j + 1 the condition says that the vertical pair sum
x(i, j + 1) + x(i + 1, j + 1) is at least x(i, j) + x(i + 1, j). Reading the array column by
column, it is a chain of columns in which each column is compatible with the next one. With
`N m r` the number of ways to continue the column `r` by `m` columns, `a n = Sum_r N n r` and
`N (m + 1) r = Sum_s [Compat r s] N m s`. Columns are coded by 0..15 (bit i = row i), the
compatibility test on codes compares the three vertical pair sums, and `G` is the transfer
recursion on codes.

For every code u, 720 * G m u = Sum_k CT u k * m ^ k + CT u 7 * 2 ^ m (k = 0..6) with an explicit
integer table CT; the base case and the induction step reduce to finite checks on the table
(binomial expansion of (m + 1) ^ k). Summing over the 16 codes gives the closed form; the
generating function follows by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a251270 Finset

/-- A column of the array, read from top to bottom. -/
abbrev Col251270 := Fin 4 → Fin 2

/-- The condition on two consecutive columns `c` (left) and `d` (right). -/
def Compat251270 (c d : Col251270) : Prop :=
  ∀ i i' : Fin 4, i'.val = i.val + 1 →
    ¬ (((d i').val : ℤ) - (c i).val < ((c i').val : ℤ) - (d i).val)

instance decCompat251270 (c d : Col251270) : Decidable (Compat251270 c d) := by
  unfold Compat251270
  infer_instance

/-- Each column is compatible with the next one. -/
def Chain251270 {m : ℕ} (A : Fin m → Col251270) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 < m), Compat251270 (A ⟨j, by omega⟩) (A ⟨j + 1, hj⟩)

theorem valid_iff251270 {n : ℕ} (x : Fin 4 → Fin (n + 1) → Fin 2) :
    (∀ i i' : Fin 4, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val)) ↔
    Chain251270 (Equiv.piComm _ x) := by
  constructor
  · intro h j hj i i' hii'
    exact h i i' hii' ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
  · intro h i i' hii' j j' hjj'
    rcases j' with ⟨jv, hjv⟩
    simp only at hjj'
    subst hjj'
    exact h j.val hjv i i' hii'

theorem chain_one251270 (A : Fin 1 → Col251270) : Chain251270 A :=
  fun j hj => absurd hj (by omega)

theorem chain_cons251270 {m : ℕ} (r : Col251270) (A : Fin (m + 1) → Col251270) :
    Chain251270 (Fin.cons r A : Fin (m + 2) → Col251270) ↔
      Compat251270 r (A ⟨0, by omega⟩) ∧ Chain251270 A := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun j hj => h (j + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ j hj
    cases j with
    | zero => exact h0
    | succ j => exact h j (by omega)

/-- The number of ways to continue the column `r` by `m` more columns into a chain. -/
noncomputable def N251270 (m : ℕ) (r : Col251270) : ℕ := by
  classical
  exact ∑ A : Fin m → Col251270,
    if Chain251270 (Fin.cons r A : Fin (m + 1) → Col251270) then 1 else 0

theorem N_zero251270 (r : Col251270) : N251270 0 r = 1 := by
  classical
  unfold N251270
  rw [Fintype.sum_unique, if_pos (chain_one251270 _)]

theorem N_succ251270 (m : ℕ) (r : Col251270) :
    N251270 (m + 1) r = ∑ s : Col251270, if Compat251270 r s then N251270 m s else 0 := by
  classical
  unfold N251270
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col251270).symm _
    (fun p => if Chain251270 (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Col251270)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : Compat251270 r s
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [chain_cons251270]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [chain_cons251270]
    exact fun h => hc h.1

theorem a_eq_N251270 (n : ℕ) : a n = ∑ r : Col251270, N251270 n r := by
  classical
  have h1 : ((Finset.univ : Finset (Fin 4 → Fin (n + 1) → Fin 2)).filter (fun x =>
      ∀ i i' : Fin 4, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
        ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val))).card =
      ∑ A : Fin (n + 1) → Col251270, if Chain251270 A then 1 else 0 := by
    rw [Finset.card_filter]
    exact Fintype.sum_equiv (Equiv.piComm _) _ _ (fun x => if_congr (valid_iff251270 x) rfl rfl)
  have h2 : (∑ A : Fin (n + 1) → Col251270, if Chain251270 A then 1 else 0) =
      ∑ r : Col251270, N251270 n r := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col251270).symm _
      (fun p => if Chain251270 (Fin.cons p.1 p.2 : Fin (n + 1) → Col251270) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  rw [a, h1, h2]

/-- The column with code `u`: the entry of row `i` is bit `i` of `u`. -/
def col251270 (u : Fin 16) : Col251270 :=
  fun i => ⟨u.val / 2 ^ i.val % 2, Nat.mod_lt _ (by norm_num)⟩

theorem col_injective251270 : Function.Injective col251270 := by
  decide +kernel

theorem col_bijective251270 : Function.Bijective col251270 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨col_injective251270, by simp⟩

/-- Sum of the bits `i` and `i + 1` of `u`. -/
def psum251270 (u i : ℕ) : ℕ := u / 2 ^ i % 2 + u / 2 ^ (i + 1) % 2

/-- `Compat251270` on codes: the three vertical pair sums do not decrease. -/
def ok251270 (u v : Fin 16) : Bool :=
  Nat.ble (psum251270 u.val 0) (psum251270 v.val 0) &&
  Nat.ble (psum251270 u.val 1) (psum251270 v.val 1) &&
  Nat.ble (psum251270 u.val 2) (psum251270 v.val 2)

theorem ok_iff251270 : ∀ u v : Fin 16,
    Compat251270 (col251270 u) (col251270 v) ↔ ok251270 u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G251270 : ℕ → Fin 16 → ℕ
  | 0, _ => 1
  | m + 1, u => ∑ v : Fin 16, if ok251270 u v then G251270 m v else 0

theorem N_eq_G251270 (m : ℕ) : ∀ u : Fin 16, N251270 m (col251270 u) = G251270 m u := by
  induction m with
  | zero => intro u; rw [N_zero251270]; rfl
  | succ m ih =>
    intro u
    rw [N_succ251270, ← col_bijective251270.sum_comp]
    simp only [G251270]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok_iff251270 u v) rfl rfl

theorem a_eq_G251270 (n : ℕ) : (a n : ℤ) = ∑ u : Fin 16, (G251270 n u : ℤ) := by
  rw [a_eq_N251270, ← col_bijective251270.sum_comp]
  push_cast
  exact Finset.sum_congr rfl fun u _ => by rw [N_eq_G251270]

/-- `720 * G m u` is `Sum_k CT u k * m ^ k` (k = 0..6) plus `CT u 7 * 2 ^ m`. -/
def CT251270 : Fin 16 → Fin 8 → ℤ :=
  ![![-287280, -197064, -65452, -13110, -1510, -66, 2, 288000],
    ![-85680, -57576, -17820, -2910, -180, 6, 0, 86400],
    ![-28080, -17700, -4350, -300, 30, 0, 0, 28800],
    ![720, 1320, 720, 120, 0, 0, 0, 0],
    ![-28080, -17700, -4350, -300, 30, 0, 0, 28800],
    ![-13680, -7920, -1440, 0, 0, 0, 0, 14400],
    ![720, 1440, 720, 0, 0, 0, 0, 0],
    ![720, 720, 0, 0, 0, 0, 0, 0],
    ![-85680, -57576, -17820, -2910, -180, 6, 0, 86400],
    ![-28080, -17880, -4680, -480, 0, 0, 0, 28800],
    ![-13680, -7920, -1440, 0, 0, 0, 0, 14400],
    ![720, 1080, 360, 0, 0, 0, 0, 0],
    ![720, 1320, 720, 120, 0, 0, 0, 0],
    ![720, 1080, 360, 0, 0, 0, 0, 0],
    ![720, 720, 0, 0, 0, 0, 0, 0],
    ![720, 0, 0, 0, 0, 0, 0, 0]]

/-- The basis values `1, m, ..., m ^ 6, 2 ^ m`. -/
def W251270 (m : ℕ) : Fin 8 → ℤ :=
  ![1, (m : ℤ), (m : ℤ) ^ 2, (m : ℤ) ^ 3, (m : ℤ) ^ 4, (m : ℤ) ^ 5, (m : ℤ) ^ 6, 2 ^ m]

/-- The coefficients after the shift `m -> m + 1`. -/
def Tn251270 (u : Fin 16) : Fin 8 → ℤ :=
  ![CT251270 u 0 + CT251270 u 1 + CT251270 u 2 + CT251270 u 3 + CT251270 u 4 + CT251270 u 5 +
      CT251270 u 6,
    CT251270 u 1 + 2 * CT251270 u 2 + 3 * CT251270 u 3 + 4 * CT251270 u 4 + 5 * CT251270 u 5 +
      6 * CT251270 u 6,
    CT251270 u 2 + 3 * CT251270 u 3 + 6 * CT251270 u 4 + 10 * CT251270 u 5 + 15 * CT251270 u 6,
    CT251270 u 3 + 4 * CT251270 u 4 + 10 * CT251270 u 5 + 20 * CT251270 u 6,
    CT251270 u 4 + 5 * CT251270 u 5 + 15 * CT251270 u 6,
    CT251270 u 5 + 6 * CT251270 u 6,
    CT251270 u 6,
    2 * CT251270 u 7]

theorem base_facts251270 : ∀ u : Fin 16, CT251270 u 0 + CT251270 u 7 = 720 := by
  decide +kernel

theorem step_facts251270 : ∀ u : Fin 16, ∀ k : Fin 8,
    (∑ v : Fin 16, if ok251270 u v then CT251270 v k else 0) = Tn251270 u k := by
  decide +kernel

theorem shift251270 (u : Fin 16) (m : ℕ) :
    ∑ k : Fin 8, Tn251270 u k * W251270 m k = ∑ k : Fin 8, CT251270 u k * W251270 (m + 1) k := by
  simp only [Fin.sum_univ_eight, Tn251270, W251270]
  simp
  ring

theorem G_closed251270 (m : ℕ) : ∀ u : Fin 16,
    720 * (G251270 m u : ℤ) = ∑ k : Fin 8, CT251270 u k * W251270 m k := by
  induction m with
  | zero =>
    intro u
    simp only [Fin.sum_univ_eight, W251270]
    simp
    have := base_facts251270 u
    simp [G251270]
    linarith
  | succ m ih =>
    intro u
    have h1 : 720 * (G251270 (m + 1) u : ℤ) =
        ∑ v : Fin 16, if ok251270 u v then ∑ k : Fin 8, CT251270 v k * W251270 m k else 0 := by
      rw [G251270]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih v
      · simp
    have h2 : ∀ v : Fin 16, (if ok251270 u v then ∑ k : Fin 8, CT251270 v k * W251270 m k else 0) =
        ∑ k : Fin 8, (if ok251270 u v then CT251270 v k else 0) * W251270 m k := by
      intro v
      split_ifs <;> simp
    rw [h1, Finset.sum_congr rfl fun v _ => h2 v, Finset.sum_comm]
    simp only [← Finset.sum_mul, step_facts251270 u]
    exact shift251270 u m

/-- Column sums of `CT251270`. -/
def TOT251270 : Fin 8 → ℤ := ![-564480, -373656, -114472, -19770, -1810, -54, 2, 576000]

theorem tot_facts251270 : ∀ k : Fin 8, (∑ u : Fin 16, CT251270 u k) = TOT251270 k := by
  decide +kernel

theorem a_closedZ251270 (n : ℕ) :
    720 * (a n : ℤ) = ∑ k : Fin 8, TOT251270 k * W251270 n k := by
  rw [a_eq_G251270, Finset.mul_sum]
  simp only [G_closed251270 n]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, tot_facts251270]

theorem a_closedQ251270 (n : ℕ) : (a n : ℚ) =
    (5760 * (25 * 2 ^ (1 + n) - 49) - 186828 * n - 57236 * n ^ 2 - 9885 * n ^ 3 - 905 * n ^ 4 -
      27 * n ^ 5 + n ^ 6) / 360 := by
  have h := a_closedZ251270 n
  simp only [Fin.sum_univ_eight, TOT251270, W251270] at h
  simp at h
  have hq : (720 : ℚ) * (a n : ℚ) = -564480 + -(373656 * (n : ℚ)) + -(114472 * (n : ℚ) ^ 2) +
      -(19770 * (n : ℚ) ^ 3) + -(1810 * (n : ℚ) ^ 4) + -(54 * (n : ℚ) ^ 5) + 2 * (n : ℚ) ^ 6 +
      576000 * 2 ^ n := by
    exact_mod_cast h
  rw [pow_add]
  linarith

/-- The closed form as a function. -/
noncomputable def F251270 (n : ℕ) : ℚ :=
  (5760 * (25 * 2 ^ (1 + n) - 49) - 186828 * n - 57236 * n ^ 2 - 9885 * n ^ 3 - 905 * n ^ 4 -
    27 * n ^ 5 + n ^ 6) / 360

theorem a_vals251270 : (a 1 : ℚ) = 108 ∧ (a 2 : ℚ) = 480 ∧ (a 3 : ℚ) = 1667 ∧
    (a 4 : ℚ) = 4930 ∧ (a 5 : ℚ) = 13052 ∧ (a 6 : ℚ) = 31936 ∧ (a 7 : ℚ) = 73805 ∧
    (a 8 : ℚ) = 163604 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_closedQ251270] <;> norm_num

open PowerSeries in
theorem gen_fun251270 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 7 * (1 - 2 * X)) =
        X * (108 - 492 * X + 1127 * X ^ 2 - 1589 * X ^ 3 + 1407 * X ^ 4 - 769 * X ^ 5 +
          238 * X ^ 6 - 32 * X ^ 7) := by
  set f : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hfdef
  have key : PowerSeries.mk f * ((1 - X) ^ 7 * (1 - 2 * X)) =
      C 1 * (PowerSeries.mk f * X ^ 0) - C 9 * (PowerSeries.mk f * X ^ 1) +
        C 35 * (PowerSeries.mk f * X ^ 2) - C 77 * (PowerSeries.mk f * X ^ 3) +
        C 105 * (PowerSeries.mk f * X ^ 4) - C 91 * (PowerSeries.mk f * X ^ 5) +
        C 49 * (PowerSeries.mk f * X ^ 6) - C 15 * (PowerSeries.mk f * X ^ 7) +
        C 2 * (PowerSeries.mk f * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (108 - 492 * X + 1127 * X ^ 2 - 1589 * X ^ 3 + 1407 * X ^ 4 -
      769 * X ^ 5 + 238 * X ^ 6 - 32 * X ^ 7) =
      C 108 * X ^ 1 - C 492 * X ^ 2 + C 1127 * X ^ 3 - C 1589 * X ^ 4 + C 1407 * X ^ 5 -
        C 769 * X ^ 6 + C 238 * X ^ 7 - C 32 * X ^ 8 := by
    simp only [map_ofNat]
    ring
  have hf : ∀ t : ℕ, f (t + 1) = F251270 (t + 1) := by
    intro t
    simp only [hfdef, F251270, if_neg (Nat.succ_ne_zero t)]
    exact a_closedQ251270 (t + 1)
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := a_vals251270
  by_cases hk : k < 9
  · interval_cases k <;>
      simp only [hfdef, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true, if_false,
        v1, v2, v3, v4, v5, v6, v7, v8] <;>
      norm_num only
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
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega, if_true, if_false, hf]
    simp only [F251270]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a251270.main :=
  ⟨OMA.Helpers.gen_fun251270, fun n _ => OMA.Helpers.a_closedQ251270 n⟩
