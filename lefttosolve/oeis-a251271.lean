import OMAStatements.S_oeis_a251271
import Mathlib

/-!
Proof of Barker's conjectures for A251271.

Read the array column by column. A 2 X 2 subblock condition only involves two consecutive
columns, so an array is good iff each column is compatible with the next one (`good_iff`).
Removing the first column gives a transfer recursion `N`, which on column codes 0..31 is `G`.
For every code `u`, `2520 * G m u = P (ctab u) m + etab u * 2 ^ m` with explicit integer
tables (`G_closed`, by induction on `m`; the step is a finite check on the tables). Summing over
the codes gives the closed form, from which the g.f. follows by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a251271 Finset

/-- A column of the array, read from top to bottom. -/
abbrev Col251271 := Fin 5 → Fin 2

/-- The subblock condition between a column `c` and the column `d` to its right. -/
def Compat251271 (c d : Col251271) : Prop :=
  ∀ i i' : Fin 5, i'.val = i.val + 1 →
    ¬ (((d i').val : ℤ) - (c i).val < ((c i').val : ℤ) - (d i).val)

instance (c d : Col251271) : Decidable (Compat251271 c d) := by
  unfold Compat251271
  infer_instance

/-- Each column is compatible with the next one. -/
def Chain251271 {m : ℕ} (A : Fin m → Col251271) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 < m), Compat251271 (A ⟨j, by omega⟩) (A ⟨j + 1, hj⟩)

theorem good_iff251271 {n : ℕ} (x : Fin 5 → Fin (n + 1) → Fin 2) :
    (∀ i i' : Fin 5, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val)) ↔
    Chain251271 (fun j i => x i j) := by
  constructor
  · intro h j hj i i' hi
    exact h i i' hi ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
  · intro h i i' hi j j' hj
    obtain ⟨j, hj0⟩ := j
    obtain ⟨j', hj'0⟩ := j'
    simp only at hj
    subst hj
    exact h j hj'0 i i' hi

theorem chain_one251271 (A : Fin 1 → Col251271) : Chain251271 A :=
  fun i hi => absurd hi (by omega)

theorem chain_cons251271 {m : ℕ} (r : Col251271) (A : Fin (m + 1) → Col251271) :
    Chain251271 (Fin.cons r A : Fin (m + 2) → Col251271) ↔
      Compat251271 r (A ⟨0, by omega⟩) ∧ Chain251271 A := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The number of ways to continue the column `r` by `m` more columns into a chain. -/
noncomputable def N251271 (m : ℕ) (r : Col251271) : ℕ := by
  classical
  exact ∑ A : Fin m → Col251271,
    if Chain251271 (Fin.cons r A : Fin (m + 1) → Col251271) then 1 else 0

theorem N_zero251271 (r : Col251271) : N251271 0 r = 1 := by
  classical
  unfold N251271
  rw [Fintype.sum_unique, if_pos (chain_one251271 _)]

theorem N_succ251271 (m : ℕ) (r : Col251271) :
    N251271 (m + 1) r = ∑ s : Col251271, if Compat251271 r s then N251271 m s else 0 := by
  classical
  unfold N251271
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col251271).symm _
    (fun p => if Chain251271 (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Col251271)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : Compat251271 r s
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [chain_cons251271]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [chain_cons251271]
    exact fun h => hc h.1

theorem a_eq_N251271 (n : ℕ) : a n = ∑ r : Col251271, N251271 n r := by
  classical
  have h1 : a n = ∑ x : Fin 5 → Fin (n + 1) → Fin 2,
      if Chain251271 (fun j i => x i j) then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr (good_iff251271 x) rfl rfl
  have h2 : (∑ x : Fin 5 → Fin (n + 1) → Fin 2,
      if Chain251271 (fun j i => x i j) then 1 else 0) =
      ∑ A : Fin (n + 1) → Col251271, if Chain251271 A then 1 else 0 :=
    Fintype.sum_equiv (Equiv.piComm fun (_ : Fin 5) (_ : Fin (n + 1)) => Fin 2) _ _
      (fun x => rfl)
  have h3 : (∑ A : Fin (n + 1) → Col251271, if Chain251271 A then 1 else 0) =
      ∑ r : Col251271, N251271 n r := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Col251271).symm _
      (fun p => if Chain251271 (Fin.cons p.1 p.2 : Fin (n + 1) → Col251271) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  rw [h1, h2, h3]

/-- The column with code `u`: the entry of row `i` is bit `i` of `u`. -/
def col251271 (u : Fin 32) : Col251271 := fun i => if Nat.testBit u.val i.val then 1 else 0

theorem col_injective251271 : Function.Injective col251271 := by
  decide +kernel

theorem col_bijective251271 : Function.Bijective col251271 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨col_injective251271, by simp⟩

/-- Sum of the bits `i` and `i + 1` of `w`. -/
def ps251271 (w i : ℕ) : ℕ := (w >>> i) % 2 + (w >>> (i + 1)) % 2

/-- `Compat` on codes: the vertical pair sums do not decrease from left to right. -/
def ok251271 (u v : Fin 32) : Bool :=
  Nat.ble (ps251271 u.val 0) (ps251271 v.val 0) && Nat.ble (ps251271 u.val 1) (ps251271 v.val 1) &&
  Nat.ble (ps251271 u.val 2) (ps251271 v.val 2) && Nat.ble (ps251271 u.val 3) (ps251271 v.val 3)

theorem ok_iff251271 : ∀ u v : Fin 32,
    Compat251271 (col251271 u) (col251271 v) ↔ ok251271 u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G251271 : ℕ → Fin 32 → ℕ
  | 0, _ => 1
  | m + 1, u => ∑ v : Fin 32, if ok251271 u v then G251271 m v else 0

theorem N_eq_G251271 (m : ℕ) : ∀ u : Fin 32, N251271 m (col251271 u) = G251271 m u := by
  induction m with
  | zero => intro u; rw [N_zero251271]; rfl
  | succ m ih =>
    intro u
    rw [N_succ251271, ← col_bijective251271.sum_comp]
    simp only [G251271]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok_iff251271 u v) rfl rfl

theorem a_eq_G251271 (n : ℕ) : a n = ∑ u : Fin 32, G251271 n u := by
  rw [a_eq_N251271, ← col_bijective251271.sum_comp]
  exact Finset.sum_congr rfl fun u _ => by rw [N_eq_G251271]

/-- A polynomial of degree at most 8 with coefficients `f`. -/
def P251271 (f : Fin 9 → ℤ) (m : ℤ) : ℤ :=
  f 0 + f 1 * m + f 2 * m ^ 2 + f 3 * m ^ 3 + f 4 * m ^ 4 + f 5 * m ^ 5 + f 6 * m ^ 6 +
    f 7 * m ^ 7 + f 8 * m ^ 8

/-- The coefficients of `m ↦ P f (m + 1)`. -/
def shift251271 (f : Fin 9 → ℤ) : Fin 9 → ℤ :=
  fun j => ∑ k : Fin 9, (Nat.choose k.val j.val : ℤ) * f k

theorem P_shift251271 (f : Fin 9 → ℤ) (m : ℤ) :
    P251271 f (m + 1) = P251271 (shift251271 f) m := by
  simp only [P251271, shift251271, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [Nat.choose]
  ring

theorem P_sum251271 (q : Fin 32 → Bool) (f : Fin 32 → Fin 9 → ℤ) (m : ℤ) :
    (∑ v : Fin 32, if q v then P251271 (f v) m else 0) =
      P251271 (fun k => ∑ v : Fin 32, if q v then f v k else 0) m := by
  simp only [P251271, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib,
    Finset.sum_mul]

/-- Coefficient table: `ctab u k` is 2520 times the coefficient of `m ^ k` in `G m u`. -/
def ctabL251271 : List (List ℤ) :=
  [[-13797000, -9553944, -3293578, -742931, -117831, -12446, -672, 1, 1],
    [-3727080, -2574786, -877989, -190169, -26670, -2009, -21, 4, 0],
    [-1116360, -765450, -252441, -48510, -4620, 0, 21, 0, 0],
    [2520, 7014, 7035, 3045, 525, 21, 0, 0, 0],
    [-1116360, -765240, -252308, -48720, -4760, 0, 28, 0, 0],
    [-370440, -248724, -75390, -10920, -210, 84, 0, 0, 0],
    [2520, 7140, 7140, 2940, 420, 0, 0, 0, 0],
    [2520, 4620, 2520, 420, 0, 0, 0, 0, 0],
    [-1116360, -765450, -252441, -48510, -4620, 0, 21, 0, 0],
    [-370440, -249186, -76335, -11655, -525, 21, 0, 0, 0],
    [-183960, -120120, -32760, -3360, 0, 0, 0, 0, 0],
    [2520, 5880, 3780, 420, 0, 0, 0, 0, 0],
    [2520, 7140, 7140, 2940, 420, 0, 0, 0, 0],
    [2520, 6300, 5040, 1260, 0, 0, 0, 0, 0],
    [2520, 5040, 2520, 0, 0, 0, 0, 0, 0],
    [2520, 2520, 0, 0, 0, 0, 0, 0, 0],
    [-3727080, -2574786, -877989, -190169, -26670, -2009, -21, 4, 0],
    [-1116360, -765996, -254072, -50295, -5495, -189, 7, 0, 0],
    [-370440, -249186, -76335, -11655, -525, 21, 0, 0, 0],
    [2520, 6090, 4935, 1470, 105, 0, 0, 0, 0],
    [-370440, -248724, -75390, -10920, -210, 84, 0, 0, 0],
    [-183960, -120120, -32760, -3360, 0, 0, 0, 0, 0],
    [2520, 6300, 5040, 1260, 0, 0, 0, 0, 0],
    [2520, 3780, 1260, 0, 0, 0, 0, 0, 0],
    [2520, 7014, 7035, 3045, 525, 21, 0, 0, 0],
    [2520, 6090, 4935, 1470, 105, 0, 0, 0, 0],
    [2520, 5880, 3780, 420, 0, 0, 0, 0, 0],
    [2520, 2520, 0, 0, 0, 0, 0, 0, 0],
    [2520, 4620, 2520, 420, 0, 0, 0, 0, 0],
    [2520, 3780, 1260, 0, 0, 0, 0, 0, 0],
    [2520, 2520, 0, 0, 0, 0, 0, 0, 0],
    [2520, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- `etab u` is 2520 times the coefficient of `2 ^ m` in `G m u`. -/
def etabL251271 : List ℤ :=
  [13799520, 3729600, 1118880, 0, 1118880, 372960, 0, 0, 1118880, 372960, 186480, 0, 0, 0, 0, 0, 3729600, 1118880, 372960, 0, 372960, 186480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def ctab251271 (u : Fin 32) (k : Fin 9) : ℤ := (ctabL251271.getD u.val []).getD k.val 0

def etab251271 (u : Fin 32) : ℤ := etabL251271.getD u.val 0

theorem base_facts251271 : ∀ u : Fin 32, ctab251271 u 0 + etab251271 u = 2520 := by
  decide +kernel

theorem step_facts251271 : ∀ u : Fin 32,
    (∀ k : Fin 9, (∑ v : Fin 32, if ok251271 u v then ctab251271 v k else 0) =
      shift251271 (ctab251271 u) k) ∧
    (∑ v : Fin 32, if ok251271 u v then etab251271 v else 0) = 2 * etab251271 u := by
  decide +kernel

theorem G_closed251271 (m : ℕ) : ∀ u : Fin 32,
    2520 * (G251271 m u : ℤ) = P251271 (ctab251271 u) m + etab251271 u * 2 ^ m := by
  induction m with
  | zero =>
    intro u
    simp only [G251271, P251271, Nat.cast_zero, pow_zero]
    have := base_facts251271 u
    push_cast
    linarith
  | succ m ih =>
    intro u
    have hsum : 2520 * (G251271 (m + 1) u : ℤ) = ∑ v : Fin 32,
        if ok251271 u v then P251271 (ctab251271 v) m + etab251271 v * 2 ^ m else 0 := by
      rw [G251271]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih v
      · simp
    have hsplit : ∀ v : Fin 32,
        (if ok251271 u v then P251271 (ctab251271 v) m + etab251271 v * 2 ^ m else 0) =
          (if ok251271 u v then P251271 (ctab251271 v) m else 0) +
            (if ok251271 u v then etab251271 v else 0) * 2 ^ m := by
      intro v
      split_ifs <;> simp
    rw [hsum]
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [P_sum251271]
    obtain ⟨h1, h2⟩ := step_facts251271 u
    rw [funext h1, h2]
    push_cast
    rw [P_shift251271]
    ring

/-- The coefficients of 2520 times the closed form. -/
def tot251271 : Fin 9 → ℤ :=
  fun k => [-27518400, -18907464, -6363848, -1352064, -190036, -16401, -637, 9, 1].getD k.val 0

theorem sum_facts251271 :
    (fun k => ∑ u : Fin 32, ctab251271 u k) = tot251271 ∧
      (∑ u : Fin 32, etab251271 u) = 27599040 := by
  refine ⟨funext ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem closedZ251271 (n : ℕ) :
    2520 * (a n : ℤ) = P251271 tot251271 n + 27599040 * 2 ^ n := by
  rw [a_eq_G251271]
  push_cast
  rw [Finset.mul_sum]
  simp only [G_closed251271]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_facts251271.2]
  congr 1
  rw [← sum_facts251271.1]
  simp only [P251271, Finset.sum_add_distrib, Finset.sum_mul]

theorem closedQ251271 (n : ℕ) : (a n : ℚ) =
    (20160 * (1369 * 2 ^ n - 1365) - 18907464 * n - 6363848 * n ^ 2 - 1352064 * n ^ 3 -
      190036 * n ^ 4 - 16401 * n ^ 5 - 637 * n ^ 6 + 9 * n ^ 7 + n ^ 8) / 2520 := by
  have h := closedZ251271 n
  have h' : ((2520 * (a n : ℤ) : ℤ) : ℚ) = ((P251271 tot251271 n + 27599040 * 2 ^ n : ℤ) : ℚ) := by
    rw [h]
  push_cast [P251271, tot251271] at h'
  simp only [List.getD] at h'
  norm_num at h'
  rw [eq_div_iff (by norm_num)]
  linear_combination h'

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a251271 PowerSeries

theorem vals251271 : (a 1 : ℚ) = 337 ∧ (a 2 : ℚ) = 2058 ∧ (a 3 : ℚ) = 9109 ∧ (a 4 : ℚ) = 32636 ∧ (a 5 : ℚ) = 100843 ∧ (a 6 : ℚ) = 279718 ∧ (a 7 : ℚ) = 715685 ∧ (a 8 : ℚ) = 1722176 ∧ (a 9 : ℚ) = 3954037 ∧ (a 10 : ℚ) = 8757506 :=
  ⟨by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num, by rw [closedQ251271]; norm_num⟩

set_option maxRecDepth 20000 in
theorem gen_fun251271 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 9 * (1 - 2 * X)) =
        X * (337 - 1649 * X + 4669 * X ^ 2 - 9003 * X ^ 3 + 11763 * X ^ 4 - 10549 * X ^ 5 +
          6447 * X ^ 6 - 2573 * X ^ 7 + 606 * X ^ 8 - 64 * X ^ 9) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * ((1 - X) ^ 9 * (1 - 2 * X)) =
      PowerSeries.mk F * X ^ 0 - C 11 * (PowerSeries.mk F * X ^ 1) + C 54 * (PowerSeries.mk F * X ^ 2) - C 156 * (PowerSeries.mk F * X ^ 3) + C 294 * (PowerSeries.mk F * X ^ 4) - C 378 * (PowerSeries.mk F * X ^ 5) + C 336 * (PowerSeries.mk F * X ^ 6) - C 204 * (PowerSeries.mk F * X ^ 7) + C 81 * (PowerSeries.mk F * X ^ 8) - C 19 * (PowerSeries.mk F * X ^ 9) + C 2 * (PowerSeries.mk F * X ^ 10) := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (337 - 1649 * X + 4669 * X ^ 2 - 9003 * X ^ 3 + 11763 * X ^ 4 -
      10549 * X ^ 5 + 6447 * X ^ 6 - 2573 * X ^ 7 + 606 * X ^ 8 - 64 * X ^ 9) =
      C 337 * X ^ 1 - C 1649 * X ^ 2 + C 4669 * X ^ 3 - C 9003 * X ^ 4 + C 11763 * X ^ 5 - C 10549 * X ^ 6 + C 6447 * X ^ 7 - C 2573 * X ^ 8 + C 606 * X ^ 9 - C 64 * X ^ 10 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := vals251271
  by_cases hk : k < 11
  · interval_cases k <;> norm_num [hF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 11 := ⟨k - 11, by omega⟩
    simp only [show 1 ≤ j + 11 by omega, show 2 ≤ j + 11 by omega, show 3 ≤ j + 11 by omega, show 4 ≤ j + 11 by omega, show 5 ≤ j + 11 by omega, show 6 ≤ j + 11 by omega, show 7 ≤ j + 11 by omega, show 8 ≤ j + 11 by omega, show 9 ≤ j + 11 by omega, show 10 ≤ j + 11 by omega, show j + 11 - 0 = j + 11 by omega, show j + 11 - 1 = j + 10 by omega, show j + 11 - 2 = j + 9 by omega, show j + 11 - 3 = j + 8 by omega, show j + 11 - 4 = j + 7 by omega, show j + 11 - 5 = j + 6 by omega, show j + 11 - 6 = j + 5 by omega, show j + 11 - 7 = j + 4 by omega, show j + 11 - 8 = j + 3 by omega, show j + 11 - 9 = j + 2 by omega, show j + 11 - 10 = j + 1 by omega, show ¬ (j + 1 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 7 = 0) by omega, show ¬ (j + 8 = 0) by omega, show ¬ (j + 9 = 0) by omega, show ¬ (j + 10 = 0) by omega, show ¬ (j + 11 = 0) by omega, show ¬ (j + 11 = 1) by omega,
      show ¬ (j + 11 = 2) by omega, show ¬ (j + 11 = 3) by omega, show ¬ (j + 11 = 4) by omega,
      show ¬ (j + 11 = 5) by omega, show ¬ (j + 11 = 6) by omega, show ¬ (j + 11 = 7) by omega,
      show ¬ (j + 11 = 8) by omega, show ¬ (j + 11 = 9) by omega, show ¬ (j + 11 = 10) by omega,
      if_true, if_false, hF, zero_le]
    rw [closedQ251271 (j + 1), closedQ251271 (j + 2), closedQ251271 (j + 3), closedQ251271 (j + 4), closedQ251271 (j + 5), closedQ251271 (j + 6), closedQ251271 (j + 7), closedQ251271 (j + 8), closedQ251271 (j + 9), closedQ251271 (j + 10), closedQ251271 (j + 11)]
    push_cast
    ring

theorem closed_main251271 : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
    (20160 * (1369 * 2 ^ n - 1365) - 18907464 * n - 6363848 * n ^ 2 - 1352064 * n ^ 3 -
      190036 * n ^ 4 - 16401 * n ^ 5 - 637 * n ^ 6 + 9 * n ^ 7 + n ^ 8) / 2520 :=
  fun n _ => closedQ251271 n

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a251271.main :=
  ⟨OMA.Helpers.gen_fun251271, OMA.Helpers.closed_main251271⟩
