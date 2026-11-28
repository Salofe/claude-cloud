import OMAStatements.S_oeis_a251130
import Mathlib

/-!
Proof of the conjectures for A251130 ((n+1) X 2 arrays over 0..2 with no 2 X 2 subblock having
diagonal sum greater than the antidiagonal maximum).

Reading the array row by row, it is a chain of rows (pairs in 0..2) in which each row is
compatible with the next one. With `N m r` the number of ways to continue the row `r` by `m`
rows, `a (n + 1) = Sum_r N (n + 1) r` and `N (m + 1) r = Sum_s [Compat r s] N m s`. Rows are coded
by 0..8 (`u % 3` in column 0, `u / 3` in column 1) and `G` is the transfer recursion on codes.

For every code u and m >= 2, 12 * G m u = CT u 0 + CT u 1 m + CT u 2 m^2 + CT u 3 m^3 +
CT u 4 2^m + CT u 5 (-1)^m with an explicit integer table CT; the base case m = 2 and the
induction step reduce to finite checks on the table. Summing over the 9 codes gives the closed
form for n >= 2 (n = 1 is a direct computation); recurrence and generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a251130 Finset

/-- A row of the array. -/
abbrev Row251130 := Fin 2 → Fin 3

/-- The condition on two consecutive rows `r` (upper) and `s` (lower). -/
def Compat251130 (r s : Row251130) : Prop := okBlock (r 0) (r 1) (s 0) (s 1)

instance decCompat251130 (r s : Row251130) : Decidable (Compat251130 r s) := by
  unfold Compat251130
  infer_instance

theorem valid_zero251130 (x : Fin 1 → Row251130) : isValid 0 x :=
  fun i => absurd i.isLt (by omega)

theorem valid_cons251130 {m : ℕ} (r : Row251130) (A : Fin (m + 1) → Row251130) :
    isValid (m + 1) (Fin.cons r A : Fin (m + 2) → Row251130) ↔
      Compat251130 r (A 0) ∧ isValid m A := by
  unfold isValid Compat251130
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 0
      simpa using h0
    · intro i j
      have h1 := h i.succ j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simpa [← Fin.succ_castSucc] using h1
  · rintro ⟨h0, h⟩ i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h0
    · have h1 := h i 0
      simpa [← Fin.succ_castSucc] using h1

/-- The number of ways to continue the row `r` by `m` more rows into a valid array. -/
noncomputable def N251130 (m : ℕ) (r : Row251130) : ℕ :=
  ∑ A : Fin m → Row251130,
    if isValid m (Fin.cons r A : Fin (m + 1) → Row251130) then 1 else 0

theorem N_zero251130 (r : Row251130) : N251130 0 r = 1 := by
  unfold N251130
  rw [Fintype.sum_unique, if_pos (valid_zero251130 _)]

theorem N_succ251130 (m : ℕ) (r : Row251130) :
    N251130 (m + 1) r = ∑ s : Row251130, if Compat251130 r s then N251130 m s else 0 := by
  unfold N251130
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row251130).symm _
    (fun p => if isValid (m + 1) (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row251130)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : Compat251130 r s
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [valid_cons251130]
    simp only [Fin.cons_zero]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [valid_cons251130]
    simp only [Fin.cons_zero]
    exact fun h => hc h.1

theorem a_eq_N251130 (n : ℕ) : a (n + 1) = ∑ r : Row251130, N251130 (n + 1) r := by
  have h1 : ((Finset.univ : Finset (Fin (n + 1 + 1) → Row251130)).filter
      (isValid (n + 1))).card =
      ∑ A : Fin (n + 2) → Row251130, if isValid (n + 1) A then 1 else 0 := by
    rw [Finset.card_filter]
  have h2 : (∑ A : Fin (n + 2) → Row251130, if isValid (n + 1) A then 1 else 0) =
      ∑ r : Row251130, N251130 (n + 1) r := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row251130).symm _
      (fun p => if isValid (n + 1) (Fin.cons p.1 p.2 : Fin (n + 2) → Row251130) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  rw [a, h1, h2]

/-- The row with code `u`: column 0 holds `u % 3`, column 1 holds `u / 3 % 3`. -/
def row251130 (u : Fin 9) : Row251130 :=
  ![⟨u.val % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨u.val / 3 % 3, Nat.mod_lt _ (by norm_num)⟩]

theorem row_injective251130 : Function.Injective row251130 := by
  decide +kernel

theorem row_bijective251130 : Function.Bijective row251130 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective251130, by simp⟩

/-- `Compat251130` on codes. -/
def ok251130 (u v : Fin 9) : Bool :=
  Nat.ble (u.val % 3 + v.val / 3 % 3) (u.val / 3 % 3) ||
  Nat.ble (u.val % 3 + v.val / 3 % 3) (v.val % 3)

theorem ok_iff251130 : ∀ u v : Fin 9,
    Compat251130 (row251130 u) (row251130 v) ↔ ok251130 u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G251130 : ℕ → Fin 9 → ℕ
  | 0, _ => 1
  | m + 1, u => ∑ v : Fin 9, if ok251130 u v then G251130 m v else 0

theorem N_eq_G251130 (m : ℕ) : ∀ u : Fin 9, N251130 m (row251130 u) = G251130 m u := by
  induction m with
  | zero => intro u; rw [N_zero251130]; rfl
  | succ m ih =>
    intro u
    rw [N_succ251130, ← row_bijective251130.sum_comp]
    simp only [G251130]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok_iff251130 u v) rfl rfl

theorem a_eq_G251130 (n : ℕ) : (a (n + 1) : ℤ) = ∑ u : Fin 9, (G251130 (n + 1) u : ℤ) := by
  rw [a_eq_N251130, ← row_bijective251130.sum_comp]
  push_cast
  exact Finset.sum_congr rfl fun u _ => by rw [N_eq_G251130]

/-- `12 * G m u` for `m >= 2` in the basis `1, m, m ^ 2, m ^ 3, 2 ^ m, (-1) ^ m`. -/
def CT251130 : Fin 9 → Fin 6 → ℤ :=
  ![![-78, -36, 0, 0, 92, -2],
    ![12, 24, 0, 0, 0, 0],
    ![12, 0, 0, 0, 0, 0],
    ![-171, -96, -18, 0, 184, -1],
    ![-30, -12, 0, 0, 46, 2],
    ![12, 0, 0, 0, 0, 0],
    ![-531, -324, -90, -12, 529, -1],
    ![-141, -84, -18, 0, 161, 1],
    ![-42, -12, 0, 0, 46, 2]]

/-- The basis values. -/
def W251130 (m : ℕ) : Fin 6 → ℤ :=
  ![1, (m : ℤ), (m : ℤ) ^ 2, (m : ℤ) ^ 3, 2 ^ m, (-1) ^ m]

/-- The coefficients after the shift `m -> m + 1`. -/
def Tn251130 (u : Fin 9) : Fin 6 → ℤ :=
  ![CT251130 u 0 + CT251130 u 1 + CT251130 u 2 + CT251130 u 3,
    CT251130 u 1 + 2 * CT251130 u 2 + 3 * CT251130 u 3,
    CT251130 u 2 + 3 * CT251130 u 3,
    CT251130 u 3,
    2 * CT251130 u 4,
    -CT251130 u 5]

theorem base_facts251130 : ∀ u : Fin 9,
    CT251130 u 0 + 2 * CT251130 u 1 + 4 * CT251130 u 2 + 8 * CT251130 u 3 + 4 * CT251130 u 4 +
      CT251130 u 5 = 12 * (G251130 2 u : ℤ) := by
  decide +kernel

theorem step_facts251130 : ∀ u : Fin 9, ∀ k : Fin 6,
    (∑ v : Fin 9, if ok251130 u v then CT251130 v k else 0) = Tn251130 u k := by
  decide +kernel

theorem shift251130 (u : Fin 9) (m : ℕ) :
    ∑ k : Fin 6, Tn251130 u k * W251130 m k = ∑ k : Fin 6, CT251130 u k * W251130 (m + 1) k := by
  simp only [Fin.sum_univ_six, Tn251130, W251130]
  simp
  ring

theorem G_closed251130 (m : ℕ) : ∀ u : Fin 9,
    12 * (G251130 (m + 2) u : ℤ) = ∑ k : Fin 6, CT251130 u k * W251130 (m + 2) k := by
  induction m with
  | zero =>
    intro u
    simp only [Fin.sum_univ_six, W251130]
    simp
    have := base_facts251130 u
    linarith
  | succ m ih =>
    intro u
    have h1 : 12 * (G251130 (m + 1 + 2) u : ℤ) =
        ∑ v : Fin 9, if ok251130 u v then ∑ k : Fin 6, CT251130 v k * W251130 (m + 2) k
          else 0 := by
      rw [show m + 1 + 2 = (m + 2) + 1 by omega, G251130]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih v
      · simp
    have h2 : ∀ v : Fin 9, (if ok251130 u v then ∑ k : Fin 6, CT251130 v k * W251130 (m + 2) k
        else 0) = ∑ k : Fin 6, (if ok251130 u v then CT251130 v k else 0) * W251130 (m + 2) k := by
      intro v
      split_ifs <;> simp
    rw [h1, Finset.sum_congr rfl fun v _ => h2 v, Finset.sum_comm]
    simp only [← Finset.sum_mul, step_facts251130 u]
    rw [shift251130 u (m + 2)]

/-- Column sums of `CT251130`. -/
def TOT251130 : Fin 6 → ℤ := ![-957, -540, -126, -12, 1058, 1]

theorem tot_facts251130 : ∀ k : Fin 6, (∑ u : Fin 9, CT251130 u k) = TOT251130 k := by
  decide +kernel

theorem a_closedZ251130 (m : ℕ) :
    12 * (a (m + 2) : ℤ) = ∑ k : Fin 6, TOT251130 k * W251130 (m + 2) k := by
  rw [a_eq_G251130, Finset.mul_sum]
  simp only [G_closed251130 m]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, tot_facts251130]

theorem a_one251130 : a 1 = 40 := by
  have h := a_eq_G251130 0
  have h2 : (∑ u : Fin 9, (G251130 (0 + 1) u : ℤ)) = 40 := by decide +kernel
  rw [h2] at h
  exact_mod_cast h

theorem a_closedQ251130 (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) =
    (-957 + (-1 : ℚ) ^ n + 529 * (2 : ℚ) ^ (1 + n) - 540 * n - 126 * (n : ℚ) ^ 2 -
      12 * (n : ℚ) ^ 3) / 12 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one251130]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h := a_closedZ251130 m
    simp only [Fin.sum_univ_six, TOT251130, W251130] at h
    simp at h
    have hq : (12 : ℚ) * (a (m + 2) : ℚ) = -957 + -(540 * ((m : ℚ) + 2)) +
        -(126 * ((m : ℚ) + 2) ^ 2) + -(12 * ((m : ℚ) + 2) ^ 3) + 1058 * 2 ^ (m + 2) +
        (-1) ^ (m + 2) := by
      exact_mod_cast h
    rw [pow_add (2 : ℚ) 1]
    push_cast
    linarith

/-- The closed form as a function. -/
noncomputable def F251130 (n : ℕ) : ℚ :=
  (-957 + (-1 : ℚ) ^ n + 529 * (2 : ℚ) ^ (1 + n) - 540 * n - 126 * (n : ℚ) ^ 2 -
    12 * (n : ℚ) ^ 3) / 12

theorem a_vals251130 : (a 1 : ℚ) = 40 ∧ (a 2 : ℚ) = 133 ∧ (a 3 : ℚ) = 369 ∧
    (a 4 : ℚ) = 919 ∧ (a 5 : ℚ) = 2129 ∧ (a 6 : ℚ) = 4699 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_closedQ251130 _ (by norm_num)] <;> norm_num

theorem recurrence251130 (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℤ) = 5 * a (n - 1) - 8 * a (n - 2) + 2 * a (n - 3) + 7 * a (n - 4) -
      7 * a (n - 5) + 2 * a (n - 6) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 7 := ⟨n - 7, by omega⟩
  simp only [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
    show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
    show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega]
  have key : (a (j + 7) : ℚ) = 5 * a (j + 6) - 8 * a (j + 5) + 2 * a (j + 4) + 7 * a (j + 3) -
      7 * a (j + 2) + 2 * a (j + 1) := by
    rw [a_closedQ251130 (j + 7) (by omega), a_closedQ251130 (j + 6) (by omega),
      a_closedQ251130 (j + 5) (by omega), a_closedQ251130 (j + 4) (by omega),
      a_closedQ251130 (j + 3) (by omega), a_closedQ251130 (j + 2) (by omega),
      a_closedQ251130 (j + 1) (by omega)]
    push_cast
    ring
  exact_mod_cast key

open PowerSeries in
theorem gen_fun251130 :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) * (1 - 2 * X)) =
      X * (40 - 67 * X + 24 * X ^ 2 + 58 * X ^ 3 - 60 * X ^ 4 + 17 * X ^ 5) := by
  set f : ℕ → ℚ := fun n => (a n : ℚ) with hfdef
  have key : PowerSeries.mk f * ((1 - X) ^ 4 * (1 + X) * (1 - 2 * X)) =
      C 1 * (PowerSeries.mk f * X ^ 0) - C 5 * (PowerSeries.mk f * X ^ 1) +
        C 8 * (PowerSeries.mk f * X ^ 2) - C 2 * (PowerSeries.mk f * X ^ 3) -
        C 7 * (PowerSeries.mk f * X ^ 4) + C 7 * (PowerSeries.mk f * X ^ 5) -
        C 2 * (PowerSeries.mk f * X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (40 - 67 * X + 24 * X ^ 2 + 58 * X ^ 3 - 60 * X ^ 4 + 17 * X ^ 5) =
      C 40 * X ^ 1 - C 67 * X ^ 2 + C 24 * X ^ 3 + C 58 * X ^ 4 - C 60 * X ^ 5 +
        C 17 * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hf : ∀ t : ℕ, f (t + 1) = F251130 (t + 1) := by
    intro t
    simp only [hfdef, F251130]
    exact a_closedQ251130 (t + 1) (by omega)
  have h0 : f 0 = 0 := by simp [hfdef, a]
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := a_vals251130
  by_cases hk : k < 7
  · interval_cases k <;>
      simp only [hfdef, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true, if_false,
        v1, v2, v3, v4, v5, v6] <;>
      simp [a] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = (j + 6) + 1 by omega, show j + 7 - 1 = (j + 5) + 1 by omega,
      show j + 7 - 2 = (j + 4) + 1 by omega, show j + 7 - 3 = (j + 3) + 1 by omega,
      show j + 7 - 4 = (j + 2) + 1 by omega, show j + 7 - 5 = (j + 1) + 1 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      if_true, if_false, hf]
    simp only [F251130]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a251130.main :=
  ⟨OMA.Helpers.recurrence251130, OMA.Helpers.gen_fun251130,
    fun n hn => OMA.Helpers.a_closedQ251130 n hn⟩
