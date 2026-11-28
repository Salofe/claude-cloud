import OMAStatements.S_oeis_a205220
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a205220 Finset

/-- A row of the array. -/
abbrev A205220Row := Fin 3 → Fin 2

/-- The number of equal diagonal and antidiagonal pairs of the block of rows `x` (top), `y`. -/
def a205220bn (x y : A205220Row) (j j' : Fin 3) : ℕ :=
  (if x j = y j' then 1 else 0) + (if x j' = y j then 1 else 0)

/-- The horizontal condition on two consecutive rows. -/
def a205220H (x y : A205220Row) : Prop := a205220bn x y 0 1 ≠ a205220bn x y 1 2

/-- The vertical condition on three consecutive rows. -/
def a205220V (x y z : A205220Row) : Prop :=
  a205220bn x y 0 1 ≠ a205220bn y z 0 1 ∧ a205220bn x y 1 2 ≠ a205220bn y z 1 2

/-- All horizontal and vertical conditions along the rows of `A`. -/
def a205220Chain {m : ℕ} (A : Fin m → A205220Row) : Prop :=
  (∀ (i : ℕ) (h : i + 1 < m), a205220H (A ⟨i, by omega⟩) (A ⟨i + 1, h⟩)) ∧
    ∀ (i : ℕ) (h : i + 2 < m),
      a205220V (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem a205220_cond_iff {m : ℕ} (A : Fin m → A205220Row) : Cond A ↔ a205220Chain A := by
  constructor
  · rintro ⟨hH, hV⟩
    refine ⟨fun i h => ?_, fun i h => ?_⟩
    · exact hH ⟨i, by omega⟩ ⟨i + 1, h⟩ 0 1 2 rfl rfl rfl
    · exact ⟨hV ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, h⟩ 0 1 rfl rfl rfl,
        hV ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, h⟩ 1 2 rfl rfl rfl⟩
  · rintro ⟨hH, hV⟩
    refine ⟨?_, ?_⟩
    · intro i i' j j' j'' hi hj hj'
      have h2 := j''.isLt
      have ej : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      have ej' : j' = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
      have ej'' : j'' = 2 := Fin.ext (by simp only [Fin.val_two]; omega)
      have ei' : i' = ⟨i.val + 1, by omega⟩ := Fin.ext hi
      subst ej ej' ej''
      rw [ei']
      exact hH i.val (by omega)
    · intro i i' i'' j j' hi hi' hj
      rcases i' with ⟨i', h1'⟩
      rcases i'' with ⟨i'', h2'⟩
      simp only at hi hi'
      subst hi
      subst hi'
      have h1 := j'.isLt
      rcases Nat.lt_or_ge j.val 1 with hj0 | hj0
      · have ej : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
        have ej' : j' = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
        subst ej ej'
        exact (hV i.val (by omega)).1
      · have ej : j = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
        have ej' : j' = 2 := Fin.ext (by simp only [Fin.val_two]; omega)
        subst ej ej'
        exact (hV i.val (by omega)).2

theorem a205220_rmn_iff {k : ℕ} (A : Fin (k + 1) → A205220Row) :
    RowMajorNew A ↔ A 0 0 = 0 := by
  constructor
  · intro h
    by_contra h0
    have h1 : (0 : Fin 2) < A 0 0 := by
      rcases Fin.eq_zero_or_eq_succ (A 0 0) with e | ⟨j, e⟩
      · exact absurd e h0
      · rw [e]; exact Fin.succ_pos j
    obtain ⟨i', j', hlt, _⟩ := h 0 0 0 h1
    rcases hlt with hlt | ⟨_, hlt⟩
    · exact absurd hlt (Fin.not_lt_zero i')
    · exact absurd hlt (Fin.not_lt_zero j')
  · intro h i j u hu
    have hu0 : u = 0 := by
      have := u.isLt; have := (A i j).isLt
      exact Fin.ext (by rw [Fin.lt_def] at hu; simp only [Fin.val_zero]; omega)
    subst hu0
    refine ⟨0, 0, ?_, h⟩
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj; rw [h] at hu; exact absurd hu (lt_irrefl _)
      · right; exact ⟨rfl, Fin.pos_iff_ne_zero.mpr hj⟩
    · left; exact Fin.pos_iff_ne_zero.mpr hi

instance a205220decH (x y : A205220Row) : Decidable (a205220H x y) := by
  unfold a205220H; infer_instance

instance a205220decV (x y z : A205220Row) : Decidable (a205220V x y z) := by
  unfold a205220V; infer_instance

theorem a205220_chain_cons {m : ℕ} (x : A205220Row) (B : Fin (m + 2) → A205220Row) :
    a205220Chain (Fin.cons x B : Fin (m + 3) → A205220Row) ↔
      a205220H x (B ⟨0, by omega⟩) ∧ a205220V x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) ∧
        a205220Chain B := by
  constructor
  · rintro ⟨hH, hV⟩
    have h0 := hH 0 (by omega)
    have h1 := hV 0 (by omega)
    exact ⟨h0, h1, fun i hi => hH (i + 1) (by omega), fun i hi => hV (i + 1) (by omega)⟩
  · rintro ⟨h0, h1, hH, hV⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · cases i with
      | zero => exact h0
      | succ i => exact hH i (by omega)
    · cases i with
      | zero => exact h1
      | succ i => exact hV i (by omega)

/-- The number of ways to continue the rows `x, y` by `m` more rows (the pair `x, y` itself
must satisfy the horizontal condition). -/
noncomputable def a205220T (m : ℕ) (x y : A205220Row) : ℕ := by
  classical
  exact ∑ B : Fin m → A205220Row,
    if a205220Chain (Fin.cons x (Fin.cons y B) : Fin (m + 2) → A205220Row) then 1 else 0

theorem a205220T_zero (x y : A205220Row) : a205220T 0 x y = if a205220H x y then 1 else 0 := by
  classical
  unfold a205220T
  rw [Fintype.sum_unique]
  refine if_congr ⟨fun h => ?_, fun h => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩ rfl rfl
  · have h0 := h.1 0 (by omega)
    exact h0
  · obtain rfl : i = 0 := by omega
    exact h
  · omega

theorem a205220T_succ (m : ℕ) (x y : A205220Row) :
    a205220T (m + 1) x y = if a205220H x y then
      ∑ z : A205220Row, (if a205220V x y z then a205220T m y z else 0) else 0 := by
  classical
  unfold a205220T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => A205220Row).symm _
    (fun p => if a205220Chain (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) :
      Fin (m + 3) → A205220Row) then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  by_cases hh : a205220H x y
  · rw [if_pos hh]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hv : a205220V x y z
    · rw [if_pos hv]
      refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
      rw [a205220_chain_cons]
      exact ⟨fun h => h.2.2, fun h => ⟨hh, hv, h⟩⟩
    · rw [if_neg hv]
      refine Finset.sum_eq_zero fun B _ => if_neg ?_
      rw [a205220_chain_cons]
      exact fun h => hv h.2.1
  · rw [if_neg hh]
    refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [a205220_chain_cons]
    exact fun h => hh h.1

theorem a205220_a_eq (m : ℕ) :
    a (m + 1) = ∑ x : A205220Row, ∑ y : A205220Row, if x 0 = 0 then a205220T m x y else 0 := by
  classical
  have h1 : a (m + 1) = ∑ A : Fin (m + 2) → A205220Row,
      if a205220Chain A ∧ A 0 0 = 0 then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ =>
      if_congr (and_congr (a205220_cond_iff A) (a205220_rmn_iff A)) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => A205220Row).symm _
    (fun p => if a205220Chain (Fin.cons p.1 p.2 : Fin (m + 2) → A205220Row) ∧ p.1 0 = 0
      then 1 else 0) (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => A205220Row).symm _
    (fun p => if a205220Chain (Fin.cons x (Fin.cons p.1 p.2) : Fin (m + 2) → A205220Row) ∧
      x 0 = 0 then 1 else 0) (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : x 0 = 0
  · rw [if_pos hx]
    unfold a205220T
    exact Finset.sum_congr rfl fun B _ => if_congr (and_iff_left hx) rfl rfl
  · rw [if_neg hx]
    exact Finset.sum_eq_zero fun B _ => if_neg fun h => hx h.2

/-- The row with code `c`: the bits of `c`, most significant first. -/
def a205220row (c : Fin 8) : A205220Row :=
  fun j => ⟨c.val / 2 ^ (2 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem a205220row_bijective : Function.Bijective a205220row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by simp⟩

/-- Bit `j` of the code `u`. -/
def a205220bt (u j : ℕ) : ℕ := u / 2 ^ (2 - j) % 2

/-- `a205220bn` on codes. -/
def a205220bnc (u v j j' : ℕ) : ℕ :=
  (if a205220bt u j = a205220bt v j' then 1 else 0) +
    (if a205220bt u j' = a205220bt v j then 1 else 0)

/-- The horizontal condition on codes. -/
def a205220Ht (u v : Fin 8) : Bool := !(a205220bnc u v 0 1 == a205220bnc u v 1 2)

/-- The vertical condition on codes. -/
def a205220Vt (u v w : Fin 8) : Bool :=
  !(a205220bnc u v 0 1 == a205220bnc v w 0 1) && !(a205220bnc u v 1 2 == a205220bnc v w 1 2)

theorem a205220_H_iff : ∀ u v : Fin 8,
    a205220H (a205220row u) (a205220row v) ↔ a205220Ht u v = true := by
  decide +kernel

theorem a205220_V_iff : ∀ u v w : Fin 8,
    a205220V (a205220row u) (a205220row v) (a205220row w) ↔ a205220Vt u v w = true := by
  decide +kernel

theorem a205220_top_iff : ∀ u : Fin 8, a205220row u 0 = 0 ↔ u.val < 4 := by
  decide +kernel

/-- The transfer recursion on codes. -/
def a205220G : ℕ → Fin 8 → Fin 8 → ℕ
  | 0, u, v => if a205220Ht u v then 1 else 0
  | m + 1, u, v => if a205220Ht u v then
      ∑ w : Fin 8, (if a205220Vt u v w then a205220G m v w else 0) else 0

theorem a205220G_succ (m : ℕ) (u v : Fin 8) : a205220G (m + 1) u v = if a205220Ht u v then
    ∑ w : Fin 8, (if a205220Vt u v w then a205220G m v w else 0) else 0 := rfl

theorem a205220T_eq_G (m : ℕ) : ∀ u v : Fin 8,
    a205220T m (a205220row u) (a205220row v) = a205220G m u v := by
  induction m with
  | zero =>
    intro u v
    rw [a205220T_zero]
    exact if_congr (a205220_H_iff u v) rfl rfl
  | succ m ih =>
    intro u v
    rw [a205220T_succ, a205220G_succ, ← a205220row_bijective.sum_comp]
    refine if_congr (a205220_H_iff u v) (Finset.sum_congr rfl fun w _ => ?_) rfl
    rw [ih v w]
    exact if_congr (a205220_V_iff u v w) rfl rfl

theorem a205220_a_eq_G (m : ℕ) :
    a (m + 1) = ∑ u : Fin 8, ∑ v : Fin 8, if u.val < 4 then a205220G m u v else 0 := by
  rw [a205220_a_eq, ← a205220row_bijective.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← a205220row_bijective.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [a205220T_eq_G m u v]
  exact if_congr (a205220_top_iff u) rfl rfl

theorem a205220_G_base : ∀ u v : Fin 8,
    a205220G 3 u v = a205220G 2 u v + 4 * a205220G 1 u v := by
  decide +kernel

theorem a205220_G_rec (m : ℕ) (hm : 1 ≤ m) : ∀ u v : Fin 8,
    a205220G (m + 2) u v = a205220G (m + 1) u v + 4 * a205220G m u v := by
  induction m, hm using Nat.le_induction with
  | base => exact a205220_G_base
  | succ m hm ih =>
    intro u v
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 1 = (m + 1) + 1 by omega,
      a205220G_succ (m + 2), a205220G_succ (m + 1), a205220G_succ m]
    by_cases hh : a205220Ht u v
    · simp only [hh, if_true]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hv : a205220Vt u v w
      · simp only [hv, if_true]; exact ih v w
      · simp only [hv]; simp
    · simp only [hh]; simp

theorem a205220_a1 : a 1 = 20 := by
  rw [a205220_a_eq_G]; decide +kernel

theorem a205220_a2 : a 2 = 52 := by
  rw [a205220_a_eq_G]; decide +kernel

theorem a205220_a3 : a 3 = 132 := by
  rw [a205220_a_eq_G]; decide +kernel

theorem a205220_rec (n : ℕ) (hn : 1 ≤ n) : a (n + 2) = a (n + 1) + 4 * a n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a205220_a1, a205220_a2, a205220_a3]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 + 2 = (k + 3) + 1 by omega, show k + 2 + 1 = (k + 2) + 1 by omega,
      show k + 2 = (k + 1) + 1 by omega, a205220_a_eq_G, a205220_a_eq_G, a205220_a_eq_G,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hu : u.val < 4
    · simp only [hu, if_true]
      exact a205220_G_rec (k + 1) (by omega) u v
    · simp only [hu, if_false]
      norm_num

/-- The closed form of the statement. -/
noncomputable def a205220f (n : ℕ) : ℝ :=
  (2 ^ (2 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) +
    (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17

theorem a205220_f_rec (n : ℕ) : a205220f (n + 2) = a205220f (n + 1) + 4 * a205220f n := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 17 with hsdef
  have hz1 : (2 : ℝ) ^ (2 - ((n + 1 : ℕ) : ℤ)) = 2 ^ (2 - (n : ℤ)) / 2 := by
    rw [show (2 : ℤ) - ((n + 1 : ℕ) : ℤ) = (2 - (n : ℤ)) - 1 by push_cast; ring,
      zpow_sub₀ two_ne_zero, zpow_one]
  have hz2 : (2 : ℝ) ^ (2 - ((n + 2 : ℕ) : ℤ)) = 2 ^ (2 - (n : ℤ)) / 4 := by
    rw [show (2 : ℤ) - ((n + 2 : ℕ) : ℤ) = (2 - (n : ℤ)) - 2 by push_cast; ring,
      zpow_sub₀ two_ne_zero]
    norm_num
  have ha : (1 + s) ^ 2 = 2 * (1 + s) + 16 := by linear_combination hs
  have hb : (1 - s) ^ 2 = 2 * (1 - s) + 16 := by linear_combination hs
  unfold a205220f
  rw [hz1, hz2, pow_add (1 - s) n 2, pow_add (1 + s) n 2, pow_succ (1 - s) n,
    pow_succ (1 + s) n, ha, hb]
  ring

theorem a205220_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = a205220f n := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 17 ≠ 0 := by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · rw [a205220_a1, a205220f, eq_div_iff hs0]
        norm_num
        ring
      · rw [a205220_a2, a205220f, eq_div_iff hs0]
        norm_num
        linear_combination (-2 * Real.sqrt 17) * hs
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [a205220_rec k (by omega), a205220_f_rec, Nat.cast_add, Nat.cast_mul,
        ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)]
      norm_num

theorem a205220_recQ (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 2) : ℚ) = a (n + 1) + 4 * a n := by
  rw [a205220_rec n hn]; push_cast; ring

open PowerSeries in
theorem a205220_gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X - 4 * X ^ 2) =
      4 * X * (5 + 8 * X) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X - 4 * X ^ 2) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 1 * (PowerSeries.mk F * X ^ 1) -
        C 4 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (4 * X * (5 + 8 * X) : ℚ⟦X⟧) = C 20 * X ^ 1 + C 32 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [hF, a205220_a1, a205220_a2]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show j + 3 - 0 = j + 3 by omega, show j + 3 - 1 = j + 2 by omega,
      show j + 3 - 2 = j + 1 by omega,
      show ¬ (j + 3 = 1) by omega, show ¬ (j + 3 = 2) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    rw [show j + 3 = (j + 1) + 2 by omega, a205220_recQ (j + 1) (by omega)]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a205220.main :=
  ⟨OMA.Helpers.a205220_gen_fun, fun n hn => (OMA.Helpers.a205220_closed n hn).trans rfl⟩
