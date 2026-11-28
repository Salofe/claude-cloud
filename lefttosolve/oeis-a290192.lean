import OMAStatements.S_oeis_a290192
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a290192 PowerSeries

/-- The pattern of the odd stages from stage 3 on: OFF exactly on the eight cells around the
origin. -/
def a290192_odd (p : ℤ × ℤ) : Bool :=
  !(decide (-1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧ ¬ (p.1 = 0 ∧ p.2 = 0)))

/-- The pattern of the even stages from stage 4 on: OFF exactly on the 3 × 3 square around the
origin. -/
def a290192_even (p : ℤ × ℤ) : Bool :=
  !(decide (-1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1))

/-- The value of the cells far from the origin: OFF at stage 0, ON afterwards. -/
def a290192_bg : ℕ → Bool
  | 0 => false
  | _ + 1 => true

theorem a290192_succ (t : ℕ) (p : ℤ × ℤ) :
    state (t + 1) p = rule (state t p) ((nbrs p).countP (fun q => state t q)) := rfl

theorem a290192_far : ∀ k : ℕ, ∀ x y : ℤ, ((k : ℤ) < x ∨ x < -(k : ℤ) ∨ (k : ℤ) < y ∨ y < -(k : ℤ)) →
    state k (x, y) = a290192_bg k := by
  intro k
  induction k with
  | zero =>
    intro x y h
    simp only [state, a290192_bg, decide_eq_false_iff_not, Prod.mk.injEq]
    push_cast at h
    omega
  | succ k ih =>
    intro x y h
    push_cast at h
    have h1 : state k (x, y) = a290192_bg k := ih x y (by omega)
    have h2 : state k (x + 1, y) = a290192_bg k := ih _ _ (by omega)
    have h3 : state k (x - 1, y) = a290192_bg k := ih _ _ (by omega)
    have h4 : state k (x, y + 1) = a290192_bg k := ih _ _ (by omega)
    have h5 : state k (x, y - 1) = a290192_bg k := ih _ _ (by omega)
    rw [a290192_succ]
    simp only [nbrs, List.countP_cons, List.countP_nil, h1, h2, h3, h4, h5]
    cases k <;> simp only [a290192_bg] <;> decide

theorem a290192_odd_far (x y : ℤ) (h : x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) :
    a290192_odd (x, y) = true := by
  simp only [a290192_odd, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  omega

theorem a290192_even_far (x y : ℤ) (h : x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) :
    a290192_even (x, y) = true := by
  simp only [a290192_even, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  omega

theorem a290192_three : state 3 = a290192_odd := by
  funext p
  obtain ⟨x, y⟩ := p
  by_cases h : (3 : ℤ) < x ∨ x < -3 ∨ (3 : ℤ) < y ∨ y < -3
  · rw [a290192_far 3 x y (by exact_mod_cast h), a290192_odd_far x y (by omega)]
    rfl
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    interval_cases x <;> interval_cases y <;> decide

theorem a290192_step_odd (p : ℤ × ℤ) :
    rule (a290192_odd p) ((nbrs p).countP (fun q => a290192_odd q)) = a290192_even p := by
  obtain ⟨x, y⟩ := p
  by_cases h : x ≤ -3 ∨ 3 ≤ x ∨ y ≤ -3 ∨ 3 ≤ y
  · simp only [nbrs, List.countP_cons, List.countP_nil]
    rw [a290192_odd_far x y (by omega), a290192_odd_far (x + 1) y (by omega),
      a290192_odd_far (x - 1) y (by omega), a290192_odd_far x (y + 1) (by omega),
      a290192_odd_far x (y - 1) (by omega), a290192_even_far x y (by omega)]
    decide
  · have hx1 : -2 ≤ x := by omega
    have hx2 : x ≤ 2 := by omega
    have hy1 : -2 ≤ y := by omega
    have hy2 : y ≤ 2 := by omega
    interval_cases x <;> interval_cases y <;> decide

theorem a290192_step_even (p : ℤ × ℤ) :
    rule (a290192_even p) ((nbrs p).countP (fun q => a290192_even q)) = a290192_odd p := by
  obtain ⟨x, y⟩ := p
  by_cases h : x ≤ -3 ∨ 3 ≤ x ∨ y ≤ -3 ∨ 3 ≤ y
  · simp only [nbrs, List.countP_cons, List.countP_nil]
    rw [a290192_even_far x y (by omega), a290192_even_far (x + 1) y (by omega),
      a290192_even_far (x - 1) y (by omega), a290192_even_far x (y + 1) (by omega),
      a290192_even_far x (y - 1) (by omega), a290192_odd_far x y (by omega)]
    decide
  · have hx1 : -2 ≤ x := by omega
    have hx2 : x ≤ 2 := by omega
    have hy1 : -2 ≤ y := by omega
    have hy2 : y ≤ 2 := by omega
    interval_cases x <;> interval_cases y <;> decide

theorem a290192_stages (j : ℕ) :
    state (2 * j + 3) = a290192_odd ∧ state (2 * j + 4) = a290192_even := by
  induction j with
  | zero =>
    refine ⟨a290192_three, ?_⟩
    funext p
    rw [a290192_succ, a290192_three]
    exact a290192_step_odd p
  | succ j ih =>
    have e1 : state (2 * (j + 1) + 3) = a290192_odd := by
      funext p
      rw [show 2 * (j + 1) + 3 = (2 * j + 4) + 1 by ring, a290192_succ, ih.2]
      exact a290192_step_even p
    refine ⟨e1, ?_⟩
    funext p
    rw [show 2 * (j + 1) + 4 = (2 * (j + 1) + 3) + 1 by ring, a290192_succ, e1]
    exact a290192_step_odd p

/-- The partial geometric sum 10^2 + ... + 10^(m+2). -/
theorem a290192_geom (m : ℕ) :
    9 * (∑ i ∈ Finset.range (m + 1), 10 ^ (i + 2)) + 100 = 10 ^ (m + 3) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih]
    ring

/-- The closed form from stage 3 on: the diagonal is all ON except the cell (1,1), and the
origin at even stages. -/
theorem a290192_closed (n : ℕ) (hn : 3 ≤ n) : 9 * a n + 100 = 10 ^ (n + 1) + 9 * (n % 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hst : state (m + 2) = a290192_odd ∨ state (m + 2) = a290192_even := by
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      right
      rw [show 2 * (j' + 1) + 2 = 2 * j' + 4 by ring]
      exact (a290192_stages j').2
    · left
      rw [show 2 * j + 1 + 2 = 2 * j + 3 by ring]
      exact (a290192_stages j).1
  have hfar : ∀ i : ℕ, state (m + 2) (((i + 2 : ℕ) : ℤ), ((i + 2 : ℕ) : ℤ)) = true := by
    intro i
    rcases hst with h | h <;> rw [h]
    · exact a290192_odd_far _ _ (by push_cast; omega)
    · exact a290192_even_far _ _ (by push_cast; omega)
  unfold a
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hsum : (∑ i ∈ Finset.range (m + 1),
      if state (m + 2) (((i + 1 + 1 : ℕ) : ℤ), ((i + 1 + 1 : ℕ) : ℤ)) then 10 ^ (i + 1 + 1) else 0)
      = ∑ i ∈ Finset.range (m + 1), 10 ^ (i + 2) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [if_pos (hfar i)]
  rw [hsum]
  have hg : 9 * (∑ i ∈ Finset.range (m + 1), 10 ^ (i + 2)) + 100 = 10 ^ (m + 2 + 1) := by
    rw [show m + 2 + 1 = m + 3 by ring]
    exact a290192_geom m
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hs : state (m + 2) = a290192_even := by
      rw [show m + 2 = 2 * (j - 1) + 4 by omega]
      exact (a290192_stages (j - 1)).2
    have g1 : a290192_even (((0 + 1 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ)) = false := by decide
    have g0 : a290192_even (((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) = false := by decide
    have hm : (m + 2) % 2 = 0 := by omega
    rw [hs, g1, g0, hm]
    simp only [Bool.false_eq_true, if_false]
    omega
  · have hs : state (m + 2) = a290192_odd := by
      rw [show m + 2 = 2 * j + 3 by omega]
      exact (a290192_stages j).1
    have g1 : a290192_odd (((0 + 1 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ)) = false := by decide
    have g0 : a290192_odd (((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) = true := by decide
    have hm : (m + 2) % 2 = 1 := by omega
    rw [hs, g1, g0, hm]
    simp only [Bool.false_eq_true, if_false, if_true, pow_zero]
    omega

theorem a290192_small : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 101 := by
  decide

theorem a290192_rec (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega]
  have h6 := a290192_closed (m + 6) (by omega)
  have h5 := a290192_closed (m + 5) (by omega)
  have h4 := a290192_closed (m + 4) (by omega)
  have h3 := a290192_closed (m + 3) (by omega)
  have e64 : (m + 6) % 2 = (m + 4) % 2 := by omega
  have e53 : (m + 5) % 2 = (m + 3) % 2 := by omega
  rw [e64] at h6
  rw [e53] at h5
  have z6 : (9 * (a (m + 6) : ℤ)) + 100 = 10 ^ (m + 7) + 9 * (((m + 4) % 2 : ℕ) : ℤ) := by
    exact_mod_cast h6
  have z5 : (9 * (a (m + 5) : ℤ)) + 100 = 10 ^ (m + 6) + 9 * (((m + 3) % 2 : ℕ) : ℤ) := by
    exact_mod_cast h5
  have z4 : (9 * (a (m + 4) : ℤ)) + 100 = 10 ^ (m + 5) + 9 * (((m + 4) % 2 : ℕ) : ℤ) := by
    exact_mod_cast h4
  have z3 : (9 * (a (m + 3) : ℤ)) + 100 = 10 ^ (m + 4) + 9 * (((m + 3) % 2 : ℕ) : ℤ) := by
    exact_mod_cast h3
  have key : (9 : ℤ) * ((a (m + 6) : ℤ) - (10 * a (m + 5) + a (m + 4) - 10 * a (m + 3))) = 0 := by
    linear_combination z6 - 10 * z5 - z4 + 10 * z3
  omega

theorem a290192_gf_mul :
    A * ((X - 1) * (X + 1) * (10 * X - 1)) = 10 * X ^ 5 + 89 * X ^ 4 + 91 * X ^ 3 + 1 := by
  obtain ⟨h0, h1, h2⟩ := a290192_small
  have c3 := a290192_closed 3 le_rfl
  have c4 := a290192_closed 4 (by norm_num)
  have c5 := a290192_closed 5 (by norm_num)
  norm_num at c3 c4 c5
  have h3 : a 3 = 1101 := by omega
  have h4 : a 4 = 11100 := by omega
  have h5 : a 5 = 111101 := by omega
  have e1 : A * ((X - 1) * (X + 1) * (10 * X - 1))
      = A - C (10 : ℚ) * (A * X ^ 1) - A * X ^ 2 + C (10 : ℚ) * (A * X ^ 3) := by
    simp only [map_ofNat]
    ring
  have e2 : (10 * X ^ 5 + 89 * X ^ 4 + 91 * X ^ 3 + 1 : ℚ⟦X⟧)
      = X ^ 0 + C (91 : ℚ) * X ^ 3 + C (89 : ℚ) * X ^ 4 + C (10 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> simp [h0, h1, h2, h3, h4, h5] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    have hr := a290192_rec (m + 6) (by omega)
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega] at hr
    have c1 : 1 ≤ m + 6 := by omega
    have c2 : 2 ≤ m + 6 := by omega
    have c3' : 3 ≤ m + 6 := by omega
    have c4' : 4 ≤ m + 6 := by omega
    have c5' : 5 ≤ m + 6 := by omega
    have d0 : m + 6 ≠ 0 := by omega
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega]
    have e3 : m + 3 ≠ 0 := by omega
    have e2' : m + 2 ≠ 0 := by omega
    have e1' : m + 1 ≠ 0 := by omega
    simp only [c1, c2, c3', c4', c5', d0, e3, e2', e1', if_true, if_false]
    have hq : ((a (m + 6) : ℤ) : ℚ) = ((10 * a (m + 5) + a (m + 4) - 10 * a (m + 3) : ℤ) : ℚ) := by
      rw [hr]
    push_cast at hq
    rw [hq]
    ring

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a290192.main := by
  refine ⟨a290192_rec, ?_⟩
  have hD : constantCoeff ((X - 1) * (X + 1) * (10 * X - 1) : ℚ⟦X⟧) ≠ 0 := by
    simp
  exact (eq_mul_inv_iff_mul_eq hD).mpr a290192_gf_mul
