import OMAStatements.S_oeis_a279960
import Mathlib

/-!
Proof of the four conjectures of OEIS A279960 (Rule 221 x-axis).

Rule 221 turns the empty plane into the full plane and back, and from stage 3 on the
automaton alternates between two configurations: odd stages are ON except on the plus of
radius 1 around the origin, even stages are exactly the plus of radius 2. Each step is checked
far away through the background and near the origin by a finite computation. The closed forms,
the recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a279960

/-- Stage 1: everything ON except the origin. -/
def a279960_g1 (p : ℤ × ℤ) : Bool := !(decide (p.1 = 0 ∧ p.2 = 0))

/-- Stage 2: exactly the four neighbours of the origin. -/
def a279960_g2 (p : ℤ × ℤ) : Bool :=
  decide ((p.2 = 0 ∧ (p.1 = 1 ∨ p.1 = -1)) ∨ (p.1 = 0 ∧ (p.2 = 1 ∨ p.2 = -1)))

/-- Odd stages from 3 on: everything ON except the plus of radius 1. -/
def a279960_go (p : ℤ × ℤ) : Bool :=
  !(decide ((p.2 = 0 ∧ -1 ≤ p.1 ∧ p.1 ≤ 1) ∨ (p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1)))

/-- Even stages from 4 on: exactly the plus of radius 2. -/
def a279960_ge (p : ℤ × ℤ) : Bool :=
  decide ((p.2 = 0 ∧ -2 ≤ p.1 ∧ p.1 ≤ 2) ∨ (p.1 = 0 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2))

/-- One step of the automaton applied to an arbitrary configuration. -/
def a279960_step (f : ℤ × ℤ → Bool) (p : ℤ × ℤ) : Bool :=
  rule (f p) ((nbrs p).countP (fun q => f q))

theorem a279960_state_succ (t : ℕ) : state (t + 1) = a279960_step (state t) := by
  funext p
  rfl

/-- A step is determined far away by the background and near the origin by a finite check. -/
theorem a279960_trans (f f' : ℤ × ℤ → Bool) (b b' : Bool) (R : ℤ)
    (hf : ∀ x y : ℤ, (R < x ∨ x < -R ∨ R < y ∨ y < -R) → f (x, y) = b)
    (hf' : ∀ x y : ℤ, (R + 1 < x ∨ x < -(R + 1) ∨ R + 1 < y ∨ y < -(R + 1)) → f' (x, y) = b')
    (hb : rule b ([b, b, b, b].countP (fun q => q)) = b')
    (hnear : ∀ x y : ℤ, -(R + 1) ≤ x → x ≤ R + 1 → -(R + 1) ≤ y → y ≤ R + 1 →
      a279960_step f (x, y) = f' (x, y)) :
    a279960_step f = f' := by
  funext p
  obtain ⟨x, y⟩ := p
  by_cases h : -(R + 1) ≤ x ∧ x ≤ R + 1 ∧ -(R + 1) ≤ y ∧ y ≤ R + 1
  · exact hnear x y h.1 h.2.1 h.2.2.1 h.2.2.2
  · have hfar : R + 1 < x ∨ x < -(R + 1) ∨ R + 1 < y ∨ y < -(R + 1) := by omega
    rw [hf' x y hfar]
    have e0 : f (x, y) = b := hf x y (by omega)
    have e1 : f (x + 1, y) = b := hf _ _ (by omega)
    have e2 : f (x - 1, y) = b := hf _ _ (by omega)
    have e3 : f (x, y + 1) = b := hf _ _ (by omega)
    have e4 : f (x, y - 1) = b := hf _ _ (by omega)
    have hc : (nbrs (x, y)).countP (fun q => f q) = [b, b, b, b].countP (fun q => q) := by
      simp only [nbrs, List.countP_cons, List.countP_nil, e1, e2, e3, e4]
    unfold a279960_step
    rw [e0, hc]
    exact hb

theorem a279960_s1 : state 1 = a279960_g1 := by
  rw [a279960_state_succ]
  refine a279960_trans _ _ false true 0 ?_ ?_ (by decide) ?_
  · intro x y h
    show decide ((x, y) = ((0 : ℤ), (0 : ℤ))) = false
    simp only [decide_eq_false_iff_not, Prod.mk.injEq]
    omega
  · intro x y h
    simp only [a279960_g1, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega
  · intro x y h1 h2 h3 h4
    interval_cases x <;> interval_cases y <;> decide

theorem a279960_s2 : state 2 = a279960_g2 := by
  rw [a279960_state_succ, a279960_s1]
  refine a279960_trans _ _ true false 0 ?_ ?_ (by decide) ?_
  · intro x y h
    simp only [a279960_g1, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega
  · intro x y h
    simp only [a279960_g2, decide_eq_false_iff_not]
    omega
  · intro x y h1 h2 h3 h4
    interval_cases x <;> interval_cases y <;> decide

theorem a279960_s3 : state 3 = a279960_go := by
  rw [a279960_state_succ, a279960_s2]
  refine a279960_trans _ _ false true 1 ?_ ?_ (by decide) ?_
  · intro x y h
    simp only [a279960_g2, decide_eq_false_iff_not]
    omega
  · intro x y h
    simp only [a279960_go, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega
  · intro x y h1 h2 h3 h4
    interval_cases x <;> interval_cases y <;> decide

theorem a279960_oe : a279960_step a279960_go = a279960_ge := by
  refine a279960_trans _ _ true false 2 ?_ ?_ (by decide) ?_
  · intro x y h
    simp only [a279960_go, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega
  · intro x y h
    simp only [a279960_ge, decide_eq_false_iff_not]
    omega
  · intro x y h1 h2 h3 h4
    interval_cases x <;> interval_cases y <;> decide

theorem a279960_eo : a279960_step a279960_ge = a279960_go := by
  refine a279960_trans _ _ false true 2 ?_ ?_ (by decide) ?_
  · intro x y h
    simp only [a279960_ge, decide_eq_false_iff_not]
    omega
  · intro x y h
    simp only [a279960_go, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega
  · intro x y h1 h2 h3 h4
    interval_cases x <;> interval_cases y <;> decide

theorem a279960_cycle (m : ℕ) : state (2 * m + 3) = a279960_go ∧ state (2 * m + 4) = a279960_ge := by
  induction m with
  | zero =>
    refine ⟨a279960_s3, ?_⟩
    rw [a279960_state_succ, a279960_s3, a279960_oe]
  | succ m ih =>
    have h1 : state (2 * (m + 1) + 3) = a279960_go := by
      rw [show 2 * (m + 1) + 3 = (2 * m + 4) + 1 by ring, a279960_state_succ, ih.2, a279960_eo]
    refine ⟨h1, ?_⟩
    rw [show 2 * (m + 1) + 4 = (2 * (m + 1) + 3) + 1 by ring, a279960_state_succ, h1, a279960_oe]


theorem a279960_a_odd (m : ℕ) : a (2 * m + 3) = ∑ k ∈ Finset.range (2 * m + 2), 10 ^ k := by
  unfold a
  rw [(a279960_cycle m).1, Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : a279960_go (((0 : ℕ) : ℤ), 0) = false := by decide
  have h1 : a279960_go ((((0 : ℕ) + 1 : ℕ) : ℤ), 0) = false := by decide
  have h2 : ∀ k : ℕ, a279960_go ((((k + 1 + 1 : ℕ)) : ℤ), 0) = true := by
    intro k
    simp only [a279960_go, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    push_cast
    omega
  rw [h0, h1]
  simp only [h2, Bool.false_eq_true, ↓reduceIte, add_zero]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  congr 1
  omega

theorem a279960_a_even (m : ℕ) : a (2 * m + 4) = 111 * 10 ^ (2 * m + 2) := by
  unfold a
  rw [(a279960_cycle m).2, Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_range_succ']
  have h0 : a279960_ge (((0 : ℕ) : ℤ), 0) = true := by decide
  have h1 : a279960_ge ((((0 : ℕ) + 1 : ℕ) : ℤ), 0) = true := by decide
  have h2 : a279960_ge (((((0 : ℕ) + 1 + 1 : ℕ)) : ℤ), 0) = true := by decide
  have h3 : ∀ k : ℕ, a279960_ge ((((k + 1 + 1 + 1 : ℕ)) : ℤ), 0) = false := by
    intro k
    simp only [a279960_ge, decide_eq_false_iff_not]
    push_cast
    omega
  rw [h0, h1, h2]
  simp only [h3, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero, zero_add]
  rw [show 2 * m + 4 - (0 + 1 + 1) = 2 * m + 2 by omega, show 2 * m + 4 - (0 + 1) = 2 * m + 2 + 1 by omega,
    show 2 * m + 4 - 0 = 2 * m + 2 + 2 by omega]
  ring

theorem a279960_q_odd (m : ℕ) : (a (2 * m + 3) : ℚ) * 9 = 10 ^ (2 * m + 2) - 1 := by
  rw [a279960_a_odd m]
  push_cast
  have := geom_sum_mul (10 : ℚ) (2 * m + 2)
  norm_num at this
  exact this

theorem a279960_q_even (m : ℕ) : (a (2 * m + 4) : ℚ) = 111 * 10 ^ (2 * m + 2) := by
  rw [a279960_a_even m]
  push_cast
  ring

theorem a279960_small : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 10 := by
  decide

open PowerSeries in
theorem a279960_gf_aux (g : ℕ → ℚ) (h0 : g 0 = 1) (h1 : g 1 = 1) (h2 : g 2 = 10) (h3 : g 3 = 11)
    (h4 : g 4 = 11100) (h5 : g 5 = 1111) (h6 : g 6 = 1110000)
    (hr : ∀ n : ℕ, 7 ≤ n → g n = 101 * g (n - 2) - 100 * g (n - 4)) :
    PowerSeries.mk g * (1 - 101 * X ^ 2 + 100 * X ^ 4 : ℚ⟦X⟧) =
      1 + X - 91 * X ^ 2 - 90 * X ^ 3 + 10190 * X ^ 4 + 100 * X ^ 5 - 10100 * X ^ 6 := by
  have e1 : PowerSeries.mk g * (1 - 101 * X ^ 2 + 100 * X ^ 4 : ℚ⟦X⟧)
      = PowerSeries.mk g - C (101 : ℚ) * (PowerSeries.mk g * X ^ 2)
        + C (100 : ℚ) * (PowerSeries.mk g * X ^ 4) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 + X - 91 * X ^ 2 - 90 * X ^ 3 + 10190 * X ^ 4 + 100 * X ^ 5 - 10100 * X ^ 6 : ℚ⟦X⟧)
      = C (1 : ℚ) * X ^ 0 + C (1 : ℚ) * X ^ 1 - C (91 : ℚ) * X ^ 2 - C (90 : ℚ) * X ^ 3
        + C (10190 : ℚ) * X ^ 4 + C (100 : ℚ) * X ^ 5 - C (10100 : ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge k 7 with hk | hk
  · interval_cases k <;> simp [h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · have c2 : 2 ≤ k := by omega
    have c4 : 4 ≤ k := by omega
    have d0 : k ≠ 0 := by omega
    have d1 : k ≠ 1 := by omega
    have d2 : k ≠ 2 := by omega
    have d3 : k ≠ 3 := by omega
    have d4 : k ≠ 4 := by omega
    have d5 : k ≠ 5 := by omega
    have d6 : k ≠ 6 := by omega
    simp only [c2, c4, d0, d1, d2, d3, d4, d5, d6, if_true, if_false]
    rw [hr k hk]
    ring

theorem a279960_first3 :
    (∀ n : ℕ, 2 < n → Even n → (a n : ℚ) = (989 * (-10) ^ n + 1009 * 10 ^ n) / 1800) ∧
    (∀ n : ℕ, 2 < n → Odd n → (a n : ℚ) = (989 * (-10) ^ n + 1009 * 10 ^ n - 200) / 1800) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn he
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := by
      obtain ⟨r, hr⟩ := he
      exact ⟨r - 2, by omega⟩
    rw [a279960_q_even m, Even.neg_pow ⟨m + 2, by ring⟩]
    ring
  · intro n hn ho
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := by
      obtain ⟨r, hr⟩ := ho
      exact ⟨r - 1, by omega⟩
    rw [Odd.neg_pow ⟨m + 1, by ring⟩]
    have := a279960_q_odd m
    linear_combination (1 / 9 : ℚ) * this
  · intro n hn
    have key : (a n : ℚ) = 101 * a (n - 2) - 100 * a (n - 4) := by
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 8 := by
          obtain ⟨r, hr⟩ := he
          exact ⟨r - 4, by omega⟩
        rw [show 2 * j + 8 - 2 = 2 * (j + 1) + 4 by omega, show 2 * j + 8 - 4 = 2 * j + 4 by omega,
          show 2 * j + 8 = 2 * (j + 2) + 4 by omega]
        rw [a279960_q_even, a279960_q_even, a279960_q_even]
        ring
      · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 7 := by
          obtain ⟨r, hr⟩ := ho
          exact ⟨r - 3, by omega⟩
        rw [show 2 * j + 7 - 2 = 2 * (j + 1) + 3 by omega, show 2 * j + 7 - 4 = 2 * j + 3 by omega,
          show 2 * j + 7 = 2 * (j + 2) + 3 by omega]
        have e1 := a279960_q_odd (j + 2)
        have e2 := a279960_q_odd (j + 1)
        have e3 := a279960_q_odd j
        linear_combination (1 / 9 : ℚ) * e1 - (101 / 9 : ℚ) * e2 + (100 / 9 : ℚ) * e3
    exact_mod_cast key

open PowerSeries in
theorem a279960_gf : A = (1 + X - 91 * X ^ 2 - 90 * X ^ 3 + 10190 * X ^ 4 + 100 * X ^ 5 - 10100 * X ^ 6) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ := by
  have hD : constantCoeff ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : ℚ⟦X⟧) ≠ 0 := by
    simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD,
    show ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : ℚ⟦X⟧) = 1 - 101 * X ^ 2 + 100 * X ^ 4 by ring]
  obtain ⟨h0, h1, h2⟩ := a279960_small
  have hrec := a279960_first3.2.2
  refine a279960_gf_aux (fun n => (a n : ℚ)) (by simp [h0]) (by simp [h1]) (by simp [h2])
    ?_ ?_ ?_ ?_ ?_
  · have := a279960_q_odd 0
    norm_num at this
    show (a 3 : ℚ) = 11
    linarith
  · have := a279960_q_even 0
    norm_num at this
    exact this
  · have := a279960_q_odd 1
    norm_num at this
    show (a 5 : ℚ) = 1111
    linarith
  · have := a279960_q_even 1
    norm_num at this
    exact this
  · intro n hn
    have := hrec n (by omega)
    show (a n : ℚ) = 101 * (a (n - 2) : ℚ) - 100 * (a (n - 4) : ℚ)
    exact_mod_cast this

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a279960.main := by
  obtain ⟨h1, h2, h3⟩ := OMA.Helpers.a279960_first3
  exact ⟨h1, h2, h3, OMA.Helpers.a279960_gf⟩
