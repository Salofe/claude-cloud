import OMAStatements.S_oeis_a285648
import Mathlib

/-!
Proof of the conjectures of OEIS A285648 (Rule 73, 5-celled von Neumann neighbourhood).

Rule 73 = 1001001 in binary: a cell with own value c and k ON neighbours becomes ON exactly when
2k + c is one of 0, 3, 6.
* Light cone: a cell at distance |x| + |y| > t from the origin still carries the background
  value after t steps, and the background alternates OFF, ON, OFF, ... (bit 0 of 73 is 1 and
  bit 9 is 0).
* Stage 4: every cell is OFF (checked cell by cell on the square |x|, |y| <= 4; outside it the
  light cone gives the background value, OFF).
* From stage 4 on the plane is uniform, so stage 4 + k is OFF everywhere for even k and ON
  everywhere for odd k.
Hence a(n) = 0 for even n >= 4 and a(n) = 11...1 (n + 1 ones) for odd n >= 4, while
a(0..3) = 1, 1, 100, 11. The recurrence and the generating function follow by computing.
-/

namespace OMA.Helpers
open OMA.S_oeis_a285648 PowerSeries

theorem t_far : ∀ (t : ℕ) (x y : ℤ), (t : ℤ) < |x| + |y| → state t (x, y) = decide (t % 2 = 1) := by
  intro t
  induction t with
  | zero =>
    intro x y h
    simp only [state, Nat.zero_mod, zero_ne_one, decide_false, decide_eq_false_iff_not, Prod.mk.injEq]
    intro ⟨hx, hy⟩
    subst hx; subst hy; simp at h
  | succ t ih =>
    intro x y h
    have h0 := ih x y (by push_cast at h; omega)
    have h1 := ih (x + 1) y (by push_cast at h; cases abs_cases (x+1) <;> cases abs_cases x <;> omega)
    have h2 := ih (x - 1) y (by push_cast at h; cases abs_cases (x-1) <;> cases abs_cases x <;> omega)
    have h3 := ih x (y + 1) (by push_cast at h; cases abs_cases (y+1) <;> cases abs_cases y <;> omega)
    have h4 := ih x (y - 1) (by push_cast at h; cases abs_cases (y-1) <;> cases abs_cases y <;> omega)
    simp only [state, nbrs, List.countP_cons, List.countP_nil, h0, h1, h2, h3, h4]
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have : (t + 1) % 2 = 1 := by omega
      simp only [ht, this]; decide
    · have : (t + 1) % 2 = 0 := by omega
      simp only [ht, this]; decide

theorem t_four : ∀ x y : ℤ, state 4 (x, y) = false := by
  intro x y
  by_cases h : (4 : ℤ) < |x| + |y|
  · have := t_far 4 x y (by exact_mod_cast h)
    simpa using this
  · have hx : -4 ≤ x ∧ x ≤ 4 := by constructor <;> cases abs_cases x <;> cases abs_cases y <;> omega
    have hy : -4 ≤ y ∧ y ≤ 4 := by constructor <;> cases abs_cases x <;> cases abs_cases y <;> omega
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases x <;> interval_cases y <;> decide +kernel


theorem t_tail : ∀ (k : ℕ) (x y : ℤ), state (4 + k) (x, y) = decide (k % 2 = 1) := by
  intro k
  induction k with
  | zero => intro x y; simpa using t_four x y
  | succ k ih =>
    intro x y
    rw [show 4 + (k + 1) = (4 + k) + 1 by omega]
    simp only [state, nbrs, List.countP_cons, List.countP_nil, ih]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have : (k + 1) % 2 = 1 := by omega
      simp only [hk, this]; decide
    · have : (k + 1) % 2 = 0 := by omega
      simp only [hk, this]; decide

theorem t_geom : ∀ N : ℕ, 9 * (∑ m ∈ Finset.range N, 10 ^ m) + 1 = 10 ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem t_a_even (n : ℕ) (hn : 3 < n) (he : Even n) : a n = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, n = 4 + k := ⟨n - 4, by omega⟩
  have hk2 : k % 2 = 0 := by rcases he with ⟨r, hr⟩; omega
  unfold a
  apply Finset.sum_eq_zero
  intro i _
  rw [hk, t_tail]
  simp [hk2]

theorem t_a_odd (n : ℕ) (hn : 3 < n) (ho : Odd n) : 9 * a n + 1 = 10 ^ (n + 1) := by
  have hsum : a n = ∑ m ∈ Finset.range (n + 1), 10 ^ m := by
    unfold a
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨k, hk⟩ : ∃ k, n = 4 + k := ⟨n - 4, by omega⟩
    have hk2 : k % 2 = 1 := by rcases ho with ⟨r, hr⟩; omega
    have e : state n (((n + 1 - 1 - i : ℕ) : ℤ), ((n + 1 - 1 - i : ℕ) : ℤ)) = true := by
      rw [hk, t_tail]; simp [hk2]
    rw [if_pos e]
    congr 1
    omega
  rw [hsum, t_geom]

theorem t_a0 : a 0 = 1 := by decide +kernel
theorem t_a1 : a 1 = 1 := by decide +kernel
theorem t_a2 : a 2 = 100 := by decide +kernel
theorem t_a3 : a 3 = 11 := by decide +kernel


theorem t_a4 : a 4 = 0 := t_a_even 4 (by norm_num) (by decide)
theorem t_a6 : a 6 = 0 := t_a_even 6 (by norm_num) (by decide)
theorem t_a5 : a 5 = 111111 := by
  have := t_a_odd 5 (by norm_num) (by decide)
  omega
theorem t_a7 : a 7 = 11111111 := by
  have := t_a_odd 7 (by norm_num) (by decide)
  omega

theorem t_odd_q (n : ℕ) (hn : 3 < n) (ho : Odd n) : (a n : ℚ) = (10 ^ (n + 1) - 1) / 9 := by
  have h := t_a_odd n hn ho
  have hq : (9 * (a n : ℚ) + 1) = 10 ^ (n + 1) := by exact_mod_cast h
  linarith

theorem t_rec (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4) := by
  rcases Nat.even_or_odd n with he | ho
  · have e1 : Even (n - 2) := by rcases he with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
    have e2 : Even (n - 4) := by rcases he with ⟨r, hr⟩; exact ⟨r - 2, by omega⟩
    rw [t_a_even n (by omega) he, t_a_even (n - 2) (by omega) e1, t_a_even (n - 4) (by omega) e2]
    simp
  · have o1 : Odd (n - 2) := by rcases ho with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
    have o2 : Odd (n - 4) := by rcases ho with ⟨r, hr⟩; exact ⟨r - 2, by omega⟩
    have h0 := t_a_odd n (by omega) ho
    have h1 := t_a_odd (n - 2) (by omega) o1
    have h2 := t_a_odd (n - 4) (by omega) o2
    rw [show n - 2 + 1 = (n - 4 + 1) + 2 by omega] at h1
    rw [show n + 1 = (n - 4 + 1) + 4 by omega] at h0
    have z0 : (9 * (a n : ℤ) + 1) = 10 ^ (n - 4 + 1 + 4) := by exact_mod_cast h0
    have z1 : (9 * (a (n - 2) : ℤ) + 1) = 10 ^ (n - 4 + 1 + 2) := by exact_mod_cast h1
    have z2 : (9 * (a (n - 4) : ℤ) + 1) = 10 ^ (n - 4 + 1) := by exact_mod_cast h2
    rw [pow_add] at z0 z1
    linarith

theorem t_mul : A * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
    1 + X - X ^ 2 - 90 * X ^ 3 - 10000 * X ^ 4 + 110100 * X ^ 5 + 10000 * X ^ 6 - 110000 * X ^ 7 := by
  have e1 : A * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      A - PowerSeries.C (101 : ℚ) * (A * X ^ 2) + PowerSeries.C (100 : ℚ) * (A * X ^ 4) := by
    rw [map_ofNat, map_ofNat]
    ring
  have e2 : (1 + X - X ^ 2 - 90 * X ^ 3 - 10000 * X ^ 4 + 110100 * X ^ 5 + 10000 * X ^ 6
        - 110000 * X ^ 7 : PowerSeries ℚ) =
      1 + PowerSeries.C (1 : ℚ) * X ^ 1 - PowerSeries.C (1 : ℚ) * X ^ 2
        - PowerSeries.C (90 : ℚ) * X ^ 3 - PowerSeries.C (10000 : ℚ) * X ^ 4
        + PowerSeries.C (110100 : ℚ) * X ^ 5 + PowerSeries.C (10000 : ℚ) * X ^ 6
        - PowerSeries.C (110000 : ℚ) * X ^ 7 := by
    simp only [map_ofNat, map_one, pow_one, one_mul]
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', A, PowerSeries.coeff_mk]
  by_cases hk : k < 8
  · interval_cases k <;> simp [t_a0, t_a1, t_a2, t_a3, t_a4, t_a5, t_a6, t_a7] <;> norm_num
  · rw [if_pos (show 2 ≤ k by omega), if_pos (show 4 ≤ k by omega),
      if_neg (show ¬ (k = 0) by omega), if_neg (show ¬ (k = 1) by omega),
      if_neg (show ¬ (k = 2) by omega), if_neg (show ¬ (k = 3) by omega),
      if_neg (show ¬ (k = 4) by omega), if_neg (show ¬ (k = 5) by omega),
      if_neg (show ¬ (k = 6) by omega), if_neg (show ¬ (k = 7) by omega)]
    have := t_rec k (by omega)
    have hq : (a k : ℚ) = 101 * a (k - 2) - 100 * a (k - 4) := by exact_mod_cast this
    rw [hq]
    ring


theorem t_gf : A = (1 + X - X ^ 2 - 90 * X ^ 3 - 10000 * X ^ 4 + 110100 * X ^ 5 + 10000 * X ^ 6
      - 110000 * X ^ 7) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) with hD
  have hc : constantCoeff D ≠ 0 := by
    simp [hD]
  calc A = A * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel D hc, mul_one]
    _ = (A * D) * D⁻¹ := by ring
    _ = _ := by rw [hD, t_mul]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a285648.main :=
  ⟨OMA.Helpers.t_gf,
    fun n h3 he => by rw [OMA.Helpers.t_a_even n h3 he]; simp,
    fun n h3 ho => OMA.Helpers.t_odd_q n h3 ho,
    fun n h7 => OMA.Helpers.t_rec n h7⟩
