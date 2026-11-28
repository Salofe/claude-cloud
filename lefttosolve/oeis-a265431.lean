import OMAStatements.S_oeis_a265431

/-!
Proof of Barker's closed form and generating function for OEIS A265431 (total OFF cells of
Rule 188 started from a single ON cell).

Rule 188 sends (l, c, r) to (l xor c) or (l and c and r). By induction on n, stage n is ON
exactly at the cells 0 <= x <= n with x = 0 or x + n not congruent to 3 mod 4. Hence the number of
OFF cells of row k among -k..k is k + floor((2k+1)/4) - floor((k+1)/4) (the k cells left of 0
plus the cells 0 < x < k with x + k = 3 mod 4), so a(n+4) = a(n) + 5n + 12 with
a(0..3) = 0, 1, 4, 7. The closed form follows by induction in steps of 4 (i^4 = (-i)^4 = 1),
and the generating-function identity by comparing coefficients after clearing the denominator
(1-x)^3 (1+x) (1+x^2) = 1 - 2x + x^2 - x^4 + 2x^5 - x^6.
-/

namespace OMA.Helpers

open OMA.S_oeis_a265431 PowerSeries

/-- The claimed pattern of Rule 188: ON exactly on 0..n, except at the cells x ≠ 0 with
x + n ≡ 3 (mod 4). -/
def a265431_on (n : ℕ) (x : ℤ) : Bool :=
  decide (0 ≤ x ∧ x ≤ n ∧ (x = 0 ∨ (x + n) % 4 ≠ 3))

theorem a265431_rule (l c r : Bool) :
    Nat.testBit 188 (4 * l.toNat + 2 * c.toNat + r.toNat) = ((l ^^ c) || (l && c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

theorem a265431_state (n : ℕ) (x : ℤ) : state 188 n x = a265431_on n x := by
  induction n generalizing x with
  | zero =>
    show decide (x = 0) = _
    unfold a265431_on
    by_cases h : x = 0
    · subst h; decide
    · rw [decide_eq_false h]
      symm
      rw [decide_eq_false_iff_not]
      push_cast
      omega
  | succ m ih =>
    show step 188 (state 188 m) x = _
    unfold step
    rw [ih, ih, ih, a265431_rule]
    cases h1 : a265431_on m (x - 1) <;> cases h2 : a265431_on m x <;>
      cases h3 : a265431_on m (x + 1) <;>
      simp only [a265431_on, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 ⊢ <;>
      simp <;> push_cast at * <;> omega

theorem a265431_partial (k N : ℕ) (hN : N ≤ 2 * k + 1) :
    ∑ i ∈ Finset.range N, (!a265431_on k ((k : ℤ) - i)).toNat
      = (N - (k + 1)) + ((2 * k + 1) / 4 - (2 * k + 1 - min N k) / 4) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    cases h : a265431_on k ((k : ℤ) - N) <;>
      simp only [a265431_on, decide_eq_true_eq, decide_eq_false_iff_not] at h <;>
      simp only [Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false] <;>
      omega

theorem a265431_off (k : ℕ) : offCount (state 188 k) k = k + (2 * k + 1) / 4 - (k + 1) / 4 := by
  unfold offCount
  simp only [a265431_state]
  rw [a265431_partial k (2 * k + 1) le_rfl]
  omega

theorem a265431_a_succ (n : ℕ) : a (n + 1) = a n + offCount (state 188 (n + 1)) (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

theorem a265431_a0 : a 0 = 0 := by
  unfold a
  rw [Finset.sum_range_one, a265431_off]

theorem a265431_a1 : a 1 = 1 := by
  rw [a265431_a_succ, a265431_a0, a265431_off]

theorem a265431_a2 : a 2 = 4 := by
  rw [a265431_a_succ, a265431_a1, a265431_off]

theorem a265431_a3 : a 3 = 7 := by
  rw [a265431_a_succ, a265431_a2, a265431_off]

theorem a265431_a_add_four (n : ℕ) : a (n + 4) = a n + 5 * n + 12 := by
  rw [a265431_a_succ, a265431_a_succ, a265431_a_succ, a265431_a_succ, a265431_off, a265431_off,
    a265431_off, a265431_off]
  omega

theorem a265431_closedC (n : ℕ) : (a n : ℂ) = 1/16*(10*(n : ℂ)^2+8*(n : ℂ)+3*(-1)^n
    -2*(-Complex.I)^n-2*Complex.I^n+1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | _ | m
    · rw [a265431_a0]; push_cast; ring
    · rw [a265431_a1]; push_cast; ring
    · rw [a265431_a2]; push_cast; linear_combination (1/4 : ℂ) * Complex.I_sq
    · rw [a265431_a3]; push_cast; ring
    · have h := ih m (by omega)
      rw [show m + 1 + 1 + 1 + 1 = m + 4 by omega, a265431_a_add_four]
      push_cast
      rw [h]
      have e1 : ((-1 : ℂ)) ^ (m + 4) = (-1) ^ m := by rw [pow_add]; norm_num
      have e2 : (-Complex.I) ^ (m + 4) = (-Complex.I) ^ m := by
        have h4 : (-Complex.I) ^ 4 = 1 := by
          rw [Even.neg_pow (by decide : Even 4), Complex.I_pow_four]
        rw [pow_add, h4, mul_one]
      have e3 : Complex.I ^ (m + 4) = Complex.I ^ m := by
        rw [pow_add, Complex.I_pow_four, mul_one]
      rw [e1, e2, e3]
      ring

theorem a265431_rec (j : ℕ) :
    (a (j + 6) : ℚ) - 2 * a (j + 5) + a (j + 4) - a (j + 2) + 2 * a (j + 1) - a j = 0 := by
  have h6 := a265431_a_add_four (j + 2)
  have h5 := a265431_a_add_four (j + 1)
  have h4 := a265431_a_add_four j
  rw [show j + 2 + 4 = j + 6 by omega] at h6
  rw [show j + 1 + 4 = j + 5 by omega] at h5
  rw [h6, h5, h4]
  push_cast
  ring

theorem a265431_gf :
    A = (X * (1 + 2 * X + 2 * X ^ 3)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2))⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have e1 : A * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2)) =
      A - PowerSeries.C (2 : ℚ) * (A * X ^ 1) + A * X ^ 2 - A * X ^ 4
        + PowerSeries.C (2 : ℚ) * (A * X ^ 5) - A * X ^ 6 := by
    rw [map_ofNat]
    ring
  have e2 : (X * (1 + 2 * X + 2 * X ^ 3) : ℚ⟦X⟧) =
      PowerSeries.C (1 : ℚ) * X ^ 1 + PowerSeries.C (2 : ℚ) * X ^ 2
        + PowerSeries.C (2 : ℚ) * X ^ 4 := by
    rw [map_one, map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', A, PowerSeries.coeff_mk]
  by_cases hk : k < 6
  · have h4 : a 4 = 12 := by rw [a265431_a_add_four 0, a265431_a0]
    have h5 : a 5 = 18 := by rw [a265431_a_add_four 1, a265431_a1]
    interval_cases k <;>
      simp [a265431_a0, a265431_a1, a265431_a2, a265431_a3, h4, h5] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    rw [if_pos (show 1 ≤ j + 6 by omega), if_pos (show 2 ≤ j + 6 by omega),
      if_pos (show 4 ≤ j + 6 by omega), if_pos (show 5 ≤ j + 6 by omega),
      if_pos (show 6 ≤ j + 6 by omega), if_neg (show ¬ (j + 6 = 1) by omega),
      if_neg (show ¬ (j + 6 = 2) by omega), if_neg (show ¬ (j + 6 = 4) by omega)]
    rw [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show j + 6 - 6 = j by omega]
    linear_combination a265431_rec j

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a265431.main :=
  ⟨OMA.Helpers.a265431_closedC, OMA.Helpers.a265431_gf⟩
