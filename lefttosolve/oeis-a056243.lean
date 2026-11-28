import OMAStatements.S_oeis_a056243

/-!
Proof of Barker's closed form and generating function for A056243.

With m = n - 3, a(n) = Sum_{j <= m} (-1)^(m-j) C(m, j) C(m+2+2j, m+2). Reading C(N, m+2) as the
coefficient of X^(m+2) in (X+1)^N, the binomial theorem gives
Sum_j (-1)^(m-j) C(m, j) (X+1)^(m+2+2j) = (X+1)^(m+2) ((X+1)^2 - 1)^m = (X+1)^(m+2) (X+2)^m X^m,
so a(m+3) is the coefficient of X^2 in (X+1)^(m+2) (X+2)^m, which is
2^(m-3) (9 m^2 + 19 m + 8). The generating function follows by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a056243

section PolyPart

open Polynomial

theorem a056243_poly (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
      Polynomial.C ((-1 : ℤ) ^ (m - j) * (m.choose j : ℤ)) * (X + 1) ^ (m + 2 + 2 * j) =
      (X + 1) ^ (m + 2) * (X + Polynomial.C 2) ^ m * X ^ m := by
  have h1 : ((X + 1 : ℤ[X]) ^ 2 + (-1)) ^ m = ∑ j ∈ Finset.range (m + 1),
      ((X + 1) ^ 2) ^ j * (-1) ^ (m - j) * (m.choose j : ℤ[X]) := add_pow _ _ _
  have h2 : ((X + 1 : ℤ[X]) ^ 2 + (-1)) = X * (X + Polynomial.C 2) := by
    rw [show (Polynomial.C 2 : ℤ[X]) = 2 from rfl]
    ring
  rw [h2, mul_pow] at h1
  calc _ = (X + 1) ^ (m + 2) * ∑ j ∈ Finset.range (m + 1),
        ((X + 1) ^ 2) ^ j * (-1) ^ (m - j) * (m.choose j : ℤ[X]) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast, ← pow_mul]
        ring
    _ = _ := by rw [← h1]; ring

theorem a056243_sum (m : ℕ) :
    a (m + 3) = ∑ j ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * ((m + 2 + 2 * j).choose (m + 2) : ℤ) := by
  unfold a T
  rw [if_neg (by omega), show m + 3 - 2 = m + 1 by omega, show m + 1 - 1 = m by omega]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show m - j = m - j from rfl, show m + 3 + 2 * j - 1 = m + 2 + 2 * j by omega,
    Nat.choose_symm_of_eq_add (show m + 2 + 2 * j = 2 * j + (m + 2) by omega)]

theorem a056243_coeff (m : ℕ) :
    a (m + 3) = ((X + 1 : ℤ[X]) ^ (m + 2) * (X + Polynomial.C 2) ^ m).coeff 2 := by
  have h := congrArg (fun p : ℤ[X] => p.coeff (2 + m)) (a056243_poly m)
  simp only [coeff_mul_X_pow, finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow] at h
  rw [← h, a056243_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show 2 + m = m + 2 by omega]

theorem a056243_choose2 (n : ℕ) : ((n.choose 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem a056243_closed8 (m : ℕ) : 8 * a (m + 3) = 2 ^ m * (9 * (m : ℤ) ^ 2 + 19 * m + 8) := by
  rw [a056243_coeff, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_X_add_one_pow,
    coeff_X_add_C_pow]
  rcases m with _ | _ | k
  · norm_num
  · norm_num
  · simp only [show k + 1 + 1 - (2 - 0) = k by omega, show k + 1 + 1 - (2 - 1) = k + 1 by omega,
      show k + 1 + 1 - (2 - 2) = k + 2 by omega]
    have c1 := a056243_choose2 (k + 1 + 1)
    have c2 := a056243_choose2 (k + 1 + 1 + 2)
    simp only [Nat.sub_zero, Nat.sub_self, Nat.choose_one_right, Nat.choose_zero_right,
      show 2 - 1 = 1 from rfl]
    push_cast at c1 c2 ⊢
    linear_combination (4 * 2 ^ k : ℤ) * c1 + (4 * 2 ^ (k + 2) : ℤ) * c2

end PolyPart

theorem a056243_closedQ (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 6) * (32 - 35 * (n : ℚ) + 9 * (n : ℚ) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := a056243_closed8 m
  have h' : (8 : ℚ) * (a (m + 3) : ℚ) = 2 ^ m * (9 * (m : ℚ) ^ 2 + 19 * m + 8) := by
    exact_mod_cast h
  have hz : (2 : ℚ) ^ (((m + 3 : ℕ) : ℤ) - 6) = 2 ^ m / 8 := by
    rw [show ((m + 3 : ℕ) : ℤ) - 6 = (m : ℤ) - 3 by push_cast; ring,
      zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    norm_num
  rw [hz]
  push_cast
  linear_combination (1 / 8 : ℚ) * h'

theorem a056243_small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 1 ∧ a 4 = 9 ∧ a 5 = 41 := by
  have h0 := a056243_closed8 0
  have h1 := a056243_closed8 1
  have h2 := a056243_closed8 2
  norm_num at h0 h1 h2
  refine ⟨by simp [a], by simp [a], by simp [a], by omega, by omega, by omega⟩

open PowerSeries in
theorem a056243_gf :
    PowerSeries.mk a * (1 - 2 * X) ^ 3 = X ^ 3 * (1 + 3 * X - X ^ 2) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk a with hA
  have hl : A * (1 - 2 * X) ^ 3 =
      A - C (6 : ℤ) * (A * X ^ 1) + C (12 : ℤ) * (A * X ^ 2) - C (8 : ℤ) * (A * X ^ 3) := by
    simp only [map_ofNat]
    ring
  have hr : (X : ℤ⟦X⟧) ^ 3 * (1 + 3 * X - X ^ 2) =
      X ^ 3 + C (3 : ℤ) * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hl, hr]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp only [coeff_mul_X_pow', hA, coeff_mk]
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := a056243_small
  rcases k with _ | _ | _ | _ | _ | _ | j
  · simp [s0]
  · simp [s0, s1]
  · simp [s0, s1, s2]
  · simp [s0, s1, s2, s3]
  · simp [s1, s2, s3, s4]
  · simp [s2, s3, s4, s5]
  · have e : j + 1 + 1 + 1 + 1 + 1 + 1 = j + 6 := rfl
    simp only [e, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega, show 3 ≤ j + 6 by omega,
      show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega,
      show ¬ (j + 6 = 3) by omega, show ¬ (j + 6 = 4) by omega,
      show ¬ (j + 6 = 5) by omega, if_true, if_false]
    have c3 : 8 * a (j + 6) = 2 ^ (j + 3) * (9 * ((j + 3 : ℕ) : ℤ) ^ 2 + 19 * ((j + 3 : ℕ) : ℤ) + 8) :=
      a056243_closed8 (j + 3)
    have c2 : 8 * a (j + 5) = 2 ^ (j + 2) * (9 * ((j + 2 : ℕ) : ℤ) ^ 2 + 19 * ((j + 2 : ℕ) : ℤ) + 8) :=
      a056243_closed8 (j + 2)
    have c1 : 8 * a (j + 4) = 2 ^ (j + 1) * (9 * ((j + 1 : ℕ) : ℤ) ^ 2 + 19 * ((j + 1 : ℕ) : ℤ) + 8) :=
      a056243_closed8 (j + 1)
    have c0 := a056243_closed8 j
    have h8 : 8 * (a (j + 6) - 6 * a (j + 5) + 12 * a (j + 4) - 8 * a (j + 3)) = 0 := by
      push_cast at c3 c2 c1 c0
      linear_combination c3 - 6 * c2 + 12 * c1 - 8 * c0
    simp only [mul_zero, sub_zero, add_zero]
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a056243.main :=
  ⟨OMA.Helpers.a056243_closedQ, OMA.Helpers.a056243_gf⟩
