import OMAStatements.S_oeis_a267526
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a267526

/-- The closed form of row `n` for `n ≥ 2`. -/
def a267526_F (n : ℕ) (x : ℤ) : Bool :=
  decide (x < -(n : ℤ) ∨ 2 ≤ x ∨ (x ≤ 0 ∧ -(n : ℤ) + 2 ≤ x ∧ x % 2 = 0))

theorem a267526_state_one (x : ℤ) :
    state 141 1 x = decide (x < -1 ∨ (-1 < x ∧ x < 1) ∨ 1 < x) := by
  show Nat.testBit 141 (4 * (decide (x - 1 = 0)).toNat + 2 * (decide (x = 0)).toNat +
    (decide (x + 1 = 0)).toNat) = _
  by_cases h0 : x = 0
  · subst h0; decide
  · by_cases h1 : x = 1
    · subst h1; decide
    · by_cases h2 : x = -1
      · subst h2; decide
      · have e1 : x - 1 ≠ 0 := by omega
        have e2 : x + 1 ≠ 0 := by omega
        have e3 : x < -1 ∨ (-1 < x ∧ x < 1) ∨ 1 < x := by omega
        simp only [h0, e1, e2, e3, decide_true, decide_false]
        rfl

theorem a267526_state_two (x : ℤ) : state 141 2 x = a267526_F 2 x := by
  show Nat.testBit 141 (4 * (state 141 1 (x - 1)).toNat + 2 * (state 141 1 x).toNat +
    (state 141 1 (x + 1)).toNat) = a267526_F 2 x
  rw [a267526_state_one, a267526_state_one, a267526_state_one, a267526_F]
  by_cases h1 : (x - 1 < -1 ∨ (-1 < x - 1 ∧ x - 1 < 1) ∨ 1 < x - 1) <;>
    by_cases h2 : (x < -1 ∨ (-1 < x ∧ x < 1) ∨ 1 < x) <;>
    by_cases h3 : (x + 1 < -1 ∨ (-1 < x + 1 ∧ x + 1 < 1) ∨ 1 < x + 1) <;>
    by_cases h4 : (x < -((2 : ℕ) : ℤ) ∨ 2 ≤ x ∨ (x ≤ 0 ∧ -((2 : ℕ) : ℤ) + 2 ≤ x ∧ x % 2 = 0)) <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false] <;>
    first | rfl | omega

theorem a267526_step (n : ℕ) (hn : 2 ≤ n) (x : ℤ) :
    step 141 (a267526_F n) x = a267526_F (n + 1) x := by
  unfold step a267526_F
  by_cases h1 : (x - 1 < -(n : ℤ) ∨ 2 ≤ x - 1 ∨ (x - 1 ≤ 0 ∧ -(n : ℤ) + 2 ≤ x - 1 ∧ (x - 1) % 2 = 0)) <;>
    by_cases h2 : (x < -(n : ℤ) ∨ 2 ≤ x ∨ (x ≤ 0 ∧ -(n : ℤ) + 2 ≤ x ∧ x % 2 = 0)) <;>
    by_cases h3 : (x + 1 < -(n : ℤ) ∨ 2 ≤ x + 1 ∨ (x + 1 ≤ 0 ∧ -(n : ℤ) + 2 ≤ x + 1 ∧ (x + 1) % 2 = 0)) <;>
    by_cases h4 : (x < -((n + 1 : ℕ) : ℤ) ∨ 2 ≤ x ∨
      (x ≤ 0 ∧ -((n + 1 : ℕ) : ℤ) + 2 ≤ x ∧ x % 2 = 0)) <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false] <;>
    first | rfl | omega

theorem a267526_state (n : ℕ) (x : ℤ) : state 141 (n + 2) x = a267526_F (n + 2) x := by
  induction n generalizing x with
  | zero => exact a267526_state_two x
  | succ k ih =>
    show step 141 (state 141 (k + 2)) x = _
    rw [show state 141 (k + 2) = a267526_F (k + 2) from funext ih]
    exact a267526_step (k + 2) (by omega) x


/-- Sum of `10^j` over the even `j < k`. -/
theorem a267526_evenSum (k : ℕ) :
    ∑ j ∈ Finset.range k, (if j % 2 = 0 then (10 : ℚ) ^ j else 0) =
      ((100 : ℚ) ^ ((k + 1) / 2) - 1) / 99 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
    · rw [if_pos (by omega), show (2 * t + 1) / 2 = t by omega,
        show (2 * t + 1 + 1) / 2 = t + 1 by omega, pow_mul]
      norm_num
      ring
    · rw [if_neg (by omega), show (2 * t + 1 + 1) / 2 = t + 1 by omega,
        show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega]
      ring

theorem a267526_a_nat (m : ℕ) : a (m + 2) = ∑ i ∈ Finset.range (m + 1), 10 ^ i +
    ∑ j ∈ Finset.range (m + 1), (if j % 2 = 0 then 10 ^ (m + 2) * 10 ^ j else 0) := by
  unfold a rowDigits
  rw [show 2 * (m + 2) + 1 = (m + 1) + (1 + ((m + 1) + 2)) by ring,
    Finset.sum_range_add _ (m + 1) (1 + ((m + 1) + 2)), Finset.sum_range_add _ 1 ((m + 1) + 2),
    Finset.sum_range_add _ (m + 1) 2]
  simp only [a267526_state]
  have h1 : ∀ i ∈ Finset.range (m + 1),
      (a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((i : ℕ) : ℤ))).toNat * 10 ^ i = 10 ^ i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have : a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = true := by
      simp only [a267526_F, decide_eq_true_eq]; omega
    rw [this]; simp
  have h3 : ∀ j ∈ Finset.range (m + 1),
      (a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((m + 1 + (1 + j) : ℕ) : ℤ))).toNat *
        10 ^ (m + 1 + (1 + j)) = if j % 2 = 0 then 10 ^ (m + 2) * 10 ^ j else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hp : j % 2 = 0
    · have : a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((m + 1 + (1 + j) : ℕ) : ℤ)) = true := by
        simp only [a267526_F, decide_eq_true_eq]; omega
      rw [this, if_pos hp, ← pow_add]; simp; ring_nf
    · have : a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((m + 1 + (1 + j) : ℕ) : ℤ)) = false := by
        simp only [a267526_F, decide_eq_false_iff_not]; omega
      rw [this, if_neg hp]; simp
  have h2 : ∀ j ∈ Finset.range 1,
      (a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((m + 1 + j : ℕ) : ℤ))).toNat *
        10 ^ (m + 1 + j) = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have : a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((m + 1 + j : ℕ) : ℤ)) = false := by
      simp only [a267526_F, decide_eq_false_iff_not]; omega
    rw [this]; simp
  have h4 : ∀ j ∈ Finset.range 2,
      (a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((m + 1 + (1 + (m + 1 + j)) : ℕ) : ℤ))).toNat *
        10 ^ (m + 1 + (1 + (m + 1 + j))) = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have : a267526_F (m + 2) (((m + 2 : ℕ) : ℤ) - ((m + 1 + (1 + (m + 1 + j)) : ℕ) : ℤ)) =
        false := by
      simp only [a267526_F, decide_eq_false_iff_not]; omega
    rw [this]; simp
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3,
    Finset.sum_congr rfl h4]
  simp

theorem a267526_closed (m : ℕ) : (a (m + 2) : ℚ) =
    10 ^ (m + 2) * (100 ^ ((m + 2) / 2) - 1) / 99 + (10 ^ (m + 1) - 1) / 9 := by
  rw [a267526_a_nat]
  push_cast
  rw [geom_sum_eq (by norm_num : (10 : ℚ) ≠ 1)]
  have e : ∑ j ∈ Finset.range (m + 1), (if j % 2 = 0 then (10 : ℚ) ^ (m + 2) * 10 ^ j else 0) =
      10 ^ (m + 2) * ∑ j ∈ Finset.range (m + 1), (if j % 2 = 0 then (10 : ℚ) ^ j else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [e, a267526_evenSum, show m + 1 + 1 = m + 2 by omega]
  ring


theorem a267526_rec_q (m : ℕ) : (a (m + 6) : ℚ) = 11 * a (m + 5) + 9990 * a (m + 4) -
    110000 * a (m + 3) + 100000 * a (m + 2) := by
  rw [a267526_closed (m + 4), a267526_closed (m + 3), a267526_closed (m + 2),
    a267526_closed (m + 1), a267526_closed m]
  rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
  · rw [show (2 * t + 4 + 2) / 2 = t + 3 by omega, show (2 * t + 3 + 2) / 2 = t + 2 by omega,
      show (2 * t + 2 + 2) / 2 = t + 2 by omega, show (2 * t + 1 + 2) / 2 = t + 1 by omega,
      show (2 * t + 2) / 2 = t + 1 by omega, show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul,
      ← pow_mul, ← pow_mul]
    ring
  · rw [show (2 * t + 1 + 4 + 2) / 2 = t + 3 by omega, show (2 * t + 1 + 3 + 2) / 2 = t + 3 by omega,
      show (2 * t + 1 + 2 + 2) / 2 = t + 2 by omega, show (2 * t + 1 + 1 + 2) / 2 = t + 2 by omega,
      show (2 * t + 1 + 2) / 2 = t + 1 by omega, show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul,
      ← pow_mul, ← pow_mul]
    ring

theorem a267526_a0 : a 0 = 1 := by decide

theorem a267526_a1 : a 1 = 10 := by decide

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267526.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega]
    have h := OMA.Helpers.a267526_rec_q m
    exact_mod_cast h
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    have eD : ((1 : ℚ⟦X⟧) - X) * (1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X) =
        1 - C (11 : ℚ) * X ^ 1 - C (9990 : ℚ) * X ^ 2 + C (110000 : ℚ) * X ^ 3 -
          C (100000 : ℚ) * X ^ 4 := by
      simp only [map_ofNat]; ring
    have eN : (1 - X - 9999 * X ^ 2 + 10000 * X ^ 3 + 990000 * X ^ 4 - 1000000 * X ^ 5 : ℚ⟦X⟧) =
        C (1 : ℚ) * X ^ 0 - C (1 : ℚ) * X ^ 1 - C (9999 : ℚ) * X ^ 2 + C (10000 : ℚ) * X ^ 3 +
          C (990000 : ℚ) * X ^ 4 - C (1000000 : ℚ) * X ^ 5 := by
      simp only [map_ofNat, map_one]; ring
    rw [eD, eN, mul_sub, mul_add, mul_sub, mul_sub, mul_one]
    simp only [mul_left_comm _ (C _), ← mul_assoc]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C,
      OMA.S_oeis_a267526.A, coeff_mk]
    have v0 : (OMA.S_oeis_a267526.a 0 : ℚ) = 1 := by rw [OMA.Helpers.a267526_a0]; norm_num
    have v1 : (OMA.S_oeis_a267526.a 1 : ℚ) = 10 := by rw [OMA.Helpers.a267526_a1]; norm_num
    have v2 : (OMA.S_oeis_a267526.a 2 : ℚ) = 101 := by
      rw [OMA.Helpers.a267526_closed 0]; norm_num
    have v3 : (OMA.S_oeis_a267526.a 3 : ℚ) = 1011 := by
      rw [OMA.Helpers.a267526_closed 1]; norm_num
    have v4 : (OMA.S_oeis_a267526.a 4 : ℚ) = 1010111 := by
      rw [OMA.Helpers.a267526_closed 2]; norm_num
    have v5 : (OMA.S_oeis_a267526.a 5 : ℚ) = 10101111 := by
      rw [OMA.Helpers.a267526_closed 3]; norm_num
    rcases n with _ | _ | _ | _ | _ | _ | m
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v0, v1, v2, v3]
    · norm_num [v0, v1, v2, v3, v4]
    · norm_num [v0, v1, v2, v3, v4, v5]
    · have h := OMA.Helpers.a267526_rec_q m
      simp only [show 0 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
        show 1 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
        show 2 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
        show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
        show 4 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
        show 5 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega, if_true,
        show m + 1 + 1 + 1 + 1 + 1 + 1 - 0 = m + 6 from by omega,
        show m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 5 from by omega,
        show m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 4 from by omega,
        show m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 3 from by omega,
        show m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 2 from by omega,
        show m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 from by omega,
        show m + 1 + 1 + 1 + 1 + 1 + 1 = m + 6 from by omega,
        show m + 6 ≠ 0 from by omega, show m + 5 ≠ 0 from by omega, show m + 4 ≠ 0 from by omega,
        show m + 3 ≠ 0 from by omega, show m + 2 ≠ 0 from by omega, show m + 1 ≠ 0 from by omega,
        if_false]
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [OMA.Helpers.a267526_closed m, show m + 2 - 1 = m + 1 by omega]
