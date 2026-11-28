import OMAStatements.S_oeis_a266841
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a266841

theorem a266841_step (s : ℤ → Bool) (x : ℤ) :
    step 69 s x = (!s (x + 1) && (s x || !s (x - 1))) := by
  unfold step
  generalize s (x - 1) = l
  generalize s x = c
  generalize s (x + 1) = r
  cases l <;> cases c <;> cases r <;> decide

theorem a266841_odd_of_even (n : ℕ)
    (hE : ∀ x : ℤ, state 69 n x = decide (x % 2 = 0 ∧ -(n : ℤ) ≤ x ∧ x ≤ 0)) (x : ℤ) :
    state 69 (n + 1) x = !decide (x % 2 = 1 ∧ -(n : ℤ) - 1 ≤ x ∧ x ≤ 1) := by
  show step 69 (state 69 n) x = _
  rw [a266841_step, hE, hE, hE]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  omega

theorem a266841_even_of_odd (n : ℕ)
    (hO : ∀ x : ℤ, state 69 n x = !decide (x % 2 = 1 ∧ -(n : ℤ) ≤ x ∧ x ≤ 1)) (x : ℤ) :
    state 69 (n + 1) x = decide (x % 2 = 0 ∧ -(n : ℤ) - 1 ≤ x ∧ x ≤ 0) := by
  show step 69 (state 69 n) x = _
  rw [a266841_step, hO, hO, hO]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_not,
    decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem a266841_state (m : ℕ) :
    (∀ x : ℤ, state 69 (2 * m) x = decide (x % 2 = 0 ∧ -((2 * m : ℕ) : ℤ) ≤ x ∧ x ≤ 0)) ∧
    (∀ x : ℤ, state 69 (2 * m + 1) x = !decide (x % 2 = 1 ∧ -((2 * m + 1 : ℕ) : ℤ) ≤ x ∧ x ≤ 1)) := by
  induction m with
  | zero =>
    have hE : ∀ x : ℤ, state 69 (2 * 0) x = decide (x % 2 = 0 ∧ -((2 * 0 : ℕ) : ℤ) ≤ x ∧ x ≤ 0) := by
      intro x
      show decide (x = 0) = _
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      omega
    refine ⟨hE, fun x => ?_⟩
    rw [a266841_odd_of_even (2 * 0) hE x]
    congr 2
  | succ k ih =>
    have hE : ∀ x : ℤ, state 69 (2 * (k + 1)) x =
        decide (x % 2 = 0 ∧ -((2 * (k + 1) : ℕ) : ℤ) ≤ x ∧ x ≤ 0) := by
      intro x
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, a266841_even_of_odd (2 * k + 1) ih.2 x]
      congr 2
    refine ⟨hE, fun x => ?_⟩
    rw [a266841_odd_of_even (2 * (k + 1)) hE x]
    congr 2


theorem a266841_T (m : ℕ) :
    99 * (∑ j ∈ Finset.range (2 * m + 1), if j % 2 = 0 then (10 : ℕ) ^ j else 0) + 1 =
      100 ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, if_neg (by omega), if_pos (by omega)]
    have h1 : (10 : ℕ) ^ (2 * k + 1 + 1) = 100 ^ (k + 1) := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
    rw [h1, pow_succ 100 (k + 1)]
    omega

theorem a266841_V (m : ℕ) :
    99 * (∑ j ∈ Finset.range (2 * m + 3), if j % 2 = 1 then (10 : ℕ) ^ j else 0) + 10 =
      10 * 100 ^ (m + 1) := by
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ k ih =>
    rw [show 2 * (k + 1) + 3 = 2 * k + 3 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, if_pos (by omega), if_neg (by omega)]
    have h1 : (10 : ℕ) ^ (2 * k + 3) = 10 * 100 ^ (k + 1) := by
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 by ring, pow_succ, pow_mul]; norm_num; ring
    rw [h1, pow_succ 100 (k + 1)]
    omega

theorem a266841_G (k : ℕ) : 9 * (∑ i ∈ Finset.range k, (10 : ℕ) ^ i) + 1 = 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem a266841_a_even (m : ℕ) : 99 * a (2 * m) + 100 ^ m = 100 ^ (2 * m + 1) := by
  have hs : ∀ i ∈ Finset.range (2 * (2 * m) + 1),
      (state 69 (2 * m) (((2 * m : ℕ) : ℤ) - (i : ℤ))).toNat * 10 ^ i =
        if i % 2 = 0 ∧ 2 * m ≤ i then 10 ^ i else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [(a266841_state m).1]
    by_cases h : i % 2 = 0 ∧ 2 * m ≤ i
    · rw [if_pos h, decide_eq_true (by omega)]
      simp
    · rw [if_neg h, decide_eq_false (by omega)]
      simp
  unfold a rowDigits
  rw [Finset.sum_congr rfl hs, show 2 * (2 * m) + 1 = 2 * m + (2 * m + 1) by ring,
    Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_range] at hi; omega)), zero_add]
  have hs2 : ∀ j ∈ Finset.range (2 * m + 1),
      (if (2 * m + j) % 2 = 0 ∧ 2 * m ≤ 2 * m + j then (10 : ℕ) ^ (2 * m + j) else 0) =
        100 ^ m * (if j % 2 = 0 then 10 ^ j else 0) := by
    intro j _
    by_cases h : j % 2 = 0
    · rw [if_pos (by omega), if_pos h, pow_add, pow_mul]
      norm_num
    · rw [if_neg (by omega), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hs2, ← Finset.mul_sum]
  have hT := a266841_T m
  generalize (∑ j ∈ Finset.range (2 * m + 1), if j % 2 = 0 then (10 : ℕ) ^ j else 0) = S at hT ⊢
  calc 99 * (100 ^ m * S) + 100 ^ m = 100 ^ m * (99 * S + 1) := by ring
    _ = 100 ^ (2 * m + 1) := by rw [hT]; ring

theorem a266841_a_odd (m : ℕ) :
    99 * a (2 * m + 1) + 11 = 10 * 100 ^ (2 * m + 1) + 100 ^ m := by
  have hs : ∀ i ∈ Finset.range (2 * (2 * m + 1) + 1),
      (state 69 (2 * m + 1) (((2 * m + 1 : ℕ) : ℤ) - (i : ℤ))).toNat * 10 ^ i =
        if i % 2 = 0 ∧ 2 * m ≤ i then 0 else 10 ^ i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [(a266841_state m).2]
    by_cases h : i % 2 = 0 ∧ 2 * m ≤ i
    · rw [if_pos h, decide_eq_true (by omega)]
      simp
    · rw [if_neg h, decide_eq_false (by omega)]
      simp
  unfold a rowDigits
  rw [Finset.sum_congr rfl hs, show 2 * (2 * m + 1) + 1 = 2 * m + (2 * m + 3) by ring,
    Finset.sum_range_add]
  rw [Finset.sum_congr rfl (fun i hi => if_neg (by rw [Finset.mem_range] at hi; omega))]
  have hs2 : ∀ j ∈ Finset.range (2 * m + 3),
      (if (2 * m + j) % 2 = 0 ∧ 2 * m ≤ 2 * m + j then 0 else (10 : ℕ) ^ (2 * m + j)) =
        100 ^ m * (if j % 2 = 1 then 10 ^ j else 0) := by
    intro j _
    by_cases h : j % 2 = 1
    · rw [if_neg (by omega), if_pos h, pow_add, pow_mul]
      norm_num
    · rw [if_pos (by omega), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hs2, ← Finset.mul_sum]
  have hV := a266841_V m
  have hG := a266841_G (2 * m)
  rw [pow_mul] at hG
  norm_num at hG
  generalize (∑ j ∈ Finset.range (2 * m + 3), if j % 2 = 1 then (10 : ℕ) ^ j else 0) = V at hV ⊢
  generalize (∑ i ∈ Finset.range (2 * m), (10 : ℕ) ^ i) = G at hG ⊢
  have key : 99 * (G + 100 ^ m * V) + 11 + 10 * 100 ^ m =
      11 * (9 * G + 1) + 100 ^ m * (99 * V + 10) := by ring
  rw [hG, hV] at key
  rw [show 2 * m + 1 = m + m + 1 by ring, pow_succ, pow_add]
  rw [pow_succ] at key
  zify at key ⊢
  linear_combination key


theorem a266841_evenQ (n : ℕ) (hn : Even n) :
    (a n : ℚ) = (100 * 100 ^ n - 10 ^ n) / 99 := by
  obtain ⟨m, rfl⟩ := hn
  have h : (99 : ℚ) * a (2 * m) + 100 ^ m = 100 ^ (2 * m + 1) := by
    exact_mod_cast a266841_a_even m
  have e : (10 : ℚ) ^ (m + m) = 100 ^ m := by
    rw [← two_mul, pow_mul]; norm_num
  rw [e, eq_div_iff (by norm_num), show m + m = 2 * m by ring]
  rw [pow_succ] at h
  linarith

theorem a266841_oddQ (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = (10 * 100 ^ n + 100 ^ (n / 2) - 11) / 99 := by
  obtain ⟨m, rfl⟩ := hn
  have h : (99 : ℚ) * a (2 * m + 1) + 11 = 10 * 100 ^ (2 * m + 1) + 100 ^ m := by
    exact_mod_cast a266841_a_odd m
  rw [show (2 * m + 1) / 2 = m by omega, eq_div_iff (by norm_num)]
  linarith

theorem a266841_rec (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have e : ∀ j : ℕ, (99 : ℤ) * a (2 * j) + 100 ^ j = 100 ^ (2 * j + 1) := fun j => by
      exact_mod_cast a266841_a_even j
    rw [show m + m + 6 = 2 * (m + 3) by ring, show 2 * (m + 3) - 2 = 2 * (m + 2) by omega,
      show 2 * (m + 3) - 4 = 2 * (m + 1) by omega, show 2 * (m + 3) - 6 = 2 * m by omega]
    have h3 := e (m + 3)
    have h2 := e (m + 2)
    have h1 := e (m + 1)
    have h0 := e m
    have key : (99 : ℤ) * (a (2 * (m + 3)) - (10101 * a (2 * (m + 2)) -
        1010100 * a (2 * (m + 1)) + 1000000 * a (2 * m))) = 0 := by
      linear_combination h3 - 10101 * h2 + 1010100 * h1 - 1000000 * h0
    omega
  · have e : ∀ j : ℕ, (99 : ℤ) * a (2 * j + 1) + 11 = 10 * 100 ^ (2 * j + 1) + 100 ^ j :=
      fun j => by exact_mod_cast a266841_a_odd j
    rw [show 2 * m + 1 + 6 = 2 * (m + 3) + 1 by ring,
      show 2 * (m + 3) + 1 - 2 = 2 * (m + 2) + 1 by omega,
      show 2 * (m + 3) + 1 - 4 = 2 * (m + 1) + 1 by omega,
      show 2 * (m + 3) + 1 - 6 = 2 * m + 1 by omega]
    have h3 := e (m + 3)
    have h2 := e (m + 2)
    have h1 := e (m + 1)
    have h0 := e m
    have key : (99 : ℤ) * (a (2 * (m + 3) + 1) - (10101 * a (2 * (m + 2) + 1) -
        1010100 * a (2 * (m + 1) + 1) + 1000000 * a (2 * m + 1))) = 0 := by
      linear_combination h3 - 10101 * h2 + 1010100 * h1 - 1000000 * h0
    omega

theorem a266841_small :
    a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 10100 ∧ a 3 = 101011 ∧ a 4 = 101010000 ∧ a 5 = 1010101111 := by
  have e0 := a266841_a_even 0
  have e1 := a266841_a_even 1
  have e2 := a266841_a_even 2
  have o0 := a266841_a_odd 0
  have o1 := a266841_a_odd 1
  have o2 := a266841_a_odd 2
  norm_num at e0 e1 e2 o0 o1 o2
  omega

open PowerSeries in
theorem a266841_gf :
    A = (1 + 10 * X - X ^ 2 + X ^ 3 - 110000 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ := by
  have hD : ((1 : ℚ⟦X⟧) - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) *
      (1 + 100 * X) = 1 - C (10101 : ℚ) * X ^ 2 + C (1010100 : ℚ) * X ^ 4 -
        C (1000000 : ℚ) * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hN : (1 : ℚ⟦X⟧) + 10 * X - X ^ 2 + X ^ 3 - 110000 * X ^ 5 =
      C (1 : ℚ) * X ^ 0 + C (10 : ℚ) * X ^ 1 - C (1 : ℚ) * X ^ 2 + C (1 : ℚ) * X ^ 3 -
        C (110000 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one, pow_zero, pow_one, one_mul, mul_one]
  rw [hD, hN, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have hA : A * (1 - C (10101 : ℚ) * X ^ 2 + C (1010100 : ℚ) * X ^ 4 -
        C (1000000 : ℚ) * X ^ 6) =
      A - C (10101 : ℚ) * (A * X ^ 2) + C (1010100 : ℚ) * (A * X ^ 4) -
        C (1000000 : ℚ) * (A * X ^ 6) := by ring
  rw [hA]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := a266841_small
  rcases k with _ | _ | _ | _ | _ | _ | j
  · norm_num [s0]
  · norm_num [s1]
  · norm_num [s0, s2]
  · norm_num [s1, s3]
  · norm_num [s0, s2, s4]
  · norm_num [s1, s3, s5]
  · have hr := a266841_rec (j + 6) (by omega)
    rw [show j + 6 - 2 = j + 4 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 6 = j by omega] at hr
    have hq : (a (j + 6) : ℚ) = 10101 * a (j + 4) - 1010100 * a (j + 2) + 1000000 * a j := by
      exact_mod_cast hr
    simp only [show 2 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 6 ≤ j + 6 by omega,
      if_true, show j + 6 - 2 = j + 4 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 6 = j by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 6 = 1) by omega,
      show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega, show ¬ (j + 6 = 5) by omega,
      if_false]
    simp only [show j + 1 + 1 + 1 + 1 + 1 + 1 = j + 6 by ring] at *
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a266841.main :=
  ⟨OMA.Helpers.a266841_rec, OMA.Helpers.a266841_gf, OMA.Helpers.a266841_oddQ,
    OMA.Helpers.a266841_evenQ⟩
