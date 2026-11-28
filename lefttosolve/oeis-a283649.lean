import OMAStatements.S_oeis_a283649
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a283649 PowerSeries

def ins283 (x : ℤ) : Bool := decide (-1 ≤ x ∧ x ≤ 1)
def z283 (x : ℤ) : Bool := decide (x = 0)

theorem ins283_lo {x : ℤ} (h : x ≤ -2) : ins283 x = false := by
  simp only [ins283, decide_eq_false_iff_not]; omega
theorem ins283_hi {x : ℤ} (h : 2 ≤ x) : ins283 x = false := by
  simp only [ins283, decide_eq_false_iff_not]; omega
theorem ins283_mid {x : ℤ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : ins283 x = true := by
  simp only [ins283, decide_eq_true_eq]; omega
theorem z283_ne {x : ℤ} (h : x ≠ 0) : z283 x = false := by
  simp only [z283, decide_eq_false_iff_not]; exact h
theorem z283_zero : z283 0 = true := rfl

theorem r283_f0 : rule false 0 = true := by decide
theorem r283_f1 : rule false 1 = false := by decide
theorem r283_f2 : rule false 2 = false := by decide
theorem r283_f3 : rule false 3 = true := by decide
theorem r283_f4 : rule false 4 = false := by decide
theorem r283_t0 : rule true 0 = false := by decide
theorem r283_t1 : rule true 1 = false := by decide
theorem r283_t2 : rule true 2 = false := by decide
theorem r283_t3 : rule true 3 = true := by decide
theorem r283_t4 : rule true 4 = true := by decide

def desc283 : ℕ → ℤ × ℤ → Bool
  | 0, p => z283 p.1 && z283 p.2
  | 1, p => !(ins283 p.1 && ins283 p.2 && (z283 p.1 || z283 p.2))
  | 2, p => !(ins283 p.1 && ins283 p.2 && !z283 p.1 && !z283 p.2)
  | t + 3, p => !(ins283 p.1 && ins283 p.2) || (z283 p.1 && z283 p.2 && decide (t % 2 = 0))

theorem step283_0 (p : ℤ × ℤ) :
    rule (desc283 0 p) ((nbrs p).countP (fun q => desc283 0 q)) = desc283 1 p := by
  obtain ⟨x, y⟩ := p
  have hx : x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x := by omega
  have hy : y ≤ -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 ∨ 3 ≤ y := by omega
  rcases hx with hx | rfl | rfl | rfl | rfl | rfl | hx <;>
  rcases hy with hy | rfl | rfl | rfl | rfl | rfl | hy <;>
  simp (disch := omega) [desc283, nbrs, List.countP_cons, List.countP_nil, ins283_lo, ins283_hi, ins283_mid, z283_ne, z283_zero,
    r283_f0, r283_f1, r283_f2, r283_f3, r283_f4, r283_t0, r283_t1, r283_t2, r283_t3, r283_t4]

theorem step283_1 (p : ℤ × ℤ) :
    rule (desc283 1 p) ((nbrs p).countP (fun q => desc283 1 q)) = desc283 2 p := by
  obtain ⟨x, y⟩ := p
  have hx : x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x := by omega
  have hy : y ≤ -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 ∨ 3 ≤ y := by omega
  rcases hx with hx | rfl | rfl | rfl | rfl | rfl | hx <;>
  rcases hy with hy | rfl | rfl | rfl | rfl | rfl | hy <;>
  simp (disch := omega) [desc283, nbrs, List.countP_cons, List.countP_nil, ins283_lo, ins283_hi,
    ins283_mid, z283_ne, z283_zero, r283_f0, r283_f1, r283_f2, r283_f3, r283_f4, r283_t0, r283_t1,
    r283_t2, r283_t3, r283_t4]

theorem step283_2 (p : ℤ × ℤ) :
    rule (desc283 2 p) ((nbrs p).countP (fun q => desc283 2 q)) = desc283 3 p := by
  obtain ⟨x, y⟩ := p
  have hx : x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x := by omega
  have hy : y ≤ -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 ∨ 3 ≤ y := by omega
  rcases hx with hx | rfl | rfl | rfl | rfl | rfl | hx <;>
  rcases hy with hy | rfl | rfl | rfl | rfl | rfl | hy <;>
  simp (disch := omega) [desc283, nbrs, List.countP_cons, List.countP_nil, ins283_lo, ins283_hi,
    ins283_mid, z283_ne, z283_zero, r283_f0, r283_f1, r283_f2, r283_f3, r283_f4, r283_t0, r283_t1,
    r283_t2, r283_t3, r283_t4]

theorem step283_e (t : ℕ) (ht : t % 2 = 0) (p : ℤ × ℤ) :
    rule (desc283 (t + 3) p) ((nbrs p).countP (fun q => desc283 (t + 3) q)) =
      desc283 ((t + 1) + 3) p := by
  have ht1 : (t + 1) % 2 = 1 := by omega
  obtain ⟨x, y⟩ := p
  have hx : x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x := by omega
  have hy : y ≤ -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 ∨ 3 ≤ y := by omega
  rcases hx with hx | rfl | rfl | rfl | rfl | rfl | hx <;>
  rcases hy with hy | rfl | rfl | rfl | rfl | rfl | hy <;>
  simp (disch := omega) [desc283, nbrs, List.countP_cons, List.countP_nil, ins283_lo, ins283_hi,
    ins283_mid, z283_ne, z283_zero, r283_f0, r283_f1, r283_f2, r283_f3, r283_f4, r283_t0, r283_t1,
    r283_t2, r283_t3, r283_t4, ht, ht1]

theorem step283_o (t : ℕ) (ht : t % 2 = 1) (p : ℤ × ℤ) :
    rule (desc283 (t + 3) p) ((nbrs p).countP (fun q => desc283 (t + 3) q)) =
      desc283 ((t + 1) + 3) p := by
  have ht1 : (t + 1) % 2 = 0 := by omega
  obtain ⟨x, y⟩ := p
  have hx : x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x := by omega
  have hy : y ≤ -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 ∨ 3 ≤ y := by omega
  rcases hx with hx | rfl | rfl | rfl | rfl | rfl | hx <;>
  rcases hy with hy | rfl | rfl | rfl | rfl | rfl | hy <;>
  simp (disch := omega) [desc283, nbrs, List.countP_cons, List.countP_nil, ins283_lo, ins283_hi,
    ins283_mid, z283_ne, z283_zero, r283_f0, r283_f1, r283_f2, r283_f3, r283_f4, r283_t0, r283_t1,
    r283_t2, r283_t3, r283_t4, ht, ht1]

theorem state283 (t : ℕ) : state t = desc283 t := by
  induction t with
  | zero =>
    funext p
    obtain ⟨x, y⟩ := p
    simp [state, desc283, z283]
  | succ t ih =>
    funext p
    show rule (state t p) ((nbrs p).countP (fun q => state t q)) = desc283 (t + 1) p
    rw [ih]
    rcases t with _ | _ | _ | t
    · exact step283_0 p
    · exact step283_1 p
    · exact step283_2 p
    · rcases Nat.mod_two_eq_zero_or_one t with ht | ht
      · exact step283_e t ht p
      · exact step283_o t ht p

theorem geo283 (j : ℕ) : 9 * ∑ i ∈ Finset.range (j + 1), 10 ^ (j - i) + 1 = 10 ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hs : ∑ i ∈ Finset.range (j + 1), 10 ^ (j + 1 - i) =
        10 * ∑ i ∈ Finset.range (j + 1), 10 ^ (j - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]
      ring
    rw [hs, Nat.sub_self, pow_zero, pow_succ 10 (j + 1)]
    omega

theorem key283 (m : ℕ) :
    9 * a (m + 3) + 1 = 10 ^ (m + 2) + (if m % 2 = 0 then 9 * 10 ^ (m + 3) else 0) := by
  unfold a
  rw [state283, Finset.sum_range_succ', Finset.sum_range_succ']
  have hs : ∑ i ∈ Finset.range (m + 2),
      (if desc283 (m + 3) (((i + 1 + 1 : ℕ) : ℤ), 0) = true then 10 ^ (m + 3 - (i + 1 + 1)) else 0)
      = ∑ i ∈ Finset.range (m + 1 + 1), 10 ^ (m + 1 - i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have h1 : ins283 (((i + 1 + 1 : ℕ) : ℤ)) = false := ins283_hi (by push_cast; omega)
    simp only [desc283, h1, Bool.false_and, Bool.not_false, Bool.true_or, if_true]
    congr 1
    omega
  rw [hs]
  have hg : 9 * ∑ i ∈ Finset.range (m + 1 + 1), 10 ^ (m + 1 - i) + 1 = 10 ^ (m + 2) :=
    geo283 (m + 1)
  have h1 : desc283 (m + 3) (((0 + 1 : ℕ) : ℤ), 0) = false := by
    simp [desc283, ins283_mid, z283_ne, z283_zero]
  have h0 : desc283 (m + 3) (((0 : ℕ) : ℤ), 0) = decide (m % 2 = 0) := by
    simp [desc283, ins283_mid, z283_zero]
  rw [h1, h0]
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · simp only [hm, decide_true, if_true, Bool.false_eq_true, if_false, Nat.sub_zero]
    rw [← hg]
    ring
  · simp only [hm, decide_false, Bool.false_eq_true, if_false, one_ne_zero]
    rw [← hg]
    ring

theorem closed283 (n : ℕ) (hn : 2 < n) :
    (a n : ℚ) = (-10 + 23 * 2 ^ (1 + n) * 5 ^ n - 9 * (-2) ^ n * 5 ^ (1 + n)) / 90 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hk := key283 m
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have hm : (j + j) % 2 = 0 := by omega
    rw [if_pos hm] at hk
    have hq : (9 * (a (j + j + 3) : ℚ) + 1) = 10 ^ (j + j + 2) + 9 * 10 ^ (j + j + 3) := by
      exact_mod_cast hk
    have hodd : Odd (j + j + 3) := ⟨j + 1, by ring⟩
    rw [Odd.neg_pow hodd]
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow, mul_pow] at hq
    linear_combination (1 / 9 : ℚ) * hq
  · subst hj
    have hm : ¬ (2 * j + 1) % 2 = 0 := by omega
    rw [if_neg hm] at hk
    have hq : (9 * (a (2 * j + 1 + 3) : ℚ) + 1) = 10 ^ (2 * j + 1 + 2) := by
      exact_mod_cast hk
    have hev : Even (2 * j + 1 + 3) := ⟨j + 2, by ring⟩
    rw [Even.neg_pow hev]
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow] at hq
    linear_combination (1 / 9 : ℚ) * hq

theorem rec283q (m : ℕ) :
    (a (m + 6) : ℚ) = a (m + 5) + 100 * a (m + 4) - 100 * a (m + 3) := by
  rw [closed283 (m + 6) (by omega), closed283 (m + 5) (by omega), closed283 (m + 4) (by omega),
    closed283 (m + 3) (by omega)]
  ring

theorem small283 : a 0 = 1 ∧ a 1 = 0 ∧ a 2 = 111 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem gf283 :
    A * ((1 - X) * (1 - 10 * X) * (1 + 10 * X)) =
      (1 - X + 11 * X ^ 2 + 1000 * X ^ 3 - 12000 * X ^ 4 + 11000 * X ^ 5 : ℚ⟦X⟧) := by
  obtain ⟨h0, h1, h2⟩ := small283
  have h3 : a 3 = 1011 := by
    have h := key283 0
    norm_num at h
    omega
  have h4 : a 4 = 111 := by
    have h := key283 1
    norm_num at h
    omega
  have h5 : a 5 = 101111 := by
    have h := key283 2
    norm_num at h
    omega
  have e1 : A * ((1 - X) * (1 - 10 * X) * (1 + 10 * X))
      = A - A * X ^ 1 - PowerSeries.C (100 : ℚ) * (A * X ^ 2)
        + PowerSeries.C (100 : ℚ) * (A * X ^ 3) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 - X + 11 * X ^ 2 + 1000 * X ^ 3 - 12000 * X ^ 4 + 11000 * X ^ 5 : ℚ⟦X⟧)
      = X ^ 0 - PowerSeries.C (1 : ℚ) * X ^ 1 + PowerSeries.C (11 : ℚ) * X ^ 2
        + PowerSeries.C (1000 : ℚ) * X ^ 3 - PowerSeries.C (12000 : ℚ) * X ^ 4
        + PowerSeries.C (11000 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, A,
    PowerSeries.coeff_mk]
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> simp [h0, h1, h2, h3, h4, h5] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    have c1 : 1 ≤ m + 6 := by omega
    have c2 : 2 ≤ m + 6 := by omega
    have c3 : 3 ≤ m + 6 := by omega
    have d0 : m + 6 ≠ 0 := by omega
    have d1 : m + 6 ≠ 1 := by omega
    have d2 : m + 6 ≠ 2 := by omega
    have d3 : m + 6 ≠ 3 := by omega
    have d4 : m + 6 ≠ 4 := by omega
    have d5 : m + 6 ≠ 5 := by omega
    simp only [c1, c2, c3, d0, d1, d2, d3, d4, d5, if_true, if_false]
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, rec283q m]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a283649.main := by
  refine ⟨?_, OMA.Helpers.closed283, ?_⟩
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    exact OMA.Helpers.gf283
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega]
    have h := OMA.Helpers.rec283q m
    exact_mod_cast h
