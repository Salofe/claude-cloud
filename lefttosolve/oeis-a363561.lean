import OMAStatements.S_oeis_a363561
import Mathlib

namespace OMA.Helpers

open PowerSeries Finset OMA.S_oeis_a363561

theorem a363561_binom (c : ℝ) (n k : ℕ) :
    coeff k ((C c + X : PowerSeries ℝ) ^ n) = c ^ (n - k) * (n.choose k : ℝ) := by
  have h : (C c + X : PowerSeries ℝ) =
      ((Polynomial.X + Polynomial.C c : Polynomial ℝ) : PowerSeries ℝ) := by
    rw [Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, add_comm]
  rw [h, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_X_add_C_pow]

theorem a363561_pos (c : ℝ) (n N : ℕ) (hn : n ≠ 0) :
    coeff N (posTerm c n) = if n ≤ N then (if n ∣ (N - n) then
      c ^ (2 * n - (N - n) / n) * ((2 * n).choose ((N - n) / n) : ℝ) else 0) else 0 := by
  have e : (C c + X ^ n : PowerSeries ℝ) ^ (2 * n) = expand n hn ((C c + X) ^ (2 * n)) := by
    rw [map_pow, map_add, expand_C, expand_X]
  rw [posTerm, coeff_X_pow_mul', e, coeff_expand, a363561_binom]

theorem a363561_geom_pow (c : ℝ) (j r : ℕ) (hj : j ≠ 0) :
    coeff r ((PowerSeries.mk fun k => (-c) ^ k : PowerSeries ℝ) ^ (2 * j)) =
      (-c) ^ r * ((2 * j - 1 + r).choose (2 * j - 1) : ℝ) := by
  have e : (PowerSeries.mk fun k => (-c) ^ k : PowerSeries ℝ) = rescale (-c) (mk 1) := by
    rw [rescale_mk]; simp
  obtain ⟨d, hd⟩ : ∃ d, 2 * j = d + 1 := ⟨2 * j - 1, by omega⟩
  rw [e, ← map_pow, hd, mk_one_pow_eq_mk_choose_add, coeff_rescale, coeff_mk, Nat.add_sub_cancel]

theorem a363561_neg (c : ℝ) (j N : ℕ) (hj : j ≠ 0) :
    coeff N (negTerm c j) = if 2 * j ^ 2 - j ≤ N then (if j ∣ (N - (2 * j ^ 2 - j)) then
      (-c) ^ ((N - (2 * j ^ 2 - j)) / j) *
        ((2 * j - 1 + (N - (2 * j ^ 2 - j)) / j).choose (2 * j - 1) : ℝ) else 0) else 0 := by
  have e : invGeom c j = expand j hj (PowerSeries.mk fun k => (-c) ^ k) := by
    ext k; rw [coeff_expand, invGeom, coeff_mk, coeff_mk]
  rw [negTerm, coeff_X_pow_mul', e, ← map_pow, coeff_expand, a363561_geom_pow c j _ hj]

theorem a363561_pair (c : ℝ) (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    coeff (2 * a * b) (posTerm c a) + coeff (2 * a * b) (negTerm c b) = 0 := by
  rw [a363561_pos c a _ ha, a363561_neg c b _ hb]
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have h1 : 2 * a * (b' + 1) - a = a * (2 * b' + 1) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : a ≤ 2 * a * (b' + 1) := by nlinarith
  have h4 : 2 * (b' + 1) ^ 2 - (b' + 1) = (b' + 1) * (2 * b' + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h7 : 2 * (b' + 1) - 1 = 2 * b' + 1 := by omega
  rw [if_pos h2, h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha),
    h4, h7]
  by_cases hab : 2 * b' + 1 ≤ 2 * a
  · obtain ⟨s, hs⟩ : ∃ s, 2 * a = 2 * b' + 1 + s := ⟨2 * a - (2 * b' + 1), by omega⟩
    have hodd : Odd s := ⟨a - b' - 1, by omega⟩
    have h6 : 2 * a * (b' + 1) - (b' + 1) * (2 * b' + 1) = (b' + 1) * s :=
      Nat.sub_eq_of_eq_add (by rw [hs]; ring)
    have h8 : (b' + 1) * (2 * b' + 1) ≤ 2 * a * (b' + 1) := by
      rw [hs]; nlinarith
    rw [if_pos h8, h6, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.succ_pos b'), hs,
      Nat.add_sub_cancel_left, hodd.neg_pow]
    ring
  · have h8 : ¬ (b' + 1) * (2 * b' + 1) ≤ 2 * a * (b' + 1) := by
      intro h
      apply hab
      have h' : (b' + 1) * (2 * b' + 1) ≤ (b' + 1) * (2 * a) := by
        calc (b' + 1) * (2 * b' + 1) ≤ 2 * a * (b' + 1) := h
          _ = (b' + 1) * (2 * a) := by ring
      exact Nat.le_of_mul_le_mul_left h' (Nat.succ_pos b')
    rw [if_neg h8, Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem a363561_pos_zero (c : ℝ) (n N : ℕ) (hn : n ≠ 0) (hd : ¬ n ∣ N) :
    coeff N (posTerm c n) = 0 := by
  rw [a363561_pos c n N hn]
  split_ifs with h1 h2
  · exfalso; apply hd
    have e : N = (N - n) + n := by omega
    rw [e]; exact dvd_add h2 dvd_rfl
  · rfl
  · rfl

theorem a363561_neg_zero (c : ℝ) (n N : ℕ) (hn : n ≠ 0) (hd : ¬ n ∣ N) :
    coeff N (negTerm c n) = 0 := by
  rw [a363561_neg c n N hn]
  split_ifs with h1 h2
  · exfalso; apply hd
    have e : N = (N - (2 * n ^ 2 - n)) + (2 * n ^ 2 - n) := by omega
    have h3 : n ∣ 2 * n ^ 2 - n := Nat.dvd_sub (Dvd.intro (2 * n) (by ring)) dvd_rfl
    rw [e]; exact dvd_add h2 h3
  · rfl
  · rfl

/-- The `n`-th summand of the coefficient of `x^N` in `A`. -/
noncomputable def a363561f (N n : ℕ) : ℝ :=
  coeff N (posTerm (Real.sqrt 2) n) + coeff N (negTerm (Real.sqrt 2) n)

theorem a363561_coeffA (N : ℕ) (hN : N ≠ 0) :
    coeff N A = ∑ n ∈ N.divisors, a363561f N n := by
  rw [A, coeff_mk, if_neg hN, zero_add]
  symm
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hn, Nat.divisor_le hn⟩
  · intro n hn hnd
    rw [Finset.mem_Icc] at hn
    have hd : ¬ n ∣ N := fun h => hnd (Nat.mem_divisors.mpr ⟨h, hN⟩)
    rw [a363561f, a363561_pos_zero _ _ _ (by omega) hd, a363561_neg_zero _ _ _ (by omega) hd,
      add_zero]

theorem a363561_cpow (k : ℕ) : Real.sqrt 2 ^ (2 * k) = 2 ^ k := by
  rw [pow_mul, Real.sq_sqrt (by norm_num)]

theorem a363561_top (N : ℕ) (hN : 2 ≤ N) : a363561f N N = 2 ^ N := by
  rw [a363561f, a363561_pos _ _ _ (by omega), a363561_neg _ _ _ (by omega)]
  have hx : 2 * N ≤ N * N := Nat.mul_le_mul_right N hN
  have hneg : ¬ 2 * N ^ 2 - N ≤ N := by rw [pow_two]; omega
  rw [if_neg hneg, if_pos le_rfl, Nat.sub_self, if_pos (dvd_zero N), Nat.zero_div,
    Nat.sub_zero, Nat.choose_zero_right, a363561_cpow]
  simp

theorem a363561_part1 (m : ℕ) (hm : 0 < m) : coeff (2 ^ m) A = (2 : ℝ) ^ (2 ^ m) := by
  rw [a363561_coeffA _ (by positivity), Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ, a363561_top _ (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)]
  simp only [a363561f]
  rw [Finset.sum_add_distrib,
    ← Finset.sum_range_reflect (fun i => coeff (2 ^ m) (negTerm (Real.sqrt 2) (2 ^ i))) m,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [Finset.mem_range] at hi
  have e : 2 ^ m = 2 * 2 ^ i * 2 ^ (m - 1 - i) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [e]
  exact a363561_pair _ _ _ (by positivity) (by positivity)

theorem a363561_part2 (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    coeff p A = (p : ℝ) * (2 : ℝ) ^ ((p - 1) / 2) + (2 : ℝ) ^ p := by
  rw [a363561_coeffA _ hp.ne_zero, Nat.Prime.divisors hp, Finset.sum_pair (by omega),
    a363561_top _ hp.two_le, a363561f, a363561_pos _ _ _ (by norm_num : (1 : ℕ) ≠ 0),
    a363561_neg _ _ _ (by norm_num : (1 : ℕ) ≠ 0)]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hev : Even (p - 1) := ⟨(p - 1) / 2, by omega⟩
  have e1 : 2 * 1 ^ 2 - 1 = 1 := by norm_num
  rw [e1, if_pos hp.one_le, if_pos (one_dvd _), if_pos hp.one_le, if_pos (one_dvd _),
    Nat.div_one, Nat.choose_eq_zero_of_lt (by omega : 2 * 1 < p - 1),
    hev.neg_pow]
  have e2 : 2 * 1 - 1 + (p - 1) = p := by omega
  have e3 : p - 1 = 2 * ((p - 1) / 2) := by omega
  rw [e2, Nat.choose_one_right]
  have e4 : Real.sqrt 2 ^ (p - 1) = 2 ^ ((p - 1) / 2) := by
    rw [← a363561_cpow]; congr 1
  rw [e4, Nat.cast_zero, mul_zero, zero_add]
  ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a363561.main :=
  ⟨a363561_part1, a363561_part2⟩
