import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1

/-!
# Step H1 of the reduction Erdos542.erdos_542.variants.only_two.R1

For 12 <= n <= 100 the inequality is checked by the kernel in exact rational arithmetic.
For n >= 100 both sums are written as differences of harmonic blocks over (a, b] (removing
the multiples of 3, which form a dilated block), every block is bounded by logarithms via
1/(m+1) <= log(m+1) - log m <= 1/m, the floors are compared with n/2, n/3, n/6, n/9,
and the resulting combination of logarithms is the logarithm of an explicit rational
function of n, which is at most 54 < e^4 for n >= 100.
-/

open Finset

namespace OMA.Helpers

theorem e542_step_upper (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.log_le_sub_one_of_pos (x := (m : ℝ) / ((m : ℝ) + 1)) (by positivity)
  rw [Real.log_div hm0.ne' (by positivity)] at h
  have e : (m : ℝ) / ((m : ℝ) + 1) - 1 = -((1 : ℝ) / ((m : ℝ) + 1)) := by
    field_simp
    ring
  linarith

theorem e542_step_lower (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((m : ℝ) + 1) - Real.log m ≤ (1 : ℝ) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.log_le_sub_one_of_pos (x := ((m : ℝ) + 1) / (m : ℝ)) (by positivity)
  rw [Real.log_div (by positivity) hm0.ne'] at h
  have e : ((m : ℝ) + 1) / (m : ℝ) - 1 = (1 : ℝ) / m := by
    field_simp
    ring
  linarith

theorem e542_T_upper (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Ioc a b, (1 : ℝ) / m ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ioc_succ_top hb]
    have h := e542_step_upper b (le_trans ha hb)
    push_cast
    linarith

theorem e542_T_lower (a b : ℕ) (hab : a ≤ b) :
    Real.log ((b : ℝ) + 1) - Real.log ((a : ℝ) + 1) ≤ ∑ m ∈ Ioc a b, (1 : ℝ) / m := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ioc_succ_top hb]
    have h := e542_step_lower (b + 1) (by omega)
    push_cast at h ⊢
    linarith

theorem e542_S1 (n : ℕ) :
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m =
      ∑ m ∈ Ioc (n / 2) n, (1 : ℝ) / m - (1 / 3) * ∑ k ∈ Ioc (n / 6) (n / 3), (1 : ℝ) / k := by
  have hA : (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0) =
      (Ioc (n / 2) n).filter (fun m => m % 3 ≠ 0) := by
    ext m
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  have hB : (Ioc (n / 2) n).filter (fun m => ¬ m % 3 ≠ 0) =
      (Ioc (n / 6) (n / 3)).image (fun k => 3 * k) := by
    ext m
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨m / 3, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (Ioc (n / 2) n) (fun m => m % 3 ≠ 0)
    (fun m => (1 : ℝ) / m)
  rw [hB, Finset.sum_image (by intro x _ y _ h; simp only at h; omega)] at hsplit
  have h3 : ∑ k ∈ Ioc (n / 6) (n / 3), (1 : ℝ) / ((3 * k : ℕ) : ℝ) =
      (1 / 3) * ∑ k ∈ Ioc (n / 6) (n / 3), (1 : ℝ) / k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    push_cast
    rw [one_div_mul_one_div]
  rw [hA]
  linarith

theorem e542_S2 (n : ℕ) :
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) =
      (1 / 2) * (∑ b ∈ Ioc (n / 3) (n / 2), (1 : ℝ) / b -
        (1 / 3) * ∑ k ∈ Ioc (n / 9) (n / 6), (1 : ℝ) / k) := by
  have hA : (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0) =
      (Ioc (n / 3) (n / 2)).filter (fun m => m % 3 ≠ 0) := by
    ext m
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  have hB : (Ioc (n / 3) (n / 2)).filter (fun m => ¬ m % 3 ≠ 0) =
      (Ioc (n / 9) (n / 6)).image (fun k => 3 * k) := by
    ext m
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨m / 3, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (Ioc (n / 3) (n / 2)) (fun m => m % 3 ≠ 0)
    (fun m => (1 : ℝ) / m)
  rw [hB, Finset.sum_image (by intro x _ y _ h; simp only at h; omega)] at hsplit
  have h3 : ∑ k ∈ Ioc (n / 9) (n / 6), (1 : ℝ) / ((3 * k : ℕ) : ℝ) =
      (1 / 3) * ∑ k ∈ Ioc (n / 9) (n / 6), (1 : ℝ) / k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    push_cast
    rw [one_div_mul_one_div]
  have h2 : ∑ b ∈ (Ioc (n / 3) (n / 2)).filter (fun m => m % 3 ≠ 0), (1 : ℝ) / (2 * b) =
      (1 / 2) * ∑ b ∈ (Ioc (n / 3) (n / 2)).filter (fun m => m % 3 ≠ 0), (1 : ℝ) / b := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [one_div_mul_one_div]
  rw [hA, h2]
  linarith

theorem e542_poly (t : ℝ) (ht : 0 ≤ t) :
    (t + 100) ^ 6 * ((t + 100) / 6 + 1) * ((t + 100) / 9 + 1) ≤
      54 * (((t + 100 - 1) / 2) ^ 3 * ((t + 100 - 2) / 3) ^ 3 * ((t + 100) / 3) ^ 2) := by
  have h : 0 ≤ (t + 100) ^ 2 * (428912969224 + 31458369492 * t + 929403498 * t ^ 2 +
      14296211 * t ^ 3 + 121491 * t ^ 4 + 543 * t ^ 5 + t ^ 6) := by positivity
  nlinarith [h]

theorem e542_log_combo (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f) :
    Real.log (a ^ 6 * b * c / (d ^ 3 * e ^ 3 * f ^ 2)) =
      6 * Real.log a + Real.log b + Real.log c - 3 * Real.log d - 3 * Real.log e -
        2 * Real.log f := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

theorem e542_large (n : ℕ) (hn : 100 ≤ n) :
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) ≤ 2 / 3 := by
  rw [e542_S1, e542_S2]
  have u1 := e542_T_upper (n / 2) n (by omega) (by omega)
  have u2 := e542_T_upper (n / 3) (n / 2) (by omega) (by omega)
  have l1 := e542_T_lower (n / 6) (n / 3) (by omega)
  have l2 := e542_T_lower (n / 9) (n / 6) (by omega)
  set x : ℝ := (n : ℝ) with hx
  set q2 : ℝ := ((n / 2 : ℕ) : ℝ) with hq2
  set q3 : ℝ := ((n / 3 : ℕ) : ℝ) with hq3
  set q6 : ℝ := ((n / 6 : ℕ) : ℝ) with hq6
  set q9 : ℝ := ((n / 9 : ℕ) : ℝ) with hq9
  have hx100 : (100 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have f2 : x - 1 ≤ 2 * q2 := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have f3 : x - 2 ≤ 3 * q3 := by
    have : n ≤ 3 * (n / 3) + 2 := by omega
    have : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast this
    linarith
  have f6 : 6 * q6 ≤ x := by
    have : 6 * (n / 6) ≤ n := by omega
    have : 6 * ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have f9 : 9 * q9 ≤ x := by
    have : 9 * (n / 9) ≤ n := by omega
    have : 9 * ((n / 9 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have q6nn : 0 ≤ q6 := by positivity
  have q9nn : 0 ≤ q9 := by positivity
  have g2 : Real.log ((x - 1) / 2) ≤ Real.log q2 :=
    Real.log_le_log (by linarith) (by linarith)
  have g3 : Real.log ((x - 2) / 3) ≤ Real.log q3 :=
    Real.log_le_log (by linarith) (by linarith)
  have g3' : Real.log (x / 3) ≤ Real.log (q3 + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have g6 : Real.log (q6 + 1) ≤ Real.log (x / 6 + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have g9 : Real.log (q9 + 1) ≤ Real.log (x / 9 + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hpos1 : 0 < (x - 1) / 2 := by linarith
  have hpos2 : 0 < (x - 2) / 3 := by linarith
  have hpos3 : 0 < x / 3 := by linarith
  have hpos6 : 0 < x / 6 + 1 := by linarith
  have hpos9 : 0 < x / 9 + 1 := by linarith
  have hxpos : 0 < x := by linarith
  have hcomb : 6 * Real.log x + Real.log (x / 6 + 1) + Real.log (x / 9 + 1) -
      3 * Real.log ((x - 1) / 2) - 3 * Real.log ((x - 2) / 3) - 2 * Real.log (x / 3) =
      Real.log (x ^ 6 * (x / 6 + 1) * (x / 9 + 1) /
        (((x - 1) / 2) ^ 3 * ((x - 2) / 3) ^ 3 * (x / 3) ^ 2)) := by
    rw [e542_log_combo x (x / 6 + 1) (x / 9 + 1) ((x - 1) / 2) ((x - 2) / 3) (x / 3)
      hxpos hpos6 hpos9 hpos1 hpos2 hpos3]
  have hbig : x ^ 6 * (x / 6 + 1) * (x / 9 + 1) /
        (((x - 1) / 2) ^ 3 * ((x - 2) / 3) ^ 3 * (x / 3) ^ 2) ≤ 54 := by
    rw [div_le_iff₀ (by positivity)]
    have := e542_poly (x - 100) (by linarith)
    simp only [sub_add_cancel] at this
    linarith
  have hexp : (54 : ℝ) ≤ Real.exp 4 := by
    have h1 := Real.exp_one_gt_d9
    have e : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    have : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
      pow_le_pow_left₀ (by norm_num) h1.le 4
    have h2 : (54 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 := by norm_num
    linarith
  have hlog : Real.log (x ^ 6 * (x / 6 + 1) * (x / 9 + 1) /
        (((x - 1) / 2) ^ 3 * ((x - 2) / 3) ^ 3 * (x / 3) ^ 2)) ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    linarith
  linarith

end OMA.Helpers

namespace OMA.Helpers

theorem e542_small : ∀ n ∈ Finset.Icc (12 : ℕ) 100,
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / m +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℚ) / (2 * b) ≤ 2 / 3 := by
  decide +kernel

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos542_erdos_542_variants_only_two_R1.H1 := by
  intro n hn
  by_cases h : n ≤ 100
  · have hq := OMA.Helpers.e542_small n (Finset.mem_Icc.mpr ⟨hn, h⟩)
    have hr : ((∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / m +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℚ) / (2 * b) : ℚ) : ℝ) ≤ ((2 / 3 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    push_cast at hr
    exact hr
  · exact OMA.Helpers.e542_large n (by omega)
