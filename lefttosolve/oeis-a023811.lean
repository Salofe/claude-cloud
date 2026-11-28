import OMAStatements.S_oeis_a023811
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a023811 Filter Topology

theorem sum_closed (x : ℝ) (N : ℕ) :
    (x - 1) ^ 2 * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * x ^ (N - k) =
      x ^ (N + 1) - (N + 1) * x + N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * x ^ (N + 1 - k) =
        x * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * x ^ (N - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [show N + 1 - k = (N - k) + 1 by omega, pow_succ]
      ring
    rw [hs, Nat.sub_self, pow_zero, mul_add, ← mul_assoc, mul_comm ((x - 1) ^ 2) x, mul_assoc, ih]
    push_cast
    ring

theorem a_real (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℝ) * ((n : ℝ) - 1) ^ 2 = (n : ℝ) ^ n - ((n : ℝ) ^ 2 - n + 1) := by
  have h := sum_closed (n : ℝ) (n - 1)
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc, show n - 1 + 1 = n by omega] at h
  unfold a
  push_cast
  rw [mul_comm, h]
  ring

theorem log_est {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 2) :
    |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * y ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y)
    (by rw [abs_neg, abs_of_pos hy0]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos hy0,
    sub_neg_eq_add] at h
  norm_num at h
  have e1 : -y + y ^ 2 / 2 + Real.log (1 + y) = Real.log (1 + y) - (y - y ^ 2 / 2) := by ring
  rw [e1] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos hy0 3]

theorem E_le (m : ℕ) (hm : 1 ≤ m) : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
  have h1 : 1 + 1 / (m : ℝ) ≤ Real.exp (1 / m) := by
    have := Real.add_one_le_exp (1 / (m : ℝ)); linarith
  calc (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp (1 / m) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
    _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        field_simp

theorem E_est (k : ℕ) (hk : 2 ≤ k) :
    |(1 + 1 / (k : ℝ)) ^ k - Real.exp 1 * (1 - 1 / (2 * k))| ≤ 13 / (k : ℝ) ^ 2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set y : ℝ := 1 / k with hy
  have hy0 : 0 < y := by positivity
  have hy2 : y ≤ 1 / 2 := by
    rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hk'
  have hky : (k : ℝ) * y = 1 := by rw [hy]; field_simp
  have hlog := log_est hy0 hy2
  set η : ℝ := k * Real.log (1 + y) - 1 with hη
  have hη1 : |η + y / 2| ≤ 2 * y ^ 2 := by
    have e : η + y / 2 = k * (Real.log (1 + y) - (y - y ^ 2 / 2)) := by
      rw [hη]
      have : (k : ℝ) * (y - y ^ 2 / 2) = 1 - y / 2 := by
        have : (k : ℝ) * y ^ 2 = y := by rw [pow_two, ← mul_assoc, hky, one_mul]
        linear_combination hky - this / 2
      linear_combination this
    rw [e, abs_mul, abs_of_pos (by positivity)]
    calc (k : ℝ) * |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ k * (2 * y ^ 3) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 2 * y ^ 2 := by
          have : (k : ℝ) * y ^ 3 = y ^ 2 := by
            rw [pow_succ, mul_comm (y ^ 2) y, ← mul_assoc, hky, one_mul]
          linear_combination 2 * this
  have hηb : |η| ≤ 3 * y / 2 := by
    have := abs_le.1 hη1
    rw [abs_le]; constructor <;> nlinarith
  have hexp := Real.abs_exp_sub_one_sub_id_le (x := η) (by nlinarith)
  have hE : (1 + y) ^ k = Real.exp 1 * Real.exp η := by
    rw [← Real.exp_add, hη, show (1 : ℝ) + (k * Real.log (1 + y) - 1) = k * Real.log (1 + y) by ring,
      Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hsplit : (1 + y) ^ k - Real.exp 1 * (1 - 1 / (2 * k)) =
      Real.exp 1 * ((Real.exp η - 1 - η) + (η + y / 2)) := by
    rw [hE]
    have : 1 / (2 * (k : ℝ)) = y / 2 := by rw [hy]; field_simp
    rw [this]; ring
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hy2' : 13 / (k : ℝ) ^ 2 = 13 * y ^ 2 := by rw [hy]; field_simp
  rw [hsplit, hy2', abs_mul, abs_of_pos he0]
  have h1 := abs_add_le (Real.exp η - 1 - η) (η + y / 2)
  have hη2 : η ^ 2 ≤ 9 / 4 * y ^ 2 := by
    have := sq_abs η
    nlinarith [abs_nonneg η]
  calc Real.exp 1 * |Real.exp η - 1 - η + (η + y / 2)|
      ≤ Real.exp 1 * (9 / 4 * y ^ 2 + 2 * y ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ he0.le
        linarith
    _ ≤ 13 * y ^ 2 := by nlinarith [pow_pos hy0 2]

end OMA.Helpers

namespace OMA.Helpers
open OMA.S_oeis_a023811 Filter Topology

/-- The main term of the ratio `a (k + 1) / a k`. -/
noncomputable def w (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 * (1 + 1 / (k : ℝ)) ^ k

theorem w_est (k : ℕ) (hk : 2 ≤ k) :
    |w k - Real.exp 1 * ((k : ℝ) - 3 / 2)| ≤ 25 / (k : ℝ) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set c : ℝ := ((k : ℝ) + 1) * ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 3 / 2 * k := by
    rw [hc, div_le_iff₀ (by positivity)]
    nlinarith
  set E : ℝ := (1 + 1 / (k : ℝ)) ^ k with hE
  have hEst := E_est k hk
  have hid : c * (1 - 1 / (2 * k)) - ((k : ℝ) - 3 / 2) =
      (-(k : ℝ) ^ 2 + 3 * k - 1) / (2 * (k : ℝ) ^ 3) := by
    rw [hc]; field_simp; ring
  have hsplit : w k - Real.exp 1 * ((k : ℝ) - 3 / 2) =
      c * (E - Real.exp 1 * (1 - 1 / (2 * k))) +
        Real.exp 1 * (c * (1 - 1 / (2 * k)) - ((k : ℝ) - 3 / 2)) := by
    rw [w]; ring
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hX : |(-(k : ℝ) ^ 2 + 3 * k - 1) / (2 * (k : ℝ) ^ 3)| ≤ 11 / (8 * (k : ℝ)) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (k : ℝ) ^ 3),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hN : |(-(k : ℝ) ^ 2 + 3 * k - 1)| ≤ (k : ℝ) ^ 2 + 3 * k + 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ 8 * k)
    nlinarith
  have h1 : |c * (E - Real.exp 1 * (1 - 1 / (2 * k)))| ≤ 39 / (2 * (k : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |E - Real.exp 1 * (1 - 1 / (2 * k))| ≤ 3 / 2 * k * (13 / (k : ℝ) ^ 2) :=
          mul_le_mul hc1 hEst (abs_nonneg _) (by positivity)
      _ = 39 / (2 * (k : ℝ)) := by field_simp; ring
  have h2 : |Real.exp 1 * (c * (1 - 1 / (2 * k)) - ((k : ℝ) - 3 / 2))| ≤
      3 * (11 / (8 * (k : ℝ))) := by
    rw [abs_mul, abs_of_pos he0, hid]
    exact mul_le_mul he3.le hX (abs_nonneg _) (by norm_num)
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have e : 39 / (2 * (k : ℝ)) + 3 * (11 / (8 * (k : ℝ))) = 189 / (8 * (k : ℝ)) := by
    field_simp; ring
  have : 189 / (8 * (k : ℝ)) ≤ 25 / k := by
    rw [div_le_div_iff₀ (by positivity) hk0]; nlinarith
  linarith

theorem Q_big (x Q : ℝ) (hx : 10 ≤ x) (hQ6 : (x - 1) ^ 6 ≤ Q) : 4 * x ^ 4 + x ^ 2 ≤ Q := by
  have hu : (9 : ℝ) ≤ x - 1 := by linarith
  have hxu : x ≤ 2 * (x - 1) := by linarith
  have h4 : x ^ 4 ≤ 16 * (x - 1) ^ 4 := by
    have := pow_le_pow_left₀ (by linarith) hxu 4
    rw [mul_pow] at this; norm_num at this; linarith
  have hu2 : (81 : ℝ) ≤ (x - 1) ^ 2 := by nlinarith
  have h2a : x ^ 2 ≤ 4 * (x - 1) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hxu 2
    rw [mul_pow] at this; norm_num at this; linarith
  have hu4 : (x - 1) ^ 4 = (x - 1) ^ 2 * (x - 1) ^ 2 := by ring
  have h2b : 4 * (x - 1) ^ 2 ≤ (x - 1) ^ 4 := by
    rw [hu4]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hu6 : (x - 1) ^ 6 = (x - 1) ^ 2 * (x - 1) ^ 4 := by ring
  have h6 : 81 * (x - 1) ^ 4 ≤ (x - 1) ^ 6 := by
    rw [hu6]; exact mul_le_mul_of_nonneg_right hu2 (by positivity)
  linarith

theorem core_ineq (x P Q q0 q1 : ℝ) (hx : 10 ≤ x) (hP0 : 0 ≤ P) (hP3 : P ≤ 3 * x * Q)
    (hQbig : 4 * x ^ 4 + x ^ 2 ≤ Q) (hq0 : 0 ≤ q0 ∧ q0 ≤ x ^ 2) (hq1 : 0 ≤ q1 ∧ q1 ≤ x ^ 2) :
    |(P * q0 - q1 * Q) / ((Q - q0) * Q)| ≤ 1 / x := by
  have hx0 : 0 < x := by linarith
  have hx4 : 0 < x ^ 4 := by positivity
  have hx2 : 0 ≤ x ^ 2 := by positivity
  have hQpos : 0 < Q := by linarith
  have hQq : 0 < Q - q0 := by linarith
  rw [abs_div, abs_of_pos (mul_pos hQq hQpos), div_le_div_iff₀ (mul_pos hQq hQpos) hx0]
  have hab : |P * q0 - q1 * Q| ≤ P * q0 + q1 * Q := by
    rw [abs_le]; constructor <;> linarith [mul_nonneg hP0 hq0.1, mul_nonneg hq1.1 hQpos.le]
  have j0 : |P * q0 - q1 * Q| * x ≤ (P * q0 + q1 * Q) * x := mul_le_mul_of_nonneg_right hab hx0.le
  have j1 : P * q0 ≤ 3 * x * Q * x ^ 2 := mul_le_mul hP3 hq0.2 hq0.1 (by positivity)
  have j1' : P * q0 * x ≤ 3 * x * Q * x ^ 2 * x := mul_le_mul_of_nonneg_right j1 hx0.le
  have j2 : q1 * Q ≤ x ^ 2 * Q := mul_le_mul_of_nonneg_right hq1.2 hQpos.le
  have j2' : q1 * Q * x ≤ x ^ 2 * Q * x := mul_le_mul_of_nonneg_right j2 hx0.le
  have j3 : 4 * x ^ 4 * Q ≤ (Q - q0) * Q := mul_le_mul_of_nonneg_right (by linarith) hQpos.le
  have j4 : x ^ 3 ≤ x ^ 4 := by
    have : x ^ 3 * 1 ≤ x ^ 3 * x := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [show x ^ 3 * x = x ^ 4 by ring]
  have j4' : x ^ 3 * Q ≤ x ^ 4 * Q := mul_le_mul_of_nonneg_right j4 hQpos.le
  have e1 : 3 * x * Q * x ^ 2 * x = 3 * (x ^ 4 * Q) := by ring
  have e2 : x ^ 2 * Q * x = x ^ 3 * Q := by ring
  have e3 : (P * q0 + q1 * Q) * x = P * q0 * x + q1 * Q * x := by ring
  rw [one_mul]
  linarith

theorem diff_id (x P Q q0 q1 : ℝ) (_h1 : (x - 1) ^ 2 ≠ 0) (_h2 : (x - 2) ^ 2 ≠ 0) (hQ : Q ≠ 0)
    (hQq : Q - q0 ≠ 0) :
    (P - q1) / (x - 1) ^ 2 / ((Q - q0) / (x - 2) ^ 2) - (x - 2) ^ 2 / (x - 1) ^ 2 * (P / Q) =
      (x - 2) ^ 2 / (x - 1) ^ 2 * ((P * q0 - q1 * Q) / ((Q - q0) * Q)) := by
  field_simp
  ring

theorem r_close (n : ℕ) (hn : 10 ≤ n) :
    |(a n : ℝ) / (a (n - 1) : ℝ) - w (n - 1)| ≤ 1 / (n : ℝ) := by
  have hx10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hx1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hx2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hx1s : ((n : ℝ) - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hx1
  have hx2s : ((n : ℝ) - 2) ^ 2 ≠ 0 := pow_ne_zero 2 hx2
  have ha1 : (a n : ℝ) = ((n : ℝ) ^ n - ((n : ℝ) ^ 2 - n + 1)) / ((n : ℝ) - 1) ^ 2 := by
    rw [eq_div_iff hx1s]; exact a_real n (by omega)
  have ha0 : (a (n - 1) : ℝ) = (((n : ℝ) - 1) ^ (n - 1) - (((n : ℝ) - 1) ^ 2 - ((n : ℝ) - 1) + 1)) /
      ((n : ℝ) - 2) ^ 2 := by
    have h := a_real (n - 1) (by omega)
    rw [hc1, show (n : ℝ) - 1 - 1 = (n : ℝ) - 2 by ring] at h
    rw [eq_div_iff hx2s]
    exact h
  have hQ6 : ((n : ℝ) - 1) ^ 6 ≤ ((n : ℝ) - 1) ^ (n - 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hQbig := Q_big (n : ℝ) _ hx10 hQ6
  have hPQ : (n : ℝ) ^ n = (n : ℝ) * (1 + 1 / ((n : ℝ) - 1)) ^ (n - 1) * ((n : ℝ) - 1) ^ (n - 1) := by
    rw [mul_assoc, ← mul_pow,
      show (1 + 1 / ((n : ℝ) - 1)) * ((n : ℝ) - 1) = n by rw [add_mul, one_div, inv_mul_cancel₀ hx1]; ring,
      ← pow_succ', show n - 1 + 1 = n by omega]
  have hE := E_le (n - 1) (by omega)
  rw [hc1] at hE
  have hQpos : 0 < ((n : ℝ) - 1) ^ (n - 1) := pow_pos (by linarith) _
  have hP3 : (n : ℝ) ^ n ≤ 3 * n * ((n : ℝ) - 1) ^ (n - 1) := by
    rw [hPQ]
    have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have : (n : ℝ) * (1 + 1 / ((n : ℝ) - 1)) ^ (n - 1) ≤ 3 * n := by
      have := mul_le_mul_of_nonneg_left (hE.trans he3.le) (by linarith : (0 : ℝ) ≤ n)
      linarith
    exact mul_le_mul_of_nonneg_right this hQpos.le
  have hw : w (n - 1) = ((n : ℝ) - 2) ^ 2 / ((n : ℝ) - 1) ^ 2 *
      ((n : ℝ) ^ n / ((n : ℝ) - 1) ^ (n - 1)) := by
    rw [w, hc1, show (n : ℝ) - 1 - 1 = (n : ℝ) - 2 by ring, show (n : ℝ) - 1 + 1 = n by ring, hPQ]
    field_simp
  have hq0 : 0 ≤ ((n : ℝ) - 1) ^ 2 - ((n : ℝ) - 1) + 1 ∧
      ((n : ℝ) - 1) ^ 2 - ((n : ℝ) - 1) + 1 ≤ (n : ℝ) ^ 2 := by
    constructor <;> nlinarith
  have hq1 : 0 ≤ (n : ℝ) ^ 2 - n + 1 ∧ (n : ℝ) ^ 2 - n + 1 ≤ (n : ℝ) ^ 2 := by
    constructor <;> nlinarith
  have hQq : ((n : ℝ) - 1) ^ (n - 1) - (((n : ℝ) - 1) ^ 2 - ((n : ℝ) - 1) + 1) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
    nlinarith
  rw [ha1, ha0, hw, diff_id _ _ _ _ _ hx1s hx2s hQpos.ne' hQq,
    abs_mul, abs_of_nonneg (by positivity)]
  have hfac : ((n : ℝ) - 2) ^ 2 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hD := core_ineq (n : ℝ) _ _ _ _ hx10 (by positivity) hP3 hQbig hq0 hq1
  calc ((n : ℝ) - 2) ^ 2 / ((n : ℝ) - 1) ^ 2 * |_| ≤ 1 * (1 / (n : ℝ)) :=
        mul_le_mul hfac hD (abs_nonneg _) (by norm_num)
    _ = 1 / (n : ℝ) := one_mul _

end OMA.Helpers

namespace OMA.Helpers
open OMA.S_oeis_a023811 Filter Topology

theorem f_bound (n : ℕ) (hn : 15 ≤ n) :
    |(a n : ℝ) / (a (n - 1) : ℝ) - (a (n - 1) : ℝ) / (a (n - 2) : ℝ) - Real.exp 1| ≤
      60 / (n : ℝ) := by
  have hx : (15 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hc2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  have h1 := abs_le.1 (r_close n (by omega))
  have h2 := abs_le.1 (r_close (n - 1) (by omega))
  rw [show n - 1 - 1 = n - 2 by omega, hc1] at h2
  have h3 := abs_le.1 (w_est (n - 1) (by omega))
  rw [hc1] at h3
  have h4 := abs_le.1 (w_est (n - 2) (by omega))
  rw [hc2] at h4
  have hx2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have i1 : 1 / (n : ℝ) ≤ 1 / ((n : ℝ) - 2) := one_div_le_one_div_of_le hx2 (by linarith)
  have i2 : 1 / ((n : ℝ) - 1) ≤ 1 / ((n : ℝ) - 2) := one_div_le_one_div_of_le hx2 (by linarith)
  have i3 : 25 / ((n : ℝ) - 1) ≤ 25 / ((n : ℝ) - 2) :=
    div_le_div_of_nonneg_left (by norm_num) hx2 (by linarith)
  have i4 : 52 / ((n : ℝ) - 2) ≤ 60 / (n : ℝ) := by
    rw [div_le_div_iff₀ hx2 (by linarith)]; linarith
  have e52 : 52 / ((n : ℝ) - 2) = 1 / ((n : ℝ) - 2) + 1 / ((n : ℝ) - 2) + 25 / ((n : ℝ) - 2) +
      25 / ((n : ℝ) - 2) := by ring
  rw [abs_le]
  constructor <;> nlinarith
  
end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a023811.main := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (60 : ℝ))
  filter_upwards [Filter.eventually_ge_atTop 15] with n hn
  rw [Real.dist_eq]
  exact OMA.Helpers.f_bound n hn
