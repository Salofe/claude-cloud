import OMAStatements.S_oeis_a267068
import Mathlib

namespace OMA.Helpers

open Polynomial

/-- The polynomials `P` with `P 0 = 0`, `P 1 = 1`, `P (d+2) = -X * P d + P (d+1)`. -/
noncomputable def a267068P : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 1
  | d + 2 => -X * a267068P d + a267068P (d + 1)

/-- The linear functional sending `X^m` to `1/(m+1)` (integration over `[0,1]`). -/
noncomputable def a267068L : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun m => ((1 : ℚ) / ((m : ℚ) + 1)) • LinearMap.id)

theorem a267068L_monomial (n : ℕ) (r : ℚ) : a267068L (monomial n r) = r / ((n : ℚ) + 1) := by
  unfold a267068L
  rw [Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  · simp [div_eq_inv_mul]
  · simp

theorem a267068L_deriv (p : ℚ[X]) : a267068L (derivative p) = p.eval 1 - p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval_add]; ring
  | monomial n r =>
    rw [derivative_monomial, a267068L_monomial]
    rcases n with _ | k
    · simp
    · simp only [eval_monomial, one_pow, mul_one, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, not_false_eq_true, zero_pow, mul_zero, sub_zero, Nat.add_sub_cancel]
      push_cast
      field_simp

theorem a267068c_eq : ∀ d m : ℕ,
    OMA.S_oeis_a267068.c m d = a267068L ((-X) ^ m * a267068P d)
  | 0, m => by
    rw [OMA.S_oeis_a267068.c]
    simp [a267068P]
  | 1, m => by
    rw [OMA.S_oeis_a267068.c]
    have h : ((-X : ℚ[X]) ^ m * a267068P 1) = monomial m ((-1 : ℚ) ^ m) := by
      rw [a267068P, mul_one, neg_pow, ← C_mul_X_pow_eq_monomial]
      simp
    rw [h, a267068L_monomial, pow_add]
    norm_num
  | d + 2, m => by
    rw [OMA.S_oeis_a267068.c, a267068c_eq d (m + 1), a267068c_eq (d + 1) m, ← map_add]
    congr 1
    rw [a267068P]
    ring

theorem a267068W_deriv : ∀ n : ℕ,
    derivative (a267068P (n + 1) - 2 * X * a267068P n) = -(((n : ℚ[X]) + 1) * a267068P n)
  | 0 => by simp [a267068P]
  | 1 => by
    simp [a267068P]
    norm_num
  | n + 2 => by
    have h1 := a267068W_deriv n
    have h2 := a267068W_deriv (n + 1)
    have e : a267068P (n + 2 + 1) - 2 * X * a267068P (n + 2) =
        (a267068P (n + 1 + 1) - 2 * X * a267068P (n + 1)) -
          X * (a267068P (n + 1) - 2 * X * a267068P n) := by
      rw [show n + 2 + 1 = (n + 1) + 2 from rfl, a267068P, show n + 1 + 1 = n + 2 from rfl,
        a267068P]
      ring
    rw [e, derivative_sub, derivative_mul, derivative_X, h1, h2,
      show n + 2 = (n + 1) + 1 from rfl, show (n + 1) + 1 = n + 2 from rfl, a267068P]
    push_cast
    ring

theorem a267068P_eval0 : ∀ n : ℕ, (a267068P (n + 1)).eval 0 = 1
  | 0 => by simp [a267068P]
  | 1 => by simp [a267068P]
  | n + 2 => by
    rw [show n + 2 + 1 = (n + 1) + 2 from rfl, a267068P, eval_add, eval_mul, eval_neg, eval_X,
      a267068P_eval0 (n + 1)]
    ring

/-- `e n = P n` evaluated at `1`. -/
noncomputable def a267068e (n : ℕ) : ℚ := (a267068P n).eval 1

theorem a267068e_rec (n : ℕ) : a267068e (n + 2) = -a267068e n + a267068e (n + 1) := by
  unfold a267068e
  rw [a267068P, eval_add, eval_mul, eval_neg, eval_X]
  ring

theorem a267068e_add3 (n : ℕ) : a267068e (n + 3) = -a267068e n := by
  rw [show n + 3 = (n + 1) + 2 from rfl, a267068e_rec, a267068e_rec]
  ring

theorem a267068e_add6 (n : ℕ) : a267068e (n + 6) = a267068e n := by
  rw [show n + 6 = (n + 3) + 3 from rfl, a267068e_add3, a267068e_add3, neg_neg]

theorem a267068e_mul6 (q r : ℕ) : a267068e (6 * q + r) = a267068e r := by
  induction q with
  | zero => simp
  | succ q ih => rw [show 6 * (q + 1) + r = (6 * q + r) + 6 by ring, a267068e_add6, ih]

theorem a267068e_vals : a267068e 0 = 0 ∧ a267068e 1 = 1 ∧ a267068e 2 = 1 ∧ a267068e 3 = 0 ∧
    a267068e 4 = -1 ∧ a267068e 5 = -1 ∧ a267068e 6 = 0 := by
  have h0 : a267068e 0 = 0 := by simp [a267068e, a267068P]
  have h1 : a267068e 1 = 1 := by simp [a267068e, a267068P]
  have h2 : a267068e 2 = 1 := by rw [a267068e_rec, h0, h1]; ring
  have h3 : a267068e 3 = 0 := by rw [a267068e_add3, h0, neg_zero]
  have h4 : a267068e 4 = -1 := by rw [a267068e_add3, h1]
  have h5 : a267068e 5 = -1 := by rw [a267068e_add3, h2]
  have h6 : a267068e 6 = 0 := by rw [a267068e_add3, h3, neg_zero]
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- `(n+1) * B(0,n) = 1 - e(n+1) + 2 e(n)`. -/
theorem a267068B0 (n : ℕ) :
    ((n : ℚ) + 1) * OMA.S_oeis_a267068.B 0 n = 1 - a267068e (n + 1) + 2 * a267068e n := by
  unfold OMA.S_oeis_a267068.B
  rw [Nat.sub_zero, a267068c_eq, pow_zero, one_mul]
  have hd := congrArg a267068L (a267068W_deriv n)
  rw [a267068L_deriv, map_neg] at hd
  have hc : ((n : ℚ[X]) + 1) * a267068P n = ((n : ℚ) + 1) • a267068P n := by
    rw [← C_mul']
    simp
  rw [hc, map_smul, smul_eq_mul] at hd
  have h0 := a267068P_eval0 n
  simp only [eval_sub, eval_mul, eval_X, mul_zero, zero_mul, sub_zero, h0] at hd
  unfold a267068e
  simp only [eval_ofNat] at hd
  linarith

theorem a267068B_mod (q r : ℕ) :
    ((6 * q + r : ℕ) + 1 : ℚ) * OMA.S_oeis_a267068.B 0 (6 * q + r) =
      1 - a267068e (r + 1) + 2 * a267068e r := by
  rw [a267068B0, show 6 * q + r + 1 = 6 * q + (r + 1) by ring, a267068e_mul6, a267068e_mul6]

theorem a267068den_inv (k : ℕ) (hk : 0 < k) (x : ℚ) (hx : x = ((k : ℕ) : ℚ)⁻¹) : x.den = k := by
  rw [hx, Rat.inv_natCast_den_of_pos hk]

theorem a267068a_mod (q : ℕ) :
    OMA.S_oeis_a267068.a (6 * q) = 6 * q + 1 ∧ OMA.S_oeis_a267068.a (6 * q + 1) = 2 ∧
      OMA.S_oeis_a267068.a (6 * q + 2) = 3 ∧ OMA.S_oeis_a267068.a (6 * q + 3) = 2 ∧
      OMA.S_oeis_a267068.a (6 * q + 4) = 6 * q + 5 ∧ OMA.S_oeis_a267068.a (6 * q + 5) = 1 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := a267068e_vals
  have hB : ∀ r : ℕ, ((6 * q + r : ℕ) + 1 : ℚ) * OMA.S_oeis_a267068.B 0 (6 * q + r) =
      1 - a267068e (r + 1) + 2 * a267068e r := fun r => a267068B_mod q r
  have b0 := hB 0
  have b1 := hB 1
  have b2 := hB 2
  have b3 := hB 3
  have b4 := hB 4
  have b5 := hB 5
  simp only [Nat.add_zero, zero_add, Nat.reduceAdd, e0, e1, e2, e3, e4, e5, e6] at b0 b1 b2 b3 b4 b5
  push_cast at b0 b1 b2 b3 b4 b5
  have pos : ∀ r : ℕ, (0 : ℚ) < 6 * q + r + 1 := fun r => by positivity
  unfold OMA.S_oeis_a267068.a OMA.S_oeis_a267068.A189733
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hz : OMA.S_oeis_a267068.B 0 (6 * q) = 0 := by
      have := pos 0
      have h : (6 * (q : ℚ) + 1) * OMA.S_oeis_a267068.B 0 (6 * q) = 0 := by linarith
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact h
    rw [hz]
    push_cast
    simp
  · have hx : OMA.S_oeis_a267068.B 0 (6 * q + 1) = ((3 * q + 1 : ℕ) : ℚ)⁻¹ := by
      have := pos 1
      push_cast
      field_simp
      linarith
    rw [a267068den_inv (3 * q + 1) (by omega) _ hx]
    push_cast
    field_simp
    ring
  · have hx : OMA.S_oeis_a267068.B 0 (6 * q + 2) = ((2 * q + 1 : ℕ) : ℚ)⁻¹ := by
      have := pos 2
      push_cast
      field_simp
      linarith
    rw [a267068den_inv (2 * q + 1) (by omega) _ hx]
    push_cast
    field_simp
    ring
  · have hx : OMA.S_oeis_a267068.B 0 (6 * q + 3) = ((3 * q + 2 : ℕ) : ℚ)⁻¹ := by
      have := pos 3
      push_cast
      field_simp
      linarith
    rw [a267068den_inv (3 * q + 2) (by omega) _ hx]
    push_cast
    field_simp
    ring
  · have hz : OMA.S_oeis_a267068.B 0 (6 * q + 4) = 0 := by
      have := pos 4
      have h : (6 * (q : ℚ) + 4 + 1) * OMA.S_oeis_a267068.B 0 (6 * q + 4) = 0 := by linarith
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact h
    rw [hz]
    push_cast
    simp
    ring
  · have hx : OMA.S_oeis_a267068.B 0 (6 * q + 5) = -((6 * q + 6 : ℕ) : ℚ)⁻¹ := by
      have := pos 5
      push_cast
      field_simp
      linarith
    rw [hx, Rat.den_neg_eq_den, Rat.inv_natCast_den_of_pos (by omega)]
    push_cast
    field_simp
    ring

theorem a267068_rec (n : ℕ) (hn : 11 < n) :
    OMA.S_oeis_a267068.a n = 2 * OMA.S_oeis_a267068.a (n - 6) - OMA.S_oeis_a267068.a (n - 12) := by
  obtain ⟨p, r, hr, rfl⟩ : ∃ p r, r < 6 ∧ n = 6 * (p + 2) + r :=
    ⟨n / 6 - 2, n % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [show 6 * (p + 2) + r - 6 = 6 * (p + 1) + r by omega,
    show 6 * (p + 2) + r - 12 = 6 * p + r by omega]
  have A := a267068a_mod p
  have B := a267068a_mod (p + 1)
  have C := a267068a_mod (p + 2)
  interval_cases r
  · simp only [Nat.add_zero] at *
    rw [A.1, B.1, C.1]
    push_cast
    ring
  · rw [A.2.1, B.2.1, C.2.1]; ring
  · rw [A.2.2.1, B.2.2.1, C.2.2.1]; ring
  · rw [A.2.2.2.1, B.2.2.2.1, C.2.2.2.1]; ring
  · rw [A.2.2.2.2.1, B.2.2.2.2.1, C.2.2.2.2.1]
    push_cast
    ring
  · rw [A.2.2.2.2.2, B.2.2.2.2.2, C.2.2.2.2.2]; ring

theorem a267068_small : OMA.S_oeis_a267068.a 0 = 1 ∧ OMA.S_oeis_a267068.a 1 = 2 ∧
    OMA.S_oeis_a267068.a 2 = 3 ∧ OMA.S_oeis_a267068.a 3 = 2 ∧ OMA.S_oeis_a267068.a 4 = 5 ∧
    OMA.S_oeis_a267068.a 5 = 1 ∧ OMA.S_oeis_a267068.a 6 = 7 ∧ OMA.S_oeis_a267068.a 7 = 2 ∧
    OMA.S_oeis_a267068.a 8 = 3 ∧ OMA.S_oeis_a267068.a 9 = 2 ∧ OMA.S_oeis_a267068.a 10 = 11 ∧
    OMA.S_oeis_a267068.a 11 = 1 := by
  have A := a267068a_mod 0
  have B := a267068a_mod 1
  simp only [Nat.reduceAdd, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, zero_add] at A B
  norm_num at A B
  exact ⟨A.1, A.2.1, A.2.2.1, A.2.2.2.1, A.2.2.2.2.1, A.2.2.2.2.2, B.1,
    B.2.1, B.2.2.1, B.2.2.2.1, B.2.2.2.2.1, B.2.2.2.2.2⟩

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267068.main := by
  refine ⟨OMA.Helpers.a267068_rec, ?_⟩
  have hden : ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 - X + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2 :
      PowerSeries ℚ) = 1 - X ^ 6 - X ^ 6 + X ^ 12 := by ring
  rw [hden]
  have hmul : PowerSeries.mk OMA.S_oeis_a267068.a * (1 - X ^ 6 - X ^ 6 + X ^ 12) =
      PowerSeries.mk OMA.S_oeis_a267068.a - PowerSeries.mk OMA.S_oeis_a267068.a * X ^ 6 -
        PowerSeries.mk OMA.S_oeis_a267068.a * X ^ 6 +
          PowerSeries.mk OMA.S_oeis_a267068.a * X ^ 12 := by ring
  have hnum : ∀ k : ℕ, coeff k (1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + X ^ 5 +
      5 * X ^ 6 - 2 * X ^ 7 - 3 * X ^ 8 - 2 * X ^ 9 + X ^ 10 - X ^ 11 : PowerSeries ℚ) =
      ((((((((((((if k = 0 then 1 else 0) + if k = 1 then 2 else 0) + if k = 2 then 3 else 0) +
        if k = 3 then 2 else 0) + if k = 4 then 5 else 0) + if k = 5 then 1 else 0) +
        if k = 6 then 5 else 0) - if k = 7 then 2 else 0) - if k = 8 then 3 else 0) -
        if k = 9 then 2 else 0) + if k = 10 then 1 else 0) - if k = 11 then 1 else 0) := by
    intro k
    simp [coeff_X_pow, coeff_one, coeff_X, show (2 : PowerSeries ℚ) = C (2 : ℚ) from rfl,
      show (3 : PowerSeries ℚ) = C (3 : ℚ) from rfl, show (5 : PowerSeries ℚ) = C (5 : ℚ) from rfl]
  rw [hmul]
  ext n
  rw [hnum n]
  simp only [map_add, map_sub, coeff_mk, coeff_mul_X_pow']
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := OMA.Helpers.a267068_small
  by_cases hn : 11 < n
  · rw [if_pos (by omega), if_pos (by omega), OMA.Helpers.a267068_rec n hn]
    simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
      show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
      show n ≠ 11 by omega, if_false]
    ring
  · interval_cases n <;> simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11] <;> norm_num
