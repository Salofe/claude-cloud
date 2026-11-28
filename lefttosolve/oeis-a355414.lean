import OMAStatements.S_oeis_a355414
import Mathlib

namespace OMA.Helpers
open PowerSeries

noncomputable def Am : PowerSeries ℚ := PowerSeries.mk 1
noncomputable def Bm : PowerSeries ℚ := PowerSeries.mk fun n => (2 : ℚ) ^ n
noncomputable def Tm : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ((2 : ℚ) ^ n - 1) / n

theorem hA : (1 - X : PowerSeries ℚ) * Am = 1 := by
  rw [mul_comm]; exact mk_one_mul_one_sub_eq_one ℚ

theorem two_eq_C : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm

theorem hB : (1 - 2 * X : PowerSeries ℚ) * Bm = 1 := by
  rw [two_eq_C]
  ext n
  rcases n with _ | n
  · simp [Bm]
  · simp [Bm, sub_mul, mul_assoc, coeff_succ_X_mul, coeff_C_mul, pow_succ]; ring

theorem hdB : d⁄dX ℚ Bm = 2 * Bm ^ 2 := by
  have h := congrArg (d⁄dX ℚ) hB
  rw [two_eq_C] at h ⊢
  simp only [Derivation.leibniz, map_sub, derivative_one, smul_eq_mul, derivative_C, derivative_X] at h
  have hB' := hB
  rw [two_eq_C] at hB'
  linear_combination (-(d⁄dX ℚ) Bm) * hB' + Bm * h

theorem hT : d⁄dX ℚ Tm = 2 * Bm - Am := by
  ext n
  rw [coeff_derivative, two_eq_C]
  simp only [Tm, Bm, Am, coeff_mk, map_sub, coeff_C_mul, Pi.one_apply]
  rw [if_neg (Nat.succ_ne_zero n)]
  push_cast
  field_simp
  ring

theorem hG : d⁄dX ℚ (log ℚ) * (1 + X) = 1 := by
  ext n
  rw [deriv_log]
  rcases n with _ | n
  · simp
  · simp [mul_add, coeff_succ_mul_X, pow_succ]

noncomputable def fS : PowerSeries ℚ := (1 - X) * Bm

theorem cc_f : constantCoeff fS = 1 := by simp [fS, Bm]

theorem hg : HasSubst (fS - 1) :=
  HasSubst.of_constantCoeff_zero' (by rw [map_sub, cc_f, map_one, sub_self])

theorem logOf_eq_T : logOf fS = Tm := by
  apply derivative.ext
  · rw [logOf_eq, derivative_subst hg, hT]
    have h1 : (d⁄dX ℚ (log ℚ)).subst (fS - 1) * ((1 - X) * Bm) = 1 := by
      have h := congrArg (substAlgHom hg) hG
      rw [map_mul, map_add, map_one, coe_substAlgHom, subst_X hg] at h
      rw [add_sub_cancel] at h
      exact h
    have hdf : d⁄dX ℚ (fS - 1) = -Bm + (1 - X) * d⁄dX ℚ Bm := by
      simp only [fS, map_sub, derivative_one, sub_zero, Derivation.leibniz, smul_eq_mul,
        derivative_X]
      ring
    rw [hdf, hdB]
    linear_combination (2 * Bm - Am) * h1 + (d⁄dX ℚ (log ℚ)).subst (fS - 1) * Bm * hA
  · rw [constantCoeff_logOf cc_f]; simp [Tm]

theorem egf_eq : OMA.S_oeis_a355414.egf = Tm * Am ^ 5 := by
  have e1 : (1 - 2 * X : PowerSeries ℚ)⁻¹ = Bm := by
    symm
    rw [eq_inv_iff_mul_eq_one (by simp), mul_comm]
    exact hB
  have e2 : ((1 - X : PowerSeries ℚ) ^ 5)⁻¹ = Am ^ 5 := by
    symm
    rw [eq_inv_iff_mul_eq_one (by simp), ← mul_pow, mul_comm, hA, one_pow]
  unfold OMA.S_oeis_a355414.egf
  rw [e1, e2, ← logOf_eq_T]
  rfl

theorem coeff_egf (n : ℕ) : coeff n OMA.S_oeis_a355414.egf =
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
      (if x.1 = 0 then 0 else ((2 : ℚ) ^ x.1 - 1) / x.1) * (Nat.choose (4 + x.2) 4 : ℚ) := by
  rw [egf_eq, Am, mk_one_pow_eq_mk_choose_add, coeff_mul]
  simp only [Tm, coeff_mk]

def zN (p : ℕ) : ℕ := ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p,
  if x.1 = 0 then 0 else p.factorial / x.1 * (2 ^ x.1 - 1) * Nat.choose (4 + x.2) 4

theorem a_eq (p : ℕ) : OMA.S_oeis_a355414.a p = (zN p : ℚ) := by
  unfold OMA.S_oeis_a355414.a zN
  rw [coeff_egf, Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h0 : x.1 = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0]
    have hle : x.1 ≤ p := by omega
    have hd : x.1 ∣ p.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero h0) hle
    have hx0 : (x.1 : ℚ) ≠ 0 := by exact_mod_cast h0
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_div hd hx0, Nat.cast_sub Nat.one_le_two_pow,
      Nat.cast_pow]
    push_cast
    field_simp

theorem zN_mod (p : ℕ) [hp : Fact p.Prime] : ((zN p : ℕ) : ZMod p) = -1 := by
  unfold zN
  rw [Nat.cast_sum, Finset.sum_eq_single_of_mem (p, 0) (by simp)]
  · rw [if_neg hp.out.ne_zero]
    have hpf : p.factorial / p = (p - 1).factorial :=
      Nat.div_eq_of_eq_mul_right hp.out.pos (Nat.mul_factorial_pred hp.out.ne_zero).symm
    rw [hpf, Nat.cast_mul, Nat.cast_mul, ZMod.wilsons_lemma, Nat.cast_sub Nat.one_le_two_pow,
      Nat.cast_pow, ZMod.pow_card]
    simp only [add_zero, Nat.choose_self, Nat.cast_one, mul_one]
    ring
  · intro x hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    split_ifs with h0
    · simp
    · have hlt : x.1 < p := by
        rcases Nat.lt_or_ge x.1 p with h | h
        · exact h
        · exfalso
          apply hne
          ext
          · simp only; omega
          · simp only; omega
      have hd : x.1 ∣ (p - 1).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero h0) (by omega)
      have e : p.factorial / x.1 = p * ((p - 1).factorial / x.1) := by
        rw [← Nat.mul_factorial_pred hp.out.ne_zero, Nat.mul_div_assoc _ hd]
      rw [e]
      simp

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a355414.main := by
  intro p hp
  have := Fact.mk hp
  refine ⟨(zN p : ℤ), ?_, ?_⟩
  · rw [a_eq]; push_cast; rfl
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [zN_mod]
    ring
