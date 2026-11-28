import OMAStatements.S_oeis_a381355
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- For a prime `p`, a series with constant coefficient one has its `m`-th coefficient of the
`p`-th power divisible by `p` when `0 < m < p`. -/
theorem a381355_dvd_coeff_pow (F : PowerSeries ℤ) (hF : constantCoeff F = 1) (p : ℕ)
    (hp : p.Prime) (m : ℕ) (hm0 : 0 < m) (hmp : m < p) : (p : ℤ) ∣ coeff m (F ^ p) := by
  obtain ⟨H, hH⟩ : (X : PowerSeries ℤ) ∣ F - 1 := by
    rw [X_dvd_iff]; simp [hF]
  have hF' : F = X * H + 1 := by rw [← hH]; ring
  rw [hF', add_pow, map_sum]
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  rw [one_pow, mul_one, ← map_natCast (C (R := ℤ)), coeff_mul_C]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [coeff_one, hm0.ne']
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hkp | rfl
  · exact Dvd.dvd.mul_left (by exact_mod_cast hp.dvd_choose_self hk0.ne' hkp) _
  · rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]
    simp

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a381355.main := by
  intro A F hF hAF hcoef n hn
  have hp : (OMA.S_oeis_a381355.nthPrime1 n).Prime := Nat.prime_nth_prime (n - 1)
  have hpn : n ≤ OMA.S_oeis_a381355.nthPrime1 n := by
    have := Nat.add_two_le_nth_prime (n - 1)
    unfold OMA.S_oeis_a381355.nthPrime1; omega
  have hg := hcoef n hn
  set p := OMA.S_oeis_a381355.nthPrime1 n with hpdef
  have hder : X * derivative ℤ (F ^ p) = C (p : ℤ) * (A * F ^ p) := by
    rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, map_natCast]
    have h1 : F ^ p = F ^ (p - 1) * F := by
      rw [← pow_succ]; congr 1; have := hp.one_lt; omega
    calc X * ((p : PowerSeries ℤ) * (F ^ (p - 1) * (derivative ℤ) F))
        = (p : PowerSeries ℤ) * F ^ (p - 1) * (X * (derivative ℤ) F) := by ring
      _ = (p : PowerSeries ℤ) * (A * F ^ p) := by rw [← hAF, h1]; ring
  have hc := congrArg (coeff n) hder
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coeff_succ_X_mul, coeff_derivative, hg, zero_mul, coeff_C_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j (F ^ p)),
    Finset.sum_range_succ, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow, hF,
    one_pow, mul_one] at hc
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsum : (p : ℤ) ∣ ∑ k ∈ Finset.range (m + 1), coeff k A * coeff (m + 1 - k) (F ^ p) := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.sub_zero, hg, mul_zero]; exact dvd_zero _
    · exact Dvd.dvd.mul_left (OMA.Helpers.a381355_dvd_coeff_pow F hF p hp _ (by omega)
        (by omega)) _
  have h2 := (mul_eq_zero.mp hc.symm).resolve_left hp0
  have h3 : coeff (m + 1) A = -∑ k ∈ Finset.range (m + 1), coeff k A * coeff (m + 1 - k) (F ^ p) := by
    linarith
  rw [h3]; exact hsum.neg_right
