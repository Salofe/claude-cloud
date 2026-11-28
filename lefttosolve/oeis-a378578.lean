import OMAStatements.S_oeis_a378578
import Mathlib

/-!
Proof of the A378578 parity conjecture. Removing factors of 3 does not change parity, so modulo 2
the series A satisfies B = 1 + X B^3. By Lucas, the parities of C(3n, n) satisfy
F = F(X^2) + X F(X^4) = F^2 + X F^4 over ZMod 2, hence F = 1 + X F^3, and this equation has a
unique solution. Finally C(3n, n)/(2n+1) has the parity of C(3n, n), as 2n+1 is odd and divides it.
-/

namespace OMA.Helpers
open PowerSeries

theorem a378578_sq_coeff (φ : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff n (φ ^ 2) = if 2 ∣ n then coeff (n / 2) φ else 0 := by
  rw [sq, coeff_mul_eq_coeff_trunc_mul_trunc φ φ (Nat.lt_succ_self n), ← Polynomial.coe_mul,
    Polynomial.coeff_coe, ← sq, ← Polynomial.map_frobenius_expand (p := 2), ZMod.frobenius_zmod,
    Polynomial.map_id, Polynomial.coeff_expand two_pos]
  split_ifs with h
  · rw [coeff_trunc, if_pos (by omega)]
  · rfl

theorem a378578_two_eq_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  have e : (2 : PowerSeries (ZMod 2)) = 1 + 1 := one_add_one_eq_two.symm
  rw [e]
  ext n
  rw [map_add, coeff_one, map_zero]
  split_ifs <;> decide

theorem a378578_unique {R : Type*} [CommRing R] (g h : PowerSeries R)
    (hg : g = 1 + X * g ^ 3) (hh : h = 1 + X * h ^ 3) : g = h := by
  have key : ∀ n : ℕ, (X : PowerSeries R) ^ n ∣ g - h := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨q, hq⟩ := ih
      have e : g - h = X * ((g - h) * (g ^ 2 + g * h + h ^ 2)) := by
        rw [hg, hh] at *
        nth_rewrite 1 [hg, hh]
        ring
      refine ⟨q * (g ^ 2 + g * h + h ^ 2), ?_⟩
      rw [e, hq]
      ring
  ext m
  have := X_pow_dvd_iff.1 (key (m + 1)) m (Nat.lt_succ_self m)
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem a378578_lucas (n k : ℕ) : ((n.choose k : ℕ) : ZMod 2) =
    (((n % 2).choose (k % 2) : ℕ) : ZMod 2) * (((n / 2).choose (k / 2) : ℕ) : ZMod 2) := by
  rw [← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 Choose.choose_modEq_choose_mod_mul_choose_div_nat

theorem a378578_L1 (m : ℕ) : (((3 * (2 * m)).choose (2 * m) : ℕ) : ZMod 2) =
    (((3 * m).choose m : ℕ) : ZMod 2) := by
  rw [a378578_lucas, show 3 * (2 * m) % 2 = 0 by omega, show 2 * m % 2 = 0 by omega,
    show 3 * (2 * m) / 2 = 3 * m by omega, show 2 * m / 2 = m by omega]
  simp

theorem a378578_L2 (k : ℕ) : (((3 * (4 * k + 1)).choose (4 * k + 1) : ℕ) : ZMod 2) =
    (((3 * k).choose k : ℕ) : ZMod 2) := by
  rw [a378578_lucas, show 3 * (4 * k + 1) % 2 = 1 by omega, show (4 * k + 1) % 2 = 1 by omega,
    show 3 * (4 * k + 1) / 2 = 6 * k + 1 by omega, show (4 * k + 1) / 2 = 2 * k by omega,
    a378578_lucas (6 * k + 1), show (6 * k + 1) % 2 = 1 by omega, show 2 * k % 2 = 0 by omega,
    show (6 * k + 1) / 2 = 3 * k by omega, show 2 * k / 2 = k by omega]
  simp

theorem a378578_L3 (k : ℕ) : (((3 * (4 * k + 3)).choose (4 * k + 3) : ℕ) : ZMod 2) = 0 := by
  rw [a378578_lucas, show 3 * (4 * k + 3) / 2 = 6 * k + 4 by omega,
    show (4 * k + 3) / 2 = 2 * k + 1 by omega,
    a378578_lucas (6 * k + 4), show (6 * k + 4) % 2 = 0 by omega,
    show (2 * k + 1) % 2 = 1 by omega]
  simp

/-- The parities of the central-type binomials `C(3n, n)`. -/
noncomputable def a378578F : PowerSeries (ZMod 2) :=
  PowerSeries.mk (fun n => (((3 * n).choose n : ℕ) : ZMod 2))

theorem a378578F_frob : a378578F = a378578F ^ 2 + X * (a378578F ^ 2) ^ 2 := by
  ext n
  rcases n with _ | j
  · rw [map_add, coeff_zero_X_mul, a378578_sq_coeff, if_pos (dvd_zero 2)]
    simp
  · rw [map_add, coeff_succ_X_mul]
    obtain ⟨k, rfl | rfl | rfl | rfl⟩ :
        ∃ k, j = 4 * k ∨ j = 4 * k + 1 ∨ j = 4 * k + 2 ∨ j = 4 * k + 3 := ⟨j / 4, by omega⟩
    · rw [a378578_sq_coeff a378578F (4 * k + 1), if_neg (by omega),
        a378578_sq_coeff (a378578F ^ 2) (4 * k), if_pos (by omega), show 4 * k / 2 = 2 * k by omega,
        a378578_sq_coeff a378578F (2 * k), if_pos (by omega), show 2 * k / 2 = k by omega,
        a378578F, coeff_mk, coeff_mk, zero_add, a378578_L2]
    · rw [a378578_sq_coeff a378578F (4 * k + 1 + 1), if_pos (by omega),
        a378578_sq_coeff (a378578F ^ 2) (4 * k + 1), if_neg (by omega), add_zero,
        show (4 * k + 1 + 1) / 2 = 2 * k + 1 by omega, a378578F, coeff_mk, coeff_mk,
        show 4 * k + 1 + 1 = 2 * (2 * k + 1) by omega, a378578_L1]
    · rw [a378578_sq_coeff a378578F (4 * k + 2 + 1), if_neg (by omega),
        a378578_sq_coeff (a378578F ^ 2) (4 * k + 2), if_pos (by omega),
        show (4 * k + 2) / 2 = 2 * k + 1 by omega,
        a378578_sq_coeff a378578F (2 * k + 1), if_neg (by omega), zero_add, a378578F, coeff_mk,
        show 4 * k + 2 + 1 = 4 * k + 3 by omega, a378578_L3]
    · rw [a378578_sq_coeff a378578F (4 * k + 3 + 1), if_pos (by omega),
        a378578_sq_coeff (a378578F ^ 2) (4 * k + 3), if_neg (by omega), add_zero,
        show (4 * k + 3 + 1) / 2 = 2 * k + 2 by omega, a378578F, coeff_mk, coeff_mk,
        show 4 * k + 3 + 1 = 2 * (2 * k + 2) by omega, a378578_L1]

theorem a378578F_eq : a378578F = 1 + X * a378578F ^ 3 := by
  have hu : IsUnit a378578F := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, a378578F, coeff_mk]
    simp
  have h0 : a378578F * (1 + a378578F + X * a378578F ^ 3) = 0 := by
    have e : a378578F * (1 + a378578F + X * a378578F ^ 3) =
        a378578F + (a378578F ^ 2 + X * (a378578F ^ 2) ^ 2) := by ring
    rw [e, ← a378578F_frob, ← two_mul, a378578_two_eq_zero, zero_mul]
  have h1 := hu.mul_right_eq_zero.1 h0
  linear_combination h1 - (1 + X * a378578F ^ 3) * a378578_two_eq_zero

theorem a378578_removeThrees_cast (m : ℤ) :
    ((OMA.S_oeis_a378578.removeThrees m : ℤ) : ZMod 2) = (m : ZMod 2) := by
  unfold OMA.S_oeis_a378578.removeThrees
  split_ifs with h
  · simp [h]
  · obtain ⟨q, hq⟩ := padicValInt_dvd (p := 3) m
    set v := padicValInt 3 m
    have h3 : ((3 : ℤ) ^ v) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hq' : m = (3 : ℤ) ^ v * q := by rw [hq]; norm_num
    rw [hq', Int.mul_ediv_cancel_left _ h3]
    push_cast
    rw [show (3 : ZMod 2) = 1 from rfl, one_pow, one_mul]

end OMA.Helpers

open PowerSeries OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a378578.main := by
  intro A hA n
  have hAb : PowerSeries.map (Int.castRingHom (ZMod 2)) A =
      1 + X * (PowerSeries.map (Int.castRingHom (ZMod 2)) A) ^ 3 := by
    ext m
    have e : (1 + X * (PowerSeries.map (Int.castRingHom (ZMod 2)) A) ^ 3 : PowerSeries (ZMod 2)) =
        PowerSeries.map (Int.castRingHom (ZMod 2)) (1 + X * A ^ 3) := by
      simp only [map_add, map_mul, map_pow, map_one, map_X]
    rw [e, coeff_map, coeff_map, hA m, eq_intCast, eq_intCast, a378578_removeThrees_cast]
  have hAf := a378578_unique _ _ hAb a378578F_eq
  have hc : ((coeff n A : ℤ) : ZMod 2) = (((3 * n).choose n : ℕ) : ZMod 2) := by
    have := congrArg (coeff n) hAf
    rw [coeff_map, a378578F, coeff_mk, eq_intCast] at this
    exact this
  have hdvd : (2 * n + 1) ∣ (3 * n).choose n := by
    rcases n with _ | k
    · simp
    · have e := Nat.choose_succ_right_eq (3 * (k + 1)) k
      rw [show 3 * (k + 1) - k = 2 * (k + 1) + 1 by omega] at e
      have hd : (2 * (k + 1) + 1) ∣ (3 * (k + 1)).choose (k + 1) * (k + 1) :=
        ⟨(3 * (k + 1)).choose k, by rw [e, mul_comm]⟩
      have hcop : Nat.Coprime (2 * (k + 1) + 1) (k + 1) := by
        rw [show 2 * (k + 1) + 1 = (k + 1) * 2 + 1 by ring, Nat.coprime_mul_left_add_left]
        exact Nat.coprime_one_left _
      exact hcop.dvd_of_dvd_mul_right hd
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, Nat.mul_div_cancel_left t (by omega)]
  have hz : ((coeff n A : ℤ) : ZMod 2) = (((t : ℕ) : ℤ) : ZMod 2) := by
    rw [hc, ht]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]
    ring
  have := (ZMod.intCast_eq_intCast_iff' _ _ 2).1 hz
  exact_mod_cast this
