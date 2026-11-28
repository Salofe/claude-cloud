import OMAStatements.S_oeis_a247031
import Mathlib

/-! Proof of OEIS A247031 conjecture: modulo 3, the cube of a power series is its Frobenius expansion,
so the coefficient of x^(3n) in B^3 is congruent to the n-th coefficient of B. -/

namespace OMA.Helpers

theorem a247031_cube_mod3 (B : PowerSeries ℤ) (n : ℕ) :
    ((PowerSeries.coeff (3 * n) (B ^ 3) : ℤ) : ZMod 3) = ((PowerSeries.coeff n B : ℤ) : ZMod 3) := by
  have h3 : (3 : ℕ) ≠ 0 := by norm_num
  have hfrob : (PowerSeries.expand 3 h3 (PowerSeries.map (Int.castRingHom (ZMod 3)) B)) =
      (PowerSeries.map (Int.castRingHom (ZMod 3)) B) ^ 3 := by
    have := MvPowerSeries.map_frobenius_expand (R := ZMod 3) (σ := Unit) 3 h3
      (f := PowerSeries.map (Int.castRingHom (ZMod 3)) B)
    rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at this
    exact this
  have e1 : ((PowerSeries.coeff (3 * n) (B ^ 3) : ℤ) : ZMod 3) =
      PowerSeries.coeff (3 * n) (PowerSeries.map (Int.castRingHom (ZMod 3)) (B ^ 3)) := by
    rw [PowerSeries.coeff_map]; rfl
  have e2 : ((PowerSeries.coeff n B : ℤ) : ZMod 3) =
      PowerSeries.coeff n (PowerSeries.map (Int.castRingHom (ZMod 3)) B) := by
    rw [PowerSeries.coeff_map]; rfl
  rw [e1, e2, map_pow, ← hfrob, PowerSeries.coeff_expand_mul]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a247031.main := by
  intro A B hAB n
  subst hAB
  have k1 := (ZMod.intCast_eq_intCast_iff (PowerSeries.coeff (3 * n) (B ^ 3)) 2 3).symm
  have k2 := (ZMod.intCast_eq_intCast_iff (PowerSeries.coeff n B) 2 3).symm
  push_cast at k1 k2
  rw [k1, k2, OMA.Helpers.a247031_cube_mod3]
