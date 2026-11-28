import OMAStatements.S_oeis_a282655
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- The recurrence for `n > 5` and the stated generating function are incompatible at `n = 7`,
for any integer sequence. -/
theorem a282655_key (f : ℕ → ℤ)
    (hrec : ∀ n : ℕ, 5 < n → f n = 4 * f (n - 2) + f (n - 4) - 4 * f (n - 6))
    (hgf : PowerSeries.mk f * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2)) =
      1 + 2 * X + 3 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 - 8 * X ^ 5 + 32 * X ^ 7
        + 128 * X ^ 11) : False := by
  have h7 : f 7 = 4 * f 5 + f 3 - 4 * f 1 := hrec 7 (by norm_num)
  have hL : PowerSeries.mk f * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2)) =
      PowerSeries.mk f * X ^ 0 - C 4 * (PowerSeries.mk f * X ^ 2) - PowerSeries.mk f * X ^ 4
        + C 4 * (PowerSeries.mk f * X ^ 6) := by
    simp only [map_ofNat]
    ring
  have hR : (1 + 2 * X + 3 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 - 8 * X ^ 5 + 32 * X ^ 7
      + 128 * X ^ 11 : PowerSeries ℤ) =
      C 1 * X ^ 0 + C 2 * X ^ 1 + C 3 * X ^ 2 - C 6 * X ^ 3 + C 2 * X ^ 4 - C 8 * X ^ 5
        + C 32 * X ^ 7 + C 128 * X ^ 11 := by
    simp only [map_ofNat, map_one]
    ring
  have hc := congrArg (PowerSeries.coeff 7) hgf
  rw [hL, hR] at hc
  simp only [map_add, map_sub] at hc
  simp only [coeff_C_mul_X_pow] at hc
  simp only [coeff_C_mul, coeff_mul_X_pow', PowerSeries.coeff_mk] at hc
  norm_num at hc
  linarith

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282655.main) := by
  rintro ⟨hrec, hgf⟩
  exact OMA.Helpers.a282655_key _ hrec hgf
