import OMAStatements.S_oeis_a271256
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- The recurrence for `n > 7` and the stated generating function are incompatible at `n = 9`,
for any integer sequence. -/
theorem a271256_key (f : ℕ → ℤ)
    (hrec : ∀ n : ℕ, 7 < n → f n = -f (n - 1) + 2 * f (n - 2) + 2 * f (n - 3) - f (n - 4) - f (n - 5))
    (hgf : PowerSeries.mk f * ((1 - X) ^ 2 * (1 + X) ^ 3) =
      4 + 4 * X + 23 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 4 * X ^ 5 + 3 * X ^ 6 - 8 * X ^ 7
        + 4 * X ^ 9) : False := by
  have h9 : f 9 = -f 8 + 2 * f 7 + 2 * f 6 - f 5 - f 4 := hrec 9 (by norm_num)
  have hL : PowerSeries.mk f * ((1 - X) ^ 2 * (1 + X) ^ 3) =
      PowerSeries.mk f * X ^ 0 + PowerSeries.mk f * X ^ 1 - C 2 * (PowerSeries.mk f * X ^ 2)
        - C 2 * (PowerSeries.mk f * X ^ 3) + PowerSeries.mk f * X ^ 4
        + PowerSeries.mk f * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have hR : (4 + 4 * X + 23 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 4 * X ^ 5 + 3 * X ^ 6
      - 8 * X ^ 7 + 4 * X ^ 9 : PowerSeries ℤ) =
      C 4 * X ^ 0 + C 4 * X ^ 1 + C 23 * X ^ 2 - C 4 * X ^ 3 + C 2 * X ^ 4 + C 4 * X ^ 5
        + C 3 * X ^ 6 - C 8 * X ^ 7 + C 4 * X ^ 9 := by
    simp only [map_ofNat]
    ring
  have hc := congrArg (PowerSeries.coeff 9) hgf
  rw [hL, hR] at hc
  simp only [map_add, map_sub] at hc
  simp only [coeff_C_mul_X_pow] at hc
  simp only [coeff_C_mul, coeff_mul_X_pow', PowerSeries.coeff_mk] at hc
  norm_num at hc
  linarith

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a271256.main) := by
  rintro ⟨-, -, -, hrec, hgf⟩
  exact OMA.Helpers.a271256_key _ hrec hgf
