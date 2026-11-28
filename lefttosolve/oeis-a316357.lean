import OMAStatements.S_oeis_a316357
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a316357 PowerSeries

theorem shell_period (n : ℕ) : shell (n + 12) = shell n + 40 := by
  rw [shell]

theorem shell_rec6 (n : ℕ) : shell (n + 6) - shell (n + 5) + shell (n + 4) - 2 * shell (n + 3) +
    shell (n + 2) - shell (n + 1) + shell n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 12 with h | h
    · interval_cases n <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have e : ∀ j, shell (m + 12 + j) = shell (m + j) + 40 := fun j => by
        rw [show m + 12 + j = (m + j) + 12 by omega, shell_period]
      have ih' := ih m (by omega)
      rw [e 6, e 5, e 4, e 3, e 2, e 1, shell_period]
      linarith

theorem total_succ (n : ℕ) : total (n + 1) = total n + shell n := rfl

theorem total_rec (n : ℕ) : total (n+7) = 2*total (n+6) - 2*total (n+5) +
      3*total (n+4) - 3*total (n+3) + 2*total (n+2) - 2*total (n+1) + total n := by
  have h := shell_rec6 n
  rw [total_succ (n + 6), total_succ (n + 5), total_succ (n + 4), total_succ (n + 3),
    total_succ (n + 2), total_succ (n + 1), total_succ n]
  linarith

theorem gf : (1 - X)^3 * (1 + X^2) * (1 + X + X^2) * mk total =
      (1 + 3*X + 5*X^2 + 2*X^3 + 5*X^4 + 3*X^5 + X^6 : PowerSeries ℤ) := by
  have key : (1 - X)^3 * (1 + X^2) * (1 + X + X^2) * mk total =
      (mk total * X ^ 0) - C 2 * (mk total * X ^ 1) + C 2 * (mk total * X ^ 2) -
      C 3 * (mk total * X ^ 3) + C 3 * (mk total * X ^ 4) - C 2 * (mk total * X ^ 5) +
      C 2 * (mk total * X ^ 6) - (mk total * X ^ 7) := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 + 3*X + 5*X^2 + 2*X^3 + 5*X^4 + 3*X^5 + X^6 : PowerSeries ℤ) =
      C 1 * X ^ 0 + C 3 * X ^ 1 + C 5 * X ^ 2 + C 2 * X ^ 3 + C 5 * X ^ 4 + C 3 * X ^ 5 +
        C 1 * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega, show 7 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega, show j + 7 - 7 = j by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega,
      show ¬ (j + 7 = 3) by omega, show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega,
      show ¬ (j + 7 = 6) by omega, if_true, if_false]
    have := total_rec j
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a316357.main :=
  ⟨OMA.Helpers.total_rec, OMA.Helpers.gf⟩
