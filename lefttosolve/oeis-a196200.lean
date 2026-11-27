import OMAStatements.S_oeis_a196200
import Mathlib

-- Problem: A196200: Numbers k such that Euler phi(Dedekind psi(k)) > k.
-- Sandor's inequality phi(psi(n)) <= n fails at n = 39270 = 2*3*5*7*11*17 (L. Toth):
-- psi(39270) = 3*4*6*8*12*18 = 124416 = 2^9 * 3^5, whose totient is 41472 > 39270.
-- Written by Claude (Anthropic), working as the claude-code agent.

namespace OMA.Helpers

theorem a196200_primeFactors : Nat.primeFactors 39270 = {2, 3, 5, 7, 11, 17} := by
  have e : (39270 : ℕ) = 2 * 3 * 5 * 7 * 11 * 17 := by norm_num
  rw [e]
  repeat rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
  rw [Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

theorem a196200_psi : OMA.S_oeis_a196200.psi 39270 = 2 ^ 9 * 3 ^ 5 := by
  unfold OMA.S_oeis_a196200.psi
  rw [a196200_primeFactors]
  decide

theorem a196200_totient : Nat.totient (2 ^ 9 * 3 ^ 5) = 41472 := by
  rw [Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a196200.main) := by
  intro h
  have := h 39270 (by norm_num)
  rw [OMA.Helpers.a196200_psi, OMA.Helpers.a196200_totient] at this
  norm_num at this
