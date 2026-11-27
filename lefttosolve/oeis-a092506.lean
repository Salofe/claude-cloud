import OMAStatements.S_oeis_a092506
import Mathlib

-- Problem: A092506: Prime numbers of the form 2^n + 1.
-- Cloitre's conjecture: the positive solutions of phi(x) + phi(x-1) = floor((3x-2)/2)
-- are exactly the primes of the form 2^n + 1.
-- Proof idea: for even m > 0 one has phi(m) <= m/2 with equality iff m is a power of 2,
-- and phi(x) <= x - 1 with equality iff x is prime. For odd x the equation forces both
-- equalities (x prime and x - 1 a power of 2); for even x >= 4 the left side is too small.

namespace OMA.Helpers

/-- For `m > 0`, `phi(2m) <= m`, with equality only when `m` is a power of two. -/
theorem totient_two_mul_le (m : ℕ) (hm : 0 < m) :
    Nat.totient (2 * m) ≤ m ∧ (Nat.totient (2 * m) = m → ∃ k : ℕ, m = 2 ^ k) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ho
    · have hj0 : 0 < j := by omega
      have hjm : j < m := by omega
      obtain ⟨h1, h2⟩ := ih j hjm hj0
      have hev : Even m := ⟨j, hj⟩
      have hm2 : m = 2 * j := by omega
      rw [Nat.totient_two_mul_of_even hev, hm2]
      refine ⟨by omega, fun h => ?_⟩
      obtain ⟨k, hk⟩ := h2 (by omega)
      exact ⟨k + 1, by rw [hk, pow_succ]; ring⟩
    · rw [Nat.totient_two_mul_of_odd ho]
      refine ⟨Nat.totient_le m, fun h => ?_⟩
      refine ⟨0, ?_⟩
      by_contra hne
      have h1 : 1 < m := by simp at hne; omega
      have := Nat.totient_lt m h1
      omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a092506.main := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx1, hx⟩
    rcases Nat.even_or_odd x with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- x = 2m is even
      have hm0 : 0 < m := by omega
      have hx2 : x = 2 * m := by omega
      by_cases hm1 : m = 1
      · subst hm1
        have : x = 2 := by omega
        subst this
        exact ⟨Nat.prime_two, 0, by norm_num⟩
      · exfalso
        have h1 := (OMA.Helpers.totient_two_mul_le m hm0).1
        rw [← hx2] at h1
        have h2 := Nat.totient_lt (x - 1) (by omega)
        omega
    · -- x = 2m + 1 is odd
      by_cases hm0 : m = 0
      · subst hm0
        have : x = 1 := by omega
        subst this
        simp at hx
      · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hxm : x - 1 = 2 * m := by omega
        obtain ⟨h1, h2⟩ := OMA.Helpers.totient_two_mul_le m hpos
        rw [← hxm] at h1 h2
        have h3 := Nat.totient_lt x (by omega)
        have hphix : Nat.totient x = x - 1 := by omega
        have hphi1 : Nat.totient (x - 1) = m := by omega
        refine ⟨(Nat.totient_eq_iff_prime (by omega)).1 hphix, ?_⟩
        obtain ⟨k, hk⟩ := h2 hphi1
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
  · rintro ⟨hp, n, rfl⟩
    refine ⟨Nat.le_add_left 1 _, ?_⟩
    rcases n with _ | k
    · simp [Nat.totient_two]
    · have e1 : Nat.totient (2 ^ (k + 1) + 1) = 2 ^ (k + 1) := by
        rw [Nat.totient_prime hp]; simp
      have e2 : Nat.totient (2 ^ (k + 1) + 1 - 1) = 2 ^ k := by
        rw [Nat.add_sub_cancel, Nat.totient_prime_pow Nat.prime_two (by omega)]
        simp
      rw [e1, e2, pow_succ]
      omega
