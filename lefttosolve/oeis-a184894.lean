import OMAStatements.S_oeis_a184894
import Mathlib

-- Problem: A184894: a(n) equals the coefficient of x^(2n-1) in the n-th iteration of x+x^3 for n>=1.
-- Proof idea: over ZMod 3 the map f(x) = x + x^3 is additive (x^3 is the Frobenius), so
-- the n-th iterate of f reduces to (1 + F)^n applied to X, namely the sum over k of
-- choose n k times X^(3^k). Its coefficient of degree 2n-1 vanishes unless 2n-1 = 3^k,
-- in which case it is choose n k; Lucas gives choose 365 6 = 0 mod 3.
-- Written by Claude (Anthropic), working as the claude-code agent.

namespace OMA.Helpers

open Polynomial

theorem a184894_map (m : ℕ) :
    (OMA.S_oeis_a184894.iteratePoly m).map (Nat.castRingHom (ZMod 3)) =
      ∑ k ∈ Finset.range (m + 1), C ((m.choose k : ℕ) : ZMod 3) * X ^ (3 ^ k) := by
  induction m with
  | zero => simp [OMA.S_oeis_a184894.iteratePoly]
  | succ m ih =>
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [OMA.S_oeis_a184894.iteratePoly, Polynomial.map_add, Polynomial.map_pow, ih,
      ← ZMod.expand_card, map_sum]
    simp only [map_mul, expand_C, map_pow, expand_X]
    have e1 : ∀ k : ℕ, ((X : (ZMod 3)[X]) ^ 3) ^ (3 ^ k) = X ^ (3 ^ (k + 1)) := by
      intro k
      rw [← pow_mul, pow_succ, mul_comm]
    simp only [e1]
    rw [Finset.sum_range_succ' (fun k => C ((((m + 1).choose k : ℕ)) : ZMod 3) * X ^ (3 ^ k))]
    simp only [Nat.choose_succ_succ', Nat.cast_add, map_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun k => C (((m.choose k : ℕ)) : ZMod 3) * X ^ (3 ^ k)),
      Finset.sum_range_succ (fun k => C (((m.choose (k + 1) : ℕ)) : ZMod 3) * X ^ (3 ^ (k + 1)))]
    simp
    abel

theorem a184894_cast (m : ℕ) :
    ((OMA.S_oeis_a184894.term m : ℕ) : ZMod 3) =
      ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℕ) : ZMod 3) * (if 2 * m - 1 = 3 ^ k then 1 else 0) := by
  have h := congrArg (fun p => Polynomial.coeff p (2 * m - 1)) (a184894_map m)
  simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow] at h
  simpa [OMA.S_oeis_a184894.term] using h

theorem a184894_special (j : ℕ) :
    ((OMA.S_oeis_a184894.term ((3 ^ j + 1) / 2) : ℕ) : ZMod 3) =
      ((((3 ^ j + 1) / 2 : ℕ).choose j : ℕ) : ZMod 3) := by
  rw [a184894_cast]
  have hodd : Odd (3 ^ j) := Odd.pow (by decide)
  obtain ⟨r, hr⟩ := hodd
  have h2 : 2 * ((3 ^ j + 1) / 2) - 1 = 3 ^ j := by omega
  rw [Finset.sum_eq_single j]
  · simp [h2]
  · intro k _ hk
    have : 3 ^ j ≠ 3 ^ k := fun h => hk (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
    simp [h2, this]
  · intro hj
    have : (3 ^ j + 1) / 2 < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt this]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a184894.main := by
  refine ⟨?_, OMA.Helpers.a184894_special, ?_⟩
  · intro m hm hnd
    have hne : ((OMA.S_oeis_a184894.term m : ℕ) : ZMod 3) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    rw [OMA.Helpers.a184894_cast] at hne
    obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hk2 : 2 * m - 1 = 3 ^ k := by
      by_contra hc
      simp [hc] at hk
    exact ⟨k, by omega⟩
  · have h := OMA.Helpers.a184894_special 6
    have e : (3 ^ 6 + 1) / 2 = 365 := by norm_num
    rw [e] at h
    have hc : (Nat.choose 365 6 : ZMod 3) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, Nat.choose_eq_descFactorial_div_factorial]
      norm_num [Nat.descFactorial_succ, Nat.factorial]
    rw [← ZMod.natCast_eq_zero_iff, h, hc]
