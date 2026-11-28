import OMAStatements.S_oeis_a363560
import Mathlib

namespace OMA.Helpers

open PowerSeries Finset

theorem a363560_three : (3 : PowerSeries (ZMod 3)) = 0 := by
  have h : (3 : ZMod 3) = 0 := by decide
  calc (3 : PowerSeries (ZMod 3)) = C (3 : ZMod 3) := (map_ofNat C 3).symm
    _ = 0 := by rw [h, map_zero]

/-- A solution of `y = x (1 + y^7)` over `ZMod 3` lives on the exponents `1 mod 7`. -/
theorem a363560_support (y : PowerSeries (ZMod 3)) (hy : y = X * (1 + y ^ 7)) :
    ∀ n, n % 7 ≠ 1 → coeff n y = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [hy]
    rcases n with _ | k
    · simp
    · rw [coeff_succ_X_mul, map_add, coeff_one, if_neg (by omega), zero_add, coeff_pow]
      apply Finset.sum_eq_zero
      intro l hl
      rw [mem_finsuppAntidiag] at hl
      obtain ⟨hsum, _⟩ := hl
      by_contra hne
      have hall : ∀ i ∈ range 7, l i % 7 = 1 := by
        intro i hi
        by_contra h1
        apply hne
        apply Finset.prod_eq_zero hi
        apply ih (l i) _ h1
        have hle : l i ≤ (range 7).sum l :=
          Finset.single_le_sum (f := l) (fun j _ => Nat.zero_le _) hi
        rw [hsum] at hle
        omega
      have hmod : ((range 7).sum l) % 7 = 0 := by
        rw [Finset.sum_nat_mod, Finset.sum_congr rfl hall]
        simp
      rw [hsum] at hmod
      omega

theorem a363560_key (y : PowerSeries (ZMod 3))
    (hy : (1 + y) ^ 3 = 1 + X * ((1 + y) + (1 + y) ^ 2 + (1 + y) ^ 9)) :
    y = 0 ∨ y = X * (1 + y ^ 7) := by
  have h3 := a363560_three
  have e : y ^ 2 * (y - X * (1 + y ^ 7)) = 0 := by
    linear_combination hy + (-y - y ^ 2 + X * (1 + y + (3 * y + 12 * y ^ 2 + 28 * y ^ 3 +
      42 * y ^ 4 + 42 * y ^ 5 + 28 * y ^ 6 + 12 * y ^ 7 + 3 * y ^ 8))) * h3
  rcases mul_eq_zero.mp e with h | h
  · left; exact (pow_eq_zero_iff two_ne_zero).mp h
  · right; exact sub_eq_zero.mp h

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a363560.main := by
  intro A hA n hn hn7
  obtain ⟨h0, hA3⟩ := hA
  have hm : (map (Int.castRingHom (ZMod 3)) A) ^ 3 = 1 + X * (map (Int.castRingHom (ZMod 3)) A +
      (map (Int.castRingHom (ZMod 3)) A) ^ 2 + (map (Int.castRingHom (ZMod 3)) A) ^ 9) := by
    have := congrArg (map (Int.castRingHom (ZMod 3))) hA3
    simp only [map_pow, map_add, map_mul, map_one, map_X] at this
    exact this
  have hA' : map (Int.castRingHom (ZMod 3)) A = 1 + (map (Int.castRingHom (ZMod 3)) A - 1) := by
    ring
  rw [hA'] at hm
  have hcoef : coeff n (map (Int.castRingHom (ZMod 3)) A - 1) = 0 := by
    rcases a363560_key _ hm with h | h
    · rw [h, map_zero]
    · exact a363560_support _ h n hn7
  have h2 : coeff n (map (Int.castRingHom (ZMod 3)) A) = 0 := by
    rw [map_sub, coeff_one, if_neg (by omega), sub_zero] at hcoef
    exact hcoef
  have : ((coeff n A : ℤ) : ZMod 3) = ((0 : ℤ) : ZMod 3) := by
    rw [Int.cast_zero]
    simpa [coeff_map] using h2
  exact (ZMod.intCast_eq_intCast_iff _ _ 3).mp this
