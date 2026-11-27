import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1

/-!
Step H2 of reduction Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H1.R1.
Since 2 is not a cube mod 13, X^(3^j) - 2 is irreducible over ZMod 13 (Kummer, prime power
degree), so the quotient is a finite field with Q = 13^(3^j) elements, and Q - 1 = 4 u with u odd.
The root x is not a square: if x = w^2 then w^(12 * 3^j) = 2^6 = -1, while
w^(4 u * 3^(j+1)) = 1 by Fermat, and also equals (w^(12 * 3^j))^u = -1, impossible in
characteristic 13. Then the quadratic character gives: x times a non-square is a square.
-/

open Polynomial

namespace OMA.Helpers

theorem pow_mod_eight (j : ℕ) : 13 ^ (3 ^ j) % 8 = 5 := by
  obtain ⟨t, ht⟩ : Odd (3 ^ j) := Odd.pow (by decide)
  rw [ht, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_cube13 : ∀ b : ZMod 13, b ^ 3 ≠ 2 := by decide

theorem two_pow_six13 : (2 : ZMod 13) ^ 6 = -1 := by decide

theorem two_ne_zero13 : (2 : ZMod 13) ≠ 0 := by decide

theorem two_ne_zero_F {F : Type*} [Field F] [Algebra (ZMod 13) F] : (2 : F) ≠ 0 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  intro h
  apply two_ne_zero13
  apply (algebraMap (ZMod 13) F).injective
  rw [map_ofNat, map_zero]
  exact h

theorem two_pow_six_F {F : Type*} [Field F] [Algebra (ZMod 13) F] : (2 : F) ^ 6 = -1 := by
  have := congrArg (algebraMap (ZMod 13) F) two_pow_six13
  rwa [map_pow, map_neg, map_one, map_ofNat] at this

theorem neg_one_ne_one_F {F : Type*} [Field F] [Algebra (ZMod 13) F] : (-1 : F) ≠ 1 := by
  intro h
  apply two_ne_zero_F (F := F)
  linear_combination -h

theorem root_not_square {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 13) F] (j : ℕ)
    (hcard : Fintype.card F = 13 ^ 3 ^ j) (r : F) (hroot : r ^ 3 ^ j = 2) : ¬ IsSquare r := by
  rintro ⟨w, hw⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [hw, mul_zero, zero_pow (by positivity)] at hroot
    exact two_ne_zero_F hroot.symm
  have hM : w ^ (12 * 3 ^ j) = -1 := by
    rw [← two_pow_six_F, ← hroot, hw, ← sq, ← pow_mul, ← pow_mul]
    ring_nf
  obtain ⟨u, hu⟩ : ∃ u, 13 ^ 3 ^ j - 1 = 4 * u ∧ Odd u := by
    have h8 := pow_mod_eight j
    have hpos : 1 ≤ 13 ^ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    refine ⟨(13 ^ 3 ^ j - 1) / 4, by omega, ?_⟩
    rw [Nat.odd_iff]
    omega
  have hF := FiniteField.pow_card_sub_one_eq_one w hw0
  rw [hcard, hu.1] at hF
  have e1 : w ^ (4 * u * 3 ^ (j + 1)) = 1 := by
    rw [pow_mul, hF, one_pow]
  have e2 : w ^ (4 * u * 3 ^ (j + 1)) = -1 := by
    have : 4 * u * 3 ^ (j + 1) = (12 * 3 ^ j) * u := by ring
    rw [this, pow_mul, hM, hu.2.neg_one_pow]
  exact neg_one_ne_one_F (e2.symm.trans e1)

theorem mul_nonsquares {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 13) F]
    (r y : F) (hr : ¬ IsSquare r) (hy : ¬ IsSquare y) : IsSquare (r * y) := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr ⟨0, by simp⟩
  have hy0 : y ≠ 0 := by rintro rfl; exact hy ⟨0, by simp⟩
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr hr
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hy
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hr0 hy0), map_mul, h1, h2]
  norm_num

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1.H2 := by
  classical
  intro j y hy
  have hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hirr : Irreducible (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) :=
    X_pow_sub_C_irreducible_of_prime_pow Nat.prime_three (by norm_num) j OMA.Helpers.not_cube13
  have hfi : Fact (Irreducible (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) := ⟨hirr⟩
  have hne : (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) ≠ 0 := hirr.ne_zero
  let b := AdjoinRoot.powerBasis hne
  have hmf : Module.Finite (ZMod 13) (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) := b.finite
  have hfin : Finite (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) :=
    Module.finite_of_finite (ZMod 13)
  let _ft : Fintype (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) = 13 ^ 3 ^ j := by
    rw [Module.card_fintype b.basis, ZMod.card, Fintype.card_fin]
    simp [b]
  have hroot : (AdjoinRoot.root (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) ^ 3 ^ j = 2 := by
    have h := AdjoinRoot.eval₂_root (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
    rw [sub_eq_zero] at h
    rw [h]
    exact map_ofNat _ 2
  exact OMA.Helpers.mul_nonsquares _ y
    (OMA.Helpers.root_not_square j hcard _ hroot) hy
