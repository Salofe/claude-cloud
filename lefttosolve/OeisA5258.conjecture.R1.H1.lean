import OMAReductions.R_OeisA5258_conjecture_R1

/-!
Step H1 of reduction OeisA5258.conjecture.R1: when p = n + 1 is prime, the Apery polynomial
a_n(x) = sum_k C(n,k)^2 C(n+k,k) x^k is irreducible over the rationals.

Write c_k = C(n,k)^2 C(n+k,k) and let P be the integer polynomial sum_k c_k x^k, whose image in
Q[X] is a_n. Then c_0 = 1, p divides C(n+k,k) for 1 <= k <= n (p divides (n+k)! but not k! n!),
and p^2 does not divide c_n = C(2n,n) (the p-adic valuation of a binomial coefficient C(m,k) is
at most 1 when m < p^2). Hence the reversed polynomial x^n P(1/x) is monic and Eisenstein at p,
so it is irreducible over Z. Since P(0) = 1, reversal is multiplicative on the factors of P and
preserves their degrees, so P is irreducible over Z; P is primitive, so by Gauss's lemma its
image a_n is irreducible over Q.
-/

open Polynomial

namespace OMA.Helpers

/-- The Apéry polynomial with integer coefficients. -/
noncomputable def aperyZ (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * X ^ k

theorem aperyZ_map (n : ℕ) : (aperyZ n).map (Int.castRingHom ℚ) = OeisA5258.aperyPoly n := by
  simp [aperyZ, OeisA5258.aperyPoly, Polynomial.map_sum]

theorem aperyZ_coeff (n i : ℕ) : (aperyZ n).coeff i =
    if i ≤ n then (((n.choose i) ^ 2 * ((n + i).choose i) : ℕ) : ℤ) else 0 := by
  simp only [aperyZ, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem aperyZ_coeff_zero (n : ℕ) : (aperyZ n).coeff 0 = 1 := by
  simp [aperyZ_coeff]

theorem aperyZ_coeff_self (n : ℕ) : (aperyZ n).coeff n = (((2 * n).choose n : ℕ) : ℤ) := by
  simp [aperyZ_coeff, two_mul]

theorem aperyZ_natDegree (n : ℕ) : (aperyZ n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp [aperyZ_coeff, Nat.not_le.mpr hN]
  · rw [aperyZ_coeff_self]
    exact_mod_cast (Nat.choose_pos (by omega)).ne'

theorem aperyZ_natTrailingDegree (n : ℕ) : (aperyZ n).natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]
  right
  simp [aperyZ_coeff_zero]

theorem aperyZ_reverse_coeff (n i : ℕ) (hi : i ≤ n) :
    (aperyZ n).reverse.coeff i = (aperyZ n).coeff (n - i) := by
  rw [coeff_reverse, aperyZ_natDegree, revAt_le hi]

theorem aperyZ_reverse_natDegree (n : ℕ) : (aperyZ n).reverse.natDegree = n := by
  rw [reverse_natDegree, aperyZ_natDegree, aperyZ_natTrailingDegree, Nat.sub_zero]

theorem aperyZ_reverse_monic (n : ℕ) : (aperyZ n).reverse.Monic := by
  rw [Monic, reverse_leadingCoeff, trailingCoeff, aperyZ_natTrailingDegree, aperyZ_coeff_zero]

theorem aperyZ_isPrimitive (n : ℕ) : (aperyZ n).IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have h := hr 0
  rw [aperyZ_coeff_zero] at h
  exact isUnit_of_dvd_one h

theorem prime_dvd_coeff (n k : ℕ) (hp : (n + 1).Prime) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (n + 1) ∣ (n.choose k) ^ 2 * ((n + k).choose k) := by
  apply Dvd.dvd.mul_left
  have h := hp.dvd_choose_add (a := k) (b := n) (by omega) (by omega) (by omega)
  rwa [Nat.add_comm k n] at h

theorem prime_sq_not_dvd (n : ℕ) (hp : (n + 1).Prime) :
    ¬ (n + 1) ^ 2 ∣ (2 * n).choose n := by
  intro h
  have hne : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [hp.pow_dvd_iff_le_factorization hne] at h
  have hle : ((2 * n).choose n).factorization (n + 1) ≤ 1 :=
    Nat.factorization_choose_le_one (by nlinarith)
  omega

theorem aperyZ_reverse_eisenstein (n : ℕ) (hp : (n + 1).Prime) :
    (aperyZ n).reverse.IsEisensteinAt (Ideal.span {((n + 1 : ℕ) : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [aperyZ_reverse_monic n, Ideal.mem_span_singleton]
    intro h
    have h' : ((n + 1 : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := by simpa using h
    rw [Int.natCast_dvd_natCast] at h'
    exact hp.one_lt.ne' (Nat.dvd_one.mp h')
  · intro i hi
    rw [aperyZ_reverse_natDegree] at hi
    rw [aperyZ_reverse_coeff n i hi.le, aperyZ_coeff, if_pos (Nat.sub_le n i),
      Ideal.mem_span_singleton, Int.natCast_dvd_natCast]
    exact prime_dvd_coeff n (n - i) hp (by omega) (Nat.sub_le n i)
  · rw [coeff_zero_reverse, leadingCoeff, aperyZ_natDegree, aperyZ_coeff_self,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have h' : (((n + 1) ^ 2 : ℕ) : ℤ) ∣ (((2 * n).choose n : ℕ) : ℤ) := by simpa using h
    rw [Int.natCast_dvd_natCast] at h'
    exact prime_sq_not_dvd n hp h'

theorem isUnit_of_isUnit_reverse {f : ℤ[X]} (h0 : f.coeff 0 ≠ 0) (h : IsUnit f.reverse) :
    IsUnit f := by
  have hd : f.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit h
  have ht : f.natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero]
    exact Or.inr h0
  rw [reverse_natDegree, ht, Nat.sub_zero] at hd
  have hf : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hd
  rw [hf, reverse_C] at h
  rwa [hf]

theorem irreducible_of_irreducible_reverse {f : ℤ[X]} (h0 : f.coeff 0 ≠ 0)
    (h : Irreducible f.reverse) : Irreducible f := by
  refine ⟨fun hu => h.not_isUnit ?_, fun a b hab => ?_⟩
  · obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hu
    rwa [reverse_C]
  · have hab0 : a.coeff 0 * b.coeff 0 ≠ 0 := by
      rw [← mul_coeff_zero, ← hab]
      exact h0
    have ha0 : a.coeff 0 ≠ 0 := left_ne_zero_of_mul hab0
    have hb0 : b.coeff 0 ≠ 0 := right_ne_zero_of_mul hab0
    rw [hab, reverse_mul_of_domain] at h
    rcases h.isUnit_or_isUnit rfl with ha | hb
    · exact Or.inl (isUnit_of_isUnit_reverse ha0 ha)
    · exact Or.inr (isUnit_of_isUnit_reverse hb0 hb)

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := by
  intro n hn hp
  rw [← OMA.Helpers.aperyZ_map,
    ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast (OMA.Helpers.aperyZ_isPrimitive n)]
  apply OMA.Helpers.irreducible_of_irreducible_reverse
  · rw [OMA.Helpers.aperyZ_coeff_zero]
    exact one_ne_zero
  · apply (OMA.Helpers.aperyZ_reverse_eisenstein n hp).irreducible
    · rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hp
    · exact (OMA.Helpers.aperyZ_reverse_monic n).isPrimitive
    · rw [OMA.Helpers.aperyZ_reverse_natDegree]
      exact hn
