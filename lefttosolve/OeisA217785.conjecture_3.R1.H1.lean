import OMAReductions.R_OeisA217785_conjecture_3_R1

-- Step H1 of reduction OeisA217785.conjecture_3.R1: when p = n + 2 is prime, the shifted
-- polynomial s_n(X + 1) has X^j coefficient (j + 1) * C(p, j + 2), so it is Eisenstein at p.
-- Eisenstein, invariance under the Taylor shift and Gauss's lemma give irreducibility over Q.

namespace OMA.Helpers


open Polynomial

theorem a217785_sum_choose (j : ℕ) : ∀ n : ℕ,
    ∑ k ∈ Finset.range (n + 1), (k + 1) * k.choose j = (j + 1) * (n + 2).choose (j + 2) := by
  intro n
  induction n with
  | zero =>
    rcases j with _ | j
    · simp
    · simp [Nat.choose_eq_zero_of_lt (show 2 < j + 1 + 2 by omega)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := Nat.add_one_mul_choose_eq (n + 1) j
    have h2 : (n + 1 + 2).choose (j + 2) = (n + 2).choose (j + 1) + (n + 2).choose (j + 2) :=
      Nat.choose_succ_succ (n + 2) (j + 1)
    rw [h2]
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e] at h1
    nlinarith [h1]

theorem a217785_coeff_taylor (n j : ℕ) :
    (taylor 1 (OeisA217785.polyS n)).coeff j = (((j + 1) * (n + 2).choose (j + 2) : ℕ) : ℤ) := by
  rw [← a217785_sum_choose j n]
  unfold OeisA217785.polyS
  simp only [map_sum, taylor_mul, taylor_C, taylor_pow, taylor_X, map_one, finsetSum_coeff,
    coeff_C_mul, coeff_X_add_one_pow]
  push_cast
  rfl

theorem a217785_coeff_zero (n : ℕ) : (OeisA217785.polyS n).coeff 0 = 1 := by
  unfold OeisA217785.polyS
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    simp at h

theorem a217785_primitive (n : ℕ) : (OeisA217785.polyS n).IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have := hr 0
  rw [a217785_coeff_zero] at this
  exact isUnit_of_dvd_one this

theorem a217785_taylor_primitive (n : ℕ) : (taylor 1 (OeisA217785.polyS n)).IsPrimitive := by
  intro r hr
  apply a217785_primitive n r
  obtain ⟨q, hq⟩ := hr
  refine ⟨taylor (-1) q, ?_⟩
  have h := congrArg (taylor (-1)) hq
  rw [taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul, taylor_C] at h
  exact h

theorem a217785_H1 (n : ℕ) (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n)) := by
  set p := n + 2 with hpdef
  set g := taylor 1 (OeisA217785.polyS n) with hg
  have hcoeff := a217785_coeff_taylor n
  have hdeg : g.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      rw [hg, hcoeff, Nat.choose_eq_zero_of_lt (by
        have : n < j := by exact_mod_cast hj
        omega)]
      simp
    · rw [hg, hcoeff, Nat.choose_self]
      simp
      omega
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  have heis : g.IsEisensteinAt (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [leadingCoeff, hdeg, hg, hcoeff, Nat.choose_self, Ideal.mem_span_singleton]
      intro hd
      have hd' : p ∣ (n + 1) * 1 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by omega) hd'
      omega
    · intro j hj
      rw [hdeg] at hj
      rw [hg, hcoeff, Ideal.mem_span_singleton]
      have : p ∣ (j + 1) * p.choose (j + 2) :=
        Dvd.dvd.mul_left (hp.dvd_choose_self (by omega) (by omega)) _
      exact_mod_cast this
    · rw [hg, hcoeff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro hd
      have hd' : p ^ 2 ∣ (0 + 1) * p.choose 2 := by exact_mod_cast hd
      have h2 := Nat.add_one_mul_choose_eq (p - 1) 1
      have e : p - 1 + 1 = p := by omega
      rw [e, Nat.choose_one_right] at h2
      have h3 : p ^ 2 ∣ p * (p - 1) := by
        rw [h2]
        simp only [zero_add, one_mul] at hd'
        exact Dvd.dvd.mul_right hd' _
      rw [pow_two] at h3
      have h4 := Nat.dvd_of_mul_dvd_mul_left (by omega) h3
      have := Nat.le_of_dvd (by omega) h4
      omega
  have hgirr : Irreducible g :=
    heis.irreducible hP (a217785_taylor_primitive n) (by omega)
  have hfirr : Irreducible (OeisA217785.polyS n) := by
    have h := (MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ) : ℤ[X] ≃* ℤ[X])
      (x := OeisA217785.polyS n)).mp
    apply h
    exact hgirr
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (a217785_primitive n)).mp hfirr

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 :=
  fun n hn hp => OMA.Helpers.a217785_H1 n hn hp
