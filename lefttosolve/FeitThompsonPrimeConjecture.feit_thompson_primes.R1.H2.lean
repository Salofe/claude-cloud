import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

namespace OMA.Helpers

open Finset

theorem N_mod_four (p q : ℕ) (hq4 : q % 4 = 1) :
    (∑ i ∈ range p, q ^ i) % 4 = p % 4 := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ range p, q ^ i % 4 = 1 := by
    intro i _
    rw [Nat.pow_mod, hq4, Nat.one_pow]
  rw [Finset.sum_congr rfl this]
  simp

theorem N_mod_p (p q : ℕ) (hp : p.Prime) (hqp : q % p ≠ 1) :
    (∑ i ∈ range p, q ^ i) % p = 1 := by
  have := Fact.mk hp
  have hx : ((q : ZMod p)) ≠ 1 := by
    intro h
    apply hqp
    have h' : ((q : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [h', Nat.mod_eq_of_lt hp.one_lt]
  have hgeom := geom_sum_mul (q : ZMod p) p
  rw [ZMod.pow_card] at hgeom
  have hsub : (q : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hs : (∑ i ∈ range p, (q : ZMod p) ^ i) = 1 := by
    have := mul_right_cancel₀ hsub (hgeom.trans (one_mul _).symm)
    exact this
  have hcast : (((∑ i ∈ range p, q ^ i : ℕ)) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    exact hs
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp.one_lt] at hcast
  exact hcast

end OMA.Helpers

open OMA.Helpers Finset in
theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2 := by
  intro p q hp hq hpq hqp hp4 hq4 hdvd
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  rw [← Nat.geomSum_eq hq2, ← Nat.geomSum_eq hp2] at hdvd
  set N := ∑ i ∈ range p, q ^ i with hN
  set M := ∑ i ∈ range q, p ^ i with hM
  have hN4 : N % 4 = 3 := by rw [hN, N_mod_four p q hq4, hp4]
  have hNp : N % p = 1 := N_mod_p p q hp hqp
  -- p ^ q = 1 in ZMod N
  have hpow : ((p : ZMod N)) ^ q = 1 := by
    have hg := geom_sum_mul (p : ZMod N) q
    have hM0 : ((M : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff M N).mpr hdvd
    have : (∑ i ∈ range q, (p : ZMod N) ^ i) = 0 := by
      rw [hM] at hM0; push_cast at hM0; exact hM0
    rw [this, zero_mul] at hg
    exact (sub_eq_zero.mp hg.symm)
  have hmod : ((p : ℤ) ^ q) % (N : ℤ) = (1 : ℤ) % (N : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff']
    push_cast
    exact hpow
  have hJ1 : jacobiSym ((p : ℤ) ^ q) N = 1 := by
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
  have hJN : jacobiSym (N : ℤ) p = 1 := by
    have : (N : ℤ) % (p : ℤ) = (1 : ℤ) % (p : ℤ) := by
      have h1 : (1 : ℤ) % (p : ℤ) = 1 := Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hp.one_lt)
      rw [h1]
      exact_mod_cast hNp
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]
  have hJp : jacobiSym (p : ℤ) N = -1 := by
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN4, hJN]
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.pow_left, hJp, hqodd.neg_one_pow] at hJ1
  norm_num at hJ1
