import OMAStatements.S_oeis_a196079
import Mathlib

namespace OMA.Helpers

theorem le_bound (x : ℕ) (hx : 0 < x) :
    x ≤ x.totient * ∏ p ∈ Finset.Icc 1 (x.totient + 1), p := by
  have h1 : 1 ≤ ∏ p ∈ x.primeFactors, (p - 1) := by
    apply Nat.one_le_iff_ne_zero.mpr
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h2 : x ≤ x * ∏ p ∈ x.primeFactors, (p - 1) := Nat.le_mul_of_pos_right x h1
  rw [← Nat.totient_mul_prod_primeFactors] at h2
  refine h2.trans (Nat.mul_le_mul_left _ ?_)
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd : p ∣ x := Nat.dvd_of_mem_primeFactors hp
    have h3 : (p - 1) ∣ x.totient := by
      rw [← Nat.totient_prime hpp]; exact Nat.totient_dvd_of_dvd hd
    have h4 : 0 < x.totient := Nat.totient_pos.mpr hx
    have h5 := Nat.le_of_dvd h4 h3
    have := hpp.two_le
    rw [Finset.mem_Icc]; omega
  · intro p hp _
    rw [Finset.mem_Icc] at hp
    exact hp.1

end OMA.Helpers

open OMA.S_oeis_a196079 in
theorem OMA.solution : type_of% @OMA.S_oeis_a196079.main := by
  intro hC t ⟨x, hx0, hxt⟩
  obtain ⟨y, hy0, hyx, hyt⟩ := hC x hx0
  have hxf : x ∈ fiber t := ⟨hx0, hxt⟩
  have hyf : y ∈ fiber t := ⟨hy0, hyt.trans hxt⟩
  have hbdd : BddAbove (fiber t) := by
    refine ⟨t * ∏ p ∈ Finset.Icc 1 (t + 1), p, ?_⟩
    rintro z ⟨hz0, hzt⟩
    have := OMA.Helpers.le_bound z hz0
    rw [hzt] at this
    exact this
  have h1 : sInf (fiber t) ≤ x := Nat.sInf_le hxf
  have h2 : sInf (fiber t) ≤ y := Nat.sInf_le hyf
  have h3 : x ≤ sSup (fiber t) := le_csSup hbdd hxf
  have h4 : y ≤ sSup (fiber t) := le_csSup hbdd hyf
  unfold width
  omega
