import OMAReductions.R_Erdos389_erdos_389_R1_H2_R1
import Mathlib

/-!
# Step H1 of the reduction Erdos389.erdos_389.R1.H2.R1

Write n = m + 1. A prime p above the bound satisfies m < p and m + 2k < p ^ 2, so Legendre's
formula gives the valuation of N! as N / p for every N up to m + 2k. The two products are
quotients of factorials, hence their valuations are a = (m + k) / p and
(m + 2k) / p - (m + k) / p. If 2 a p exceeded m + 2k, the number s = a p - k would satisfy
m < 2 s and s ≤ m with p dividing k + s = a p, which the hypothesis forbids. Hence
2 a ≤ (m + 2k) / p, which is the claim.
-/

namespace OMA.Helpers

/-- Legendre's formula below the square of the prime. -/
theorem padicValNat_factorial_of_lt_sq {p N : ℕ} [Fact p.Prime] (h : N < p ^ 2) :
    padicValNat p N.factorial = N / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow (by omega) h)]
  simp

/-- The valuation of a product of consecutive integers as a difference of factorial valuations. -/
theorem padicValNat_prod_range {p : ℕ} [Fact p.Prime] (m k : ℕ) :
    padicValNat p (∏ i ∈ Finset.range k, (m + 1 + i)) + padicValNat p m.factorial =
      padicValNat p (m + k).factorial := by
  rw [← Nat.ascFactorial_eq_prod_range, ← Nat.factorial_mul_ascFactorial,
    padicValNat.mul (Nat.factorial_ne_zero m)
      (by rw [Nat.ascFactorial_eq_prod_range]; exact Finset.prod_ne_zero_iff.mpr fun i _ => by omega),
    add_comm]

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos389_erdos_389_R1_H2_R1.H1 := by
  intro n k hn hk hs p hp hpB
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmp : m < p := lt_of_le_of_lt (by simp) hpB
  have hsq : m + 2 * k < p ^ 2 := by
    have h := Nat.sqrt_lt'.mp (lt_of_le_of_lt (le_max_right _ _) hpB)
    have e : m + 1 + 2 * k - 1 = m + 2 * k := by omega
    rwa [e] at h
  have v1 := OMA.Helpers.padicValNat_prod_range (p := p) m k
  have v2 := OMA.Helpers.padicValNat_prod_range (p := p) (m + k) k
  have e2 : m + 1 + k = m + k + 1 := by omega
  rw [e2]
  rw [OMA.Helpers.padicValNat_factorial_of_lt_sq (by omega),
    OMA.Helpers.padicValNat_factorial_of_lt_sq (by omega), Nat.div_eq_of_lt hmp] at v1
  rw [OMA.Helpers.padicValNat_factorial_of_lt_sq (by omega),
    OMA.Helpers.padicValNat_factorial_of_lt_sq (by omega)] at v2
  have e3 : m + k + k = m + 2 * k := by omega
  rw [e3] at v2
  set a := (m + k) / p with ha
  have hap : a * p ≤ m + k := Nat.div_mul_le_self (m + k) p
  have key : 2 * a * p ≤ m + 2 * k := by
    by_contra! hcon
    set c := a * p with hc
    have h2c : 2 * a * p = 2 * c := by rw [hc]; ring
    rw [h2c] at hcon
    have hkc : k + (c - k) = c := by omega
    have hdvd : p ∣ k + (c - k) := by rw [hkc, hc]; exact Dvd.intro_left a rfl
    have hle := hs (c - k) (by omega) (by omega) p hp hdvd
    omega
  have hdiv : 2 * a ≤ (m + 2 * k) / p := (Nat.le_div_iff_mul_le hp.pos).mpr key
  omega
