import OMAReductions.R_Erdos242_erdos_242_R1

/-!
Step H2 of Erdos242.erdos_242.R1: for every n > 2 that is not 1 mod 24, 4/n is a sum of three
distinct unit fractions, by one of five explicit identities.

* n = 2k:      4/n = 1/k + 1/(k+1) + 1/(k(k+1))                 (k ≥ 2)
* n = 3k:      4/n = 1/k + 1/(4k) + 1/(12k)                     (k ≥ 1)
* n = 3k+2:    4/n = 1/(k+1) + 1/n + 1/(n(k+1))                 (k ≥ 1)
* n = 4k+3:    4/n = 1/(k+1) + 1/(m+1) + 1/(m(m+1)), m = n(k+1)
* n = 8k+5:    4/n = 1/(2k+2) + 1/(n(k+1)) + 1/(2n(k+1))

An odd n that is neither 0 nor 2 mod 3 and not 3 mod 4 is 1 mod 12, hence 1 or 13 mod 24;
excluding 1 mod 24 leaves 13 mod 24, so n is 5 mod 8 in the last case.

Each identity is checked after clearing denominators, as a polynomial identity over ℕ.
-/

namespace OMA.Helpers

/-- Clearing denominators: a natural-number identity `4abc = n(bc + ac + ab)` with
`1 ≤ a < b < c` gives the required decomposition of `4/n`. -/
theorem triple_of_identity {n : ℕ} (a b c : ℕ) (hn : 0 < n) (ha : 1 ≤ a) (hab : a < b)
    (hbc : b < c) (h : 4 * (a * b * c) = n * (b * c + a * c + a * b)) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast (show c ≠ 0 by omega)
  have hq : (4 : ℚ) * (a * b * c) = n * (b * c + a * c + a * b) := by exact_mod_cast h
  rw [div_add_div _ _ ha' hb', div_add_div _ _ (mul_ne_zero ha' hb') hc',
    div_eq_div_iff hn' (mul_ne_zero (mul_ne_zero ha' hb') hc')]
  linear_combination hq

/-- `m + 1 < m (m + 1)` as soon as `m ≥ 2`. -/
theorem succ_lt_mul_succ {m : ℕ} (hm : 2 ≤ m) : m + 1 < m * (m + 1) := by
  nlinarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos242_erdos_242_R1.H2 := by
  intro n hn h24
  by_cases h2 : n % 2 = 0
  · -- n = 2k with k ≥ 2
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    exact OMA.Helpers.triple_of_identity k (k + 1) (k * (k + 1)) (by omega) (by omega)
      (by omega) (OMA.Helpers.succ_lt_mul_succ (by omega)) (by ring)
  by_cases h3 : n % 3 = 0
  · -- n = 3k with k ≥ 1
    obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    exact OMA.Helpers.triple_of_identity k (4 * k) (12 * k) (by omega) (by omega)
      (by omega) (by omega) (by ring)
  by_cases h32 : n % 3 = 2
  · -- n = 3k + 2 with k ≥ 1
    obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    have hk : 1 ≤ k := by omega
    exact OMA.Helpers.triple_of_identity (k + 1) (3 * k + 2) ((3 * k + 2) * (k + 1))
      (by omega) (by omega) (by omega) (by nlinarith) (by ring)
  by_cases h43 : n % 4 = 3
  · -- n = 4k + 3, with m = n(k + 1) ≥ k + 3
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    have hm : k + 3 ≤ (4 * k + 3) * (k + 1) := by nlinarith
    exact OMA.Helpers.triple_of_identity (k + 1) ((4 * k + 3) * (k + 1) + 1)
      ((4 * k + 3) * (k + 1) * ((4 * k + 3) * (k + 1) + 1)) (by omega) (by omega)
      (by omega) (OMA.Helpers.succ_lt_mul_succ (by omega)) (by ring)
  · -- remaining case: n = 8k + 5
    obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
    have hy : 2 * k + 2 < (8 * k + 5) * (k + 1) := by nlinarith
    exact OMA.Helpers.triple_of_identity (2 * k + 2) ((8 * k + 5) * (k + 1))
      (2 * ((8 * k + 5) * (k + 1))) (by omega) (by omega) hy (by omega) (by ring)
