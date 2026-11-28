import OMAStatements.S_oeis_a088120
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a088120

/-- `chk n s k = true` iff no odd number `2 * (s + i) + 3` with `i < k` divides `n`. -/
def chk (n s : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => (n % (2 * (s + k) + 3) != 0) && ih)

theorem chk_sound (n s : ℕ) : ∀ k, chk n s k = true → ∀ i < k, ¬ (2 * (s + i) + 3) ∣ n := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    have h' : (n % (2 * (s + k) + 3) != 0) = true ∧ chk n s k = true := by
      simpa [chk] using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih h'.2 i hlt
    · subst heq
      intro hd
      have := h'.1
      simp [Nat.mod_eq_zero_of_dvd hd] at this

theorem k0 : chk 316234143227 0 70293 = true := by decide +kernel
theorem k1 : chk 316234143227 70293 70293 = true := by decide +kernel
theorem k2 : chk 316234143227 140586 70293 = true := by decide +kernel
theorem k3 : chk 316234143227 210879 70293 = true := by decide +kernel

theorem no_odd_div (i : ℕ) (hi : i < 281172) : ¬ (2 * i + 3) ∣ 316234143227 := by
  by_cases h0 : i < 70293
  · simpa using chk_sound _ _ _ k0 i h0
  by_cases h1 : i < 140586
  · have := chk_sound _ _ _ k1 (i - 70293) (by omega)
    rwa [show 70293 + (i - 70293) = i by omega] at this
  by_cases h2 : i < 210879
  · have := chk_sound _ _ _ k2 (i - 140586) (by omega)
    rwa [show 140586 + (i - 140586) = i by omega] at this
  · have := chk_sound _ _ _ k3 (i - 210879) (by omega)
    rwa [show 210879 + (i - 210879) = i by omega] at this

theorem P0_prime : Nat.Prime 316234143227 := by
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by norm_num : 0 < 316234143227) hnp
  have hmp := Nat.minFac_prime (show (316234143227 : ℕ) ≠ 1 by norm_num)
  have hdvd := Nat.minFac_dvd 316234143227
  generalize Nat.minFac 316234143227 = m at hsq hmp hdvd
  have hm2 : m ≠ 2 := by
    rintro rfl
    omega
  obtain ⟨j, hj⟩ := hmp.odd_of_ne_two hm2
  have hm3 : 3 ≤ m := by have := hmp.two_le; omega
  have hmle : m ≤ 562346 := by
    by_contra hc
    have hc' : 562347 ≤ m := by omega
    have : 562347 * 562347 ≤ m * m := Nat.mul_le_mul hc' hc'
    nlinarith
  have hi := no_odd_div (j - 1) (by omega)
  rw [show 2 * (j - 1) + 3 = m by omega] at hi
  exact hi hdvd

theorem v12 : apProdPlus 12 1 2 = 316234143227 := by decide +kernel
theorem w1 : apProdPlus 12 1 1 = 479001601 := by decide +kernel
theorem w2 : apProdPlus 12 2 1 = 6227020801 := by decide +kernel
theorem w3 : apProdPlus 12 3 1 = 43589145601 := by decide +kernel
theorem w4 : apProdPlus 12 4 1 = 217945728001 := by decide +kernel
theorem w5 : apProdPlus 12 5 1 = 871782912001 := by decide +kernel
theorem w6 : apProdPlus 12 6 1 = 2964061900801 := by decide +kernel

theorem mono (a : ℕ) (ha : 6 ≤ a) : apProdPlus 12 6 1 ≤ apProdPlus 12 a 1 := by
  unfold apProdPlus
  have : (∏ i ∈ Finset.range 12, (6 + i * 1)) ≤ ∏ i ∈ Finset.range 12, (a + i * 1) :=
    Finset.prod_le_prod' fun i _ => by omega
  omega

end OMA.Helpers

open OMA.Helpers OMA.S_oeis_a088120 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a088120.main) := by
  intro h
  obtain ⟨a, ha, hEq⟩ := h.2 12 (by norm_num)
  rw [if_neg (by decide)] at hEq
  have hin : (316234143227 : ℕ) ∈
      {p : ℕ | p.Prime ∧ ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ apProdPlus 12 a d = p} :=
    ⟨P0_prime, 1, 2, le_refl _, by norm_num, v12⟩
  have hle : minPrime 12 ≤ 316234143227 := Nat.sInf_le hin
  have hpr : (minPrime 12).Prime := (Nat.sInf_mem ⟨_, hin⟩).1
  rw [← hEq] at hpr hle
  by_cases ha6 : a ≤ 5
  · interval_cases a
    · rw [w1] at hpr
      exact Nat.not_prime_of_dvd_of_lt (by norm_num : 13 ∣ 479001601) (by norm_num) (by norm_num) hpr
    · rw [w2] at hpr
      exact Nat.not_prime_of_dvd_of_lt (by norm_num : 83 ∣ 6227020801) (by norm_num) (by norm_num) hpr
    · rw [w3] at hpr
      exact Nat.not_prime_of_dvd_of_lt (by norm_num : 31 ∣ 43589145601) (by norm_num) (by norm_num) hpr
    · rw [w4] at hpr
      exact Nat.not_prime_of_dvd_of_lt (by norm_num : 32009 ∣ 217945728001) (by norm_num)
        (by norm_num) hpr
    · rw [w5] at hpr
      exact Nat.not_prime_of_dvd_of_lt (by norm_num : 103 ∣ 871782912001) (by norm_num)
        (by norm_num) hpr
  · have h6 := mono a (by omega)
    rw [w6] at h6
    omega
