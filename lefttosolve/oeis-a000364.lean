import OMAStatements.S_oeis_a000364
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a000364

theorem sec_succ (n : ℕ) : secantNumber (n + 1) = ∑ j ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (j + 2) * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j) := by
  rw [secantNumber, Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ (j + 2) *
    ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j))]

theorem e0 : secantNumber 0 = 1 := by rw [secantNumber]

theorem e1 : secantNumber 1 = 1 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0]

theorem e2 : secantNumber 2 = 5 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1]

theorem e3 : secantNumber 3 = 61 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2]

theorem e4 : secantNumber 4 = 1385 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3]

theorem e5 : secantNumber 5 = 50521 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4]

theorem e6 : secantNumber 6 = 2702765 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5]

theorem e7 : secantNumber 7 = 199360981 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6]

theorem e8 : secantNumber 8 = 19391512145 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7]

theorem e9 : secantNumber 9 = 2404879675441 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem e10 : secantNumber 10 = 370371188237525 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]

theorem e11 : secantNumber 11 = 69348874393137901 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

theorem e12 : secantNumber 12 = 15514534163557086905 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

theorem e13 : secantNumber 13 = 4087072509293123892361 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

theorem e14 : secantNumber 14 = 1252259641403629865468285 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]

theorem e15 : secantNumber 15 = 441543893249023104553682821 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]

theorem e16 : secantNumber 16 = 177519391579539289436664789665 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]

theorem e17 : secantNumber 17 = 80723299235887898062168247453281 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16]

theorem e18 : secantNumber 18 = 41222060339517702122347079671259045 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]

theorem e19 : secantNumber 19 = 23489580527043108252017828576198947741 := by
  rw [sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a000364.main) := by
  intro h
  obtain ⟨p, -, hpd, hper⟩ := h 27 (by norm_num)
  have htot : Nat.totient 27 = 18 := by
    rw [show (27 : ℕ) = 3 ^ (2 + 1) by norm_num, Nat.totient_prime_pow_succ Nat.prime_three]
    norm_num
  rw [htot] at hpd
  obtain ⟨q, hq⟩ := hpd
  have key : ∀ j : ℕ, Int.ModEq ((27 : ℕ) : ℤ)
      (OMA.S_oeis_a000364.secantNumber (1 + p * j)) (OMA.S_oeis_a000364.secantNumber 1) := by
    intro j
    induction j with
    | zero => simp [Int.ModEq.refl]
    | succ j ih =>
      have h1 := hper (1 + p * j) (by omega)
      rw [show 1 + p * (j + 1) = 1 + p * j + p by ring]
      exact h1.trans ih
  have h19 := key q
  rw [← hq, OMA.Helpers.e1, show 1 + 18 = 19 by rfl, OMA.Helpers.e19] at h19
  norm_num [Int.ModEq] at h19
