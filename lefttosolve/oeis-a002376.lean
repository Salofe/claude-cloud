import OMAStatements.S_oeis_a002376
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a002376 PowerSeries

/-- Below 27 only the cubes 1 and 8 are available, so a sum of k positive cubes equal to n
has the form k + 7 m with m at most k. -/
theorem a002376_small_form {n k : ℕ} (hn : n < 27) (h : IsSumOfCubes n k) :
    ∃ m ≤ k, n = k + 7 * m := by
  obtain ⟨f, hf1, hsum⟩ := h
  have hle : ∀ i, f i ≤ 2 := by
    intro i
    by_contra hc
    replace hc := not_le.mp hc
    have h3 : 27 ≤ f i ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ f i ^ 3 := Nat.pow_le_pow_left hc 3
    have : f i ^ 3 ≤ ∑ j : Fin k, f j ^ 3 :=
      Finset.single_le_sum (f := fun j => f j ^ 3) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  have hcube : ∀ i, f i ^ 3 = 1 + 7 * (f i - 1) := by
    intro i
    obtain h | h : f i = 1 ∨ f i = 2 := by have := hf1 i; have := hle i; omega
    · rw [h]; norm_num
    · rw [h]; norm_num
  refine ⟨∑ i : Fin k, (f i - 1), ?_, ?_⟩
  · calc ∑ i : Fin k, (f i - 1) ≤ ∑ _i : Fin k, 1 :=
          Finset.sum_le_sum (fun i _ => by have := hle i; omega)
      _ = k := by simp
  · rw [← hsum]
    simp_rw [hcube]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp

theorem a002376_27_le : A002376 27 ≤ 1 :=
  Nat.sInf_le ⟨![3], fun i => by fin_cases i; decide, by decide⟩

theorem a002376_18_le : A002376 18 ≤ 4 :=
  Nat.sInf_le ⟨![2, 2, 1, 1], fun i => by fin_cases i <;> decide, by decide⟩

theorem a002376_26_ge : 5 ≤ A002376 26 :=
  le_csInf ⟨5, ![2, 2, 2, 1, 1], fun i => by fin_cases i <;> decide, by decide⟩
    (fun k hk => by
      obtain ⟨m, hm, he⟩ := a002376_small_form (by norm_num) hk
      omega)

theorem a002376_19_ge : 5 ≤ A002376 19 :=
  le_csInf ⟨5, ![2, 2, 1, 1, 1], fun i => by fin_cases i <;> decide, by decide⟩
    (fun k hk => by
      obtain ⟨m, hm, he⟩ := a002376_small_form (by norm_num) hk
      omega)

theorem a002376_poly :
    ((X + 1) * (X ^ 2 + 1) * (X ^ 4 + 1) * (X - 1) ^ 2 : PowerSeries ℤ) =
      X ^ 9 - X ^ 8 - X + 1 := by
  ring

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002376.main) := by
  intro h
  rw [a002376_poly] at h
  have hc := congrArg (PowerSeries.coeff 26) h
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub, map_neg, coeff_X_pow_mul',
    coeff_mk, coeff_X_pow, coeff_one, coeff_X, coeff_C_mul] at hc
  norm_num at hc
  have h1 := a002376_27_le
  have h2 := a002376_18_le
  have h3 := a002376_26_ge
  have h4 := a002376_19_ge
  omega
