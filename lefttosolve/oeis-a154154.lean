import OMAStatements.S_oeis_a154154
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a154154

/-- Solutions `(x, m)` of `x^2 + 239 = 8 m^2` in increasing order of `x`. -/
def pr154 : ℕ → ℕ × ℕ
  | 0 => (7, 6)
  | 1 => (27, 11)
  | n + 2 => (3 * (pr154 n).1 + 8 * (pr154 n).2, (pr154 n).1 + 3 * (pr154 n).2)

theorem pr154_succ_succ (n : ℕ) : pr154 (n + 2) =
    (3 * (pr154 n).1 + 8 * (pr154 n).2, (pr154 n).1 + 3 * (pr154 n).2) := rfl

theorem pr154_sol (n : ℕ) : (pr154 n).1 ^ 2 + 239 = 8 * (pr154 n).2 ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | n + 2, ih =>
      have h := ih n (by omega)
      rw [pr154_succ_succ]
      simp only
      nlinarith [h]

theorem pr154_odd (n : ℕ) : (pr154 n).1 % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | n + 2, ih =>
      have h := ih n (by omega)
      rw [pr154_succ_succ]
      simp only
      omega

theorem sol_mono {x m x' m' : ℕ} (h : x ^ 2 + 239 = 8 * m ^ 2) (h' : x' ^ 2 + 239 = 8 * m' ^ 2)
    (hx : x < x') : m < m' := by
  by_contra hc
  push Not at hc
  have : x' ^ 2 ≤ x ^ 2 := by nlinarith [Nat.mul_le_mul hc hc]
  nlinarith

theorem pr154_lt (n : ℕ) : (pr154 n).1 < (pr154 (n + 1)).1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | n + 2, ih =>
      have h := ih n (by omega)
      have hm := sol_mono (pr154_sol n) (pr154_sol (n + 1)) h
      rw [pr154_succ_succ, show n + 2 + 1 = (n + 1) + 2 by ring, pr154_succ_succ]
      simp only
      omega

theorem small_sol : ∀ x < 44, ∀ m < 17, x ^ 2 + 239 = 8 * m ^ 2 → x = 7 ∨ x = 27 := by
  decide

theorem sol_in_range : ∀ x m : ℕ, x ^ 2 + 239 = 8 * m ^ 2 → ∃ n, (pr154 n).1 = x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro m h
    by_cases hx : x < 44
    · have hm : m < 17 := by nlinarith
      rcases small_sol x hx m hm h with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · push Not at hx
      have h1 : 8 * m ≤ 3 * x := by nlinarith
      have h2 : x ≤ 3 * m := by nlinarith
      have h3 : 3 * x - 8 * m < x := by
        have : x < 4 * m := by nlinarith
        omega
      have hsol : (3 * x - 8 * m) ^ 2 + 239 = 8 * (3 * m - x) ^ 2 := by
        zify [h1, h2]
        have h' : (x : ℤ) ^ 2 + 239 = 8 * (m : ℤ) ^ 2 := by exact_mod_cast h
        linear_combination h'
      obtain ⟨n, hn⟩ := ih _ h3 _ hsol
      refine ⟨n + 2, ?_⟩
      have hmn : (pr154 n).2 = 3 * m - x := by
        have e := pr154_sol n
        rw [hn] at e
        have : (pr154 n).2 ^ 2 = (3 * m - x) ^ 2 := by omega
        exact Nat.pow_left_injective (by norm_num) this
      rw [pr154_succ_succ]
      simp only
      rw [hn, hmn]
      omega

/-- The candidate for `nth P`. -/
def f154 (n : ℕ) : ℕ := (pr154 n).1 / 2

theorem f154_strictMono : StrictMono f154 := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 := pr154_lt n
  have h2 := pr154_odd n
  have h3 := pr154_odd (n + 1)
  unfold f154
  omega

theorem P_iff (k : ℕ) : P k ↔ ∃ n, f154 n = k := by
  constructor
  · rintro ⟨m, hm⟩
    have hk : (2 * k + 1) ^ 2 + 239 = 8 * m ^ 2 := by
      have e : k * (k + 1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self k)
      have e2 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      rw [e2]
      generalize k * (k + 1) = t at hm e
      omega
    obtain ⟨n, hn⟩ := sol_in_range _ _ hk
    exact ⟨n, by unfold f154; rw [hn]; omega⟩
  · rintro ⟨n, rfl⟩
    refine ⟨(pr154 n).2, ?_⟩
    have h1 := pr154_sol n
    have h2 := pr154_odd n
    obtain ⟨k, hk⟩ : ∃ k, (pr154 n).1 = 2 * k + 1 := ⟨(pr154 n).1 / 2, by omega⟩
    have hf : f154 n = k := by unfold f154; omega
    rw [hf]
    rw [hk] at h1
    have e2 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [e2] at h1
    generalize k * (k + 1) = t at h1 ⊢
    generalize (pr154 n).2 ^ 2 = s at h1 ⊢
    omega

theorem a_eq (n : ℕ) : a n = f154 (n - 1) := by
  unfold a
  have hinf : (Set.ofPred P).Infinite := by
    have : Set.range f154 ⊆ Set.ofPred P := by
      rintro _ ⟨j, rfl⟩
      exact (P_iff _).2 ⟨j, rfl⟩
    exact Set.Infinite.mono this (Set.infinite_range_of_injective f154_strictMono.injective)
  have hall : ∀ j : ℕ, j ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun j hf => absurd hf hinf
  symm
  apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f154
  · intro k hk
    obtain ⟨j, hj⟩ := (P_iff k).1 hk
    exact ⟨j, hall j, hj⟩
  · intro j _
    exact (P_iff _).2 ⟨j, rfl⟩
  · exact f154_strictMono.strictMonoOn _
  · exact hall _

theorem x_rec (n : ℕ) :
    ((pr154 (n + 4)).1 : ℤ) = 6 * (pr154 (n + 2)).1 - (pr154 n).1 := by
  rw [show n + 4 = (n + 2) + 2 by ring, pr154_succ_succ, pr154_succ_succ]
  simp only
  push_cast
  ring

theorem f_cast (n : ℕ) : (2 * (f154 n : ℤ) + 1) = (pr154 n).1 := by
  have h := pr154_odd n
  unfold f154
  omega

theorem rec154 (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  rw [a_eq (j + 6), a_eq (j + 6 - 1), a_eq (j + 6 - 2), a_eq (j + 6 - 3), a_eq (j + 6 - 4),
    a_eq (j + 6 - 5)]
  rw [show j + 6 - 1 - 1 = j + 4 by omega,
    show j + 6 - 2 - 1 = j + 3 by omega, show j + 6 - 3 - 1 = j + 2 by omega,
    show j + 6 - 4 - 1 = j + 1 by omega, show j + 6 - 5 - 1 = j by omega]
  have e0 := f_cast j
  have e1 := f_cast (j + 1)
  have e2 := f_cast (j + 2)
  have e3 := f_cast (j + 3)
  have e4 := f_cast (j + 4)
  have e5 := f_cast (j + 5)
  have r1 := x_rec j
  have r2 := x_rec (j + 1)
  rw [show j + 1 + 4 = j + 5 by ring, show j + 1 + 2 = j + 3 by ring] at r2
  rw [show j + 6 - 1 = j + 5 by omega]
  linarith

theorem vals154 : a 1 = 3 ∧ a 2 = 13 ∧ a 3 = 34 ∧ a 4 = 84 ∧ a 5 = 203 := by
  simp only [a_eq]
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

open PowerSeries in
theorem gf154 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (-3 - 10 * X - 3 * X ^ 2 + 10 * X ^ 3 + 4 * X ^ 4) := by
  set g : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hg
  have e1 : PowerSeries.mk g * ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1))
      = PowerSeries.mk g * X ^ 5 - PowerSeries.mk g * X ^ 4
        - C (6 : ℚ) * (PowerSeries.mk g * X ^ 3) + C (6 : ℚ) * (PowerSeries.mk g * X ^ 2)
        + PowerSeries.mk g * X ^ 1 - PowerSeries.mk g := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (-3 - 10 * X - 3 * X ^ 2 + 10 * X ^ 3 + 4 * X ^ 4) : PowerSeries ℚ)
      = C (-3 : ℚ) * X ^ 1 - C (10 : ℚ) * X ^ 2 - C (3 : ℚ) * X ^ 3 + C (10 : ℚ) * X ^ 4
        + C (4 : ℚ) * X ^ 5 := by
    simp only [map_neg, map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  obtain ⟨v1, v2, v3, v4, v5⟩ := vals154
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> simp [hg, v1, v2, v3, v4, v5] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    have r := rec154 (m + 6) (by omega)
    simp only [show 5 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
      show 2 ≤ m + 6 by omega, show 1 ≤ m + 6 by omega, if_true,
      show m + 6 ≠ 1 by omega, show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega,
      show m + 6 ≠ 4 by omega, show m + 6 ≠ 5 by omega, if_false]
    simp only [hg, show m + 6 - 5 ≠ 0 by omega, show m + 6 - 4 ≠ 0 by omega,
      show m + 6 - 3 ≠ 0 by omega, show m + 6 - 2 ≠ 0 by omega, show m + 6 - 1 ≠ 0 by omega,
      show m + 6 ≠ 0 by omega, if_false]
    have r' : (a (m + 6) : ℚ) = a (m + 6 - 1) + 6 * a (m + 6 - 2) - 6 * a (m + 6 - 3)
        - a (m + 6 - 4) + a (m + 6 - 5) := by exact_mod_cast r
    rw [r']
    ring

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a154154.main := by
  have hgf := OMA.Helpers.gf154
  refine ⟨OMA.Helpers.rec154, hgf, ?_⟩
  have hD : constantCoeff ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) : PowerSeries ℚ) ≠ 0 := by
    simp
  have hu : constantCoeff (X ^ 2 + 2 * X - 1 : PowerSeries ℚ) ≠ 0 := by simp
  have hv : constantCoeff (X ^ 2 - 2 * X - 1 : PowerSeries ℚ) ≠ 0 := by simp
  have hw : constantCoeff (X - 1 : PowerSeries ℚ) ≠ 0 := by simp
  have iu := PowerSeries.inv_mul_cancel _ hu
  have iv := PowerSeries.inv_mul_cancel _ hv
  have iw := PowerSeries.inv_mul_cancel _ hw
  have ih : C (1 / 2 : ℚ) * 2 = (1 : PowerSeries ℚ) := by
    have h2 : (C (1 / 2 : ℚ) : PowerSeries ℚ) * C (2 : ℚ) = 1 := by
      rw [← map_mul]; norm_num
    rw [show (2 : PowerSeries ℚ) = C (2 : ℚ) from (map_ofNat C 2).symm]
    exact h2
  have h1 := (PowerSeries.eq_mul_inv_iff_mul_eq hD).2 hgf
  rw [h1]
  symm
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  linear_combination (C (1 / 2 : ℚ) * (-5 - 2 * X) * (X - 1) * (X ^ 2 - 2 * X - 1)) * iu
    + (C (1 / 2 : ℚ) * (12 + 29 * X) * (X - 1) * (X ^ 2 + 2 * X - 1)) * iv
    + (C (1 / 2 : ℚ) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) * iw
    + (X * (-3 - 10 * X - 3 * X ^ 2 + 10 * X ^ 3 + 4 * X ^ 4)) * ih
