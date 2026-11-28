import OMAStatements.S_oeis_a154140
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a154140

/-- The step `(k, Y) ↦ (3k + 4Y + 1, 2k + 3Y + 1)`, i.e. multiplication of
`(2k + 1) + Y √8` by the unit `3 + √8`. -/
def a154140_st (p : ℕ × ℕ) : ℕ × ℕ := (3 * p.1 + 4 * p.2 + 1, 2 * p.1 + 3 * p.2 + 1)

def a154140_cA : ℕ → ℕ × ℕ
  | 0 => (2, 3)
  | j + 1 => a154140_st (a154140_cA j)

def a154140_cB : ℕ → ℕ × ℕ
  | 0 => (4, 4)
  | j + 1 => a154140_st (a154140_cB j)

/-- `(k, Y)` solves `k (k + 1) + 12 = 2 Y^2`. -/
def a154140_Sol (p : ℕ × ℕ) : Prop := p.1 * (p.1 + 1) + 12 = 2 * p.2 ^ 2

theorem a154140_st_sol {p : ℕ × ℕ} (h : a154140_Sol p) : a154140_Sol (a154140_st p) := by
  unfold a154140_Sol a154140_st at *
  zify at h ⊢
  linear_combination h

theorem a154140_cA_sol (j : ℕ) : a154140_Sol (a154140_cA j) := by
  induction j with
  | zero => unfold a154140_Sol a154140_cA; norm_num
  | succ j ih => exact a154140_st_sol ih

theorem a154140_cB_sol (j : ℕ) : a154140_Sol (a154140_cB j) := by
  induction j with
  | zero => unfold a154140_Sol a154140_cB; norm_num
  | succ j ih => exact a154140_st_sol ih

theorem a154140_order (j : ℕ) :
    ((a154140_cA j).1 < (a154140_cB j).1 ∧ (a154140_cA j).2 < (a154140_cB j).2) ∧
    ((a154140_cB j).1 < (a154140_cA (j + 1)).1 ∧ (a154140_cB j).2 < (a154140_cA (j + 1)).2) := by
  induction j with
  | zero => simp [a154140_cA, a154140_cB, a154140_st]
  | succ j ih =>
    simp only [a154140_cA, a154140_cB, a154140_st] at ih ⊢
    omega

theorem a154140_complete (Y : ℕ) : ∀ k : ℕ, a154140_Sol (k, Y) →
    ∃ j, (k, Y) = a154140_cA j ∨ (k, Y) = a154140_cB j := by
  induction Y using Nat.strong_induction_on with
  | _ Y ih =>
    intro k hk
    unfold a154140_Sol at hk
    simp only at hk
    by_cases hd : 4 * Y ≤ 3 * k + 1
    · have h3 : 2 * k + 1 < 3 * Y := by nlinarith
      have hY : 1 ≤ Y := by
        rcases Nat.eq_zero_or_pos Y with h | h
        · subst h; simp at hk
        · exact h
      have hk1 : 1 ≤ k := by omega
      have hlt : 3 * Y - (2 * k + 1) < Y := by omega
      have hs : a154140_Sol (3 * k + 1 - 4 * Y, 3 * Y - (2 * k + 1)) := by
        unfold a154140_Sol
        simp only
        zify [hd, h3.le]
        have hk' : ((k : ℤ) * (k + 1) + 12 = 2 * (Y : ℤ) ^ 2) := by exact_mod_cast hk
        linear_combination hk'
      obtain ⟨j, hj⟩ := ih _ hlt _ hs
      refine ⟨j + 1, ?_⟩
      rcases hj with hj | hj
      · left
        simp only [a154140_cA, ← hj, a154140_st, Prod.mk.injEq]
        omega
      · right
        simp only [a154140_cB, ← hj, a154140_st, Prod.mk.injEq]
        omega
    · have hk7 : k ≤ 7 := by nlinarith
      have hY5 : Y ≤ 6 := by nlinarith
      refine ⟨0, ?_⟩
      interval_cases k <;> interval_cases Y <;> simp_all [a154140_cA, a154140_cB]

/-- The merged enumeration: chain A at even places, chain B at odd places. -/
def a154140_c (i : ℕ) : ℕ := if i % 2 = 0 then (a154140_cA (i / 2)).1 else (a154140_cB (i / 2)).1

theorem a154140_c_strictMono : StrictMono a154140_c := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
  · unfold a154140_c
    rw [if_pos (by omega), if_neg (by omega), show 2 * j / 2 = j by omega,
      show (2 * j + 1) / 2 = j by omega]
    exact (a154140_order j).1.1
  · unfold a154140_c
    rw [if_neg (by omega), if_pos (by omega), show (2 * j + 1) / 2 = j by omega,
      show (2 * j + 1 + 1) / 2 = j + 1 by omega]
    exact (a154140_order j).2.1

theorem a154140_P_of_sol {p : ℕ × ℕ} (h : a154140_Sol p) : P p.1 := by
  refine ⟨p.2, ?_⟩
  unfold a154140_Sol at h
  omega

theorem a154140_c_P (i : ℕ) : P (a154140_c i) := by
  unfold a154140_c
  split_ifs
  · exact a154140_P_of_sol (a154140_cA_sol _)
  · exact a154140_P_of_sol (a154140_cB_sol _)

theorem a154140_c_surj {k : ℕ} (hk : P k) : ∃ i, a154140_c i = k := by
  obtain ⟨m, hm⟩ := hk
  have he : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  have hs : a154140_Sol (k, m) := by
    unfold a154140_Sol
    simp only
    omega
  obtain ⟨j, hj | hj⟩ := a154140_complete m k hs
  · refine ⟨2 * j, ?_⟩
    unfold a154140_c
    rw [if_pos (by omega), show 2 * j / 2 = j by omega, ← hj]
  · refine ⟨2 * j + 1, ?_⟩
    unfold a154140_c
    rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega, ← hj]

theorem a154140_nth (i : ℕ) : Nat.nth P i = a154140_c i := by
  have hinf : (Set.ofPred P).Infinite :=
    Set.infinite_of_injective_forall_mem a154140_c_strictMono.injective a154140_c_P
  have hall : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun n hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn a154140_c ?_ ?_ ?_ (hall i)).symm
  · intro k hk
    obtain ⟨j, hj⟩ := a154140_c_surj hk
    exact ⟨j, hall j, hj⟩
  · intro n _
    exact a154140_c_P n
  · intro x _ y _ hxy
    exact a154140_c_strictMono hxy

theorem a154140_a_eq (n : ℕ) : a (n + 1) = a154140_c n := by
  rw [a, Nat.add_sub_cancel, a154140_nth]

theorem a154140_st_st (p : ℕ × ℕ) :
    (a154140_st (a154140_st p)).1 + p.1 = 6 * (a154140_st p).1 + 2 := by
  simp only [a154140_st]; omega

theorem a154140_c_rec (i : ℕ) : a154140_c (i + 4) + a154140_c i = 6 * a154140_c (i + 2) + 2 := by
  unfold a154140_c
  rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show (2 * j + 4) / 2 = j + 2 by omega, show (2 * j + 2) / 2 = j + 1 by omega,
      show 2 * j / 2 = j by omega]
    exact a154140_st_st (a154140_cA j)
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (2 * j + 1 + 4) / 2 = j + 2 by omega, show (2 * j + 1 + 2) / 2 = j + 1 by omega,
      show (2 * j + 1) / 2 = j by omega]
    exact a154140_st_st (a154140_cB j)

theorem a154140_rec (i : ℕ) : (a (i + 6) : ℤ) = a (i + 5) + 6 * a (i + 4) - 6 * a (i + 3) -
    a (i + 2) + a (i + 1) := by
  rw [a154140_a_eq (i + 5), a154140_a_eq (i + 4), a154140_a_eq (i + 3), a154140_a_eq (i + 2),
    a154140_a_eq (i + 1), a154140_a_eq i]
  have h1 := a154140_c_rec i
  have h2 := a154140_c_rec (i + 1)
  rw [show i + 1 + 4 = i + 5 by omega, show i + 1 + 2 = i + 3 by omega] at h2
  omega

theorem a154140_small : a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 19 ∧ a 4 = 29 ∧ a 5 = 114 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [a154140_a_eq]
    decide

end OMA.Helpers

open PowerSeries in
theorem OMA.Helpers.a154140_gf1 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a154140.a n : ℚ)) *
      ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (2 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4) := by
  set B := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a154140.a n : ℚ))
    with hB
  have eD : B * ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      B - C (1 : ℚ) * (B * X ^ 1) - C (6 : ℚ) * (B * X ^ 2) + C (6 : ℚ) * (B * X ^ 3) +
        C (1 : ℚ) * (B * X ^ 4) - C (1 : ℚ) * (B * X ^ 5) := by
    simp only [map_ofNat, map_one]; ring
  have eN : (X * (2 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4) : ℚ⟦X⟧) =
      C (2 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 - C (2 : ℚ) * X ^ 4 -
        C (3 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [eD, eN]
  obtain ⟨v1, v2, v3, v4, v5⟩ := OMA.Helpers.a154140_small
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', hB, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | m
  · simp
  · norm_num [v1]
  · norm_num [v1, v2]
  · norm_num [v1, v2, v3]
  · norm_num [v1, v2, v3, v4]
  · norm_num [v1, v2, v3, v4, v5]
  · have h := OMA.Helpers.a154140_rec m
    have hq : (OMA.S_oeis_a154140.a (m + 6) : ℚ) = OMA.S_oeis_a154140.a (m + 5) +
        6 * OMA.S_oeis_a154140.a (m + 4) - 6 * OMA.S_oeis_a154140.a (m + 3) -
        OMA.S_oeis_a154140.a (m + 2) + OMA.S_oeis_a154140.a (m + 1) := by exact_mod_cast h
    simp only [show 1 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
      show 2 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
      show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
      show 4 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
      show 5 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 from by omega, if_true,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 5 from by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 4 from by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 3 from by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 2 from by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 from by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 = m + 6 from by omega,
      show m + 6 ≠ 0 from by omega, show m + 5 ≠ 0 from by omega, show m + 4 ≠ 0 from by omega,
      show m + 3 ≠ 0 from by omega, show m + 2 ≠ 0 from by omega, show m + 1 ≠ 0 from by omega,
      if_false, coeff_C]
    linarith

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a154140.main := by
  refine ⟨?_, OMA.Helpers.a154140_gf1, ?_⟩
  · intro n hn
    obtain ⟨i, rfl⟩ : ∃ i, n = i + 6 := ⟨n - 6, by omega⟩
    rw [show i + 6 - 1 = i + 5 by omega, show i + 6 - 2 = i + 4 by omega,
      show i + 6 - 3 = i + 3 by omega, show i + 6 - 4 = i + 2 by omega,
      show i + 6 - 5 = i + 1 by omega]
    exact OMA.Helpers.a154140_rec i
  · set D : ℚ⟦X⟧ := (1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) with hD
    have hD0 : D ≠ 0 := by
      intro h
      have := congrArg constantCoeff h
      simp [hD] at this
    refine mul_right_cancel₀ hD0 ?_
    rw [OMA.Helpers.a154140_gf1]
    have hq1 : (X ^ 2 + 2 * X - 1 : ℚ⟦X⟧)⁻¹ * (X ^ 2 + 2 * X - 1) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp)
    have hq2 : (X ^ 2 - 2 * X - 1 : ℚ⟦X⟧)⁻¹ * (X ^ 2 - 2 * X - 1) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp)
    have hq3 : (X - 1 : ℚ⟦X⟧)⁻¹ * (X - 1) = 1 := PowerSeries.inv_mul_cancel _ (by simp)
    have hC : C (1 / 2 : ℚ) * 2 = 1 := by
      rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, ← map_mul]; norm_num
    rw [hD]
    linear_combination (-(C (1 / 2 : ℚ)) * (-1 - 4 * X) * (1 - X) * (X ^ 2 - 2 * X - 1)) * hq1 -
      C (1 / 2 : ℚ) * (6 + 13 * X) * (1 - X) * (X ^ 2 + 2 * X - 1) * hq2 +
      C (1 / 2 : ℚ) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) * hq3 -
      X * (2 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4) * hC
