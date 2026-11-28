import OMAStatements.S_oeis_a154148
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a154148

def T (q : ℕ × ℕ) : ℕ × ℕ := (3 * q.1 + 8 * q.2, q.1 + 3 * q.2)

def W : ℕ → ℕ × ℕ
  | 0 => (11, 6)
  | 1 => (15, 7)
  | n + 2 => T (W n)

theorem W_add_two (n : ℕ) : W (n + 2) = T (W n) := rfl

theorem W_sol (n : ℕ) : (W n).1 ^ 2 + 167 = 8 * (W n).2 ^ 2 ∧ (W n).1 % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | n + 2, ih =>
      obtain ⟨h1, h2⟩ := ih n (by omega)
      rw [W_add_two]
      simp only [T]
      constructor
      · nlinarith [h1]
      · omega

theorem W_complete (y : ℕ) : ∀ x : ℕ, x ^ 2 + 167 = 8 * y ^ 2 → ∃ n, W n = (x, y) := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x hx
    by_cases hy : y < 14
    · have hx' : x < 37 := by nlinarith
      have key : ∀ x < 37, ∀ y < 14, x ^ 2 + 167 = 8 * y ^ 2 →
          (x = 11 ∧ y = 6) ∨ (x = 15 ∧ y = 7) := by decide
      rcases key x hx' y hy hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · replace hy : 14 ≤ y := by omega
      have h1 : 8 * y ≤ 3 * x := by
        by_contra h
        replace h := Nat.lt_of_not_le h
        have : (3 * x) ^ 2 < (8 * y) ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
        nlinarith
      have h2 : x ≤ 3 * y := by
        by_contra h
        replace h := Nat.lt_of_not_le h
        have : (3 * y) ^ 2 < x ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
        nlinarith
      have h3 : 2 * y < x := by
        by_contra h
        replace h := Nat.le_of_not_lt h
        have : x ^ 2 ≤ (2 * y) ^ 2 := Nat.pow_le_pow_left h 2
        nlinarith
      have hsol : (3 * x - 8 * y) ^ 2 + 167 = 8 * (3 * y - x) ^ 2 := by
        zify [h1, h2]
        have hx' : ((x : ℤ)) ^ 2 + 167 = 8 * (y : ℤ) ^ 2 := by exact_mod_cast hx
        linear_combination hx'
      obtain ⟨n, hn⟩ := ih (3 * y - x) (by omega) (3 * x - 8 * y) hsol
      refine ⟨n + 2, ?_⟩
      rw [W_add_two, hn]
      simp only [T, Prod.mk.injEq]
      constructor <;> omega

theorem W_mono (n : ℕ) : (W n).1 < (W (n + 1)).1 ∧ (W n).2 < (W (n + 1)).2 ∧
    (W (n + 1)).1 < 3 * (W n).1 + 8 * (W n).2 ∧ (W (n + 1)).2 < (W n).1 + 3 * (W n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [W_add_two]
    simp only [T]
    omega

/-- The `n`-th solution `k` (from 0). -/
def K (n : ℕ) : ℕ := ((W n).1 - 1) / 2

theorem K_spec (n : ℕ) : 2 * K n + 1 = (W n).1 := by
  have := (W_sol n).2
  unfold K
  omega

theorem K_strictMono : StrictMono K := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h1 := K_spec n
  have h2 := K_spec (n + 1)
  have h3 := (W_mono n).1
  omega

theorem P_iff (k : ℕ) : P k ↔ ∃ n, K n = k := by
  have he : k * (k + 1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self k)
  have hsq : (2 * k + 1) ^ 2 + 167 = 4 * (k * (k + 1)) + 168 := by ring
  constructor
  · rintro ⟨m, hm⟩
    have : (2 * k + 1) ^ 2 + 167 = 8 * m ^ 2 := by
      rw [hsq]
      generalize k * (k + 1) = s at he hm
      generalize m ^ 2 = M at hm
      omega
    obtain ⟨n, hn⟩ := W_complete m (2 * k + 1) this
    refine ⟨n, ?_⟩
    have := K_spec n
    rw [hn] at this
    simp only at this
    omega
  · rintro ⟨n, rfl⟩
    refine ⟨(W n).2, ?_⟩
    have h1 := (W_sol n).1
    have h2 := K_spec n
    have he' : K n * (K n + 1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self (K n))
    have hsq' : (2 * K n + 1) ^ 2 + 167 = 4 * (K n * (K n + 1)) + 168 := by ring
    rw [h2] at hsq'
    rw [hsq'] at h1
    generalize K n * (K n + 1) = s at he' h1 ⊢
    generalize (W n).2 ^ 2 = M at h1 ⊢
    omega

theorem nth_eq (j : ℕ) : Nat.nth P j = K j := by
  have hinf : (Set.ofPred P).Infinite := by
    have : Set.range K ⊆ Set.ofPred P := by
      rintro _ ⟨n, rfl⟩
      exact (P_iff _).2 ⟨n, rfl⟩
    exact Set.Infinite.mono this (Set.infinite_range_of_injective K_strictMono.injective)
  have hS : ∀ n : ℕ, n ∈ {n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card} :=
    fun n hf => absurd hf hinf
  have := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := P) K
    (fun k hk => by
      obtain ⟨n, hn⟩ := (P_iff k).1 hk
      exact ⟨n, hS n, hn⟩)
    (fun n _ => (P_iff _).2 ⟨n, rfl⟩)
    (K_strictMono.strictMonoOn _) (hS j)
  exact this.symm

theorem a_eq (n : ℕ) : a (n + 1) = K n := by
  unfold a
  rw [Nat.add_sub_cancel, nth_eq]

theorem K_rec (n : ℕ) : (K (n + 4) : ℤ) = 6 * K (n + 2) - K n + 2 := by
  have h1 := K_spec (n + 4)
  have h2 := K_spec (n + 2)
  have h3 := K_spec n
  have e1 : (W (n + 4)).1 = 3 * (W (n + 2)).1 + 8 * (W (n + 2)).2 := rfl
  have e2 : (W (n + 2)).1 = 3 * (W n).1 + 8 * (W n).2 := rfl
  have e3 : (W (n + 2)).2 = (W n).1 + 3 * (W n).2 := rfl
  omega

theorem recur (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  simp only [show j + 6 - 1 = j + 4 + 1 by omega, show j + 6 - 2 = j + 3 + 1 by omega,
    show j + 6 - 3 = j + 2 + 1 by omega, show j + 6 - 4 = j + 1 + 1 by omega,
    show j + 6 - 5 = j + 1 by omega, show j + 6 = j + 5 + 1 by omega, a_eq]
  have h1 := K_rec (j + 1)
  have h2 := K_rec j
  simp only [show j + 1 + 4 = j + 5 by omega, show j + 1 + 2 = j + 3 by omega] at h1
  linarith

theorem a_vals : a 1 = 5 ∧ a 2 = 7 ∧ a 3 = 40 ∧ a 4 = 50 ∧ a 5 = 237 := by
  rw [a_eq 0, a_eq 1, a_eq 2, a_eq 3, a_eq 4]
  decide

open PowerSeries in
theorem gf1 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (-5 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4) := by
  set f := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hf
  have key : f * ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      C 1 * (f * X ^ 1) - C 1 * (f * X ^ 0) + C 6 * (f * X ^ 2) - C 6 * (f * X ^ 3) -
        C 1 * (f * X ^ 4) + C 1 * (f * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (-5 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4) : PowerSeries ℚ) =
      C 2 * X ^ 4 + C 6 * X ^ 5 - C 5 * X ^ 1 - C 2 * X ^ 2 - C 3 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hf, coeff_mk, coeff_C]
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [v1, v2, v3, v4, v5]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    have hr := recur (j + 6) (by omega)
    simp only [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 5 = j + 1 by omega] at hr
    simp only [show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega]
    simp (disch := omega) only [if_pos, if_neg]
    have hr' : (a (j + 6) : ℚ) = a (j + 5) + 6 * a (j + 4) - 6 * a (j + 3) - a (j + 2) +
        a (j + 1) := by exact_mod_cast hr
    linarith

open PowerSeries in
theorem gf2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (12 + (12 + 25 * X) * (X ^ 2 - 2 * X - 1)⁻¹ + (X - 1)⁻¹ +
        (-1 - 10 * X) * (X ^ 2 + 2 * X - 1)⁻¹) := by
  have h1 : (X ^ 2 - 2 * X - 1 : ℚ⟦X⟧) * (X ^ 2 - 2 * X - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have h2 : (X ^ 2 + 2 * X - 1 : ℚ⟦X⟧) * (X ^ 2 + 2 * X - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have h3 : (X - 1 : ℚ⟦X⟧) * (X - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hC : C (1 / 2 : ℚ) * 2 = 1 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  have hD0 : ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (constantCoeff (R := ℚ)) h
    simp at this
  have hR : C (1 / 2 : ℚ) * (12 + (12 + 25 * X) * (X ^ 2 - 2 * X - 1)⁻¹ + (X - 1)⁻¹ +
        (-1 - 10 * X) * (X ^ 2 + 2 * X - 1)⁻¹) *
        ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      X * (-5 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4) := by
    linear_combination (C (1 / 2 : ℚ) * (12 + 25 * X) * (X - 1) * (X ^ 2 + 2 * X - 1)) * h1 +
      (C (1 / 2 : ℚ) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) * h3 +
      (C (1 / 2 : ℚ) * (-1 - 10 * X) * (X - 1) * (X ^ 2 - 2 * X - 1)) * h2 +
      (X * (-5 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4)) * hC
  exact mul_right_cancel₀ hD0 (gf1.trans hR.symm)

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a154148.main :=
  ⟨OMA.Helpers.recur, OMA.Helpers.gf1, OMA.Helpers.gf2⟩
