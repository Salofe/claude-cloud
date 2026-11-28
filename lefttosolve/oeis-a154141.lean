import OMAStatements.S_oeis_a154141
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- The automorphism `(k, m) ↦ (3k + 4m + 1, 2k + 3m + 1)` of `16 + k(k+1) = 2m^2`. -/
def T (p : ℕ × ℕ) : ℕ × ℕ := (3 * p.1 + 4 * p.2 + 1, 2 * p.1 + 3 * p.2 + 1)

/-- The two orbits `(1, 3)` and `(7, 6)` interleaved. -/
def s : ℕ → ℕ × ℕ
  | 0 => (1, 3)
  | 1 => (7, 6)
  | n + 2 => T (s n)

theorem s_two (n : ℕ) : s (n + 2) = T (s n) := rfl

theorem s_sol (n : ℕ) : 16 + (s n).1 * ((s n).1 + 1) = 2 * (s n).2 ^ 2 ∧
    16 + (s (n + 1)).1 * ((s (n + 1)).1 + 1) = 2 * (s (n + 1)).2 ^ 2 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 1 = n + 2 by omega, s_two, T]
    have h := ih.1
    simp only
    nlinarith [h]

theorem s_lt (n : ℕ) : ((s n).1 < (s (n + 1)).1 ∧ (s n).2 < (s (n + 1)).2) ∧
    ((s (n + 1)).1 < (s (n + 2)).1 ∧ (s (n + 1)).2 < (s (n + 2)).2) := by
  induction n with
  | zero => exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 1 = n + 2 by omega, show n + 2 + 1 = (n + 1) + 2 by omega, s_two, s_two, T, T]
    obtain ⟨⟨h1, h2⟩, -⟩ := ih
    simp only
    constructor <;> omega

/-- `f n` is the `n`-th solution `k`. -/
def f (n : ℕ) : ℕ := (s n).1

theorem f_strictMono : StrictMono f := strictMono_nat_of_lt_succ fun n => (s_lt n).1.1

theorem small : ∀ k < 13, ∀ m < 10, 16 + k * (k + 1) = 2 * m ^ 2 →
    (k = 1 ∧ m = 3) ∨ (k = 7 ∧ m = 6) := by
  decide

theorem complete (k : ℕ) : ∀ m, 16 + k * (k + 1) = 2 * m ^ 2 → ∃ n, s n = (k, m) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m h
    by_cases hk : k < 13
    · have hm : m < 10 := by
        by_contra hc
        have : 10 * 10 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
        have : k * (k + 1) ≤ 12 * 13 := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      rcases small k hk m hm h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · have h1 : 4 * m ≤ 3 * k + 1 := by
        by_contra hc
        have : (3 * k + 2) * (3 * k + 2) ≤ (4 * m) * (4 * m) := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      have h2 : 2 * k + 1 ≤ 3 * m := by
        by_contra hc
        have : (3 * m) * (3 * m) ≤ (2 * k) * (2 * k) := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      have h3 : 2 * k + 1 < 4 * m := by
        by_contra hc
        have : (4 * m) * (4 * m) ≤ (2 * k + 1) * (2 * k + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      have hsol : 16 + (3 * k + 1 - 4 * m) * (3 * k + 1 - 4 * m + 1) =
          2 * (3 * m - (2 * k + 1)) ^ 2 := by
        zify [h1, h2]
        have hz : (16 : ℤ) + k * (k + 1) = 2 * m ^ 2 := by exact_mod_cast h
        linear_combination hz
      obtain ⟨n, hn⟩ := ih (3 * k + 1 - 4 * m) (by omega) (3 * m - (2 * k + 1)) hsol
      refine ⟨n + 2, ?_⟩
      rw [s_two, hn, T]
      simp only [Prod.mk.injEq]
      omega

/-- `P k` in the form `16 + k(k+1) = 2 m^2`. -/
theorem P_iff (k : ℕ) : OMA.S_oeis_a154141.P k ↔ ∃ m, 16 + k * (k + 1) = 2 * m ^ 2 := by
  have he : k * (k + 1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self k)
  unfold OMA.S_oeis_a154141.P
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩

theorem P_f (n : ℕ) : OMA.S_oeis_a154141.P (f n) :=
  (P_iff _).mpr ⟨(s n).2, (s_sol n).1⟩

theorem P_range (k : ℕ) (hk : OMA.S_oeis_a154141.P k) : ∃ n, f n = k := by
  obtain ⟨m, hm⟩ := (P_iff k).mp hk
  obtain ⟨n, hn⟩ := complete k m hm
  exact ⟨n, by simp [f, hn]⟩

theorem nth_eq (n : ℕ) : Nat.nth OMA.S_oeis_a154141.P n = f n := by
  have hinf : (Set.ofPred OMA.S_oeis_a154141.P).Infinite :=
    Set.infinite_of_injective_forall_mem f_strictMono.injective P_f
  have hS : ∀ j, j ∈ {n : ℕ | ∀ hf : (Set.ofPred OMA.S_oeis_a154141.P).Finite,
      n < hf.toFinset.card} := fun j hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hS n)).symm
  · intro k hk
    obtain ⟨j, hj⟩ := P_range k hk
    exact ⟨j, hS j, hj⟩
  · intro j _
    exact P_f j
  · exact f_strictMono.strictMonoOn _

theorem a_eq (j : ℕ) : OMA.S_oeis_a154141.a (j + 1) = f j := by
  rw [OMA.S_oeis_a154141.a, Nat.add_sub_cancel, nth_eq]

theorem f_rec (i : ℕ) : (f (i + 4) : ℤ) = 6 * f (i + 2) - f i + 2 := by
  have e1 : s (i + 4) = T (T (s i)) := rfl
  have e2 : s (i + 2) = T (s i) := rfl
  simp only [f, e1, e2, T]
  push_cast
  ring

theorem a_rec (j : ℕ) : (OMA.S_oeis_a154141.a (j + 6) : ℤ) = OMA.S_oeis_a154141.a (j + 5) +
    6 * OMA.S_oeis_a154141.a (j + 4) - 6 * OMA.S_oeis_a154141.a (j + 3) -
    OMA.S_oeis_a154141.a (j + 2) + OMA.S_oeis_a154141.a (j + 1) := by
  rw [show j + 6 = (j + 5) + 1 by omega, show j + 5 = (j + 4) + 1 by omega,
    show j + 4 = (j + 3) + 1 by omega, show j + 3 = (j + 2) + 1 by omega,
    show j + 2 = (j + 1) + 1 by omega]
  simp only [a_eq]
  have r1 := f_rec (j + 1)
  have r0 := f_rec j
  rw [show j + 1 + 4 = j + 5 by omega, show j + 1 + 2 = j + 3 by omega] at r1
  linarith

/-- The coefficient of `x^k` in `A * (c x^j)`. -/
theorem coeff_mul_CX (A : ℚ⟦X⟧) (c : ℚ) (j k : ℕ) :
    coeff k (A * (C c * X ^ j)) = if j ≤ k then c * coeff (k - j) A else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', mul_ite, mul_zero]

theorem gf1 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a154141.a n : ℚ)) *
      ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (1 + 6 * X + 3 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else
    (OMA.S_oeis_a154141.a n : ℚ)) with hA
  have hD : A * ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      A * (C (1 : ℚ) * X ^ 0) - A * (C (1 : ℚ) * X ^ 1) - A * (C (6 : ℚ) * X ^ 2) +
        A * (C (6 : ℚ) * X ^ 3) + A * (C (1 : ℚ) * X ^ 4) - A * (C (1 : ℚ) * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hN : (X : ℚ⟦X⟧) * (1 + 6 * X + 3 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4) =
      C (1 : ℚ) * X ^ 1 + C (6 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 - C (6 : ℚ) * X ^ 4 -
        C (2 : ℚ) * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_mul_CX, hA, coeff_mk, zero_le, if_true,
    Nat.sub_zero, one_mul]
  have h1 : (OMA.S_oeis_a154141.a 1 : ℚ) = 1 := by rw [a_eq 0]; rfl
  have h2 : (OMA.S_oeis_a154141.a 2 : ℚ) = 7 := by rw [a_eq 1]; rfl
  have h3 : (OMA.S_oeis_a154141.a 3 : ℚ) = 16 := by rw [a_eq 2]; rfl
  have h4 : (OMA.S_oeis_a154141.a 4 : ℚ) = 46 := by rw [a_eq 3]; rfl
  have h5 : (OMA.S_oeis_a154141.a 5 : ℚ) = 97 := by rw [a_eq 4]; rfl
  rcases k with _ | _ | _ | _ | _ | _ | j
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2, h3]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2, h3, h4]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2, h3, h4, h5]
    norm_num
  · simp only [show ¬ (j + 6 = 0) by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega,
      show ¬ (j + 6 = 3) by omega, show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega,
      if_true, if_false]
    have r := a_rec j
    have rq : (OMA.S_oeis_a154141.a (j + 6) : ℚ) = OMA.S_oeis_a154141.a (j + 5) +
        6 * OMA.S_oeis_a154141.a (j + 4) - 6 * OMA.S_oeis_a154141.a (j + 3) -
        OMA.S_oeis_a154141.a (j + 2) + OMA.S_oeis_a154141.a (j + 1) := by exact_mod_cast r
    rw [rq]
    ring

theorem gf2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a154141.a n : ℚ)) =
      C (1 / 2 : ℚ) * (4 + (X - 1)⁻¹ - 3 * (X ^ 2 + 2 * X - 1)⁻¹ +
        (6 + 15 * X) * (X ^ 2 - 2 * X - 1)⁻¹) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else
    (OMA.S_oeis_a154141.a n : ℚ)) with hA
  have hu : ((X : ℚ⟦X⟧) - 1) * (X - 1)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp)
  have hv : ((X : ℚ⟦X⟧) ^ 2 + 2 * X - 1) * (X ^ 2 + 2 * X - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hw : ((X : ℚ⟦X⟧) ^ 2 - 2 * X - 1) * (X ^ 2 - 2 * X - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hD : ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) : ℚ⟦X⟧) *
      ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hC : C (1 / 2 : ℚ) * (2 : ℚ⟦X⟧) = 1 := by
    rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  have hR : C (1 / 2 : ℚ) * (4 + (X - 1)⁻¹ - 3 * (X ^ 2 + 2 * X - 1)⁻¹ +
        (6 + 15 * X) * (X ^ 2 - 2 * X - 1)⁻¹) *
        ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      X * (1 + 6 * X + 3 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4) := by
    linear_combination (C (1 / 2 : ℚ) * (-((X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)))) * hu +
      (C (1 / 2 : ℚ) * (-3 * (1 - X) * (X ^ 2 - 2 * X - 1))) * hv +
      (C (1 / 2 : ℚ) * ((6 + 15 * X) * (1 - X) * (X ^ 2 + 2 * X - 1))) * hw +
      (X * (1 + 6 * X + 3 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4)) * hC
  have h1 := gf1
  rw [← hA] at h1
  calc A = A * (((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) : ℚ⟦X⟧) *
          ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1))⁻¹) := by rw [hD, mul_one]
    _ = _ := by rw [← mul_assoc, h1, ← hR, mul_assoc, hD, mul_one]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a154141.main := by
  refine ⟨fun n hn => ?_, OMA.Helpers.gf1, OMA.Helpers.gf2⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  rw [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
    show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
    show j + 6 - 5 = j + 1 by omega]
  exact OMA.Helpers.a_rec j
