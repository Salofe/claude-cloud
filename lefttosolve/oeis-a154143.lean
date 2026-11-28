import OMAStatements.S_oeis_a154143
import Mathlib

/-!
Proof of the conjectured recurrence and generating functions for A154143 (the k with
10 + k(k+1)/2 a perfect square).

`10 + k(k+1)/2 = m^2` iff `k(k+1) + 20 = 2 m^2` (`Q`). The map `(k, m) ↦ (3k + 4m + 1, 2k + 3m + 1)`
preserves `Q`, and every solution is reached from `(3, 4)` or `(5, 5)` (`descent`: for `m ≥ 10`
the inverse map gives a solution with smaller `m`; the cases `m ≤ 9` are checked directly).
Interleaving the two orbits gives a strictly increasing enumeration `s` of the solutions, so
`Nat.nth P = s`, and `s (n + 4) + s n = 6 s (n + 2) + 2`. The recurrence follows, the first
generating function by comparing coefficients, and the partial fraction form by multiplying out
the inverses of the (invertible) denominators.
-/

namespace OMA.Helpers

open OMA.S_oeis_a154143 PowerSeries

/-- One step `(k, m) ↦ (3k + 4m + 1, 2k + 3m + 1)` (multiplication by the unit `3 + 2√2`). -/
def st (p : ℕ × ℕ) : ℕ × ℕ := (3 * p.1 + 4 * p.2 + 1, 2 * p.1 + 3 * p.2 + 1)

/-- The solutions `(k, m)` starting from `(3, 4)`. -/
def A : ℕ → ℕ × ℕ
  | 0 => (3, 4)
  | j + 1 => st (A j)

/-- The solutions `(k, m)` starting from `(5, 5)`. -/
def B : ℕ → ℕ × ℕ
  | 0 => (5, 5)
  | j + 1 => st (B j)

/-- `k (k + 1) + 20 = 2 m ^ 2`, that is `10 + k (k + 1) / 2 = m ^ 2`. -/
def Q (p : ℕ × ℕ) : Prop := p.1 * p.1 + p.1 + 20 = 2 * (p.2 * p.2)

theorem Q_st {p : ℕ × ℕ} (h : Q p) : Q (st p) := by
  unfold Q st at *
  nlinarith [h]

theorem Q_A (j : ℕ) : Q (A j) := by
  induction j with
  | zero => unfold Q A; norm_num
  | succ j ih => exact Q_st ih

theorem Q_B (j : ℕ) : Q (B j) := by
  induction j with
  | zero => unfold Q B; norm_num
  | succ j ih => exact Q_st ih

theorem P_iff (k : ℕ) : P k ↔ ∃ m, Q (k, m) := by
  unfold P Q
  obtain ⟨t, ht⟩ := (Nat.even_mul_succ_self k).two_dvd
  have h1 : k * (k + 1) / 2 = t := by rw [ht]; omega
  have h2 : k * k + k = 2 * t := by rw [← ht]; ring
  simp only [h1, h2]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [sq] at hm; omega⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [sq]; omega⟩

theorem descent : ∀ m k : ℕ, Q (k, m) → ∃ j, (k, m) = A j ∨ (k, m) = B j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k h
  unfold Q at h
  simp only at h
  by_cases hm : m ≤ 9
  · have hk : k ≤ 13 := by nlinarith
    interval_cases m <;> interval_cases k <;>
      first | omega | exact ⟨0, Or.inl rfl⟩ | exact ⟨0, Or.inr rfl⟩
  · push Not at hm
    have h1 : 2 * k + 1 < 3 * m := by nlinarith
    have h2 : 2 * m < 2 * k + 1 := by nlinarith
    have h3 : 4 * m ≤ 3 * k + 1 := by nlinarith
    have hQ : Q (3 * k + 1 - 4 * m, 3 * m - (2 * k + 1)) := by
      unfold Q
      simp only
      have e1 : ((3 * k + 1 - 4 * m : ℕ) : ℤ) = 3 * k + 1 - 4 * m := by omega
      have e2 : ((3 * m - (2 * k + 1) : ℕ) : ℤ) = 3 * m - (2 * k + 1) := by omega
      have hz : (k : ℤ) * k + k + 20 = 2 * ((m : ℤ) * m) := by exact_mod_cast h
      zify
      rw [e1, e2]
      linear_combination hz
    obtain ⟨j, hj⟩ := ih (3 * m - (2 * k + 1)) (by omega) (3 * k + 1 - 4 * m) hQ
    refine ⟨j + 1, ?_⟩
    have hst : (k, m) = st (3 * k + 1 - 4 * m, 3 * m - (2 * k + 1)) := by
      unfold st
      ext <;> simp only <;> omega
    rcases hj with hj | hj
    · left
      rw [hst, hj]
      rfl
    · right
      rw [hst, hj]
      rfl

/-- The candidate enumeration: `s (2 j) = (A j).1`, `s (2 j + 1) = (B j).1`. -/
def s (n : ℕ) : ℕ := if n % 2 = 0 then (A (n / 2)).1 else (B (n / 2)).1

theorem s_even (j : ℕ) : s (2 * j) = (A j).1 := by
  unfold s
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]

theorem s_odd (j : ℕ) : s (2 * j + 1) = (B j).1 := by
  unfold s
  rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]

theorem s_mem (n : ℕ) : P (s n) := by
  rw [P_iff]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact ⟨(A j).2, by rw [s_even]; exact Q_A j⟩
  · exact ⟨(B j).2, by rw [s_odd]; exact Q_B j⟩

theorem mem_s (k : ℕ) (h : P k) : k ∈ Set.range s := by
  rw [P_iff] at h
  obtain ⟨m, hm⟩ := h
  obtain ⟨j, hj | hj⟩ := descent m k hm
  · exact ⟨2 * j, by rw [s_even, ← hj]⟩
  · exact ⟨2 * j + 1, by rw [s_odd, ← hj]⟩

theorem order (j : ℕ) : (A j).1 < (B j).1 ∧ (A j).2 < (B j).2 ∧
    (B j).1 < (A (j + 1)).1 ∧ (B j).2 < (A (j + 1)).2 := by
  induction j with
  | zero => simp only [A, B, st]; norm_num
  | succ j ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [A, B, st] at *
    omega

theorem s_strictMono : StrictMono s := strictMono_nat_of_lt_succ fun n => by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [s_even, s_odd]
    exact (order j).1
  · rw [s_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, s_even]
    exact (order j).2.2.1

theorem nth_eq (n : ℕ) : Nat.nth P n = s n := by
  have hinf : (Set.ofPred P).Infinite := by
    refine (Set.infinite_range_of_injective s_strictMono.injective).mono ?_
    rintro _ ⟨i, rfl⟩
    exact s_mem i
  have key := Nat.nth_comp_of_strictMono (p := P) (n := n) s_strictMono mem_s
    (fun hfi => absurd hfi hinf)
  have hall : (fun i => P (s i)) = fun _ => True := funext fun i => eq_true (s_mem i)
  rw [hall, Nat.nth_of_forall (fun _ _ => trivial)] at key
  exact key.symm

theorem s_rec (n : ℕ) : s (n + 4) + s n = 6 * s (n + 2) + 2 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * j + 4 = 2 * (j + 2) by ring, show 2 * j + 2 = 2 * (j + 1) by ring, s_even,
      s_even, s_even]
    simp only [A, st]
    omega
  · rw [show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by ring, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring,
      s_odd, s_odd, s_odd]
    simp only [B, st]
    omega

theorem a_eq (n : ℕ) : a n = s (n - 1) := by
  unfold a
  rw [nth_eq]

theorem a_vals : a 1 = 3 ∧ a 2 = 5 ∧ a 3 = 26 ∧ a 4 = 36 ∧ a 5 = 155 := by
  simp only [a_eq]
  decide

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  have e : ∀ i, a (i + 1) = s i := fun i => by rw [a_eq, Nat.add_sub_cancel]
  rw [show j + 6 - 1 = j + 4 + 1 by omega, show j + 6 - 2 = j + 3 + 1 by omega,
    show j + 6 - 3 = j + 2 + 1 by omega, show j + 6 - 4 = j + 1 + 1 by omega,
    show j + 6 - 5 = j + 1 by omega, show j + 6 = j + 5 + 1 by omega, e, e, e, e, e, e]
  have r1 := s_rec (j + 1)
  have r2 := s_rec j
  simp only [show j + 1 + 4 = j + 5 by omega, show j + 1 + 2 = j + 3 by omega] at r1
  omega

theorem gen_fun1 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (3 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 1 * (PowerSeries.mk F * X ^ 1) -
        C 6 * (PowerSeries.mk F * X ^ 2) + C 6 * (PowerSeries.mk F * X ^ 3) +
        C 1 * (PowerSeries.mk F * X ^ 4) - C 1 * (PowerSeries.mk F * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (3 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4) =
      C 3 * X ^ 1 + C 2 * X ^ 2 + C 3 * X ^ 3 - C 2 * X ^ 4 - C 4 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    have r := recurrence (j + 6) (by omega)
    simp only [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 5 = j + 1 by omega] at r
    have r' : ((a (j + 6) : ℤ) : ℚ) = ((a (j + 5) + 6 * a (j + 4) - 6 * a (j + 3) - a (j + 2) +
        a (j + 1) : ℤ) : ℚ) := by rw [r]
    push_cast at r'
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega, show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    linarith

theorem gen_fun2 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (8 + (-1 - 6 * X) * (X ^ 2 + 2 * X - 1)⁻¹ +
        (8 + 17 * X) * (X ^ 2 - 2 * X - 1)⁻¹ + (X - 1)⁻¹) := by
  set F := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hF
  set q1 : ℚ⟦X⟧ := X ^ 2 + 2 * X - 1 with hq1
  set q2 : ℚ⟦X⟧ := X ^ 2 - 2 * X - 1 with hq2
  set q3 : ℚ⟦X⟧ := X - 1 with hq3
  set D : ℚ⟦X⟧ := (1 - X) * q2 * q1 with hD
  have c1 : q1 * q1⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hq1])
  have c2 : q2 * q2⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hq2])
  have c3 : q3 * q3⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hq3])
  have cD : D * D⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hD, hq1, hq2])
  have hc : C (1 / 2 : ℚ) * 2 = (1 : ℚ⟦X⟧) := by
    rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  have h1 : F * D = X * (3 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4) := gen_fun1
  have h2 : C (1 / 2 : ℚ) * (8 + (-1 - 6 * X) * q1⁻¹ + (8 + 17 * X) * q2⁻¹ + q3⁻¹) * D =
      X * (3 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4) := by
    calc C (1 / 2 : ℚ) * (8 + (-1 - 6 * X) * q1⁻¹ + (8 + 17 * X) * q2⁻¹ + q3⁻¹) * D
        = C (1 / 2 : ℚ) * (8 * D + (-1 - 6 * X) * (1 - X) * q2 * (q1 * q1⁻¹) +
            (8 + 17 * X) * (1 - X) * q1 * (q2 * q2⁻¹) - q2 * q1 * (q3 * q3⁻¹)) := by
          rw [hD, hq3]
          ring
      _ = C (1 / 2 : ℚ) * 2 * (X * (3 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4)) := by
          rw [c1, c2, c3, hD, hq1, hq2]
          ring
      _ = X * (3 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4) := by
          rw [hc, one_mul]
  calc F = F * D * D⁻¹ := by rw [mul_assoc, cD, mul_one]
    _ = C (1 / 2 : ℚ) * (8 + (-1 - 6 * X) * q1⁻¹ + (8 + 17 * X) * q2⁻¹ + q3⁻¹) * D * D⁻¹ := by
        rw [h1, h2]
    _ = C (1 / 2 : ℚ) * (8 + (-1 - 6 * X) * q1⁻¹ + (8 + 17 * X) * q2⁻¹ + q3⁻¹) := by
        rw [mul_assoc _ D, cD, mul_one]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a154143.main :=
  ⟨OMA.Helpers.recurrence, OMA.Helpers.gen_fun1, OMA.Helpers.gen_fun2⟩
