import OMAStatements.S_oeis_a222139
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a222139 Finset

/-- A row of the array. -/
abbrev T := Fin 5 × Fin 5 × Fin 5

/-- Every row is admissible and every two consecutive rows fit, with natural-number indices. -/
def Chain {m : ℕ} (A : Fin m → T) : Prop :=
  (∀ (i : ℕ) (h : i < m), hrow (A ⟨i, h⟩)) ∧
    ∀ (i : ℕ) (h : i + 1 < m), ok (A ⟨i, by omega⟩) (A ⟨i + 1, h⟩)

theorem chain_iff {m : ℕ} (A : Fin m → T) :
    ((∀ i, hrow (A i)) ∧ (∀ i j : Fin m, j.val = i.val + 1 → ok (A i) (A j))) ↔ Chain A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i h => h1 _, fun i h => h2 _ _ rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h1 i.1 i.2, fun i j hij => ?_⟩
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only at hij
    subst hij
    exact h2 i hj

theorem chain_cons {m : ℕ} (x : T) (B : Fin (m + 1) → T) :
    Chain (Fin.cons x B : Fin (m + 2) → T) ↔ hrow x ∧ ok x (B 0) ∧ Chain B := by
  constructor
  · rintro ⟨h1, h2⟩
    have hx := h1 0 (by omega)
    have hxb := h2 0 (by omega)
    exact ⟨hx, hxb, fun i h => h1 (i + 1) (by omega), fun i h => h2 (i + 1) (by omega)⟩
  · rintro ⟨hx, hxb, h1, h2⟩
    refine ⟨fun i h => ?_, fun i h => ?_⟩
    · cases i with
      | zero => exact hx
      | succ i => exact h1 i (by omega)
    · cases i with
      | zero => exact hxb
      | succ i => exact h2 i (by omega)

/-- The number of ways to continue the first row `r` by `m` more rows. -/
noncomputable def K (m : ℕ) (r : T) : ℕ := by
  classical
  exact ∑ B : Fin m → T, if Chain (Fin.cons r B : Fin (m + 1) → T) then 1 else 0

theorem K_zero (r : T) : K 0 r = if hrow r then 1 else 0 := by
  classical
  unfold K
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, _⟩
    exact h1 0 (by omega)
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => by omega⟩
    obtain rfl : i = 0 := by omega
    exact h

theorem K_succ (m : ℕ) (r : T) :
    K (m + 1) r = ∑ s : T, if hrow r ∧ ok r s then K m s else 0 := by
  classical
  unfold K
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => T).symm _
    (fun p => if Chain (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → T) then 1 else 0)
    (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hv : hrow r ∧ ok r s
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chain_cons]
    simp only [Fin.cons_zero]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chain_cons]
    simp only [Fin.cons_zero]
    exact fun h => hv ⟨h.1, h.2.1⟩

theorem a_eq (m : ℕ) : a (m + 1) = ∑ r : T, if r.1 = 0 then K m r else 0 := by
  classical
  have h1 : a (m + 1) = ∑ A : Fin (m + 1) → T, if Chain A ∧ (A 0).1 = 0 then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [← chain_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3 0 rfl⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun i hi => ?_⟩
      have : i = 0 := Fin.ext hi
      subst this
      exact h3
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => T).symm _
    (fun p => if Chain (Fin.cons p.1 p.2 : Fin (m + 1) → T) ∧ p.1.1 = 0 then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r.1 = 0
  · rw [if_pos hr]
    unfold K
    exact Finset.sum_congr rfl fun B _ => if_congr (and_iff_left hr) rfl rfl
  · rw [if_neg hr]
    exact Finset.sum_eq_zero fun B _ => if_neg (fun h => hr h.2)

/-- The number of continuations of the row `r` by one row: 43 when `x(i,2) = x(i,0) + 3 mod 5`,
42 otherwise (for an admissible row). -/
def D (r : T) : ℕ := if hrow r then (if r.2.2.val = (r.1.val + 3) % 5 then 43 else 42) else 0

theorem chk1 : ∀ r : T,
    (∑ s : T, if hrow r ∧ ok r s then (if hrow s then 1 else 0) else 0) = D r := by
  decide +kernel

theorem chk2 : ∀ r : T,
    (∑ s : T, if hrow r ∧ ok r s then D s else 0) + 116 * (if hrow r then 1 else 0) =
      45 * D r := by
  decide +kernel

theorem K_one (r : T) : K 1 r = D r := by
  rw [K_succ]
  simp only [K_zero]
  exact chk1 r

theorem rec_K (m : ℕ) : ∀ r : T, K (m + 2) r + 116 * K m r = 45 * K (m + 1) r := by
  induction m with
  | zero =>
    intro r
    show K (1 + 1) r + 116 * K 0 r = 45 * K 1 r
    rw [K_succ 1 r]
    simp only [K_one]
    rw [K_zero]
    exact chk2 r
  | succ m ih =>
    intro r
    show K (m + 2 + 1) r + 116 * K (m + 1) r = 45 * K (m + 1 + 1) r
    rw [K_succ (m + 2), K_succ m, K_succ (m + 1), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · exact ih s
    · simp

theorem a_rec (m : ℕ) : a (m + 3) + 116 * a (m + 1) = 45 * a (m + 2) := by
  show a (m + 2 + 1) + 116 * a (m + 1) = 45 * a (m + 1 + 1)
  rw [a_eq (m + 2), a_eq m, a_eq (m + 1), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · exact rec_K m r
  · simp

theorem a_one : a 1 = 16 := by
  show a (0 + 1) = 16
  rw [a_eq 0]
  simp only [K_zero]
  decide +kernel

theorem a_two : a 2 = 676 := by
  show a (1 + 1) = 676
  rw [a_eq 1]
  simp only [K_one]
  decide +kernel

theorem a_recQ (m : ℕ) : (a (m + 3) : ℚ) = 45 * a (m + 2) - 116 * a (m + 1) := by
  have h : ((a (m + 3) + 116 * a (m + 1) : ℕ) : ℚ) = ((45 * a (m + 2) : ℕ) : ℚ) := by
    rw [a_rec m]
  push_cast at h
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 45 * X + 116 * X ^ 2) = 4 * X * (4 - 11 * X) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - 45 * X + 116 * X ^ 2) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 45 * (PowerSeries.mk F * X ^ 1) +
        C 116 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (4 * X * (4 - 11 * X) : ℚ⟦X⟧) = C 16 * X ^ 1 - C 44 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [hF, a_one, a_two]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show j + 3 - 0 = j + 3 by omega, show j + 3 - 1 = j + 2 by omega,
      show j + 3 - 2 = j + 1 by omega,
      show ¬ (j + 3 = 1) by omega, show ¬ (j + 3 = 2) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    rw [a_recQ j]
    ring

theorem P_pair (s : ℝ) (hs : s * s = 1561) (m : ℕ) :
    (a (m + 1) : ℝ) * (58 * s) =
        ((45 - s) / 2) ^ (m + 1) * (-433 + 11 * s) + ((45 + s) / 2) ^ (m + 1) * (433 + 11 * s) ∧
      (a (m + 2) : ℝ) * (58 * s) =
        ((45 - s) / 2) ^ (m + 2) * (-433 + 11 * s) + ((45 + s) / 2) ^ (m + 2) * (433 + 11 * s) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a_one]
      push_cast
      ring
    · rw [a_two]
      push_cast
      linear_combination (-(11 / 2) * s) * hs
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    have hrec : (a (m + 3) : ℝ) = 45 * a (m + 2) - 116 * a (m + 1) := by
      have h : ((a (m + 3) + 116 * a (m + 1) : ℕ) : ℝ) = ((45 * a (m + 2) : ℕ) : ℝ) := by
        rw [a_rec m]
      push_cast at h
      linarith
    show (a (m + 3) : ℝ) * (58 * s) =
        ((45 - s) / 2) ^ (m + 3) * (-433 + 11 * s) + ((45 + s) / 2) ^ (m + 3) * (433 + 11 * s)
    linear_combination (58 * s) * hrec + 45 * h1 - 116 * h0 -
      ((((45 - s) / 2) ^ (m + 1) * (-433 + 11 * s) + ((45 + s) / 2) ^ (m + 1) * (433 + 11 * s)) / 4) * hs

theorem closed_real (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) * ((45 - Real.sqrt 1561) ^ n * (-433 + 11 * Real.sqrt 1561) +
      (45 + Real.sqrt 1561) ^ n * (433 + 11 * Real.sqrt 1561))) / (29 * Real.sqrt 1561) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hs : Real.sqrt 1561 * Real.sqrt 1561 = 1561 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 1561 := Real.sqrt_pos.mpr (by norm_num)
  have hz : (2 : ℝ) ^ (-1 - ((m + 1 : ℕ) : ℤ)) = 2⁻¹ / 2 ^ (m + 1) := by
    rw [zpow_sub₀ two_ne_zero, zpow_neg_one, zpow_natCast]
  have hP := (P_pair (Real.sqrt 1561) hs m).1
  have e1 : (45 - Real.sqrt 1561) ^ (m + 1) = 2 ^ (m + 1) * ((45 - Real.sqrt 1561) / 2) ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have e2 : (45 + Real.sqrt 1561) ^ (m + 1) = 2 ^ (m + 1) * ((45 + Real.sqrt 1561) / 2) ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have h2 : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
  rw [hz, e1, e2, eq_div_iff (by positivity)]
  have hc : (2 : ℝ)⁻¹ / 2 ^ (m + 1) * (2 ^ (m + 1) * ((45 - Real.sqrt 1561) / 2) ^ (m + 1) *
      (-433 + 11 * Real.sqrt 1561) + 2 ^ (m + 1) * ((45 + Real.sqrt 1561) / 2) ^ (m + 1) *
      (433 + 11 * Real.sqrt 1561)) = (((45 - Real.sqrt 1561) / 2) ^ (m + 1) *
      (-433 + 11 * Real.sqrt 1561) + ((45 + Real.sqrt 1561) / 2) ^ (m + 1) *
      (433 + 11 * Real.sqrt 1561)) / 2 := by
    field_simp
  rw [hc, ← hP]
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a222139.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed_real⟩
