import OMAStatements.S_oeis_a154151
import Mathlib

/-!
P k holds iff 50 + k(k+1) = 2 m^2 for some m, i.e. (2k+1)^2 - 8 m^2 = -199. The solutions with
k >= 21 descend by (k, m) -> (3k + 1 - 4m, 3m - 2k - 1) to smaller solutions, and the solutions with
k < 21 are (0, 5) and (18, 14). Hence the solutions in increasing order are pr 0 = (0, 5),
pr 1 = (18, 14), pr (n + 2) = (3k + 4m + 1, 2k + 3m + 1) where pr n = (k, m), so a(n) = (pr (n - 1)).1,
which satisfies a(n + 4) = 6 a(n + 2) - a(n) + 2. The recurrence and both generating functions follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a154151

/-- The pairs (k, m) with 50 + k(k+1) = 2 m^2, in increasing order. -/
def pr : ℕ → ℕ × ℕ
  | 0 => (0, 5)
  | 1 => (18, 14)
  | n + 2 => (3 * (pr n).1 + 4 * (pr n).2 + 1, 2 * (pr n).1 + 3 * (pr n).2 + 1)

theorem pr_add_two (n : ℕ) :
    pr (n + 2) = (3 * (pr n).1 + 4 * (pr n).2 + 1, 2 * (pr n).1 + 3 * (pr n).2 + 1) := rfl

theorem pr_sol (n : ℕ) : 50 + (pr n).1 * ((pr n).1 + 1) = 2 * (pr n).2 ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | n + 2, ih =>
      have h := ih n (by omega)
      rw [pr_add_two]
      dsimp only
      zify at h ⊢
      linear_combination h

theorem pr_mono (n : ℕ) : (pr n).1 < (pr (n + 1)).1 ∧ (pr n).2 < (pr (n + 1)).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | n + 2, ih =>
      have h := ih n (by omega)
      rw [pr_add_two, show n + 2 + 1 = (n + 1) + 2 by omega, pr_add_two]
      dsimp only
      constructor <;> omega

theorem small_cases : ∀ k < 21, ∀ m < 16, 50 + k * (k + 1) = 2 * m ^ 2 →
    (k = 0 ∧ m = 5) ∨ (k = 18 ∧ m = 14) := by
  decide

theorem complete (k : ℕ) : ∀ m, 50 + k * (k + 1) = 2 * m ^ 2 → ∃ n, pr n = (k, m) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m h
    by_cases hk : k < 21
    · have hm : m < 16 := by nlinarith
      rcases small_cases k hk m hm h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · replace hk : 21 ≤ k := by omega
      have hA : 4 * m ≤ 3 * k + 1 := by nlinarith
      have hB : 2 * k + 1 ≤ 3 * m := by nlinarith
      have hC : 2 * k + 1 < 4 * m := by nlinarith
      obtain ⟨k', hk'⟩ : ∃ k', k' + 4 * m = 3 * k + 1 := ⟨3 * k + 1 - 4 * m, by omega⟩
      obtain ⟨m', hm'⟩ : ∃ m', m' + 2 * k + 1 = 3 * m := ⟨3 * m - (2 * k + 1), by omega⟩
      have hlt : k' < k := by omega
      have hs : 50 + k' * (k' + 1) = 2 * m' ^ 2 := by
        have e1 : (k' : ℤ) = 3 * k + 1 - 4 * m := by omega
        have e2 : (m' : ℤ) = 3 * m - 2 * k - 1 := by omega
        zify at h ⊢
        rw [e1, e2]
        linear_combination h
      obtain ⟨n, hn⟩ := ih k' hlt m' hs
      refine ⟨n + 2, ?_⟩
      rw [pr_add_two, hn]
      dsimp only
      ext <;> dsimp only <;> omega

theorem P_iff (k : ℕ) : P k ↔ ∃ m, 50 + k * (k + 1) = 2 * m ^ 2 := by
  have he : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  unfold P
  generalize k * (k + 1) = t at he ⊢
  obtain ⟨c, rfl⟩ := he
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩

theorem q_strictMono : StrictMono (fun n => (pr n).1) :=
  strictMono_nat_of_lt_succ (fun n => (pr_mono n).1)

theorem nth_eq (n : ℕ) : Nat.nth P n = (pr n).1 := by
  have hP : ∀ i, P ((fun n => (pr n).1) i) := fun i => (P_iff _).2 ⟨_, pr_sol i⟩
  have hinf : (Set.ofPred P).Infinite :=
    Set.infinite_of_injective_forall_mem q_strictMono.injective hP
  have h0 : ∀ k, P k → k ∈ Set.range (fun n => (pr n).1) := by
    intro k hk
    obtain ⟨m, hm⟩ := (P_iff k).1 hk
    obtain ⟨j, hj⟩ := complete k m hm
    exact ⟨j, by simp [hj]⟩
  have := Nat.nth_comp_of_strictMono (p := P) (n := n) q_strictMono h0
    (fun hf => absurd hf hinf)
  have h2 : Nat.nth (fun i => P (pr i).1) n = n := Nat.nth_of_forall (fun i _ => hP i)
  rw [h2] at this
  exact this.symm

theorem a_eq (n : ℕ) : a n = (pr (n - 1)).1 := by
  unfold a
  exact nth_eq _

theorem q_rec (j : ℕ) : (pr (j + 4)).1 + (pr j).1 = 6 * (pr (j + 2)).1 + 2 := by
  rw [show j + 4 = (j + 2) + 2 by omega, pr_add_two, pr_add_two]
  dsimp only
  omega

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  rw [a_eq _, a_eq _, a_eq _, a_eq _,
    a_eq _, a_eq _]
  simp only [show j + 6 - 1 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
    show j + 6 - 2 - 1 = j + 3 by omega, show j + 6 - 3 - 1 = j + 2 by omega,
    show j + 6 - 4 - 1 = j + 1 by omega, show j + 6 - 5 - 1 = j by omega]
  have h1 := q_rec (j + 1)
  have h2 := q_rec j
  simp only [show j + 1 + 4 = j + 5 by omega, show j + 1 + 2 = j + 3 by omega] at h1
  omega

open PowerSeries in
theorem A_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else ((pr (n - 1)).1 : ℚ)) := by
  congr 1
  funext n
  split_ifs <;> simp [a_eq]

theorem q_recQ (j : ℕ) : ((pr (j + 4)).1 : ℚ) = 6 * (pr (j + 2)).1 - (pr j).1 + 2 := by
  have := q_rec j
  have h : ((pr (j + 4)).1 : ℚ) + (pr j).1 = 6 * (pr (j + 2)).1 + 2 := by exact_mod_cast this
  linarith

open PowerSeries in
theorem gf1 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 2 + 2 * X - 1) * (X ^ 2 - 2 * X - 1)) =
        X ^ 2 * (-18 - 3 * X + 18 * X ^ 2 + X ^ 3) := by
  rw [A_eq]
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else ((pr (n - 1)).1 : ℚ)) with hA
  have hD : A * (((X : ℚ⟦X⟧) - 1) * (X ^ 2 + 2 * X - 1) * (X ^ 2 - 2 * X - 1)) =
      A * X ^ 5 - A * X ^ 4 - C (6 : ℚ) * (A * X ^ 3) + C (6 : ℚ) * (A * X ^ 2) + A * X ^ 1 - A := by
    simp only [map_ofNat]
    ring
  have hN : (X : ℚ⟦X⟧) ^ 2 * (-18 - 3 * X + 18 * X ^ 2 + X ^ 3) =
      C (-18 : ℚ) * X ^ 2 + C (-3 : ℚ) * X ^ 3 + C (18 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_neg, map_one]
    ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  have q0 : (pr 0).1 = 0 := rfl
  have q1 : (pr 1).1 = 18 := rfl
  have q2 : (pr 2).1 = 21 := rfl
  have q3 : (pr 3).1 = 111 := rfl
  have q4 : (pr 4).1 = 128 := rfl
  rcases k with _ | _ | _ | _ | _ | _ | j
  · simp
  · norm_num [q0]
  · norm_num [q0, q1]
  · norm_num [q0, q1, q2]
  · norm_num [q0, q1, q2, q3]
  · norm_num [q0, q1, q2, q3, q4]
  · simp only [show j + 1 + 1 + 1 + 1 + 1 + 1 = j + 6 by omega]
    simp only [show ¬ (j + 6 = 0) by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 5 = j + 1 by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      show j + 5 - 1 = j + 4 by omega, show j + 4 - 1 = j + 3 by omega,
      show j + 3 - 1 = j + 2 by omega, show j + 2 - 1 = j + 1 by omega,
      show j + 1 - 1 = j by omega, if_true, if_false]
    have h1 := q_recQ (j + 1)
    have h2 := q_recQ j
    simp only [show j + 1 + 4 = j + 5 by omega, show j + 1 + 2 = j + 3 by omega] at h1
    linarith

open PowerSeries in
theorem gf2 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (2 + (X - 1)⁻¹ + (10 + 29 * X) * (X ^ 2 - 2 * X - 1)⁻¹ +
        (-9 + 8 * X) * (X ^ 2 + 2 * X - 1)⁻¹) := by
  set u : ℚ⟦X⟧ := X - 1 with hu
  set v : ℚ⟦X⟧ := X ^ 2 - 2 * X - 1 with hv
  set w : ℚ⟦X⟧ := X ^ 2 + 2 * X - 1 with hw
  have iu : u⁻¹ * u = 1 := PowerSeries.inv_mul_cancel _ (by simp [hu])
  have iv : v⁻¹ * v = 1 := PowerSeries.inv_mul_cancel _ (by simp [hv])
  have iw : w⁻¹ * w = 1 := PowerSeries.inv_mul_cancel _ (by simp [hw])
  have hD0 : u * w * v ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    simp [hu, hv, hw] at this
  have h2 : C (1 / 2 : ℚ) * 2 = 1 := by
    have h2' : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := map_ofNat _ 2
    rw [← h2', ← map_mul]
    norm_num
  apply mul_right_cancel₀ hD0
  rw [gf1]
  have e : C (1 / 2 : ℚ) * (2 + u⁻¹ + (10 + 29 * X) * v⁻¹ + (-9 + 8 * X) * w⁻¹) * (u * w * v)
      = C (1 / 2 : ℚ) * (2 * (u * w * v) + (u⁻¹ * u) * w * v + (10 + 29 * X) * (v⁻¹ * v) * u * w
        + (-9 + 8 * X) * (w⁻¹ * w) * u * v) := by ring
  rw [e, iu, iv, iw, hu, hv, hw]
  linear_combination (-1 : ℚ⟦X⟧) * (X ^ 2 * (-18 - 3 * X + 18 * X ^ 2 + X ^ 3)) * h2

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a154151.main :=
  ⟨OMA.Helpers.recurrence, OMA.Helpers.gf1, OMA.Helpers.gf2⟩
