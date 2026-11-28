import OMAStatements.S_oeis_a267946
import Mathlib

/-!
Scanning a column from the top, the number of valid continuations of length `n` depends only on
the scan state. Before the first repeat it is `A n`; after a repeat it is `D n (p - r)`, where `p`
is the current element and `r` the value of the last repeat. These satisfy
`A (n+1) = 2 A n + D n 0`, `D (n+1) 0 = D n 1 + D n 2`, `D (n+1) 1 = D n 2 + 2 D n 0`,
`D (n+1) 2 = D n 0 + D n 1`, and `a (n+1) = A n`. Hence `D (n+2) 0 = D (n+1) 0 + 3 D n 0` and
`a (n+2) = a (n+1) + 3 a n + 2 ^ n`, which gives both the order-3 recurrence behind the generating
function and Barker's closed form (with `(1 -+ sqrt 13) ^ 2 = 2 (1 -+ sqrt 13) + 12`).
-/

namespace OMA.Helpers

open OMA.S_oeis_a267946 PowerSeries

/-- Number of continuations of length `n` from scan state `(r, p)`. -/
def N (r : Option (Fin 3)) (p : Fin 3) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 3 => ok r p (List.ofFn x) = true).card

theorem N_eq_sum (r : Option (Fin 3)) (p : Fin 3) (n : ℕ) :
    N r p n = ∑ x : Fin n → Fin 3, if ok r p (List.ofFn x) = true then 1 else 0 := by
  unfold N; rw [Finset.card_filter]

theorem N_succ (r : Option (Fin 3)) (p : Fin 3) (n : ℕ) :
    N r p (n + 1) = ∑ c : Fin 3, if c = p then
      (if (r.all fun v => decide (c = v + 1)) = true then N (some c) c n else 0)
      else N r c n := by
  rw [N_eq_sum, Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _
    (fun q => if ok r p (List.ofFn (Fin.cons q.1 q.2 : Fin (n + 1) → Fin 3)) = true then 1 else 0)
    (fun x => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, ok]
  by_cases hc : c = p
  · subst hc
    simp only [if_true]
    by_cases hr : (r.all fun v => decide (c = v + 1)) = true
    · rw [if_pos hr, N_eq_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [hr]
    · rw [if_neg hr]
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [hr]
  · simp only [hc, if_false]
    rw [N_eq_sum]

/-- Continuation counts after a repeat, indexed by `p - r`. -/
def D : ℕ → Fin 3 → ℕ
  | 0 => fun _ => 1
  | n + 1 => fun δ =>
    if δ = 0 then D n 1 + D n 2 else if δ = 1 then D n 2 + 2 * D n 0 else D n 0 + D n 1

/-- Continuation counts before the first repeat. -/
def A : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * A n + D n 0

theorem N_zero (r : Option (Fin 3)) (p : Fin 3) : N r p 0 = 1 := by
  rw [N_eq_sum]; simp [ok]

theorem N_eq : ∀ n : ℕ, ∀ r p, N r p n = (match r with | none => A n | some v => D n (p - v)) := by
  intro n
  induction n with
  | zero =>
    intro r p
    rcases r with _ | v <;> simp [N_zero, A, D]
  | succ n ih =>
    intro r p
    rw [N_succ]
    simp only [ih]
    rcases r with _ | v
    · fin_cases p <;> simp [Fin.sum_univ_three, A] <;> omega
    · have hm1 : (-1 : Fin 3) = 2 := rfl
      have hm2 : (-2 : Fin 3) = 1 := rfl
      fin_cases v <;> fin_cases p <;> simp [Fin.sum_univ_three, D, hm1, hm2] <;> omega

theorem a_succ (n : ℕ) : a (n + 1) = A n := by
  have h1 : a (n + 1) = ∑ x : Fin (n + 1) → Fin 3, if valid (List.ofFn x) = true then 1 else 0 := by
    unfold a; rw [Finset.card_filter]
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _
    (fun q => if valid (List.ofFn (Fin.cons q.1 q.2 : Fin (n + 1) → Fin 3)) = true then 1 else 0)
    (fun x => by simp), Fintype.sum_prod_type]
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, valid, Fin.sum_univ_three]
  have h0 := N_eq_sum none 0 n
  rw [N_eq n none 0] at h0
  simp only [Fin.isValue, decide_true, Bool.true_and, Fin.reduceEq, decide_false,
    Bool.false_and, Bool.false_eq_true, if_false, Finset.sum_const_zero, add_zero]
  exact h0.symm

theorem D_rec (n : ℕ) : D (n + 2) 0 = D (n + 1) 0 + 3 * D n 0 := by
  simp [D]; ring

theorem A_rec : ∀ n : ℕ, A (n + 2) = A (n + 1) + 3 * A n + 2 ^ (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : A (n + 3) = 2 * A (n + 2) + D (n + 2) 0 := rfl
    have e2 : A (n + 2) = 2 * A (n + 1) + D (n + 1) 0 := rfl
    have e3 : A (n + 1) = 2 * A n + D n 0 := rfl
    have e4 := D_rec n
    have e5 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
    show A (n + 3) = A (n + 2) + 3 * A (n + 1) + 2 ^ (n + 2)
    omega

theorem A_rec3 (j : ℕ) : (A (j + 3) : ℚ) = 3 * A (j + 2) + A (j + 1) - 6 * A j := by
  have h1 := A_rec (j + 1)
  have h2 := A_rec j
  have e5 : (2 : ℚ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  have h1' : (A (j + 3) : ℚ) = A (j + 2) + 3 * A (j + 1) + 2 ^ (j + 2) := by exact_mod_cast h1
  have h2' : (A (j + 2) : ℚ) = A (j + 1) + 3 * A j + 2 ^ (j + 1) := by exact_mod_cast h2
  linear_combination h1' - 2 * h2' + e5

theorem closed (m : ℕ) :
    39 * 2 ^ (m + 1) * ((A m : ℝ) + 2 ^ (m + 1)) =
      (26 - 7 * Real.sqrt 13) * (1 - Real.sqrt 13) ^ (m + 1) +
        (26 + 7 * Real.sqrt 13) * (1 + Real.sqrt 13) ^ (m + 1) := by
  have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hu : (1 - Real.sqrt 13) ^ 2 = 2 * (1 - Real.sqrt 13) + 12 := by linear_combination h13
  have hw : (1 + Real.sqrt 13) ^ 2 = 2 * (1 + Real.sqrt 13) + 12 := by linear_combination h13
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ =>
      simp only [A]; push_cast; linear_combination (-14) * h13
    | 1, _ =>
      simp only [A, D]; push_cast
      linear_combination (-80) * h13
    | k + 2, ih =>
      have i1 := ih (k + 1) (by omega)
      have i0 := ih k (by omega)
      have hr : (A (k + 2) : ℝ) = A (k + 1) + 3 * A k + 2 ^ (k + 1) := by exact_mod_cast A_rec k
      rw [hr]
      linear_combination 2 * i1 + 12 * i0 -
        (26 - 7 * Real.sqrt 13) * (1 - Real.sqrt 13) ^ (k + 1) * hu -
        (26 + 7 * Real.sqrt 13) * (1 + Real.sqrt 13) ^ (k + 1) * hw

end OMA.Helpers

open OMA.S_oeis_a267946 OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267946.main := by
  constructor
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F : ℕ → ℚ := fun n => if n = 0 then 0 else (a n : ℚ) with hF
    have hgf : gf = PowerSeries.mk F := rfl
    rw [hgf]
    have key : PowerSeries.mk F * ((1 - 2 * X) * (1 - X - 3 * X ^ 2)) =
        C 1 * (PowerSeries.mk F * X ^ 0) - C 3 * (PowerSeries.mk F * X ^ 1) -
          C 1 * (PowerSeries.mk F * X ^ 2) + C 6 * (PowerSeries.mk F * X ^ 3) := by
      simp only [map_one, map_ofNat]
      ring
    have hrhs : (X : ℚ⟦X⟧) * (1 - 2 * X ^ 2) = C 1 * X ^ 1 - C 2 * X ^ 3 := by
      simp only [map_one, map_ofNat]
      ring
    rw [key, hrhs]
    ext k
    simp only [map_sub, map_add, coeff_C_mul_X_pow]
    simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    by_cases hk : k < 4
    · interval_cases k <;> simp [hF, a_succ, A, D] <;> norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
      simp only [show 0 ≤ j + 4 by omega, show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega,
        show 3 ≤ j + 4 by omega,
        show j + 4 - 0 = j + 4 by omega, show j + 4 - 1 = j + 3 by omega,
        show j + 4 - 2 = j + 2 by omega, show j + 4 - 3 = j + 1 by omega,
        show ¬ (j + 4 = 1) by omega, show ¬ (j + 4 = 3) by omega,
        show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
        show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
        if_true, if_false, hF]
      rw [show j + 4 = (j + 3) + 1 by omega, show j + 3 = (j + 2) + 1 by omega,
        show j + 2 = (j + 1) + 1 by omega, a_succ, a_succ, a_succ, a_succ]
      linear_combination A_rec3 j
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [a_succ]
    have hc := closed m
    have h4 : (4 : ℝ) ^ (m + 1) = 2 ^ (m + 1) * 2 ^ (m + 1) := by rw [← mul_pow]; norm_num
    have key : -39 * (4 : ℝ) ^ (m + 1) + (26 - 7 * Real.sqrt 13) * (1 - Real.sqrt 13) ^ (m + 1) +
        (1 + Real.sqrt 13) ^ (m + 1) * (26 + 7 * Real.sqrt 13) = 39 * 2 ^ (m + 1) * A m := by
      rw [h4]; linear_combination (-1) * hc
    rw [key, zpow_neg, zpow_natCast]
    field_simp
