import OMAStatements.S_oeis_a267905
import Mathlib

/-!
Proof of Barker's two conjectures for OEIS A267905.

The column scan is an automaton. Once the three values have all appeared (k = 3), the number of
ways to finish depends only on whether there was no repeat yet (sA), the last repeat equals the
current value (sB), or it differs from it (sC); with k = 2 the same counts appear. These satisfy
sA' = sB + 2 sA, sB' = sB + 2 sC, sC' = sB + sC, so sB and sC are the Pell companions Q(n+1) and
P(n+1), sA = Q(n+2) - 2^(n+1), and the k = 1 counts give 2 a(n) = Q(n+1) - 2^n + 1 for n >= 1.
The closed form and the generating function follow.
-/

namespace OMA.Helpers
open OMA.S_oeis_a267905

def N (P : List (Fin 3) → Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 3 => P (List.ofFn x) = true).card

theorem N_zero (P : List (Fin 3) → Bool) : N P 0 = if P [] = true then 1 else 0 := by
  unfold N
  rw [Finset.card_filter, Fintype.sum_unique]
  rfl

theorem N_succ (P : List (Fin 3) → Bool) (n : ℕ) :
    N P (n + 1) = ∑ c : Fin 3, N (fun l => P (c :: l)) n := by
  unfold N
  simp only [Finset.card_filter]
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _
    (fun q => if P (List.ofFn (Fin.cons q.1 q.2 : Fin (n + 1) → Fin 3)) = true then 1 else 0)
    (fun x => by simp), Fintype.sum_prod_type]
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

theorem N_false (n : ℕ) : N (fun _ => false) n = 0 := by
  unfold N
  simp

def ABC : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 1, 1)
  | n + 1 => ((ABC n).2.1 + 2 * (ABC n).1, (ABC n).2.1 + 2 * (ABC n).2.2,
      (ABC n).2.1 + (ABC n).2.2)

def sA (n : ℕ) : ℕ := (ABC n).1
def sB (n : ℕ) : ℕ := (ABC n).2.1
def sC (n : ℕ) : ℕ := (ABC n).2.2

theorem sA_succ (n : ℕ) : sA (n + 1) = sB n + 2 * sA n := rfl
theorem sB_succ (n : ℕ) : sB (n + 1) = sB n + 2 * sC n := rfl
theorem sC_succ (n : ℕ) : sC (n + 1) = sB n + sC n := rfl

def cf (r : Option (Fin 3)) (p : Fin 3) (n : ℕ) : ℕ :=
  match r with
  | none => sA n
  | some q => if q = p then sB n else sC n

theorem k3 (n : ℕ) : ∀ r p, N (ok r p 3) n = cf r p n := by
  induction n with
  | zero =>
    intro r p
    rcases r with _ | q <;> simp [N_zero, ok, cf, sA, sB, sC, ABC]
  | succ n ih =>
    intro r p
    rw [N_succ, Fin.sum_univ_three]
    rcases r with _ | q <;> fin_cases p <;> (try fin_cases q) <;>
      simp [ok, ih, cf, N_false, sA_succ, sB_succ, sC_succ] <;> ring


theorem k2 (n : ℕ) : ∀ r p, p.val ≤ 1 → (∀ q, r = some q → q.val ≤ 1) →
    N (ok r p 2) n = cf r p n := by
  induction n with
  | zero =>
    intro r p _ _
    rcases r with _ | q <;> simp [N_zero, ok, cf, sA, sB, sC, ABC]
  | succ n ih =>
    intro r p hp hr
    rw [N_succ, Fin.sum_univ_three]
    rcases r with _ | q
    · fin_cases p
      · simp [ok, ih, k3, cf, N_false, sA_succ, sB_succ, sC_succ]; ring
      · simp [ok, ih, k3, cf, N_false, sA_succ, sB_succ, sC_succ]; ring
      · simp at hp
    · have hq := hr q rfl
      fin_cases p <;> fin_cases q <;> simp at hp hq <;>
        simp [ok, ih, k3, cf, N_false, sA_succ, sB_succ, sC_succ] <;> ring

def sH : ℕ → ℕ
  | 0 => 1
  | n + 1 => sH n + sC n

theorem k1H (n : ℕ) : N (ok (some 0) 0 1) n = sH n := by
  induction n with
  | zero => simp [N_zero, ok, sH]
  | succ n ih =>
    rw [N_succ, Fin.sum_univ_three]
    simp [ok, ih, k2, cf, N_false, sH]

theorem k1G (n : ℕ) : N (ok none 0 1) (n + 1) = sH n + sA n := by
  rw [N_succ, Fin.sum_univ_three]
  simp [ok, k1H, k2, cf, N_false]

theorem a_succ (n : ℕ) : a (n + 1) = N (ok none 0 1) n := by
  show N valid (n + 1) = _
  rw [N_succ, Fin.sum_univ_three]
  simp [valid, N_false]

def pq : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n + 1 => ((pq n).1 + (pq n).2, (pq n).2 + 2 * (pq n).1)

def Pn (n : ℕ) : ℤ := (pq n).1
def Qn (n : ℕ) : ℤ := (pq n).2

theorem Pn_succ (n : ℕ) : Pn (n + 1) = Pn n + Qn n := rfl
theorem Qn_succ (n : ℕ) : Qn (n + 1) = Qn n + 2 * Pn n := rfl

theorem Qn_rec (n : ℕ) : Qn (n + 2) = 2 * Qn (n + 1) + Qn n := by
  rw [Qn_succ (n + 1), Pn_succ, Qn_succ n]
  ring

theorem BC_cf (n : ℕ) : (sB n : ℤ) = Qn (n + 1) ∧ (sC n : ℤ) = Pn (n + 1) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [sB_succ, sC_succ, Qn_succ (n + 1), Pn_succ (n + 1)]
    push_cast
    rw [ih.1, ih.2]
    constructor <;> ring

theorem A_cf (n : ℕ) : (sA n : ℤ) = Qn (n + 2) - 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sA_succ]
    push_cast
    rw [ih, (BC_cf n).1, Qn_rec (n + 1)]
    ring

theorem H_cf (n : ℕ) : 2 * (sH n : ℤ) = Qn (n + 1) + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sH]
    push_cast
    rw [mul_add, ih, (BC_cf n).2, Qn_succ (n + 1)]
    ring

theorem a_cf (n : ℕ) (hn : 1 ≤ n) : 2 * (a n : ℤ) = Qn (n + 1) - 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · rw [a_succ]
    simp [N_succ, N_zero, ok, N_false]
    rfl
  · rw [a_succ, k1G]
    push_cast
    rw [mul_add, H_cf, A_cf, Qn_rec (m + 1)]
    ring


theorem Qn_real (m : ℕ) : (Qn m : ℝ) = ((1 - Real.sqrt 2) ^ m + (1 + Real.sqrt 2) ^ m) / 2 ∧
    (Qn (m + 1) : ℝ) = ((1 - Real.sqrt 2) ^ (m + 1) + (1 + Real.sqrt 2) ^ (m + 1)) / 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · norm_num [Qn, pq]
    · norm_num [Qn, pq]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have h := Qn_rec m
    have h' : (Qn (m + 2) : ℝ) = 2 * (Qn (m + 1) : ℝ) + (Qn m : ℝ) := by exact_mod_cast h
    rw [h', ih.1, ih.2]
    linear_combination (-((1 - Real.sqrt 2) ^ m + (1 + Real.sqrt 2) ^ m) / 2) * hs

theorem a_real (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) =
    ((1 - Real.sqrt 2) ^ (1 + n) + (1 + Real.sqrt 2) ^ (1 + n) - 2 * (2 ^ n - 1)) / 4 := by
  have h := a_cf n hn
  have h' : 2 * (a n : ℝ) = (Qn (n + 1) : ℝ) - 2 ^ n + 1 := by exact_mod_cast h
  rw [add_comm 1 n]
  rw [(Qn_real (n + 1)).1] at h'
  linear_combination h' / 2

theorem a_rat (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((Qn (n + 1) : ℚ) - 2 ^ n + 1) / 2 := by
  have h := a_cf n hn
  have h' : 2 * (a n : ℚ) = (Qn (n + 1) : ℚ) - 2 ^ n + 1 := by exact_mod_cast h
  linear_combination h' / 2

theorem a_one : (a 1 : ℚ) = 1 := by
  rw [a_rat 1 le_rfl, show Qn 2 = 3 from rfl]; norm_num
theorem a_two : (a 2 : ℚ) = 2 := by
  rw [a_rat 2 (by norm_num), show Qn 3 = 7 from rfl]; norm_num
theorem a_three : (a 3 : ℚ) = 5 := by
  rw [a_rat 3 (by norm_num), show Qn 4 = 17 from rfl]; norm_num
theorem a_four : (a 4 : ℚ) = 13 := by
  rw [a_rat 4 (by norm_num), show Qn 5 = 41 from rfl]; norm_num

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      X * (1 - 3 * X + 2 * X ^ 2 + X ^ 3) * ((1 - X) * (1 - 2 * X) * (1 - 2 * X - X ^ 2))⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hlhs : A * ((1 - X) * (1 - 2 * X) * (1 - 2 * X - X ^ 2)) =
      A - C (5 : ℚ) * (A * X ^ 1) + C (7 : ℚ) * (A * X ^ 2) - C (1 : ℚ) * (A * X ^ 3) -
        C (2 : ℚ) * (A * X ^ 4) := by
    simp only [map_ofNat, map_one]
    ring
  have hrhs : (X * (1 - 3 * X + 2 * X ^ 2 + X ^ 3) : ℚ⟦X⟧) =
      C (1 : ℚ) * X ^ 1 - C (3 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hlhs, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k <;> norm_num [a_one, a_two, a_three, a_four]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show ¬ (j + 5 = 0) by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false]
    rw [a_rat (j + 5) (by omega), a_rat (j + 4) (by omega), a_rat (j + 3) (by omega),
      a_rat (j + 2) (by omega), a_rat (j + 1) (by omega)]
    have r4 : (Qn (j + 6) : ℚ) = 2 * Qn (j + 5) + Qn (j + 4) := by exact_mod_cast Qn_rec (j + 4)
    have r3 : (Qn (j + 5) : ℚ) = 2 * Qn (j + 4) + Qn (j + 3) := by exact_mod_cast Qn_rec (j + 3)
    have r2 : (Qn (j + 4) : ℚ) = 2 * Qn (j + 3) + Qn (j + 2) := by exact_mod_cast Qn_rec (j + 2)
    linear_combination (1 / 2 : ℚ) * r4 - (3 / 2 : ℚ) * r3 + r2

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a267905.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.a_real⟩
