import OMAStatements.S_oeis_a234875
import Mathlib

/-!
Proof of the recurrence, generating function and closed forms for A234875.

Rows are pairs of entries; validity is a chain condition on consecutive rows, giving a transfer
recursion over the 25 row codes. Each per-state count satisfies
12 G m u = tA u + tB u (-1)^m + tC u 2^m + tD u (-2)^m for m at least 1 (eigenvector checks),
so 3 a n = 2 + 2 (-1)^n + 49 2^n + (-2)^n for n at least 1, from which everything follows.
-/

namespace OMA.Helpers

open OMA.S_oeis_a234875 Finset

/-- A row of an `(m + 1) X 2` array. -/
abbrev Row234875 := Fin 2 → Fin 5

/-- The block condition between a row `r` and the row `s` just below it. -/
def Compat234875 (r s : Row234875) : Prop := okBlock (r 0) (r 1) (s 0) (s 1)

instance (r s : Row234875) : Decidable (Compat234875 r s) := by
  unfold Compat234875; infer_instance

/-- Each row of `A` is compatible with the next one. -/
def Chain234875 {m : ℕ} (A : Fin m → Row234875) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < m), Compat234875 (A ⟨i, by omega⟩) (A ⟨i + 1, hi⟩)

theorem valid_iff_chain234875 {m : ℕ} (x : Fin (m + 1) → Fin 2 → Fin 5) :
    isValid m x ↔ Chain234875 x := by
  constructor
  · intro h i hi
    exact h ⟨i, by omega⟩ 0
  · intro h i j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact h i.val (by omega)

theorem chain234875_one (A : Fin 1 → Row234875) : Chain234875 A :=
  fun i hi => absurd hi (by omega)

theorem chain234875_cons {m : ℕ} (r : Row234875) (A : Fin (m + 1) → Row234875) :
    Chain234875 (Fin.cons r A : Fin (m + 2) → Row234875) ↔
      Compat234875 r (A ⟨0, by omega⟩) ∧ Chain234875 A := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The number of ways to continue the row `r` by `m` more rows into a chain. -/
noncomputable def N234875 (m : ℕ) (r : Row234875) : ℕ := by
  classical
  exact ∑ A : Fin m → Row234875, if Chain234875 (Fin.cons r A : Fin (m + 1) → Row234875) then 1 else 0

theorem N234875_zero (r : Row234875) : N234875 0 r = 1 := by
  classical
  unfold N234875
  rw [Fintype.sum_unique, if_pos (chain234875_one _)]

theorem N234875_succ (m : ℕ) (r : Row234875) :
    N234875 (m + 1) r = ∑ s : Row234875, if Compat234875 r s then N234875 m s else 0 := by
  classical
  unfold N234875
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row234875).symm _
    (fun p => if Chain234875 (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row234875)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : Compat234875 r s
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [chain234875_cons]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [chain234875_cons]
    exact fun h => hc h.1

theorem a234875_succ (m : ℕ) : (a (m + 1) : ℤ) = ∑ r : Row234875, (N234875 (m + 1) r : ℤ) := by
  classical
  have h1 : (Finset.univ.filter (isValid (m + 1))).card =
      ∑ A : Fin (m + 2) → Row234875, if Chain234875 A then 1 else 0 := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun g _ => if_congr (valid_iff_chain234875 g) rfl rfl
  have h2 : (∑ A : Fin (m + 2) → Row234875, if Chain234875 A then 1 else 0) =
      ∑ r : Row234875, N234875 (m + 1) r := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row234875).symm _
      (fun p => if Chain234875 (Fin.cons p.1 p.2 : Fin (m + 2) → Row234875) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  rw [a, h1, h2]
  push_cast
  rfl

/-- The row with code `u`: entries `u / 5` and `u % 5`. -/
def row234875 (u : Fin 25) : Row234875 :=
  ![⟨u.val / 5, by have := u.isLt; omega⟩, ⟨u.val % 5, by have := u.isLt; omega⟩]

theorem row234875_injective : Function.Injective row234875 := by
  decide +kernel

theorem row234875_bijective : Function.Bijective row234875 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row234875_injective, by simp⟩

/-- `Compat234875` on codes. -/
def ok234875 (u v : Fin 25) : Bool :=
  let a := u.val / 5
  let b := u.val % 5
  let c := v.val / 5
  let d := v.val % 5
  !(a == b) && !(c == d) && !(a == c) && !(b == d) && (a + d == b + c + 1 || b + c == a + d + 1)

theorem ok234875_iff : ∀ u v : Fin 25,
    Compat234875 (row234875 u) (row234875 v) ↔ ok234875 u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G234875 : ℕ → Fin 25 → ℕ
  | 0, _ => 1
  | m + 1, u => ∑ v : Fin 25, if ok234875 u v then G234875 m v else 0

theorem N_eq_G234875 (m : ℕ) : ∀ u : Fin 25, N234875 m (row234875 u) = G234875 m u := by
  induction m with
  | zero => intro u; rw [N234875_zero]; rfl
  | succ m ih =>
    intro u
    rw [N234875_succ, ← row234875_bijective.sum_comp]
    simp only [G234875]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok234875_iff u v) rfl rfl

theorem a_eq_G234875 (m : ℕ) : (a (m + 1) : ℤ) = ∑ u : Fin 25, (G234875 (m + 1) u : ℤ) := by
  rw [a234875_succ, ← row234875_bijective.sum_comp]
  exact Finset.sum_congr rfl fun u _ => by rw [N_eq_G234875]

/-- Coefficient tables: `12 G m u = tA u + tB u (-1)^m + tC u 2^m + tD u (-2)^m` for `m ≥ 1`. -/
def tA234875 : Fin 25 → ℤ :=
  ![0, -2, 2, 2, 0, -2, 0, 2, -4, 2, 2, 2, 0, 2, 2, 2, -4, 2, 0, -2, 0, 2, 2, -2, 0]

def tB234875 : Fin 25 → ℤ :=
  ![0, -2, -2, 2, 0, -2, 0, 2, 4, 2, -2, 2, 0, 2, -2, 2, 4, 2, 0, -2, 0, 2, -2, -2, 0]

def tC234875 : Fin 25 → ℤ :=
  ![0, 14, 14, 7, 0, 14, 0, 7, 14, 7, 14, 7, 0, 7, 14, 7, 14, 7, 0, 14, 0, 7, 14, 14, 0]

def tD234875 : Fin 25 → ℤ :=
  ![0, 2, -2, 1, 0, 2, 0, 1, -2, 1, -2, 1, 0, 1, -2, 1, -2, 1, 0, 2, 0, 1, -2, 2, 0]

theorem base234875 : ∀ u : Fin 25, 12 * (G234875 1 u : ℤ) =
    tA234875 u + tB234875 u * (-1) ^ 1 + tC234875 u * 2 ^ 1 + tD234875 u * (-2) ^ 1 := by
  decide +kernel

theorem step234875 : ∀ u : Fin 25,
    (∑ v : Fin 25, if ok234875 u v then tA234875 v else 0) = tA234875 u ∧
    (∑ v : Fin 25, if ok234875 u v then tB234875 v else 0) = -tB234875 u ∧
    (∑ v : Fin 25, if ok234875 u v then tC234875 v else 0) = 2 * tC234875 u ∧
    (∑ v : Fin 25, if ok234875 u v then tD234875 v else 0) = -2 * tD234875 u := by
  decide +kernel

theorem G234875_closed (m : ℕ) (hm : 1 ≤ m) : ∀ u : Fin 25, 12 * (G234875 m u : ℤ) =
    tA234875 u + tB234875 u * (-1) ^ m + tC234875 u * 2 ^ m + tD234875 u * (-2) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => exact base234875
  | succ m hm ih =>
    intro u
    have hsum : 12 * (G234875 (m + 1) u : ℤ) = ∑ v : Fin 25, if ok234875 u v then
        tA234875 v + tB234875 v * (-1) ^ m + tC234875 v * 2 ^ m + tD234875 v * (-2) ^ m
        else 0 := by
      rw [G234875]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih v
      · simp
    rw [hsum]
    have hP : ∀ v : Fin 25, (if ok234875 u v then
        tA234875 v + tB234875 v * (-1) ^ m + tC234875 v * 2 ^ m + tD234875 v * (-2) ^ m
        else 0) = (if ok234875 u v then tA234875 v else 0) +
          (if ok234875 u v then tB234875 v else 0) * (-1) ^ m +
          (if ok234875 u v then tC234875 v else 0) * 2 ^ m +
          (if ok234875 u v then tD234875 v else 0) * (-2) ^ m := by
      intro v
      split_ifs <;> simp
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h1, h2, h3, h4⟩ := step234875 u
    rw [h1, h2, h3, h4]
    ring

theorem sums234875 : (∑ u : Fin 25, tA234875 u) = 8 ∧ (∑ u : Fin 25, tB234875 u) = 8 ∧
    (∑ u : Fin 25, tC234875 u) = 196 ∧ (∑ u : Fin 25, tD234875 u) = 4 := by
  decide +kernel

theorem closed234875 (n : ℕ) (hn : 1 ≤ n) :
    3 * (a n : ℤ) = 2 + 2 * (-1) ^ n + 49 * 2 ^ n + (-2) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h12 : 12 * (a (m + 1) : ℤ) = ∑ u : Fin 25, 12 * (G234875 (m + 1) u : ℤ) := by
    rw [a_eq_G234875, Finset.mul_sum]
  simp only [G234875_closed (m + 1) (by omega)] at h12
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at h12
  obtain ⟨s1, s2, s3, s4⟩ := sums234875
  rw [s1, s2, s3, s4] at h12
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination h12

theorem a234875_zero : a 0 = 0 := rfl

theorem rec234875 (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h0 := closed234875 (k + 5) (by omega)
  have h2 := closed234875 (k + 3) (by omega)
  have h4 := closed234875 (k + 1) (by omega)
  rw [show k + 5 - 2 = k + 3 by omega, show k + 5 - 4 = k + 1 by omega]
  apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
  linear_combination h0 - 5 * h2 + 4 * h4

theorem closedQ234875 (n : ℕ) (hn : 1 ≤ n) :
    3 * (a n : ℚ) = 2 + 2 * (-1) ^ n + 49 * 2 ^ n + (-2) ^ n := by
  exact_mod_cast closed234875 n hn

open PowerSeries in
theorem gf_generic234875 (f : ℕ → ℚ) (h0 : f 0 = 0) (h1 : f 1 = 32) (h2 : f 2 = 68)
    (h3 : f 3 = 128) (h4 : f 4 = 268) (hr : ∀ j, f (j + 5) = 5 * f (j + 3) - 4 * f (j + 1)) :
    PowerSeries.mk f * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3) := by
  have key : PowerSeries.mk f * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X))
      = C 1 * (PowerSeries.mk f * X ^ 0) - C 5 * (PowerSeries.mk f * X ^ 2) +
        C 4 * (PowerSeries.mk f * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (4 : ℚ⟦X⟧) * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3) =
      C 32 * X ^ 1 + C 68 * X ^ 2 - C 32 * X ^ 3 - C 72 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [h0, h1, h2, h3, h4]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    have hrj := hr j
    simp only [show 0 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 2 = j + 3 by omega,
      show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, if_true, if_false]
    linarith

open PowerSeries in
theorem gf234875 : PowerSeries.mk (fun n => (a n : ℚ)) *
    ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3) := by
  refine gf_generic234875 (fun n => (a n : ℚ)) ?_ ?_ ?_ ?_ ?_ ?_
  · show ((a 0 : ℕ) : ℚ) = 0
    rw [a234875_zero, Nat.cast_zero]
  · have h := closedQ234875 1 le_rfl
    linear_combination h / 3
  · have h := closedQ234875 2 (by omega)
    linear_combination h / 3
  · have h := closedQ234875 3 (by omega)
    linear_combination h / 3
  · have h := closedQ234875 4 (by omega)
    linear_combination h / 3
  · intro j
    have hr := rec234875 (j + 5) (by omega)
    rw [show j + 5 - 2 = j + 3 by omega, show j + 5 - 4 = j + 1 by omega] at hr
    show ((a (j + 5) : ℕ) : ℚ) = 5 * ((a (j + 3) : ℕ) : ℚ) - 4 * ((a (j + 1) : ℕ) : ℚ)
    exact_mod_cast hr

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a234875.main := by
  refine ⟨OMA.Helpers.rec234875, OMA.Helpers.gf234875, ?_, ?_⟩
  · intro n hn he
    have h := OMA.Helpers.closedQ234875 n hn
    rw [he.neg_one_pow] at h
    linarith
  · intro n hn ho
    have h := OMA.Helpers.closedQ234875 n hn
    rw [ho.neg_one_pow] at h
    linarith
