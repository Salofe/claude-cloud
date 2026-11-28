import OMAStatements.S_oeis_a208138
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a208138

/-- The number of descending chains of length `h` starting below `r`. -/
def T (rs : List Nat) (h r : Nat) : Int := ((tails rs h r).length : Int)

theorem T_zero (rs : List Nat) (r : Nat) : T rs 0 r = 1 := by
  simp [T, tails]

theorem T_succ (rs : List Nat) (h r : Nat) :
    T rs (h + 1) r = ((below rs r).map (T rs h)).sum := by
  unfold T
  simp only [tails, List.length_flatMap, List.length_map]
  push_cast
  rw [List.map_map]
  rfl

theorem mem_below {rs : List Nat} {r s : Nat} (h : s ∈ below rs r) : s ∈ rs :=
  (List.mem_filter.mp h).1

/-- The fifth finite difference. -/
def D (rs : List Nat) (h r : Nat) : Int :=
  T rs (h + 5) r - 5 * T rs (h + 4) r + 10 * T rs (h + 3) r - 10 * T rs (h + 2) r +
    5 * T rs (h + 1) r - T rs h r

theorem sum_D (rs : List Nat) (h : Nat) (l : List Nat) :
    (l.map (D rs h)).sum = (l.map (T rs (h + 5))).sum - 5 * (l.map (T rs (h + 4))).sum +
      10 * (l.map (T rs (h + 3))).sum - 10 * (l.map (T rs (h + 2))).sum +
      5 * (l.map (T rs (h + 1))).sum - (l.map (T rs h)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    unfold D
    ring

theorem D_succ (rs : List Nat) (h r : Nat) :
    D rs (h + 1) r = ((below rs r).map (D rs h)).sum := by
  have e : ∀ k, T rs (h + 1 + k) r = ((below rs r).map (T rs (h + k))).sum := fun k => by
    rw [show h + 1 + k = (h + k) + 1 by omega, T_succ]
  rw [sum_D]
  unfold D
  rw [e 5, e 4, e 3, e 2, e 1, T_succ rs h r]

theorem D_vanish (rs : List Nat) (h0 : ∀ s ∈ rs, D rs 0 s = 0) :
    ∀ h, ∀ s ∈ rs, D rs h s = 0 := by
  intro h
  induction h with
  | zero => exact h0
  | succ h ih =>
    intro s _
    rw [D_succ]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ih y (mem_below hy)

theorem D_vanish_all (rs : List Nat) (h0 : ∀ s ∈ rs, D rs 0 s = 0) (h : Nat) (r : Nat) :
    D rs (h + 1) r = 0 := by
  rw [D_succ]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact D_vanish rs h0 h y (mem_below hy)

theorem gridCount_succ (w p q h : Nat) :
    gridCount w p q (h + 1) = ((rows w p q).length : Int) * T (rows w p q) h (2 ^ w - 1) := by
  simp only [gridCount, T, List.length_flatMap, List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]
  push_cast
  ring

theorem h0 : ∀ s ∈ rows 4 1 3, D (rows 4 1 3) 0 s = 0 := by decide +kernel

theorem htop : D (rows 4 1 3) 0 (2 ^ 4 - 1) = 0 := by decide +kernel

theorem hlen : (rows 4 1 3).length = 9 := by decide +kernel

theorem Dtop (h : Nat) : D (rows 4 1 3) h (2 ^ 4 - 1) = 0 := by
  cases h with
  | zero => exact htop
  | succ h => exact D_vanish_all _ h0 h _

theorem rec5 (n : Nat) : a (n + 6) = 5 * a (n + 5) - 10 * a (n + 4) + 10 * a (n + 3) -
    5 * a (n + 2) + a (n + 1) := by
  have := Dtop n
  unfold D at this
  simp only [a, gridCount_succ, hlen]
  push_cast
  linear_combination 9 * this

theorem small : a 0 = 0 ∧ a 1 = 9 ∧ a 2 = 81 ∧ a 3 = 324 ∧ a 4 = 900 ∧ a 5 = 2025 := by
  decide +kernel

theorem closed (n : Nat) : 4 * a n = 9 * (n : Int) ^ 2 * (1 + (n : Int)) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := small
    rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with hn | hn
    · interval_cases n <;> simp [s0, s1, s2, s3, s4, s5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [rec5]
      have e5 := ih (m + 5) (by omega)
      have e4 := ih (m + 4) (by omega)
      have e3 := ih (m + 3) (by omega)
      have e2 := ih (m + 2) (by omega)
      have e1 := ih (m + 1) (by omega)
      push_cast at e5 e4 e3 e2 e1 ⊢
      linear_combination 5 * e5 - 10 * e4 + 10 * e3 - 5 * e2 + e1

open PowerSeries in
theorem gen_fun : PowerSeries.mk a * (1 - PowerSeries.X) ^ 5 =
      9 * PowerSeries.X * (1 + 4 * PowerSeries.X + PowerSeries.X ^ 2) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := small
  have key : PowerSeries.mk a * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk a * X ^ 0) - C 5 * (PowerSeries.mk a * X ^ 1) +
        C 10 * (PowerSeries.mk a * X ^ 2) - C 10 * (PowerSeries.mk a * X ^ 3) +
        C 5 * (PowerSeries.mk a * X ^ 4) - C 1 * (PowerSeries.mk a * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (9 : PowerSeries Int) * X * (1 + 4 * X + X ^ 2) =
      C 9 * X ^ 1 + C 36 * X ^ 2 + C 9 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> simp [s0, s1, s2, s3, s4, s5]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega,
      show ¬ (j + 6 = 3) by omega, if_true, if_false, rec5]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a208138.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed⟩
