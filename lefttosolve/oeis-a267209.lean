import OMAStatements.S_oeis_a267209
import Mathlib

/-!
Proof of the two conjectures of OEIS A267209 (middle column of Rule 109).

Closed form of the automaton: at stage n, a cell at distance d from the origin is
* the background value (ON iff n is odd) when d > n,
* ON iff n is even when d = n, and ON when d + 1 = n,
* otherwise G (n mod 3) (d mod 12) for an explicit 3 x 12 table G.
The closed form is proved by induction on n (finitely many residue checks). Hence the middle
cell is ON except at the stages n >= 3 divisible by 3, so c(n) = c(n - 3) for n >= 4,
a(n) = 10 a(n - 1) + c(n) gives the recurrence, and the generating function follows by
comparing coefficients of A * (1 - 10 X - X^3 + 10 X^4).
-/

namespace OMA.Helpers

open OMA.S_oeis_a267209

/-- Rule 109 as a function of the three neighbourhood values. -/
def r109 (l c r : Bool) : Bool := Nat.testBit 109 (4 * l.toNat + 2 * c.toNat + r.toNat)

theorem r109_symm (l c r : Bool) : r109 l c r = r109 r c l := by
  cases l <;> cases c <;> cases r <;> decide

theorem r109_const (b : Bool) : r109 b b b = !b := by
  cases b <;> decide

/-- The periodic interior pattern: row `r` (the stage mod 3), column `s` (the distance mod 12). -/
def G (r s : ℕ) : Bool := Nat.testBit ([1404, 1989, 3159].getD r 0) s

/-- Closed form of stage `n` at distance `a` from the origin. -/
def Fa (n a : ℕ) : Bool :=
  if n < a then decide (n % 2 = 1)
  else if a = n then decide (n % 2 = 0)
  else if a + 1 = n then true
  else G (n % 3) (a % 12)

theorem Fa_out {n a : ℕ} (h : n < a) : Fa n a = decide (n % 2 = 1) := by
  unfold Fa; rw [if_pos h]

theorem Fa_edge {n a : ℕ} (h : a = n) : Fa n a = decide (n % 2 = 0) := by
  unfold Fa; rw [if_neg (by omega), if_pos h]

theorem Fa_edge1 {n a : ℕ} (h : a + 1 = n) : Fa n a = true := by
  unfold Fa; rw [if_neg (by omega), if_neg (by omega), if_pos h]

theorem Fa_in {n a : ℕ} (h : a + 2 ≤ n) : Fa n a = G (n % 3) (a % 12) := by
  unfold Fa; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem G_step : ∀ r < 3, ∀ s < 12,
    r109 (G r ((s + 11) % 12)) (G r s) (G r ((s + 1) % 12)) = G ((r + 1) % 3) s := by
  decide

theorem G_seam : ∀ r < 3, r109 (G r 1) (G r 0) (G r 1) = G ((r + 1) % 3) 0 := by
  decide

theorem G_near1 : ∀ m < 12,
    r109 (G (m % 3) ((m + 10) % 12)) true (decide (m % 2 = 0)) =
      G ((m + 1) % 3) ((m + 11) % 12) := by
  decide

theorem G_near2 : ∀ m < 12,
    r109 (G (m % 3) ((m + 9) % 12)) (G (m % 3) ((m + 10) % 12)) true =
      G ((m + 1) % 3) ((m + 10) % 12) := by
  decide

theorem parity_succ (n : ℕ) : decide ((n + 1) % 2 = 1) = !decide (n % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have : (n + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (n + 1) % 2 = 0 := by omega
    simp [h, this]

/-- One step of the closed form, away from the origin. -/
theorem Fa_step (n a : ℕ) (ha : 1 ≤ a) :
    r109 (Fa n (a - 1)) (Fa n a) (Fa n (a + 1)) = Fa (n + 1) a := by
  rcases (by omega : n + 1 < a ∨ a = n + 1 ∨ a = n ∨ a + 1 = n ∨ a + 2 = n ∨ a + 3 ≤ n) with
    h | h | h | h | h | h
  · rw [Fa_out (by omega : n < a - 1), Fa_out (by omega : n < a), Fa_out (by omega : n < a + 1),
      Fa_out (by omega : n + 1 < a), r109_const, parity_succ]
  · -- a = n + 1
    rw [Fa_edge (by omega : a - 1 = n), Fa_out (by omega : n < a), Fa_out (by omega : n < a + 1),
      Fa_edge (by omega : a = n + 1)]
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · have : (n + 1) % 2 = 1 := by omega
      simp only [hp, this]; decide
    · have : (n + 1) % 2 = 0 := by omega
      simp only [hp, this]; decide
  · -- a = n
    rw [Fa_edge1 (by omega : a - 1 + 1 = n), Fa_edge (by omega : a = n),
      Fa_out (by omega : n < a + 1), Fa_edge1 (by omega : a + 1 = n + 1)]
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · simp only [hp]; decide
    · simp only [hp]; decide
  · -- a + 1 = n
    rw [Fa_in (by omega : a - 1 + 2 ≤ n), Fa_edge1 (by omega : a + 1 = n),
      Fa_edge (by omega : a + 1 = n), Fa_in (by omega : a + 2 ≤ n + 1)]
    have key := G_near1 (n % 12) (Nat.mod_lt _ (by norm_num))
    have e1 : n % 12 % 3 = n % 3 := by omega
    have e2 : (n % 12 + 10) % 12 = (a - 1) % 12 := by omega
    have e3 : n % 12 % 2 = n % 2 := by omega
    have e4 : (n % 12 + 1) % 3 = (n + 1) % 3 := by omega
    have e5 : (n % 12 + 11) % 12 = a % 12 := by omega
    rw [e1, e2, e3, e4, e5] at key
    exact key
  · -- a + 2 = n
    rw [Fa_in (by omega : a - 1 + 2 ≤ n), Fa_in (by omega : a + 2 ≤ n),
      Fa_edge1 (by omega : a + 1 + 1 = n), Fa_in (by omega : a + 2 ≤ n + 1)]
    have key := G_near2 (n % 12) (Nat.mod_lt _ (by norm_num))
    have e1 : n % 12 % 3 = n % 3 := by omega
    have e2 : (n % 12 + 9) % 12 = (a - 1) % 12 := by omega
    have e3 : (n % 12 + 10) % 12 = a % 12 := by omega
    have e4 : (n % 12 + 1) % 3 = (n + 1) % 3 := by omega
    rw [e1, e2, e3, e4] at key
    exact key
  · -- interior
    rw [Fa_in (by omega : a - 1 + 2 ≤ n), Fa_in (by omega : a + 2 ≤ n),
      Fa_in (by omega : a + 1 + 2 ≤ n), Fa_in (by omega : a + 2 ≤ n + 1)]
    have key := G_step (n % 3) (Nat.mod_lt _ (by norm_num)) (a % 12) (Nat.mod_lt _ (by norm_num))
    have e1 : (a % 12 + 11) % 12 = (a - 1) % 12 := by omega
    have e2 : (a % 12 + 1) % 12 = (a + 1) % 12 := by omega
    have e3 : (n % 3 + 1) % 3 = (n + 1) % 3 := by omega
    rw [e1, e2, e3] at key
    exact key

/-- One step of the closed form at the origin. -/
theorem Fa_step_zero (n : ℕ) : r109 (Fa n 1) (Fa n 0) (Fa n 1) = Fa (n + 1) 0 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> decide
  · rw [Fa_in (by omega : 1 + 2 ≤ n), Fa_in (by omega : 0 + 2 ≤ n), Fa_in (by omega : 0 + 2 ≤ n + 1)]
    have key := G_seam (n % 3) (Nat.mod_lt _ (by norm_num))
    have e3 : (n % 3 + 1) % 3 = (n + 1) % 3 := by omega
    rw [e3] at key
    exact key

theorem state_eq (n : ℕ) (x : ℤ) : state 109 n x = Fa n x.natAbs := by
  induction n generalizing x with
  | zero =>
    show decide (x = 0) = Fa 0 x.natAbs
    rcases eq_or_ne x 0 with h | h
    · subst h; decide
    · rw [Fa_out (by omega)]; simp [h]
  | succ n ih =>
    show r109 (state 109 n (x - 1)) (state 109 n x) (state 109 n (x + 1)) = Fa (n + 1) x.natAbs
    rw [ih, ih, ih]
    rcases lt_trichotomy x 0 with h | h | h
    · rw [r109_symm, show (x + 1).natAbs = x.natAbs - 1 by omega,
        show (x - 1).natAbs = x.natAbs + 1 by omega]
      exact Fa_step n _ (by omega)
    · subst h
      exact Fa_step_zero n
    · rw [show (x + 1).natAbs = x.natAbs + 1 by omega, show (x - 1).natAbs = x.natAbs - 1 by omega]
      exact Fa_step n _ (by omega)

theorem c_zero : c 0 = 1 := by
  unfold c; rw [state_eq]; decide

theorem c_one : c 1 = 1 := by
  unfold c; rw [state_eq]; decide

theorem c_of_two_le (n : ℕ) (h : 2 ≤ n) : c n = if n % 3 = 0 then 0 else 1 := by
  unfold c
  rw [state_eq, Int.natAbs_zero, Fa_in (by omega : 0 + 2 ≤ n)]
  have hr : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = r at hr ⊢
  interval_cases r <;> decide

theorem c_periodic (n : ℕ) (h : 4 ≤ n) : c n = c (n - 3) := by
  rcases Nat.eq_or_lt_of_le h with h' | h'
  · subst h'; rw [c_of_two_le 4 (by norm_num)]; simp [c_one]
  · rw [c_of_two_le n (by omega), c_of_two_le (n - 3) (by omega)]
    have : (n - 3) % 3 = n % 3 := by omega
    rw [this]

theorem a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

theorem a_zero : a 0 = 1 := by
  unfold a; simp [c_zero]

theorem rec_int (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 10 * a (n - 1) + a (n - 3) - 10 * a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h1 := a_succ (m + 3)
  have h2 := a_succ m
  have hc := c_periodic (m + 4) (by omega)
  simp only [show m + 4 - 3 = m + 1 by omega] at hc
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega,
    show m + 4 - 4 = m by omega]
  rw [show m + 3 + 1 = m + 4 by omega] at h1
  rw [h1, hc, h2]
  push_cast
  ring

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267209.main := by
  refine ⟨OMA.Helpers.rec_int, ?_⟩
  have hD : PowerSeries.constantCoeff
      (((1 - X) * (1 - 10 * X) * (1 + X + X ^ 2)) : ℚ⟦X⟧) ≠ 0 := by
    simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  have h10 : (PowerSeries.C (10 : ℚ) : ℚ⟦X⟧) = 10 := map_ofNat _ 10
  have eD : OMA.S_oeis_a267209.A * ((1 - X) * (1 - 10 * X) * (1 + X + X ^ 2) : ℚ⟦X⟧)
      = OMA.S_oeis_a267209.A - PowerSeries.C (10 : ℚ) * (OMA.S_oeis_a267209.A * X ^ 1)
        - OMA.S_oeis_a267209.A * X ^ 3 + PowerSeries.C (10 : ℚ) * (OMA.S_oeis_a267209.A * X ^ 4) := by
    rw [h10]; ring
  have eN : (1 + X + X ^ 2 - X ^ 3 : ℚ⟦X⟧) = X ^ 0 + X ^ 1 + X ^ 2 - X ^ 3 := by ring
  rw [eD, eN]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_X_pow, OMA.S_oeis_a267209.A, PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | k
  · simp [OMA.Helpers.a_zero]
  · simp [OMA.Helpers.a_zero, OMA.Helpers.a_succ, OMA.Helpers.c_one]
    norm_num
  · simp [OMA.Helpers.a_zero, OMA.Helpers.a_succ, OMA.Helpers.c_one,
      OMA.Helpers.c_of_two_le]
    norm_num
  · simp [OMA.Helpers.a_zero, OMA.Helpers.a_succ, OMA.Helpers.c_one,
      OMA.Helpers.c_of_two_le]
    norm_num
  · have h := OMA.Helpers.rec_int (k + 1 + 1 + 1 + 1) (by omega)
    have hq : ((OMA.S_oeis_a267209.a (k + 1 + 1 + 1 + 1) : ℤ) : ℚ) =
        ((10 * (OMA.S_oeis_a267209.a (k + 1 + 1 + 1 + 1 - 1) : ℤ)
          + OMA.S_oeis_a267209.a (k + 1 + 1 + 1 + 1 - 3)
          - 10 * OMA.S_oeis_a267209.a (k + 1 + 1 + 1 + 1 - 4) : ℤ) : ℚ) := by rw [h]
    push_cast at hq
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    simp only [show k + 1 + 1 + 1 + 1 ≠ 0 by omega, show k + 1 + 1 + 1 + 1 ≠ 1 by omega,
      show k + 1 + 1 + 1 + 1 ≠ 2 by omega, show k + 1 + 1 + 1 + 1 ≠ 3 by omega, if_false]
    simp only [show k + 1 + 1 + 1 + 1 - 1 = k + 3 by omega, show k + 1 + 1 + 1 + 1 - 3 = k + 1 by omega,
      show k + 1 + 1 + 1 + 1 - 4 = k by omega]
    rw [hq]
    ring
