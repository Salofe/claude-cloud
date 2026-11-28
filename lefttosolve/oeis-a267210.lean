import OMAStatements.S_oeis_a267210
import Mathlib

/-!
Proof of the two conjectures of OEIS A267210 (middle column of Rule 109 from a single ON cell).

Closed form: at time n the cell at distance m from the origin is n mod 2 outside the light cone
(n < m), and inside it depends only on d = n - m and m mod 4: for m = 0 mod 4 it is OFF iff
d >= 3 and 3 divides d; for m = 1 mod 4 it is ON iff d = 1 mod 3; for m = 2 mod 4 it is ON; for
m = 3 mod 4 it is ON iff d = 1 or (d >= 3 and 3 divides d). The step is checked on residues.
Hence the middle cell c(n) is 0 iff n >= 3 and 3 divides n, a(n+1) = 2 a(n) + c(n+1), and
c(n+4) = c(n+1) gives the recurrence and the generating function.
-/

namespace OMA.Helpers

open OMA.S_oeis_a267210 PowerSeries

/-- Inside the light cone: the value of the cell at distance m from the origin at time m + d
depends on d and on m mod 4 (k = m mod 4). -/
def a267210_H (d k : ℕ) : Bool :=
  match k with
  | 0 => !(decide (3 ≤ d) && decide (d % 3 = 0))
  | 1 => decide (d % 3 = 1)
  | 2 => true
  | _ => decide (d = 1) || (decide (3 ≤ d) && decide (d % 3 = 0))

/-- Closed form of Rule 109 from a single ON cell at time n and distance m from the origin;
outside the light cone the background alternates with the parity of n. -/
def a267210_F (n m : ℕ) : Bool :=
  if n < m then n % 2 == 1 else a267210_H (n - m) (m % 4)

theorem a267210_H_period (d k : ℕ) (hd : 3 ≤ d) : a267210_H d k = a267210_H (3 + d % 3) k := by
  have h1 : (3 + d % 3) % 3 = d % 3 := by omega
  have h2 : 3 ≤ 3 + d % 3 := by omega
  have h3 : d ≠ 1 := by omega
  have h4 : 3 + d % 3 ≠ 1 := by omega
  rcases k with _ | _ | _ | k <;> simp [a267210_H, h1, hd, h3, h4]

/-- The generic interior step. -/
theorem a267210_interior (e k : ℕ) (hk : k < 4) :
    Nat.testBit 109 (4 * (a267210_H (e + 2) k).toNat + 2 * (a267210_H (e + 1) ((k + 1) % 4)).toNat
      + (a267210_H e ((k + 2) % 4)).toNat) = a267210_H (e + 2) ((k + 1) % 4) := by
  rcases Nat.lt_or_ge e 3 with he | he
  · interval_cases e <;> interval_cases k <;> decide
  · rw [a267210_H_period e _ he, a267210_H_period (e + 1) _ (by omega),
      a267210_H_period (e + 2) k (by omega), a267210_H_period (e + 2) ((k + 1) % 4) (by omega)]
    have h1 : (e + 1) % 3 = (e % 3 + 1) % 3 := by omega
    have h2 : (e + 2) % 3 = (e % 3 + 2) % 3 := by omega
    rw [h1, h2]
    have hr : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
    generalize e % 3 = r at hr ⊢
    interval_cases r <;> interval_cases k <;> decide


theorem a267210_F_out (n m : ℕ) (h : n < m) : a267210_F n m = (n % 2 == 1) := by
  rw [a267210_F, if_pos h]

theorem a267210_F_in (n m : ℕ) (h : m ≤ n) : a267210_F n m = a267210_H (n - m) (m % 4) := by
  rw [a267210_F, if_neg (by omega)]

/-- The step at distance m + 1 from the origin (cells m, m + 1, m + 2 at time n). -/
theorem a267210_core (n m : ℕ) :
    Nat.testBit 109 (4 * (a267210_F n m).toNat + 2 * (a267210_F n (m + 1)).toNat
      + (a267210_F n (m + 2)).toNat) = a267210_F (n + 1) (m + 1) := by
  rcases Nat.lt_or_ge n m with h | h
  · rw [a267210_F_out n m h, a267210_F_out n (m + 1) (by omega), a267210_F_out n (m + 2) (by omega),
      a267210_F_out (n + 1) (m + 1) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · have h3 : (n + 1) % 2 = 1 := by omega
      rw [h2, h3]; decide
    · have h3 : (n + 1) % 2 = 0 := by omega
      rw [h2, h3]; decide
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h
      rw [a267210_F_in m m le_rfl, a267210_F_out m (m + 1) (by omega),
        a267210_F_out m (m + 2) (by omega), a267210_F_in (m + 1) (m + 1) le_rfl,
        Nat.sub_self, Nat.sub_self]
      have h1 : m % 2 = m % 4 % 2 := by omega
      have h2 : (m + 1) % 4 = (m % 4 + 1) % 4 := by omega
      have hk : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [h1, h2]
      generalize m % 4 = k at hk ⊢
      interval_cases k <;> decide
    · obtain ⟨e, rfl⟩ : ∃ e, n = m + 1 + e := ⟨n - m - 1, by omega⟩
      have hk : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have h1 : (m + 1) % 4 = (m % 4 + 1) % 4 := by omega
      rw [a267210_F_in (m + 1 + e) m (by omega), a267210_F_in (m + 1 + e) (m + 1) (by omega),
        a267210_F_in (m + 1 + e + 1) (m + 1) (by omega)]
      have e1 : m + 1 + e - m = e + 1 := by omega
      have e2 : m + 1 + e - (m + 1) = e := by omega
      have e3 : m + 1 + e + 1 - (m + 1) = e + 1 := by omega
      rw [e1, e2, e3, h1]
      rcases e with _ | e
      · rw [a267210_F_out (m + 1 + 0) (m + 2) (by omega)]
        have h3 : (m + 1 + 0) % 2 = (m % 4 + 1) % 2 := by omega
        rw [h3]
        generalize m % 4 = k at hk ⊢
        interval_cases k <;> decide
      · rw [a267210_F_in (m + 1 + (e + 1)) (m + 2) (by omega)]
        have e4 : m + 1 + (e + 1) - (m + 2) = e := by omega
        have h4 : (m + 2) % 4 = (m % 4 + 2) % 4 := by omega
        rw [e4, h4]
        exact a267210_interior e (m % 4) hk

/-- The step at the origin (cells -1, 0, 1 at time n). -/
theorem a267210_origin (n : ℕ) :
    Nat.testBit 109 (4 * (a267210_F n 1).toNat + 2 * (a267210_F n 0).toNat
      + (a267210_F n 1).toNat) = a267210_F (n + 1) 0 := by
  rcases n with _ | e
  · decide
  · rw [a267210_F_in (e + 1) 1 (by omega), a267210_F_in (e + 1) 0 (by omega),
      a267210_F_in (e + 1 + 1) 0 (by omega)]
    have e1 : e + 1 - 1 = e := by omega
    rw [e1, Nat.sub_zero, Nat.sub_zero]
    rcases Nat.lt_or_ge e 3 with he | he
    · interval_cases e <;> decide
    · rw [a267210_H_period e _ he, a267210_H_period (e + 1) _ (by omega),
        a267210_H_period (e + 1 + 1) _ (by omega)]
      have h1 : (e + 1) % 3 = (e % 3 + 1) % 3 := by omega
      have h2 : (e + 1 + 1) % 3 = (e % 3 + 2) % 3 := by omega
      rw [h1, h2]
      have hr : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
      generalize e % 3 = r at hr ⊢
      interval_cases r <;> decide

theorem a267210_rule_symm (l c r : Bool) :
    Nat.testBit 109 (4 * l.toNat + 2 * c.toNat + r.toNat)
      = Nat.testBit 109 (4 * r.toNat + 2 * c.toNat + l.toNat) := by
  cases l <;> cases c <;> cases r <;> decide

/-- The closed form of the whole evolution. -/
theorem a267210_state (n : ℕ) (x : ℤ) : state 109 n x = a267210_F n x.natAbs := by
  induction n generalizing x with
  | zero =>
    show decide (x = 0) = a267210_F 0 x.natAbs
    by_cases hx : x = 0
    · subst hx; decide
    · have h0 : 0 < x.natAbs := Int.natAbs_pos.mpr hx
      rw [a267210_F, if_pos h0]
      simp [hx]
  | succ n ih =>
    show Nat.testBit 109 (4 * (state 109 n (x - 1)).toNat + 2 * (state 109 n x).toNat
      + (state 109 n (x + 1)).toNat) = a267210_F (n + 1) x.natAbs
    rw [ih, ih, ih]
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg x
    · rcases m with _ | m
      · exact a267210_origin n
      · have h1 : ((((m + 1 : ℕ) : ℤ) - 1)).natAbs = m := by omega
        have h2 : (((m + 1 : ℕ) : ℤ)).natAbs = m + 1 := by omega
        have h3 : ((((m + 1 : ℕ) : ℤ) + 1)).natAbs = m + 2 := by omega
        rw [h1, h2, h3]
        exact a267210_core n m
    · rcases m with _ | m
      · exact a267210_origin n
      · have h1 : ((-((m + 1 : ℕ) : ℤ) - 1)).natAbs = m + 2 := by omega
        have h2 : (-((m + 1 : ℕ) : ℤ)).natAbs = m + 1 := by omega
        have h3 : ((-((m + 1 : ℕ) : ℤ) + 1)).natAbs = m := by omega
        rw [h1, h2, h3, a267210_rule_symm]
        exact a267210_core n m


/-- The middle column: OFF exactly at the times n ≥ 3 divisible by 3. -/
theorem a267210_c_eq (n : ℕ) : c n = if 3 ≤ n ∧ n % 3 = 0 then 0 else 1 := by
  unfold c
  rw [a267210_state, Int.natAbs_zero, a267210_F_in n 0 (Nat.zero_le n), Nat.sub_zero, Nat.zero_mod]
  by_cases h1 : 3 ≤ n <;> by_cases h2 : n % 3 = 0 <;> simp [a267210_H, h1, h2]

theorem a267210_c_shift (j : ℕ) : c (j + 4) = c (j + 1) := by
  rw [a267210_c_eq, a267210_c_eq]
  split_ifs <;> omega

theorem a267210_a_succ (n : ℕ) : a (n + 1) = 2 * a n + c (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have e : n + 1 - k = (n - k) + 1 := by omega
  rw [e, pow_succ]
  ring

theorem a267210_a_zero : a 0 = 1 := by
  unfold a
  rw [Finset.sum_range_one, a267210_c_eq]
  simp

theorem a267210_a_one : a 1 = 3 := by
  rw [a267210_a_succ, a267210_a_zero, a267210_c_eq]
  simp

theorem a267210_a_two : a 2 = 7 := by
  rw [a267210_a_succ, a267210_a_one, a267210_c_eq]
  simp

theorem a267210_a_three : a 3 = 14 := by
  rw [a267210_a_succ, a267210_a_two, a267210_c_eq]
  simp

theorem a267210_rec (j : ℕ) : a (j + 4) + 2 * a j = 2 * a (j + 3) + a (j + 1) := by
  have h1 : a (j + 4) = 2 * a (j + 3) + c (j + 4) := a267210_a_succ (j + 3)
  have h2 : a (j + 1) = 2 * a j + c (j + 1) := a267210_a_succ j
  have h3 := a267210_c_shift j
  omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a267210.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have e1 : j + 4 - 1 = j + 3 := by omega
    have e3 : j + 4 - 3 = j + 1 := by omega
    have e4 : j + 4 - 4 = j := by omega
    rw [e1, e3, e4]
    have h := OMA.Helpers.a267210_rec j
    omega
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    have eD : (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X + PowerSeries.X ^ 2)
        = (1 : PowerSeries ℚ) - (PowerSeries.X ^ 1 + PowerSeries.X ^ 1) - PowerSeries.X ^ 3
          + (PowerSeries.X ^ 4 + PowerSeries.X ^ 4) := by ring
    have eN : (1 + PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 : PowerSeries ℚ)
        = PowerSeries.X ^ 0 + PowerSeries.X ^ 1 + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by ring
    rw [eD, eN]
    have eA : OMA.S_oeis_a267210.A * ((1 : PowerSeries ℚ) - (PowerSeries.X ^ 1 + PowerSeries.X ^ 1)
        - PowerSeries.X ^ 3 + (PowerSeries.X ^ 4 + PowerSeries.X ^ 4))
        = OMA.S_oeis_a267210.A - (OMA.S_oeis_a267210.A * PowerSeries.X ^ 1
          + OMA.S_oeis_a267210.A * PowerSeries.X ^ 1) - OMA.S_oeis_a267210.A * PowerSeries.X ^ 3
          + (OMA.S_oeis_a267210.A * PowerSeries.X ^ 4 + OMA.S_oeis_a267210.A * PowerSeries.X ^ 4) := by
      ring
    rw [eA]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      OMA.S_oeis_a267210.A, PowerSeries.coeff_mk]
    rcases k with _ | _ | _ | _ | k
    · simp [OMA.Helpers.a267210_a_zero]
    · simp [OMA.Helpers.a267210_a_zero, OMA.Helpers.a267210_a_one]
      norm_num
    · simp [OMA.Helpers.a267210_a_one, OMA.Helpers.a267210_a_two]
      norm_num
    · simp [OMA.Helpers.a267210_a_zero, OMA.Helpers.a267210_a_two, OMA.Helpers.a267210_a_three]
      norm_num
    · have h := OMA.Helpers.a267210_rec k
      have hq : (OMA.S_oeis_a267210.a (k + 4) : ℚ) + 2 * OMA.S_oeis_a267210.a k
          = 2 * OMA.S_oeis_a267210.a (k + 3) + OMA.S_oeis_a267210.a (k + 1) := by exact_mod_cast h
      simp
      linarith
