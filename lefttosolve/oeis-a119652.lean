import OMAStatements.S_oeis_a119652
import Mathlib

/-!
Proof of the three conjectures of Colin Barker (Oct 25 2019) for OEIS A119652, the number of
different values of at most n coins taken from 1, 5, 10 and 25 cents.

* Greedy is optimal for these coins: with `g v = v/25 + (v%25)/10 + (v%25%10)/5 + v%5`, any
  collection of value `v` has at least `g v` coins, and the greedy collection has exactly
  `g v` coins. So `v` is the value of 1 to n coins exactly when `1 <= v` and `g v <= n`.
* Write `v = 25 q + r` with `r < 25`; then `g v = q + g r`, and `g r <= 6` for `r < 25`.
  For `n >= 5`, the values `v` with `g v = n + 1` are exactly the 25 numbers
  `25 (n + 1 - g r) + r` with `r < 25`, so the count grows by 25 from n to n + 1.
* Counting directly, the values for n = 0, 1, 2, 3, 4, 5 number 0, 4, 13, 27, 46, 69, hence
  a(n) = 25 n - 56 for n >= 5. The recurrence for n > 6 and the generating function
  (coefficient by coefficient) follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a119652

/-- The greedy number of coins for the value `v`: as many quarters as possible, then dimes,
then nickels, then pennies. -/
def a119652_g (v : ℕ) : ℕ := v / 25 + v % 25 / 10 + v % 25 % 10 / 5 + v % 5

/-- Greedy is optimal for the coins 1, 5, 10, 25: a collection of `p` pennies, `m` nickels,
`d` dimes and `q` quarters has at least as many coins as the greedy collection. -/
theorem a119652_g_le (p m d q : ℕ) :
    a119652_g (p + 5 * m + 10 * d + 25 * q) ≤ p + m + d + q := by
  unfold a119652_g
  omega

/-- A number is the value of between 1 and `n` coins exactly when it is positive and its greedy
number of coins is at most `n`. -/
theorem a119652_mem_iff (n v : ℕ) : v ∈ coinValues n ↔ 1 ≤ v ∧ a119652_g v ≤ n := by
  constructor
  · rintro ⟨p, m, d, q, h1, h2, rfl⟩
    have := a119652_g_le p m d q
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    unfold a119652_g at h2
    exact ⟨v % 5, v % 25 % 10 / 5, v % 25 / 10, v / 25, by omega, by omega, by omega⟩

/-- The values of at most `n` coins, as a filter of an initial segment of ℕ. -/
def a119652_T (n : ℕ) : Finset ℕ :=
  (Finset.range (25 * n + 25)).filter (fun v => 1 ≤ v ∧ a119652_g v ≤ n)

theorem a119652_a_eq (n : ℕ) : a n = (a119652_T n).card := by
  have h : coinValues n = ↑(a119652_T n) := by
    ext v
    rw [a119652_mem_iff, Finset.mem_coe, a119652_T, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, h2⟩
      unfold a119652_g at h2
      omega
    · rintro ⟨_, h⟩
      exact h
  unfold a
  rw [h, Set.ncard_coe_finset]

/-- For `n >= 5` and `r < 25`, the number `25 (n + 1 - g r) + r` needs exactly `n + 1` coins. -/
theorem a119652_g_new (n r : ℕ) (hn : 5 ≤ n) (hr : r < 25) :
    a119652_g (25 * (n + 1 - a119652_g r) + r) = n + 1 := by
  unfold a119652_g
  omega

/-- For `n >= 5`, the values of at most `n + 1` coins are those of at most `n` coins and the 25
numbers `25 (n + 1 - g r) + r` with `r < 25`. -/
theorem a119652_T_succ (n : ℕ) (hn : 5 ≤ n) :
    a119652_T (n + 1) =
      a119652_T n ∪ (Finset.range 25).image (fun r => 25 * (n + 1 - a119652_g r) + r) := by
  ext v
  simp only [a119652_T, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro ⟨h0, h1, h2⟩
    by_cases h : a119652_g v ≤ n
    · left
      refine ⟨?_, h1, h⟩
      unfold a119652_g at h
      omega
    · right
      refine ⟨v % 25, Nat.mod_lt _ (by norm_num), ?_⟩
      unfold a119652_g at h h2 ⊢
      omega
  · rintro (⟨h0, h1, h2⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨by omega, h1, by omega⟩
    · have e := a119652_g_new n r hn hr
      refine ⟨by omega, ?_, by omega⟩
      unfold a119652_g at e ⊢
      omega

/-- For `n >= 5`, one more coin gives exactly 25 more values. -/
theorem a119652_card_succ (n : ℕ) (hn : 5 ≤ n) :
    (a119652_T (n + 1)).card = (a119652_T n).card + 25 := by
  rw [a119652_T_succ n hn, Finset.card_union_of_disjoint, Finset.card_image_of_injOn,
    Finset.card_range]
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_range] at hx hy
    simp only at hxy
    omega
  · rw [Finset.disjoint_left]
    intro v hv hv'
    rw [a119652_T, Finset.mem_filter] at hv
    rw [Finset.mem_image] at hv'
    obtain ⟨r, hr, rfl⟩ := hv'
    have := a119652_g_new n r hn (Finset.mem_range.mp hr)
    omega

theorem a119652_T_five : (a119652_T 5).card = 69 := by decide

theorem a119652_card_closed (n : ℕ) (hn : 5 ≤ n) : (a119652_T n).card + 56 = 25 * n := by
  induction n, hn using Nat.le_induction with
  | base => rw [a119652_T_five]
  | succ m hm ih =>
    rw [a119652_card_succ m hm]
    omega

/-- The closed form `a(n) = 25 n - 56` for `n > 4`. -/
theorem a119652_closed (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 25 * n - 56 := by
  rw [a119652_a_eq]
  have := a119652_card_closed n hn
  omega

theorem a119652_zero : a 0 = 0 := by rw [a119652_a_eq]; decide

theorem a119652_one : a 1 = 4 := by rw [a119652_a_eq]; decide

theorem a119652_two : a 2 = 13 := by rw [a119652_a_eq]; decide

theorem a119652_three : a 3 = 27 := by rw [a119652_a_eq]; decide

theorem a119652_four : a 4 = 46 := by rw [a119652_a_eq]; decide

/-- The recurrence `a(n) = 2 a(n-1) - a(n-2)` for `n > 6`, from the closed form. -/
theorem a119652_rec (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    a119652_closed (m + 7) (by omega), a119652_closed (m + 6) (by omega),
    a119652_closed (m + 5) (by omega)]
  push_cast
  ring

/-- The generating function, as a product identity in ℤ⟦X⟧, checked coefficient by
coefficient: coefficients 0..6 from a(0..6) = 0, 4, 13, 27, 46, 69, 94, and coefficient
k >= 7 from the closed form. -/
theorem a119652_gf :
    PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) * (1 - PowerSeries.X) ^ 2 =
      PowerSeries.X * (4 + 5 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 5 * PowerSeries.X ^ 3
        + 4 * PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5) := by
  have hb : (fun n => if n = 0 then 0 else (a n : ℤ)) = fun n => (a n : ℤ) := by
    funext n
    split_ifs with h
    · rw [h, a119652_zero, Nat.cast_zero]
    · rfl
  rw [hb]
  set p : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ)) with hp
  have e1 : p * (1 - PowerSeries.X) ^ 2 =
      p - PowerSeries.C (2 : ℤ) * (p * PowerSeries.X ^ 1) + p * PowerSeries.X ^ 2 := by
    rw [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (4 + 5 * PowerSeries.X + 5 * PowerSeries.X ^ 2
        + 5 * PowerSeries.X ^ 3 + 4 * PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5) :
        PowerSeries ℤ) =
      PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 2
        + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 3 + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 4
        + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 5
        + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;>
      simp [a119652_zero, a119652_one, a119652_two, a119652_three, a119652_four,
        a119652_closed]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    rw [if_pos (show 1 ≤ j + 7 by omega), if_pos (show 2 ≤ j + 7 by omega),
      if_neg (show ¬ (j + 7 = 1) by omega), if_neg (show ¬ (j + 7 = 2) by omega),
      if_neg (show ¬ (j + 7 = 3) by omega), if_neg (show ¬ (j + 7 = 4) by omega),
      if_neg (show ¬ (j + 7 = 5) by omega), if_neg (show ¬ (j + 7 = 6) by omega),
      show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      a119652_closed (j + 7) (by omega), a119652_closed (j + 6) (by omega),
      a119652_closed (j + 5) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a119652.main :=
  ⟨OMA.Helpers.a119652_gf, OMA.Helpers.a119652_rec, OMA.Helpers.a119652_closed⟩
