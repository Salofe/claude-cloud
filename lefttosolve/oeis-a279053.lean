import OMAStatements.S_oeis_a279053
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a279053

theorem cell_succ' (t : ℕ) (i j : ℤ) : cell 131 (t + 1) i j =
    Nat.testBit 131 ((cell 131 t i j).toNat + 2 * ((cell 131 t (i + 1) j).toNat +
      (cell 131 t (i - 1) j).toNat + (cell 131 t i (j + 1)).toNat +
      (cell 131 t i (j - 1)).toNat)) := rfl

theorem r_off : ∀ b1 b2 b3 b4 : Bool, (b1 || b2 || b3 || b4) = true →
    Nat.testBit 131 (false.toNat + 2 * (b1.toNat + b2.toNat + b3.toNat + b4.toNat)) = false := by
  decide

theorem r_zero : ∀ c : Bool,
    Nat.testBit 131 (c.toNat + 2 * (false.toNat + false.toNat + false.toNat + false.toNat)) = true := by
  decide

theorem r_full :
    Nat.testBit 131 (true.toNat + 2 * (true.toNat + true.toNat + true.toNat + true.toNat)) = false := by
  decide

theorem r_three : ∀ b1 b2 b3 b4 : Bool, b1.toNat + b2.toNat + b3.toNat + b4.toNat = 3 →
    Nat.testBit 131 (true.toNat + 2 * (b1.toNat + b2.toNat + b3.toNat + b4.toNat)) = true := by
  decide

theorem bt {α : Type} [DecidableEq α] {a b : α} (h : a = b) : (a == b) = true := by simp [h]

theorem bf {α : Type} [DecidableEq α] {a b : α} (h : a ≠ b) : (a == b) = false := by simp [h]

/-- The invariant: outside the light cone every cell has the background value, on the axis
the even cells are on and the odd ones off, and next to the axis the even cells are off. -/
def Inv (t : ℕ) : Prop :=
  (∀ i j : ℤ, t < i.natAbs + j.natAbs → cell 131 t i j = (t % 2 == 1)) ∧
  (∀ i : ℤ, i.natAbs ≤ t → cell 131 t i 0 = (i % 2 == 0)) ∧
  (∀ i j : ℤ, i.natAbs ≤ t → i % 2 = 0 → (j = 1 ∨ j = -1) → cell 131 t i j = false)

theorem inv_zero : Inv 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    show decide (i = 0 ∧ j = 0) = (0 % 2 == 1)
    have : ¬ (i = 0 ∧ j = 0) := by omega
    simp [this]
  · intro i h
    have hi : i = 0 := by omega
    subst hi
    rfl
  · intro i j h _ hj
    have hi : i = 0 := by omega
    subst hi
    show decide ((0 : ℤ) = 0 ∧ j = 0) = false
    have : j ≠ 0 := by omega
    simp [this]

theorem axis_odd {t : ℕ} (hI : Inv t) {i : ℤ} (hi : i % 2 ≠ 0)
    (h : i.natAbs ≤ t ∨ (t < i.natAbs ∧ t % 2 = 0)) : cell 131 t i 0 = false := by
  rcases h with h | ⟨h1, h2⟩
  · rw [hI.2.1 i h]; exact bf hi
  · rw [hI.1 i 0 (by omega)]; exact bf (by omega)

theorem inv_succ {t : ℕ} (hI : Inv t) : Inv (t + 1) := by
  obtain ⟨hA, hB, hC⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [cell_succ', hA i j (by omega), hA (i + 1) j (by omega), hA (i - 1) j (by omega),
      hA i (j + 1) (by omega), hA i (j - 1) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one t with h0 | h0
    · rw [bf (show t % 2 ≠ 1 by omega), bt (show (t + 1) % 2 = 1 by omega)]
      exact r_zero false
    · rw [bt (show t % 2 = 1 by omega), bf (show (t + 1) % 2 ≠ 1 by omega)]
      exact r_full
  · intro i hi
    rw [cell_succ']
    simp only [zero_add, zero_sub]
    by_cases he : i % 2 = 0
    · rw [bt he]
      by_cases hit : i.natAbs ≤ t
      · rw [hB i hit, bt he, hC i 1 hit he (Or.inl rfl), hC i (-1) hit he (Or.inr rfl),
          axis_odd ⟨hA, hB, hC⟩ (i := i + 1) (by omega) (by omega),
          axis_odd ⟨hA, hB, hC⟩ (i := i - 1) (by omega) (by omega)]
        exact r_zero true
      · have ht : t % 2 = 1 := by omega
        have e1 : cell 131 t i 0 = true := by rw [hA i 0 (by omega)]; exact bt ht
        have e2 : cell 131 t i 1 = true := by rw [hA i 1 (by omega)]; exact bt ht
        have e3 : cell 131 t i (-1) = true := by rw [hA i (-1) (by omega)]; exact bt ht
        rw [e1, e2, e3]
        rcases le_or_gt 0 i with hpos | hneg
        · have e4 : cell 131 t (i + 1) 0 = true := by rw [hA (i + 1) 0 (by omega)]; exact bt ht
          have e5 : cell 131 t (i - 1) 0 = false := by
            rw [hB (i - 1) (by omega)]; exact bf (by omega)
          rw [e4, e5]
          rfl
        · have e4 : cell 131 t (i - 1) 0 = true := by rw [hA (i - 1) 0 (by omega)]; exact bt ht
          have e5 : cell 131 t (i + 1) 0 = false := by
            rw [hB (i + 1) (by omega)]; exact bf (by omega)
          rw [e4, e5]
          rfl
    · rw [bf he, axis_odd ⟨hA, hB, hC⟩ he (by omega)]
      apply r_off
      rcases le_or_gt 0 i with hpos | hneg
      · have e5 : cell 131 t (i - 1) 0 = true := by
          rw [hB (i - 1) (by omega)]; exact bt (by omega)
        rw [e5]; simp
      · have e5 : cell 131 t (i + 1) 0 = true := by
          rw [hB (i + 1) (by omega)]; exact bt (by omega)
        rw [e5]; simp
  · intro i j hi he hj
    rw [cell_succ']
    by_cases hit : i.natAbs ≤ t
    · rw [hC i j hit he hj]
      apply r_off
      rcases hj with rfl | rfl
      · have e : cell 131 t i (1 - 1) = true := by
          rw [show (1 : ℤ) - 1 = 0 by norm_num, hB i hit]; exact bt he
        rw [e]; simp
      · have e : cell 131 t i (-1 + 1) = true := by
          rw [show (-1 : ℤ) + 1 = 0 by norm_num, hB i hit]; exact bt he
        rw [e]; simp
    · have ht : t % 2 = 1 := by omega
      rw [hA i j (by omega), hA (i + 1) j (by omega), hA (i - 1) j (by omega),
        hA i (j + 1) (by omega), hA i (j - 1) (by omega), bt ht]
      exact r_full

theorem inv_all (t : ℕ) : Inv t := by
  induction t with
  | zero => exact inv_zero
  | succ t ih => exact inv_succ ih

/-- Sum of the even powers of ten up to `10 ^ m`. -/
def g (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), if k % 2 = 0 then (10 : ℤ) ^ k else 0

theorem a_eq_g (n : ℕ) : a n = g n := by
  unfold a g
  rw [← Finset.sum_range_reflect (fun k => if k % 2 = 0 then (10 : ℤ) ^ k else 0) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [(inv_all n).2.1 _ (by omega)]
  simp only [beq_iff_eq, Nat.add_sub_cancel]
  by_cases h : (n - k) % 2 = 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem g_succ (m : ℕ) : g (m + 1) = g m + if (m + 1) % 2 = 0 then (10 : ℤ) ^ (m + 1) else 0 := by
  unfold g
  rw [Finset.sum_range_succ]

theorem g_even (m : ℕ) : 99 * g (2 * m) = 100 ^ (m + 1) - 1 ∧ g (2 * m + 1) = g (2 * m) := by
  have hodd : ∀ m : ℕ, g (2 * m + 1) = g (2 * m) := by
    intro m
    rw [g_succ, if_neg (by omega), add_zero]
  refine ⟨?_, hodd m⟩
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, g_succ, hodd, if_pos (by omega), mul_add, ih,
      show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    ring

theorem closed (n : ℕ) : (a n : ℚ) =
    (9 * (-2 : ℚ) ^ n * (5 : ℚ) ^ (n + 1) + 11 * (2 : ℚ) ^ n * (5 : ℚ) ^ (n + 1) - 1) / 99 := by
  rw [a_eq_g]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hq : (99 : ℚ) * (g (2 * m) : ℚ) = (100 : ℚ) ^ (m + 1) - 1 := by
      exact_mod_cast (g_even m).1
    have h4 : (-2 : ℚ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
    have h4' : (2 : ℚ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
    have h25 : (5 : ℚ) ^ (2 * m) = 25 ^ m := by rw [pow_mul]; norm_num
    have h100 : (100 : ℚ) ^ m = 4 ^ m * 25 ^ m := by rw [← mul_pow]; norm_num
    rw [eq_div_iff (by norm_num), mul_comm, hq, pow_succ (5 : ℚ) (2 * m), pow_succ (100 : ℚ) m,
      h4, h4', h25, h100]
    ring
  · rw [(g_even m).2]
    have hq : (99 : ℚ) * (g (2 * m) : ℚ) = (100 : ℚ) ^ (m + 1) - 1 := by
      exact_mod_cast (g_even m).1
    have h4 : (-2 : ℚ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
    have h4' : (2 : ℚ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
    have h25 : (5 : ℚ) ^ (2 * m) = 25 ^ m := by rw [pow_mul]; norm_num
    have h100 : (100 : ℚ) ^ m = 4 ^ m * 25 ^ m := by rw [← mul_pow]; norm_num
    rw [eq_div_iff (by norm_num), mul_comm, hq, pow_succ (-2 : ℚ) (2 * m), pow_succ (2 : ℚ) (2 * m),
      pow_succ (5 : ℚ) (2 * m + 1), pow_succ (5 : ℚ) (2 * m), pow_succ (100 : ℚ) m,
      h4, h4', h25, h100]
    ring

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a279053.main := by
  have hc := OMA.Helpers.closed
  have hrec : ∀ n : ℕ, 3 ≤ n → ((OMA.S_oeis_a279053.a n : ℤ) : ℚ) =
      OMA.S_oeis_a279053.a (n - 1) + 100 * OMA.S_oeis_a279053.a (n - 2) -
        100 * OMA.S_oeis_a279053.a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega, hc, hc, hc, hc]
    ring
  refine ⟨hc, hrec, ?_⟩
  set f : ℕ → ℚ := fun n => (OMA.S_oeis_a279053.a n : ℚ) with hf
  have h0 : f 0 = 1 := by rw [hf]; simp only; rw [hc]; norm_num
  have h1 : f 1 = 1 := by rw [hf]; simp only; rw [hc]; norm_num
  have h2 : f 2 = 101 := by rw [hf]; simp only; rw [hc]; norm_num
  have hr : ∀ m : ℕ, f (m + 3) - f (m + 2) - 100 * f (m + 1) + 100 * f m = 0 := by
    intro m
    have := hrec (m + 3) (by omega)
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega] at this
    rw [hf]; simp only; rw [this]; ring
  have e1 : ((1 - X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      X ^ 0 - C (1 : ℚ) * X ^ 1 - C (100 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 3 := by
    simp only [map_one, map_ofNat]
    ring
  rw [e1]
  ext k
  simp only [mul_sub, mul_add, map_add, map_sub, ← mul_assoc]
  simp only [mul_comm (mk f) (C _), mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> simp [h0, h1, h2] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    rw [show m + 3 - 0 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega,
      show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
    linear_combination hr m
