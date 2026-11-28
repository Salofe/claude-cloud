import OMAStatements.S_oeis_a283641
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a283641

theorem c_succ (t : ℕ) (i j : ℤ) : cell 678 (t + 1) i j =
    Nat.testBit 678 ((cell 678 t i j).toNat + 2 * ((cell 678 t (i + 1) j).toNat +
      (cell 678 t (i - 1) j).toNat + (cell 678 t i (j + 1)).toNat +
      (cell 678 t i (j - 1)).toNat)) := rfl

theorem cone (t : ℕ) : ∀ i j : ℤ, (t : ℤ) < |i| + |j| → cell 678 t i j = false := by
  induction t with
  | zero =>
    intro i j h
    show decide (i = 0 ∧ j = 0) = false
    rw [decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ t ih =>
    intro i j h
    push_cast at h
    rw [c_succ, ih i j (by linarith),
      ih (i + 1) j (by cases abs_cases i <;> cases abs_cases (i + 1) <;> linarith),
      ih (i - 1) j (by cases abs_cases i <;> cases abs_cases (i - 1) <;> linarith),
      ih i (j + 1) (by cases abs_cases j <;> cases abs_cases (j + 1) <;> linarith),
      ih i (j - 1) (by cases abs_cases j <;> cases abs_cases (j - 1) <;> linarith)]
    rfl

/-- At even times only cells with both coordinates even can be ON. -/
def Par (u : ℕ) : Prop := ∀ i j : ℤ, (i % 2 = 1 ∨ j % 2 = 1) → cell 678 (2 * u) i j = false

theorem odd_ee (u : ℕ) (hP : Par u) (i j : ℤ) (hi : i % 2 = 0) (hj : j % 2 = 0) :
    cell 678 (2 * u + 1) i j = cell 678 (2 * u) i j := by
  rw [c_succ, hP (i + 1) j (by omega), hP (i - 1) j (by omega), hP i (j + 1) (by omega),
    hP i (j - 1) (by omega)]
  cases cell 678 (2 * u) i j <;> rfl

theorem odd_oe (u : ℕ) (hP : Par u) (i j : ℤ) (hi : i % 2 = 1) (hj : j % 2 = 0) :
    cell 678 (2 * u + 1) i j = xor (cell 678 (2 * u) (i - 1) j) (cell 678 (2 * u) (i + 1) j) := by
  rw [c_succ, hP i j (by omega), hP i (j + 1) (by omega), hP i (j - 1) (by omega)]
  cases cell 678 (2 * u) (i - 1) j <;> cases cell 678 (2 * u) (i + 1) j <;> rfl

theorem odd_eo (u : ℕ) (hP : Par u) (i j : ℤ) (hi : i % 2 = 0) (hj : j % 2 = 1) :
    cell 678 (2 * u + 1) i j = xor (cell 678 (2 * u) i (j - 1)) (cell 678 (2 * u) i (j + 1)) := by
  rw [c_succ, hP i j (by omega), hP (i + 1) j (by omega), hP (i - 1) j (by omega)]
  cases cell 678 (2 * u) i (j - 1) <;> cases cell 678 (2 * u) i (j + 1) <;> rfl

theorem odd_oo (u : ℕ) (hP : Par u) (i j : ℤ) (hi : i % 2 = 1) (hj : j % 2 = 1) :
    cell 678 (2 * u + 1) i j = false := by
  rw [c_succ, hP i j (by omega), hP (i + 1) j (by omega), hP (i - 1) j (by omega),
    hP i (j + 1) (by omega), hP i (j - 1) (by omega)]
  rfl

theorem par_zero : Par 0 := by
  intro i j h
  show decide (i = 0 ∧ j = 0) = false
  rw [decide_eq_false_iff_not]
  omega

theorem par_succ (u : ℕ) (hP : Par u) : Par (u + 1) := by
  intro i j h
  rw [show 2 * (u + 1) = (2 * u + 1) + 1 by ring, c_succ]
  rcases Int.emod_two_eq_zero_or_one i with hi | hi <;>
    rcases Int.emod_two_eq_zero_or_one j with hj | hj
  · omega
  · rw [odd_eo u hP i j hi hj, odd_oo u hP (i + 1) j (by omega) hj,
      odd_oo u hP (i - 1) j (by omega) hj, odd_ee u hP i (j + 1) hi (by omega),
      odd_ee u hP i (j - 1) hi (by omega)]
    cases cell 678 (2 * u) i (j - 1) <;> cases cell 678 (2 * u) i (j + 1) <;> rfl
  · rw [odd_oe u hP i j hi hj, odd_ee u hP (i + 1) j (by omega) hj,
      odd_ee u hP (i - 1) j (by omega) hj, odd_oo u hP i (j + 1) hi (by omega),
      odd_oo u hP i (j - 1) hi (by omega)]
    cases cell 678 (2 * u) (i - 1) j <;> cases cell 678 (2 * u) (i + 1) j <;> rfl
  · rw [odd_oo u hP i j hi hj, odd_eo u hP (i + 1) j (by omega) hj,
      odd_eo u hP (i - 1) j (by omega) hj, odd_oe u hP i (j + 1) hi (by omega),
      odd_oe u hP i (j - 1) hi (by omega)]
    cases cell 678 (2 * u) (i - 1) (j - 1) <;> cases cell 678 (2 * u) (i + 1) (j - 1) <;>
      cases cell 678 (2 * u) (i - 1) (j + 1) <;> cases cell 678 (2 * u) (i + 1) (j + 1) <;> rfl

theorem par_all (u : ℕ) : Par u := by
  induction u with
  | zero => exact par_zero
  | succ u ih => exact par_succ u ih

theorem two_step (u : ℕ) (i j : ℤ) (hi : i % 2 = 0) (hj : j % 2 = 0) :
    cell 678 (2 * (u + 1)) i j = Nat.testBit 678 ((cell 678 (2 * u) i j).toNat +
      2 * ((xor (cell 678 (2 * u) i j) (cell 678 (2 * u) (i + 2) j)).toNat +
        (xor (cell 678 (2 * u) (i - 2) j) (cell 678 (2 * u) i j)).toNat +
        (xor (cell 678 (2 * u) i j) (cell 678 (2 * u) i (j + 2))).toNat +
        (xor (cell 678 (2 * u) i (j - 2)) (cell 678 (2 * u) i j)).toNat)) := by
  have hP := par_all u
  rw [show 2 * (u + 1) = (2 * u + 1) + 1 by ring, c_succ, odd_ee u hP i j hi hj,
    odd_oe u hP (i + 1) j (by omega) hj, odd_oe u hP (i - 1) j (by omega) hj,
    odd_eo u hP i (j + 1) hi (by omega), odd_eo u hP i (j - 1) hi (by omega)]
  rw [show i + 1 - 1 = i by ring, show i + 1 + 1 = i + 2 by ring, show i - 1 - 1 = i - 2 by ring,
    show i - 1 + 1 = i by ring, show j + 1 - 1 = j by ring, show j + 1 + 1 = j + 2 by ring,
    show j - 1 - 1 = j - 2 by ring, show j - 1 + 1 = j by ring]

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a283641

/-- The x-axis and the rows `y = 2` and `y = -2` at time `2u`. -/
def Band (u : ℕ) : Prop :=
  (∀ p : ℤ, cell 678 (2 * u) (2 * p) 0 = decide (-(u : ℤ) ≤ p ∧ p ≤ u)) ∧
  (∀ p : ℤ, cell 678 (2 * u) (2 * p) 2 = decide (p % 2 = 0 ∧ -(u : ℤ) < p ∧ p < u)) ∧
  (∀ p : ℤ, cell 678 (2 * u) (2 * p) (-2) = decide (p % 2 = 0 ∧ -(u : ℤ) < p ∧ p < u))

theorem band_zero : Band 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro p
  · show decide (2 * p = 0 ∧ (0 : ℤ) = 0) = decide (-((0 : ℕ) : ℤ) ≤ p ∧ p ≤ ((0 : ℕ) : ℤ))
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; push_cast
    constructor <;> intro h <;> simp only [and_true, true_and, and_false, false_and] at h ⊢ <;> first | omega | simp_all
  · show decide (2 * p = 0 ∧ (2 : ℤ) = 0) =
      decide (p % 2 = 0 ∧ -((0 : ℕ) : ℤ) < p ∧ p < ((0 : ℕ) : ℤ))
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; push_cast
    constructor <;> intro h <;> simp only [and_true, true_and, and_false, false_and] at h ⊢ <;> first | omega | simp_all
  · show decide (2 * p = 0 ∧ (-2 : ℤ) = 0) =
      decide (p % 2 = 0 ∧ -((0 : ℕ) : ℤ) < p ∧ p < ((0 : ℕ) : ℤ))
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; push_cast
    constructor <;> intro h <;> simp only [and_true, true_and, and_false, false_and] at h ⊢ <;> first | omega | simp_all

theorem cone4 (u : ℕ) (p : ℤ) (j : ℤ) (hj : j = 4 ∨ j = -4)
    (h : cell 678 (2 * u) (2 * p) j = true) : -(u : ℤ) < p ∧ p < u := by
  by_contra hc
  rw [cone (2 * u) (2 * p) j (by
    have h4 : |j| = 4 := by rcases hj with rfl | rfl <;> norm_num
    rw [h4]
    push_cast
    cases abs_cases (2 * p) <;> omega)] at h
  exact Bool.false_ne_true h

theorem band_succ (u : ℕ) (hB : Band u) : Band (u + 1) := by
  obtain ⟨h0, h2, hm2⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · intro p
    rw [two_step u (2 * p) 0 (by omega) (by norm_num)]
    rw [show 2 * p + 2 = 2 * (p + 1) by ring, show 2 * p - 2 = 2 * (p - 1) by ring,
      show (0 : ℤ) + 2 = 2 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num,
      h0 p, h0 (p + 1), h0 (p - 1), h2 p, hm2 p]
    push_cast
    cases hc : decide (-(u : ℤ) ≤ p ∧ p ≤ u) <;>
      cases hE : decide (-(u : ℤ) ≤ p + 1 ∧ p + 1 ≤ u) <;>
      cases hW : decide (-(u : ℤ) ≤ p - 1 ∧ p - 1 ≤ u) <;>
      cases hN : decide (p % 2 = 0 ∧ -(u : ℤ) < p ∧ p < u) <;>
      cases hz : decide (-((u : ℤ) + 1) ≤ p ∧ p ≤ u + 1) <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hc hE hW hN hz <;>
      first | rfl | (exfalso; omega)
  · intro p
    rw [two_step u (2 * p) 2 (by omega) (by norm_num)]
    rw [show 2 * p + 2 = 2 * (p + 1) by ring, show 2 * p - 2 = 2 * (p - 1) by ring,
      show (2 : ℤ) + 2 = 4 by norm_num, show (2 : ℤ) - 2 = 0 by norm_num,
      h2 p, h2 (p + 1), h2 (p - 1), h0 p]
    have hy := cone4 u p 4 (Or.inl rfl)
    push_cast
    cases hc : decide (p % 2 = 0 ∧ -(u : ℤ) < p ∧ p < u) <;>
      cases hE : decide ((p + 1) % 2 = 0 ∧ -(u : ℤ) < p + 1 ∧ p + 1 < u) <;>
      cases hW : decide ((p - 1) % 2 = 0 ∧ -(u : ℤ) < p - 1 ∧ p - 1 < u) <;>
      cases hS : decide (-(u : ℤ) ≤ p ∧ p ≤ u) <;>
      cases hN : cell 678 (2 * u) (2 * p) 4 <;>
      cases hz : decide (p % 2 = 0 ∧ -((u : ℤ) + 1) < p ∧ p < u + 1) <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hc hE hW hS hz <;>
      first | rfl | (exfalso; have := hy hN; omega) | (exfalso; omega)
  · intro p
    rw [two_step u (2 * p) (-2) (by omega) (by norm_num)]
    rw [show 2 * p + 2 = 2 * (p + 1) by ring, show 2 * p - 2 = 2 * (p - 1) by ring,
      show (-2 : ℤ) + 2 = 0 by norm_num, show (-2 : ℤ) - 2 = -4 by norm_num,
      hm2 p, hm2 (p + 1), hm2 (p - 1), h0 p]
    have hy := cone4 u p (-4) (Or.inr rfl)
    push_cast
    cases hc : decide (p % 2 = 0 ∧ -(u : ℤ) < p ∧ p < u) <;>
      cases hE : decide ((p + 1) % 2 = 0 ∧ -(u : ℤ) < p + 1 ∧ p + 1 < u) <;>
      cases hW : decide ((p - 1) % 2 = 0 ∧ -(u : ℤ) < p - 1 ∧ p - 1 < u) <;>
      cases hS : decide (-(u : ℤ) ≤ p ∧ p ≤ u) <;>
      cases hN : cell 678 (2 * u) (2 * p) (-4) <;>
      cases hz : decide (p % 2 = 0 ∧ -((u : ℤ) + 1) < p ∧ p < u + 1) <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hc hE hW hS hz <;>
      first | rfl | (exfalso; have := hy hN; omega) | (exfalso; omega)

theorem band_all (u : ℕ) : Band u := by
  induction u with
  | zero => exact band_zero
  | succ u ih => exact band_succ u ih

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a283641

theorem axis (n d : ℕ) (hd : d ≤ n) :
    cell 678 n (-(d : ℤ)) 0 = decide (d % 2 = 0 ∨ d = n) := by
  rcases Nat.even_or_odd' n with ⟨u, rfl | rfl⟩
  · rcases Nat.even_or_odd' d with ⟨q, rfl | rfl⟩
    · rw [show (-((2 * q : ℕ) : ℤ)) = 2 * (-(q : ℤ)) by push_cast; ring, (band_all u).1]
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
      constructor <;> intro h <;> omega
    · rw [par_all u _ _ (Or.inl (by push_cast; omega))]
      symm; rw [decide_eq_false_iff_not]; omega
  · rcases Nat.even_or_odd' d with ⟨q, rfl | rfl⟩
    · rw [odd_ee u (par_all u) _ _ (by push_cast; omega) (by norm_num)]
      rw [show (-((2 * q : ℕ) : ℤ)) = 2 * (-(q : ℤ)) by push_cast; ring, (band_all u).1]
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
      constructor <;> intro h <;> omega
    · rw [odd_oe u (par_all u) _ _ (by push_cast; omega) (by norm_num)]
      rw [show (-((2 * q + 1 : ℕ) : ℤ)) - 1 = 2 * (-(q : ℤ) - 1) by push_cast; ring,
        show (-((2 * q + 1 : ℕ) : ℤ)) + 1 = 2 * (-(q : ℤ)) by push_cast; ring,
        (band_all u).1, (band_all u).1]
      cases h1 : decide (-(u : ℤ) ≤ -(q : ℤ) - 1 ∧ -(q : ℤ) - 1 ≤ u) <;>
        cases h2 : decide (-(u : ℤ) ≤ -(q : ℤ) ∧ -(q : ℤ) ≤ u) <;>
        cases h3 : decide ((2 * q + 1) % 2 = 0 ∨ 2 * q + 1 = 2 * u + 1) <;>
        simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 <;>
        first | rfl | (exfalso; omega)

theorem a_eq (n : ℕ) :
    a n = ∑ d ∈ Finset.range n, (if d % 2 = 0 then (10 : ℤ) ^ d else 0) + 10 ^ n := by
  unfold a
  have h : ∀ k ∈ Finset.range (n + 1),
      (if cell 678 n (((n + 1 - 1 - k : ℕ) : ℤ) - n) 0 then (10 : ℤ) ^ (n - (n + 1 - 1 - k))
        else 0) = if k % 2 = 0 ∨ k = n then (10 : ℤ) ^ k else 0 := by
    intro k hk
    have hk' : k ≤ n := by simp at hk; omega
    rw [show (((n + 1 - 1 - k : ℕ) : ℤ) - n) = -(k : ℤ) by omega,
      show n - (n + 1 - 1 - k) = k by omega, axis n k hk']
    simp only [decide_eq_true_eq]
  rw [← Finset.sum_range_reflect, Finset.sum_congr rfl h, Finset.sum_range_succ]
  simp only [or_true, if_true]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≠ n := by simp at hk; omega
  simp only [hk', or_false]

theorem e_closed (n : ℕ) :
    (∑ d ∈ Finset.range n, (if d % 2 = 0 then (10 : ℚ) ^ d else 0)) =
      ((10 ^ n - 1) / 9 + (1 - (-10) ^ n) / 11) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs with h
    · have he : Even n := Nat.even_iff.mpr h
      rw [pow_succ (-10 : ℚ), he.neg_pow]
      ring
    · have ho : Odd n := Nat.odd_iff.mpr (by omega)
      rw [pow_succ (-10 : ℚ), ho.neg_pow]
      ring

theorem a_closed (n : ℕ) : (a n : ℚ) = (-2 - 9 * (-10 : ℚ) ^ n + 209 * (10 : ℚ) ^ n) / 198 := by
  rw [a_eq]
  push_cast
  rw [e_closed]
  ring

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a283641.main := by
  have hz := OMA.Helpers.a_closed
  refine ⟨?_, hz, ?_⟩
  · have e1 : PowerSeries.mk (fun n => (OMA.S_oeis_a283641.a n : ℚ)) *
        ((1 - X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ)
        = PowerSeries.mk (fun n => (OMA.S_oeis_a283641.a n : ℚ))
          - PowerSeries.mk (fun n => (OMA.S_oeis_a283641.a n : ℚ)) * X ^ 1
          - C (100 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a283641.a n : ℚ)) * X ^ 2)
          + C (100 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a283641.a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat]
      ring
    have e2 : (1 + 10 * X - 10 * X ^ 2 : PowerSeries ℚ)
        = C (1 : ℚ) * X ^ 0 + C (10 : ℚ) * X ^ 1 + C (-10 : ℚ) * X ^ 2 := by
      simp only [map_one, map_neg, map_ofNat]
      ring
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k <;> simp [hz] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      simp only [show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, show 3 ≤ m + 3 by omega,
        if_true, show m + 3 ≠ 0 by omega, show m + 3 ≠ 1 by omega, show m + 3 ≠ 2 by omega,
        if_false]
      rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
        show m + 3 - 3 = m by omega, hz (m + 3), hz (m + 2), hz (m + 1), hz m]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega, hz (m + 3), hz (m + 2), hz (m + 1), hz m]
    ring
