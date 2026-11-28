import OMAStatements.S_oeis_a282796
import Mathlib

/-!
Proof of the conjectures of OEIS A282796 (Rule 505, 5-celled von Neumann neighbourhood).

Rule 505 = 111111001 in binary: a cell with own value c and k ON neighbours is OFF at the next
step exactly when (c, k) is (1, 0), (0, 1) or (1, 4). Call a cell even or odd according to the
parity of x + y; the neighbours of a cell have the other parity.
* Light cone: after t steps a cell at distance |x| + |y| > t carries the background value, which
  alternates OFF, ON, OFF, ...
* Invariant at every odd time t: every even cell other than the origin is ON, the origin is OFF,
  the odd cells (x, 0) with |x| <= t are OFF, and the cells (x, 1) with x even and nonzero are ON.
  The rule is symmetric under (x, y) -> (y, x) and (x, y) -> (x, -y), so the same holds on the
  other half-axes and rows.
* From odd t to t + 1, every odd cell sees four ON even neighbours (or three plus the OFF
  origin, when it is next to the origin and itself OFF), so every odd cell flips. An even cell
  other than the origin is then ON at t + 1 unless its four odd neighbours were equal at t, and
  at t + 2 it sees the four flipped neighbours, so it is ON again in both cases. The remaining
  parts of the invariant at t + 2 are checked from the values at t + 1 near the axis.
* At odd n the axis cells (-m, 0), m = 0..n, are ON exactly for m even and nonzero; at even n
  they are all ON. This gives a(n) = 1...1 (n + 1 ones) for even n and a(n) = 1010...100 for odd
  n, and the recurrence and generating function follow by computing.
-/

namespace OMA.Helpers
open OMA.S_oeis_a282796 PowerSeries

theorem r_st (t : ℕ) (i j : ℤ) : cell 505 (t + 1) i j = (505 : ℕ).testBit ((cell 505 t i j).toNat +
    2 * ((cell 505 t (i + 1) j).toNat + (cell 505 t (i - 1) j).toNat + (cell 505 t i (j + 1)).toNat +
      (cell 505 t i (j - 1)).toNat)) := rfl

theorem r_swap : ∀ (t : ℕ) (i j : ℤ), cell 505 t i j = cell 505 t j i := by
  intro t
  induction t with
  | zero => intro i j; simp only [cell, and_comm]
  | succ t ih =>
    intro i j
    rw [r_st, r_st, ih i j, ih (i + 1) j, ih (i - 1) j, ih i (j + 1), ih i (j - 1)]
    congr 1
    omega

theorem r_negj : ∀ (t : ℕ) (i j : ℤ), cell 505 t i (-j) = cell 505 t i j := by
  intro t
  induction t with
  | zero => intro i j; simp only [cell, neg_eq_zero]
  | succ t ih =>
    intro i j
    have h1 := ih i (j - 1)
    have h2 := ih i (j + 1)
    rw [show -(j - 1) = -j + 1 by ring] at h1
    rw [show -(j + 1) = -j - 1 by ring] at h2
    rw [r_st, r_st, ih i j, ih (i + 1) j, ih (i - 1) j, h1, h2]
    congr 1
    omega

theorem r_lc : ∀ (t : ℕ) (i j : ℤ), (t : ℤ) < |i| + |j| → cell 505 t i j = decide (t % 2 = 1) := by
  intro t
  induction t with
  | zero =>
    intro i j h
    simp only [cell, Nat.zero_mod, zero_ne_one, decide_false, decide_eq_false_iff_not]
    intro ⟨hx, hy⟩
    subst hx; subst hy; simp at h
  | succ t ih =>
    intro i j h
    have h0 := ih i j (by push_cast at h; omega)
    have h1 := ih (i + 1) j (by push_cast at h; cases abs_cases (i+1) <;> cases abs_cases i <;> omega)
    have h2 := ih (i - 1) j (by push_cast at h; cases abs_cases (i-1) <;> cases abs_cases i <;> omega)
    have h3 := ih i (j + 1) (by push_cast at h; cases abs_cases (j+1) <;> cases abs_cases j <;> omega)
    have h4 := ih i (j - 1) (by push_cast at h; cases abs_cases (j-1) <;> cases abs_cases j <;> omega)
    rw [r_st, h0, h1, h2, h3, h4]
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have : (t + 1) % 2 = 1 := by omega
      simp only [ht, this]; decide
    · have : (t + 1) % 2 = 0 := by omega
      simp only [ht, this]; decide


/-- The invariant at odd times. -/
def r_Inv (t : ℕ) : Prop :=
  (∀ i j : ℤ, (i + j) % 2 = 0 → ¬(i = 0 ∧ j = 0) → cell 505 t i j = true) ∧
  cell 505 t 0 0 = false ∧
  (∀ i : ℤ, i % 2 = 1 → |i| ≤ t → cell 505 t i 0 = false) ∧
  (∀ i : ℤ, i % 2 = 0 → i ≠ 0 → cell 505 t i 1 = true)

theorem r_mixed (t : ℕ) (x y : ℤ) (hc : cell 505 t x y = true)
    (hf : cell 505 t (x + 1) y = false ∨ cell 505 t (x - 1) y = false ∨ cell 505 t x (y + 1) = false ∨
      cell 505 t x (y - 1) = false)
    (htr : cell 505 t (x + 1) y = true ∨ cell 505 t (x - 1) y = true ∨ cell 505 t x (y + 1) = true ∨
      cell 505 t x (y - 1) = true) : cell 505 (t + 1) x y = true := by
  rw [r_st, hc]
  revert hf htr
  generalize cell 505 t (x + 1) y = b1
  generalize cell 505 t (x - 1) y = b2
  generalize cell 505 t x (y + 1) = b3
  generalize cell 505 t x (y - 1) = b4
  revert b1 b2 b3 b4
  decide

theorem r_flip (t : ℕ) (ht : 1 ≤ t) (hI : r_Inv t) :
    ∀ i j : ℤ, (i + j) % 2 = 1 → cell 505 (t + 1) i j = !cell 505 t i j := by
  obtain ⟨ha, ha0, hb, hc⟩ := hI
  have L0 : ∀ x y : ℤ, (x + y) % 2 = 0 → cell 505 t x y = !decide (x = 0 ∧ y = 0) := by
    intro x y h
    by_cases hxy : x = 0 ∧ y = 0
    · obtain ⟨rfl, rfl⟩ := hxy; simp [ha0]
    · simp [hxy, ha x y h hxy]
  intro i j hp
  rw [r_st, L0 (i + 1) j (by omega), L0 (i - 1) j (by omega), L0 i (j + 1) (by omega),
    L0 i (j - 1) (by omega)]
  by_cases hA : |i| + |j| = 1
  · rcases (by cases abs_cases i <;> cases abs_cases j <;> omega :
      (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hb 1 (by norm_num) (by simp; omega)]; decide
    · rw [hb (-1) (by norm_num) (by simp; omega)]; decide
    · rw [r_swap, hb 1 (by norm_num) (by simp; omega)]; decide
    · rw [r_swap, hb (-1) (by norm_num) (by simp; omega)]; decide
  · have e1 : ¬(i + 1 = 0 ∧ j = 0) := by cases abs_cases i <;> cases abs_cases j <;> omega
    have e2 : ¬(i - 1 = 0 ∧ j = 0) := by cases abs_cases i <;> cases abs_cases j <;> omega
    have e3 : ¬(i = 0 ∧ j + 1 = 0) := by cases abs_cases i <;> cases abs_cases j <;> omega
    have e4 : ¬(i = 0 ∧ j - 1 = 0) := by cases abs_cases i <;> cases abs_cases j <;> omega
    simp only [e1, e2, e3, e4, decide_false, Bool.not_false]
    generalize cell 505 t i j = c
    cases c <;> decide

theorem r_org (t : ℕ) (ht : 1 ≤ t) (hI : r_Inv t) : cell 505 (t + 1) 0 0 = true := by
  obtain ⟨ha, ha0, hb, hc⟩ := hI
  rw [r_st]
  simp only [zero_add, zero_sub]
  rw [ha0, hb 1 (by norm_num) (by simp; omega), hb (-1) (by norm_num) (by simp; omega), r_swap t 0 1,
    r_swap t 0 (-1), hb 1 (by norm_num) (by simp; omega), hb (-1) (by norm_num) (by simp; omega)]
  decide


theorem r_lt2 (a i j : ℤ) (h : a < i + |j| ∨ a < -i + |j|) : a < |i| + |j| := by
  cases abs_cases i <;> omega

theorem r_step (t : ℕ) (ht : 1 ≤ t) (ht2 : t % 2 = 1) (hI : r_Inv t) : r_Inv (t + 1 + 1) := by
  have F := r_flip t ht hI
  have O1 := r_org t ht hI
  obtain ⟨ha, ha0, hb, hc⟩ := hI
  have bgt : decide (t % 2 = 1) = true := by simp [ht2]
  have bgt1 : decide ((t + 1) % 2 = 1) = false := by simp; omega
  have bgt2 : decide ((t + 1 + 1) % 2 = 1) = true := by simp; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- even sublattice: ON except the origin
    intro i j hp hno
    rw [r_st (t + 1) i j, F (i + 1) j (by omega), F (i - 1) j (by omega), F i (j + 1) (by omega),
      F i (j - 1) (by omega), r_st t i j, ha i j hp hno]
    generalize cell 505 t (i + 1) j = b1
    generalize cell 505 t (i - 1) j = b2
    generalize cell 505 t i (j + 1) = b3
    generalize cell 505 t i (j - 1) = b4
    revert b1 b2 b3 b4
    decide
  · -- the origin is OFF
    rw [r_st (t + 1) 0 0]
    simp only [zero_add, zero_sub]
    rw [O1, F 1 0 (by norm_num), F (-1) 0 (by norm_num), F 0 1 (by norm_num), F 0 (-1) (by norm_num),
      hb 1 (by norm_num) (by simp; omega), hb (-1) (by norm_num) (by simp; omega), r_swap t 0 1,
      r_swap t 0 (-1), hb 1 (by norm_num) (by simp; omega), hb (-1) (by norm_num) (by simp; omega)]
    decide
  · -- odd cells of the axis
    intro i hi habs
    push_cast at habs
    have hcase : |i| ≤ t ∨ i = t + 2 ∨ i = -(t + 2) := by
      cases abs_cases i <;> omega
    rcases hcase with hle | hpos | hneg
    · have n1 : cell 505 (t + 1) (i + 1) 0 = true := by
        by_cases h0 : i + 1 = 0
        · rw [h0]; exact O1
        · apply r_mixed t (i + 1) 0 (ha (i + 1) 0 (by omega) (by omega))
          · right; left; rw [show i + 1 - 1 = i by ring]; exact hb i hi hle
          · right; right; left; rw [zero_add]; exact hc (i + 1) (by omega) h0
      have n2 : cell 505 (t + 1) (i - 1) 0 = true := by
        by_cases h0 : i - 1 = 0
        · rw [h0]; exact O1
        · apply r_mixed t (i - 1) 0 (ha (i - 1) 0 (by omega) (by omega))
          · left; rw [show i - 1 + 1 = i by ring]; exact hb i hi hle
          · right; right; left; rw [zero_add]; exact hc (i - 1) (by omega) h0
      have n3 : cell 505 (t + 1) i 1 = true := by
        apply r_mixed t i 1 (ha i 1 (by omega) (by omega))
        · right; right; right; rw [sub_self]; exact hb i hi hle
        · by_cases h0 : i + 1 = 0
          · right; left; exact hc (i - 1) (by omega) (by omega)
          · left; exact hc (i + 1) (by omega) h0
      rw [r_st (t + 1) i 0]
      simp only [zero_add, zero_sub]
      rw [r_negj (t + 1) i 1, F i 0 (by omega), hb i hi hle, n1, n2, n3]
      decide
    · have hout : cell 505 t i 0 = true := by
        rw [r_lc t i 0 (r_lt2 _ _ _ (by simp only [abs_zero]; omega)), bgt]
      have hin : cell 505 t (i - 1 - 1) 0 = false :=
        hb (i - 1 - 1) (by omega) (by rw [abs_le]; omega)
      have n1 : cell 505 (t + 1) (i + 1) 0 = false := by
        rw [r_lc (t + 1) (i + 1) 0 (r_lt2 _ _ _ (by simp only [abs_zero]; omega)), bgt1]
      have n2 : cell 505 (t + 1) (i - 1) 0 = true := by
        apply r_mixed t (i - 1) 0 (ha (i - 1) 0 (by omega) (by omega))
        · right; left; exact hin
        · left; rw [show i - 1 + 1 = i by ring]; exact hout
      have n3 : cell 505 (t + 1) i 1 = false := by
        rw [r_lc (t + 1) i 1 (r_lt2 _ _ _ (by simp only [abs_zero, abs_one]; omega)), bgt1]
      rw [r_st (t + 1) i 0]
      simp only [zero_add, zero_sub]
      rw [r_negj (t + 1) i 1, F i 0 (by omega), hout, n1, n2, n3]
      decide
    · have hout : cell 505 t i 0 = true := by
        rw [r_lc t i 0 (r_lt2 _ _ _ (by simp only [abs_zero, abs_one]; omega)), bgt]
      have hin : cell 505 t (i + 1 + 1) 0 = false :=
        hb (i + 1 + 1) (by omega) (by rw [abs_le]; omega)
      have n1 : cell 505 (t + 1) (i - 1) 0 = false := by
        rw [r_lc (t + 1) (i - 1) 0 (r_lt2 _ _ _ (by simp only [abs_zero, abs_one]; omega)), bgt1]
      have n2 : cell 505 (t + 1) (i + 1) 0 = true := by
        apply r_mixed t (i + 1) 0 (ha (i + 1) 0 (by omega) (by omega))
        · left; exact hin
        · right; left; rw [show i + 1 - 1 = i by ring]; exact hout
      have n3 : cell 505 (t + 1) i 1 = false := by
        rw [r_lc (t + 1) i 1 (r_lt2 _ _ _ (by simp only [abs_zero, abs_one]; omega)), bgt1]
      rw [r_st (t + 1) i 0]
      simp only [zero_add, zero_sub]
      rw [r_negj (t + 1) i 1, F i 0 (by omega), hout, n1, n2, n3]
      decide
  · -- even cells of the row y = 1
    intro i hi hne
    by_cases hfar : (t : ℤ) + 3 ≤ |i|
    · rw [r_lc (t + 1 + 1) i 1 (by push_cast; rw [abs_one]; omega), bgt2]
    · have hself : cell 505 (t + 1) i 1 = false := by
        rw [F i 1 (by omega), hc i hi hne]; rfl
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have hk : |i + 1| ≤ t := by rw [abs_le]; cases abs_cases i <;> omega
        have n1 : cell 505 (t + 1) (i + 1) 1 = true := by
          apply r_mixed t (i + 1) 1 (ha (i + 1) 1 (by omega) (by omega))
          · right; right; right; rw [sub_self]; exact hb (i + 1) (by omega) hk
          · right; left; rw [show i + 1 - 1 = i by ring]; exact hc i hi hne
        have n2 : cell 505 (t + 1) i 0 = true := by
          apply r_mixed t i 0 (ha i 0 (by omega) (fun h => hne h.1))
          · left; exact hb (i + 1) (by omega) hk
          · right; right; left; rw [zero_add]; exact hc i hi hne
        rw [r_st (t + 1) i 1, hself, n1, show (1 : ℤ) - 1 = 0 by norm_num, n2]
        generalize cell 505 (t + 1) (i - 1) 1 = b1
        generalize cell 505 (t + 1) i (1 + 1) = b2
        revert b1 b2
        decide
      · have hk : |i - 1| ≤ t := by rw [abs_le]; cases abs_cases i <;> omega
        have n1 : cell 505 (t + 1) (i - 1) 1 = true := by
          apply r_mixed t (i - 1) 1 (ha (i - 1) 1 (by omega) (by omega))
          · right; right; right; rw [sub_self]; exact hb (i - 1) (by omega) hk
          · left; rw [show i - 1 + 1 = i by ring]; exact hc i hi hne
        have n2 : cell 505 (t + 1) i 0 = true := by
          apply r_mixed t i 0 (ha i 0 (by omega) (fun h => hne h.1))
          · right; left; exact hb (i - 1) (by omega) hk
          · right; right; left; rw [zero_add]; exact hc i hi hne
        rw [r_st (t + 1) i 1, hself, n1, show (1 : ℤ) - 1 = 0 by norm_num, n2]
        generalize cell 505 (t + 1) (i + 1) 1 = b1
        generalize cell 505 (t + 1) i (1 + 1) = b2
        revert b1 b2
        decide


theorem r_base : r_Inv 1 := by
  refine ⟨?_, by decide, ?_, ?_⟩
  · intro i j hp hno
    by_cases h : (1 : ℤ) < |i| + |j|
    · rw [r_lc 1 i j (by exact_mod_cast h)]; rfl
    · exfalso
      cases abs_cases i <;> cases abs_cases j <;> omega
  · intro i hi habs
    rcases (by rw [abs_le] at habs; push_cast at habs; omega : i = 1 ∨ i = -1) with rfl | rfl <;> decide
  · intro i hi hne
    rw [r_lc 1 i 1 (by rw [abs_one]; cases abs_cases i <;> omega)]; rfl

theorem r_inv (m : ℕ) : r_Inv (2 * m + 1) := by
  induction m with
  | zero => exact r_base
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring]
    exact r_step (2 * m + 1) (by omega) (by omega) ih

theorem r_odd_axis (m x : ℕ) (hx : x ≤ 2 * m + 1) :
    cell 505 (2 * m + 1) (-(x : ℤ)) 0 = decide (x % 2 = 0 ∧ x ≠ 0) := by
  obtain ⟨ha, ha0, hb, hc⟩ := r_inv m
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · by_cases h0 : x = 0
    · subst h0; simpa using ha0
    · rw [ha (-(x : ℤ)) 0 (by omega) (by omega)]
      simp [h, h0]
  · rw [hb (-(x : ℤ)) (by omega) (by rw [abs_neg, Nat.abs_cast]; exact_mod_cast hx)]
    simp [h]

theorem r_even_axis (m x : ℕ) (hx : x ≤ 2 * m + 2) :
    cell 505 (2 * m + 1 + 1) (-(x : ℤ)) 0 = true := by
  have hI := r_inv m
  have F := r_flip (2 * m + 1) (by omega) hI
  have O1 := r_org (2 * m + 1) (by omega) hI
  obtain ⟨ha, ha0, hb, hc⟩ := hI
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · by_cases h0 : x = 0
    · subst h0; simpa using O1
    · apply r_mixed _ _ _ (ha (-(x : ℤ)) 0 (by omega) (by omega))
      · left
        exact hb _ (by omega) (by rw [abs_le]; push_cast; omega)
      · right; right; left
        rw [zero_add]; exact hc _ (by omega) (by omega)
  · rw [F _ 0 (by omega), hb (-(x : ℤ)) (by omega) (by rw [abs_le]; push_cast; omega)]
    rfl

theorem r_a_sum (n : ℕ) :
    a n = ∑ m ∈ Finset.range (n + 1), if cell 505 n (-(m : ℤ)) 0 then (10 : ℤ) ^ m else 0 := by
  rw [← Finset.sum_range_reflect]
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega]
  congr 2
  push_cast [Nat.cast_sub (show k ≤ n by omega)]
  ring

theorem r_geom (N : ℕ) : 9 * (∑ m ∈ Finset.range N, (10 : ℤ) ^ m) + 1 = 10 ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; linarith

theorem r_geom2 (r : ℕ) : 99 * (∑ m ∈ Finset.range (2 * r + 2),
    (if m % 2 = 0 ∧ m ≠ 0 then (10 : ℤ) ^ m else 0)) + 100 = 10 ^ (2 * r + 2) := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 2 * (r + 1) + 2 = 2 * r + 2 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : (2 * r + 2) % 2 = 0 ∧ 2 * r + 2 ≠ 0 := by omega
    have e2 : ¬((2 * r + 2 + 1) % 2 = 0 ∧ 2 * r + 2 + 1 ≠ 0) := by omega
    rw [if_pos e1, if_neg e2, show (10 : ℤ) ^ (2 * r + 2 + 1 + 1) = 10 ^ (2 * r + 2) * 100 by ring]
    linarith

theorem r_even (m : ℕ) : 9 * a (2 * m) + 1 = 10 ^ (2 * m + 1) := by
  rw [r_a_sum]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; decide
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have : ∀ x ∈ Finset.range (2 * (k + 1) + 1),
        (if cell 505 (2 * (k + 1)) (-(x : ℤ)) 0 then (10 : ℤ) ^ x else 0) = 10 ^ x := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, r_even_axis k x (by omega), if_pos rfl]
    rw [Finset.sum_congr rfl this, r_geom]

theorem r_odd (m : ℕ) : 99 * a (2 * m + 1) + 100 = 10 ^ (2 * m + 2) := by
  rw [r_a_sum]
  have : ∀ x ∈ Finset.range (2 * m + 1 + 1),
      (if cell 505 (2 * m + 1) (-(x : ℤ)) 0 then (10 : ℤ) ^ x else 0) =
        if x % 2 = 0 ∧ x ≠ 0 then (10 : ℤ) ^ x else 0 := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [r_odd_axis m x (by omega)]
    by_cases hc : x % 2 = 0 ∧ x ≠ 0
    · simp [hc]
    · simp [hc]
  rw [Finset.sum_congr rfl this, r_geom2]


theorem r_even_q (n : ℕ) (he : Even n) : (a n : ℚ) = ((10 : ℚ) ^ (n + 1) - 1) / 9 := by
  obtain ⟨m, rfl⟩ := he
  have h := r_even m
  rw [show 2 * m = m + m by ring] at h
  have hq : (9 * (a (m + m) : ℚ) + 1) = 10 ^ (m + m + 1) := by exact_mod_cast h
  linarith

theorem r_odd_q (n : ℕ) (ho : Odd n) : (a n : ℚ) = 10 * ((10 : ℚ) ^ n - 10) / 99 := by
  obtain ⟨m, rfl⟩ := ho
  have h := r_odd m
  have hq : (99 * (a (2 * m + 1) : ℚ) + 100) = 10 ^ (2 * m + 2) := by exact_mod_cast h
  rw [show (10 : ℚ) ^ (2 * m + 2) = 10 * 10 ^ (2 * m + 1) by ring] at hq
  linarith

theorem r_rec (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = 101 * a (n - 2) - 100 * a (n - 4) := by
  rcases Nat.even_or_odd n with he | ho
  · have e1 : Even (n - 2) := by rcases he with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
    have e2 : Even (n - 4) := by rcases he with ⟨r, hr⟩; exact ⟨r - 2, by omega⟩
    rw [r_even_q n he, r_even_q (n - 2) e1, r_even_q (n - 4) e2,
      show n = (n - 4) + 4 by omega, show n - 4 + 4 - 2 = (n - 4) + 2 by omega,
      show n - 4 + 4 - 4 = n - 4 by omega]
    ring
  · have o1 : Odd (n - 2) := by rcases ho with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
    have o2 : Odd (n - 4) := by rcases ho with ⟨r, hr⟩; exact ⟨r - 2, by omega⟩
    rw [r_odd_q n ho, r_odd_q (n - 2) o1, r_odd_q (n - 4) o2,
      show n = (n - 4) + 4 by omega, show n - 4 + 4 - 2 = (n - 4) + 2 by omega,
      show n - 4 + 4 - 4 = n - 4 by omega]
    ring

theorem r_v0 : (a 0 : ℚ) = 1 := by rw [r_even_q 0 (by decide)]; norm_num
theorem r_v1 : (a 1 : ℚ) = 0 := by rw [r_odd_q 1 (by decide)]; norm_num
theorem r_v2 : (a 2 : ℚ) = 111 := by rw [r_even_q 2 (by decide)]; norm_num
theorem r_v3 : (a 3 : ℚ) = 100 := by rw [r_odd_q 3 (by decide)]; norm_num

theorem r_gf : PowerSeries.mk (fun n => (a n : ℚ)) *
    ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      1 + 10 * X ^ 2 + 100 * X ^ 3 := by
  set p : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ)) with hp
  have e1 : p * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      p - PowerSeries.C (101 : ℚ) * (p * X ^ 2) + PowerSeries.C (100 : ℚ) * (p * X ^ 4) := by
    rw [map_ofNat, map_ofNat]
    ring
  have e2 : (1 + 10 * X ^ 2 + 100 * X ^ 3 : PowerSeries ℚ) =
      1 + PowerSeries.C (10 : ℚ) * X ^ 2 + PowerSeries.C (100 : ℚ) * X ^ 3 := by
    simp only [map_ofNat]
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  by_cases hk : k < 4
  · interval_cases k <;> simp [r_v0, r_v1, r_v2, r_v3] <;> norm_num
  · rw [if_pos (show 2 ≤ k by omega), if_pos (show 4 ≤ k by omega),
      if_neg (show ¬ (k = 0) by omega), if_neg (show ¬ (k = 2) by omega),
      if_neg (show ¬ (k = 3) by omega), r_rec k (by omega)]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a282796.main :=
  ⟨OMA.Helpers.r_even_q, OMA.Helpers.r_odd_q, OMA.Helpers.r_rec, OMA.Helpers.r_gf⟩
