import OMAStatements.S_oeis_a273406
import Mathlib

/-!
Proof of the conjectures of OEIS A273406 (partial sums of the ON-cell counts of Rule 673 on the
5-celled von Neumann neighbourhood, started from a single ON cell).

673 = 1010100001 in binary: the new value of a cell with own value c and k ON neighbours is bit
2k + c, so an OFF cell turns ON exactly when it has no ON neighbour, and an ON cell stays ON
exactly when it has at least two ON neighbours. From stage 1 on, every cell is ON except the four
orthogonal neighbours of the origin, and except the origin itself at odd stages (the origin has
no ON neighbour, so it flips at each step). Hence the count over the (2s+1) x (2s+1) square is
(2s+1)^2 - 5 at odd s and (2s+1)^2 - 4 at even s >= 2, which gives Barker's closed form; the
other closed forms, the recurrence and the generating function follow from it.
-/

namespace OMA.Helpers

open OMA.S_oeis_a273406 PowerSeries

/-- The four orthogonal neighbours of the origin. -/
abbrev a273406_P (x y : ℤ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)

/-- The configuration at a stage `t ≥ 1`: everything ON except the four neighbours of the
origin, and the origin itself at odd stages. -/
def a273406_C (t : ℕ) (p : ℤ × ℤ) : Bool :=
  !(decide (a273406_P p.1 p.2)) && (!(decide (p.1 = 0 ∧ p.2 = 0)) || decide (t % 2 = 0))

theorem a273406_state_one (p : ℤ × ℤ) : state 1 p = a273406_C 1 p := by
  obtain ⟨x, y⟩ := p
  simp only [state, nbrs, a273406_C, a273406_P, List.countP_cons, List.countP_nil, Prod.mk.injEq]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    decide
  by_cases h1 : (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)
  · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · have e1 : ¬ (x + 1 = 0 ∧ y = 0) := by omega
    have e2 : ¬ (x - 1 = 0 ∧ y = 0) := by omega
    have e3 : ¬ (x = 0 ∧ y + 1 = 0) := by omega
    have e4 : ¬ (x = 0 ∧ y - 1 = 0) := by omega
    simp only [h0, h1, e1, e2, e3, e4, decide_false]
    decide

theorem a273406_state_step (t : ℕ) (ih : ∀ p, state t p = a273406_C t p)
    (p : ℤ × ℤ) : state (t + 1) p = a273406_C (t + 1) p := by
  obtain ⟨x, y⟩ := p
  have hs : state (t + 1) (x, y) =
      rule (a273406_C t (x, y)) ((nbrs (x, y)).countP (fun q => a273406_C t q)) := by
    simp only [state, ih]
  rw [hs]
  simp only [nbrs, a273406_C, List.countP_cons, List.countP_nil]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      simp only [h, h']
      decide
    · have h' : (t + 1) % 2 = 0 := by omega
      simp only [h, h']
      decide
  by_cases h1 : (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)
  · rcases Nat.mod_two_eq_zero_or_one t with h | h <;>
    · have h' : (t + 1) % 2 = 1 - t % 2 := by omega
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [h, h'] <;> decide
  · have e1 : ¬ (x + 1 = 0 ∧ y = 0) := by omega
    have e2 : ¬ (x - 1 = 0 ∧ y = 0) := by omega
    have e3 : ¬ (x = 0 ∧ y + 1 = 0) := by omega
    have e4 : ¬ (x = 0 ∧ y - 1 = 0) := by omega
    simp only [h0, h1, e1, e2, e3, e4, decide_false, Bool.not_false, Bool.true_or,
      Bool.and_true]
    by_cases g1 : a273406_P (x + 1) y <;> by_cases g2 : a273406_P (x - 1) y <;>
      by_cases g3 : a273406_P x (y + 1) <;> by_cases g4 : a273406_P x (y - 1) <;>
      simp only [g1, g2, g3, g4, decide_true, decide_false] <;>
      first | decide | (exfalso; simp only [a273406_P] at *; omega)

theorem a273406_state (t : ℕ) : ∀ p, state (t + 1) p = a273406_C (t + 1) p := by
  induction t with
  | zero => exact a273406_state_one
  | succ t ih => exact a273406_state_step (t + 1) ih


/-- The number of ON cells of stage `s` in the square `[-s, s]²`. -/
def a273406_cnt (s : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * s + 1), ∑ y ∈ Finset.range (2 * s + 1),
    if state s ((x : ℤ) - s, (y : ℤ) - s) then 1 else 0

theorem a273406_a_eq (n : ℕ) : a n = ∑ s ∈ Finset.range (n + 1), a273406_cnt s := rfl

theorem a273406_cnt_zero : a273406_cnt 0 = 1 := by
  decide

theorem a273406_cnt_succ (m : ℕ) :
    a273406_cnt (m + 1) + 4 + (if (m + 1) % 2 = 1 then 1 else 0) = (2 * (m + 1) + 1) ^ 2 := by
  unfold a273406_cnt
  simp only [a273406_state m]
  set N := m + 1 with hN
  set R := Finset.range (2 * N + 1) with hR
  rw [← Finset.sum_product' (f := fun (i j : ℕ) =>
    if a273406_C N ((i : ℤ) - N, (j : ℤ) - N) = true then 1 else 0)]
  rw [Finset.sum_boole, Nat.cast_id]
  have hsplit := Finset.card_filter_add_card_filter_not (s := R ×ˢ R)
    (fun p : ℕ × ℕ => a273406_C N ((p.1 : ℤ) - N, (p.2 : ℤ) - N) = true)
  have hcard : (R ×ˢ R).card = (2 * N + 1) ^ 2 := by
    rw [Finset.card_product, hR, Finset.card_range, sq]
  rw [hcard] at hsplit
  rcases Nat.mod_two_eq_zero_or_one N with hp | hp
  · have hneg : (R ×ˢ R).filter
        (fun p : ℕ × ℕ => ¬ a273406_C N ((p.1 : ℤ) - N, (p.2 : ℤ) - N) = true) =
        {(N + 1, N), (N - 1, N), (N, N + 1), (N, N - 1)} := by
      ext ⟨i, j⟩
      simp only [hR, Finset.mem_filter, Finset.mem_product, Finset.mem_range, a273406_C,
        a273406_P, hp, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Bool.not_eq_true,
        Bool.and_eq_false_iff, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
        Bool.not_true, decide_eq_true_eq, decide_eq_false_iff_not, Bool.true_eq_false,
        Bool.false_eq_true, and_false, and_true, or_false, Nat.one_ne_zero, decide_true,
        decide_false]
      omega
    have h4 : ({(N + 1, N), (N - 1, N), (N, N + 1), (N, N - 1)} : Finset (ℕ × ℕ)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
      all_goals simp only [ne_eq, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
      all_goals omega
    rw [hneg, h4] at hsplit
    rw [if_neg (by omega)]
    omega
  · have hneg : (R ×ˢ R).filter
        (fun p : ℕ × ℕ => ¬ a273406_C N ((p.1 : ℤ) - N, (p.2 : ℤ) - N) = true) =
        {(N, N), (N + 1, N), (N - 1, N), (N, N + 1), (N, N - 1)} := by
      ext ⟨i, j⟩
      simp only [hR, Finset.mem_filter, Finset.mem_product, Finset.mem_range, a273406_C,
        a273406_P, hp, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Bool.not_eq_true,
        Bool.and_eq_false_iff, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
        Bool.not_true, decide_eq_true_eq, decide_eq_false_iff_not, Bool.true_eq_false,
        Bool.false_eq_true, and_false, and_true, or_false, Nat.one_ne_zero, decide_true,
        decide_false]
      omega
    have h5 : ({(N, N), (N + 1, N), (N - 1, N), (N, N + 1), (N, N - 1)} :
        Finset (ℕ × ℕ)).card = 5 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_pair]
      all_goals simp only [ne_eq, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
      all_goals omega
    rw [hneg, h5] at hsplit
    rw [if_pos (by omega)]
    omega


theorem a273406_closed (n : ℕ) :
    (a n : ℚ) = (9 + 3 * (-1) ^ n - 10 * n + 48 * n ^ 2 + 16 * n ^ 3) / 12 := by
  induction n with
  | zero =>
    rw [a273406_a_eq, Finset.sum_range_one, a273406_cnt_zero]
    norm_num
  | succ n ih =>
    have hs : a (n + 1) = a n + a273406_cnt (n + 1) := by
      rw [a273406_a_eq, a273406_a_eq, Finset.sum_range_succ]
    have hc := a273406_cnt_succ n
    rw [hs]
    push_cast
    rw [ih]
    rcases Nat.even_or_odd n with he | ho
    · rw [if_pos (by have := Nat.even_iff.mp he; omega)] at hc
      have hq : ((a273406_cnt (n + 1) : ℕ) : ℚ) + 4 + 1 = (2 * ((n : ℚ) + 1) + 1) ^ 2 := by
        exact_mod_cast hc
      rw [pow_succ (-1 : ℚ) n, he.neg_one_pow]
      linear_combination hq
    · rw [if_neg (by have := Nat.odd_iff.mp ho; omega)] at hc
      have hq : ((a273406_cnt (n + 1) : ℕ) : ℚ) + 4 + 0 = (2 * ((n : ℚ) + 1) + 1) ^ 2 := by
        exact_mod_cast hc
      rw [pow_succ (-1 : ℚ) n, ho.neg_one_pow]
      linear_combination hq

theorem a273406_rec (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) - 2 * a (n - 3) + 3 * a (n - 4) - a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega]
  have h : (((a (m + 5) : ℤ)) : ℚ) =
      ((3 * a (m + 4) - 2 * a (m + 3) - 2 * a (m + 2) + 3 * a (m + 1) - a m : ℤ) : ℚ) := by
    push_cast
    rw [a273406_closed, a273406_closed, a273406_closed, a273406_closed, a273406_closed,
      a273406_closed]
    push_cast
    ring
  exact_mod_cast h

theorem a273406_gf :
    A = (1 + 2 * X + 13 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4) * ((1 - X) ^ 4 * (1 + X))⁻¹ := by
  have hD : constantCoeff ((1 - X) ^ 4 * (1 + X) : ℚ⟦X⟧) ≠ 0 := by
    simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  have hA := a273406_closed
  have v0 : (a 0 : ℚ) = 1 := by rw [hA]; norm_num
  have v1 : (a 1 : ℚ) = 5 := by rw [hA]; norm_num
  have v2 : (a 2 : ℚ) = 26 := by rw [hA]; norm_num
  have v3 : (a 3 : ℚ) = 70 := by rw [hA]; norm_num
  have v4 : (a 4 : ℚ) = 147 := by rw [hA]; norm_num
  have e : A * ((1 - X) ^ 4 * (1 + X)) =
      X ^ 0 * A - C (3 : ℚ) * (X ^ 1 * A) + C (2 : ℚ) * (X ^ 2 * A)
      + C (2 : ℚ) * (X ^ 3 * A) - C (3 : ℚ) * (X ^ 4 * A) + X ^ 5 * A := by
    simp only [map_ofNat]
    ring
  have e2 : (1 + 2 * X + 13 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4 : ℚ⟦X⟧) =
      C (1 : ℚ) * X ^ 0 + C (2 : ℚ) * X ^ 1 + C (13 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3
        - C (4 : ℚ) * X ^ 4 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_X_pow_mul', A, PowerSeries.coeff_mk, mul_ite, mul_one, mul_zero]
  by_cases hk : 5 ≤ k
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
    have i0 : 0 ≤ m + 5 := by omega
    have i1 : 1 ≤ m + 5 := by omega
    have i2 : 2 ≤ m + 5 := by omega
    have i3 : 3 ≤ m + 5 := by omega
    have i4 : 4 ≤ m + 5 := by omega
    have i5 : 5 ≤ m + 5 := by omega
    have n0 : m + 5 ≠ 0 := by omega
    have n1 : m + 5 ≠ 1 := by omega
    have n2 : m + 5 ≠ 2 := by omega
    have n3 : m + 5 ≠ 3 := by omega
    have n4 : m + 5 ≠ 4 := by omega
    simp only [i0, i1, i2, i3, i4, i5, n0, n1, n2, n3, n4, ↓reduceIte,
      show m + 5 - 5 = m by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 1 = m + 4 by omega, show m + 5 - 0 = m + 5 by omega]
    rw [hA (m + 5), hA (m + 4), hA (m + 3), hA (m + 2), hA (m + 1), hA m]
    push_cast
    ring
  · interval_cases k <;> simp [v0, v1, v2, v3, v4] <;> norm_num

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a273406.main := by
  refine ⟨OMA.Helpers.a273406_closed, ?_, ?_, OMA.Helpers.a273406_rec, OMA.Helpers.a273406_gf⟩
  · intro n hn
    rw [OMA.Helpers.a273406_closed, hn.neg_one_pow]
    ring
  · intro n hn
    rw [OMA.Helpers.a273406_closed, hn.neg_one_pow]
    ring
