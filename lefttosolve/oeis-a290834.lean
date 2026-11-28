import OMAStatements.S_oeis_a290834
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a290834

theorem a290834_nb (x y : ℤ) (t : ℕ) (h : ((t + 1 : ℕ) : ℤ) < |x| + |y|) :
    (t : ℤ) < |x + 1| + |y| ∧ (t : ℤ) < |x - 1| + |y| ∧ (t : ℤ) < |x| + |y + 1| ∧
      (t : ℤ) < |x| + |y - 1| ∧ (t : ℤ) < |x| + |y| := by
  push_cast at h
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases y with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (x + 1) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
    rcases abs_cases (x - 1) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
    rcases abs_cases (y + 1) with ⟨h5, _⟩ | ⟨h5, _⟩ <;>
    rcases abs_cases (y - 1) with ⟨h6, _⟩ | ⟨h6, _⟩ <;> omega

theorem a290834_far : ∀ (t : ℕ) (p : ℤ × ℤ), (t : ℤ) < |p.1| + |p.2| →
    state t p = decide (t ≠ 0)
  | 0, (x, y), h => by
    have : (x, y) ≠ ((0 : ℤ), (0 : ℤ)) := by
      intro e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp at h
    simp [state, this]
  | t + 1, (x, y), h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := a290834_nb x y t h
    have e1 := a290834_far t (x + 1, y) h1
    have e2 := a290834_far t (x - 1, y) h2
    have e3 := a290834_far t (x, y + 1) h3
    have e4 := a290834_far t (x, y - 1) h4
    have e5 := a290834_far t (x, y) h5
    simp only [state, nbrs, List.countP_cons, List.countP_nil, e1, e2, e3, e4, e5]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · decide
    · have : t ≠ 0 := by omega
      simp only [this, ne_eq, not_false_eq_true, decide_true, add_eq_zero, one_ne_zero,
        and_false]
      decide

theorem a290834_box : ∀ i : Fin 11, ∀ j : Fin 11, state 5 ((i : ℤ) - 5, (j : ℤ) - 5) = true := by
  decide +kernel

theorem a290834_five (p : ℤ × ℤ) : state 5 p = true := by
  obtain ⟨x, y⟩ := p
  by_cases h : (5 : ℤ) < |x| + |y|
  · rw [a290834_far 5 (x, y) (by exact_mod_cast h)]
    decide
  · have hx : -5 ≤ x ∧ x ≤ 5 := by
      rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases y with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        omega
    have hy : -5 ≤ y ∧ y ≤ 5 := by
      rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases y with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        omega
    have := a290834_box ⟨(x + 5).toNat, by omega⟩ ⟨(y + 5).toNat, by omega⟩
    simp only at this
    rwa [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
      show x + 5 - 5 = x by ring, show y + 5 - 5 = y by ring] at this

theorem a290834_on : ∀ n : ℕ, 5 ≤ n → ∀ p : ℤ × ℤ, state n p = true
  | 0, h, _ => by omega
  | n + 1, h, p => by
    rcases Nat.eq_or_lt_of_le h with e | h'
    · rw [← e]
      exact a290834_five p
    · have ih := a290834_on n (by omega)
      simp only [state, nbrs, List.countP_cons, List.countP_nil, ih]
      decide

theorem a290834_a_ge (n : ℕ) (hn : 5 ≤ n) : (a n : ℚ) = (10 ^ (1 + n) - 1) / 9 := by
  have : a n = ∑ k ∈ Finset.range (n + 1), 10 ^ k := by
    unfold a
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [a290834_on n hn]
    rfl
  rw [this]
  push_cast
  rw [geom_sum_eq (by norm_num : (10 : ℚ) ≠ 1), add_comm 1 n]
  norm_num

theorem a290834_small : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 101 ∧ a 3 = 1111 ∧ a 4 = 11100 := by
  decide +kernel

theorem a290834_gf_aux (g : ℕ → ℚ) (h0 : g 0 = 1) (h1 : g 1 = 10) (h2 : g 2 = 101)
    (h3 : g 3 = 1111) (h4 : g 4 = 11100) (hz : ∀ n : ℕ, 5 ≤ n → g n = (10 ^ (1 + n) - 1) / 9) :
    PowerSeries.mk g * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X)) =
      1 - PowerSeries.X + PowerSeries.X ^ 2 + 100 * PowerSeries.X ^ 3 - 111 * PowerSeries.X ^ 4
        + 121 * PowerSeries.X ^ 5 - 110 * PowerSeries.X ^ 6 := by
  have e1 : PowerSeries.mk g * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X))
      = PowerSeries.mk g - PowerSeries.C (11 : ℚ) * (PowerSeries.mk g * PowerSeries.X ^ 1)
        + PowerSeries.C (10 : ℚ) * (PowerSeries.mk g * PowerSeries.X ^ 2) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 - PowerSeries.X + PowerSeries.X ^ 2 + 100 * PowerSeries.X ^ 3
      - 111 * PowerSeries.X ^ 4 + 121 * PowerSeries.X ^ 5 - 110 * PowerSeries.X ^ 6 : PowerSeries ℚ)
      = PowerSeries.X ^ 0 - PowerSeries.X ^ 1 + PowerSeries.X ^ 2
        + PowerSeries.C (100 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (111 : ℚ) * PowerSeries.X ^ 4
        + PowerSeries.C (121 : ℚ) * PowerSeries.X ^ 5
        - PowerSeries.C (110 : ℚ) * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge k 7 with hk | hk
  · interval_cases k
    · simp [h0]
    · norm_num [h0, h1]
    · simp [h0, h1, h2]; norm_num
    · simp [h1, h2, h3]; norm_num
    · simp [h2, h3, h4]; norm_num
    · simp [h3, h4, hz 5 le_rfl]; norm_num
    · simp [h4, hz 5 le_rfl, hz 6 (by norm_num)]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    have c1 : 1 ≤ m + 7 := by omega
    have c2 : 2 ≤ m + 7 := by omega
    have d0 : m + 7 ≠ 0 := by omega
    have d1 : m + 7 ≠ 1 := by omega
    have d2 : m + 7 ≠ 2 := by omega
    have d3 : m + 7 ≠ 3 := by omega
    have d4 : m + 7 ≠ 4 := by omega
    have d5 : m + 7 ≠ 5 := by omega
    have d6 : m + 7 ≠ 6 := by omega
    simp only [c1, c2, d0, d1, d2, d3, d4, d5, d6, if_true, if_false]
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega]
    rw [hz (m + 7) (by omega), hz (m + 6) (by omega), hz (m + 5) (by omega)]
    rw [show 1 + (m + 7) = (m + 5) + 3 by omega, show 1 + (m + 6) = (m + 5) + 2 by omega,
      show 1 + (m + 5) = (m + 5) + 1 by omega]
    simp only [pow_add]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a290834.main := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := OMA.Helpers.a290834_small
  have hz := OMA.Helpers.a290834_a_ge
  refine ⟨?_, fun n hn => hz n (by omega), ?_⟩
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    exact OMA.Helpers.a290834_gf_aux (fun n => (OMA.S_oeis_a290834.a n : ℚ))
      (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4]) hz
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega]
    have q : ((OMA.S_oeis_a290834.a (m + 7) : ℤ) : ℚ) = 11 * ((OMA.S_oeis_a290834.a (m + 6) : ℤ) : ℚ)
        - 10 * ((OMA.S_oeis_a290834.a (m + 5) : ℤ) : ℚ) := by
      push_cast
      rw [hz (m + 7) (by omega), hz (m + 6) (by omega), hz (m + 5) (by omega)]
      rw [show 1 + (m + 7) = (m + 5) + 3 by omega, show 1 + (m + 6) = (m + 5) + 2 by omega,
        show 1 + (m + 5) = (m + 5) + 1 by omega]
      simp only [pow_add]
      ring
    exact_mod_cast q
