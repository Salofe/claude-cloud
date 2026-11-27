import OMAReductions.R_Erdos242_erdos_242_variants_schinzel_generalization_R1

/-!
# Step H2 of the reduction Erdos242.erdos_242.variants.schinzel_generalization.R1

Write n = a q + r with q = n / a at least 2. Explicit three-term expansions:
* r = 0: a / n = 1 / q = 1 / (2q) + 1 / (3q) + 1 / (6q).
* r = a - 1: n + 1 = a (q + 1), so with N = n (q + 1),
  a / n = 1 / (q + 1) + 1 / N = 1 / (q + 1) + 1 / (N + 1) + 1 / (N (N + 1)).
* r = a - 2: n + 2 = a (q + 1), so a / n = 1 / (q + 1) + 2 / M with M = n (q + 1);
  for M = 2K use 1 / (K + 1) + 1 / (K (K + 1)), for M = 2K + 1 use
  1 / (K + 1) + 1 / ((K + 1) M).
-/

namespace OMA.Helpers

theorem e242_case0 (a n q : ℕ) (ha : 0 < a) (hq : 2 ≤ q) (hn : n = a * q) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a/n : ℚ) = 1/x+1/y+1/z := by
  refine ⟨2*q, 3*q, 6*q, by omega, by omega, by omega, ?_⟩
  subst hn
  have ha' : (a:ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hq' : (q:ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  push_cast
  field_simp
  ring

theorem e242_case1 (a n q : ℕ) (hq : 2 ≤ q) (hn : n + 1 = a * (q + 1)) (hn2 : 2 ≤ n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a/n : ℚ) = 1/x+1/y+1/z := by
  have hN : q + 1 ≤ n * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hN2 : 2 ≤ n * (q + 1) := by nlinarith
  refine ⟨q + 1, n * (q + 1) + 1, (n * (q + 1)) * (n * (q + 1) + 1), by omega, by omega,
    by nlinarith, ?_⟩
  have hn' : (n:ℚ) + 1 = a * (q + 1) := by exact_mod_cast hn
  have h0 : (n:ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : (q:ℚ) + 1 ≠ 0 := by positivity
  have h2 : (n:ℚ) * (q + 1) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-((n:ℚ) * (q + 1) + 1)) * hn'

theorem e242_case2 (a n q : ℕ) (ha : 3 ≤ a) (hq : 2 ≤ q) (hn : n + 2 = a * (q + 1)) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a/n : ℚ) = 1/x+1/y+1/z := by
  have hn' : (n:ℚ) + 2 = a * (q + 1) := by exact_mod_cast hn
  have hnpos : 3 * (q + 1) ≤ n + 2 := by rw [hn]; exact Nat.mul_le_mul_right _ ha
  have h0 : (n:ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : (q:ℚ) + 1 ≠ 0 := by positivity
  obtain ⟨K, hK | hK⟩ := Nat.even_or_odd' (n * (q + 1))
  · have hKq : q < K := by nlinarith
    refine ⟨q + 1, K + 1, K * (K + 1), by omega, by omega, by nlinarith, ?_⟩
    have hK' : (n:ℚ) * (q + 1) = 2 * K := by exact_mod_cast hK
    have h2 : (K:ℚ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    push_cast
    field_simp
    linear_combination (-(K:ℚ) * (K + 1)) * hn' - ((K:ℚ) + 1) * hK'
  · have hKq : q < K := by nlinarith
    have hM : 2 ≤ n * (q + 1) := by omega
    refine ⟨q + 1, K + 1, (K + 1) * (n * (q + 1)), by omega, by omega, by nlinarith, ?_⟩
    have hK' : (n:ℚ) * (q + 1) = 2 * K + 1 := by exact_mod_cast hK
    push_cast
    field_simp
    linear_combination (-((K:ℚ) + 1)) * hn' - hK'

theorem e242_H2 : ∀ a n : ℕ, 0 < a → 2*a ≤ n → (n%a = 0 ∨ a ≤ n%a+2) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a/n : ℚ) = 1/x+1/y+1/z := by
  intro a n ha hn hr
  have hdm := Nat.div_add_mod n a
  have hq : 2 ≤ n / a := (Nat.le_div_iff_mul_le ha).2 (by linarith)
  have hlt := Nat.mod_lt n ha
  rcases Nat.eq_zero_or_pos (n % a) with h0 | hpos
  · exact e242_case0 a n (n / a) ha hq (by rw [h0] at hdm; linarith)
  · rcases hr with hr | hr
    · omega
    · rcases (show n % a + 1 = a ∨ n % a + 2 = a by omega) with h1 | h2
      · exact e242_case1 a n (n / a) hq (by rw [mul_add, mul_one]; omega) (by nlinarith)
      · exact e242_case2 a n (n / a) (by omega) hq (by rw [mul_add, mul_one]; omega)

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1.H2 :=
  OMA.Helpers.e242_H2
