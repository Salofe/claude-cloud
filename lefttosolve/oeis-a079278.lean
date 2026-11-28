import OMAStatements.S_oeis_a079278
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a079278

/-- Numerator and denominator of `b (k + 1)`, as a pair. -/
def pq : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | k + 1 => ((pq k).1 * ((pq k).1 + 2 * (pq k).2), (pq k).2 * ((pq k).1 + (pq k).2))

theorem pq_succ (k : ℕ) : pq (k + 1) =
    ((pq k).1 * ((pq k).1 + 2 * (pq k).2), (pq k).2 * ((pq k).1 + (pq k).2)) := rfl

theorem pq_pos (k : ℕ) : 0 < (pq k).1 ∧ 0 < (pq k).2 := by
  induction k with
  | zero => exact ⟨by simp [pq], by simp [pq]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [pq_succ]
    exact ⟨by positivity, by positivity⟩

theorem pq_cop (k : ℕ) : IsCoprime (pq k).1 (pq k).2 := by
  induction k with
  | zero => exact isCoprime_one_left
  | succ k ih =>
    rw [pq_succ]
    set p := (pq k).1
    set q := (pq k).2
    have h1 : IsCoprime p (p + q) := by
      have : p + q = q + p * 1 := by ring
      rw [this]
      exact ih.add_mul_left_right 1
    have h2 : IsCoprime (p + 2 * q) q := by
      have : p + 2 * q = p + q * 2 := by ring
      rw [this]
      exact ih.add_mul_left_left 2
    have h3 : IsCoprime (p + 2 * q) (p + q) := by
      have hqp : IsCoprime q (p + q) := by
        have : p + q = p + q * 1 := by ring
        rw [this]
        exact ih.symm.add_mul_left_right 1
      have : p + 2 * q = q + (p + q) * 1 := by ring
      rw [this]
      exact hqp.add_mul_left_left 1
    exact (ih.mul_right h1).mul_left (h2.mul_right h3)

theorem b_eq (k : ℕ) : b (k + 1) = ((pq k).1 : ℚ) / ((pq k).2 : ℚ) := by
  induction k with
  | zero => simp [pq, b]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := pq_pos k
    have h1' : (0 : ℚ) < (pq k).1 := by exact_mod_cast h1
    have h2' : (0 : ℚ) < (pq k).2 := by exact_mod_cast h2
    show b (k + 1) + 1 / (1 + 1 / b (k + 1)) = _
    rw [ih, pq_succ]
    push_cast
    field_simp
    ring

theorem a_eq (k : ℕ) : (a (k + 1) : ℚ) = ((pq k).2 : ℚ) := by
  have h := Rat.den_div_eq_of_coprime (pq_pos k).2
    (Int.isCoprime_iff_gcd_eq_one.mp (pq_cop k))
  unfold a
  rw [b_eq]
  exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a079278.main := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e1 : k + 2 + 1 = (k + 2) + 1 := rfl
  have e2 : k + 2 - 1 = k + 1 := by omega
  rw [e2, show k + 2 = (k + 1) + 1 from rfl, a_eq, a_eq, a_eq, pq_succ, pq_succ]
  obtain ⟨h1, h2⟩ := pq_pos k
  have h2' : (0 : ℚ) < (pq k).2 := by exact_mod_cast h2
  push_cast
  field_simp
  ring
