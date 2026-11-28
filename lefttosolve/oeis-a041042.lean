import OMAStatements.S_oeis_a041042
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a041042

theorem beta_add12 (n : ℕ) : beta (n + 12) = -2702 * beta (n + 6) - beta n := by
  rw [beta]

theorem block_succ1 (k : ℕ) :
    ((block (k + 1)).1 : ℤ) = 51 * ((block k).1 : ℤ) + 520 * ((block k).2 : ℤ) := by
  simp only [block]; push_cast; ring

theorem block_succ2 (k : ℕ) :
    ((block (k + 1)).2 : ℤ) = 260 * ((block k).1 : ℤ) + 2651 * ((block k).2 : ℤ) := by
  simp only [block]; push_cast; ring

/-- The four subsequences of `beta` that carry the numerators, with their signs. -/
def Q (k : ℕ) : Prop :=
  beta (6 * k + 1) = (-1) ^ k * ((block k).1 : ℤ) ∧
  beta (6 * k + 2) = (-1) ^ k * ((block k).2 : ℤ) ∧
  beta (6 * k + 4) = (-1) ^ k * (((block k).1 : ℤ) + 10 * ((block k).2 : ℤ)) ∧
  beta (6 * k + 6) = -(-1) ^ k * (5 * ((block k).1 : ℤ) + 51 * ((block k).2 : ℤ))

theorem key (k : ℕ) : Q k ∧ Q (k + 1) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [Q, block]; norm_num [beta]
    · simp only [Q, block]; norm_num [beta]
  | succ k ih =>
    obtain ⟨⟨a1, a2, a4, a6⟩, ⟨b1, b2, b4, b6⟩⟩ := ih
    refine ⟨⟨b1, b2, b4, b6⟩, ?_⟩
    have e1 : 6 * (k + 1 + 1) + 1 = (6 * k + 1) + 12 := by ring
    have e2 : 6 * (k + 1 + 1) + 2 = (6 * k + 2) + 12 := by ring
    have e4 : 6 * (k + 1 + 1) + 4 = (6 * k + 4) + 12 := by ring
    have e6 : 6 * (k + 1 + 1) + 6 = (6 * k + 6) + 12 := by ring
    have f1 : 6 * k + 1 + 6 = 6 * (k + 1) + 1 := by ring
    have f2 : 6 * k + 2 + 6 = 6 * (k + 1) + 2 := by ring
    have f4 : 6 * k + 4 + 6 = 6 * (k + 1) + 4 := by ring
    have f6 : 6 * k + 6 + 6 = 6 * (k + 1) + 6 := by ring
    rw [block_succ1] at b1 b4 b6
    rw [block_succ2] at b2 b4 b6
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, beta_add12, f1, b1, a1]
      simp only [block_succ1, block_succ2]; ring
    · rw [e2, beta_add12, f2, b2, a2]
      simp only [block_succ1, block_succ2]; ring
    · rw [e4, beta_add12, f4, b4, a4]
      simp only [block_succ1, block_succ2]; ring
    · rw [e6, beta_add12, f6, b6, a6]
      simp only [block_succ1, block_succ2]; ring

theorem abs_sign (k : ℕ) (z : ℤ) : |(-1) ^ k * z| = |z| := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a041042.main := by
  intro n
  obtain ⟨⟨h1, h2, h4, h6⟩, -⟩ := key (n / 4)
  unfold OMA.S_oeis_a041042.numerator OMA.S_oeis_a041042.part
  have hx : (0 : ℤ) ≤ ((OMA.S_oeis_a041042.block (n / 4)).1 : ℤ) := by positivity
  have hy : (0 : ℤ) ≤ ((OMA.S_oeis_a041042.block (n / 4)).2 : ℤ) := by positivity
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
    rw [h]
  · refine ⟨6 * (n / 4) + 1, ?_⟩
    rw [h1, abs_sign, abs_of_nonneg hx]
    simp [OMA.S_oeis_a041042.weights]
  · refine ⟨6 * (n / 4) + 2, ?_⟩
    rw [h2, abs_sign, abs_of_nonneg hy]
    simp [OMA.S_oeis_a041042.weights]
  · refine ⟨6 * (n / 4) + 4, ?_⟩
    rw [h4, abs_sign, abs_of_nonneg (by positivity)]
    simp [OMA.S_oeis_a041042.weights]
  · refine ⟨6 * (n / 4) + 6, ?_⟩
    rw [h6, neg_mul, abs_neg, abs_sign, abs_of_nonneg (by positivity)]
    simp [OMA.S_oeis_a041042.weights]
