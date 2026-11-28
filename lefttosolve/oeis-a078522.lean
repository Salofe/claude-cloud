import OMAStatements.S_oeis_a078522
import Mathlib

namespace OMA.Helpers

/-- Solutions of `X^2 + (X+1)^2 = Z^2`: `(0,1), (3,5), (20,29), ...`. -/
def xz : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | i + 1 => (3 * (xz i).1 + 2 * (xz i).2 + 1, 4 * (xz i).1 + 3 * (xz i).2 + 2)

theorem xz_pell (i : ℕ) : (xz i).2 ^ 2 = (xz i).1 ^ 2 + ((xz i).1 + 1) ^ 2 := by
  induction i with
  | zero => simp [xz]
  | succ i ih =>
    simp only [xz]
    nlinarith [ih]

theorem p_eq (m i : ℕ) :
    OMA.S_oeis_a078522.p m i = (m : ℤ) ^ 2 * (2 * (xz i).1 * ((xz i).1 + 1)) ∧
    OMA.S_oeis_a078522.p m (i + 1) = (m : ℤ) ^ 2 * (2 * (xz (i + 1)).1 * ((xz (i + 1)).1 + 1)) := by
  induction i with
  | zero => simp [OMA.S_oeis_a078522.p, xz]; ring
  | succ i ih =>
    refine ⟨ih.2, ?_⟩
    have hp := xz_pell i
    have hz : ((xz i).2 : ℤ) ^ 2 = ((xz i).1 : ℤ) ^ 2 + ((xz i).1 + 1) ^ 2 := by exact_mod_cast hp
    rw [show i + 1 + 1 = i + 2 from rfl, OMA.S_oeis_a078522.p, ih.1, ih.2]
    simp only [xz]
    push_cast
    linear_combination (-(m : ℤ) ^ 2 * 16) * hz

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a078522.main := by
  intro m i
  refine ⟨2 * m * (OMA.Helpers.xz i).1, 2 * m * (OMA.Helpers.xz i).2, ?_, ?_⟩
  · have := OMA.Helpers.xz_pell i
    have e : 2 * m * (OMA.Helpers.xz i).1 + 2 * m = 2 * m * ((OMA.Helpers.xz i).1 + 1) := by ring
    rw [e, mul_pow (2 * m) _ 2, mul_pow (2 * m) _ 2, mul_pow (2 * m) _ 2, this]; ring
  · rw [(OMA.Helpers.p_eq m i).1]
    push_cast
    ring
