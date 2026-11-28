import OMAStatements.S_mo_250663
import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace OMA.Helpers

theorem diag_inv (v w : Fin 2 → ℝ) (h : ∀ i, v i * w i = 1) :
    (diagonal v)⁻¹ = diagonal w := by
  apply Matrix.inv_eq_right_inv
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem norm_vec (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    ‖(![a, b] : Fin 2 → ℝ)‖ = b := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by linarith)).2 ?_
    intro i
    fin_cases i
    · simp [abs_of_nonneg ha, hab]
    · simp [abs_of_nonneg hb]
  · have := norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 1
    simpa [abs_of_nonneg hb] using this

theorem norm_vec' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a) :
    ‖(![a, b] : Fin 2 → ℝ)‖ = a := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by linarith)).2 ?_
    intro i
    fin_cases i
    · simp [abs_of_nonneg ha]
    · simp [abs_of_nonneg hb, hab]
  · have := norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 0
    simpa [abs_of_nonneg ha] using this

end OMA.Helpers

open OMA.Helpers in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_250663.main) := by
  intro h
  have hA : (diagonal (![2, 4] : Fin 2 → ℝ)).PosDef := by
    rw [posDef_diagonal_iff]
    intro i; fin_cases i <;> norm_num
  have := h 2 (diagonal ![2, 4]) hA ![2, 1/2] (by intro i; fin_cases i <;> norm_num)
  have e1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) + diagonal ![2, 1/2] = diagonal ![3, 3/2] := by
    rw [← diagonal_one, diagonal_add]
    congr 1
    ext i; fin_cases i <;> norm_num
  have e2 : (diagonal (![3, 3/2] : Fin 2 → ℝ))⁻¹ = diagonal ![1/3, 2/3] :=
    diag_inv _ _ (by intro i; fin_cases i <;> norm_num)
  have e3 : diagonal (![2, 4] : Fin 2 → ℝ) + diagonal ![2, 1/2] = diagonal ![4, 9/2] := by
    rw [diagonal_add]
    congr 1
    ext i; fin_cases i <;> norm_num
  have e4 : diagonal (![4, 9/2] : Fin 2 → ℝ) * diagonal ![1/3, 2/3] = diagonal ![4/3, 3] := by
    rw [diagonal_mul_diagonal]
    congr 1
    ext i; fin_cases i <;> norm_num
  have e5 : (diagonal (![4/3, 3] : Fin 2 → ℝ))⁻¹ = diagonal ![3/4, 1/3] :=
    diag_inv _ _ (by intro i; fin_cases i <;> norm_num)
  have e6 : (diagonal (![2, 4] : Fin 2 → ℝ))⁻¹ = diagonal ![1/2, 1/4] :=
    diag_inv _ _ (by intro i; fin_cases i <;> norm_num)
  unfold OMA.S_mo_250663.condNum at this
  rw [e1, e2, e3, e4, e5, e6] at this
  rw [l2_opNorm_diagonal, l2_opNorm_diagonal, l2_opNorm_diagonal, l2_opNorm_diagonal] at this
  rw [norm_vec' (3/4) (1/3) (by norm_num) (by norm_num) (by norm_num),
    norm_vec (4/3) 3 (by norm_num) (by norm_num) (by norm_num),
    norm_vec 2 4 (by norm_num) (by norm_num) (by norm_num),
    norm_vec' (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num)] at this
  norm_num at this
