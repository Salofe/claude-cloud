import Mathlib

/-!
# Laplace expansion of the permanent along the first column

Mathlib has the determinant version (`Matrix.det_succ_column_zero`) but not this one.
-/

namespace PvsNP

open Matrix Equiv

variable {R : Type*} [CommRing R]

/-- Laplace expansion of the permanent of an `(n+1) × (n+1)` matrix along column `0`. -/
theorem permanent_succ_column_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    A.permanent = ∑ i : Fin n.succ, A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.permanent, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.swap_self, Equiv.coe_refl, id,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_zero, submatrix_apply]
  · rw [← permanent_permute_cols i.cycleRange (A.submatrix i.succ.succAbove Fin.succ),
      Matrix.permanent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Fin.prod_univ_succ, Fin.succAbove_cycleRange,
      Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
      submatrix_apply, id]

end PvsNP
