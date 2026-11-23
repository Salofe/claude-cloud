import PvsNP.FourByFourExactBase

namespace PvsNP
variable {K : Type*} [Field K]

/-- The slice matrix `B_w` of the permanent. -/
def Bmat (w : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, w 2 + w 3, w 1 + w 3, w 1 + w 2; w 2 + w 3, 0, w 0 + w 3, w 0 + w 2;
    w 1 + w 3, w 0 + w 3, 0, w 0 + w 1; w 1 + w 2, w 0 + w 2, w 0 + w 1, 0]

lemma Bmat_apply (w : Fin 4 → K) (i j : Fin 4) :
    Bmat w i j = E3 w (Pi.single i 1) (Pi.single j 1) := by
  fin_cases i <;> fin_cases j <;> simp [Bmat, E3_eq, Pi.single_apply]

lemma det_Bmat (w : Fin 4 → K) :
    (Bmat w).det = -4 * ((w 0 + w 1 + w 2 + w 3) * (w 1 * w 2 * w 3 + w 0 * w 2 * w 3 + w 0 * w 1 * w 3 + w 0 * w 1 * w 2)
    - 4 * (w 0 * w 1 * w 2 * w 3)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Bmat, Fin.succAbove, Matrix.submatrix]
  ring
end PvsNP
