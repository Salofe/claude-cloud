import OMAStatements.S_mo_428070
import Mathlib

/-- No such example exists: the augmentation map `ℚ[G] → ℚ` (sum of coefficients) is a ring
homomorphism, so it would send `x` to a rational number whose square is `2`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_428070.main) := by
  rintro ⟨G, group, _, x, hx⟩
  let _ := group
  set f := MonoidAlgebra.lift ℚ ℚ G (1 : G →* ℚ) with hf
  have h1 : (f x) ^ 2 = 2 := by
    rw [← map_pow, hx]
    exact map_ofNat f 2
  have h2 : ((f x : ℚ) : ℝ) ^ 2 = 2 := by exact_mod_cast h1
  apply irrational_sqrt_two
  refine ⟨|f x|, ?_⟩
  rw [← h2, Real.sqrt_sq_eq_abs]
  push_cast
  rfl
