import OMAStatements.S_oeis_a396722
import Mathlib

namespace OMA.Helpers

open Polynomial OMA.S_oeis_a396722

noncomputable def e (n : ℕ) : ℚ :=
  (Lagrange.basis (Finset.range (n + 1)) (fun i : ℕ => (i : ℚ) + 1) 0).eval (5 / 2)

theorem p_eval (n : ℕ) : (p n).eval (5 / 2) = 1 - e n := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ℚ) + 1) (Finset.range (n + 1) : Set ℕ) := by
    intro x _ y _ h
    simpa using h
  have hsum := Lagrange.sum_basis hinj (s := Finset.range (n + 1)) ⟨0, by simp⟩
  have h0 : (0 : ℕ) ∈ Finset.range (n + 1) := by simp
  unfold p e
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  have h1 := congrArg (Polynomial.eval (5 / 2 : ℚ)) hsum
  rw [eval_finsetSum, eval_one] at h1
  rw [← Finset.add_sum_erase _ _ h0] at h1 ⊢
  simp only [eval_mul, eval_C, ↓reduceIte, zero_mul, zero_add]
  rw [Finset.sum_congr rfl (g := fun i => (Lagrange.basis (Finset.range (n + 1))
    (fun i : ℕ => (i : ℚ) + 1) i).eval (5 / 2))]
  · linarith
  · intro i hi
    rw [if_neg (Finset.ne_of_mem_erase hi), one_mul]

theorem e_zero : e 0 = 1 := by
  simp [e, Lagrange.basis]

theorem e_succ (n : ℕ) : e (n + 1) = e n * ((-((n : ℚ) + 1))⁻¹ * (3 / 2 - ((n : ℚ) + 1))) := by
  unfold e Lagrange.basis
  rw [Finset.range_add_one (n := n + 1), Finset.erase_insert_of_ne (by omega),
    Finset.prod_insert (by simp), eval_mul, mul_comm]
  congr 1
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  push_cast
  congr 1
  · ring_nf
  · ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a396722.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [OMA.S_oeis_a396722.a, OMA.Helpers.p_eval, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega, OMA.Helpers.e_succ]
  have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
