import Mathlib

/-!
# Arbitrary factors versus multilinear factors

A split product for a row set `R` can be defined permissively (an arbitrary function of the
rows in `R` times an arbitrary function of the other rows) or strictly (a multilinear form
times a multilinear form). For a target that is multilinear in the rows, the two notions need
the same number of terms: `multilinear_split_of_function_split` turns any permissive
decomposition into a strict one with the same row sets, by evaluating the factors on basis
vectors. So upper bounds stated with arbitrary factors (as in `SixBySix.lean`) are not weaker
than they look, and lower bounds may assume multilinear factors.
-/

namespace PvsNP

open Finset Matrix

/-- Let `f` be multilinear in the rows, with coefficient tensor `T`.  If `f` is a sum of `n`
products `F v (rows in R v) * G v (rows not in R v)` with ARBITRARY functions `F v`, `G v`, then
`f` is the sum of the `n` products of the multilinear forms whose coefficients are the values
of `F v`, `G v` on basis vectors, for the same row sets `R v`.  Any commutative ring. -/
theorem multilinear_split_of_function_split {K : Type*} [CommRing K] {m n : ℕ}
    (R : Fin n → Finset (Fin m))
    (F : ∀ v, ({r // r ∈ R v} → Fin m → K) → K) (G : ∀ v, ({r // r ∉ R v} → Fin m → K) → K)
    (f : Matrix (Fin m) (Fin m) K → K) (T : (Fin m → Fin m) → K)
    (hf : ∀ A, f A = ∑ c : Fin m → Fin m, T c * ∏ r, A r (c r))
    (h : ∀ A, f A = ∑ v, F v (fun r => A r) * G v (fun r => A r)) :
    ∀ A, f A = ∑ v,
      (∑ cF : {r // r ∈ R v} → Fin m,
          F v (fun r => Pi.single (cF r) 1) * ∏ r : {r // r ∈ R v}, A r (cF r)) *
      (∑ cG : {r // r ∉ R v} → Fin m,
          G v (fun r => Pi.single (cG r) 1) * ∏ r : {r // r ∉ R v}, A r (cG r)) := by
  classical
  -- the 0/1 matrix of an assignment: row `r` is the basis vector `e_(c r)`
  let E : (Fin m → Fin m) → Matrix (Fin m) (Fin m) K := fun c r => Pi.single (c r) 1
  have hT : ∀ c, T c = f (E c) := by
    intro c
    rw [hf (E c), Finset.sum_eq_single c]
    · simp [E]
    · intro c' _ hne
      obtain ⟨r, hr⟩ := Function.ne_iff.mp hne
      have h0 : ∏ r, E c r (c' r) = 0 :=
        Finset.prod_eq_zero (mem_univ r) (by simp [E, hr])
      rw [h0, mul_zero]
    · intro hc
      exact absurd (mem_univ c) hc
  intro A
  have step : ∀ v,
      (∑ cF : {r // r ∈ R v} → Fin m,
          F v (fun r => Pi.single (cF r) 1) * ∏ r : {r // r ∈ R v}, A r (cF r)) *
      (∑ cG : {r // r ∉ R v} → Fin m,
          G v (fun r => Pi.single (cG r) 1) * ∏ r : {r // r ∉ R v}, A r (cG r)) =
      ∑ c : Fin m → Fin m,
        F v (fun r => E c r) * G v (fun r => E c r) * ∏ r, A r (c r) := by
    intro v
    rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    symm
    refine Fintype.sum_equiv
      (Equiv.piEquivPiSubtypeProd (fun r => r ∈ R v) (fun _ => Fin m)) _ _ fun c => ?_
    have hprod : ∏ r, A r (c r) =
        (∏ r : {r // r ∈ R v}, A r (c r)) * ∏ r : {r // r ∉ R v}, A r (c r) := by
      convert (Fintype.prod_subtype_mul_prod_subtype (fun r => r ∈ R v)
        (fun r => A r (c r))).symm
    rw [hprod]
    simp only [Equiv.piEquivPiSubtypeProd_apply, E]
    ring
  simp_rw [step]
  rw [hf A, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hT, h (E c), Finset.sum_mul]

end PvsNP
