import PvsNP.FifteenTerm
import PvsNP.SixBySixForms

/-!
# The 15-term limit for the 6 × 6 permanent, with trilinear factors

`FifteenTerm.lean` states the bound with `IsSplit3`, which allows arbitrary functions of three
rows as factors. Here the same fifteen terms are shown to be products of genuine trilinear
forms (`IsTriSplit` from `SixBySixForms.lean`), so the count compares like with like against
the Laplace expansion (`permanent_eq_twenty_triSplit`, twenty such products).
-/

namespace PvsNP

open Matrix

section Fifteen

variable {K : Type*} [Field K]

theorem isTriForm_gmf (a b c d e f : K) (p q r : Fin 6) : IsTriForm (gmf a b c d e f p q r) :=
  ((((((isTriForm_monomial p q r).const_mul a).add ((isTriForm_monomial p r q).const_mul b)).add
    ((isTriForm_monomial q p r).const_mul c)).add ((isTriForm_monomial q r p).const_mul d)).add
    ((isTriForm_monomial r p q).const_mul e)).add ((isTriForm_monomial r q p).const_mul f)

theorem isTriForm_wsq (a b lam : K) : IsTriForm (wsq a b lam) :=
  ((isTriForm_perm3 0 1 2).const_mul a).add (((isTriForm_perm3 3 4 5).const_mul b).const_mul lam)

variable [CharZero K]

theorem permanent_add_eq_fifteen_triSplit (lam : K) (hlam : lam ≠ 0) :
    ∃ ts : List (Matrix (Fin 6) (Fin 6) K → K), ts.length = 15 ∧ (∀ t ∈ ts, IsTriSplit t) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) K, A.permanent + lam * (wrest A / 90) = (ts.map fun t => t A).sum := by
  refine ⟨[
      mk 0 1 2 3 4 5 (fun u v w => (90 * lam)⁻¹ * wsq 3 1 lam u v w) (fun u v w => wsq 90 30 lam u v w),
      mk 0 1 3 2 4 5 (fun u v w => (90 * lam)⁻¹ * wsq (-15) 1 lam u v w) (fun u v w => wsq 90 (-6) lam u v w),
      mk 0 1 4 2 3 5 (fun u v w => (90 * lam)⁻¹ * wsq 3 1 lam u v w) (fun u v w => wsq 90 30 lam u v w),
      mk 0 1 5 2 3 4 (fun u v w => (90 * lam)⁻¹ * wsq 9 1 lam u v w) (fun u v w => wsq 90 10 lam u v w),
      mk 0 2 3 1 4 5 (fun u v w => (90 * lam)⁻¹ * wsq (-18) 1 lam u v w) (fun u v w => wsq 90 (-5) lam u v w),
      mk 0 2 4 1 3 5 (fun u v w => (90 * lam)⁻¹ * wsq (-6) 1 lam u v w) (fun u v w => wsq 90 (-15) lam u v w),
      mk 0 2 5 1 3 4 (fun u v w => (90 * lam)⁻¹ * wsq 6 1 lam u v w) (fun u v w => wsq 90 15 lam u v w),
      mk 0 3 4 1 2 5 (fun u v w => (90 * lam)⁻¹ * wsq (-18) 1 lam u v w) (fun u v w => wsq 90 (-5) lam u v w),
      mk 0 3 5 1 2 4 (fun u v w => (90 * lam)⁻¹ * wsq 6 1 lam u v w) (fun u v w => wsq 90 15 lam u v w),
      mk 0 4 5 1 2 3 (fun u v w => (90 * lam)⁻¹ * wsq 30 1 lam u v w) (fun u v w => wsq 90 3 lam u v w),
      mk 0 1 2 3 4 5 (fun u v w => lam⁻¹ * (-2) * gmf 3 3 (-1) (-2) (-1) (-2) 0 1 2 u v w) (fun u v w => gmf 9 6 3 (-3) (-6) (-9) 0 1 2 u v w),
      mk 0 1 2 3 4 5 (fun u v w => lam⁻¹ * (-2) * gmf (-1) (-2) 3 3 (-2) (-1) 0 1 2 u v w) (fun u v w => gmf 3 (-3) 9 6 (-9) (-6) 0 1 2 u v w),
      mk 0 1 3 2 4 5 (fun u v w => lam⁻¹ * (-2) * gmf 5 5 (-7) 2 (-7) 2 0 1 2 u v w) (fun u v w => gmf 2 1 1 (-1) (-1) (-2) 0 1 2 u v w),
      mk 0 1 3 2 4 5 (fun u v w => lam⁻¹ * (-2) * gmf (-7) 2 5 5 2 (-7) 0 1 2 u v w) (fun u v w => gmf 1 (-1) 2 1 (-2) (-1) 0 1 2 u v w),
      mk 0 2 4 1 3 5 (fun u v w => lam⁻¹ * 12 * gmf 1 (-1) (-1) 1 1 (-1) 0 1 2 u v w) (fun u v w => gmf 1 (-1) (-1) 1 1 (-1) 0 1 2 u v w)], rfl, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact isTriSplit_mk (by decide) ((isTriForm_wsq _ _ _).const_mul _) (isTriForm_wsq _ _ _)
        | exact isTriSplit_mk (by decide) ((isTriForm_gmf _ _ _ _ _ _ _ _ _).const_mul _)
            (isTriForm_gmf _ _ _ _ _ _ _ _ _)
  · intro A
    have h := fifteen_term_identity A lam
    simp only [wsquares, extras5] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mk]
    have h0 : ((90 : K)) ≠ 0 := by norm_num
    field_simp
    linear_combination h

end Fifteen

end PvsNP
