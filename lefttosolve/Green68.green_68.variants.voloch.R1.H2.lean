import OMAReductions.R_Green68_green_68_variants_voloch_R1

/-!
# Step H2 of the reduction Green68.green_68.variants.voloch.R1

Plane polynomials of total degree at most two form a vector space of dimension at most six:
such a polynomial is determined by its coefficients at the six exponents `(i, j)` with
`i + j ≤ 2`. For a finite set `S` of points, let `V S` be the subspace of those polynomials
vanishing on `S`. By induction on `A`, there is a subset `S` of `A` with `V S = V A` and
`card S + finrank (V S) ≤ finrank (V ∅)`: adding a point either leaves the subspace unchanged,
or cuts it to a proper subspace, which drops its dimension by at least one. Hence `card S ≤ 6`,
so a nonzero conic through `S` exists by hypothesis, and it vanishes on all of `A`.
-/

namespace OMA.Helpers

open MvPolynomial Module

variable {K : Type*} [Field K]

/-- Polynomials of total degree at most two vanishing on `S`. -/
def green68Quad (S : Finset (Fin 2 → K)) : Submodule K (MvPolynomial (Fin 2) K) where
  carrier := {F | F.totalDegree ≤ 2 ∧ ∀ a ∈ S, eval a F = 0}
  add_mem' := by
    intro F G hF hG
    refine ⟨(totalDegree_add F G).trans (max_le hF.1 hG.1), fun a ha => ?_⟩
    rw [map_add, hF.2 a ha, hG.2 a ha, add_zero]
  zero_mem' := ⟨by simp, fun a _ => by simp⟩
  smul_mem' := by
    intro c F hF
    refine ⟨(totalDegree_smul_le c F).trans hF.1, fun a ha => ?_⟩
    rw [smul_eval, hF.2 a ha, mul_zero]

theorem mem_green68Quad {S : Finset (Fin 2 → K)} {F : MvPolynomial (Fin 2) K} :
    F ∈ green68Quad S ↔ F.totalDegree ≤ 2 ∧ ∀ a ∈ S, eval a F = 0 := Iff.rfl

theorem mem_green68Quad_insert [DecidableEq (Fin 2 → K)] {S : Finset (Fin 2 → K)}
    {a : Fin 2 → K} {F : MvPolynomial (Fin 2) K} :
    F ∈ green68Quad (insert a S) ↔ F ∈ green68Quad S ∧ eval a F = 0 := by
  simp only [mem_green68Quad, Finset.mem_insert, forall_eq_or_imp]
  tauto

/-- The six exponents of total degree at most two. -/
abbrev Green68Idx : Type := {ij : Fin 3 × Fin 3 // (ij.1 : ℕ) + ij.2 ≤ 2}

theorem card_green68Idx : Fintype.card Green68Idx = 6 := by decide

/-- The coefficient map at the six exponents. -/
noncomputable def green68Coeffs : green68Quad (∅ : Finset (Fin 2 → K)) →ₗ[K] (Green68Idx → K) :=
  LinearMap.pi fun ij =>
    (lcoeff K (Finsupp.single 0 (ij.1.1 : ℕ) + Finsupp.single 1 (ij.1.2 : ℕ))).comp
      (green68Quad (∅ : Finset (Fin 2 → K))).subtype

theorem green68Coeffs_injective :
    Function.Injective (green68Coeffs (K := K)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  apply Subtype.ext
  change (F : MvPolynomial (Fin 2) K) = 0
  ext m
  rw [coeff_zero]
  by_contra hne
  have hm : m ∈ (F : MvPolynomial (Fin 2) K).support := mem_support_iff.2 hne
  have hdeg := (le_totalDegree hm).trans F.2.1
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hdeg
  have hm' : m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
    ext i
    fin_cases i <;> simp
  have h0 : m 0 < 3 := by omega
  have h1 : m 1 < 3 := by omega
  have hc := congrFun hF ⟨(⟨m 0, h0⟩, ⟨m 1, h1⟩), hdeg⟩
  apply hne
  rw [hm']
  exact hc

instance green68Quad_empty_fd : FiniteDimensional K (green68Quad (∅ : Finset (Fin 2 → K))) :=
  FiniteDimensional.of_injective green68Coeffs green68Coeffs_injective

theorem finrank_green68Quad_empty :
    finrank K (green68Quad (∅ : Finset (Fin 2 → K))) ≤ 6 := by
  have h := LinearMap.finrank_le_finrank_of_injective (green68Coeffs_injective (K := K))
  rw [Module.finrank_fintype_fun_eq_card, card_green68Idx] at h
  exact h

theorem green68Quad_le_empty (S : Finset (Fin 2 → K)) :
    green68Quad S ≤ green68Quad (∅ : Finset (Fin 2 → K)) :=
  fun _ hF => ⟨hF.1, fun _ ha => absurd ha (Finset.notMem_empty _)⟩

theorem green68Quad_fd (S : Finset (Fin 2 → K)) : FiniteDimensional K (green68Quad S) :=
  Submodule.finiteDimensional_of_le (green68Quad_le_empty S)

/-- Every finite set has a subset cutting out the same space, whose size plus the dimension of
that space is at most the dimension of the whole space. -/
theorem green68_exists_subset (A : Finset (Fin 2 → K)) :
    ∃ S ⊆ A, S.card + finrank K (green68Quad S) ≤ finrank K (green68Quad (∅ : Finset (Fin 2 → K)))
      ∧ green68Quad S = green68Quad A := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, subset_refl _, by simp, rfl⟩
  | insert a A _ ih =>
    obtain ⟨S, hSA, hcard, hEq⟩ := ih
    by_cases h : ∀ F ∈ green68Quad A, eval a F = 0
    · refine ⟨S, hSA.trans (Finset.subset_insert a A), hcard, ?_⟩
      rw [hEq]
      ext F
      rw [mem_green68Quad_insert]
      exact ⟨fun hF => ⟨hF, h F hF⟩, fun hF => hF.1⟩
    · simp only [not_forall] at h
      obtain ⟨G, hG, hGa⟩ := h
      have hins : green68Quad (insert a S) = green68Quad (insert a A) := by
        ext F
        rw [mem_green68Quad_insert, mem_green68Quad_insert, hEq]
      have hlt : green68Quad (insert a S) < green68Quad S := by
        refine lt_of_le_of_ne (fun F hF => (mem_green68Quad_insert.1 hF).1) ?_
        intro heq
        have hGS : G ∈ green68Quad S := hEq ▸ hG
        rw [← heq] at hGS
        exact hGa (mem_green68Quad_insert.1 hGS).2
      have := green68Quad_fd (K := K) S
      have hrk := Submodule.finrank_lt_finrank_of_lt hlt
      have hc := Finset.card_insert_le a S
      refine ⟨insert a S, Finset.insert_subset_insert a hSA, by omega, hins⟩

theorem green68_conic_of_six (A : Finset (Fin 2 → K))
    (h : ∀ S ⊆ A, S.card ≤ 6 → ∃ F : MvPolynomial (Fin 2) K,
      F ≠ 0 ∧ F.totalDegree ≤ 2 ∧ ∀ a ∈ S, eval a F = 0) :
    ∃ F : MvPolynomial (Fin 2) K, F ≠ 0 ∧ F.totalDegree ≤ 2 ∧ ∀ a ∈ A, eval a F = 0 := by
  obtain ⟨S, hSA, hcard, hEq⟩ := green68_exists_subset A
  have h6 := finrank_green68Quad_empty (K := K)
  obtain ⟨F, hF0, hdeg, hvan⟩ := h S hSA (by omega)
  have hFS : F ∈ green68Quad S := ⟨hdeg, hvan⟩
  rw [hEq] at hFS
  exact ⟨F, hF0, hdeg, hFS.2⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Green68_green_68_variants_voloch_R1.H2 := by
  intro p _ A h
  exact OMA.Helpers.green68_conic_of_six A h
