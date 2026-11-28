import OMAReductions.R_Erdos20_erdos_20_R1

/-!
# Step H1 of the reduction Erdos20.erdos_20.R1

The colour-coding lemma: for every finite family `F` of `n`-element sets (with `0 < n`) there is a
colouring `c : α → Fin n` such that the rainbow members of `F` (those `A` on which `c` is a
bijection onto `Fin n`) number at least `|F| * n! / n ^ n`.

Proof by averaging. Put `U = ⋃ F` and consider all colourings `f : U → Fin n`. For a fixed
`A ∈ F`, the colourings that are injective on `A` are counted by splitting a colouring into its
restriction to `A` (an embedding of `A` into `Fin n`, `n!` choices) and its restriction to the
complement (`n ^ (|U| - n)` choices). Double counting the pairs `(f, A)` with `A` rainbow for `f`
gives `∑ f, #rainbow(f) * n ^ n = |F| * n! * n ^ |U|`, so some colouring `f` has
`|F| * n! ≤ #rainbow(f) * n ^ n`. Finally `f` is extended to all of `α` by a constant colour, and
injectivity on an `n`-set into `Fin n` is upgraded to bijectivity by counting.

Only Mathlib and our own helper lemmas below are used.
-/

namespace OMA.Helpers

open Finset

/-- The number of colourings `f : ι → Fin n` that are injective on a finset `A` is
`n.descFactorial |A| * n ^ (|ι| - |A|)`. -/
theorem card_injOn {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (A : Finset ι) :
    Fintype.card {f : ι → Fin n // Set.InjOn f (A : Set ι)} =
      n.descFactorial A.card * n ^ (Fintype.card ι - A.card) := by
  classical
  have e1 : {f : ι → Fin n // Set.InjOn f (A : Set ι)} ≃
      {g : ({i // i ∈ A} → Fin n) × ({i // ¬ i ∈ A} → Fin n) // Function.Injective g.1} :=
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) (fun _ => Fin n)).subtypeEquiv (by
      intro f
      constructor
      · intro hf x y hxy
        exact Subtype.ext (hf x.2 y.2 hxy)
      · intro hf x hx y hy hxy
        have := @hf ⟨x, hx⟩ ⟨y, hy⟩ hxy
        exact congrArg Subtype.val this)
  have e2 := e1.trans (Equiv.prodSubtypeFstEquivSubtypeProd.trans
    (Equiv.prodCongr (Equiv.subtypeInjectiveEquivEmbedding _ _) (Equiv.refl _)))
  rw [Fintype.card_congr e2, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fun]
  simp

/-- Averaging over all colourings of a finite type `ι` with `n` colours: for a finite family of
`n`-element finsets `S A` (indexed by `A ∈ F`) some colouring is injective on at least
`|F| * n! / n ^ n` of them. -/
theorem exists_coloring {ι β : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (hn : 0 < n)
    (F : Finset β) (S : β → Finset ι) (hS : ∀ A ∈ F, (S A).card = n) :
    ∃ (f : ι → Fin n) (G : Finset β), G ⊆ F ∧ (∀ A ∈ G, Set.InjOn f (S A : Set ι)) ∧
      F.card * n.factorial ≤ G.card * n ^ n := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let r : (ι → Fin n) → β → Prop := fun f A => Set.InjOn f (S A : Set ι)
  have hcount : ∀ A ∈ F, ((univ : Finset (ι → Fin n)).bipartiteBelow r A).card * n ^ n =
      n.factorial * n ^ Fintype.card ι := by
    intro A hA
    have h1 : ((univ : Finset (ι → Fin n)).bipartiteBelow r A).card =
        Fintype.card {f : ι → Fin n // Set.InjOn f (S A : Set ι)} := by
      rw [Fintype.card_subtype]
      rfl
    have hle : n ≤ Fintype.card ι := by
      calc n = (S A).card := (hS A hA).symm
        _ ≤ Fintype.card ι := Finset.card_le_univ _
    rw [h1, card_injOn, hS A hA, Nat.descFactorial_self, mul_assoc, ← pow_add,
      Nat.sub_add_cancel hle]
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset (ι → Fin n))) (t := F) r
  have hL : ∑ _f : ι → Fin n, F.card * n.factorial =
      n ^ Fintype.card ι * (F.card * n.factorial) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
  have hR : ∑ f : ι → Fin n, (F.bipartiteAbove r f).card * n ^ n =
      F.card * (n.factorial * n ^ Fintype.card ι) := by
    rw [← Finset.sum_mul, hdouble, Finset.sum_mul, Finset.sum_congr rfl hcount,
      Finset.sum_const, smul_eq_mul]
  have hsum : ∑ _f : ι → Fin n, F.card * n.factorial ≤
      ∑ f : ι → Fin n, (F.bipartiteAbove r f).card * n ^ n := by
    rw [hL, hR]
    apply le_of_eq
    ring
  obtain ⟨f, -, hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨f, F.bipartiteAbove r f, Finset.filter_subset _ _,
    fun A hA => ((Finset.mem_bipartiteAbove r).mp hA).2, hf⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  intro α n hn F hF
  classical
  let U : Finset α := F.biUnion id
  have hsub : ∀ A ∈ F, A ⊆ U := fun A hA => Finset.subset_biUnion_of_mem id hA
  obtain ⟨f, G, hGF, hGinj, hcard⟩ := OMA.Helpers.exists_coloring (ι := U) n hn F
    (fun A => A.subtype (· ∈ U)) (by
      intro A hA
      rw [Finset.card_subtype, Finset.filter_true_of_mem (hsub A hA)]
      exact hF A hA)
  let c : α → Fin n := fun x => if h : x ∈ U then f ⟨x, h⟩ else ⟨0, hn⟩
  refine ⟨c, G, hGF, ?_, hcard⟩
  intro A hA
  have hAU := hsub A (hGF hA)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hxU : (x : α) ∈ U := hAU x.2
    have hyU : (y : α) ∈ U := hAU y.2
    have hxy' : f ⟨x, hxU⟩ = f ⟨y, hyU⟩ := by
      simpa [c, hxU, hyU] using hxy
    have := hGinj A hA (by simp) (by simp) hxy'
    exact Subtype.ext (Subtype.mk.inj this)
  · simp [hF A (hGF hA)]
