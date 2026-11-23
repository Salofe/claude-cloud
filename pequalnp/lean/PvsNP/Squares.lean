import Mathlib

/-!
# The square construction for the 2k × 2k permanent, for every k

Rows and columns are indexed by `κ ⊕ κ`; the columns `inl j` form the first block and the
columns `inr j` the second. For a set `S` of rows, `blockForm A Sum.inl S` is the permanent of
the rows `S` on the first block of columns and `blockForm A Sum.inr S` the permanent of the
rows `S` on the second block (both are zero unless `S` has exactly `card κ` elements).

* `permanent_eq_sum_blockForm`: Laplace expansion along the first block of columns,
  `permanent A = ∑ S, blockForm A inl S * blockForm A inr Sᶜ`. Mathlib does not have it.
* `two_mul_permanent_eq_squares`: with `X S = blockForm A inl S + lam * blockForm A inr S`,
  `2 * lam * permanent A = ∑ S, X S * X Sᶜ - ∑ S, q₁ S * q₁ Sᶜ - lam ^ 2 * ∑ S, q₂ S * q₂ Sᶜ`.

In the first sum `S` and `Sᶜ` give the same product, so it has half as many distinct terms as
the Laplace expansion; the last sum carries a factor `lam ^ 2`. This is the polarisation of
`2 * lam * q₁ * q₂ = (q₁ + lam * q₂) ^ 2 - q₁ ^ 2 - lam ^ 2 * q₂ ^ 2`.
-/

namespace PvsNP

open Finset Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {R : Type*} [CommRing R]

/-- The product of the entries picked when column `side j` of a block uses row `f j`. -/
def pick (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (side : κ → κ ⊕ κ) (f : κ ↪ κ ⊕ κ) : R :=
  ∏ j, A (f j) (side j)

/-- The permanent of the rows `S` on one block of columns (`side = Sum.inl` or `Sum.inr`):
the sum over all ways of assigning the columns of the block bijectively to the rows of `S`. -/
noncomputable def blockForm (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (side : κ → κ ⊕ κ) (S : Finset (κ ⊕ κ)) : R :=
  ∑ f : κ ↪ κ ⊕ κ, if univ.map f = S then pick A side f else 0

/-- The permanent as a sum over pairs of embeddings with complementary images. -/
theorem permanent_eq_sum_embeddings (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) :
    A.permanent = ∑ f : κ ↪ κ ⊕ κ, ∑ g : κ ↪ κ ⊕ κ,
      if univ.map g = (univ.map f)ᶜ then pick A Sum.inl f * pick A Sum.inr g else 0 := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_filter]
  unfold Matrix.permanent
  refine Finset.sum_bij
    (fun σ _ => (Function.Embedding.inl.trans σ.toEmbedding,
      Function.Embedding.inr.trans σ.toEmbedding)) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [mem_filter, mem_product, mem_univ, true_and]
    ext x
    simp only [mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
      Function.Embedding.inr_apply, Function.Embedding.inl_apply, Equiv.coe_toEmbedding,
      mem_compl, not_exists]
    constructor
    · rintro ⟨j, rfl⟩ i h
      exact Sum.inl_ne_inr (σ.injective h)
    · intro h
      obtain ⟨y, rfl⟩ := σ.surjective x
      cases y with
      | inl i => exact absurd rfl (h i)
      | inr j => exact ⟨j, rfl⟩
  · intro σ _ τ _ h
    simp only [Prod.mk.injEq] at h
    ext x
    cases x with
    | inl i => exact DFunLike.congr_fun h.1 i
    | inr j => exact DFunLike.congr_fun h.2 j
  · rintro ⟨f, g⟩ hfg
    simp only [mem_filter, mem_product, mem_univ, true_and] at hfg
    have hinj : Function.Injective (Sum.elim f g) := by
      rintro (a | a) (b | b) h
      · exact congrArg _ (f.injective h)
      · exfalso
        have h' : f a = g b := h
        have hb : g b ∈ univ.map g := mem_map_of_mem g (mem_univ b)
        rw [hfg, mem_compl] at hb
        exact hb (h' ▸ mem_map_of_mem f (mem_univ a))
      · exfalso
        have h' : g a = f b := h
        have ha : g a ∈ univ.map g := mem_map_of_mem g (mem_univ a)
        rw [hfg, mem_compl] at ha
        exact ha (h'.symm ▸ mem_map_of_mem f (mem_univ b))
      · exact congrArg _ (g.injective h)
    refine ⟨Equiv.ofBijective (Sum.elim f g) (Finite.injective_iff_bijective.mp hinj),
      mem_univ _, ?_⟩
    ext <;> rfl
  · intro σ _
    simp only [pick, Fintype.prod_sum_type, Function.Embedding.trans_apply,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply, Equiv.coe_toEmbedding]

/-- **Laplace expansion of the permanent along the first block of columns**: a sum over the
sets `S` of rows used by the first block. -/
theorem permanent_eq_sum_blockForm (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) :
    A.permanent = ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inl S * blockForm A Sum.inr Sᶜ := by
  classical
  rw [permanent_eq_sum_embeddings]
  simp only [blockForm, Finset.sum_mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset (Finset (κ ⊕ κ))))]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_comm (s := (univ : Finset (Finset (κ ⊕ κ))))]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single (univ.map f)]
  · by_cases h : univ.map g = (univ.map f)ᶜ <;> simp [h]
  · intro S _ hS
    simp [Ne.symm hS]
  · intro h
    exact absurd (mem_univ _) h

/-- The same expansion with the roles of the two blocks exchanged. -/
theorem permanent_eq_sum_blockForm' (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) :
    A.permanent = ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inr S * blockForm A Sum.inl Sᶜ := by
  rw [permanent_eq_sum_blockForm]
  refine Fintype.sum_equiv (Equiv.ofBijective (fun S => Sᶜ) compl_bijective) _ _ fun S => ?_
  simp [mul_comm]

/-- **The square construction, for every size.** `2 * lam` times the permanent is a sum of
"squares" `X S * X Sᶜ`, minus what the squares leave behind in the first block, minus `lam ^ 2`
times what they leave behind in the second block. -/
theorem two_mul_permanent_eq_squares (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (lam : R) :
    2 * lam * A.permanent =
      ∑ S : Finset (κ ⊕ κ), (blockForm A Sum.inl S + lam * blockForm A Sum.inr S)
          * (blockForm A Sum.inl Sᶜ + lam * blockForm A Sum.inr Sᶜ)
        - ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ
        - lam ^ 2 * ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ := by
  have h1 := permanent_eq_sum_blockForm A
  have h2 := permanent_eq_sum_blockForm' A
  have expand : ∑ S : Finset (κ ⊕ κ), (blockForm A Sum.inl S + lam * blockForm A Sum.inr S)
          * (blockForm A Sum.inl Sᶜ + lam * blockForm A Sum.inr Sᶜ)
      = ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ
        + lam * ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inl S * blockForm A Sum.inr Sᶜ
        + lam * ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inr S * blockForm A Sum.inl Sᶜ
        + lam ^ 2 * ∑ S : Finset (κ ⊕ κ), blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  rw [expand, ← h1, ← h2]
  ring

end PvsNP
