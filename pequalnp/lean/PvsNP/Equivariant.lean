import Mathlib

/-!
# A symmetric lower bound for split decompositions of the permanent

The `m × m` permanent is the sum of the `m !` permutation monomials. A term of a
"`k`-split" decomposition is a product `F · G` where `F` involves `k` rows and `G` the
other `m - k`. If such a term is a weight vector for the row and column scalings of the
matrix (the symmetry of the permanent that Grenet's formula respects), then the
permutation monomials it contains all map one fixed `k`-set of rows `R` onto one fixed
`k`-set of columns `C`.

This file proves the counting core: any family of `n` such terms whose coefficients sum to
the permanent's (every permutation monomial gets coefficient `1`) has `n ≥ m.choose k`.
So a decomposition with fewer than `m.choose k` terms at a layer has to break the scaling
symmetry and rely on cancellation between non-permutation monomials.
-/

namespace PvsNP

open Finset

/-- A permutation that maps `R` onto `C` preserves membership in both directions. -/
lemma mem_iff_of_image_eq {m : ℕ} {R C : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (h : R.image σ = C) (a : Fin m) : a ∈ R ↔ σ a ∈ C := by
  constructor
  · intro ha
    rw [← h]
    exact Finset.mem_image_of_mem σ ha
  · intro ha
    rw [← h] at ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    rwa [σ.injective hba] at hb

/-- There are at most `(card α)!` bijections from `α` to `β`. -/
lemma card_equiv_le (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Fintype.card (α ≃ β) ≤ (Fintype.card α).factorial := by
  by_cases h : Nonempty (α ≃ β)
  · obtain ⟨e⟩ := h
    exact (Fintype.card_equiv e).le
  · have : IsEmpty (α ≃ β) := not_nonempty_iff.mp h
    simp

/-- **Covering bound.** If every permutation of `Fin m` maps one of the `k`-sets `R v` onto
the corresponding `k`-set `C v`, then there are at least `m.choose k` pairs. -/
theorem choose_le_of_cover (m k n : ℕ) (R C : Fin n → Finset (Fin m))
    (hR : ∀ v, (R v).card = k)
    (hcover : ∀ σ : Equiv.Perm (Fin m), ∃ v, (R v).image σ = C v) :
    m.choose k ≤ n := by
  classical
  -- `k ≤ m`, using the pair that covers the identity
  obtain ⟨v₀, -⟩ := hcover 1
  have hkm : k ≤ m := by
    have := Finset.card_le_univ (R v₀)
    rw [hR v₀, Fintype.card_fin] at this
    exact this
  choose v hv using hcover
  -- local data of a permutation: the pair it is covered by, and its two restrictions
  let T := Σ w : Fin n, ({x // x ∈ R w} ≃ {x // x ∈ C w}) × ({x // x ∉ R w} ≃ {x // x ∉ C w})
  let f : Equiv.Perm (Fin m) → T := fun σ =>
    ⟨v σ, Equiv.subtypeEquiv σ (mem_iff_of_image_eq (hv σ)),
      Equiv.subtypeEquiv σ (fun a => not_congr (mem_iff_of_image_eq (hv σ) a))⟩
  let g : T → Fin m → Fin m := fun t a =>
    if h : a ∈ R t.1 then (t.2.1 ⟨a, h⟩ : Fin m) else (t.2.2 ⟨a, h⟩ : Fin m)
  have hg : ∀ σ : Equiv.Perm (Fin m), g (f σ) = σ := by
    intro σ
    funext a
    by_cases h : a ∈ R (v σ)
    · simp [g, f, h]
    · simp [g, f, h]
  have hf : Function.Injective f := by
    intro σ τ h
    have := congrArg g h
    rw [hg, hg] at this
    exact DFunLike.coe_injective this
  have hcard : Fintype.card (Equiv.Perm (Fin m)) ≤ Fintype.card T :=
    Fintype.card_le_of_injective f hf
  have hT : Fintype.card T ≤ n * (k.factorial * (m - k).factorial) := by
    rw [Fintype.card_sigma]
    calc ∑ w : Fin n, Fintype.card (({x // x ∈ R w} ≃ {x // x ∈ C w}) ×
            ({x // x ∉ R w} ≃ {x // x ∉ C w}))
        ≤ ∑ _w : Fin n, k.factorial * (m - k).factorial := by
          apply Finset.sum_le_sum
          intro w _
          rw [Fintype.card_prod]
          apply Nat.mul_le_mul
          · have := card_equiv_le {x // x ∈ R w} {x // x ∈ C w}
            rwa [Fintype.card_coe, hR w] at this
          · have := card_equiv_le {x // x ∉ R w} {x // x ∉ C w}
            have hc : Fintype.card {x // x ∉ R w} = m - k := by
              rw [Fintype.card_subtype_compl, Fintype.card_coe, hR w, Fintype.card_fin]
            rwa [hc] at this
      _ = n * (k.factorial * (m - k).factorial) := by simp
  rw [Fintype.card_perm, Fintype.card_fin] at hcard
  have hmul : m.choose k * (k.factorial * (m - k).factorial) ≤
      n * (k.factorial * (m - k).factorial) := by
    rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial hkm]
    exact hcard.trans hT
  exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos _))

/-- **Symmetric split lower bound.** Let `a v σ` be the coefficient of the permutation
monomial `σ` in term `v`. If term `v` only contains permutation monomials that map the
`k`-set of rows `R v` onto the `k`-set of columns `C v`, and the terms add up to the
permanent (coefficient `1` on every permutation monomial), then there are at least
`m.choose k` terms. -/
theorem choose_le_of_equivariant_split (m k n : ℕ) (R C : Fin n → Finset (Fin m))
    (hR : ∀ v, (R v).card = k)
    (a : Fin n → Equiv.Perm (Fin m) → ℂ)
    (hsupp : ∀ v σ, a v σ ≠ 0 → (R v).image σ = C v)
    (hsum : ∀ σ : Equiv.Perm (Fin m), ∑ v, a v σ = 1) :
    m.choose k ≤ n := by
  apply choose_le_of_cover m k n R C hR
  intro σ
  by_contra hno
  push Not at hno
  have hzero : ∀ v, a v σ = 0 := by
    intro v
    by_contra hv
    exact hno v (hsupp v σ hv)
  have := hsum σ
  simp [hzero] at this

/-- Summing over the layers: a program whose every layer `k = 0, …, m` is a symmetric split
needs `2 ^ m` vertices in total. -/
theorem two_pow_le_of_all_layers (m : ℕ) (width : ℕ → ℕ)
    (h : ∀ k ≤ m, m.choose k ≤ width k) :
    2 ^ m ≤ ∑ k ∈ Finset.range (m + 1), width k := by
  rw [← Nat.sum_range_choose]
  apply Finset.sum_le_sum
  intro k hk
  exact h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

end PvsNP
