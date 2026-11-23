import Mathlib

/-!
# A symmetric lower bound for split decompositions of the permanent

The `m × m` permanent is the sum of the `m !` permutation monomials. A term of a
"`k`-split" decomposition is a product `F · G` where `F` involves `k` rows and `G` the
other `m - k`. If such a term is a weight vector for the row and column scalings of the
matrix (the symmetry of the permanent that Grenet's formula respects), then the
permutation monomials it contains all map one fixed `k`-set of rows `R` onto one fixed
`k`-set of columns `C`.

This file proves the counting core (`choose_le_of_cover`, `choose_le_of_equivariant_split`): any
family of `n` such terms whose coefficients sum to the permanent's (every permutation monomial
gets coefficient `1`) has `n ≥ m.choose k`, and the bound is attained (`choose_cover_attained`).
`choose_le_of_column_weight_split` derives the support hypothesis from the symmetry itself:
terms are products `F · G` of coefficient tensors and each term is a weight vector for the
column scalings. So a decomposition with fewer than `m.choose k` terms at a layer has to break
the scaling symmetry and rely on cancellation between non-permutation monomials.
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

/-- Arithmetic corollary: if `width k ≥ m.choose k` for every `k ≤ m`, the widths add up to at
least `2 ^ m`. (No branching program is defined here; the hypothesis is the conclusion of the
symmetric bound, assumed at every layer.) -/
theorem two_pow_le_of_all_layers (m : ℕ) (width : ℕ → ℕ)
    (h : ∀ k ≤ m, m.choose k ≤ width k) :
    2 ^ m ≤ ∑ k ∈ Finset.range (m + 1), width k := by
  rw [← Nat.sum_range_choose]
  apply Finset.sum_le_sum
  intro k hk
  exact h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-! ### Variants: nonzero coefficients suffice, and the bound is attained -/

/-- Strengthening of `choose_le_of_equivariant_split`: any coefficient monoid, and the sum of the
coefficients of each permutation monomial only has to be nonzero (so the bound also applies to
every member of an approximating family, i.e. to border decompositions). -/
theorem choose_le_of_support_cover {M : Type*} [AddCommMonoid M] (m k n : ℕ)
    (R C : Fin n → Finset (Fin m)) (hR : ∀ v, (R v).card = k)
    (a : Fin n → Equiv.Perm (Fin m) → M)
    (hsupp : ∀ v σ, a v σ ≠ 0 → (R v).image σ = C v)
    (hsum : ∀ σ : Equiv.Perm (Fin m), ∑ v, a v σ ≠ 0) :
    m.choose k ≤ n := by
  apply choose_le_of_cover m k n R C hR
  intro σ
  by_contra hno
  push Not at hno
  exact hsum σ (Finset.sum_eq_zero fun v _ => by
    by_contra hv
    exact hno v (hsupp v σ hv))

/-- The hypotheses of `choose_le_of_cover` are satisfiable with exactly `m.choose k` pairs
(Laplace: one fixed row set, all column sets), so the bound is attained. -/
theorem choose_cover_attained (m k : ℕ) (hk : k ≤ m) :
    ∃ R C : Fin (m.choose k) → Finset (Fin m), (∀ v, (R v).card = k) ∧
      ∀ σ : Equiv.Perm (Fin m), ∃ v, (R v).image σ = C v := by
  classical
  have hcard : (Finset.powersetCard k (Finset.univ : Finset (Fin m))).card = m.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : Finset (Fin m), R₀.card = k := by
    have : k ≤ (Finset.univ : Finset (Fin m)).card := by simpa using hk
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq this
    exact ⟨t, ht⟩
  let e : Fin (m.choose k) ≃ {S // S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin m))} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard])).symm
  refine ⟨fun _ => R₀, fun v => (e v).1, fun _ => hR₀, fun σ => ?_⟩
  have hmem : R₀.image σ ∈ Finset.powersetCard k (Finset.univ : Finset (Fin m)) := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ σ.injective, hR₀]⟩
  refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
  simp

/-! ### The symmetry hypothesis stated on the terms

Terms are products of coefficient tensors of multilinear forms. An *assignment* is a map
`c : Fin m → Fin m` giving each row `r` a column `c r`; it stands for the monomial
`∏ r, A r (c r)`. "Weight vector for the column scalings" means: all assignments in the support
of the term use every column the same number of times. -/

section Bridge

open Matrix

/-- The permanent is the form whose coefficient tensor is the indicator of the bijective
assignments (this ties the tensor statement below to `Matrix.permanent`). -/
theorem permanent_eq_sum_assignments {S : Type*} [CommRing S] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) S) :
    A.permanent =
      ∑ c : Fin m → Fin m, (if Function.Bijective c then 1 else 0) * ∏ r, A r (c r) := by
  classical
  rw [← permanent_transpose]
  simp only [permanent, transpose_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun σ _ => (σ : Fin m → Fin m)) ?_ ?_ ?_ ?_
  · intro σ _
    exact Finset.mem_filter.mpr ⟨mem_univ _, σ.bijective⟩
  · intro σ _ τ _ h
    exact DFunLike.coe_injective h
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    exact ⟨Equiv.ofBijective c hc, mem_univ _, rfl⟩
  · intro σ _
    rfl

/-- **Symmetric split lower bound, with the symmetry hypothesis stated on the terms.**
Term `v` is the product of a multilinear form in the rows `R v` (coefficients `F v`) and a
multilinear form in the other rows (coefficients `G v`); its coefficient on the assignment `c`
is `F v (c restricted to R v) * G v (c restricted to the complement)`.
`hw`: each term is a weight vector for the column scalings, i.e. all assignments in its support
use every column `j` the same number `w j` of times.
`hsum`: the terms add up to the permanent tensor.
Then there are at least `m.choose k` terms. -/
theorem choose_le_of_column_weight_split (m k n : ℕ) (R : Fin n → Finset (Fin m))
    (hR : ∀ v, (R v).card = k)
    (F : ∀ v, ({r // r ∈ R v} → Fin m) → ℂ) (G : ∀ v, ({r // r ∉ R v} → Fin m) → ℂ)
    (hw : ∀ v, ∃ w : Fin m → ℕ, ∀ c : Fin m → Fin m,
      F v (fun r => c r) * G v (fun r => c r) ≠ 0 →
        ∀ j, (Finset.univ.filter fun r => c r = j).card = w j)
    (hsum : ∀ c : Fin m → Fin m,
      ∑ v, F v (fun r => c r) * G v (fun r => c r) = if Function.Bijective c then 1 else 0) :
    m.choose k ≤ n := by
  classical
  -- coefficient of the permutation monomial `σ` in term `v`
  let a : Fin n → Equiv.Perm (Fin m) → ℂ := fun v σ => F v (fun r => σ r) * G v (fun r => σ r)
  -- two permutation monomials of the same term send `R v` into the same set of columns
  have sub : ∀ v (σ τ : Equiv.Perm (Fin m)), a v σ ≠ 0 → a v τ ≠ 0 →
      (R v).image σ ⊆ (R v).image τ := by
    intro v σ τ hσ hτ
    obtain ⟨w, hw⟩ := hw v
    have hw1 : ∀ j, w j = 1 := by
      intro j
      rw [← hw (fun r => σ r) hσ j, Finset.card_eq_one]
      refine ⟨σ.symm j, ?_⟩
      ext r
      simp [Equiv.eq_symm_apply]
    -- the mixed assignment: `σ` on `R v`, `τ` elsewhere
    let c : Fin m → Fin m := fun r => if r ∈ R v then σ r else τ r
    have hcF : (fun r : {r // r ∈ R v} => c r) = fun r : {r // r ∈ R v} => σ r := by
      funext r
      simp [c, r.2]
    have hcG : (fun r : {r // r ∉ R v} => c r) = fun r : {r // r ∉ R v} => τ r := by
      funext r
      simp [c, r.2]
    have hc : F v (fun r => c r) * G v (fun r => c r) ≠ 0 := by
      rw [hcF, hcG]
      exact mul_ne_zero (left_ne_zero_of_mul hσ) (right_ne_zero_of_mul hτ)
    have hcount := hw c hc
    have hinj : Function.Injective c := by
      intro x y hxy
      have h1 := hcount (c x)
      rw [hw1] at h1
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h1
      have hx : x ∈ ({z} : Finset (Fin m)) := by
        rw [← hz]
        simp
      have hy : y ∈ ({z} : Finset (Fin m)) := by
        rw [← hz]
        simp [hxy]
      rw [Finset.mem_singleton] at hx hy
      rw [hx, hy]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    -- `σ y` with `y ∈ R v`; its `τ`-preimage must lie in `R v`
    refine Finset.mem_image.mpr ⟨τ.symm (σ y), ?_, by simp⟩
    by_contra hx
    have hcx : c (τ.symm (σ y)) = σ y := by simp [c, hx]
    have hcy : c y = σ y := by simp [c, hy]
    have hxy := hinj (hcx.trans hcy.symm)
    rw [hxy] at hx
    exact hx hy
  let C : Fin n → Finset (Fin m) := fun v =>
    if h : ∃ σ, a v σ ≠ 0 then (R v).image h.choose else ∅
  refine choose_le_of_equivariant_split m k n R C hR a ?_ ?_
  · intro v σ hσ
    have h : ∃ σ, a v σ ≠ 0 := ⟨σ, hσ⟩
    simp only [C, dite_eq_left h]
    exact Finset.Subset.antisymm (sub v σ _ hσ h.choose_spec) (sub v _ σ h.choose_spec hσ)
  · intro σ
    have := hsum (fun r => σ r)
    rw [ite_eq_left σ.bijective] at this
    exact this

end Bridge

end PvsNP
