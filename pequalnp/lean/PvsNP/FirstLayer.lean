import Mathlib
import PvsNP.PermanentLaplace

/-!
# First-layer lower bound for the permanent, with no symmetry assumption

A "first-layer term" is a product `ℓ(row i) * G(A)` where `ℓ` is a linear form in a single row
of the matrix `A` and `G` is an arbitrary function of the whole matrix.  Laplace expansion along a
row writes the `m × m` permanent as a sum of `m` such terms, all reading the same row.

The main theorem `le_of_permanent_eq_sum_row_linear_mul` says that `m` terms are needed even when
different terms are allowed to read different rows, and with no assumption whatsoever on the
cofactors `G`: over any field, if

  `A.permanent = ∑ v : Fin n, (∑ j, c v j * A (i v) j) * G v A`   for all `A`,

then `m ≤ n`.  Equivalently: the permanent does not vanish identically on the common zero set of
fewer than `m` linear forms, each of which involves a single row.

The proof goes through the key lemma `exists_permanent_ne_zero_of_codim_lt`: if `V i` is a
subspace of `K^m` for each row `i` and the codimensions of the `V i` add up to less than `m`,
then some matrix whose `i`-th row lies in `V i` has nonzero permanent.  This is proved by
induction on `m`, deleting a row whose subspace is everything and a column `j` such that the
basis vector `e_j` lies outside one of the proper subspaces.

`exists_permanent_eq_sum_row_linear_mul` records that the bound is attained (Laplace expansion
along row `0`).
-/

namespace PvsNP

open Matrix Module

section Laplace

variable {R : Type*} [CommRing R]

/-- If row `i0` of `A` is the basis vector `e_j`, then the permanent of `A` is the permanent of
the minor obtained by deleting row `i0` and column `j`. -/
theorem permanent_eq_of_row_single {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (i0 j : Fin (m + 1)) (h : A i0 = Pi.single j 1) :
    A.permanent = (A.submatrix i0.succAbove j.succAbove).permanent := by
  have h1 : A.permanent = ((Aᵀ).submatrix id i0.cycleRange.symm).permanent := by
    rw [permanent_permute_rows, permanent_transpose]
  rw [h1, permanent_succ_column_zero, Finset.sum_eq_single j]
  · have h2 : ((Aᵀ).submatrix id i0.cycleRange.symm).submatrix j.succAbove Fin.succ
        = (A.submatrix i0.succAbove j.succAbove)ᵀ := by
      ext a b
      simp [Fin.cycleRange_symm_succ]
    rw [h2, permanent_transpose]
    simp [Fin.cycleRange_symm_zero, h]
  · intro b _ hb
    simp [Fin.cycleRange_symm_zero, h, hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Laplace expansion of the permanent along row `0`. -/
theorem permanent_succ_row_zero {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    A.permanent = ∑ j : Fin (m + 1), A 0 j * (A.submatrix Fin.succ j.succAbove).permanent := by
  rw [← permanent_transpose, permanent_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← permanent_transpose (A.submatrix Fin.succ j.succAbove)]
  rfl

end Laplace

variable {K : Type*} [Field K]

/-- Deleting one coordinate lowers the dimension of a subspace by at most one. -/
theorem finrank_le_finrank_map_funLeft_succAbove_add_one {m : ℕ}
    (V : Submodule K (Fin (m + 1) → K)) (j : Fin (m + 1)) :
    finrank K V ≤ finrank K (V.map (LinearMap.funLeft K K j.succAbove)) + 1 := by
  set π : (Fin (m + 1) → K) →ₗ[K] (Fin m → K) := LinearMap.funLeft K K j.succAbove with hπ
  let f : V →ₗ[K] (V.map π) × K :=
    LinearMap.prod
      ((π.domRestrict V).codRestrict (V.map π) (fun x => Submodule.mem_map_of_mem x.2))
      ((LinearMap.proj j).comp V.subtype)
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : π (x : Fin (m + 1) → K) = π (y : Fin (m + 1) → K) :=
      congrArg (fun p : (V.map π) × K => (p.1 : Fin m → K)) hxy
    have h2 : (x : Fin (m + 1) → K) j = (y : Fin (m + 1) → K) j :=
      congrArg (fun p : (V.map π) × K => p.2) hxy
    ext k
    rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k', rfl⟩
    · exact h2
    · exact congrFun h1 k'
  calc finrank K V ≤ finrank K ((V.map π) × K) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = finrank K (V.map π) + 1 := by rw [Module.finrank_prod, Module.finrank_self]

/-- Deleting coordinate `j` does not lower the dimension of a subspace that does not contain the
basis vector `e_j`. -/
theorem finrank_le_finrank_map_funLeft_succAbove {m : ℕ}
    (V : Submodule K (Fin (m + 1) → K)) (j : Fin (m + 1)) (hj : Pi.single j (1 : K) ∉ V) :
    finrank K V ≤ finrank K (V.map (LinearMap.funLeft K K j.succAbove)) := by
  set π : (Fin (m + 1) → K) →ₗ[K] (Fin m → K) := LinearMap.funLeft K K j.succAbove with hπ
  let f : V →ₗ[K] (V.map π) :=
    (π.domRestrict V).codRestrict (V.map π) (fun x => Submodule.mem_map_of_mem x.2)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ∀ k', (x : Fin (m + 1) → K) (j.succAbove k') = 0 := fun k' =>
      congrFun (congrArg (fun p : V.map π => (p : Fin m → K)) hx) k'
    by_cases hxj : (x : Fin (m + 1) → K) j = 0
    · apply Subtype.ext
      funext k
      rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k', rfl⟩
      · exact hxj
      · exact h1 k'
    · exfalso
      apply hj
      have h3 : ((x : Fin (m + 1) → K) j)⁻¹ • (x : Fin (m + 1) → K) = Pi.single j (1 : K) := by
        funext k
        rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k', rfl⟩
        · simp [hxj]
        · simp [h1 k']
      rw [← h3]
      exact V.smul_mem _ x.2
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- **Key lemma.**  Let `V i` be a subspace of `K^m` for each row `i`, of codimension at most
`d i`, with `∑ i, d i < m`.  Then there is a matrix whose `i`-th row lies in `V i` for every `i`
and whose permanent is nonzero. -/
theorem exists_permanent_ne_zero_of_codim_lt :
    ∀ (m : ℕ) (V : Fin m → Submodule K (Fin m → K)) (d : Fin m → ℕ),
      (∀ i, m ≤ finrank K (V i) + d i) → ∑ i, d i < m →
      ∃ A : Matrix (Fin m) (Fin m) K, (∀ i, A i ∈ V i) ∧ A.permanent ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro V d _ h
    simp at h
  | succ m ih =>
    intro V d hd hsum
    -- a subspace of codimension `0` is everything
    have htop : ∀ i, d i = 0 → V i = ⊤ := by
      intro i hi
      apply Submodule.eq_top_of_finrank_eq
      have h1 := hd i
      have h2 := Submodule.finrank_le (V i)
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2 ⊢
      omega
    -- some row has codimension `0`
    obtain ⟨i0, hi0⟩ : ∃ i0, d i0 = 0 := by
      by_contra! hcon
      have h1 : ∑ _i : Fin (m + 1), 1 ≤ ∑ i, d i :=
        Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hcon i)
      simp at h1
      omega
    have hV0 : V i0 = ⊤ := htop i0 hi0
    by_cases hall : ∀ i, V i = ⊤
    · exact ⟨1, fun i => by rw [hall i]; trivial, by rw [permanent_one]; exact one_ne_zero⟩
    obtain ⟨i1, hi1⟩ := not_forall.mp hall
    -- a basis vector outside `V i1`
    obtain ⟨j, hj⟩ : ∃ j, Pi.single j (1 : K) ∉ V i1 := by
      by_contra! hcon
      apply hi1
      rw [eq_top_iff]
      intro x _
      have hx : x = ∑ j, x j • Pi.single j (1 : K) := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hx]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcon j)
    have hi10 : i1 ≠ i0 := by
      rintro rfl
      exact hi1 hV0
    obtain ⟨i1', rfl⟩ := Fin.exists_succAbove_eq hi10
    have hd1 : 1 ≤ d (i0.succAbove i1') := by
      by_contra hcon
      exact hi1 (htop _ (by omega))
    let W : Fin m → Submodule K (Fin m → K) := fun i' =>
      (V (i0.succAbove i')).map (LinearMap.funLeft K K j.succAbove)
    let d' : Fin m → ℕ := fun i' => d (i0.succAbove i') - if i' = i1' then 1 else 0
    have hd' : ∀ i', m ≤ finrank K (W i') + d' i' := by
      intro i'
      have h1 := hd (i0.succAbove i')
      by_cases h : i' = i1'
      · subst h
        have h2 : finrank K (V (i0.succAbove i')) ≤ finrank K (W i') :=
          finrank_le_finrank_map_funLeft_succAbove (V (i0.succAbove i')) j hj
        simp only [d', ↓reduceIte]
        omega
      · have h2 : finrank K (V (i0.succAbove i')) ≤ finrank K (W i') + 1 :=
          finrank_le_finrank_map_funLeft_succAbove_add_one (V (i0.succAbove i')) j
        simp only [d', h, ↓reduceIte]
        omega
    have hsum' : ∑ i', d' i' < m := by
      have h1 : ∑ i, d i = d i0 + ∑ i', d (i0.succAbove i') := Fin.sum_univ_succAbove d i0
      have h2 : ∑ i', d' i' + 1 = ∑ i', d (i0.succAbove i') := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i1'),
          ← Finset.add_sum_erase (f := fun i' => d (i0.succAbove i')) _ (Finset.mem_univ i1')]
        have h3 : ∑ x ∈ Finset.univ.erase i1', d' x
            = ∑ x ∈ Finset.univ.erase i1', d (i0.succAbove x) :=
          Finset.sum_congr rfl fun x hx => by simp [d', Finset.ne_of_mem_erase hx]
        rw [h3]
        simp only [d', ↓reduceIte]
        omega
      omega
    obtain ⟨B, hB, hBperm⟩ := ih W d' hd' hsum'
    choose x hxV hxB using fun i' => Submodule.mem_map.mp (hB i')
    -- put `e_j` in row `i0` and the lifted rows of `B` in the other rows
    let A : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
      Matrix.of (Fin.insertNth (α := fun _ => Fin (m + 1) → K) i0 (Pi.single j 1) x)
    have hA0 : A i0 = Pi.single j 1 :=
      Fin.insertNth_apply_same (α := fun _ => Fin (m + 1) → K) i0 _ x
    have hAs : ∀ i', A (i0.succAbove i') = x i' := fun i' =>
      Fin.insertNth_apply_succAbove (α := fun _ => Fin (m + 1) → K) i0 _ x i'
    refine ⟨A, ?_, ?_⟩
    · rw [Fin.forall_iff_succAbove i0]
      refine ⟨?_, fun i' => ?_⟩
      · rw [hA0, hV0]
        trivial
      · rw [hAs]
        exact hxV i'
    · rw [permanent_eq_of_row_single A i0 j hA0]
      have hsub : A.submatrix i0.succAbove j.succAbove = B := by
        ext a b
        rw [submatrix_apply, hAs, ← hxB a]
        rfl
      rw [hsub]
      exact hBperm

/-- The key lemma stated with the actual codimensions: if `∑ i, (m - dim (V i)) < m`, some
matrix with `i`-th row in `V i` has nonzero permanent. -/
theorem exists_permanent_ne_zero_of_sum_codim_lt (m : ℕ) (V : Fin m → Submodule K (Fin m → K))
    (h : ∑ i, (m - finrank K (V i)) < m) :
    ∃ A : Matrix (Fin m) (Fin m) K, (∀ i, A i ∈ V i) ∧ A.permanent ≠ 0 :=
  exists_permanent_ne_zero_of_codim_lt m V (fun i => m - finrank K (V i)) (fun i => by omega) h

/-- **First-layer lower bound, no symmetry assumption.**  If the `m × m` permanent over a field
is written as a sum of `n` terms, each of which is a linear form in a single row `i v` (with
coefficients `c v`) times an *arbitrary* function `G v` of the matrix, then `m ≤ n`.  Terms are
allowed to read different rows. -/
theorem le_of_permanent_eq_sum_row_linear_mul {m n : ℕ} (i : Fin n → Fin m)
    (c : Fin n → Fin m → K) (G : Fin n → Matrix (Fin m) (Fin m) K → K)
    (h : ∀ A : Matrix (Fin m) (Fin m) K,
      A.permanent = ∑ v : Fin n, (∑ j, c v j * A (i v) j) * G v A) :
    m ≤ n := by
  by_contra! hlt
  -- the linear forms attached to row `i'`, bundled into one linear map
  let L : ∀ i' : Fin m, (Fin m → K) →ₗ[K] ({v : Fin n // i v = i'} → K) := fun i' =>
    LinearMap.pi fun v => ∑ j, c v.1 j • LinearMap.proj j
  let V : Fin m → Submodule K (Fin m → K) := fun i' => LinearMap.ker (L i')
  let d : Fin m → ℕ := fun i' => Fintype.card {v : Fin n // i v = i'}
  have hd : ∀ i', m ≤ finrank K (V i') + d i' := by
    intro i'
    have h1 := LinearMap.finrank_range_add_finrank_ker (L i')
    have h2 := Submodule.finrank_le (LinearMap.range (L i'))
    rw [Module.finrank_fintype_fun_eq_card] at h1 h2
    simp only [Fintype.card_fin] at h1
    simp only [V, d]
    omega
  have hsum : ∑ i', d i' < m := by
    have h1 : ∑ i', d i' = n := by
      simp only [d, Fintype.card_subtype]
      rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
      simp
    omega
  obtain ⟨A, hA, hperm⟩ := exists_permanent_ne_zero_of_codim_lt m V d hd hsum
  apply hperm
  rw [h A]
  apply Finset.sum_eq_zero
  intro v _
  have h3 : L (i v) (A (i v)) ⟨v, rfl⟩ = 0 := by
    rw [LinearMap.mem_ker.mp (hA (i v))]
    rfl
  have h4 : ∑ j, c v j * A (i v) j = 0 := by
    simpa [L] using h3
  rw [h4, zero_mul]

/-- The bound `m ≤ n` is attained: Laplace expansion along row `0` writes the `m × m` permanent
(`m ≥ 1`) as a sum of `m` terms of the allowed shape, all reading row `0`. -/
theorem exists_permanent_eq_sum_row_linear_mul (m : ℕ) :
    ∃ (i : Fin (m + 1) → Fin (m + 1)) (c : Fin (m + 1) → Fin (m + 1) → K)
      (G : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) K → K),
      ∀ A : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
        A.permanent = ∑ v : Fin (m + 1), (∑ j, c v j * A (i v) j) * G v A := by
  refine ⟨fun _ => 0, fun v j => if j = v then 1 else 0,
    fun v A => (A.submatrix Fin.succ v.succAbove).permanent, fun A => ?_⟩
  rw [permanent_succ_row_zero]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp

end PvsNP
