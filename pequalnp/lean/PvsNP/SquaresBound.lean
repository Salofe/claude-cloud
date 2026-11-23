import PvsNP.Squares
import PvsNP.SplitRank

/-!
# The square construction as a bound on the mixed split rank, for every `k`

Rows and columns of the matrix are indexed by `κ ⊕ κ`, with `k = card κ ≥ 1`; `K` is any field.
In the language of `SplitRank.lean` (`IsSplitProduct`, `MixedSplitLE`, `BorderMixedSplitLE`),
with `k` rows against `k`:

* `borderMixedSplit_perm_squares`: the `2k × 2k` permanent has border mixed split rank at most
  `C(2k, k) / 2 + numWeights κ`;
* `mixedSplit_perm_squares`: it is an exact sum of `C(2k, k) / 2 + 2 * numWeights κ` split
  products;
* `borderMixedSplit_perm_squares_sub_one`: if `2 ^ (k - 1) ≠ 1` in `K` (for instance in
  characteristic zero with `k ≥ 2`, `borderMixedSplit_perm_squares_sub_one_of_charZero`), the
  border bound improves by one, to `C(2k, k) / 2 + numWeights κ - 1`.

Here `C(2k, k) / 2` is the number of pairings `{S, Sᶜ}` (`card_pairings`) and `numWeights κ`
is the number of `w : κ → {0, 1, 2}` with sum `k`, the central trinomial coefficient
`1, 3, 7, 19, 51, …` (`numWeights_eq_coeff`: the coefficient of `X ^ k` in
`(1 + X + X ^ 2) ^ k`; `numWeights_fin_two`, …, `numWeights_fin_five`). Laplace expansion has
`C(2k, k)` terms.

For matrices indexed by `Fin (k + k)`: `borderMixedSplit_perm_fin`, `mixedSplit_perm_fin`,
`borderMixedSplit_perm_fin_sub_one`, and for concrete sizes

* `mixedSplit_perm_ten`: the `10 × 10` permanent is an exact sum of `228` split products, five
  rows against five; Laplace expansion has `252` terms, so it is NOT optimal for exact
  decompositions (`exists_mixedSplit_perm_ten_lt_laplace`);
* `borderMixedSplit_perm_eight` (`54`), `borderMixedSplit_perm_ten` (`177`), any field;
  `borderMixedSplit_perm_eight_sub_one` (`53`), `borderMixedSplit_perm_ten_sub_one` (`176`),
  `borderMixedSplit_perm_six_of_squares` (`16`), characteristic zero;
* `borderMixedSplit_perm_four_of_squares`: at `4 × 4` the merged bound is `3 + 3 - 1 = 5`, the
  optimal value, for any field.

## The proof

1. `mul_permanent_eq_squares_half` (`Squares.lean`): with `q₁ S = blockForm A inl S`,
   `q₂ S = blockForm A inr S`, `X S = q₁ S + lam * q₂ S` and the sums over the sets `S` that
   contain a fixed row `r₀`,
   `lam * perm = ∑ X S * X Sᶜ - ∑ q₁ S * q₁ Sᶜ - lam ^ 2 * ∑ q₂ S * q₂ Sᶜ`.
2. Each square `X S * X Sᶜ` is a split product for `S` (`blockML`, `isSplitProduct_square`), and
   it vanishes unless `S` has `k` elements (`blockForm_eq_zero_of_card_ne`).
3. The leftover `∑ q₁ S * q₁ Sᶜ` is the permanent of the matrix `garbMat r₀ A` whose two blocks
   of columns are both the first block of `A`, with row `r₀` set to zero on the second copy
   (`permanent_garbMat`; the zero row selects one set of each pairing, so nothing is divided by
   `2` and the argument works in every characteristic).
4. Laplace expansion of that permanent along the first block of ROWS is a sum over the sets `C`
   of columns (`permanent_eq_sum_permML`). The weight `wt C : κ → {0, 1, 2}` counts how many of
   the two copies of each column are in `C`. Because the second block of rows of `garbMat` has
   two equal blocks of columns, its factor only depends on the weight of `C`
   (`permML_dup_compl_congr`, by exchanging copies of columns). So all `C` of the same weight
   can be collected into ONE product (`garbLeft`, `garbRight`, `permanent_garbMat_eq_sum`),
   which is zero unless the weight has sum `k`: `sum_blockForm_inl_eq_sum_weights`. This gives
   `numWeights κ` split products, all for the first block of rows
   (`mixedSplit_leftover_inl`). No counting of fibres is needed for this step.
5. The second leftover is the first one after exchanging the two blocks of columns
   (`mixedSplit_leftover_inr`, by `MixedSplitLE.comp_rowLinear`). Dividing by `lam` gives the
   border bound, with error term `lam * ∑ q₂ S * q₂ Sᶜ`; putting `lam = 1` gives the exact
   bound.
6. For the bound with one term fewer, the leftover of weight `(1, …, 1)` is computed:
   it is `2 ^ (k - 1) * q₁ S₀ * q₁ S₀ᶜ` for the splitting `S₀` into the two blocks of rows
   (`garb_one_eq`; here the embeddings whose image has weight `(1, …, 1)` are counted,
   `sum_embedding_wt_one`). With `c = 2 ^ (k - 1)` and `a = (1 - c)⁻¹`,
   `X S₀ * X S₀ᶜ - c * q₁ S₀ * q₁ S₀ᶜ` is the single product
   `(1 - c) * (q₁ S₀ + lam * a * q₂ S₀) * (q₁ S₀ᶜ + lam * a * q₂ S₀ᶜ)` plus a multiple of
   `lam ^ 2 * q₂ S₀ * q₂ S₀ᶜ`, which goes into the error term (`merge_algebra`).

Compared with the usual statement of the construction (leftover `= 2 ^ (k - 1)` times a sum
over `w` of products of two "weight forms"), the factors `garbLeft`, `garbRight` here are
sums of permanents on sets of columns of a given weight; the number of terms is the same.

Also here: `IsSplitProduct.comp_rowLinear`, `MixedSplitLE.comp_rowLinear` (a linear map applied
to every row), `IsSplitProduct.reindex`, `MixedSplitLE.reindex`, `BorderMixedSplitLE.reindex`
(renaming rows and columns), `permanent_submatrix_equiv`, `mixedSplitLE_of_fintype_sub`.
-/

namespace PvsNP

open Finset Matrix

section Blocks

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- `blockForm` vanishes on sets of rows that do not have exactly `card κ` elements. -/
theorem blockForm_eq_zero_of_card_ne (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) (side : κ → κ ⊕ κ)
    (S : Finset (κ ⊕ κ)) (hS : S.card ≠ Fintype.card κ) : blockForm A side S = 0 := by
  unfold blockForm
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [ite_eq_right]
  rintro rfl
  exact hS (by simp)

/-- An embedding of `κ` with image `S` identifies `κ` with `S`. -/
noncomputable def equivOfMap (f : κ ↪ κ ⊕ κ) {S : Finset (κ ⊕ κ)} (h : univ.map f = S) :
    κ ≃ S :=
  Equiv.ofBijective (fun j => ⟨f j, h ▸ mem_map_of_mem f (mem_univ j)⟩)
    ⟨fun a b hab => f.injective (Subtype.ext_iff.mp hab), by
      subst h
      rintro ⟨r, hr⟩
      obtain ⟨j, -, rfl⟩ := mem_map.mp hr
      exact ⟨j, rfl⟩⟩

omit [DecidableEq κ] in
@[simp] theorem equivOfMap_apply (f : κ ↪ κ ⊕ κ) {S : Finset (κ ⊕ κ)} (h : univ.map f = S)
    (j : κ) : (equivOfMap f h j : κ ⊕ κ) = f j := rfl

/-- `blockForm A side S` as a multilinear form in the rows of `A` that belong to `S`. -/
noncomputable def blockML (side : κ → κ ⊕ κ) (S : Finset (κ ⊕ κ)) :
    MultilinearMap (RingHom.id K) (fun _ : S => κ ⊕ κ → K) K :=
  ∑ f : κ ↪ κ ⊕ κ, if h : univ.map f = S then
    ((MultilinearMap.mkPiAlgebra K κ K).compLinearMap
      fun j => LinearMap.proj (side j)).domDomCongr (equivOfMap f h)
  else 0

theorem blockML_apply (side : κ → κ ⊕ κ) (S : Finset (κ ⊕ κ)) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    blockML side S (fun r : S => A r) = blockForm A side S := by
  simp only [blockML, blockForm, sum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : univ.map f = S
  · rw [dite_eq_left h, ite_eq_left h]
    simp [pick]
  · rw [dite_eq_right h, ite_eq_right h]
    rfl

/-- Each square `X S * X Sᶜ` of the square construction is a split product for `S`. -/
theorem isSplitProduct_square (lam : K) (S : Finset (κ ⊕ κ)) :
    IsSplitProduct S (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
      (blockForm A Sum.inl S + lam * blockForm A Sum.inr S)
        * (blockForm A Sum.inl Sᶜ + lam * blockForm A Sum.inr Sᶜ)) := by
  refine ⟨blockML Sum.inl S + lam • blockML Sum.inr S,
    blockML Sum.inl Sᶜ + lam • blockML Sum.inr Sᶜ, fun A => ?_⟩
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [blockML_apply, blockML_apply, blockML_apply, blockML_apply]

/-- A form of the rows of `S` times a form of the other rows is a split product for `S`. -/
theorem isSplitProduct_blockForm_mul (side side' : κ → κ ⊕ κ) (S : Finset (κ ⊕ κ)) :
    IsSplitProduct S (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
      blockForm A side S * blockForm A side' Sᶜ) :=
  ⟨blockML side S, blockML side' Sᶜ, fun A => by rw [blockML_apply, blockML_apply]⟩

end Blocks

section Garbage

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- Forget to which block a column belongs. -/
def fold : κ ⊕ κ → κ := Sum.elim id id

/-- The weight of a set `C` of columns: how many of the two columns `inl j`, `inr j` it
contains. -/
def wt (C : Finset (κ ⊕ κ)) (j : κ) : Fin 3 :=
  if Sum.inl j ∈ C then (if Sum.inr j ∈ C then 2 else 1) else (if Sum.inr j ∈ C then 1 else 0)

theorem sum_wt (C : Finset (κ ⊕ κ)) : ∑ j, (wt C j : ℕ) = C.card := by
  have h : C.card = ∑ x : κ ⊕ κ, if x ∈ C then 1 else 0 := by simp
  rw [h, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : Sum.inl j ∈ C <;> by_cases h2 : Sum.inr j ∈ C <;> simp [wt, h1, h2]

/-- The permanent of the `k` vectors `v j : κ ⊕ κ → K` (as rows) on the set of columns `C`,
as a multilinear form in the vectors. It is zero unless `C` has `card κ` elements. -/
noncomputable def permML (C : Finset (κ ⊕ κ)) :
    MultilinearMap (RingHom.id K) (fun _ : κ => κ ⊕ κ → K) K :=
  ∑ f : κ ↪ κ ⊕ κ, if univ.map f = C then
    (MultilinearMap.mkPiAlgebra K κ K).compLinearMap fun j => LinearMap.proj (f j)
  else 0

theorem permML_apply (C : Finset (κ ⊕ κ)) (v : κ → κ ⊕ κ → K) :
    permML C v = ∑ f : κ ↪ κ ⊕ κ, if univ.map f = C then ∏ j, v j (f j) else 0 := by
  simp only [permML, sum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : univ.map f = C
  · rw [ite_eq_left h, ite_eq_left h]
    simp
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

theorem permML_eq_zero (C : Finset (κ ⊕ κ)) (h : C.card ≠ Fintype.card κ) :
    permML (K := K) C = 0 := by
  unfold permML
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [ite_eq_right]
  rintro rfl
  exact h (by simp)

theorem blockForm_transpose (M : Matrix (κ ⊕ κ) (κ ⊕ κ) K) (side : κ → κ ⊕ κ)
    (C : Finset (κ ⊕ κ)) : blockForm Mᵀ side C = permML C (fun j => M (side j)) := by
  rw [permML_apply]
  rfl

/-- Laplace expansion of the permanent along the first block of ROWS. -/
theorem permanent_eq_sum_permML (M : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    M.permanent = ∑ C : Finset (κ ⊕ κ),
      permML C (fun j => M (Sum.inl j)) * permML Cᶜ (fun j => M (Sum.inr j)) := by
  rw [← permanent_transpose, permanent_eq_sum_blockForm]
  simp only [blockForm_transpose]

/-- Copy the first block of a row onto the second block. -/
def dup : (κ ⊕ κ → K) →ₗ[K] (κ ⊕ κ → K) where
  toFun v := fun x => v (Sum.inl (fold x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Keep the first block of a row and put zero on the second block. -/
def dupZ : (κ ⊕ κ → K) →ₗ[K] (κ ⊕ κ → K) where
  toFun v := Sum.elim (fun j => v (Sum.inl j)) (fun _ => 0)
  map_add' u v := by ext x; cases x <;> simp
  map_smul' c v := by ext x; cases x <;> simp

/-- The matrix whose two blocks of columns are both the first block of `A`, except that the
row `r₀` is zero on the second block. -/
def garbMat (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) : Matrix (κ ⊕ κ) (κ ⊕ κ) K :=
  Matrix.of fun r => Sum.elim (fun j => A r (Sum.inl j))
    (fun j => if r = r₀ then 0 else A r (Sum.inl j))

theorem blockForm_garbMat_inl (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K)
    (S : Finset (κ ⊕ κ)) : blockForm (garbMat r₀ A) Sum.inl S = blockForm A Sum.inl S := by
  simp [blockForm, pick, garbMat]

theorem blockForm_garbMat_inr (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K)
    (T : Finset (κ ⊕ κ)) :
    blockForm (garbMat r₀ A) Sum.inr T = if r₀ ∈ T then 0 else blockForm A Sum.inl T := by
  unfold blockForm
  split_ifs with h
  · refine Finset.sum_eq_zero fun f _ => ?_
    by_cases hf : univ.map f = T
    · rw [ite_eq_left hf]
      subst hf
      obtain ⟨j, -, hj⟩ := mem_map.mp h
      exact Finset.prod_eq_zero (mem_univ j) (by simp [garbMat, hj])
    · rw [ite_eq_right hf]
  · refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hf : univ.map f = T
    · rw [ite_eq_left hf, ite_eq_left hf]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hne : f j ≠ r₀ := by
        rintro rfl
        exact h (hf ▸ mem_map_of_mem f (mem_univ j))
      simp [garbMat, hne]
    · rw [ite_eq_right hf, ite_eq_right hf]

/-- The first-block leftovers of the squares, one for each pairing, are the permanent of
`garbMat r₀ A`. -/
theorem permanent_garbMat (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    (garbMat r₀ A).permanent = ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
      blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ := by
  rw [permanent_eq_sum_blockForm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [blockForm_garbMat_inl, blockForm_garbMat_inr]
  by_cases h : r₀ ∈ S <;> simp [h]

omit [Fintype κ] in
theorem garbMat_inr (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) (j : κ) :
    garbMat (Sum.inl j₀) A (Sum.inr j) = dup (A (Sum.inr j)) := by
  funext x
  cases x <;> simp [garbMat, dup, fold]

omit [Fintype κ] in
theorem garbMat_inl (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) (j : κ) :
    garbMat (Sum.inl j₀) A (Sum.inl j) = (if j = j₀ then dupZ else dup) (A (Sum.inl j)) := by
  funext x
  by_cases h : j = j₀ <;> cases x <;> simp [garbMat, dup, dupZ, fold, h]

/-! ### Exchanging the two copies of some columns -/

/-- Exchange the columns `inl j` and `inr j` for the `j` in `J`. -/
def swapOn (J : Finset κ) (x : κ ⊕ κ) : κ ⊕ κ := if fold x ∈ J then x.swap else x

omit [Fintype κ] [DecidableEq κ] in
theorem fold_swap (x : κ ⊕ κ) : fold x.swap = fold x := by cases x <;> rfl

omit [Fintype κ] in
theorem fold_swapOn (J : Finset κ) (x : κ ⊕ κ) : fold (swapOn J x) = fold x := by
  unfold swapOn
  split_ifs <;> simp [fold_swap]

omit [Fintype κ] in
theorem swapOn_involutive (J : Finset κ) : Function.Involutive (swapOn J) := by
  intro x
  by_cases h : fold x ∈ J
  · simp [swapOn, h, fold_swap]
  · simp [swapOn, h]

/-- `swapOn J` as a permutation of the columns. -/
def swapPerm (J : Finset κ) : Equiv.Perm (κ ⊕ κ) := (swapOn_involutive J).toPerm

/-- Composing embeddings with a permutation of the target. -/
def embPost (ρ : Equiv.Perm (κ ⊕ κ)) : (κ ↪ κ ⊕ κ) ≃ (κ ↪ κ ⊕ κ) where
  toFun f := f.trans ρ.toEmbedding
  invFun f := f.trans ρ.symm.toEmbedding
  left_inv f := by ext j; simp
  right_inv f := by ext j; simp

/-- On rows whose two blocks are equal, the permanent on the columns `D` does not change when
some columns of `D` are replaced by their copies. -/
theorem permML_dup_map (J : Finset κ) (D : Finset (κ ⊕ κ)) (v : κ → κ ⊕ κ → K) :
    permML (D.map (swapPerm J).toEmbedding) (fun j => dup (v j)) =
      permML D (fun j => dup (v j)) := by
  rw [permML_apply, permML_apply]
  symm
  refine Fintype.sum_equiv (embPost (swapPerm J)) _ _ fun f => ?_
  have h1 : univ.map (embPost (swapPerm J) f) = (univ.map f).map (swapPerm J).toEmbedding := by
    simp [embPost, Finset.map_map]
  rw [h1]
  have h3 : ∏ j, dup (v j) (embPost (swapPerm J) f j) = ∏ j, dup (v j) (f j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [dup, embPost, swapPerm, fold_swapOn]
  rw [h3]
  by_cases h : univ.map f = D
  · rw [ite_eq_left h, ite_eq_left (Finset.map_inj.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Finset.map_inj.mp h'))]

/-- Two sets of columns with the same weight have complements that differ by exchanging some
columns with their copies. -/
theorem compl_eq_map_of_wt_eq {C C' : Finset (κ ⊕ κ)} (h : wt C = wt C') :
    C'ᶜ = Cᶜ.map (swapPerm
      (univ.filter fun j => ¬(Sum.inl j ∈ C ↔ Sum.inl j ∈ C'))).toEmbedding := by
  ext y
  rw [Finset.mem_map_equiv, mem_compl, mem_compl]
  show y ∉ C' ↔ swapOn _ y ∉ C
  rcases y with j | j
  · have hj := congrFun h j
    unfold wt at hj
    by_cases a : Sum.inl j ∈ C <;> by_cases b : Sum.inr j ∈ C <;>
      by_cases a' : Sum.inl j ∈ C' <;> by_cases b' : Sum.inr j ∈ C' <;>
      simp_all [swapOn, fold]
  · have hj := congrFun h j
    unfold wt at hj
    by_cases a : Sum.inl j ∈ C <;> by_cases b : Sum.inr j ∈ C <;>
      by_cases a' : Sum.inl j ∈ C' <;> by_cases b' : Sum.inr j ∈ C' <;>
      simp_all [swapOn, fold]

theorem permML_dup_compl_congr {C C' : Finset (κ ⊕ κ)} (h : wt C = wt C')
    (v : κ → κ ⊕ κ → K) :
    permML C'ᶜ (fun j => dup (v j)) = permML Cᶜ (fun j => dup (v j)) := by
  rw [compl_eq_map_of_wt_eq h, permML_dup_map]

/-! ### The leftovers as a sum of one split product for each weight -/

/-- The factor in the first block of rows of the leftover term of weight `w`. -/
noncomputable def garbLeft (j₀ : κ) (w : κ → Fin 3) :
    MultilinearMap (RingHom.id K) (fun _ : κ => κ ⊕ κ → K) K :=
  ∑ C ∈ univ.filter (fun C : Finset (κ ⊕ κ) => wt C = w),
    (permML C).compLinearMap fun j => if j = j₀ then dupZ else dup

/-- The factor in the second block of rows of the leftover term of weight `w`. -/
noncomputable def garbRight (w : κ → Fin 3) :
    MultilinearMap (RingHom.id K) (fun _ : κ => κ ⊕ κ → K) K :=
  if h : ∃ C : Finset (κ ⊕ κ), wt C = w then
    (permML (Classical.choose h)ᶜ).compLinearMap fun _ => dup
  else 0

theorem garbLeft_eq_zero (j₀ : κ) (w : κ → Fin 3)
    (hw : ∑ j, (w j : ℕ) ≠ Fintype.card κ) : garbLeft (K := K) j₀ w = 0 := by
  unfold garbLeft
  refine Finset.sum_eq_zero fun C hC => ?_
  rw [permML_eq_zero]
  · ext v
    simp
  · rw [← sum_wt, (mem_filter.mp hC).2]
    exact hw

/-- The permanent of `garbMat (inl j₀) A` as a sum over the weights. -/
theorem permanent_garbMat_eq_sum (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    (garbMat (Sum.inl j₀) A).permanent = ∑ w : κ → Fin 3,
      garbLeft j₀ w (fun j => A (Sum.inl j)) * garbRight w (fun j => A (Sum.inr j)) := by
  rw [permanent_eq_sum_permML,
    ← Finset.sum_fiberwise (univ : Finset (Finset (κ ⊕ κ))) (fun C => wt C)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [garbLeft, sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCw : wt C = w := (mem_filter.mp hC).2
  have hex : ∃ C : Finset (κ ⊕ κ), wt C = w := ⟨C, hCw⟩
  rw [garbRight, dite_eq_left hex, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compLinearMap_apply]
  have h1 : (fun j => garbMat (Sum.inl j₀) A (Sum.inl j)) =
      fun j => (if j = j₀ then dupZ else dup) (A (Sum.inl j)) :=
    funext fun j => garbMat_inl j₀ A j
  have h2 : (fun j => garbMat (Sum.inl j₀) A (Sum.inr j)) = fun j => dup (A (Sum.inr j)) :=
    funext fun j => garbMat_inr j₀ A j
  rw [h1, h2, permML_dup_compl_congr ((Classical.choose_spec hex).trans hCw.symm)]

/-- **The leftovers along one splitting.** The first-block leftovers of the squares (one for
each pairing) are a sum of products of a form in the first block of rows and a form in the
second block of rows, one product for each weight `w : κ → {0, 1, 2}` with sum `card κ`. -/
theorem sum_blockForm_inl_eq_sum_weights (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
        blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ =
      ∑ w : {w : κ → Fin 3 // ∑ j, (w j : ℕ) = Fintype.card κ},
        garbLeft j₀ w.1 (fun j => A (Sum.inl j)) * garbRight w.1 (fun j => A (Sum.inr j)) := by
  rw [← permanent_garbMat, permanent_garbMat_eq_sum]
  refine Eq.trans ?_ (Finset.sum_subtype
    (univ.filter fun w : κ → Fin 3 => ∑ j, (w j : ℕ) = Fintype.card κ) (by simp)
    (fun w => garbLeft j₀ w (fun j => A (Sum.inl j)) * garbRight w (fun j => A (Sum.inr j))))
  symm
  refine Finset.sum_filter_of_ne fun w _ hne => ?_
  by_contra hw
  exact hne (by rw [garbLeft_eq_zero j₀ w hw]; simp)

end Garbage

/-! ### Substituting a linear map in every row -/

section RowLinear

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Applying one linear map to every row of the matrix turns a split product into a split
product for the same row set. -/
theorem IsSplitProduct.comp_rowLinear (L : (ι → K) →ₗ[K] (ι → K)) {S : Finset ι}
    {t : Matrix ι ι K → K} (h : IsSplitProduct S t) :
    IsSplitProduct S (fun A : Matrix ι ι K => t (Matrix.of fun r => L (A r))) := by
  obtain ⟨F, G, hFG⟩ := h
  exact ⟨F.compLinearMap fun _ => L, G.compLinearMap fun _ => L, fun A => (hFG _).trans rfl⟩

/-- Applying one linear map to every row of the matrix does not increase the mixed split
rank. -/
theorem MixedSplitLE.comp_rowLinear (L : (ι → K) →ₗ[K] (ι → K)) {k n : ℕ}
    {f : Matrix ι ι K → K} (h : MixedSplitLE k n f) :
    MixedSplitLE k n (fun A : Matrix ι ι K => f (Matrix.of fun r => L (A r))) := by
  obtain ⟨S, t, hS, ht, hsum⟩ := h
  exact ⟨S, fun v A => t v (Matrix.of fun r => L (A r)), hS,
    fun v => (ht v).comp_rowLinear L, fun A => hsum _⟩

end RowLinear

/-! ### The bounds -/

section Bound

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- The number of weights `w : κ → {0, 1, 2}` with sum `card κ`: the central trinomial
coefficient of `card κ` (`1, 1, 3, 7, 19, 51, …`). -/
def numWeights (κ : Type*) [Fintype κ] [DecidableEq κ] : ℕ :=
  Fintype.card {w : κ → Fin 3 // ∑ j, (w j : ℕ) = Fintype.card κ}

open Polynomial in
/-- `numWeights κ` is the central trinomial coefficient: the coefficient of `X ^ k` in
`(1 + X + X ^ 2) ^ k`, `k = card κ`. -/
theorem numWeights_eq_coeff (κ : Type*) [Fintype κ] [DecidableEq κ] :
    numWeights κ = ((1 + X + X ^ 2 : ℕ[X]) ^ Fintype.card κ).coeff (Fintype.card κ) := by
  have h3 : (1 + X + X ^ 2 : ℕ[X]) = ∑ a : Fin 3, X ^ (a : ℕ) := by
    simp [Fin.sum_univ_three]
  have hpow : (1 + X + X ^ 2 : ℕ[X]) ^ Fintype.card κ =
      ∑ w : κ → Fin 3, X ^ (∑ j, (w j : ℕ)) := by
    rw [h3, ← Finset.card_univ, ← Finset.prod_const, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hpow, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [numWeights, Fintype.card_subtype, Finset.card_filter]
  exact Finset.sum_congr rfl fun w _ => if_congr eq_comm rfl rfl

/-- The sets of `card κ` rows that contain a fixed row `r₀` are half of all sets of `card κ`
rows (one for each pairing `{S, Sᶜ}`). -/
theorem card_pairings (r₀ : κ ⊕ κ) :
    Fintype.card {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ} =
      (2 * Fintype.card κ).choose (Fintype.card κ) / 2 := by
  have hι : Fintype.card (κ ⊕ κ) = 2 * Fintype.card κ := by
    rw [Fintype.card_sum]
    omega
  have hT : (univ.filter fun S : Finset (κ ⊕ κ) => S.card = Fintype.card κ).card =
      (2 * Fintype.card κ).choose (Fintype.card κ) := by
    rw [← hι, ← Fintype.card_finset_len, Fintype.card_subtype]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := univ.filter fun S : Finset (κ ⊕ κ) => S.card = Fintype.card κ) (fun S => r₀ ∈ S)
  rw [Finset.filter_filter, Finset.filter_filter, hT] at hsplit
  have hcompl : ∀ S : Finset (κ ⊕ κ), S.card = Fintype.card κ → Sᶜ.card = Fintype.card κ := by
    intro S hS
    rw [Finset.card_compl, hS, hι]
    omega
  have heq : (univ.filter fun S : Finset (κ ⊕ κ) => S.card = Fintype.card κ ∧ r₀ ∈ S).card =
      (univ.filter fun S : Finset (κ ⊕ κ) => S.card = Fintype.card κ ∧ ¬ r₀ ∈ S).card := by
    refine Finset.card_bij' (fun S _ => Sᶜ) (fun S _ => Sᶜ) ?_ ?_ ?_ ?_
    · intro S hS
      rw [mem_filter] at hS ⊢
      exact ⟨mem_univ _, hcompl S hS.2.1, by simpa using hS.2.2⟩
    · intro S hS
      rw [mem_filter] at hS ⊢
      exact ⟨mem_univ _, hcompl S hS.2.1, by simpa using hS.2.2⟩
    · intro S _
      simp
    · intro S _
      simp
  have hcard : Fintype.card {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ} =
      (univ.filter fun S : Finset (κ ⊕ κ) => S.card = Fintype.card κ ∧ r₀ ∈ S).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext S
    simp [and_comm]
  omega

/-- In the sum of the squares only the sets with `card κ` rows contribute. -/
theorem sum_squares_eq_sum_subtype (r₀ : κ ⊕ κ) (lam : K) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
        (blockForm A Sum.inl S + lam * blockForm A Sum.inr S)
          * (blockForm A Sum.inl Sᶜ + lam * blockForm A Sum.inr Sᶜ) =
      ∑ S : {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ},
        (blockForm A Sum.inl S.1 + lam * blockForm A Sum.inr S.1)
          * (blockForm A Sum.inl S.1ᶜ + lam * blockForm A Sum.inr S.1ᶜ) := by
  refine Eq.trans ?_ (Finset.sum_subtype
    (univ.filter fun S : Finset (κ ⊕ κ) => r₀ ∈ S ∧ S.card = Fintype.card κ) (by simp)
    (fun S => (blockForm A Sum.inl S + lam * blockForm A Sum.inr S)
      * (blockForm A Sum.inl Sᶜ + lam * blockForm A Sum.inr Sᶜ)))
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hc : S.card = Fintype.card κ
  · simp [hc]
  · rw [blockForm_eq_zero_of_card_ne A Sum.inl S hc, blockForm_eq_zero_of_card_ne A Sum.inr S hc]
    simp

/-- The squares, one for each pairing, are a sum of split products. -/
theorem mixedSplit_squares (r₀ : κ ⊕ κ) (lam : K) :
    MixedSplitLE (Fintype.card κ)
      (Fintype.card {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ})
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
          (blockForm A Sum.inl S + lam * blockForm A Sum.inr S)
            * (blockForm A Sum.inl Sᶜ + lam * blockForm A Sum.inr Sᶜ)) :=
  mixedSplitLE_of_fintype
    (fun S : {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ} => S.1)
    (fun S A => (blockForm A Sum.inl S.1 + lam * blockForm A Sum.inr S.1)
      * (blockForm A Sum.inl S.1ᶜ + lam * blockForm A Sum.inr S.1ᶜ))
    (fun S => S.2.2) (fun S => isSplitProduct_square lam S.1)
    (sum_squares_eq_sum_subtype r₀ lam)

/-- Each leftover term is a split product for the first block of rows. -/
theorem isSplitProduct_garb (j₀ : κ) (w : κ → Fin 3) :
    IsSplitProduct (univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ))
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        garbLeft j₀ w (fun j => A (Sum.inl j)) * garbRight w (fun j => A (Sum.inr j))) :=
  isSplitProduct_of_bijective (id : κ ⊕ κ → κ ⊕ κ) Function.bijective_id _
    (fun a => by simp) (fun b => by simp) (garbLeft j₀ w) (garbRight w)

/-- The first-block leftovers of the squares are a sum of `numWeights κ` split products, all
for the first block of rows. -/
theorem mixedSplit_leftover_inl (j₀ : κ) :
    MixedSplitLE (Fintype.card κ) (numWeights κ)
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
          blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ) := by
  have hcard : (univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ)).card = Fintype.card κ := by
    simp
  exact mixedSplitLE_of_fintype
    (fun _ : {w : κ → Fin 3 // ∑ j, (w j : ℕ) = Fintype.card κ} =>
      univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ))
    (fun w A => garbLeft j₀ w.1 (fun j => A (Sum.inl j)) * garbRight w.1 (fun j => A (Sum.inr j)))
    (fun _ => hcard) (fun w => isSplitProduct_garb j₀ w.1) (sum_blockForm_inl_eq_sum_weights j₀)

/-- The second-block leftovers of the squares are a sum of `numWeights κ` split products. -/
theorem mixedSplit_leftover_inr (j₀ : κ) :
    MixedSplitLE (Fintype.card κ) (numWeights κ)
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
          blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ) := by
  refine ((mixedSplit_leftover_inl (K := K) j₀).comp_rowLinear
    (LinearMap.funLeft K K Sum.swap)).congr fun A => ?_
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : ∀ T : Finset (κ ⊕ κ),
      blockForm (Matrix.of fun r => LinearMap.funLeft K K Sum.swap (A r)) Sum.inl T =
        blockForm A Sum.inr T := by
    intro T
    simp [blockForm, pick, LinearMap.funLeft]
  rw [h, h]

/-- **Border bound from the square construction, every `k`.** For the `2k × 2k` permanent
(`k = card κ ≥ 1`, any field), `k` rows against `k`: for a fixed `g`, itself a sum of split
products, and every `lam ≠ 0`, the function `permanent + lam * g` is a sum of
`C(2k, k) / 2 + numWeights κ` split products: one square for each pairing, and one product
for each weight, all on the same pairing. -/
theorem borderMixedSplit_perm_squares [Nonempty κ] :
    BorderMixedSplitLE (Fintype.card κ)
      ((2 * Fintype.card κ).choose (Fintype.card κ) / 2 + numWeights κ)
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K => A.permanent) := by
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  rw [← card_pairings (Sum.inl j₀)]
  refine ⟨fun A => ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
    blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ, _, mixedSplit_leftover_inr j₀,
    fun lam hlam => ?_⟩
  refine (((mixedSplit_squares (Sum.inl j₀) lam).const_mul lam⁻¹).add
    ((mixedSplit_leftover_inl j₀).const_mul (-lam⁻¹))).congr fun A => ?_
  have h := mul_permanent_eq_squares_half (Sum.inl j₀) A lam
  field_simp
  linear_combination h

/-- **Exact bound from the square construction, every `k`.** The `2k × 2k` permanent
(`k = card κ ≥ 1`, any field) is a sum of `C(2k, k) / 2 + 2 * numWeights κ` split products,
`k` rows against `k`. -/
theorem mixedSplit_perm_squares [Nonempty κ] :
    MixedSplitLE (Fintype.card κ)
      ((2 * Fintype.card κ).choose (Fintype.card κ) / 2 + 2 * numWeights κ)
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K => A.permanent) := by
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  rw [← card_pairings (Sum.inl j₀), two_mul, ← add_assoc]
  refine (((mixedSplit_squares (Sum.inl j₀) (1 : K)).add
    ((mixedSplit_leftover_inl j₀).const_mul (-1))).add
    ((mixedSplit_leftover_inr j₀).const_mul (-1))).congr fun A => ?_
  have h := mul_permanent_eq_squares_half (Sum.inl j₀) A (1 : K)
  linear_combination h

end Bound

/-! ### The leftover of weight `(1, …, 1)` -/

section WeightOne

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- A sum over the embeddings with the same image as `side` is a sum over the permutations
of `κ`. -/
theorem sum_embedding_map_eq (side : κ ↪ κ ⊕ κ) (φ : (κ ↪ κ ⊕ κ) → K) :
    ∑ f : κ ↪ κ ⊕ κ, (if univ.map f = univ.map side then φ f else 0) =
      ∑ π : Equiv.Perm κ, φ (π.toEmbedding.trans side) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun π _ => π.toEmbedding.trans side) ?_ ?_ ?_ ?_
  · intro π _
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← Finset.map_map, Finset.map_univ_equiv]
  · intro π _ π' _ h
    ext j
    exact side.injective (DFunLike.congr_fun h j)
  · intro f hf
    have h := (mem_filter.mp hf).2
    refine ⟨(equivOfMap f h).trans (equivOfMap side rfl).symm, mem_univ _, ?_⟩
    ext j
    show side ((equivOfMap side rfl).symm (equivOfMap f h j)) = f j
    rw [← equivOfMap_apply side rfl, Equiv.apply_symm_apply, equivOfMap_apply]
  · intro π _
    rfl

/-- `blockForm` on the image of an embedding `rows` is the permanent of a `k × k` matrix. -/
theorem blockForm_map (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) (side : κ → κ ⊕ κ) (rows : κ ↪ κ ⊕ κ) :
    blockForm A side (univ.map rows) = (Matrix.of fun i j => A (rows i) (side j)).permanent := by
  unfold blockForm
  rw [sum_embedding_map_eq]
  rfl

/-- On rows whose two blocks are equal, the permanent on the first block of columns. -/
theorem permML_map_inl_dup (v : κ → κ ⊕ κ → K) :
    permML (univ.map Function.Embedding.inl) (fun j => dup (v j)) =
      (Matrix.of fun i j => v i (Sum.inl j)).permanent := by
  rw [permML_apply, sum_embedding_map_eq, ← permanent_transpose]
  rfl

theorem compl_map_inl :
    (univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ))ᶜ = univ.map Function.Embedding.inr := by
  ext x
  cases x <;> simp

theorem compl_map_inr :
    (univ.map (Function.Embedding.inr : κ ↪ κ ⊕ κ))ᶜ = univ.map Function.Embedding.inl := by
  ext x
  cases x <;> simp

theorem wt_map_inr : wt (univ.map (Function.Embedding.inr : κ ↪ κ ⊕ κ)) = fun _ => 1 := by
  funext j
  simp [wt]

/-- The second factor of the leftover of weight `(1, …, 1)` is the permanent of the second
block of rows on the first block of columns. -/
theorem garbRight_one (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    garbRight (fun _ => 1) (fun j => A (Sum.inr j)) =
      blockForm A Sum.inl (univ.map Function.Embedding.inl)ᶜ := by
  have hex : ∃ C : Finset (κ ⊕ κ), wt C = fun _ => 1 := ⟨_, wt_map_inr⟩
  rw [garbRight, dite_eq_left hex, MultilinearMap.compLinearMap_apply,
    permML_dup_compl_congr (C := univ.map Function.Embedding.inr) (C' := Classical.choose hex)
      (wt_map_inr.trans (Classical.choose_spec hex).symm),
    compl_map_inr, permML_map_inl_dup, compl_map_inl, blockForm_map]
  rfl

/-- The sum of the permanents on all sets of columns of a given weight, as a sum over
embeddings. -/
theorem sum_permML_wt (w : κ → Fin 3) (u : κ → κ ⊕ κ → K) :
    ∑ C ∈ univ.filter (fun C : Finset (κ ⊕ κ) => wt C = w), permML C u =
      ∑ f : κ ↪ κ ⊕ κ, if wt (univ.map f) = w then ∏ j, u j (f j) else 0 := by
  simp only [permML_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- The embedding that sends `j` to the copy of the column `π j` chosen by `s j`. -/
def sideEmb (π : Equiv.Perm κ) (s : κ → Bool) : κ ↪ κ ⊕ κ where
  toFun j := if s j then Sum.inl (π j) else Sum.inr (π j)
  inj' a b hab := by
    have e : ∀ j, fold (if s j then Sum.inl (π j) else Sum.inr (π j) : κ ⊕ κ) = π j := by
      intro j
      split_ifs <;> rfl
    have h : fold (if s a then Sum.inl (π a) else Sum.inr (π a) : κ ⊕ κ) =
        fold (if s b then Sum.inl (π b) else Sum.inr (π b)) := congrArg fold hab
    rw [e, e] at h
    exact π.injective h

omit [Fintype κ] [DecidableEq κ] in
theorem eq_inl_or_inr (x : κ ⊕ κ) : x = Sum.inl (fold x) ∨ x = Sum.inr (fold x) := by
  cases x <;> simp [fold]

/-- The embeddings whose image has weight `(1, …, 1)` are the `sideEmb π s`. -/
theorem sum_embedding_wt_one (φ : (κ ↪ κ ⊕ κ) → K) :
    ∑ f : κ ↪ κ ⊕ κ, (if wt (univ.map f) = (fun _ => 1) then φ f else 0) =
      ∑ π : Equiv.Perm κ, ∑ s : κ → Bool, φ (sideEmb π s) := by
  rw [← Finset.sum_filter, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => sideEmb p.1 p.2) ?_ ?_ ?_ ?_
  · rintro ⟨π, s⟩ _
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    funext i
    have hl : Sum.inl i ∈ univ.map (sideEmb π s) ↔ s (π.symm i) = true := by
      rw [mem_map]
      constructor
      · rintro ⟨j, -, hj⟩
        have hj' : (if s j then Sum.inl (π j) else Sum.inr (π j) : κ ⊕ κ) = Sum.inl i := hj
        by_cases h : s j = true
        · rw [ite_eq_left h] at hj'
          have hji : π j = i := Sum.inl.inj hj'
          rw [← hji]
          simpa using h
        · rw [ite_eq_right h] at hj'
          exact absurd hj' (by simp)
      · intro h
        refine ⟨π.symm i, mem_univ _, ?_⟩
        show (if s (π.symm i) then Sum.inl (π (π.symm i)) else Sum.inr (π (π.symm i)) : κ ⊕ κ)
          = Sum.inl i
        rw [ite_eq_left h, Equiv.apply_symm_apply]
    have hr : Sum.inr i ∈ univ.map (sideEmb π s) ↔ ¬ s (π.symm i) = true := by
      rw [mem_map]
      constructor
      · rintro ⟨j, -, hj⟩
        have hj' : (if s j then Sum.inl (π j) else Sum.inr (π j) : κ ⊕ κ) = Sum.inr i := hj
        by_cases h : s j = true
        · rw [ite_eq_left h] at hj'
          exact absurd hj' (by simp)
        · rw [ite_eq_right h] at hj'
          have hji : π j = i := Sum.inr.inj hj'
          rw [← hji]
          simpa using h
      · intro h
        refine ⟨π.symm i, mem_univ _, ?_⟩
        show (if s (π.symm i) then Sum.inl (π (π.symm i)) else Sum.inr (π (π.symm i)) : κ ⊕ κ)
          = Sum.inr i
        rw [ite_eq_right h, Equiv.apply_symm_apply]
    unfold wt
    by_cases h : s (π.symm i) = true
    · rw [ite_eq_left (hl.mpr h), ite_eq_right (fun h' => hr.mp h' h)]
    · rw [ite_eq_right (fun h' => h (hl.mp h')), ite_eq_left (hr.mpr h)]
  · rintro ⟨π, s⟩ _ ⟨π', s'⟩ _ h
    have h1 : ∀ j, (if s j then Sum.inl (π j) else Sum.inr (π j) : κ ⊕ κ) =
        if s' j then Sum.inl (π' j) else Sum.inr (π' j) := fun j => DFunLike.congr_fun h j
    have e1 : ∀ (b : Bool) (x : κ), fold (if b then Sum.inl x else Sum.inr x : κ ⊕ κ) = x := by
      intro b x
      cases b <;> rfl
    have e2 : ∀ (b : Bool) (x : κ),
        Sum.isLeft (if b then Sum.inl x else Sum.inr x : κ ⊕ κ) = b := by
      intro b x
      cases b <;> rfl
    have hπ : π = π' := by
      ext j
      have h2 := congrArg fold (h1 j)
      rwa [e1, e1] at h2
    have hs : s = s' := by
      funext j
      have h2 := congrArg Sum.isLeft (h1 j)
      rwa [e2, e2] at h2
    rw [hπ, hs]
  · intro f hf
    have hw := (mem_filter.mp hf).2
    have hinj : Function.Injective (fun j => fold (f j)) := by
      intro a b hab
      by_contra hne
      have hab' : fold (f a) = fold (f b) := hab
      have hfab : f a ≠ f b := fun h => hne (f.injective h)
      have ha : f a ∈ univ.map f := mem_map_of_mem f (mem_univ a)
      have hb : f b ∈ univ.map f := mem_map_of_mem f (mem_univ b)
      have h1 : Sum.inl (fold (f a)) ∈ univ.map f ∧ Sum.inr (fold (f a)) ∈ univ.map f := by
        rcases eq_inl_or_inr (f a) with h | h <;> rcases eq_inl_or_inr (f b) with h' | h'
        · rw [← hab'] at h'
          exact absurd (h.trans h'.symm) hfab
        · rw [← hab'] at h'
          exact ⟨by rw [← h]; exact ha, by rw [← h']; exact hb⟩
        · rw [← hab'] at h'
          exact ⟨by rw [← h']; exact hb, by rw [← h]; exact ha⟩
        · rw [← hab'] at h'
          exact absurd (h.trans h'.symm) hfab
      have hi := congrFun hw (fold (f a))
      unfold wt at hi
      rw [ite_eq_left h1.1, ite_eq_left h1.2] at hi
      exact absurd hi (by decide)
    refine ⟨(Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj),
      fun j => (f j).isLeft), by simp, ?_⟩
    ext j
    show (if (f j).isLeft then Sum.inl (fold (f j)) else Sum.inr (fold (f j)) : κ ⊕ κ) = f j
    generalize f j = x
    cases x <;> rfl
  · rintro ⟨π, s⟩ _
    rfl

/-- Summing over the choices of copies turns each entry into the sum of the two copies. -/
theorem sum_sideEmb_prod (u : κ → κ ⊕ κ → K) (π : Equiv.Perm κ) :
    ∑ s : κ → Bool, ∏ j, u j (sideEmb π s j) =
      ∏ j, (u j (Sum.inl (π j)) + u j (Sum.inr (π j))) := by
  have e : ∀ j, u j (Sum.inl (π j)) + u j (Sum.inr (π j)) =
      ∑ b : Bool, u j (if b then Sum.inl (π j) else Sum.inr (π j)) := by
    intro j
    rw [Fintype.sum_bool]
    rfl
  simp only [e]
  rw [Fintype.prod_sum]
  rfl

/-- The first factor of the leftover of weight `(1, …, 1)` is `2 ^ (k - 1)` times the
permanent of the first block of rows on the first block of columns. -/
theorem garbLeft_one (j₀ : κ) (v : κ → κ ⊕ κ → K) :
    garbLeft j₀ (fun _ => 1) v =
      2 ^ (Fintype.card κ - 1) * (Matrix.of fun i j => v i (Sum.inl j)).permanent := by
  have h1 : garbLeft j₀ (fun _ => 1) v =
      ∑ C ∈ univ.filter (fun C : Finset (κ ⊕ κ) => wt C = fun _ => 1),
        permML C (fun j => (if j = j₀ then dupZ else dup) (v j)) := by
    simp only [garbLeft, sum_apply, MultilinearMap.compLinearMap_apply]
  rw [h1, sum_permML_wt, sum_embedding_wt_one]
  simp only [sum_sideEmb_prod]
  have h2 : ∀ (j i : κ), (if j = j₀ then dupZ else dup) (v j) (Sum.inl i) +
      (if j = j₀ then dupZ else dup) (v j) (Sum.inr i) =
        (if j = j₀ then 1 else 2) * v j (Sum.inl i) := by
    intro j i
    by_cases h : j = j₀
    · simp [h, dupZ]
    · simp [h, dup, fold]
      ring
  simp only [h2, Finset.prod_mul_distrib]
  have h3 : ∏ j : κ, (if j = j₀ then (1 : K) else 2) = 2 ^ (Fintype.card κ - 1) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ j₀), ite_eq_left rfl, one_mul,
      Finset.prod_congr rfl (fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj)),
      Finset.prod_const, Finset.card_erase_of_mem (mem_univ j₀), Finset.card_univ]
  rw [h3, ← Finset.mul_sum, ← permanent_transpose]
  rfl

/-- **The leftover of weight `(1, …, 1)`** is `2 ^ (k - 1)` times the product of the two
first-block forms of the splitting into the two blocks of rows. -/
theorem garb_one_eq (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    garbLeft j₀ (fun _ => 1) (fun j => A (Sum.inl j)) *
        garbRight (fun _ => 1) (fun j => A (Sum.inr j)) =
      2 ^ (Fintype.card κ - 1) *
        (blockForm A Sum.inl (univ.map Function.Embedding.inl) *
          blockForm A Sum.inl (univ.map Function.Embedding.inl)ᶜ) := by
  rw [garbLeft_one, garbRight_one, blockForm_map, mul_assoc]
  rfl

end WeightOne

/-! ### One term fewer: merging the leftover of weight `(1, …, 1)` with a square -/

section Sharp

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- A finite family of split products minus one of its members: one term fewer. -/
theorem mixedSplitLE_of_fintype_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    {T : Type*} [Fintype T] [DecidableEq T] (S : T → Finset ι) (t : T → Matrix ι ι K → K)
    (hS : ∀ v, (S v).card = k) (ht : ∀ v, IsSplitProduct (S v) (t v)) (v₀ : T) :
    MixedSplitLE k (Fintype.card T - 1) (fun A => ∑ v, t v A - t v₀ A) := by
  have h := mixedSplitLE_of_fintype (fun v : {v : T // ¬ v = v₀} => S v.1) (fun v => t v.1)
    (fun v => hS _) (fun v => ht _) (f := fun A => ∑ v, t v A - t v₀ A) (fun A => by
      rw [← Finset.sum_erase_eq_sub (mem_univ v₀)]
      exact Finset.sum_subtype (univ.erase v₀) (by simp) _)
  rwa [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h

/-- The algebra behind the merge: a square `(q + lam p)(q' + lam p')` minus `c q q'` is, up to
a term of order `lam ^ 2`, the single product `(1 - c)(q + lam a p)(q' + lam a p')` with
`a = (1 - c)⁻¹`. -/
theorem merge_algebra (perm G2 p p' q q' sP sW gt lam a c : K) (hlam : lam ≠ 0)
    (ha : (1 - c) * a = 1) (h : lam * perm = sP - sW - lam ^ 2 * G2) (h1 : gt = c * (q * q')) :
    perm + lam * (G2 + -(1 - a) * (p * p')) =
      lam⁻¹ * (sP - (q + lam * p) * (q' + lam * p'))
        + lam⁻¹ * (1 - c) * ((q + lam * a * p) * (q' + lam * a * p'))
        + -lam⁻¹ * (sW - gt) := by
  have hl : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam
  subst h1
  linear_combination lam⁻¹ * h - (perm + lam * (G2 + -(1 - a) * (p * p'))) * hl
    - lam⁻¹ * (lam * (q * p' + p * q') + lam ^ 2 * a * (p * p')) * ha

/-- **Border bound with one term fewer.** If `2 ^ (k - 1) ≠ 1` in `K` (`k = card κ`), the
leftover of weight `(1, …, 1)` can be merged with the square on the same pairing: for a fixed
`g`, itself a sum of split products, and every `lam ≠ 0`, the function `permanent + lam * g` is
a sum of `C(2k, k) / 2 + numWeights κ - 1` split products (`5, 16, 53, 176, …` for
`k = 2, 3, 4, 5, …`). -/
theorem borderMixedSplit_perm_squares_sub_one [Nonempty κ]
    (hc : (2 : K) ^ (Fintype.card κ - 1) ≠ 1) :
    BorderMixedSplitLE (Fintype.card κ)
      ((2 * Fintype.card κ).choose (Fintype.card κ) / 2 + numWeights κ - 1)
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K => A.permanent) := by
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hc' : (1 : K) - 2 ^ (Fintype.card κ - 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hS₀ : (univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ)).card = Fintype.card κ := by simp
  -- the pairing and the weight that are merged
  let P₀ : {S : Finset (κ ⊕ κ) // Sum.inl j₀ ∈ S ∧ S.card = Fintype.card κ} :=
    ⟨univ.map Function.Embedding.inl, by simp, hS₀⟩
  let W₁ : {w : κ → Fin 3 // ∑ j, (w j : ℕ) = Fintype.card κ} := ⟨fun _ => 1, by simp⟩
  have hP : 1 ≤ Fintype.card {S : Finset (κ ⊕ κ) // Sum.inl j₀ ∈ S ∧ S.card = Fintype.card κ} :=
    Fintype.card_pos_iff.mpr ⟨P₀⟩
  have hW : 1 ≤ Fintype.card {w : κ → Fin 3 // ∑ j, (w j : ℕ) = Fintype.card κ} :=
    Fintype.card_pos_iff.mpr ⟨W₁⟩
  have hcount : (2 * Fintype.card κ).choose (Fintype.card κ) / 2 + numWeights κ - 1 =
      (Fintype.card {S : Finset (κ ⊕ κ) // Sum.inl j₀ ∈ S ∧ S.card = Fintype.card κ} - 1) + 1
        + (Fintype.card {w : κ → Fin 3 // ∑ j, (w j : ℕ) = Fintype.card κ} - 1) := by
    rw [← card_pairings (Sum.inl j₀), numWeights]
    omega
  rw [hcount]
  refine ⟨fun A => (∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
        blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ)
      + (-(1 - (1 - 2 ^ (Fintype.card κ - 1))⁻¹)) *
        (blockForm A Sum.inr (univ.map Function.Embedding.inl) *
          blockForm A Sum.inr (univ.map Function.Embedding.inl)ᶜ),
    numWeights κ + 1,
    (mixedSplit_leftover_inr j₀).add ((MixedSplitLE.of_isSplitProduct hS₀
      (isSplitProduct_blockForm_mul Sum.inr Sum.inr _)).const_mul _),
    fun lam hlam => ?_⟩
  have hSQ := (mixedSplitLE_of_fintype_sub (K := K)
    (fun S : {S : Finset (κ ⊕ κ) // Sum.inl j₀ ∈ S ∧ S.card = Fintype.card κ} => S.1)
    (fun S A => (blockForm A Sum.inl S.1 + lam * blockForm A Sum.inr S.1)
      * (blockForm A Sum.inl S.1ᶜ + lam * blockForm A Sum.inr S.1ᶜ))
    (fun S => S.2.2) (fun S => isSplitProduct_square lam S.1) P₀).const_mul lam⁻¹
  have hM := (MixedSplitLE.of_isSplitProduct hS₀
    (isSplitProduct_square (lam * (1 - 2 ^ (Fintype.card κ - 1))⁻¹)
      (univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ)))).const_mul
        (lam⁻¹ * (1 - 2 ^ (Fintype.card κ - 1)))
  have hG := (mixedSplitLE_of_fintype_sub (K := K)
    (fun _ : {w : κ → Fin 3 // ∑ j, (w j : ℕ) = Fintype.card κ} =>
      univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ))
    (fun w A => garbLeft j₀ w.1 (fun j => A (Sum.inl j)) * garbRight w.1 (fun j => A (Sum.inr j)))
    (fun _ => hS₀) (fun w => isSplitProduct_garb j₀ w.1) W₁).const_mul (-lam⁻¹)
  refine ((hSQ.add hM).add hG).congr fun A => ?_
  have h := mul_permanent_eq_squares_half (Sum.inl j₀) A lam
  rw [sum_squares_eq_sum_subtype, sum_blockForm_inl_eq_sum_weights] at h
  exact merge_algebra _ _ _ _ _ _ _ _ _ _ _ _ hlam (mul_inv_cancel₀ hc') h (garb_one_eq j₀ A)

/-- In characteristic zero the bound with one term fewer holds for every `k ≥ 2`. -/
theorem borderMixedSplit_perm_squares_sub_one_of_charZero [CharZero K]
    (hk : 2 ≤ Fintype.card κ) :
    BorderMixedSplitLE (Fintype.card κ)
      ((2 * Fintype.card κ).choose (Fintype.card κ) / 2 + numWeights κ - 1)
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K => A.permanent) := by
  have : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  refine borderMixedSplit_perm_squares_sub_one fun h => ?_
  have h2 : ((2 ^ (Fintype.card κ - 1) : ℕ) : K) = ((1 : ℕ) : K) := by
    push_cast
    exact h
  have h3 : 2 ^ (Fintype.card κ - 1) = 1 := Nat.cast_injective h2
  have h4 : 2 ^ 1 ≤ 2 ^ (Fintype.card κ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

open Filter Topology in
/-- **The bound as a limit.** Over `ℝ` or `ℂ`, for `k = card κ ≥ 2`, the `2k × 2k` permanent
is a pointwise limit of functions that are sums of `C(2k, k) / 2 + numWeights κ - 1` split
products, `k` rows against `k`. -/
theorem exists_tendsto_perm_squares {𝕜 : Type*} [RCLike 𝕜] (hk : 2 ≤ Fintype.card κ) :
    ∃ F : ℕ → Matrix (κ ⊕ κ) (κ ⊕ κ) 𝕜 → 𝕜,
      (∀ j, MixedSplitLE (Fintype.card κ)
        ((2 * Fintype.card κ).choose (Fintype.card κ) / 2 + numWeights κ - 1) (F j)) ∧
      ∀ A, Tendsto (fun j => F j A) atTop (𝓝 A.permanent) :=
  (borderMixedSplit_perm_squares_sub_one_of_charZero (K := 𝕜) hk).exists_tendsto

end Sharp

/-! ### Other index types: `Fin (k + k)` and concrete sizes -/

section Reindex

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι']

/-- Renaming rows and columns by the same bijection does not change the permanent. -/
theorem permanent_submatrix_equiv (e : ι ≃ ι') (A : Matrix ι' ι' K) :
    (A.submatrix e e).permanent = A.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ fun σ => ?_
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Equiv.permCongr_apply]

/-- Split products can be transported along a renaming of the rows and columns. -/
theorem IsSplitProduct.reindex (e : ι ≃ ι') {S : Finset ι} {t : Matrix ι ι K → K}
    (h : IsSplitProduct S t) :
    IsSplitProduct (S.map e.toEmbedding) (fun A : Matrix ι' ι' K => t (A.submatrix e e)) := by
  obtain ⟨F, G, hFG⟩ := h
  have hb : Function.Bijective (fun x : S ⊕ (Sᶜ : Finset ι) =>
      e (Sum.elim (fun a : S => (a : ι)) (fun b : (Sᶜ : Finset ι) => (b : ι)) x)) := by
    refine e.bijective.comp ⟨?_, ?_⟩
    · rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (Subtype.ext hab)
      · have h' : (a : ι) = b := hab
        exact absurd (h' ▸ a.2) (Finset.mem_compl.mp b.2)
      · have h' : (a : ι) = b := hab
        exact absurd (h' ▸ b.2) (Finset.mem_compl.mp a.2)
      · exact congrArg Sum.inr (Subtype.ext hab)
    · intro x
      by_cases hx : x ∈ S
      · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨x, Finset.mem_compl.mpr hx⟩, rfl⟩
  refine (isSplitProduct_of_bijective _ hb (S.map e.toEmbedding) ?_ ?_
    (F.compLinearMap fun _ => LinearMap.funLeft K K e)
    (G.compLinearMap fun _ => LinearMap.funLeft K K e)).congr fun A => ?_
  · intro a
    simp
  · intro b
    simpa using Finset.mem_compl.mp b.2
  · exact (hFG _).trans rfl

/-- The mixed split rank does not depend on the names of the rows and columns. -/
theorem MixedSplitLE.reindex (e : ι ≃ ι') {k n : ℕ} {f : Matrix ι ι K → K}
    (h : MixedSplitLE k n f) :
    MixedSplitLE k n (fun A : Matrix ι' ι' K => f (A.submatrix e e)) := by
  obtain ⟨S, t, hS, ht, hsum⟩ := h
  exact ⟨fun v => (S v).map e.toEmbedding, fun v A => t v (A.submatrix e e),
    fun v => by rw [Finset.card_map, hS], fun v => (ht v).reindex e, fun A => hsum _⟩

/-- The border mixed split rank does not depend on the names of the rows and columns. -/
theorem BorderMixedSplitLE.reindex (e : ι ≃ ι') {k n : ℕ} {f : Matrix ι ι K → K}
    (h : BorderMixedSplitLE k n f) :
    BorderMixedSplitLE k n (fun A : Matrix ι' ι' K => f (A.submatrix e e)) := by
  obtain ⟨g, n', hg, hlam⟩ := h
  exact ⟨fun A => g (A.submatrix e e), n', hg.reindex e, fun lam hl => (hlam lam hl).reindex e⟩

end Reindex

section Fin

variable {K : Type*} [Field K]

/-- The border bound of the square construction for matrices indexed by `Fin (k + k)`. -/
theorem borderMixedSplit_perm_fin (k : ℕ) (hk : 1 ≤ k) :
    BorderMixedSplitLE k ((2 * k).choose k / 2 + numWeights (Fin k))
      (fun A : Matrix (Fin (k + k)) (Fin (k + k)) K => A.permanent) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := (borderMixedSplit_perm_squares (κ := Fin k) (K := K)).reindex finSumFinEquiv
  simpa only [Fintype.card_fin, permanent_submatrix_equiv] using h

/-- The exact bound of the square construction for matrices indexed by `Fin (k + k)`. -/
theorem mixedSplit_perm_fin (k : ℕ) (hk : 1 ≤ k) :
    MixedSplitLE k ((2 * k).choose k / 2 + 2 * numWeights (Fin k))
      (fun A : Matrix (Fin (k + k)) (Fin (k + k)) K => A.permanent) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := (mixedSplit_perm_squares (κ := Fin k) (K := K)).reindex finSumFinEquiv
  simpa only [Fintype.card_fin, permanent_submatrix_equiv] using h

theorem numWeights_fin_two : numWeights (Fin 2) = 3 := by decide

theorem numWeights_fin_three : numWeights (Fin 3) = 7 := by decide

theorem numWeights_fin_four : numWeights (Fin 4) = 19 := by decide

theorem numWeights_fin_five : numWeights (Fin 5) = 51 := by decide

/-- **`8 × 8`, border.** The `8 × 8` permanent has border mixed split rank at most
`35 + 19 = 54` for four rows against four (Laplace: `70`). Any field. -/
theorem borderMixedSplit_perm_eight :
    BorderMixedSplitLE 4 54 (fun A : Matrix (Fin 8) (Fin 8) K => A.permanent) := by
  have h := borderMixedSplit_perm_fin (K := K) 4 (by norm_num)
  rw [numWeights_fin_four] at h
  exact h

/-- **`10 × 10`, border.** The `10 × 10` permanent has border mixed split rank at most
`126 + 51 = 177` for five rows against five (Laplace: `252`). Any field. -/
theorem borderMixedSplit_perm_ten :
    BorderMixedSplitLE 5 177 (fun A : Matrix (Fin 10) (Fin 10) K => A.permanent) := by
  have h := borderMixedSplit_perm_fin (K := K) 5 (by norm_num)
  rw [numWeights_fin_five] at h
  exact h

/-- **`10 × 10`, exact: Laplace expansion is not optimal.** The `10 × 10` permanent is a sum
of `126 + 2 * 51 = 228` split products for five rows against five, fewer than the
`252 = C(10, 5)` terms of Laplace expansion. Any field. -/
theorem mixedSplit_perm_ten :
    MixedSplitLE 5 228 (fun A : Matrix (Fin 10) (Fin 10) K => A.permanent) := by
  have h := mixedSplit_perm_fin (K := K) 5 (by norm_num)
  rw [numWeights_fin_five] at h
  exact h

/-- The border bound with one term fewer for matrices indexed by `Fin (k + k)`. -/
theorem borderMixedSplit_perm_fin_sub_one (k : ℕ) (hk : 1 ≤ k) (hc : (2 : K) ^ (k - 1) ≠ 1) :
    BorderMixedSplitLE k ((2 * k).choose k / 2 + numWeights (Fin k) - 1)
      (fun A : Matrix (Fin (k + k)) (Fin (k + k)) K => A.permanent) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := (borderMixedSplit_perm_squares_sub_one (κ := Fin k) (K := K)
    (by simpa only [Fintype.card_fin] using hc)).reindex finSumFinEquiv
  simpa only [Fintype.card_fin, permanent_submatrix_equiv] using h

/-- **`4 × 4`, border, again.** The general construction with the merge gives the border bound
`3 + 3 - 1 = 5` of `borderMixedSplit_perm_four` (which is optimal over `ℝ` and `ℂ`,
`borderMixedSplit_perm_four_iff`). Any field. -/
theorem borderMixedSplit_perm_four_of_squares :
    BorderMixedSplitLE 2 5 (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent) := by
  have h2 : (2 : K) ^ (2 - 1) ≠ 1 := by
    intro h
    have h' : (2 : K) = 1 := by simpa using h
    exact one_ne_zero (show (1 : K) = 0 by linear_combination h')
  have h := borderMixedSplit_perm_fin_sub_one (K := K) 2 (by norm_num) h2
  rw [numWeights_fin_two] at h
  exact h

/-- **`6 × 6`, border.** `10 + 7 - 1 = 16` split products, three rows against three, in
characteristic zero. (The two-block identity of `FifteenForms.lean` gives `15`.) -/
theorem borderMixedSplit_perm_six_of_squares [CharZero K] :
    BorderMixedSplitLE 3 16 (fun A : Matrix (Fin 6) (Fin 6) K => A.permanent) := by
  have h := borderMixedSplit_perm_fin_sub_one (K := K) 3 (by norm_num) (by norm_num)
  rw [numWeights_fin_three] at h
  exact h

/-- **`8 × 8`, border, one term fewer.** `35 + 19 - 1 = 53` split products, four rows against
four, in characteristic zero (Laplace: `70`). -/
theorem borderMixedSplit_perm_eight_sub_one [CharZero K] :
    BorderMixedSplitLE 4 53 (fun A : Matrix (Fin 8) (Fin 8) K => A.permanent) := by
  have h := borderMixedSplit_perm_fin_sub_one (K := K) 4 (by norm_num) (by norm_num)
  rw [numWeights_fin_four] at h
  exact h

/-- **`10 × 10`, border, one term fewer.** `126 + 51 - 1 = 176` split products, five rows
against five, in characteristic zero (Laplace: `252`). -/
theorem borderMixedSplit_perm_ten_sub_one [CharZero K] :
    BorderMixedSplitLE 5 176 (fun A : Matrix (Fin 10) (Fin 10) K => A.permanent) := by
  have h := borderMixedSplit_perm_fin_sub_one (K := K) 5 (by norm_num) (by norm_num)
  rw [numWeights_fin_five] at h
  exact h

/-- At `10 × 10` the mixed split rank (five rows against five) is strictly smaller than the
number of terms of Laplace expansion, which is the optimum when all terms use the same row
set (`single_split_perm_iff`). -/
theorem exists_mixedSplit_perm_ten_lt_laplace :
    ∃ n, n < (Fintype.card (Fin 10)).choose 5 ∧
      MixedSplitLE 5 n (fun A : Matrix (Fin 10) (Fin 10) K => A.permanent) :=
  ⟨228, by decide, mixedSplit_perm_ten⟩

end Fin

end PvsNP
