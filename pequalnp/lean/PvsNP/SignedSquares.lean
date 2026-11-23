import PvsNP.SquaresBound

/-!
# The signed square construction: `C(2k, k) / 2 + C(k, k / 2)` split products for even `k`

Rows and columns of the matrix are indexed by `κ ⊕ κ`, `k = card κ` EVEN and positive; `K` is
any field (no assumption on the characteristic). In the language of `SplitRank.lean`
(`IsSplitProduct`, `MixedSplitLE`, `BorderMixedSplitLE`), with `k` rows against `k`:

* `borderMixedSplit_perm_signed`: the `2k × 2k` permanent has border mixed split rank at most
  `C(2k, k) / 2 + C(k, k / 2)`;
* `mixedSplit_perm_signed`: it is an exact sum of `C(2k, k) / 2 + 2 * C(k, k / 2)` split
  products;
* `exists_tendsto_perm_signed`: the border statement as a limit over `ℝ` or `ℂ`.

For matrices indexed by `Fin (k + k)`: `borderMixedSplit_perm_signed_fin`,
`mixedSplit_perm_signed_fin`, and for concrete sizes

* `borderMixedSplit_perm_eight_signed`: `8 × 8`, border, `35 + 6 = 41`
  (Laplace `70`, unsigned squares `53`);
* `mixedSplit_perm_eight_signed`: `8 × 8`, exact, `35 + 12 = 47 < 70`, so Laplace expansion is
  NOT optimal for exact decompositions already at `8 × 8`
  (`exists_mixedSplit_perm_eight_lt_laplace`);
* `borderMixedSplit_perm_twelve_signed` (`482`), `mixedSplit_perm_twelve_signed` (`502`);
* `borderMixedSplit_perm_four_signed`: at `4 × 4` the signed construction gives `3 + 2 = 5`.

The unsigned construction of `SquaresBound.lean` costs the central trinomial coefficient
(`3, 19, 141, …` for `k = 2, 4, 6`) for each leftover instead of `C(k, k / 2)` (`2, 6, 20, …`).
This is Theorem 1 and Corollaries 2, 3 of `pequalnp/notes/extra_terms.md`.

## The proof

1. Signs. `rowSign` is `-1` on the first block of rows `Q` and `1` on the second block;
   `setSign S = ∏ r ∈ S, rowSign r = (-1) ^ |S ∩ Q|`. Only `setSign S * setSign S = 1` is used
   in the identity (`setSign_mul_self`).
2. `mul_permanent_eq_signed_squares_half` (any `k`): with `c = setSign S`,
   `q₁ = blockForm A inl`, `q₂ = blockForm A inr` and the sums over the sets `S` that contain a
   fixed row `r₀`,
   `lam * perm = ∑ c * (q₁ S + c * lam * q₂ S) * (q₁ Sᶜ + c * lam * q₂ Sᶜ)
       - ∑ c * q₁ S * q₁ Sᶜ - lam ^ 2 * ∑ c * q₂ S * q₂ Sᶜ`.
   Each signed square is a split product for `S` (`isSplitProduct_signed_square`).
3. The signed leftover `∑ c * q₁ S * q₁ Sᶜ` (over `S ∋ r₀`) is the permanent of the matrix
   `sgarbMat r₀ A` whose two blocks of columns are both the first block of `A`, the first copy
   multiplied by the row signs, and with the row `r₀` set to zero on the second copy
   (`permanent_sgarbMat`). As in `SquaresBound.lean` the zero row selects one set of each
   pairing, so nothing is divided by `2`.
4. Laplace expansion of that permanent along the first block of rows, collected by the weight
   `wt C : κ → {0, 1, 2}` of the set of columns `C`, gives one product
   `sgarbLeft j₀ w * garbRight w` for each weight (`permanent_sgarbMat_eq_sum`; `garbRight` is
   the factor of `SquaresBound.lean`).
5. Cancellation (`sum_embedding_wt_eq_zero`). If `w` has the value `1` at two different
   columns, `sgarbLeft j₀ w = 0`: the row `r₀ = inl j₀` can only use first copies, say of the
   column `i₀`; exchange the two copies of a column `i ≠ i₀` of weight `1`. The row that uses
   this column is not `r₀`, and on it the two copies differ by the sign `-1`, so this is a
   sign-reversing involution without fixed points (`Finset.sum_involution`, valid in every
   characteristic). Since the sum of the weights is `k`, which is even, a weight with a value
   `1` has at least two of them (`exists_ne_wt_one_of_even`). This is the only place where `k` even
   is used.
6. The surviving weights are `twoWt J` (the value `2` on `J`, `0` elsewhere) for the sets `J`
   of `k / 2` columns: `C(k, k / 2)` split products, all for the first block of rows
   (`sum_signed_blockForm_inl_eq`, `mixedSplit_signed_leftover_inl`). For such a weight there
   is only one set of columns, both copies of `J` (`wt_eq_twoWt_iff`), so each product is a
   permanent of the rows of `Q` on the columns of `J` taken twice times a permanent of the
   other rows on the columns outside `J` taken twice
   (`sum_signed_blockForm_inl_eq_bothCopies`).
7. The second leftover is the first one after exchanging the two blocks of columns
   (`mixedSplit_signed_leftover_inr`). Dividing by `lam` gives the border bound with error term
   `lam * ∑ c * q₂ S * q₂ Sᶜ`; `lam = 1` gives the exact bound.
-/

namespace PvsNP

open Finset Matrix

section Signs

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- The sign of a row: `-1` on the first block of rows, `1` on the second block. -/
def rowSign (K : Type*) [Field K] : κ ⊕ κ → K := Sum.elim (fun _ => -1) (fun _ => 1)

/-- The sign of a set of rows: `(-1) ^ (number of its rows in the first block)`. -/
def setSign (K : Type*) [Field K] (S : Finset (κ ⊕ κ)) : K := ∏ r ∈ S, rowSign K r

omit [Fintype κ] [DecidableEq κ] in
theorem rowSign_mul_self (r : κ ⊕ κ) : rowSign K r * rowSign K r = 1 := by
  cases r <;> simp [rowSign]

omit [Fintype κ] [DecidableEq κ] in
theorem setSign_mul_self (S : Finset (κ ⊕ κ)) : setSign K S * setSign K S = 1 := by
  rw [setSign, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun r _ => rowSign_mul_self r

/-- **The signed square construction with one term per pairing.** Only `c * c = 1` is used, so
this holds for every `k` and in every characteristic. -/
theorem mul_permanent_eq_signed_squares_half (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K)
    (lam : K) :
    lam * A.permanent =
      ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
          setSign K S * ((blockForm A Sum.inl S + setSign K S * lam * blockForm A Sum.inr S)
            * (blockForm A Sum.inl Sᶜ + setSign K S * lam * blockForm A Sum.inr Sᶜ))
        - ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
            setSign K S * (blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ)
        - lam ^ 2 * ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
            setSign K S * (blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ) := by
  rw [permanent_eq_sum_blockForm, sum_eq_sum_half r₀]
  simp only [compl_compl, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  linear_combination
    (-(lam * (blockForm A Sum.inl S * blockForm A Sum.inr Sᶜ
        + blockForm A Sum.inl Sᶜ * blockForm A Sum.inr S)
      + setSign K S * lam ^ 2 * (blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ)))
      * setSign_mul_self (K := K) S

/-- Each signed square is a split product for `S`. -/
theorem isSplitProduct_signed_square (lam : K) (S : Finset (κ ⊕ κ)) :
    IsSplitProduct S (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
      setSign K S * ((blockForm A Sum.inl S + setSign K S * lam * blockForm A Sum.inr S)
        * (blockForm A Sum.inl Sᶜ + setSign K S * lam * blockForm A Sum.inr Sᶜ))) :=
  (isSplitProduct_square (setSign K S * lam) S).const_mul (setSign K S)

/-- A sum over the sets containing `r₀` of a function that vanishes unless the set has
`card κ` elements is a sum over the pairings. -/
theorem sum_filter_eq_sum_subtype_card (r₀ : κ ⊕ κ) (φ : Finset (κ ⊕ κ) → K)
    (hφ : ∀ S : Finset (κ ⊕ κ), S.card ≠ Fintype.card κ → φ S = 0) :
    ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S), φ S =
      ∑ S : {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ}, φ S.1 := by
  refine Eq.trans ?_ (Finset.sum_subtype
    (univ.filter fun S : Finset (κ ⊕ κ) => r₀ ∈ S ∧ S.card = Fintype.card κ) (by simp) φ)
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hc : S.card = Fintype.card κ
  · simp [hc]
  · rw [hφ S hc]
    simp

/-- The signed squares, one for each pairing, are a sum of split products. -/
theorem mixedSplit_signed_squares (r₀ : κ ⊕ κ) (lam : K) :
    MixedSplitLE (Fintype.card κ)
      (Fintype.card {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ})
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
          setSign K S * ((blockForm A Sum.inl S + setSign K S * lam * blockForm A Sum.inr S)
            * (blockForm A Sum.inl Sᶜ + setSign K S * lam * blockForm A Sum.inr Sᶜ))) :=
  mixedSplitLE_of_fintype
    (fun S : {S : Finset (κ ⊕ κ) // r₀ ∈ S ∧ S.card = Fintype.card κ} => S.1)
    (fun S A => setSign K S.1 *
      ((blockForm A Sum.inl S.1 + setSign K S.1 * lam * blockForm A Sum.inr S.1)
        * (blockForm A Sum.inl S.1ᶜ + setSign K S.1 * lam * blockForm A Sum.inr S.1ᶜ)))
    (fun S => S.2.2) (fun S => isSplitProduct_signed_square lam S.1)
    (fun A => sum_filter_eq_sum_subtype_card r₀ _ fun S hc => by
      rw [blockForm_eq_zero_of_card_ne A Sum.inl S hc, blockForm_eq_zero_of_card_ne A Sum.inr S hc]
      simp)

end Signs

/-! ### The signed leftover as a permanent, expanded along the first block of rows -/

section SignedGarbage

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- Copy the first block of a row onto the second block and change the sign of the first
copy. -/
def sdup : (κ ⊕ κ → K) →ₗ[K] (κ ⊕ κ → K) where
  toFun v := Sum.elim (fun j => -v (Sum.inl j)) (fun j => v (Sum.inl j))
  map_add' u v := by ext x; cases x <;> simp [add_comm]
  map_smul' c v := by ext x; cases x <;> simp

/-- Change the sign of the first block of a row and put zero on the second block. -/
def sdupZ : (κ ⊕ κ → K) →ₗ[K] (κ ⊕ κ → K) where
  toFun v := Sum.elim (fun j => -v (Sum.inl j)) (fun _ => 0)
  map_add' u v := by ext x; cases x <;> simp [add_comm]
  map_smul' c v := by ext x; cases x <;> simp

/-- The matrix whose two blocks of columns are both the first block of `A`, the first copy
with the row signs, and with the row `r₀` set to zero on the second copy. -/
def sgarbMat (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) : Matrix (κ ⊕ κ) (κ ⊕ κ) K :=
  Matrix.of fun r => Sum.elim (fun j => rowSign K r * A r (Sum.inl j))
    (fun j => if r = r₀ then 0 else A r (Sum.inl j))

theorem blockForm_sgarbMat_inl (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K)
    (S : Finset (κ ⊕ κ)) :
    blockForm (sgarbMat r₀ A) Sum.inl S = setSign K S * blockForm A Sum.inl S := by
  unfold blockForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hf : univ.map f = S
  · rw [ite_eq_left hf, ite_eq_left hf]
    subst hf
    rw [setSign, Finset.prod_map]
    simp [pick, sgarbMat, Finset.prod_mul_distrib]
  · rw [ite_eq_right hf, ite_eq_right hf, mul_zero]

theorem blockForm_sgarbMat_inr (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K)
    (T : Finset (κ ⊕ κ)) :
    blockForm (sgarbMat r₀ A) Sum.inr T = if r₀ ∈ T then 0 else blockForm A Sum.inl T := by
  rw [← blockForm_garbMat_inr]
  rfl

/-- The signed first-block leftovers of the squares, one for each pairing, are the permanent
of `sgarbMat r₀ A`. -/
theorem permanent_sgarbMat (r₀ : κ ⊕ κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    (sgarbMat r₀ A).permanent = ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => r₀ ∈ S),
      setSign K S * (blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ) := by
  rw [permanent_eq_sum_blockForm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [blockForm_sgarbMat_inl, blockForm_sgarbMat_inr]
  by_cases h : r₀ ∈ S <;> simp [h, mul_assoc]

omit [Fintype κ] in
theorem sgarbMat_inr (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) (j : κ) :
    sgarbMat (Sum.inl j₀) A (Sum.inr j) = dup (A (Sum.inr j)) := by
  funext x
  cases x <;> simp [sgarbMat, rowSign, dup, fold]

omit [Fintype κ] in
theorem sgarbMat_inl (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) (j : κ) :
    sgarbMat (Sum.inl j₀) A (Sum.inl j) = (if j = j₀ then sdupZ else sdup) (A (Sum.inl j)) := by
  funext x
  by_cases h : j = j₀ <;> cases x <;> simp [sgarbMat, rowSign, sdup, sdupZ, h]

/-- The factor in the first block of rows of the signed leftover term of weight `w`. -/
noncomputable def sgarbLeft (j₀ : κ) (w : κ → Fin 3) :
    MultilinearMap (RingHom.id K) (fun _ : κ => κ ⊕ κ → K) K :=
  ∑ C ∈ univ.filter (fun C : Finset (κ ⊕ κ) => wt C = w),
    (permML C).compLinearMap fun j => if j = j₀ then sdupZ else sdup

theorem sgarbLeft_eq_zero (j₀ : κ) (w : κ → Fin 3)
    (hw : ∑ j, (w j : ℕ) ≠ Fintype.card κ) : sgarbLeft (K := K) j₀ w = 0 := by
  unfold sgarbLeft
  refine Finset.sum_eq_zero fun C hC => ?_
  rw [permML_eq_zero]
  · ext v
    simp
  · rw [← sum_wt, (mem_filter.mp hC).2]
    exact hw

/-- The permanent of `sgarbMat (inl j₀) A` as a sum over the weights. -/
theorem permanent_sgarbMat_eq_sum (j₀ : κ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    (sgarbMat (Sum.inl j₀) A).permanent = ∑ w : κ → Fin 3,
      sgarbLeft j₀ w (fun j => A (Sum.inl j)) * garbRight w (fun j => A (Sum.inr j)) := by
  rw [permanent_eq_sum_permML,
    ← Finset.sum_fiberwise (univ : Finset (Finset (κ ⊕ κ))) (fun C => wt C)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [sgarbLeft, sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCw : wt C = w := (mem_filter.mp hC).2
  have hex : ∃ C : Finset (κ ⊕ κ), wt C = w := ⟨C, hCw⟩
  rw [garbRight, dite_eq_left hex, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compLinearMap_apply]
  have h1 : (fun j => sgarbMat (Sum.inl j₀) A (Sum.inl j)) =
      fun j => (if j = j₀ then sdupZ else sdup) (A (Sum.inl j)) :=
    funext fun j => sgarbMat_inl j₀ A j
  have h2 : (fun j => sgarbMat (Sum.inl j₀) A (Sum.inr j)) = fun j => dup (A (Sum.inr j)) :=
    funext fun j => sgarbMat_inr j₀ A j
  rw [h1, h2, permML_dup_compl_congr ((Classical.choose_spec hex).trans hCw.symm)]

end SignedGarbage

/-! ### Cancellation: only the weights with values in `{0, 2}` survive -/

section Cancel

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

omit [Fintype κ] in
theorem swapOn_singleton_of_fold_ne {i : κ} {x : κ ⊕ κ} (h : fold x ≠ i) :
    swapOn {i} x = x := by
  simp [swapOn, h]

omit [Fintype κ] in
theorem swapOn_singleton_of_fold_eq {i : κ} {x : κ ⊕ κ} (h : fold x = i) :
    swapOn {i} x = x.swap := by
  simp [swapOn, h]

omit [Fintype κ] [DecidableEq κ] in
theorem sumSwap_ne_self (x : κ ⊕ κ) : x.swap ≠ x := by
  cases x <;> simp

omit [Fintype κ] [DecidableEq κ] in
theorem sdup_swap (v : κ ⊕ κ → K) (x : κ ⊕ κ) : sdup v x.swap = -sdup v x := by
  cases x <;> simp [sdup]

omit [Fintype κ] in
/-- The weight of a set of columns does not change when columns are exchanged with their
copies. -/
theorem wt_map_swapPerm (J : Finset κ) (C : Finset (κ ⊕ κ)) :
    wt (C.map (swapPerm J).toEmbedding) = wt C := by
  funext j
  have hl : Sum.inl j ∈ C.map (swapPerm J).toEmbedding ↔ swapOn J (Sum.inl j) ∈ C := by
    rw [Finset.mem_map_equiv]
    rfl
  have hr : Sum.inr j ∈ C.map (swapPerm J).toEmbedding ↔ swapOn J (Sum.inr j) ∈ C := by
    rw [Finset.mem_map_equiv]
    rfl
  unfold wt
  by_cases hj : j ∈ J
  · have e1 : swapOn J (Sum.inl j) = Sum.inr j := by simp [swapOn, fold, hj]
    have e2 : swapOn J (Sum.inr j) = Sum.inl j := by simp [swapOn, fold, hj]
    rw [e1] at hl
    rw [e2] at hr
    simp only [hl, hr]
    by_cases a : Sum.inl j ∈ C <;> by_cases b : Sum.inr j ∈ C <;> simp [a, b]
  · have e1 : swapOn J (Sum.inl j) = Sum.inl j := by simp [swapOn, fold, hj]
    have e2 : swapOn J (Sum.inr j) = Sum.inr j := by simp [swapOn, fold, hj]
    rw [e1] at hl
    rw [e2] at hr
    simp only [hl, hr]

/-- If the image of `f` has weight `1` at the column `i`, exactly one `j` is sent to a copy of
the column `i`. -/
theorem exists_unique_fold_eq_of_wt_one (f : κ ↪ κ ⊕ κ) (i : κ) (h : wt (univ.map f) i = 1) :
    ∃ j₁, fold (f j₁) = i ∧ ∀ j, fold (f j) = i → j = j₁ := by
  unfold wt at h
  by_cases a : Sum.inl i ∈ univ.map f <;> by_cases b : Sum.inr i ∈ univ.map f
  · simp [a, b] at h
  · obtain ⟨j₁, -, hj₁⟩ := mem_map.mp a
    refine ⟨j₁, by rw [hj₁]; rfl, fun j hj => ?_⟩
    rcases eq_inl_or_inr (f j) with h' | h'
    · rw [hj] at h'
      exact f.injective (h'.trans hj₁.symm)
    · rw [hj] at h'
      exact absurd (h' ▸ mem_map_of_mem f (mem_univ j)) b
  · obtain ⟨j₁, -, hj₁⟩ := mem_map.mp b
    refine ⟨j₁, by rw [hj₁]; rfl, fun j hj => ?_⟩
    rcases eq_inl_or_inr (f j) with h' | h'
    · rw [hj] at h'
      exact absurd (h' ▸ mem_map_of_mem f (mem_univ j)) a
    · rw [hj] at h'
      exact f.injective (h'.trans hj₁.symm)
  · simp [a, b] at h

/-- The column whose two copies are exchanged by the sign-reversing involution: one of two
given columns, different from the column used by the row `j₀`. -/
def cancelCol (j₀ i₁ i₂ : κ) (f : κ ↪ κ ⊕ κ) : κ := if fold (f j₀) = i₁ then i₂ else i₁

/-- **The cancellation.** If the weight `w` has the value `1` at two different columns, the
embeddings whose image has weight `w` cancel in pairs: exchange the two copies of a column of
weight `1` that is not the column used by the row `j₀` (the row whose second copy is zero).
On the other rows the two copies differ by the sign. -/
theorem sum_embedding_wt_eq_zero (j₀ : κ) (w : κ → Fin 3) {i₁ i₂ : κ} (hne : i₁ ≠ i₂)
    (h₁ : w i₁ = 1) (h₂ : w i₂ = 1) (v : κ → κ ⊕ κ → K) :
    ∑ f : κ ↪ κ ⊕ κ, (if wt (univ.map f) = w then
      ∏ j, (if j = j₀ then sdupZ else sdup) (v j) (f j) else 0) = 0 := by
  rw [← Finset.sum_filter]
  have hix_w : ∀ f : κ ↪ κ ⊕ κ, w (cancelCol j₀ i₁ i₂ f) = 1 := by
    intro f
    unfold cancelCol
    split_ifs <;> assumption
  have hix_ne : ∀ f : κ ↪ κ ⊕ κ, fold (f j₀) ≠ cancelCol j₀ i₁ i₂ f := by
    intro f
    unfold cancelCol
    split_ifs with h
    · rw [h]
      exact hne
    · exact h
  have hg_apply : ∀ (f : κ ↪ κ ⊕ κ) (j : κ),
      embPost (swapPerm {cancelCol j₀ i₁ i₂ f}) f j = swapOn {cancelCol j₀ i₁ i₂ f} (f j) :=
    fun f j => rfl
  have hix_g : ∀ f : κ ↪ κ ⊕ κ,
      cancelCol j₀ i₁ i₂ (embPost (swapPerm {cancelCol j₀ i₁ i₂ f}) f) = cancelCol j₀ i₁ i₂ f := by
    intro f
    have h : fold (embPost (swapPerm {cancelCol j₀ i₁ i₂ f}) f j₀) = fold (f j₀) := by
      rw [hg_apply, fold_swapOn]
    unfold cancelCol at h ⊢
    rw [h]
  have hmap : ∀ f : κ ↪ κ ⊕ κ, univ.map (embPost (swapPerm {cancelCol j₀ i₁ i₂ f}) f) =
      (univ.map f).map (swapPerm {cancelCol j₀ i₁ i₂ f}).toEmbedding := by
    intro f
    simp [embPost, Finset.map_map]
  refine Finset.sum_involution
    (fun f _ => embPost (swapPerm {cancelCol j₀ i₁ i₂ f}) f) ?_ ?_ ?_ ?_
  · intro f hf
    have hwf : wt (univ.map f) = w := (mem_filter.mp hf).2
    obtain ⟨j₁, hj₁, huniq⟩ := exists_unique_fold_eq_of_wt_one f (cancelCol j₀ i₁ i₂ f)
      (by rw [hwf]; exact hix_w f)
    have hj₁₀ : j₁ ≠ j₀ := by
      rintro rfl
      exact hix_ne f hj₁
    have hfac : ∀ j, (if j = j₀ then sdupZ else sdup) (v j)
          (embPost (swapPerm {cancelCol j₀ i₁ i₂ f}) f j) =
        (if j = j₁ then -1 else 1) * (if j = j₀ then sdupZ else sdup) (v j) (f j) := by
      intro j
      rw [hg_apply]
      by_cases hj : j = j₁
      · subst hj
        rw [swapOn_singleton_of_fold_eq hj₁, ite_eq_right hj₁₀, ite_eq_left rfl, sdup_swap]
        ring
      · rw [swapOn_singleton_of_fold_ne (fun h => hj (huniq j h)), ite_eq_right hj, one_mul]
    simp only [hfac, Finset.prod_mul_distrib]
    rw [Fintype.prod_eq_single j₁ (fun j hj => ite_eq_right hj), ite_eq_left rfl]
    ring
  · intro f hf _ h
    have hwf : wt (univ.map f) = w := (mem_filter.mp hf).2
    obtain ⟨j₁, hj₁, -⟩ := exists_unique_fold_eq_of_wt_one f (cancelCol j₀ i₁ i₂ f)
      (by rw [hwf]; exact hix_w f)
    have h' := DFunLike.congr_fun h j₁
    rw [hg_apply, swapOn_singleton_of_fold_eq hj₁] at h'
    exact sumSwap_ne_self _ h'
  · intro f hf
    rw [mem_filter] at hf ⊢
    exact ⟨mem_univ _, by rw [hmap, wt_map_swapPerm]; exact hf.2⟩
  · intro f hf
    ext j
    rw [hg_apply, hix_g, hg_apply]
    exact swapOn_involutive _ _

/-- The first factor of the signed leftover vanishes when the weight has the value `1` at two
different columns. -/
theorem sgarbLeft_apply_eq_zero_of_two (j₀ : κ) (w : κ → Fin 3) {i₁ i₂ : κ} (hne : i₁ ≠ i₂)
    (h₁ : w i₁ = 1) (h₂ : w i₂ = 1) (v : κ → κ ⊕ κ → K) : sgarbLeft j₀ w v = 0 := by
  have h : sgarbLeft j₀ w v = ∑ C ∈ univ.filter (fun C : Finset (κ ⊕ κ) => wt C = w),
      permML C (fun j => (if j = j₀ then sdupZ else sdup) (v j)) := by
    simp only [sgarbLeft, sum_apply, MultilinearMap.compLinearMap_apply]
  rw [h, sum_permML_wt]
  exact sum_embedding_wt_eq_zero j₀ w hne h₁ h₂ v

/-- Parity: a weight with even sum that has the value `1` somewhere has it at least twice. -/
theorem exists_ne_wt_one_of_even (hk : Even (Fintype.card κ)) (w : κ → Fin 3)
    (hw : ∑ j, (w j : ℕ) = Fintype.card κ) (i₁ : κ) (h₁ : w i₁ = 1) :
    ∃ i₂, i₁ ≠ i₂ ∧ w i₂ = 1 := by
  by_contra hcon
  push Not at hcon
  have h2 : 2 ∣ ∑ j ∈ univ.erase i₁, (w j : ℕ) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj1 : w j ≠ 1 := hcon j (Finset.ne_of_mem_erase hj).symm
    have hall : ∀ a : Fin 3, a ≠ 1 → 2 ∣ (a : ℕ) := by decide
    exact hall _ hj1
  rw [← Finset.add_sum_erase univ _ (mem_univ i₁), h₁] at hw
  have h3 : ((1 : Fin 3) : ℕ) = 1 := rfl
  rw [h3] at hw
  obtain ⟨m, hm⟩ := h2
  obtain ⟨n, hn⟩ := hk
  omega

/-- For even `k` the first factor of the signed leftover vanishes as soon as the weight has
the value `1` somewhere. -/
theorem sgarbLeft_apply_eq_zero (hk : Even (Fintype.card κ)) (j₀ : κ) (w : κ → Fin 3) {i₁ : κ}
    (h₁ : w i₁ = 1) (v : κ → κ ⊕ κ → K) : sgarbLeft j₀ w v = 0 := by
  by_cases hw : ∑ j, (w j : ℕ) = Fintype.card κ
  · obtain ⟨i₂, hne, h₂⟩ := exists_ne_wt_one_of_even hk w hw i₁ h₁
    exact sgarbLeft_apply_eq_zero_of_two j₀ w hne h₁ h₂ v
  · rw [sgarbLeft_eq_zero j₀ w hw]
    rfl

end Cancel

/-! ### The bounds -/

section SignedBound

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- The weight with the value `2` on `J` and `0` elsewhere. -/
def twoWt (J : Finset κ) : κ → Fin 3 := fun i => if i ∈ J then 2 else 0

omit [Fintype κ] in
theorem twoWt_injective : Function.Injective (twoWt : Finset κ → κ → Fin 3) := by
  intro J J' h
  ext i
  have hi := congrFun h i
  unfold twoWt at hi
  by_cases a : i ∈ J <;> by_cases b : i ∈ J' <;> simp_all

theorem sum_twoWt (J : Finset κ) : ∑ j, (twoWt J j : ℕ) = 2 * J.card := by
  have h : ∀ j, (twoWt J j : ℕ) = if j ∈ J then 2 else 0 := by
    intro j
    unfold twoWt
    split_ifs <;> rfl
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The signed leftovers along one splitting, `k` even.** The signed first-block leftovers
of the squares (one for each pairing) are a sum of products of a form in the first block of
rows and a form in the second block of rows, one product for each set `J` of `k / 2` columns
(the weight `2` on `J` and `0` elsewhere). -/
theorem sum_signed_blockForm_inl_eq (hk : Even (Fintype.card κ)) (j₀ : κ)
    (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
        setSign K S * (blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ) =
      ∑ J : {J : Finset κ // J.card = Fintype.card κ / 2},
        sgarbLeft j₀ (twoWt J.1) (fun j => A (Sum.inl j))
          * garbRight (twoWt J.1) (fun j => A (Sum.inr j)) := by
  rw [← permanent_sgarbMat, permanent_sgarbMat_eq_sum]
  symm
  refine Fintype.sum_of_injective
    (fun J : {J : Finset κ // J.card = Fintype.card κ / 2} => twoWt J.1)
    (fun J J' h => Subtype.ext (twoWt_injective h)) _ _ (fun w hw => ?_) (fun _ => rfl)
  by_cases h1 : ∃ i, w i = 1
  · obtain ⟨i, hi⟩ := h1
    rw [sgarbLeft_apply_eq_zero hk j₀ w hi, zero_mul]
  · by_cases hs : ∑ j, (w j : ℕ) = Fintype.card κ
    · exfalso
      apply hw
      push Not at h1
      have hwJ : twoWt (univ.filter fun i => w i = 2) = w := by
        funext i
        have hall : ∀ a : Fin 3, a ≠ 1 → (if a = 2 then (2 : Fin 3) else 0) = a := by decide
        simpa [twoWt] using hall (w i) (h1 i)
      refine ⟨⟨univ.filter fun i => w i = 2, ?_⟩, hwJ⟩
      have h2 := sum_twoWt (univ.filter fun i => w i = 2)
      rw [hwJ, hs] at h2
      omega
    · rw [sgarbLeft_eq_zero j₀ w hs]
      simp

/-- Each signed leftover term is a split product for the first block of rows. -/
theorem isSplitProduct_sgarb (j₀ : κ) (w : κ → Fin 3) :
    IsSplitProduct (univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ))
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        sgarbLeft j₀ w (fun j => A (Sum.inl j)) * garbRight w (fun j => A (Sum.inr j))) :=
  isSplitProduct_of_bijective (id : κ ⊕ κ → κ ⊕ κ) Function.bijective_id _
    (fun a => by simp) (fun b => by simp) (sgarbLeft j₀ w) (garbRight w)

/-- For even `k` the signed first-block leftovers of the squares are a sum of `C(k, k / 2)`
split products, all for the first block of rows. -/
theorem mixedSplit_signed_leftover_inl (hk : Even (Fintype.card κ)) (j₀ : κ) :
    MixedSplitLE (Fintype.card κ) ((Fintype.card κ).choose (Fintype.card κ / 2))
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
          setSign K S * (blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ)) := by
  have hcard : (univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ)).card = Fintype.card κ := by
    simp
  have h := mixedSplitLE_of_fintype
    (fun _ : {J : Finset κ // J.card = Fintype.card κ / 2} =>
      univ.map (Function.Embedding.inl : κ ↪ κ ⊕ κ))
    (fun J A => sgarbLeft j₀ (twoWt J.1) (fun j => A (Sum.inl j))
      * garbRight (twoWt J.1) (fun j => A (Sum.inr j)))
    (fun _ => hcard) (fun J => isSplitProduct_sgarb j₀ (twoWt J.1))
    (sum_signed_blockForm_inl_eq (K := K) hk j₀)
  rwa [Fintype.card_finset_len] at h

/-- For even `k` the signed second-block leftovers of the squares are a sum of `C(k, k / 2)`
split products. -/
theorem mixedSplit_signed_leftover_inr (hk : Even (Fintype.card κ)) (j₀ : κ) :
    MixedSplitLE (Fintype.card κ) ((Fintype.card κ).choose (Fintype.card κ / 2))
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K =>
        ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
          setSign K S * (blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ)) := by
  refine ((mixedSplit_signed_leftover_inl (K := K) hk j₀).comp_rowLinear
    (LinearMap.funLeft K K Sum.swap)).congr fun A => ?_
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : ∀ T : Finset (κ ⊕ κ),
      blockForm (Matrix.of fun r => LinearMap.funLeft K K Sum.swap (A r)) Sum.inl T =
        blockForm A Sum.inr T := by
    intro T
    simp [blockForm, pick, LinearMap.funLeft]
  rw [h, h]

omit [Fintype κ] [DecidableEq κ] in
/-- The algebra of the border statement: divide the square identity by `lam`. -/
theorem signed_border_algebra (perm G sP sW lam : K) (hlam : lam ≠ 0)
    (h : lam * perm = sP - sW - lam ^ 2 * G) :
    perm + lam * G = lam⁻¹ * sP + -lam⁻¹ * sW := by
  have hl : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam
  linear_combination lam⁻¹ * h - (perm + lam * G) * hl

/-- **Border bound from the signed square construction, `k` even.** For the `2k × 2k`
permanent (`k = card κ` even and positive, any field), `k` rows against `k`: for a fixed `g`,
itself a sum of split products, and every `lam ≠ 0`, the function `permanent + lam * g` is a
sum of `C(2k, k) / 2 + C(k, k / 2)` split products: one signed square for each pairing, and
one product for each set of `k / 2` columns of the first block, all on the same pairing. -/
theorem borderMixedSplit_perm_signed [Nonempty κ] (hk : Even (Fintype.card κ)) :
    BorderMixedSplitLE (Fintype.card κ)
      ((2 * Fintype.card κ).choose (Fintype.card κ) / 2
        + (Fintype.card κ).choose (Fintype.card κ / 2))
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K => A.permanent) := by
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  rw [← card_pairings (Sum.inl j₀)]
  refine ⟨fun A => ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
    setSign K S * (blockForm A Sum.inr S * blockForm A Sum.inr Sᶜ), _,
    mixedSplit_signed_leftover_inr hk j₀, fun lam hlam => ?_⟩
  refine (((mixedSplit_signed_squares (Sum.inl j₀) lam).const_mul lam⁻¹).add
    ((mixedSplit_signed_leftover_inl hk j₀).const_mul (-lam⁻¹))).congr fun A => ?_
  exact signed_border_algebra _ _ _ _ _ hlam (mul_permanent_eq_signed_squares_half (Sum.inl j₀) A lam)

/-- **Exact bound from the signed square construction, `k` even.** The `2k × 2k` permanent
(`k = card κ` even and positive, any field) is a sum of `C(2k, k) / 2 + 2 * C(k, k / 2)` split
products, `k` rows against `k`. -/
theorem mixedSplit_perm_signed [Nonempty κ] (hk : Even (Fintype.card κ)) :
    MixedSplitLE (Fintype.card κ)
      ((2 * Fintype.card κ).choose (Fintype.card κ) / 2
        + 2 * (Fintype.card κ).choose (Fintype.card κ / 2))
      (fun A : Matrix (κ ⊕ κ) (κ ⊕ κ) K => A.permanent) := by
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  rw [← card_pairings (Sum.inl j₀), two_mul, ← add_assoc]
  refine (((mixedSplit_signed_squares (Sum.inl j₀) (1 : K)).add
    ((mixedSplit_signed_leftover_inl hk j₀).const_mul (-1))).add
    ((mixedSplit_signed_leftover_inr hk j₀).const_mul (-1))).congr fun A => ?_
  have h := mul_permanent_eq_signed_squares_half (Sum.inl j₀) A (1 : K)
  linear_combination h

open Filter Topology in
/-- **The signed bound as a limit.** Over `ℝ` or `ℂ`, for `k = card κ` even and positive, the
`2k × 2k` permanent is a pointwise limit of functions that are sums of
`C(2k, k) / 2 + C(k, k / 2)` split products, `k` rows against `k`. -/
theorem exists_tendsto_perm_signed {𝕜 : Type*} [RCLike 𝕜] [Nonempty κ]
    (hk : Even (Fintype.card κ)) :
    ∃ F : ℕ → Matrix (κ ⊕ κ) (κ ⊕ κ) 𝕜 → 𝕜,
      (∀ j, MixedSplitLE (Fintype.card κ)
        ((2 * Fintype.card κ).choose (Fintype.card κ) / 2
          + (Fintype.card κ).choose (Fintype.card κ / 2)) (F j)) ∧
      ∀ A, Tendsto (fun j => F j A) atTop (𝓝 A.permanent) :=
  (borderMixedSplit_perm_signed (K := 𝕜) hk).exists_tendsto

end SignedBound

/-! ### The surviving terms, explicitly -/

section Explicit

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

/-- Both copies of the columns in `J`. -/
def bothCopies (J : Finset κ) : Finset (κ ⊕ κ) := univ.filter fun x => fold x ∈ J

theorem inl_mem_bothCopies (J : Finset κ) (j : κ) :
    Sum.inl j ∈ bothCopies J ↔ j ∈ J := by
  rw [bothCopies, mem_filter]
  simp [fold]

theorem inr_mem_bothCopies (J : Finset κ) (j : κ) :
    Sum.inr j ∈ bothCopies J ↔ j ∈ J := by
  rw [bothCopies, mem_filter]
  simp [fold]

/-- The only set of columns of weight `twoWt J` consists of both copies of the columns in
`J`. -/
theorem wt_eq_twoWt_iff (C : Finset (κ ⊕ κ)) (J : Finset κ) :
    wt C = twoWt J ↔ C = bothCopies J := by
  constructor
  · intro h
    ext x
    rcases x with j | j
    · have hx := congrFun h j
      unfold wt twoWt at hx
      rw [inl_mem_bothCopies]
      by_cases a : Sum.inl j ∈ C <;> by_cases b : Sum.inr j ∈ C <;> by_cases c : j ∈ J <;>
        simp_all
    · have hx := congrFun h j
      unfold wt twoWt at hx
      rw [inr_mem_bothCopies]
      by_cases a : Sum.inl j ∈ C <;> by_cases b : Sum.inr j ∈ C <;> by_cases c : j ∈ J <;>
        simp_all
  · rintro rfl
    funext j
    by_cases c : j ∈ J <;> simp [wt, twoWt, inl_mem_bothCopies, inr_mem_bothCopies, c]

theorem compl_bothCopies (J : Finset κ) : (bothCopies J)ᶜ = bothCopies Jᶜ := by
  ext x
  rcases x with j | j
  · rw [mem_compl, inl_mem_bothCopies, inl_mem_bothCopies, mem_compl]
  · rw [mem_compl, inr_mem_bothCopies, inr_mem_bothCopies, mem_compl]

/-- For the weight `twoWt J` the first factor of the signed leftover is a single permanent:
the first block of rows on both copies of the columns in `J`. -/
theorem sgarbLeft_twoWt (j₀ : κ) (J : Finset κ) :
    sgarbLeft (K := K) j₀ (twoWt J) =
      (permML (bothCopies J)).compLinearMap fun j => if j = j₀ then sdupZ else sdup := by
  have h : univ.filter (fun C : Finset (κ ⊕ κ) => wt C = twoWt J) = {bothCopies J} := by
    ext C
    simp [wt_eq_twoWt_iff]
  rw [sgarbLeft, h, Finset.sum_singleton]

/-- For the weight `twoWt J` the second factor of the leftover is the permanent of the second
block of rows on both copies of the columns outside `J`. -/
theorem garbRight_twoWt (J : Finset κ) :
    garbRight (K := K) (twoWt J) = (permML (bothCopies Jᶜ)).compLinearMap fun _ => dup := by
  have hex : ∃ C : Finset (κ ⊕ κ), wt C = twoWt J := ⟨_, (wt_eq_twoWt_iff _ _).mpr rfl⟩
  rw [garbRight, dite_eq_left hex, (wt_eq_twoWt_iff _ _).mp (Classical.choose_spec hex),
    compl_bothCopies]

/-- **The signed leftover identity, explicitly (`k` even).** The signed first-block leftovers
of the squares, one for each pairing, are a sum over the sets `J` of `k / 2` columns of the
first block of: (permanent of the first block of rows, with signs, on both copies of the
columns in `J`; the row `j₀` is zero on the second copy) times (permanent of the second block
of rows on both copies of the columns outside `J`). -/
theorem sum_signed_blockForm_inl_eq_bothCopies (hk : Even (Fintype.card κ)) (j₀ : κ)
    (A : Matrix (κ ⊕ κ) (κ ⊕ κ) K) :
    ∑ S ∈ univ.filter (fun S : Finset (κ ⊕ κ) => Sum.inl j₀ ∈ S),
        setSign K S * (blockForm A Sum.inl S * blockForm A Sum.inl Sᶜ) =
      ∑ J : {J : Finset κ // J.card = Fintype.card κ / 2},
        permML (bothCopies J.1) (fun j => (if j = j₀ then sdupZ else sdup) (A (Sum.inl j)))
          * permML (bothCopies J.1ᶜ) (fun j => dup (A (Sum.inr j))) := by
  rw [sum_signed_blockForm_inl_eq hk j₀]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [sgarbLeft_twoWt, garbRight_twoWt]
  rfl

end Explicit

/-! ### `Fin (k + k)` and concrete sizes -/

section SignedFin

variable {K : Type*} [Field K]

/-- The border bound of the signed square construction for matrices indexed by `Fin (k + k)`,
`k` even and positive. -/
theorem borderMixedSplit_perm_signed_fin (k : ℕ) (hk : 1 ≤ k) (hk2 : Even k) :
    BorderMixedSplitLE k ((2 * k).choose k / 2 + k.choose (k / 2))
      (fun A : Matrix (Fin (k + k)) (Fin (k + k)) K => A.permanent) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := (borderMixedSplit_perm_signed (κ := Fin k) (K := K)
    (by simpa only [Fintype.card_fin] using hk2)).reindex finSumFinEquiv
  simpa only [Fintype.card_fin, permanent_submatrix_equiv] using h

/-- The exact bound of the signed square construction for matrices indexed by `Fin (k + k)`,
`k` even and positive. -/
theorem mixedSplit_perm_signed_fin (k : ℕ) (hk : 1 ≤ k) (hk2 : Even k) :
    MixedSplitLE k ((2 * k).choose k / 2 + 2 * k.choose (k / 2))
      (fun A : Matrix (Fin (k + k)) (Fin (k + k)) K => A.permanent) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := (mixedSplit_perm_signed (κ := Fin k) (K := K)
    (by simpa only [Fintype.card_fin] using hk2)).reindex finSumFinEquiv
  simpa only [Fintype.card_fin, permanent_submatrix_equiv] using h

/-- **`8 × 8`, border.** The `8 × 8` permanent has border mixed split rank at most
`35 + 6 = 41` for four rows against four (Laplace: `70`; unsigned squares: `53`). Any field. -/
theorem borderMixedSplit_perm_eight_signed :
    BorderMixedSplitLE 4 41 (fun A : Matrix (Fin 8) (Fin 8) K => A.permanent) := by
  have h := borderMixedSplit_perm_signed_fin (K := K) 4 (by norm_num) (by decide)
  have e : (2 * 4).choose 4 / 2 + (4).choose (4 / 2) = 41 := by decide
  rw [e] at h
  exact h

/-- **`8 × 8`, exact.** The `8 × 8` permanent is a sum of `35 + 2 * 6 = 47` split products for
four rows against four, fewer than the `70 = C(8, 4)` terms of Laplace expansion. Any field. -/
theorem mixedSplit_perm_eight_signed :
    MixedSplitLE 4 47 (fun A : Matrix (Fin 8) (Fin 8) K => A.permanent) := by
  have h := mixedSplit_perm_signed_fin (K := K) 4 (by norm_num) (by decide)
  have e : (2 * 4).choose 4 / 2 + 2 * (4).choose (4 / 2) = 47 := by decide
  rw [e] at h
  exact h

/-- **Laplace expansion is not optimal for exact decompositions at `8 × 8`.** The mixed split
rank of the `8 × 8` permanent (four rows against four) is strictly smaller than the number
`C(8, 4) = 70` of terms of Laplace expansion, which is the optimum when all terms use the same
row set (`single_split_perm_iff`). Any field. -/
theorem exists_mixedSplit_perm_eight_lt_laplace :
    ∃ n, n < Nat.choose 8 4 ∧
      MixedSplitLE 4 n (fun A : Matrix (Fin 8) (Fin 8) K => A.permanent) :=
  ⟨47, by decide, mixedSplit_perm_eight_signed⟩

/-- **`12 × 12`, border.** `462 + 20 = 482` split products, six rows against six (Laplace:
`924`). Any field. -/
theorem borderMixedSplit_perm_twelve_signed :
    BorderMixedSplitLE 6 482 (fun A : Matrix (Fin 12) (Fin 12) K => A.permanent) := by
  have h := borderMixedSplit_perm_signed_fin (K := K) 6 (by norm_num) (by decide)
  have e : (2 * 6).choose 6 / 2 + (6).choose (6 / 2) = 482 := by decide
  rw [e] at h
  exact h

/-- **`12 × 12`, exact.** `462 + 2 * 20 = 502` split products, six rows against six (Laplace:
`924`). Any field. -/
theorem mixedSplit_perm_twelve_signed :
    MixedSplitLE 6 502 (fun A : Matrix (Fin 12) (Fin 12) K => A.permanent) := by
  have h := mixedSplit_perm_signed_fin (K := K) 6 (by norm_num) (by decide)
  have e : (2 * 6).choose 6 / 2 + 2 * (6).choose (6 / 2) = 502 := by decide
  rw [e] at h
  exact h

/-- **`4 × 4`, border, by signs.** The signed construction gives `3 + 2 = 5`, the optimal
border value (`borderMixedSplit_perm_four_iff`), for any field. -/
theorem borderMixedSplit_perm_four_signed :
    BorderMixedSplitLE 2 5 (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent) := by
  have h := borderMixedSplit_perm_signed_fin (K := K) 2 (by norm_num) (by decide)
  have e : (2 * 2).choose 2 / 2 + (2).choose (2 / 2) = 5 := by decide
  rw [e] at h
  exact h

end SignedFin

end PvsNP
