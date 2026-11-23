import PvsNP.FiveTerm
import PvsNP.FourByFourLower
import PvsNP.FifteenForms
import PvsNP.SplitBridge
import PvsNP.FirstLayer

/-!
# Mixed split rank: one language for every size

The other files of this project use several different notions of "split product"
(`IsSplit` with coefficient tables at `4 × 4`, `splitTerm`, `IsSplit3` / `IsTriSplit` at
`6 × 6`, a linear form in one row times an arbitrary function in `FirstLayer.lean`). This file
fixes ONE definition that works for every size and every index type, and restates the main
results in it.

Rows and columns of a matrix are indexed by a finite type `ι` (so `Fin m` and `κ ⊕ κ` are both
covered). The three definitions are at the top of the file:

* `IsSplitProduct S t`: `t` is a multilinear form in the rows in `S` times a multilinear form
  in the other rows;
* `MixedSplitLE k n f`: `f` is a sum of `n` split products whose row sets all have `k`
  elements but may differ from term to term ("mixed split rank at most `n`");
* `BorderMixedSplitLE k n f`: for a fixed error term `g`, itself a sum of split products,
  `f + lam * g` is a sum of `n` split products for every `lam ≠ 0` ("border mixed split rank at
  most `n`").

## Main statements

In the uniform language, with `perm` the permanent:

* `borderMixedSplit_perm_four`: `BorderMixedSplitLE 2 5 perm` at `4 × 4`, any field;
* `not_mixedSplit_perm_four`: `¬ MixedSplitLE 2 4 perm` at `4 × 4`, characteristic zero;
* `not_borderMixedSplit_perm_four`: `¬ BorderMixedSplitLE 2 4 perm` at `4 × 4` over `ℝ` and `ℂ`,
  and `borderMixedSplit_perm_four_iff`: over `ℝ` and `ℂ` the border bound holds with `n` terms
  exactly when `5 ≤ n`;
* `mixedSplit_perm_six_laplace`: `MixedSplitLE 3 20 perm` at `6 × 6`, any field;
* `borderMixedSplit_perm_six`: `BorderMixedSplitLE 3 15 perm` at `6 × 6`, characteristic zero;
* `choose_le_of_single_split`: if all terms use the SAME row set `S` with `k` elements and add
  up to the permanent, there are at least `(card ι).choose k` of them;
  `permanent_eq_sum_single_split`, `mixedSplit_perm_laplace`: that number is attained (Laplace
  expansion along `S`), for every size and every `k`; `single_split_perm_iff` puts the two
  together; `choose_le_of_border_single_split`: over an infinite field the bound for one fixed
  row set also holds for border decompositions;
* `mixedSplit_one_perm_iff`: the first layer (one row against the rest, the row may change from
  term to term) of the `m × m` permanent has mixed split rank exactly `m`, any field; the lower
  bound is `le_of_permanent_eq_sum_row_linear_mul` of `FirstLayer.lean`. By the complement
  symmetry `mixedSplitLE_compl_iff` the same holds for the last layer
  (`mixedSplit_pred_perm_iff`);
* `mixedSplit_perm_four_laplace`: `MixedSplitLE 2 6 perm` at `4 × 4`. Whether five terms suffice
  exactly is not decided here.

## Tools

* API: `IsSplitProduct.const_mul`, `IsSplitProduct.compl`, `MixedSplitLE.add`,
  `MixedSplitLE.const_mul`, `MixedSplitLE.mono`, `mixedSplitLE_zero`, `mixedSplitLE_list`,
  `mixedSplitLE_of_fintype`, `MixedSplitLE.compl`, `MixedSplitLE.border`,
  `BorderMixedSplitLE.mono`, `BorderMixedSplitLE.exists_tendsto`.
* Bridges: `isSplitProduct_of_bijective` and `IsSplitProduct.exists_of_bijective` translate
  between row sets and explicit lists of rows; `isSplit_iff_isSplitProduct` and
  `IsSplitProduct.isSplit_of_card_two` (`4 × 4`, coefficient tables of `FiveTerm.lean`);
  `isTriSplit_iff_exists_isSplitProduct` (`6 × 6`, coefficient tensors of `SixBySixForms.lean`);
  `isSplitProduct_of_coeff` (any size, coefficient tensors) and `mixedSplitLE_of_function_split`
  (arbitrary functions as factors are no better than multilinear forms when the target is
  multilinear; this is `SplitBridge.lean` in the uniform language).

Not covered here: the identities of `Squares.lean` (general even size) are not restated in this
language.
-/

namespace PvsNP

open Matrix

/-! ### The three definitions -/

section Defs

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Split product.** `t` is a split product for the set of rows `S`: it is the product of a
form `F` that is multilinear in the rows of the matrix that belong to `S` (and does not look at
the other rows) and a form `G` that is multilinear in the rows that do not belong to `S`. Each
row is a vector in `ι → K`. For `S` with two elements in a `4 × 4` matrix this is a bilinear
form in two rows times a bilinear form in the other two. -/
def IsSplitProduct (S : Finset ι) (t : Matrix ι ι K → K) : Prop :=
  ∃ (F : MultilinearMap (RingHom.id K) (fun _ : S => ι → K) K)
    (G : MultilinearMap (RingHom.id K) (fun _ : (Sᶜ : Finset ι) => ι → K) K),
    ∀ A, t A = F (fun i => A i) * G (fun i => A i)

/-- **Mixed split rank at most `n`.** `f` is a sum of `n` split products; each of them uses a
set of exactly `k` rows, and these sets may be different for different terms. (Laplace
expansion along a fixed set of `k` rows is the special case in which all terms use the same
set.) In the literature this is the `(k, m - k)` partition rank. -/
def MixedSplitLE (k n : ℕ) (f : Matrix ι ι K → K) : Prop :=
  ∃ (S : Fin n → Finset ι) (t : Fin n → Matrix ι ι K → K),
    (∀ v, (S v).card = k) ∧ (∀ v, IsSplitProduct (S v) (t v)) ∧ ∀ A, f A = ∑ v, t v A

/-- **Border mixed split rank at most `n`**, with an explicit error of first order. There is a
fixed function `g`, itself a sum of finitely many split products, such that for every nonzero
scalar `lam` the function `f + lam * g` is a sum of `n` split products (with `k`-element row
sets that may depend on the term and on `lam`). Letting `lam → 0` the error `lam * g` vanishes,
so `f` is a limit of sums of `n` split products: see `BorderMixedSplitLE.exists_tendsto` for
that statement over `ℝ` and `ℂ`. The definition is only meaningful over an infinite field: over
a finite field there are finitely many `lam` and no limit to take. -/
def BorderMixedSplitLE (k n : ℕ) (f : Matrix ι ι K → K) : Prop :=
  ∃ (g : Matrix ι ι K → K) (n' : ℕ), MixedSplitLE k n' g ∧
    ∀ lam : K, lam ≠ 0 → MixedSplitLE k n (fun A => f A + lam * g A)

end Defs

/-! ### Basic properties -/

section API

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Being a split product only depends on the values of the function. -/
theorem IsSplitProduct.congr {S : Finset ι} {t t' : Matrix ι ι K → K} (h : IsSplitProduct S t)
    (htt' : ∀ A, t' A = t A) : IsSplitProduct S t' := by
  obtain ⟨F, G, hFG⟩ := h
  exact ⟨F, G, fun A => (htt' A).trans (hFG A)⟩

/-- A scalar multiple of a split product is a split product for the same row set. -/
theorem IsSplitProduct.const_mul {S : Finset ι} {t : Matrix ι ι K → K} (h : IsSplitProduct S t)
    (c : K) : IsSplitProduct S (fun A => c * t A) := by
  obtain ⟨F, G, hFG⟩ := h
  refine ⟨c • F, G, fun A => ?_⟩
  simp [hFG A, mul_assoc]

/-- A scalar multiple of a split product is a split product for the same row set. -/
theorem IsSplitProduct.smul {S : Finset ι} {t : Matrix ι ι K → K} (h : IsSplitProduct S t)
    (c : K) : IsSplitProduct S (c • t) :=
  h.const_mul c

/-- The zero function is a split product for every row set. -/
theorem isSplitProduct_zero (S : Finset ι) : IsSplitProduct S (fun _ : Matrix ι ι K => (0 : K)) :=
  ⟨0, 0, fun A => by simp⟩

/-- A split product for `S` is also one for the complement of `S`: swap the two factors. -/
theorem IsSplitProduct.compl {S : Finset ι} {t : Matrix ι ι K → K} (h : IsSplitProduct S t) :
    IsSplitProduct Sᶜ t := by
  obtain ⟨F, G, hFG⟩ := h
  refine ⟨G, F.domDomCongr (Equiv.subtypeEquivRight fun i => by simp), fun A => ?_⟩
  rw [hFG A, mul_comm]
  rfl

/-- The row sets `S` and `Sᶜ` have the same split products. -/
theorem isSplitProduct_compl_iff {S : Finset ι} {t : Matrix ι ι K → K} :
    IsSplitProduct Sᶜ t ↔ IsSplitProduct S t :=
  ⟨fun h => by simpa using h.compl, fun h => h.compl⟩

/-- A bijection `h : α ⊕ β → ι` that sends `α` into `S` and `β` outside `S` identifies `α`
with `S` and `β` with the complement of `S`. -/
theorem exists_equiv_of_bijective {α β : Type*} (h : α ⊕ β → ι) (hh : Function.Bijective h)
    (S : Finset ι) (hS : ∀ a, h (Sum.inl a) ∈ S) (hSc : ∀ b, h (Sum.inr b) ∉ S) :
    ∃ (e₁ : α ≃ S) (e₂ : β ≃ (Sᶜ : Finset ι)),
      (∀ a, (e₁ a : ι) = h (Sum.inl a)) ∧ ∀ b, (e₂ b : ι) = h (Sum.inr b) := by
  have b₁ : Function.Bijective (fun a : α => (⟨h (Sum.inl a), hS a⟩ : S)) := by
    constructor
    · intro a a' haa'
      simpa using hh.1 (Subtype.ext_iff.mp haa')
    · rintro ⟨i, hi⟩
      obtain ⟨x, rfl⟩ := hh.2 i
      rcases x with a | b
      · exact ⟨a, rfl⟩
      · exact absurd hi (hSc b)
  have b₂ : Function.Bijective
      (fun b : β => (⟨h (Sum.inr b), by simpa using hSc b⟩ : (Sᶜ : Finset ι))) := by
    constructor
    · intro b b' hbb'
      simpa using hh.1 (Subtype.ext_iff.mp hbb')
    · rintro ⟨i, hi⟩
      obtain ⟨x, rfl⟩ := hh.2 i
      rcases x with a | b
      · exact absurd (hS a) (by simpa using hi)
      · exact ⟨b, rfl⟩
  exact ⟨Equiv.ofBijective _ b₁, Equiv.ofBijective _ b₂, fun _ => rfl, fun _ => rfl⟩

/-- **From a list of rows to a row set.** Let the rows be listed by a bijection
`h : α ⊕ β → ι` whose first part enumerates `S` and whose second part enumerates the other
rows. A multilinear form in the rows `h (inl a)` times a multilinear form in the rows
`h (inr b)` is a split product for `S`. -/
theorem isSplitProduct_of_bijective {α β : Type*} (h : α ⊕ β → ι) (hh : Function.Bijective h)
    (S : Finset ι) (hS : ∀ a, h (Sum.inl a) ∈ S) (hSc : ∀ b, h (Sum.inr b) ∉ S)
    (F : MultilinearMap (RingHom.id K) (fun _ : α => ι → K) K)
    (G : MultilinearMap (RingHom.id K) (fun _ : β => ι → K) K) :
    IsSplitProduct S
      (fun A : Matrix ι ι K => F (fun a => A (h (Sum.inl a))) * G (fun b => A (h (Sum.inr b)))) := by
  obtain ⟨e₁, e₂, h₁, h₂⟩ := exists_equiv_of_bijective h hh S hS hSc
  refine ⟨F.domDomCongr e₁, G.domDomCongr e₂, fun A => ?_⟩
  simp only [MultilinearMap.domDomCongr_apply, h₁, h₂]

/-- **From a row set to a list of rows.** The converse of `isSplitProduct_of_bijective`: a
split product for `S` is a multilinear form in the rows `h (inl a)` times a multilinear form
in the rows `h (inr b)`, for every listing `h` of the rows as above. -/
theorem IsSplitProduct.exists_of_bijective {α β : Type*} (h : α ⊕ β → ι)
    (hh : Function.Bijective h) {S : Finset ι} (hS : ∀ a, h (Sum.inl a) ∈ S)
    (hSc : ∀ b, h (Sum.inr b) ∉ S) {t : Matrix ι ι K → K} (ht : IsSplitProduct S t) :
    ∃ (F : MultilinearMap (RingHom.id K) (fun _ : α => ι → K) K)
      (G : MultilinearMap (RingHom.id K) (fun _ : β => ι → K) K),
      ∀ A : Matrix ι ι K, t A = F (fun a => A (h (Sum.inl a))) * G (fun b => A (h (Sum.inr b))) := by
  obtain ⟨e₁, e₂, h₁, h₂⟩ := exists_equiv_of_bijective h hh S hS hSc
  obtain ⟨F, G, hFG⟩ := ht
  refine ⟨F.domDomCongr e₁.symm, G.domDomCongr e₂.symm, fun A => ?_⟩
  simp only [MultilinearMap.domDomCongr_apply, ← h₁, ← h₂, Equiv.apply_symm_apply]
  exact hFG A

/-- Having mixed split rank at most `n` only depends on the values of the function. -/
theorem MixedSplitLE.congr {k n : ℕ} {f f' : Matrix ι ι K → K} (h : MixedSplitLE k n f)
    (hff' : ∀ A, f' A = f A) : MixedSplitLE k n f' := by
  obtain ⟨S, t, hS, ht, hsum⟩ := h
  exact ⟨S, t, hS, ht, fun A => (hff' A).trans (hsum A)⟩

/-- The zero function is a sum of no split products. -/
theorem mixedSplitLE_zero (k : ℕ) : MixedSplitLE k 0 (fun _ : Matrix ι ι K => (0 : K)) :=
  ⟨Fin.elim0, Fin.elim0, fun v => v.elim0, fun v => v.elim0, fun A => by simp⟩

/-- Only the zero function is a sum of no split products. -/
theorem mixedSplitLE_zero_iff {k : ℕ} {f : Matrix ι ι K → K} :
    MixedSplitLE k 0 f ↔ ∀ A, f A = 0 := by
  constructor
  · rintro ⟨S, t, -, -, hsum⟩ A
    simpa using hsum A
  · intro h
    exact (mixedSplitLE_zero k).congr h

/-- A single split product for a set of `k` rows has mixed split rank at most `1`. -/
theorem MixedSplitLE.of_isSplitProduct {k : ℕ} {S : Finset ι} {t : Matrix ι ι K → K}
    (hS : S.card = k) (h : IsSplitProduct S t) : MixedSplitLE k 1 t :=
  ⟨fun _ => S, fun _ => t, fun _ => hS, fun _ => h, fun A => by simp⟩

/-- Mixed split rank is subadditive. -/
theorem MixedSplitLE.add {k n n' : ℕ} {f g : Matrix ι ι K → K} (hf : MixedSplitLE k n f)
    (hg : MixedSplitLE k n' g) : MixedSplitLE k (n + n') (fun A => f A + g A) := by
  obtain ⟨S, t, hS, ht, hsum⟩ := hf
  obtain ⟨S', t', hS', ht', hsum'⟩ := hg
  refine ⟨Fin.append S S', Fin.append t t', fun v => ?_, fun v => ?_, fun A => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) v
    · rw [Fin.append_left]; exact hS i
    · rw [Fin.append_right]; exact hS' j
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) v
    · rw [Fin.append_left, Fin.append_left]; exact ht i
    · rw [Fin.append_right, Fin.append_right]; exact ht' j
  · show f A + g A = _
    rw [Fin.sum_univ_add, hsum A, hsum' A]
    simp only [Fin.append_left, Fin.append_right]

/-- Scalar multiples do not increase the mixed split rank. -/
theorem MixedSplitLE.const_mul {k n : ℕ} {f : Matrix ι ι K → K} (h : MixedSplitLE k n f)
    (c : K) : MixedSplitLE k n (fun A => c * f A) := by
  obtain ⟨S, t, hS, ht, hsum⟩ := h
  exact ⟨S, fun v A => c * t v A, hS, fun v => (ht v).const_mul c, fun A => by
    show c * f A = _
    rw [hsum A, Finset.mul_sum]⟩

/-- Scalar multiples do not increase the mixed split rank. -/
theorem MixedSplitLE.smul {k n : ℕ} {f : Matrix ι ι K → K} (h : MixedSplitLE k n f)
    (c : K) : MixedSplitLE k n (c • f) :=
  h.const_mul c

/-- More terms are allowed: pad with zero terms. The hypothesis `k ≤ card ι` says that sets of
`k` rows exist at all; without it the statement fails for `n = 0 < n'` (the zero function is a
sum of no split products, but no split product with `k` rows exists). -/
theorem MixedSplitLE.mono {k n n' : ℕ} {f : Matrix ι ι K → K} (h : MixedSplitLE k n f)
    (hnn' : n ≤ n') (hk : k ≤ Fintype.card ι) : MixedSplitLE k n' f := by
  obtain ⟨S₀, -, hS₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (by simpa using hk)
  have hz : ∀ d : ℕ, MixedSplitLE k d (fun _ : Matrix ι ι K => (0 : K)) := fun d =>
    ⟨fun _ => S₀, fun _ _ => 0, fun _ => hS₀, fun _ => isSplitProduct_zero S₀, fun A => by simp⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  exact (h.add (hz d)).congr fun A => by simp

/-- A decomposition with at least one term can only exist if `k ≤ card ι`. -/
theorem MixedSplitLE.card_le {k n : ℕ} {f : Matrix ι ι K → K} (h : MixedSplitLE k n f)
    (hn : 0 < n) : k ≤ Fintype.card ι := by
  obtain ⟨S, -, hS, -, -⟩ := h
  rw [← hS ⟨0, hn⟩]
  exact Finset.card_le_univ _

/-- More terms are allowed, starting from a decomposition with at least one term. -/
theorem MixedSplitLE.mono_of_pos {k n n' : ℕ} {f : Matrix ι ι K → K} (h : MixedSplitLE k n f)
    (hnn' : n ≤ n') (hn : 0 < n) : MixedSplitLE k n' f :=
  h.mono hnn' (h.card_le hn)

/-- The sum of a list of split products, each for some set of `k` rows, has mixed split rank
at most the length of the list. -/
theorem mixedSplitLE_list {k : ℕ} (ts : List (Matrix ι ι K → K))
    (h : ∀ t ∈ ts, ∃ S : Finset ι, S.card = k ∧ IsSplitProduct S t) :
    MixedSplitLE k ts.length (fun A => (ts.map fun t => t A).sum) := by
  induction ts with
  | nil => exact (mixedSplitLE_zero k).congr fun A => by simp
  | cons t ts ih =>
    obtain ⟨S, hS, ht⟩ := h t (by simp)
    have h' := (ih fun t' ht' => h t' (by simp [ht'])).add (MixedSplitLE.of_isSplitProduct hS ht)
    exact h'.congr fun A => by simp [add_comm]

/-- The sum of a finite family of split products, each for some set of `k` rows, has mixed
split rank at most the size of the family. -/
theorem mixedSplitLE_of_fintype {k : ℕ} {T : Type*} [Fintype T] (S : T → Finset ι)
    (t : T → Matrix ι ι K → K) (hS : ∀ v, (S v).card = k) (ht : ∀ v, IsSplitProduct (S v) (t v))
    {f : Matrix ι ι K → K} (hsum : ∀ A, f A = ∑ v, t v A) :
    MixedSplitLE k (Fintype.card T) f := by
  let e := Fintype.equivFin T
  refine ⟨fun i => S (e.symm i), fun i => t (e.symm i), fun i => hS _, fun i => ht _, fun A => ?_⟩
  rw [hsum A]
  exact (e.symm.sum_comp fun v => t v A).symm

/-- An exact decomposition is in particular a border decomposition (with error term zero). -/
theorem MixedSplitLE.border {k n : ℕ} {f : Matrix ι ι K → K} (h : MixedSplitLE k n f) :
    BorderMixedSplitLE k n f :=
  ⟨fun _ => 0, 0, mixedSplitLE_zero k, fun lam _ => h.congr fun A => by simp⟩

/-- More terms are allowed in a border decomposition (see `MixedSplitLE.mono` for the
hypothesis `k ≤ card ι`). -/
theorem BorderMixedSplitLE.mono {k n n' : ℕ} {f : Matrix ι ι K → K}
    (h : BorderMixedSplitLE k n f) (hnn' : n ≤ n') (hk : k ≤ Fintype.card ι) :
    BorderMixedSplitLE k n' f := by
  obtain ⟨g, m, hg, hlam⟩ := h
  exact ⟨g, m, hg, fun lam hl => (hlam lam hl).mono hnn' hk⟩

/-- **Complement symmetry.** A sum of `n` split products with `k`-element row sets is also a
sum of `n` split products with row sets of `card ι - k` elements (the complements). -/
theorem MixedSplitLE.compl {k n : ℕ} {f : Matrix ι ι K → K} (h : MixedSplitLE k n f) :
    MixedSplitLE (Fintype.card ι - k) n f := by
  obtain ⟨S, t, hS, ht, hsum⟩ := h
  exact ⟨fun v => (S v)ᶜ, t, fun v => by rw [Finset.card_compl, hS v], fun v => (ht v).compl, hsum⟩

/-- Layers `k` and `card ι - k` have the same mixed split rank. -/
theorem mixedSplitLE_compl_iff {k n : ℕ} {f : Matrix ι ι K → K} (hk : k ≤ Fintype.card ι) :
    MixedSplitLE (Fintype.card ι - k) n f ↔ MixedSplitLE k n f :=
  ⟨fun h => by simpa [Nat.sub_sub_self hk] using h.compl, fun h => h.compl⟩

/-- Complement symmetry for border decompositions. -/
theorem BorderMixedSplitLE.compl {k n : ℕ} {f : Matrix ι ι K → K}
    (h : BorderMixedSplitLE k n f) : BorderMixedSplitLE (Fintype.card ι - k) n f := by
  obtain ⟨g, m, hg, hlam⟩ := h
  exact ⟨g, m, hg.compl, fun lam hl => (hlam lam hl).compl⟩

end API

/-! ### Multilinear forms and coefficient tensors -/

section Expand

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A multilinear form in vectors of `ι → K` is determined by its values on basis vectors: it
is the form whose coefficient tensor is given by those values. -/
theorem multilinear_eq_sum_basis {α : Type*} [Fintype α] [DecidableEq α]
    (F : MultilinearMap (RingHom.id K) (fun _ : α => ι → K) K) (x : α → ι → K) :
    F x = ∑ r : α → ι, (∏ i, x i (r i)) * F (fun i => Pi.single (r i) 1) := by
  have hx : x = fun i => ∑ j, x i j • (Pi.single j 1 : ι → K) := by
    funext i
    exact pi_eq_sum_univ' (x i)
  conv_lhs => rw [hx]
  rw [F.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [F.map_smul_univ]
  simp

end Expand

/-! ### Bridge to `IsSplit` (`4 × 4`, coefficient tables) -/

section Four

variable {K : Type*} [Field K]

/-- The bilinear form with coefficient table `c`, as a multilinear map in two vectors. -/
def rowFormML (c : Matrix (Fin 4) (Fin 4) K) :
    MultilinearMap (RingHom.id K) (fun _ : Fin 2 => Fin 4 → K) K :=
  ∑ p, ∑ q, c p q •
    (MultilinearMap.mkPiAlgebra K (Fin 2) K).compLinearMap ![LinearMap.proj p, LinearMap.proj q]

theorem rowFormML_apply (c : Matrix (Fin 4) (Fin 4) K) (x : Fin 2 → Fin 4 → K) :
    rowFormML c x = ∑ p, ∑ q, c p q * x 0 p * x 1 q := by
  simp [rowFormML, Fin.prod_univ_two, mul_assoc]

/-- Every multilinear map in two vectors of `K ^ 4` is given by a coefficient table: the table
of its values on pairs of basis vectors. -/
theorem exists_rowForm_of_multilinear
    (F : MultilinearMap (RingHom.id K) (fun _ : Fin 2 => Fin 4 → K) K) :
    ∃ c : Matrix (Fin 4) (Fin 4) K, ∀ x : Fin 2 → Fin 4 → K,
      F x = ∑ p, ∑ q, c p q * x 0 p * x 1 q := by
  refine ⟨fun p q => F ![Pi.single p 1, Pi.single q 1], fun x => ?_⟩
  rw [multilinear_eq_sum_basis F x, ← (finTwoArrowEquiv (Fin 4)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have h : (fun i : Fin 2 => (Pi.single (((finTwoArrowEquiv (Fin 4)).symm (p, q)) i) 1 : Fin 4 → K))
      = ![Pi.single p 1, Pi.single q 1] := by
    funext i
    fin_cases i <;> rfl
  rw [h, Fin.prod_univ_two]
  simp [finTwoArrowEquiv]
  ring

/-- Four distinct rows `a, b, c, d` of a `4 × 4` matrix list all the rows. -/
theorem bijective_sumElim_four {a b c d : Fin 4} (h : [a, b, c, d].Nodup) :
    Function.Bijective (Sum.elim ![a, b] ![c, d] : Fin 2 ⊕ Fin 2 → Fin 4) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := h
  rintro (x | x) (y | y) hxy <;> fin_cases x <;> fin_cases y <;> simp_all

/-- **Bridge from `IsSplit`.** A split product for the pairing `ab|cd` in the sense of
`FiveTerm.lean` (coefficient tables) is a split product for the row set `{a, b}`. -/
theorem IsSplit.isSplitProduct {a b c d : Fin 4} (h : [a, b, c, d].Nodup)
    {t : Matrix (Fin 4) (Fin 4) K → K} (ht : IsSplit a b c d t) :
    IsSplitProduct {a, b} t := by
  obtain ⟨F, G, hFG⟩ := ht
  have hb := bijective_sumElim_four h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := h
  refine (isSplitProduct_of_bijective (Sum.elim ![a, b] ![c, d]) hb {a, b} ?_ ?_
    (rowFormML F) (rowFormML G)).congr fun A => ?_
  · intro x
    fin_cases x <;> simp
  · intro x
    fin_cases x <;> simp [Ne.symm hac, Ne.symm hbc, Ne.symm had, Ne.symm hbd]
  · rw [hFG A, rowFormML_apply, rowFormML_apply]
    simp [rowForm]

/-- **Bridge to `IsSplit`.** A split product for the row set `{a, b}` of a `4 × 4` matrix is a
split product for the pairing `ab|cd` in the sense of `FiveTerm.lean`, where `c, d` are the
other two rows. -/
theorem IsSplitProduct.isSplit {a b c d : Fin 4} (h : [a, b, c, d].Nodup)
    {t : Matrix (Fin 4) (Fin 4) K → K} (ht : IsSplitProduct {a, b} t) :
    IsSplit a b c d t := by
  have hb := bijective_sumElim_four h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := h
  obtain ⟨F, G, hFG⟩ := ht.exists_of_bijective (Sum.elim ![a, b] ![c, d]) hb
    (by intro x; fin_cases x <;> simp)
    (by intro x; fin_cases x <;> simp [Ne.symm hac, Ne.symm hbc, Ne.symm had, Ne.symm hbd])
  obtain ⟨cF, hcF⟩ := exists_rowForm_of_multilinear F
  obtain ⟨cG, hcG⟩ := exists_rowForm_of_multilinear G
  refine ⟨cF, cG, fun A => ?_⟩
  rw [hFG A, hcF, hcG]
  simp [rowForm]

/-- At `4 × 4` the two notions of split product agree. -/
theorem isSplit_iff_isSplitProduct {a b c d : Fin 4} (h : [a, b, c, d].Nodup)
    {t : Matrix (Fin 4) (Fin 4) K → K} : IsSplit a b c d t ↔ IsSplitProduct {a, b} t :=
  ⟨fun ht => ht.isSplitProduct h, fun ht => ht.isSplit h⟩

/-- The pairings `ab|cd` and `cd|ab` have the same split products. -/
theorem IsSplit.swap {a b c d : Fin 4} {t : Matrix (Fin 4) (Fin 4) K → K}
    (ht : IsSplit a b c d t) : IsSplit c d a b t := by
  obtain ⟨F, G, hFG⟩ := ht
  exact ⟨G, F, fun A => by rw [hFG A, mul_comm]⟩

/-- The six sets of two rows of a `4 × 4` matrix. -/
theorem card_two_fin_four (S : Finset (Fin 4)) (hS : S.card = 2) :
    S = {0, 1} ∨ S = {0, 2} ∨ S = {0, 3} ∨ S = {1, 2} ∨ S = {1, 3} ∨ S = {2, 3} := by
  revert S
  decide

/-- **Converse bridge at `4 × 4`.** A split product for any set of two rows is a split product
in the sense of `FiveTerm.lean` for one of the three pairings `01|23`, `02|13`, `03|12`. -/
theorem IsSplitProduct.isSplit_of_card_two {S : Finset (Fin 4)} (hS : S.card = 2)
    {t : Matrix (Fin 4) (Fin 4) K → K} (ht : IsSplitProduct S t) :
    IsSplit 0 1 2 3 t ∨ IsSplit 0 2 1 3 t ∨ IsSplit 0 3 1 2 t := by
  rcases card_two_fin_four S hS with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (ht.isSplit (by decide))
  · exact Or.inr (Or.inl (ht.isSplit (by decide)))
  · exact Or.inr (Or.inr (ht.isSplit (by decide)))
  · exact Or.inr (Or.inr (ht.isSplit (c := 0) (d := 3) (by decide)).swap)
  · exact Or.inr (Or.inl (ht.isSplit (c := 0) (d := 2) (by decide)).swap)
  · exact Or.inl (ht.isSplit (c := 0) (d := 1) (by decide)).swap

end Four

/-! ### Bridge from `IsTriSplit` (`6 × 6`, coefficient tensors) -/

section Six

variable {K : Type*} [Field K]

/-- The trilinear form with coefficient tensor `c`, as a multilinear map in three vectors. -/
def triFormML (c : Fin 6 → Fin 6 → Fin 6 → K) :
    MultilinearMap (RingHom.id K) (fun _ : Fin 3 => Fin 6 → K) K :=
  ∑ p, ∑ q, ∑ r, c p q r • (MultilinearMap.mkPiAlgebra K (Fin 3) K).compLinearMap
    ![LinearMap.proj p, LinearMap.proj q, LinearMap.proj r]

theorem triFormML_apply (c : Fin 6 → Fin 6 → Fin 6 → K) (x : Fin 3 → Fin 6 → K) :
    triFormML c x = triForm c (x 0) (x 1) (x 2) := by
  simp [triFormML, triForm, Fin.prod_univ_three, mul_assoc]

/-- Six distinct rows of a `6 × 6` matrix list all the rows. -/
theorem bijective_sumElim_six {a b c d e f : Fin 6} (h : [a, b, c, d, e, f].Nodup) :
    Function.Bijective (Sum.elim ![a, b, c] ![d, e, f] : Fin 3 ⊕ Fin 3 → Fin 6) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩ := h
  rintro (x | x) (y | y) hxy <;> fin_cases x <;> fin_cases y <;> simp_all

/-- **Bridge from `IsTriSplit`.** A split product with trilinear factors in the sense of
`SixBySixForms.lean` (coefficient tensors, rows `abc|def`) is a split product for the set of
three rows `{a, b, c}`. -/
theorem IsTriSplit.exists_isSplitProduct {t : Matrix (Fin 6) (Fin 6) K → K} (ht : IsTriSplit t) :
    ∃ S : Finset (Fin 6), S.card = 3 ∧ IsSplitProduct S t := by
  obtain ⟨a, b, c, d, e, f, h, cF, cG, hFG⟩ := ht
  have hb := bijective_sumElim_six h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩ := h
  refine ⟨{a, b, c}, Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩, ?_⟩
  refine (isSplitProduct_of_bijective (Sum.elim ![a, b, c] ![d, e, f]) hb {a, b, c} ?_ ?_
    (triFormML cF) (triFormML cG)).congr fun A => ?_
  · intro x
    fin_cases x <;> simp
  · intro x
    fin_cases x <;> simp [Ne.symm had, Ne.symm hbd, Ne.symm hcd, Ne.symm hae, Ne.symm hbe,
      Ne.symm hce, Ne.symm haf, Ne.symm hbf, Ne.symm hcf]
  · rw [hFG A, triFormML_apply, triFormML_apply]
    simp

/-- Every multilinear map in three vectors of `K ^ 6` is given by a coefficient tensor: the
tensor of its values on triples of basis vectors. -/
theorem exists_triForm_of_multilinear
    (F : MultilinearMap (RingHom.id K) (fun _ : Fin 3 => Fin 6 → K) K) :
    ∃ c : Fin 6 → Fin 6 → Fin 6 → K, ∀ x : Fin 3 → Fin 6 → K,
      F x = triForm c (x 0) (x 1) (x 2) := by
  refine ⟨fun p q r => F ![Pi.single p 1, Pi.single q 1, Pi.single r 1], fun x => ?_⟩
  rw [multilinear_eq_sum_basis F x, ← (Fin.consEquiv fun _ : Fin 3 => Fin 6).sum_comp,
    Fintype.sum_prod_type, triForm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← (finTwoArrowEquiv (Fin 6)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have h : (fun i : Fin 3 => (Pi.single
      (((Fin.consEquiv fun _ : Fin 3 => Fin 6) (p, (finTwoArrowEquiv (Fin 6)).symm (q, r))) i) 1 :
        Fin 6 → K)) = ![Pi.single p 1, Pi.single q 1, Pi.single r 1] := by
    funext i
    fin_cases i <;> rfl
  rw [h, Fin.prod_univ_three]
  have e0 : ((Fin.consEquiv fun _ : Fin 3 => Fin 6) (p, (finTwoArrowEquiv (Fin 6)).symm (q, r))) 0 = p :=
    rfl
  have e1 : ((Fin.consEquiv fun _ : Fin 3 => Fin 6) (p, (finTwoArrowEquiv (Fin 6)).symm (q, r))) 1 = q :=
    rfl
  have e2 : ((Fin.consEquiv fun _ : Fin 3 => Fin 6) (p, (finTwoArrowEquiv (Fin 6)).symm (q, r))) 2 = r :=
    rfl
  rw [e0, e1, e2]
  ring

/-- **Converse bridge at `6 × 6`.** A split product for a set of three rows is a split product
with trilinear factors in the sense of `SixBySixForms.lean`. -/
theorem IsSplitProduct.isTriSplit {S : Finset (Fin 6)} (hS : S.card = 3)
    {t : Matrix (Fin 6) (Fin 6) K → K} (ht : IsSplitProduct S t) : IsTriSplit t := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  have hc : ({a, b, c} : Finset (Fin 6))ᶜ.card = 3 := by
    rw [Finset.card_compl, hS]
    rfl
  obtain ⟨d, e, f, hde, hdf, hef, hdef⟩ := Finset.card_eq_three.mp hc
  have hd : d ∈ ({a, b, c} : Finset (Fin 6))ᶜ := by rw [hdef]; simp
  have he : e ∈ ({a, b, c} : Finset (Fin 6))ᶜ := by rw [hdef]; simp
  have hf : f ∈ ({a, b, c} : Finset (Fin 6))ᶜ := by rw [hdef]; simp
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hd he hf
  obtain ⟨hda, hdb, hdc⟩ := hd
  obtain ⟨hea, heb, hec⟩ := he
  obtain ⟨hfa, hfb, hfc⟩ := hf
  have hnd : [a, b, c, d, e, f].Nodup := by
    simp [hab, hac, hbc, hde, hdf, hef, Ne.symm hda, Ne.symm hdb, Ne.symm hdc, Ne.symm hea,
      Ne.symm heb, Ne.symm hec, Ne.symm hfa, Ne.symm hfb, Ne.symm hfc]
  obtain ⟨F, G, hFG⟩ := ht.exists_of_bijective (Sum.elim ![a, b, c] ![d, e, f])
    (bijective_sumElim_six hnd)
    (by intro x; fin_cases x <;> simp)
    (by intro x; fin_cases x <;> simp [hda, hdb, hdc, hea, heb, hec, hfa, hfb, hfc])
  obtain ⟨cF, hcF⟩ := exists_triForm_of_multilinear F
  obtain ⟨cG, hcG⟩ := exists_triForm_of_multilinear G
  refine ⟨a, b, c, d, e, f, hnd, cF, cG, fun A => ?_⟩
  rw [hFG A, hcF, hcG]
  simp

/-- At `6 × 6` the two notions of split product (three rows against three) agree. -/
theorem isTriSplit_iff_exists_isSplitProduct {t : Matrix (Fin 6) (Fin 6) K → K} :
    IsTriSplit t ↔ ∃ S : Finset (Fin 6), S.card = 3 ∧ IsSplitProduct S t :=
  ⟨fun h => h.exists_isSplitProduct, fun ⟨_, hS, h⟩ => h.isTriSplit hS⟩

end Six

/-! ### The main results in the uniform language -/

section Main

variable {K : Type*} [Field K]

/-- **Border upper bound at `4 × 4`.** Over any field, the `4 × 4` permanent has border mixed
split rank at most `5` for two rows against two: for every `lam ≠ 0`, the permanent plus `lam`
times one fixed split product is a sum of five split products. (Laplace expansion uses six.)
From `permanent_sub_eq_five_split`. -/
theorem borderMixedSplit_perm_four :
    BorderMixedSplitLE 2 5 (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent) := by
  refine ⟨fun A => -(altPair A 2 3 0 1 * altPair A 2 3 2 3), 1, ?_, fun lam hlam => ?_⟩
  · refine MixedSplitLE.of_isSplitProduct (S := {0, 1}) (by decide) ?_
    refine IsSplit.isSplitProduct (c := 2) (d := 3) (by decide)
      ⟨!![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0],
        !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0], fun A => ?_⟩
    simp [rowForm, altPair, Fin.sum_univ_four]
    ring
  · obtain ⟨t₁, t₂, t₃, t₄, t₅, h₁, h₂, h₃, h₄, h₅, hsum⟩ := permanent_sub_eq_five_split lam hlam
    have s₁ := MixedSplitLE.of_isSplitProduct (k := 2) (by decide) (h₁.isSplitProduct (by decide))
    have s₂ := MixedSplitLE.of_isSplitProduct (k := 2) (by decide) (h₂.isSplitProduct (by decide))
    have s₃ := MixedSplitLE.of_isSplitProduct (k := 2) (by decide) (h₃.isSplitProduct (by decide))
    have s₄ := MixedSplitLE.of_isSplitProduct (k := 2) (by decide) (h₄.isSplitProduct (by decide))
    have s₅ := MixedSplitLE.of_isSplitProduct (k := 2) (by decide) (h₅.isSplitProduct (by decide))
    refine ((((s₁.add s₂).add s₃).add s₄).add s₅).congr fun A => ?_
    rw [← hsum A]
    ring

/-- **Exact lower bound at `4 × 4`.** Over a field of characteristic zero, the `4 × 4`
permanent is not a sum of four split products for two rows against two, whatever row sets the
four terms use. From `permanent_ne_sum_four_isSplit`. -/
theorem not_mixedSplit_perm_four [CharZero K] :
    ¬ MixedSplitLE 2 4 (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent) := by
  rintro ⟨S, t, hS, ht, hsum⟩
  exact permanent_ne_sum_four_isSplit t (fun v => (ht v).isSplit_of_card_two (hS v)) hsum

/-- **Laplace at `6 × 6`.** Over any field, the `6 × 6` permanent is a sum of twenty split
products for three rows against three. From `permanent_eq_twenty_triSplit`. -/
theorem mixedSplit_perm_six_laplace :
    MixedSplitLE 3 20 (fun A : Matrix (Fin 6) (Fin 6) K => A.permanent) := by
  obtain ⟨ts, hlen, hts, hsum⟩ := permanent_eq_twenty_triSplit (R := K)
  have h := mixedSplitLE_list (k := 3) ts fun t ht => (hts t ht).exists_isSplitProduct
  rw [hlen] at h
  exact h.congr hsum

/-- The error term `wrest A / 90` of the fifteen-term identity is a sum of ten split products
for three rows against three. -/
theorem mixedSplit_wrest [CharZero K] :
    MixedSplitLE 3 10 (fun A : Matrix (Fin 6) (Fin 6) K => wrest A / 90) := by
  have h := mixedSplitLE_list (K := K) (k := 3)
    [mk 0 1 2 3 4 5 (fun u v w => (30 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 1 3 2 4 5 (fun u v w => (-6 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 1 4 2 3 5 (fun u v w => (30 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 1 5 2 3 4 (fun u v w => (10 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 2 3 1 4 5 (fun u v w => (-5 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 2 4 1 3 5 (fun u v w => (-15 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 2 5 1 3 4 (fun u v w => (15 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 3 4 1 2 5 (fun u v w => (-5 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 3 5 1 2 4 (fun u v w => (15 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5),
     mk 0 4 5 1 2 3 (fun u v w => (3 / 90) * perm3 3 4 5 u v w) (perm3 3 4 5)]
    (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (isTriSplit_mk (by decide) ((isTriForm_perm3 3 4 5).const_mul _)
          (isTriForm_perm3 3 4 5)).exists_isSplitProduct)
  refine h.congr fun A => ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mk, wrest]
  ring

/-- **Border upper bound at `6 × 6`.** Over a field of characteristic zero, the `6 × 6`
permanent has border mixed split rank at most `15` for three rows against three: for every
`lam ≠ 0`, the permanent plus `lam * (wrest A / 90)` is a sum of fifteen split products, and the
error term is itself a sum of ten split products. (Laplace expansion uses twenty.) From
`permanent_add_eq_fifteen_triSplit`. -/
theorem borderMixedSplit_perm_six [CharZero K] :
    BorderMixedSplitLE 3 15 (fun A : Matrix (Fin 6) (Fin 6) K => A.permanent) := by
  refine ⟨fun A => wrest A / 90, 10, mixedSplit_wrest, fun lam hlam => ?_⟩
  obtain ⟨ts, hlen, hts, hsum⟩ := permanent_add_eq_fifteen_triSplit lam hlam
  have h := mixedSplitLE_list (k := 3) ts fun t ht => (hts t ht).exists_isSplitProduct
  rw [hlen] at h
  exact h.congr hsum

end Main

/-! ### Limits over `ℝ` and `ℂ` -/

section Limit

open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A border decomposition is a limit.** Over `ℝ` or `ℂ`, if `f` has border mixed split rank
at most `n`, then there is a sequence of functions, each a sum of `n` split products, that
converges pointwise to `f`. -/
theorem BorderMixedSplitLE.exists_tendsto {k n : ℕ} {f : Matrix ι ι 𝕜 → 𝕜}
    (h : BorderMixedSplitLE k n f) :
    ∃ F : ℕ → Matrix ι ι 𝕜 → 𝕜, (∀ j, MixedSplitLE k n (F j)) ∧
      ∀ A, Tendsto (fun j => F j A) atTop (𝓝 (f A)) := by
  obtain ⟨g, n', -, hg⟩ := h
  refine ⟨fun j A => f A + (1 / ((j : 𝕜) + 1)) * g A,
    fun j => hg _ (one_div_ne_zero (Nat.cast_add_one_ne_zero j)), fun A => ?_⟩
  have h0 : Tendsto (fun j : ℕ => 1 / ((j : 𝕜) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := (h0.mul_const (g A)).const_add (f A)
  simpa using h1

/-- **Border lower bound at `4 × 4`.** Over `ℝ` or `ℂ`, the `4 × 4` permanent does not have
border mixed split rank at most `4` for two rows against two. From
`not_tendsto_sum_four_isSplit`. -/
theorem not_borderMixedSplit_perm_four :
    ¬ BorderMixedSplitLE 2 4 (fun A : Matrix (Fin 4) (Fin 4) 𝕜 => A.permanent) := by
  intro h
  obtain ⟨F, hF, hlim⟩ := h.exists_tendsto
  choose S t hS ht hsum using hF
  refine not_tendsto_sum_four_isSplit t
    (fun j v => (ht j v).isSplit_of_card_two (hS j v)) fun A => ?_
  exact (hlim A).congr fun j => hsum j A

/-- **The border mixed split rank of the `4 × 4` permanent is exactly `5`** over `ℝ` and `ℂ`
(two rows against two). -/
theorem borderMixedSplit_perm_four_iff (n : ℕ) :
    BorderMixedSplitLE 2 n (fun A : Matrix (Fin 4) (Fin 4) 𝕜 => A.permanent) ↔ 5 ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact not_borderMixedSplit_perm_four (h.mono (by omega) (by simp))
  · intro hn
    exact borderMixedSplit_perm_four.mono hn (by simp)

end Limit

/-! ### One fixed row set: exactly `(card ι).choose k` terms -/

section SingleSplit

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The permanent of a permutation matrix is `1`. -/
theorem permanent_single_perm (π : Equiv.Perm ι) :
    (Matrix.of fun i => (Pi.single (π i) 1 : ι → K)).permanent = 1 := by
  rw [Matrix.permanent, Finset.sum_eq_single π⁻¹]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp
  · intro τ _ hτ
    have : ∃ i, π (τ i) ≠ i := by
      by_contra hall
      push Not at hall
      apply hτ
      ext i
      rw [Equiv.Perm.eq_inv_iff_eq, hall i]
    obtain ⟨i, hi⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- If every row is a basis vector and two rows are the same basis vector, the permanent
vanishes. -/
theorem permanent_single_of_not_injective (σ : ι → ι) (hσ : ¬ Function.Injective σ) :
    (Matrix.of fun i => (Pi.single (σ i) 1 : ι → K)).permanent = 0 := by
  rw [Matrix.permanent]
  refine Finset.sum_eq_zero fun τ _ => ?_
  have : ∃ i, σ (τ i) ≠ i := by
    by_contra hall
    push Not at hall
    apply hσ
    have hsurj : Function.Surjective σ := fun i => ⟨τ i, hall i⟩
    exact Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨i, hi⟩ := this
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [Ne.symm hi]

/-- **Test matrices for one fixed row set.** For a set `S` of `k` rows there is a family of
`0/1` matrices `B C D`, indexed by pairs of `k`-sets of columns, such that the permanent of
`B C D` is `1` if `C = D` and `0` otherwise, and such that for every sum of `n` split products
that all use the row set `S`, the matrix of its values on the `B C D` has rank at most `n`.
(In `B C D` the rows of `S` are basis vectors placed on the columns `C` by a permutation, and
the other rows are basis vectors placed outside `D`.) -/
theorem exists_test_matrices {k : ℕ} (S : Finset ι) (hS : S.card = k) :
    ∃ B : {C : Finset ι // C.card = k} → {C : Finset ι // C.card = k} → Matrix ι ι K,
      (∀ C D, (B C D).permanent = (1 : Matrix {C : Finset ι // C.card = k} _ K) C D) ∧
      ∀ (n : ℕ) (t : Fin n → Matrix ι ι K → K), (∀ v, IsSplitProduct S (t v)) →
        (Matrix.of fun C D => ∑ v, t v (B C D)).rank ≤ n := by
  -- for each `k`-set `C` of columns, a permutation mapping `S` onto `C`
  have hperm : ∀ C : {C : Finset ι // C.card = k}, ∃ π : Equiv.Perm ι, ∀ i, i ∈ S ↔ π i ∈ C.1 := by
    intro C
    let e : {x // x ∈ S} ≃ {x // x ∈ C.1} := Finset.equivOfCardEq (hS.trans C.2.symm)
    refine ⟨e.extendSubtype, fun i => ⟨fun hi => e.extendSubtype_mem i hi, fun hi => ?_⟩⟩
    by_contra hiS
    exact e.extendSubtype_not_mem i hiS hi
  choose π hπ using hperm
  -- rows in `S` follow `π C`, the other rows follow `π D`
  refine ⟨fun C D => Matrix.of fun i => (Pi.single (if i ∈ S then π C i else π D i) 1 : ι → K),
    fun C D => ?_, fun n t ht => ?_⟩
  · by_cases hCD : C = D
    · subst hCD
      show (Matrix.of fun i => (Pi.single (if i ∈ S then π C i else π C i) 1 : ι → K)).permanent
        = _
      simp only [ite_self]
      rw [permanent_single_perm, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hCD]
      apply permanent_single_of_not_injective
      -- some column of `C` is not in `D`
      obtain ⟨j, hjC, hjD⟩ : ∃ j, j ∈ C.1 ∧ j ∉ D.1 := by
        by_contra hall
        push Not at hall
        exact hCD (Subtype.ext (Finset.eq_of_subset_of_card_le hall (by rw [C.2, D.2])))
      intro hinj
      have h₁ : (π C).symm j ∈ S := (hπ C _).mpr (by simpa using hjC)
      have h₂ : (π D).symm j ∉ S := fun hmem => hjD (by simpa using (hπ D _).mp hmem)
      have heq : (fun i => if i ∈ S then π C i else π D i) ((π C).symm j) =
          (fun i => if i ∈ S then π C i else π D i) ((π D).symm j) := by
        simp [h₁, h₂]
      exact h₂ (hinj heq ▸ h₁)
  · choose F G hFG using ht
    let U : Matrix {C : Finset ι // C.card = k} (Fin n) K :=
      fun C v => F v (fun i => Pi.single (π C i) 1)
    let V : Matrix (Fin n) {C : Finset ι // C.card = k} K :=
      fun v D => G v (fun i => Pi.single (π D i) 1)
    have hUV : (Matrix.of fun C D => ∑ v, t v
        (Matrix.of fun i => (Pi.single (if i ∈ S then π C i else π D i) 1 : ι → K))) = U * V := by
      ext C D
      rw [Matrix.mul_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hFG v]
      have e1 : (fun i : S => (Matrix.of fun i =>
          (Pi.single (if i ∈ S then π C i else π D i) 1 : ι → K)) i) =
          fun i : S => (Pi.single (π C i) 1 : ι → K) := by
        funext i
        show (Pi.single (if (i : ι) ∈ S then π C i else π D i) 1 : ι → K) = _
        simp [i.2]
      have e2 : (fun i : (Sᶜ : Finset ι) => (Matrix.of fun i =>
          (Pi.single (if i ∈ S then π C i else π D i) 1 : ι → K)) i) =
          fun i : (Sᶜ : Finset ι) => (Pi.single (π D i) 1 : ι → K) := by
        funext i
        have hi : (i : ι) ∉ S := Finset.mem_compl.mp i.2
        show (Pi.single (if (i : ι) ∈ S then π C i else π D i) 1 : ι → K) = _
        simp [hi]
      rw [e1, e2]
    rw [hUV]
    exact (Matrix.rank_mul_le_left U V).trans (U.rank_le_card_width.trans (Fintype.card_fin n).le)

/-- **One fixed row set needs `(card ι).choose k` terms.** If the permanent is a sum of `n`
split products that all use the SAME set `S` of `k` rows, then `(card ι).choose k ≤ n`. Any
field. (Proof: evaluating the decomposition on the test matrices of `exists_test_matrices`
writes the identity matrix of size `(card ι).choose k` as a matrix of rank at most `n`.) -/
theorem choose_le_of_single_split {k n : ℕ} (S : Finset ι) (hS : S.card = k)
    (t : Fin n → Matrix ι ι K → K) (ht : ∀ v, IsSplitProduct S (t v))
    (h : ∀ A : Matrix ι ι K, A.permanent = ∑ v, t v A) :
    (Fintype.card ι).choose k ≤ n := by
  obtain ⟨B, hB, hrank⟩ := exists_test_matrices (K := K) S hS
  have h1 := hrank n t ht
  have hone : (Matrix.of fun C D => ∑ v, t v (B C D)) =
      (1 : Matrix {C : Finset ι // C.card = k} _ K) := by
    ext C D
    rw [Matrix.of_apply, ← h, hB]
  rwa [hone, Matrix.rank_one, Fintype.card_finset_len] at h1

/-- **One fixed row set, in the limit.** Over an infinite field, let `g` be any function. If
for every `lam ≠ 0` the function `permanent + lam * g` is a sum of `n` split products that all
use the same set `S` of `k` rows, then `(card ι).choose k ≤ n`. So Laplace expansion along a
fixed row set cannot be improved even by border decompositions. (Proof: on the test matrices
the values form the matrix `1 + lam • M`, of rank at most `n` for all `lam ≠ 0`; if `n` were
smaller than its size, the polynomial `det (1 + X • M)` would vanish at every `lam ≠ 0` but
not at `0`.) -/
theorem choose_le_of_border_single_split [Infinite K] {k n : ℕ} (S : Finset ι) (hS : S.card = k)
    (g : Matrix ι ι K → K)
    (h : ∀ lam : K, lam ≠ 0 → ∃ t : Fin n → Matrix ι ι K → K, (∀ v, IsSplitProduct S (t v)) ∧
      ∀ A : Matrix ι ι K, A.permanent + lam * g A = ∑ v, t v A) :
    (Fintype.card ι).choose k ≤ n := by
  obtain ⟨B, hB, hrank⟩ := exists_test_matrices (K := K) S hS
  by_contra hlt
  push Not at hlt
  let M : Matrix {C : Finset ι // C.card = k} {C : Finset ι // C.card = k} K :=
    Matrix.of fun C D => g (B C D)
  have hdet : ∀ lam : K, lam ≠ 0 → (1 + lam • M).det = 0 := by
    intro lam hlam
    obtain ⟨t, ht, hsum⟩ := h lam hlam
    have h1 := hrank n t ht
    have hM : (Matrix.of fun C D => ∑ v, t v (B C D)) = 1 + lam • M := by
      ext C D
      rw [Matrix.of_apply, ← hsum, hB]
      simp [M]
    rw [hM] at h1
    by_contra hne
    have hu : IsUnit (1 + lam • M) := (Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ hne)
    rw [Matrix.rank_of_isUnit _ hu, Fintype.card_finset_len] at h1
    omega
  let P : Matrix {C : Finset ι // C.card = k} {C : Finset ι // C.card = k} (Polynomial K) :=
    1 + (Polynomial.X : Polynomial K) • M.map Polynomial.C
  have heval : ∀ lam : K, P.det.eval lam = (1 + lam • M).det := by
    intro lam
    have h1 := (Polynomial.evalRingHom lam).map_det P
    rw [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext C D
    by_cases hCD : C = D
    · subst hCD
      simp [P]
      exact mul_comm _ _
    · simp [P, hCD]
      exact mul_comm _ _
  have hzero : P.det = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {x : K | x ≠ 0}) (fun x hx => ?_)
      (Set.finite_singleton (0 : K)).infinite_compl
    show P.det.IsRoot x
    rw [Polynomial.IsRoot, heval, hdet x hx]
  have h0 := heval 0
  rw [hzero] at h0
  simp at h0

/-- The `m × m` case of `choose_le_of_single_split`: if the `m × m` permanent is a sum of `n`
split products that all use the same set of `k` rows, then `m.choose k ≤ n`. -/
theorem choose_le_of_single_split_fin {m k n : ℕ} (S : Finset (Fin m)) (hS : S.card = k)
    (t : Fin n → Matrix (Fin m) (Fin m) K → K) (ht : ∀ v, IsSplitProduct S (t v))
    (h : ∀ A : Matrix (Fin m) (Fin m) K, A.permanent = ∑ v, t v A) :
    m.choose k ≤ n := by
  simpa using choose_le_of_single_split S hS t ht h

end SingleSplit

/-! ### Coefficient tensors, arbitrary factors, and Laplace expansion in general -/

section Coeff

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multilinear form in vectors `x i : ι → K` (`i : α`) with coefficient tensor `T`:
`∑ c, T c * ∏ i, x i (c i)`, the sum over all assignments `c` of a column to each `i`. -/
def coeffForm {α : Type*} [Fintype α] [DecidableEq α] (T : (α → ι) → K) :
    MultilinearMap (RingHom.id K) (fun _ : α => ι → K) K :=
  ∑ c : α → ι, T c •
    (MultilinearMap.mkPiAlgebra K α K).compLinearMap fun i => LinearMap.proj (c i)

omit [DecidableEq ι] in
theorem coeffForm_apply {α : Type*} [Fintype α] [DecidableEq α] (T : (α → ι) → K)
    (x : α → ι → K) : coeffForm T x = ∑ c, T c * ∏ i, x i (c i) := by
  simp [coeffForm]

/-- **Split products from coefficient tensors.** For any two coefficient tensors, the form in
the rows of `S` with the first tensor times the form in the other rows with the second tensor
is a split product for `S`. -/
theorem isSplitProduct_of_coeff (S : Finset ι) (T : ({r // r ∈ S} → ι) → K)
    (T' : ({r // r ∉ S} → ι) → K) :
    IsSplitProduct S (fun A : Matrix ι ι K =>
      (∑ c, T c * ∏ r : {r // r ∈ S}, A r (c r)) *
        (∑ c, T' c * ∏ r : {r // r ∉ S}, A r (c r))) := by
  refine ⟨coeffForm T,
    (coeffForm T').domDomCongr (Equiv.subtypeEquivRight fun i => Finset.mem_compl.symm),
    fun A => ?_⟩
  rw [coeffForm_apply, MultilinearMap.domDomCongr_apply, coeffForm_apply]
  rfl

/-- **Arbitrary factors are no better than multilinear ones.** Let `f` be multilinear in the
rows (coefficient tensor `T`). If `f` is a sum of `n` products of an ARBITRARY function of the
rows in `R v` and an arbitrary function of the other rows, each `R v` having `k` elements, then
`f` has mixed split rank at most `n` in the sense of this file (multilinear factors). This is
`multilinear_split_of_function_split` in the uniform language. -/
theorem mixedSplitLE_of_function_split {m n k : ℕ} (R : Fin n → Finset (Fin m))
    (hR : ∀ v, (R v).card = k)
    (F : ∀ v, ({r // r ∈ R v} → Fin m → K) → K) (G : ∀ v, ({r // r ∉ R v} → Fin m → K) → K)
    (f : Matrix (Fin m) (Fin m) K → K) (T : (Fin m → Fin m) → K)
    (hf : ∀ A, f A = ∑ c : Fin m → Fin m, T c * ∏ r, A r (c r))
    (h : ∀ A, f A = ∑ v, F v (fun r => A r) * G v (fun r => A r)) : MixedSplitLE k n f :=
  ⟨R, _, hR, fun v => isSplitProduct_of_coeff (R v) (fun cF => F v (fun r => Pi.single (cF r) 1))
      (fun cG => G v (fun r => Pi.single (cG r) 1)),
    multilinear_split_of_function_split R F G f T hf h⟩

/-- The permanent is the form whose coefficient tensor is the indicator of the bijective
assignments of columns to rows. -/
theorem permanent_eq_sum_bijective (A : Matrix ι ι K) :
    A.permanent = ∑ d : ι → ι, (if Function.Bijective d then 1 else 0) * ∏ r, A r (d r) := by
  rw [← permanent_transpose]
  simp only [permanent, transpose_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun σ _ => (σ : ι → ι)) ?_ ?_ ?_ ?_
  · intro σ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩
  · intro σ _ τ _ h
    exact DFunLike.coe_injective h
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact ⟨Equiv.ofBijective c hc, Finset.mem_univ _, rfl⟩
  · intro σ _
    rfl

/-- The permanent of the `m × m` matrix: arbitrary factors are no better than multilinear
ones. -/
theorem mixedSplitLE_permanent_of_function_split {m n k : ℕ} (R : Fin n → Finset (Fin m))
    (hR : ∀ v, (R v).card = k)
    (F : ∀ v, ({r // r ∈ R v} → Fin m → K) → K) (G : ∀ v, ({r // r ∉ R v} → Fin m → K) → K)
    (h : ∀ A : Matrix (Fin m) (Fin m) K,
      A.permanent = ∑ v, F v (fun r => A r) * G v (fun r => A r)) :
    MixedSplitLE k n (fun A : Matrix (Fin m) (Fin m) K => A.permanent) :=
  mixedSplitLE_of_function_split R hR F G _ _ permanent_eq_sum_bijective h

/-- An assignment `d` of columns to rows is bijective exactly when, for one (then unique) set
`C` of `k` columns, it maps the rows of `S` injectively into `C` and the other rows injectively
outside `C`. -/
theorem sum_indicator_single_split {k : ℕ} (S : Finset ι) (hS : S.card = k) (d : ι → ι) :
    ∑ C : {C : Finset ι // C.card = k},
      (if Function.Injective (fun r : {r // r ∈ S} => d r) ∧ ∀ r : {r // r ∈ S}, d r ∈ C.1
        then (1 : K) else 0) *
      (if Function.Injective (fun r : {r // r ∉ S} => d r) ∧ ∀ r : {r // r ∉ S}, d r ∉ C.1
        then 1 else 0) = if Function.Bijective d then 1 else 0 := by
  by_cases hd : Function.Bijective d
  · rw [ite_eq_left hd]
    have hcard : (S.image d).card = k := by rw [Finset.card_image_of_injective S hd.1, hS]
    rw [Finset.sum_eq_single (⟨S.image d, hcard⟩ : {C : Finset ι // C.card = k})]
    · rw [ite_eq_left, ite_eq_left, one_mul]
      · refine ⟨fun r r' hrr' => Subtype.ext (hd.1 hrr'), fun r hr => ?_⟩
        obtain ⟨s, hs, hsr⟩ := Finset.mem_image.mp hr
        exact r.2 (hd.1 hsr ▸ hs)
      · exact ⟨fun r r' hrr' => Subtype.ext (hd.1 hrr'),
          fun r => Finset.mem_image_of_mem d r.2⟩
    · intro C _ hC
      rw [ite_eq_right, zero_mul]
      rintro ⟨-, hmem⟩
      apply hC
      apply Subtype.ext
      symm
      refine Finset.eq_of_subset_of_card_le (fun j hj => ?_) (by rw [C.2, hcard])
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      exact hmem ⟨s, hs⟩
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hd]
    refine Finset.sum_eq_zero fun C _ => ?_
    by_contra hne
    apply hd
    have h1 : Function.Injective (fun r : {r // r ∈ S} => d r) ∧ ∀ r : {r // r ∈ S}, d r ∈ C.1 := by
      by_contra h1
      exact hne (by rw [ite_eq_right h1, zero_mul])
    have h2 : Function.Injective (fun r : {r // r ∉ S} => d r) ∧ ∀ r : {r // r ∉ S}, d r ∉ C.1 := by
      by_contra h2
      exact hne (by rw [ite_eq_right h2, mul_zero])
    have hinj : Function.Injective d := by
      intro i j hij
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
      · exact congrArg Subtype.val (h1.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
      · exact absurd (hij ▸ h1.2 ⟨i, hi⟩) (h2.2 ⟨j, hj⟩)
      · exact absurd (hij ▸ h1.2 ⟨j, hj⟩) (h2.2 ⟨i, hi⟩)
      · exact congrArg Subtype.val (h2.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- **Laplace expansion along the rows of `S`, any size.** For every set `S` of `k` rows the
permanent is a sum of split products that all use the row set `S`, one for each set `C` of `k`
columns (the permanent of rows `S` on the columns `C` times the permanent of the other rows on
the other columns). Any field. -/
theorem permanent_eq_sum_single_split {k : ℕ} (S : Finset ι) (hS : S.card = k) :
    ∃ t : {C : Finset ι // C.card = k} → Matrix ι ι K → K,
      (∀ C, IsSplitProduct S (t C)) ∧ ∀ A : Matrix ι ι K, A.permanent = ∑ C, t C A := by
  refine ⟨fun C A =>
    (∑ c : {r // r ∈ S} → ι, (if Function.Injective c ∧ ∀ r, c r ∈ C.1 then (1 : K) else 0) *
        ∏ r : {r // r ∈ S}, A r (c r)) *
      (∑ c : {r // r ∉ S} → ι, (if Function.Injective c ∧ ∀ r, c r ∉ C.1 then (1 : K) else 0) *
        ∏ r : {r // r ∉ S}, A r (c r)),
    fun C => isSplitProduct_of_coeff S _ _, fun A => ?_⟩
  have step : ∀ C : {C : Finset ι // C.card = k},
      (∑ c : {r // r ∈ S} → ι, (if Function.Injective c ∧ ∀ r, c r ∈ C.1 then (1 : K) else 0) *
          ∏ r : {r // r ∈ S}, A r (c r)) *
        (∑ c : {r // r ∉ S} → ι, (if Function.Injective c ∧ ∀ r, c r ∉ C.1 then (1 : K) else 0) *
          ∏ r : {r // r ∉ S}, A r (c r)) =
      ∑ d : ι → ι,
        ((if Function.Injective (fun r : {r // r ∈ S} => d r) ∧ ∀ r : {r // r ∈ S}, d r ∈ C.1
            then (1 : K) else 0) *
          (if Function.Injective (fun r : {r // r ∉ S} => d r) ∧ ∀ r : {r // r ∉ S}, d r ∉ C.1
            then 1 else 0)) * ∏ r, A r (d r) := by
    intro C
    rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    symm
    refine Fintype.sum_equiv
      (Equiv.piEquivPiSubtypeProd (fun r => r ∈ S) (fun _ => ι)) _ _ fun d => ?_
    have hprod : ∏ r, A r (d r) =
        (∏ r : {r // r ∈ S}, A r (d r)) * ∏ r : {r // r ∉ S}, A r (d r) := by
      convert (Fintype.prod_subtype_mul_prod_subtype (fun r => r ∈ S)
        (fun r => A r (d r))).symm
    rw [hprod]
    simp only [Equiv.piEquivPiSubtypeProd_apply]
    ring
  simp_rw [step]
  rw [Finset.sum_comm, permanent_eq_sum_bijective]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_mul, sum_indicator_single_split S hS d]

/-- **Laplace upper bound, any size.** If sets of `k` rows exist, the permanent has mixed
split rank at most `(card ι).choose k`. -/
theorem mixedSplit_perm_laplace {k : ℕ} (hk : k ≤ Fintype.card ι) :
    MixedSplitLE k ((Fintype.card ι).choose k) (fun A : Matrix ι ι K => A.permanent) := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (by simpa using hk)
  obtain ⟨t, ht, hsum⟩ := permanent_eq_sum_single_split (K := K) S hS
  have h := mixedSplitLE_of_fintype (fun _ : {C : Finset ι // C.card = k} => S) t
    (fun _ => hS) ht hsum
  rwa [Fintype.card_finset_len] at h

/-- **One fixed row set: exactly `(card ι).choose k` terms.** For a set `S` of `k` rows, the
permanent is a sum of `n` split products that all use the row set `S` if and only if
`(card ι).choose k ≤ n`. Any field. -/
theorem single_split_perm_iff {k n : ℕ} (S : Finset ι) (hS : S.card = k) :
    (∃ t : Fin n → Matrix ι ι K → K, (∀ v, IsSplitProduct S (t v)) ∧
      ∀ A : Matrix ι ι K, A.permanent = ∑ v, t v A) ↔ (Fintype.card ι).choose k ≤ n := by
  constructor
  · rintro ⟨t, ht, h⟩
    exact choose_le_of_single_split S hS t ht h
  · intro hn
    obtain ⟨t, ht, hsum⟩ := permanent_eq_sum_single_split (K := K) S hS
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    let e : {C : Finset ι // C.card = k} ≃ Fin ((Fintype.card ι).choose k) :=
      Fintype.equivFinOfCardEq (Fintype.card_finset_len k)
    refine ⟨Fin.append (fun i => t (e.symm i)) (fun _ _ => 0), fun v => ?_, fun A => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) v
      · rw [Fin.append_left]; exact ht _
      · rw [Fin.append_right]; exact isSplitProduct_zero S
    · rw [Fin.sum_univ_add, hsum A]
      simp only [Fin.append_left, Fin.append_right, Finset.sum_const_zero, add_zero]
      exact (e.symm.sum_comp fun C => t C A).symm

/-- Laplace at `4 × 4` in the uniform language: six split products, two rows against two. So
the mixed split rank of the `4 × 4` permanent is `5` or `6` (`not_mixedSplit_perm_four`), and
its border version is `5`. -/
theorem mixedSplit_perm_four_laplace :
    MixedSplitLE 2 6 (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent) := by
  have h := mixedSplit_perm_laplace (K := K) (ι := Fin 4) (k := 2) (by simp)
  simpa [Nat.choose] using h

end Coeff

/-! ### The first layer: one row against the rest -/

section FirstLayer

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A multilinear form in the rows of a one-element set `{i}` is a linear form in row `i`. -/
theorem multilinear_singleton {S : Finset ι} {i : ι} (hS : S = {i})
    (F : MultilinearMap (RingHom.id K) (fun _ : S => ι → K) K) (x : S → ι → K) :
    F x = ∑ j, F (fun _ => Pi.single j 1) * x ⟨i, by rw [hS]; simp⟩ j := by
  subst hS
  have hall : ∀ r : ({i} : Finset ι), r = ⟨i, by simp⟩ := fun r =>
    Subtype.ext (Finset.mem_singleton.mp r.2)
  have hx : x = Function.update x ⟨i, by simp⟩
      (∑ j, x ⟨i, by simp⟩ j • (Pi.single j 1 : ι → K)) := by
    rw [← pi_eq_sum_univ' (x ⟨i, by simp⟩), Function.update_eq_self]
  conv_lhs => rw [hx]
  rw [F.map_update_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [F.map_update_smul]
  have hu : Function.update x ⟨i, by simp⟩ (Pi.single j 1 : ι → K) = fun _ => Pi.single j 1 := by
    funext r
    rw [hall r, Function.update_self]
  rw [hu]
  simp [mul_comm]

/-- **First layer, lower bound.** If the `m × m` permanent is a sum of `n` split products for
one row against the rest (the single rows may differ from term to term), then `m ≤ n`. Any
field. From `le_of_permanent_eq_sum_row_linear_mul`. -/
theorem le_of_mixedSplit_one {m n : ℕ}
    (h : MixedSplitLE 1 n (fun A : Matrix (Fin m) (Fin m) K => A.permanent)) : m ≤ n := by
  obtain ⟨S, t, hS, ht, hsum⟩ := h
  have hi : ∀ v, ∃ i, S v = {i} := fun v => Finset.card_eq_one.mp (hS v)
  choose i hi using hi
  choose F G hFG using ht
  refine le_of_permanent_eq_sum_row_linear_mul i (fun v j => F v (fun _ => Pi.single j 1))
    (fun v A => G v (fun r => A r)) fun A => ?_
  refine (hsum A).trans (Finset.sum_congr rfl fun v _ => ?_)
  rw [hFG v A, multilinear_singleton (hi v) (F v)]

/-- **The first layer of the `m × m` permanent has mixed split rank exactly `m`** (`m ≥ 1`, any
field): the permanent is a sum of `n` split products for one row against the rest if and only
if `m ≤ n`. -/
theorem mixedSplit_one_perm_iff {m n : ℕ} (hm : 1 ≤ m) :
    MixedSplitLE 1 n (fun A : Matrix (Fin m) (Fin m) K => A.permanent) ↔ m ≤ n := by
  constructor
  · exact le_of_mixedSplit_one
  · intro hn
    have h := mixedSplit_perm_laplace (K := K) (ι := Fin m) (k := 1) (by simpa using hm)
    rw [Fintype.card_fin, Nat.choose_one_right] at h
    exact h.mono hn (by simpa using hm)

/-- The last layer (`m - 1` rows against one) of the `m × m` permanent has mixed split rank
exactly `m` as well. -/
theorem mixedSplit_pred_perm_iff {m n : ℕ} (hm : 1 ≤ m) :
    MixedSplitLE (m - 1) n (fun A : Matrix (Fin m) (Fin m) K => A.permanent) ↔ m ≤ n := by
  rw [← mixedSplit_one_perm_iff (K := K) hm]
  simpa using mixedSplitLE_compl_iff (K := K) (ι := Fin m) (k := 1) (n := n)
    (f := fun A : Matrix (Fin m) (Fin m) K => A.permanent) (by simpa using hm)

end FirstLayer

end PvsNP
