import PvsNP.FourByFourExactA
import PvsNP.FourByFourExactC

/-!
# The `4 × 4` permanent is not an exact sum of five split products

A *split product* is a bilinear form in two rows of a `4 × 4` matrix times a bilinear form in
the other two rows (`IsSplitProduct`, `MixedSplitLE` of `PvsNP.SplitRank`). Laplace expansion
writes the permanent with six split products, and sums of five split products converge to the
permanent (`borderMixedSplit_perm_four_iff`). This file proves that five do not suffice
exactly, over every field of characteristic zero:

* `not_mixedSplit_perm_four_five`: the permanent is not a sum of five split products;
* `mixedSplit_perm_four_iff`: it is a sum of `n` split products if and only if `6 ≤ n`.

So the exact value (six) is strictly larger than the border value (five).

## Structure of the proof

A decomposition has a *pattern* `(n0, n1, n2)`: the numbers of terms on the pairings `01|23`,
`02|13`, `03|12` (`HasDec`, `exists_hasDec_of_mixedSplit`). Row permutations permute the
pairings, so five patterns remain:

* `(5,0,0)`: `no_dec_500` (rank of the flattening), file `FourByFourExactA`;
* `(4,1,0)`: `no_dec_410` (restriction to two planes), file `FourByFourExactA`;
* `(3,2,0)`: `no_dec_320` and `(2,2,1)`: `no_dec_221`, file `FourByFourExactB`, from the
  structure of a pencil whose slices are singular (`weakS`, file `FourByFourExactPencil`:
  the sixteen planes on the quartic `det B_u = 0`);
* `(3,1,1)`: `no_dec_311`, file `FourByFourExactC` (the ten nodes of the quartic).

The tools common to all patterns are in `FourByFourExactBase`.
-/

namespace PvsNP

open Matrix

variable {K : Type*} [Field K]

/-- No pattern with five terms has a decomposition of the permanent. -/
theorem not_hasDec_of_sum_five [CharZero K] {n0 n1 n2 : ℕ} (h : n0 + n1 + n2 = 5) :
    ¬ HasDec K n0 n1 n2 := by
  intro hD
  have h0 : n0 ≤ 5 := by omega
  have h1 : n1 ≤ 5 := by omega
  have h2 : n2 ≤ 5 := by omega
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;>
    first
      | omega
      | exact no_dec_500 hD
      | exact no_dec_500 hD.swap12
      | exact no_dec_500 hD.swap23.swap12
      | exact no_dec_410 hD
      | exact no_dec_410 hD.swap12
      | exact no_dec_410 hD.swap23
      | exact no_dec_410 hD.swap12.swap23
      | exact no_dec_410 hD.swap23.swap12
      | exact no_dec_410 hD.swap12.swap23.swap12
      | exact no_dec_320 hD
      | exact no_dec_320 hD.swap12
      | exact no_dec_320 hD.swap23
      | exact no_dec_320 hD.swap12.swap23
      | exact no_dec_320 hD.swap23.swap12
      | exact no_dec_320 hD.swap12.swap23.swap12
      | exact no_dec_311 hD
      | exact no_dec_311 hD.swap12
      | exact no_dec_311 hD.swap23.swap12
      | exact no_dec_221 hD
      | exact no_dec_221 hD.swap23
      | exact no_dec_221 hD.swap12.swap23

/-- **The `4 × 4` permanent is not a sum of five split products.** Over a field of
characteristic zero, the permanent of a `4 × 4` matrix is not a sum of five products of a
bilinear form in two rows and a bilinear form in the other two rows, whatever pairs of rows
the five terms use. -/
theorem not_mixedSplit_perm_four_five {K : Type*} [Field K] [CharZero K] :
    ¬ MixedSplitLE 2 5 (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent) := by
  intro h
  obtain ⟨n0, n1, n2, hsum, hD⟩ := exists_hasDec_of_mixedSplit h
  exact not_hasDec_of_sum_five hsum hD

/-- **The mixed split rank of the `4 × 4` permanent is exactly six** (two rows against two,
characteristic zero): the permanent is a sum of `n` split products if and only if `6 ≤ n`. -/
theorem mixedSplit_perm_four_iff {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    MixedSplitLE 2 n (fun A : Matrix (Fin 4) (Fin 4) K => A.permanent) ↔ 6 ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact not_mixedSplit_perm_four_five (h.mono (by omega) (by simp))
  · intro hn
    exact mixedSplit_perm_four_laplace.mono hn (by simp)

end PvsNP
