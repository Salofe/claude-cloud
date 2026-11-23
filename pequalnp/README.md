# Split products of the permanent

This folder started as an attempt on P vs NP through its algebraic cousin (is the permanent as
easy as the determinant?). **Nothing here bears on P vs NP itself.** What it contains is a set of
results, most of them machine-checked in Lean, about one concrete measure of the complexity of
the permanent, for which no good lower bound is known.

Every statement below carries one of four labels:

- **Lean**: proved in `lean/` (Lean 4.36.0 + Mathlib), no `sorry`, only the standard axioms
  `propext`, `Classical.choice`, `Quot.sound`.
- **paper**: a complete written proof in `notes/`, not machine-checked.
- **exact**: an exact computer check (integer, rational or modular arithmetic).
- **numerical**: floating-point evidence only.

## The question

Take an `m × m` matrix with rows `r_0, …, r_{m-1}`. A **split product** for a set `S` of rows is

    F(rows in S) · G(rows not in S)

with `F` and `G` multilinear. Laplace expansion along a fixed set of `k` rows writes the
permanent as a sum of `C(m, k)` split products, all with the same `S`.

The **mixed split rank** is the least number of split products with `|S| = k` that add up to the
permanent when the row sets may differ from term to term. The **border** (limit) value is the
least `n` such that the permanent is a limit of sums of `n` such products. In the literature this
is the `(k, m-k)` partition rank, and it is exactly the width of one layer of an *unordered
set-multilinear branching program*. No superpolynomial lower bound is known for such programs
computing the permanent ([Arvind–Raja](https://arxiv.org/abs/1511.02308)).

The middle layer is `m = 2k`. A *pairing* is `{S, complement of S}`; there are `N = C(2k,k)/2` of
them, and Laplace uses `2N` terms.

## Results

### 4 × 4, two rows against two: completely settled

| statement | status | where |
|---|---|---|
| the permanent is a limit of sums of 5 split products | Lean | `FiveTerm.lean`, `borderMixedSplit_perm_four` |
| it is not a limit of sums of 4 (over ℝ and ℂ) | Lean | `FourByFourLower.lean`, `borderMixedSplit_perm_four_iff` |
| it is an exact sum of `n` split products if and only if `n ≥ 6` (characteristic 0) | Lean | `FourByFourExact.lean`, `mixedSplit_perm_four_iff` |

So the exact value is 6 (Laplace is optimal) and the limit value is 5: a fully machine-checked
example where this rank drops in the limit. For comparison the 4 × 4 determinant is an exact sum
of 3 ([Lampert–Moshkovitz](https://arxiv.org/abs/2509.06294)).

### General size

| statement | status | where |
|---|---|---|
| with one fixed row set, exactly `C(m,k)` terms are needed, also in the limit | Lean | `SplitRank.lean`, `single_split_perm_iff`, `choose_le_of_border_single_split` |
| first layer (one row against the rest): exactly `m` | Lean | `mixedSplit_one_perm_iff` |
| 6 × 6: limit of sums of 15 (Laplace: 20) | Lean | `FifteenTerm.lean`, `borderMixedSplit_perm_six` |
| `2k × 2k`: the square identity behind the upper bounds | Lean | `Squares.lean`, `mul_permanent_eq_squares_half` |
| `2k × 2k`: limit of sums of `N + T_k − 1` terms (`T_k` the central trinomial coefficient: 5, 16, 53, …), about half of Laplace | paper + exact for `k ≤ 4` | `checks/p1_check.py` |
| `2k × 2k`: exact sum of `N + 2T_k` terms, below Laplace from `k = 5` on | paper | same identity with `lam = 1` |
| any shapes of split: at least `m` terms, also in the limit | paper + exact certificates for `m ≤ 6` | `notes/linear_lower_bound.md` |
| replacing multilinear factors by arbitrary functions does not help | Lean | `SplitBridge.lean` |

The linear lower bound rests on the statement that the `(m−1) × m` matrices whose maximal
subpermanents all vanish have codimension `m`. That is Conjecture 3.4 of
[Boralevi–Carlini–Michałek–Ventura](https://arxiv.org/abs/2402.17839), proved there for small
sizes; an unrefereed preprint ([Xie](https://arxiv.org/abs/2609.27320)) claims it in general. The
proof in `notes/linear_lower_bound.md` is short and independent (characteristic 0), but it has
only been checked by the agents of this project.

### The determinant, for contrast

| statement | status | where |
|---|---|---|
| `det_{2k}` is an exact sum of `N` products, one per pairing, for every `k ≥ 2` | paper; identity tested in exact arithmetic on random integer matrices for `k ≤ 5` | `checks/det_identities.py` |
| `det_8` is an exact sum of 15 products (Laplace: 70); `det_12` of 92 | paper; same kind of test | `checks/det_pfaffian_cover.py`, `det_pfaffian_greedy.py` |

The mechanism is `det(R) = Pf(R W Rᵀ)` and a partition of the perfect matchings of the rows into
products of matchings of the two sides of a cut (`notes/next_steps.md`, Section 3). The tests
evaluate both sides on random integer matrices; that is strong evidence for a polynomial
identity but not a symbolic proof, and the proof is the Pfaffian argument in the note. The
symmetric analogue for the permanent does not help (numerical, `k = 2, 3`). So the determinant
is far below one term per pairing, and any lower-bound method that cannot tell the permanent
from the determinant is capped accordingly.

### What does not work

- Flattening ranks, also after restricting rows to subspaces, cannot prove more than `2k²` terms
  (paper, `notes/next_steps.md`, Proposition 1). At 4 × 4 they prove 3; the truth is 5.
- Searches at 6 × 6 outside the two-block form found nothing below 15, but the solver recovers a
  known 15-term solution from only about one random start in eight, so this excludes nothing
  (`fullw_search.py`).
- Restricting to the few row pairings compatible with a fixed matching of the rows needs more
  terms than Laplace (numerical).

## Open

- Whether the middle layer of the permanent needs exponentially many terms. Known: between
  `2k` and about `N`.
- The exact and limit values at 6 × 6 (between 6 and 15 in the limit, at most 20 exactly).

## How to check

Lean (Mathlib is fetched and built on first use; this takes a while):

    cd lean && lake build

Exact checks, each a few seconds to a few minutes:

    python3 checks/p1_check.py            # square construction, k = 2, 3
    python3 checks/gr_dual.py 3 4 5       # codimension certificates (add 6: about 10 minutes)
    python3 checks/sum_matrix_referee.py  # the sum-matrix lemma
    python3 exact4.py all                 # ingredients of the 4 x 4 exact proof
    python3 checks/det_pfaffian_cover.py 4

## Files

- `lean/PvsNP/`: the Lean development. `SplitRank.lean` holds the uniform definitions
  (`IsSplitProduct`, `MixedSplitLE`, `BorderMixedSplitLE`) and the main statements.
- `notes/`: paper proofs and reports (`linear_lower_bound.md`, `exact_five_terms_4x4.md`,
  `next_steps.md`).
- `checks/`: exact and numerical checks written by independent referee agents.
- `twoblock.py`, `garbage_fast.py`, `fullw.py`, `fullw_search.py`, `lower4.py`, `exact4.py`,
  `splitrank.py`: solvers and searches.
- `permsearch.py`, `prune.py`, `bordertrack.py`, `splitcurve.py`, `redteam_check.py`: earlier
  explorations.
