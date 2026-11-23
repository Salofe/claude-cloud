# What to attack next: tested proposals

Note of 2026-11-23. Subject: the mixed split rank R_k(perm_2k) at the middle layer (one cut of an
unordered set-multilinear branching program). Every proposal below was tested at small size; the
tests, their outcomes and the scripts are given. Levels of evidence: **Lean** (none in this note),
**paper** = complete written argument in this note, **exact** = exact integer or symbolic computer
check, **numerical** = floating point.

Notation as in the project brief: m = 2k rows r_0..r_{m-1}, a *pairing* is {S, S^c} with |S| = k,
N = C(2k,k)/2 pairings, a *k-split product* is F(rows in S) * G(rows in S^c).

## 0. Summary

1. **The determinant needs far fewer than N products (new, exact).** det_8 is an exact sum of
   **15** 4-split products (Laplace 70, one product per pairing 35) and det_12 an exact sum of
   **92** 6-split products (Laplace 924, one per pairing 462). The mechanism is the Pfaffian
   expansion det(R) = Pf(R W R^T) plus a partition of the perfect matchings of the rows into
   "rectangles" (Section 3). So N is not a natural barrier, and any lower-bound method that does
   not tell the permanent from the determinant is capped by these numbers.
2. **Correction to the brief.** "For k even det_2k is an exact sum of N products" holds for every
   k >= 2, odd k included, with one sign changed (Section 3.1, exact check for k = 2..5). And by
   item 1 the value N is not optimal for k = 4, 6.
3. **Flattening ranks are dead for this problem (paper + numerical).** Proposition 1: no argument
   built on ranks of flattenings after restricting the rows to subspaces (of equal or unequal
   dimensions) can prove more than 2k^2 terms; with equal dimensions and k even, not more than k.
   Measured: such arguments prove 3 at 4 x 4 (truth: 5) and 5 at 6 x 6 (Theorem L already gives 6).
4. **Calibration at 4 x 4** (true border value 5): equal-dimension flattening proves 2, unequal
   dimensions 3, Koszul flattenings 3, shifted partial derivatives 2, geometric rank 4. Only the
   pattern-by-pattern argument of `FourByFourLower.lean` reaches 5.
5. **No sign of a saving for the permanent itself**: perm_5 is not found to be a sum of 9, 8 or 7
   products F(2 rows) G(3 rows) on distinct row sets, while det_5 is an exact sum of 6 (numerical
   for the permanent, exact for the determinant).

## 1. Lower bounds from flattening ranks: a barrier (task A1)

### 1.1 The method and its integer program

Restrict row i to a generic subspace of dimension d_i (1 <= d_i <= m; d_i = 1 means substituting
a fixed vector) and write D(X) = prod_{i in X} d_i. For a set T of rows let rk_T be the rank of
the flattening (rows in T | other rows).

* For a split product, rk_T(F(S) G(S^c)) <= rho(S) := min(D(S∩T), D(S\T)) * min(D(S^c∩T), D(S^c\T)),
  with equality for generic F and G (the flattening is the Kronecker product of the flattenings of
  F and G, and a generic tensor has full flattening rank).
* The restricted permanent has rk_T =: R(d,T) <= min(D(T), D(T^c), C(m,|T|)).

Rank is subadditive and lower semicontinuous, so every (d,T) gives a necessary condition on the
numbers n_pi of terms on each pairing pi, valid for limits too:

    sum_pi n_pi * rho_{d,T}(pi) >= R(d,T).                                          (*)

The best lower bound that this method can give for terms allowed on a set P of pairings is the
integer program  min sum n_pi  subject to all conditions (*), n_pi = 0 outside P.  Any linear
combination of flattening ranks (for example "sum of the ranks over all T", or the dimension of a
space of partial derivatives graded by T) is a dual solution of its LP relaxation, so it is
covered. Script: `checks/flat_barrier.py` (option `--true` computes R(d,T) numerically for
random subspaces; otherwise the upper bound above is used, which can only overstate the method).

### 1.2 Proposition 1 (cap; paper)

Let S_i = {i, i+1, .., i+k-1} mod 2k for i = 0..k-1 (the k *cyclic interval* pairings).

**Proposition 1.** For every choice of dimensions d and every T, some cyclic interval S_i has
rho(S_i) >= min(D(T), D(T^c)) / max_j d_j. Hence the multiset "m copies of each of the k cyclic
pairings" (2k^2 terms) satisfies every condition (*), and no argument that uses only conditions
(*) can prove that more than 2k^2 terms are needed. If all d_j are equal and k is even, one copy
of each cyclic pairing satisfies every condition: the cap is k.

*Proof.* Rename so that D(T) <= D(T^c) (rho and the bound are symmetric in T, T^c). Put
x = D(S∩T), y = D(S\T), x' = D(S^c∩T), y' = D(S^c\T), so xx' = D(T) <= yy' = D(T^c). The case
x > y and x' > y' is impossible, and in the three other cases
rho = D(T) * min(1, y/x, y'/x') = D(T) * exp(-max(0, phi(S), phi(S^c))), where phi(S) = log(x/y)
and phi(S) + phi(S^c) = log(D(T)/D(T^c)) =: -delta <= 0. Let g(i) = phi(S_i) - phi(S_i^c). Since
S_k = S_0^c, g(k) = -g(0). Passing from S_i to S_{i+1} removes row i and adds row i+k, so phi(S_i)
changes by at most log d_i + log d_{i+k} and g by at most 4 log d_max. A sequence that changes sign
in steps of size <= 4 log d_max has a member with |g(i)| <= 2 log d_max. For that i,
max(phi(S_i), phi(S_i^c)) = (|g(i)| - delta)/2 <= log d_max, so rho(S_i) >= D(T)/d_max.
Equal dimensions d, k even, |T| = t <= k (else pass to T^c): rho(S) = d^(min(a,k-a) + min(t-a,k-t+a))
with a = |S∩T|, which equals d^t >= R whenever t - k/2 <= a <= k/2. The numbers a_i = |S_i∩T|
move in steps of at most 1 from a_0 to t - a_0, so one of them is floor(t/2) or ceil(t/2), and
both lie in that range because k/2 is an integer. ∎

This is the "discrete intermediate value" remark of the brief made precise. It is the same
obstruction that makes Raz-type arguments need many factors: with only two balanced factors a
single well-placed pairing is balanced with respect to any T.

### 1.3 Measured values (numerical, except where noted)

Integer optimum of the program (LP relaxation in brackets). "true" = ranks of the restricted
permanent computed numerically for random subspaces; "ub" = the upper bound for them.

| k | conditions | all N pairings | the k cyclic pairings | one pairing | known truth |
|---|---|---|---|---|---|
| 2 | equal d, true | 2 (1.38) | 2 | 6 | border 5, exact 6 |
| 2 | any d in 1..4, true (87 conditions) | **3** (2.40) | 4 | 6 | |
| 3 | equal d, true | 4 (2.44) | 4 | 20 | border in [6, 15] |
| 3 | any d in 1..6, true (396767 conditions) | **5** (2.77) | 8 | 20 | |
| 4 | equal d, ub | <= 3 (1.74) | <= 4 | 70 | border in [8, 53] |
| 4 | d in {1,2,8}, ub (150010 conditions) | LP 2.92; integer program not finished | | | |

* Against (i) all pairings: the method proves 3 at 4 x 4 and 5 at 6 x 6. At k = 4 with equal
  dimensions three pairings (0146, 0236, 0567) already satisfy every condition.
* Against (ii) the pairings of the 15-term identity (012 x3, 013 x3, 024 x2, the other seven once):
  integer optimum **5**; five of its terms (012, 013, 024, 035, 045) already satisfy every
  condition, and the full multiset satisfies every condition with a factor >= 4.58 to spare. The
  method sees nothing near 15.
* For which sets of pairings is there a nontrivial bound? Only for very few pairings (equal d;
  `fewpair.py` in the scratch folder, see Section 6): k = 3: one pairing 20, every family of two
  or more pairings containing 012: 4. k = 4 (ub): one pairing 70; two pairings between 8 and 14;
  three pairings between 3 and 14, the weakest family being {0123, 0145, 0167} with 3.
* By symmetry the LP optimum against all pairings equals max over (d,T) of
  N R / sum_pi min(rho(pi), R). For d = 2 and balanced T a random pairing is exactly balanced with
  probability about 1/sqrt(k), so this is of order sqrt(k) (heuristic estimate, consistent with the
  values 2.4, 2.8, 2.9 above): the fractional bound does not even reach the cap of Proposition 1.

Commands: `python3 flat_barrier.py 2 --true`, `python3 flat_barrier.py 3 --true` (about 5 min),
`python3 flat_barrier.py K --true --equal`, `python3 flat_barrier.py 4 --equal`.

## 2. Is any measure small on every pairing at once? Calibration at 4 x 4 (task A2)

True values at 4 x 4: border 5 (Lean), exact 6 (`notes/exact_five_terms_4x4.md`); det_4: 3.

| candidate measure | what it proves at 4 x 4 | evidence |
|---|---|---|
| flattening rank, rows restricted to equal dimensions | 2 | numerical, Section 1 |
| flattening rank, unequal dimensions (substitutions included) | 3 | numerical, Section 1 |
| Koszul flattenings Lambda^p A (x) B^* -> Lambda^(p+1) A (x) C over all groupings of the rows into A, B, C, restriction dimensions in {2,3,4}, dim A <= 9: 7668 maps | 3 (LP 2.2) | numerical (`meas4.py`) |
| shifted partial derivatives, dim < x^(=l) d^(=s) f >: (s,l) = (1,0), (2,0), (1,1), (2,1), and shifts by a variable of a derived row for s = 2, 3 | 2 (ratios perm / one split product: 1.00, 0.55, 250/199 = 1.26, 0.86, 0.88, 1.00) | numerical (`sp4.py`) |
| geometric rank (Theorem L) | 4 | paper (`notes/linear_lower_bound.md`) |
| pattern-by-pattern argument with the slice matrices B_u | 5 | Lean |

Remarks.

* A single condition can be small on all pairings at once: T = {3}, d = (2,2,2,4) at 4 x 4. The
  permanent has rank 4 and every split product, on every pairing, has rank <= 2. So a measure that is small on all
  pairings simultaneously does exist, but the gain is the factor 2 and Proposition 1 caps the family.
* The integer optimum 3 of the unequal-dimension flattening program equals the true value for
  det_4. Without restriction det and perm have the same flattening ranks C(m,t) (I did not compute
  restricted ranks of det). This is the general pattern of Section 3: a method that cannot tell
  perm from det cannot exceed the determinant's value.
* Geometric-rank arguments ("a factor of every term vanishes on a variety of small codimension")
  cannot exceed m in any variant I tried, for a structural reason (paper): with the last row free,
  every term has a factor in the other rows, of class (0/1 vector) in the Chow ring of the product
  of projective spaces of the rows; but the target variety Z_m is cut out by m divisors of the
  ample class (1,..,1), so it meets every product of subspaces of total projective dimension >= m.
  Forcing all rows to be nonzero therefore gains nothing. Using fewer rows (J of size j < m-1,
  to exploit |S| = k) fails for a different reason: a term whose two row sets both stick out of J
  costs m^(number of rows sticking out) equations, at least m, against a target codimension of at
  most j(m-j+1). At j = 2 the target (2 x m matrices with nonzero rows and vanishing 2 x 2
  subpermanents) has multiprojective codimension 2m-3 by a hand computation, far more than for
  the determinant (m-1), so the invariant is permanent-specific, but I found no way to charge it
  to split products.

At 6 x 6 the same ranking holds as far as tested: flattening 5 < geometric rank 6 <= truth <= 15.

## 3. Upper bounds: the determinant (task B)

### 3.1 One product per pairing, for every k >= 2 (exact)

With d1(S), d2(S) the minors of the rows S on the first and on the last k columns and e = (-1)^k,

    det_2k = e * sum over pairings {S,S^c}, 0 in S, of sgn(S,S^c) (d1(S) + d2(S)) (d1(S^c) + e d2(S^c)).

For k even this is the identity of `checks/det4.py`. For k odd the brief did not claim it; it
holds because the two "square" sums vanish separately: sum_{S∋0} sgn(S,S^c) d(S) d(S^c) is the value
of (i_{r_0} delta) ∧ delta on r_1..r_{2k-1}, which is 0 for a decomposable k-form delta when
k >= 2 (Laplace expansion of a determinant with repeated columns). Exact checks: symbolic for the
square sum at k = 3, random integer matrices for k = 2, 3, 4, 5 (`checks/det_identities.py`).

### 3.2 Fewer than one product per pairing: Pfaffian rectangles (exact + paper)

Let W be the standard symplectic form on K^2k and w(x,y) = x^T W y. Then det(R) = Pf(R W R^T), i.e.

    det(r_0..r_{2k-1}) = sum over perfect matchings M of the rows of sgn(M) prod_{{a,b} in M} w(r_a, r_b).

For k even and a pairing {S,S^c}, a matching with no edge across the cut is a pair (a,b) of
matchings of S and of S^c, and its term factors. So for sets X, Y of matchings of S and S^c,

    sgn(S,S^c) * (sum_{a in X} sgn(a) prod_a w) * (sum_{b in Y} sgn(b) prod_b w)

is ONE k-split product that accounts for all matchings in the *rectangle* X x Y. **A partition of
the (2k-1)!! perfect matchings into rectangles is a decomposition of det_2k into that many k-split
products.** A full rectangle holds ((k-1)!!)^2 matchings, so the counting bound for this model is
(2k-1)!!/((k-1)!!)^2 = C(2k,k)/C(k,k/2), about 2^k/sqrt(2), against N about 4^k/(2 sqrt(pi k)).

| k | Laplace | one per pairing (N) | rectangle partition found | counting bound |
|---|---|---|---|---|
| 2 | 6 | 3 | 3 (this is the Lampert-Moshkovitz identity) | 3 |
| 4 | 70 | 35 | **15** (optimal among partitions into rectangles: integer program solved to optimality) | 12 |
| 6 | 924 | 462 | **92** (greedy, not optimised) | 47 |

Each line was verified as an identity on random integer matrices in exact arithmetic
(`checks/det_pfaffian_cover.py 4`, `checks/det_pfaffian_greedy.py 6`). The 15 products for det_8
use 15 distinct pairings (0124, 0125, 0126, 0137, 0145, 0146, 0156, 0237, 0245, 0246, 0256, 0347,
0357, 0367, 0456 with their complements), five of them with full 3 x 3 rectangles and ten with
3 x 2 (5 * 9 + 10 * 6 = 105). This answers the question of the brief: det_8 IS a sum of fewer than 35 4-split products.
I did not find this in the sources I checked (abstracts of the three determinant papers of
Section 5 only); it is the classical Pfaffian identity, so it may well be known.

Unbalanced layer, same idea: det_5 is an exact sum of **6** products F(2 rows) G(3 rows), the six
row pairs being the edges of the complete graph on rows 1..4 (w ∧ w ∧ e_4 = 2 vol; the 15 terms
w(A) w(B) x_c each contain a factor w(B) with B inside {1,2,3,4}; the six such B form a minimum
vertex cover of the Petersen graph of disjoint pairs). Laplace along two fixed rows needs 10.
Exact check in `checks/det_identities.py`. Numerically no 5-term decomposition exists (all 35
multisets of five row pairs up to symmetry, 2 restarts each, residual >= 0.15), and among the six
orbits of six distinct row pairs only the K_4 works.

What the mechanism cannot do: for k odd a cut cannot avoid all edges of a perfect matching, and the
variant w^(k-1) ∧ e ∧ e' gives the counting bound 90/9 = 10 = N at k = 3. Numerically det_6 is
not a sum of 9 products on 9 distinct pairings (two restarts, both stalled at relative squared
residual 0.1000), nor of 9 products on three pairings (012, 034, 015, three each; one restart,
residual 0.42). The solver (`checks/splitfast.py`) finds the 10-term decomposition from a random
start in 16 iterations, so these failures carry some weight; multisets with repeated pairings were
otherwise not explored.

### 3.3 What this means for the permanent

* **A cap on determinant-blind lower bounds.** Any lower bound for R_k(perm_2k) proved by a method
  that gives the same value for det_2k is at most 15 at k = 4, at most 92 at k = 6, and at most
  the rectangle partition number in general (probably about 2^k up to a polynomial factor; only
  the counting bound and two data points support this). A lower bound of the order of N must use
  a property that the determinant lacks. In this project the only such ingredient so far is the
  geometric rank: GR(perm_m) = m against GR(det_m) = 2.
* **The symmetric analogue produces garbage.** Replacing W by a symmetric form on k column pairs
  gives the hafnian of R Sigma R^T = perm(R) + (monomials using some column pair twice). At k = 2
  this is the two-block model (3 + 2 = 5 terms). For k = 4 extracting the multilinear part exactly
  costs 2^(k-1) evaluations (the Waring rank of a product of k variables), i.e. 8 * 15 = 120 > 70:
  no gain. Whether a limit construction with weights on the column pairs removes the garbage
  cheaply is open and was NOT tested (the 8 x 8 tensor has 16.7 million entries, out of reach of
  the present solvers).
* Small-case contrast (numerical): perm_5 is not found to be a sum of 9 products F(2 rows)
  G(3 rows) on distinct row sets (residual 0.034), nor of 8 (two orbits) or 7 (four orbits);
  det_5 needs 6. Only exact fits on distinct row sets were tried, so this is weak evidence.

## 4. Ranked proposals

**1. Rectangle partitions of perfect matchings (upper bound, determinant; then the permanent).**
*Aim.* (a) Theorem: for even k, R_k(det_2k) <= p(k), the least number of rectangles partitioning
the perfect matchings of K_2k; p(4) = 15, p(6) <= 92. Determine the growth of p(k): is it
C(2k,k)/C(k,k/2) up to a polynomial factor? Allowing signed combinations (coefficient matrices of
low rank on each pairing instead of 0/1 rectangles) may go lower. (b) Decide whether
R_3(det_6) < 10. (c) Decide whether a weighted hafnian construction gives border
R_4(perm_8) < 35.
*Test.* det_8 = 15 products and det_12 = 92 products, exact; integer program optimal at k = 4.
For (b): 9 distinct pairings and 3 x 3 fail numerically. For (c): only the count 120 > 70 for the
naive exact version; no numerical test.
*Why not ruled out.* "Every pairing needs its own term" was proved only inside the two-block
model. The determinant identity is exact, so no barrier applies to (a).
*Difficulty.* (a) low to medium (a covering-design question; the Lean proof of the general
identity needs Pfaffians, medium; det_8 = 15 alone could be a finite Lean check but an expensive
one). (b) medium (numerics with `splitfast.py` over multisets of 9 pairings: a few minutes per
configuration). (c) hard and speculative; it is listed because it is the only route found here
that could bring the permanent below N.

**2. Adopt the determinant as a control and state the barrier (lower bounds).**
*Aim.* Record Proposition 1 and the cap of Section 3.3 as the working rule: before investing in a
lower-bound measure mu, evaluate it on det_2k; if mu cannot separate perm from det it proves at
most p(k). Concretely: prove a lower bound for R_k(det_2k) itself (is 15 optimal for det_8? the
known bound is 7, the largest prime <= 8, from Chen-Zhao), since the gap [2k - o(k), about 2^k]
for the determinant is the same open problem with one difficulty (garbage) removed.
*Test.* Sections 1 and 2: every determinant-blind candidate tried proves at most 3 at 4 x 4 and
5 at 6 x 6. *Why not ruled out.* It is itself the barrier. *Difficulty.* Writing up: low.
A superlinear lower bound for the determinant's middle layer: as hard as the main problem,
but cleaner.

**3. One more than Theorem L at 6 x 6: border R_3(perm_6) >= 7.**
*Aim.* perm_6 is not a limit of sums of 6 3-split products. Method: the one that gave 5 at 4 x 4.
Substitute a vector in row 0 (terms become F(2 rows) G(3 rows) on 10 types); for a type {a,b}
carrying j >= 1 terms, on the variety {its F_i(r_a, r_b) = 0} (codimension <= j) every other term
becomes a slice of the 3-tensor perm(v, r_a, r_b, ., ., .), whose slice rank must then be
<= 6 - j, while a generic 6 x 6 x 6 tensor has slice rank 6. Patterns concentrated on few types
are excluded by flattening (Section 1.3: few pairings is where flattening works).
*Test.* (i) Calibration at 4 x 4: after substituting the all-ones vector, the only feasible
4-term configuration is "all four slices in one direction", exactly the pattern that flattening
excludes; 3 terms: none; 5 terms: all five configurations (numerical). (ii) At 6 x 6, with row 0 =
all-ones, none of 16 randomly chosen multisets of six types admits an exact fit (one restart each,
relative squared residual >= 0.31) (numerical, `e5.py`). So nothing contradicts the statement, and
the substituted problem behaves as at 4 x 4.
*Why not ruled out.* It is not a rank method; it already beat geometric rank by one at 4 x 4.
*Difficulty.* Medium to hard: there are many patterns of 6 terms on 10 types, and the analogue of
"rank B_u <= 2 only on ten lines" is a statement about the locus where a 6 x 6 x 6 tensor in a
12-parameter family drops slice rank, which I did not compute. The gain is +1; I see no way to
iterate it (killing one type gains the number of terms on that type, at most n/N on average).

**4. Exact value at 6 x 6 and a 14-term search with the fast solver.**
*Aim.* Is the exact mixed split rank of perm_6 equal to 20 (as 6 = Laplace at 4 x 4), and is the
border value below 15? *Test.* `checks/splitfast.py` assembles the Gauss-Newton matrix from small
contractions instead of the explicit Jacobian: det_6 with 10 pairings converges from a random
start to residual 3e-32 in 16 iterations (16 s of CPU); at 4 x 4 it reproduces the known picture
(6 terms on one pairing: exact; pattern (3,1,1): residual 1e-5..1e-7 with growing unknowns, the
signature of a limit; det_4: 3 exact, 2 fails). It was NOT run on perm_6 with 14 to 19 terms.
*Why not ruled out.* Pure computation. *Difficulty.* Low; cost about a second per iteration for
10 terms, growing cubically with the number of terms. Limit decompositions will show up only as
slowly decaying residuals, so `fullw.py`-style gradings remain necessary for the border question.

**5. Pairings-versus-terms trade-off (lower bound for decompositions on few pairings).**
*Aim.* A theorem of the form: a decomposition of perm_2k (or det_2k) supported on p distinct
pairings needs at least f(k,p) terms, with f exponential in k for small p (choose T unbalanced
for all p pairings at once; restriction to dimension 2).
*Test.* Flattening integer program restricted to families of pairings (Section 1.3): k = 3: p = 1
gives 20, every family with p = 2 gives 4. k = 4 (upper bound for the ranks): p = 1: 70, p = 2:
8 to 14, p = 3: as low as 3. So the trade-off is real only for p <= 2 at these sizes, and
Proposition 1 kills it at p = k.
*Why not ruled out.* It is inside the barrier, deliberately: it describes where flattening still
says something. *Difficulty.* Low. *Value.* Low; it would only formalise "few pairings is easy".
Ranked last.

## 5. Ideas that were tested and failed

* Flattening ranks with equal or unequal restriction dimensions, and any linear combination of
  them: capped by Proposition 1; prove 3 at 4 x 4 and 5 at 6 x 6 (Section 1).
* Koszul flattenings at 4 x 4: 3. Shifted partial derivatives at 4 x 4: 2 (Section 2). In both a
  generic split product is as large as the permanent or larger in most settings.
* Geometric rank with all rows forced nonzero, or with fewer evaluated rows: capped at m (Section
  2, paper argument). Comparing multidegrees of {all first factors vanish} with that of Z_m gives
  nothing either: Z_m is a complete intersection of class (t_0 + .. + t_{m-2})^m, which contains
  every monomial.
* A real (Borsuk-Ulam) version of the same argument is weaker, not stronger: modulo 2,
  (t_a + t_b)^4 = t_a^4 + t_b^4, which vanishes on projective 3-spaces, so it cannot even exclude
  four terms on one pairing at 4 x 4.
* Substituting a vector in one row and solving the smaller problem alone: loses information. At
  4 x 4 the substituted tensor is a sum of 4 slices in one direction, although perm_4 is not a sum
  of 4 products on one pairing. The substitution must be combined with a pattern analysis.
* det_6 with fewer than 10 products: not found (two configurations only).
* perm_5 as F(2 rows) G(3 rows) with fewer than 10 products on distinct row sets: not found.
* The exact hafnian route for perm_8: 120 terms, worse than Laplace.
* Not completed: the unequal-dimension integer program at k = 4 (only its LP relaxation, 2.92,
  for dimensions in {1,2,8}).

## 6. Sources and scripts

Sources consulted for this note (abstract level unless stated):

* A. Lampert, G. Moshkovitz, *Slice rank and partition rank of the determinant*,
  https://arxiv.org/abs/2509.06294 : prk(det_4) = 3, prk(det_n) >= log2(n) + 1. Partition rank
  there allows all splits, so prk(det_n) <= n; the balanced restriction studied here is different.
* Q. Chen, Y. Zhao, *Lower bounds on the strength of the determinant*,
  https://arxiv.org/abs/2607.21015 : prk(det_n) >= largest prime <= n, prk(det_n) = n - o(n).
  This gives R_4(det_8) >= 7 and R_3(det_6) >= 5 for the balanced layer.
* P. Chatterjee, D. Kush, S. Saraf, A. Shpilka, *Lower bounds for set-multilinear branching
  programs*, https://arxiv.org/abs/2312.15874 : superpolynomial lower bounds for sums of ordered
  set-multilinear branching programs. A sum of s ordered programs gives a middle cut on s pairings,
  but there each summand has small rank for a suitable T because of its other layers; a single cut
  with arbitrary factors does not (Proposition 1). Their result does not apply to one cut.
* V. Arvind, S. Raja, https://arxiv.org/abs/1511.02308 : the open problem.
* C. Brand, P. Kaski, J. Wang, https://arxiv.org/abs/2607.02241 : partition ranks and
  multiplicative complexity (abstract only; no statement on the permanent or determinant found).
* From memory, not re-read: Efremenko-Garg-Oliveira-Wigderson, *Barriers for rank methods in
  arithmetic complexity* (rank methods cannot prove strong tensor rank bounds), and
  Limaye-Srinivasan-Tavenas (unequal set sizes make partial-derivative measures work for products
  of many factors). Proposition 1 is the two-factor counterpart: with two balanced factors unequal
  sizes buy at most a factor max d_j.

Scripts added with this note in `pequalnp/checks/`: `flat_barrier.py` (Section 1),
`det_identities.py` (3.1 and det_5), `det_pfaffian_cover.py` and `det_pfaffian_greedy.py` (3.2),
`splitfast.py` (solver). One-off scripts left in the scratch folder
`/tmp/claude-0/-home-user-claude-cloud/9d4f02d2-16ab-5b7a-9dfc-330543a2ec0f/scratchpad/next/`:
`meas4.py` (Koszul), `sp4.py` (shifted partials; its two largest settings were not run),
`fewpair.py`, `e5.py` (row 0 substituted), `det5all.py` (exhaustive det_5 / perm_5 runs), with
their logs. All numerical runs used at most 2 restarts per configuration unless stated; the machine
was heavily loaded, so the searches are small.
