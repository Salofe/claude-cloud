# The determinant at the middle layer

Note of 2026-11-23. Subject: how few k-split products add up to det_2k, what is known, and what
this says about the permanent. Companion script: `checks/det_rectangles.py`; Lean file:
`lean/PvsNP/DetFour.lean`. Levels of evidence: **Lean**, **paper** (complete argument written
here), **exact** (exact integer computer check), **numerical** (floating point), **cited**
(statement of a paper; I did not check its proof).

Notation: 2k rows r_0..r_{2k-1} in K^{2k}; W is the standard symplectic form (column pairs
(0,1), (2,3), ..), w(x,y) = x^T W y, G = R W R^T the Gram matrix G[a,b] = w(r_a, r_b). A *pairing*
is {S, S^c} with |S| = k; N = C(2k,k)/2. R_k(f) is the mixed split rank at the middle layer (least
number of products F(rows S) G(rows S^c), |S| = k, S free in each term), prk the partition rank
(all shapes of S allowed), str the strength.

## 0. Results

| statement | level |
|---|---|
| det(R) = Pf(R W R^T); expanding the Pfaffian along row 0 gives det_2k = 2k-1 products of type (2 rows \| 2k-2 rows). So **prk(det_n) <= n-1 and str(det_n) <= n-1 for every even n >= 4** | paper (classical identities) + exact for n = 4, 6, 8, 10 |
| with the Chen-Zhao lower bound (largest prime <= n): **prk(det_n) = n-1 whenever n is even and n-1 is prime** (n = 4, 6, 8, 12, 14, 18, 20, ..), e.g. prk(det_6) = 5, prk(det_8) = 7 | paper + cited |
| **R_k(det_2k) <= C(3k/2, k/2)** for every even k (3, 15, 84, 495, ..; about 2.598^k), by an explicit partition of the perfect matchings into rectangles ("min rule") | paper + exact for k = 2, 4, 6, 8 |
| more generally det_2k is a sum of C(2k-j, j) products of type (2j rows \| 2k-2j rows), 1 <= j <= k-1 | paper + exact for 2k = 8, 10, 12 |
| k odd: R_k(det_2k) <= 2k C((3k-1)/2, (k-1)/2), which is below N for k >= 7 | paper + exact for k = 3, 5, 7 |
| det_12 is a sum of **84** 6-split products (previous: 92); det_16 of 495 8-split products; det_14 of 1680 7-split products (N = 1716) | exact |
| inside the matching model (factors in the span of products of w's), with arbitrary coefficients, the cost is at least the *cover number* c(k) of the perfect matchings by pairings; **c(4) = 15**, so 15 is optimal for det_8 in that model, signed or not | paper + exact (two independent searches) |
| R_2(det_4) = 3 exactly, over every field: `mixedSplit_det_four` (upper bound), `not_mixedSplit_det_four_two` (lower bound), `mixedSplit_det_four_iff` | **Lean** (compiled, no sorry) |
| det_6 with 9 products on 3 + 3 rows: not found (all 15 orbits of nine pairings with at least seven distinct ones, single starts; residuals >= 0.10) | numerical, Section 4 |
| the exact uniform hafnian analogue for the permanent costs at least 2^(k-1) C(2k,k)/C(k,k/2) >= Laplace | paper + cited, Section 7 |

Not achieved: an upper bound c^k with c = 2 (the counting bound). The proved constant is
c = sqrt(27)/2 = 2.598.., and I have no evidence for or against c = 2: the matching model is
squeezed between c(k) >= C(2k,k)/C(k,k/2) (about 2^k/sqrt 2) and C(3k/2,k/2), see Section 2.4.
No lower bound for R_k(det_2k) beyond the cited 2k - o(k) was obtained, except at 4 x 4.

## 1. Literature

What I read: the arXiv abstract pages and the full HTML texts of the two determinant papers,
through a summarising reader that I questioned about specific statements (I did not read the
papers line by line; theorem numbers below are as reported by that reader).

* A. Lampert, G. Moshkovitz, *Slice rank and partition rank of the determinant*,
  https://arxiv.org/abs/2509.06294 (full text https://arxiv.org/html/2509.06294v1). Theorem 3.5:
  det_4 = sum of three products, one for each pairing of the rows, each factor being
  sum_{i<j} (a_{r,i} a_{s,j} - a_{r,j} a_{s,i}); Corollary 3.6: prk(det_4) = 3 over any field;
  prk(det_n) >= log2(n) + 1; Problem 1: determine the asymptotics of prk(det_n). The factor is
  the alternating form with matrix E = (sign(j - i)), whose Pfaffian is 1, so their identity is
  det(A) = Pf(A E A^T) for n = 4. According to the reader the paper does not mention Pfaffians or
  symplectic forms and gives **no upper bound for n > 4** other than the trivial n.
* Q. Chen, Y. Zhao, *Lower bounds on the strength of the determinant*,
  https://arxiv.org/abs/2607.21015 (full text https://arxiv.org/html/2607.21015v1; a preprint of
  July 2026, field assumptions not checked by me). str(det_p) = p for p prime; prk(det_n) >= largest prime <= n, hence n - n^0.525 <= prk(det_n) <= n, "where
  the upper bound is from the Laplace expansion"; str(det_4) = 3; str(f_T) <= prk(T). Open
  question (their Section 7.2): are the primes the only n with str(det_n) = n? According to the
  reader: no mention of Pfaffians, no value for n = 6 or 8, no upper bound below n except n = 4,
  nothing on balanced partitions or prescribed degrees.
* Searches for the combinatorial problem (partitions or covers of the perfect matchings of K_2k
  by products of matchings of the two sides of a balanced cut; "rectangle", "unambiguous cover",
  "biclique partition", "matching design") returned nothing that addresses it. Nearby but
  different: communication complexity of bipartite perfect matching with a fixed edge partition
  (Beniamini, https://arxiv.org/abs/2203.01071), rectangle lower bounds for unambiguous grammars
  (https://arxiv.org/abs/2412.03199). I did not find the numbers 15 or C(3k/2,k/2) in this role.

Conclusions. (a) The bound prk(det_2k) <= 2k-1 (Proposition 1 below) is not stated in either
paper as far as the reader could tell; it is two classical identities, so it may well be folklore.
Together with Chen-Zhao it gives exact values prk(det_n) = n-1 for n = 6, 8, 12, 14, 18, 20 and
answers half of their question: no even n >= 4 has str(det_n) = n. It also settles, for even n,
a remark in the introduction of Lampert-Moshkovitz (quoted by the reader: "As far as we know, it
could be true that str(det_n) = n for all n ≠ 4!"): str(det_n) <= n-1 for every even n >= 4. (b) No bound for the balanced
(k,k) rank of det_2k other than n = 4 is in these papers. Both statements should be re-checked by
a person against the PDFs before being claimed as new.

## 2. Upper bounds from the Pfaffian

### 2.1 The two identities (paper; exact checks `det_rectangles.py rowexp`)

For an alternating matrix G of even size 2k, Pf(G) = sum over perfect matchings M of
sgn(M) prod_{{a,b} in M} G[a,b], and Pf(R W R^T) = det(R) Pf(W) = det(R).

**Proposition 1.** For k >= 2,
det(r_0..r_{2k-1}) = sum_{b=1}^{2k-1} (-1)^{b-1} w(r_0, r_b) Pf(G without rows and columns 0, b).
Each summand is a bilinear form in rows 0, b times a multilinear form in the other 2k-2 rows. So
prk(det_2k) <= 2k-1 and str(det_2k) <= 2k-1.

*Proof.* Expansion of the Pfaffian along its first row. ∎ (Exact check for 2k = 4, 6, 8, 10 on
random integer matrices.) For 2k = 4 this is the Lampert-Moshkovitz identity with W in place of
E, and it is the content of `DetFour.lean`.

For odd n the same idea gives nothing below n (det_5 needs 6 products of type (2|3), see
`next_steps.md`), consistent with str(det_p) = p.

### 2.2 The min rule (paper; exact checks `det_rectangles.py minrule K` for K = 2, 4, 6, 8, `layers M`)

Let k be even. For a k-set S and sets X, Y of perfect matchings of S and of S^c,

    sgn(S,S^c) * (sum_{a in X} sgn(a) prod_a w) * (sum_{b in Y} sgn(b) prod_b w)

is one k-split product and equals the sum of the Pfaffian terms of the matchings in the
*rectangle* X x Y (`next_steps.md`, 3.2). A partition of all perfect matchings into rectangles
gives a decomposition of det_2k.

**Theorem 2 (min rule).** Order the edges of a perfect matching M of {0..2k-1} by their lower
endpoints and let S(M) be the union of the first k/2 edges. For a k-set S put t = min(S^c) and
X_S = {perfect matchings of S in which every edge has an endpoint below t}. Then
{M : S(M) = S} = X_S x {all perfect matchings of S^c}, and X_S is nonempty exactly when
[0,t) is contained in S and k/2 <= t <= k. Consequently

    det_2k = sum_S sgn(S,S^c) * (sum_{a in X_S} sgn(a) prod_a w) * Pf(G restricted to S^c)

with C(3k/2, k/2) nonzero terms: **R_k(det_2k) <= C(3k/2, k/2)**.

*Proof.* Let S(M) = S, a the first k/2 edges and b the others. The vertex t = min(S^c) lies on an
edge of b and is its lower endpoint (its partner is in S^c, hence larger). Every edge of a
precedes that edge, so its lower endpoint is below t: a is in X_S. Conversely let a in X_S and b
any perfect matching of S^c. Lower endpoints of edges of b are in S^c, hence >= t, and those of a
are < t; so the edges of a are the first k/2 and S(a ∪ b) = S. For the count: if X_S is nonempty
then S contains [0,t), the k-t vertices of S above t are matched to vertices below t, and the
other 2t-k vertices below t are matched among themselves, so k/2 <= t <= k (2t-k is even); given
t there are C(2k-1-t, k-t) choices of S, and sum_{t=k/2}^{k} C(2k-1-t, k-t) =
sum_{i=0}^{k/2} C(k-1+i, i) = C(3k/2, k/2) (hockey stick). Also |X_S| = t!/(2t-k)! * (2t-k-1)!!. ∎

In other words: expand the Pfaffian along the smallest remaining row k/2 times and collect the
terms by the set of rows used. Stopping after j expansions gives

**Corollary 3.** det_2k is a sum of C(2k-j, j) products of type (2j rows | 2k-2j rows),
1 <= j <= k-1 (j = 1: Proposition 1; j = k/2: Theorem 2). (Exact check for 2k = 8, 10, 12, all j.
The shapes (2j | 2k-2j) and (2k-2j | 2j) are the same, so the bound for a shape is C(2k-j', j')
with j' = min(j, k-j).)

| k | Laplace C(2k,k) | one per pairing N | previous | **min rule C(3k/2,k/2)** | counting bound | sizes of X_S |
|---|---|---|---|---|---|---|
| 2 | 6 | 3 | 3 | 3 | 3 | 1 (x3) |
| 4 | 70 | 35 | 15 | 15 | 12 | 2 (x10), 3 (x5) |
| 6 | 924 | 462 | 92 | **84** | 47 | 6 (x56), 12 (x21), 15 (x7) |
| 8 | 12870 | 6435 | - | 495 | 184 | 24 (x330), 60 (x120), 90 (x36), 105 (x9) |
| 10 | 184756 | 92378 | - | 3003 | 734 | |

Asymptotically C(3k/2,k/2) ~ sqrt(3/(2 pi k)) (27/4)^(k/2), i.e. base sqrt(27)/2 = 2.598.. per
unit of k, against 4 for N and for Laplace, and 2 for the counting bound. For k = 4 the min rule
has the same profile as the optimal partition found by integer programming in `next_steps.md`
(five full rectangles and ten of size 2 x 3).

### 2.3 Odd k (paper; exact checks `det_rectangles.py oddrule K` for K = 3, 5, 7)

For k odd every cut S | S^c crosses an odd number of edges of every perfect matching. Take
j = (k-1)/2, let a' be the first j edges of M, x the lower endpoint of the next edge {x,y}, and
S(M) = (vertices of a') ∪ {x}. As in Theorem 2 the fibre of S is X_S x {all (y, b')} with X_S the
set of (a', x) such that x < min(S^c) and all lower endpoints of a' are below x; there are
C((3k-1)/2, (k-1)/2) sets S. The crossing edge contributes w(r_x, r_y) = sum_i (r_x)_i (W r_y)_i,
of rank 2k across the cut, so

    det_2k = sum_S sgn(S,S^c) sum_{i<2k} [sum_{(a',x) in X_S} sgn(a',x) (r_x)_i prod_{a'} w]
                                        * [sum_{y,b'} sgn(y,b') (W r_y)_i prod_{b'} w],

**R_k(det_2k) <= 2k C((3k-1)/2, (k-1)/2)** for k odd: 24, 210, 1680, 12870 for k = 3, 5, 7, 9
against N = 10, 126, 1716, 24310. So for odd k >= 7 one product per pairing is not optimal
either, and for all k the middle-layer rank of the determinant is O(k 2.598^k). For k = 3, 5 the
identity "one product per pairing" of `next_steps.md` 3.1 remains the best known.
An untested variant for odd k: write W = omega_1 + W' with omega_1 the form of the first column
pair; then every Pfaffian term has exactly one edge carrying omega_1, which has rank 2 (not 2k)
across a cut, and the objects to be partitioned are the pairs (matching, distinguished edge).
Its counting bound is 2 (2k-1)!! / (k ((k-2)!!)^2) = 10, 42, 172 for k = 3, 5, 7, far below N
for k >= 5, but I did not find a rule whose fibres are single rectangles (the natural ones give
about 2k times more row sets, which cancels the gain).

### 2.4 Limits of the matching model (paper + exact)

*Matching model*: every factor is a linear combination of the functions prod_a w, a a perfect
matching of its row set (k even). The products prod_M w over perfect matchings M of the 2k rows
are linearly independent functions: over an algebraically closed field every alternating
2k x 2k matrix is of the form R W R^T, so the functions G[a,b], a < b, are algebraically
independent, and different matchings give different monomials in them. Hence a decomposition in the model is the same thing as a family of real
matrices g_S, one for each pairing, indexed by (matchings of S) x (matchings of S^c), with

    sum over the pairings S not crossed by M of g_S(M ∩ S, M ∩ S^c) = sgn-normalised 1   for every M,

and its number of terms is sum_S rank(g_S). Partitions into rectangles are the solutions with
0/1 matrices of disjoint supports.

**Proposition 4.** In the matching model the number of terms is at least the *cover number*
c(k) = the least number of pairings such that every perfect matching is uncrossed by one of
them. Moreover C(2k,k)/C(k,k/2) <= c(k) <= (1 + 2 ln((k-1)!!)) C(2k,k)/C(k,k/2) = O(k log k 2^k).

*Proof.* Every M needs a pairing S with g_S nonzero at M, so the pairings with g_S != 0 cover
all matchings, and each costs at least rank 1. Every pairing is uncrossed by ((k-1)!!)^2 of the
(2k-1)!! matchings and every matching leaves C(k,k/2)/2 pairings uncrossed, which gives the
lower bound and, by the greedy covering lemma (Lovász-Stein: at most 1 + ln(largest set) times
the fractional optimum), the upper bound. ∎

**Proposition 5.** c(4) = 15. Hence 15 terms are optimal for det_8 inside the matching model,
with arbitrary (signed, real) coefficients.

*Proof (exact, two ways).* Integer program (`det_rectangles.py cover 4`, solved to optimality)
and an independent exhaustive search branching on the three pairings of an uncovered matching
(`coverx 4 14`: no cover with 14 pairings, 417223 nodes). By hand: an affine structure AG(3,2)
on the 8 rows has 7 parallel classes of planes (7 pairings) and 7 parallel classes of lines (7
perfect matchings); the matching of direction d is uncrossed by exactly the pairings a with
a.d = 0, three of them, all inside the structure, and these triples are the lines of a Fano
plane. A cover must therefore contain a blocking set of that Fano plane, at least 3 pairings, for
each of the 30 affine structures on 8 points, and every pairing belongs to 6 structures:
6 |cover| >= 30 * 3. (All of this is checked by `det_rectangles.py fano`.) ∎

So the signed version asked in the brief has the answer **15 for k = 4**: allowing real
coefficients or overlapping supports does not help. For general k the model is caught between
the two exponents: 2 <= lim c(k)^(1/k) and the min rule gives 2.598. Whether partitions (or
low-rank signed solutions) with about 2^k terms exist is open; the only structural information
found: two FULL rectangles are disjoint iff |S ∩ S'| is odd, and a family of k-sets (k even)
with pairwise odd intersections has at most 2k+1 members (Gram matrix J - I over F_2), so a
partition close to the counting bound cannot consist of full rectangles.

For k = 6 see Section 3.

## 3. The numbers for k = 6

* **Partition: 84** (min rule, exact; previous value 92). I found nothing below 84: a randomised
  greedy that repeatedly takes a nearly largest rectangle of uncovered matchings
  (`det_rectangles.py partgreedy 6`, 3 runs) gives 176 to 185, far worse, and the greedy of
  `det_pfaffian_greedy.py` gave 92. The integer program over all rectangles is out of reach
  (2^15 x 2^15 rectangles per pairing), and no search over structured families was done.
* **Cover number: 48 <= c(6) <= 70.** Upper bound: randomised greedy covers with redundant
  pairings removed (`covergreedy 6 300 1`: 111 of 300 runs end with 70 pairings, the other runs
  with 77 or more; the cover is printed and re-verified). Lower bound: the integer program
  (`cover 6 900`) stopped at the time limit with dual bound 48 and incumbent 87, so it did not
  even find the greedy value. So for k = 6 the lower bound of Proposition 4 is below the min rule,
  unlike k = 4, and it is open whether the matching model allows fewer than 84 terms.
* The 70-cover is very regular (every pairing covers exactly 96 matchings alone; multiplicities
  1, 2, 4, 6, 10 occur 6720, 3024, 504, 126, 21 times) but it does **not** carry a decomposition
  with one term per pairing (exact check, one-off script): in every block the uniquely covered
  cells form a connected bipartite graph, so a rank-one matrix equal to 1 on them equals 1 on
  their whole bounding rectangle, and 1008 matchings lie in two such bounding rectangles while
  being covered exactly twice, which gives the value 2 instead of 1. Higher ranks on this cover
  were not tried.
* A lead that was tried and failed. The waste of the min rule is in the 56 rectangles with t = 3
  (size 6 x 15): they hold the 5040 matchings in which rows 0, 1, 2, 3 are all matched to rows
  >= 4. The same matchings lie in the 210 blocks S = {0, j} ∪ H (j in {1,2,3}, H four rows >= 4),
  each of size 12 x 12, six blocks per matching, so 35 of them would do if an exact cover existed.
  It does not (integer program, infeasible), and the integer program with one sub-rectangle per
  block found no feasible solution in 150 s. So 84 stands.

| k | counting bound | cover number c(k) | best decomposition in the matching model | N |
|---|---|---|---|---|
| 2 | 3 | 3 | 3 | 3 |
| 4 | 12 | **15** (exact) | **15** (optimal in the model) | 35 |
| 6 | 47 | 48..70 | 84 | 462 |

## 4. Odd k: is det_6 a sum of 9 products on 3 + 3 rows?

Known: 10 products, one for each pairing (`next_steps.md` 3.1, exact). Lower bounds: 5 (cited,
Chen-Zhao), 6 (numerical: substituting e_0 in row 0 turns a decomposition into one of det_5 by
products of type (2|3), and none with 5 terms was found in `next_steps.md`).

*The Pfaffian mechanism cannot give fewer than 10 here.* Every cut 3 + 3 crosses one or three
edges of a perfect matching of 6 rows. With one crossing edge {x,y} the term is
w(a') w(r_x, r_y) w(b'), and w across the cut has rank 6. A pairing has 9 matchings with exactly
one crossing edge (x in S, y in S^c), and one family of 6 products (index i of Section 2.3) can
carry any rank-one pattern alpha(x) beta(y) on them and nothing more (the coefficient matrix g
of a pairing costs 6 rank(g)). Since the 15 products of w's are linearly independent and a
pairing reaches only 9 of them, at least two pairings are needed: the cost is at least 12, more
than 10; the min rule of Section 2.3 gives 24. Three crossing edges are worse: one such matching
has rank 6^3 across the cut, and the six of a pairing together (the 3 x 3 determinant of the
w(r_x, r_y)) rank 20. So fewer than 10 terms would need factors outside the span of the
w-products.

*Numerical search* (`checks/splitfast.py` through `det_rectangles.py det6`, model: arbitrary
real 6 x 6 x 6 tensors as factors, Levenberg-Marquardt, ONE random start per configuration; a
run stops when the loss improves by less than 5 % in 60 iterations). The multisets of nine
pairings fall into 140 orbits under S_6 (1 with nine distinct pairings, 2 of type 2 1^7, 4 of
type 3 1^6, 8 of type 2 2 1^5, ...). Results ("residual" = relative squared residual; an
exact decomposition would reach 1e-20):

| multiset of pairings (xN = N terms on that pairing) | residual | rms of unknowns | iterations |
|---|---|---|---|
| 012;013;014;015;023;024;025;034;035 (nine distinct; `next_steps.md`, 2 starts) | 0.1000 | | |
| 012x3;034x3;015x3 (`next_steps.md`, 1 start) | 0.42 | | |
| 012x2;013;014;015;023;024;025;034 | 0.1780 | 3.26 | 78 |
| 012x2;013;014;015;023;024;034;035 | 0.1899 | 2.36 | 85 |
| 012x3;013;014;015;023;024;034 | 0.2559 | 2.65 | 86 |
| 012x3;013;014;015;023;024;025 | 0.2443 | 1.63 | 77 |
| 012x3;013;014;015;023;024;035 | 0.2922 | 0.27 | 87 |
| 012x3;013;014;023;025;034;035 | 0.2954 | 0.56 | 73 |
| 012x2;013x2;014;015;023;024;034 | 0.2669 | 0.25 | 74 |
| 012x2;013x2;014;023;024;025;034 | 0.2728 | 1.47 | 100 |
| 012x2;013x2;014;024;025;034;035 | 0.2671 | 0.36 | 79 |
| 012x2;013x2;014;015;023;024;025 | 0.2636 | 0.32 | 77 |
| 012x2;013x2;014;015;023;024;035 | 0.2994 | 0.24 | 88 |
| 012x2;013x2;014;023;024;025;035 | 0.2826 | 0.28 | 84 |
| 012x2;013x2;014;015;024;025;034 | 0.2925 | 0.26 | 90 |
| 012x2;013x2;014;015;023;024;045 | 0.2721 | 2.04 | 88 |
| 012x2;013x2;014x2;023;024;034 | 0.3198 | 0.27 | 76 |

(15 new configurations: both orbits of type 2 1^7, all four of type 3 1^6, all eight of type
2 2 1^5 and one of type 2 2 2 1 1 1. With the nine distinct pairings of `next_steps.md` this
covers every orbit with at least seven distinct pairings; 123 orbits with fewer distinct pairings
were not run.) For comparison the same solver reaches 1e-27 in about 16 iterations for
the ten distinct pairings (`next_steps.md`). None of the nine-term configurations comes close,
and the residuals follow a pattern: about 0.1 for each of the ten pairings that is missing,
slightly less when another pairing is doubled (0.10 for nine distinct pairings, 0.18 to 0.19 for
eight, 0.24 to 0.30 for seven, 0.32 for six). This is what "every pairing needs its own term"
would look like. This is numerical evidence from single starts on 17 of the 140 orbits (the
machine was heavily loaded: 1 to 10 minutes per run); it does not decide the question, and border decompositions were not searched
at all.

A side observation, not pursued: if every row is restricted to a random 4-dimensional subspace of
K^6, nine distinct pairings give residual 2e-7 after 300 iterations with slowly growing unknowns
(rms 12 to 18), the signature of a limit decomposition of the restricted tensor. So restrictions
to small subspaces are useless as a screening test for the full problem.

## 5. Lower bounds for the balanced rank of the determinant

| | k = 2 (det_4) | k = 3 (det_6) | k = 4 (det_8) |
|---|---|---|---|
| Lampert-Moshkovitz: prk(det_n) >= log2 n + 1; prk(det_4) = 3 | 3 | 4 | 4 |
| Chen-Zhao: prk(det_n) >= largest prime <= n (cited) | 3 | 5 | 7 |
| this project, Lean: `not_mixedSplit_det_four_two` | 3 | | |
| substitution to det_5 + numerics of `next_steps.md` | | 6 (numerical) | |
| matching model only: cover number | 3 | | 15 |
| best upper bound for R_k(det_2k) | **3** | 10 | 15 |
| unrestricted partition rank (Section 2.1 + Chen-Zhao) | 3 | **5** | **7** |

* The balanced rank is at least the partition rank, so the cited bound gives R_3(det_6) >= 5 and
  R_4(det_8) >= 7; R_4(det_8) >= R_{3|4}(det_7) >= prk(det_7) = 7 gives the same number by
  substitution.
* The flattening and geometric-rank arguments of this project add nothing for the determinant.
  Flattening ranks are capped by Proposition 1 of `next_steps.md` and do not distinguish det
  from perm without restrictions. The geometric-rank argument of `linear_lower_bound.md` rests
  on codim Z_m = m for the permanent; for the determinant the corresponding variety (all maximal
  minors of an (m-1) x m matrix vanish) has codimension 2, so it proves 2.
* The Lean proof at 4 x 4 is the same kind of argument (substitute e_0, choose rows in the
  kernels of the linear factors). It works because with k = 2 one substitution makes a factor of
  EVERY term linear. For k >= 3 no substitution of fewer than k-1 rows does that for terms on
  different pairings, and I see no extension.
* Is 15 optimal for det_8? Inside the matching model yes (Proposition 5). Outside it nothing is
  known beyond 7. A direct numerical search is not feasible with the present tools: the tensor
  has 8^8 = 16.7 million entries and each factor 4096 unknowns, so 14 terms have 114688 unknowns
  and the Gauss-Newton matrix of `splitfast.py` would need about 100 GB. Feasible but not done:
  a solver that works with torus weights (as `fullw.py` does for the permanent) or inside a
  larger invariant model. Restricting rows to small subspaces is cheap but misleading (end of
  Section 4).

## 6. Lean (`lean/PvsNP/DetFour.lean`, imports `PvsNP.SplitRank`)

Checked with `cd pequalnp/lean && lake env lean PvsNP/DetFour.lean` (no errors, no warnings, no
`sorry`; about 40 s). All statements are over an arbitrary field K.

* `sympPair A a b` = w(r_a, r_b); `det_fin_four` (the 24 terms);
  `det_eq_three_sympPair : A.det = sympPair A 0 1 * sympPair A 2 3 - sympPair A 0 2 * sympPair A 1 3 + sympPair A 0 3 * sympPair A 1 2`.
* `mixedSplit_det_four : MixedSplitLE 2 3 (fun A : Matrix (Fin 4) (Fin 4) K => A.det)`.
* `not_mixedSplit_det_four_two : ¬ MixedSplitLE 2 2 (fun A => A.det)`.
* `mixedSplit_det_four_iff (n) : MixedSplitLE 2 n (fun A => A.det) ↔ 3 ≤ n`.
* Helpers in the namespace `PvsNP.DetFour`: `D3` (determinant of rows e_0, x, y, z), `no_mixed`
  (D3 is not (linear form in x)(function of y, z) + (linear form in y)(function of x, z)),
  `no_same` (the same with two linear forms in x).

`#print axioms` for `mixedSplit_det_four`, `not_mixedSplit_det_four_two`,
`mixedSplit_det_four_iff`, `det_eq_three_sympPair`: `[propext, Classical.choice, Quot.sound]`.

Proof of the lower bound: put e_0 in row 0. A term on the pairing 0b|cd becomes
(linear form in r_b) * (function of r_c, r_d). If x and y are taken in the kernels of the two
linear forms the sum vanishes, so D3(x, y, z) = 0 for all such x, y and all z. Evaluating at
kernel vectors of the shape a_p e_q - a_q e_p gives a_j a'_k = 0 for all j, k (two different
pairings) or the proportionality of a and a' (same pairing), and a second round of kernel
vectors gives a = a' = 0, contradicting D3(e_1, e_2, e_3) = 1. The header of the file states the
contrast with the permanent (5 in the limit, 6 exactly). The file is not yet imported by
`PvsNP.lean` (I may not edit it); `lake build PvsNP.DetFour` succeeded, so the compiled module
exists and can be imported.

## 7. Transfer to the permanent

**Why the mechanism is special to the determinant.** Write eta_j = sum_a theta_a R[a,j] for the
column forms. With anticommuting theta the forms omega_i = eta_{2i} eta_{2i+1} commute and have
square zero, so prod_i omega_i = (sum_i omega_i)^k / k!: the determinant is the top power of ONE
2-form, which is the Pfaffian of G, a sum over perfect matchings with no further index. With
commuting theta (permanent) the quadrics q_i = eta_{2i} eta_{2i+1} do not have square zero.
For the symmetric form sigma_c = sum_i c_i sigma_i (sigma_i(x,y) = x_{2i} y_{2i+1} + x_{2i+1} y_{2i})

    Haf(R sigma_c R^T) = sum over profiles m (m_1 + .. + m_k = k) of c^m H_m,   H_(1,..,1) = perm(R),

where H_m collects the monomials in which column pair i is used by 2 m_i rows. The H_m are
nonzero with disjoint monomial supports, hence linearly independent. Every rectangle partition
P of the perfect matchings writes Haf(R sigma_c R^T) as |P| k-split products, exactly as for
the Pfaffian (no signs).

**Proposition 6 (the uniform hafnian route never beats Laplace; paper, one step cited).**
Suppose perm_2k = sum_{j<=J} lam_j Haf(R sigma_{c_j} R^T), or perm_2k is a limit of such
expressions with J terms, each hafnian being computed by a rectangle partition. Then
J >= C(k, k/2) and the number of products is at least C(k,k/2) * C(2k,k)/C(k,k/2) = C(2k,k), the
Laplace number. In the exact case J >= 2^(k-1), so the count is at least
2^(k-1) C(2k,k)/C(k,k/2); with the min rule it is 2^(k-1) C(3k/2,k/2), e.g. 120 > 70 at k = 4.

*Proof.* The H_m are independent, so sum_j lam_j c_j^m = 1 for m = (1,..,1) and 0 for the other
m (in the limit for limits), i.e. sum_j lam_j (c_j . x)^k = k! x_1 ... x_k: the monomial
x_1...x_k is a sum (a limit of sums) of J k-th powers of linear forms. Its partial derivatives of
order k/2 are the C(k,k/2) squarefree monomials of degree k/2, so its middle catalecticant has
rank C(k,k/2), which bounds J from below also for limits. Exactly, the Waring rank of x_1...x_k
is 2^(k-1) (Ranestad-Schreyer, Carlini-Catalisano-Geramita; cited from memory, not re-read).
Each hafnian needs at least the counting bound C(2k,k)/C(k,k/2) of rectangles. ∎

(The border Waring rank of x_1...x_k is stated in the literature to be 2^(k-1) as well; I did not
re-check that and it is not needed for the comparison with Laplace.)

This agrees with the numerical finding quoted in the brief (exactly 2^(k-1) powers for k = 2, 3).

**Variants.** (i) Different weights c, c' in the two factors of a product: within one
rectangle the coefficient pattern is the polynomial P(x,y) = sum_{|T| = k/2} x^T y^{T^c}, whose
flattening rank is C(k,k/2); if the garbage has to cancel inside each rectangle separately this
costs C(k,k/2) products per rectangle, and C(k,k/2) times the counting bound is again exactly
C(2k,k). (ii) So a gain can only come from garbage that cancels ACROSS rectangles, in the limit.
That is what the five-term identity does at k = 2: c = (1, lam), one product per pairing, and
the leading garbage H_(2,0) (summed over the three pairings) is cancelled by two extra products
on one pairing. It is the two-block mechanism of this project, and there "every pairing needs
its own term" (N forced) is proved inside the two-block model, whereas the whole point of the
Pfaffian rectangles is to use far fewer than N pairings. For k = 4, where the two notions first
differ (p(4) = 15 < N = 35), the garbage of a weighted hafnian consists of all H_m of order
below the multilinear one; with c = (1, lam, .., lam) these are the profiles with m_1 >= 2.
Whether they can be cancelled with few extra products is open and was **not tested** (8 x 8 is
out of reach of the solvers; nothing at 4 x 4 or 6 x 6 distinguishes the two mechanisms).

**The cap on determinant-blind lower bounds.** A lower-bound method that returns the same value
for det_2k as for perm_2k (flattening ranks without restrictions, and any method that is valid
for the determinant as well) cannot prove more than

    R_k(det_2k) <= C(3k/2, k/2) (k even),  2k C((3k-1)/2, (k-1)/2) (k odd, and N if smaller):
    3, 10, 15, 126, 84, 1680, 495 for k = 2..8,

against Laplace 6, 20, 70, 252, 924, 3432, 12870 and against the best border upper bounds for the
permanent 5, 15, 53 (k = 2, 3, 4). Asymptotically the cap is O(k 2.598^k) while N grows like
4^k / (2 sqrt(pi k)). For the first unbalanced layer (2 rows | 2k-2 rows) the cap is 2k-1
(Proposition 1), and for all shapes together it is also 2k-1, which by Chen-Zhao is the truth
for the determinant whenever 2k-1 is prime. So at the middle layer a bound of order N, or even
of order 2.6^k, must use a property that separates the permanent from the determinant; the only
such ingredient in this project is the codimension used in the geometric-rank argument (m for
perm_m, 2 for det_m), which proves m.

## 8. Reproduction

    cd pequalnp/checks
    python3 det_rectangles.py rowexp            # Proposition 1, 2k = 4..10
    python3 det_rectangles.py minrule 6         # Theorem 2 (also 2, 4, 8), det_12 = 84 products
    python3 det_rectangles.py layers 12         # Corollary 3 (also 8, 10)
    python3 det_rectangles.py oddrule 7         # Section 2.3 (also 3, 5)
    python3 det_rectangles.py cover 4; python3 det_rectangles.py coverx 4 14; python3 det_rectangles.py fano
    python3 det_rectangles.py covergreedy 6 300 1; python3 det_rectangles.py cover 6 900
    python3 det_rectangles.py signed 4 15; python3 det_rectangles.py onesided 4 60
    python3 det_rectangles.py partgreedy 6 3
    python3 det_rectangles.py det6 0 16         # slow; orbits are listed by name, in an order that
                                                # differs from the table of Section 4
    cd ../lean && lake env lean PvsNP/DetFour.lean

Failed or unfinished: the cover integer program at k = 6 (time limit); the local search
`coverls` (weak: it finds covers only near its greedy start); the randomised greedy partition
(176 at k = 6); the one-sided integer program at k = 6 was not run; nothing was found below 84
for det_12, below 15 for det_8 or below 10 for det_6.
