# The "two free rows" method for the balanced middle layer

Note of 2026-11-23. Code: `pequalnp/pairs.py` (every exact statement below can be rerun, Section 9).
Levels of evidence used in this note: **paper** = complete written argument here; **exact** = exact
computer check (integer arithmetic, or linear algebra modulo a prime whose conclusion holds over Q);
**numerical** = floating point; **conjecture**. Nothing here is formalised in Lean.

Notation: m = 2k, perm_m as a multilinear form in the rows r_0..r_{m-1}; a k-split product is
F(rows in S) G(rows not in S), |S| = k, F and G multilinear; a pairing is {S, S^c}. K is C unless said
otherwise.

## 0. Summary

1. **Lemma (paper), Section 1.** Fix two rows i, j; let R be the other m-2 rows, x the (m-2) x m
   matrix of those rows, and M_x the symmetric m x m matrix with zero diagonal and
   M_x[c,d] = perm(x without columns c, d), so perm_m(x, r_i, r_j) = r_i^T M_x r_j. If perm_m is a
   sum (or a limit of sums) of r k-split products, s of which separate i from j, then the common
   zero set of r - s multilinear forms, each in k rows of R, lies in D_s = {rank M_x <= s}. Four usable
   consequences are proved, all valid for limits: codimension (L1), a **multiprojective form (L2)**,
   the hypersurface form (L3) and a fibre form (L4). L2 is the one that does the work.
2. **Theorem 6 (paper + exact), Section 3.** The 6 x 6 permanent is **not a limit of sums of 7**
   3-split products. So the border mixed split rank of perm_6 at k = 3 lies in **[8, 15]**; before
   it was [6, 15]. This is two more than Claim A of the brief asked for (>= 7). The proof uses L2, six
   exact certificates (25 s in total) and a parity argument; it does **not** need the irreducibility
   of det M_x nor any classification of components.
3. At 6 x 6 the method stops at 8: for r = 8 there are 165 multisets of pairings that pass every test
   I can certify (Section 4).
4. 4 x 4: the same uniform argument gives the known border value 5 (Section 5; exact certificates).
5. **Corrections to the brief** (Section 8): (a) the plain codimension version does not prove Claim A
   (it cannot exclude s = 5, nor s = 2, nor s = 0); (b) the "Chow class of X is not a multiple of
   [Z_c]" argument of step (iv) is right in spirit, and is made rigorous by L2; (c) in the heuristic
   for Claim C the zero-column components should not count: they are invisible to every count
   vector with a zero entry, and every pattern has such a count vector.
6. **Theorem 8 (paper + exact), Section 6.** The 8 x 8 permanent is **not a limit of sums of 8**
   4-split products: border R_4(perm_8) >= 9 (Claim B for k = 4; previously 8). All cases are
   certified (irreducibility of det M_x of degree 48, and 16 multiprojective certificates). For
   general k the facts needed are listed; none of them is proved for all k. In the generic model
   the method should reach 11 at k = 4; the extra certificates for r = 9, 10 were not run.
7. **Claim C (Section 7).** In the generic model (only the generic corank loci matter) the pairs
   condition alone excludes r <= 7, 10, 13 for k = 3, 4, 5, i.e. conjectural bounds 8, 11, 14
   (integer programs), and asymptotically 4k - O(sqrt k). For k = 3 the value 8 is the theorem above.
   So the heuristic "between 2.5k and 3k" is right for small k and too pessimistic for large k, *if*
   the generic model is right. Still linear.

## 1. The lemma

### 1.1 Setting

Let perm_m = sum_{v=1..r} F_v(rows S_v) G_v(rows S_v^c) with |S_v| = k (zero terms are allowed, so
"r terms" includes "fewer than r terms"). Fix rows i != j, R = the other m-2 rows, x = (x_a)_{a in R}
in (K^m)^R.

* M_x: expansion of the permanent along the two rows i, j gives
  perm_m(x, r_i, r_j) = sum_{c != d} r_i[c] r_j[d] perm(x without columns c, d) = r_i^T M_x r_j.
  M_x is symmetric with zero diagonal, its entries are multilinear in the rows of x, and it does not
  change when the rows of x are permuted. Scaling column c of x by t_c multiplies M_x[c,d] by
  (prod t)/(t_c t_d), which does not change the rank.
* A term v *separates* i, j if exactly one of them is in S_v. For fixed x such a term is
  (linear form in r_i)(linear form in r_j): a bilinear form of rank <= 1 in (r_i, r_j).
* A non-separating term has both i, j on one side; its factor on the other side, call it f_v, is a
  multilinear form in the rows of a k-subset A_v of R and does not involve r_i, r_j.
* s = s_ij = number of separating terms, kappa = r - s the number of non-separating ones. The
  *pattern* of the pair is the family (A_v), v non-separating.
* D_s = {x : rank M_x <= s}, a closed set, stable under scaling each row of x.

**Lemma 1 (exact form; paper).** X := {x : f_v(x) = 0 for all non-separating v} is contained in D_s.

*Proof.* For x in X the non-separating terms vanish identically in (r_i, r_j), so the bilinear form
r_i^T M_x r_j is a sum of s forms of rank <= 1. ∎

Counting: each pairing separates k^2 of the k(2k-1) pairs and each row from exactly k others, so

    sum_{i<j} s_ij = r k^2,     sum_j s_ij = r k for every i,                                   (1)

and for three rows i, j, l each term separates 0 or 2 of the three pairs, so

    s_ij + s_jl + s_il is even.                                                                 (2)

### 1.2 Consequences that survive limits

A *limit decomposition* is a sequence T_n = sum_{v<=r} F_{n,v} G_{n,v} of sums of r k-split products
whose coefficients converge to those of perm_m. The row sets may depend on n; there are finitely
many families of r pairings, so after passing to a subsequence the pairings, hence s_ij and the
patterns, do not depend on n. Then T_n -> perm_m uniformly on compact sets, and for x_n -> x with
f_{n,v}(x_n) = 0 for all non-separating v, the bilinear forms T_n(x_n, ., .) have rank <= s and
converge to r_i^T M_x r_j, so rank M_x <= s (rank <= s is a closed condition). All four statements
below are proved by producing such x_n.

**(L1) Codimension (paper).** D_s meets every linear subspace of (K^m)^R of dimension kappa + 1 in a
nonzero point; equivalently some irreducible component of D_s has codimension <= kappa.
*Proof.* As Proposition A of `linear_lower_bound.md`: kappa homogeneous forms have a common zero of
norm 1 on a (kappa+1)-dimensional subspace; take a limit point. The equivalence is Lemma G there plus
the dimension theorem. ∎

**(L2) Multiprojective form (paper).** Call e in N^R a *count vector of the pattern* if there is a map
a from the non-separating terms to R with a(v) in A_v for all v and e_b = #a^{-1}(b) <= m-1 for all b
(equivalently: the monomial prod h_b^{e_b} occurs in prod_v (sum_{b in A_v} h_b)). Then for every count
vector e and every choice of linear subspaces L_b of K^m with dim L_b = e_b + 1 there is x in D_s with
x_b in L_b and x_b != 0 for every b in R.

*Proof.* Claim: multilinear forms f_v on A_v (v in V) with an assignment a as above have a common zero
x with x_b in L_b \ {0} for all b. Induction on |V|. For V empty take any nonzero vectors. Let v_0 in V,
b_0 = a(v_0), so dim L_{b_0} >= 2, and V' = V \ {v_0}. Put Y = prod_b P(L_b) and
W = {x in Y : f_v(x) = 0 for v in V'}, a closed subset. For every hyperplane H of L_{b_0} the induction
hypothesis (subspaces H and L_b for b != b_0, assignment a restricted to V') gives a point of W whose
b_0-coordinate lies in P(H). So the projection of W to P(L_{b_0}) is a closed set meeting every
hyperplane, hence infinite, and W contains an irreducible projective curve C whose projection to
P(L_{b_0}) is not constant. Suppose f_{v_0} has no zero on C. Pick points p, q of C with different
b_0-coordinates, a linear form lam_{b_0} on L_{b_0} vanishing at the b_0-coordinate of p and not at
that of q, and for the other b in A_{v_0} linear forms lam_b on L_b not vanishing at the b-coordinate
of q. Then g = prod_{b in A_{v_0}} lam_b(x_b) has the same multidegree as f_{v_0}, so g/f_{v_0} is a
regular function on the projective curve C, hence constant; it vanishes at p and not at q, a
contradiction. So f_{v_0} has a zero on C, which is a common zero of all f_v. (b_0 in A_{v_0} was used
to make g depend on the b_0-coordinate.)
Exact case: apply the claim to the f_v and use Lemma 1. Limit case: apply it to the f_{n,v}, scale the
rows of the zero x_n to norm 1 and take a limit point; its rows have norm 1 and lie in the L_b. ∎

In the language of intersection theory: X carries the class prod_v (sum_{b in A_v} h_b) of the Chow
ring of (P^{m-1})^R, and L2 says that D_s must meet a generic product of subspaces prod P^{e_b} for
every monomial h^e of that class. L2 is used in the contrapositive: **if for one count vector e of
the pattern there is one product of subspaces of dimensions e_b + 1 containing no point of D_s with
all rows nonzero, the pattern is impossible for a pair with s separating terms.** Because D_s is
invariant under permutations of the rows of x, a certificate for e serves every permutation of e.

**(L3) Hypersurface form, kappa = 1 (paper).** If kappa = 1 and the factor f is not identically zero,
then {f = 0} is contained in D_s. In the limit: normalise f_n to norm 1 (move the scalar to the other
factor), f_n -> f != 0 along a subsequence; every zero x of f is a limit of zeros of f_n (Hurwitz's
theorem on a line through x on which f is not identically zero), so {f = 0} lies in D_s.
Consequence: if s = m-1 and det M_x is irreducible over Q, the pair is impossible (if f is
identically zero the term is zero and can be dropped, giving kappa = 0 and s = m-1 < m = rank of a
generic M_x). Proof of the consequence: let f' be an irreducible factor of f over C. It vanishes
only where det M_x does, so f' divides det M_x, and f' may be taken with algebraic coefficients. The
product of its Galois conjugates has rational coefficients and divides a power of det M_x, hence is a
constant times a positive power of det M_x, which has positive degree in every row of x; but f' and its
conjugates have degree 0 in the rows outside A. Contradiction.

**(L4) Fibre form (paper).** Suppose a row b lies in every A_v. Then for every choice w of the other
m-3 rows of R, the set {y in K^m : rank M_{(w,y)} <= s} contains a linear subspace of dimension
>= m - kappa. (Exact case: the f_v(w, .) are linear forms in y. Limit case: compactness of the
Grassmannian.) Here M_{(w,y)} is linear in y, and in fact

    M_{(w,y)} = Hessian at y of the cubic g_w(y) = perm_m(w, y, y, y)/6 = sum_{c<d<l} tau_{cdl} y_c y_d y_l,

tau_{cdl} = perm(w without the columns c, d, l). So the fibres of D_s over w are the Hessian rank loci
of a squarefree cubic, and L4 says they contain large linear spaces. For m = 4, w = l is one row
and g_l = sum l_f y_c y_d y_e; for l = (1,1,1,1) it is e_3(y), with Hessian (B_y)_{ab} = y_c + y_d,
the matrix of `FourByFourLower.lean`. L4 is the "finer multilinear information" of the brief; it is
not needed for Theorem 6 and I did not find a way to turn it into certificates cheaply (one must
show that a variety contains no linear space of a given dimension).

What does **not** survive in a simple form: the statement "D_s supports an effective cycle of class
prod_v (sum h_b)". It is true in the exact case when X has the expected dimension, and in the limit
by compactness of Chow varieties, but I did not need it and do not rely on it.

### 1.3 General facts about D_s (paper)

* D_1 = D_0: a symmetric matrix of rank 1 is lam u u^T, and a zero diagonal forces it to vanish.
* D_0 = {all (m-2) x (m-2) subpermanents of x vanish}. A zero row gives M_x = 0 (codimension m).
* A zero column c of x gives M_x supported on row c and column c: rank <= 2. These loci Z_c have
  codimension m-2 and contain no point with all rows in a product of subspaces having some e_b = 0,
  if the fixed vector has a nonzero c-th entry. Z_c is in D_s for every s >= 2.
* Generic expectation for a symmetric matrix: corank t in codimension t(t+1)/2.
* For the determinant the analogous matrix of minors has rank 2 identically (Plücker relations), so
  D_2 is everything and the method gives nothing, as it must (det_8 is a sum of 15 products).

## 2. Geometry of D_s for m = 6 (x is 4 x 6, M_x is 6 x 6 with entries 4 x 4 permanents)

### 2.1 Certificates

Affine form ("cone"): to prove that every component of D_s has codimension >= c, exhibit a linear
subspace Lambda of dimension c with D_s ∩ Lambda = {0}. Multiprojective form ("multi"): to prove that
D_s has no point with all rows nonzero and x_b in L_b, with given integer subspaces L_b.
Method in both cases: the (s+1)-minors of M_x, restricted to the subspace(s), are (multi)homogeneous
polynomials g_i with integer coefficients in the coordinates. Take N + 30 random points p_b over F_p
(N = number of monomials of the tested (multi)degree D) and compute the matrix
E[(a,i), b] = mu_a(p_b) g_i(p_b), mu_a running over the monomials of degree D - deg g_i. E is the
Macaulay matrix of degree D times an evaluation matrix, so rank_p E <= rank_Q (Macaulay matrix) <= N.
If rank_p E = N, every monomial of degree D is in the ideal over Q and the g_i have no common zero
with all coordinate groups nonzero. A failure proves nothing (the degree may be too low, or the
random subset of rows too small: use `--all`). Arithmetic is exact (integers modulo p = 32003,
echelon form of `checks/gr_dual.py`); M_x and the minors modulo p were tested against direct
computation.

| statement (m = 6) | certificate | level |
|---|---|---|
| det M_x (degree 24) is irreducible over Q | restriction to a random integer line has degree 24 and is irreducible (seeds 0 and 1) | exact |
| every component of D_4 has codimension >= 3 | cone, c = 3, degree 26 (378 monomials) | exact |
| every component of D_3 has codimension >= 4 | cone, c = 4, degree 19 (1540 monomials) | exact |
| every component of D_0 = D_1 has codimension >= 6 | cone, c = 6, degree 7 (792 monomials) | exact |
| D_3 misses a product of subspaces of dimensions (5,1,1,1) | multi, e = (4,0,0,0), multidegree (5,4,4,4) | exact |
| D_3 misses (4,2,1,1) | multi, e = (3,1,0,0), (5,5,4,4) | exact |
| D_3 misses (6,1,1,1) | multi, e = (5,0,0,0), (7,4,4,4) | exact |
| D_3 misses (5,2,1,1) | multi, e = (4,1,0,0), (8,8,4,4), 4455 monomials | exact |
| D_2 misses (5,2,1,1) and (6,2,1,1) | multi, e = (4,1,0,0) at (5,5,3,3); e = (5,1,0,0) at (5,5,3,3) | exact |
| D_0 misses (6,2,1,1) and (6,3,1,1) | multi, e = (5,1,0,0) and (5,2,0,0), (2,2,1,1), all products | exact |

The first six multiprojective lines were recomputed with the prime 65521 (same result).

### 2.2 The components (numerical, except where a certificate is quoted)

Sampling (`pairs.py sample`, and the coordinator's `strata.py`): minimise |M_x - A A^T|^2 over complex x
with unit rows; at a solution of rank exactly s the rank of the conditions u^T dM u' = 0 (u, u' in the
kernel) is a lower bound for the local codimension.

| s | components seen | codimension |
|---|---|---|
| 5 | det M_x = 0, irreducible (exact) | 1 |
| 4 | points of rank exactly 4, tangent codimension 3 (generic corank 2); certified >= 3 | 3 |
| 3 | zero-column loci Z_c (rank 2); points of rank exactly 3, tangent codimension 6 (18 of 24 starts) | 4 (Z_c); 6 |
| 2 | Z_c (rank 2, codimension 4); isolated finds of rank 2 without zero column, tangent codimension 7 and 8 | 4 (Z_c); >= 7 (numerical) |
| 1, 0 | a zero row (codimension 6); others seen have tangent codimension 9 and 11; certified >= 6 | 6 |

Other loci found by hand: rows 1, 2, 3 zero in two columns (codimension 6, rank <= 4); two rows
supported on two columns with vanishing 2 x 2 permanent (codimension 9, M_x = 0, all rows nonzero).
I did **not** classify the components; Theorem 6 does not need it.

A warning on reading multigraded ranks: for e = (2,1,1,0) the corank of the Macaulay matrix grew
linearly along the diagonal multidegrees (t,t,t), which looks like a curve of solutions; it is a
transient (the numerical search finds no point, and other count vectors certify at once). The
certificates are one-sided: only "CERTIFIED" means something.

## 3. Theorem 6: perm_6 is not a limit of sums of 7 balanced split products

**Theorem 6 (paper + exact).** Let K = C or R. The 6 x 6 permanent is not a limit of sums of 7
products F(3 rows) G(the other 3 rows), with row sets free to differ between terms and along the
sequence. In particular it is not an exact sum of 7 such products over any field of characteristic 0
(extend scalars to C; for arbitrary function factors use `multilinear_split_of_function_split`).
Hence 8 <= border R_3(perm_6) <= 15.

*Proof.* Suppose it is, with r = 7 (fewer terms: add zero terms). Pass to a subsequence with constant
pairings. Here R has 4 rows and A_v = R \ {rho_v}: a pattern is a multiset of kappa omitted rows.
Take a pair i, j with s = s_ij <= 3, so kappa = 7 - s >= 4.

* s = 3, kappa = 4. Every multiset of 4 omitted rows has a count vector that is a permutation of
  (4,0,0,0) or of (3,1,0,0). (If some row b is omitted by no term, send all four terms to b. Otherwise
  rho = {1,2,3,4}: send the terms omitting 2, 3, 4 to row 1 and the term omitting 1 to row 2.)
  D_3 misses products of dimensions (5,1,1,1) and (4,2,1,1). Contradiction with L2.
* s = 2, kappa = 5. Every multiset of 5 omitted rows has a count vector of type (5,0,0,0) (a row
  omitted by no term) or (4,1,0,0) (all rows are omitted, so some row a is omitted exactly once: send
  that term to another row b and the other four to a). D_2 is contained in D_3, which misses (6,1,1,1) and
  (5,2,1,1). Contradiction.
* s = 1, kappa = 6, D_1 = D_0. Every multiset of 6 omitted rows has a count vector of type (5,1,0,0)
  (some row a is omitted at most once). D_0 misses (6,2,1,1). Contradiction.
* s = 0, kappa = 7. Every multiset of 7 omitted rows has a count vector of type (5,2,0,0). D_0 misses
  (6,3,1,1). Contradiction.

The four statements about count vectors were also verified by enumeration of all 35, 56, 84, 120
multisets (`pairs.py support`). So s_ij >= 4 for all 15 pairs. By (1), sum_j s_ij = 21 for every row
i, over five values >= 4: the values are 4, 4, 4, 4, 5. Let s_ij = 5 and l a third row. Then
s_il = s_jl = 4 (the only 5 of row i is at j, the only 5 of row j is at i), so
s_ij + s_il + s_jl = 13 is odd, contradicting (2). (Also checked by enumerating all 11440 multisets of
7 pairings: none has all s_ij >= 4.) ∎

Remarks. (a) Everything used is on the list of Section 2.1 (the six multiprojective lines for D_3
and D_0) plus Lemma L2; the command `python3 pairs.py theorem6` reruns all of it in 25 s.
(b) Claim A of the brief (r = 6) follows. Its own route also works after two repairs (Section 8):
s = 5 by L3 and irreducibility, s = 4 and s = 3 by L1 with codim D_4 >= 3 and codim D_3 >= 4,
s = 2 by L2 as above, s = 1 by L1 with codim D_0 >= 6; then every s_ij is 0 or 6, "never separated"
is an equivalence relation with at most two classes (three rows in three classes cannot be pairwise
separated by one term), so all six terms are on one pairing, against the flattening rank 20.
(c) The proof is permanent-specific through the certificates only.
(d) Not independently refereed. The weakest link is the correctness of the certificate code; the
ranks came out equal to the number of monomials exactly (never larger), for two primes.

## 4. What the method gives for r = 8 at 6 x 6

For r = 8 the same certificates exclude s = 3 (kappa = 5), s = 2 (kappa = 6: every pattern has a count
vector of type (5,1,0,0), and D_2 misses (6,2,1,1)) and s = 1 (kappa = 7, type (5,2,0,0)). Not
excluded: s >= 4, and s = 0 (kappa = 8; no certificate tried). L1 cannot exclude s = 4 (kappa = 4,
codim D_4 = 3) or s = 5 (kappa = 3).

Exhaustive search (`pairs.py combx 3 8 ...`): 165 multisets of 8 pairings have all s_ij in {4,..,8},
for example 012, 012, 013, 013, 024, 024, 034, 034 (twelve pairs with s = 4, three with s = 8); 235
if s = 0 is allowed as well, for example four copies of 012 and four of 013.

To go past 8 one needs a finer statement about s = 4 with kappa = 4 (or s = 5, kappa = 3). Candidates,
none carried out:
* L4 when the four A_v share a row b (i.e. the four omitted rows miss b): the Hessian corank-2
  locus of the cubic g_w, a surface of degree 35 in P^5, would have to contain a projective line for
  every w. This needs a certificate that a surface contains no line.
* The cycle statement: the codimension-3 part of D_4 has class 35 (h_1+h_2+h_3+h_4)^3 (Harris-Tu
  formula, if it has the expected dimension); if it is irreducible it contains no complete
  intersection of three trilinear forms, which would exclude s = 4 with kappa = 3 (relevant for
  r = 7 only, where it is no longer needed).
* The analogue of the pattern-by-pattern analysis of `exact_five_terms_4x4.md`. Not attempted.

So for 6 x 6: **proved 8 <= border value <= 15**, and the present tools do not decide r = 8.

## 5. 4 x 4 (k = 2): the uniform argument gives 5

Here R = {l, u}, every A_v = R, a pattern is just kappa, and its count vectors are all (a, b) with
a + b = kappa, a, b <= 3.

| fact (m = 4) | certificate | level |
|---|---|---|
| det M_x (degree 8) irreducible over Q | line restriction irreducible of degree 8 (seed 2; seeds 0, 1, 3 hit rational points) | exact |
| every component of D_2 has codimension >= 2; a random 3-dimensional subspace meets D_2 in 4 points | cone c = 2 at degree 6; Hilbert function 4 in degrees 13, 14 for c = 3 | exact; the count 4 is one-sided |
| D_2 misses a product of dimensions (3,1) | multi e = (2,0) at (3,3), seeds 1, 2 | exact |
| D_0 misses (4,1), (4,2), (3,3) | multi e = (3,0), (3,1), (2,2) | exact |
| every component of D_0 has codimension >= 4 | cone c = 4, degree 3 | exact |

With r = 4: s = 3 is excluded by L3; s = 2 (kappa = 2) by L2 with e = (2,0); s = 1 (kappa = 3) by L2
with e = (3,0); s = 0 (kappa = 4) by L2 with e = (3,1). So all six s_ij equal 4, against (1)
(sum = 16). Hence perm_4 is not a limit of sums of 4 products: the Lean-proved bound 5, by the same
argument as Theorem 6. For r = 5 the pairs with s = 3 (kappa = 2) and s = 2 (kappa = 3) are not excluded by
anything I ran (for kappa = 3 the count vector (3,0) is met by the "ten lines" component; the other
count vectors were not tested), consistent with the border value being exactly 5.
D_2 at m = 4: the zero-column loci (codimension 2) and the ten-lines component (codimension 3), as
in the brief; the second seed of the (2,0) certificate failed only because the fixed random vector
had a zero entry (then a zero column is possible), which is the expected behaviour.

## 6. General k

### 6.1 What Claim B (R_k(perm_2k) >= 2k + 1, limits included) needs

Let r = 2k = m. A pair with s separating terms has kappa = m - s. It is enough to exclude
1 <= s <= m-1 for every pair: then every s_ij is 0 or m, the argument of Remark (b) in Section 3 puts
all terms on one pairing, and C(2k,k) > 2k. The cases:

* (B1) s = m-1: det M_x irreducible over Q (L3), or just: no factor that is multilinear in k rows.
* (B2) 2 <= s <= m-2 (kappa = m-s between 2 and m-2): for every family of kappa k-subsets A_v of the
  m-2 rows, a count vector e and a product of subspaces of dimensions e_b + 1 missed by D_s. Any two
  k-subsets of a (2k-2)-set meet when k >= 3, and a 2-subset T of R meets A_v unless T is inside the
  (k-2)-set R \ A_v; for k = 4 a suitable T always exists when kappa <= 14, so count vectors supported
  on two rows suffice (verified by enumeration for kappa = 2, 6, 7).
* (B3) s = 1 (kappa = m-1): the same for D_0.

In terms of codimension: (B2) and (B3) follow from "every component of D_s that contains a point with
all rows nonzero and meets the relevant products has codimension > m - s", i.e. from
codim D_{m-t} > t for 2 <= t <= m-3 (true generically since t(t+1)/2 > t), together with the
zero-column statement for s = 2 and codim D_0 >= m. I have **no proof for all k** of any of these.
What is proved for all k: Lemma 1, L1 to L4, (1), (2), the facts of Section 1.3 and the reduction
above.

### 6.2 Theorem 8: k = 4 (x is 6 x 8, M_x is 8 x 8 with entries 6 x 6 permanents)

**Theorem 8 (paper + exact).** The 8 x 8 permanent is not a limit of sums of 8 products
F(4 rows) G(the other 4 rows) (K = C or R; exact sums: any field of characteristic 0). Hence
9 <= border R_4(perm_8) <= 53.

*Proof.* The reduction of 6.1 with the following table. Here R has 6 rows and the A_v are 4-subsets;
for every kappa <= 7 every pattern has a count vector supported on two rows of one of the listed
types (enumeration of all 120, 680, 3060, 11628, 38760, 116280 patterns, `pairs.py support`).
A certificate for D_s' with s' >= s and a count vector e' >= e (entrywise) serves (s, e).

| case (r = 8) | needed: D_s misses a product for the types | certificates (all exact) |
|---|---|---|
| s = 7, kappa = 1 | det M_x irreducible over Q (L3) | line restriction irreducible of degree 48 (seed 0, about 5 min) |
| s = 6, kappa = 2 | (2,0), (1,1) | D_6: (2,0) at multidegree (8,7,..); (1,1) at (8,8,7,..) |
| s = 5, kappa = 3 | (3,0), (2,1) | D_5: (5,0) at degree 11 (4368 monomials); (2,1) at (8,8,6,..) |
| s = 4, kappa = 4 | (4,0), (3,1), (2,2) | D_5 (5,0); D_4: (3,1) at (7,7,5,..), (2,2) at (8,8,5,..) |
| s = 3, kappa = 5 | (5,0), (4,1), (3,2) | D_5 (5,0); D_3: (4,1) and (3,2) at (7,7,4,..) |
| s = 2, kappa = 6 | (6,0), (5,1), (4,2), (3,3) | D_2: (6,0) at (4,3,..); (5,1), (4,2), (3,3) at (5,5,3,..) |
| s = 1, kappa = 7 | (7,0), (6,1), (5,2), (4,3) | D_0: (7,0) at (1,..,1); the others at (2,2,1,..) |

So every s_ij is 0 or 8; as in Remark (b) of Section 3 all eight terms are then on one pairing, and
the flattening rank of perm_8 along a pairing is 70 > 8 (rank is lower semicontinuous). ∎

`python3 pairs.py theorem8` reruns the supports and the 16 certificates; `python3 pairs.py irred 8 0`
the irreducibility. Not independently refereed.

Not done for k = 4: r = 9 and r = 10, which the generic model (Section 7) says the method excludes.
For r = 9 one needs D_5 to miss the two-row types of size 4, D_4 those of size 5, D_3 of size 6,
D_2 of size 7, D_0 of size 8 (then all s_ij >= 6, against sum s_ij = 144 < 6 * 28). The two runs
tried for D_5 with (4,1) and (3,2) at multidegree (8,8,6,..) did not certify (corank 275 of 4455;
undecided, the degree is probably too low).

### 6.3 Sum matrices (paper; not exploited)

On x[a][l] = sig_a + t_l (a in R, l a column) with P(z) = prod_l (z + t_l) and lambda the functional of
Lemma B1 of `linear_lower_bound.md` (n = m-2; lambda(z^i) = i!(n-i)! e_i(sig)),
M_x[c,d] = lambda(P/((z+t_c)(z+t_d))). Extend lambda to degree n+1 by lambda(z^{n+1}) = 0 and put
psi(tau) = lambda_z((P(z) - P(-tau))/(z + tau)), a polynomial of degree exactly m-1 in tau
(leading coefficient +-n!). Then for t_c != t_d

    M_x[c,d] = (psi(t_c) - psi(t_d))/(t_d - t_c),   i.e.   M_x = diag(psi'(t_c)) - [psi[t_c, t_d]]_{c,d},

a diagonal matrix minus the full divided-difference (Löwner) matrix of the polynomial psi, and the
second matrix equals V^T H V with V the Vandermonde matrix of t and H the Hankel matrix
(psi_{p+q+1}), of rank m-1. The dimension-theorem argument of Proposition B would turn a bound for the
rank strata of "diagonal minus Löwner" inside the (2m-3)-dimensional space of sum matrices into a
bound for every component of D_s. I did not find the count; the zero diagonal is what makes it hard.
The certificates of Section 2.1 do not need it.

## 7. Claim C: how far can the pairs condition go?

A pair with s = m - t separating terms (t >= 1) needs D_s to meet the products of every count vector of
its pattern, with kappa = r - s.

**Generic model (conjecture).** Only the generic corank-t locus matters: a pair is possible iff
r - s >= t(t+1)/2. (Zero-column loci do not count: every pattern has a count vector with a zero entry.
Loci with zero rows do not count either. Special components with all rows nonzero would weaken the
model; at m = 6 the certified facts agree with it for s = 3 up to kappa = 5 and for s = 2 up to
kappa = 6, and D_0 is excluded at least up to kappa = 7.)

For fixed r the possible s form an up-set s >= s_min(r), so the pairs condition is a covering problem:
is there a multiset of r pairings in which every pair of rows is separated at least s_min(r) times?
Integer programs (`pairs.py comb K`):

| k | m | r excluded | first r not excluded | example | Laplace / best known border bound |
|---|---|---|---|---|---|
| 3 | 6 | <= 7 (this is Theorem 6) | 8 (s_min = 4) | 012, 015, 024, 045 twice each | 20 / 15 |
| 4 | 8 | <= 10 (proved: <= 8, Theorem 8) | 11 (s_min = 5) | 0123 x3, 0147 x2, 0246 x3, 0367 x3 | 70 / 53 |
| 5 | 10 | <= 13 | 14 (s_min = 7) | 14 distinct pairings | 252 / (N + T_5 - 1 = 176) |

So the bounds of the generic model are 8 (proved), 11, 14, i.e. 2.67k, 2.75k, 2.8k; what is proved is
8 for k = 3 and 9 for k = 4. Asymptotically: the average of s
is r k/(2k-1), about r/2, and all pairs need s >= m - t with t(t+1)/2 about r - m + t; solving gives
r about 4k - 4 sqrt(k). This is still linear and at most 2m. The flattening program of
`checks/flat_barrier.py` was **not** combined with the pairs condition (apart from "all terms on
one pairing is impossible"); by Proposition 1 of `next_steps.md` it adds at most a constraint that
four or so well-chosen pairings satisfy, and the examples in the table use at least four distinct
pairings, so I expect no gain, but this was not computed.

What would beat the generic model: the finer statements of Section 4 (L4, cycle classes), which
could exclude pairs at the boundary kappa = t(t+1)/2.

## 8. Errors and corrections to the brief

1. "r >= s_ij + (least codimension of a component of D_{s_ij})" is correct but does **not** give
   Claim A: for r = 6 it leaves s = 5 (D_5 is a hypersurface), s = 2 (the zero-column loci have
   codimension 4 = kappa) and s = 0. The brief's own list of extra arguments (irreducibility for
   s = 5, a class argument for s = 2) is what is needed; the clean tool is L2.
2. Step (iv): "the only components of D_2 of codimension <= 4 are the Z_c" need not be classified.
   It is enough that every pattern has a count vector with a zero entry and that D_2 (even D_3)
   misses one product of subspaces for it.
3. The sanity check at 4 x 4 in the brief ("no plane on the quartic for generic l") is the L4 route;
   the L2/L3 route of Section 5 is simpler and is what generalises.
4. D_0 at 6 x 6: codimension 6 is right (zero row; certified >= 6), but with all rows nonzero D_0 is
   much smaller (the largest locus I know has codimension 9), and this is what the method sees.
5. Claim C: the dichotomy "low s <= rho + 2 / high s" of the brief treats the zero-column loci as
   available; by L2 they are not. In the generic model there are no low pairs at all for r < 2m.
6. A random integer line can hit rational points of {det M_x = 0} when x has only two rows (m = 4:
   three of four seeds), so one irreducible restriction is the certificate, not every restriction.

## 9. Reproduction

    cd pequalnp
    python3 pairs.py theorem6                      # all exact ingredients of Theorem 6 (25 s); add --prime=65521
    python3 pairs.py theorem8                      # supports and 16 certificates of Theorem 8; plus: pairs.py irred 8 0
    python3 pairs.py irred 6 0                     # det M_x irreducible, m = 6 (about 1 min); irred 4 2; irred 8 0 (about 5 min)
    python3 pairs.py cone 6 4 3 26                 # codim D_4 >= 3
    python3 pairs.py cone 6 3 4 19                 # codim D_3 >= 4
    python3 pairs.py cone 6 0 6 7                  # codim D_0 >= 6
    python3 pairs.py multi 6 3 4,1,0,0 8,8,4,4     # one multiprojective certificate (others: table in 2.1)
    python3 pairs.py multi 6 2 5,1,0,0 5,5,3,3
    python3 pairs.py multi 4 2 2,0 3,3 1 --all     # 4 x 4 (seed 1)
    python3 pairs.py support 3 5 5 4,1             # count vectors of all patterns
    python3 pairs.py combx 3 7 4,5,6,7             # no multiset of 7 pairings; combx 3 8 4,5,6,7,8 gives 165
    python3 pairs.py comb 4                        # generic model, integer program
    python3 pairs.py sample 6 3 24                 # numerical sampling of D_3
    python3 pairs.py hilb 6 3 4 40                 # Hilbert function on a random subspace (finds the degree)

## 9a. Literature (web search of 2026-11-23; I read search summaries only, not the papers)

* Boralevi, Carlini, Michalek, Ventura, *On the codimension of permanental varieties*,
  https://arxiv.org/abs/2402.17839 : loci where all subpermanents of a given size vanish (our D_0 and
  Z_m), and the singular locus of the permanental hypersurface. I found nothing on the rank loci of
  the matrix M_x of (m-2)-subpermanents, and no use of the terms "permanental adjugate/adjoint" for it.
* Hessian rank loci of cubic hypersurfaces are classical (e.g. https://arxiv.org/abs/2305.10871,
  *On the Hessian of cubic hypersurfaces*); by L4 the fibres of D_s are such loci for the squarefree
  cubic g_w. I did not find the cubics perm(w, y, y, y) treated.
* Lampert, Moshkovitz (https://arxiv.org/abs/2509.06294) and Kopparty-Moshkovitz-Zuiddam: geometric
  rank <= partition rank, the mechanism of `linear_lower_bound.md`. Lemma 1 is a two-slice version:
  fixing all but two factors, a partition-rank decomposition gives a matrix of rank <= s on a variety
  cut out by r - s forms. Kumar's method for homogeneous branching programs and its refinement by
  Gesmundo-Ghosal (https://arxiv.org/abs/2205.02149) bound the dimension of a singular locus in the
  same spirit. I found no earlier use of the two-free-rows restriction for partition rank or for
  unordered set-multilinear branching programs (Arvind-Raja, https://arxiv.org/abs/1511.02308;
  Brand-Kaski-Wang, https://arxiv.org/abs/2607.02241), but the search was two queries deep, so
  absence of evidence only.
