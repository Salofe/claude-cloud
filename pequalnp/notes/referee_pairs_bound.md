# Referee report on `notes/pairs_bound.md` (the "two free rows" method)

Report of 2026-11-23. Refereed: `pequalnp/notes/pairs_bound.md` and `pequalnp/pairs.py`.
I did not write either. Everything below was re-derived or recomputed by me; the code I used is my own
(Appendix; nothing is shared with `pairs.py` or `checks/gr_dual.py`) except where a line says "author's code".

Levels of evidence, as in the brief: **paper** = complete written argument that I checked line by line;
**exact** = exact computer check (integers, or linear algebra modulo a prime whose conclusion holds over Q);
**numerical** = floating point. Nothing here is in Lean.

## 0. Verdict

**I could not break the two theorems.** Theorem 6 (perm_6 is not a limit of sums of 7 products of type 3 rows | 3 rows,
so the border value at 6 x 6 lies in [8, 15]) and Theorem 8 (perm_8 is not a limit of sums of 8 products of type
4 rows | 4 rows, border value at least 9) are correct as far as I can check: the paper arguments are sound, the
combinatorial case analyses were redone by my own exhaustive enumeration, and **every** exact certificate the two
proofs rest on was recomputed with independent code, other primes and other subspaces (the six 6 x 6 certificates
also by a second, different method). One real gap was found, in a side statement (the 4 x 4 recheck), and it is
repaired below. A few small inaccuracies and some additions are listed (Section 8).

| # | Statement of the note | Verdict |
|---|---|---|
| 1 | Lemma 1 (exact form), counting identities (1), (2) | **correct** (paper; identities also checked on all multisets for (k, r) = (2,4), (2,5), (3,6), (3,7), (3,8)) |
| 2 | L1 (codimension form), limits included | **correct** (paper) |
| 3 | L2 (multiprojective form), limits included | **correct** (paper; the elementary induction is right, and the statement is also a standard consequence of intersection theory, Section 1.3) |
| 4 | L3 (hypersurface form) and its consequence "s = m-1 impossible if det M_x is irreducible over Q" | **correct for k >= 3; gap for k = 2** (the degree argument is empty when R = A). **Correct after the repair** of Section 1.4 |
| 5 | L4 (fibre form, Hessian of the cubic) | **correct** (paper); not used in any theorem |
| 6 | Theorem 6: perm_6 is not a limit of sums of 7 balanced split products; 8 <= border R_3(perm_6) <= 15 | **correct** (paper + exact; all ingredients recomputed, Section 2) |
| 7 | Theorem 8: perm_8 is not a limit of sums of 8 balanced split products; border R_4(perm_8) >= 9 | **correct** (paper + exact; 16 certificates and the irreducibility of det M_x recomputed independently, Section 3) |
| 8 | Certified geometry at m = 6 (irreducibility of det M_x; codim D_4 >= 3, D_3 >= 4, D_0 >= 6; D_2 misses (5,2,1,1) and (6,2,1,1)) | **correct** (exact, recomputed). The D_2 certificates hold for subspaces whose fixed vectors have no zero entry; with a zero entry there is a genuine point of D_2 (new locus (b), Section 4) |
| 9 | Components of D_s at m = 6 (numerical table) | not a theorem; **one inaccuracy** ("rows 1, 2, 3 zero in two columns: rank <= 4" should read rank <= 3) and three explicit families added (Section 4) |
| 10 | "At 6 x 6 the method stops at 8": 165 multisets (235 with s = 0 allowed) | counts **correct** (own enumeration). **Addition**: s = 0 can be excluded too (two new certificates), so exactly the 165 survive (Section 5) |
| 11 | 4 x 4 recheck (the uniform argument gives border value >= 5) | **correct after the repair** of item 4 (the case s = 3 uses L3 with k = 2). All certificates recomputed |
| 12 | Corrections to the brief (a), (b), (c) | mathematical content **correct** (I did not see the original brief the author was given) |
| 13 | Claim C, generic model: bounds 8, 11, 14 for k = 3, 4, 5 | integer programs **correct** (examples verified; infeasibility of r = 13 at k = 5 proved by hand, Section 6). The model itself is a **conjecture**, as the note says |
| 14 | General k: (B1), (B2), (B3) open; Loewner form on sum matrices | **correct as stated** (open). The Loewner formula, which the note says was not checked, is now checked exactly at m = 6 |
| 15 | Literature | **not checked** by me (no search done) |

No statement of the note is wrong in a way that affects a theorem. No error was found in the coordinator's brief.

## 1. The lemma and its consequences (paper)

### 1.1 Lemma 1 and the points the brief asked about

* *Which factor.* For a term F(S)G(S^c) with i, j on the same side, the factor used is the one on the **other** side.
  It is a multilinear form in k rows, none of them i or j, so it is a form f_v on a k-subset A_v of R (|R| = 2k-2).
  For x with f_v(x) = 0 the whole term vanishes identically in (r_i, r_j), whatever the other factor is. Correct.
* *Separating terms.* For fixed x such a term is (linear form in r_i)(linear form in r_j): rank <= 1. Correct.
  So on X = {all f_v = 0} the bilinear form r_i^T M_x r_j has rank <= s. Correct.
* *Zero or proportional forms.* Nothing in the note uses a lower bound on the codimension of X. L1 uses only
  "kappa forms have a common nonzero zero on every (kappa+1)-dimensional linear space", L2 only the existence of a
  common zero in a product of projective spaces. Both hold for arbitrary forms, zero and proportional ones included.
  Every inequality has the right direction: X cut out by kappa forms gives a subvariety of D_s of codimension
  **<=** kappa, and the contradiction always comes from a certified statement of the opposite kind about D_s
  (all components of codimension >= c, or D_s misses a product of subspaces).
* *Identities.* (1) sum_j s_ij = rk for each i and (2) s_ij + s_jl + s_il even: correct, and verified on every
  multiset of pairings for the five (k, r) above (0 violations).

### 1.2 The limit version

Checked. After passing to a subsequence the pairings are constant. If x_n -> x and f_{n,v}(x_n) = 0 for all
non-separating v, then T_n(x_n, ., .) is a sum of s forms of rank <= 1 and converges to r_i^T M_x r_j (T_n -> perm
coefficientwise and x_n is bounded), so rank M_x <= s. In L2 the subspaces L_b are the same for all n, the zero x_n is
taken with unit rows, and D_s is stable under scaling rows. Correct. Real limits are complex limits, and the
certificates exclude complex points, so K = R is covered.

A wording point: item 1 of the note's summary ("the common zero set of r - s multilinear forms ... lies in D_s") is
literally true only in the exact case; in the limit case there are no fixed forms and only L1 to L4 hold. Section 1.2
of the note says this correctly.

### 1.3 L2

The induction is correct. Points I checked: the hyperplane H has dimension e_{b_0} = (e_{b_0} - 1) + 1, as the
induction hypothesis needs; "closed and meets every hyperplane implies infinite" holds also when dim L_{b_0} = 2
(hyperplanes are points, so the projection is everything); the curve C exists (two points of an irreducible component
with different projections lie on an irreducible curve); g/f_{v_0} is a regular function on C because g and f_{v_0}
have the same multidegree and f_{v_0} has no zero on C; the factor lam_{b_0} exists in g because b_0 is in A_{v_0}.
A zero form f_{v_0} is covered (it has zeros on C).

Second proof, as a cross-check of the use of classes: in Y = prod_b P(L_b), of dimension sum e_b = |V|, the divisors
{f_v = 0} (or all of Y) have the nef classes sum_{b in A_v} h_b; the coefficient of prod h_b^{e_b} in their product
is the number of assignments with count vector e, which is positive; an empty intersection would force the product
of the classes to be 0. So the "Chow class" intuition of the note is exactly right, and the note is right not to
rely on the stronger cycle statement, which it does not prove.

The contrapositive is applied correctly: one count vector of the pattern and **one** product of subspaces missing D_s
suffice, and D_s is invariant under permutations of the rows of x, so the position of the entries of e is immaterial.

### 1.4 L3: a gap for k = 2, and its repair

The consequence of L3 is proved in the note by: "the product of the Galois conjugates of f' is a constant times a
power of det M_x, which has positive degree in every row; but f' has degree 0 in the rows outside A". For k >= 3
there are k - 2 >= 1 rows outside A and the argument is complete (this is the case used in Theorem 8). For k = 2,
R = A has two rows, there is no row outside A, and the argument says nothing: irreducibility over Q of a form of
bidegree (4,4) does not by itself exclude four conjugate bilinear factors. The note uses L3 in exactly this case
in Section 5 ("With r = 4: s = 3 is excluded by L3").

**Repair (paper), valid for every k >= 2.** Scaling column c of x by t_c multiplies det M_x by (prod t)^(m-2), so
det M_x is a weight vector for the column torus, of weight (m-2)(1,..,1); its irreducible factors over C are weight
vectors too (a connected group cannot permute them). Let f' be an irreducible factor of f over C. It vanishes only
where det M_x does, so it divides det M_x and may be taken with algebraic coefficients; it is multilinear in a
nonempty set A' of k' <= k rows, and it is a weight vector, of some weight w with |w| = k'. Its Galois conjugates
have the same monomials, hence the same weight and the same rows. If det M_x is irreducible over Q, the product of
the d distinct conjugates is c * det M_x (distinct irreducible factors, and a rational product). Comparing row
degrees (det M_x has degree m in each of the m-2 rows) gives A' = R and d = m; comparing weights gives
d w = (m-2)(1,..,1), so w = ((m-2)/m)(1,..,1), which is not an integer vector. Contradiction. (For k >= 3 already
A' = R is impossible because |A'| <= k < 2k-2; that is the note's argument.)

**Exact confirmation for m = 4.** For my line (Appendix, `irr.py 4`), F(t) = det M_{a+tb} has degree 8 and factor
degrees [1,2,2,3] modulo 1009 and [8] modulo 1013. The second shows irreducibility over Q. The first is a Frobenius
cycle type that cannot preserve four blocks of size two (a 3-cycle on blocks would give two 3-cycles or a 6-cycle),
which is what four conjugate bilinear factors would force. So det M_x at m = 4 has no factor of bidegree (1,1) over C.

### 1.5 L1, L4, Section 1.3

L1: correct, direction included (some component of D_s has codimension <= kappa; used against certificates
"every component has codimension >= c" with c > kappa). L4: correct, including the limit (Grassmannian compactness)
and the identity M_(w,y) = Hessian of perm(w,y,y,y)/6. Section 1.3: D_1 = D_0, zero row, zero column (rank <= 2,
codimension m-2), determinant analogue of rank 2: all correct.

## 2. Theorem 6 (6 x 6, r = 7)

### 2.1 Logic

R has four rows and A_v = R minus one row. The four case statements about count vectors are right (I rechecked the
hand arguments and enumerated: 35, 56, 84, 120 patterns, none without a count vector of the stated types; my code
computes the full set of count vectors of each pattern by brute force). The types used never exceed e_b = 5 = m-1.
The certificates used are for D_3 (cases s = 3 and s = 2, since D_2 is inside D_3) and D_0 = D_1 (cases s = 1, 0),
and each count vector needed is covered:

| case | kappa | count vector types | needed: a product of these dimensions misses | certificate |
|---|---|---|---|---|
| s = 3 | 4 | (4,0,0,0), (3,1,0,0) | D_3: (5,1,1,1), (4,2,1,1) | yes |
| s = 2 | 5 | (5,0,0,0), (4,1,0,0) | D_2 (the note uses D_3): (6,1,1,1), (5,2,1,1) | yes, for D_3 and for D_2 |
| s = 1 | 6 | (5,1,0,0) | D_0: (6,2,1,1) | yes |
| s = 0 | 7 | (5,2,0,0) | D_0: (6,3,1,1) | yes |

Then all s_ij >= 4; each row has sum 21 over five values, so 4,4,4,4,5; a triple containing the pair with value 5
has sum 13, odd. Correct. Own enumeration: of the 11440 multisets of 7 pairings none has all s_ij >= 4.
Padding with zero terms to exactly 7 terms is harmless.

### 2.2 Certificates, recomputed (exact)

Logic of a certificate: the rows of the Macaulay matrix are the coefficient vectors of (monomial) x ((s+1)-minor of
M_x), all multihomogeneous of the tested multidegree, N = number of monomials of that multidegree. In the evaluation
form the rows are instead the vectors of values at more than N points; that matrix is the Macaulay matrix times a
matrix of monomial values, so its rank is at most that of the Macaulay matrix, which is at most N. Rank N modulo a
prime implies rank N over Q, so every monomial of that multidegree lies in the ideal, so there is no common zero with
every coordinate group nonzero, i.e. no point of D_s with all rows nonzero in the product of subspaces. This is the
right variety and the right conclusion for L2. A failure proves nothing.

Three independent recomputations:

1. author's code, `python3 pairs.py theorem6`: "ALL INGREDIENTS VERIFIED" (15 s);
2. **my evaluation-form code** (`refcert.py`: M_x by Ryser's formula, minors by Laplace expansion, my own blocked
   rank routine; self-tested against brute force), prime 65519, my own subspaces;
3. **my direct method** (`direct.py`: the minors are expanded as polynomials with exact integer coefficients and the
   Macaulay matrix is written down explicitly; no evaluation), prime 32749, other subspaces without zero entries.

| statement (m = 6) | multidegree | N | eval form, p = 65519 | direct Macaulay, p = 32749 |
|---|---|---|---|---|
| D_3 misses (5,1,1,1) | (5,4,4,4) | 126 | rank 126 | rank 126 (301 x 126) |
| D_3 misses (4,2,1,1) | (5,5,4,4) | 336 | rank 336 | rank 336 (553 x 336) |
| D_3 misses (6,1,1,1) | (7,4,4,4) | 792 | rank 792 | rank 792 (1100 x 792) |
| D_3 misses (5,2,1,1) | (8,8,4,4) | 4455 | rank 4455 | rank 4455 (5496 x 4455) |
| D_2 misses (6,1,1,1) | (5,3,3,3) | 252 | rank 252 | rank 252 (452 x 252) |
| D_2 misses (5,2,1,1) | (5,5,3,3) | 756 | rank 756 | rank 756 (1057 x 756) |
| D_0 misses (6,2,1,1) | (2,2,1,1) | 63 | rank 63 | rank 63 (180 x 63) |
| D_0 misses (6,3,1,1) | (2,2,1,1) | 126 | rank 126 | rank 126 (270 x 126) |

No rank ever exceeded N. So the six certificates of Theorem 6 stand, by three codes, three primes (32003, 65519,
32749) and three families of subspaces.

**Consistency test of the whole chain against a machine-checked fact** (`consist.py`). The Lean theorem
`tendsto_five_split_strong` gives a limit decomposition of perm_4 with 5 terms (3 on 01|23, 1 on 02|13, 1 on 03|12).
For the pair (0,1): s = 2, kappa = 3. By L2, D_2 at m = 4 must meet every product of dimensions (4,1), (3,2), (2,3),
(1,4), so no certificate may succeed there. My direct code gives corank 10 in every bidegree (3,3)..(8,8) for (4,1)
and (1,4) (the ten points of `FourByFourLower.lean`), and coranks 34, 38, 42 in bidegrees (5,5), (6,6), (7,7) for
(3,2) and (2,3) (five seeds each; one special seed gave more). And it certifies (3,1), as the note says. So L2 and
the certificate code agree with Lean where they can be compared, in both directions.

## 3. Theorem 8 (8 x 8, r = 8)

### 3.1 Logic

Reduction of Section 6.1: if 1 <= s_ij <= 7 is impossible for every pair, every s_ij is 0 or 8; "never separated" is
an equivalence relation; three rows in three classes would be pairwise separated by every term, impossible for a
single term; one class contradicts (1); so two classes, every term is on the same pairing, and the flattening rank
70 > 8 finishes, also in the limit. Correct.

The table of Section 6.2 is complete: for kappa <= 7 every pattern of 4-subsets of the six rows has a count vector
supported on two rows (a 2-subset T meets A_v unless T is the complement of A_v; there are 15 two-subsets and at most
7 complements), and every two-part type of size kappa (parts <= 7) is in the table. Own enumeration: 120, 680, 3060,
11628, 38760 patterns for kappa = 2..6 by brute-force count vectors, 116280 patterns for kappa = 7 by the two-subset
criterion; no exception. The domination rule ("a certificate for D_s', s' >= s, and e' >= e serves (s, e)") is
correct and is applied correctly ((4,0) and (5,0) for s = 4, 3 come from D_5 with (5,0)). The case s = 7 uses L3 with
k = 4, where the note's degree argument is complete; a zero form is handled (then rank M_x <= 7 everywhere, but
det M_x is not identically zero).

### 3.2 Certificates, recomputed (exact)

Author's code with a **second prime** (the note used one): `python3 pairs.py theorem8 --prime=65521` gives
"ALL INGREDIENTS VERIFIED".

**My code** (`refcert.py` via `run8.py`), prime 65519, my own subspaces with no zero entries, all 16 certified:

| D_s | dimensions | multidegree | rank = N |
|---|---|---|---|
| D_6 | (3,1,1,1,1,1) | (8,7,..) | 45 |
| D_6 | (2,2,1,1,1,1) | (8,8,7,..) | 81 |
| D_5 | (6,1,1,1,1,1) | (11,6,..) | 4368 |
| D_5 | (3,2,1,1,1,1) | (8,8,6,..) | 405 |
| D_4 | (4,2,1,1,1,1) | (7,7,5,..) | 960 |
| D_4 | (3,3,1,1,1,1) | (8,8,5,..) | 2025 |
| D_3 | (5,2,1,1,1,1) | (7,7,4,..) | 2640 |
| D_3 | (4,3,1,1,1,1) | (7,7,4,..) | 4320 |
| D_2 | (7,1,1,1,1,1) | (4,3,..) | 210 |
| D_2 | (6,2,1,1,1,1) | (5,5,3,..) | 1512 |
| D_2 | (5,3,1,1,1,1) | (5,5,3,..) | 2646 |
| D_2 | (4,4,1,1,1,1) | (5,5,3,..) | 3136 |
| D_0 | (8,1,1,1,1,1) | (1,..,1) | 8 |
| D_0 | (7,2,1,1,1,1) | (2,2,1,..) | 84 |
| D_0 | (6,3,1,1,1,1) | (2,2,1,..) | 126 |
| D_0 | (5,4,1,1,1,1) | (2,2,1,..) | 150 |

**Irreducibility of det M_x, independent proof** (`irr.py`; the note factors a restriction to a line over Q with
sympy). For an integer line, F(t) = det M_{a+tb} is computed modulo p by evaluation at 0..deg and interpolation in
F_p; if F mod p has full degree, the degree of any rational factor is a subset sum of the factor degrees mod p.

| m | degree | factor degrees modulo primes | conclusion |
|---|---|---|---|
| 4 | 8 | 1009: [1,2,2,3]; 1013: [8] | irreducible over Q; no bilinear factor over C (Section 1.4) |
| 6 | 24 | 1009: [1,3,4,7,9]; 1013: [1,1,8,14]; 1019: [1,10,13]; 1021: [1,1,1,3,3,4,11]; 1031: [24] | irreducible over Q |
| 8 | 48 | 1009: [1,1,1,5,12,28]; 1013: [1,5,5,16,21]; 1019: [3,3,5,8,12,17]; 1021: [48] | irreducible over Q |

(Full degree on the line, so a factorisation of det M_x would restrict to one of F with the same degrees.) This takes
one second for m = 8, against five minutes for the note's route, and uses a different line.

## 4. Geometry of D_s: recomputations, one inaccuracy, three explicit families

Cone certificates, my code, p = 65519, my own subspaces: at m = 6, D_4 on a 3-dimensional space (degree 26, rank
378 = N), D_3 on a 4-dimensional space (degree 19, rank 1540 = N), D_0 on a 6-dimensional space (degree 7, rank
792 = N); at m = 4, D_2 on a 2-dimensional space (degree 6) and D_0 on a 4-dimensional space (degree 3). So
"every component of D_4, D_3, D_0 has codimension >= 3, 4, 6" is confirmed. The logic "Lambda meets D_s only in 0
implies every component has codimension >= dim Lambda" is applied to the right variety (D_s is a cone).

**Why some D_2 certificates fail (and why that is harmless).** With my first two seeds the certificate
"D_2 misses (6,2,1,1)" gave rank 1511 of 1512, also with all 13230 rows of the Macaulay matrix, and for the first
seed corank exactly 1 again in the multidegrees (6,5,3,3), (5,6,3,3), (6,6,3,3); the author's code does the same with
its seed 2. In all three cases one of the two fixed vectors has a zero entry, and there is a genuine point of D_2
there, which I found numerically (|M - AA^T|^2 = 3e-32, singular values (0.089, 0.089, 0, 0, 0, 0); for subspaces
that certify, the same minimisation from 12 starts stays above 5e-6) and then explained:

* **(b)** *two rows vanish at a column c and the other two rows are proportional outside c and anti-proportional at c*
  (x_1 = lam x_3 on the other columns, x_1c = -lam x_3c). Then every subpermanent whose column set contains c
  vanishes (expand along column c: the two terms cancel), so M_x is supported on row c and column c: rank <= 2.
  Codimension 2 + 5 = 7 at m = 6 (in general (m-4) + (m-1) = 2m-5), all rows nonzero, no zero column.
  Exact check on a random rational point at m = 6 and at m = 8: rank 2. Numerically the tangent codimension of D_2
  at such points is 7, so this is (locally) a component of D_2.

For subspaces whose fixed vectors have no zero entry the certificate succeeds (my seed 3, the author's seeds 0, 1,
and my direct method: rank 1512 of 1512). Since L2 needs only one product, the claim "D_2 misses (6,2,1,1)" is
correct. This is the m = 6 form of the remark the note makes at m = 4, but the mechanism is not a zero column.

Two more families, found by expanding M_x along a block of zeros (paper; exact spot checks in `loci.py`):

* **(a)** *three rows vanish on two columns c, d* (codimension 6 at m = 6; in general m-3 rows, codimension 2(m-3)).
  With w the remaining row, pi_a = perm(x[A, O minus a]) on the other columns O, mu = perm(x on the columns O) and
  v = x_wd e_c + x_wc e_d: M_x = v pi^T + pi v^T + mu (E_cd + E_dc). Its column space is in span(e_c, e_d, pi), so
  **rank <= 3**, and rank exactly 3 at a random rational point. The note lists this locus with "rank <= 4"; the
  correct bound is 3, so it is a codimension-6 family inside D_3 with all rows nonzero and no zero column.
  Numerically the tangent codimension of D_3 at its points is only 3, so the scheme of 4-minors is singular or
  non-reduced along it; it is not the "rank 3, tangent codimension 6" component of the note's table. I did not
  determine whether (a) is a component.
* **(a')** *(a) together with mu = 0* (codimension 7 at m = 6, in general 2m-5): rank <= 2 (the rank is <= 2 exactly
  when mu x_wc x_wd = 0), all rows nonzero, no zero column; exact check: rank 2; tangent codimension 7 (numerical).

For m = 4 the families (a') (with A the single row u) and (b) are the ten lines of `FourByFourLower.lean`:
u = e_a - e_b is (a'), u = 1 - 2 e_a is (b), for the all-ones row. So D_2 contains, for every m, the zero-column
loci (codimension m-2) and the two families (a'), (b) of codimension 2m-5 that generalise the ten lines. They
explain the note's "isolated finds of rank 2 without zero column, tangent codimension 7".

None of this touches the theorems. For generic subspaces at m = 6, a product meets (a) or (a') only if three of the
e_b are >= 2, and it meets (b) only if e_b >= 1 on the two vanishing rows and e_b + e_b' >= 5 on the other two, so at
least three entries of e are nonzero; the count vectors used in the proofs have at most two nonzero entries (at
m = 8 the families need at least five nonzero entries). It does bear on the "generic model" of Section 7 of the
note: special components with all rows nonzero exist; they are invisible to two-row count vectors, as the
zero-column loci are.

Also confirmed exactly: two rows proportional to the same coordinate vector give M_x = 0 (codimension 10 at m = 6).

## 5. Section 4 of the note (r = 8 at 6 x 6) and an addition

Own enumeration of the 24310 multisets of 8 pairings: 165 with all s_ij in {4,..,8}, 235 with 0 also allowed. The
example 012, 012, 013, 013, 024, 024, 034, 034 has twelve values 4 and three values 8. Correct. The certificates
quoted for s = 3, 2, 1 at r = 8 are the ones recomputed above (D_3 misses (6,1,1,1) and (5,2,1,1); D_2 misses
(6,2,1,1); D_0 misses (6,3,1,1)).

**Addition (exact; both of my methods).** The note leaves s = 0 at r = 8 open ("no certificate tried"). Every
multiset of 8 omitted rows has a count vector of type (5,3,0,0) (own enumeration of the C(11,3) = 165 patterns; the
equality with the number 165 of surviving multisets of pairings is a coincidence), and
D_0 misses a product of dimensions (6,4,1,1): rank 210 = N at multidegree (2,2,1,1), by the evaluation form
(p = 65519) and by the direct Macaulay matrix (p = 32749, 360 x 210). Also D_0 misses (5,5,1,1): rank 225 = N, both
methods. So at r = 8 a pair with s = 0 is impossible as well, and the configurations that survive the method are
exactly the 165 multisets with all s_ij >= 4. The conclusion of the note ("the present tools do not decide r = 8")
is unchanged: a pair with s = 4 has kappa = 4, D_4 is only certified to have codimension >= 3 (and numerically has
codimension 3), so neither L1 nor a dimension count for L2 excludes it, and I have no certificate either.

## 6. Sections 5, 6.3, 7, 8 of the note

* **Section 5 (4 x 4).** Certificates recomputed by the direct method (p = 32749): D_2 misses (3,1) (10 x 10, rank
  10); D_0 misses (4,1), (4,2), (3,3) (ranks 4, 30, 36). The case s = 3 needs the repair of Section 1.4. With it, the
  argument is complete and agrees with the Lean theorem (not a limit of sums of 4).
* **Section 6.2, remark on r = 9.** The text says D_5 must miss the two-row types of size 4, but the two runs it
  reports are for the types (4,1) and (3,2) of size 5 (those belong to r = 10). The types of size 4 do certify with
  my code (exact, p = 65519): D_5 misses (4,2,1,1,1,1), rank 1485 = N, and (3,3,1,1,1,1), rank 2025 = N, both at
  multidegree (8,8,6,..), and again at (9,9,6,..). For the type (4,1) I also get no certificate: rank 4210 of 4455 at
  (8,8,6,..) and 7060 of 7150 at (9,9,6,..) (random subset of rows; undecided). The other certificates r = 9 would
  need (D_4 with types of size 5, D_3 of size 6, D_2 of size 7) were not attempted; some have more than 10^4
  monomials.
* **Section 6.3 (Loewner form).** Verified exactly at m = 6 on a random sum matrix with rational entries:
  M_x[c,d] = (psi(t_c) - psi(t_d))/(t_d - t_c) for all c < d, deg psi = 5, leading coefficient -24 = -(n!).
* **Section 7 (generic model).** `pairs.py comb 3 / 4 / 5` rerun; the three example multisets were checked with my
  own code (minimal s = 4, 5, 7; the k = 4 example has twelve 5s, twelve 6s and four 11s). Infeasibility below them:
  k = 4, r = 10 needs all s >= 6 but the average is 40/7; k = 5, r = 13 needs all s >= 7 with row sums 65 over nine
  values, so every row has at least seven values equal to 7; three rows with pairwise value 7 would have odd sum,
  against (2); so the graph of 7s is triangle-free with minimum degree 7 on 10 vertices, impossible (Mantel). The
  heuristic r about 4k - 4 sqrt(k) follows from the same count. The model remains a conjecture; see the end of
  Section 4 for what the special families do and do not change.
* **Section 8.** (a) is right: for r = 6 the plain codimension count leaves s = 5, 2, 0. (b) and (c) are right.
  Item 6 (rational points on a random line at m = 4) is consistent with my m = 4 patterns.

## 7. Numerical attempts to refute the theorems

`checks/splitfast.py` (exact-decomposition search with fixed row sets, Levenberg-Marquardt), two restarts per
configuration, up to 300 iterations. Every 7-term multiset has a pair with s <= 3; I took the configurations closest
to passing (minimum s = 3 attained by 2, 3, 4 or 6 pairs), and for 6 terms those with the largest minimum.

Calibration at 4 x 4 (same solver, three restarts): 6 terms 01x2;02x2;03x2 reaches 6.8e-28 (the others 2e-7 and
3e-7 with unknowns of size 10); 5 terms 01x3;02;03 (only a limit exists) reaches 1.5e-7 with unknowns of size 9 in
one restart and stalls at 0.098 in two; 4 terms stall at 0.15 to 0.33.

| terms | row sets | least s_ij (number of such pairs) | best relative squared residual | rms of unknowns |
|---|---|---|---|---|
| 7 | 012;013;014;015;023;024;025 | 3 (2) | 0.611 | 0.18 |
| 7 | 012;013;014;015;023;024;034 | 3 (2) | 0.611 | 0.18 |
| 7 | 012;013;024;035;045;025;034 | 3 (2) | 0.585 | 0.18 |
| 7 | 012;013;014;015;023;024;035 | 3 (3) | 0.585 | 0.18 |
| 7 | 012;013;014;015;023;025;034 | 3 (3) | 0.585 | 0.18 |
| 7 | 012;012;013;014;023;024;034 | 3 (4) | 0.608 | 0.18 |
| 7 | 012;012;013;014;025;035;045 | 3 (4) | 0.607 | 0.18 |
| 7 | 012;012;013;013;024;024;034 | 3 (6) | 0.644 | 0.18 |
| 7 | 012;012;013;014;015;023;045 | 2 (2) | 0.610 | 0.18 |
| 6 | 012;013;014;023;024;034 | 3 (8) | 0.655 | 0.18 |
| 6 | 012;013;014;015;023;024 | 2 (1) | 0.663 | 0.18 |
| 8 (not excluded by the note) | 012x2;013x2;024x2;034x2 | 4 (12) | 0.599 | 0.22 |
| 8 (not excluded by the note) | 012x2;015x2;024x2;045x2 | 4 (12) | 0.599 | 0.22 |

(Row sets are written with the side containing row 0; two of the runs were entered with the complementary sets
134, 125 and 345, which is the same model.) All runs stall after 70 to 110 iterations with bounded unknowns and a
residual barely below what seven Laplace terms of one pairing leave (13/20 = 0.65). No decomposition and no sign of a
limit decomposition. This is **numerical evidence only**, and weak: the brief records that at 6 x 6 the available
searches recover a known 15-term limit decomposition from about one random start in eight. It is consistent with
Theorem 6 and says nothing about r = 8.

## 8. Small corrections for the note

1. Section 1.2, L3, and Section 5: add the weight argument of Section 1.4 (needed for k = 2).
2. Section 2.2: "rows 1, 2, 3 zero in two columns (codimension 6, rank <= 4)" should be rank <= 3; add the families
   (a'), (b) and their relation to the ten lines.
3. Section 2.1 / Section 5: a certificate can fail at m = 6 because a fixed vector has a zero entry even though no
   zero column is possible (family (b)); draw the subspaces without zero entries.
4. Section 4: s = 0 at r = 8 is excluded by D_0 missing (6,4,1,1); the count is 165, not "165, or 235 if s = 0".
5. Section 6.2: the runs reported for r = 9 are for types of size 5; the types of size 4 certify.
6. Summary, item 1: the sentence about the common zero set holds in the exact case only.

## 9. What I did not check

* The literature section (no search).
* The numerical component table of Section 2.2 beyond the families above (no classification attempted), the
  Hilbert-function remarks, and the (2,1,1,0) transient.
* The upper bounds quoted (15 at 6 x 6 is in Lean; 53 at 8 x 8 and 176 at 10 x 10 are the brief's paper-level counts).
* Nothing was formalised. The exact checks are computer checks modulo primes with code written for this report;
  the self-tests of `refcert.py` compare Ryser's formula, the identity perm = r_i^T M_x r_j, the minors and both rank
  routines with brute force.

## Appendix: the referee's code

The scripts were run in a scratch directory and are reproduced here so that the checks can be repeated. Save the
three blocks as `refcert.py`, `direct.py`, `irr.py` in one directory. Commands and expected output:

    python3 refcert.py selftest          # selftest passed (Ryser, M_x identity, minors, ranks) with prime 65519
    python3 direct.py m6 32749           # seven lines, each CERTIFIED; then ALL CERTIFIED          (6 s)
    python3 direct.py m6big 32749        # D_3 misses (5,2,1,1): Macaulay matrix 5496x4455, rank 4455 (35 s)
    python3 direct.py m4 32749           # four lines CERTIFIED
    python3 irr.py 4 ; python3 irr.py 6 ; python3 irr.py 8      # the table of Section 3.2

The 8 x 8 certificates of Section 3.2 are the calls

    rc.certificate(8, s, e + [0,0,0,0], D + [s+1]*4, seed, 65519, subspaces=subs, use_all=(N < 700))

for (s, e, D) in the list (6,(2,0),(8,7)), (6,(1,1),(8,8)), (5,(5,0),(11,6)), (5,(2,1),(8,8)), (4,(3,1),(7,7)),
(4,(2,2),(8,8)), (3,(4,1),(7,7)), (3,(3,2),(7,7)), (2,(6,0),(4,3)), (2,(5,1),(5,5)), (2,(4,2),(5,5)),
(2,(3,3),(5,5)), (0,(7,0),(1,1)), (0,(6,1),(2,2)), (0,(5,2),(2,2)), (0,(4,3),(2,2)), with `subs` random integer
bases with entries in -12..12 without zeros (about 80 s in total). The 6 x 6 lines of Section 2.2 are
`rc.certificate(6, s, e, D, 1, 65519)` with the (s, D) of the table and e = dimensions minus one.

Other scripts, not reproduced (each is a few lines on top of the code below): `penum.py` (multisets of pairings, the
identities (1), (2), brute-force count vectors of all patterns), `cone.py` (the cone certificates: x ranges over
the span of c random integer matrices, same Macaulay rank test in one group of c variables), `consist.py` (coranks of
the direct Macaulay matrices at m = 4), `loci.py` (ranks of M_x at random rational points of the families (a), (a'),
(b), and the Loewner identity, with sympy), `tangent.py` (rank of the conditions u^T dM u' = 0 on the kernel of M_x,
floating point), `look3.py` (minimisation of |M_x - A A^T|^2 over a product of subspaces), and the runs of
`checks/splitfast.py` of Section 7.

### refcert.py

```python
"""Referee's independent implementation of the evaluation-form Macaulay certificates (no code shared with pairs.py).
  - M_x via Ryser's formula for each (m-2) x (m-2) subpermanent (pairs.py uses a subset DP)
  - minors by Laplace expansion along the last row with tuples of columns
  - rank mod p by my own blocked Schur-complement elimination (float64 matmul, all values < 2^53)
Soundness: every row of E is the vector of values, at the sample points, of (monomial) * (minor of M_x), a
multihomogeneous polynomial of multidegree D with integer coefficients.  So rank_p(E) <= rank_Q(Macaulay) <= N.
rank_p(E) = N  =>  every monomial of multidegree D is in the ideal of the minors  =>  no common zero with all groups nonzero.
"""
import itertools, math, sys, time
import numpy as np

def ryser_perm(A, p):
    """A: (B, n, n) int64 mod p -> permanent mod p, shape (B,)"""
    B, n, _ = A.shape
    tot = np.zeros(B, dtype=np.int64)
    for mask in range(1, 1 << n):
        cols = [j for j in range(n) if mask >> j & 1]
        rs = A[:, :, cols].sum(axis=2) % p          # (B, n)
        pr = np.ones(B, dtype=np.int64)
        for i in range(n):
            pr = pr * rs[:, i] % p
        if (n - len(cols)) % 2:
            tot = (tot - pr) % p
        else:
            tot = (tot + pr) % p
    return tot

def Mx(x, p):
    """x: (B, n, m), n = m-2.  M[c,d] = perm(x without columns c,d)."""
    B, n, m = x.shape
    M = np.zeros((B, m, m), dtype=np.int64)
    for c in range(m):
        for d in range(c + 1, m):
            keep = [l for l in range(m) if l != c and l != d]
            v = ryser_perm(x[:, :, keep], p)
            M[:, c, d] = v; M[:, d, c] = v
    return M

def minors(M, q, p):
    """all q x q minors with row set I <= column set J (lexicographic); returns array (ngen, B) and labels"""
    B, m, _ = M.shape
    out, labels = [], []
    for I in itertools.combinations(range(m), q):
        cur = {(): np.ones(B, dtype=np.int64)}
        for t, i in enumerate(I):                      # after step t: minors of rows I[:t+1] on all (t+1)-subsets of columns
            nxt = {}
            for J in itertools.combinations(range(m), t + 1):
                acc = np.zeros(B, dtype=np.int64)
                for pos, j in enumerate(J):            # expand along the last row (row index t), column position pos
                    Jm = J[:pos] + J[pos + 1:]
                    term = M[:, i, j] * cur[Jm] % p
                    if (t + pos) % 2:
                        acc = (acc - term) % p
                    else:
                        acc = (acc + term) % p
                nxt[J] = acc
            cur = nxt
        for J in itertools.combinations(range(m), q):
            if J >= I:
                out.append(cur[J]); labels.append((I, J))
    return np.array(out), labels

def monos(nv, d):
    if nv == 1:
        return [(d,)]
    return [(a,) + r for a in range(d + 1) for r in monos(nv - 1, d - a)]

def eval_monos(mons, pts, p):
    """mons: list of exponent tuples; pts (npts, nv) -> (nmons, npts)"""
    out = np.ones((len(mons), pts.shape[0]), dtype=np.int64)
    nv = pts.shape[1]
    dmax = max(max(mn) for mn in mons) if mons else 0
    pw = [np.ones_like(pts)]
    for e in range(dmax):
        pw.append(pw[-1] * pts % p)
    for k, mn in enumerate(mons):
        v = np.ones(pts.shape[0], dtype=np.int64)
        for j in range(nv):
            if mn[j]:
                v = v * pw[mn[j]][:, j] % p
        out[k] = v
    return out

# ---------------------------------------------------------------- exact rank mod p
def rank_naive(A, p):
    A = np.array(A, dtype=np.int64) % p
    R, C = A.shape; r = 0
    for c in range(C):
        if r == R: break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0: continue
        q = r + int(nz[0])
        if q != r: A[[r, q]] = A[[q, r]]
        A[r] = A[r] * pow(int(A[r, c]), p - 2, p) % p
        rows = r + 1 + np.nonzero(A[r + 1:, c])[0]
        if rows.size:
            A[rows] = (A[rows] - np.outer(A[rows, c], A[r])) % p
        r += 1
    return r

def inv_mod(W, p):
    k = W.shape[0]
    A = np.concatenate([np.array(W, dtype=np.int64) % p, np.eye(k, dtype=np.int64)], axis=1)
    for c in range(k):
        nz = np.nonzero(A[c:, c])[0]
        assert nz.size, 'singular'
        q = c + int(nz[0])
        if q != c: A[[c, q]] = A[[q, c]]
        A[c] = A[c] * pow(int(A[c, c]), p - 2, p) % p
        rows = np.array([i for i in range(k) if i != c and A[i, c]], dtype=np.int64)
        if rows.size:
            A[rows] = (A[rows] - np.outer(A[rows, c], A[c])) % p
    return A[:, k:]

def rank_blocked(E, p, bs=96):
    """rank mod p.  Block step: find pivot rows/columns of the panel by naive elimination on a copy; with W = panel[pivrows, pivcols]
    (invertible), subtract  panel[i, pivcols] W^-1 A[pivrows, trailing]  from every other active row (their panel part becomes 0)."""
    A = np.array(E, dtype=np.float64) % p
    R, C = A.shape
    active = np.arange(R)
    rank = 0
    for c0 in range(0, C, bs):
        if active.size == 0: break
        c1 = min(C, c0 + bs)
        P0 = np.rint(A[active, c0:c1]).astype(np.int64) % p
        Pc = P0.copy()
        used = np.zeros(active.size, dtype=bool)
        prow, pcol = [], []
        for j in range(c1 - c0):
            cand = np.nonzero((Pc[:, j] != 0) & ~used)[0]
            if cand.size == 0: continue
            q = int(cand[0])
            Pc[q] = Pc[q] * pow(int(Pc[q, j]), p - 2, p) % p
            others = cand[1:]
            if others.size:
                Pc[others] = (Pc[others] - np.outer(Pc[others, j], Pc[q])) % p
            used[q] = True; prow.append(q); pcol.append(j)
        k = len(prow)
        if k == 0: continue
        rank += k
        rest = np.nonzero(~used)[0]
        if c1 < C and rest.size:
            Winv = inv_mod(P0[np.ix_(prow, pcol)], p)
            Y = np.rint(Winv.astype(np.float64) @ A[active[prow], c1:]) % p          # k x trailing, sums < k p^2
            L = P0[np.ix_(rest, pcol)].astype(np.float64)
            A[np.ix_(active[rest], np.arange(c1, C))] = (A[active[rest], c1:] - L @ Y) % p
        active = active[rest]
    return rank

def certificate(m, s, e, D, seed, p, rng_lo=-12, rng_hi=12, extra_pts=40, over=1.15, extra_rows=120, verbose=True, subspaces=None, use_all=False):
    """rows of x: row a ranges over a random integer subspace of dimension e[a]+1.  D: tested multidegree (len n).
    Returns (certified, rank, N)."""
    n = m - 2; q = s + 1
    assert len(e) == n and len(D) == n and all(D[a] >= q for a in range(n))
    rng = np.random.default_rng(1000003 * seed + 17)
    if subspaces is None:
        subspaces = [rng.integers(rng_lo, rng_hi + 1, size=(e[a] + 1, m)) for a in range(n)]
    N = 1
    for a in range(n):
        N *= math.comb(D[a] + e[a], e[a])
    npts = N + extra_pts
    coords = [rng.integers(0, p, size=(npts, e[a] + 1)) for a in range(n)]
    x = np.stack([coords[a] @ (subspaces[a] % p) % p for a in range(n)], axis=1)
    M = Mx(x, p)
    G, labels = minors(M, q, p)
    mult = np.ones((1, npts), dtype=np.int64)
    for a in range(n):
        va = eval_monos(monos(e[a] + 1, D[a] - q), coords[a], p)
        mult = (mult[:, None, :] * va[None, :, :] % p).reshape(-1, npts)
    total = G.shape[0] * mult.shape[0]
    want = total if use_all else min(total, int(over * N) + extra_rows)
    sel = rng.choice(total, size=want, replace=False) if want < total else np.arange(total)
    E = mult[sel // G.shape[0]] * G[sel % G.shape[0]] % p
    t0 = time.time()
    r = rank_blocked(E, p)
    if verbose:
        print(f"  m={m} D_{s} dims {[v+1 for v in e]} multidegree {tuple(D)} seed {seed} prime {p}: {G.shape[0]} minors, "
              f"E {E.shape[0]}x{E.shape[1]}, rank {r} of N={N}  -> {'CERTIFIED' if r == N else 'no certificate'}  ({time.time()-t0:.1f}s)", flush=True)
    return r == N, r, N, subspaces

# ---------------------------------------------------------------- self tests
def selftest(p=65519):
    import sympy
    assert sympy.isprime(p)
    rng = np.random.default_rng(5)
    # Ryser vs brute force, exact integers
    for n in (2, 3, 4, 5):
        A = rng.integers(-9, 10, size=(3, n, n))
        for b in range(3):
            bf = sum(math.prod(int(A[b, i, s_[i]]) for i in range(n)) for s_ in itertools.permutations(range(n)))
            assert ryser_perm(A[b:b+1] % p, p)[0] == bf % p
    # M_x: perm(x, ri, rj) = ri^T M rj, checked with exact integers by brute force
    for m in (4, 6):
        x = rng.integers(-5, 6, size=(1, m - 2, m)); ri = rng.integers(-5, 6, size=m); rj = rng.integers(-5, 6, size=m)
        full = np.concatenate([x[0], ri[None], rj[None]]).tolist()
        bf = sum(math.prod(full[i][s_[i]] for i in range(m)) for s_ in itertools.permutations(range(m)))
        Mm = Mx(x % p, p)[0]
        val = int(sum(int(ri[c]) * int(Mm[c, d]) * int(rj[d]) for c in range(m) for d in range(m)) % p)
        assert val == bf % p, (m, val, bf % p)
    # minors vs sympy determinants
    Mi = rng.integers(-6, 7, size=(2, 6, 6))
    for q in (1, 2, 3, 4, 5, 6):
        G, lab = minors(Mi % p, q, p)
        for idx in rng.choice(len(lab), size=min(12, len(lab)), replace=False):
            I, J = lab[idx]
            for b in range(2):
                d = int(sympy.Matrix(Mi[b][np.ix_(I, J)].tolist()).det())
                assert G[idx, b] == d % p
    # rank routines on matrices of known rank
    for (R, C, rk) in [(300, 250, 250), (300, 250, 180), (700, 640, 600), (500, 520, 333)]:
        A = rng.integers(0, p, size=(R, rk)); Bm = rng.integers(0, p, size=(rk, C))
        E = np.zeros((R, C), dtype=np.int64)
        for i0 in range(0, rk, 50):
            E = (E + A[:, i0:i0+50] @ Bm[i0:i0+50]) % p
        r1 = rank_naive(E, p); r2 = rank_blocked(E, p)
        assert r1 == r2 == min(rk, R, C), (R, C, rk, r1, r2)
    print("selftest passed (Ryser, M_x identity, minors, ranks) with prime", p)

if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest()
```

### direct.py

```python
"""Second, different method: DIRECT Macaulay matrices.  The minors of M_x restricted to the product of subspaces are expanded
as polynomials with exact integer coefficients (Python ints, dict exponent -> coefficient); the Macaulay matrix in the tested
multidegree is written down explicitly (coefficients reduced mod p) and its rank computed mod p.
rank_p = number of monomials  =>  rank over Q is full  =>  no common zero with all coordinate groups nonzero."""
import itertools, math, sys, time
import numpy as np
from refcert import rank_blocked, monos

def padd(a, b, sign=1):
    out = dict(a)
    for k, v in b.items():
        w = out.get(k, 0) + sign * v
        if w: out[k] = w
        else: out.pop(k, None)
    return out

def pmul(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(x + y for x, y in zip(ka, kb))
            out[k] = out.get(k, 0) + va * vb
    return {k: v for k, v in out.items() if v}

def perm_int(A):
    n = len(A)
    return sum(math.prod(A[i][s[i]] for i in range(n)) for s in itertools.permutations(range(n)))

def M_poly(m, subspaces):
    """entries of M_x as polynomials in the coordinates of the rows w.r.t. the given integer bases (multilinear in the groups).
    Variables: group a has len(subspaces[a]) coordinates; exponent tuples are over the concatenation of all groups."""
    n = m - 2
    dims = [len(S) for S in subspaces]
    off = np.concatenate([[0], np.cumsum(dims)]); nv = int(off[-1])
    M = [[{} for _ in range(m)] for _ in range(m)]
    for choice in itertools.product(*[range(d) for d in dims]):        # one basis vector per row
        x = [subspaces[a][choice[a]] for a in range(n)]
        ex = [0] * nv
        for a in range(n): ex[off[a] + choice[a]] += 1
        ex = tuple(ex)
        for c in range(m):
            for d in range(c + 1, m):
                keep = [l for l in range(m) if l != c and l != d]
                v = perm_int([[x[i][l] for l in keep] for i in range(n)])
                if v:
                    M[c][d][ex] = v; M[d][c][ex] = v
    return M, dims, off

def all_minors(M, q):
    """dict (I, J) -> polynomial, for all q-subsets I <= J, by Laplace expansion along the first row with memoisation"""
    m = len(M)
    memo = {}
    def minor(I, J):
        key = (I, J)
        if key in memo: return memo[key]
        if len(I) == 1:
            r = M[I[0]][J[0]]
        else:
            r = {}
            for pos, j in enumerate(J):
                e = M[I[0]][j]
                if not e: continue
                sub = minor(I[1:], J[:pos] + J[pos + 1:])
                if not sub: continue
                r = padd(r, pmul(e, sub), 1 if pos % 2 == 0 else -1)
        memo[key] = r
        return r
    out = {}
    for I in itertools.combinations(range(m), q):
        for J in itertools.combinations(range(m), q):
            if J >= I:
                out[(I, J)] = minor(I, J)
    return out

def direct_certificate(m, s, subspaces, D, p, seed=0, max_rows_factor=1.2, extra=150, verbose=True):
    n = m - 2; q = s + 1
    t0 = time.time()
    M, dims, off = M_poly(m, subspaces)
    gens = [g for g in all_minors(M, q).values() if g]
    # column index: monomials of multidegree D
    group_monos = [monos(dims[a], D[a]) for a in range(n)]
    cols = {}
    for combo in itertools.product(*group_monos):
        cols[tuple(itertools.chain(*combo))] = len(cols)
    N = len(cols)
    mult = [tuple(itertools.chain(*combo)) for combo in itertools.product(*[monos(dims[a], D[a] - q) for a in range(n)])]
    total = len(gens) * len(mult)
    rng = np.random.default_rng(seed)
    want = min(total, int(max_rows_factor * N) + extra)
    sel = rng.choice(total, size=want, replace=False) if want < total else np.arange(total)
    E = np.zeros((want, N), dtype=np.int64)
    for r, idx in enumerate(sel):
        g = gens[idx % len(gens)]; mu = mult[idx // len(gens)]
        for k, v in g.items():
            E[r, cols[tuple(a + b for a, b in zip(k, mu))]] = v % p
    t1 = time.time()
    rk = rank_blocked(E, p)
    if verbose:
        print(f"  DIRECT m={m} D_{s} dims {dims} multidegree {tuple(D)} prime {p}: {len(gens)} nonzero minors (max {max(len(g) for g in gens)} terms), "
              f"Macaulay matrix {E.shape[0]}x{N}, rank {rk} -> {'CERTIFIED' if rk == N else 'no certificate'}  (build {t1-t0:.0f}s, rank {time.time()-t1:.0f}s)", flush=True)
    return rk == N

def nz_subspaces(m, e, seed, lo=-10, hi=10):
    rng = np.random.default_rng(seed)
    vals = [v for v in range(lo, hi + 1) if v != 0]
    return [[[int(v) for v in rng.choice(vals, size=m)] for _ in range(e[a] + 1)] for a in range(len(e))]

if __name__ == '__main__':
    p = int(sys.argv[2]) if len(sys.argv) > 2 else 32749
    import sympy; assert sympy.isprime(p)
    which = sys.argv[1]
    ok = True
    if which == 'm6':
        items = [(3, (4,0,0,0), (5,4,4,4)), (3, (3,1,0,0), (5,5,4,4)), (3, (5,0,0,0), (7,4,4,4)), (2, (4,1,0,0), (5,5,3,3)),
                 (0, (5,1,0,0), (2,2,1,1)), (0, (5,2,0,0), (2,2,1,1)), (2, (5,1,0,0), (5,5,3,3))]
        for i, (s, e, D) in enumerate(items):
            ok &= direct_certificate(6, s, nz_subspaces(6, e, 4242 + i), D, p, seed=i)
    if which == 'm6big':
        ok &= direct_certificate(6, 3, nz_subspaces(6, (4,1,0,0), 99), (8,8,4,4), p, seed=5)
    if which == 'm4':
        for i, (s, e, D) in enumerate([(2, (2,0), (3,3)), (0, (3,0), (1,1)), (0, (3,1), (2,2)), (0, (2,2), (2,2))]):
            ok &= direct_certificate(4, s, nz_subspaces(4, e, 31 + i), D, p, seed=i, max_rows_factor=50)
    print('ALL CERTIFIED' if ok else 'SOME NOT CERTIFIED')
```

### irr.py

```python
"""Independent proof that det M_x is irreducible over Q (m = 4, 6, 8), by reduction modulo primes.
F(t) = det M_{a + t b} in Z[t] for an integer line (a, b); deg F <= m(m-2).  F mod p is obtained by evaluating at
t = 0..deg and interpolating in F_p (exact, needs p > deg).  If deg (F mod p) = m(m-2), any factorisation F = G H over Q
(Gauss: over Z) reduces to a factorisation mod p with the same degrees, so deg G is a subset sum of the factor degrees mod p,
for every such p.  If the only common subset sums are 0 and m(m-2), F is irreducible over Q of full degree, hence so is det M_x
(a factorisation of det M_x restricts to one of F with the same degrees because F has full degree)."""
import random, sys, time
from sympy import ZZ, nextprime
from sympy.polys.galoistools import gf_factor, gf_ddf_zassenhaus, gf_sqf_p, gf_monic

def Mint(x, m, p):
    n = m - 2
    dp = {0: 1}
    for j in range(n):
        nd = {}
        for mask, v in dp.items():
            for l in range(m):
                if not mask >> l & 1:
                    k = mask | 1 << l
                    nd[k] = (nd.get(k, 0) + v * x[j][l]) % p
        dp = nd
    full = (1 << m) - 1
    M = [[0] * m for _ in range(m)]
    for c in range(m):
        for d in range(c + 1, m):
            M[c][d] = M[d][c] = dp[full ^ (1 << c) ^ (1 << d)]
    return M

def det_mod(M, p):
    M = [r[:] for r in M]; n = len(M); det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] % p), None)
        if piv is None: return 0
        if piv != c: M[c], M[piv] = M[piv], M[c]; det = -det
        det = det * M[c][c] % p
        inv = pow(M[c][c], p - 2, p)
        for r in range(c + 1, n):
            f = M[r][c] * inv % p
            if f:
                M[r] = [(u - f * v) % p for u, v in zip(M[r], M[c])]
    return det % p

def interpolate_mod(vals, p):
    """coefficients (low to high) of the polynomial of degree < len(vals) with P(i) = vals[i], i = 0..n-1, in F_p (Newton)"""
    n = len(vals)
    dd = list(vals)
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            dd[i] = (dd[i] - dd[i - 1]) * pow(j, p - 2, p) % p
    coeffs = [0] * n          # Horner on the Newton form
    for k in range(n - 1, -1, -1):
        # coeffs = coeffs * (t - k) + dd[k]
        new = [0] * n
        for i in range(n - 1):
            new[i + 1] = coeffs[i]
        for i in range(n):
            new[i] = (new[i] - k * coeffs[i]) % p
        new[0] = (new[0] + dd[k]) % p
        coeffs = new
    return coeffs

def pattern(a, b, m, p):
    deg = m * (m - 2)
    vals = []
    for tv in range(deg + 1):
        x = [[(a[i][j] + tv * b[i][j]) % p for j in range(m)] for i in range(m - 2)]
        vals.append(det_mod(Mint(x, m, p), p))
    co = interpolate_mod(vals, p)
    # check the interpolation at one more point
    tv = deg + 7
    x = [[(a[i][j] + tv * b[i][j]) % p for j in range(m)] for i in range(m - 2)]
    assert sum(c * pow(tv, i, p) for i, c in enumerate(co)) % p == det_mod(Mint(x, m, p), p)
    if co[deg] == 0:
        return None
    f = [ZZ(c) for c in reversed(co)]
    if not gf_sqf_p(gf_monic(f, p, ZZ)[1], p, ZZ):
        return None                                   # ramified prime: skip
    lc, facs = gf_factor(f, p, ZZ)
    degs = sorted(len(g) - 1 for g, e in facs for _ in range(e))
    ddf = sorted(d for g, d in gf_ddf_zassenhaus(gf_monic(f, p, ZZ)[1], p, ZZ) for _ in range((len(g) - 1) // d))
    assert degs == ddf, (degs, ddf)
    return degs

def subset_sums(degs):
    s = {0}
    for d in degs:
        s |= {u + d for u in s}
    return s

def blocks_ok(degs, nblocks, bsize=2):
    """can a permutation with cycle type degs preserve a system of nblocks blocks of size 2?  (cycle of length c on blocks gives
    two cycles of length c or one cycle of length 2c)"""
    from functools import lru_cache
    degs = tuple(sorted(degs))
    @lru_cache(None)
    def rec(rem):
        if not rem: return True
        d = rem[0]; rest = rem[1:]
        if d % 2 == 0 and rec(rest): return True       # one cycle of length 2c
        if d in rest:
            r = list(rest); r.remove(d)
            if rec(tuple(r)): return True
        return False
    return rec(degs)

if __name__ == '__main__':
    m = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 2026
    random.seed(seed)
    a = [[random.randint(-6, 6) for _ in range(m)] for _ in range(m - 2)]
    b = [[random.randint(-6, 6) for _ in range(m)] for _ in range(m - 2)]
    deg = m * (m - 2)
    common = set(range(deg + 1)); p = 1000; used = 0; t0 = time.time(); blockfree = False
    while used < 40 and (common != {0, deg} or (m == 4 and not blockfree)):
        p = nextprime(p)
        degs = pattern(a, b, m, p)
        if degs is None: continue
        used += 1
        common &= subset_sums(degs)
        if m == 4 and not blocks_ok(degs, 4): blockfree = True
        print(f"  p={p}: factor degrees {degs}; possible degrees of a rational factor so far: {sorted(common)}" + (f"; pattern incompatible with 4 blocks of size 2: {not blocks_ok(degs, 4)}" if m == 4 else ''), flush=True)
    print(f"m={m} seed={seed}: line a={a} b={b}")
    print(f"m={m}: det M_x restricted to the line has degree {deg} and is " + ("IRREDUCIBLE over Q" if common == {0, deg} else "NOT shown irreducible") + f"  ({used} primes, {time.time()-t0:.0f}s)")
    if m == 4:
        print("m=4: some prime has a cycle type that cannot preserve 4 blocks of size 2 (so no factor of bidegree (1,1) over C):", blockfree)
```
