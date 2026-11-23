# The extra terms of the two-block model for general k

Note of 2026-11-23. Code: `pequalnp/garbage_general.py` (all commands below are run in `pequalnp/`).
Levels of evidence: **paper** = complete argument written here, **exact** = exact integer or rational
computer check, **numerical** = floating point. Nothing in this note is formalised in Lean.

## 0. Summary

Notation: 2k rows, column blocks B1 = first k columns, B2 = last k; a pairing is {R, R^c}, |R| = k;
N = C(2k,k)/2; q1(R), q2(R) = permanent of the rows R on B1, on B2. In the two-block model the
2k x 2k permanent is a limit of N + E(k) k-split products, where E(k) is the least number of split
products that cancel Gamma(c) = sum_R c_R q1(R) q1(R^c) for some c with **all** c_R nonzero.
Known before this note: E(2) = 2, E(3) <= 5, E(k) <= T_k - 1 (T_k = central trinomial coefficient).

1. **Signs instead of ones (paper + exact).** Take c_R = (-1)^{|R ∩ Q|} for a set Q of rows of even
   size. Then Gamma(c) only involves the matchings with no pair between Q and Q^c (Theorem 1), and

       E(k) <= C(k, k/2)                      for k even   (2, 6, 20, 70 for k = 2, 4, 6, 8),
       E(k) <= (k+1)/2 * C(k, (k-1)/2)        for k odd    (6, 30, 140 for k = 3, 5, 7).

   This replaces T_k - 1 ~ 3^k by about 2^k. In particular **E(4) <= 6** (before: 18).
2. **Consequences for the permanent (paper + exact for k <= 4).** Because c_R = 1/c_R, the same signs
   give an exact decomposition: perm_2k is an exact sum of N + 2E split products and a limit of N + E.

   | k | N | Laplace 2N | squares, limit N+T_k-1 | signs, limit N+E | signs, exact N+2E |
   |---|---|---|---|---|---|
   | 2 | 3 | 6 | 5 | 5 | 7 |
   | 3 | 10 | 20 | 16 (15 by search) | 16 | 22 |
   | 4 | 35 | 70 | 53 | **41** | **47** |
   | 5 | 126 | 252 | 176 | 156 | 186 |
   | 6 | 462 | 924 | 602 | 482 | 502 |
   | 8 | 6435 | 12870 | 7541 | 6505 | 6575 |

   So perm_8 is an exact sum of 47 4-split products (Laplace: 70) and a limit of 41. Laplace expansion
   is therefore not optimal for exact decompositions already at k = 4. `garbage_general.py verify 4`
   checks this on the full 8^8 integer tensors.
3. **One pairing (paper + exact/numerical linear algebra).** If all extra terms sit on one pairing, then
   for k >= 3 at least min_{i>=1} k!/(i! i! (k-2i)!) of them are needed; with the computed forced zeros
   the optimum on one pairing is exactly 6, 6, 30, 20 for k = 3, 4, 5, 6. So item 1 is optimal among
   one-pairing solutions for k = 4, 5, 6. With several pairings nothing is proved (k = 3: 5 < 6).
4. **Matching sub-model (the model asked for in the task).** The formulation with functions h_R on
   S_k and cost "sum of dim * rank of the Fourier blocks" is correct: it gives 2 at k = 2 and 5 at
   k = 3 (Section 4). At k = 4 it is the wrong place to look: the solution of item 1 is not in it,
   every admissible set of costly pairings has at least 3 elements (exact), and a rank-surrogate search
   finds nothing below cost 45 with all constants nonzero, 39 if vanishing constants are allowed at
   cost 1 each (numerical; 20 restarts). No sub-model solution with cost < 18 was found.
5. **Not achieved.** No polynomial bound for E(k): the best is about 2^k, and N ~ 4^k / (2 sqrt(pi k))
   dominates in any case, so every count above is N (1 + o(1)); the gain is in the lower-order term.
   No lower bound for E(k) beyond E >= 2 when the extra terms may use several pairings. Whether
   E(4) < 6 is open (a small numerical search found nothing, Section 5).

## 1. Setting

Rows 0..2k-1, first-block entries x_{ij} (row i, column j in [k]). For a perfect matching m of the
rows let

    w_m = sum over bijections l : m -> [k] of prod_{{i,i'} in m} x_{i,l(e)} x_{i',l(e)}

(the two rows of each pair share a column, every column is used). The w_m have disjoint monomial
supports, so they are linearly independent. Expanding q1(R) q1(R^c) and grouping the monomials by
"which row of R shares a column with which row of R^c" gives q1(R) q1(R^c) = sum of w_m over the
matchings m *separated* by R (every pair has one row in R). Hence

    Gamma(c) = sum_m (A c)_m w_m ,      (A c)_m = sum_{R separates m} c_R .                    (1)

**Lemma 1 (paper).** A is injective (characteristic not 2), for every k.

*Proof.* Induction on k; k = 1 is clear. Let A c = 0, k >= 2. Fix rows r1 != r2 and define, on the
pairings {R', R'^c} of the other 2k-2 rows, c'(R') = c(R'+r1 | R'^c+r2) + c(R'+r2 | R'^c+r1). A pairing
separates m' ∪ {r1 r2} iff it is one of these two extensions of a pairing separating m', so
(A_k c)(m' ∪ {r1 r2}) = (A_{k-1} c')(m') and by induction c' = 0:

    c(R) = - c(R with x and z exchanged)   for all x in R, z not in R.                          (2)

Take x, y in R, z not in R. By (2): c(R) = -c(R-x+z); c(R-x+z) = -c(R-y+z) (exchange y and x);
c(R) = -c(R-y+z). So c(R) = -c(R). ∎

## 2. Walsh characters

For Q ⊂ rows with |Q| = 2q put chi_Q(R) = (-1)^{|R ∩ Q|}. Since |R ∩ Q| + |R^c ∩ Q| is even this
is a function on pairings, with values +-1.

**Theorem 1 (paper; exact check `char` for k <= 6).**

    (A chi_Q)_m = (-1)^q 2^{k-1}   if no pair of m joins Q to Q^c,       0 otherwise.

*Proof.* The k-sets separating m are obtained by choosing one row from each pair (2^k choices, every
pairing twice), and (-1)^{|R ∩ Q|} is the product over the pairs of -1 or +1 according to whether the
chosen row lies in Q. So twice the sum is the product over the pairs {i,i'} of
((-1)^{[i in Q]} + (-1)^{[i' in Q]}), which is 0 for a pair joining Q to Q^c, -2 for a pair inside Q
and +2 for a pair inside Q^c. If no pair joins Q to Q^c there are exactly q pairs inside Q. ∎

For a set S of rows and a set J of columns with |S| = 2|J| let M_J(S) be the sum of the monomials of
the rows S that use every column of J exactly twice (equivalently the sum of w_mu over the matchings
mu of S, with labels in J). A matching without pairs between Q and Q^c is a matching of Q together
with a matching of Q^c, and its k labels split as J for Q and J^c for Q^c. With (1):

**Corollary 2 (paper).** Gamma(chi_Q) = (-1)^q 2^{k-1} sum_{J ⊂ [k], |J| = q} M_J(Q) M_{J^c}(Q^c).

* **k even, Q = R0** (a k-set): these are C(k, k/2) k-split products on the pairing R0, and every
  c_R = (-1)^{|R ∩ R0|} is +-1. So E(k) <= C(k, k/2).
* **k odd, |Q| = k-1**, r a row outside Q, R0 = Q + r: expand along row r,
  M_{J^c}(Q^c) = sum_{j in J^c} x_{rj} L_{J^c,j}(Q^c - r), where L_{J',j}(S) is the sum of the monomials
  of the rows S that use column j once and the other columns of J' twice. This gives the k-split
  products (M_J(Q) x_{rj}) * L_{J^c,j}(Q^c - r) on the pairing R0, C(k,(k-1)/2) (k+1)/2 of them.
* For any even Q the corollary writes Gamma(chi_Q) with C(k,q) products of shape (2q | 2k-2q); for
  |Q| = 2 these are k products. (Not used here: the squares are k-splits.)

For k = 2 this is a five-term limit decomposition with c = (1,-1,-1) and two extra products on
01|23: the same pattern (3,1,1) as `FiveTerm.lean`, but not the same identity (there 01|23 carries two
Laplace terms and det * det). For k = 3 it gives 6, the same as the square construction; the search
result 5 is better.

**Corollary 3 (paper; exact tensor check `verify` for k = 2, 3, 4).** Let c = chi_Q as above,
Gamma_1, Gamma_2 the expressions of Corollary 2 in the first and second column block. Since c_R^2 = 1,

    (c_R q1(R) + lam q2(R)) (q1(R^c) + lam c_R q2(R^c))
        = c_R q1(R) q1(R^c) + lam (q1(R) q2(R^c) + q2(R) q1(R^c)) + lam^2 c_R q2(R) q2(R^c),

and summing over the pairings (Laplace expansion by column blocks for the middle term):

    lam * perm = sum_R (c_R q1 + lam q2)(R) (q1 + lam c_R q2)(R^c)  -  Gamma_1(c)  -  lam^2 Gamma_2(c).

* lam = 1: perm_2k is an **exact** sum of N + 2E split products.
* lam -> 0 after dividing by lam: perm_2k + lam Gamma_2(c) is a sum of N + E split products for
  every lam != 0, so perm_2k is a **limit** of N + E split products (in the sense of
  `BorderMixedSplitLE` of `SplitRank.lean`, with g = Gamma_2(c)).

Output of `python3 garbage_general.py verify 4` (int32 tensors with 8^8 entries):

    k = 4: N = 35, c_R = (-1)^|R cap [0, 1, 2, 3]| (all +-1: [-1, 1]), E = 6 extra products on 0123, scalar -8
       lam^0  sum_R c_R q1(R) q1(R^c) + extras = 0                  : True
       lam^1  sum_R q1 q2 + q2 q1 = perm_8 (40320 = 8! entries)   : True
       lam^2  sum_R c_R q2(R) q2(R^c) + extras(second block) = 0    : True
       exact  perm_8 = sum of N + 2E = 47 split products            : True     (Laplace: 70)
       limit  perm_8 is a limit of N + E = 41 split products  (lam^0 and lam^1)
    ALL EXACT CHECKS PASSED

Explicitly for k = 4, with R0 = {0,1,2,3} and e2_S(j) = sum_{i<i' in S} x_{ij} x_{i'j}:

    sum_R (-1)^{|R ∩ R0|} q1(R) q1(R^c)  =  8 * sum_{J = {j1,j2} ⊂ [4]}  M_J(R0) M_{J^c}(R0^c),
    M_{{j1,j2}}(S) = multilinear part of e2_S(j1) e2_S(j2)   (6 monomials: 3 matchings of S, 2 labellings).

**Remark (why signs).** For c depending only on r = |R ∩ R0| (c(r) = c(k-r)), (A c)_m depends only on
the *type* i of m = number of pairs of m inside R0: gamma_i = 2^{2i-1} sum_j C(k-2i, j) c(i+j). This
system is triangular, gamma_{k/2} = 2^{k-1} c(k/2) for k even. The square construction c = (1-2^{k-1},
1, .., 1) keeps all types i >= 1 (that is the T_k - 1). The signs c(r) = (-1)^r are, up to scaling,
the only such c for which all types except the top one i = k/2 vanish, and no symmetric c with
c(k/2) != 0 can avoid the top type.

## 3. All extra terms on one pairing

Let R0 be a pairing and call *type* of a matching the number i of its pairs inside R0 (then i pairs
lie inside R0^c and k - 2i join R0 to R0^c); type 0 = separated by R0. Suppose

    sum_R c_R q1(R) q1(R^c) + sum_{e=1}^E F_e(R0) G_e(R0^c) = 0,     F_e, G_e arbitrary.

**Proposition 4 (paper).** Let k >= 3 and c_R != 0 for some R != R0. Then
E >= min over 1 <= i <= k/2 of k!/(i! i! (k-2i)!). More precisely E is at least the sum of these
multinomial coefficients over the types i >= 1 on which A c does not vanish identically.

*Proof.* Flatten along R0 | R0^c: the matrix of Gamma(c) has rank <= E. Index its rows by the index
tuples of the rows R0 and group them by weight w (column multiplicities), likewise the columns by w';
by (1) an entry is nonzero only if w + w' = (2,..,2), so the matrix is block diagonal and its rank is
the sum of the ranks of the blocks. A weight with i twos, i zeros and k-2i ones only meets matchings
of type i, every matching of type i occurs in each of the k!/(i! i! (k-2i)!) such blocks, and the
entries are the values (A c)_m. So each of these blocks is nonzero as soon as A c is nonzero on some
matching of type i. It remains to see that A c cannot vanish on all types i >= 1. If it does, then for
r1, r2 in R0 the function c' of the proof of Lemma 1 satisfies A_{k-1} c' = 0, hence (2) holds for all
x in R ∩ R0, z in R0 - R. For R != R0, R0^c and k >= 3 there are three rows of R0, two on one side of
R (say x, y in R) and z on the other; the three exchanges of the proof of Lemma 1 stay inside R0 and
give c(R) = 0. ∎

Computed (`single`; exact rational arithmetic for k <= 4, floating-point ranks of 0/1 matrices for
k = 5, 6): if A c vanishes on all types >= 2 then c vanishes on every pairing with
2 <= |R ∩ R0| <= k-2 for k = 5, 6 (not for k = 4). Therefore, on one pairing and with all c_R != 0:

| k | cost of a block of type 1, 2, 3 | types that must occur | optimum on one pairing |
|---|---|---|---|
| 3 | 6 | 1 | 6 |
| 4 | 12, 6 | 1 or 2 | 6 (attained by the signs) |
| 5 | 20, 30 | 2 | 30 (attained) |
| 6 | 30, 90, 20 | 2 or 3 | 20 (attained) |

For large k a block of type 1 (cost k(k-1)) or 2 would be cheaper than the top type, but for k = 5, 6
the low types alone force zeros in c; whether this persists for all k is not proved.
With several pairings the bound does not apply: k = 3 has a 5-term solution on three pairings.

## 4. The matching sub-model

**Formulation.** On every pairing R the sum of the extra terms is required to be a combination of
the w_m, m separated by R. Identify R and R^c with [k] in increasing order, so that these matchings
are the bijections b in S_k. With the square on R the pairing contributes sum_b h_R(b) w_b, where
h_R = c_R + g_R, c_R != 0 the constant of the square and g_R the extra terms. The unknowns are the
functions h_R on S_k, the constraint is

    for every perfect matching m:   sum over the pairings R separating m of h_R(m) = 0,

and the cost is

    cost = sum_R [ sum_{rho != trivial} dim(rho) rank(h_R^(rho)) + (1 if the mean of h_R is 0) ].

**Proposition 5 (paper).** The least number of products F(R) G(R^c), F and G arbitrary, with sum
sum_b g(b) w_b is the rank of the k! x k! matrix K[sigma, tau] = g(tau^-1 sigma), which equals
sum_rho dim(rho) rank(g^(rho)); minimising over c_R != 0 gives the cost above.

*Proof.* sum_b g(b) w_b = sum_{sigma, tau} g(tau^-1 sigma) (monomial sigma of R) (monomial tau of R^c),
since the monomials sigma, tau share columns along the bijection tau^-1 sigma. The least number of
products is the rank of this flattening, i.e. of K. K is the matrix of right convolution by g on
C[S_k] = sum_rho Mat_{dim rho}, which acts on the block of rho as X -> X g^(rho), of rank
dim(rho) rank(g^(rho)). The trivial block of g = h - c is mean(h) - c; it can be made 0 with c != 0
exactly when mean(h) != 0. ∎

**k = 2 (paper; `check` confirms by enumeration).** Pairings R1, R2, R3, matchings m1, m2, m3, R_i
separates the two m_j with j != i. Cost 0 means all h_R are nonzero constants, impossible by Lemma 1.
Cost 1: one pairing, say R1, has cost 1 and h_2 = a_2, h_3 = a_3 are nonzero constants; m1 gives
a_2 + a_3 = 0, and m2, m3 give h_1 = (-a_3, -a_2) = (-a_3, a_3), which has mean 0 and a nonzero sign
component: cost 2, contradiction. Cost 2 is attained by h = ((-a, a), a, -a). So the sub-model gives 2.

**k = 3 (exact).** `check` verifies that the E = 5 identity of `garbage_fast.py` (C5, TERMS5) lies in
the sub-model (on each pairing the kernel of the extra terms depends only on tau^-1 sigma), satisfies
the 15 constraints and has cost 5 = 2 + 2 + 1 in the formula above (standard representation, rank
one, on 012 and 013; sign on 024); `garbage_fast.syntheme_check` shows cost <= 4 is impossible.

**k = 4 (exact + numerical): the sub-model is not competitive.**

* The solution of Section 2 is not in the sub-model: its extra terms use the 9 matchings of type 2
  for R0, which R0 does not separate.
* Necessary condition (exact, `active 4 3`): let T be the set of pairings with nonzero cost. A
  matching separated by no pairing of T gives (A c)_m = 0 with c supported off T, and no c_R may be
  forced to 0. No T with |T| <= 2 passes; for |T| = 3 exactly two orbits pass, {0123, 0145, 0167} and
  {0123, 0145, 0246} (for the second, c is forced to be chi_Q with Q = {1,2,4,7} off T).
* Search (numerical, `solve 4 all`): minimise the smooth surrogate sum dim(rho) log det(h^ h^T + delta)
  - sum log(constant^2 + delta) over the 735-dimensional solution space, delta -> 0, L-BFGS from random
  starts. The same procedure finds 6 at k = 3 from random starts with all pairings active and the
  optimum 5 on the right active set, so it is only a weakly validated heuristic. At k = 4, 20 restarts:
  best cost 45 with all constants nonzero, 39 when vanishing constants are allowed (at cost 1 each);
  on the two admissible 3-sets the best costs were 36 and 42 (8 restarts each, vanishing constants
  allowed). Nothing below 18, let alone below 6.
* Heuristic reason: C^{matchings} = S^(8) + S^(6,2) + S^(4,4) + S^(4,2,2) + S^(2,2,2,2) (dimensions
  1, 20, 14, 56, 14) and the image of A is the first three summands (35 dimensions). The extra terms
  must cancel each other in the remaining 70 dimensions, while a rank-one block of the standard
  representation (cost 3) has 5 parameters, of the 2-dimensional representation (cost 2) 3 parameters
  and a sign term (cost 1) one. At k = 3 the corresponding codimension is 5.

## 5. What is open

* **E(4) < 6?** Not excluded. On one pairing 6 is optimal (Section 3). A Levenberg-Marquardt search
  with the machinery of `garbage_fast.py` (`fixed_model` and `run` for k = 4; terms of weight
  (1,1,1,1) or a permutation of (2,2,0,0)) was run on 14 random configurations of five terms (10 with
  mixed kinds, 4 with weight (1,1,1,1) only), 2 restarts each: nothing found, best relative residual
  14. A run takes about a minute, so this is far from exhaustive and excludes nothing. The same
  solver does recover the six-term solution on its own configuration (relative residual 2e-32).
  (Ad hoc script, not kept in the repository.)
* **Polynomial E(k)?** Open. The best upper bound is about 2^k sqrt(2/(pi k)) for even k and
  2^k sqrt(k/(2 pi)) for odd k; the only lower bounds are E >= 2 in general and Proposition 4 on one
  pairing. Since N ~ 4^k / (2 sqrt(pi k)), all counts are N (1 + o(1)): the result does not touch the
  leading term N, which the two-block model forces.
* **Odd k.** The bound (k+1)/2 * C(k,(k-1)/2) is certainly not optimal with several pairings
  (k = 3: 5 < 6); a construction for odd k that avoids the expansion along a row is missing.
* **Lean.** Corollary 3 is a signed version of `Squares.lean` (permanent_eq_sum_blockForm,
  mul_permanent_eq_squares_half) and should formalise along the same lines for all even k; this has
  not been done.

## 6. Reproduction

    python3 garbage_general.py check          # sub-model formulation: k = 2 -> 2, k = 3 -> 5   (seconds)
    python3 garbage_general.py char           # Theorem 1 on matchings, k = 2..6, and the table (seconds)
    python3 garbage_general.py verify 4       # 8^8 integer tensors: 41-term limit, 47-term exact (15 s, ~1.5 GB)
    python3 garbage_general.py single 6       # one pairing: forced zeros by type
    python3 garbage_general.py active 4 3     # admissible active sets of the sub-model (exact)
    python3 garbage_general.py solve 4 all 6  # rank-surrogate search in the sub-model (jax, ~10 s per restart)
