# The linear lower bound for split products of the permanent

Referee note, 2026-11-23. Subject: the claim called THEOREM L in the project brief.

**Verdict.** The proof sketch was re-derived from scratch and no gap was found. Theorem L below is
proved for every m >= 2, over the complex numbers, by a complete argument written out in Section 2.
The proof is on paper: nothing in it is formalised in Lean. What is machine-checked is listed in
Section 3 (exact computer checks of the two computational ingredients, and exact certificates for
m = 3, 4, 5, 6 that do not use the general argument). Both ingredients of the proof have
counterparts in the literature (Section 4). The mechanism (geometric rank is a lower bound for
partition rank, also in the limit) is published. The codimension of the variety of vanishing
maximal permanents is published for m <= 6, is stated as a conjecture for all m in the same paper,
and is claimed for all m in an unrefereed preprint of September 2026 whose proof I did not check.
The proof of the codimension given here is short and self-contained, and I did not find it in the
sources I read. The theorem needs characteristic 0 or >= m; it is false in characteristic 2
(Section 2.5).

Notation. Rows and columns are indexed from 0. A is an m x m matrix with rows r_0, .., r_{m-1} in
C^m. perm_m(A) = sum over permutations sigma of prod_i A[i, sigma(i)], regarded as a multilinear
form in the m rows. N = m(m-1) is the dimension of the space M = C^{(m-1) x m} of matrices B
formed by the first m-1 rows. n = m-1.


## 1. Statement

A *split product* is a function A -> F(A) G(A) where, for some set S of rows with S and its
complement both nonempty, F is a multilinear form in the rows r_i, i in S, and G is a multilinear
form in the rows r_i, i not in S. Sizes |S| are arbitrary and may differ from product to product.

**Theorem L.** Let m >= 2. Suppose perm_m is a limit of sums of r split products: there are, for
every k = 1, 2, .., split products P_{k,1}, .., P_{k,r} (with row sets S_{k,i} that may depend on k
and i) such that the coefficients of T_k = P_{k,1} + .. + P_{k,r} converge to those of perm_m as
k -> infinity. Then r >= m.

Expansion along one row, perm_m(A) = sum_c A[0,c] * perm(A without row 0 and column c), is an exact
sum of m split products (with S = {0}). So the least number of split products needed for perm_m,
exactly or in the limit, is exactly m when the sizes of the row sets are unrestricted.

In particular, for m = 2k and all S of size k (the middle layer), at least 2k products are needed,
exactly or in the limit.


## 2. Proof

Let Z_m be the set of B in M all of whose m maximal subpermanents vanish:

    Z_m = { B in M : Phi_c(B) = 0 for c = 0..m-1 },   Phi_c(B) = perm(B without column c).

Each Phi_c is homogeneous of degree m-1, so Z_m is a closed cone. By expansion along the last row,

    perm_m(B, x) = sum_c x_c Phi_c(B)        (B in M the first m-1 rows, x in C^m the last row),   (1)

so Z_m = { B : perm_m(B, x) = 0 for all x }.

The proof has two independent parts. Proposition A: if perm_m is a limit of sums of r split
products then Z_m meets every linear subspace of M of dimension r+1 in a nonzero point.
Proposition B: Z_m has codimension m in M. Section 2.4 puts them together.

Standard facts used (K an algebraically closed field):

* (F1) r homogeneous polynomials of positive degree in r+1 variables have a common zero other
  than 0. (Hartshorne, *Algebraic Geometry*, Theorem I.7.2; it is Krull's height theorem: the zero
  set contains 0 and each of its components has dimension >= 1.)
* (F2) Affine dimension theorem: if V, W are irreducible closed subsets of K^N then every
  irreducible component of V ∩ W has dimension >= dim V + dim W - N. (Hartshorne, Proposition
  I.7.1.)
* (F3) If the zero set of m polynomials in K^N is nonempty, each of its irreducible components has
  dimension >= N - m. (Krull; Hartshorne I.1.11A and I.7.1.)
* (F4) If f : X -> W is a morphism of varieties all of whose fibres are finite, then
  dim X <= dim W. (Theorem on the dimension of fibres, e.g. Shafarevich, *Basic Algebraic
  Geometry 1*, Chapter I, Section 6.3, applied to each irreducible component of X.)
* (F5) The map eps : K^n -> K^n, s -> (e_1(s), .., e_n(s)) (elementary symmetric polynomials) is
  surjective with finite fibres: the fibre over (a_1..a_n) is the set of orderings of the roots of
  x^n - a_1 x^{n-1} + a_2 x^{n-2} - .. .


### 2.1 Proposition A (from a limit decomposition to points of Z_m)

**Proposition A.** Assume perm_m = lim T_k with T_k = sum_{i=1..r} P_{k,i} as in Theorem L. Then
for every linear subspace L of M with dim L >= r+1 there is B in L, B != 0, with B in Z_m.

*Proof.* Fix k and i. The product P_{k,i} = F G has row sets S and its complement, both nonempty.
Exactly one of them contains the last row m-1. Call A_{k,i} the factor whose row set does not
contain the last row and C_{k,i} the other factor. Then:

* A_{k,i} is a multilinear form in a *nonempty* set of rows among the first m-1 (nonempty because
  both row sets of a split product are nonempty). As a polynomial in the entries of B in M it is
  homogeneous of degree |row set| >= 1. It does not involve the last row x.
* C_{k,i} is a polynomial in the entries of (B, x).

So T_k(B, x) = sum_i A_{k,i}(B) C_{k,i}(B, x), and

    A_{k,1}(B) = .. = A_{k,r}(B) = 0   implies   T_k(B, x) = 0 for every x in C^m.                (2)

Let L be a linear subspace of M of dimension r+1 (a larger L contains one). The restrictions of
A_{k,1}, .., A_{k,r} to L are r homogeneous polynomials of positive degree (or zero) in r+1
variables, so by (F1) they have a common zero B_k in L with B_k != 0. Since the A_{k,i} are
homogeneous we may scale B_k to have norm 1 (any fixed norm on M). By (2), T_k(B_k, x) = 0 for
all x.

The unit sphere of L is compact, so along a subsequence B_k -> B with B in L and |B| = 1. Fix x.
Convergence of coefficients implies that T_k -> perm_m uniformly on the compact set
{ (B', x) : |B'| <= 1 } (a polynomial of bounded degree is bounded on a compact set by a constant
times the largest modulus of its coefficients). Hence

    |perm_m(B, x)| <= |perm_m(B, x) - perm_m(B_k, x)| + |perm_m(B_k, x) - T_k(B_k, x)| -> 0

along the subsequence: the first term by continuity of perm_m, the second by uniform convergence
(recall T_k(B_k, x) = 0). So perm_m(B, x) = 0 for every x, i.e. B is in Z_m by (1), and B != 0. ∎

Remarks. (a) The row sets S_{k,i} may vary with k and i; nothing in the argument fixes them.
(b) The case excluded by the definition of split product, an empty row set, is exactly the case in
which the argument would fail (A_{k,i} would be a nonzero constant), and it must fail there:
perm_m = 1 * perm_m. (c) For an exact decomposition perm_m = sum_{i<=r} A_i C_i no limit is needed:
{A_1 = .. = A_r = 0} is contained in Z_m, is nonempty and has codimension <= r by (F3). (d) The
proof used only that each A_{k,i} is a homogeneous polynomial of positive degree in the first m-1
rows and that the degrees of the T_k are bounded; multilinearity of the factors is not needed.

Proposition A is a special case of known results on the *geometric rank* of
Kopparty-Moshkovitz-Zuiddam: GR(T) is the codimension of { (x_1..x_{d-1}) : T(x_1, .., x_{d-1}, .) = 0 },
GR <= partition rank, and { GR <= r } is closed (Section 4). In that language Z_m is the variety
defining GR(perm_m), Proposition B below says GR(perm_m) = m, and Theorem L is the inequality
"partition rank >= GR" in its limit form.


### 2.2 Proposition B (the codimension of Z_m)

**Proposition B.** Let K be an algebraically closed field of characteristic 0 or of characteristic
p >= m, and m >= 2. Every irreducible component of Z_m (matrices over K) has dimension exactly
N - m = m(m-2). In particular codim Z_m = m.

The lower bound dim >= N - m for every component is (F3): Z_m is defined by m equations and
contains 0. The content is the upper bound. It is proved by intersecting Z_m with the linear space
of *sum matrices*

    Sigma = { B(s,t) : s in K^n, t in K^m },    B(s,t)[i,l] = s_i + t_l      (0 <= i < n, 0 <= l < m).

The linear map (s,t) -> B(s,t) has kernel the line spanned by (-1,..,-1; 1,..,1) (if s_i + t_l = 0
for all i, l then all t_l are equal to a common value a and all s_i = -a), so dim Sigma = 2m-2.

Write t^(c) for t with the coordinate t_c removed, and e_j for the j-th elementary symmetric
polynomial (e_0 = 1).

**Lemma B1 (subpermanents of a sum matrix).** For s in K^n, t in K^m and c in {0..m-1},

    Phi_c(B(s,t)) = sum_{j=0..n} j! (n-j)! e_{n-j}(s) e_j(t^(c)).

*Proof.* Phi_c(B(s,t)) = sum over bijections sigma from {0..n-1} to the columns other than c of
prod_i (s_i + t_{sigma(i)}). Expanding the product, this is the sum over subsets J of {0..n-1} of
(prod_{i not in J} s_i) * (sum over sigma of prod_{i in J} t_{sigma(i)}). Fix J with |J| = j. A
bijection sigma restricts to an injection of J into the columns other than c, and each injection
is the restriction of exactly (n-j)! bijections. The sum of prod_{i in J} t_{tau(i)} over
injections tau is j! e_j(t^(c)), because every j-element set of columns other than c is the image
of exactly j! injections. So the inner sum is j!(n-j)! e_j(t^(c)), which depends on J only through
j, and the sum of prod_{i not in J} s_i over the J of size j is e_{n-j}(s). ∎

Reformulation. For s in K^n let lambda_s be the linear functional on the space K[x]_{<=n} of
polynomials of degree <= n defined by

    lambda_s(x^i) = i! (n-i)! e_i(s)          (i = 0..n).

Since prod_{l != c} (x + t_l) = sum_j e_j(t^(c)) x^{n-j}, Lemma B1 says

    Phi_c(B(s,t)) = lambda_s( prod_{l != c} (x + t_l) ).                                         (3)

**Lemma B2 (the fibre over t).** Let t in K^m have exactly d distinct coordinates, and let
F_t = { s in K^n : Phi_c(B(s,t)) = 0 for all c }.

* If d = m then F_t is empty.
* If d <= m-1 then there are affine-linear functions g_0, .., g_{d-1} (depending on t) such that
  s is in F_t if and only if

      e_{m-d+a}(s) = g_a( e_1(s), .., e_{m-d+a-1}(s) )      for a = 0, .., d-1.                  (4)

  Consequently the values e_1(s), .., e_{m-d-1}(s) are unrestricted on F_t, they determine all
  the e_i(s), and F_t has dimension exactly n - d.

*Proof.* Let tau_1, .., tau_d be the distinct coordinates of t, with multiplicities mu_1, .., mu_d
(sum m). Put Q(x) = prod_b (x + tau_b)^{mu_b - 1}, monic of degree m-d, and
R_a(x) = prod_{b != a} (x + tau_b), of degree d-1. If t_c = tau_a then

    prod_{l != c} (x + t_l) = (x + tau_a)^{mu_a - 1} prod_{b != a} (x + tau_b)^{mu_b} = Q(x) R_a(x).

The polynomials R_1, .., R_d are linearly independent: R_a(-tau_b) = 0 for b != a and
R_a(-tau_a) = prod_{b != a} (tau_b - tau_a) != 0, so evaluating a linear relation
sum_a alpha_a R_a = 0 at -tau_a gives alpha_a = 0. Being d independent polynomials of degree <= d-1 they span K[x]_{<=d-1}. Hence
the span of the m polynomials prod_{l != c}(x + t_l) is Q * K[x]_{<=d-1}, with basis Q, xQ, ..,
x^{d-1}Q, and by (3)

    s in F_t   iff   lambda_s(x^a Q) = 0 for a = 0, .., d-1.                                     (5)

Write Q = sum_{b=0..m-d} q_b x^b with q_{m-d} = 1. Then

    lambda_s(x^a Q) = (m-d+a)! (d-1-a)! e_{m-d+a}(s) + sum_{b < m-d} q_b (a+b)! (n-a-b)! e_{a+b}(s).

All the factorials are of integers <= n = m-1, hence nonzero in K (this is where the
characteristic is used). If d = m then Q = 1 and (5) for a = 0 reads n! = 0, which is false: F_t
is empty. If d <= m-1 then m-d+a >= 1, the leading coefficient is invertible, and (5) for
a = 0, 1, .., d-1 is the triangular system (4): it expresses e_{m-d}(s), then e_{m-d+1}(s), ..,
then e_n(s), as affine-linear functions of the e_i(s) of smaller index (with e_0 = 1). So eps(F_t)
is the graph A_t of an affine map K^{m-d-1} -> K^d and F_t = eps^{-1}(A_t); by (F5) and (F4),
dim F_t = dim A_t = m-d-1 = n-d. ∎

**Lemma B3.** Y = { (s,t) in K^n x K^m : B(s,t) in Z_m } has dimension <= m-1.

*Proof.* For a partition pi of the index set {0..m-1} into d blocks let T_pi be the set of t that
are constant on each block and take different values on different blocks. T_pi is locally closed,
of dimension d, and K^m is the disjoint union of the finitely many T_pi. Put
Y_pi = Y ∩ (K^n x T_pi), a locally closed set. If d = m then Y_pi is empty by Lemma B2. If
d <= m-1, consider the morphism

    Y_pi -> K^{m-d-1} x T_pi,     (s,t) -> ( e_1(s), .., e_{m-d-1}(s), t ).

Its fibres are finite: by (4), t and e_1(s), .., e_{m-d-1}(s) determine all the e_i(s), hence s up
to reordering (F5). By (F4), dim Y_pi <= (m-d-1) + d = m-1. Y is the union of the Y_pi. ∎

Note that the argument needs no irreducibility and no non-emptiness, and that the strata with
repeated values of t are not negligible: every stratum with d <= m-1 contributes dimension exactly
m-1 (for d = 1, t = (a,..,a), F_t is the set of s with prod_i (s_i + a) = 0: a row of B vanishes).
What makes the count work is that each coincidence among the t_l lowers the number of conditions
on s by exactly one.

*Proof of Proposition B.* The set Y of Lemma B3 is the preimage of Z_m ∩ Sigma under the
surjective linear map K^n x K^m -> Sigma, whose fibres are lines. So
dim (Z_m ∩ Sigma) = dim Y - 1 <= m-2. Let W be an irreducible component of Z_m. W is closed and
stable under scaling, so 0 is in W ∩ Sigma. By (F2) applied to W and the linear space Sigma,

    m - 2 >= dim (W ∩ Sigma) >= dim W + (2m-2) - N,

so dim W <= N - m. With (F3), dim W = N - m. ∎


### 2.3 A linear space that misses Z_m

**Lemma G.** Let Z be a closed cone in K^N (closed, stable under scaling) of dimension D. Then
there is a linear subspace L of K^N of dimension N - D with L ∩ Z = {0}.

*Proof.* Induction on D. If D = 0 then Z = {0} and L = K^N. Let D >= 1. Z has finitely many
irreducible components; pick a nonzero point v_a in each component of positive dimension and a
linear form h with h(v_a) != 0 for all a (possible since K is infinite). Then no component of
positive dimension lies in the hyperplane H = {h = 0}, so each meets H in a proper closed subset,
of smaller dimension. Thus Z ∩ H is a closed cone of dimension <= D-1 in H = K^{N-1}; by induction
(and passing to a subspace if the dimension dropped by more than one) there is a linear subspace
L of H of dimension (N-1) - (D-1) = N - D with L ∩ Z = {0}. ∎


### 2.4 Proof of Theorem L

By Proposition B (K = C), Z_m is a closed cone of dimension N - m. By Lemma G there is a linear
subspace L of M of dimension m with L ∩ Z_m = {0}. Suppose perm_m is a limit of sums of r split
products with r <= m-1. Let L' be a subspace of L of dimension r+1 <= m. By Proposition A, L'
contains a nonzero point of Z_m, contradicting L ∩ Z_m = {0}. Hence r >= m. ∎

For m = 3, 4, 5, 6 the space L can be taken explicit and the general Proposition B is not needed:
L_m = { ( f(m*i + j) )_{i<m-1, j<m} : f a polynomial of degree < m } (the values of f at the
integers 0, .., m(m-1)-1 written row by row) satisfies L_m ∩ Z_m = {0}; this is an exact computer
check (Section 3, Appendix A).


### 2.5 Scope and variants

* **Real numbers.** A limit of real decompositions is a limit of complex ones, so the theorem holds
  over R.
* **Exact decompositions over other fields.** If perm_m = sum_{i<=r} F_i G_i exactly over a field
  K of characteristic 0 or >= m, extend scalars to the algebraic closure and use Remark (c) after
  Proposition A with Proposition B: r >= m. By `multilinear_split_of_function_split`
  (SplitBridge.lean) the same holds when F_i, G_i are arbitrary functions of their rows.
* **Characteristic.** Lemma B2 divides by the factorials j!, j <= m-1. In characteristic 2 the
  theorem is false: there perm = det, and det_4 is an exact sum of 3 split products of type 2|2
  (Lampert-Moshkovitz, Theorem 3.5, over any field; checked in pequalnp/checks/det4.py). For
  2 < p < m the argument above does not apply; the preprint of Xie cited in Section 4 claims
  codim Z_m = m in every characteristic other than 2.
* **The determinant.** The same argument applied to det_m gives only 2: the matrices B whose
  maximal minors all vanish are those of rank < m-1, of codimension 2. This is why the method says
  nothing for the determinant, where the truth is smaller than m for m = 4.
* **The method cannot give more than m, for any tensor.** The set in Proposition A is cut out by
  the m coefficients of the last row, so its codimension is at most m. More to the point, the
  statement proved is blind to the sizes of the row sets: it bounds the number of split products of
  *all* shapes at once, and for that quantity m is the truth (row expansion). Any argument that
  does not use that both row sets have at least two elements, or that |S| = k, is capped at m. At
  the middle layer of perm_4 the true value in the limit is 5 (FourByFourLower.lean), strictly
  more than the bound 4 given here; at the middle layer of perm_6 the bound is 6 against the
  upper bound 15 (FifteenTerm.lean).


## 3. What was checked by machine

Nothing in Sections 2.1-2.4 is formalised in Lean. The Lean project contains two related exact
statements proved independently: `le_of_permanent_eq_sum_row_linear_mul` (FirstLayer.lean: the
case where every product has a linear form in one row as a factor, the other factor an arbitrary
function) and `not_tendsto_sum_four_isSplit` (FourByFourLower.lean: 4 x 4, type 2|2, which gives
5 > 4).

Exact computer checks (integer or modular arithmetic, no floating-point rounding), all run on
2026-11-23:

1. `python3 pequalnp/checks/sum_matrix_check.py` (existing script, 2 min 26 s): Lemma B1 verified
   symbolically for m = 3, 4, 5; fibre dimensions of Lemma B2 for m = 4 by Groebner bases for eight
   choices of t (empty, 0, 0, 1, 1, 1, 2, 0 as predicted); point counts over F_q of the set Y for
   m = 3 (q = 5, 7, 11, 13), m = 4 (q = 5, 7, 11), m = 5 (q = 7), all between 4 and 62 times
   q^(m-1), consistent with dimension m-1, and with no point having pairwise distinct t. The
   script runs as described and every line of its output agrees with its predictions.
2. `python3 pequalnp/checks/gr_certificate.py 3 4 5` (existing script, 17 s): an m-dimensional
   linear space meeting Z_m only in 0, certified by full column rank mod 32003 of the Macaulay
   matrix in degree m(m-2)+1, for m = 3 and 5 (circulant B[i,j] = t_{(i+j) mod m}) and m = 4 (rows
   t, A_2 t, A_3 t). Reproduced: full column rank in every block. The logic of the certificate is
   sound: full column rank mod p implies full column rank over Q, so every monomial of that degree
   is in the ideal and the m subpermanents have no common zero other than 0 on the subspace.
3. Referee's own checks of the sum-matrix lemma (script in Appendix B, 6 s): Lemma B1 at random
   integer points for m = 2..8; the identity det[ e_j(t^(c)) ]_{c,j} = +-prod_{c<c'} (t_c - t_c')
   (symbolic for m <= 5, at random integer points for m = 6..9), which gives the case d = m of
   Lemma B2 independently; and, for every multiplicity pattern of t (every partition of m, with
   and without a zero value, m = 2..8, 130 cases), exact rational linear algebra confirming that
   the conditions have rank d and that the solution set in (e_1..e_n) is empty for d = m and of
   dimension n - d otherwise.
4. Referee's certificate for m = 3, 4, 5, 6 with the subspace L_m of Section 2.4 (script in
   Appendix A). It computes the Hilbert function of F_p[t_0..t_{m-1}] / (Phi_0, .., Phi_{m-1})
   degree by degree through the dual space (inverse system) of the ideal, so that only the
   quotient, of total dimension (m-1)^m, is stored; the Macaulay matrix in degree 25 for m = 6
   would have 142506 columns. Results:
   * m = 3, 4, 5 (36 s in total): the Hilbert function equals that of a complete intersection,
     i.e. the coefficients of (1 + z + .. + z^(m-2))^m, in every degree, and is 0 in degree
     m(m-2)+1 = 4, 9, 16. Every value agrees with the rank of the Macaulay matrix of that degree
     computed directly.
   * m = 6 (prime 32003, 591 s, largest matrix 26265 x 10116): h_5, .., h_25 = 246, 426, 666,
     951, 1246, 1506, 1686, 1751, 1686, 1506, 1246, 951, 666, 426, 246, 126, 56, 21, 6, 1, 0.
     These are the coefficients of (1 + z + z^2 + z^3 + z^4)^6, and h_25 = 0. The values in
     degrees 6..11 agree with the Macaulay matrices computed directly. A second run with
     the prime 65521 (619 s) gives the same Hilbert function and the same agreement.
     Hence L_6 meets Z_6 only in 0 and codim Z_6 >= 6, independently of Section 2.2.
   * Safeguards: the modular linear algebra (blocked elimination, integers mod p held in
     floating point with every intermediate value below 2^53) was tested against a naive
     integer elimination on 60 random matrices of assorted ranks; every kernel vector the
     script produces is verified against the defining equations before it is used. A kernel
     that is too large is therefore impossible; a kernel that is too small (a false pivot)
     would not be caught by that verification, and is excluded only by the tests and by the
     agreement with the direct Macaulay computations.
   * m = 7 is out of reach of this computation on the present machine and is not needed: the
     quotient has dimension 6^7 = 279936 with a peak of 24017 in degree 17, so the matrices
     would have about 168000 columns (about 24000 per block with the Z_7-grading of the
     circulant, in 7 blocks and 30 degrees, each about 72000 x 24000).

Remark on the circulant. For composite m the circulant subspace B[i,j] = c_ij t_{(i+j) mod m}
(any nonzero constants c_ij) always meets Z_m outside 0, so it cannot be used for m = 4 or 6: if
e divides m with 1 < e < m, the matrices with t_k = 0 unless e divides k split into e-1 square
blocks of size m/e and one block of size (m/e - 1) x (m/e), every nonzero maximal subpermanent is
divisible by the permanent of a square block, and that permanent vanishes on a hypersurface of
this (m/e)-dimensional space. (Checked for m = 4: the Hilbert function of the quotient stabilises
at 4 instead of reaching 0, for the plain circulant and for six other choices of the c_ij.) This
explains the remark "the circulant fails for even m" in gr_certificate.py. For m = 6 the
computation in item 4 is therefore done on a subspace without any grading.

Numerical evidence only (not part of the proof): `python3 pequalnp/splitrank.py --m 3 --k 1
--terms 2` finds no decomposition of perm_3 with two products (best residual 0.334 over 20
restarts for each configuration), as the theorem requires.


## 4. Literature

What I read is stated for each item. Searches were run on 2026-11-23.

**The mechanism (Proposition A).** S. Kopparty, G. Moshkovitz, J. Zuiddam, *Geometric rank of
tensors and subrank of matrix multiplication*, Discrete Analysis 2023:1,
https://arxiv.org/abs/2002.09472 . Read: Sections 1.5, 2 (definition for k-tensors) and 5. For a
k-tensor T, GR(T) is the codimension of { (x_1, .., x_{k-1}) : T(x_1, .., x_{k-1}, .) = 0 };
Theorem 5 states GR(T) <= PR(T) (partition rank, Naslund,
https://arxiv.org/abs/1701.04475 ) for k-tensors; Lemma 5.3 states that { GR <= r } is Zariski
closed (written for 3-tensors, with the remark that all proofs extend to k-tensors). Together they
give: a limit of tensors of partition rank <= r has GR <= r. Proposition A is this statement for
perm_m with a direct proof. So step (i) of the sketch is not new, and Theorem L is the published
inequality applied to the value GR(perm_m) = m, which is Proposition B.

**The codimension (Proposition B).** Z_m is the variety P_{k,k+1} of maximal permanents of a
generic k x (k+1) matrix, k = m-1.

* A. Boralevi, E. Carlini, M. Michałek, E. Ventura, *On the codimension of permanental varieties*,
  Advances in Mathematics 461 (2025) 110079, https://arxiv.org/abs/2402.17839 . Read: version 2,
  Sections 1-3 in full, statements of Proposition 4.13 and Theorem 4.23. Theorem 3.18: in
  characteristic 0 the variety P_{k,n} has codimension n for 2 <= k <= 5 and n >= k+1; the base
  cases k x (k+1) are from Laubenbacher-Swanson (k = 2), Kirkup (k = 3) and Macaulay2 computations
  (k = 3, 4 on a section by circulant Hankel matrices; k = 5 in Proposition 4.13). **Conjecture
  3.4** of that paper: P_{k,k+1} is a complete intersection, in particular of codimension k+1, for
  every k >= 2. So in the refereed literature Proposition B is a theorem for m <= 6 and a
  conjecture for m >= 7. They remark that restricting to a suitable linear space "might be a
  strategy to give the desired lower bound on the codimension"; the space of sum matrices used in
  Section 2.2 is such a space, and it works for every m.
  Their Theorem 3.19 shows that codim P_{h,h+1} = h+1 for all h <= k implies codim P_{k,n} = n for
  all n >= k+1; combined with Proposition B this gives codim P_{k,n} = n for all k < n in
  characteristic 0.
* Y. Xie, *Dimensions of permanental varieties in arbitrary size*, arXiv:2609.27320 (23 September
  2026), https://arxiv.org/abs/2609.27320 . Read: abstract, introduction, Section 6, Appendix A;
  the proofs were **not** checked. A 9-page preprint, not refereed as far as I can tell; its
  acknowledgment states that an AI system assisted with proof development. Theorem 1.3 there
  claims that for every k >= 1 and every field of characteristic != 2 the ideal of maximal
  permanents of a generic k x (k+1) matrix is a radical complete intersection of height k+1, which
  contains Proposition B (and extends it to characteristics 2 < p < m). Corollary 1.2 claims that
  the critical locus of perm_n has codimension 2n, and Corollary 6.2 deduces that perm_n is not a
  sum of fewer than n products of two homogeneous polynomials of positive degree. If correct, that
  corollary contains the exact form of Theorem L (and more: the factors need not be multilinear);
  the limit form would follow by semicontinuity of the dimension of the critical locus. I treat
  these as claims of an unverified preprint; Theorem L as proved here does not depend on them.
* G. Kirkup, *Minimal primes over permanental ideals*, https://arxiv.org/abs/math/0510025 (abstract
  only; Boralevi et al. attribute codim P_{3,4} = 4 to its Section 7). R. Laubenbacher, I. Swanson,
  *Permanental ideals*, J. Symbolic Comput. 30 (2000), https://arxiv.org/abs/math/9812112 (abstract
  and a summary only): 2 x 2 permanents.
* I did not find the sum-matrix argument of Section 2.2 in any of the sources above. Boralevi et
  al. use circulant sections and computer algebra; Xie's abstract describes a different method
  (pivot expansion and cubic relations).

**Partition rank of the determinant, for contrast.**

* A. Lampert, G. Moshkovitz, *Slice rank and partition rank of the determinant*, ITCS 2026,
  https://arxiv.org/abs/2509.06294 . Read: abstract, Section 1, statement of Theorem 2.6,
  Section 3 through Theorem 3.5. Slice rank of det_n is n; prk(det_n) >= log2(n) + 1;
  prk(det_4) = 3 over any field. Remark 3.3 records the route used here ("prk(T) >= grk(T)", from
  Kopparty-Moshkovitz-Zuiddam) and that it is useless for the determinant because grk(det_n) = 2.
  The permanent is not mentioned anywhere in the paper (text search).
* Q. Chen, Y. Zhao, *Lower bounds on the strength of the determinant*,
  https://arxiv.org/abs/2607.21015 (23 July 2026). Read: abstract and introduction. str(det_p) = p
  for primes p and prk(det_n) >= largest prime <= n, by an intersection-theoretic argument. The
  permanent is not mentioned (text search).
* C. Brand, P. Kaski, J. Wang, *Partition rank and algebraic circuit lower bounds*,
  https://arxiv.org/abs/2607.02241 . Read: abstract and introduction. The (k, m-k) rank of the
  project is their lambda-rank for lambda = (m-k, k). The permanent is not mentioned (text search).

**Slice rank.** W. Sawin and T. Tao, *Notes on the "slice rank" of tensors* (blog post, 24 August
2016), https://terrytao.wordpress.com/2016/08/24/notes-on-the-slice-rank-of-tensors/ (read through
an automatic summary of the page, statement of Proposition 4 only): a tensor with nonzero
coefficients supported on an antichain has slice rank equal to the least number of slices covering
the support. The support of perm_m (and of det_m), the permutations inside {0..m-1}^m, is an
antichain, and it cannot be covered by fewer than m slices (each slice contains (m-1)! of the m!
permutations). So the slice rank of perm_m is m over every field. I did not find this stated for
the permanent in so many words; it is immediate, and the exact lower bound is also in
FirstLayer.lean. Theorem L extends "m" from slice rank to partition rank, in characteristic 0.

**Search for the statement itself.** Queries for "geometric rank", "analytic rank" or "partition
rank" of the permanent (tensor) returned no source that computes any of them for the permanent.
So I found the statement "the partition rank of perm_m is m" (exactly and in the limit) in print
only implicitly: for m <= 6 it follows from Kopparty-Moshkovitz-Zuiddam plus Boralevi et al., and
for all m (exact form) from the unverified corollary of Xie. By Theorem 6 of
Kopparty-Moshkovitz-Zuiddam, GR(perm_m) = m also means that the analytic rank of perm_m over F_p
has liminf m as p -> infinity.

**The open problem.** V. Arvind, S. Raja, *Some lower bound results for set-multilinear arithmetic
computations*, https://arxiv.org/abs/1511.02308 (abstract and introduction only): lower bounds for
narrow set-multilinear branching programs computing the permanent, with the general case left
open. Theorem L gives width >= m at every layer of such a program, in the limit as well, and by
Section 2.5 this type of argument cannot give more.


## Appendix A. Certificate script for m = 3, 4, 5, 6

Save the block below as a file, say `gr_dual.py`, and run `python3 gr_dual.py 3 4 5` (36 s) or
`python3 gr_dual.py 6` (about 10 minutes on 2 cores, about 4 GB of memory); `--prime=65521`
changes the prime. Requires numpy and scipy. The script is not in pequalnp/checks because the
referee's task allowed only this file to be written; it can be copied there unchanged.

```python
"""Exact certificate that an m-dimensional linear space L of (m-1) x m matrices meets
Z_m = {B : all m maximal subpermanents of B vanish} only in 0.  Consequence: codim Z_m >= m.

L = {B(t) : t in C^m},  B_ij(t) = f_t(m*i + j),  f_t(u) = t_0 + t_1 u + .. + t_{m-1} u^{m-1}
(the values of a polynomial of degree < m at the nodes 0, 1, .., m(m-1)-1, written row by row).
Phi_c(t) = perm(B(t) without column c),  c = 0..m-1 :  m forms of degree m-1 in m variables, integer coefficients.

Method: Hilbert function of F_p[t]/(Phi_0..Phi_{m-1}) degree by degree through the inverse system of the ideal.
  I_D^perp = {phi in (R_D)^* : phi(I_D) = 0},  h_D = dim I_D^perp = dim (R/I)_D.
  For D > m-1:  I_D = sum_i t_i I_{D-1},  so  I_D^perp = {phi : t_i.phi in I_{D-1}^perp for all i},
  where (t_i.phi)(g) = phi(t_i g);  phi -> (t_i.phi)_i identifies I_D^perp with the tuples (psi_i) in
  (I_{D-1}^perp)^m with  t_j.psi_i = t_i.psi_j  (i < j).  So h_D is the nullity of a matrix built from the
  contraction matrices of the previous degree; only the quotient (total dimension (m-1)^m) is stored.
If h_N = 0 for N = m(m-2)+1 then the Macaulay matrix of degree N has full column rank mod p, hence over Q,
every monomial of degree N lies in the ideal, and the Phi_c have no common zero t != 0 over C.
All arithmetic is exact: integers mod p held in float64, every intermediate value below 2^53.
"""
import itertools, sys, time
import numpy as np
from scipy.linalg.blas import dgemm

P = 32003
for _a in sys.argv[1:]:
    if _a.startswith('--prime='):
        P = int(_a.split('=')[1])

# ---------------------------------------------------------------- linear algebra mod p (float64, exact)
def echelon(A, p=P, bs=64):
    """A: float64 Fortran-ordered integer-valued matrix.  Row echelon form mod p without row exchanges, in place.
    Returns (pivrows, pivcols): row pivrows[k] is the k-th echelon row (unit pivot in column pivcols[k])."""
    R, C = A.shape
    done = np.zeros(R, dtype=bool)
    pivrows, pivcols = [], []
    c0 = 0
    while c0 < C and len(pivrows) < R:
        c1 = min(C, c0 + bs)
        act = np.flatnonzero(~done)
        S = np.remainder(A[act, c0:c1], p)
        b = c1 - c0
        Mloc = np.zeros((len(act), b))
        ldone = np.zeros(len(act), dtype=bool)
        newpiv, invs = [], []
        for cc in range(b):
            cand = np.flatnonzero((S[:, cc] != 0) & ~ldone)
            if cand.size == 0:
                continue
            q = int(cand[0])
            inv = pow(int(S[q, cc]), p - 2, p)
            S[q, cc:] = np.remainder(S[q, cc:] * inv, p)
            mult = S[:, cc].copy(); mult[ldone] = 0; mult[q] = 0
            Mloc[:, len(newpiv)] = mult
            nzr = np.flatnonzero(mult)
            if nzr.size:
                S[nzr, cc:] = np.remainder(S[nzr, cc:] - np.outer(mult[nzr], S[q, cc:]), p)
            ldone[q] = True
            newpiv.append(q); invs.append(inv); pivcols.append(c0 + cc)
        A[act, c0:c1] = S
        k = len(newpiv)
        if k:
            prow = act[newpiv]
            if c1 < C:
                T = A[:, c1:]
                U = np.empty((k, C - c1))
                for a in range(k):
                    row = np.remainder(T[prow[a], :], p)
                    if a:
                        row = np.remainder(row - Mloc[newpiv[a], :a] @ U[:a], p)
                    U[a] = np.remainder(row * invs[a], p)
                Mfull = np.zeros((R, k), order='F')
                Mfull[act] = Mloc[:, :k]
                Mfull[prow] = 0
                out = dgemm(-1.0, Mfull, U, beta=1.0, c=T, overwrite_c=1)
                if not np.shares_memory(out, A):
                    A[:, c1:] = out
                A[prow, c1:] = U
            done[prow] = True
            pivrows.extend(int(x) for x in prow)
        c0 = c1
    return pivrows, pivcols

def nullspace(A, p=P):
    """Basis (columns) of {x : A x = 0 mod p};  A (float64, Fortran order) is destroyed."""
    R, C = A.shape
    if R == 0:
        return np.eye(C)
    pivrows, pivcols = echelon(A, p)
    rank = len(pivrows)
    pset = set(pivcols)
    free = [c for c in range(C) if c not in pset]
    K = np.zeros((C, len(free)))
    if free:
        K[free, np.arange(len(free))] = 1
        if rank:
            U = A[pivrows]
            UF = np.remainder(U[:, free], p)
            UP = np.remainder(U[:, pivcols], p)
            del U
            V = np.zeros((rank, len(free)))
            blk = 128
            for hi in range(rank, 0, -blk):
                lo = max(0, hi - blk)
                W = UF[lo:hi].copy()
                if hi < rank:
                    W += np.remainder(UP[lo:hi, hi:] @ V[hi:], p)
                for k in range(hi - 1, lo - 1, -1):
                    acc = W[k - lo]
                    if k < hi - 1:
                        acc = acc + UP[k, k + 1:hi] @ V[k + 1:hi]
                    V[k] = np.remainder(-acc, p)
            K[pivcols, :] = V
    return K

def rank_mod_p(M, p=P):
    A = np.asfortranarray(np.remainder(M, p), dtype=np.float64)
    return len(echelon(A, p)[0])

# ---------------------------------------------------------------- polynomials
def monomials(nv, d):
    if nv == 1:
        yield (d,); return
    for a in range(d + 1):
        for rest in monomials(nv - 1, d - a):
            yield (a,) + rest

def pmul(f, g):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            k = tuple(a + b for a, b in zip(m1, m2))
            out[k] = out.get(k, 0) + c1 * c2
    return {k: v for k, v in out.items() if v}

def subperm_polys(m, entry):
    """entry(i, j) = list of the m integer coefficients of the linear form B_ij(t).  Returns the m maximal
    subpermanents (column c omitted) as dicts monomial -> integer (exact Python integers)."""
    one = tuple([0] * m)
    lin = [[{tuple(1 if a == k else 0 for a in range(m)): int(v) for k, v in enumerate(entry(i, j)) if v}
            for j in range(m)] for i in range(m - 1)]
    phis = []
    for c in range(m):
        cols = [j for j in range(m) if j != c]
        # dynamic programme over subsets of columns (rows taken in order)
        dp = {0: {one: 1}}
        for i in range(m - 1):
            nd = {}
            for mask, f in dp.items():
                for a, j in enumerate(cols):
                    if not mask >> a & 1:
                        g = pmul(f, lin[i][j])
                        tgt = nd.setdefault(mask | 1 << a, {})
                        for k, v in g.items():
                            tgt[k] = tgt.get(k, 0) + v
            dp = nd
        f = dp[(1 << (m - 1)) - 1]
        phis.append({k: v for k, v in f.items() if v})
    return phis

# ---------------------------------------------------------------- Hilbert function through the dual space
def hilbert_function(m, phis, Dmax=None, p=P, verbose=True):
    d = m - 1
    Dmax = Dmax or m * (m - 2) + 1
    unit = [tuple(1 if a == i else 0 for a in range(m)) for i in range(m)]
    mons_lo = list(monomials(m, d - 1))
    mons_d = list(monomials(m, d)); idx_d = {mon: i for i, mon in enumerate(mons_d)}
    E = np.zeros((len(phis), len(mons_d)), order='F')
    for a, f in enumerate(phis):
        assert all(sum(k) == d for k in f)
        for k, v in f.items():
            E[a, idx_d[k]] = v % p
    K = nullspace(E, p)
    X = []                                   # X[i] : I_D^perp -> I_{D-1}^perp, contraction with t_i
    for i in range(m):
        rows = [idx_d[tuple(x + y for x, y in zip(mon, unit[i]))] for mon in mons_lo]
        X.append(K[rows, :].copy())
    H = {d - 1: len(mons_lo), d: K.shape[1]}
    if verbose:
        print(f"   D={d}: h = {H[d]}", flush=True)
    pairs = [(i, j) for i in range(m) for j in range(i + 1, m)]
    for D in range(d + 1, Dmax + 1):
        t0 = time.time()
        hp, hpp = H[D - 1], H[D - 2]
        A = np.zeros((len(pairs) * hpp, m * hp), order='F')
        for a, (i, j) in enumerate(pairs):       # t_j.psi_i - t_i.psi_j = 0
            A[a * hpp:(a + 1) * hpp, i * hp:(i + 1) * hp] = X[j]
            A[a * hpp:(a + 1) * hpp, j * hp:(j + 1) * hp] = np.remainder(-X[i], p)
        shape = A.shape
        K = nullspace(A, p)
        del A
        Xn = [K[i * hp:(i + 1) * hp, :].copy() for i in range(m)]
        for i, j in pairs:                       # every kernel vector is verified
            assert not np.remainder(X[j] @ Xn[i] - X[i] @ Xn[j], p).any()
        H[D] = K.shape[1]
        X = Xn
        if verbose:
            print(f"   D={D}: h = {H[D]}   (matrix {shape[0]} x {shape[1]}, {time.time()-t0:.1f} s)", flush=True)
        if H[D] == 0:
            for D2 in range(D + 1, Dmax + 1):
                H[D2] = 0
            break
    return H

def ci_hilbert(m):
    c = np.array([1], dtype=object)
    for _ in range(m):
        c = np.convolve(c, np.array([1] * (m - 1), dtype=object))
    return [int(x) for x in c]

def macaulay_h(m, phis, D, p=P):
    """h_D directly: (#monomials of degree D) - rank of the Macaulay matrix in degree D (for cross-checks)."""
    d = m - 1
    cols = list(monomials(m, D)); index = {mon: i for i, mon in enumerate(cols)}
    mults = list(monomials(m, D - d))
    M = np.zeros((len(mults) * len(phis), len(cols)), order='F')
    r = 0
    for f in phis:
        for mu in mults:
            for k, v in f.items():
                M[r, index[tuple(a + b for a, b in zip(k, mu))]] = v % p
            r += 1
    return len(cols) - len(echelon(M, p)[0])

def poly_eval_entry(m):
    return lambda i, j: [(m * i + j) ** k for k in range(m)]

def run(m, entry, label, crosscheck=()):
    t0 = time.time()
    phis = subperm_polys(m, entry)
    print(f"m={m}  [{label}]  {len(phis)} forms of degree {m-1}, numbers of terms {[len(f) for f in phis]}, prime {P}", flush=True)
    H = hilbert_function(m, phis)
    ci = ci_hilbert(m)
    N = m * (m - 2) + 1
    same = all(H[D] == (ci[D] if D < len(ci) else 0) for D in range(m - 1, N + 1))
    print(f"   Hilbert function = coefficients of (1+z+..+z^{m-2})^{m} in every degree {m-1}..{N}: {same};  h_{N} = {H[N]}", flush=True)
    ok = True
    for D in crosscheck:
        hd = macaulay_h(m, phis, D)
        print(f"   cross-check, Macaulay matrix in degree {D}: h = {hd}  ({'agrees' if hd == H[D] else 'DISAGREES'})", flush=True)
        ok &= (hd == H[D])
    cert = ok and H[N] == 0
    print(f"m={m}: L meets Z_{m} only in 0, hence codim Z_{m} >= {m}: {'CERTIFIED' if cert else 'NO CERTIFICATE'}"
          f"   ({time.time()-t0:.1f} s)", flush=True)
    return cert, H

if __name__ == '__main__':
    which = [int(a) for a in sys.argv[1:] if not a.startswith('-')] or [3, 4, 5]
    for m in which:
        N = m * (m - 2) + 1
        cc = range(m, N + 1) if m <= 5 else (range(6, 12) if m == 6 else ())
        run(m, poly_eval_entry(m), "B_ij = f(m*i+j), deg f < m", crosscheck=cc)
```

Output for m = 6:

```
m=6  [B_ij = f(m*i+j), deg f < m]  6 forms of degree 5, numbers of terms [252, 252, 252, 252, 252, 252], prime 32003
   D=5: h = 246
   D=6: h = 426   (matrix 1890 x 1476, 0.7 s)
   D=7: h = 666   (matrix 3690 x 2556, 2.0 s)
   D=8: h = 951   (matrix 6390 x 3996, 6.3 s)
   D=9: h = 1246   (matrix 9990 x 5706, 14.4 s)
   D=10: h = 1506   (matrix 14265 x 7476, 31.4 s)
   D=11: h = 1686   (matrix 18690 x 9036, 52.8 s)
   D=12: h = 1751   (matrix 22590 x 10116, 75.0 s)
   D=13: h = 1686   (matrix 25290 x 10506, 93.2 s)
   D=14: h = 1506   (matrix 26265 x 10116, 92.1 s)
   D=15: h = 1246   (matrix 25290 x 9036, 81.2 s)
   D=16: h = 951   (matrix 22590 x 7476, 62.2 s)
   D=17: h = 666   (matrix 18690 x 5706, 41.2 s)
   D=18: h = 426   (matrix 14265 x 3996, 20.4 s)
   D=19: h = 246   (matrix 9990 x 2556, 9.0 s)
   D=20: h = 126   (matrix 6390 x 1476, 3.3 s)
   D=21: h = 56   (matrix 3690 x 756, 1.0 s)
   D=22: h = 21   (matrix 1890 x 336, 0.2 s)
   D=23: h = 6   (matrix 840 x 126, 0.1 s)
   D=24: h = 1   (matrix 315 x 36, 0.0 s)
   D=25: h = 0   (matrix 90 x 6, 0.0 s)
   Hilbert function = coefficients of (1+z+..+z^4)^6 in every degree 5..25: True;  h_25 = 0
   cross-check, Macaulay matrix in degree 6: h = 426  (agrees)
   cross-check, Macaulay matrix in degree 7: h = 666  (agrees)
   cross-check, Macaulay matrix in degree 8: h = 951  (agrees)
   cross-check, Macaulay matrix in degree 9: h = 1246  (agrees)
   cross-check, Macaulay matrix in degree 10: h = 1506  (agrees)
   cross-check, Macaulay matrix in degree 11: h = 1686  (agrees)
m=6: L meets Z_6 only in 0, hence codim Z_6 >= 6: CERTIFIED   (590.8 s)
```


## Appendix B. Script for the checks of the sum-matrix lemma (item 3 of Section 3)

```python
"""Independent exact checks of the sum-matrix lemma (referee's own script, exact rational/integer arithmetic).
 (a) Phi_c(s,t) = perm[(s_i + t_l)]_{l != c} = sum_j j!(n-j)! e_{n-j}(s) e_j(t without t_c)   at random integer points, m <= 8
 (b) det [ e_j(t^(c)) ]_{c,j} = +- prod_{c<c'} (t_c - t_c')                                    (symbolic m <= 5, numeric m <= 9)
 (c) for every multiplicity pattern of t (partition of m into d parts): the solution set of the m conditions,
     as an affine-linear system in (e_1(s),..,e_n(s)), is empty if d = m and has dimension exactly n - d otherwise.
"""
import itertools, math, random
import sympy as sp
from fractions import Fraction

def esym_list(vals):
    """[e_0, e_1, .., e_len] of the integers vals"""
    e = [1]
    for v in vals:
        e = [1] + [e[k] + v * e[k - 1] for k in range(1, len(e))] + [v * e[-1]]
    return e

def perm_int(M):
    """permanent of a square integer matrix by Ryser/DP over subsets (exact)"""
    n = len(M)
    dp = {0: 1}
    for i in range(n):
        nd = {}
        for mask, v in dp.items():
            for j in range(n):
                if not mask >> j & 1:
                    nd[mask | 1 << j] = nd.get(mask | 1 << j, 0) + v * M[i][j]
        dp = nd
    return dp[(1 << n) - 1]

random.seed(7)
print("(a) formula at random integer points")
for m in range(2, 9):
    n = m - 1
    ok = True
    for trial in range(5):
        s = [random.randint(-9, 9) for _ in range(n)]
        t = [random.randint(-9, 9) for _ in range(m)]
        es = esym_list(s)
        for c in range(m):
            cols = [l for l in range(m) if l != c]
            lhs = perm_int([[s[i] + t[l] for l in cols] for i in range(n)])
            et = esym_list([t[l] for l in cols])
            rhs = sum(math.factorial(j) * math.factorial(n - j) * es[n - j] * et[j] for j in range(n + 1))
            ok &= (lhs == rhs)
    print(f"   m={m}: {ok}")

print("(b) det[e_j(t^(c))] = +- Vandermonde")
for m in range(2, 6):
    t = sp.symbols(f't0:{m}')
    E = sp.Matrix(m, m, lambda c, j: sum(sp.prod(cc) for cc in itertools.combinations([t[l] for l in range(m) if l != c], j)) if j else 1)
    V = sp.prod([t[a] - t[b] for a in range(m) for b in range(a + 1, m)])
    d = sp.expand(E.det(method='berkowitz'))
    print(f"   m={m} symbolic: det = +Vandermonde: {sp.expand(d - V) == 0},  det = -Vandermonde: {sp.expand(d + V) == 0}")
for m in range(6, 10):
    ok = True
    for trial in range(3):
        t = random.sample(range(-20, 21), m)
        E = sp.Matrix(m, m, lambda c, j: esym_list([t[l] for l in range(m) if l != c])[j])
        V = math.prod(t[a] - t[b] for a in range(m) for b in range(a + 1, m))
        ok &= (abs(E.det()) == abs(V))
    print(f"   m={m} at random integer points: |det| = |Vandermonde|: {ok}")

def partitions(n, maxpart=None):
    maxpart = maxpart or n
    if n == 0:
        yield []; return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield [k] + rest

print("(c) fibre over t, for every multiplicity pattern: affine-linear system in (e_1(s), .., e_n(s))")
allok = True
for m in range(2, 9):
    n = m - 1
    res = []
    for mu in partitions(m):
        d = len(mu)
        for variant in range(2):          # variant 1: one of the values is 0
            vals = random.sample([v for v in range(-12, 13) if v != 0], d)
            if variant:
                vals[random.randrange(d)] = 0
            t = [v for v, k in zip(vals, mu) for _ in range(k)]
            # row c: coefficients a_j = j!(n-j)! e_j(t^(c)) of e_{n-j}(s), j = 0..n ; e_0(s) = 1 belongs to j = n
            rows = []
            for c in range(m):
                et = esym_list([t[l] for l in range(m) if l != c])
                rows.append([math.factorial(j) * math.factorial(n - j) * et[j] for j in range(n + 1)])
            A = sp.Matrix(rows)
            hom = A[:, :n]            # coefficients of the unknowns e_n(s), .., e_1(s)
            rk_full = A.rank(); rk_hom = hom.rank()
            if rk_full > rk_hom:
                dim = None            # inconsistent: empty fibre
            else:
                dim = n - rk_hom
            want = None if d == m else n - d
            good = (dim == want) and (rk_full == d)
            allok &= good
            res.append(good)
    print(f"   m={m}: {len(res)} cases (all partitions of m, with and without a zero value): rank of the conditions = d and "
          f"fibre dimension = n-d (empty for d=m) in every case: {all(res)}")
print("ALL CHECKS PASSED" if allok else "SOME CHECK FAILED")
```
