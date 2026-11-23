# Is the 4 x 4 permanent an exact sum of five split products? No.

**Update (same day): the final statement is now proved in Lean.** `not_mixedSplit_perm_four_five`
and `mixedSplit_perm_four_iff` in `lean/PvsNP/FourByFourExact.lean` (with the files
`FourByFourExactBase`, `A`, `Pencil`, `B`, `C`; no `sorry`, standard axioms only) state that over any
field of characteristic zero the 4 x 4 permanent is a sum of n split products if and only if
n >= 6. The Lean proof follows this note for the patterns (5,0,0), (4,1,0), (3,1,1) and (2,2,1),
with several lemmas replaced by weaker statements that suffice, and uses a different argument
for (3,2,0). Sentences below saying that nothing is checked in Lean describe the state of the
note when it was written.

**Status.** No. The pattern (2,2,1), which was open, is impossible: `perm_4` is not an exact sum
of two split products of the pairing 01|23, two of 02|13 and one of 03|12 (Theorem 1 below: a
complete paper proof, every computational ingredient checked in exact arithmetic by
`pequalnp/exact4.py`, and the second half of the proof re-proved independently by an exhaustive
machine enumeration). The three paper proofs in the docstring of `t3()` / `p410()` in `lower4.py`
(patterns (4,1,0), (3,2,0), (3,1,1)) were refereed step by step and are **correct**; a few steps
that were stated without proof are filled in below and machine-checked. Pattern (5,0,0) is
excluded by the flattening rank 6. Hence (Theorem 2): over any field of characteristic 0 the
4 x 4 permanent is **not** a sum of five split products, so its exact mixed split rank at k = 2
(its (2,2) partition rank) is **6**, while its border value is 5 (Lean, `FourByFourLower.lean`
and `FiveTerm.lean`). Nothing in this note is checked in Lean. Pattern (2,2,1) does admit limit
decompositions; Section 6 gives them in closed form (a new five-term limit identity, of a
different shape from `FiveTerm.lean`).

Level of each claim: "paper" = complete written argument below; "exact" = exact computer check
(sympy, rational arithmetic) by the named mode of `exact4.py`; "numerical" = floating point.

| pattern | exact decomposition | limit decomposition | source |
|---|---|---|---|
| (5,0,0) | no | no | flattening rank 6 |
| (4,1,0) | no | no | paper (Section 5.1), ingredients exact |
| (3,2,0) | no | not found (numerical, lower4.py) | paper (Section 5.2), ingredients exact |
| (3,1,1) | no | yes (`FiveTerm.lean`) | paper (Section 5.3), ingredients exact |
| (2,2,1) | **no (new)** | yes (Section 6, exact identity) | paper (Section 4) + exact enumeration |

## 0. Setting and notation

K is an algebraically closed field of characteristic 0 (the arguments use only: K infinite,
characteristic not 2 or 3; all computer checks are over Q). A decomposition over a subfield is
a decomposition over K, so the negative results hold over Q, R, C alike.

V = K^4 with basis e_0..e_3; `1` is the all-ones vector; `l*u` is the coordinatewise product;
T = {l : all l_i != 0} is the torus. Rows of the matrix are r_0..r_3 in V and
perm(r_0, r_1, r_2, r_3) is symmetric in its four arguments. A bilinear form Phi on V x V is
identified with its matrix, Phi(x, y) = sum Phi[i,j] x_i y_j; Phi^T(x, y) = Phi(y, x);
E_ij(x, y) = x_i y_j; alt_ab = E_ab - E_ba; s_ab = E_ab + E_ba. For a 2-subset {a,b} of
{0,1,2,3}, {c,d} always denotes its complement.

A split product of the pairing 01|23 is F(r_0,r_1) G(r_2,r_3); of 02|13: X(r_0,r_2) Y(r_1,r_3);
of 03|12: X'(r_0,r_3) Y'(r_1,r_2), with bilinear factors. (By `SplitBridge.lean` nothing changes
if the factors are allowed to be arbitrary functions of their two rows.) Pattern (a,b,c) means
a, b, c terms of the three pairings; row permutations permute the pairings arbitrarily and fix
perm, so only the multiset {a,b,c} matters.

**The slice matrix.** For l, u in V let B^l_u be the bilinear form (x, y) -> perm(l, u, x, y) and
B_u = B^1_u. Then

1. B^l_u is symmetric with zero diagonal and B^l_u[c,d] = l_a u_b + l_b u_a for c != d.
2. For l in T: B^l_u = (prod l) D^-1 B_{u/l} D^-1 with D = diag(l). So rank B^l_u = rank B_{u/l}
   and ker B^l_u = l * ker B_{u/l}.
3. A symmetric matrix with zero diagonal and rank <= 1 is zero; and B^l_u = 0 means
   l_p u_q + l_q u_p = 0 for all p != q.

(exact: `exact4.py p221`, first two lines.)

## 1. Two lemmas on the quartic surface det B_u = 0

**Lemma R (ten nodes).** rank B_u <= 1 only for u = 0, and rank B_u <= 2 exactly when u is a
multiple of one of n_ab = e_a - e_b (six "pair" nodes) or m_a = 1 - 2 e_a (four "star" nodes).
For l in T:

* u = l*n_ab = l_a e_a - l_b e_b:  B^l_u = a_l (x) b_l + b_l (x) a_l with a_l = l_a e_b - l_b e_a,
  b_l = l_d e_c + l_c e_d;
* u = l*m_a:  B^l_u = e_a (x) b_l + b_l (x) e_a with b_l = 2 sum_{j != a} (prod_{i != a,j} l_i) e_j.

(exact: `lower4.py lemma` by branching on linear factors; independently `exact4.py referee`,
which solves the 3 x 3 minors in the four charts u_i = 1 and certifies completeness of the
solution set, see Section 7.)

**Lemma L (sixteen lines).** det B_u = -4 sigma(u) with sigma = e_1 e_3 - 4 e_4 (elementary
symmetric polynomials of u_0..u_3). The 2-dimensional subspaces of V on which sigma vanishes are
exactly sixteen:

* six coordinate planes  C_ab = span(e_a, e_b);
* six pair planes  Lam_ab = span(e_a + e_b, e_c - e_d) = {u_a = u_b, u_c + u_d = 0}
  (Lam_ab = ker B_{n_ab}; note Lam_ab != Lam_cd);
* four star planes  Sig_a = {u_a = 0, sum u = 0} (= ker B_{m_a}).

No 3-dimensional subspace lies in {sigma = 0}. For p = s(e_a + e_b) + t(e_c - e_d) in Lam_ab,
B_p (e_a - e_b) = 0 and the principal minor of B_p on (a, c, d) is 4 s (s^2 - t^2), so
rank B_p = 3 with kernel K(e_a - e_b) for generic p in Lam_ab.

*Proof (paper; coefficients exact by `exact4.py lines`).* Projectively: lines L on the quartic
surface S = {sigma = 0} in P^3. On the coordinate plane u_3 = 0, sigma = u_0 u_1 u_2 (u_0+u_1+u_2);
so the lines of S inside a coordinate plane are the coordinate lines and the star line of that
plane: 6 + 4 lines in total. Let L not lie in a coordinate plane, and let ell_i be the restriction
of u_i to L, a nonzero linear form on L = P^1 with a single root p_i. If p_i is the root of no
other ell_j, then at p_i: e_4 = 0 and e_3 = prod_{j != i} ell_j != 0, hence e_1(p_i) = 0. If this
happened for two indices, the linear form e_1 restricted to L would have two roots, so e_1 = 0 on
L, then e_4 = 0 on L and some ell_j = 0: excluded. So at most one root is unshared, and the
pattern of coincidences among p_0..p_3 is {2,2}, {3,1} or {4}. {4} means that the four ell_i are
proportional: not a line. {3,1}: ell = (alpha x, beta x, gamma x, delta y) in suitable coordinates
(x, y) of L, all coefficients nonzero; the x^4 coefficient of sigma is
alpha beta gamma (alpha+beta+gamma), so gamma = -alpha-beta, and then the x^3 y coefficient is
3 alpha beta delta (alpha+beta) = -3 alpha beta gamma delta != 0: impossible. {2,2}:
ell = (alpha x, beta x, gamma y, delta y) on indices (a, b, c, d); the coefficients of x^3 y,
x^2 y^2, x y^3 are alpha beta (alpha+beta)(gamma+delta), (alpha delta + beta gamma)(alpha gamma
+ beta delta), gamma delta (alpha+beta)(gamma+delta). So beta = -alpha or delta = -gamma; if
beta = -alpha the middle coefficient is -alpha^2 (gamma-delta)^2, so gamma = delta and
L = {u_a + u_b = 0, u_c = u_d} = Lam_cd; symmetrically delta = -gamma gives Lam_ab. So six more
lines, sixteen in all. A plane inside S would contain infinitely many lines. The last sentence
of the lemma is a direct computation (`exact4.py p221`, line "kernel"). QED

*Independent exact check* (`exact4.py lines`): in each of the six standard charts of the
Grassmannian of 2-planes, p = e_i + a e_k + b e_m, q = e_j + c e_k + d e_m, the five coefficients
of sigma(s p + t q) generate a zero-dimensional ideal in Q[a,b,c,d] whose zero set consists of
exactly 7 rational points (certified as in Section 7); the union over the charts is the list of
16 planes above.

## 2. The structure lemma for a doubled pencil

Let S_{ab|cd} = span(alt_ab, s_cd) (a transpose-invariant 2-dimensional space of forms; there are
six of them, one for each 2-subset {a,b}), and
N_ab = {Theta : Theta(l, l_a e_a - l_b e_b) = 0 for all l}.

**Lemma N.** N_ab = {f s_ab + Theta' : Theta'(., e_a) = Theta'(., e_b) = 0}: columns a and b of
Theta are those of a multiple of s_ab. Consequently S_{a'b'|c'd'} is contained in N_ab if and
only if {a',b'} = {c,d}.

*Proof.* Theta(l, l_a e_a - l_b e_b) = sum_i Theta[i,a] l_i l_a - sum_i Theta[i,b] l_i l_b vanishes
identically iff Theta[a,a] = Theta[b,b] = 0, Theta[i,a] = Theta[i,b] = 0 for i in {c,d}, and
Theta[b,a] = Theta[a,b]. The matrix alt_{a'b'} satisfies this only for {a',b'} = {c,d}, and
then s_ab does too. (exact: `exact4.py types`.) QED

**Lemma S.** Let Phi_1, Phi_2 be bilinear forms on V x V such that

  (*) for every l in T and every u with Phi_1(l,u) = Phi_2(l,u) = 0:  det B^l_u = 0.

Then exactly one of the following holds.

* **(S)** span(Phi_1, Phi_2) = S_{ab|cd} for some 2-subset {a,b}. Then for l in T the common zero
  set of Phi_1(l,.), Phi_2(l,.) is l*Lam_ab, and for generic u in it rank B^l_u = 3 and
  ker B^l_u = K (l*n_ab) = K (l_a e_a - l_b e_b).
* **(C)** there are a != b with Phi_v(x, e_a) = Phi_v(x, e_b) = 0 for all x and v = 1, 2 (columns
  a and b of both forms vanish).

*Proof.* For l in T let U(l) = {u : Phi_1(l,u) = Phi_2(l,u) = 0}, a subspace of dimension >= 2.
By (*) and fact 2, sigma vanishes on l^-1 * U(l). By Lemma L, dim U(l) = 2 and l^-1 * U(l) is one
of the sixteen planes Lam_1..Lam_16. For each j the set
Z_j = {l in V : Phi_v(l, l*p) = 0 for all p in Lam_j, v = 1, 2} is Zariski closed (it is cut out by
quadrics in l), and T is contained in the union of the Z_j. V is irreducible and T is dense, so
Z_j = V for some j. It remains to compute T(Lam) = {Phi : Phi(l, l*p) = 0 for all l and p in Lam}.
Since Phi(l, l*p) = sum_{i,k} Phi[i,k] p_k l_i l_k, the condition is Phi[i,i] p_i = 0 and
Phi[i,k] p_k + Phi[k,i] p_i = 0 (i != k) for p in a basis of Lam:

* Lam = C_ab (p = e_a, e_b): columns a and b of Phi vanish. This is (C).
* Lam = Lam_ab (p = e_a + e_b, e_c - e_d): Phi in span(alt_ab, s_cd). Both Phi_v lie in this
  2-dimensional space and are independent (otherwise dim U(l) >= 3), so they span it. The common
  zero set of alt_ab(l,.) and s_cd(l,.) is {l_a u_b = l_b u_a, l_c u_d + l_d u_c = 0} = l*Lam_ab;
  rank and kernel come from Lemma L and fact 2. This is (S).
* Lam = Sig_a (p = e_b - e_c with b, c != a): all columns of Phi except column a vanish, so
  Phi_v(l, u) = phi_v(l) u_a and U(l) contains the hyperplane u_a = 0: contradiction.

(exact: `exact4.py types` computes T(Lam) for the sixteen planes.) QED

## 3. Frames

Assume an exact decomposition of pattern (2,2,1):

  perm(r_0,r_1,r_2,r_3) = sum_{v=1,2} F_v(r_0,r_1) G_v(r_2,r_3) + sum_{v=1,2} X_v(r_0,r_2) Y_v(r_1,r_3)
                          + X'(r_0,r_3) Y'(r_1,r_2).                                        (D)

Call two rows *linked* if they form a block of a doubled pairing (01, 23, 02, 13: the 4-cycle
0 - 1 - 3 - 2 - 0); the unlinked pairs 03, 12 are the blocks of the single pairing. A *frame* is
(i, j, k, m) with i linked to j and to k, and m the remaining row (so {i,m}, {j,k} are unlinked).
In a frame (D) reads

  perm = sum_v Phi_v(r_i,r_j) Phi'_v(r_k,r_m) + sum_v Psi_v(r_i,r_k) Psi'_v(r_j,r_m)
         + Omega(r_i,r_m) Omega'(r_j,r_k),                                                   (D')

where each form is one of the given ones or its transpose. The frames used below:

| frame (i,j,k,m) | Phi | Psi | Psi' | Omega | Omega' |
|---|---|---|---|---|---|
| (0,1,2,3) | F | X | Y | X' | Y' |
| (0,2,1,3) | X | F | G | X' | Y'^T |
| (1,0,3,2) | F^T | Y | X | Y' | X' |
| (1,3,0,2) | Y | F^T | G^T | Y' | X'^T |

Three facts hold in every frame.

**(a) Slice.** Put r_i = l and r_j = u with Phi_1(l,u) = Phi_2(l,u) = 0. Then, as a bilinear form
in (r_k, r_m),

  B^l_u = Psi_1(l,.) (x) Psi'_1(u,.) + Psi_2(l,.) (x) Psi'_2(u,.) + Omega'(u,.) (x) Omega(l,.),

a sum of three rank-one forms. So det B^l_u = 0, the pair (Phi_1, Phi_2) satisfies (*), and
Lemma S applies to it.

**(b) Type (C) is impossible.** Suppose Phi_v(x, e_a) = Phi_v(x, e_b) = 0 for all x, v. Put
r_j = l = x e_a + y e_b with x y != 0: the Phi-terms vanish. Choose u with
Psi'_1(l,u) = Psi'_2(l,u) = 0 (a space of dimension >= 2) and put r_m = u: (D') becomes
perm(r_i, l, r_k, u) = Omega(r_i, u) Omega'(l, r_k), a form of rank <= 1 in (r_i, r_k). This form is
B^l_u, so by fact 3 it is zero and l_p u_q + l_q u_p = 0 for all p != q: (p,q) = (a,c), (a,d) give
u_c = u_d = 0 and (a,b) gives x u_b + y u_a = 0. So u lies on one line, contradicting
dimension >= 2. (exact: `exact4.py p221`, line "fact (b)".)

**(c) Kernel.** If span(Phi_1, Phi_2) = S_{ab|cd}, then Psi_1, Psi_2 and Omega all lie in N_ab.
Indeed take l in T and u generic in l*Lam_ab: by Lemma S, B^l_u has rank exactly 3 and both its
kernels are spanned by k = l*n_ab. A rank-3 sum of three rank-one forms alpha_t (x) beta_t has
independent alpha's and independent beta's; so B^l_u(k, .) = sum alpha_t(k) beta_t = 0 forces
alpha_t(k) = 0 for all t, in particular Psi_v(l, k) = 0; and B^l_u(., k) = 0 forces beta_t(k) = 0,
in particular Omega(l, k) = 0. These hold for all l in T, hence identically.

(The bookkeeping of (a) and (c), i.e. which covectors appear on which side in each of the eight
frames, is checked on a random integer tensor of pattern (2,2,1): `exact4.py frames`.)

## 4. Theorem 1: no exact decomposition of pattern (2,2,1)

**Theorem 1.** There are no bilinear forms F_v, G_v, X_v, Y_v (v = 1, 2), X', Y' on K^4 x K^4
satisfying (D).

*Proof.* Assume (D).

Step 1. By (a), (b) and Lemma S in the frame (0,1,2,3): span(F_1, F_2) = S_{ab|cd} for some
2-subset {a,b}. In the frame (0,2,1,3): span(X_1, X_2) = S_{a'b'|c'd'}. In the frame (1,3,0,2):
span(Y_1, Y_2) = S_{a''b''|c''d''}.

Step 2. By (c) in the frame (0,1,2,3): X_v in N_ab. By Lemma N, {a',b'} = {c,d}:
span(X_1, X_2) = S_{cd|ab}. The pencil of the F_v^T is also S_{ab|cd} (transpose-invariant), so
(c) in the frame (1,0,3,2) gives Y_v in N_ab, hence span(Y_1, Y_2) = S_{cd|ab}.

Step 3. By (c) in the frame (0,2,1,3), where Phi = X spans S_{cd|ab} and Omega = X':
X' in N_cd. So columns c and d of X' are those of a multiple of s_cd; in particular
X'[a,c] = X'[a,d] = 0.

Step 4. Compare the coefficients of (D) at the two permutations (j_0,j_1,j_2,j_3) = (a,c,b,d) and
(a,d,b,c), where perm has coefficient 1. The F-terms contribute F_v[a,c] G_v[b,d] and
F_v[a,d] G_v[b,c], which vanish because F_v in span(alt_ab, s_cd). The last term contributes
X'[a,d] Y'[c,b] and X'[a,c] Y'[d,b], which vanish by Step 3. So

  1 = sum_v X_v[a,b] Y_v[c,d]   and   1 = sum_v X_v[a,b] Y_v[d,c].

But Y_v in span(alt_cd, s_ab) gives Y_v[d,c] = -Y_v[c,d]: the two right-hand sides are opposite.
Contradiction. (exact: `exact4.py p221`, line "Step 4", with G_v and Y' left arbitrary.) QED

**Independent machine proof of Theorem 1 from Lemma S alone** (`exact4.py enum`, exact). By
Lemma S applied in all eight frames, each of the four doubled pencils (F, G, X, Y) is, as a
space of matrices, either S_{ab|cd} or contained in the matrices supported on a 2 x 2 block R x C
(type (C) for both arguments; a pencil of type (S) for one argument is S_{ab|cd} itself). That
leaves 39 possible supports per pencil (3 pairing supports, 36 blocks), 39^4 = 2 313 441 cases.
Writing A, B for the sums of the terms of 01|23 and 02|13, T = perm - A - B must have rank <= 1 in
the flattening 03|12. A necessary combinatorial condition (if O is the set of ones of perm outside
supp A u supp B, every zero of perm in rows(O) x cols(O) must lie in supp A u supp B) leaves
exactly 3 cases: all four pencils supported on the positions of the same column pairing. For
each of these and each of the 16 choices S_{ab|cd} / S_{cd|ab} for the four pencils, A and B range
over 4-dimensional linear spaces and the 2 x 2 minors of T (polynomials in 8 unknowns) generate
the unit ideal of Q[a_0..a_3, b_0..b_3] (Groebner basis = {1}). This check does not use (b), (c)
or Steps 2-4. (Control of the pipeline: for a target tensor built as A + B + (rank one for 03|12)
with planted coefficients, the same code returns a proper ideal vanishing at the planted point.)

## 5. Referee report on the paper proofs in lower4.py

Verdict for all three: **correct**. No step is wrong. The points a skeptical reader would ask
about are listed with each proof; all of them hold and are machine-checked.

Common ingredient ("type of a triple"), used in 5.2 and 5.3. Let three forms F_1, F_2, F_3 on the
rows (i, j) be such that for l in T every common zero u of the F_v(l,.) has rank B^l_u <= 2. Then
there is ONE node n (one of the ten of Lemma R, the "type") with F_v(l, l*n) = 0 for all l and v.
*Proof.* The common zero space K(l) is nonzero (three linear forms in four variables), and by
Lemma R and fact 2 it is contained in the union of the ten lines K(l*n); a subspace inside a
finite union of lines is one of the lines. The ten conditions Z_n = {l : F_v(l, l*n) = 0 for
v = 1,2,3} are Zariski closed and cover the dense subset T of the irreducible V, so one Z_n is
everything. (This is the "one type holds for all l" step; it is fine.)

For a type n let W_n = {Xi : Xi(l,.) in span(a_l, b_l) for all l in T} with a_l, b_l as in Lemma R.
**Lemma W.** For a pair type (a,b): W = span(alt_ab, s_cd). For a star type a: W = {xi (x) e_a},
the forms xi(x) y_a. (The lower4 docstring uses this without proof; the coefficients of a_l, b_l
could a priori depend on l.) *Proof.* Pair: Xi(l,.) = lam(l) a_l + mu(l) b_l gives
Xi(l,e_b) = lam l_a and Xi(l,e_a) = -lam l_b; both are linear forms in l and
l_b Xi(l,e_b) = -l_a Xi(l,e_a), so Xi(l,e_b) = kappa l_a with kappa constant: lam is constant;
likewise mu. Star: for the three j != a, Xi(l,e_j) = 2 mu(l) prod_{i != a,j} l_i, so
l_j Xi(l,e_j) does not depend on j; unique factorisation forces Xi(l,e_j) = 0. (exact:
`exact4.py referee` solves the linear system "all 3 x 3 minors of (Xi^T l, a_l, b_l) vanish
identically in l".) QED

So, as the task statement suspected, a single slice X(l,.) is only forced into the
two-dimensional span(a_l, b_l) (pair type) or into a multiple of e_a (star type), never into a
single form; the proofs below use exactly this and no more.

Intersections (exact: `referee`): W_pair is transpose-invariant; W_n n W_n'^T is 2-dimensional
if n = n' is a pair type, 0 for two different pair types and for a pair and a star type, and
K E_{a'a} for star types a, a'. A nonzero element of a pair-type W has rank 2 or 4.

### 5.1 Pattern (4,1,0): correct (and it excludes limits too)

Claim: perm is not a limit of sums of four products F_v(r_0,r_1) G_v(r_2,r_3) plus one product
X(r_0,r_2) Y(r_1,r_3). Proof as in `p410()`: let L0 = span(1, e_0) and let L2 be a plane inside
{r_2 : X(1,r_2) = X(e_0,r_2) = 0}. On (L0 (x) V) x (L2 (x) V) the last product vanishes, so perm
restricted there has rank <= 4. (For limits: the planes L2 of the approximants have a convergent
subsequence in the Grassmannian, and rank <= 4 is closed.) But (a) the forms perm(r_0, r_1, ., .)
with r_0 in L0 span all six-dimensional space of symmetric zero-diagonal forms [r_0 = e_0,
r_1 = e_i gives s_jk with {j,k} = {1,2,3} minus i; r_0 = 1, r_1 = e_i gives the sum of the three
s_jk avoiding i]; and (b) for every plane L2 the symmetric zero-diagonal B with B(L2,.) = 0 form
a space of dimension <= 1 [B is a quadratic form on V/L2 = K^2 vanishing at the images of
e_0..e_3, which span K^2; a binary quadric vanishing at two independent vectors is a multiple of
the product of their two dual coordinates]. So the rank is >= 6 - 1 = 5. Contradiction.
Checked: every step re-derived; (a) rank 6 and (b) unit ideal of the 5 x 5 minors in the six
charts recomputed in `exact4.py referee`.

### 5.2 Pattern (3,2,0): correct

Assume perm = sum_{v=1..3} F_v(r_0,r_1) G_v(r_2,r_3) + sum_{i=1,2} X_i(r_0,r_2) Y_i(r_1,r_3).
For l in T and u a common zero of the F_v(l,.), B^l_u = sum_i X_i(l,.) (x) Y_i(u,.) has rank <= 2,
so the triple has a type n. For u = l*n, B^l_u has rank exactly 2 (Lemma R), so X_1(l,.), X_2(l,.)
are independent and span span(a_l, b_l): X_i in W_n and the X_i(l,.) are independent for every
l in T. A star type is impossible (both X_i(l,.) would be multiples of e_a). So n = n_ab,
X_i in span(alt_ab, s_cd) and F_v in N_ab. Now put r_0 = e_c, r_2 = e_a: alt_ab(e_c,e_a) =
s_cd(e_c,e_a) = 0, and F_v(e_c, r_1) = sum_j F_v[c,j] r_1j does not involve r_1a, r_1b (Lemma N);
but perm(e_c, r_1, e_a, r_3) = r_1b r_3d + r_1d r_3b does. Contradiction.
Points checked: the type step; Lemma W (unstated in the docstring); independence of the two
slices (from rank exactly 2); the final evaluation (exact, `referee`).

### 5.3 Pattern (3,1,1): correct

Assume perm = sum_{v=1..3} F_v(r_0,r_1) G_v(r_2,r_3) + X(r_0,r_2) Y(r_1,r_3) + X'(r_0,r_3) Y'(r_1,r_2).
There are four triples with a fixed row, each with a type:

* t1: F_v(l,.), r_0 = l, r_1 = u:  B^l_u = X(l,.) (x) Y(u,.) + Y'(u,.) (x) X'(l,.) in (r_2, r_3);
* t2: F_v(.,l), r_1 = l, r_0 = u:  B^l_u = X(u,.) (x) Y(l,.) + Y'(l,.) (x) X'(u,.) in (r_2, r_3);
* t3: G_v(l,.), r_2 = l, r_3 = u:  B^l_u = X(.,l) (x) Y(.,u) + X'(.,u) (x) Y'(.,l) in (r_0, r_1);
* t4: G_v(.,l), r_3 = l, r_2 = u:  B^l_u = X(.,u) (x) Y(.,l) + X'(.,l) (x) Y'(.,u) in (r_0, r_1).

Each B^l_u has rank exactly 2 = a_l (x) b_l + b_l (x) a_l, so in each line both products are
nonzero and each of the four covectors lies in span(a_l, b_l). Reading off the covectors that
depend on l only: X, X' in W_t1; Y, Y' in W_t2; X^T, Y'^T in W_t3; X'^T, Y^T in W_t4; and all of
X, X', Y, Y' are nonzero. By the table of intersections, X in W_t1 n W_t3^T, X' in W_t1 n W_t4^T,
Y in W_t2 n W_t4^T, Y' in W_t2 n W_t3^T force: either all four types are the same pair (a,b), or
all four are star types.

*Stars.* Each of X, X', Y, Y' is a multiple of a matrix unit, so both extra products are
monomials, i.e. rank-one tensors, and the flattening rank of perm for 01|23 would be
<= 3 + 1 + 1 < 6.

*Pair (a,b).* X, X', Y, Y' in span(alt_ab, s_cd), and F_v in N_ab n N_ab^T = {f s_ab + (block
cd x cd)}. Coefficients of the identity at (a,c,b,d) and (b,c,a,d): F_v[a,c] = F_v[b,c] = 0,
X'[a,d] = X'[b,d] = 0, so 1 = X[a,b] Y[c,d] and 1 = X[b,a] Y[c,d] = -X[a,b] Y[c,d]. Contradiction.
(The docstring phrases the same contradiction as "s_ab(r_0,r_2) s_cd(r_1,r_3) is not a multiple
of alt_ab(r_0,r_2) s_cd(r_1,r_3)".)

Points checked: the docstring argues the star case by fixing the rows one after the other
("constant direction, which only a star type allows"); this is the statement
W_star n W_pair^T = 0 above and is correct. The remark "p1 q2 + p2 q1 = 0" in the docstring is
true but not used. Everything is exact in `exact4.py referee`.

### 5.4 Theorem 2

**Theorem 2.** Over a field of characteristic 0 the 4 x 4 permanent is not a sum of five split
products (any pairings, bilinear or arbitrary factors). Its mixed split rank at k = 2, i.e. its
(2,2) partition rank, equals 6 (Laplace), and its border value is 5.

*Proof.* A sum of five products has pattern (5,0,0), (4,1,0), (3,2,0), (3,1,1) or (2,2,1) up to a
row permutation; zero terms are allowed in all the arguments, so fewer than five terms are
covered as well. (5,0,0): flattening rank 6. The others: Sections 5.1-5.3 and Theorem 1. The
border statement is `not_tendsto_sum_four_isSplit` and `permanent_sub_eq_five_split` (Lean). QED

So perm_4, a 4 x 4 x 4 x 4 tensor with entries 0 and 1, has (2,2) partition rank 6 strictly above
its border (2,2) partition rank 5, with the gap certified by paper proofs plus exact computer
checks (not by Lean). Terminology: only splits of the four rows into 2 + 2 are allowed here. The
unrestricted partition rank (splits 1 + 3 allowed as well) of perm_4 is at most 4, by Laplace
expansion along one row, so the statement is about the (2,2) type only. Whether an explicit
tensor with such a gap was known before has not been checked against the literature.

## 6. Limit decompositions of pattern (2,2,1), in closed form

Let s_I = s_01, s_II = s_23, alt_I = alt_01 (bilinear forms of two rows: s_I(x,y) = x_0 y_1 + x_1 y_0
is the 2 x 2 permanent on the first two columns, etc.).

**Identity A** (exact, `exact4.py limit`; also checked on random rational matrices). Let
c_1 + c_2 + c_3 = 0 with all c_i != 0, and q_c = s_I + (lam/c) s_II. Then for all lam

    c_1 q_{c_1}(r_0,r_1) q_{c_1}(r_2,r_3) + c_2 alt_I(r_0,r_1) alt_I(r_2,r_3)
  + c_2 q_{c_2}(r_0,r_2) q_{c_2}(r_1,r_3) + c_1 alt_I(r_0,r_2) alt_I(r_1,r_3)
  + c_3 q_{c_3}(r_0,r_3) q_{c_3}(r_1,r_2)
  = lam perm(r_0,r_1,r_2,r_3)
    + lam^2 [ s_II(r_0,r_1) s_II(r_2,r_3)/c_1 + s_II(r_0,r_2) s_II(r_1,r_3)/c_2 + s_II(r_0,r_3) s_II(r_1,r_2)/c_3 ].

The left side is a sum of five split products of pattern (2,2,1). Dividing by lam:
perm = lim_{lam -> 0} (1/lam) (the five products), the error being lam times a fixed tensor. With
c = (1, 1, -2) everything is rational:

  perm = lim (1/lam) [ (s_I + lam s_II)(r_0,r_1) (s_I + lam s_II)(r_2,r_3) + alt_I(r_0,r_1) alt_I(r_2,r_3)
                     + (s_I + lam s_II)(r_0,r_2) (s_I + lam s_II)(r_1,r_3) + alt_I(r_0,r_2) alt_I(r_1,r_3)
                     - 2 (s_I - (lam/2) s_II)(r_0,r_3) (s_I - (lam/2) s_II)(r_1,r_2) ].

Why it works: at order lam^0 the left side is
c_1 s_I s_I (01|23) + c_2 s_I s_I (02|13) + c_3 s_I s_I (03|12) + c_2 alt_I alt_I (01|23) + c_1 alt_I alt_I (02|13),
which vanishes when c_1 + c_2 + c_3 = 0, by the two identities for 2 x 2 blocks
s(01)s(23) - alt(01)alt(23) = s(02)s(13) - alt(02)alt(13) and
2 s(03)s(12) = s(01)s(23) + alt(01)alt(23) + s(02)s(13) + alt(02)alt(13); at order lam^1 each pairing {S, S^c}
contributes s_I(S) s_II(S^c) + s_II(S) s_I(S^c), and the sum over the three pairings is perm.
This is the two-block model of `twoblock.py` with the two extra terms on two different pairings
(extras of pattern (1,1,0)); in `FiveTerm.lean` both extras sit on the same pairing (pattern
(3,1,1)) and the error is a single product.

**Identity B, the general family** (exact, `exact4.py limit`). Parameters c_3, p, q with
c_3 (c_3^2 - p q) != 0; D = c_3^2 - p q, phi_1 = -(c_3+q)/D, phi_2 = -(c_3+p)/D, psi_1 = (q-c_3)/D,
psi_2 = (p-c_3)/D:

    (E_01 + lam phi_1 s_II)(r_0,r_1) (-c_3 E_01 + p E_10 + lam s_II)(r_2,r_3)
  + (E_10 + lam phi_2 s_II)(r_0,r_1) ( q E_01 - c_3 E_10 + lam s_II)(r_2,r_3)
  + (E_01 + lam psi_1 s_II)(r_0,r_2) (-c_3 E_01 - p E_10 + lam s_II)(r_1,r_3)
  + (E_10 + lam psi_2 s_II)(r_0,r_2) (-q E_01 - c_3 E_10 + lam s_II)(r_1,r_3)
  + c_3 (s_I + (lam/c_3) s_II)(r_0,r_3) (s_I + (lam/c_3) s_II)(r_1,r_2)
  = lam perm + lam^2 [ (phi_1+phi_2) s_II s_II (01|23) + (psi_1+psi_2) s_II s_II (02|13) + (1/c_3) s_II s_II (03|12) ].

Identity A is the case p = q = c_1 - c_2, c_3 = -c_1 - c_2 (written in the basis s_I, alt_I instead
of E_01, E_10). The order-zero parts are forced by the block structure: on the first column
block, the 01|23 part must be -c_3 (E_01 (x) E_01 + E_10 (x) E_10) + p E_01 (x) E_10 + q E_10 (x) E_01
and the 02|13 part the same with p, q replaced by -p, -q, in order to cancel c_3 s_I (x) s_I of
the single pairing.

*What the numerical fits do* (numerical evidence, `python3 exact4.py fit 4 3`; complex factors,
Levenberg-Marquardt from random starts). Three of the four starts reach residual 7e-8 with terms
of size 2.7e3, the fourth stalls at residual 0.083 (with seed 11 all three starts stall, at
0.083-0.125). The three converging runs land in the family above, each on a different column
block ({1,3}, {0,3}, {2,3} in place of {0,1}): the two terms of 01|23 add up to a tensor of which
99.89% of the mass sits on the four entries of that block, with ratios
(A[abab], A[baba], p, q)/c_3 = (-1.0000, -1.0000, -1.6693, 1.6693), and residual * size^2 = 0.520
at every checkpoint of the run (residual = |sum - P|^2/|P|^2, size = max |F||G| over the terms).
For the family this constant is an explicit function of (p/c_3, q/c_3): on the subfamily
p = -q = t c_3 it equals (2 - 8/D + 24/D^2)/3 for D = 1 + t^2 <= 4 and (2D - 8 + 24/D)/12 for
D >= 4, which is 0.520 at t = 1.6693 and has its minimum 1/2 at t = sqrt 3 (the member checked
in `exact4.py limit`); a numerical minimisation over complex (p, q) did not go below 1/2. I did
not prove that every limit decomposition of this pattern is of this form up to the symmetries
of perm (column permutations and scalings, row permutations preserving the pattern).

*Relation with Theorem 1.* As lam -> 0 each doubled pencil of the family tends to span(E_01, E_10),
which is of type (C) of Lemma S (the limiting common zero set is the coordinate plane C_23).
Fact (b) of Section 3 shows that type (C) cannot occur in an exact decomposition; in the limit
family the single term escapes this because its size goes to infinity.

## 7. What is machine-checked, and how

`python3 exact4.py all` runs every exact mode (under a minute). All arithmetic is exact (sympy over Q).

* `lines`: det B_u = -4 (e_1 e_3 - 4 e_4); the 16 planes lie on S; the coefficients used in the
  hand proof of Lemma L; and, independently, in each of the six charts of the Grassmannian the
  zero set of the ideal is exactly the expected 7 points.
* `types`: T(Lam) for the sixteen planes (Lemma S); N_ab; Lemma N.
* `frames`: bookkeeping of the eight frames on a random integer tensor of pattern (2,2,1).
* `p221`: facts 1-2; fact (b); the kernel and rank on Lam_ab; Step 4 with symbolic factors.
* `enum`: the independent machine proof of Theorem 1 from Lemma S (3 of 2 313 441
  support cases survive the combinatorial test; 48 Groebner bases equal to {1}).
* `referee`: Lemma R with certificate; the forms a_l (x) b_l + b_l (x) a_l; Lemma W; N for pair
  types; the table of intersections; the final contradictions of 5.2 and 5.3; (a), (b) of 5.1.
* `limit`: Identities A and B on all 256 entries with symbolic parameters.
* `fit` (numerical evidence only, needs `lower4.py`, a few minutes): the fits of pattern (2,2,1).

*Completeness certificate for finite zero sets* (used for Lemma L and Lemma R). To prove that
the zero set of polynomials f_1..f_r in Q[x_1..x_n] is exactly a given finite set E of rational
points: for each variable x_k let g_k = prod (x_k - v) over the values v taken by x_k on E; the
script checks that the Groebner basis of (f_1, .., f_r, 1 - z g_k) is {1} (so g_k vanishes on the
whole zero set, over the algebraic closure), and then tests every point of the finite grid of
admissible coordinate values by substitution.

Not machine-checked: the logical skeleton of the proofs (irreducibility step in Lemma S and in
the type lemma; the deductions in Sections 3-5). No Lean. A Lean formalisation of Theorem 1
would need the density argument of Lemma S in an elementary form (for instance: the product of
the sixteen families of quadrics vanishes identically, hence one factor family does) and
Lemma L; the rest is finite linear algebra.

## 8. Remarks

* Nothing in the earlier material was found to be wrong. One number is sharpened: the constant
  "residual * size^2 = 1/2" quoted for the fits of pattern (2,2,1) is 0.520 in the runs made
  here; 1/2 is the minimum of that constant over the closed-form family.
* The same slice technique gives the earlier patterns a uniform reading: a pairing carrying
  three terms sees the ten nodes of S (rank <= 2), a pairing carrying two terms sees the sixteen
  lines of S (rank <= 3), and a single term must then fit into the rank-2 or rank-3 forms left
  over.
* An attempted numerical falsification of Lemma S was uninformative and is not part of the
  evidence: minimising sum |det B^l_u|^2 over random pencils (BFGS and Levenberg-Marquardt, 70
  random complex starts) never reached a pencil satisfying (*), not even one of the known types
  (S) and (C), so it neither supports nor contradicts the lemma. The lemma rests on its proof
  and on the exact checks `lines`, `types`.
* Not attempted here: the analogous exactness question for perm_6 at k = 3; a Lean
  formalisation.
