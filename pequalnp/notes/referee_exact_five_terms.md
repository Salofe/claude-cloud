# Referee report on `exact_five_terms_4x4.md`

Independent adversarial referee report. The referee did not write the note and was asked to try
to break it.

**Claim refereed.** Over a field of characteristic 0 the 4 x 4 permanent is not an exact sum of
five split products (a split product = a bilinear form in two rows times a bilinear form in the
other two rows), so the exact (2,2) value is 6 while the limit value is 5.

**Verdict.** I could not break it. Every step of Sections 0-5 of the note was re-derived by hand
and is correct; no step needs a repair that changes the mathematics (a few sentences should be
made more precise, Section 3 below). Every computational ingredient was recomputed with scripts
written independently of `exact4.py`, with the same results. Two different numerical searches
found no exact decomposition of pattern (2,2,1) (and do find exact decompositions in all the
control problems where one exists). My own work is paper proofs, exact computer checks and
numerics, not Lean.

**Lean status (not my work; spot-checked only).** While this report was being written, another
agent committed a Lean formalisation of the final statement
(`lean/PvsNP/FourByFourExact.lean` and five supporting files; the note now has an "Update"
paragraph about it). I did not read those files. I did run the top file read-only:
`cd pequalnp/lean && lake env lean <scratch copy of PvsNP/FourByFourExact.lean with three lines appended>`
with output

    'PvsNP.not_mixedSplit_perm_four_five' depends on axioms: [propext, Classical.choice, Quot.sound]
    'PvsNP.mixedSplit_perm_four_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
    @PvsNP.mixedSplit_perm_four_iff : ∀ {K : Type u_1} [inst : Field K] [CharZero K] (n : ℕ),
      (PvsNP.MixedSplitLE 2 n fun A => A.permanent) ↔ 6 ≤ n

This checks the top file against the stored compiled files of its five imports (each compiled
file is newer than its source, the sources are unchanged in git, and none of the six files
contains `sorry`, `axiom` or `native_decide`); I did not recompile the imports. So the claim
refereed here is, in addition, **proved in Lean** by that formalisation, which is independent of
my checks. According to the note the Lean proof follows the note for the patterns (5,0,0),
(4,1,0), (3,1,1), (2,2,1) and uses a different argument for (3,2,0); the rest of this report
referees the PAPER proofs as written.

Levels used below: **paper** = I re-derived the complete argument by hand; **exact** = exact
computer arithmetic (sympy over Q, or integers mod p); **numerical** = floating point.

| item of the note | verdict | level of my check |
|---|---|---|
| facts 1-3 on the slice matrix | correct | paper + exact |
| Lemma R (ten nodes) | correct (char 0) | exact, two methods |
| Lemma L (sixteen lines) | correct (any field of char not 2, 3; false in char 3) | paper + exact, three methods |
| Lemma N | correct | paper + exact |
| Lemma S | correct | paper + exact; numerical corroboration |
| frames, facts (a), (b), (c) | correct | paper |
| Theorem 1, Steps 1-4 | correct | paper + exact (Step 4) |
| machine proof of Theorem 1 from Lemma S (`enum`) | correct, reproduced | exact, own implementation |
| "type of a triple", Lemma W, intersection table | correct | paper + exact |
| 5.1 pattern (4,1,0) (also for limits) | correct | paper + exact |
| 5.2 pattern (3,2,0) | correct | paper + exact |
| 5.3 pattern (3,1,1) | correct | paper + exact |
| 5.4 Theorem 2 | correct | paper |
| Section 6, Identities A and B, the constant 1/2 | correct | exact (identities), numerical (constant) |
| Section 7, completeness certificate | correct | paper (logic) + independent recomputation |

## 1. Step-by-step verdicts (hand re-derivation)

Notation as in the note. B^l_u(x, y) = perm(l, u, x, y).

**Facts 1-3. Correct.** B^l_u[c,d] = l_a u_b + l_b u_a is immediate from the definition of perm.
Fact 2 is B^l_u[c,d] = l_a l_b (u_a/l_a + u_b/l_b); consequently ker B^l_u = l * ker B_{u/l}
(x is in the kernel of D^-1 B D^-1 iff D^-1 x is in ker B). Fact 3: a symmetric matrix of rank
one is c v v^T, and a zero diagonal forces v = 0; this holds over every field.

**Lemma R. Correct in characteristic 0.** Not proved by hand in the note (it is a computation).
My check (exact): the ideal of the 3 x 3 minors of B_u together with h(u) = 1, for a linear form
h not vanishing at the ten nodes, has quotient dimension exactly 10, and the ten nodes are ten
distinct zeros; so there is no other zero over the algebraic closure. The ideal (minors, h) has
finite quotient dimension, so nothing is lost at h = 0. The 2 x 2 minors have only the zero u = 0.
The two formulas a_l (x) b_l + b_l (x) a_l were re-derived by hand entry by entry and by sympy.
Finite-field count (plain enumeration, no Groebner basis): 10 projective points with
rank B_u <= 2 over F_9, F_25 and F_49.

**Lemma L. Correct, for every field of characteristic different from 2 and 3.** I re-derived the
hand proof line by line.
* On u_3 = 0: e_4 = 0 and e_3 = u_0 u_1 u_2, so sigma = u_0 u_1 u_2 (u_0+u_1+u_2): four lines per
  coordinate plane, 6 + 4 distinct lines in all.
* For a line in no coordinate plane the argument "at most one unshared root" is right; it uses
  characteristic not 2 (to pass from 4 e_4 = 0 to e_4 = 0) and the fact that two unshared roots are
  two DIFFERENT points (p_i is not a root of ell_i', so p_i != p_i').
* Root pattern {3,1}: I recomputed the coefficients. x^4: alpha beta gamma (alpha+beta+gamma);
  x^3 y: delta [ (alpha+beta+gamma)(alpha beta + alpha gamma + beta gamma) - 3 alpha beta gamma ].
  With gamma = -alpha-beta the second is -3 alpha beta gamma delta, nonzero **when the
  characteristic is not 3**.
* Root pattern {2,2}: x^3 y: alpha beta (alpha+beta)(gamma+delta); x^2 y^2:
  (alpha+beta)^2 gamma delta + (gamma+delta)^2 alpha beta - 4 alpha beta gamma delta
  = (alpha delta + beta gamma)(alpha gamma + beta delta); x y^3 symmetric. The conclusion
  (the six pair lines) follows as written.
* The hand proof never uses algebraic closure: all roots are rational. So the list of sixteen is
  complete over every field of characteristic not 2, 3, in particular over the algebraic closure.
* "No 3-dimensional subspace": a 3-dimensional space contains infinitely many 2-planes when K is
  infinite. Correct.
* The count of chart points is consistent: a coordinate line lies in 1 of the six Grassmannian
  charts, a pair line in 4, a star line in 3: 6 + 24 + 12 = 42 = 6 x 7.

In characteristic 3 the lemma is FALSE: the four lines {u_i = u_j = u_k} also lie on the surface
(root pattern {3,1} with alpha = beta = gamma), 20 lines in all. This agrees with the brute-force
count over F_9 (20 lines) against F_25, F_49 (16 lines). The note excludes characteristic 3, so
this is not an error; see Section 6.3 for what happens there.

**Lemma N. Correct.** Theta(l, l_a e_a - l_b e_b) has coefficients Theta[a,a] (l_a^2), -Theta[b,b]
(l_b^2), Theta[b,a] - Theta[a,b] (l_a l_b), Theta[i,a] and -Theta[i,b] (i in {c,d}). So N_ab has
dimension 9 and is as stated. alt_{a'b'} lies in N_ab only if {a',b'} is disjoint from {a,b}
(if a' = a, the entry [b',a] = -1 must be the entry [b,a] of a symmetric multiple of s_ab,
impossible when 2 != 0).

**Lemma S. Correct.** Points I examined, because this is where a hidden assumption could sit:
* dim U(l) = 2 exactly: U(l) is cut out by two linear forms, so dim >= 2; by (*) and fact 2,
  sigma vanishes on the linear space l^-1 * U(l); by Lemma L that space has dimension <= 2. This
  also shows that (*) forces Phi_1(l,.), Phi_2(l,.) to be independent for EVERY l in the torus (in
  particular Phi_1, Phi_2 independent, and neither is zero): the lemma is not vacuous about
  proportional or zero forms, it excludes them.
* The covering: for l in T, l^-1 * U(l) is one of the sixteen planes Lam_j, and then l is in Z_j
  (for p in Lam_j the vector l*p lies in U(l)). So T is contained in Z_1 u ... u Z_16; the cover
  is finite and complete precisely because Lemma L is a complete list.
* Each Z_j is Zariski closed in V: it is the common zero set of the quadrics
  l -> Phi_v(l, l*p), p in a basis of Lam_j, v = 1, 2. Note that Z_j is defined for all l in V,
  not only on the torus, which is what the irreducibility step needs.
* Irreducibility: elementary form. If no Z_j were all of V, choose for each j one of its quadrics
  q_j that is not identically zero; the product q_1 ... q_16 vanishes on T, and (multiplying by
  l_0 l_1 l_2 l_3) on all of V; a nonzero polynomial over an infinite field does not vanish
  identically. Uses only: K infinite.
* The three computations of T(Lam): I redid them by hand from "coefficient of l_i^2 is
  Phi[i,i] p_i, coefficient of l_i l_k is Phi[i,k] p_k + Phi[k,i] p_i". C_ab: columns a, b vanish.
  Lam_ab: p = e_a + e_b kills Phi[a,a], Phi[b,b], Phi[c,a], Phi[c,b], Phi[d,a], Phi[d,b] and
  gives Phi[a,b] = -Phi[b,a]; p = e_c - e_d kills Phi[c,c], Phi[d,d], Phi[a,c], Phi[a,d],
  Phi[b,c], Phi[b,d] and gives Phi[c,d] = Phi[d,c]. So T = span(alt_ab, s_cd). Sig_a: every
  column except a vanishes, so U(l) contains the hyperplane u_a = 0, contradicting dim U(l) = 2.
  All sixteen planes are accounted for; there is no case besides (S) and (C).
* "Exactly one": (S) and (C) exclude each other (S_{ab|cd} has no zero column) and different
  {a,b} give different spaces.
* The rank statement in (S): B_p (e_a - e_b) = 0 and the principal minor 4 s (s^2 - t^2) were
  recomputed by hand. An explicit witness with rank 3 is p = e_a + e_b (s = 1, t = 0), so
  "generic u" is not an existence assumption.

**Frames. Correct.** I re-derived the table: for the frame (i,j,k,m), Phi is the form on
(r_i,r_j), Psi on (r_i,r_k), Psi' on (r_j,r_m), Omega on (r_i,r_m), Omega' on (r_j,r_k):
(0,1,2,3): F; X; Y; X'; Y'. (0,2,1,3): X; F; G; X'; Y'^T. (1,0,3,2): F^T; Y; X; Y'; X'.
(1,3,0,2): Y; F^T; G^T; Y'; X'^T. These agree with the note. All four are frames (i is linked to
j and to k). The transposes are right: in (1,0,3,2) the form on (r_1, r_0) is F^T, and the proof
uses only that the span of the F_v^T is again S_{ab|cd}, which holds because alt^T = -alt and
s^T = s.

**(a). Correct.** With Phi_v(l,u) = 0 the identity (D') leaves three rank-one forms in (r_k, r_m).

**(b). Correct, and it uses no genericity.** l = x e_a + y e_b is NOT in the torus, and the
argument does not need it to be: fact 3 holds for all l, u. The space of admissible u (two linear
conditions) has dimension >= 2 whatever Psi'_1, Psi'_2 are (zero and proportional forms included),
while B^l_u = 0 confines u to the line K (x e_a - y e_b). I checked the three frames in which (b)
is used: (0,1,2,3): r_1 = l, r_3 = u, remaining term X'(r_0,u) Y'(l,r_2); (0,2,1,3): r_2 = l,
r_3 = u with G_v(l,u) = 0, remaining term X'(r_0,u) Y'(r_1,l); (1,3,0,2): r_3 = l, r_2 = u with
G_v(u,l) = 0, remaining term X'(r_0,l) Y'(r_1,u). In each case the remaining term has rank <= 1 in
the two free rows.

**(c). Correct.** A sum of three rank-one forms of rank exactly 3 has independent left factors and
independent right factors, so each factor vanishes on the corresponding kernel. If X' = 0 or
Y' = 0 (or any term is zero) the rank could not be 3, so zero terms lead to a contradiction at
this point rather than slipping through. The conclusions Psi_v(l, l*n_ab) = 0 and
Omega(l, l*n_ab) = 0 do not depend on u; they hold for all l in T, hence identically (quadrics
vanishing on the torus of an infinite field).

**Theorem 1, Steps 1-4. Correct.** Step 1 uses Lemma S + (b) in the frames (0,1,2,3), (0,2,1,3),
(1,3,0,2). Step 2 uses (c) in (0,1,2,3) (X_v in N_ab) and in (1,0,3,2) (Y_v in N_ab), then
Lemma N. Step 3 uses (c) in (0,2,1,3) with the roles (ab) -> (cd): X' in N_cd, hence
X'[a,c] = X'[a,d] = 0. Step 4: at (j_0..j_3) = (a,c,b,d) the three kinds of terms contribute
F_v[a,c] G_v[b,d] = 0, X_v[a,b] Y_v[c,d], X'[a,d] Y'[c,b] = 0; at (a,d,b,c): F_v[a,d] G_v[b,c] = 0,
X_v[a,b] Y_v[d,c], X'[a,c] Y'[d,b] = 0; and Y_v[d,c] = -Y_v[c,d]. So 1 = -1. Uses 2 != 0.

**Machine proof from Lemma S alone. Correct; reproduced with my own code** (Section 4, item E7).
The reduction is right: each of F, G, X, Y is the Phi of one frame and its transpose is the Phi of
another frame ((2,3,0,1) and (3,2,1,0) for G); a pencil which is of type (S) in either reading is
S_{ab|cd}; otherwise it has two zero columns and two zero rows. The combinatorial test is a valid
necessary condition: if T = x y^T and T is nonzero at (r,c) and at (r',c'), it is nonzero at
(r,c').

**"Type of a triple". Correct.** The common zero space of three linear forms is nonzero and, by
Lemma R and fact 2, lies in the union of the ten lines K (l*n); a nonzero subspace inside a finite
union of lines is one of them (K infinite). The closed sets Z_n cover T as in Lemma S.

**Lemma W. Correct.** a_l = alt_ab(l,.) and b_l = s_cd(l,.), so span(alt_ab, s_cd) is inside W.
Conversely l_b Xi(l,e_b) = -l_a Xi(l,e_a) as polynomials, so Xi(l,e_b) = kappa l_a with kappa
constant; same for (c,d). Star: l_j Xi(l,e_j) is independent of j among the three j != a, and three
linear forms L_j with l_j L_j = l_j' L_j' must vanish. The intersection table was recomputed
(dimension 2 for the same pair type, 0 for different pair types and for pair/star, 1 for two star
types).

**5.1. Correct, including the statement about limits.** The restricted form has rank equal to
dim{B restricted to L2 x V : B symmetric with zero diagonal} >= 6 - 1. (a) and (b) were checked by
hand and exactly. For limits over R or C the planes L2 of the approximants have a convergent
subsequence; equivalently, "there is a plane L2 with rank <= 4" is the image of a closed subset
of (tensors) x Gr(2,4) under a projection with projective fibre, hence a closed condition.

**5.2. Correct.** Rank exactly 2 of B^l_{l*n} forces X_1(l,.), X_2(l,.) to be independent and to
span span(a_l, b_l); a star type would make them proportional. The final evaluation at r_0 = e_c,
r_2 = e_a is right: X_i[c,a] = 0, F_v[c,a] = F_v[c,b] = 0 by Lemma N, and perm(e_c, r_1, e_a, r_3)
contains r_1b r_3d.

**5.3. Correct.** I re-derived the four slice formulas t1-t4 and which covectors depend on l only:
t1: X(l,.), X'(l,.); t2: Y(l,.), Y'(l,.); t3: X(.,l), Y'(.,l); t4: X'(.,l), Y(.,l). So
X in W_t1 n W_t3^T, X' in W_t1 n W_t4^T, Y in W_t2 n W_t4^T, Y' in W_t2 n W_t3^T, all nonzero, and
the table forces "all four types the same pair" or "all four stars". Stars: two monomial terms
have flattening rank 1 each, 3 + 1 + 1 < 6. Pair: F_v in N_ab n N_ab^T gives F_v[a,c] = F_v[b,c] = 0;
X'[a,d] = X'[b,d] = 0; X[b,a] = -X[a,b]; so 1 = -1.

**5.4 Theorem 2. Correct.** The partitions of 5 into at most three parts are exactly the five
patterns. Row permutations fix perm and act on the three pairings through the surjection
S_4 -> S_3, so the assignment of the multiplicities to the pairings is irrelevant. Zero terms are
allowed in every argument (checked above for each step), so sums of fewer than five products are
covered. A decomposition over a subfield is a decomposition over the algebraic closure. Arbitrary
function factors reduce to bilinear ones by `SplitBridge.lean`.

**Section 6. Correct.** Identities A and B hold on all 256 entries with symbolic parameters (my
own sympy check). The closed formula for "residual x size^2" on the subfamily p = -q = t c_3 agrees
with a direct numerical evaluation at t = 1, 1.5, 1.6693, sqrt 3, 2, 3 (1.3333, 0.6036, 0.5204,
0.5000, 0.5667, 1.2000). These identities are limit decompositions only (error lam x a fixed
tensor, terms of size 1/lam); they do not contradict Theorem 1.

**Section 7, completeness certificate. Correct logic.** If, for each variable x_k, the polynomial
g_k = prod (x_k - v) lies in the radical of the ideal (Rabinowitsch), every zero over the algebraic
closure has all coordinates in the finite rational grid, and the grid is tested point by point.
I read `certified_zero_set` in `exact4.py`; it implements this.

## 2. The specific worries listed in the referee brief

* *Hidden genericity (l in the torus, generic u, rank exactly 3).* None. The torus is used only to
  transport Lemma L by fact 2; every conclusion drawn on the torus is a polynomial identity in l
  and extends to all l. The only "generic u" has an explicit witness. (b) works at a point l
  outside the torus and needs no torus.
* *Algebraic closure / infinite field.* Algebraic closure is never used. Infiniteness is used in
  Lemma L (no 3-space on the quartic), in the irreducibility steps, in "a subspace inside a finite
  union of lines is one of them", and in extending identities from the torus. Since a
  decomposition over K is one over any extension, Theorem 1 holds over EVERY field of
  characteristic not 2, 3 (finite ones included).
* *Irreducibility step.* Sound; see Lemma S above.
* *dim U(l) = 2 exactly.* Sound.
* *Only (S) and (C).* Sound, all sixteen planes treated; the four star planes are excluded by the
  dimension of U(l).
* *Frames and transposes.* Sound; every frame used in Steps 1-3 and in (b) was written out.
* *Zero or proportional terms.* F_1, F_2 proportional (or one of them zero): then dim U(l) >= 3
  and (*) contradicts Lemma L; the same for X and Y. X' = 0 or Y' = 0: contradiction in (c)
  (rank 3 impossible). The G_v enter the hand proof only as Psi' (in (b), where any Psi' works,
  zero included, and in (c), where a degenerate Psi' again contradicts rank 3), and Step 4 holds
  for arbitrary G_v and Y'. So degenerate decompositions are excluded by the same proof; this is
  consistent with the Lean theorem that four terms do not suffice.
* *Pattern up to row permutation.* Sound.

## 3. Remarks (no error; suggested precisions)

1. Section 0 says "the arguments use only: K infinite, characteristic not 2 or 3". For
   Sections 1-4 (Theorem 1) I agree, and "K infinite" can be dropped by extending scalars. For
   Sections 5.2 and 5.3 the input Lemma R is certified by a Groebner computation over Q only, so
   what is established for Theorem 2 is characteristic 0, as the theorem states. (Brute force
   gives the same ten nodes over F_9, F_25, F_49, so nothing suggests a problem in other odd
   characteristics, but that is not a proof.)
2. Lemma L should say "characteristic not 2, 3" in its statement: it is false in characteristic 3.
3. Lemma S: it would help to state in the lemma that (*) implies that Phi_1(l,.), Phi_2(l,.) are
   independent for all l in T (now only inside the proof), because Step 1 silently relies on it to
   dispose of proportional F_1, F_2.
4. Fact (c): replace "u generic in l*Lam_ab" by "u = l*(e_a + e_b)".
5. Section 3 lists four of the eight frames in the table and (c) mentions "eight frames"; the
   proof of Theorem 1 uses exactly the four listed, the machine proof uses all eight. Fine.
6. Section 5 refers to proofs "in the docstring of t3() / p410() in lower4.py". I refereed the
   proofs as written out in Sections 5.1-5.3 of the note, which are self-contained, and then read
   the two docstrings: they contain the same arguments in shorter form. The points the note says
   it adds (that the common zero space is a line and a single type holds for all l; Lemma W,
   i.e. that the coefficients in span(a_l, b_l) are constants; the intersection table replacing
   "constant direction, which only a star type allows") are genuinely needed and are correctly
   supplied.
7. Section 6: the note says the numerical fits give the constant 0.520. My ridge-regularised
   solver gives 0.5212 and my box-constrained solver 0.528-0.546 at moderate sizes; these are the
   same phenomenon measured with a different size functional (see Section 5 below).

## 4. Independent exact checks

All scripts were written without looking at `exact4.py` (I read `exact4.py` afterwards; it is
organised differently and I found no flaw in it). They live in the scratch directory
`/tmp/claude-0/-home-user-claude-cloud/9d4f02d2-16ab-5b7a-9dfc-330543a2ec0f/scratchpad/ref221/`
(not durable); the outputs are quoted here. sympy, rational arithmetic unless stated.

| id | script | what it checks | output |
|---|---|---|---|
| E1 | `ref1.py` A | facts 1, 2; det B_u = -4 sigma | True, True, True |
| E2 | `ref1.py` B | Lemma R: quotient dimension of (3x3 minors, h - 1) | 10 (= the ten known nodes); nothing at h = 0; 2x2 minors: only u = 0; node formulas True |
| E3 | `ref1.py` C | Lemma L: in each of the six Grassmannian charts, the 7 expected planes solve the equations; quotient dimension | 21 in every chart; union 16 planes; kernel and minor on Lam_ab True |
| E4 | `ref2.py` | Lemma L completeness over the algebraic closure, two certificates per chart: (1) the local multiplicities at the 7 rational points (each 3) add up to the total quotient dimension 21, so there is no further point; (2) every lex eliminant splits into linear factors over Q with roots in {-1, 0, 1}, and the grid {-1,0,1}^4 contains exactly 7 solutions | "complete: True", "eliminants split over Q: True", "7 solutions" in all six charts |
| E5 | `ref3_ff.py` | plain enumeration over finite fields (no Groebner): number of lines on sigma = 0 and of projective points with rank B_u <= 2 | F_9: 20 lines, 10 nodes; F_25: 16, 10; F_49: 16, 10 |
| E6 | `ref1.py` D, E, F | T(Lam) for the sixteen planes (dims 8, 2, 4 and the stated spaces); Lemma N (dim 9, containment iff {a',b'} = {c,d}); Lemma W and the intersection table; Step 4 with G_v, Y' and the free part of X' symbolic, all 12 ordered cases | all True; intersection dimensions 2 / 0 / 0 / 1 |
| E7 | `ref10_enum39.py` | own implementation of the machine proof from Lemma S: 39 supports per pencil, 39^4 = 2 313 441 cases, combinatorial filter, then all 2 x 2 minors of the 03\|12 flattening | 3 survivors (all four pencils on the positions of one column pairing); 48 sub-cases, all with Groebner basis {1}; 0 alive |
| E8 | `ref4_enum.py`, `ref4_control.py` | Steps 2-4 replaced by enumeration, assuming Lemma S + (b): 6^4 = 1296 choices of S_{ab\|cd} for F, G, X, Y; perm - A - B of rank <= 1 for 03\|12 | 1248 dead by a constant minor, 48 by Groebner basis {1}, 0 alive; control with planted solutions: ideal proper and the planted point is a zero (3 of 3) |
| E9 | `ref9_modp.py` | the same 1296 cases over F_5 and F_7 by brute force over all p^8 coefficient vectors (no Groebner) | p = 5: 1248 cases dead by a constant minor, 48 enumerated over all 390 625 vectors, 0 solutions; p = 7: the same with 5 764 801 vectors, 0 solutions |
| E10 | `ref6_sec5.py`, `ref6b_identB.py` | flattening ranks of perm (6, 6, 6); 5.1 (a) rank 6, (b) unit ideal of the 5 x 5 minors in six charts; final evaluations of 5.2 and 5.3; Identities A and B on all 256 entries, symbolic parameters | all True |
| E11 | `ref16_frames.py` (first part numerical) | my hand table of the four frames, on a random complex tensor of pattern (2,2,1): slice with r_i = l, r_j = u in U(l) equals the three predicted rank-one forms; and, exactly, T(M_m) modulo 3 for the four extra lines of characteristic 3 | differences 7e-15 to 2e-14, slice rank 3 in all four frames; T(M_m) has dimension 3 and contains alt(ijk) |

E4 deserves a comment: the scheme of lines is not reduced (each of the sixteen lines counts with
multiplicity 3 in every chart), so "quotient dimension = number of points" would have been the
wrong test; the multiplicity count and the eliminant test are both insensitive to this.

## 5. Numerical attempts to find a counterexample (numerical evidence only)

A genuine exact decomposition with bounded factors would refute the theorem. Two solvers of my
own, both over C, both validated on problems where an exact decomposition exists.

**Solver 1** (`ref5_num.py`): complex Levenberg-Marquardt with analytic Jacobian on
|perm - sum|^2 + mu |theta|^2, continuation mu = 1e-1 ... 1e-8, random starts. An exact solution
shows residual ~ mu^2 at bounded size.
* Controls, all passed (residual proportional to mu^2 down to mu = 1e-8, at bounded size): a
  planted random tensor of pattern (2,2,1) (6 of 6 starts, residual 3.1e-19, size 30); perm with
  pattern (6,0,0), i.e. Laplace (6 of 6, 2.5e-17, size 2.0); det_4 with pattern (1,1,1), the
  Lampert-Moshkovitz identity (8 of 8, 2.5e-17, size 4.0); perm with six terms in the patterns
  (2,2,2), (3,2,1), (4,1,1) (2.5e-17 at size 2.0; 2.1e-16 at size 4.1; 5.8e-17). Side
  observation, 4 starts each, not a claim: nothing found for six terms in the patterns (4,2,0),
  (5,1,0), (3,3,0) (residuals 0.111, 0.073, 0.134).
* perm, pattern (2,2,1): 50 complex random starts (log of the earlier, interrupted session of this
  same referee task, same script) and 14 real starts. 39 of 50 complex starts and 8 of 14 real
  starts converge to the border family: the residual falls with the size of the terms, but
  **residual x size^2 tends to 0.5212** (real runs, four digits; the complex log has two printed
  digits, consistent with it): 1.3e-2 at size 6.6, 6.0e-4 at size 30, 6.0e-6 at size 295, 1.3e-6
  at size 635. The other starts stall at residual 0.083 or 0.13. No start gives a small residual
  at bounded size. Best residual among all recorded points with largest term <= 10: 1.3e-2.
* For comparison: (3,1,1): residual x size^2 -> 0.6667 (6 starts); (3,2,0): all 6 starts stall at
  residual 0.23 with size 2.4, and (4,1,0): all 4 starts stall at 0.1995 with size 2.3 (no limit
  decomposition, in agreement with the note's table).

**Solver 2** (`ref11_box.py`, a different method): hard box constraint |Re|, |Im| <= R on every
entry of every factor, trust-region-reflective least squares (scipy), analytic Jacobian.
* Control: a planted (2,2,1) tensor with entries in [-1,1], R = 2: residual 2e-32 after 12-17
  evaluations.
* perm, pattern (2,2,1): R = 2: 12 starts (two batches), best residual 3.43e-3 (9 starts
  between 3.43e-3 and 3.52e-3, three stalled at 0.086, 0.087 and 0.135), the solution sits on the
  box (24-25 coordinates at the bound); R = 4: 8 starts, best 2.17e-4 (six between 2.17e-4 and
  2.26e-4, one at 3.2e-4, one stalled at 0.084); R = 8: 6 starts, 1.6e-5 to 2.4e-5, each stopped
  by the limit of 3000 evaluations, so not fully converged. The
  best residual scales like R^-4 (3.43e-3 / 2.17e-4 = 15.8; 2.17e-4 / 1.6e-5 = 13.6 with the
  unconverged R = 8 runs), i.e. like size^-2, with residual x size^2 between 0.53 and 0.60: the
  signature of a limit decomposition, not of an exact one.

By the standard of the project ("a fit counts only if the residual falls faster than size^-2
allows, or the solution is bounded and exact to rounding") **no decomposition was found** in
about 100 random starts over the two solvers; the best bounded-factor residuals
(|perm - sum|^2 / |perm|^2) are 3.4e-3 (all entries of all factors <= 2 in real and imaginary
part), 2.2e-4 (<= 4) and 1.6e-5 (<= 8).

## 6. Another side: independent sanity arguments

6.1 **A prediction of Lemma S for LIMIT decompositions, tested numerically** (`ref15_pencils.py`).
Lemma S is the heart of the proof, and it says more than the theorem. If T_n -> perm are sums of
pattern (2,2,1) and a doubled pencil span(F_1, F_2) converges in the Grassmannian Gr(2,16) to a
pencil P with dim U_P(l) = 2 for generic l, then P satisfies (*) for perm itself (rank <= 3 is a
closed condition), so P must be S_{ab|cd} or of type (C); the same for the transposed pencil. So in
any border decomposition every doubled pencil must tend to S_{ab|cd}, or to a pencil supported on
a 2 x 2 block, or to a degenerate pencil (all matrices a (x) c with a common c). This is
falsifiable. In the border solutions found by Solver 1 from random starts (continued to
mu = 1e-10, residual 6e-8, terms of size 2.9e3) all four doubled pencils F, G, X, Y have two
columns of norm 0.0005 and two rows of norm 0.0005 (orthonormalised pencil; the other two have
norm 1): type (C) for both arguments, as predicted, and as in the closed-form family of Section 6
of the note. (8 random complex starts: 6 border solutions, all six as described; 2 stalled local
minima at residual 0.083 and 0.135, which are not border solutions.) A direct numerical search
for pencils satisfying (*) was uninformative, as the author also reports: with
u = *(m_1 ^ m_2 ^ w) (`ref7_lemmaS.py`, 20 starts) the optimiser drifts to degenerate pencils
where the objective vanishes to high order; with a projector formulation that removes those
(`ref12_lemmaS.py`; it does vanish at S_{ab|cd} and at random type (C) pencils, to 1e-11) not one
start had terminated after 20 minutes and I stopped it. So there is no numerical counterexample
to Lemma S and no direct numerical confirmation either, apart from the test above.

6.2 **The proof fails where it must.** A proof of impossibility that also "proved" something
false would be suspect. (i) det_4 IS a sum of three split products, one per pairing: there
B^l_u is antisymmetric of rank 2, det B^l_u vanishes identically, (*) is empty and no step
applies. (ii) Six terms of pattern (2,2,2) exist (Laplace along the column blocks 01|23 is of this
pattern): with two terms on the third pairing the slices have rank <= 4 and (*) is not implied.
(iii) Limits exist for (2,2,1): the proof uses exactness only through "rank <= 3 for u in U(l)" and
through (b); in the limit family the single term blows up and (b) fails, which is exactly how the
type (C) pencils of 6.1 arise. (iv) Characteristic 2: perm = det, three terms; Step 4 and Lemma N
use 2 != 0.

6.3 **Characteristic 3, where Lemma L fails** (side result; exact computation resting on a short
hand modification of Lemmas L and S that I sketch here and did not write out in full). In
characteristic 3 the surface has four more lines M_m = {u_i = u_j = u_k}, and
T(M_m) = alt(ijk), the antisymmetric forms on the three indices other than m (same computation as
in Lemma S; for two independent forms in alt(ijk), U(l) = span(l restricted to ijk, e_m), of
dimension 2; the dimension 3 of T(M_m) modulo 3 was confirmed exactly, E11). (b) is
characteristic free. So in characteristic 3 each doubled pencil is
S_{ab|cd} or lies in some alt(ijk). `ref14_char3.py`: 10^4 choices of spaces for F, G, X, Y; 48
pass the support filter; for all 48 the 2 x 2 minors of perm - A - B (A in P_F (x) P_G, B in
P_X (x) P_Y, up to 18 unknowns) generate the unit ideal over GF(3). So pattern (2,2,1) is
impossible in characteristic 3 as well: the theorem does not hinge on the coincidence that makes
Lemma L true. (Patterns (3,2,0), (3,1,1) were not examined in characteristic 3.)

6.4 **Finite-field brute force of the reduced problem** (E9): over F_5 and over F_7, for all 1296
assignments of S_{ab|cd} to the four pencils and ALL p^8 coefficient vectors, perm - A - B never
has rank <= 1 in the flattening 03|12. This re-proves Steps 2-4 over F_5 and F_7 (rational points
only) without Groebner bases. A brute-force
check of the full statement over a finite field is out of reach (5^160 parameter values) and I
found no honest way to make it semi-exhaustive without assuming Lemma S.

6.5 **Dimension count** (`ref8_dim.py`, exact rank of the Jacobian modulo 2^61 - 1 at a random
integer point). The closure of the set of sums of five split products has dimension 135, 143,
147, 149, 151 for the patterns (5,0,0), (4,1,0), (3,2,0), (3,1,1), (2,2,1) (151 = 60 + 60 + 31: the
join of the three determinantal varieties is not defective), inside a space of dimension 256. At
the closed-form limit decomposition (Identity A, lam = 1/3) the rank drops to 148. What this
shows: only that these are thin sets and that the parametrisation degenerates along the limit
family; it does not decide whether perm, which lies in the closure, lies in the image. I record
it because the brief suggested it; it is not evidence either way.

## 7. Literature

What I actually read is stated for each item. I found no statement of the (2,2) partition rank,
or of any partition rank, of the 4 x 4 permanent; and no explicit small tensor with a gap between
a partition-type rank and its border version.

* **E. Naslund, "The partition rank of a tensor and k-right corners in F_q^n"**,
  https://arxiv.org/abs/1701.04475 (abstract only): introduces partition rank, a generalisation of
  slice rank.
* **E. Ballico, A. Bik, A. Oneto, E. Ventura, "The set of forms with bounded strength is not
  closed"**, https://arxiv.org/abs/2012.01237 (abstract, and the statement of Theorem 3.2 in the
  PDF): the set of quartics of strength <= 3 is not Zariski closed when the number of variables is
  large (algebraically closed field); the proof goes through polynomial functors and the formal
  quartic x^2 f + y^2 g + u^2 p + v^2 q in placeholders (strength 4, Theorem 3.2); the number of
  variables is not explicit.
* **A. Bik, J. Draisma, A. Lampert, T. Ziegler, "Strength and partition rank under limits and
  field extensions"**, https://arxiv.org/abs/2502.10007 (v2 of 3 Aug 2026; I read the
  introduction in the PDF). Definition 1.12 defines partition rank with all proper nonempty
  subsets and the border partition rank; the abstract says both ranks "can jump in a limit".
  Remark 1.5, verbatim: "We do not know an explicit example of a form over C whose border
  strength is strictly lower than its strength. However, such forms do exist for d = 4 [BBOV22,
  Theorem 3] and likely also for d > 4. For d <= 3 they do not exist". Theorem 1.14: if the border
  partition rank of a d-tensor is r then its partition rank is at most a constant (depending on d)
  times r^(d-1) over an infinite field. (For d = 4 and r = 5 this bound is far above 6, so it
  says nothing here.)
* **B. Baily, A. Danelon, "Closedness of bounded strength and partition rank loci"**,
  https://arxiv.org/abs/2610.28792 (20 Oct 2026; I read the introduction and the statements of
  Theorems 4.6, 4.11 and Corollary 4.13 in the PDF, not the proofs). For Naslund's partition rank
  (all partition types, tensors of any order, algebraically closed field): the locus of partition
  rank <= 2 is closed (Theorem 4.6); the locus of partition rank <= 3 is not: an order-4 tensor
  T_n in (k^n)^{(x)4}, given by a formula in placeholders, has partition rank 4 and is a limit of
  tensors of partition rank <= 3 "for n sufficiently large" (Theorem 4.11; n is not explicit);
  and for every r >= 3 the locus of partition rank <= r is not closed for suitable n
  (Corollary 4.13). Their introduction lists geometric rank, slice rank, analytic rank and others
  as closed and strength, partition rank, tensor rank as not closed. They do not mention the
  permanent or the determinant.
* **A. Lampert, G. Moshkovitz, "Slice rank and partition rank of the determinant"**,
  https://arxiv.org/abs/2509.06294 (I read the abstract and, in the PDF, the statements of
  Theorem 3.5 and Corollary 3.6): "Over any field, prk(det_4) = 3", by an expansion with three
  products of bilinear forms in complementary pairs of rows (so only (2,2) splits are used); a
  lower bound log_2(n) + 1 for prk(det_n); the permanent is not mentioned, and nothing is said
  about limits. Remark: combined with Baily-Danelon Theorem 4.6 (rank <= 2 is closed), det_4 also
  has border partition rank 3 over an algebraically closed field.
* **S. Kopparty, G. Moshkovitz, J. Zuiddam, "Geometric rank of tensors and subrank of matrix
  multiplication"**, https://arxiv.org/abs/2002.09472 (abstract only): introduces geometric rank,
  which lies below slice rank; the abstract does not speak of limits. Baily-Danelon cite it for
  geometric rank being closed. Partition rank is not mentioned.
* **C. Brand, P. Kaski, J. Wang, "Partition rank and algebraic circuit lower bounds"**,
  https://arxiv.org/abs/2607.02241 (abstract only): relates partition ranks to multiplicative
  complexity; the abstract mentions neither the permanent nor limits.

Position of the note's result relative to this. (1) It concerns the RESTRICTED rank where only
splits of type (2,2) are allowed. For the unrestricted partition rank perm_4 shows no gap: Laplace
along a row gives 4, and `linear_lower_bound.md` (paper proof of this project) gives border value
>= 4. (2) That a partition-type rank can drop in the limit is known in general (Ballico-Bik-
Oneto-Ventura for strength; Baily-Danelon for partition rank from rank 3 on), but the known
examples live in a large, non-explicit number of variables, and Bik-Draisma-Lampert-Ziegler state
that no explicit form with border strength below strength is known over C. So an explicit
4 x 4 x 4 x 4 tensor with exact (2,2) value 6 and border value 5 is, as far as I could find, not
in the literature; but note that for a rank with a prescribed partition TYPE the set of sums is a
join of determinantal varieties and failure of closedness is less surprising than for the
unrestricted rank. I did not find the restricted (2,2) rank of perm_4 or det_4 treated anywhere
except, implicitly, in Lampert-Moshkovitz for det_4 (value 3).

## 8. Not done

* No Lean work of my own, and no reading of the Lean formalisation beyond the spot check
  reported at the top.
* The numerical `fit` mode of `exact4.py` was not rerun; my own solvers replace it.
* Sections 5.2 and 5.3 were not examined in positive characteristic.
* The proofs in the cited papers were not read; only the statements quoted above.

## Appendix: the core of the enumeration E7 (for reproducibility)

```python
import itertools, numpy as np
two = list(itertools.combinations(range(4), 2))
comp = lambda a, b: tuple(sorted(set(range(4)) - {a, b}))
supports = []
for (a, b) in [(0, 1), (0, 2), (0, 3)]:               # supports of S_{ab|cd} and S_{cd|ab}
    c, d = comp(a, b); M = np.zeros((4, 4), bool)
    M[a, b] = M[b, a] = M[c, d] = M[d, c] = True; supports.append(M)
for R in two:                                          # 2 x 2 blocks (type (C) in both arguments)
    for C in two:
        M = np.zeros((4, 4), bool)
        for i in R:
            for j in C: M[i, j] = True
        supports.append(M)
P = np.zeros((4,)*4, bool)
for j in itertools.permutations(range(4)): P[j] = True
P = P.ravel()
SA = np.array([np.einsum('ab,cd->abcd', f, g).ravel() for f in supports for g in supports])
SB = np.array([np.einsum('ac,bd->abcd', x, y).ravel() for x in supports for y in supports])
idx = list(itertools.product(range(4), repeat=4))
rowid = np.array([j[0]*4 + j[3] for j in idx]); colid = np.array([j[1]*4 + j[2] for j in idx])
Rm = np.zeros((16, 256), bool); Rm[rowid, np.arange(256)] = True
Cm = np.zeros((16, 256), bool); Cm[colid, np.arange(256)] = True
surv = []
for ia in range(len(SA)):
    U = SA[ia][None, :] | SB                           # supp A u supp B
    O = P[None, :] & ~U                                # ones of perm outside it
    rows = (O[:, None, :] & Rm[None]).any(axis=2); cols = (O[:, None, :] & Cm[None]).any(axis=2)
    viol = (~P & ~U & rows[:, rowid] & cols[:, colid]).any(axis=1)
    surv += [(ia // 39, ia % 39, ib // 39, ib % 39) for ib in np.nonzero(~viol)[0]]
print(len(surv), surv)        # 3 survivors: (0,0,0,0), (1,1,1,1), (2,2,2,2)
```

For the three survivors and the 16 choices S_{ab|cd} / S_{cd|ab} per pencil, the 2 x 2 minors of
the 03|12 flattening of perm - A - B (8 unknown coefficients) have Groebner basis {1} (sympy).
