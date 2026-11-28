# WOWII Conjecture 189 -- working notes (session of 2026-11-28)

Statement (Lean, formal-conjectures): G connected simple graph on a finite nontrivial type,
`max_v distEven(v) <= 1 + secondSmallestDegree G`  ==>  G has a Hamiltonian path.

STATUS: NOT PROVED.  No counterexample.  New lemmas (one machine-checked in Lean), a Lean-checked
reduction to a weaker open statement, exhaustive verification for all graphs with n <= 18
(frontier in logs_plab2.txt), and several refuted strengthenings.

Notation: n = |V|, sigma = d_2 (second smallest degree), delta = d_1, z = a vertex of minimum degree
("low" vertex; every other vertex has degree >= sigma).  E(v) = #{w : dist(v,w) even} (v counted),
e(v) = E(v) - 1.  Hypothesis (H): e(v) <= sigma for every v.  L_i(v) = i-th distance layer of v.

## 0. Literature (checked 2026-11-28)

R. Easwar, S. Johari, "Conditions for traceability under a bound on the size of even-distance sets",
arXiv:2609.11719 (10 Sep 2026), partial progress only: under (H) the graph is traceable if
(1) diam <= 2, (2) n <= 2 d_2 + 2, (3) n = 2 d_2 + 3 and G 2-connected, (4) G is not 2-connected.
Tools: Chvatal's degree-sequence theorem, Bondy-Chvatal-type closure lemmas with distance conditions,
block graph analysis.  So the conjecture is open exactly for 2-connected graphs with n >= 2 d_2 + 4.
The WOWII list still shows #189 as open.  Nothing found that proves it.

## 1. New results of this session

### 1.1 Absorption Lemma (proved; Lean-checked: lean/Absorb.lean, theorem OMA.Helpers.absorb)
Let G satisfy (H), let P be ANY path of G (not necessarily longest) and x a vertex not on P with
deg(x) >= sigma and N(x) contained in V(P).  Then x is adjacent to an end of P or to two consecutive
vertices of P; hence V(P) + x is the vertex set of a path.

Proof.  Otherwise let J = positions of the neighbours of x on P = v_0..v_k.  0, k not in J and J has
no two consecutive elements, so every v_{j+1}, v_{j-1} (j in J) exists, is not adjacent to x and is at
distance exactly 2 from x.  The successors v_{j+1} (j in J) are |J| distinct vertices, and the
predecessor of the first neighbour is one more.  So e(x) >= |L_2(x)| >= deg(x) + 1 >= sigma + 1.  QED
(J is nonempty because G is connected and nontrivial.)

Special case (Lemma A): for a longest path P, every off-path vertex other than the low vertex has an
off-path neighbour.  This fact is not in the Easwar-Johari paper.

### 1.2 Reduction to dominating paths (proved; Lean-checked: theorem OMA.Helpers.ham_of_dominating)
If G satisfies the hypothesis of the conjecture and has a path P such that the vertices off P are
pairwise non-adjacent and all have degree >= sigma, then G has a Hamiltonian path (absorb the off-path
vertices one at a time).  Hence, for graphs satisfying (H):

    Hamiltonian path  <=>  a path whose vertex set is a vertex cover and contains the low vertex.

In particular, in a counterexample G - I is non-traceable for every independent set I avoiding the low
vertex (e.g. G - x is non-traceable for every x of degree >= sigma).

A complete reduction file in the site's format (candidate R3; lint passes, compiles, axioms
propext/Classical.choice/Quot.sound) is lean/R3_candidate.lean:
  H1: (H) and n <= 2 sigma + 2  ==> Hamiltonian path          (known: Chvatal + Easwar-Johari Thm 4.1)
  H2: (H) and n >= 2 sigma + 3  ==> dominating path as above  (open, weaker than the conjecture)
  main : H1 -> H2 -> conjecture189.   (Hypotheses are stated over `Type`; main transports along
  an isomorphism with a graph on `Fin n`.)  NOT submitted.

### 1.3 Corollary with classical theorems (paper level, not formalised)
 * Bondy (1980): G 2-connected with sigma_3 >= n + 2 has every longest cycle dominating; applied to
   G + K_1: G connected with sigma_3(G) >= n has every longest path dominating.  With 1.2:
   (H) and delta = sigma and n <= 3 sigma  ==>  traceable.   (New range: 2 sigma + 4 <= n <= 3 sigma.)
 * Lu-Liu-Tian (J. Graph Theory 2005): 3-connected, n >= 13, sigma_4 >= (4n+5)/3 => every longest cycle is
   dominating.  Applied to G + K_1 this again only gives n <= 3 sigma, so the window
   3 sigma + 1 <= n <= ~10 sigma/3 is open even at paper level.
 * Because of 1.2 ANY dominating path suffices (it need not be a longest path).  So existence theorems for
   dominating cycles apply to G + K_1, e.g. Nikoghosyan (arXiv:0906.1857): a 4-connected graph has a cycle of
   length >= 4 delta - 2 kappa or a dominating cycle.  For 3-connected G without low vertex this gives a
   Hamiltonian path whenever n <= 4 sigma - 2 kappa(G).  Not pursued further.
 * What remains for a paper proof: (a) the low vertex (delta < sigma); (b) the window n >= 3 sigma + 1 (under (H)
   n seems to be at most about (10 sigma + 1)/3, see 3.2, but no upper bound on n is proved).

### 1.4 Degree counting in a non-traceable graph (paper level)
P = v_0..v_k longest path, Q = x_0..x_m a longest path of G - V(P), q = m + 1 >= 2, y = x_m with
a = |J_y| >= 1 attachments.  Then q <= j <= k - q for j in J_y, v_0 is not adjacent to v_{j+t}
(1 <= t <= q), attachments of y differ by >= 2, N(v_0) lies in [1,k] minus U, |U| >= q + 2(a-1), so
n >= deg(v_0) + 2 deg(y) + 1 (>= 3 sigma + 1 without low vertices).  Tight for K_s v (s+2)K_r, r = 2 or s = 1.

### 1.5 Local inequality for off-path vertices (paper level)
P longest, x off P with deg(x) >= sigma, J_x != {} its attachments, W_x its off-path neighbours.  Adjacent
off-path vertices have equal or far (index difference >= 3) attachments.  Then
   1 + g_x + |J_{W_x} \ J_x| + |N^2_{G-P}(x)| <= |W_x|,     g_x = #gaps >= 3 between consecutive attachments.
Consequence: a component {w,w'} of G - V(P) with deg >= sigma forces J_w = J_w' with gaps >= 3,
2|J| <= sigma <= |J| + 1, so sigma <= 2.  A clique component of h twins with a common attachments needs
a <= h - 1 ("big blob, few hubs"); that case needs counting on the path side.

### 1.6 Cut vertices (re-derived; now superseded by Easwar-Johari Thm 5.8/5.11)
No cut vertex with >= 3 components, no three end-blocks (parity counting from the cut vertices).

## 2. Verification by computer

### 2.1 Path-labelled SAT search (py/plab.py; main tool)
A counterexample has a longest path P = v_0..v_k, k + 1 < n.  Label P by 0..k.  Clauses: (H) (all-pairs BFS
distance encoding, levels up to min(n-1, 2 sigma + 1) -- valid since diam <= 2 sigma + 1), degree >= sigma
except one vertex, d_2 = sigma, and necessary conditions for P being longest (off-path vertices not adjacent
to ends or to consecutive vertices; w ~ v_j => v_0 !~ v_{j+1}, v_k !~ v_{j-1}; successors/predecessors of
attachments of one vertex pairwise non-adjacent; no spanning cycle of V(P); adjacent off-path vertices have
attachments equal or >= 3 apart; Lemma A).  Remaining models are checked for a path with k + 2 vertices
(C bitmask DP, c/hamlib.c) which is then forbidden (CEGAR).  The necessary conditions were validated against
all 1230 connected non-traceable graphs with n <= 8 and all their longest paths (py/validate_nc.py); with the
hypothesis weakened by one (e <= sigma + 1) the search immediately finds non-traceable graphs (sanity).

RESULT: no counterexample with n <= 18 and n >= 2 sigma + 3 (all sigma, all k); logs_plab2.txt.  For n = 19
only sigma = 1, 2, 3 were completed (run stopped to respect the CPU budget; `./run_plab2.sh 19 22` resumes).  Together with the published dense case
n <= 2 sigma + 2 this verifies the conjecture for all graphs with at most 18 vertices.  (Independently:
exhaustive isomorph-free enumeration for n <= 9 (c/an1.c: every connected non-traceable graph on at most 9
vertices violates the hypothesis), and an older CEGAR without path labels for 2 sigma + 2 <= n <= 11 and (n,sigma) = (12,4).)
Remarkably, almost no CEGAR cut is ever needed: the local conditions above are already contradictory with
(H).  Cuts occurred only for the near-dense pairs (n,sigma) = (13,5), (15,6), (16,6), (17,7), (18,7), i.e.
n = 2 sigma + 3 or 2 sigma + 4, and in the instances inspected ((13,5), (15,6), (16,6)) only for k = n - 2
(a single off-path vertex).

### 2.2 Other searches
 * cut certificates (a set S, |S| <= sigma, with >= |S| + 2 components): none for 13 <= n <= 16 with
   10 sigma >= 3n - 6, and partly n = 17 (logs_cut.txt); superseded by 2.1.
 * blow-ups of all connected base graphs with <= 7 vertices (clique blobs of size <= 4; mixed
   clique/independent blobs of size <= 3) and 8 vertices (clique blobs <= 3): no counterexample (logs_blow.txt).

## 3. Refuted strengthenings (so a proof cannot go through them)

3.1 "Distance exactly two" version is FALSE: there is a connected non-traceable graph on 40 vertices in which
    every vertex has at most d_2 = 9 vertices at distance exactly 2 (py/h2_counterexample.py: three arms
    K_7 - K_3 - c_i attached to a K_7; three end blocks).  True for n <= 9.  So even distances >= 4 matter.
3.2 n <= 3 sigma + 1 is FALSE: thick C_7 with clique blobs (2,2,3,3,3,2,2) has n = 17, sigma = 5 and satisfies
    (H) (py/blow.py).  LP over blow-ups of all base graphs with <= 8 vertices: sup n/sigma = 10/3, attained
    only by thick 7-cycles (py/lpratio.py).  For sigma <= 4, SAT shows n <= 3 sigma + 1 for the next two n.
3.3 "|Odd3(v)| <= sigma for every v" is FALSE (thick C_7 (2,2,2,3,3,2,2), n = 16); true for n <= 9.
3.4 "every connected non-traceable graph has two vertices with e(v) > deg(v)" is FALSE (triangle with three
    pendant triangles, n = 9).  The violating vertex of (H) can be a hub, an end of a longest path, or an
    off-path vertex, depending on the graph.
3.5 The conjecture is tight: with e <= sigma + 1 there are many non-traceable graphs (K_{s,s+2}, two cliques
    sharing a vertex plus a pendant vertex, ...), py/tight.py lists those with n <= 8.

## 4. Why a full proof was not reached

After 1.2 the open core is: every 2-connected graph with (H) and n >= 2 sigma + 4 has a path whose
complement is independent (and contains the low vertex).  For a longest path this means excluding off-path
components with >= 2 vertices.  Degree counting gives n >= 3 sigma + 1 there, but (H)-graphs exist up to
n ~ 10 sigma / 3, so the classical extremal analysis (Bondy / Lu-Liu-Tian type, exceptional vertex included)
would have to be redone with (H) in the window above; the SAT refutations show that this is a finite local analysis for each n,
but no uniform argument was found.  Formalising such a proof (no Dirac/Ore/Chvatal in Mathlib) would be
several thousand lines.

## 5. Files
 * lean/Absorb.lean         Lean: absorption lemma, iterated absorption, ham_of_dominating (compiles)
 * lean/R3_candidate.lean   Lean: reduction candidate (lint ok, compiles); not submitted
 * py/plab.py               path-labelled CEGAR search;  run_plab2.sh, logs_plab2.txt
 * py/validate_nc.py        validation of the necessary conditions on exhaustive data
 * py/core.py               UNSAT-core extraction (which conditions are used)
 * py/enc.py, cegar.py, exist.py, cut.py, cutsweep.py   older global encodings
 * py/gen.py, genall.py     isomorph-free generation up to n = 9 (pynauty), data/
 * c/an1..an7.c, c/blow.c, c/hamlib.c   analyses over all graphs with n <= 9, blow-up search, path DP
 * py/h2_counterexample.py, py/blow.py, py/lpratio.py, py/tight.py
