# Geodesic deletion conjecture: attempt 2

Status: **partial result.** I found no complete proof and no counterexample. Everything below
is either proved in full on paper, with every proof also checked numerically where a check is
possible, or explicitly labelled as computational evidence. The proofs are pen and paper and
have not been machine-checked.

Work directory: `a2/` (scripts and data) under
`/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad/open/moonshot/gillibert-geodesic-deletion/`.

## Summary of what is new in this attempt

Proved (sections 1 to 4):

* **Twin reduction (Thm 2.2).** A connected vertex-transitive graph with a pair of open twins
  (N(x) = N(y)) or closed twins (N[x] = N[y]) has no separating geodesic. All eight 2-orbit
  regular counterexamples from attempt 1 are "twin shadows", so this is exactly what transitivity
  rules out there.
* **Short proof that lengths 0, 1, 2 never separate (Thm 2.1)**, with a cleaner cubic case.
* **Isometric amalgam (Lemma 1.3).** If P separates and A is a union of components, then
  G[A ∪ V(P)] is an isometric subgraph. So a counterexample is two isometric pieces glued along
  a geodesic, with no edges across.
* **Transmission-domination lemma (Lemma 1.8)**, which generalises T7. In a
  transmission-regular graph, no vertex of a component of size < n/2 has a neighbour that is
  strictly closer to every vertex of P. There is also a quantitative version for weak domination.
* **Local criteria (Thm 2.3).** If the neighbourhood graph minus any one vertex is connected, or
  if every two vertices at distance 2 have at least 4 common neighbours, the conjecture holds.
  More generally a 2-local graph Λ(x; x1, x2) suffices.
* **Abelian Cayley graphs of degree ≥ 7 (Thm 2.4).**
* **Atoms (Thm 2.5).** In a twin-free vertex-transitive graph with κ < k, every component C of
  G − V(P) has |N(C)| ≥ κ + 1. Consequently a separating geodesic of length 3 forces degree
  k ∈ {3, 4}, and degree 3 is excluded by Thm 2.6. For k = 4 (Prop 2.8, Prop 2.10), every
  vertex must lie in at most one triangle, both sides must have edge boundary exactly 5, and the
  configuration near P is pinned down. **So for length 3, only 4-regular twin-free graphs with
  at most one triangle per vertex and this rigid local structure remain.**
* **Super edge-connectivity (Lemma 2.9; classical, proof included).** A VT graph with a
  nontrivial k-edge cut is partitioned into K_k blocks.
* **Cubic graphs (Thm 2.6, Cor 2.7).** (a) No geodesic of length ≤ 4 separates a cubic
  vertex-transitive graph. Girth ≥ 4 forces l ≥ 5, and girth 3 forces l ≥ 7. The proof uses
  only Lemma 2.9 and the classical facts κ = λ = 3. (b) For girth 3, G is the truncation T(H) of
  a cubic arc-transitive graph H. A minimal separating geodesic of G has odd length 2m+1 and
  projects to a separating geodesic of length m in H, so a girth-3 counterexample yields a
  cubic arc-transitive counterexample on n/3 vertices. (c) For girth g ≥ 5, every separating
  geodesic has length ≥ 2g − 3. Part (c) uses the Nedela–Škoviera theorem (cyclic
  edge-connectivity = girth for cubic vertex-transitive graphs).

New negative results (section 5). These are counterexamples, with explicit certificates, to
natural metric strengthenings of the conjecture:

* **Twin-free, regular, 3-connected graphs with separating geodesics**: cubic with κ = 3 and
  l = 6, 7, 8 (24 to 48 vertices), and **4-regular, 4-connected** ones with l = 3 (16 vertices)
  and l = 6. All are non-vertex-transitive. So twin-freeness, regularity and maximal
  connectivity together are still not enough.
* **Transmission regularity plus twin-freeness plus regularity is NOT sufficient.** The
  "prism-gadget necklaces" N_r with r odd are cubic, twin-free and transmission-regular, and they
  have a separating geodesic of length 3 (verified for r = 3, 5, ..., 11; n = 6r). So every proof
  must use more than transmission regularity (TR). The necklaces are not distance-degree-regular
  (DDR), not walk-regular and only 2-connected.

Computational (section 6). The two-step law was re-verified. On the twin-free vertex-transitive
graphs with at most 23 vertices, a much more local "Uc + Wadj" linking certificate always
suffices. No non-vertex-transitive DDR graph tested has a separating geodesic: 340 twin-free
polycirculants, and the 876 graphs of the 2-orbit census, 231 of them twin-free.

What remains (section 7): the general twin-free case, for degree ≥ 4 and l ≥ 3. For l = 3
only k = 4 with at most one triangle per vertex is left. For cubic graphs, girth 4 with l ≥ 5
and girth ≥ 5 with l ≥ max(5, 2g − 3) are left; girth 3 reduces to cubic arc-transitive
graphs.

---

## 0. Statement and conventions

G is a finite, connected, vertex-transitive (VT) graph on n ≥ 3 vertices. It is k-regular,
with distance d and vertex connectivity κ. A geodesic is a path P = (v_0, ..., v_l) with
d(v_0, v_l) = l. G − V(P) is the subgraph induced on V \ V(P). P *separates* if G − V(P) is
disconnected. (The Lean statement, `statements/gillibert-geodesic-deletion.lean`, includes the
one-vertex geodesic, and its `Connected` requires nonempty: see Lemma 1.1.) For an edge or pair
xy, W_xy = {w : d(w,x) < d(w,y)} and M_xy = {w : d(w,x) = d(w,y)}. For a vertex z off P, its
*profile* is f_z(t) = d(z, v_t). For a set X, N(X) is the set of vertices outside X with a
neighbour in X.

External theorems used (all classical):

* (W) Watkins 1970 and Mader 1971: κ ≥ 2(k+1)/3 for connected VT graphs. Atom theory: let a
  fragment be a set F with |N(F)| = κ and V \ (F ∪ N(F)) ≠ ∅, and an atom a fragment of minimum
  size. Then distinct atoms are disjoint, every vertex of a VT graph lies in an atom, atoms
  induce connected VT subgraphs, and an atom X and a fragment F satisfy X ⊆ F, X ⊆ N(F) or
  X ⊆ V \ (F ∪ N(F)). See Godsil–Royle, *Algebraic Graph Theory*, §3.3–3.4.
* (M) Mader 1971: the edge connectivity of a connected VT graph equals k.
* (NS) Nedela–Škoviera, *Atoms of cyclic connectivity in cubic graphs*, Math. Slovaca 45
  (1995): a connected cubic VT graph with cyclic edge cuts has cyclic edge-connectivity equal to
  its girth. Sanity check: `a2/cyclic.c` verifies this for all 29 connected cubic VT graphs on
  at most 22 vertices in the census files.

---

## 1. Structure of a minimal counterexample (all rigorous)

**Lemma 1.1 (nonempty remainder).** V(P) ≠ V.
*Proof.* If V(P) = V then diam G = n − 1, so G is the path P_n, which is not VT for n ≥ 3. ∎

**Lemma 1.2 (minimal separating geodesic).** Suppose some geodesic separates G, and let l be
the least length of a separating geodesic. If P separates with length l, then every component C
of G − V(P) has a neighbour of v_0 and a neighbour of v_l, and |N(C)| ≥ κ.
*Proof.* Suppose C has no neighbour of v_0 (so l ≥ 1). Then C is a component of
G − {v_1, ..., v_l}, which also contains v_0 ∉ C. So the geodesic (v_1, ..., v_l) of length
l − 1 separates, a contradiction. For the second claim, N(C) ⊆ V(P) separates C from the other
components, which are nonempty. ∎

From now on P = (v_0, ..., v_l) is such a geodesic. A is a smallest component and B is the
union of the other components, so 1 ≤ |A| ≤ |B| and |A| < n/2. G − A is connected (every
component of B touches the connected set V(P)).

**Lemma 1.3 (isometric amalgam).** For every union X of components of G − V(P), the induced
subgraph G[X ∪ V(P)] is isometric in G.
*Proof.* Take a geodesic Q between two vertices of X ∪ V(P). A maximal subpath of Q outside
X ∪ V(P) runs inside one other component, so it starts and ends at path vertices v_i, v_j.
Its length is at least d(v_i, v_j) = |i − j|, so replacing it by P[i..j] does not lengthen Q.
∎
So G is obtained from L_A = G[A ∪ V(P)] and L_B = G[B ∪ V(P)], both isometric, by gluing
along P with no A–B edges. For a ∈ A and b ∈ B, d(a,b) = min_t (d(a,v_t) + d(v_t,b)). This was
checked numerically on all 236 non-VT counterexample instances found (the 8 two-orbit ones and
228 twin-free polycirculants; `a2/verify_lemmas.py`).

**Lemma 1.4 (half-space lemma, = L1 of attempt 1).** This holds in any graph. Let S ⊆ V,
z ∉ S, and u ∈ V with d(u,s) ≤ d(z,s) for all s ∈ S. Then every x with d(z,x) < d(u,x) is
joined to z by a geodesic avoiding S.
*Proof.* If a z–x geodesic met s ∈ S, then d(u,x) ≤ d(u,s) + d(s,x) ≤ d(z,s) + d(s,x) = d(z,x).
∎
**Corollary 1.5.** For y ∈ N(v_0) \ {v_1}, the set W_{y v_1} lies in the component of y. Indeed
v_1 weakly dominates y on P: d(v_1, v_t) = |t − 1| ≤ d(y, v_t). The same holds in
G − {v_0, v_1} − Sh(v_2), where Sh(v_2) = {x : d(v_0,x) = 2 + d(v_2,x)}.

**Lemma 1.6 (pocket lemma, = L3).** Let X = N(A) ⊆ V(P). No automorphism φ satisfies
φ(X) ⊆ A.
*Proof.* G − A is connected and avoids φ(X), so it lies in one component of G − φ(X). That
component is either inside φ(A), impossible since |G − A| > |A|, or inside
φ(V \ (A ∪ X)), giving n − |A| ≤ n − |A| − |X|. ∎
**Corollary 1.6'.** For every a ∈ A, every index i and every automorphism φ with φ(v_i) = a,
the image φ(P) meets V(P). Otherwise φ(P) would be a connected set through a avoiding P, hence
contained in A, and φ(X) ⊆ A. For a Cayley graph Cay(Γ,S), with vertices v_i = s_1⋯s_i, this
reads A ⊆ ∩_i V(P)V(P)^{-1} v_i. Taking i = ⌊l/2⌋, φ(P) lies within distance ⌈l/2⌉ of a, so
every vertex of A is within ⌈l/2⌉ of P.

**Lemma 1.7 (swap lemma, = L4).** Choose (P, A) with l minimal and then |A| minimal over all
pairs (separating l-geodesic, component). Then every separating geodesic of length l that
avoids B contains v_0 and v_l. Hence it is a v_0–v_l geodesic. (Proof as in attempt 1: if
Q ⊆ A ∪ V(P) misses v_0, then B ∪ {v_0} lies in one component of G − V(Q). The other components
lie in (A ∪ V(P)) \ (V(Q) ∪ {v_0}), which has |A| − 1 vertices. But Q separates, so there is
another component, and it would have fewer than |A| vertices.)

**Lemma 1.8 (transmission-domination lemma; generalises T7).** Let G be transmission-regular
(Σ_w d(w,x) is independent of x). This holds for VT graphs. Equivalently, |W_xy| = |W_yx| for
every edge xy. Let C be a component of G − V(P) with |C| < n/2, and let z ∈ C and u ∈ N(z).
 (a) If d(u, v_t) < d(z, v_t) for every t, we get a contradiction.
 (b) If d(u, v_t) ≤ d(z, v_t) for every t, then W_zu ⊆ C and
 |W_uz \ C| ≤ |C| − 2|W_uz ∩ C| − |M_uz ∩ C|.
 Moreover w ∈ (V \ C) ∩ M_uz only if some shortest w–z path enters C through a vertex v_t with
 d(u, v_t) = d(z, v_t).
*Proof.* By Lemma 1.4 with S = V(P), W_zu ⊆ C. For w ∉ C, a shortest w–z path enters C through
some v_t, so d(w,z) = d(w,v_t) + d(v_t,z) ≥ d(w,v_t) + d(v_t,u) ≥ d(w,u). The first inequality
is strict in case (a), giving V \ C ⊆ W_uz. Then |C| ≥ |W_zu| = |W_uz| ≥ n − |C|, a
contradiction. Part (b) is the same bookkeeping, using C ⊇ W_zu ⊔ (W_uz ∩ C) ⊔ (M_uz ∩ C). ∎
Checks: in the three transmission-regular 2-orbit counterexamples, (a) has 0 violations, as it
must. In the non-TR twin-free counterexamples, (a) or (b) fails, often badly. For example, in
the 32-vertex cubic example of §5 the pair z = 27, u = v_4 gives |W_zu| = 5 and |W_uz| = 23.
See `a2/tr_viol.py` and `a2/wd_study.py`.

---

## 2. Classes for which the conjecture is proved

**Theorem 2.1 (lengths 0, 1, 2).** No geodesic of length ≤ 2 separates a connected VT graph on
n ≥ 3 vertices.
*Proof.* If k = 2, G = C_n and the complement of an arc is an arc (nonempty by Lemma 1.1).
If k ≥ 4, then κ ≥ ⌈10/3⌉ = 4 > 3 by (W). If k = 3, then κ = 3, so lengths ≤ 1 do not
separate. Let P = (a, b, c) separate, with l = 2 minimal. Each component touches a and c
(Lemma 1.2). Since a has only two neighbours off P, there are exactly two components C_1 and
C_2, and b's unique off-path neighbour lies in one of them, say C_1. Then N(C_2) ⊆ {a, c}, a
2-vertex cut, contradicting κ = 3. ∎

**Theorem 2.2 (twins).** If G has distinct x, y with N(x) = N(y) or N[x] = N[y], no geodesic
separates G.
*Proof.* By Thm 2.1, take l ≥ 3. Open twinship is an Aut-invariant equivalence relation, and
by transitivity all classes have the same size t ≥ 2. Open twins x, y are non-adjacent and have
d(x,w) = d(y,w) for every w ∉ {x, y}. If v_i ≡ v_j with i < j, then j − i = 2, and every other
index m satisfies |m − i| = |m − j|, forcing V(P) ⊆ {v_i, v_{i+1}, v_{i+2}}, i.e. l ≤ 2. So P
meets each class at most once, and every class keeps a vertex outside P. Given u, w off P and a
u–w path u = u_0, ..., u_r = w in G, replace each inner u_i by a class-mate u'_i ∉ V(P).
Consecutive u_i are adjacent, hence in different classes, and twins have equal neighbourhoods,
so u'_i ~ u'_{i+1}. This gives a u–w walk in G − V(P). Closed twins are the same argument:
closed twins on P would be consecutive and satisfy |m − i| = |m − i − 1| for every other m,
forcing l ≤ 1. Consecutive path vertices in the same class are merged. ∎

**Theorem 2.3 (local criteria).** Fix a vertex x.
 (i) If, for every y ∈ N(x), the graph G[N(x) \ {y}] is connected, no geodesic separates.
 (ii) More generally, suppose the following graph Λ(x; x_1, x_2) is connected for every geodesic
 (x, x_1, x_2). Its vertex set is N(x) \ {x_1}, and y ~ y' when they are adjacent or have a
 common neighbour outside {x, x_1, x_2}. Then no geodesic separates.
 (iii) In particular this holds if every two vertices at distance 2 have at least 4 common
 neighbours.
*Proof.* Take a minimal separating P with v_0 = x and l ≥ 3. Every component contains a vertex
of N(x) \ {v_1}, and no edge of G − V(P) joins two components. A common neighbour of two
vertices of N(x) lies within distance 2 of x, and the only path vertices there are
v_0, v_1, v_2. So the components induce a disconnection of the graph in (i) or (ii). ∎

**Theorem 2.4 (abelian Cayley graphs).** If G = Cay(Γ, S) with Γ abelian and |S| ≥ 7, no
geodesic separates G.
*Proof.* Thm 2.1 covers l ≤ 2, so take a minimal separating P with v_0 = 0 and l ≥ 3. Write
v_1 = s_1, v_2 = s_1 + s_2, Z = {0, s_1, s_1 + s_2} and S' = S \ {s_1}. For distinct
y, y' ∈ S', the vertex y + y' is adjacent to both. It is at distance ≤ 2 from 0, so it lies on
P iff it lies in Z. Let Λ be the graph on S' with y ~ y' iff y + y' ∉ Z. Each y has at most 3
non-neighbours in Λ, namely the elements of Z − y. If Λ is disconnected, both sides have at most
3 vertices. This settles |S'| ≥ 7. For |S'| = 6 both sides X, Y have exactly 3 vertices and
X + Y ⊆ Z, so Z = x + Y = x' + Y for x ≠ x' in X. Then Z has a nonzero period d, which forces
Z = {0, d, 2d} with 3d = 0. But then s_1 + s_2 = −s_1 ∈ S, contradicting d(0, v_2) = 2. So S'
lies in one component, contradicting Lemma 1.2. ∎
The combinatorial core was tested on 13,420 random abelian instances with no failure
(`a2/` inline test).

**Theorem 2.5 (atoms; twin-free case).** Let G be VT, twin-free, with κ < k. Then
 (a) every atom has at least 3 vertices;
 (b) for every separating geodesic P and every component C of G − V(P), |N(C)| ≥ κ + 1.
Consequently, in a twin-free VT graph a separating geodesic of length l needs k ≤ l + 1 when
κ = k, and κ ≤ l (hence k ≤ (3l − 2)/2) when κ < k. For l = 3 only k ∈ {3, 4} is possible.
*Proof.* (a) Since κ < k, atoms are not singletons. Let X = {x, x'} be an atom of size 2. By
(W), N(X) is a union of m ≥ 2 atoms and κ = 2m. Then k = 1 + |N(x) ∩ N(X)| ≤ 1 + κ, and κ < k
forces equality for both x and x', so N[x] = N[x'] = X ∪ N(X): closed twins. (b) If
|N(C)| = κ then C is a fragment, since the other components lie outside C ∪ N(C). Every atom
then lies in C, in N(C) or in the rest, and every vertex lies in an atom, so N(C) is a nonempty
union of atoms. Such an atom has ≥ 3 vertices by (a) and induces a connected VT subgraph of
G[N(C)]. But G[N(C)] is an induced subgraph of the path P, and a connected induced subgraph of a
path on ≥ 3 vertices is a path P_a with a ≥ 3, which is not VT. For l = 3 we have |N(C)| ≤ 4.
Then k = 5 gives κ = 4 < k, so |N(C)| ≥ 5, a contradiction; and k ≥ 6 gives κ ≥ 5 > 4. ∎

**Theorem 2.6 (cubic VT graphs).** Let G be cubic VT and let P separate with minimal length l.
Then there are exactly two components A, B. Each interior v_i has one off-path neighbour u_i,
so l + 3 = |∂A| + |∂B| (edge boundaries), and |∂C| = 2 + #{0 < i < l : u_i ∈ C}.
 (a) l ≥ 4. That is, geodesics of length ≤ 3 never separate a cubic VT graph.
 (b) (girth 3) G ≠ K_4 is the truncation T(H) of a simple cubic arc-transitive graph H, or the
 prism. Then l = 2m + 1 is odd, and the triangles met by P form a geodesic of length m in H
 whose deletion disconnects H. So a girth-3 counterexample on n vertices yields a cubic
 arc-transitive (hence VT) counterexample on n/3 vertices. For the converse one has to choose
 the end vertices so that the lifted path is a geodesic; I did not need it.
 (c) (girth g ≥ 5) l ≥ 2g − 3.
*Proof.* Tree pockets: if G[A] is a tree then |∂A| = |A| + 2. A leaf of A has two path
neighbours v_i, v_j with |i − j| ≤ 2, which gives a triangle or a 4-cycle, and |A| = 1 is
impossible for l ≥ 3.
(c) Since g ≥ 5, neither side is a tree, so ∂A and ∂B are cyclic cuts. By (NS) each has size
≥ g, so l + 3 ≥ 2g.
(b) In a cubic VT graph of girth 3 other than K_4, every vertex lies in exactly one triangle.
(A vertex in two triangles forces K_4 by transitivity.) The two off-path neighbours of v_0 lie
in different components, hence are non-adjacent. So the triangle of v_0 is {v_0, v_1, u_1},
and inductively the triangles along P are T_j = {v_{2j}, v_{2j+1}, w_j}; this forces l odd.
Contracting triangles gives a cubic multigraph H. Vertices of G correspond to arcs of H, so H
is arc-transitive, and it is simple unless H = θ_3 (G is the prism, diameter 2). The triangles
T_0, ..., T_m form an H-path, which is a geodesic: an H-path of length r < m would give a
v_0–v_l walk of length ≤ 2r + 1 < l. Its side edges and end edges go to non-path triangles by
simplicity and the geodesic property. G − V(P) is T(H − path) with pendant vertices w_j
attached, so it is connected iff H − path is connected.
(a) l ≤ 2 is Thm 2.1. For l = 3, both A and B touch an interior vertex since |N(·)| ≥ κ = 3,
so |∂A| = |∂B| = 3. Also |A|, |B| ≥ 2: a single vertex would be adjacent to v_0 and v_3. So ∂A
is a nontrivial 3-edge cut, and Lemma 2.9 (below) gives triangle blocks. Hence every vertex lies
in exactly one triangle (the unique outside neighbour rules out other triangles), i.e. we are in
case (b) with l = 3 = 2m + 1, m = 1. H would then have a separating geodesic of length 1, which
is impossible since κ(H) = 3. Alternatively, (NS) gives g = 3 directly. There is also a direct
check: with T(v_1) = {v_0, v_1, u_1}, the set A \ {u_1} has a 2-edge boundary, contradicting (M).
∎

**Corollary 2.7.** A separating geodesic in a twin-free VT graph has length l ≥ 4 unless k = 4.
For cubic VT graphs the bound improves using Lemma 2.9 below:
 * if g ≥ 4 (no triangles), every edge cut with both sides of size ≥ 2 has ≥ 4 edges. So
   l + 3 = |∂A| + |∂B| ≥ 8, i.e. **l ≥ 5**; and l ≥ 2g − 3 if g ≥ 5;
 * if g = 3, l = 2m + 1, where m is the length of a separating geodesic in the cubic
   arc-transitive graph H. Thm 2.1 for H gives m ≥ 3, so **l ≥ 7**.
So no geodesic of length ≤ 4 separates a cubic VT graph.

**Proposition 2.8 (the open case k = 4, l = 3).** Let G be twin-free VT of degree 4 and let P
be a separating geodesic of length 3. Then every local graph L(x) = G[N(x)] has at most one
edge, i.e. every vertex lies in at most one triangle.
*Proof.* By (W), κ = 4, so N(C) = V(P) for every component (Lemma 1.2). Since v_1 has two
off-path neighbours and every component touches v_1, there are exactly two components A, B.
Write N(v_1) = {v_0, v_2, a_1, b_1} and N(v_2) = {v_1, v_3, a_2, b_2} with a_i ∈ A, b_i ∈ B,
and Y = N(v_0) \ {v_1} = Y_A ⊔ Y_B with both parts nonempty. Since v_0 ≁ v_2 and a_1 ≁ b_1,
L(v_1) ⊆ K_{2,2}({v_0, v_2}, {a_1, b_1}), and likewise for L(v_2). By transitivity
e := |E(L(x))| is constant, and L(v_0) − v_1 has no Y_A–Y_B edge.

* e = 4: L(v_1) = C_4, so a_1, b_1 ∈ Y. L(v_0) ≅ C_4 contains the path a_1 v_1 b_1, so its
  fourth vertex is adjacent to both a_1 and b_1: an A–B edge.
* e = 3 (L ≅ P_4): if v_1 were an end of L(v_0), then L(v_0) − v_1 = P_3 would span
  Y_A ⊔ Y_B, giving an A–B edge. So v_1 has degree 2 in L(v_0), hence a_1, b_1 ∈ Y. L(v_1)
  then has v_0a_1, v_0b_1 and exactly one of v_2a_1, v_2b_1; say v_2a_1 (swap A and B
  otherwise). Then a_2 = a_1 and b_2 ≠ b_1. In L(v_2) the edges v_1b_2 and v_3a_1 are absent
  (the latter would give d(v_0, v_3) ≤ 2), so e(L(v_2)) ≤ 2. Contradiction.
* e = 2, L ≅ 2K_2: L(v_1) is a perfect matching, say {v_0a_1, v_2b_1}. Then b_2 = b_1 ≁ v_0.
  In L(v_0) the vertex v_1 has only the neighbour a_1, so the second edge joins the other two
  vertices of Y; they must lie in B, giving Y_A = {a_1}. In L(v_2) the edge v_1a_2 would force
  a_2 = a_1 ~ v_2, so the matching is {v_1b_1, v_3a_2}. Now X = A ∪ {v_1, v_2} has
  N(X) = {v_0, v_3, b_1}, a 3-vertex cut (Y_B ⊆ B \ {b_1} is nonempty), contradicting κ = 4.
* e = 2, L ≅ P_3 + K_1. Let c be the centre of the P_3 in L(v_1).
  - c = v_0: a_1, b_1 ∈ Y and L(v_0) = (a_1 v_1 b_1) + K_1, so a_1 has no neighbour in Y. In
    L(a_1), the edge v_0v_1 cannot be extended to a P_3: v_1 has no other neighbour in A, and
    v_0 has no neighbour in N(a_1) \ {v_1}. Contradiction.
  - c = v_2: a_1, b_1 ≁ v_0, so v_1 is isolated in L(v_0), and the P_3 of L(v_0) spans
    Y_A ⊔ Y_B: an A–B edge.
  - c = a_1 (c = b_1 is symmetric): a_2 = a_1 ~ v_0 and b_2 ≠ b_1. In L(v_2) on
    {v_1, v_3, a_1, b_2}, the edge v_1a_1 is present, while v_1b_2 and v_3a_1 are absent. So
    L(v_2) is K_2 + 2K_1 or 2K_2, never P_3 + K_1.

∎

So for l = 3 only k = 4 with e ∈ {0, 1} remains open (triangle-free, or every vertex in exactly
one triangle). The 16-vertex 4-regular 4-connected example of §5.1 has e varying in {1, 2, 3}.

**Lemma 2.9 (super edge-connectivity).** Let G be connected VT of degree k ≥ 3 with n ≥ 6.
Suppose some edge cut ∂X has |∂X| = k and |X|, |V \ X| ≥ 2. Then V is partitioned into blocks
inducing K_k, and every vertex has exactly one neighbour outside its block. In particular every
local graph contains K_{k−1}. (This is classical: Tindell 1996, Meng 2003. Proof for
completeness below.)
*Proof.* By (M), λ = k. Choose such an X of minimum size a; replacing X by V \ X if needed,
a ≤ n/2. Call such sets super-atoms.
1. G[X] is connected. Otherwise ∂X would split into two cuts, each of size ≥ k.
2. Distinct super-atoms X, Y are disjoint. Suppose X ∩ Y ≠ ∅. Edge boundaries satisfy
   |∂(X\Y)| + |∂(Y\X)| ≤ |∂X| + |∂Y| = 2k and |∂(X∩Y)| + |∂(X∪Y)| ≤ 2k.
   - If |X \ Y| ≥ 2, both differences are nontrivial (their complements have ≥ n/2 vertices),
     so |∂(X \ Y)| = k with |X \ Y| < a. Contradiction.
   - If |X \ Y| = 1 and a ≥ 3, then X ∩ Y (size a − 1 ≥ 2) and X ∪ Y (complement of size
     ≥ n − a − 1 ≥ 2) are nontrivial, so |∂(X∩Y)| = k. Contradiction.
   - If a = 2, then |∂X| ≥ 2k − 2 > k.
3. By transitivity the super-atoms partition V into blocks, and the setwise stabiliser of X is
   transitive on X. So G[X] is d-regular and k = |∂X| = a(k − d). Hence a divides k, so a ≤ k.
   From d ≤ a − 1 we get k(a − 1)/a ≤ a − 1, i.e. k ≤ a. So a = k, d = k − 1 and G[X] = K_k. ∎

Numerical check (`a2/superlam.c`): among the 2,107 connected VT graphs with degree ≥ 3 and
6 ≤ n ≤ 20 in the census files, 13 have a nontrivial k-edge cut, and all 13 have the K_k-block
structure.

**Remark (cubic l = 3 without (NS)).** For k = 3 a nontrivial 3-edge cut gives triangle blocks.
So in Thm 2.6(a) one may use Lemma 2.9 instead of (NS): ∂A is a 3-edge cut with |A| ≥ 2, so G
has girth 3 with every vertex in exactly one triangle, and part (b) finishes. (NS) is still needed
for Thm 2.6(c).

**Proposition 2.10 (k = 4, l = 3, continued).** In the situation of Prop 2.8:
 (a) |∂A| = |∂B| = 5. Moreover, after possibly swapping A and B, |Y_A| = 1, |Y_B| = 2,
 |Z_A| = 2, |Z_B| = 1 (Z = N(v_3) \ {v_2}).
 (b) a_1 ≠ a_2 and b_1 ≠ b_2. Also a_1, a_2 ≁ v_0 and b_1, b_2 ≁ v_3. The unique vertex of Y_A
 and the unique vertex of Z_B have exactly one neighbour on P.
 (c) If e = 1, then the triangles at the path are T(v_0) = T(v_1) = {v_0, v_1, b_1} and
 T(v_2) = T(v_3) = {v_2, v_3, a_2}. The configuration is invariant under reversing P together
 with swapping A and B.
*Proof.* (a) Counting gives |∂A| + |∂B| = 4·4 − 2·3 = 10, and |∂A|, |∂B| ≥ 4 by (M). If one of
them equals 4, Lemma 2.9 gives K_4 blocks, hence e ≥ 3, contradicting Prop 2.8. So both equal 5.
Now |∂A| = 2 + |Y_A| + |Z_A|, |Y_A| + |Y_B| = |Z_A| + |Z_B| = 3, and all four are ≥ 1.
(b) Each claim comes from a vertex set A ∪ S or B ∪ S (S ⊆ V(P)) whose neighbourhood would
have only 3 vertices, contradicting κ = 4. Note N(A ∪ S) = (V(P) \ S) ∪ (N(S) ∩ B):
 - S = {v_1, v_2} gives b_1 ≠ b_2, and symmetrically a_1 ≠ a_2.
 - S = {v_0, v_1} rules out Y_A = {a_1}, and S = {v_0, v_2} rules out Y_A = {a_2}. Both use
   the cut N(B ∪ S).
 - The same arguments at the v_3 end rule out Z_B = {b_2} and Z_B = {b_1}.
 The non-adjacencies follow, since |Y_A| = |Z_B| = 1.
(c) T(v_1) cannot be {v_1, v_2, x}, since x would be a_1 = a_2 or b_1 = b_2. So
T(v_1) = {v_0, v_1, x} with x ∈ Y ∩ {a_1, b_1} = {b_1}. Symmetrically T(v_2) = {v_2, v_3, a_2}. ∎

These were the last structural facts I could derive for k = 4, l = 3. Finishing needs the
transmission-domination lemma 1.8 applied to y_A and a_1 (strictly dominated unless
y_A ~ a_2 or d(y_A, v_3) ≤ 3, and a_1 must come within distance 2 of v_3), together with a
count of 4-cycles.

---

## 3. Where transitivity is used

* All eight 2-orbit regular counterexamples (16 to 40 vertices) are *twin shadows*. The pocket
  A consists of twins of interior path vertices: in the 16-vertex theta graph with
  P = 0,1,10,5,9, A = {2,11,12,6} with 2 ≡ 1, 11, 12 ≡ 10 and 6 ≡ 5. All eight have κ = 2 and
  non-uniform twin classes. In a VT graph twin classes are uniform, and Thm 2.2 kills them.
* Twin-free counterexamples need "poles" (special vertices). Every counterexample found has at
  least 2 distance profiles.

---

## 4. The two-step law, restated

For a geodesic (a, b, c), the law says that N(a) \ {b} lies in one component of
H(a,b,c) = G − {a,b} − (W_ba ∩ W_cb). Here W_ba ∩ W_cb = Sh_a(c) is the shadow of c. It
decomposes as H = U ∪ R, where:

* U = {x ≠ a : d(x,a) ≤ d(x,b)} is star-shaped from a: every geodesic to a stays in U ∪ {a},
  so each component of U contains a vertex of N(a) \ {b}.
* R = {x ≠ b : d(x,a) = d(x,b) + 1, d(x,b) ≤ d(x,c)} is star-shaped from b, so each component
  of R contains a vertex of N(b) \ (N[a] ∪ {c}).

The law says that the R-components bridge all U-components meeting N(a) \ {b}. The depth-1
law (U alone) fails in 52 twin-free VT graphs on at most 24 vertices (mostly bipartite, with
|W_ab| = n/2). The two-step law never failed on any VT graph tested.

---

## 5. New negative results (certificates)

**5.1 Twin-free, regular, 3-connected counterexamples (non-VT).** These came from random
regular polycirculants (`a2/polycirc2.py` and `a2/pcgen.cpp`, then the exact checker
`src/gd`). There are 228 twin-free counterexample instances (not deduplicated); see
`a2/kappa.py`. Their (κ, k) counts are (2,3): 153, (2,4): 12, (2,5): 1, (3,3): 57, (4,4): 5.
The 3-connected ones are:

* cubic with κ = 3: l = 6 (n = 24), l = 7 (n = 28, 32), l = 8 (n = 32, 36, 48);
* 4-regular with κ = 4: l = 3 (n = 16) and l = 6 (n = 32).

The 16-vertex one, graph6 `OQ??OHQgQoS_b@PgCY?qO` with P = (12,5,7,14), is relevant to the
open case k = 4, l = 3. Its local graphs have 1, 2 or 3 edges at different vertices, which a VT
graph cannot have (compare Prop. 2.8). Two further certificates follow.

* 32 vertices, cubic, κ = 3, transmissions {104, 122, 130},
  graph6 `_CQa`O????????????????H??Q??Q??H??AO?GO??`??@A?G?CGCG?C@A?@?GO?G?`A??@AC?C?AC?A?@A??`.
  P = (8,25,3,0,5,2,7,29,12) is a geodesic of length 8. G − V(P) has components
  {10,13,15,18,20,21,23,24,27,30} and {1,4,6,9,11,14,16,17,19,22,26,28,31}. The adjacency list
  is printed by `a2/certs.py`. Vertices 0..7 form a "hub" 8-cycle; P runs along half of it.
* 16 vertices, cubic, transmissions {34, 39, 46}, graph6 `O?EA@@IHOsOgG?C?o?I?D`.
  P = (0,5,9,2), length 3; components {7,11} and the other 10 vertices. This is the
  *prism gadget*: triangles {0,5,11} and {2,9,7} joined by the edges 5–9 and 11–7. It is
  2-connected only, since the gadget hangs on the two ports 0 and 2.

**5.2 Transmission regularity is not enough.** The *prism-gadget necklace* N_r is built from r
gadgets j = 0..r−1, each on vertices p, q, a, b, c, d = 6j..6j+5. The gadget edges are
pa, pc, ac, qb, qd, bd, ab and cd, and the external edges are q_j p_{j+1}. N_r is cubic and
twin-free, and for **every odd r it is transmission-regular** (checked for r = 3, 5, 7, 9, 11:
n = 18, 30, 42, 54, 66, with common transmissions 55, 151, 295, 487, 727). In each, the path
(p_0, a_0, b_0, q_0) = (0,2,3,1) is a geodesic and G − V(P) has the component {c_0, d_0} = {4,5}.
Script: `a2/gadget_necklace.py`; the exact checker confirms all five. N_r is not DDR, not
walk-regular (ports lie on no 4-cycle, rails do) and has κ = 2. **Consequence:** no proof can
rely only on transmission-regularity, twin-freeness and regularity, and Lemma 1.8 cannot be
the engine of a proof by itself.

**5.3 Positive evidence for stronger hypotheses (computational, not proved).**

* Transmission-regular: 5,221 + 703 unique non-VT twin-free regular polycirculants (2 to 6
  orbits) have 0 separating geodesics. With the same generator and no TR filter, 22 of 8,231
  unique graphs are counterexamples. This is now superseded by 5.2, but it shows TR graphs
  rarely have them.
* Distance-degree-regular (every vertex has the same sphere sizes): 340 unique non-VT DDR
  twin-free polycirculants (3 to 6 orbits) and the 876 non-VT DDR graphs of the 2-orbit census
  (231 twin-free, 645 with twins) have 0 separating geodesics (`src/gd -all`). It is open
  whether DDR (perhaps with twin-freeness) implies the conclusion. That would be a purely metric
  theorem implying the conjecture.

---

## 6. Computational status of the two-step law and of local certificates

* Two-step law (depth-2 pruning always succeeds) re-verified on all 18,969 connected VT graphs
  in `data/vt10..vt24.g6` and `small_cayley.g6`: depth histogram {0: 18843, 1: 126}, so nothing
  survives depth 2. Attempt 1 additionally recorded this for the cubic census, cubic Cayley
  graphs to 5000 vertices, and parts of orders 24 to 46.
* Certificates on twin-free VT graphs with at most 23 vertices (3,211 graphs, every geodesic
  (0,b,c)), for y, y' ∈ N(a) \ {b} (script `a2/combos.py`):
  * Wadj: W_yb and W_y'b intersect or are joined by an edge.
  * Uc: some vertex lies in Desc_a(y) ∩ Desc_a(y') \ Desc_a(c), a common "upper" vertex
    outside the shadow of c.

  Neither certificate alone suffices: Wadj fails in 22 graphs and Uc in 449. **Uc ∪ Wadj always
  connects N(a) \ {b}** (0 failures). By Lemma 1.4 both certificates are valid connections in
  H(a,b,c), so a proof that Uc ∪ Wadj connects N(a)\{b} in every twin-free VT graph would prove
  the conjecture. In bipartite graphs, Wadj is about the cones U(y) \ U(b), because there
  W_yb = Desc_a(y) \ Desc_a(b). In bipartite VT graphs every cone has exactly n/2 vertices and
  |Desc(y) ∩ Desc(y')| = 1 + #{x ≠ a : x ∉ Desc(y) ∪ Desc(y')}.

---

## 7. What remains

A complete proof needs: **no twin-free VT graph with k ≥ 3 has a separating geodesic of length
l ≥ 3, where l is minimal.** The proved results narrow this: for l = 3 only k = 4 with at most
one triangle per vertex remains (Thm 2.5, 2.6, Prop 2.8); for general l, k ≤ max(l+1, (3l−2)/2)
(Thm 2.5); κ ≥ 3; every component touches both ends and at least κ path vertices, or κ + 1 when
κ < k. Twins, short lengths, locally connected or dense graphs (Thm 2.3) and abelian Cayley
graphs of degree ≥ 7 are done. For cubic graphs, what remains is girth 4 with l ≥ 5 and girth
≥ 5 with l ≥ max(5, 2g − 3). Girth-3 cubic graphs reduce to cubic arc-transitive graphs with a
separating geodesic of length (l − 1)/2 ≥ 3: a girth-3 counterexample would give an
arc-transitive one.

Why the natural approaches fail:

* Metric or counting arguments alone (TR, W-balance, Lemma 1.8) cannot work, by 5.2. DDR is
  untested theoretically.
* Atom-style crossing arguments fail because the intersection of two geodesic pockets is bounded
  by two geodesic pieces meeting at a corner, which is not a geodesic. The family is not closed.
* Pocket and swap lemmas give "every automorphic image of P through A crosses P"
  (Cor 1.6'), but for GRRs (trivial vertex stabilisers) only translates are available. In the
  abelian case this already forces strong additive coincidences (A ⊆ ∩_i (v_i + P − P) and
  A ⊆ ∩_i (P + P − v_i)). Turning that into a contradiction for small degree is a finite but
  unfinished case analysis.

Most promising next steps:

1. Prove the Uc ∪ Wadj linking statement (§6) for twin-free VT graphs, perhaps first in the
   bipartite case, where both certificates are statements about BFS cones from a.
2. Decide whether DDR + twin-free suffices. Try to make a DDR version of the gadget necklace;
   gadget-based constructions are the natural place to look for such a counterexample.
3. Finish cubic girth 4 (tree pockets with leaves straddling path vertices, plus cyclic 4-cuts).
   Finish k = 4, l = 3 in the two remaining local types: triangle-free, or every vertex in
   exactly one triangle. Prop 2.10 already gives |∂A| = |∂B| = 5, |Y_A| = |Z_B| = 1, and (for
   e = 1) the triangles {v_0,v_1,b_1}, {v_2,v_3,a_2}. What is left is to combine Lemma 1.8 with
   4-cycle counts.
4. Use Lemma 2.9 more widely. In a twin-free VT graph without K_k blocks, every component has
   edge boundary ≥ k + 1. The K_k-block case is a clique-blowup of a k-regular arc-transitive
   graph H. As in Thm 2.6(b), it should reduce to an edge-deletion question on H: can the edges
   of a geodesic, together with 2 end edges, form an edge cut?
