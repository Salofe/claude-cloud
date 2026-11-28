# Gillibert geodesic-deletion conjecture: Fable 5.2 long-shot attempt (2026-11-27)

Problem: https://lefttosolve.com/p/gillibert-geodesic-deletion

Outcome: **partial**. No proof and no counterexample; nothing submitted. Below is the agent report verbatim (computations and pen-and-paper lemmas, not machine-checked).

No full proof and no counterexample. No Lean file was written (proofs/gillibert-geodesic-deletion.lean does not exist), so nothing was submitted. What I have is a much larger verified range and a set of pen-and-paper partial results that isolate the remaining obstruction.

STATEMENT CHECK. The Lean statement matches the source note: every vertex of the walk is deleted, the one-vertex geodesic is included, and Connected requires a nonempty remainder.

COMPUTATION (0 counterexamples everywhere)
Method: exact search for a minimal separating geodesic from one base vertex. A separating geodesic contains a minimal one, whose components all touch both ends; transitivity moves its start to the base vertex. A prefix (v0..vi) is pruned when the neighbours of v0 other than v1 are already joined in G minus the prefix minus all BFS-descendants of vi. Validated against brute force on 260,000 random graphs (identical verdicts, about 88,000 positives). A bitset version (gd64.cpp) gives identical node counts.
- All vertex-transitive graphs on at most 47 vertices. Holt-Royle census, orders 10-47: 100,720,344 graphs, which equals the published total 100,720,391 minus the 47 graphs of order below 10. Of these, 99,576,398 are in the orders the triage had not checked (36: 1,963,202; 38: 814,216; 40: 13,104,170; 42: 9,462,226; 44: 39,134,640; 45: 399,420; 46: 34,333,800; 47: 364,724). I also re-ran the triage's orders 10-35, 37, 39, 41, 43 (1,143,946 graphs). Orders 3-9: all Cayley graphs (263 labelled, 200 connected), which covers every vertex-transitive graph there.
- Cubic vertex-transitive census (Potocnik-Spiga-Verret), all 111,360 graphs up to 1280 vertices. Brute force without pruning on the first 10,000 (up to 390 vertices) also found nothing; 157 of those hit the 3M-node cap.
- Cubic Cayley graphs up to 5000 vertices (graphsym atlas, streamed): 1,791,850 graphs for orders 4-4776 plus 150,122 for orders 4774-5000 (two orders overlap).
- 4-valent arc-transitive up to 640 vertices (4,820); 4-valent 2-arc-transitive up to 2000 (165); 5-valent arc-transitive (95); Census4valSS (2,956, all base vertices); 701 regular edge-transitive graphs up to 47 vertices, all base vertices; 400 random Cayley graphs on symmetric, metacyclic, Heisenberg and abelian groups up to 19,736 vertices; 101 classical graphs (Kneser, Johnson, Hamming, folded and halved cubes, tori, lexicographic products).
- Empirical two-step law: wherever I recorded depth, the search never survived depth 2. That is, for every geodesic (v0,v1,v2), the neighbours of v0 other than v1 lie in one component of G - {v0,v1,v2} - {x : d(v0,x) = d(v2,x)+2}. Depth was recorded for the cubic census, cubic Cayley to 5000, the arc-transitive censuses, order 24, order 42 degrees 0-23, order 44 degrees 21-43 and order 46 degrees 19-45. This statement implies the conjecture.
- Transitivity is really needed: 8 regular graphs with two edge orbits (16-40 vertices, e.g. a 16-vertex 4-regular blown-up theta graph with geodesic 0,1,10,5,9) have separating geodesics, and 3 of them are transmission-regular. None of 876 provably non-transitive distance-degree-regular graphs from that census has one.

PROVED ON PAPER (not machine-checked; L1-L3 tested numerically, about 1.4 million instances, 0 violations)
L1 Half-space lemma (any graph, any set S). If z is outside S and d(u,s) <= d(z,s) for all s in S, then every x with d(z,x) < d(u,x) is joined to z by a geodesic avoiding S.
L2 Domination. For a geodesic P = (v_0..v_l) and z off P there is s with d(z,v_t) >= |t-s| for all t. So everything strictly closer to z than to v_s lies in z's component. In particular, for y adjacent to v_0 and off P, {x : d(y,x) < d(v_1,x)} lies in y's component.
L3 Pocket lemma. If |A| < n/2 and G - A is connected, no automorphism maps N(A) into A. Consequence: every vertex of a non-giant component of G - V(P) is within ceil(l/2) of its complement.
L4 Swap lemma. Take the least separating length l, then the smallest component A, with B the union of the other components. Any separating geodesic of length l that avoids B contains both ends of P.
T5 Lengths 0, 1, 2 never separate a connected vertex-transitive graph on at least 3 vertices (minimal component, then closed-twin classes for length 2). Hence the conjecture holds for diameter at most 2.
T6 Unique antipodes. If all eccentricities equal D and each vertex has exactly one vertex at distance D, no geodesic separates (L2 applied to the antipode of v_1). This covers hypercubes, even cycles and Cayley graphs of finite Coxeter groups on simple reflections; no transitivity is used. It also held on 1,045 census graphs meeting the hypothesis, 543 of them non-transitive. More generally, no minimal separating geodesic starts with (v_0,v_1) if some x at distance D from v_1 is closer than D to every other neighbour of v_0.
T7 Perpendicular attachments. In a transmission-regular graph, a component containing a neighbour z of v_s with d(z,v_t) = |t-s|+1 for all t has at least n/2 vertices. Corollary: girth g implies no separating geodesic of length at most (g-2)/2.
T8 Bipartite case. In a bipartite vertex-transitive graph, every vertex of a component smaller than n/2 that is adjacent to P lies on a geodesic between two vertices of P. With L4 and an open-twin count this rules out length 3, so the conjecture holds for bipartite vertex-transitive graphs of diameter at most 3.

REMAINING GAP. Components whose vertices all lie on (or one step off) geodesics between path vertices: a thick strand between the two ends, as in the 16-vertex theta graph. L1-L4 say nothing there; the known ways out are block-system or connectivity arguments (twin classes, no 2-cuts, cyclic edge-connectivity), which I completed only for length at most 2 (all) and 3 (bipartite). The image of P can also cross from A into the other components, and transmission-regularity alone cannot decide it (the 3 counterexamples above).

FILES (all under lefttosolve/moonshots/gillibert-geodesic-deletion/ (copied from the session scratchpad))
- src/gd.cpp, src/gd2.cpp (depth statistics), src/gd64.cpp (bitset): checkers
- src/test_lemmas.py: numeric tests of L1-L3
- logs/: per-order results (hr*.log, cub3*.out, cubcay*.out)
The census downloads were deleted after use.


## Attempt 2 (28 Nov, Opus, ~78 min): partial, no full proof, no counterexample
Full write-up: `gillibert-geodesic-deletion/proof_attempt2.md`. New results (pen and paper, numerically checked):
- **Twins:** a connected vertex-transitive graph with open or closed twins has no separating geodesic; all 8 known
  2-orbit counterexamples are "twin shadows" of this kind.
- **Isometric halves:** a separating geodesic splits G into two isometric pieces glued along P.
- **Transmission-domination lemma** (generalises T7) and local sufficient criteria (neighbourhood graphs 2-connected,
  >= 4 common neighbours at distance 2); abelian Cayley graphs of degree >= 7 are done.
- **Atoms:** in twin-free graphs with connectivity < degree, every component touches >= kappa+1 path vertices, so a
  separating geodesic of length 3 forces degree 3 or 4.
- **Cubic graphs:** no geodesic of length <= 4 separates; girth 3 reduces to truncations of cubic arc-transitive graphs
  (a counterexample would give one on n/3 vertices); girth >= 5 forces length >= 2g-3.
- **Degree 4, length 3:** the only open length-3 case; its local structure is pinned down.
- **New counterexamples to stronger statements:** twin-free, regular, 3- and 4-connected non-transitive graphs, and cubic
  transmission-regular "prism-gadget necklaces" (18-66 vertices) with separating geodesics of length 3, so any proof
  must use more of vertex-transitivity than transmission regularity plus twin-freeness.
- Computation: the two-step law holds on all 18,969 local census graphs; two simple certificates (Uc, Wadj) always
  connect the neighbours of v0 on twin-free vertex-transitive graphs with <= 23 vertices (proving that would prove the
  conjecture).
Remaining: twin-free vertex-transitive graphs of degree >= 4 with minimal separating length >= 3 (for length 3 only a
rigid degree-4 structure), and cubic girth-4 length >= 5 / girth >= 5 length >= max(5, 2g-3).
