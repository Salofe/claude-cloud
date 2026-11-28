# Moonshot: Gillibert's fair-traversal conjecture (lefttosolve `gillibert-fair-traversal`)

**Result: not resolved.** No counterexample was found and no proof was written. A proof would imply Lovász's conjecture, so the only realistic "first" was a computer-found counterexample with a Lean disproof. Nothing was submitted.

The conjecture was posed on 17 Nov 2026 by Luc Gillibert (with GPT) on lefttosolve.com. It says that every connected vertex-transitive graph has a family of Hamiltonian paths that uses every edge orbit fairly. Before this run it had only been tested on circulants with at most 14 vertices.

## Reformulation
Averaging over Aut(G), the statement holds for G if and only if the vector of edge-orbit sizes lies in the cone spanned by the orbit-count vectors of Hamiltonian paths. A disproof needs orbit weights w with w·m ≤ 0 and w·c(P) > 0 for every Hamiltonian path P.

## Verified (every graph passes, each with a re-validated certificate)
- All 182 connected Cayley graphs of orders 2–9, which is every connected vertex-transitive graph of those orders.
- The Holt–Royle census, all connected vertex-transitive graphs of orders 10–39, 41, 43, 45 and 47: **4,684,251 graphs**.
- Orders 40, 42, 44 and 46 with degree ≤ 12: 1,268,890 graphs.
- The cubic vertex-transitive census, all 50,113 graphs on ≤ 864 vertices, plus 2,423 graphs on 866–1280 vertices.
- Exact enumeration of the Hamiltonian-path count vectors for all 290 cubic vertex-transitive graphs on ≤ 64 vertices.

Cross-checks: an independent Python brute force agrees on all graphs of orders 10–14, and 319 certificates were re-verified independently.

Three graphs defeated the heuristics. Each was resolved by an explicit construction and then verified:
- CVT[876,4]: an alternating Hamiltonian cycle.
- CVT[1264,187]: obtained from GP(316,157).
- CVT[1152,3767]: "face cycles plus bands" on a regular map of type {24,3}.

## Partial results (pen and paper)
1. **Truncations.** For an arc-transitive graph B, fairness of its truncation T(B) is equivalent to B having a Hamiltonian path. On truncations the conjecture is therefore exactly Lovász's conjecture for arc-transitive graphs.
2. **Local bounds.** Among bounds coming from a single orbit or a single block system (cut bound, path-cover bound), only truncations are tight.
3. **Parity.** For cubic graphs with a 2-factor of 4-cycles, parity arguments alone can never refute fairness. The extreme case is the 2-arc graphs, with margin exactly 5/3.
4. **Flag graphs of cubic maps** form a new tight family. Their bands use exactly 2V−2 change-vertex edges, against a fair value of 2V.

**Conclusion.** A counterexample would need a new, non-local obstruction, and a Lean disproof is out of reach.

Sources: `gillibert-fair-traversal/` holds the checkers (ft.c, ftc_t.c, exact.c), the independent verifiers (ref.py, verify_cert.py, hex/) and the full findings (findings.json).
