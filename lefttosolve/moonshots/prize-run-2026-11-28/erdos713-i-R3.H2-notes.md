# Erdos713.erdos_713.parts.i.R3.H2 — notes

Statement (reduction R3 by @mucoucah, upstream reductions/Erdos713.erdos_713.parts.i.R3.lean):

    H2 : ∀ q (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ #E(G) → (∀ v, ¬ G.IsIsolated v) →
         ¬ G.Connected → G.IsAcyclic → (∀ n, ex(n,G) ≤ q n) →
         ∃ c > 0, ex(n,G)/n → c

Competitor check 01:27 UTC 28 Nov 2026: no open PR for this id, not upstream.

## Mathematics (own proof, written from scratch)

Write F for the forbidden graph on [q], a(n) = ex(n,F). Only three facts about F are used:
no isolated vertex, a(n) ≤ q n (given), a(n) ≥ n/2 (reduction lemma extremal_linear_lower).
Acyclicity, bipartiteness and disconnectedness are not used directly.

### 1. Hubs, patterns, witnesses
H a graph on V, X ⊆ V a nonempty set (the hubs), R = V \ X.
A pattern is a pair (W, g), W ⊆ [q], g : [q] → X.
A witness for (W,g) is h : W → R injective, edge preserving on F[W], such that
for w ∈ W, a ∉ W, wa ∈ E(F): h(w) ~ g(a) in H.
(W,g) is dead if it has no witness, robust if for every S ⊆ V with |S| ≤ q some witness avoids S.
(H,X) is clean if every pattern is dead or robust.
Witnesses are monotone in H: a subgraph has fewer witnesses.

### 2. Elimination lemma
If every v ∉ X has degree ≤ Δ then there is H'' ≤ H clean with e(H) ≤ e(H'') + K q Δ,
K = 2^q |X|^q = number of patterns.
Proof: induction on the number of live (= non-dead) patterns. If (W,g) is live and not robust, take S,
|S| ≤ q, meeting every witness, and delete all edges at S \ X (≤ qΔ edges). A witness of the new graph is
a witness of the old one, so it puts some w ∈ W on a vertex of S \ X; w has a neighbour in F (no isolated
vertices), either inside W or outside W, and in both cases the image of w needs an edge. So (W,g) is dead
now and stays dead; the number of live patterns dropped.

### 3. Blow-up lemma
B_t = blow-up of H around X: vertices X ∪ (R × [t]), hubs joined to every copy of R as in H, copies of R
pairwise non adjacent. (In Lean: vertex set V × Fin (t+1), hubs live in layer 0, the other hub copies are
isolated dummies.)
If H is F-free and (H,X) is clean then B_t is F-free.
Proof: let f : F → B_t be an embedding, p the projection to V. A collision is a pair u ≠ v with
p f u = p f v. Induct on the number of collisions. No collision: p∘f embeds F in H. Otherwise the two
vertices lie in different layers i ≠ j over the same r ∈ R (uses: no isolated vertex in F, so image vertices
over hubs are in layer 0). Let W = vertices of F mapped into layer i over R, g = p∘f on f⁻¹(X) (anything on
the rest). Then p∘f|W is a witness for (W,g): a neighbour a ∉ W of w ∈ W cannot be over R (it would be in
the same layer), so it is over a hub. So (W,g) is live, hence robust: take a witness h avoiding
S = p f (Wᶜ), and re-embed W by w ↦ (h w, i). This is again an embedding and all collisions involving W
are gone, none is created.

### 4. Degree gap (pigeonhole)
H extremal on N ≥ 1 vertices, e(H) = a(N) ≤ qN. Fix k ≥ 1. c_0 = 1, c_{i+1} = k q 2^q (2 q c_i + 1)^q.
X_i = {v : N ≤ c_i deg v}; |X_i| ≤ 2 q c_i since Σ deg ≤ 2qN. M_i = X_{i+1} \ X_i are disjoint, so for
some i < 2qk the degree sum over M_i is ≤ N/k. Delete all edges at M_i: H'. Hubs X = X_i ∪ {v0}.
Every v ∉ X has c_{i+1} deg_{H'} v ≤ N. Elimination costs K q Δ ≤ N/k by the choice of c_{i+1}.
Result: H'' ≤ H clean w.r.t. X, |X| ≤ s_k := 2 q c_{2qk} + 1, k e(H'') ≥ k a(N) − 2N.

### 5. Amplification
B_t has N(t+1) vertices and ≥ (t+1)(e(H'') − s(s+1)/2) edges (each edge with an endpoint outside X is
copied t+1 times). So
    a(N(t+1)) ≥ (t+1) (a(N) − 2N/k − s_k²)      for all N ≥ 1, t ≥ 0, k ≥ 1.

### 6. Limit
a is monotone (add isolated vertices; F has none). u_n = a(n)/n ∈ [0,q], L = limsup u_n ≥ 1/2.
Given ε, pick k with 2/k ≤ ε, then N large with u_N > L − ε and s_k²/N ≤ ε:
a(tN) ≥ tN(L − 3ε) for all t, and monotonicity gives u_n ≥ L − 4ε for n ≥ N L/ε. So liminf = limsup.

## Literature
Exact values (hence limits) are known for path forests and star forests (Bushaw–Kettle 2011,
Lidický–Liu–Palmer 2013) and some mixed families. Searches on 28 Nov 2026 (forest Turán number, limit of
ex(n,F)/n, Fekete/superadditivity for forests) found no statement that the limit exists for every forest.
The argument here was written from scratch and is elementary (pattern/hub cleaning + blow-up); I make no
novelty claim for the mathematics beyond not having found it in print.

## Computer experiments
- sanity.py: random hosts (9-11 vertices, 1-2 hubs), forests 2K2, P3+K2, P4, K13, P3, 2P3: run the
  elimination until clean, then search the 3-layer blow-up for F by brute force. 206 trials, 83 non-trivial
  clean F-free graphs, 0 violations. The script also asserts that an eliminated pattern is dead afterwards.
- sanity_teeth.py: same without cleaning: the blow-up of an F-free graph contains F in 308/558 (2K2),
  684/1045 (P3+K2), 274/947 (P4) cases, so the cleaning step is what makes the lemma true.

## Lean
- Final file: oma-check/proofs/Erdos713.erdos_713.parts.i.R3.H2.lean (798 lines, copy in this directory),
  sha256 a26a35a4054e68a382bb9516e1168c44a5d118b242e0752e606489596abb009e.
- Structure: IsWit / Robust / Clean / live, delAt (+ edge count), exists_clean (elimination), blow,
  blow_step, blow_free, lift, card_edgeFinset_blow, cseq, exists_gap (pigeonhole), exists_clean_sub,
  exists_extremal, amplify, extremalNumber_mono, tendsto_of_amplify, OMA.solution.
- Uses from the reduction module only extremal_linear_lower (n/2 ≤ ex(n,G)) for positivity of the limit.
- Hypotheses of H2 actually used: no isolated vertex, 2 ≤ #edges (for q > 0 and the lower bound),
  ex(n,G) ≤ q n. Bipartite / disconnected / acyclic are not used, so the same helpers prove the sibling
  statement R4.H1 verbatim (that step has a rival open PR 15994, not touched).
- Development pieces: lean/p1..p6.lean, lean/t5.lean, lean/final.lean.

## Log
- 01:27 UTC competitor check clean (no open PR, not upstream).
- 01:36 proof found and written down; 01:38 sanity experiments pass.
- 01:39 reduction module built in the pinned checkout (identical to upstream reductions file).
- 01:52 full Lean proof compiles; axioms propext, Classical.choice, Quot.sound.
- 01:55 official lint ok, tools/check.sh verdict: accepted (verdict.json, lint.json here).
- 01:56 competitor check again: no open PR with this id (only the merged reduction PR 8020), no
  proofs/Erdos713.erdos_713.parts.i.R3.H2.lean upstream at commit 1c6393ba.
