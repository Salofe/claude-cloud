# Fable run on "first-ever" open problems (28 Nov 2026)

Fable read the triage notes of 2,024 unclaimed open problems on lefttosolve, picked three that were unclaimed and had a realistic chance of a first-ever resolution, and attacked each one in a long session. **None was resolved.** Partial results:

| Problem | Result |
|---|---|
| **Catch-Up game** (Isaksen–Ismail–Brams–Nealen 2015: {1..N} is a draw whenever N(N+1)/2 is even) | **Partial.** A new elementary swap lemma, kernel-checked against the site's definition, shows that at most one opening can lose for the second player. A reduction file accepted by the official checker shows the conjecture is equivalent to: after the opening 1, the position (second player to move, trailing by 1 on {2..N}) is a draw. Exact solver: a draw for every admissible N ≤ 24. Not submitted. Notes: `catchup-notes.md`. |
| **Written on the Wall II, Conjecture 189** (Graffiti.pc: if max_v dist_even(v) ≤ 1 + σ(G), then G has a Hamiltonian path) | **Partial.** A new absorption lemma, checked in Lean (`lean/Absorb.lean`), reduces the conjecture to finding a dominating path. A SAT search finds no counterexample on ≤ 18 vertices in the sparse range. Four natural strengthenings were refuted, including a 40-vertex counterexample to the distance-exactly-2 version. Notes: `wowii189-notes.md`. |
| **MathOverflow 273976** (is every group of order 2^p − 1 abelian?) | Not attacked: the session hit the Fable usage limit. Earlier search: no counterexample pair for p < 3·10^6. |

Selection notes: only a disproof is realistic for mo-479419 (2^^∞ + 3), and that is now out of reach (searched to p < 6·10^15 by others). mse-2645263 is false at n = 3, but it is already claimed (PR #16631).
