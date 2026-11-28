# Fable run on the Erdős prize problems (28 Nov 2026)

Fable read all 103 unclaimed prize statements on lefttosolve, built the reduction tree (211 reductions, 283 open leaf steps), checked every open leaf for competing PRs, and attacked the three with the best odds.

| Target | Result |
|---|---|
| Erdős 713 (i), step R3.H2 — for a forest F with no isolated vertices and at least 2 edges, ex(n,F)/n converges | **Proved** (798-line Lean file, accepted by the official checker). Elementary argument written from scratch: robust patterns and cleaning, layered blow-up over a bounded hub set, degree cascade, amplification. Filed as PR #18340. Notes: `erdos713-i-R3.H2-notes.md`. |
| Erdős 1, a(9) = 161 (least_N_9) | **Not proved.** New rigorous pruning rule (window-density bound) cuts the n = 9 search from ~1e10 to ~2.6e8 nodes, but a kernel-checked search still needs ~10 hours of kernel time against a 30-minute limit. A reduction tree of ~40 leaf files would work. Notes: `erdos1-least_N_9-notes.md`. |
| Erdős 470, step R2.H2 (odd weird numbers have ≥ 6 prime factors, Liddy–Riedl case) | **Stopped:** the step is covered by competing PRs already ahead in the checker queue. Fable enumerated the whole family exactly (55.6 million candidates) and found every member pseudoperfect by a uniform per-base argument, but this was not formalized. Notes: `erdos470-R2.H2-notes.md`. |

Follow-up considered and dropped: the same R3.H2 argument would also give the forest steps Erdős 713 (i) R1.H2.R1.H1/H2/H3, but an earlier PR by another account (#16430) proves their parent R1.H2 directly and passes the official checker, so those steps would score nothing.
