# Prize-lead session report (Erdős prize problems, full statements only)

Running log of the Fable-led prize session started 28 Nov 2026. Goal: a FULL solution of one open Erdős problem
that carries a real prize, as formalized on lefttosolve. Nothing here is a submitted result unless it says so.

## Status summary
| Target | Prize | Outcome |
|---|---|---|
| Erdős 647 (n > 24 with max_{m<n}(m + tau(m)) <= n + 2) | £25 | Rejected after analysis: almost surely no such n; non-existence unprovable. |
| Erdős 711 (i) (max_m f(n,m) <= n^{1+o(1)}) | ₹1000 | Attempted, stopped: reduces to an arithmetic-Kakeya-type statement. |
| Erdős 13 general, 552 (ii), 470 (ii) | $100 / $100 / $10 | Rejected at audit (reasons below). |

## Erdős 647: do not search
- Forced structure (my derivation, agrees with the forum): for n > 24 the conditions tau(n-k) <= k+2 for
  k = 1,2,3,4,5,6,8,9,10,12,16,18,20,24 force 14 simultaneous prime values (n-1, (n-2)/2, ...), and about 18 more
  values of k force a prime-or-semiprime cofactor.
- Decisive point: the generic conditions also fail. For k near (log n)^{2 log 2}, the number of k with
  tau(n-k) > k+2 has expectation about sum_j 2^j e^{-L} L^j / j! = e^{L} = log n (L = log log n), so the chance
  that no k fails is about 1/n. Expected number of solutions beyond the searched range is far below 1.
- Literature (subagent, 28 Nov): searched to 10^22 with no solution (OEIS A087280); Lean-certified to 10^9
  (arXiv:2608.17880). Non-existence hits the prime-tuples barrier. The rival step Erdos647.R2.H3 (existence of a
  witness) is therefore almost surely false.

## Erdős 711 (i): analysis and why it stops
Setup: Z an interval of L integers, i ~ z iff i | z, want a matching saturating [1,n] when L = n^{1+eps}.
1. Level scheme (my own): call z good if it has at most D = n^delta divisors <= n. Among good z, left degree
   >= right degree gives Hall at once. Iterating on the set R of i with fewer than D good multiples, the theorem
   is equivalent to: there is no nonempty R in [1,n] such that almost every multiple (in Z) of every i in R has
   more than D divisors in R. For L >= n^{3/2+o(1)} pair counting closes this (two elements of Z share at most
   tau(z - z') divisors); this recovers the Erdős–Pomerance bound.
2. Core case: for primes p in (n/2, n] the residues of the window modulo p are free (CRT). So the conjecture
   contains: N progressions with distinct prime differences in (n/2, n], arbitrary residues, K = n^eps terms each,
   have union of size >= N.
3. Dual form: a set G of N points (d, r) in Z^2 with distinct first coordinates whose K projections r + k d
   (k = 0..K-1) all land in a set smaller than N. This is a sums-differences (arithmetic Kakeya) configuration.
   - Tensor-power/entropy argument: a violation exists for a fixed K iff there are integer random variables with
     H(D) > max_k H(X + kD). Lattice-simplex examples give this for K = 3 (dimension 4) and K = 4 (dimension 16),
     so for bounded K the union bound is FALSE; they fail for K >= 5 (Rogers–Shephard, 4^d against (K-1)^d).
   - Generalized-arithmetic-progression constructions fail for all large K (a Möbius map cannot send K consecutive
     integers to rationals of small height; the gcd obstruction divides a fixed determinant).
   - A correct proof must use that the slopes are consecutive integers; Szemerédi–Trotter in the (k, x) plane does
     not apply directly because two progressions can share a point at different indices k.
4. Literature (subagent): Tao, forum thread 29 Sep 2025: the problem "morally implies the Kakeya conjecture in all
   dimensions"; best bound n^{4/3+o(1)} (Chen–Korsky, arXiv:2607.26450, unrefereed); Kominers (arXiv:2607.10431)
   settles windows at polynomial height. Lower bound n exp(c log n / log log n).
Verdict: a full proof would be a major result in incidence geometry. Stopped.

## Audit rejections
- Erdős 13 variants.general: the $100 was for the r = 2 case (Bedert, solved); rivals have a deep reduction tree.
- Erdős 552 (ii): equivalent to non-existence of C4-free graphs with minimum degree s on s^2 + O(s) vertices for
  infinitely many s; needs non-existence of near-projective-plane structures.
- Erdős 470 (ii): every known family (2^k p q, more primes) needs a prime in an interval of length about sqrt(x)
  at a prescribed place (the Melfi condition); binary problem at level of distribution 1/2.
