# Prize-lead session report (Erdős prize problems, full statements only)

Running log of the Fable-led prize session started 28 Nov 2026. Goal: a FULL solution of one open Erdős problem
that carries a real prize, as formalized on lefttosolve. Nothing here is a submitted result unless it says so.

## Status summary
| Target | Prize | Outcome |
|---|---|---|
| Erdős 647 (n > 24 with max_{m<n}(m + tau(m)) <= n + 2) | £25 | Rejected after analysis: almost surely no such n; non-existence unprovable. |
| Erdős 711 (i) (max_m f(n,m) <= n^{1+o(1)}) | ₹1000 | Attempted, stopped: reduces to an arithmetic-Kakeya-type statement. |
| Erdős 13 general, 552 (ii), 470 (ii) | $100 / $100 / $10 | Rejected at audit (reasons below). |
| Erdős 32, 50, 128, 120, 661 | $50-$250 | Examined in some depth, rejected (reasons below). |
| Erdős 595, 601, 633, 710 | $25-$500 | Rejected: set-theoretic independence or answer too large to state. |

Outcome: no full prize problem was solved and nothing was submitted. Every remaining open prize id on the site
(84 catalog entries without a merged proof on 28 Nov) is a genuine research core; the reasons are recorded here so
the audit need not be repeated.

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

## Further candidates examined (second pass)
- Erdős 32 (every large n = p + a with |A ∩ [1,N]| = o((log N)^2)): open as stated. Each a covers a 1/log N
  fraction of a dyadic block, so covering ALL n needs about (log N)^2 trials by any union-bound or greedy argument;
  sieve weights do not help because the average over residue classes is fixed. Kolountzakis and Ruzsa improve the
  bound only for almost all n.
- Erdős 50 (no point where the distribution function of phi(n)/n has a positive finite derivative): my reduction:
  the mass just left of y = phi(m)/m is at least c / (phi(m) log(1/delta)), so the derivative at x is infinite
  along a sequence whenever x is approximable by phi(m)/m within o(1/(phi(m) log phi(m))). Greedy prime-by-prime
  approximation misses this by a factor log; points that are badly approximable need a separate argument, and the
  local cascade (new primes shift mass left at rate ln 2 / log(1/eta) per halving of scale) is consistent with a
  flat profile, so no contradiction appears. Open in both directions.
- Erdős 128: as formalized it is the sparse-halves conjecture. Trivial for e <= 2n^2/25, known for e >= n^2/5
  (rival step proved); the middle range is the open problem (Razborov has 27/1024 instead of 1/50).
- Erdős 120 (similarity problem) and 661 (cross distances o(n/sqrt(log n))): classical open problems; lattice
  constructions for 661 give C n / sqrt(log n) for every fixed lattice and worse when the lattice varies with n.
- Erdős 595: existence of a K4-free graph that is not a countable union of triangle-free graphs is only known to
  be consistent (database state: not disprovable). Erdős 601: state not provable; value problem.
- Erdős 633: solved in the literature (Beeson-Laczkovich-Zhang, arXiv:2604.03609) but the answer is a long
  classification that the upstream file itself calls too involved to encode. Erdős 710: value problem whose true
  asymptotic is unknown.

## Tools worth reusing
- Status of all Erdős problems (state, Lean status, forum proof claims): one fetch of
  raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml.
- data/catalog.json in the upstream repo has prize and erdosState per id; a file proofs/<id>.lean means a merged
  proof. Their difference is the list of unsolved prize ids.
