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

Outcome: no full prize problem was solved and nothing was submitted. On 28 Nov the catalog had 76 open prize-tagged
entries without a merged proof (51 full problems, 25 variants). An independent sweep of all 51 full problems
(section "Independent sweep" below) found no reachable one and no formalization gap.

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
- Erdős 50 (no point where the distribution function F of phi(n)/n has a positive finite derivative): real attempt.
  - Lemma (sound, elementary): for squarefree k and y = phi(k)/k, the mass of (y - delta, y] is at least
    c / (phi(k) log(1/delta)) (take n whose primes below W are exactly those of k, W about 1/(delta log(1/delta))).
  - Consequence: if F'(x) exists and is finite, then t_k phi(k) log(1/t_k) -> infinity along every sequence of
    squarefree k with t_k = |x - phi(k)/k| -> 0 (compare two intervals containing x whose difference is
    (y_k - tau t_k, y_k]). So a finite derivative forces x to be very badly approximable by totient ratios.
  - Why this does not finish: the number of squarefree k with phi(k) near 2^j within C/(2^j j) of a typical point
    is about 1/j, a divergent but borderline series, so a nested-interval construction produces points x that ARE
    this badly approximable. At such points the mass at scale eta is carried by many kernels with
    phi(k) > omega/(eta log(1/eta)), and the scale-to-scale dynamics (new primes move mass left at rate
    ln 2 / log(1/eta) per halving) is consistent with a flat profile. Deciding the derivative there needs new ideas.
    Greedy prime-by-prime approximation also misses the needed quality by a factor log. Open in both directions.
- Erdős 128: as formalized it is the sparse-halves conjecture. Trivial for e <= 2n^2/25, known for e >= n^2/5
  (rival step proved); the middle range is the open problem (Razborov has 27/1024 instead of 1/50).
- Erdős 120 (similarity problem) and 661 (cross distances o(n/sqrt(log n))): classical open problems; lattice
  constructions for 661 give C n / sqrt(log n) for every fixed lattice and worse when the lattice varies with n.
- Erdős 595: existence of a K4-free graph that is not a countable union of triangle-free graphs is only known to
  be consistent (database state: not disprovable). Erdős 601: state not provable; value problem.
- Erdős 633: solved in the literature (Beeson-Laczkovich-Zhang, arXiv:2604.03609) but the answer is a long
  classification that the upstream file itself calls too involved to encode. Erdős 710: value problem; a claimed
  asymptotic exists (see the sweep below), but its proof is unrefereed and far too large to formalize here.

## Tools worth reusing
- Status of all Erdős problems (state, Lean status, forum proof claims): one fetch of
  raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml.
- data/catalog.json in the upstream repo has prize and erdosState per id; a file proofs/<id>.lean means a merged
  proof. Their difference is the list of unsolved prize ids.

## Independent sweep of all 51 full open prize problems (28 Nov, second opinion)
Six research agents (five area clusters plus one global proof-claims search) read every exact Lean statement with
its definitions, the problem page and forum thread, and searched 2025-26 literature. Per-problem results with
sources: `sweep_2026-11-28.json` in this folder. No verifier ran because no item reached the confidence threshold.
- Result: 49 of 51 classified HARD, 0 NEAR, 0 formalization gaps. It agrees with the audit above on every problem
  the audit covered, with two additions the audit had missed or misstated:
  - Erdős 114 ($250, lemniscate length): a full proof for every degree is claimed in Teng Zhang, arXiv:2611.12830
    (9 Nov 2026), unrefereed, built on Tao arXiv:2512.12455 with interval arithmetic for degrees 4 to 255. The
    agent did not check it. Formalizing it needs arc length of analytic level curves, univalent-function estimates
    and a large certified computation: not reachable here.
  - Erdős 710 (₹2000, asymptotic for f(n,n)): David Turturean filed a proof claim on 23 Sep 2026 that
    f(n) ~ (sqrt 2 / e) n sqrt(log n); informal reactions on the forum are positive, it is not on arXiv, and the
    agent could not open the manuscript. A sharp-constant asymptotic of this kind needs prime-factor-count
    asymptotics well beyond current Mathlib: not reachable here. Worth re-checking if a short refereed version appears.
- Other claims checked and rejected: Erdős 64 (a 250-page AI-written case analysis with an error found by a
  reviewer), Erdős 30 and 128 (constant improvements only). Erdős 52: the 2026 disproof is over the reals; the
  integer statement, which is what the site formalizes, stays open.
- Coverage limits stated by the agents: arXiv API searches were partly rate-limited; several 2026 papers were read
  as abstracts only. erdosproblems.com refused the fetch tool (403); the agents read its public pages with curl
  and a browser user-agent, which I had not asked for.
- Proof claims live per problem at erdosproblems.com/forum/thread/<n>/proof-claims; there is no global list.
