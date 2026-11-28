# Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2 — working notes

Target (reduction R2 by LoopsGod, upstream):
  H2 : forall m, Odd m -> m.Abundant -> m.primeFactors.card <= 5 ->
       (forall d in m.properDivisors, d.Deficient) -> 9 | m -> m.Pseudoperfect

## Competitor check (2026-11-28 ~02:00 UTC)
- exact-title check for `...R2.H2`: no open PR.
- parent `Erdos470.erdos_470.variants.odd_weird_prime_div`: open PR 15985 (AndrewRegnier), created 00:27Z, no verdict yet.
- upstream now has reduction `...R2.H2.R1` (physbuzz, merged 00:54Z) splitting R2.H2 into H1..H4;
  open PRs: R2.H2.R1.H1 (dasante78 17033, AndrewRegnier 17181), .H2 (AndrewRegnier 17128),
  .H3 (AndrewRegnier 17190), .H4.R1 (AndrewRegnier 17191, a further reduction), and a second
  R2.H2.R1 PR (hoodbroskillson 16852).
- upstream proofs present: R1.H1, R2.H1. No proofs/...R2.H2.lean upstream.
- I did not read any of the other teams' proof files or the R2.H2.R1 reduction body.

## Mathematics (own derivations)
(see below, appended as work proceeds)

### Reformulation
For m abundant put E = sigma(m) - 2m. Then m is pseudoperfect iff E is a sum of distinct proper divisors of m
(complement inside the proper divisors). For m primitive (all proper divisors deficient) and p^e || m:
  E < 2m / (sigma(p^e) - 1),   and   E = D_p * sigma(p^(e-1)) - delta(m/p^e),  D_p = p*sigma(w) - 2(p-1)w, w = m/p^e,
  delta(w) = 2w - sigma(w).   For e = 1:  E = sigma(w) - p*delta(w),  p < sigma(w)/delta(w).
gcd(m, sigma(m)) | E (m odd).

### Why no purely "uniform" argument can exist
E = 2 is never a sum of distinct odd divisors, so H2 contains the Diophantine statement
"no odd primitive abundant m with 9 | m, omega(m) <= 5 has sigma(m) = 2m + 2" (and similar statements for the other
non-representable small values 5,6,7,8,11,22,... depending on which of 5,7,11 divide m). Congruences only give
gcd(m, sigma(m)) | E; they do not exclude these values. So any proof must contain an exhaustive (finite) search over the
family of odd primitive abundant numbers with <= 5 primes -- the route "exclude the few bad E by congruences" of the
selection note is not viable. The family is finite (Dickson) and I enumerated it exactly (below).

### Exact enumeration of the family (py/panenum.py, py/run5.py; logs in py/)
Odd primitive abundant m with 9 | m:
  3 primes:  8 members (945, 1575, 2205, 7425, 78975, 131625, 342225, 570375)
  4 primes:  563 members (the other 13 of Dickson's 576 have 3 || m)
  5 primes:  50947 "bases" w = 3^a q^b r^c x^d (deficient) each with a non-empty window of last primes y (y || m),
             total window length 55 611 801 integers (the largest integer in a window is 36 550 416, consistent
             with the bound 36 550 417 of the upstream statement R1.H1), plus 7775 members whose last prime has exponent >= 2.
             Prime triples (3,q,r): (3,5,r) r in {7,11,13,17,19,23,29,31,37,41}; (3,7,r) r in {11,13,17,19}; (3,11,13).
             Fourth prime 13 <= x <= 769 (131 values). Max exponents (28,19,11,8); largest prime power 17^11 ~ 3.4e13.
             5088 distinct 3-prime prefixes, 503 distinct 2-prime prefixes.
  The counts are stable for exponent caps 1e15 and 1e18 (identical output).
  Cross-check: a brute-force sigma sieve of all odd numbers <= 4e7 gives exactly the same 2708 members with 9 | m and
  omega <= 5 as the enumeration (py/sieve_check.py). d=3 gives 8 and d=4 gives 576 (Dickson/Ferrier), as it should.

### Structure of the semiperfectness proof (all verified exactly in Python, py/verify_all.py, py/prodlemma.py, py/small_k.py)
Cov(n, A) := every integer in [A, s(n) - A] is a sum of distinct proper divisors of n   (s(n) = sigma(n) - n).
 (1) growth lemma: if Sigma(S) covers [A, T - A] (T = sum S) and d <= T - 2A + 1, then Sigma(S + {d}) covers [A, T + d - A].
 (2) product lemma: Cov(n, A), x prime not dividing n, (x+1)A <= s(n) - A + 1, n <= x (s(n) - 2A)  ==>  Cov(n x^d, A) for all d.
 (3) last prime: m = w y, E = sigma(w) - y delta(w). If Cov(w, A), y <= s(w) - 2A + 1 and
        E >= A and (E <= s(w) - A  or  E >= (y+1) A)
     then E = r + y t with r, t in [A, s(w) - A] or 0, so m is pseudoperfect.
Data: for all 50947 bases Cov(w, A) holds with A in {3,7,8,12,16,19,23,27,36} (exact subset sums of divisors <= 3000 +
growth afterwards). 45023 bases get Cov from the 2-prime prefix by two product steps, 5851 from the 3-prime prefix by one
product step, 73 small bases need a direct check (total 2434 divisors); 1215 direct prefix checks (113 826 divisors).
For EVERY integer y in every window (primality of y is not needed): E >= A except for one single (w, y):
w = 3^5*5*11*73, y = 163, E = 18 = 15 + 3. The condition "E <= s - A or E >= (y+1)A" never fails (565 integers y have
E > s - A). min delta(w) = 18 (w = 315*107).
The 7775 members with last exponent >= 2 and the 571 members with 3 or 4 primes all satisfy Cov(m, A) and A <= E <= s(m) - A.
Small-E members in the whole family (E < 64): 945 (30), 7425 (30), 78975 (26), 2205 (36), 32445 (6), 31815 (18),
8415 (18), 30555 (42), 3^3*7*11*13^2 (18), 3^5*5*11*73*163 (18), 315*109*2287 (30). Everything else has E >= 64.

### Proofs of the two lemmas (checked by hand; not yet in Lean)
Product lemma. S = proper divisors of n, B = [A, s-A] u {0} (all are subset sums of S). U_j = {r_0 + x r_1 + ... + x^j r_j :
r_i in B} consists of subset sums of proper divisors of n x^d (x^i c, c | n proper; distinct since x does not divide n).
U_j contains [A, T_j], T_j = (1+x+...+x^j)(s-A): for v in (T_j, T_{j+1}] take t = min(s-A, floor((v-A)/x^(j+1)));
t >= A because T_j >= A x^(j+1) + A - 1 (from s - A >= (x+1)A - 1), and v - x^(j+1) t in [A, T_j]. Complementation inside the
proper divisors of N = n x^d (their sum is s(N) = sigma(x^d) s + n sigma(x^(d-1))) gives [s(N) - T_d, s(N) - A]; the two
intervals overlap when n sigma(x^(d-1)) <= sigma(x^d)(s - 2A), which follows from n <= x (s - 2A).
Last-prime lemma. m = w y^h, y prime not dividing w, Cov(w, A), E = sigma(m) - 2m. If A <= E <= s(w) - A, E is a subset sum of
proper divisors of w. If E > s(w) - A, E >= (y+1)A, y <= s(w) - 2A + 1 and E <= y (s(w) - A) + A: t = floor((E-A)/y) lies in
[A, s-A], r = E - y t lies in [A, A+y-1] inside [A, s-A]; E = r + y t uses divisors c and y c (c | w proper), all proper
divisors of m and pairwise distinct. (For h >= 2 one has E < 2w, so the same two layers suffice.)

### Rigorous finite search tree (py/rigdfs.py) -- what a kernel computation would have to do
Parameters of a member: primes 3 = p1 < p2 < ... < pk (k <= 5), exponents e_i (e_1 >= 2). I(p^e) = sigma(p^e)/p^e is decreasing
in p and increasing in e with supremum p/(p-1). Only two facts about m are used:
   (A)   prod I(p_i^e_i) > 2                                   (abundant)
   (D_j) I(p_j^(e_j - 1)) * prod_{i != j} I(p_i^e_i) < 2        (m/p_j deficient)
A box (ranges for the p_i and e_i, exponent ranges may be unbounded) is dead if sup(A) <= 2 or inf(D_j) >= 2 for some j, both
obtained by evaluating at the corners. The search = repeated splitting of boxes until every box is dead or is a leaf:
  leaf 1: first four prime powers fixed (base w), last prime y in a window, exponent 1  -> last-prime lemma, uniform in y
  leaf 2: everything fixed (members with 3 or 4 primes, or last exponent >= 2)          -> Cov + A <= E <= s - A, or last-prime lemma
The prototype (exact nodes for explicit prefixes, interval nodes for "exponent >= F" tails, last prime treated as an arbitrary
integer without a factor < 100) closes with prime-power cap 1e13: 480 743 exact nodes, 1 166 542 interval nodes (almost all of
them O(1) last-prime checks), 434 783 exact bases of which 37 459 have a non-empty window and 37 782 an integer "special" last
prime; 571 members with 3 or 4 primes. No interval node is left undecided. (With cap 1e11, 22 tails are undecided.)
Coverage Cov is only ever checked directly on about 1300 short prefixes (about 116 000 divisors in total); every other use
goes through the product lemma. So the whole proof is roughly 2e6 cheap big-integer node evaluations: within reach of
`decide +kernel`-style evaluation in the 30 minute limit if the checker is written carefully (structural recursion on fuel,
cross-multiplied naturals, no rationals).

### Lean plan (not started)
 M1  Cov on Finset Nat: growth lemma, complement, bitmask checker for the small part (Nat.testBit of a fold of b ||| (b <<< d)),
     validation of a generated divisor list against Nat.properDivisors (all divide, strictly increasing, length = prod (e_i+1) - 1).
 M2  product lemma, last-prime lemma, "E is a subset sum of proper divisors => Pseudoperfect".
 M3  glue: sorted prime factorisation of m, sigma multiplicative, I(p^e) monotone, facts (A), (D_j).
 M4  boxes: dead-box test in cross-multiplied naturals, splitting function with fuel, soundness by induction on fuel
     (dead box / leaf / split; the splitting policy is untrusted, only exhaustiveness of each split is proved).
 M5  leaves + kernel run + assembly of OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2.H2.
 Estimated 1300-2000 lines of Lean and several kernel-performance iterations; not attempted in this run (see status).

### Competitor landscape at 03:05 UTC (statements of the upstream reduction R2.H2.R1 looked at only after the above was fixed;
### its proofs and helper lemmas were not read)
 R2.H2.R1 (physbuzz, merged) splits R2.H2 into H1 (multiples of 315), H2 (63 | n, 5 not), H3 (45 | n, 7 not, 11 or 13 | n),
 H4 (45 | n, none of 7, 11, 13, some r in 17..43 | n). In my enumeration H4 is the bulk: 42 079 of the 50 947 bases
 ((3,5,17) 27236, (3,5,19) 8845, (3,5,23) 3419, (3,5,29) 1480, (3,5,31) 805, (3,5,37) 219, (3,5,41) 75).
 Open PRs: H1 17033 (dasante78), 17181 (AndrewRegnier); H2 17128, H3 17190 (AndrewRegnier); H4.R1 17191 (AndrewRegnier, a
 further reduction); parent 15985 (AndrewRegnier). Checker queue latency was about 3h45m at 02:15 UTC and growing (PR 13355
 merged 02:15; 15985 will be reached around 08:00 UTC, the 17xxx PRs around 10:30 UTC).

### Status at 03:06 UTC -- stopped here
 New since the first check: PR 18406 (dasante78, created 02:56Z) is a direct proof PR for R2.H2.R1.H4. So every step of the
 merged reduction R2.H2.R1 now has a pending proof PR (H1 17033/17181, H2 17128, H3 17190, H4 18406), and the parent has
 PR 15985. All of them are ahead of anything we could submit in the checker queue; if they pass, R2.H2 closes through the
 reduction around midday UTC. No PR is titled exactly `...R2.H2`, so the step is not formally blocked, but a direct proof
 would only count if at least one of those rival PRs fails.
 No Lean file was written: proofs/Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.lean does not exist.
 What is established (computationally, exact arithmetic, not kernel-checked): the complete list of odd primitive abundant
 numbers with 9 | m and at most 5 primes, a rigorous finite search tree that proves the list complete, and a uniform
 pseudoperfectness argument for every leaf (see above). This re-proves the 9 | m half of Liddy-Riedl with a certificate of
 about 2e6 cheap checks instead of an enumeration of several million numbers.
 If the rival PRs fail: implement the Lean plan above (M1-M5); the Python files in py/ are the reference implementation.
 Literature: J. Liddy, An algorithm to determine all odd primitive abundant numbers with d prime divisors, Univ. of Akron
 Honors Research Project 728 (2018), supervised by J. Riedl (theorem only; the PDF could not be fetched, the argument here
 is independent); L. E. Dickson, Finiteness of the odd perfect and primitive abundant numbers with n distinct prime factors,
 Amer. J. Math. 35 (1913).
