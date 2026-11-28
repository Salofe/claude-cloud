# Erdos1.erdos_1.variants.least_N_9 — working notes (2026-11-28, 01:27–03:25 UTC)

Goal: prove R1.H2 (no 9-element sum-distinct subset of [1,160]) in a form the Lean kernel can check in
< 30 min per file, file < 512 KiB.  (R1.H1 already upstream.)

**Outcome: no accepted proof.**  A new pruning rule (window-density bound) cuts the search tree by a factor
of about 15–40 against the scout's baseline, but the remaining exact work is still ~20x above what one
30-minute kernel run can do.  Details below so that the work can be resumed.

## 0. Competitor / upstream state
- 01:35 UTC: no open PR whose title is the problem id, R1.H2, R2.H1 or R2.H2.
- Open PR #9920 (physbuzz), title `...least_N_9.R1.H2.R1`: a *reduction* of R1.H2, opened 2026-11-27 18:05 UTC,
  still open and not merged at 03:12 UTC.  Not consulted (other team's Lean).
- Upstream: proofs/…R1.H1.lean, reductions/…R1.lean, reductions/…R2.lean only.

## 1. Kernel facts measured here (Lean 4.33.1, `decide +kernel`)
- Raw `Nat.rec` loop with `Nat.lor/land/shiftLeft/shiftRight` and one forcing `Nat.rec` on the state:
  ~23 us per iteration of ~18 elementary steps, i.e. ~1 us per kernel step, *independent of operand size*
  up to a few kbit (60-bit and 3000-bit operands cost the same).  Typeclass-style code is 3x slower.
- Megabit operands: linear GMP operations run at ~5 GB/s (400 iterations x 5 ops on 4 Mbit numbers: 0.25 s).
- **The kernel keeps intermediate results** (whnf cache): ~3.5 KB per loop iteration for small operands,
  and ~3.5 operand-sizes per iteration for big ones (700 MB for 400 iterations on 500 KB numbers).
  So (a) a declaration can do only ~10^6 scalar node-steps before using several GB (split into many theorems),
  and (b) "SIMD inside one huge Nat" over the whole search frontier is impossible: its data volume (TBs) would
  all be retained.
- **Theorems of one file are kernel-checked sequentially** (per-thread CPU times of the lean process: one busy
  thread at a time, four `decide +kernel` theorems take 4x the CPU and are not concurrent).  No in-file parallelism.
- Budget per file therefore: <= ~1.5e9 kernel steps, in practice ~1e8 "candidate evaluations" at 10–15 steps each.

## 2. Search-tree sizes (C programs in c/, Knuth sampling unless marked exact)
n=8, N=83 (a(8)=84, sanity):
| search | nodes | child tests |
|---|---|---|
| fixed-M top-down, exact signed-sum set T (td.c, exact) | 1.09e8 | |
| + Erdős–Moser 2nd moment (tw3.c mode 1, exact) | 2.1e7 | |
| + uniform window bound (tw3.c mode 3, exact) | 1.42e6 | 1.7e7 |
| + centred class bound (tw4.c mode 7, exact) | 7.8e5 | 8.7e6 |
All variants find exactly the known solutions at N=84 (3 sets: {84,83,82,80,77,71,60,40}, {…,71,40,20},
{84,81,79,78,77,70,59,39}) and at N=44 for n=7 (1 set): the pruning rules lose nothing there.

n=9, N=160:
| search | nodes | child tests |
|---|---|---|
| fixed-M top-down, exact T (td.c) | 5.0e10 | |
| all-M difference coordinates (ds.c mode 0; scout's method) | 1.3e10 | |
| all-M + Erdős–Moser per M (ds.c mode 1) | 2.6e9–4.6e9 | |
| fixed-M + EM + uniform window bound (tw3.c) | 5.4e8 | 6.9e9 |
| fixed-M + EM + uniform + centred class bound (tw4.c) | 2.6e8 | 3.1e9 |
Per maximum M (tw4.c, stop at 7 chosen elements, last two by an exact pair test):
| M | nodes | child tests | 7-element survivors (need the exact pair test) |
|---|---|---|---|
| 130 | 7.7e4 | 5.0e6 | ~0 |
| 135 | 2.1e5 | 1.2e7 | ~0 |
| 140 | 5.7e5 | 2.6e7 | |
| 145 | 1.3e6 | 5.0e7 | 8.8e4 |
| 151 | 4.6e6 | 1.1e8 | 1.7e6 |
| 156 | 1.5e7 | 1.9e8 | 9.9e6 |
| 160 | 4.8e7 | 3.2e8 | 3.9e7 |
Sum over M <= 151 (the range of step R2.H1): nodes 2.7e7, child tests 8.4e8, 7-element survivors 6.5e6.
Sum over all M: nodes ~2.6e8, child tests ~3e9, 7-element survivors ~1e8.
No solution is ever found (as it must be); these runs are estimates, not a completed exhaustive run.

BD relaxation ("A ∪ {0} has no zero signed sum of weight 0", reflection-symmetric): not sufficient — 4394 BD
9-sets exist in [0,83] although a(8)=84; n=9 tree 8e10 nodes.

## 3. The new pruning rule (own; rigorous; proof is a pigeonhole count)
Setting: descending search with fixed maximum M.  B = the k chosen (largest) elements, S_B its 2^k subset sums,
r = 9-k unknown elements, all < m = min B.

**Uniform window bound.**  Let C be the unknown part, s_max = (m-1)+…+(m-r) >= sum C.  If there are L >= 1 and X
with  #(S_B ∩ [X-t, X-t+L)) >= theta  for every t in [0, s_max]  and  2^r * theta > L,  then B ∪ C is not
sum-distinct.  Proof: the 2^r translates S_B + s (s a subset sum of C, 0 <= s <= s_max) are pairwise disjoint
if B ∪ C is sum-distinct; each has >= theta points in the L integers [X, X+L); so 2^r*theta <= L.

**Centred class bound (stronger).**  Take the window starting at floor((sigma_B + sigma_C - L)/2).  For V ⊆ C with
|V| = j the translate S_B + s_V is seen through the window starting at floor((sigma_B - L + w_V)/2),
w_V = sum(C \ V) - sum(V), |w_V| <= max(j, r-j)(m-1).  Hence, with g_L(y) = #(S_B ∩ [y, y+L)) and
mu_j = min of g_L over y in [floor((sigma_B-L-W_j)/2), floor((sigma_B-L+W_j)/2)], W_j = max(j,r-j)(m-1):
if  sum_j C(r,j) mu_j > L  then B ∪ C is not sum-distinct.

Why it works: a 9-set in [1,160] whose subset sums look Gaussian has central density
512 / sqrt(2 pi sum a^2 / 4); this exceeds 1 unless sum a^2 >= (2/pi) 4^9 = 166 886 (Erdős–Moser only gives
87 381).  The window bound is the rigorous, exact-counting form of that statement, evaluated on the known part
with the worst case over the unknown part.  It kills all "spread-out" sets 2–3 levels earlier.
What it cannot kill ("hard core"): top-heavy sets (six or seven elements within ~45 of M, sum a^2 > ~160 000),
whose sums are clustered with period ~M and where N=160 is within a few percent of feasible at the volume
level (at N=161 the Conway–Guy set fills ~150 of every 161 central positions).  These need exact arithmetic:
~1e8 seven-element prefixes over all M.

Kernel-friendly evaluation: keep S_B as a digit-spread number (digit width 10 bits at position 10*s); then
S_B * (sum_{i<L} 2^{10 i}) has digit p = #(S_B ∩ [p-L+1, p]) (no carries), and "all digits in a stretch >= theta"
is one add + one land + one comparison.  Exact last-two-elements test: bit matrix
V[y,x] = f[x] f[y] f[y-x] f[y+x] (f = complement of the signed-sum set) built from two multiplications by
repunits (Toeplitz and Hankel parts), V = 0 iff no completing pair.

## 4. Why this still fails
- Even with the best variant the scalar kernel search needs ~3e9 candidate evaluations (each: update, window
  test, ~10–15 kernel steps ≈ 12 us) plus ~1e8 exact pair tests (~30 us): about 4e4 s ≈ 10 hours of kernel time,
  i.e. >= 40 files of 15 minutes.  Step R2.H1 alone (M <= 151) is ~8e8 evaluations ≈ 3 hours.
- A simplified, easily verified variant (uniform bound, one window length per level, bulk pruning by the
  central run; c/sim.c) is far weaker: 3.3e7 evaluations and 5.9e6 survivors for M = 140 alone.
- Batching children with multiplications costs more than it saves (shift amounts differ per child), and
  level-synchronous batching over all nodes (uniform shifts in centred +-sum coordinates, ~0.4 us per
  node-candidate) is ruled out by the kernel's retention of intermediates (section 1).
- Other things tried or analysed and found insufficient: Erdős–Moser on sub-collections and on derived sets
  (pair differences), balanced-sum variance bounds for A ∪ {0} (tight to 6–14% but only bound concentration
  from below), parity/divisibility descent (|odd elements| >= 3 follows from a(8)=84, prunes a few percent),
  mod-M occupancy counts, one-period counts in difference coordinates (give M >= ~148 for the Conway–Guy
  pattern, not 161), Harper/Dubroff–Fox–Xu boundary counts (M >= C(9,4) = 126), reflection symmetry of the BD
  relaxation (mirror images of top-heavy sets are bottom-heavy and die immediately), 2-D/3-D bit-tensor tests
  for the last three elements (ms per node).

## 5. If someone resumes
- The only route that closes the problem with the present ideas is a reduction tree (each leaf a 30-minute file):
  e.g. below R2.H1 about 12 leaves, below R2.H2 about 30, using the fixed-M search of section 3.  Leaves are
  ranges of the maximum, and for M >= 156 ranges of the second-largest element.
- Soundness proof needed once: (i) signed-sum bitset invariant, (ii) the pigeonhole lemma of section 3,
  (iii) "digit of the product = window count" (convolution of digit strings without carries) and the
  threshold test, (iv) the exact pair test.  Only (iii)/(iv) need bit-level lemmas.
- An extra factor ~10 in the count of evaluated candidates would make R2.H1 a single file.  What was measured:
  * four window lengths (128, 176, 224, 288) prune as well as 32 (M=150: 4.3e6 nodes either way);
  * testing the next element in chunks (c/tw8.c: one test for all z in [zlo, zhi], shifted half counted with the
    window shortened by zhi-zlo) at M=150: 1.15e8 single tests become 4.1e7 chunk tests + 2.2e7 single tests
    (width 8), or 8.0e7 + 7.2e6 (width 4): a factor ~2 with adaptive widths, not 10 — the evaluated candidates
    are children of near-feasible nodes, so margins are thin;
  * range pruning of small candidates by the parent's own bound with a reduced maximum (c/tw6.c): 1.7x fewer
    child tests in the tight-top region; surviving children sit in the upper half of the candidate range.
  Untested: sharing between consecutive M; interval boxes over several elements at once.

## Files
- c/td.c, c/bd.c, c/ds.c (+ds2/ds3): baseline searches and samplers (fixed M; BD relaxation; all-M).
- c/tw.c … c/tw7.c: window-density pruning (tw3: uniform, fast; tw4: + centred class bound; tw5: prints heavy
  survivors; tw6: range pruning by binary search; tw7: statistics on survivors).
- c/sim.c: reference simulation of the simplified kernel-oriented design.
- c/ext.py: completions of a given top pattern.  lean/*.lean: kernel timing experiments (k1–k3, par, big).
