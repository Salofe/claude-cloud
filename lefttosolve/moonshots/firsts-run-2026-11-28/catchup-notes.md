# Catch-Up conjecture: working notes

## SUMMARY (read this first)
Status: NOT solved.  No complete proof of CatchUp.value_of_even_mul_succ_self_div_two was found.
What was established (details below):
1. Swap lemma (new, elementary, kernel-checked in Lean for the real `valueAux`): for a finite set T and d < x in T,
   if the player trailing by x on T-{x} loses then the player trailing by d on T-{d} wins.  Corollaries: among the
   positions "T with one element taken by the opponent" at most one is lost for the mover; a tie on T is a draw as soon
   as ONE opening leads to an exactly drawn position, or as soon as the first player has TWO different safe openings.
2. Checker-accepted reduction file (NOT submitted, left for the orchestrator to decide):
     lean/reductions/CatchUp.value_of_even_mul_succ_self_div_two.R2.lean
   theorem main : H1 -> H2 -> conjecture, where H1/H2 say that after the opening 1 the second player (trailing by 1 on
   {2..N}) does not win / does not lose.  Official tools/lint.py: ok; official tools/check.sh: verdict accepted
   (lean/verdict_R2.json).  It strictly weakens the second hypothesis of the merged reduction R1 (all openings -> opening 1).
3. Exact computation: the conjecture holds for all N <= 28 (full DP), and every opening draws for N in
   {12,15,16,19,20,23,24,27,28}; N = 31 is a draw via the opening 1 (solve3_31.log).  So the conjecture is
   verified for all N <= 31 (previously: N <= 20 in the paper, N <= 24 by the selection run).
4. Empirical structure theorems (unproved): Z (complete multiset R+{d} => mover never loses; 0 exceptions on 2.3M
   positions in [20], on multisets, and on 2454 random sparse complete sets with values up to 3000) and N* (nearly
   complete from l => only the minimum can be a losing mark).  Either would imply the conjecture; neither class is
   closed under play, and sparse complete positions have very few safe moves, so no simple inductive proof was found.
5. Many natural shortcuts were refuted by computation (listed under "Things that turned out FALSE").


Problem: CatchUp.value_of_even_mul_succ_self_div_two (formal-conjectures, Paper/CatchUpConjecture.lean):
for N with N(N+1)/2 even, value(Icc 1 N) = draw.

Competitor check (2026-11-28, repeated before finishing): no open PR, no upstream proof; only the merged reduction R1 by
another user.  Its proof was NOT read; only its two hypothesis statements were extracted with tools/lint.py:
  R1.H1: after opening 1 the second player does not win;  R1.H2: for EVERY opening x the second player does not lose.

## Model
Position (R, d): remaining set R, mover is behind by d >= 0.  A pick x: if x >= d, turn passes, new
deficit x-d; if x < d, same mover continues with deficit d-x.  valueAux(R, s_me, s_opp, false) depends
only on (R, s_opp - s_me) when s_me <= s_opp.  First move = position (R, 0) (single pick forced).
Multiset view: C = R + {d} with d marked; a pick replaces {x, d} by |x - d|; mover changes iff x >= d.
Sum of C drops by 2d each turn; mover's need a = sum(C)/2, opponent's need b = a - d.

## Programs
- solve.c  : exact solver for all subsets of [n], deficits 0..DM -> V_n_DM.bin (0=L,1=D,2=W for mover).
- lib.py, an*.py, gap.c, nc.c, ncc.c, eq.c, types.c, closure.c, multi.py : analysis scripts.

## Empirical laws (all R subset of [20], d <= 20; parity right = sum(R)+d even)
- (Z)  If the multiset R + {d} is complete (sorted c_1<=c_2<=..., c_1 = 1, c_{i+1} <= 1 + c_1+..+c_i), parity right,
       then the mover does NOT lose.  0 exceptions among 2,306,922 positions.  Also 0 exceptions for general
       multisets with values <= 6 (mult <= 3) and values <= 8 (mult <= 2)  (multi.py).
       Z implies the conjecture: ([N],0) and ([N]-x, x) are all Z-positions.
- (N)  If C = R+{d} has all subset sums in [l, sum(C)-l] where l = min C, parity right, and (d = 0 or d > l):
       mover does not lose.  0 exceptions (2.9M positions).  For d = l exceptions exist when l >= 2.
- Z and N are NOT closed under (my best move, any reply): the opponent can always leave the class by taking
  the smallest elements (e.g. he picks min R at a tie, leaving me a forced single pick with d < min R).
- Exact hit lemma (proved on paper): in a Z-position, if max R > b (opponent's need) the mover draws at once.

## Swap lemma (proved; elementary)  [KEY TOOL]
For a finite set (or multiset) T and elements d < x of T:
    V(T - d, d) >= -V(T - x, x).
Proof: from (T-d, d) the mover picks x >= d, turn ends: value >= -V(T-{d,x}, x-d).  From (T-x, x) the mover
picks d < x and continues: V(T-x, x) >= V(T-{d,x}, x-d).  Chain the two.
Write f_T(x) := V(T - x, x) ("mark x").  Then f_T(x) + f_T(y) >= 0 for all x != y in T.  Consequences:
 * at most one mark of T is L ("killer"), and then every other mark is W;
 * the tie (T, 0) is a draw  <=>  some mark is exactly D  <=  two distinct marks x != y with f <= 0
   (two distinct safe first picks for the first player).  In particular
       value([N]) = draw  <=>  exists x: V([N]-x, x) = D  <=  P1 has two different non-losing first moves.
 * Z (no L mark in complete even-sum multisets)  <=>  ties on complete even-sum multisets are never first-player wins.
Descent formulation: a class K of even-sum sets closed under T -> (T - z - Q) + {q - z} (for two chosen marks z and
all legal reply turns Q) consists of drawn ties.  Computation (kfix*.c, gmin.c): pure swap/"forget the lead"
schemes certify only a tiny fraction of positions -- in the true game the defender often survives by threatening
a win, so a 3-valued analysis of sparse endgames cannot be avoided.

## Other experiments
- Restricted families for the defender (fam.c): turns of size <= 2 (one optional non-crossing pick + crossing pick)
  suffice for N <= 20 (both as P1 and P2).  Pure bottom-eating, top-taking, "bottom segment + one", and
  overshoot-bounded families all fail.
- Forcing single picks (delta <= min R) all the time fails (s1.c).
- Even-sum subsets T of [m] with |T| >= ~2m/3 + 1 are always drawn ties (m <= 20); largest non-drawn ties look like
  {1,2} + [10..20] ("few small + top block").
- Cluster endgames (all elements in [l, l+w], w < l): with even count and defender's lead delta in [w+3, l-3]
  the defender never lost in the data (cluster.py, cluster2.py); with small slack exceptions exist.

## KERNEL-CHECKED partial result: reduction to the single opening 1  (our own Lean, not submitted)
File: lean/reductions/CatchUp.value_of_even_mul_succ_self_div_two.R2.lean  (site reduction format, namespace
OMA.R_CatchUp_value_of_even_mul_succ_self_div_two_R2).  Compiles against the pinned formal-conjectures
(`lake env lean`), axioms = [propext, Classical.choice, Quot.sound], official tools/lint.py says ok=true (type reduction).
    H1 : forall N, Even (N*(N+1)/2) -> 1 <= N -> valueAux ((Icc 1 N).erase 1) 0 1 false != win
    H2 : forall N, Even (N*(N+1)/2) -> 1 <= N -> valueAux ((Icc 1 N).erase 1) 0 1 false != loss
    theorem main : H1 -> H2 -> (the conjecture)
i.e. the conjecture is equivalent to: "after the opening 1 the position ([2..N], second player trailing by 1) is a
draw".  It contains the swap lemma for the real `valueAux`:
    lemma swap (T) (d x) (hd : d in T) (hx : x in T) (hdx : d < x)
        (hB : valueAux (T.erase x) 0 x false = loss) : valueAux (T.erase d) 0 d false = win
plus reusable unfolding lemmas (valueAux_eq, valueAux_pruned, best_eq_win_iff, best_eq_loss_iff, opt_mem).
Relation to the merged reduction R1 (another user; only its hypothesis statements were read, via lint.py):
R1.H1 is our H1; R1.H2 demands "second player does not lose" for EVERY opening x, ours only for x = 1.
The file is NOT copied into oma-check/reductions and no PR was opened (outside this task's mandate).

## Extended exact verification (solve2.c, solve3.c)
- solve2.c (2-bit packed full DP over subsets of [28], 1 GB, 2 min CPU): value([N]) = draw for every N <= 28 with
  N(N+1)/2 even; for N = 12,15,16,19,20,23,24,27,28 EVERY first move leads to an exactly drawn position
  (N=3: marks D,W,D; N=4: DDWW; N=7: DDDDWWW; N=11: only the opening 10 loses for the first player).
- solve3.c (opening 1 only, subsets of [2..N], 4 GB file-backed table, 10 min CPU): the position ([2..N], second player
  trailing by 1) is a draw for every N <= 31 with N(N+1)/2 even, in particular N = 31; by the swap lemma (kernel-checked)
  the game on {1..31} is a draw.  N = 32 was not attempted (8.5 GB table on a shared machine).

## Things that turned out FALSE (do not retry)
- "Ties on symmetric sets with an even number of pairs {a_i, s-a_i} are draws": true for all 2519 such subsets of
  [20], but FALSE in general (298 first-player wins among 4832 random instances with values up to 400, e.g.
  {6,97,112,136,232,256,271,362}).  Data on subsets of [20] can mislead for sparse statements.
- "Unions of balanced quadruples (p+t = q+r) are drawn ties": false.
- "Picking 1 at a tie on a complete even-sum set is always safe": false for sparse complete sets with large values
  (303 of 2454 random instances), although the tie itself was always a draw (Z survived this test: 0 killer marks).
- "Equalise with y-1 after (1, y)": not always safe.  One-round induction schemes for Z (zscheme.py): only 42/360.
- Simple strategy families for the defender: see "Other experiments".

## Structural facts found (not proofs)
- Exact-hit lemma: mover with need a (= half of sum(R)+d), opponent need b = a-d.  If some x in R has x > b and
  a-x is a subset sum of R-x (always true when R+{d} is complete), the mover collects exactly a at once: draw.
  Consequently in a complete multiset C with maximum M and half-sum a, every mark d > a - M is non-losing.
- FIN race: a player wins iff at some turn he can collect strictly more than his need in one legal turn.  A legal turn
  from deficit d has sum < d + (last pick).  If the player who just moved keeps his own remaining need >= max(R') - 1,
  the opponent cannot finish strictly on the next turn.  The whole fight is about exact subset sums at the moment
  when sum(R) drops below about 2*max(R); the opponent's only weapon is to remove the small elements first.
- Conjecture (N*), 0 exceptions on [20] and on 1436 random large-valued sets: if all subset sums of C = R+{d} cover
  [l, sum(C)-l] with l = min C, then the only mark that can be losing is the minimum l (for l = 1: none, this is Z).
- Cluster endgames (all elements in [c, c+w], c >> w) are scale-free: they reduce to an "offset game" on e_i = x_i - c
  with states Level(nu)/Unit(mu); values depend only on offsets once c exceeds the relevant offset sums.

## Lean file contents (lean/reductions/...R2.lean, 282 lines, checker verdict: accepted)
Reusable lemmas (namespace OMA.R_CatchUp_value_of_even_mul_succ_self_div_two_R2):
  foldl_char, best_eq_win_iff, best_eq_loss_iff, neg_eq_win_iff, neg_eq_loss_iff,
  valueAux_eq      : unfolding at a non-first position with R != empty and mover able to catch up,
  valueAux_pruned  : sm + sum R < so  ->  valueAux R sm so false = loss,
  opt_mem          : each single pick is in the option list,
  swap, swap'      : both directions of the swap lemma,
  valueAux_shift   : valueAux R (sm+c) (so+c) false = valueAux R sm so false (only the score difference matters),
  value_eq, value_eq_draw : unfolding of the first move; draw criterion,
  value_eq_draw_of_opening : for ANY finite set T, one opening x with value != win and != loss gives value T = draw,
  value_eq_draw_of_two_safe: for ANY finite set T, two openings x < y that are both != win give value T = draw,
  main             : H1 -> H2 -> conjecture.

## File index
solve.c (all subsets of [n], byte table) | solve2.c (packed, N<=28) | solve3.c (opening 1, file-backed, N<=31)
gsolve.c (arbitrary sets with large values, reads sets from stdin) | fam.c (restricted strategy families)
gap.c nc.c ncc.c eq.c types.c closure.c kfix*.c gmin.c s1.c (class / closure / certificate experiments)
lib.py line.py an*.py ties.py cluster*.py sym*.py quad.py multi.py zscheme.py zex.py z1.py d1.py mirror.py h1check.py
solve2_28.log, solve3_31.log (results); compres.txt / ncres.txt / symres.txt (random large-value tests)

## Ideas not yet exhausted (for whoever continues)
1. FIN-race analysis of rich endgames: characterise, for complete R+{d}, when the mover has a move after which the
   opponent has no strict finishing turn, in terms of the top two elements, the needs and the available subset sums.
2. Prove H1/H2 of the reduction for N >= 11 through: after (1, y) the first player equalises with y-1 (tie on
   [2..N] minus {y-1,y}; these ties are draws for all N in {11,...,20}), then use the swap lemma at every tie
   (a tie is not a first-player win as soon as the picker has two safe picks).  The families of sets generated
   this way are "[l..N] minus difference pairs {z-l, z}"; no closed description was found.
3. Offset game for cluster endgames (scale-free), and the invariant "even count, lead in [width+3, min-3]".

## "Rich world" principle (why everything is a draw until exact change runs out)
Mover D with need a, opponent need b <= a, d = a - b, M = max R.
 * D loses the game  <=>  at some later turn the opponent has a legal turn collecting MORE than his need
   (a "strict finish").  A legal turn from deficit e has sum < e + (last pick), so if D leaves (R', e) with his own
   remaining need a' >= max(R') - 1 the opponent has no strict finish on that turn.
 * If M > b and a - M is a subset sum of R - M, D takes that subset and then M: he collects exactly a (draw at least).
 * If M <= b and d is a subset sum of R, D equalises; then the opponent (tie, max <= half of the rest) cannot finish
   strictly with his single pick.
So with unlimited exact change nobody ever loses.  A player can only be beaten when, at his turn, neither d nor a - M
is representable in the way required -- and the only way the opponent can cause this is by taking the small elements
(he picks the minimum at a tie: the minimum can never be matched exactly).  The proof difficulty is therefore
concentrated in "bottom duels" (both sides eating the smallest elements, leads growing by the gaps) followed by
sparse endgames with 3-6 large elements, where tempo (who may take two large elements in one turn) decides.
The recursive class "TR": even-sum R with max R <= sum/2 such that for every y in R either
   max(R-y) > sum/2 - y and sum/2 - max(R-y) is a subset sum of the rest, or
   max(R-y) <= sum/2 - y and some Q in R-y has sum y with R-y-Q in TR,
is a class of ties where the second player never loses; it fails for dense sets only because of y = min R.

## Generalised conjecture (strongly supported, unproved)
(T) Catch-Up played on ANY complete multiset C of positive integers (sorted c_1 <= c_2 <= ..., c_1 = 1,
    c_{i+1} <= 1 + c_1 + ... + c_i, i.e. every integer in [0, sum C] is a subset sum) with even sum is a draw.
(Z) Moreover no opening loses for the second player (equivalent to (T) restricted to "first player cannot win", by the
    swap lemma), i.e. the mover trailing by any element d of C on C - {d} never loses.
Evidence: all 183,102 complete subsets of [20] (2.3M marked positions); all complete multisets with values <= 6 (mult <= 3)
and <= 8 (mult <= 2); 2454 random sparse complete sets with values up to 3000 (compres.txt); 2500 random complete
multisets with duplicates, values up to 400 (compmsres.txt).  Zero exceptions.  {1,...,N} is the densest instance.
The analogous statement for "nearly complete" sets fails only through the minimum element (conjecture N*), and the
statement for symmetric sets fails outright for sparse sets.

## Run-structure observations (dense phase; informal)
With the opponent O to move and D leading by delta <= min R (so O single-picks y):
 * if succ(y) exists, D may answer succ(y): lead grows by the gap; if pred(y) >= y - delta, D may answer pred(y);
 * the only pick D cannot answer with ONE element is the global maximum when delta < max - second max (D must then
   take two elements; the count parity flips);
 * bad parity (odd number of elements at O's turn) is fatal only in top-heavy/cluster sets; with a rich bottom D can
   re-flip by a voluntary double (possible whenever his deficit exceeds min R), which O can prevent only by picking
   the minimum, at a cost of at least 1 per round.
After the opening 16 on {1..16} almost every reply is safe (all 56 two-element replies, 287 of 290 three-element ones).
A proof along these lines needs a class of positions tolerating arbitrarily many holes in the middle: not found.
