# Left to Solve: points strategy (2026-11-28)

## How the site scores (from upstream lib/points.ts and lib/ledgercore.ts)
- Proof of a problem: round(difficulty^1.5 / 10), times 1.5 for open problems. Only the FIRST merged proof scores.
- Step of a reduction: parent's points divided by the number of steps (2 to 4). Closing a parent through all its steps
  gives the reduction's author max(1, sum of step points / 10).
- Statements and shorter proofs: 0 points (shown in history only).
- The merger handles pull requests oldest first, so the earliest filed valid proof wins.

## Where the points are (solved list, 18:00-00:10 UTC on 2026-11-27)
- Proofs of new site statements (mostly OEIS): about 12,100 points over 299 proofs (about 40 each).
- Steps: about 2,700. Catalog open problems: about 1,900. MathOverflow statements: about 1,800.
- Leaders: Genbox 6,691 (5,743 of it from 292 catalog "known" problems, early), marcusbuffett 5,182 (steps),
  TheWaler 4,518, ivillar 4,098 (steps). Salofe: 1,786, rank 9.

## Plan
1. Prove pending statements first: other teams file about 100-600 statement PRs an hour. We prove the provable ones
   (OEIS closed forms, recurrences, generating functions, counting formulas) while the statement PR is still open and file
   our proof PR at once, so we are first in filing order. Two snipe workflows run on the newest candidates.
2. Our own statement + proof pairs: file the proof PR immediately after the statement PR (holding it let other teams in).
3. Watch upstream every 4 minutes: new merged statements and new reductions with no PR get triaged at once.
4. Steps of new reductions (step-stream workflows) whenever upstream adds reductions.
5. Fable: long attacks on important, unclaimed open problems for a first-ever solution (lefttosolve-fable-firsts).
