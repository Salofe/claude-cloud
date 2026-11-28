# Memory for lefttosolve work (always loaded; keep current)

We compete on lefttosolve.com (Lean 4 proofs of open/known problems; upstream GuillaumeBAUD-coder/open-math-agents;
our account Salofe submits via the fork Salofe/open-math-agents). Goals: (1) leaderboard points, (2) first-ever solutions
of known open problems, ideally Erdős prize problems. Records live in `lefttosolve/` (README table of PRs, proofs,
`moonshots/` reports, `prize_kit/` setup + prior prize work, `LEARNINGS.md` details). This file is an interim version;
a fuller one generated from all our history replaces it.

## Scoring and merger
- Points = max(1, round(d^1.5/10)), x1.5 for open problems; ONLY the first merged proof of a problem scores.
- Steps of a reduction are worth max(1, parent/n); statements score 0 points (they only enable proofs).
- The merger gives verdicts oldest PR first: filing early wins. CI runs on the merge with current main, so a proof
  fails if its statement is not on main yet when CI runs (re-file it after the statement merges).
- 28 Nov: the merge queue lagged ~5,000 PRs and then stalled; a rejected PR stays open with a comment.

## What worked / what failed
- Worked: proving statements other accounts filed but not yet merged, filing the proof right away; filing our own
  statement then its proof immediately; adapting our proof to a rival's earlier statement (bridge lemmas).
- Failed: racing freshly merged statements (others snipe in 5-15 min); holding proofs until statements merge;
  submit steps waiting behind busy agents (file accepted results yourself, immediately); a GitHub Actions outage whose
  queued PRs were partly never opened (always verify that every "queued" item became a PR).
- Before investing in a problem with a rival PR, run the rival's proof through the official checker; if it passes, skip.

## Lean / checker
- Format, lint rules and check commands: see `lefttosolve/prize_kit/README.md`. No double quotes; only @[simp];
  axioms propext/Classical.choice/Quot.sound; `decide +kernel` allowed; 30-minute check limit; kernel ~1 us per
  reduction step, files are checked sequentially, intermediate values are retained (chunk big computations).
- Fast patterns: card bijections (card_nbij', Fintype.card_congr), row-state/transfer recursions, closed form ->
  recurrence -> g.f. by coefficient comparison, interval_cases + decide, omega (rewrite abs first), covering congruences
  for disproofs. Mathlib has a top-level toZ: use full names to avoid ambiguity.

## Research method
- Test every lemma numerically before proving; verify certificates independently; use 2 skeptical reviewers before
  trusting a proof; check literature and rival PRs first; stop and switch when an approach stalls.
- Prize money requires a FULL solution accepted by mathematicians; steps only earn site points.

## Hard constraints (user)
- Never ask for or paste tokens; PR bodies say `Model: unknown`; never model identifiers in PRs/commits.
- Never copy other teams' Lean proofs. No duplicate submissions. Don't work around permission denials.
- Commit trailers and PR footers: use the attribution lines your session is given.

## Parallel sessions
- The main session (orchestrator, points pipeline) and a Fable-led prize session run in parallel and talk with the
  session message tools. Do not duplicate each other's work; report results to the other session by message.

## Keeping this file current
- Append durable learnings here (one line each) and details to `lefttosolve/LEARNINGS.md`; prune stale facts; commit.
