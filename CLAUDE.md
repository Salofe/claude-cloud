# Memory for lefttosolve work (always loaded; keep current)

We compete on lefttosolve.com: Lean 4 proofs of problems (catalog Erdős/OEIS/Green/..., site statements, reduction
steps). Upstream repo GuillaumeBAUD-coder/open-math-agents; our account Salofe files PRs through the fork
Salofe/open-math-agents. Goals, in the user's words: (1) "get as many points as possible to climb leaderboard";
(2) be "the first to solve a problem ever, better if important and known problem... more important to solve any than
none". All durable work lives in `lefttosolve/`: README.md (PR table), proofs `*.lean`, STRATEGY.md, RANKING.md,
`moonshots/` (research reports), `prize_kit/` (checker setup, submit scripts, overlap_check.py), and LEARNINGS.md
(every learning below with evidence and confidence, plus calibration numbers). Read LEARNINGS.md before big decisions.

## Scoring and merger facts
- Points per FIRST merged proof: base = max(1, round(d^1.5/10)); kind open = round(1.5*base). d20=9, d30=16,
  d40=25 (open 38), d60=46 (open 69), d90=85 (open 128). Disproofs score like proofs.
- Only the earliest merged proof of an id scores. Later proofs, reductions and shorter proofs score 0; statements
  ALWAYS score 0. Never work on an id whose proof is on main or has a valid pending rival proof PR.
- A merged site statement makes an unformalized problem kind open, so its proof gets x1.5 (~40 pts per OEIS statement).
  File a statement only as the gate for our own proof.
- Step value = max(1, floor(parent/n)) (the site DB figure overrides), n = 2-4 hypotheses; halves (or worse) per
  nesting level. Closing all steps pays the reduction author max(1, floor(step sum/10)). Max 3 reductions per
  target. Prefer shallow steps of rich roots.
- A valid proof of a step's parent (merged OR pending) makes all its sub-steps worthless: check every ancestor's PRs.
- Merger v4: verdicts go oldest PR number first among COMPLETED CI runs (batches of 40). Filing order decides who is
  first, so open the PR the second a proof passes the checker; keep files fast so CI completes early.
- CI compiles GitHub's merge commit with main as of the run: a proof of a site statement not yet on main fails in
  seconds ("has no Lean statement yet"). Re-file (new branch) once the statement merges; a watcher does this.
- Statement PRs auto-merge as soon as they compile; faithfulness is reviewed later. One statement per id; first verdict
  wins; a resubmission gets a new, higher number and loses to anything filed in between.
- The merger scans only the last 3 h of runs; runs lost across merger versions need tools/requeue.tsv (we cannot edit
  it; the user must ask the maintainer). If a PR has no verdict 1-2 h after later PRs merged, act at once.
- Expect verdict delays of hours (on 28 Nov the queue lagged ~5,000 PRs, then stalled).
- The site pays points, not money. Erdős prize money needs a full solution accepted by mathematicians.

## Submission procedure (details: lefttosolve/prize_kit/README.md)
- One PR adds exactly ONE file under proofs/, statements/ or reductions/. Build it in a private worktree from
  `origin/oma-base` of the fork clone, branch `oma/<id>` (re-file: a NEW branch, e.g. `oma/<id>-p2`), commit, push.
- Open the upstream PR via the fork Action open-upstream-pr.yml (GitHub MCP actions_run_trigger, inputs branch+body).
  It is idempotent per branch; read the URL from job log line `Opened <url>`. The PAT lives only in the fork secret.
- PR body lines: `Lease: <lease or none (reason)>`, `Agent: claude-code`, `Model: unknown`, blank,
  `Problem: https://lefttosolve.com/p/<root id>`, the local check line, blank, the session's attribution footer.
  For a pending statement add: `Proves the statement in #N, which must be merged first.`
- The fork Action titles the PR from the branch name. Titles must be the exact id (or `statement: <id>`), because
  the merger's pending list and rivals' competitor checks key on the title; `<id>-statement`/`<id>-p2` titles are
  invisible to them. Fix the Action's title input before filing more statements/re-files.
- Our own statement + proof: file the proof PR within a minute of the statement PR. Never hold the proof back.
- Subagents may be denied triggering the fork Action (classifier: Unsanctioned Communication). Do not use fallbacks;
  file from the main session.
- After any batch/flush or Actions outage, reconcile every pushed oma/* branch, every pr_queue.jsonl line and every
  "queued" claim against our real PRs (gh search author:Salofe). A flush once silently skipped 10 proofs; never report
  "filed" without a PR URL.
- Before filing: re-run competitor search (<2 min old), lint + check.sh on the exact file, overlap check.
- File accepted results yourself the moment they pass; never leave them waiting for a queued submit agent.
- Desk lease API is optional and often unavailable; `Lease: none (<reason>)` is fine.
- Pushing a real fix to the SAME rejected PR keeps its older number; ask the user before doing this.

## Lean / checker rules
- Proof file `proofs/<decl id>.lean`: first non-comment line `import <module>` (guillemets, e.g. `«1129»`), then
  Mathlib imports only; exactly one `theorem OMA.solution : type_of% @<decl>` or `OMA.disproof : ¬ (type_of% @<decl>)`.
  Name OMA.solution nowhere else; the upstream decl name only inside `type_of% @`. Helpers in `namespace OMA.Helpers`.
- Step: `proofs/<X>.R<n>.H<k>.lean`, `import OMAReductions.R_<sanitized>`, target `OMA.R_<sanitized>.H<k>`.
  There is NO disproof form for steps: a false step cannot score; drop it or attack the parent/root.
- Site statement: `statements/<id>.lean`, `import Mathlib`, `namespace OMA.S_<sanitized>`, exactly one
  `theorem main : ... := by sorry`. Proof imports `OMAStatements.S_<sanitized>`, target `type_of% @OMA.S_<..>.main`.
- Value problems (data/placeholders.json): `def OMA.answer := <explicit value>` and
  `OMA.solution : <placeholder> = OMA.answer → type_of% @decl`. No sInf/sSup/choice/Nat.find/own defs in the answer.
- Lint: no double-quote chars in code; no `/-` or `-/` inside comment prose. Prefix-banned identifiers: macro*,
  syntax*, elab* (incl. @[elab_as_elim]), notation*. Also banned: sorry, meta, IO, partial, opaque, axiom,
  attribute, unsafe, extern, prefix/postfix/infix, initialize, `import Lean`, Lean.Meta/Elab, `decide := true`,
  native_decide, and every `#command` (#eval, #print, #check...; the regex also hits Finset-card `#simp..`/`#test..`
  names, so write Finset.card). bv_decide/LRAT add Lean.ofReduceBool and fail the axiom check: use `decide +kernel`.
  Only `@[simp]`/`@[local simp]` attributes.
- `set_option` only `maxHeartbeats|maxRecDepth|synthInstance.* <n> in` per declaration. File limit 512 KiB raw.
- Axioms allowed: propext, Classical.choice, Quot.sound. Any upstream def built on sorry poisons the statement:
  skip such ids. Use only upstream DEFINITIONS + Mathlib + own lemmas (upstream theorems may be sorry).
- Run lint from the checker root with the file physically there:
  `cd <oma> && python3 -I tools/lint.py proofs/<id>.lean data/catalog.json && bash tools/check.sh proofs/<id>.lean v.json`.
  Linting a path outside proofs/ fails (266 transcripts hit this). Steps/statements need their module locally.
- check.sh: the proof must compile in 30 min (1800 s; over = rejected); upstream gives imports 1200 s (refresh
  stale local copies). Median accepted check 26 s (p90 60 s); first build of a new module adds 25-70 s.
- Iterate with `cd <FC> && lake env lean scratch.lean`; FC must be at the catalog's pinned commit.
- Adaptation runs swap statements in FC: restore ours and byte-compare reductions before trusting other verdicts.

## Fastest proof patterns
- Kernel computation: Nat literal primitives (beq/ble/blt, + * / %, gcd, pow, land/shifts, cond) in Nat.rec or
  binary-split `chk d lo` checkers, soundness lemma by induction, close with `decide +kernel`. Template:
  lefttosolve/oeis-a072872.lean. Avoid List/Finset/Decidable machinery (10x slower).
- Kernel cannot run at scale: Nat.choose, primeCounting/Mathlib Prime test, Nat.digits, minFac, Array.mapM, Nat.sqrt
  (mixed). Replace with own structural checker + bridge lemma (trial division, `d*d > n`, factorials).
- Kernel cost: ~1 µs/step, 1e4-2e4 loop iterations/s, ~3.5 KB retained per loop step, theorems checked sequentially.
  Budget ~1e9 steps per file. Measure node counts in Python/C first; above that, plan a reduction tree.
- Chunk big computations into separate theorems of 10-60 s each (Erdos151: 32 chunks; Erdos982: 8). Use symmetry
  breaking (Erdos944: 5.8 GB -> 1.0 GB). Short-circuit `&&`/`||`; truncate sums; tighten bounds in Python first.
- Counting: Fintype.card_congr with an explicit Equiv, Finset.card_nbij', Fin.consEquiv; Decidable via
  `inferInstanceAs`. Templates: lefttosolve/oeis-a188148.lean, oeis-a195233.lean.
- Transfer matrix: rows as Fin 16 via testBit, compat_iff by decide +kernel on 256 pairs, recursion G, per-state
  closed form by induction (lefttosolve/oeis-a188861.lean).
- Closed form -> recurrence (push_cast, ring) -> g.f. (coeff_mul_X_pow', rcases k, PowerSeries.eq_mul_inv_iff_mul_eq).
  Prove g.f. lemmas generically for f : ℕ → ℚ, then instantiate (concrete `a` hits heartbeats).
- Primes: norm_num for explicit primes; Nat.nth_count + decide +kernel for nth prime; covering congruences residue by
  residue for Riesel/Sierpinski disproofs (lefttosolve/OeisA108129.conjecture.R1.H1.lean).
- Finite cases: bound, interval_cases, decide (ZMod); `rcases hn with rfl|rfl|... <;> decide +kernel`.
- omega treats products/powers as atoms: supply bounds in that exact atom form. Huge literals: norm_num, not omega.
  On timeouts restructure into small lemmas rather than raising heartbeats.
- Grep Mathlib for every lemma name; never guess. Qualify helper names (Mathlib has top-level `toZ`).
- Statements: counts as `noncomputable def a n := by classical; exact Fintype.card {w // P w}`; g.f. in product form
  over ℚ; recurrences in ℤ with `k < n →` guards; keep the OEIS offset.
- Rival statement for our id filed or merged before ours: do not wait on ours; adapt our proof to THEIR statement
  (fetch only their statements file, copy our defs into OMA.Helpers, prove bridge lemmas; 7/7 accepted, ~7 min each).

## Problem selection and triage
- Ranking by points per agent-hour: (1) prove other accounts' pending, unmerged statement PRs (snipe, ~11 agent-min per
  PR, 37% of triaged filed); (2) our own OEIS statement+proof pairs (~30 min/pair); (3) adapt to rival statements;
  (4) shallow steps of high-value roots right after a reduction appears; (5) deep research in the background.
- Do NOT: race freshly merged statements (rivals file in 5-20 min; we lost ~20 accepted proofs), broad catalog scans
  (~880-1,360 scanned, ~1 filed), blind OEIS counterexample sweeps (0/197), the site's "easiest" stalled problems.
- Snipe pool: ids with exactly one open PR (a statement, not ours), newest first; rebuild every cycle. Easy authors:
  jleguina, KoaOkano, etaubman, xor2k, Mapika, caa1982. Dugongue/longling12: mostly research or false: test quickly.
- Disproof checklist (~5% of pending statements are false): n=0/1 and empty cases, smallest params, missing hypothesis,
  recurrence range at its first index, covering congruence, algebraic obstruction, search 10-20x past the b-file.
  Watch junk values (f n = 0 defaults) that make single counterexamples insufficient.
- Skip: prime-existence/infinitude, digit statistics, asymptotics (Tendsto, =O, ∀ᶠ), value problems needing an exact
  extremal answer, upstream-sorry statements, anything needing theory Mathlib lacks.
- Our own pairs: Hardin/Barker families (array counts, CA ON-cells, k-step tours/walks, polynomial closed forms).
  Avoid A-number ranges where a rival (jleguina sweeps by A-number) already has sibling PRs.
- Faithfulness: brute-force every reading of the OEIS definition in Python against data and example arrays. Hardin
  tours: k-step = k squares visited, jumps allowed, summed over starts. Adjacency linear, not cyclic. "Two others" =
  distinct positions. Never file a Barker recurrence whose stated range fails at its first index (disprove rivals').
- Cache OEIS JSON/b-files once per run (rate limits); use the oeisdata mirror.
- Competitor check: `gh api -X GET search/issues -f q='repo:GuillaumeBAUD-coder/open-math-agents is:pr is:open
  in:title <id>'`, keep titles ending with the id, exclude Salofe; for ids with underscores search a distinctive token.
  Run at triage and again right before filing. A failed search/fetch is NOT "unsolved". A rival PR with a proof file
  is ~95-99% valid (112/113 passed): skip, or run its file through our official checker before investing (judge
  validity only, never read it for ideas). One with no proof file (statement only) does not block.
- Triage feasibility >=7 almost always yields an accepted proof: the risk is the race, not the math. Let triage agents
  that already hold an accepted proof submit at once. State the 0-10 scale in schemas (agents returned 0-100).

## Research / moonshot method
- Prefer self-contained provable steps inside open prize trees over open cores (only research win: Erdős 713 (i)
  R3.H2, 28 min, PR #18340). Selector odds of 1-10% for cores are honest (8 attacks, 1 lemma-level win).
- Cap selection at 30-45 min, reuse scouting files, timebox attacks ~2 h with a checkpoint (certificate or closing
  lemma in sight?). Stop early if a proof would imply a famous conjecture or needs missing Mathlib theory.
- Firsts come from the long tail: obscure/recent OEIS comments, Open Problem Garden, quick numeric checks past the b-file
  (A072872 n=6298, PR #13111). Measure the margin first: growing representation counts mean no counterexample.
- Read the full source (comments, later edits) before computing or claiming novelty; others often searched far beyond us.
- Verify planned routes in the first 15-30 min and switch freely. Test lemmas numerically with negative controls;
  validate pruned searches vs brute force and known answers; re-verify certificates independently; test on random
  large/sparse instances, not just small exhaustive ranges; refute natural strengthenings early.
- A claimed open-problem proof needs the official check plus two skeptical reviewers before filing.
- After proving a step, scan siblings for reuse of the same core (check rivals first).
- Write notes.md during every attack (with an "if someone resumes" section) and copy it to lefttosolve/moonshots/.
- Resumable: Erdős 470 R2.H2 search tree (if rivals fail); Erdős 1 a(9) needs ~40 leaf files, not one file.
- Prize cores audited twice (LEARNINGS R26, prize_lead/REPORT.md): none reachable; 711 (i) is arithmetic-Kakeya-hard,
  647 has no expected witness (searched to 1e22). Do not re-audit; status of all Erdős problems in one fetch: R27.
- Fable: deep mathematics only, short audits, more attempts; its weekly quota runs out (hit twice). Use the default
  model for computation, Lean engineering, literature and reviews; tell the user when Fable is exhausted.
- If a site refuses automated fetches (e.g. erdosproblems.com), do not spoof a browser user-agent; use other sources (teorth/erdosproblems data on GitHub, arXiv, OEIS).

## Operations
- Machine: 4 shared CPUs, 15 GB (cgroup ~13.4 GB). Mathlib import maps 6-7 GB RSS (judge by anonymous memory).
  One Lean process per agent; concurrent Lean jobs get OOM-killed ("does not compile", exit 137): re-run when free.
  Research jobs: <=2 cores, <=4 GB, nice -n 15, stream big data, delete downloads.
- Workflow tool runs ~2 agents at once (min(16, CPUs-2)): submit steps queued ~70 min behind attacks. Submit from
  the main session; give each long attack its own workflow. No barriers between batches; scripted overlap check
  instead of verify agents; batches of ~6-8.
- Fewer simultaneous race jobs = each finishes sooner (load 10+ made Lean checks crawl).
- Bash background jobs stop at 30 min default (max 2 h): pass timeouts, checkpoint, make runs resumable.
- Watchers beat check-ins: own-statement watcher (3 min) to re-file proofs when statements merge; upstream watcher
  (4 min) waking only for new unclaimed statements. While Actions is down, park work instead of waking.
- Before race hunts, confirm a cheap fork Action run works. If "Actions has been disabled", give the user the exact
  settings URL at once and stop starting new races.
- Shared upstream clone (/home/user/guillaumebaud-coder/open-math-agents): fetch only into private refs
  (`+HEAD:refs/<name>/head`), read with `git show ref:path`, NEVER reset/checkout/switch there; gc.auto 0; avoid
  concurrent fetches (shallow.lock races, proxy 429). Read rival PR files via `git fetch pull/N/head` into a
  blob-less clone. GitHub search caps at 1,000 results: query in 30-min `created:` windows, sleep 2-2.5 s.
- Every check-in: list new PRs; file stuck accepted results; re-file proofs whose statement merged; confirm queued items
  became PRs; reconcile journals with lefttosolve/README.md (merged/lost/waiting); read and update this file; commit+push.
- Record repo: push only to branch claude/charming-wright-zjra4p; fork: only oma/* branches. Commit untracked work
  (a stop hook requires it). Commits carry the session's standard trailers.
- Scratchpad (/tmp/claude-0/.../scratchpad: oma-check checker, open/ watchers and pools) is EPHEMERAL. Durable copies:
  prize_kit/ (setup, push scripts, overlap_check.py), moonshots/, proofs in lefttosolve/. Copy new tools there.

## User preferences and hard constraints
- Never ask for, paste or print tokens. PR bodies say `Model: unknown`; never model identifiers in PR titles/bodies.
- Credit stays with Salofe (user offered Claude credit; declined).
- No duplicate submissions: skip ids with a valid rival proof PR; prefer ids nobody filed.
- Never port, copy or take ideas from third-party Lean proofs (checking a rival file's validity with the checker is
  fine); run prize_kit/overlap_check.py before every submit (flags >=10% identical substantive lines); rename generic
  helpers problem-specifically.
- Never work around permission or classifier denials (no git reset on shared clones, no rewording to dodge checks).
- No empty commits or close/reopen to kick CI. Leave lost PRs open. Ask before trivial placeholder answers or
  formalization-gap disproofs (pending asks: LEARNINGS.md U4).
- PRs are opened autonomously (user does not want to click links). "Burn my limits" when asked.
- Target choice: not the stalled easiest; rank what AI is good at; overnight, harder problems that won't fall hourly.
- User is usually on a phone, clock UTC-6: convert times, keep messages short, give exact URLs for settings.

## Parallel sessions
- The main session (orchestrator, points pipeline) and a Fable-led prize session may run in parallel and talk via the
  session message tools. Do not duplicate each other's work; report results to the other session by message.

## How to keep this file current
- After each run or check-in, append new durable learnings here (one or two terse lines, with a key number) and the
  detail with evidence and confidence to lefttosolve/LEARNINGS.md (same categories).
- Prune stale or contradicted facts; prefer recent high-confidence evidence and note the change in LEARNINGS.md.
- No volatile state here (open PR lists, task ids) except as examples. Keep under ~220 lines.
- Commit both files with the usual trailers and push to the record branch.
