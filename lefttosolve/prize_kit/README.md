# Prize kit: everything a fresh session needs to attack an Erdős prize problem on lefttosolve

Durable copy in this repo; the original working copies lived in an ephemeral scratchpad of the main session.

## 1. Set up the official checker (once per container, ~15-30 min)
```bash
git clone --depth 1 https://github.com/GuillaumeBAUD-coder/open-math-agents ~/oma   # public, read-only
cd ~/oma && tools/oma.sh setup        # installs formal-conjectures at the pinned commit + the Mathlib cache (~14 GB)
export OMA_FC=~/oma/.oma/formal-conjectures PATH="$HOME/.elan/bin:$PATH"
```
If `tools/oma.sh setup` needs elan: `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`.
Read https://lefttosolve.com/join.txt for the site's own instructions.

Check a proof (both must pass; check.sh has a 30-minute limit):
```bash
cd ~/oma && python3 -I tools/lint.py proofs/<id>.lean data/catalog.json && bash tools/check.sh proofs/<id>.lean /tmp/verdict.json
```
Iterate on scratch files with `cd $OMA_FC && lake env lean <file>` (one Lean process per agent; 4 shared CPUs).
Never `git reset`/checkout in a clone other agents use; fetch into a private ref (`git fetch -q --depth 1 origin +HEAD:refs/<name>/head`).

## 2. Proof file format
- Catalog problem `<decl>` in module `<M>`: `proofs/<id>.lean` = `import <M>` then helpers in `namespace OMA.Helpers`, then
  `theorem OMA.solution : type_of% @<decl> := ...` (or `theorem OMA.disproof : ¬ (type_of% @<decl>) := ...`).
- Reduction step `<rid>.H<k>`: `import OMAReductions.R_<rid with non-alphanumerics as _>`, target `OMA.R_<...>.H<k>`.
- Lint: no double-quote characters anywhere; banned words include sorry, admit, axiom, native_decide, unsafe, partial,
  opaque, macro, syntax, notation, attribute (only `@[simp]`); `decide +kernel` is allowed; axioms only propext,
  Classical.choice, Quot.sound; file < 512 KiB.

## 3. Submitting (only a COMPLETE, checker-accepted, independently reviewed solution)
- Attach the fork with push access (add_repo owner Salofe repo open-math-agents access push), then in its clone:
  private worktree from `origin/oma-base`, branch `oma/<id>`, add exactly one file `proofs/<id>.lean`, commit, push.
- Open the upstream PR through the fork's Action (it holds the user's token; never ask for or paste tokens):
  GitHub MCP `actions_run_trigger` method=run_workflow owner=Salofe repo=open-math-agents workflow_id=open-upstream-pr.yml
  ref=main inputs={branch: "oma/<id>", body: <body>}; the job log line `Opened <url>` gives the PR URL.
- PR body: `Lease: none` / `Agent: claude-code` / `Model: unknown` / blank / `Problem: https://lefttosolve.com/p/<root id>` /
  `Checked locally with tools/check.sh: ACCEPTED (axioms within propext, Classical.choice, Quot.sound).` / blank /
  the attribution footer for YOUR session. Never put model identifiers in PRs or commits.
- Competitor check before investing and before submitting (gh only for search):
  `gh api -X GET search/issues -f q='repo:GuillaumeBAUD-coder/open-math-agents is:pr is:open in:title <distinctive token>'`
  (ids containing underscores need a distinctive token rather than the full id).
- `SUBMIT_PROCEDURE_original.md`, `push_branch.sh`, `push_statement.sh`, `overlap_check.py` are the main session's versions
  (their paths point at its scratchpad; adapt paths before use).

## 4. Prior prize-problem work (read before choosing; do not repeat)
- `scout/`: full reduction tree of the prize problems (`red_tree.txt`), all statements (`all_statements.txt`), open and
  unclaimed leaf steps with points (`open_leaves.json`, `free_leaves_live.json`, snapshot 28 Nov 01:25 UTC; re-check live).
- `../moonshots/prize-run-2026-11-28/` (Erdős 713 step proved, Erdős 1 a(9)=161 kernel-time analysis, Erdős 470 notes),
  `../moonshots/firsts-run-2026-11-28/` (Catch-Up, WOWII 189), `../moonshots/gillibert-*` (geodesic deletion, fair traversal).
- Survey conclusion so far: no full prize problem looked realistically solvable; easy steps of prize trees are claimed
  within an hour by other teams; the money is only for a FULL solution accepted by mathematicians.
