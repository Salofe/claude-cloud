export const meta = {
  name: 'lefttosolve-formalize-prove-v2',
  description: 'Side track: pick provable OEIS conjectures that have no Lean statement yet, write statement + full proof, check both, submit the statement PR and the proof PR right after it',
  phases: [
    { title: 'Select', detail: 'pick the most provable conjecture in each small batch (faithful statement + full proof feasible today)' },
    { title: 'Formalize', detail: 'write statements/<id>.lean and proofs/<id>.lean, pass the official checker on both' },
    { title: 'Submit', detail: 'competitor check, then open the statement PR via the fork Action' },
  ],
}
const SP = '/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad'
const FC = '/home/user/google-deepmind/formal-conjectures'
const UP = '/home/user/guillaumebaud-coder/open-math-agents'
const F = `${SP}/open/formalize`
const CTX = `
CONTEXT (shared):
- Site lefttosolve.com lists about 18,000 OEIS conjectures that have no Lean statement yet. A new problem enters the site in two pull requests: first statements/<id>.lean (the statement, reviewed by a human before merge), then, once that is merged, proofs/<id>.lean (the proof). Solving one counts as an OPEN PROBLEM SOLVED. Our policy: only send a statement when we already hold a complete, checker-accepted proof of it, and never send a statement we are unsure of (a wrong statement wastes everyone's time).
- Statement file rules (tools/lint.py): path statements/<id>.lean in ${SP}/oma-check; first line import Mathlib (or Mathlib modules only); namespace OMA.S_<id with every non-alphanumeric character replaced by _>; definitions as needed; exactly one theorem main : <the conjecture> := by sorry (that is the only sorry and the only theorem); no other theorem/lemma. A doc comment at the top: # <OEIS title>, Source: https://oeis.org/A......, Credit: @Salofe, the conjecture quoted verbatim with its author and date, and Formalization notes (offset, index ranges, conventions). State it EXACTLY: same definition of the sequence as the OEIS name/definition, same quantifiers, same index range (e.g. for n > 6), no simplification, no special case. Model the format on ${SP}/oma-check/statements/oeis-a001045.lean and ${SP}/oma-check/statements/oeis-a401159.lean.
- Proof file rules: ${SP}/oma-check/proofs/<id>.lean, first line import OMAStatements.S_<sanitized id> (only Mathlib imports may follow), exactly one theorem OMA.solution : type_of% @OMA.S_<sanitized id>.main := ... (helpers in namespace OMA.Helpers). Lint: no double-quote characters; banned words sorry admit axiom native_decide unsafe partial opaque implemented_by extern macro syntax elab notation infix prefix postfix initialize run_cmd run_tac attribute meta IO, any #command, 'decide := true'; only @[simp]/@[local simp]; set_option only maxHeartbeats/maxRecDepth/synthInstance.* with a number and 'in'; decide +kernel allowed; axioms within propext, Classical.choice, Quot.sound.
- Official checks: cd ${SP}/oma-check && export PATH="$HOME/.elan/bin:$PATH" OMA_FC=${FC} && python3 -I tools/lint.py <file> data/catalog.json && bash tools/check.sh <file> <your dir>/verdict.json . For the statement the verdict must be accepted (the statement compiles); for the proof (which needs the statement file present locally in ${SP}/oma-check/statements/) accepted with axioms within the three. Iterate with scratch files: cd ${FC} && lake env lean <file> (imports of OMAStatements work after one check.sh run). If lake reports a lock, wait and retry.
- OEIS data: curl -s 'https://oeis.org/search?q=id:A186864&fmt=json' (name, data terms, formulas, comments) and the b-file https://oeis.org/A186864/b186864.txt. Mathlib source: ${FC}/.lake/packages/mathlib/Mathlib (grep lemma names; never guess).
- The proof must be OUR OWN work; never copy or port third-party Lean.
- 4 CPUs / 15 GB RAM shared: one Lean process at a time per agent.
- COMPETITOR CHECK: gh api -X GET search/issues -f q='repo:lefttosolve2/open-math-agents is:pr in:title <id>' --jq '.items[] | "\\(.number) \\(.state) \\(.user.login) \\(.title)"' (gh only for this search). If another team has an open PR whose title contains this id, skip it. Also skip if ${UP} already has statements/<id>.lean (git -C ${UP} fetch -q --depth 1 origin HEAD; git -C ${UP} cat-file -e FETCH_HEAD:statements/<id>.lean; never reset that clone).
`
const SEL_SCHEMA = { type: 'object', properties: { chosen: { type: 'string', description: 'id of the single best candidate, or empty' }, feasibility: { type: 'integer' },
  reason: { type: 'string' }, plan: { type: 'string' }, others: { type: 'string', description: 'one line per other candidate: id - why not' } },
  required: ['chosen', 'feasibility', 'reason', 'plan', 'others'] }
const FORM_SCHEMA = { type: 'object', properties: { id: { type: 'string' }, status: { type: 'string', enum: ['both_accepted', 'statement_only', 'failed'] },
  statement_file: { type: 'string' }, proof_file: { type: 'string' }, faithfulness_notes: { type: 'string' }, summary: { type: 'string' } },
  required: ['id', 'status', 'statement_file', 'proof_file', 'faithfulness_notes', 'summary'] }
const SUB_SCHEMA = { type: 'object', properties: { id: { type: 'string' }, submitted: { type: 'boolean' }, pr_url: { type: 'string' }, reason: { type: 'string' } },
  required: ['id', 'submitted', 'pr_url', 'reason'] }

const start = args.start, end = args.end, BATCH = 6
const ranges = []
for (let i = start; i < end; i += BATCH) ranges.push([i, Math.min(i + BATCH, end)])
const out = await pipeline(ranges,
  ([a, b]) => agent(`${CTX}
SELECT: candidates ${a}..${b - 1} (0-based, inclusive) of ${F}/candidates.json (fields id, title, conjecture, ref, authors). For each, run the COMPETITOR CHECK, fetch the OEIS entry, and judge: (1) can the sequence's definition be stated faithfully in Lean without heavy machinery, and (2) can we PROVE the conjecture completely in Lean today (hours, not weeks)? Check the conjecture numerically against the OEIS data/b-file first (a conjecture that fails on the data should be skipped, not disproved here). Prefer conjectures whose proof is a clean combinatorial or algebraic argument (for example a polynomial formula for a count of small configurations on an n X n board for n beyond a threshold, where the count splits by position classes). Choose at most ONE candidate (the most certain to succeed); feasibility >= 7 only if you see the complete route for both the faithful statement and the proof. Return chosen = empty if none qualifies.`,
    { label: `select:${a}-${b - 1}`, phase: 'Select', schema: SEL_SCHEMA }),
  async (s) => {
    if (!s || !s.chosen || s.feasibility < 7) return { select: s }
    const f = await agent(`${CTX}
FORMALIZE AND PROVE ${s.chosen}. Selection notes (verify, do not trust blindly): ${s.reason} Plan: ${s.plan}
1. Fetch the OEIS entry; re-check the conjecture numerically against the data and b-file (python).
2. Write ${SP}/oma-check/statements/${s.chosen}.lean exactly per the statement rules; run the official lint + check.sh on it until accepted. Also write a short python script that recomputes the first terms from YOUR Lean definition's logic and compare them with the OEIS data (faithfulness check).
3. Write ${SP}/oma-check/proofs/${s.chosen}.lean (full proof, no sorry) and run the official lint + check.sh until accepted.
4. Copy both final files to ${F}/statements/ and ${F}/proofs/. If the proof cannot be completed, DELETE ${SP}/oma-check/statements/${s.chosen}.lean and ${SP}/oma-check/proofs/${s.chosen}.lean (keep drafts in ${F}/drafts/) and return failed or statement_only.
Persist: hours are fine. Report faithfulness_notes: how each part of the OEIS definition and conjecture maps to the Lean statement, and the data comparison.`,
      { label: `formalize:${s.chosen}`, phase: 'Formalize', schema: FORM_SCHEMA, effort: 'max' })
    if (!f || f.status !== 'both_accepted') return { select: s, formalize: f }
    const sub = await agent(`${CTX}
SUBMIT THE STATEMENT ${s.chosen} AND THEN IMMEDIATELY ITS PROOF (other accounts read open statement PRs and race to prove them, so the proof PR must follow within minutes). Files: ${F}/statements/${s.chosen}.lean (statement) and ${F}/proofs/${s.chosen}.lean (proof).
1. Re-run the official lint + check.sh on both (statement first, then proof); stop if either is not accepted.
2. Read both files yourself and confirm the statement says exactly what the OEIS conjecture says (definition, indices, quantifiers). Faithfulness notes from the author: ${f.faithfulness_notes}. If anything is doubtful, do not submit (submitted=false, reason).
3. COMPETITOR CHECK again; skip if another team now has a PR for it or statements/${s.chosen}.lean exists upstream.
4. Open the PR: cd /home/user/open-math-agents && git fetch -q origin oma-base (retry if locked); W=${SP}/submit/${s.chosen}-statement; git worktree add -f -B oma/${s.chosen}-statement "$W" origin/oma-base; cp ${F}/statements/${s.chosen}.lean "$W/statements/"; git -C "$W" add statements/${s.chosen}.lean; git -C "$W" commit -q -m "Statement: ${s.chosen}" -m "States the OEIS conjecture for review. A checker-accepted Lean proof is ready and will follow once this is merged." -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ"; git -C "$W" -c push.negotiate=true push -q -u origin oma/${s.chosen}-statement (retry up to 4 times); then git worktree remove --force "$W". Trigger the fork Action with mcp__github__actions_run_trigger (load via ToolSearch): method run_workflow, owner Salofe, repo open-math-agents, workflow_id open-upstream-pr.yml, ref main, inputs {branch: oma/${s.chosen}-statement, body: <body>}, then find the run with mcp__github__actions_list (list_workflow_runs, then list_workflow_jobs) and read the line Opened <url> with mcp__github__get_job_logs (return_content true). Body (no model names):
Statement: ${s.chosen} (states the OEIS conjecture for review)
Source: https://oeis.org/<A-number>
Agent: claude-code
Model: unknown

<two or three lines: what is stated and the formalization notes (offsets, ranges)>
Checked locally with tools/check.sh: the statement compiles. A complete Lean proof of this statement (accepted locally by tools/check.sh) follows as proofs/${s.chosen}.lean in a separate pull request.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ
5. Right after the statement PR has opened (you have its number N): open the PROOF PR. W2=${SP}/submit/${s.chosen}; git -C /home/user/open-math-agents worktree add -f -B oma/${s.chosen} "$W2" origin/oma-base; mkdir -p "$W2/proofs"; cp ${F}/proofs/${s.chosen}.lean "$W2/proofs/"; git -C "$W2" add proofs/${s.chosen}.lean; commit with message ${s.chosen} plus the same two trailer lines; push with retries; remove the worktree; trigger the fork Action with inputs {branch: oma/${s.chosen}, body: <proof body>} and read Opened <url>. Proof body: Lease: none (proof of our own pending statement) / Agent: claude-code / Model: unknown / blank line / Problem: https://lefttosolve.com/p/${s.chosen} / Proves the statement in #N, which must be merged first. / Checked locally with tools/check.sh against that statement: ACCEPTED (axioms within propext, Classical.choice, Quot.sound). / blank line / the two footer lines above. If the Action fails with Actions disabled, append {branch, body} JSON lines for both PRs to ${SP}/open/pr_queue.jsonl and report it.
6. Afterwards remove ${SP}/oma-check/statements/${s.chosen}.lean and ${SP}/oma-check/proofs/${s.chosen}.lean from the shared checker (the copies in ${F} stay). Put the statement PR URL in pr_url and mention the proof PR URL in reason.`,
      { label: `submit:${s.chosen}`, phase: 'Submit', schema: SUB_SCHEMA })
    return { select: s, formalize: f, submit: sub }
  })
return { results: out.filter(Boolean) }
