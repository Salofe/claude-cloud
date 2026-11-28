export const meta = {
  name: 'lefttosolve-statement-snipe-v2',
  description: 'Prove site statements that other teams submitted but that are not merged yet and have no proof PR: triage, prove, file the proof PR first (queued while Actions is disabled)',
  phases: [
    { title: 'Triage', detail: 'fetch each pending statement from its PR, judge provability, prove the quick ones at once' },
    { title: 'Prove', detail: 'full Lean proof of the promising ones' },
    { title: 'Submit', detail: 'competitor check, provenance, branch + PR (or queue)' },
  ],
}
const SP = '/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad'
const FC = '/home/user/google-deepmind/formal-conjectures'
const UP = '/home/user/guillaumebaud-coder/open-math-agents'
const PRR = SP + '/open/prrepo'
const POOL = SP + '/open/' + (args.pool || 'snipe_candidates.json')
const CTX = `
CONTEXT (shared):
- Site lefttosolve.com scores the FIRST merged proof of a problem. Other teams submit statements/<id>.lean pull requests (new open problems, mostly OEIS conjectures); once a statement is merged anyone may prove it, and teams race. We prove statements that are still in an OPEN statement PR (not yet merged) and file our proof PR early, so we are first in the merger's filing order. Each candidate below comes with the number of the statement PR.
- Get the statement text: git -C ${PRR} fetch -q --filter=blob:none --depth 1 origin pull/<pr>/head && git -C ${PRR} show FETCH_HEAD:statements/<id>.lean > <your work dir>/statement.lean . If that file does not exist in the PR, the PR is not a statement PR: skip the candidate (feasibility 0, reason not a statement PR). Never reset or check out in that clone; FETCH_HEAD is shared, so run the show right after your own fetch, in the same command.
- A proof is ${SP}/oma-check/proofs/<id>.lean whose FIRST line is import OMAStatements.S_<id with every non-alphanumeric character replaced by _> (only Mathlib imports may follow) and which contains exactly one of theorem OMA.solution : type_of% @OMA.S_<sanitized id>.main := ... or theorem OMA.disproof : ¬ (type_of% @OMA.S_<sanitized id>.main) := ... ; helpers in namespace OMA.Helpers. Statement definitions may be used. Example of an accepted file (format only): ${SP}/oma-check/proofs/oeis-a072872.lean.
- To check locally, copy the statement into ${SP}/oma-check/statements/<id>.lean (it is not on main yet), then: cd ${SP}/oma-check && export PATH="$HOME/.elan/bin:$PATH" OMA_FC=${FC} && python3 -I tools/lint.py proofs/<id>.lean data/catalog.json && bash tools/check.sh proofs/<id>.lean <your dir>/verdict.json ; the verdict must be accepted. Iterate with scratch files: cd ${FC} && lake env lean <file> (one Lean process at a time per agent; if lake reports a lock, wait and retry).
- Lint rules: no double-quote characters; banned words: sorry admit axiom native_decide unsafe partial opaque implemented_by extern macro syntax elab notation infix prefix postfix initialize run_cmd run_tac attribute meta IO, any #command, 'decide := true'. Only @[simp]/@[local simp]. set_option only maxHeartbeats/maxRecDepth/synthInstance.* with a number and 'in'. 'decide +kernel' allowed. Axioms within propext, Classical.choice, Quot.sound.
- Typical provable OEIS statements: closed forms, recurrences and generating functions of counting sequences (R. H. Hardin's n X k array counts, cellular automata cell counts, lattice walks, linear recurrences), identities with explicit sums. Typical unprovable ones: prime-existence or infinitude conjectures, Goldbach-type statements, digit-pattern finiteness. Our own earlier accepted OEIS proofs (technique only, the statements differ): ${SP}/open/formalize/proofs/.
- Mathlib: ${FC}/.lake/packages/mathlib/Mathlib (grep for lemma names; never guess).
- The proof must be OUR OWN: never copy, port or consult other teams' Lean proofs (do not open other PRs' proofs/ files).
- 4 CPUs / 15 GB shared with other agents: keep decide +kernel computations modest (chunk them).
- COMPETITOR CHECK (mandatory, before starting a proof and again just before submitting): gh api -X GET search/issues -f q='repo:lefttosolve2/open-math-agents is:pr is:open in:title <id>' --jq '.items[] | select(.title | ascii_downcase | endswith(\"<id>\")) | \"\\(.number) \\(.user.login)\"' (gh only for this search; if rate-limited wait 60 s and retry). Ignore the statement PR itself (its number is given) and PRs by Salofe. If any OTHER open PR exists for the id, another team is already proving it (or competing with the statement): skip, unless you check its files (git -C ${PRR} fetch -q --filter=blob:none --depth 1 origin pull/<n>/head && git -C ${PRR} cat-file -e FETCH_HEAD:proofs/<id>.lean && echo PROOF) and it has no proofs/<id>.lean. Also skip if proofs/<id>.lean already exists upstream (git -C ${UP} fetch -q --depth 1 origin HEAD; git -C ${UP} cat-file -e FETCH_HEAD:proofs/<id>.lean).
`
const SUBMIT = (id, pr, user) => `Submit the proof of ${id} now. 1. Re-run the official lint + check.sh (statement copied from PR #${pr} into ${SP}/oma-check/statements/${id}.lean); do not submit unless accepted. 2. COMPETITOR CHECK again (ignore #${pr} and Salofe). 3. python3 -I ${SP}/overlap_check.py ${SP}/oma-check/proofs/${id}.lean (do not submit if SUSPICIOUS). 4. Follow ${SP}/SUBMIT_PROCEDURE.md exactly (read it first, including the note on Actions being disabled and the queue file): private worktree from origin/oma-base on branch oma/${id}, push, then open the PR with the fork Action or queue it. PR body: Lease: none (statement pending in #${pr}) / Agent: claude-code / Model: unknown / blank line / Problem: https://lefttosolve.com/p/${id} / Proves the statement in #${pr} (by ${user}), which must be merged first. / Checked locally with tools/check.sh against that statement: ACCEPTED (axioms within propext, Classical.choice, Quot.sound). / then the footer from SUBMIT_PROCEDURE.md. You are authorized to use git in /home/user/open-math-agents for this.`
const TRI = { type: 'object', properties: { candidates: { type: 'array', items: { type: 'object', properties: {
  id: { type: 'string' }, pr: { type: 'integer' }, user: { type: 'string' }, feasibility: { type: 'integer' }, direction: { type: 'string', enum: ['prove', 'disprove', 'skip'] },
  reason: { type: 'string' }, plan: { type: 'string' }, submitted: { type: 'string', description: 'PR URL, or queued, or empty' } },
  required: ['id', 'pr', 'user', 'feasibility', 'direction', 'reason', 'plan', 'submitted'] } } }, required: ['candidates'] }
const ATT = { type: 'object', properties: { id: { type: 'string' }, status: { type: 'string', enum: ['accepted', 'partial', 'failed'] }, notes: { type: 'string' } }, required: ['id', 'status', 'notes'] }
const SUB = { type: 'object', properties: { id: { type: 'string' }, submitted: { type: 'boolean' }, pr_url: { type: 'string' }, queued: { type: 'boolean' }, reason: { type: 'string' } }, required: ['id', 'submitted', 'pr_url', 'queued', 'reason'] }
const B = 8
const ranges = []
for (let i = args.start; i < args.end; i += B) ranges.push([i, Math.min(i + B, args.end)])
const out = await pipeline(ranges,
  ([a, b]) => agent(`${CTX}
TRIAGE candidates ${a}..${b - 1} (0-based, inclusive) of ${POOL}: each entry is [id, statement PR number, statement author, created_at, flag]. Read your slice with python3 -I. For each: fetch the statement from its PR (see CONTEXT), read it exactly, run the COMPETITOR CHECK, and judge whether a complete Lean proof (or a disproof, if the statement is false as written: test numerically first) is feasible TODAY (hours). Be fast and decisive: skip research-level statements in one or two sentences. If a proof is quick, write it, get it ACCEPTED, and submit it yourself at once: ${SUBMIT('<id>', '<pr>', '<user>')} Put the PR URL (or the word queued) in submitted. Return one entry per candidate (${b - a} entries).`, { label: `triage:${a}-${b - 1}`, phase: 'Triage', schema: TRI }),
  (t) => {
    if (!t) return []
    const good = t.candidates.filter(c => !c.submitted && c.feasibility >= 6 && c.direction !== 'skip').sort((x, y) => y.feasibility - x.feasibility).slice(0, 3)
    const done = t.candidates.filter(c => c.submitted).map(c => ({ triage: c, submit: { id: c.id, submitted: true, pr_url: c.submitted } }))
    if (good.length) log(`prove: ${good.map(c => c.id).join(', ')}`)
    return parallel(good.map(c => async () => {
      const r = await agent(`${CTX}
GOAL: a checker-ACCEPTED proof file ${SP}/oma-check/proofs/${c.id}.lean for the pending statement ${c.id} (statement PR #${c.pr} by ${c.user}). Direction: ${c.direction}. Triage notes (verify): ${c.reason} Plan: ${c.plan}
Work in ${SP}/open/snipe/${c.id}/. Fetch the statement from PR #${c.pr} and copy it to ${SP}/oma-check/statements/${c.id}.lean. COMPETITOR CHECK first; stop (status failed) if blocked. Formalize incrementally, test numerically, then run the official lint + check.sh until accepted. Persist up to a few hours; stop early on a concrete obstruction.`, { label: `prove:${c.id}`, phase: 'Prove', schema: ATT, effort: 'high' })
      if (!r || r.status !== 'accepted') return { triage: c, attempt: r }
      const s = await agent(`${CTX}\n${SUBMIT(c.id, c.pr, c.user)}\nReport the PR URL (from the Action log line Opened <url>) or queued=true.`, { label: `submit:${c.id}`, phase: 'Submit', schema: SUB })
      return { triage: c, attempt: r, submit: s }
    })).then(x => done.concat(x))
  })
return { results: out.filter(Boolean).flat().filter(Boolean) }
