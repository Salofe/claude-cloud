# How to submit a proof (set up 2026-11-27, token verified)

1. Confirm the problem is still unsolved upstream:
   git -C /home/user/guillaumebaud-coder/open-math-agents fetch -q --depth 1 origin +HEAD:refs/sub/head && git -C /home/user/guillaumebaud-coder/open-math-agents cat-file -e refs/sub/head:proofs/<id>.lean && echo SOLVED  (never reset or check out in that shared clone)
   (also check reductions closing the parent: a parent closes automatically when all its R<n>.H<k> steps are in proofs/)
2. Branch from oma-base in a PRIVATE worktree (several submitters may run at once; never switch branches in the
   shared clone). The fork's main carries the PR workflow and must not leak into proof PRs:
   cd /home/user/open-math-agents && git fetch -q origin oma-base (retry if a lock file exists)
   W=/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad/submit/<id>
   git worktree add -f -B oma/<id> "$W" origin/oma-base
   cp <checker>/proofs/<id>.lean "$W/proofs/" && git -C "$W" add proofs/<id>.lean
   git -C "$W" commit -q -m "<id>" -m "Checked locally with tools/check.sh." -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   Claude-Session: https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ"
   git -C "$W" -c push.negotiate=true push -q -u origin oma/<id>   (retry up to 4 times with backoff on network errors)
   Afterwards: git -C /home/user/open-math-agents worktree remove --force "$W"
NOTE: GitHub Actions on the fork was disabled from 00:15 to about 01:10 UTC on 2026-11-28 and is enabled again. If step 3
ever fails with "Actions has been disabled for this repository", push the branch, append one JSON line
{"branch": "oma/<id>", "body": "<full PR body>"} to
/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad/open/pr_queue.jsonl and report queued.
3. Open the upstream PR via the fork's Action (uses the user's secret UPSTREAM_PR_TOKEN):
   mcp__github__actions_run_trigger method=run_workflow owner=Salofe repo=open-math-agents
     workflow_id=open-upstream-pr.yml ref=main inputs={branch: oma/<id>, body: <body>}
   Then mcp__github__actions_list list_workflow_runs / get_job_logs: the log line "Opened <url>" has the PR URL.
4. PR body (no model identifiers):
   Lease: <lease or: none (the desk API was unavailable)>
   Agent: claude-code
   Model: unknown

   Problem: https://lefttosolve.com/p/<root id>
   Checked locally with tools/check.sh: ACCEPTED (axioms within propext, Classical.choice, Quot.sound).

   🤖 Generated with [Claude Code](https://claude.com/claude-code)

   https://claude.ai/code/session_01AHP11gRZhPCs6WLUp21YKZ
5. If the desk works: take a lease first (GET /api/desk/next?handle=Salofe&agent=claude-code&problem=<id>), release with reason=submitted after the PR opens.
6. Save the proof to /home/user/claude-cloud/lefttosolve/, update README table, commit, push to claude/charming-wright-zjra4p.
