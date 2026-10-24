---
name: periodic-check
description: Run the project's periodic consolidation check (notes/design/PERIODIC_CHECK.md) on the sections that changed since the last one, file findings in Linear, and open a PR with the fixes and report. Use when asked to run the periodic check.
argument-hint: "[nearcore checkout]"
---

Run the periodic check described in `notes/design/PERIODIC_CHECK.md`. That file
says what each section checks and the rules for fixes; this one says how to run
it. You are the coordinator: you own the report and delegate the sections.

1. **Start clean.** Work in a fresh worktree of `origin/main` with a clean tree.
   Never merge anything; the result is a PR.

2. **Find what is due.** Run `just periodic-due`. If it prints "Nothing is
   due.", say so and stop. Otherwise only the listed sections run; the report
   names the skipped ones.

3. **Section 1 first (`build`), if due.** Find the nearcore checkout: the
   argument (`$ARGUMENTS`) if given, otherwise `~/Documents/near/nearcore`. It
   must be clean and at the revision in `near-lean/runtime/reference.json`. If
   it isn't, don't touch it: add a worktree of it at that revision in the
   scratchpad (`git -C <checkout> worktree add <dir> <revision>`) and use that.
   Run `just periodic-check <checkout>` in the background; it takes hours. If a
   step fails, fixing it comes before everything else.

4. **The other due sections in parallel**, as subagents with narrow briefs:
   the section text from `PERIODIC_CHECK.md`, the commit range since the
   section's `commit` in `reports/periodic/LEDGER.json`, the files to look at,
   and the answer format (findings with file, line and a proposed fix). Follow
   "Running the check with agents" for models and for one editor per Lean
   package. Accept a fix only after a rebuild that actually ran.

5. **File what isn't fixed** in Linear, team Safe-near, following "Findings in
   Linear": open the review issue first, search the open issues with the label
   and comment instead of duplicating, and file the rest as its sub-issues.

6. **Report and ledger.** Attach the report to the review issue as a Linear
   document, as section 10 describes; don't commit it. Then record the
   sections that ran:

       python3 tools/periodic_check.py --record <section>... --report <review issue URL> --issue <ID>...

7. **PR.** Run `just ci-check`, commit the fixes and the ledger, and open a
   PR. Its description lists the findings, their Linear IDs and anything that
   needs the maintainer.
