# CI runner

The workflows use self-hosted Linux x64 runners. Hostnames, provider details,
user accounts and service-management instructions belong in private operator
configuration.

## Public pull request approval

All external contributors must receive workflow approval before their fork PR
workflows can run, including contributors whose earlier PRs were merged. The
desired GitHub setting is committed in `.github/actions-approval-policy.json`.
With an authenticated GitHub CLI, run:

```sh
just ci-approval-check  # read the live setting and fail if it differs
just ci-approval-apply  # apply the committed policy and verify it (repo admin)
```

These commands deliberately target `mfornet/safe-near`, even in a fork. The
policy file only takes effect when applied through GitHub's API; merging it
alone does not configure GitHub. No admin credential belongs in CI.

GitHub enforces this gate before it schedules a runner. An allowlist or `if:`
condition in a `pull_request` workflow cannot enforce it: a contributor can
modify that workflow in their PR. Keep PR workflows on `pull_request`; do not
switch to `pull_request_target` to check out and execute PR code, since that
event bypasses this approval policy.

Review the proposed code, workflow changes, dependencies and build hooks before
using **Approve and run**. Approval allows arbitrary PR code to execute on
the runner, with access to the runner user's persistent files and build caches.
Read-only `GITHUB_TOKEN` permissions do not isolate the host. Only approve code
you trust on this server; use an isolated disposable runner for untrusted code.

This is approval to run workflows, separate from approving a PR review or
merging it. Any repository user with write access can approve runs; repository
collaborators are exempt from the external-contributor gate. Keep repository
access restricted to people trusted to run code here. This setting does not
cancel runs already queued or executing.

References: [GitHub approval settings](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository#controlling-changes-from-forks-to-workflows-in-public-repositories),
[approval API](https://docs.github.com/en/rest/actions/permissions#set-fork-pr-contributor-approval-permissions-for-a-repository).

## Workspace and tool requirements

Runner workspaces retain ignored build outputs between jobs. Checkouts use
`clean: false`, followed by `git clean -ffd` to remove untracked sources and
`git clean -ffdX -- audit/` to discard evidence from earlier runs. Lake and
Cargo caches remain available for subsequent builds.

This persistence is part of the trust boundary: approved code can affect files
that a later job reuses. Use disposable isolated runners for untrusted code.
A build must refresh the outputs an audit reads; never audit stale artifacts.

The workflows expect native build dependencies, Python, Rust and Lean tooling.
Install required system packages through private runner administration. Each
runner needs its own toolchain and workspace directories to avoid concurrent
jobs modifying the same files. Scratch files belong in `$RUNNER_TEMP`.

GitHub's cache service is not used; the retained workspace is the build cache.
Cache cleanup and runner registration are private operational procedures.
