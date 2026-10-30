# CI runner

The GitHub Actions workflows in `.github/workflows` run on our own server,
`fv01` (Hetzner, Ubuntu 24.04, 16 cores, 64 GB), registered as self-hosted
runners of `mfornet/safe-near`. Every job uses `runs-on: [self-hosted, fv01]`;
no job runs on GitHub-hosted machines.

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
`fv01`, with access to the runner user's persistent files and build caches.
Read-only `GITHUB_TOKEN` permissions do not isolate the host. Only approve code
you trust on this server; use an isolated disposable runner for untrusted code.

This is approval to run workflows, separate from approving a PR review or
merging it. Any repository user with write access can approve runs; repository
collaborators are exempt from the external-contributor gate. Keep repository
access restricted to people trusted to run code here. This setting does not
cancel runs already queued or executing.

References: [GitHub approval settings](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository#controlling-changes-from-forks-to-workflows-in-public-repositories),
[approval API](https://docs.github.com/en/rest/actions/permissions#set-fork-pr-contributor-approval-permissions-for-a-repository).

## Layout

- Three runners, `fv01-1`, `fv01-2`, `fv01-3`, so the workflows a pull request
  triggers run at the same time.
- Each runner has its own unprivileged user (`gha1`, `gha2`, `gha3`, no sudo)
  with the runner in `~/runner`. Separate homes matter: `lean-action`
  reinstalls elan into `$HOME` on every job, and runners sharing a home would
  race on it. Each user keeps its own elan toolchains, Mathlib cache, cargo
  registry and job workspaces (`~/runner/_work`) between jobs.
- Each runner is a systemd service,
  `actions.runner.mfornet-safe-near.fv01-<i>.service`.
- Jobs write scratch files to `$RUNNER_TEMP`, not fixed `/tmp` paths: the
  runner users cannot overwrite each other's files.

## System packages

Jobs cannot `sudo`, so what they need from apt is installed on the host:

```bash
sudo apt-get install -y build-essential clang libclang-dev cmake protobuf-compiler \
  libssl-dev pkg-config libzstd-dev zstd python3 python3-venv curl git jq unzip libicu74
```

A workflow that needs another system package needs it installed here first.

## Adding or replacing a runner

As an admin of the repository, with `gh` logged in, for runner `<i>`:

```bash
TOKEN=$(gh api -X POST repos/mfornet/safe-near/actions/runners/registration-token --jq .token)
```

then on `fv01`, with the runner tarball from
<https://github.com/actions/runner/releases> unpacked into `/home/gha<i>/runner`:

```bash
sudo useradd -m -s /bin/bash gha<i>
sudo -u gha<i> bash -c 'cd ~/runner && ./config.sh --unattended --replace \
  --url https://github.com/mfornet/safe-near --token <TOKEN> --name fv01-<i> --labels fv01 --work _work'
sudo bash -c 'cd /home/gha<i>/runner && ./svc.sh install gha<i> && ./svc.sh start'
```

The runner updates itself when GitHub releases a new version.

## Caching: the workspace is the cache

Every job checks out with `clean: false` and then runs `git clean -ffd`: files
a previous job left untracked are removed, but ignored ones stay. Jobs also
run `git clean -ffdX -- audit/` to discard previous evidence: even when a build
fails before producing a report, artifact uploads must not reuse an old report.
The retained caches are the Lake builds and packages (`.lake/`, Mathlib and
iris included), the formatter build (`near-lean/.lake/lean-fmt`), Rust `target/` directories and the pinned
nearcore checkouts. All workflows of the repository share one workspace per
runner, so whichever job built something last leaves it warm for the next.

Nothing goes through GitHub's cache service (`actions/cache`, lean-action's
`use-github-cache`): it holds at most 10 GB per repository, evicted older
entries before they were reused, did not share pull request caches with
`main`, and moved gigabytes per job that were already on this disk. Do not add
it back.

Since a module's build output can outlive the commit that built it, the axiom
audits build what they read (no `--no-build`): with a warm workspace that costs
seconds, and a stale `.olean` is never audited.

## Disk

Workspaces and caches persist, so disk use grows. If it fills, stop the
services and delete `/home/gha*/runner/_work`, `/home/gha*/.cache` and
Lake's artifact cache `/home/gha*/.elan/toolchains/*/lake/cache`; the next
jobs start cold.
