# CI runner

Workflows use self-hosted Linux x64 runners. Host-specific administration
instructions belong in private operator configuration. All external contributors
require approval in the repository's GitHub Actions settings before fork PR
workflows can run. Review code, dependencies and workflow changes before
approval: approved code can access persistent runner files and caches.

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
