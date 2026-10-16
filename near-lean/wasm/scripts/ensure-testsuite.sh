#!/usr/bin/env bash
# Make sure the WebAssembly spec testsuite submodule (vendor/testsuite/) is
# checked out. It is pinned as a git submodule, so a fresh clone has an empty
# directory until it is initialised.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if ! compgen -G "$ROOT/vendor/testsuite/*.wast" >/dev/null; then
    echo "vendor/testsuite is empty; initialising the submodule..." >&2
    git -C "$ROOT" submodule update --init -- "$ROOT/vendor/testsuite"
fi
