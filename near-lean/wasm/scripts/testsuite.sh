#!/usr/bin/env bash
# Run the WebAssembly spec testsuite (vendor/testsuite/) against the interpreter.
# Optional first argument is a case-sensitive substring on the .wast filename
# stem; empty/missing runs the whole suite. Any flag understood by
# `lake exe testsuite` (e.g. --fuel N, --json) is passed through.
#
# Exit code is the testsuite's own: 1 if any command failed, errored or ran out
# of fuel; 0 when everything passed or was merely skipped (unimplemented).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
"$ROOT/scripts/ensure-testsuite.sh"

cd "$ROOT"
lake exe testsuite "$@"
