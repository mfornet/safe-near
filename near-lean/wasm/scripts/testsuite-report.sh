#!/usr/bin/env bash
# Regenerate testsuite_report.txt (one sorted line per spec-testsuite command
# with its outcome). CI runs the same command and fails if the committed
# report drifts, so changes that shift coverage must commit the new report.
#
# The report is pinned to one exact wasm-tools version because different
# releases can produce different .wast decodes. Bumping the pin here and
# regenerating the report belong in the same commit.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
required_version="${WASM_TOOLS_VERSION:-1.251.0}"

if ! command -v wasm-tools >/dev/null 2>&1; then
    echo "error: wasm-tools not on PATH (need exactly $required_version)" >&2
    echo "       install: 'cargo install wasm-tools@$required_version'" >&2
    exit 1
fi
got=$(wasm-tools --version | awk 'NR==1 {print $2}')
if [[ "$got" != "$required_version" ]]; then
    echo "error: wasm-tools $required_version required, found $got" >&2
    echo "       the committed testsuite_report.txt is pinned to that version" >&2
    exit 1
fi

"$ROOT/scripts/ensure-testsuite.sh"

cd "$ROOT"
lake exe testsuite --report > "$ROOT/testsuite_report.txt"
echo "wrote $ROOT/testsuite_report.txt"
"$ROOT/scripts/testsuite-summary.sh" "$ROOT/testsuite_report.txt"
