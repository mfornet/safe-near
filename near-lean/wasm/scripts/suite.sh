#!/usr/bin/env bash
# The spec testsuite, in one place. Subcommands:
#   ensure    check out the vendor/testsuite submodule when it is empty
#   run ...   build the driver and run it (arguments go to `lake exe testsuite`)
#   report    regenerate testsuite_report.txt with the pinned wasm-tools, then summarise
#   summary   count outcomes in a report (default testsuite_report.txt) and list bugs
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
suite="${WASM_TESTSUITE:-$here/vendor/testsuite}"
pinned_tools="${WASM_TOOLS_VERSION:-1.251.0}"

ensure() {
    local any
    any=$(find "$suite" -maxdepth 1 -name '*.wast' -print -quit 2>/dev/null || true)
    if [ -z "$any" ]; then
        echo "initialising the testsuite submodule in $suite" >&2
        git -C "$here" submodule update --init -- "$suite"
    fi
}

run() {
    ensure
    (cd "$here" && lake build testsuite > /dev/null)
    exec "$here/.lake/build/bin/testsuite" "$@"
}

report() {
    local version
    version="$(wasm-tools --version 2>/dev/null || true)"
    if [ "$version" != "wasm-tools $pinned_tools" ]; then
        echo "need wasm-tools $pinned_tools (cargo install wasm-tools@$pinned_tools); found: ${version:-none}" >&2
        exit 1
    fi
    ensure
    (cd "$here" && lake build testsuite > /dev/null)
    "$here/.lake/build/bin/testsuite" --report > "$here/testsuite_report.txt"
    echo "wrote $here/testsuite_report.txt"
    summary "$here/testsuite_report.txt"
}

summary() {
    local file="${1:-$here/testsuite_report.txt}"
    echo "outcomes in $file:"
    cut -d' ' -f3 "$file" | sort | uniq -c | sort -rn
    echo
    echo "bugs (fail, decode_error, invalid_error), by file:"
    grep -E ' (fail|decode_error|invalid_error)$' "$file" | sed 's/:[0-9]* / /' | cut -d' ' -f1,3 \
        | sort | uniq -c | sort -k2 || true
}

case "${1:-}" in
    ensure) ensure ;;
    run) shift; run "$@" ;;
    report) report ;;
    summary) shift; summary "$@" ;;
    *) sed -n '2,6p' "$0" >&2; exit 2 ;;
esac
