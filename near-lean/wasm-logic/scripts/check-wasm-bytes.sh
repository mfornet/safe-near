#!/usr/bin/env bash
# Recompile the examples' .wat files with the pinned wasm-tools and check that
# the committed .wasm files and their Lean byte literals are up to date.
set -euo pipefail
cd "$(dirname "$0")/.."

pinned_tools="1.251.0"
version="$(wasm-tools --version 2>/dev/null || true)"
if [ "$version" != "wasm-tools $pinned_tools" ]; then
    echo "need wasm-tools $pinned_tools (cargo install wasm-tools@$pinned_tools); found: ${version:-none}" >&2
    exit 1
fi

status=0
check() {  # <dir> <base> <Lean namespace> <def name>
    local dir="$1" base="$2" ns="$3" def="$4"
    local tmp
    tmp="$(mktemp -d)"
    wasm-tools parse "$dir/$base.wat" -o "$tmp/$base.wasm"
    wasm-tools validate "$tmp/$base.wasm"
    python3 scripts/wasm-bytes.py "$tmp/$base.wasm" "$ns" "$def" > "$tmp/Bytes.lean"
    if ! cmp -s "$tmp/$base.wasm" "$dir/$base.wasm"; then
        echo "$dir/$base.wasm is out of date: run scripts/check-wasm-bytes.sh --write" >&2
        status=1
    fi
    if ! cmp -s "$tmp/Bytes.lean" "$dir/Bytes.lean"; then
        echo "$dir/Bytes.lean is out of date: run scripts/check-wasm-bytes.sh --write" >&2
        status=1
    fi
    if [ "${WRITE:-0}" = 1 ]; then
        cp "$tmp/$base.wasm" "$dir/$base.wasm"
        cp "$tmp/Bytes.lean" "$dir/Bytes.lean"
    fi
    rm -rf "$tmp"
}

if [ "${1:-}" = "--write" ]; then WRITE=1; fi
check WasmLogic/Examples/Stack stack WasmLogic.Examples.Stack stackBytes
check WasmLogic/Examples/Client client WasmLogic.Examples.Client clientBytes

if [ "${WRITE:-0}" = 1 ]; then exit 0; fi
exit "$status"
