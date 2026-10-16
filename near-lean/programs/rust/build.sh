#!/usr/bin/env bash
# Build every workspace crate to Wasm and write, per crate,
#   build/<crate>/program.wasm   (stripped of all custom sections)
#   build/<crate>/program.wat    (wasm-tools print of that binary)
#
# This mirrors `verifier build` in Talos so the outputs are byte-identical to
# upstream: RUSTFLAGS remaps machine-specific path prefixes, and `strip --all`
# drops the `name` section whose mangled symbols embed cargo's per-unit hash.
# The .wat is what the Lean side (../lean/Programs/*/Program.lean) splices in
# at compile time and checks for fidelity, so a changed .wat requires
# regenerating those files.
#
# Requires: rustup (toolchain and wasm32 target are pinned in
# rust-toolchain.toml and installed on demand) and wasm-tools.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

command -v wasm-tools >/dev/null 2>&1 || {
    echo "error: wasm-tools not on PATH (cargo install wasm-tools)" >&2; exit 1; }

sysroot="$(rustc --print sysroot 2>/dev/null || true)"
cargo_home="${CARGO_HOME:-${HOME:-}/.cargo}"
remaps=()
[[ -n "${HOME:-}" ]] && remaps+=("--remap-path-prefix=$HOME=/home")
[[ -n "$cargo_home" ]] && remaps+=("--remap-path-prefix=$cargo_home=/cargo-home")
if [[ -n "$sysroot" ]]; then
    remaps+=("--remap-path-prefix=$sysroot=/rustc-sysroot")
    # With `rust-src` installed, rustc resolves core/std panic locations to
    # <sysroot>/lib/rustlib/src/rust/... instead of /rustc/<commit>/...; the
    # different prefix length shifts the data section. Map it back.
    hash="$(rustc -vV | awk '/^commit-hash: / {print $2}')"
    if [[ -n "$hash" && "$hash" != "unknown" ]]; then
        remaps+=("--remap-path-prefix=$sysroot/lib/rustlib/src/rust=/rustc/$hash")
    fi
fi

echo "==> cargo build-wasm (workspace)"
RUSTFLAGS="${remaps[*]}" cargo build-wasm

target="$ROOT/target/wasm32-unknown-unknown/release"
crates=$(awk '/^members = \[/{f=1; next} f && /^\]/{f=0} f {gsub(/[",]/, ""); print $1}' Cargo.toml)
for crate in $crates; do
    src="$target/$crate.wasm"
    [[ -f "$src" ]] || continue   # support crates (no cdylib) produce no .wasm
    out="$ROOT/build/$crate"
    mkdir -p "$out"
    wasm-tools strip --all -o "$out/program.wasm" "$src"
    wasm-tools print "$out/program.wasm" > "$out/program.wat"
    echo "    $crate: $(shasum -a 256 "$out/program.wat" | cut -c1-64)  build/$crate/program.wat"
done
