#!/usr/bin/env bash
# Sputnik DAO factory (sputnikdao-factory2)
# Rebuilds contract.wasm from source/ (pinned at 2b0f34a3860460f285307ec2ccf36345acbe05a2) into build/contract.wasm.
# Method: cargo-near-reproducible. Requirements: docker, cargo-near (https://github.com/near/cargo-near).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=2b0f34a3860460f285307ec2ccf36345acbe05a2
UPSTREAM=https://github.com/near-daos/sputnik-dao-contract
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/sputnik-dao-factory/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-sputnik-dao-factory.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
export PATH="$HOME/.cargo/bin:$PATH"
# cargo-near runs the build inside the docker image pinned in Cargo.toml
# ([package.metadata.near.reproducible_build]: sourcescan/cargo-near:0.19.0-rust-1.86.0@sha256:772638e343baeeea24e49062c7d424274f3441452cc06ce97fc4e5695b19fecc).
# Run from inside the clone: cargo-near discovers the git repository from the working directory.
(cd "$REPO/sputnikdao-factory2" && cargo near build reproducible-wasm)
cp "$REPO/target/near/sputnikdao_factory2/sputnikdao_factory2.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
