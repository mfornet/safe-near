#!/usr/bin/env bash
# Rainbow Bridge Ethereum 2 light client
# Rebuilds contract.wasm from source/ (pinned at 9783ca494c2cea62512d7396274087b487af0805) into build/contract.wasm.
# Method: cargo-near-reproducible. Requirements: docker, cargo-near (https://github.com/near/cargo-near).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=9783ca494c2cea62512d7396274087b487af0805
UPSTREAM=https://github.com/Near-One/rainbow-bridge
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/eth2-client/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-eth2-client.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
export PATH="$HOME/.cargo/bin:$PATH"
# cargo-near runs the build inside the docker image pinned in Cargo.toml
# ([package.metadata.near.reproducible_build]: sourcescan/cargo-near:0.16.0-rust-1.86.0@sha256:3220302ebb7036c1942e772810f21edd9381edf9a339983da43487c77fbad488).
# Run from inside the clone: cargo-near discovers the git repository from the working directory.
(cd "$REPO/contracts/near/eth2-client" && cargo near build reproducible-wasm)
cp "$REPO/contracts/near/target/near/eth2_client/eth2_client.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
