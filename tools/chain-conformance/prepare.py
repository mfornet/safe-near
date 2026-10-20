#!/usr/bin/env python3
"""Build the full Runtime::apply oracle from the clean pinned nearcore source."""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = "runtime/runtime/Cargo.toml"
SHIM = "runtime/runtime/safe_near_apply_reference.rs"
TARGET = "safe-near-apply-reference"
FEATURES = "test_features,estimator,near-crypto/rand"
STANZA = f'''\n# Build-only adapter; the runtime implementation is unchanged.
[[bin]]
name = "{TARGET}"
path = "safe_near_apply_reference.rs"
required-features = ["test_features", "estimator"]
'''.encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(source: Path, *arguments: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(source), *arguments])


def verify_source(source: Path, revision: str, manifest: bytes | None = None,
                  shim: bytes | None = None) -> None:
    if git(source, "rev-parse", "HEAD").decode().strip() != revision:
        raise ValueError("nearcore checkout does not match the pinned revision")
    changed = set(git(source, "diff", "--name-only", "-z", "HEAD").decode().strip("\0").split("\0")) - {""}
    untracked = set(git(source, "ls-files", "--others", "--exclude-standard", "-z").decode().strip("\0").split("\0")) - {""}
    if manifest is None:
        if changed or untracked:
            raise ValueError("nearcore source has unrecognized tracked or untracked changes")
    else:
        if changed != {MANIFEST} or untracked != {SHIM}:
            raise ValueError("nearcore build overlay contains unexpected source changes")
        if (source / MANIFEST).read_bytes() != manifest or (source / SHIM).read_bytes() != shim:
            raise ValueError("nearcore build overlay changed during compilation")


def recover_overlay(source: Path, revision: str, original: bytes) -> None:
    """Recover only our exact interrupted overlay, while holding its kernel lock."""
    marker = source / ".git/safe-near-apply-overlay.json"
    if not marker.exists():
        return
    ownership = json.loads(marker.read_text())
    if ownership.get("revision") != revision or ownership.get("manifestBefore") != digest(original):
        raise ValueError("unrecognized nearcore overlay ownership record")
    manifest, shim = source / MANIFEST, source / SHIM
    if manifest.read_bytes() == original and not shim.exists():
        marker.unlink()
        return
    if manifest.read_bytes() != original + STANZA or not shim.is_file():
        raise ValueError("interrupted nearcore overlay was modified; preserving it")
    if digest(shim.read_bytes()) != ownership.get("shimSha256"):
        raise ValueError("interrupted oracle adapter was modified; preserving it")
    manifest.write_bytes(original)
    shim.unlink()
    marker.unlink()


def clone_source(destination: Path, repository: str, revision: str) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="nearcore-fetch-", dir=destination.parent) as temporary:
        checkout = Path(temporary) / "source"
        subprocess.run(["git", "init", "--quiet", str(checkout)], check=True)
        subprocess.run(["git", "-C", str(checkout), "fetch", "--depth=1", repository, revision], check=True)
        subprocess.run(["git", "-C", str(checkout), "checkout", "--quiet", "--detach", "FETCH_HEAD"], check=True)
        checkout.rename(destination)


def atomic_write(path: Path, data: bytes, mode: int | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(prefix=f".{path.name}-", dir=path.parent, delete=False) as temporary:
        staged = Path(temporary.name)
        temporary.write(data)
    try:
        if mode is not None:
            staged.chmod(mode)
        staged.replace(path)
    finally:
        staged.unlink(missing_ok=True)


def publish_binary(binary: Path, output: Path) -> str:
    """Freeze large native executables without reading them all into memory."""
    output.parent.mkdir(parents=True, exist_ok=True)
    checksum = hashlib.sha256()
    with tempfile.NamedTemporaryFile(prefix=f".{output.name}-", dir=output.parent, delete=False) as temporary:
        staged = Path(temporary.name)
        with binary.open("rb") as original:
            shutil.copyfileobj(original, temporary, length=1024 * 1024)
    try:
        with staged.open("rb") as frozen:
            for chunk in iter(lambda: frozen.read(1024 * 1024), b""):
                checksum.update(chunk)
        staged.chmod(0o755)
        staged.replace(output)
        return checksum.hexdigest()
    finally:
        staged.unlink(missing_ok=True)


def build(source: Path, revision: str, output: Path, check_only: bool = False) -> dict:
    if output == source or source in output.parents:
        raise ValueError("binary output must be outside the pinned source checkout")
    with (source / ".git/safe-near-apply.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if git(source, "rev-parse", "HEAD").decode().strip() != revision:
            raise ValueError("nearcore checkout does not match the pinned revision")
        original = git(source, "show", f"{revision}:{MANIFEST}")
        recover_overlay(source, revision, original)
        verify_source(source, revision)
        toolchain = (source / "rust-toolchain.toml").read_text()
        match = re.search(r'^channel\s*=\s*"(\d+\.\d+\.\d+)"', toolchain, re.MULTILINE)
        if not match:
            raise ValueError("nearcore must pin a stable Rust toolchain")
        channel = match.group(1)
        shim = (HERE / "reference.rs").read_bytes()
        manifest = original + STANZA
        cargo_lock = (source / "Cargo.lock").read_bytes()
        marker = source / ".git/safe-near-apply-overlay.json"
        marker.write_text(json.dumps({"revision": revision, "manifestBefore": digest(original), "shimSha256": digest(shim)}))
        environment = os.environ.copy()
        environment["CARGO_BUILD_JOBS"] = environment.get("CARGO_BUILD_JOBS", "2")
        environment["CARGO_TARGET_DIR"] = str(source / "target")
        environment["SAFE_NEAR_REFERENCE_REVISION"] = revision
        environment["SAFE_NEAR_ADAPTER_SHA256"] = digest(shim)
        try:
            (source / MANIFEST).write_bytes(manifest)
            (source / SHIM).write_bytes(shim)
            subprocess.run(["cargo", f"+{channel}", "check" if check_only else "build", "--locked",
                            "-p", "node-runtime", "--bin", TARGET, "--features", FEATURES],
                           cwd=source, env=environment, check=True)
            verify_source(source, revision, manifest, shim)
            if (source / "Cargo.lock").read_bytes() != cargo_lock:
                raise ValueError("nearcore Cargo.lock changed during compilation")
            evidence = {
                "sourceRevision": revision, "sourceImplementationClean": True,
                "features": FEATURES.split(","), "rustToolchain": channel,
                "rustc": subprocess.check_output(["rustc", f"+{channel}", "--version"], cwd=source, text=True).strip(),
                "cargoLockSha256": digest(cargo_lock), "manifestOverlaySha256": digest(manifest),
                "shimSha256": digest(shim), "checkOnly": check_only,
                "cargoProfileDevDebug": environment.get("CARGO_PROFILE_DEV_DEBUG"),
            }
            if not check_only:
                binary = source / "target/debug" / TARGET
                runtime = json.loads(subprocess.check_output([str(binary), "--metadata"], text=True))
                if runtime.get("sourceRevision") != revision or runtime.get("adapterSha256") != digest(shim):
                    raise ValueError("compiled runtime adapter does not match its source")
                evidence["runtime"] = runtime
                evidence["binarySha256"] = publish_binary(binary, output)
                metadata = output.with_name(output.name + ".build.json")
                atomic_write(metadata, (json.dumps(evidence, indent=2) + "\n").encode())
            return evidence
        finally:
            if (source / MANIFEST).read_bytes() == manifest:
                (source / MANIFEST).write_bytes(original)
            if (source / SHIM).exists() and (source / SHIM).read_bytes() == shim:
                (source / SHIM).unlink()
            if (source / MANIFEST).read_bytes() == original and not (source / SHIM).exists():
                marker.unlink(missing_ok=True)


def main() -> None:
    pin = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())
    revision = pin["revision"]
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("invalid nearcore source revision")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="reuse a clean checkout at the exact source pin")
    parser.add_argument("--output", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--check", action="store_true", help="type-check the adapter without publishing a binary")
    arguments = parser.parse_args()
    source = (arguments.source or HERE / ".nearcore" / revision).resolve()
    if not source.exists():
        if arguments.source:
            raise ValueError("the requested nearcore source checkout does not exist")
        clone_source(source, pin["repository"], revision)
    evidence = build(source, revision, arguments.output.resolve(), arguments.check)
    print(json.dumps(evidence, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"runtime oracle build failed: {error}", file=sys.stderr)
        raise SystemExit(1)
