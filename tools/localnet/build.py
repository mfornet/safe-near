#!/usr/bin/env python3
"""Build `neard` and the corpus exporter from the clean pinned nearcore source.

The exporter (`exporter.rs`) is overlaid onto the `neard` package as a second
binary, so it links exactly the pinned `near-store`/`near-chain`/`nearcore`
crates and shares every compiled dependency with `neard`.  The implementation
sources are untouched; only `neard/Cargo.toml` gains one `[[bin]]` stanza while
cargo runs, and it is restored afterwards.
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "tools/chain-conformance"))
import prepare  # noqa: E402  (reuse the download/hash/publish helpers)

# (package, manifest, shim path, source file here, binary name)
OVERLAYS = [
    ("state-viewer", "tools/state-viewer/Cargo.toml", "tools/state-viewer/safe_near_corpus_export.rs",
     "exporter.rs", "safe-near-corpus-export"),
    ("node-runtime", "runtime/runtime/Cargo.toml", "runtime/runtime/safe_near_corpus_check.rs",
     "checker.rs", "safe-near-corpus-check"),
]


def stanza(shim: str, name: str) -> bytes:
    return f'''\n# Build-only adapter; the implementation is unchanged.
[[bin]]
name = "{name}"
path = "{Path(shim).name}"
'''.encode()

# The pinned `release` profile uses fat LTO with one codegen unit, which needs
# more RAM and time than the 4-core/15 GB budget allows and cannot share
# compiled dependencies between binaries.  Execution semantics do not depend on
# these knobs; they are recorded in the build metadata.
PROFILE = {
    "CARGO_PROFILE_RELEASE_LTO": "off",
    "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "16",
    "CARGO_PROFILE_RELEASE_DEBUG": "0",
    "CARGO_PROFILE_RELEASE_INCREMENTAL": "false",
}


def neard_environment(outdir: Path) -> dict:
    """neard insists on a 65535 hard descriptor limit; sandboxes that cap it use the preload shim."""
    import resource
    environment = dict(os.environ)
    if resource.getrlimit(resource.RLIMIT_NOFILE)[1] < 65535:
        environment["LD_PRELOAD"] = str(outdir / "sandbox_shim.so")
    return environment


CONTRACTS = ["test_contract_rs", "estimator_contract", "sharded_contract"]


def publish_contracts(source: Path, destination: Path) -> dict:
    """Freeze the contracts that nearcore's own build produced (test_contract_rs and friends)."""
    outputs = sorted((HERE / "target/release/build").glob("near-test-contracts-*/out/test_contract_rs.wasm"))
    if len(outputs) != 1:
        raise ValueError("expected exactly one built near-test-contracts output")
    destination.mkdir(parents=True, exist_ok=True)
    published = {}
    for name in CONTRACTS:
        shutil.copyfile(outputs[0].parent / f"{name}.wasm", destination / f"{name}.wasm")
    shutil.copyfile(source / "runtime/near-test-contracts/res/fungible_token.wasm", destination / "fungible_token.wasm")
    for path in sorted(destination.glob("*.wasm")):
        published[path.name] = prepare.digest(path.read_bytes())
    return published


def build(source: Path, revision: str, outdir: Path, with_adapters: bool, jobs: str) -> dict:
    with (source / ".git/safe-near-localnet.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if prepare.git(source, "rev-parse", "HEAD").decode().strip() != revision:
            raise ValueError("nearcore checkout does not match the pinned revision")
        originals = {m: prepare.git(source, "show", f"{revision}:{m}") for _, m, _, _, _ in OVERLAYS}
        # restore a previously interrupted overlay
        for _, manifest, shim, _, name in OVERLAYS:
            if (source / manifest).read_bytes() == originals[manifest] + stanza(shim, name):
                (source / manifest).write_bytes(originals[manifest])
            (source / shim).unlink(missing_ok=True)
        changed = prepare.git(source, "status", "--porcelain").decode().strip()
        if changed:
            raise ValueError(f"nearcore source is not clean:\n{changed}")
        channel = re.search(r'^channel\s*=\s*"(\d+\.\d+\.\d+)"',
                            (source / "rust-toolchain.toml").read_text(), re.MULTILINE).group(1)
        cargo_lock = (source / "Cargo.lock").read_bytes()
        env = os.environ.copy()
        env.update(PROFILE)
        env["CARGO_BUILD_JOBS"] = jobs
        env["CARGO_TARGET_DIR"] = str(HERE / "target")
        env["SAFE_NEAR_REFERENCE_REVISION"] = revision
        def cargo_build(packages):
            command = ["cargo", f"+{channel}", "build", "--release", "--locked"]
            for package, binary in packages:
                command += ["-p", package, "--bin", binary]
            subprocess.run(command, cwd=source, env=env, check=True)

        # Phase 1 builds neard from the untouched tree, so its version string says "clean".
        cargo_build([("neard", "neard")])
        neard_path = outdir / "neard"
        prepare.publish_binary(HERE / "target/release/neard", neard_path)
        packages = [("neard", "neard")]
        adapters = {}
        if with_adapters:
            adapter_packages = []
            try:
                for package, manifest, shim, local, name in OVERLAYS:
                    body = (HERE / local).read_bytes()
                    adapters[name] = prepare.digest(body)
                    (source / manifest).write_bytes(originals[manifest] + stanza(shim, name))
                    (source / shim).write_bytes(body)
                    adapter_packages.append((package, name))
                cargo_build(adapter_packages)
            finally:
                for _, manifest, shim, _, _ in OVERLAYS:
                    (source / manifest).write_bytes(originals[manifest])
                    (source / shim).unlink(missing_ok=True)
            packages += adapter_packages
        if (source / "Cargo.lock").read_bytes() != cargo_lock:
            raise ValueError("nearcore Cargo.lock changed during compilation")
        evidence = {
            "sourceRevision": revision, "sourceImplementationClean": True,
            "profile": "release", "profileOverrides": PROFILE,
            "rustToolchain": channel,
            "rustc": subprocess.check_output(["rustc", f"+{channel}", "--version"], cwd=source, text=True).strip(),
            "cargoLockSha256": prepare.digest(cargo_lock),
            "adapterSha256": adapters,
            "binaries": {},
        }
        for _, binary in packages:
            evidence["binaries"][binary] = prepare.publish_binary(HERE / "target/release" / binary, outdir / binary)
        if (source / "Cargo.lock").read_bytes() != cargo_lock or prepare.git(source, "status", "--porcelain").strip():
            raise ValueError("nearcore checkout changed during the build")
        contracts = outdir / "contracts"
        evidence["contracts"] = publish_contracts(source, contracts)
        shim = outdir / "sandbox_shim.so"
        subprocess.run(["gcc", "-shared", "-fPIC", "-O2", "-o", str(shim), str(HERE / "sandbox_shim.c"), "-ldl"], check=True)
        evidence["neardVersion"] = subprocess.check_output([str(outdir / "neard"), "--version"], text=True,
                                                           env=neard_environment(outdir)).strip()
        evidence["sandboxShimSha256"] = prepare.digest((HERE / "sandbox_shim.c").read_bytes())
        prepare.atomic_write(outdir / "build.json", (json.dumps(evidence, indent=2) + "\n").encode())
        return evidence


def main() -> None:
    pin = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())
    revision = pin["revision"]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="reuse a clean checkout at the exact pin")
    parser.add_argument("--outdir", type=Path, default=HERE / "target/bin")
    parser.add_argument("--neard-only", action="store_true", help="skip the exporter and checker overlays")
    parser.add_argument("--jobs", default="4")
    a = parser.parse_args()
    source = (a.source or HERE / ".nearcore" / revision).resolve()
    if not source.exists():
        prepare.clone_source(source, pin["repository"], revision)
    print(json.dumps(build(source, revision, a.outdir.resolve(), not a.neard_only, a.jobs), indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"neard build failed: {error}", file=sys.stderr)
        raise SystemExit(1)
