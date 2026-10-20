#!/usr/bin/env python3
"""Build a visibility-only adapter against the clean, pinned nearcore checkout."""
import argparse
import fcntl
import tempfile
import hashlib
import json
from pathlib import Path
import subprocess

PIN = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
p = argparse.ArgumentParser()
p.add_argument("checkout", type=Path)
a = p.parse_args()
checkout = a.checkout.resolve()
# Both adapters mutate this checkout briefly; serialize their overlays.
lock_path = Path(tempfile.gettempdir()) / ("safe-near-reference-" + hashlib.sha256(str(checkout).encode()).hexdigest() + ".lock")
checkout_lock = lock_path.open("a")
fcntl.flock(checkout_lock, fcntl.LOCK_EX)
assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip() == PIN
assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=checkout)
root = Path(__file__).resolve().parent
lib = checkout / "runtime/runtime/src/lib.rs"
manifest = checkout / "runtime/runtime/Cargo.toml"
original_lib, original_manifest = lib.read_bytes(), manifest.read_bytes()
try:
    lib.write_bytes(original_lib + f'\n#[path = "{root / "adapter.rs"}"]\npub mod safe_near_finance_reference;\n'.encode())
    manifest.write_bytes(original_manifest + f'\n[[bin]]\nname = "safe-near-finance-reference"\npath = "{root / "main.rs"}"\n'.encode())
    subprocess.run(["cargo", "build", "--locked", "-p", "node-runtime", "--bin", "safe-near-finance-reference",
                    "--features", "test_features,estimator,near-crypto/rand"], cwd=checkout, check=True)
finally:
    lib.write_bytes(original_lib)
    manifest.write_bytes(original_manifest)
binary = checkout / "target/debug/safe-near-finance-reference"
assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=checkout)
metadata = {
    "sourceRevision": PIN, "sourceImplementationClean": True,
    "adapterSha256": hashlib.sha256((root / "adapter.rs").read_bytes()).hexdigest(),
    "driverSha256": hashlib.sha256((root / "main.rs").read_bytes()).hexdigest(),
    "binarySha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
    "cargoLockSha256": hashlib.sha256((checkout / "Cargo.lock").read_bytes()).hexdigest(),
    "rustc": subprocess.check_output(["rustc", "--version"], cwd=checkout, text=True).strip(),
    "features": ["test_features", "estimator", "near-crypto/rand"],
}
report = root.parents[1] / "audit/finance-reference-build.json"
report.parent.mkdir(parents=True, exist_ok=True)
report.write_text(json.dumps(metadata, indent=2) + "\n")
print(binary)
