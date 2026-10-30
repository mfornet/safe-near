"""Stable digest of owned Lean sources and their build configuration."""
import hashlib
from pathlib import Path
import subprocess


def source_digest(root: Path) -> str:
    paths = subprocess.check_output([
        'git', '-C', str(root), 'ls-files', '-z', '--cached', '--others', '--exclude-standard',
        '--', '*.lean', '*lakefile.toml', '*lakefile.lean', '*lean-toolchain', '*lake-manifest.json',
        'tools/axiom-audit.py', 'tools/proof_sources.py', 'tools/wnear_blueprint.py',
        'tools/wnear_pipeline.py', 'tools/wnear_validate.py', 'justfile',
        'contracts/w-near/verification/statements.json',
        'contracts/w-near/verification/blueprint/frontier.json',
        'contracts/w-near/contract.wasm', 'near-lean/vm/configs/runtime_config_v86.json',
    ]).decode().split('\0')
    result = hashlib.sha256()
    for name in sorted(set(paths) - {''}):
        path = root / name
        if path.is_file():
            result.update(name.encode() + b'\0' + path.read_bytes() + b'\0')
    return result.hexdigest()
