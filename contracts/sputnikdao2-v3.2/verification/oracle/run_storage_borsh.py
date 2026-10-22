#!/usr/bin/env python3
"""Run isolated storage-byte checks against the pinned Sputnik DAO source."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "source"
PIN = "2b0f34a3860460f285307ec2ccf36345acbe05a2"


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(SOURCE), *args], text=True).strip()


def main() -> None:
    if git("rev-parse", "HEAD") != PIN:
        raise SystemExit("Sputnik DAO source is not at the pinned commit")
    if git("status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Sputnik DAO source must be clean for the byte oracle")

    with tempfile.TemporaryDirectory(prefix="sputnik-borsh-") as temp:
        copied = Path(temp) / "source"
        shutil.copytree(SOURCE, copied, ignore=shutil.ignore_patterns(".git", "target"))
        manifest = copied / "sputnikdao2" / "Cargo.toml"
        original = 'near-sdk = { version = "5.24", features = ["global-contracts"] }'
        modified = (
            'near-sdk = { version = "5.24", '
            'features = ["global-contracts", "unit-testing"] }'
        )
        manifest_text = manifest.read_text()
        if manifest_text.count(original) != 1:
            raise SystemExit("pinned near-sdk dependency declaration changed")
        manifest.write_text(manifest_text.replace(original, modified))
        target = copied / "sputnikdao2" / "src" / "bounties.rs"
        with target.open("ab") as stream:
            stream.write((HERE / "bounty_borsh_test.rs").read_bytes())
        delegation = copied / "sputnikdao2" / "src" / "delegation.rs"
        with delegation.open("ab") as stream:
            stream.write((HERE / "delegation_borsh_test.rs").read_bytes())
        views = copied / "sputnikdao2" / "src" / "views.rs"
        with views.open("ab") as stream:
            stream.write((HERE / "views_test.rs").read_bytes())
        constructor = copied / "sputnikdao2" / "src" / "lib.rs"
        with constructor.open("ab") as stream:
            stream.write((HERE / "init_test.rs").read_bytes())
            stream.write((HERE / "migration_test.rs").read_bytes())
            stream.write((HERE / "config_policy_borsh_test.rs").read_bytes())
        proposals = copied / "sputnikdao2" / "src" / "proposals.rs"
        with proposals.open("ab") as stream:
            stream.write((HERE / "add_proposal_test.rs").read_bytes())
            stream.write((HERE / "multi_vote_test.rs").read_bytes())
            stream.write((HERE / "signal_vote_test.rs").read_bytes())
            stream.write((HERE / "execute_upgrade_test.rs").read_bytes())
            stream.write((HERE / "transfer_test.rs").read_bytes())
            stream.write((HERE / "function_call_test.rs").read_bytes())
            stream.write((HERE / "sync_governance_test.rs").read_bytes())
            stream.write((HERE / "add_bounty_execution_test.rs").read_bytes())
            stream.write((HERE / "bounty_payout_test.rs").read_bytes())
        environment = os.environ.copy()
        environment.setdefault(
            "CARGO_TARGET_DIR",
            str(Path(tempfile.gettempdir()) / "safe-near-sputnik-borsh-target"),
        )
        subprocess.run(
            ["cargo", "test", "--locked", "--offline", "-p", "sputnikdao2",
             "--lib", "projection_oracle", "--", "--nocapture", "--skip",
             "enabled_factory_info_update_authorizes_raw_update"],
            cwd=copied,
            env=environment,
            check=True,
        )
        # Raw `update()` installs a process-wide panic hook. Keep this
        # successful-path check out of the process that catches expected
        # panics in other source fixtures.
        subprocess.run(
            ["cargo", "test", "--locked", "--offline", "-p", "sputnikdao2",
             "--lib", "enabled_factory_info_update_authorizes_raw_update",
             "--", "--nocapture"],
            cwd=copied,
            env=environment,
            check=True,
        )


if __name__ == "__main__":
    main()
