#!/usr/bin/env python3
"""Check or apply the repository's fork PR workflow approval policy via gh."""

import argparse
import json
from pathlib import Path
import subprocess
import sys


POLICY = Path(__file__).resolve().parents[1] / ".github/actions-approval-policy.json"
# Deliberately target the upstream repository, even when run from a fork.
ENDPOINT = "repos/mfornet/safe-near/actions/permissions/fork-pr-contributor-approval"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true", help="apply the policy before checking")
    args = parser.parse_args()
    expected = json.loads(POLICY.read_text())
    if expected != {"approval_policy": "all_external_contributors"}:
        raise ValueError("Policy must require approval for all external contributors")

    if args.apply:
        subprocess.run(
            ["gh", "api", "--method", "PUT", ENDPOINT, "--input", str(POLICY)],
            check=True,
        )
    result = subprocess.run(
        ["gh", "api", "-H", "Cache-Control: no-cache", ENDPOINT],
        check=True, capture_output=True, text=True,
    )
    actual = json.loads(result.stdout)
    if actual.get("approval_policy") != expected["approval_policy"]:
        print(
            f"Approval policy mismatch: expected {expected['approval_policy']}, "
            f"got {actual.get('approval_policy')!r}. "
            "Run `just ci-approval-apply` as a repository admin.",
            file=sys.stderr,
        )
        return 1
    print("Verified: all external contributors require approval to run fork PR workflows.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Unable to verify Actions approval policy: {error}", file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr, file=sys.stderr, end="")
        sys.exit(1)
