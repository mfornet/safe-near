#!/usr/bin/env python3
"""The campaign driver (tools/campaign/driver.py): `run`, `status`, `results`, `auth`, `new`, `merge`."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from campaign.driver import main  # noqa: E402

if __name__ == "__main__":
    raise SystemExit(main())
