"""MkDocs hooks for the Safe NEAR documentation site.

1. Publishes the contracts dataset documentation (contracts/README.md,
   contracts/CATALOG.md and every contracts/<name>/README.md) as pages of the
   site, so those files stay the single source of truth and are not copied
   into docs/.
2. Marks every page under docs/human/ with a "written by humans" banner at
   render time. The files themselves are never touched.
"""

import re
from pathlib import Path

from mkdocs.structure.files import File

ROOT = Path(__file__).resolve().parents[1]
CONTRACTS = ROOT / "contracts"

# `[w-near](w-near/)` in CATALOG.md points at a folder on GitHub; in the site
# that folder is rendered as contracts/<name>/index.md.
FOLDER_LINK = re.compile(r"\]\(([A-Za-z0-9._-]+)/\)")

HUMAN_BANNER = (
    '!!! info "Written by humans"\n'
    "    This page lives in `docs/human/` and is maintained by people only. "
    "AI agents must not edit it.\n\n"
)


def _entries():
    """Contract folders that have a README, sorted by name."""
    return sorted(p.parent.name for p in CONTRACTS.glob("*/README.md"))


def _title(path, fallback):
    for line in path.read_text().splitlines():
        if line.startswith("# "):
            return line[2:].strip()
    return fallback


def on_config(config):
    entries = [
        {_title(CONTRACTS / name / "README.md", name): f"contracts/{name}/index.md"}
        for name in _entries()
    ]
    config.nav.append(
        {
            "Contracts dataset": [
                {"Overview": "contracts/index.md"},
                {"Catalog": "contracts/catalog.md"},
                {"Entries": entries},
            ]
        }
    )
    return config


def on_files(files, config):
    def add(src_uri, text):
        files.append(File.generated(config, src_uri, content=text))

    add("contracts/index.md", (CONTRACTS / "README.md").read_text())
    catalog = (CONTRACTS / "CATALOG.md").read_text()
    add("contracts/catalog.md", FOLDER_LINK.sub(r"](\1/index.md)", catalog))
    for name in _entries():
        add(f"contracts/{name}/index.md", (CONTRACTS / name / "README.md").read_text())
    return files


def on_page_markdown(markdown, page, config, files):
    if not page.file.src_uri.startswith("human/"):
        return markdown
    lines = markdown.split("\n", 1)
    if lines[0].startswith("# ") and len(lines) == 2:
        return f"{lines[0]}\n\n{HUMAN_BANNER}{lines[1]}"
    return HUMAN_BANNER + markdown
