# Safe NEAR

Formally verify NEAR smart contracts.

Check [human written notes](docs/human/SAFE_NEAR.md).

## Documentation

All documentation lives in `docs/` and is published as a static site with
[MkDocs](https://www.mkdocs.org/) (Material theme). `docs/human/` is written by
humans only; see [docs/human/AGENTS.md](docs/human/AGENTS.md).

```
uv run mkdocs serve            # preview at http://127.0.0.1:8000
uv run mkdocs build --strict   # static site in site/
```

The contracts pages of the site are generated from `contracts/` at build time
(`tools/mkdocs_hooks.py`), so there is a single source of truth.

## Contracts dataset

`contracts/` holds one folder per on-chain binary: the binary, its NEAR code
hash, a reproducible `build.sh`, and the upstream source pinned as a git
submodule. See [contracts/README.md](contracts/README.md) for the format and
[contracts/CATALOG.md](contracts/CATALOG.md) for the list of contracts.

```
git submodule update --init contracts/<name>/source   # fetch the pinned source
tools/verify_build.sh contracts/<name>              # rebuild and compare hashes
```
