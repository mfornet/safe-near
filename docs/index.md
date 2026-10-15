# Safe NEAR

Formal verification of NEAR smart contracts in Lean.

The project is split into components with clear boundaries so that each one
can be audited or replaced on its own, and so that the trusted base is explicit
at every step. The plan and the reasoning behind it are in the
[human-written notes](human/SAFE_NEAR.md).

## How this documentation is organised

| Section | Who writes it | Source |
|---|---|---|
| [Human notes](human/SAFE_NEAR.md) | People only. AI agents are forbidden from editing anything there. | `docs/human/` |
| [Contracts dataset](contracts/index.md) | Mostly generated with AI, reviewed by people. | `contracts/README.md`, `contracts/CATALOG.md`, `contracts/<name>/README.md` |
| Everything else | Mixed. | `docs/` |

The separation is deliberate: the human section records intent and decisions,
the rest records what was built. See the [policy](human/AGENTS.md) for the
human section.

## Components

- **WASM runtime**: a Lean interpreter for WebAssembly, generic over the host.
- **NEAR runtime**: the host functions, state, receipts and gas model needed to
  replay NEAR history bit for bit.
- **Contracts dataset**: one folder per on-chain binary with the pinned source
  and a reproducible build. See the [catalog](contracts/catalog.md).
- **Specifications and proofs**: one Lean project per contract, with statements
  kept separate from proofs so they are easy to audit.

## Working with the docs

```sh
uv run mkdocs serve          # live preview at http://127.0.0.1:8000
uv run mkdocs build --strict # static site in site/, fails on broken links
```

Pages under *Contracts dataset* are generated from the files in `contracts/`
at build time, so edit those files rather than anything under `docs/`.
