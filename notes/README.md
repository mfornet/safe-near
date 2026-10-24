# Notes

Design notes describe how the project works today; [TODO](TODO.md) lists what
is left. Keep the two separate: when something is done, update the design note
and remove it from the TODO.

## Principles

- Components have clear boundaries so each can be audited or replaced on its own.
- The trusted base is always explicit: what must be trusted, and what we do to
  reduce it.

## Design

- [Project structure](design/PROJECT_STRUCTURE.md): repository layout.
- [Wasm runtime](design/WASM_RUNTIME.md): the Lean Wasm runtime.
- [NEAR runtime](design/NEAR_RUNTIME.md): VM, runtime and chain layers.
- [Smart contracts](design/SMART_CONTRACTS.md): the contracts dataset.
- [NEAR model](design/NEAR_MODEL.md): state views, access keys, upgrades.
- [Specifications](design/SPECIFICATIONS.md): how contract properties are written.
- [Proving](design/PROVING.md): blueprint, accepted axioms, audits.
- [Periodic checks](design/PERIODIC_CHECK.md): weekly consolidation review.

Check reports live in Linear (label `periodic-check`); the ledger of what
each section last covered is [reports/periodic/LEDGER.json](../reports/periodic/LEDGER.json).
