# Safe NEAR

This project formally verifies NEAR smart contracts using Lean.

Development uses AI alongside contributors. Components have clear
responsibilities and boundaries so each can be audited or replaced
independently.

The previous point is also linked to the idea of maintaining clarity
about the trusted base at every point, which pieces of code needed to be
trusted, and what are the current and future efforts to make sure we
can actually trust them.

The component notes describe current implementation and remaining goals:

- [Project structure](PROJECT_STRUCTURE.md)
- [NEAR model and specifications](NEAR_MODEL.md)
- [WASM Runtime](WASM_RUNTIME.md)
- [NEAR Runtime](NEAR_RUNTIME.md)
- [Smart Contracts](SMART_CONTRACTS.md)
- [Specifications](SPECIFICATIONS.md)
- [Proving](PROVING.md)

## Future work

Theorems that span multiple contracts simultaneously (do we really need this?)
