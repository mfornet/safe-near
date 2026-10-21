# Specifications

Proven specifications are the evidence that a contract is correct, so they must
be easy for a person to read and audit, and so must every definition they use.

## Layout

```text
contracts/<name>/verification/
    Model/       -- Contract state and methods as Lean definitions
    Spec/        -- Properties, each a `def ... : Prop`
    Proofs/      -- Theorems proving them
    blueprint/   -- Prose explanations linked to statements and proofs
```

Only wNEAR has a verification project so far.

## Shared vocabulary

Common definitions (JSON, near-sdk data structures, runtime concepts) should
live in a shared library. It is part of the trusted base, so it should grow
slowly and always have an up-to-date audit.

The format will be refined as more contracts are verified. Keep statements
self-contained and model assumptions explicit.
