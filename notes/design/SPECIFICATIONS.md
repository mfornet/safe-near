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

wNEAR is complete at the model level; `sputnik-dao-factory` and
`sputnikdao2-v3.2` are in progress (see `contracts/VERIFICATION.md`).

## Shared vocabulary

Common definitions live in `near-lean/interface` (`NearInterface`): the raw
values of a function call (bytes, storage, receipts, return data, promise
results), the protocol configuration, JSON as serde_json accepts and writes
it, and the refinement statement. It is part of the trusted base: it should
grow slowly, stay definitions-only (no interpreter, so `Spec/` libraries can
import it cheaply), and always have an up-to-date audit.

## Refinement

There is one refinement statement for every contract,
`NearInterface.Refines R protocol code M` (design: `notes/todo/refinement_equivalence.md`).
A contract provides a `ContractModel`: its state encoding and invariant,
`Parses` (which inputs are calls), a `step` from the boundary `Context`, exact
encodings of return values, receipts and failures, and a gas bound. The
runtime provides a `RuntimeInterface`; near-lean's is
`Near.Boundary.nearRuntime`. The statement has no hypotheses beyond storage
representing a model state and the context being one the runtime builds with
the protocol configuration `protocol` (gas costs and limits are protocol
parameters, so a gas bound holds for given configurations, not for all):

- with at least the model's gas bound attached, the execution is the model's
  and uses at most that much gas;
- with less, it is the model's or an out-of-gas failure with no effects;
- input that is no call fails with no effects;
- no execution reports an interpreter limitation.

wNEAR (`refines_wnear`) states it for its deployed binary under protocol
version 86, with adapter tests that run the binary against the model under the
same configuration.

Specifications about the model become facts about the binary through
`Refines.transfer`. Specifications that need resources (a withdrawal needs
the balance for its payout and the storage stake of its new state) state them
as explicit hypotheses on the context, and are stated on the contract's
boundary step so they can transfer (see wNEAR's
`WithdrawAvailableAtBoundary` and `withdraw_available_binary`).

The format will be refined as more contracts are verified. Keep statements
self-contained and model assumptions explicit.
