# wNEAR verification

Formal model and specifications of `wrap.near`
(`../contract.wasm`, code hash `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1`,
source `../source/w-near` at core-contracts commit `54f8267`, near-sdk 3.1.0).

The layout follows `notes/design/PROJECT_STRUCTURE.md`:

| Directory | Lake library | Content |
|---|---|---|
| `Model/` | `Model` | The model: state, host context, every method as a Lean function, on-chain layout |
| `Spec/` | `Spec` | Properties to prove, one `def ... : Prop` each |
| `Proofs/` | `Proofs` | Completed model proofs; deployed refinement remains open |
| `blueprint/` | | Lean blueprint (`notes/design/PROVING.md`), fed by `@[blueprint]` annotations via LeanArchitect |

```
just build            # lake build
just sorries          # transitive sorry audit (open statements need no sorry)
just blueprint-web    # extract annotations and run plasTeX -> blueprint/web/
just blueprint-pdf    # -> blueprint/print/print.pdf
```

Packages are shared with `near-lean` (`packagesDir = ../../../near-lean/.lake/packages`,
toolchain `v4.34.1`, Mathlib `v4.34.1`, LeanArchitect `v4.34.0`); the project
depends on `near-lean/runtime` (and through it `near-lean/interface`) for the
refinement statement and its runtime instance.

## The model

`Model/State.lean` keeps the three pieces of on-chain state of the
`FungibleToken` with mathematical types: the set of registered accounts, a
balance function, the total supply and the measured per-account storage usage.
`Model/Methods.lean` has one function per exported method and the entry point
`step cfg state env call : Except Panic Outcome`, which also implements the
checks the `#[near_bindgen]` wrapper generates. Every `require` is one panic
site in the Rust source, in source order. `Model/Storage.lean` is the exact
Borsh layout (`encode`) and its inverse, the view of `notes/design/NEAR_MODEL.md`.

Facts about the source the model relies on (verified against near-sdk 3.1.0,
near-sdk-core 3.1.0 and near-contract-standards 3.1.0):

- View methods (`&self`) have no attached-deposit check; non-payable mutating
  methods panic with `Method <name> doesn't accept deposit`.
- `ft_resolve_transfer` is `#[private]`; `new` is `#[init]` and the contract
  is `PanicOnDefault`.
- `storage_byte_cost()` is the constant `10^19`, not a host call.
- `ft_transfer_call` computes `prepaid_gas - 30 TGas` with overflow checks on.
- `ft_resolve_transfer` parses the receiver's return value as a JSON `U128`;
  anything else counts as "nothing used". The model receives the parsed value
  in `Env.promiseResult`.
- `account_storage_usage` is measured with a 64-byte account id (125 bytes
  under mainnet accounting, hence the 0.00125 NEAR fee).

## Specifications

Proofs below concern the mathematical model. Applying them to deployed execution
requires the open runtime refinement proof and explicit gas/storage assumptions.

| Spec | Statement | Proof |
|---|---|---|
| `InvPreserved` | Bounds, `Σ balances = total_supply` and the measured storage usage are preserved by every execution | proved |
| `BalanceAuthorization` | Only the predecessor loses balance, except the receiver of a transfer-call inside the contract's own callback, by at most the transferred amount | proved |
| `RegistrationAuthorization` | Only the predecessor can be unregistered | proved |
| `Conservation` | Minted supply plus collected fees never exceed deposit minus NEAR sent out (per execution; chain-level solvency remains open) | proved |
| `WithdrawAvailable` | A holder attaching 1 yoctoNEAR can always unwrap any amount it holds, and gets `amount + 1` back | proved |
| `DepositAvailable` | A positive deposit that fits the supply (and covers the fee if unregistered) always wraps | proved |
| `WithdrawAvailableAtBoundary`, `DepositAvailableAtBoundary` | The same for a real call: with the balance covering the payout and the storage stake paid, a withdrawal succeeds at the function-call boundary; a deposit succeeds there unless the account cannot pay the stake of its new storage | proved |
| `ViewsPure`, `ViewsTotal` | View methods never panic, never change state, never schedule promises | proved |
| `BalanceOfCorrect`, `TotalSupplyCorrect` | `ft_balance_of` and `ft_total_supply` report the model balance and the sum of balances | proved |
| `InitOnce` | `new` cannot run twice; nothing runs before `new` | proved |
| `ProjectEncode` | The view recovers every well-formed state from its storage | proved |
| `StorageCoverage` | Occupied storage is at most the `STATE` record plus `account_storage_usage` per registered account | proved |
| `refines_wnear` | `NearInterface.Refines` for `contract.wasm` on near-lean's function-call boundary and the `wnear` contract model, under the pinned protocol configuration (version 86): every input, every amount of gas, every resource state | proved for methods the binary does not export; open for the 15 exported ones (`refines_wnear_exported`) |

## Proof approach and lessons

`Proofs/StateLemmas.lean` characterises each internal operation
(`deposit_ok`, `withdraw_ok`, `registerAccount_ok`, ...) as an iff, plus how
`setBalance`/`register`/`unregister` move `supply`. Preservation proofs then
follow the monadic structure of each method with `bind_ok_iff` and
`split_ifs`. Two things learnt while doing it, both relevant to how models
should be written:

- Keep amounts as literal `Nat`. `omega` does not look through `abbrev`s, so
  `abbrev Balance := Nat` silently disables it on every hypothesis typed with
  the alias.
- Split long methods where the Rust code switches concerns
  (`ft_resolve_transfer` became `unusedAmount` + `resolveRefund`): the pieces
  get their own lemmas and the proofs stop depending on how `do` desugars.

`RegistrationAuthorization` is proved by case analysis over all fifteen
methods, with reusable lemmas that refund callbacks preserve registration.
`BalanceAuthorization` is also proved: a non-predecessor balance can fall
only in refund resolution, for the receiver and by at most the transfer amount.
`Conservation` is proved for every model method: increases in supply and
registration liabilities are covered by the attached NEAR after outgoing promises. `StorageCoverage` is proved by bounding each encoded account record by the
64-byte entry measured at initialization. This uses a kernel-checked byte-array
length lemma and does not assume encoder injectivity. `ProjectEncode` is proved using fixed-width integer round trips, byte/string
encoding injectivity, disjoint storage keys, and equality of all registered
records. Thus `project (encode s) = some s` for every well-formed state.

## Refinement

The refinement statement is the generic `NearInterface.Refines`
(`near-lean/interface`, design in `notes/todo/refinement_equivalence.md`).
`Spec/Contract.lean` makes wNEAR a `ContractModel`; `NearRuntime.Boundary`
makes near-lean a `RuntimeInterface` (one function-call action, then the
receipt's storage-stake check); `Proofs/Refinement.lean` states
`refines_wnear` for the embedded `contract.wasm` and the embedded protocol
configuration (`runtime_config_v86.json`, the latest in `near-lean/vm/configs`
and the one the adapter tests run on). Its only hypotheses are that the
storage represents a model state, that the context is one the runtime builds,
and that it carries that configuration. Gas costs and limits are protocol
parameters: `gasBound` is measured under the pinned configuration, and under a
configuration with, say, a much larger `regular_op_cost` or no room for logs
the binary would not behave as the model. With at least the model's gas bound attached, the execution agrees with
the model exactly (return value bytes, storage, balance, storage usage, logs,
receipt bytes, failure with its exact message) and uses at most that much gas;
with less, it agrees or fails for gas with no effects; input that is no call
fails with no effects; no execution reports an interpreter limitation.

What the model adds to `step` for this (`Model/Interface.lean`,
`Model/Args.lean`, `Model/Contract.lean`):

- **Context.** Account ids carry over: nearcore's byte-level account-id rules
  and near-sdk 3.1.0's are proved to accept the same strings
  (`validAccountIdBytes_toUTF8`). The callback result is parsed as
  `serde_json::from_slice::<U128>`.
- **Arguments.** `Call.decode` reads JSON as serde_json 1.0.60 and the derived
  `Deserialize` accept it (`NearInterface.Json`): object or exact-length array
  form, duplicate known fields rejected, unknown fields ignored (their
  strings are only scanned: UTF-8 is not checked there), escapes and
  surrogates as serde handles them. Methods without parameters never read
  their input. `Parses` is the graph of `Call.decode`, hence functional.
- **Failures.** Every panic site carries the data its message depends on, and
  `Panic.message` is the exact text the binary reports, source location
  included; `Panic.logs` are the logs emitted before it. `step` is followed
  by the runtime's checks: the logs against the protocol's limits on their
  number and total length (`logLimit`, at the log that exceeds them), then
  on a success promise deposits against the liquid balance
  (`balanceExceeded`), the runtime's validation of the receipts the call
  created (`receiptInvalid`, with nearcore's message) and the storage stake
  of the new state (`lackBalanceForState`).
- **Outputs.** Return values and receipts are compared as bytes, in the field
  order and escaping serde_json and near-sdk's `ext_contract` produce.
- **Gas.** `gasBound` is measured compute and per-argument-byte constants with
  margin, the gas a call attaches to its receipts and the fees they reserve
  (a transfer's for the costliest receiver, a NEAR-implicit account it creates),
  the bytes of the arguments and of the promise result a callback parses,
  and a worst-case trie term: every node of the longest possible key path,
  cold, for each distinct key a call touches. That the bound holds is part of
  the obligation; it is not proved.

`just runtime-adapter-test` runs `contract.wasm` through the boundary and
compares every execution with the model as `Refines` does: a life cycle, every
callback result shape, every panic, malformed and non-canonical arguments,
unknown methods, balance exceeded, lack of balance for state, out of gas below
the bound, and an adversarial state whose registered accounts share ever
longer key prefixes with the accounts a transfer touches.
`just wnear-scenarios` (`scenarios/`, runner in `Differential/`) does the
same along timelines: an initial world and blocks of receipts, with delayed
callbacks, their promise results and the chunk's trie cache written in the
scenario, every receipt checked against the three clauses of `Refines`.
It found and fixed five gaps in the model (log limits, UTF-8 in ignored
JSON strings, the runtime's validation of the receipts a call creates, and
two missing terms in `gasBound`: transfer fees to implicit accounts and the
promise result a callback parses); see `scenarios/README.md`.
`withdraw_available_binary` shows what the statement buys: under it,
`WithdrawAvailableAtBoundary` is a fact about the binary's execution.

All model/spec/proof declarations are subject to a strict transitive axiom
audit (`just wnear-audit`). It rejects `sorryAx`, `native_decide` and every
axiom outside `propext`, `Classical.choice` and `Quot.sound`, except the one
open obligation `refines_wnear`. The storage projection still uses classical
choice, not an executable Borsh decoder.

Solvency, storage-lock coverage and end-to-end transfer-call behaviour remain
future chain-level specifications; `near-lean/chain` has the definitions
(`Reachable`, `runIsolated`, `touches`, `upgrades`) to write them in Lean.

### Returned receipt selection and delayed callbacks

`Ret.promise index` and `ReturnData.receiptIndex index` preserve the local receipt
index instead of coarsening all promise returns. `nearWithdraw` and
`WithdrawAvailable` explicitly return index 0 (the payout); `ftTransferCall`
returns index 1 (the resolver). The adapter tests compare that exact selection.

Whole-receipt result forwarding, transfer result data, rollback after storage
checks and delayed callback delivery are exercised separately through the native
and Lean full runtimes. See [receipt-result conformance](../../../tools/runtime-receipt-reference/README.md)
for the tested schedules and the still-failing full gas/financial comparison.
These finite tests do not prove deployed refinement or eventual chain progress.
