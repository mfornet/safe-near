# Linear drafts — periodic check 2026-10-23

This session had no Linear access (no connector, no API key), so nothing below
is filed yet. Each entry is ready to file in team **Safe-near** with labels
`periodic-check` and the label shown. Before filing, search the open
`periodic-check` issues with the same label and comment on a match instead.
All refer to the check at `eea6053` (origin/main) plus this check's commits;
nearcore refs are at `44f7ae6` (2.13.4, protocol 86). Paths without a package
are under `near-lean/runtime/NearRuntime/` or `near-lean/vm/NearVM/`.

## divergence

D1. **Receipts the VM creates are not validated like `validate_receipt(NewReceipt)`.**
`Apply.lean:256` checks only the decoders; nearcore `lib.rs:868-881`,
`verifier.rs:540-630` fail the parent with NewReceiptValidationError. In the model
the child fails instead (contract size `Apply.lean:337`, delete-must-be-final
`Apply.lean:390`) or succeeds (receipt size, total prepaid gas, method-name length).

D2. **DeleteAccount has no large-state check.** `Apply.lean:388-399` never raises
`deleteAccountWithLargeState` (constructor at `Types.lean:197`). nearcore
`actions.rs:383`, limit 10000 bytes excluding contract storage.

D3. **DeleteAccount emits a refund receipt for a zero balance.** `Apply.lean:394`
calls `refundReceipt` unconditionally (`Refund.lean:29`); nearcore only when
`account_balance > 0` (`actions.rs:401`). Extra receipt, outcome and id.
Confirmed by the coordinator against both sources.

D4. **Duplicate transactions get an InvalidNonce outcome.** `Apply.lean:826-846`;
nearcore v85+ drops them with no outcome (`UniqueChunkTransactions`, `lib.rs:1988`).

D5. **Delay limit compares burnt gas, not compute and storage proof size.**
`Apply.lean:854,878`; nearcore `lib.rs:2385,2463,2575`. Which receipts get delayed
can differ.

D6. **No per-receipt storage proof limit** (`EnforcePerReceiptStorageProofLimit`,
enabled at v86: `logic.rs:272-275,4126`, `lib.rs:839`). Calls nearcore aborts
succeed in the model.

D7. **Wasm prepare limits are not enforced.** `near-lean/vm/NearVM/Run.lean:266-267`
validates and normalizes memory only; nearcore `prepare_v3.rs:41-46` also limits
functions, locals, body size, tables, table elements and types.

D8. **Log limits.** `Host.lean:128-129` checks each message against
`max_total_log_length` instead of the running total (`logic.rs:105-116`); both limits
surface as `guestPanic` (`Run.lean:68`) instead of TotalLogLengthExceeded /
NumberOfLogsExceeded; gas is charged before the count check (`logic.rs:3908-3914`).

D9. **Oversized `value_return`** (`Host.lean:611`, `Metered.lean:384-389`) yields
`guestPanic`, not ReturnedValueLengthExceeded, and burns data-receipt gas before
the check (`logic.rs:3823-3834`).

## missing-feature

F1. **Hash host functions** (sha256, keccak256, keccak512, ripemd160) are rejected
by `unsupportedRuntimeHost` (`Metered.lean`); 8 dataset contracts import sha256.
A pure SHA-256 exists in `near-lean/interface/NearInterface/Sha256.lean`. Size S-M.

F2. **Signature and curve hosts as named trusted oracles** (ed25519_verify,
ecrecover, alt_bn128_*, bls12381_*) instead of rejection; blocks `Refines` for
intents-defuse, mpc-contract, eth2-client, aurora-engine. Size M-L.

F3. **Yield/resume lifecycle** (promise_yield_create/resume, timeout delivery) in
vm, runtime and chain; needed by mpc-contract and omni-bridge. Size L.

F4. **Check the invariant on live mainnet state**: download a contract's storage
and decide `project`/`Inv`/`Represents` on it (tools/ + executable `Inv` per
contract). Size M.

F5. **Shared near-sdk storage/serialization library** (Borsh, collections key
layouts, JSON args); sputnik-dao-factory already carries its own
`Model/Borsh.lean` and `Collections.lean`. Size M.

F6. **Models of standard environment contracts (NEP-141/145) and cross-contract
assumption composition** at the chain level, for ref-farming, skyward, the DAO
factory, omni. Size L.

F7. **Validator view hosts** (`validator_stake`, `validator_total_stake`) as block
context inputs; imported by ref-farming and skyward. Size S.

## simplification

S1. **`set_option maxHeartbeats 0`** at `near-lean/vm/NearVM/Metered.lean:897`
(`prepareStorageCallAux_gas`), the only unbounded budget: bound it or split the
proof per branch.

S2. **Registry proofs do a 76-way `rcases` with 18 copied cases** —
`EncodingRegistry.lean:19`, `ReservationRegistry.lean:31`, `DepositRegistry.lean:6`
(2M heartbeats, maxRecDepth 16384; DepositRegistry is the slowest vm module at
~105 s). Prove over the list with `List.forall_mem_cons`.

S3. **Remaining copies of the host tactic block** (~114 in NeutralEncoding,
NeutralReservations, HostDispatch, HostSelection, plus 17 in HostPromises from
:209). Same `local macro` as this check's HostGas/HostNeutralDeposits change,
taking `hwf` as an argument.

S4. **4M heartbeats in Wasm** `Fuel.lean:168,337`, `HostInvariant.lean:78`
(`cases i <;> repeat' split`): lemmas per instruction class.

S5. **Shared encoding primitives in runtime**: private `unsigned` in
`QueueEncoding.lean:33`, `ReceiptEncoding.lean:14`, `TransactionEncoding.lean:9`
(different body in `StateEncoding.lean:14`); `vector`/`string` in Receipt/State
encoding; `unique` in `QueueEncoding.lean:37`, `ReceiptRegistry.lean:10`,
`StateEncoding.lean:61`. One `NearRuntime.EncodingPrimitives` module keeps the
encoders from drifting.

S6. **Copied rollback/settlement `let` block** in `FinalizedOutputIdentifierBounds.lean:119`,
`ProcessedFreshReceiptIds.lean:86`, `AllocatorMonotonicity.lean:219`,
`ActionIdentifierBounds.lean:234`: one definition plus an unfolding lemma.

## test-coverage

T1. **Nothing automatic builds near-lean/{interface,vm,runtime,chain} or the contract
projects.** This check found `main` broken (ChainReplay.Encode missing a case after
62fbab7) and the Wasm testsuite report broken when run from the repo root; both
went unnoticed. Propose a cheap path-filtered `lake build` of the chain package
(which builds everything below it) on push.

T2. **`use_global_contract` hosts have no native oracle scenario** in
`tools/runtime-conformance` (fees were hand-copied from `77.yaml`), and no
runtime/chain test of the action's pricing, encoding or the `unsupportedAction` path.

T3. **`distributedGas` (62fbab7)**: no runtime-level test that observed gas used
equals used plus distributed on a real receipt.

T4. **wasm-tools version with a build suffix (87597ef)**: no case in
`tools/tests/test_wasm_logic.py`.

T5. **Python regressions skipped by automatic CI**: `tools/tests/check_axiom_audit.py`
and `check_vm_dependencies.py` aren't named `test_*`, so the `repository` job's
`unittest discover` skips them (they need Lean builds; decide whether they belong
in the periodic plan only).

## stale

X1. **Orphan module** `near-lean/runtime/NearRuntime/TrieAccounting.lean` (one-line
`import NearVM.TrieAccounting`, imported by nothing, only a build target in
`tools/periodic_check.py:64` and `tools/chain-conformance/README.md:352`): import
it from `NearRuntime.lean` or drop it.

X2. **Sputnik blueprints** `contracts/{sputnik-dao-factory,sputnikdao2-v3.2}/verification/blueprint/`
hold only a README index; `notes/design/PROVING.md` and `PROJECT_STRUCTURE.md`
describe `blueprint/` as a generated leanblueprint. Note the exception or add blueprints.

X3. **`notes/todo/wasm_runtime_rewrite.md` is mostly history** (phases 1-3 done,
an Outcome section); move out of `todo/` or trim, fixing links from
`near-lean/wasm/README.md`, `REVIEW.md`, `wasm_logic_iris.md`.

X4. **nearcore SHA repeated in `runtime-reference.yml:30`** (`ref:`) besides
`near-lean/runtime/reference.json`; add a consistency check (e.g. in
`tools/check_lean_toolchains.py`).
