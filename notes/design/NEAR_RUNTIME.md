# NEAR runtime

The Wasm interpreter is connected to NEAR through three layers:

| Package | Entry point | Responsibility |
|---|---|---|
| `near-lean/vm` | `NearVM.run` | One contract call: metering and host functions |
| `near-lean/runtime` | `Near.apply` | Transactions, receipts, account state |
| `near-lean/chain` | block application | Ordering queued work across blocks |

Together they model receipts, promises and callbacks, storage, accounts, access
keys and gas.

## Trust and validation

- Consensus and cryptography are out of scope. Block context is an input, and
  proofs must state which inputs they trust.
- Conformance harnesses compare supported VM and runtime behavior with pinned
  nearcore adapters (`tools/runtime-*-reference`). They are tests, not an
  equivalence proof.

## Divergences from nearcore

Where the Lean code simplifies or omits nearcore behavior, it says so with a
comment starting `nearcore divergence:` (what differs and why), and the place
is listed here. The periodic check ([section 6](PERIODIC_CHECK.md#6-nearcore-divergence-divergence))
looks for simplifications that are neither marked nor listed.

| Where | What differs from nearcore | Why |
|---|---|---|
| `vm/NearVM/Run.lean` `prepareLimitError` | `prepare_v3` limits are checked before validation rather than interleaved with it, and also at older versions whose non-Wasmtime engines used `prepare_v2` | A module both invalid and over a limit may report the other error; the oracle runs Wasmtime (`prepare_v3`) at every version |
| `runtime/NearRuntime/Types.lean` `ReceiptId`/`DataId` | Ids are `freshId` counters, not hashes; tx outcomes use id 0 | Identity is abstract; native hashes are bound by `NativeIdentity` when needed |
| `runtime/NearRuntime/Types.lean` `Action` | No Delegate/DelegateV2, DeployGlobalContract, DeterministicStateInit, gas-key actions | Not yet modeled; inputs with them cannot be expressed |
| `runtime/NearRuntime/Types.lean` `ReceiptEnum` | No yield/resume, ActionV2 `refund_to`, global-contract distribution receipts; refunds go to predecessor | Not yet modeled |
| `runtime/NearRuntime/Types.lean` `Transaction` | No `block_hash`; no `Expired` validity-period check | Chunk inclusion is a chain-level input |
| `runtime/NearRuntime/Fees.lean` `txCost` | No `signature_verification_cost` | Zero for Ed25519/secp256k1; other key types are rejected |
| `runtime/NearRuntime/Apply.lean` `applyAction` `.stake` | Successful stake/unstake is an `unsupportedAction` issue | Needs epoch machinery (proposals, minimum stake) |
| `runtime/NearRuntime/Apply.lean` `applyAction` `.useGlobalContract`, `Metered.unsupportedRuntimeHost` | Global contracts are an `unsupportedAction`/host issue | Needs the global contract registry and distribution |
| `runtime/NearRuntime/Apply.lean` `actionRandomSeed` | Without `nativeReceiptHashes`, calls get the seed directly, not `create_random_seed(action_hash, seed)` | Trusted direct-seed interface; exact mode derives it |
| `runtime/NearRuntime/Apply.lean` `applyAttempt` | One shard; no congestion buffering, bandwidth scheduler, instant receipts, yield timeouts, validator rewards, incoming-receipt validation | Out of scope for single-shard runtime model |
| `vm/NearVM/Run.lean` `execLimits` | Call depth 10000 instead of `max_stack_height` stack limiter | Stack-limiter instrumentation not modeled |
| `vm/NearVM/Run.lean` `runAttempt` (start) | Start function is an execution issue | Unsupported; no contract in the dataset has one |
| `vm/NearVM/Run.lean` `runAttempt` (imports) | Six v86 host functions (`promise_set_refund_to`, state-init, `current_contract_code`, `refund_to_account_id`) are unknown imports | Not yet implemented; reported as `unsupportedHost` |
| `vm/NearVM/Metered.lean` header, `prepareStorageCallAux` | Trie-node costs charged only with `storageAccounting` | Needs the chunk trie, which callers may omit |
| `vm/NearVM/Metered.lean` `unsupportedRuntimeHost` | Signature and curve, validator, yield and global-deploy hosts are execution issues; the hash hosts (SHA-256, Keccak-256/512, RIPEMD-160) run on pure Lean implementations | Semantics not supplied by `VMContext` |
| `chain/NearChain/Step.lean` `step` | Block context arbitrary; receipt delivery any schedule | Over-approximates nearcore ordering; consensus out of scope |
| `chain/NearChain/Step.lean` `settle` | Every settling block reuses one `ApplyState` | Test/proof helper, not block production |

## Goals

- Replay NEAR history with bit-for-bit agreement, including runtime upgrades.
- Broader real-chain snapshots and fuzzing.
- Specify callback delivery under failed dependencies, resource limits and
  scheduling, and connect it to contract lifetime properties.
