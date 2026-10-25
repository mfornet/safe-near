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

- Consensus and cryptography are out of scope for these packages. Block context
  is an input, and proofs must state which inputs they trust. The node built
  on top of them supplies that context (see `NEAR_NODE.md`). The chunk's
  recorded storage proof size (`ApplyState.storageProofSize`) is such an
  input: with it the runtime checks `main_storage_proof_size_soft_limit` and
  the VM checks `per_receipt_storage_proof_size_limit`.
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
| `runtime/NearRuntime/Types.lean` `Action` | No DeterministicStateInit action | Not yet modeled; inputs with it cannot be expressed |
| `runtime/NearRuntime/Types.lean` `ReceiptEnum` | No ActionV2 `refund_to` receipts; refunds go to the predecessor | Not yet modeled |
| `runtime/NearRuntime/Types.lean` `Transaction` | No `block_hash`; no `Expired` validity-period check | Chunk inclusion is a chain-level input |
| `runtime/NearRuntime/Fees.lean` `txCost` | No `signature_verification_cost` | Zero for Ed25519/secp256k1; other key types are rejected |
| `runtime/NearRuntime/Apply.lean` `applyAction` `.stake`, `runtime/NearRuntime/State.lean` `EpochInfo` | The epoch is an input: the minimum stake, the validators' stakes and their total are `ApplyState.epochInfo` (what `EpochInfoProvider` answers), and proposals are returned in `ApplyResult.proposals` (`uniqueProposals` is the chunk's dedup). No epoch manager: validator selection, proposal acceptance and the minimum stake's own computation are the chain's | The epoch manager is consensus state, outside `Runtime::apply`; the chain supplies its answers |
| `runtime/NearRuntime/Apply.lean` `actionRandomSeed` | Without `nativeReceiptHashes`, calls get the seed directly, not `create_random_seed(action_hash, seed)` | Trusted direct-seed interface; exact mode derives it |
| `runtime/NearRuntime/Apply.lean` `applyAttempt` | Applies receipts only: outgoing receipts are returned unfiltered; no incoming-receipt validation | The surrounding steps of `Runtime::apply` (scheduler, forwarding, buffering, congestion info) are in `ShardSink`/`Bandwidth`/`Congestion` and `ChainReplay/ShardChunk.lean`, so the proved `apply` is unchanged |
| `runtime/NearRuntime/ShardLayout.lean` | Only `ShardLayout::V2` without a split history; no V0/V1/V3, no resharding (parent buffers, `get_split_parent_shard_ids`) | The corpus layout is V2; resharding is not exercised |
| `runtime/NearRuntime/ShardSink.lean` | An own congestion info missing from the input is an error, not bootstrapped by scanning the queues; a buffered receipt stored without `StateStoredReceipt` metadata is rejected | Both only arise around protocol upgrades the replay does not cover |
| `runtime/NearRuntime/Congestion.lean` | `max_receipt_size` is read from `limit_config` and `ClampOutgoingGasAdmission` is tied to protocol 85; bandwidth parameters are the protocol 74-86 constants of `Bandwidth.Params.protocol`, not read from the configuration dump | The dump (`tools/dump-runtime-config`) does not export `bandwidth_scheduler_config` |
| `runtime/NearRuntime/Congestion.lean` `shardAcceptsTransactions` | Admission by congestion is a function here but is not applied by `apply` | nearcore applies it when a chunk producer selects and a validator validates transactions (`chain/chain/src/runtime/mod.rs`), not inside `Runtime::apply` |
| `chain/ChainReplay/ShardChunk.lean` | Missing chunks (`is_new_chunk = false`), receipt validation of incoming receipts and the storage-proof limit are not modelled | The corpus has none of them |
| `runtime/NearRuntime/Epoch.lean` `ValidatorAccountsUpdate.apply` | `update_validator_accounts` runs on a supplied `ValidatorAccountsUpdate`, restricted to the shard's accounts; the rewards, `stake_info` and `last_proposals` are the epoch manager's output, not computed. The trie nodes the update reads are not replayed into the chunk's node cache: the chunk trie is built from the already updated accounts. A `StorageInconsistentState` or overflow is an `Except` error that stops the replay. The update's `HashMap` order is the list order | Same as above; the update only moves balances, and the one corpus shape (a validator account, the treasury) does not depend on order or on the cache |
| `runtime/NearRuntime/State.lean` `ApplyState.storageProofSize`, `vm/NearVM/Metered.lean` `recordedStorageError` | The recorded storage proof (`recorded_storage_size_upper_bound`) is a trusted input, a function of the trie overlay state supplied by the node; without it neither the chunk soft limit nor the per-receipt limit is checked | The model records no trie proof; the node's trie recorder does (SAF-33) |
| `vm/NearVM/Run.lean` `execLimits` | Call depth 10000 instead of `max_stack_height` stack limiter | Stack-limiter instrumentation not modeled |
| `vm/NearVM/Run.lean` `runAttempt` (start) | Start function is an execution issue | Unsupported; no contract in the dataset has one |
| `vm/NearVM/Run.lean` `runAttempt` (imports) | Six v86 host functions (`promise_set_refund_to`, state-init, `current_contract_code`, `refund_to_account_id`) are unknown imports | Not yet implemented; reported as `unsupportedHost` |
| `vm/NearVM/Metered.lean` header, `prepareStorageCallAux` | Trie-node costs charged only with `storageAccounting` | Needs the chunk trie, which callers may omit |
| `chain/NearChain/Step.lean` `step` | Block context arbitrary; receipt delivery any schedule | Over-approximates nearcore ordering; consensus out of scope |
| `chain/NearChain/Step.lean` `settle` | Every settling block reuses one `ApplyState` | Test/proof helper, not block production |
| `NearRuntime/Apply.lean` `functionCallContext` | A yield created by an earlier action of the same receipt is invisible to `promise_yield_resume` in a later action; the VM sees the yields stored at the start of the receipt | The context is built once per action from the stored columns; the case needs a yield and its resume in different actions of one receipt |
| `NearRuntime/Apply.lean` transaction validation | A transaction signed by a gas key is reported as an execution issue instead of paying from the key's balance and nonce lane | Out of scope for M3b; the replay converter keeps these transactions as a blocker |
| `NearRuntime/Apply.lean` `applyDelegateAction` | Send fees of the inner actions are burnt per delegate action, not summed over the receipt; access-key failures of the delegate carry text instead of a structured `InvalidAccessKeyError` | The totals agree for a receipt with one delegate action; the structured error needs the access-key error types |
| `NearRuntime/Apply.lean` `processReceipt` | A yielded receipt whose data id is already waiting is reported as an unsupported execution instead of overwriting the stored receipt | The trie would overwrite it; hashes make this unreachable, and overwriting would lose the funds of the first receipt |
| `NearRuntime/Apply.lean` `planDeployGlobal` | `DeployGlobalContract` is reported as unsupported when the configuration does not include the burnt storage in the outcome | Before that feature the storage cost leaves the account without appearing in the outcome's burnt tokens; only the reporting protocols are modelled |
| `NearRuntime/Apply.lean` `processInstants` | An instant receipt addressed to the `system` account (a lone `DeleteAccount` or a yield) is reported as unsupported | The funding theory covers only receipts that neither name the system account as receiver nor as signer |
| `NearRuntime/Apply.lean` `specialImplicitAccount` | Creating an ETH-implicit account before `EthImplicitGlobalContract` (the legacy wallet contract installed as local code) is reported as unsupported | Only the global wallet contract of the current protocols is modelled; its hash comes from `ethWalletGlobalContractHash` |
| `NearVM/Metered.lean` `transferToGasKeyPlan` | A key that does not decode, with a balance that is also too large, reports `InvalidPublicKey` where nearcore reports the balance error | The plan reads the key first; nearcore checks the balance first |
| `NearVM/Metered.lean` `unsupportedRuntimeHost` | `promise_yield_create_with_id`, `promise_yield_resume_with_yield_id`, `promise_set_refund_to` and `promise_batch_action_state_init_by_account_id` are linked but trap when called | Refund targets and deterministic state init are outside the modelled receipts |
| `NearVM/Host.lean` `promiseYieldCreateFn` | The call traps if the executing account id is not valid UTF-8 | Keeps the yielded receipt encoding total; the protocol never produces such an id |
| `vm/NearVM/CryptoHost.lean`, `chain/ChainReplay/HostCrypto.lean` | `sha256`, `keccak256`, `keccak512`, `ripemd160`, `ecrecover`, `ed25519_verify`, `p256_verify`, `alt_bn128_*` and `bls12381_*` run on primitives injected through `RuntimeConfig.hostCrypto` (`NearCrypto` in the chain package); without them they are `unsupportedHost`. The `AltBn128InvalidInput` message of an invalid point is `NearCrypto`'s, not nearcore's (which prints the offending bytes). A result larger than `max_register_size` traps with `MemoryAccessViolation` without the write-register gas that nearcore charges first; an output register id of `u64::MAX` is discarded by the shared `writeRegisterResult` where nearcore stores it. `p256_verify` is linked at every protocol, not only where `p256_verify_host_fn` is set | The VM and runtime must not import cryptography. The first two are corner cases (a register over 100 MB, a contract writing register `2^64-1`); the register-count limit (`max_number_registers`) is not modelled for any host function |
| `vm/NearVM/LogRead.lean` `scanNulBytes` | In the NUL-terminated form of `log_utf8`/`panic_utf8` the address `ptr + i` is not wrapped modulo `2^64`: an address past the end of the `u64` range is out of bounds | nearcore adds in `u64`; a pointer within a megabyte of `2^64` would wrap into low memory, which no contract does (the rest of `log_utf8`, `log_utf16`, `panic_utf8` and `abort` follows `logic.rs`: decoding, `log_byte` on the decoded length, the total log length, the order of charges and errors) |
| `near-lean/chain` `ChainReplay/DelegateSignature.lean` | The signature of a delegate action is checked by an injected verifier (`NearCrypto`), wired only in the chain package; the runtime and VM take it as a function. Only Ed25519 and secp256k1 keys verify; a delegate action under an ML-DSA key is rejected as having an invalid signature | The runtime and VM must not import cryptography; the verifier is a boundary the node supplies, and `NearCrypto` has no ML-DSA verifier |

## Goals

- Replay NEAR history with bit-for-bit agreement, including runtime upgrades.
- Broader real-chain snapshots and fuzzing.
- Specify callback delivery under failed dependencies, resource limits and
  scheduling, and connect it to contract lifetime properties.
