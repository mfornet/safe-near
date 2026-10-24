# NEAR runtime

The Wasm interpreter is connected to NEAR through three layers:

| Package | Entry point | Responsibility |
|---|---|---|
| `near-lean/vm` | `NearVM.run` | One contract call: metering and host functions |
| `near-lean/runtime` | `NearRuntime.apply` | Transactions, receipts, account state |
| `near-lean/chain` | block application | Ordering queued work across blocks |

Together they model receipts, promises and callbacks, storage, accounts, access
keys and gas.

## Trust and validation

- Consensus and cryptography are out of scope for these packages. Block context
  is an input, and proofs must state which inputs they trust. The node built
  on top of them supplies that context (see `NEAR_NODE.md`).
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
| `near-lean/chain` `ChainReplay/DelegateSignature.lean` | The signature of a delegate action is checked by an injected verifier (`NearCrypto`), wired only in the chain package; the runtime and VM take it as a function. Only Ed25519 and secp256k1 keys verify; a delegate action under an ML-DSA key is rejected as having an invalid signature | The runtime and VM must not import cryptography; the verifier is a boundary the node supplies, and `NearCrypto` has no ML-DSA verifier |

## Goals

- Replay NEAR history with bit-for-bit agreement, including runtime upgrades.
- Broader real-chain snapshots and fuzzing.
- Specify callback delivery under failed dependencies, resource limits and
  scheduling, and connect it to contract lifetime properties.
