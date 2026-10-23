# Linkdrop verification

Source-level model of the `near` account contract, pinned at
`9a6bb316f6b7c83b504ce9c94a80c37178097655`; binary code hash
`HiyC5tB1gBDpgR4x1guEp1orBde5PXqUYGoWaZfX3JGX`.
The manifest requests near-sdk 5.17.0, but the pinned Cargo.lock resolves
**5.17.1**, checksum `a241826c1e10492edc565c459348d4aa11b34894e80e728701100774804dc822`.
The SDK and macro sources at that version were inspected locally.

This is the first contract after w-near in the sequential dataset effort.
The model proofs are complete for the properties listed below. **Deployed Wasm
refinement, the concrete VM adapter, and compatibility with actual SDK storage writes are open.**
The mathematical storage projection round trip is proved.
The project is intentionally self-contained, using Lean 4.34.1 and Std only;
it passes the same strict transitive axiom audit as w-near.

From the repository root:

```sh
just build linkdrop
just audit contracts/linkdrop/verification
```

[binary-boundary.json](binary-boundary.json) records the binary hash, all imports,
and all function exports. A static check against the current NearVM host table
finds five missing import names:

- `env.promise_batch_action_function_call_weight`
- `env.promise_batch_action_deploy_global_contract`
- `env.promise_batch_action_deploy_global_contract_by_account_id`
- `env.promise_batch_action_use_global_contract`
- `env.promise_batch_action_use_global_contract_by_account_id`

NearVM resolves all imports before running a method, so these names prevent even
initialization through the current runner. This is a concrete runtime capability
gap. The inventory is a name check, not a native conformance run or signature
verification. Weighted callbacks also require unused-gas distribution semantics;
replacing them with ordinary fixed-gas calls would misstate this binary.

The periodic checker automatically builds new verification projects with
`--wfail` and audits all declarations without allowing sorry. Its full native
conformance run is separate from these model checks.

## Model and proven properties

`Model/Methods.lean` models all ten explicit public entry points, including SDK
privacy/deposit/init guards in macro source order. Arguments are already parsed.
`Key := Nat` supplies abstract key identities; accounts are abstract validated
strings. Byte interpretation, valid identifier syntax and JSON encodings still
need a concrete adapter. Generated NEP-330 metadata/ABI exports are outside this
financial model and must be classified when the binary exports are connected.

| Area | Checked result |
|---|---|
| Representation | Every successful call preserves u128 balance bounds; uninitialized maps are empty |
| Reachability | All bounded successful model traces preserve these bounds and finite map support |
| Authorization | Private methods require predecessor=current; other map entries cannot change |
| Initialization | Nonpayable `new` cannot initialize twice; successful initialization empties the map |
| Views | Successful balance/information views report the stored amount and have no effects; absent keys panic |
| Send | Positive deposits credit `min(old + deposit, u128::MAX)` and request exactly the restricted one-NEAR access key |
| Liability | Aggregate deposit credit is at most the attached deposit; a claim removes exactly its payout from liabilities |
| Claim | Only the inherited signer key is consumed; it cannot be claimed again without a subsequent insertion |
| Creation refund | Failed direct creation schedules its captured amount to its captured predecessor |
| Claim restoration | Failed creation-and-claim overwrites the signer-key entry with its captured amount |
| Callbacks | Exactly one result is required; bytes in Successful are ignored, Failed restores/refunds, NotReady aborts |
| Advanced options | An option must be present and at most one of four deployment options may be selected |
| Return values | Returned receipt indices are in range: claim returns payout 1; creation returns resolver 1; send returns 0 |
| Storage sizes | 34-byte STATE header; three records per map entry; ED25519 costs 120 bytes and SECP256K1 184 bytes, plus three record overheads |

The liability theorems sum over a duplicate-free finite key universe containing
the changed key. Finite support is proved separately. They concern liabilities
and scheduled payouts, not contract liquid balance or successful transfers.
`RestoreConservation` assumes the signer-key entry is still absent; it cannot
be strengthened to preserve arbitrary intervening deposits.

## Contract-specific behavior that constrains security claims

`Proofs/Interleavings.lean` contains kernel-checked model executions:

1. Send 10, begin account creation, send another 7 to the same key, then resolve
   failure. The intermediate balance 7 is overwritten by 10 rather than 17.
2. The same schedule resolving success leaves balance 7 while scheduling deletion
   of that key. Map membership therefore does not ensure a usable claim key.
3. Repeated sends credit the map and request AddKey again. A duplicate-key action
   can fail later; `send` has no resolver to undo its already committed credit.
4. Ordinary claim removes the entry and schedules independent key deletion and
   payout receipts. It has no callback to restore funds after payout failure.

These are **model witnesses**, not verified mainnet exploit traces. Runtime
receipt ordering, key-add failure, account existence, gas, key deletion and
refund settlement must be validated independently. In particular, key deletion
on a success callback and a concurrent AddKey can race in either direction.

Other distinctions from w-near:

- `send` uses saturating addition, not checked addition. Exact credit requires
  `old + deposit ≤ u128::MAX`; the general conservation result is an inequality.
- There is no storage registration fee or minimum funding check. A one-yocto send
  can schedule a one-NEAR key allowance and grow three trie records. Gas expenditure
  through that allowance is separate from the map liability and can erode backing.
- `#[private]` checks predecessor, not signer account or callback provenance.
  Legitimate signers and callback arguments require chain-level authentication.
- `create_account*` does not enforce account existence, subaccount/TLA naming,
  minimum account balance, or usable options. Those checks occur during actions.
- `Some([])` counts as a present key option; no usable key/contract is guaranteed.
  In advanced options an allowance of zero means Unlimited, not a zero allowance.
- Advanced action order is create, transfer, full keys, limited keys, deployment.
  Simple creation instead schedules create, full key, transfer. Both append a
  callback depending on receipt 0 with 13 TGas static gas **and unused-gas
  weight 1**, and return callback receipt 1. Its final gas can exceed 13 TGas;
  the model records the scheduling policy, not an exact finalized gas amount.
- Successful callback bytes can be arbitrary: `is_promise_success` checks status,
  not a boolean JSON return value. Raw result counts and NotReady are retained.

## Storage and remaining obligations

The legacy `UnorderedMap` is not w-near's LookupMap. With prefix `a`, its trie
contains `ai + borsh(PublicKey) → u64 index`, `ak + u64 index → borsh(PublicKey)`,
and `av + u64 index → u128 amount`. `STATE` contains the serialized index prefix
and two vector headers. PublicKey serializes its Vec (length prefix, curve tag,
key bytes), unlike the nearcore public-key enum encoding.

`Model/Storage.lean` specifies this layout using an explicit vector-order witness
and globally injective public-key byte assignment. Removing a non-last key swaps the last
entry into its slot. Canonically sorting the logical map would produce incorrect
trie observations. `Proofs/Projection.lean` proves that two valid encodings with the same trie
records (up to enumeration order) represent the same logical state. It follows
that `project data (encode data state order) = some state` for every valid
layout. The projection uses classical choice, as w-near does; an executable
Borsh decoder remains open. Global key-byte injectivity is explicit: injectivity
only among stored keys would not distinguish an absent colliding abstract key.

Size and projection theorems concern this encoding; compatibility with actual
SDK storage writes and a standalone proof that all encoded trie keys are
unique remain open.

## Refinement

Deployed refinement is stated once for every contract, as
`NearInterface.Refines` (`near-lean/interface`; design in
`notes/todo/refinement_equivalence.md`). wNEAR instantiates it. linkdrop's
earlier, divergent `RefinesTypedExecution` has been removed rather than
retargeted with guessed parts: a `ContractModel` instance needs facts that
come from running the binary, and near-lean cannot run it yet (the five
missing host functions above). Once it can, the instance needs:

- `Parses`: the SDK 5.17.1 argument decoding of every entry point, on the
  shared JSON layer (`NearInterface.Json`), including `PublicKey` strings
  and the `Key`/`keyData` interpretation;
- `encodeState`/`Inv`: `Storage.encode` with its order witness folded into the
  state (the raw storage is a set, the vector order a physical choice);
- `step` from the context: privacy, deposit and initialisation guards as now,
  then the runtime's balance and storage-stake checks;
- `encodeReceipts` with the leftover gas, which the weighted callbacks share;
- the exact panic texts and the logs before each panic, observed on
  `contract.wasm`;
- a gas bound, calibrated on the binary and valid for every trie;
- adapter tests comparing every entry point with the model through
  `Near.Boundary.execOn`.

Beyond single calls, chain-level obligations remain: callback provenance,
pending liabilities, gas allowance costs, runtime refunds, sufficient backing
throughout interleavings, and conditional liveness (funded valid creation and
transfer, successful action execution, eventual delivery). None follows merely
from scheduling a promise.

The blueprint proof index is [blueprint/README.md](blueprint/README.md).
It is a source document; LeanArchitect annotations and generated web/PDF views
have not been added yet. Open propositions are definitions, never axioms or sorry.
