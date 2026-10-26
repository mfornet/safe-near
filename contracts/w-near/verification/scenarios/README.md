# Differential scenarios

Each scenario is an initial world and a timeline of blocks. Every receipt
of the timeline runs on `contract.wasm` through `Near.Boundary.execOn` (the
runtime `refines_wnear` is stated against) and on the wNEAR model, and is
checked against the three clauses of `NearInterface.Refines` for that
context. The aim is to find where the model and the binary disagree before
proving `refines_wnear_exported`. A discrepancy means the model or the
statement is wrong. Agreement on these inputs proves nothing in general.

```sh
just wnear-scenarios                       # every file here except slow/
just wnear-scenarios -v scenarios/10_callbacks.json
just wnear-scenarios --only "reverse order"
just wnear-scenarios scenarios/slow        # megabyte inputs: minutes each
just wnear-scenarios scenarios/open        # open findings: they fail by design
python3 scenarios/generate.py              # regenerate 40_gas.json, 60_random.json, 61_random_wide.json, slow/
```

The runner is `Differential/` (contract-independent `Runner.lean`, the wNEAR
instance `WNear.lean`). It runs with the working directory
`contracts/w-near/verification`.

## What a step checks

Before each receipt the runner checks the hypotheses of `Refines`: the
contract storage encodes the model state, the state satisfies the
decidable part of `Inv`, and the context satisfies the parts of
`Context.WF` that a scenario can break (`u128` balance, `u64` gas, storage
usage). A violated hypothesis reports the scenario as BROKEN, not as a
discrepancy. Then, as `Refines` states it:

- No execution reports an interpreter limitation (`executionIssue`).
- For input that decodes to a call: with at least the model's gas bound
  attached, `Matches` holds (return bytes, storage, balance, storage usage,
  logs, receipt bytes, exact failure) and the used gas is within the bound.
  With less gas, either `Matches` holds or the call fails for gas with no
  effects and logs that are a prefix of the model's.
- Input that is no call fails with no effects.

The world then advances by the binary's observation: committed storage,
balance, storage usage, the trie with its cache. The model takes the state
of the outcome it matched. The worlds cannot drift apart unnoticed, because
the next step re-checks that storage encodes the model state.

## Determinism: what the scenario decides

Everything the network would decide is written in the scenario:

- **Blocks.** A block is one chunk. Within it the trie keeps committed
  writes and its node cache, so later receipts read warm nodes. A new block
  starts from the committed records with a cold cache. `height` (default:
  the previous plus one) and `timestamp` (default `height · 10^9`) go into
  the context.
- **Receipt order.** Receipts run in the order listed, one after another,
  on the contract account.
- **Delayed receipts.** Every receipt a successful call creates is pending
  under `label#index`. Index `i` follows `RawReceipt` creation order: for
  `ft_transfer_call`, `#0` is `ft_on_transfer` and `#1` the
  `ft_resolve_transfer` callback. A `deliver` step runs it in any later
  block, as many blocks later as the scenario wants. It runs as the receipt's
  action, called by the contract under the original signer, with the
  receipt's own deposit and gas.
- **Results of other contracts.** Receipts to other accounts, such as
  `ft_on_transfer` on the receiver, are not executed. The scenario states
  what they returned: it gives the `results` of the callback that waits on
  them.
- **External balance changes.** `credit` and `debit` change the contract's
  balance, for example a refund arriving. Delivering a transfer receipt
  addressed to the contract also credits it.

## Format

A file holds one scenario object or an array of them.

```jsonc
{
  "name": "...",                       // used by --only
  "description": "...",
  "protocolVersion": 86,               // default: latest config in near-lean/vm/configs
  "contract": "wrap.near",
  "state": null,                       // no contract state yet, or:
  // {"accounts": {"alice.near": "1000"}, "totalSupply": "1000", "accountStorageUsage": 125}
  //   (totalSupply and accountStorageUsage default to the invariant's values)
  "account": {"balance": "...", "locked": "0", "overhead": 1000},
  //   overhead: storage usage beyond the contract's records (account and code)
  "trie": [{"account": "wrap.neaq", "key": "STATE", "value": "..."}],
  //   other accounts' records in the chunk trie; they only change gas
  "blocks": [
    {"height": 10, "receipts": [
      {"label": "t", "call": {
        "from": "alice.near",          // predecessor (and signer unless "signer")
        "method": "ft_transfer_call",
        "args": {"receiver_id": "bob.near", "amount": "5", "msg": ""},
        // or "argsText": "exact text" or a list of parts with {"repeat": s, "times": n}
        // or "argsHex": "7b7d"
        "deposit": "1",
        "gas": "300000000000000",      // or "bound", "bound-1", "bound+5"
        "results": [],                 // promise results the call sees
        "outputDataReceivers": ["bob.near", {"repeat": "x.near", "times": 1024}],
        //   receivers of the call's result (default none); also on a deliver
        "storageProofSize": 0},        // a constant recorded storage proof (default: unchecked)
       "expect": "ok"},
      {"label": "r", "deliver": "t#1", "results": [{"ok": "\"3\""}]},
      {"credit": "100"},
      {"probe": true, "label": "p", "call": {"method": "ft_total_supply"}}
    ]}
  ]
}
```

- **`gas: "bound"`** is the least prepaid gas for which the model's bound fits
  the call's gas limit. It is the boundary where `Refines` starts promising
  `Matches`. The bound can depend on the prepaid gas, which `ft_transfer_call`
  forwards, so the runner finds it by bisection.
- **Promise results:** `"failed"`, `"notReady"`, `{"ok": text}` or
  `{"okHex": hex}`.
- **`expect`** is not part of `Refines`. It makes a scenario BROKEN when it no
  longer exercises the path it was written for. Values: `ok`, `fail`,
  `noCall`, `outOfGas`, `balanceExceeded`, `lackBalanceForState`,
  `methodNotFound`, `panic`, `panic:<substring>`, `other`, `other:<substring>`.
- **`probe: true`** runs the receipt on the current world and leaves the world
  unchanged. A discrepancy is recorded instead of stopping the scenario, so
  a block of independent probes reports every disagreement.
- **`ft_transfer_call` at `bound`** panics: its bound fits below the 30 Tgas
  the call keeps, so `bound` exercises the gas-subtraction panic. Its success
  edge is `"30000000000001"`, one gas for `ft_on_transfer`.
- **`optional: true`** on a `deliver` skips it when the receipt does not exist,
  because the call that would create it failed. Generated scenarios use it.

## Files

| File | What it targets |
|---|---|
| `00_lifecycle.json` | The happy path across blocks; checks the runner itself |
| `10_callbacks.json` | Transfer-call interleavings: reverse resolution order, receiver spending or unregistering before the refund, sender unregistering (burn) or re-registering, replayed and forged resolutions, every promise-result shape, `ft_on_transfer` landing on the contract itself, a payout to the contract itself |
| `15_wrapper.json` | The `#[near_bindgen]` wrapper's order: private check, deposit check, arguments, state; on an initialised and an uninitialised contract |
| `20_arguments.json` | serde_json acceptance as the binary sees it: nesting depth in ignored values, UTF-8 and escapes in ignored and parsed strings, numbers, account ids, options, array forms, whitespace, BOM |
| `25_arguments_more.json` | Escaped and duplicate keys, the array form with missing, null and extra elements, `U128` strings at `from_str_radix`'s edges, 1- and 2-byte account ids, overlong and surrogate UTF-8 in typed and ignored strings, malformed numbers and literals, empty and `null` input |
| `30_logs.json` | Memos at, and one byte past, the total log length limit, including multibyte ones |
| `35_receipts.json` | Validation of the receipts a transfer-call creates: no gas for `ft_on_transfer` at exactly 30 Tgas, more than the total prepaid gas limit above 1030 Tgas |
| `40_gas.json` (generated) | Every method at `bound` and `bound-1` on a trie whose keys share prefixes with the touched ones; warm and cold cache; long arguments (ignored strings, arrays, escapes, whitespace, leading zeros); promise results up to 20 KB in the costliest shapes |
| `45_output_data.json` | `value_return` with 1, 100 and 1024 receivers of the result, on the contract and elsewhere, for every value-returning method at `bound`, below it and at 300 Tgas; a transfer-call at its success edge; a second promise result of 200 KB that is never read |
| `50_resources.json` | `u128` edges of balances, supply and the contract balance; balance exceeded; the 770-byte zero-balance exemption; locked balance; huge storage usage; deposits on views |
| `55_failure_order.json` | Two failures at once under a storage-stake deficit: panic, log limit and balance exceeded before receipt validation, receipt validation before the stake check |
| `60_random.json` (generated) | Seeded random interleavings of every method across 7 accounts, two of them 64 characters long; delayed callbacks with random results |
| `61_random_wide.json` (generated) | Seeded random interleavings with ETH-implicit and deterministic callers, a 64-character contract account on even seeds, receivers of results on calls and deliveries, forged resolutions with deposits, transfer-calls at 30 Tgas + 1 and 1000 Tgas |
| `70_accounts.json` | Payouts, refunds and transfer-calls for ETH-implicit, deterministic and NEAR-implicit accounts at the bound; contracts named with 64 characters, `0x` + 40 hex, and as a sub-account |
| `slow/40_gas_large.json` (generated) | Arguments of 1 to 4 MB, promise results of 100 KB to 4 MB |
| `open/storage_proof_size.json` | Fails by design: finding 8, a gap in `Context.WF` |

## Findings

The first round found four gaps in the model, and a fifth appeared after
merging `main`. All five are now fixed in the model, and the scenarios that
found them pass.

1. **Log limits.** A memo longer than 16340 bytes pushes the logs past
   `max_total_log_length`. The binary then fails with a log-limit host error,
   while the model succeeded.
   - **Fix:** a generic `NearInterface.logLimitError`, a new
     `ModelFailure.logLimit`, and the check in `contractStep`. Logs come
     before promises in every method, so this check precedes the balance
     and stake checks.
   - **Consequence:** `WithdrawAvailableAtBoundary`,
     `withdraw_available_binary` and `withdraw_available_wasm` now assume the
     withdrawal log fits the limits. `DepositAvailableAtBoundary` assumes the
     same of the deposit log.
2. **Ignored strings.** serde_json 1.0.60 skips an unknown field's strings
   without checking their UTF-8. Keys inside the ignored value are skipped the
   same way, but the struct's own keys are checked. The binary therefore
   accepts `{"receiver_id":…,"amount":…,"x":"\xff"}`, where the model said
   "no call".
   - **Fix:** `Json.Value.invalidStr` and `none` keys. Only a typed field or
     a struct key rejects them.
3. **Gas bound.** A transfer to a NEAR-implicit account (64 hex characters)
   also pays for creating the account and its key: 7.2 Tgas of
   `create_account` execution under protocol 86. `near_withdraw`,
   `storage_deposit` and `storage_unregister` called by such an account used
   up to 9.0 Tgas against a bound of 8.5.
   - **Fix:** `transferReceiptGas` is now computed from the protocol's fees
     for the costliest receiver, instead of a measured 0.5 Tgas.
4. **Gas bound, promise results.** `ft_resolve_transfer` reads and parses
   the result of `ft_on_transfer`. The receiver decides that result, up to
   4 MB. A 100 KB `U128` string of leading zeros ran out of gas at the
   model's bound. Measured costs per byte of result are 245 Mgas for leading
   zeros, 172 for `\u` escapes and 92 for whitespace.
   - **Fix:** `gasBound` charges `argumentByteGas` (400 Mgas) per byte of the
     first promise result (`Call.resultBytes`).
   - **Consequence:** the 5 Tgas the transfer-call gives its callback is
     below this bound, as it already was. For callbacks, `Refines` only ever
     promises "matches or runs out of gas with no effects".
5. **Receipt validation.** `main` added nearcore's validation of the
   receipts a call creates at the boundary (`checkVMReceipts`, reported as
   `NewReceiptValidationError`). `ft_transfer_call` with exactly 30 Tgas
   prepaid gives `ft_on_transfer` zero gas. With more than 1030 Tgas it gives
   `ft_on_transfer` more than `max_total_prepaid_gas`. In both cases the
   binary fails, where the model succeeded.
   - **Fix:** the interface's `ReceiptValidation.callReceiptsError` checks a
     call's function-call and transfer receipts, and returns nearcore's
     message. `contractStep` applies it after the balance check, as
     `ModelFailure.receiptInvalid`.
   - **Boundary:** the runtime now reports these errors with the same
     messages, through one `runtimeFailure` that `observe` and the seam
     share, instead of the `repr` of the error.
   - **Consequence:** `WithdrawAvailableAtBoundary` and its corollaries also
     assume the runtime accepts the payout receipt.
   - **Unreachable limits:** the argument and receipt size limits cannot be
     reached by wNEAR. `ft_transfer_call` forwards all but 30 Tgas, so a
     `msg` near 4 MB runs out of gas before its receipt exists.

The second round (the `refinement-stress` skill) found two more gaps in the
model, now fixed, and one in the statement, still open.

6. **Wrapper order.** near-sdk-core 3.1.0's `method_wrapper` checks the
   predecessor of a `#[private]` method before the deposit. The model checked
   the deposit first. So another account calling `ft_resolve_transfer` with a
   deposit got "is private" from the binary and "doesn't accept deposit" from
   the model.
   - **Fix:** `step` checks `isPrivate` first.
   - **Found by:** `15_wrapper.json`, and seeds 1 to 4 of `61_random_wide.json`.
7. **Gas bound, receivers of the result.** `value_return` pays
   `new_data_receipt_byte` (64.9 Mgas per byte to another account under
   protocol 86) for every byte and every receiver in `output_data_receivers`.
   `Context.WF` does not bound the number of receivers. `ft_metadata` with
   1024 receivers used 9.47 Tgas against a bound of 8.04 Tgas. A method that
   returns a promise still pays for `null`, which near-sdk passes to
   `value_return` before the promise replaces it.
   - **Fix:** a generic `NearInterface.returnDataGas`, the VM's charge for a
     value of a given length, and `Call.returnBytes`, the longest value each
     method returns. `gasBound` adds their product.
   - **Consequence:** the gas hypothesis of `WithdrawAvailableAtBoundary` and
     its corollaries now also pays for the receivers of the withdrawal's
     result.
   - **Harness:** the runner had fixed `outputDataReceivers := []`; scenarios
     can now set it.
8. **Open: the recorded storage proof (statement).** `Context.storageProofSize`
   is a trusted input that `Context.WF` does not constrain. When it reports
   more than `per_receipt_storage_proof_size_limit` (4 MB), the first storage
   access fails with "Size of the recorded trie storage proof has exceeded the
   allowed limit", which no model predicts. So `Refines` is false for every
   contract that touches storage. On a real chain one wNEAR call records at
   most three short trie paths, far below 4 MB. The fix belongs in the shared
   statement, in `Context.WF` or a hypothesis, and is not made here.
   `open/storage_proof_size.json` shows it. Filed as SAF-67.

Not found, with what was tried: the limits in `limit_config` that wNEAR can reach
(log length, receipt validation) were already covered. Number of logs (at most 2
per call), promises per call (2), actions per receipt (1), data dependencies (1),
storage key length (69 bytes), returned data (under 200 bytes) and register size
(the input, at most 4 MB) cannot be reached. Every account kind as the receiver
of a payout, and three contract names, stay within the bound.
