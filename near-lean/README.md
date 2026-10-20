# near-lean

NEAR in Lean, bottom up. Each directory is its own Lake package; they share
one toolchain (`lean-toolchain`) and one `packagesDir` (`.lake/packages`).

| Package | Seam in nearcore | What it is |
|---|---|---|
| `wasm/` | wasmer / wasmtime | The Wasm interpreter (Talos), WAT decoder, official test suite |
| `vm/` | `near_vm_runner::run` | One function call: host functions, gas, `VMContext` → `VMOutcome` |
| `runtime/` | `Runtime::apply` | Accounts, access keys, receipts, actions, fees, refunds |
| `chain/` | the "trustless manipulator" | Blocks, reachable states, explicit run completion, measured burnt gas |
| `iris-wasm/` | | Separation logic over the interpreter (Talos codelib), for proofs about Wasm code |
| `programs/` | | Small Rust programs used as interpreter tests |

```
just near-build     # from the repository root: build wasm, vm, runtime, chain
just near-test      # run the three scenario suites on the real wNEAR binary
just near-configs   # regenerate vm/configs from nearcore (needs cargo)
```

## vm

`NearVM.run cfg code codeSize method ctx storage : VMOutcome` executes one
export of a decoded module under a `VMContext` (`NearVM/Context.lean`,
nearcore's struct field for field) and returns a `VMOutcome`
(`NearVM/Outcome.lean`): balance, storage usage, return data, burnt and used
gas, logs, the receipts the call created, and `aborted : Option
FunctionCallError` with nearcore's error taxonomy (`NearVM/Error.lean`).

- `NearVM/Host.lean` and `NearVM/State.lean` are the NEAR host functions
  over the interpreter's store (copied from `iris-wasm/CodeLib/Near`, which
  will be repointed here).
- `NearVM/Metered.lean` wraps every host function with the gas it costs in
  nearcore's `logic.rs`: charges computed from the arguments before the call
  and from its effect after it, action fees and prepaid gas for promises,
  storage-usage accounting, attached deposits leaving the balance, and
  structured `guestPanic` errors carrying the panic message.
- `NearVM/Run.lean` steps the interpreter charging `regular_op_cost` per
  instruction and stops at gas exhaustion.
- `NearVM/Config.lean` loads `RuntimeConfig` from `configs/`: nearcore's own
  parameter tables (`RuntimeConfigView` JSON, one file per protocol version
  at which something changed, produced by `tools/dump-runtime-config`).
  Nothing is hand-copied.

Known gaps against nearcore: trie-dependent costs (`touching_trie_node`,
`read_cached_trie_node`) are not charged. The independent fixtures check exact
instruction and host gas, but do not prove metering correct for all programs.
Contract code enters as WAT text
because there is no binary Wasm decoder in Lean yet; the cryptographic host
functions are rejected by the metered VM until concrete semantics are supplied.

`lake exe vm-tests` runs the real wNEAR binary (`tests/fixtures/w_near.wat`,
printed from `contracts/w-near/contract.wasm`) through `run`: initialisation,
deposits, withdrawals, transfer-call promises with their callback, panics
with the SDK's messages, out-of-gas, storage usage, view calls.

## runtime

`Near.apply cfg applyState codeOf state txs incoming : ApplyResult`
(`NearRuntime/Apply.lean`) is one chunk's worth of work: transactions are
verified and charged and become local receipts; local, delayed and incoming
receipts run in that order until the gas limit; every receipt yields an
`ExecutionOutcome` when it runs. Action receipts implement eight action kinds
(`applyAction`), roll back on failure, and refund unused gas to the signer
and deposits to the predecessor through system receipts. Function calls go
through `NearVM.run`; the receipts they create get fresh ids, data
dependencies become `input_data_ids` / `output_data_receivers`, and a receipt
whose data has not arrived is postponed until it has. `NearRuntime/Fees.lean`
is `config.rs`: send and execution fees per action, transaction cost.

Model limits such as interpreter fuel exhaustion, cryptographic operations,
yield/resume, validator queries, staking and unstaking are reported as execution issues.
An issue preserves the entire apply's input state and publishes no protocol
outcomes or refunds. Actor checks protect administrative actions; implicit
accounts use decoded Ed25519 public keys and block-derived initial key nonces.
See [runtime/VERIFICATION.md](runtime/VERIFICATION.md) for the reference pin,
trusted inputs, remaining discrepancies, and proof obligations.

`lake exe runtime-tests` deploys wNEAR on `wrap.near` and drives it with
transactions: wrap, unwrap, a transfer-call whose receiver has no contract
(callback refund), out-of-gas with deposit refund, invalid transactions,
implicit accounts, account deletion, gas-limit delaying. Every step checks
that NEAR is conserved: balances plus burnt tokens plus in-flight deposits
never change.

## chain

`NearChain/Step.lean`: a `Snapshot` is a chain state plus the receipts in
flight; `step` applies a block; `Reachable` closes it under block sequences;
`runIsolated` runs transactions and everything they cause with nothing else
interleaved; `Receipt.touches`, `Receipt.upgrades` and `Block.independentOf`
inspect direct interactions in pending, delayed and postponed queues. They do
not establish independence from indirect contract effects. `settle` and
`runIsolated` return a `RunResult` distinguishing quiescence, exhausted block
budget and execution issues. Their completion implies quiescence by proved
lemmas. `measureCallGasBurnt` measures successful settled executions with
maximum attached gas; it does not establish sufficient prepaid gas.
`lake exe chain-tests` exercises these boundaries on wNEAR.

## Axiom audit: no `sorry`, no `native_decide`

A finished proof may depend only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`. `tools/axiom-audit.py` checks the
transitive axioms of every declaration in a package (private helpers and proof
fields included) and fails on anything else, in particular `sorryAx` and
`Lean.ofReduceBool` (what `native_decide` and `decide +native` rely on).

```
tools/axiom-audit.py near-lean/wasm --report audit/wasm.json
tools/axiom-audit.py near-lean/iris-wasm --report audit/iris-wasm.json
tools/axiom-audit.py near-lean/programs/lean --report audit/programs.json --allow-sorry
tools/axiom-audit.py near-lean/vm --report audit/vm.json
tools/axiom-audit.py near-lean/runtime --report audit/runtime.json
tools/axiom-audit.py near-lean/chain --report audit/chain.json
```

`wasm` and `iris-wasm` must be clean. `programs` holds specs whose proofs are
open by design, so there `--allow-sorry` tolerates `sorryAx` alone and prints
each sorried declaration; any other nonstandard axiom still fails. CI runs all
three on every change under `near-lean/`. Pass `--no-build` to audit already
built artefacts.

The public VM result also carries a checked receipt DAG: dependencies refer only
to earlier receipts, returned receipt indices exist, and dependency cycles are
impossible (`run_receipts_valid`, `run_dependency_before`,
`run_returnedReceipt_lt`, `run_no_receipt_cycle`). Raw promise handles are checked
before accepting an outcome, so malformed joins cannot silently disappear
during conversion. Rejection is an explicit model issue with rollback, not contract
success. Concrete host preservation for dependency structure, returned-handle
selection, liquid funding and raw receipt gas backing is proved below.
Correspondence with nearcore beyond the conformance fixtures, global identifier
freshness and scheduler correctness remain separate obligations.

`NearVM/PromiseGraph.lean` now implements total incremental conversion, replacing
the bounded recursive join walk. It stores each handle's exact ordered receipt
vector, preserves duplicate dependencies and rejects missing/future references
or yielded promises. Executable conversion is proved equivalent to an explicit
transition relation, succeeds exactly on supported well-formed raw graphs, and
preserves receipt validity from the empty graph. Returned receipt identity comes
from that same handle table. Successful `value_return` and `promise_return`
selections now overwrite each other; overwrite lemmas and independent regressions
cover both call orders.

`NearVM/HostPromises.lean` proves dependency well-formedness preservation for
18 promise and return-value host functions, including
error outcomes. A generic metering theorem lifts these proofs through gas
charging, deposit deductions and storage-usage updates. Initialization starts
with a well-formed empty graph; successful preserving host calls therefore
admit conversion to a valid receipt graph. These local proofs do not establish
full action validity, identifier bounds/freshness, or global token conservation.

`NearVM/HostDispatch.lean` extends dependency preservation to the complete
metered registry, including unsupported/deprecated rejection and gas imports.
Successful `resolveMetered` environments contain only preserving host functions.
The resolver uses structural recursion; alignment and length theorems establish
that each output slot is the first matching registry function for its input
import, preserving declaration order and duplicate imports. This closes host
dispatch preservation; the execution lifting is described below.

`NearVM/ExecutionPromises.lean` lifts dependency preservation through every
small-step transition and finite trace, instruction/frame gas charging, and
all exits of `runMetered`. The proof includes indirect/foreign calls,
cross-instance calls, GC operations, exception preparation and indexed-memory
execution. Resolved initialization establishes the callable-host invariant;
`runResolved_promises_convertible` proves that execution from a well-formed
initial promise list produces a convertible valid graph without assuming an
output-validator check. Full state well-formedness, global identifier freshness
and conservation remain separate obligations.

`NearVM/ExecutionSelection.lean` adds returned-handle preservation. Every
resolved host operation and metered execution preserves the existence and
non-joint kind of the selected handle. `ReturnGraph.lean` proves conversion
keeps that slot's receipt identity and produces an in-bounds returned receipt.
`runResolved_return_selection` combines both invariants from resolved
initialization; `PromiseGraph.returnData?_total` proves the exact return helper
used by the VM cannot reject such a selection. Ordinary contexts start with no
selection. The shared `InterpreterInvariant` and `MeteredInvariant` theorems now
carry both dependency and selection proofs, with gas preservation explicit.
These guarantees do not establish numeric bounds, identifier freshness, full
state validity, token conservation, or deployed wNEAR refinement.

Metered `promise_and` now enforces the configured limit on expanded receipt
dependencies, checking each ordered prefix and counting duplicate dependencies.
It also rejects overflow in the u64 count-to-byte conversion before charging
per-element or memory-read costs. `PromiseLimits.lean` relates successful checks
to exact ordered expansion and proves the resulting dependency-length bound.
Independent fixtures cover the 128/129 boundary, nested joins, empty joins,
invalid-index precedence, memory bounds, overflow and view restrictions.
Broader host limits remain open.

All five supported promise allocators now enforce the configured handle-count
limit, including empty joints. Receiver parsing and callback-handle validation
precede the count check; receipt fees are retained when capacity is exceeded,
while function-action reads and fees are skipped. `promise_create` and
`promise_then` include both underlying base charges and the reference's view
error names. Protocol V2 receiver syntax is installed in the host configuration.
`preInvokeError_count_bound` proves accepted allocations fit the limit;
`checked_nextPromiseIdx_fresh` proves the u64 handle is unwrapped, absent from
the old list, and resolves to the appended promise when the limit fits u64.
This is local handle freshness, not global receipt/data identifier freshness.

Function-call action inputs now use one staged validation/charge plan: amount,
method (including empty-method rejection), arguments, then target handle,
followed by action fees and prepaid gas. Combined create/then operations retain
their receiver/receipt/count prefix before this plan. Memory-or-register reads
of missing registers incur no register-read charge, matching the reference.
`FunctionCallValidation.lean` proves accepted inputs are readable, methods are
nonempty, direct targets are receipts, and the functional host builds the same
raw action. One-yocto sponsorship follows the protocol flag: eligible function
calls at zero liquid balance receive minted deposits. VM outcomes retain attempted
grants on failure; receipt/apply results count only committed grants separately
from burnt tokens. `deductPromiseDeposit_accounting` proves local accounting.
Global conservation and deployed refinement are still open.

Receipt backing now includes purchased gas as well as deposits. Financial
settlement carries purchase price separately from block burn price and applies
the pinned v85+ minimum price, surplus refunds and account-creation charge.
`Fees.settleGas_conservation` kernel-checks the local gas-token partition;
`tools/runtime-finance-reference` compares 72 cases to nearcore's actual routines.
Full receipt and chain conservation remain open.

The runtime also provides kernel-checked finite-map and transaction invariants.
For successful transaction conversion it proves map-key uniqueness preservation,
exact account debit, receipt backing plus burnt-gas conservation, unrelated-account
isolation, authorized access-key updates and exact nonce/counter changes.
These results have explicit unique-map and reserved-signer premises; they do not
yet establish full admission equivalence or receipt/chain invariant preservation.

Transaction nonce validation now enforces the pinned monotonic/strict ordering,
checked strict increment and saturating block-height ceiling. Strict mode uses
the generated v85+ feature gate. Kernel proofs connect successful conversion to
these bounds; 126 exact comparisons exercise nearcore's actual private validator.
Apply defaults to block height one; explicit zero-height transactions are rejected.

Gas refunds now preserve their signer-key marker and restore the current finite
allowance with u128 saturation. Kernel proofs establish key/nonce isolation,
unchanged account funds and storage size, and exact bounded restoration. Native
trie/constructor/Borsh comparisons cover 66 cases; restricted-key runtime scenarios
cover delayed refunds, replacement/deletion and failure rollback. Access-key
storage accounting distinguishes absent allowances and counts receiver UTF-8 bytes.

Receipt execution is split into the action attempt, rollback and finalization.
`ReceiptInvariants` proves that rollback discards tentative state, promises and
subsidies while preserving logs and burnt gas. Refund constructors account for
exact in-flight funds; failure data carries zero funds; reward credits account
for the exact balance increase. Failed ordinary receipt finalization conserves
incoming deposit and gas backing against refunds plus gross settlement burn,
with receiver rewards shown separately. The theorem connects to
`applyActionReceipt`, with explicit account-uniqueness, matching action receipt,
non-system predecessor/signer, v85+ settlement and reward-fraction premises.
The finalization trace proves that returned burn matches settlement, logs and gas
survive failure, and attempted subsidies are erased. Storage, access keys and
scheduler state are restored, and unrelated accounts keep their full records.
The net-conservation theorem uses returned burn minus returned reward; it derives
the reward bound from a reward fraction at most one and function-call gas at most
total burnt gas. Gas bounds now follow from action execution. Successful ordinary
receipt conservation and chain conservation remain open.

`GasInvariants` proves counter bounds and exact successful charge increments,
failure saturation/error precedence, irreversible burn, and limit preservation.
These proofs cover every host charge variant, charge lists and Wasm charging.
The executable `runMetered` loop returns a counter bounded by its final limits on
all exits, including fuel exhaustion and stepper errors. A compositional theorem
bounds it by the original call budget when imported hosts preserve those limits.
`HostGas` and `HostGasLimits` derive that invariant for the actual metered registry
and resolver, including gas imports and unsupported/deprecated rejection paths.
`ExecutionGas.runResolved_gas_bounds` connects it to initialization and resolved
execution: burnt gas is at most used gas, used gas fits the original prepaid
budget, and burnt gas fits the original per-call limit.
`OutcomeGas.run_gas_bounded` lifts these facts to every public VM result, without
contract or host-behavior premises, for any interpreter fuel and view/normal call
limits. It covers loading, method/import/init failures, entry charges, execution
and receipt validation. `runInitialized` and `outcomeOfExecution` expose the
executable stages for proofs. Runtime `GasInvariants` composes the VM bound with
protocol fees and ordered action traversal, covering early errors and the final
storage-staking check. `runReceiptActions_gas_bounds` derives function-call burn ≤
total burn ≤ gas used ≤ the purchased receipt budget.
`applyActionReceipt_failed_net_conservation` uses these derived bounds rather than
assuming gas accounting. VM state/promise materialization is separated from gas
recording, and `ExecM.GasBound` provides reusable composition rules.

`RefundReceiptInvariants.applyActionReceipt_refund_conservation` covers system
balance/gas refunds containing one transfer, under account-key uniqueness and a
matching receipt payload. Successful execution credits backing exactly once;
current-key allowance restoration changes no account funds. Failed execution
restores balances and reports the complete deposit as non-gas burn, without a
recursive balance refund or gas reward. Zero gas use is derived from execution.
Missing receivers, including implicit-account names, cannot be created by system
refunds; storage-staking failure also follows the rollback/burn path. This does
not yet prove ordinary successful action-receipt or chain-level conservation.

Stake-promise scheduling preserves liquid balance: stake targets are not attached
deposits. `deductDeposit_stake` kernel-checks the no-op financial frame, and 16
native comparison cases cover zero balances, amount bounds, repeated actions,
rollback and mixed transfer/stake construction. Epoch-dependent stake execution
remains explicitly unsupported by the receipt runtime.

`PromiseAccounting` proves that the actual promise-to-receipt converter preserves
arbitrary receiver/action valuations, including total attached deposits.
`DepositRegistry.resolveMetered_funding` proves that every successfully returning
resolved host import preserves liquid balance plus pending promise deposits,
with subsidies accounted for explicitly. This includes the actual memory-decoded
amounts for create, then, batch function-call, and transfer APIs. Other registered
hosts preserve those financial fields; rejected calls have no success guarantee.
`LiveInvariant` and `MeteredLiveInvariant` lift these guarantees through actual
interpreter transitions and the metered loop. A terminal trap discards its
speculative financial state; catchable exceptions must preserve live invariants.
`HostNoThrow.resolveMetered_noThrow` proves that the concrete NEAR host registry
never raises catchable Wasm exceptions.

`OutcomeFunding.run_success_funding` proves for the public executable VM, for
arbitrary contract code, context and fuel, that success implies:

```
final balance + outgoing receipt deposits
  = initial account balance + attached deposit + recorded subsidy
```

It covers loading/entry charging, actual resolved imports, promise conversion,
and final receipt validation, with no assumed financial equation or host oracle.
The stronger live-state invariant also covers caught Wasm exceptions and indexed
memories. This closes successful VM-call funding; ordinary successful multi-action
receipt and whole-chain conservation remain open.

`MaterializeInvariants` gives a kernel-checked stage decomposition of the existing
receipt constructor. Allocation, dependency linking and data emission preserve
all chain fields except `nextId`, including pending, postponed and delayed work.
The final id counter increases by the promise count, dependency count and direct
output-data count. Promise receipt ids form a consecutive, duplicate-free range
between the initial and post-allocation counters, in promise order.
The constructor preserves arbitrary receiver/action valuations. Its specialized
funds theorem covers deposits and purchased outgoing gas, using the proved
predecessor and gas-price metadata of every emitted receipt.

`FunctionCallInvariants.applyFunctionCall_success_funded` connects the public VM
to actual successful action execution. With unique account keys, it identifies
the account, deployed code and VM result and proves:

```
after funds + before subsidy
  = before funds + incoming deposit + after subsidy + outgoing gas backing
```

Here funds include liquid/locked account balances and complete newly emitted
receipt backing. Successful commit preserves account-key uniqueness and frames
the chain outside the receiver's account/storage and id allocation. The outgoing
gas term is explicit: linking it to VM reserved gas, composing multiple actions,
and receipt-wide settlement remain required for full successful-receipt
conservation.

Transfer fees use the pinned account classification in both VM scheduling and
runtime transaction/receipt budgets: 64 lowercase hex bytes reserve creation and
full-access-key execution, `0x` plus 40 lowercase hex bytes add creation when
`eth_implicit_accounts` is enabled, and `0s` deterministic addresses carry their
creation fee. The protocol flag is loaded from the configuration and propagated
into host metering. Fees are accumulated into one charge, preserving exhaustion
precedence. Invalid amount pointers retain only reading costs, before handle
lookup and transfer fees; `chargesBefore_transfer_invalidAmount` proves that
public charge-plan frame.

`ChargeReservations.applyCharges_success_reservation` proves that successful
charge lists add exactly the sum of execution/prepaid obligations to promise
gas. Ext/instruction burn and dependency-data charges reserve no action gas.
`HostGasObligations` derives the raw obligations from the actual ABI reads and
successful append operations for all nine batch-action hosts and all five
promise-creation/join hosts. `ActionReservations` connects the public batch-action
charge plans to their action obligations, including deployment payload lengths,
implicit-transfer fees, function-call prepaid gas and key-method bytes.
`CreationReservations` proves that valid creation/callback plans reserve one
receipt base plus their action/prepaid gas; joins reserve none. Creation checks
are derived from the executable pre-invocation guard. Dependency-data fees remain
local burn. `MeteredReservations.finishMeteredCall_reservationInvariant` proves
that successful post-call charging, deposit deductions/subsidies and storage
usage updates preserve the fee table, protocol flag and raw gas backing. Terminal
traps are excluded; catchable exceptions must preserve the invariant.

`MeteredBatchReservations` connects successful precharging to raw action append
and the complete metered wrapper for all nine batch-action hosts. Its concrete
preservation theorems require only the incoming invariant, not an assumed output
accounting equation. Precharging preserves memory/register reads, protocol
validation and target lookup, so the charge and append proofs use the same ABI
inputs. `MeteredCreationReservations` extends this to function-call creation,
callbacks, empty batches and joins. `NeutralReservations` proves that context,
storage, register, log and return hosts create no onward obligation and preserve
backing. `ReservationRegistry` covers every published host, including explicit
unsupported/deprecated rejection and legacy instruction metering.
`ResolvedReservations` lifts this through actual import resolution and VM
initialization; contract proofs supply no host-preservation oracle.

Existing ETH/deterministic receivers support ordinary transfers. Creation of
these account types requires protocol code/context that is not implemented;
the runtime now reports an explicit model issue and rolls back the apply batch.
Account-existence checks take the protocol flag explicitly; disabled protocols
treat these addresses as named accounts for creation admission.

`PromiseGas` defines execution/prepaid gas obligations for every raw action and
receipt. It proves that append operations charge each receipt base once and
that promise conversion preserves the obligation through arbitrary joins.
`SuccessInvariant` and `ExecutionReservations` connect instruction/frame and
entry charging, metered execution and successful outcome packing.
`OutcomeReservations.run_success_gas_backing` discharges the concrete host
premise for the public executable VM: every successful call satisfies
`usedGas = burntGas + receiptsGas fees ethEnabled receipts`. The accompanying
budget theorem bounds burn plus all outgoing raw obligations by actual prepaid
gas, for arbitrary code, context, storage and interpreter fuel. Rejected, trapped
and incomplete attempts are excluded by the executable success condition.
This closes raw VM gas backing; runtime decoding/materialization and complete
multi-action/receipt/chain conservation remain separate obligations.

`PromiseGasInvariants` connects every modeled runtime action variant to its
raw VM execution/prepaid cost, under explicit method-decoding facts. The
byte-array and UTF-8 roundtrip proofs are shared in `Interpreter.Wasm.ByteEncoding`;
wNEAR keeps its existing Borsh theorem names as wrappers around those proofs.
Runtime calls now explicitly require UTF-8 action method names. The external
validation policy belongs to `VMContext`, not protocol fee/limit configuration;
`functionCallContext` always enables it. Validation runs after action fees,
prepaid gas and deposit deduction, matching the pinned receipt manager. Invalid
bytes produce structured `invalidMethodName` and rollback while retaining prior
logs. Opaque-byte mode is explicit for the VM mock conformance adapter only.
`ActionMethodValidation` proves rejection, successful decoding witnesses and
charge/deposit error precedence. Existing funding and gas-backing proofs cover
the additional rejection path.

`MethodEncoding` splits raw comma-separated method bytes before decoding, as
nearcore does. It proves exact field-byte reconstruction and terminator billing,
including empty CSV and multibyte names. The VM key guard validates each field;
successful postprocessing supplies that decoding fact and still implies a whole
CSV UTF-8 witness. Runtime key conversion uses the same byte fields.

The gas bridge covers action lists, receipt budgets and actual materialization.
`materialize_run_funds` identifies outgoing receipt funds as raw deposits plus
`(usedGas - burntGas) * gasPrice` for ordinary contracts. Its decoding condition
is now derived from successful execution under the strict runtime policy;
callers no longer supply `ReceiptGasEncodingValid` for emitted receipts.
`materialize_functionCall_run_funds` instantiates the actual runtime context,
which sets that policy, and therefore needs no separate decoding/policy premise.
`FunctionCallFunding` connects that result to successful commits and the actual
function-call action path. `Exec.FundingStep` uses additive gas and subsidy
terms so sequential steps telescope without truncated subtraction.
`ActionFunding` supplies monadic composition and proves the law for receipt
attempts containing arbitrary ordered function-call actions, including execution
fees, admission checks and the final storage-staking check.

`ReceiptFunding` factors settlement into a reusable action-body funding rule.
`MetadataFunding` covers deployment and key insertion/deletion, retaining their
actual account/key admission witnesses. `BalanceActionFunding` covers account
creation, transfers to existing or supported implicit accounts, best-effort gas
refund allowance restoration, and final account deletion. Deletion's beneficiary
refund is backed by the removed unlocked balance; positive locked balances are
rejected by the actual guard. Creation adds no balance, and implicit creation
credits the deposit exactly once.

`AllActionFunding.applyActionReceipt_net_conservation` has no incoming action-
family restriction. For ordinary modeled action receipts, on success and failure,
it equates account funds plus outgoing receipt backing and net burn with the
initial account funds, incoming receipt backing and explicit subsidy. Gas
refunds, rewards, admission errors and final storage-staking rollback are part
of the actual executable path. Stake/unstake still reject epoch-dependent
semantics; their successful funding rule is vacuous and does not add support.
`applyActionReceipt_accountsUnique` also preserves the unique-account premise
needed by subsequent receipt proofs.

The concrete conservation theorem requires unique account records, an ordinary
receiver, non-system predecessor/signer, matching action-receipt metadata, the
v85+ settlement branch (`accountCostIncrease = true`), and a reward fraction at
most one. No existing-receiver, VM-output or financial-equation premise is
assumed. Account-creation charges add to gross burn and cannot underfund rewards.
`MixedFunding` and function-call-only results remain available as narrower
consequences. Ordinary receipt settlement is now covered; composing it with
system refunds, scheduling, transactions and chain execution remains open.
This is a theorem of the modeled runtime, not full nearcore equivalence.

`NearVM.ReceiptPredicates` transports arbitrary decidable receiver/action
predicates through actual promise updates, conversion and successful outcome
packing, without requiring unique dependencies. `PromiseEncoding` specializes
this to receiver UTF-8 and byte-preserving method decoding. `CreationEncoding`
and `MeteredEncoding` derive witnesses from the ordered receiver and external
method guards for all five creators/joins and nine batch-action hosts.
`NeutralEncoding`, `PolicyEncoding`, `EncodingHosts` and `EncodingRegistry`
prove that strict policy and receipt encoding survive every published live
host call, including legacy gas metering; unsupported operations still trap.
`ResolvedEncoding` covers actual import resolution and initialization, and
`ExecutionEncoding` covers checked steps and instruction/frame charges.
`OutcomeEncoding.run_success_receipt_encoding` establishes the public VM result
for arbitrary code, context, storage and fuel when execution succeeds and the
context selects strict runtime decoding. Mock opaque-byte execution is excluded
by this explicit policy premise. Encoding validity is not complete action
validity or authorization. Chain conservation, verified binary decoding and full nearcore equivalence
remain open.

Promise deployment derives `ContractCode.size` from the actual payload through
`ContractCode.decodeSized`. Size limits, storage accounting and outgoing gas
budgets therefore use the byte length even when decoder metadata differs.
Three runtime regressions cover scheduling, deployment and final refunds and
previously failed with inconsistent decoder size metadata. The decoder remains
trusted for module/hash correspondence; this does not establish a verified
binary-decoding theorem.

Function-call-key host actions encode zero allowance as unlimited. Nonempty
CSV method lists cost their raw byte length plus one: comma separators become
terminators. The independent fixture checks empty/single/multiple/UTF-8 names,
positive and maximum allowances, and a tight gas budget.
The successful key cases do not establish malformed-list rejection or complete
host input-error ordering; those remain implementation/conformance gaps.
