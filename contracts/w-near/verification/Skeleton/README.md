# Walking skeleton (M2 in progress)

Run `just wnear-skeleton` from the repository root, or `lake exe
wnear-skeleton` from the verification package.

`Module.lean` defines a small Wasm method which reads arbitrary input into a
register, writes it at `k`, logs `saved`, and returns the input bytes. It uses
the actual NEAR register-sentinel ABI, metered host functions, trie accounting,
and receipt boundary. Its declared byte size is zero; binary correspondence
is deliberately outside this example.

`Model.lean` independently defines a `ContractModel`, including deterministic
register-size, storage-size, log, return-size, and storage-stake failures in
execution order. Its gas bound is a parameter, not an inferred runtime result.

`Main.lean` validates six storage/input scenarios against that model, then
repeats each at its measured exact burn budget and at four smaller burn budgets.
It separately holds the protocol fixed and varies prepaid gas, checking the
exact measured cost and three smaller budgets.
The smaller-budget checks hold prepaid gas fixed, require out of gas, verify
rollback (including prospective trie writes), and check the log-prefix rule.
It also checks invalid methods, late storage-stake failures, forced host limits,
and the zero-balance storage exemption below 770 bytes.

The explicit `runtime-known-limit-gap` regression records that the interpreter
currently accepts `maxNumberRegisters = 0`; it is not a nearcore differential
validation. Register **size** limits are enforced and separately tested.

`Instantiation.lean` proves validation, real host resolution, import checks and
initialization of the original one-page module from arbitrary host state. The
data write remains symbolic and is proved for every positive memory page count.
`Prepared.lean` lifts validation and initialization to the runtime's configured
memory bounds. `Memory.lean` proves the key and log bytes at their fixed
addresses. `Startup.lean` connects actual loading and entry activation to the
method body. `Body`, `Calls`, and `Success` compose all fifteen opcodes, input,
log and return contracts; one local metered storage frontier remains. `Execution` connects this to actual
VM success; `Fuel` proves the default interpreter fuel is sufficient.

Kernel-checked facts currently cover the export, signature, absence of start,
model parse functionality, installation of the new key-value pair,
preservation of every unrelated pair, and equivalence of the executable
success checker with the actual `NearInterface.Matches` proposition. There is no `sorry` or `native_decide` in
these files.

M2 is **open**. Remaining obligations are a universal metered contract for the
method (including dynamic trie and host costs), a proved gas-bound expression,
local host/machine compatibility for the below-bound run theorem,
and assembly of all `Refines` clauses for arbitrary well-formed contexts and
represented states. The concrete contexts use canonical tries and valid account
IDs; their complete `Context.WF` propositions are not yet formally discharged. The scenarios validate proposed statements; they do not
replace these universal proofs.

`OverlayProbe.lean` records a premise counterexample: duplicate pending trie
updates can make view and lookup disagree, causing `executionIssue` even for
deployed wNEAR `new`. The old `Context.WF` admitted these contexts (kernel
proofs in commit `a65583a`). Corrected `Context.WF` requires unique keys in
each overlay, with preservation proofs for actual runtime operations; the
probe now proves these malformed contexts are excluded. This is a correction
to the refinement premise, not a proof of the old statement.

`InputFailure.lean` proves the actual early register-size rejection: two
instructions, both fixed input charges, an exact trap state and untouched
storage/logs/registers. Classification as the expected guest panic uses
explicit fresh error-marker premises.

`FailureExecution.lean` now lifts input rejection through loading, activation,
the public VM runner and the receipt boundary. It proves model matching and
a symbolic used-gas bound from the actual initial gas limits. `Costs.lean`
shares that expression with executable checks at three lengths, its exact
budget and one unit below.

`StorageResources.lean` proves the storage host sees the prepared memory,
original raw records and register-zero input after actual startup/input effects.

`ProofSizeProbe.lean` reproduces the separately documented SAF-67 statement gap:
a canonical, unique-overlay context satisfying current WF supplies an arbitrary
oversized proof oracle; deployed wNEAR `new` fails while the model succeeds.
WF and conditional non-refinement are kernel proved; the deployed outcome is
executable-checked. Run `just wnear-proofsize-probe`. This remains open and
prevents a full refinement claim.
