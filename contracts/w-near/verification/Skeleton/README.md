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

Kernel-checked facts currently cover the export, signature, absence of start,
model parse functionality, installation of the new key-value pair,
preservation of every unrelated pair, and equivalence of the executable
success checker with the actual `NearInterface.Matches` proposition. There is no `sorry` or `native_decide` in
these files.

M2 is **open**. Remaining obligations are a universal metered contract for the
method (including dynamic trie and host costs), a proved gas-bound expression,
a below-bound execution-prefix theorem, module validation/instantiation facts,
and assembly of all `Refines` clauses for arbitrary well-formed contexts and
represented states. The concrete contexts use canonical tries and valid account
IDs; their complete `Context.WF` propositions are not yet formally discharged. The scenarios validate proposed statements; they do not
replace these universal proofs.
