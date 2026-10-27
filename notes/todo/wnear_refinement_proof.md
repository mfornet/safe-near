# Proving the wNEAR refinement

The campaign that closes `refines_wnear_exported`
(`contracts/w-near/verification/Proofs/Refinement.lean`): the deployed
`contract.wasm` refines the wNEAR model, for every input, state, context and
amount of gas, with every hypothesis discharged by the kernel.

Items marked **Decided** are not re-opened without discussing first. Items
marked **Open** are for whoever reaches them to settle and record here.

## Why this is doable

This is the largest formalization in the project, and it is large for one
reason only: size. The binary is 907 functions and about 67k lines of
instructions. No single piece of it is deep. A function either moves bytes,
does arithmetic, loops over a buffer, or calls something else. Each of those
has a contract, and each contract is a small, checkable statement.

So the job is a long list of small, simple tasks, and the plan below is
built so that the list is always visible, always shrinking, and never
blocked on one hard problem. Every contract stated, validated or proved is
real progress, and the dashboard shows it. Every wrong statement caught
before a proof is a detour avoided, and it is celebrated as such (section 7).
Keep going, one function at a time: it adds up.

## 1. What "done" means — **Decided**

- `refines_wnear` holds with no hypotheses beyond `cfg.WF`. The current
  hypotheses `hcode` (decoding), `hprotocol` (config parsing), `hstart` (no
  start function) and `hexports` (the exported functions) are discharged in
  the kernel.
- `just wnear-audit` passes with no module allowed to depend on `sorryAx`.
- Only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), no
  `native_decide` (`notes/design/PROVING.md`).
- The blueprint shows every contract and its status, and nothing is marked
  proved that is not.

## 2. Principles — **Decided**

1. **Contracts are the interface.** Every Wasm function the proof crosses
   gets one contract: a `wpInvoke`-style separation-logic statement of what
   it needs (arguments, owned memory, host-state fragments, gas credits) and
   what it gives back on each way of ending. Call sites use the contract,
   never the body. From one contract we derive the call-site lemmas we need
   (for example a `_ok` form whose precondition rules out the panic branch),
   so every use point has a direct lemma to apply. The same discipline holds
   for loops (a loop invariant is a contract for the loop body) and for
   branches whose two sides are long.
2. **Sorried contracts are progress.** A contract can be stated with
   `sorry`, validated (section 5) and used by its callers before its own
   proof exists. The blueprint marks it open. This lets us work top-down
   and bottom-up at once, and shows the full shape of the proof early.
3. **Gas credits are threaded everywhere.** Every contract consumes gas
   credits in its precondition: the cost bound is proved together with
   correctness, in one pass. There is no "enough gas" version proved first
   and a gas pass afterwards.
4. **Infrastructure grows with the proof.** The separation logic for NEAR's
   metered machine (wp lemmas for each step, host contracts, representation
   predicates, tactics) is built as the proofs need it. Nothing is built in
   advance "because it will be needed".
5. **No early generalisation.** The first time a pattern shows up, it is
   written out by hand. Repetition is fine: it shows how complex each branch
   really is. A pattern becomes a lemma or tactic once it has shown up
   several times and its shape is clear. The obvious exceptions exist from
   the start: tactics that consume straight-line instructions (constants,
   locals, globals, arithmetic, comparisons, loads and stores with a known
   footprint).
6. **Validate before proving.** Most of the effort on a contract goes into
   making sure it is true and usable before anyone tries to prove it
   (section 5).
7. **A wrong statement is a step back.** When a statement turns out wrong,
   stop, find the cause, record it (section 7) and look for the same mistake
   everywhere else in the formalization.
8. **Never stuck.** There is always a list of independent tasks at the
   frontier, and a stalled proof follows the protocol of section 10 instead
   of absorbing unbounded effort.

## 3. The layers of the proof

Each layer only uses the contracts of the layer below.

| Layer | What it is | Where |
|---|---|---|
| L0 Code facts | Lemmas `body i = <literal>` for each function, the module's exports, start, tables, data, and the parsed config, all checked by the kernel | wNEAR verification |
| L1 Metered logic | A separation logic over NearVM's metered machine: gas credits, host-state resources, the rule for every instruction including its charge, host contracts for every import wNEAR calls | `near-lean` (new package next to `wasm-logic`) |
| L2 Bridge | From a contract for an exported function to the three clauses of `Refines` on `Near.Boundary.execOn` | `near-lean` (generic part) and wNEAR |
| L3 Rust runtime | The shadow stack (`__stack_pointer`), wee_alloc's heap invariant, representation predicates (`Vec`, `String`, `&[u8]`, `Option`, `Result`, `u128`, `AccountId`), vtables | wNEAR verification |
| L4 Library contracts | compiler builtins (`memcpy`, `memset`, `memcmp`, u128 multiply and divide), `core::fmt`, `alloc`, `serde_json`, Borsh, near-sdk's `env` wrappers and `LookupMap`, near-contract-standards | wNEAR verification |
| L5 Methods | One contract per exported method, whose postcondition is the model's `step` and whose gas cost is `gasBound` | wNEAR verification |
| L6 Assembly | `refines_wnear_exported` from L5 and L2 | `Proofs/Refinement.lean` |

### 3.1 How the `Refines` clauses come out of a contract — **Open, to validate in M2**

The intended route, which the walking skeleton (M2) must confirm:

- **Enough gas.** A method contract, given credits for `gasBound`, proves
  the execution ends in the model's outcome: `Matches` and
  `usedGas ≤ gasBound`.
- **Below the bound.** One generic lemma about `runMetered`: a run with a
  smaller burn budget follows the same steps as a run with an unbounded
  budget until the first failed charge, and then stops with `outOfGas`. The
  program sees the same `prepaid_gas`, and `used_gas` agrees on the common
  prefix. So the small run is the model's or an out-of-gas failure whose
  logs are a prefix of the model's, and the boundary rolls it back. This is
  proved once, for every contract.
- **Invalid input.** The argument parser's contract says it either returns
  the parsed call or panics, and nothing before it has effects; the
  boundary rolls a panic back.
- **No execution issue.** Fuel sufficiency is already proved; the contracts
  never reach an unsupported construct.

### 3.2 Shape of a function contract — **Open, fix with the first examples**

To be settled on the first real functions (M3), and then written down here:

- how the outcomes appear in the postcondition: a normal return, a trap, and
  a host abort (a guest panic with its message, a host error);
- how gas credits are written, and how a cost expression depends on the
  arguments;
- the footprint convention: which memory a function owns, borrows or
  returns, and that it restores `__stack_pointer`;
- the file header of each contract: Wasm index, Rust name, source location,
  and a comment for each hypothesis saying which call site needs it.

## 4. Representation

- **One file per function or library component**, named after the Rust
  function. Its Wasm index is in the file header.
- **Names come from a rebuild.** The binary is stripped
  (`-C link-arg=-s`). The build is reproduced exactly (`contract.toml`), so
  M0 rebuilds without `-s`, checks that the code section is byte-identical,
  and takes the name section from it. The table mapping indices to Rust
  names is committed.
- **Rust source as reference.** Each contract cites the Rust source it
  describes (rustc 1.51 `library/`, serde_json 1.0.60, near-sdk 3.1.0,
  wee_alloc 0.4.5, near-contract-standards 3.1.0). The contract is about
  the Wasm; the source helps write it and spot mistakes.

## 5. Validating statements

A contract is validated before its proof starts. The statement must be
**true** (no execution violates it) and **usable** (every call site can be
proved from it). Mistakes in either direction are cheap now and expensive
later.

### 5.1 The internal-function harness (milestone M1)

A test executable that runs one internal Wasm function in near-lean's
metered interpreter, from a memory, stack pointer, arguments and host state
that the test builds, and checks an executable form of the contract on the
result: the postcondition, the footprint (nothing outside it changed),
`__stack_pointer` restored, and gas burnt at most the stated cost.

Each contract comes with:

- an **executable checker**, or a generator of the states its precondition
  describes, decided by hand when a predicate is not decidable;
- **counterexample tests in both directions:**
  - *too strong*: inputs that satisfy the precondition and look for a
    violated postcondition: border values, empty and maximal buffers,
    `u128` limits, aliasing, invalid UTF-8, deep nesting, memory near the
    allocator's limit;
  - *too weak*: inputs the call sites actually produce, captured from
    running the methods, to check the precondition admits them;
- a **gas check**: the stated cost against the measured cost, on random and
  worst-case inputs. The stated cost must be an upper bound, and close
  enough that the method's bound stays under `gasBound`.

### 5.2 Use before proving

A sorried contract is used by its callers before it is proved. If a caller
cannot be proved from it, the contract is too weak or has the wrong shape,
and it is changed now, while nothing depends on its proof.

### 5.3 Review checklist for every contract

- Is the footprint complete? Every byte read or written, every global, every
  host-state fragment.
- Are all the ways it can end covered: trap, panic, host error, and out of
  gas through the credits?
- Does the cost cover every instruction, every charge of every host call,
  and the worst case of the trie?
- Are integer widths and overflows right (`i32` vs `u32`, wrapping)?
- Does it say what callers need, and nothing a caller cannot establish?
- Does a similar contract already exist, and does this one agree with it?

### 5.4 Method contracts against the model

Method contracts (L5) are also checked by `just wnear-scenarios`: their
postcondition is the model's `step`, so the existing differential scenarios
stress them. The `refinement-stress` skill runs a round before each method's
proof starts.

## 6. When a statement or the model is wrong — **Decided**

1. Stop the proof that found it.
2. Find the cause: what assumption about the code, the runtime or the model
   was wrong.
3. Record it in the misstatement log (section 7).
4. Sweep: look for the same mistake in every other statement, contract and
   model definition, and fix each one found.
5. If the model changed: fix the model, rerun `just wnear-scenarios` and the
   adapter tests, and re-prove the `Spec/` theorems.
6. Add a harness test that would have caught it.

## 7. The misstatement log — **Decided**

[`wnear_refinement_misstatements.md`](wnear_refinement_misstatements.md).
One entry per wrong statement caught: what was stated, what was true, how it
was caught (harness, call site, failed proof, review), the root cause, what
the sweep found, and the test added. Catching one before a proof is
finished is a success: it records a detour that did not happen.

## 8. Milestones

Each milestone has a deliverable and an exit check. Milestones after M2 can
overlap; the order of M5–M8 is free.

### M0. Code in the kernel

- Decoding made compositional, so each function body is decoded and checked
  by the kernel on its own: lemmas `body i = <literal>` for every function,
  and the exports, start, tables, elements, data and globals.
- The rebuild with a name section and the committed index-to-name table.
- A call graph with precise `call_indirect` targets (from the types and the
  table), per exported method.

*Trouble to expect:* kernel memory and time for 907 bodies; a decoder
whose structure does not split cleanly by section; data segment size.
*Exit:* `hstart` and `hexports` are proved; one function's body is a
kernel-checked literal.

*Status: done.* `Binary.decode_wNearBytes` proves in the kernel what
`contract.wasm` decodes to, and `hstart` and `hexports` are gone from
`refines_wnear`. `Binary/functions.tsv` names every function, from a rebuild
without `-s` whose non-custom sections are byte-identical to the deployed
binary (`tools/wasm_names.py`, `SAFE_NEAR_RUSTFLAGS="" contracts/w-near/build.sh`),
and lists the exported methods that can reach each one (`call_indirect`
resolved to the table entries of its type). This over-approximates: even
`ft_total_supply` reaches 457 functions, mostly through the panic path's
`core::fmt`. Of the reached code, about 43 KB is `core`, 44 KB `serde_json`,
21 KB `std` and `alloc`, 18 KB near-sdk and near-contract-standards, and
3.8 KB the contract itself. What we learnt:

- Kernel decoding from a `ByteArray` is quadratic: each byte read walks a
  list from the start. The decoder now reads through a function
  (`Input.read`), and proofs supply a `Wasm.ByteSource`, chunks at the
  leaves of a tree. A 4.7 KB entry went from failing at 62 GB to 15 s.
- The kernel's cache grows with all the work one declaration does and is
  freed between declarations. Every heavy check is split into per-range
  declarations (22 part files), and the pieces are combined by lemmas
  (`Parser.Reads`, `count_of_reads`, `body_eq`, `List.zipWith_append`).
  One declaration for the whole module took 20 GB; the split takes at
  most 5 GB per file.
- Equations between large terms must match syntactically. Letting the
  elaborator unfold a 907-element list to compare it took minutes; each
  list is now defined in the shape its proof produces.
- **Trust.** `wNearBytes` is the content of `contract.wasm` because the
  elaborator `byte_source%` read it from the file, as `file_hex%` did
  before; the kernel cannot check a 185 KB literal against a hex string
  (deep recursion). The adapter tests check the embedded bytes against the
  file. This is the one link from the statement to the file, and it is the
  same kind of link as before.

### M1. The internal-function harness

Section 5.1, with checkers for a handful of library functions (`memcpy`, an
allocation, a u128 operation) to fix its interface.

*Exit:* a contract can be stated and stressed in both directions before
anyone proves it.

*Status: done.* `just wnear-harness` (`contracts/w-near/verification/Harness/`).
`Harness.load` instantiates the binary as `runAttempt` does, `Harness.call`
runs one function by its Wasm index from a prepared store with
`runInitialized`'s charging, and `Harness.capture` records the store and
arguments at every entry into chosen functions while a method runs (the
`call` and `call_indirect` targets, resolved through the table). A
`Contract α` (`Harness/Contract.lean`) gives `pre`, `footprint`, `post`,
`cost`, a stack window and ghost data `α`; `Contract.check` also checks that
nothing outside the footprint changed, every global is restored, the host
state changed only in gas, and the burnt gas is at most `cost`. Each
contract gets border and random inputs (which must satisfy `pre`), inputs
captured from twelve method calls (which must satisfy `pre`: otherwise it is
too strong for a caller) and probes outside `pre` (on which a check must
fail: each clause is needed).

First contracts (`Harness/Builtins.lean`): `memcpy`, `memset`, `bcmp`,
`__multi3`, with costs that match the burnt gas exactly on every input, and
`__rust_alloc` with live allocations as ghost (result aligned, in the heap,
disjoint from every live block, no live block changed). Its cost is
provisional and loose (up to 9x): fixed work plus a bound per free cell, to
be replaced in M4. What we learnt:

- Costs can be stated exactly, from a count of the body under
  `runMetered`'s rules (activation, one per instruction, one more per loop
  back-edge, nothing for `block`). The harness caught two miscounts
  (misstatement log, 1 and 2), so every cost is stated from a count and
  checked, never from a guess.
- `memcpy`'s forward loop is also right for overlapping ranges with
  `dst < src`; the contract still requires disjoint ranges, which is what
  Rust's callers guarantee.
- `bcmp` stops at the first difference, so it reads past memory's end
  without trapping when an earlier pair differs; its precondition asks for
  both ranges in memory all the same.
- The prepared memory is the protocol's initial size (1024 pages), not the
  binary's 17.

### M2. Walking skeleton

The whole chain from a contract to `Refines`, on a tiny test module with
one exported function that reads its input, writes storage, logs and
returns:

- the metered logic of L1, for the instructions and host functions the
  test module uses, gas credits included;
- the adequacy bridge L2, including the below-the-bound lemma of 3.1;
- the three `Refines` clauses for the test module against a tiny model.

*Trouble to expect:* gas credits interacting with host calls whose cost
depends on their result (registers, storage reads); the boundary's
storage-stake check after the run; how host aborts appear in `Post`.
*Exit:* a closed `Refines` proof for the test module. This is the milestone
that removes the risk of getting stuck on the glue at the end.

*Status: in progress (continuation in PR #39).* The current pieces are:

| Piece | Evidence | Status |
|---|---|---|
| Gas credits, spending and residual frames | `NearVM/GasCredits.lean` | Kernel checked |
| Replay of successful charges at larger counter limits | `NearVM/GasBudget.lean` | Kernel checked; lifted to runs by `MeteredPrefix` under local step compatibility |
| Actual metered-machine WP, charging, composition and error exits | `NearVM/MeteredLogic.lean` | Kernel checked; no separation frame rule yet |
| Constants, locals and a symbolic constant-return program | `NearVM/MeteredRules.lean` | Kernel checked, including exact gas and memory preservation |
| Direct host calls and a symbolic metered `input` caller | `NearVM/MeteredCall.lean` | Kernel checked, including opcode and host costs |
| Boundary success, abort, receipt and stake-failure adequacy | `NearRuntime/Refinement.lean` | Kernel checked; assembly retains the method/low-gas premises |
| Host burn-list credits and storage-write functional core | `NearVM/MeteredHosts/{Charges,Storage}.lean` | Kernel checked; trie/metered storage contract remains open |
| Metered input and output hosts | `NearVM/MeteredHosts/{Input,Output}.lean` | Kernel checked; concrete `Skeleton/Output` discharges fixed log reads from original memory |
| Effectful walking module and independent resource-aware model | `Skeleton/{Module,Model}.lean` | Syntax/model facts and checker-to-`Matches` equivalence kernel checked |
| Walking-module validation, linking and initialization | `Skeleton/Instantiation.lean` | Kernel checked for original and prepared memory (`Prepared`, `Memory`) |
| Walking-module executions | `just wnear-skeleton` | Validated on creation, replacement, binary/long inputs, gas and resource limits |
| Actual loading and entry activation | `Skeleton/{Startup,Execution,Fuel}.lean` | Kernel checked; actual VM success conditional on local storage/resources; default fuel sufficient |
| Host-trap call rule and early register-size rejection | `NearVM/MeteredTrap.lean`, `Skeleton/InputFailure.lean` | Kernel checked; exact trap state, gas, resources and fresh-marker classification |
| Whole successful body | `Skeleton/{Body,Calls,Success}.lean` | Kernel checked; local storage frontier and explicit resources remain |
| Trie-write metered phases | `NearVM/MeteredHosts/StorageMetered.lean` | Kernel checked from local lookup/dereference/accounting/proof-size obligations |
| Below-bound run lifting and input/return host compatibility | `NearVM/MeteredPrefix.lean`, `MeteredHosts/{Budget,ReturnBudget}.lean` | Kernel checked; logging, storage and machine compatibility open |
| Reachable overlay representation | `NearInterface/TrieOverlayInvariant.lean`, `NearRuntime/TrieOverlayInvariant.lean`, `Skeleton/OverlayProbe.lean` | Old context premise refuted; corrected uniqueness invariant preserved by actual operations |
| Overlay lookup/view consistency | `NearInterface/TrieOverlayLookup.lean` | Kernel checked under unique overlay keys; on-disk base agreement remains separate |
| Actual input-size failure through receipt observation and its symbolic gas bound | `Skeleton/{Costs,FailureExecution}.lean`, `NearRuntime/InitialCredits.lean` | Kernel checked; exact/smaller-budget cost checks pass |
| Trie compact-path and leaf serialization | `NearInterface/{TrieEncoding,TrieSerialization}.lean` | Kernel checked against actual parsers, with explicit byte widths |
| Actual singleton construction and reads | `NearInterface/TrieLeaf.lean` | Kernel checked; lookup keeps the unresolved nonzero-root premise explicit |
| Metered overlay/empty-base writes and resource frames | `NearVM/MeteredHosts/{StorageOverlay,StorageEmpty,StorageFrame}.lean` | Kernel checked from initial credits and local resources, with no assumed primitive outcomes |
| Storage representation and usage | `NearInterface/StorageUsage.lean`, `NearVM/StorageRepresentation.lean`, `Skeleton/StorageResources.lean` | Kernel checked through initialized storage entry and computed final storage |
| Actual pure/input/output machine budget compatibility | `NearVM/{MeteredPureBudget,MeteredHostBudget,MeteredOutputBudget}.lean` | Kernel checked; storage and whole-run invariant assembly remain |
| Isolated native recorder arithmetic and necessary history | `NearInterface/{TrieRecorder,TrieRecordingHistory}.lean` | Kernel checked; no runtime/WF integration or recorder-fidelity claim |
| Whole effectful gas bound, other deterministic failures and `Refines` | — | Open; SAF-67 also requires statement repair |

The walking module uses `input`, `storage_write`, `log_utf8` and
`value_return` through the actual NEAR metered runtime and receipt boundary.
The harness tests both kinds of budget edges: varying the burn cap with
prepaid gas fixed, and varying prepaid gas with the protocol fixed. It checks
exact deterministic resource failures, invalid methods, storage-stake rollback,
and log prefixes. Neither those tests nor a parameterized `ContractModel`
constitute a universal refinement proof.

**Frontier:** repair the recorded-proof-size input contract and discharge nonempty
canonical-trie lookup/dereference agreement with raw storage; instantiate
remaining on-disk storage cases; derive a symbolic cost
including trie charges and establish its resource conditions. Connect the
successful VM outcome to the receipt boundary, then prove deterministic
resource failures and local step compatibility for the remaining hosts and
machine instructions before assembling `Refines`. The counter-level simulation
may relax prepaid and burn limits, but immutable `NearContext.prepaidGas` seen
by guest code must stay fixed. Host compatibility is a premise to discharge,
not an implicit generic monotonicity assumption.

Prepared validation and instantiation now cover arbitrary positive configured
memory sizes within the Wasm limit. `Memory` proves the exact key/log byte reads
without expanding zero-filled pages. `Startup` connects the actual `runAttempt`
pipeline to the prepared body; `Success` composes all fifteen opcodes and the
four actual hosts, leaving storage's local invocation/gas evidence explicit. `Execution` now
connects this to actual VM success, with the post-storage empty-promise
invariant explicit. `Fuel` discharges the default interpreter fuel requirement.

A substantive premise correction was necessary: old `Context.WF` admitted
duplicate overlay keys and therefore actual `executionIssue` counterexamples
on both the skeleton and deployed wNEAR. The corrected premise requires unique
keys within each overlay, an invariant of runtime construction and operations.
See misstatement 5 for kernel/executable evidence and the scope of the repair.

**Open shared statement repair (SAF-67):** the current WF predicate admits
an arbitrary recorded-proof-size function. `ProofSizeProbe` proves a current-WF
canonical empty context and conditional non-refinement; executing deployed
`new` reports the proof-limit error while the model succeeds with ample gas.
See misstatement 6 and `just wnear-proofsize-probe`. This is independent of
canonical trie correctness and must be repaired before full refinement.

The reviewed native model requires a finite hash-to-first-object map, removal
count, code-byte contribution and receipt baseline. Its upper bound is object
bytes plus 2000 per removal plus code bytes. Distinct recording is idempotent;
removal is counted every time, including repeated tombstones. These are the
pinned [recorder](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/core/store/src/trie/trie_recording.rs#L102)
and [removal](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/core/store/src/trie/update.rs#L154)
behaviors. The VM consumes this upper bound relative to its receipt snapshot
([RuntimeExt](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/runtime/runtime/src/ext.rs#L297)).
Current overlay state alone loses repeated-removal history, so a function of
that state cannot encode the faithful recorder generally.

The recommended repair is explicit recorder state and a fidelity relation,
then a wNEAR footprint proof. It needs valid full-trie key domains, serialized
node/value bounds, code/prefix contributions and bounded accesses/removals;
"three short paths" is not a proof under current WF. The alternative is to
make the high-level model predict legitimate proof-limit failures in order.
`TrieRecorder` now proves isolated object/removal/code/snapshot arithmetic and
finite event-budget bounds. `TrieRecordingHistory` proves no state-only removal
counter can represent every removal on current overlays. Runtime fidelity,
native overflow conditions and integration remain open.
The user preference is pending. No unchecked global size bound, forced
unchecked recorder mode or weakened failure alternative has been applied.

**Open canonical-trie obligation:** `TrieAccounting.walk` treats the all-zero
hash as the empty subtree at every depth. `TrieConstruction.finish` does not
reject that digest for a nonempty encoded node; witness deduplication rejects
conflicting payloads but does not establish nonzero node hashes. Thus the
intended build/lookup theorem needs a proof that all reachable nonempty node
hashes are nonzero, or a reviewed change to construction that enforces the
reserved sentinel. No concrete SHA256 preimage or runtime counterexample is
known. A cryptographic assumption is not silently added, and arbitrary
zero-valued *value* hashes are not a problem for direct dereference. This
obligation remains open alongside serialization, traversal and witness proofs.

The runtime currently does not enforce `maxNumberRegisters`; the skeleton
pins this observed limitation explicitly. Register-size limits are enforced.
This does not affect the default configuration's one-register example, but
must not be described as nearcore conformance for arbitrary register limits.

Validation for this increment (2026-10-27): 55 proof modules were checked
transitively for axioms (3060 declarations, 2196 theorems, zero violations); the
walking-skeleton checks pass; all five existing builtin harness contracts
pass; all 211 adapter checks and all 51 differential scenarios pass. The web
blueprint builds after giving Binary, Harness and Skeleton explicit library
roots. The full wNEAR audit covers 84 modules, 5033 declarations and 2477
theorems, permitting only the original refinement module's open proof and its
two dependent theorems.

### M3. The first method, top-down

`ft_total_supply`, or another small view: its contract, proved from sorried
contracts of every function it calls, then those leaves proved. This fixes
the contract shape of 3.2, the first representation predicates and the
first automation.

*Exit:* one exported method's `Refines` clauses proved with no `sorry`.

### M4. The Rust runtime layer

The shadow stack, wee_alloc (its free lists and growing memory through
`memory.grow`), and `Vec`/`String` growth.

*Trouble to expect:* wee_alloc's invariant is the most intricate heap
invariant in the binary; `memory.grow` can fail, and that branch must be
shown unreachable under the protocol's limits or matched to the model; the
shadow stack can silently overflow into the data segment, so stack usage
needs a proved bound.

### M5. Formatting and panics

`core::fmt` (`Formatter`, `write_str`, `Display` for strings and integers,
u128 to decimal through the u128 builtins), the panic machinery, and
vtables: a predicate "a vtable whose entries satisfy these contracts" that
`call_indirect` sites use.

*Trouble to expect:* trait objects; formatting through several layers of
indirect calls; exact panic and log text with near-sdk's prefix.

### M6. JSON arguments

serde_json's deserializer for each argument struct. Its contract states the
accepted inputs exactly as `NearInterface.Json` does, in both directions,
and that rejection panics with no prior effects.

*Trouble to expect:* the largest invariant of the campaign; recursion when
skipping ignored values (depth limit 128) and its stack usage; UTF-8 and
escapes; numbers; duplicate and unknown fields; the gas cost per argument
byte.

### M7. State and storage

Borsh encoding of the state, `LookupMap` keys, near-sdk's `env` wrappers
over registers and storage, against `Model/Storage.lean`; host contracts
for storage with worst-case trie charges.

### M8. Every method

The remaining 14 methods, roughly in order of size: the views; `new`,
`near_deposit`, `storage_*`; `ft_transfer`, `near_withdraw`;
`ft_transfer_call` and `ft_resolve_transfer` (promises, prepaid gas
arithmetic, promise results). A `refinement-stress` round before each.

### M9. Closing

`refines_wnear_exported` assembled; `hcode` and `hprotocol` discharged;
`just wnear-audit` with no `sorry` allowance; blueprint and README updated.

## 9. Infrastructure that grows

- **From the start:** tactics that consume straight-line instructions with
  no branching and a known footprint.
- **On demand:** wp lemmas for each instruction in the metered logic and
  host contracts, added when a proof first needs them.
- **When a pattern is clear:** lemmas and tactics for repeated shapes (a
  loop over a byte buffer, a bounds-checked slice access, a `Result`
  match), added only after several proofs wrote them by hand. Each is
  listed in an automation catalog in the logic package's README, with the
  proofs that motivated it.

## 10. Measuring progress and not getting stuck

### 10.1 The dashboard

A `just` recipe that lists, for each function reached by an exported
method: Rust name, size, and whether its contract is *stated*,
*validated*, *used* by its callers and *proved*. Totals per milestone. The
blueprint has one node per contract with the same status, so the
dependency graph shows the frontier.

### 10.2 The frontier

Contracts make proofs independent: once a function's contract and its
callees' contracts are stated and validated, its proof can be done by
anyone, in any order. There is always a list of such tasks, and work is
picked from it.

### 10.3 When a proof stalls

After two approaches to a proof have failed:

1. Stop. Write down the goal that does not close.
2. Check the statement again with the harness: is the goal actually true?
   If not, it is a misstatement (section 6).
3. If it is true, split it: state the intermediate fact as its own lemma,
   validate it, and work on it separately.
4. If it is still stuck, escalate (section 11.2) or put it on the open list
   with the goal written down, and pick the next task from the frontier.

## 11. Parallel work and agents — **Decided**

### 11.1 Working in parallel

- One file per function contract and its proof, so independent work does
  not touch the same files.
- A shared convention for contracts (section 3.2), written down once M3
  fixes it.
- A contract changes only through review: its callers depend on it. Changing
  a contract means rechecking every caller and rerunning its harness tests.

### 11.2 Choosing the model for each agent

The campaign has many tasks, so agent cost matters. Each task goes to the
cheapest model likely to succeed, and the choice is adjusted from results.

| Task | Model |
|---|---|
| Running the harness, scenarios, audit and dashboard; transcribing bodies and names; mechanical edits; straight-line proofs with established tactics | Haiku |
| Proving a function against a validated contract with known patterns; writing harness checkers and counterexample tests; loop invariants that follow an existing template; reviews against the checklist of 5.3 | Sonnet |
| Designing the logic (L1, L2); contract shapes and new representation predicates; the hard invariants (wee_alloc, serde_json, fmt, vtables); triaging misstatements and their sweeps; deciding when a pattern becomes automation | Opus |

- Brief each agent with a clear goal, the files, the contract and what done
  looks like. A task that cannot be briefed clearly is not ready for a
  cheaper model.
- If a cheaper model fails a task twice, escalate it one level and note the
  task type.
- Keep a short record of success and failure per task type and model, in
  the "Agent results" section of the log of section 7. When
  a type succeeds reliably on a cheaper model, move it down; when it keeps
  failing, move it up.
