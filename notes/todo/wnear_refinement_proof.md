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
| Host burn-list credits and storage-write functional core | `NearVM/MeteredHosts/{Charges,Storage}.lean` | Kernel checked; full canonical metered contract assembled below under explicit node/proof premises |
| Metered input and output hosts | `NearVM/MeteredHosts/{Input,Output}.lean` | Kernel checked; concrete `Skeleton/Output` discharges fixed log reads from original memory |
| Effectful walking module and independent resource-aware model | `Skeleton/{Module,Model}.lean` | Syntax/model facts and checker-to-`Matches` equivalence kernel checked |
| Walking-module validation, linking and initialization | `Skeleton/Instantiation.lean` | Kernel checked for original and prepared memory (`Prepared`, `Memory`) |
| Walking-module executions | `just wnear-skeleton` | Validated on creation, replacement, binary/long inputs, gas and resource limits |
| Actual loading and entry activation | `Skeleton/{Startup,Execution,Fuel}.lean` | Kernel checked; actual VM success conditional on local storage/resources; default fuel sufficient |
| Host-trap call rule and early register-size rejection | `NearVM/MeteredTrap.lean`, `Skeleton/InputFailure.lean` | Kernel checked; exact trap state, gas, resources and fresh-marker classification |
| Whole successful body | `Skeleton/{Body,Calls,Success}.lean` | Kernel checked; local storage frontier and explicit resources remain |
| Trie-write metered phases | `NearVM/MeteredHosts/StorageMetered.lean` | Kernel checked from local lookup/dereference/accounting/proof-size obligations |
| Below-bound run lifting and input/return host compatibility | `NearVM/MeteredPrefix.lean`, `MeteredHosts/{Budget,ReturnBudget}.lean` | Kernel checked; logging, storage and machine compatibility assembled below |
| Reachable overlay representation | `NearInterface/TrieOverlayInvariant.lean`, `NearRuntime/TrieOverlayInvariant.lean`, `Skeleton/OverlayProbe.lean` | Old context premise refuted; corrected uniqueness invariant preserved by actual operations |
| Overlay lookup/view consistency | `NearInterface/TrieOverlayLookup.lean` | Kernel checked under unique overlay keys; on-disk base agreement remains separate |
| Actual input-size failure through receipt observation and its symbolic gas bound | `Skeleton/{Costs,FailureExecution}.lean`, `NearRuntime/InitialCredits.lean` | Kernel checked; exact/smaller-budget cost checks pass |
| Trie compact-path and leaf serialization | `NearInterface/{TrieEncoding,TrieSerialization}.lean` | Kernel checked against actual parsers, with explicit byte widths |
| Extension/branch parsing, construction and traversal | `NearInterface/{TrieExtension,TrieBranch,TrieBitmap,TrieConstructionBranch,TrieBranchLookup,TrieBranchConstructionLookup,TrieWitnessTransfer}.lean` | Kernel checked against actual parsers/branch loop and actual child/reference/value/missing lookup composition; isolated child walk transfers through actual parent witness segments with explicit alias/ancestor safety |
| Actual singleton construction and reads | `NearInterface/TrieLeaf.lean` | Kernel checked; lookup keeps the unresolved nonzero-root premise explicit |
| Metered overlay/empty-base writes and resource frames | `NearVM/MeteredHosts/{StorageOverlay,StorageEmpty,StorageFrame}.lean` | Kernel checked from initial credits and local resources, with no assumed primitive outcomes |
| Storage representation and usage | `NearInterface/StorageUsage.lean`, `NearVM/StorageRepresentation.lean`, `Skeleton/StorageResources.lean` | Kernel checked through initialized storage entry and computed final storage |
| Actual pure/input/output/storage machine budget compatibility | `NearVM/{MeteredPureBudget,MeteredHostBudget,MeteredOutputBudget,MeteredStorageBudget}.lean` | Kernel checked direct storage step and metered advance; general canonical readiness/body and receipt assembly instantiated below under explicit node/proof premises |
| Functional invariant and whole-body gas simulation | `Skeleton/FunctionalInvariant.lean` | Actual continuing resources close; storage readiness derives from original empty-base WF and proof check; concrete StepSimulation and run lifting prove matched-or-gas/prefix with no fuel error, holding guest context fixed; startup and checked-receipt replay assembled below |
| Concrete phase control and prefix logs | `Skeleton/BudgetSimulation.lean` | All fifteen opcodes and administrative leave dispatched; actual control/stack/installed-host invariant closed; every actual runner prefix preserves shape and log prefix; guest context unchanged by auxiliary internal gas enlargement |
| Isolated native recorder arithmetic and necessary history | `NearInterface/{TrieRecorder,TrieRecordingHistory}.lean` | Kernel checked; no runtime/WF integration or recorder-fidelity claim |
| Actual empty-base receipt success | `Skeleton/{EmptyStorage,EmptySuccess}.lean` | Kernel checked through actual `execOn` and independent model step from original WF/representation/credits/limits; empty base, absent key, proof check, usage room and stake remain explicit |
| Final output fields and actual receipt success | `Skeleton/{FinalState,SuccessObservation,SuccessExecution}.lean` | Kernel checked through default-fuel public execution and `Matches` for the independent model step, conditional on local storage/resources/representation |
| Original-budget storage reservation | `Skeleton/StorageCredits.lean` | Kernel checked; empty storage frontier now uses original total credits without a second intermediate gas premise |
| Arbitrary returning storage frame | `NearVM/MeteredHosts/StorageReturnFrame.lean` | Actual successful metered discard-register write implies the full storage frame with no extra validation/trie/billing premises; supplies functional simulation closure |
| Storage budget replay | `NearVM/MeteredHosts/{StorageBudget,StoragePrepareBudget,StorageMeteredBudget}.lean` | Kernel checked through the complete non-view metered wrapper, including ordinary validation and gas stops; accepted primitive trie/proof facts supplied at low paid state only |
| Key/value length failures through receipt observation | `NearVM/MeteredHosts/StorageFailure.lean`, `Skeleton/{StorageFailure,StorageValueFailure,StorageFailureGas}.lean` | Kernel checked exact eight-instruction prefix, startup/default public run, structured failure, model matching and actual execOn used-gas bounds under the shared original-data cost; no trie/proof premise |
| All deterministic resource failures | `Skeleton/{LogFailure,LogLengthFailure,ReturnLengthFailure,FailureCosts,EmptyFailures,OutputFailureGas,EmptyBounded}.lean` | Kernel checked matching and actual used-gas bounds for all resource/stake branches on empty base; exact finite-set RuntimeInterface sufficient-gas clause under one original-context cost; no acceptance-limit or local storage callback premise |
| Body fuel and exact phase progress | `Skeleton/Progress.lean` | Every continuing error-free transition advances exactly one source suffix; sixteen body transitions suffice independently of gas/trie success; actual activation wrapper retains the bound |
| Invalid methods | `Skeleton/InvalidMethod.lean` | Complete unparsed-input rollback and no-interpreter-limitation clause for the exact RuntimeInterface, with no context/gas hypotheses |
| Actual build collision validation and dedup traversal | `NearInterface/{TrieConstructionInvariant,TrieWitnessFuel}.lean` | Successful actual build derives raw/final witness consistency and fetch preservation; lookup transfers with exact result/accounting at the smaller final default fuel |
| Node-only ancestor ranks | `NearInterface/{TrieNodeRank,TrieConstructionRanks}.lean` | Actual successful recursive construction produces a node certificate with serialized binding/rank bounds and ancestor exclusion; arbitrary value objects need not be excluded; decoded traversal follows this certificate in TrieRankedLookup |
| Actual canonical reference lookup | `NearInterface/{TrieRankedLookup,TrieReadableConstruction,TrieEntryLookup,TrieEntryDereference}.lean` | Actual public reference and full value lookup agree with original byte entries, using recursive decode certificates, retained value objects and deduplicated witness fuel; nonzero node hashes remain explicit |
| Startup and checked receipt budget replay | `Skeleton/{StartupSimulation,ReceiptSimulation}.lean`, `NearRuntime/BudgetObservation.lean` | Actual execOn matches an auxiliary reference or stops for gas with rollback and prefix logs; original preparation/empty-base/proof acceptance remain explicit |
| Model-level lower-gas alternative, accepted resources | `Skeleton/{FundedEmpty,FundedObservation}.lean` | Actual funded reference matches model for either stake outcome; actual execOn matches or returns out-of-gas with rollback and model-log prefix for arbitrary original gas, on the explicit accepted-resource empty-base slice |
| All-resource pointwise refinement clauses | `Skeleton/{FundedInputFailures,FundedOutputFailures,EmptyRefinement}.lean` | Sufficient-gas matching/bound, arbitrary-gas model-or-gas with rollback/model-log prefix, no execution issue and invalid-call rollback assembled for exact RuntimeInterface, with empty-base/native/proof assumptions explicit |
| Canonical overlay reads | `NearInterface/TrieCanonicalLookup.lean` | Actual canonical getReference/dereference agree with materialized view; base callback eliminated under canonical build, unique overlays and explicit nonzero-node certificate |
| Canonical raw storage and usage | `NearInterface/TrieCanonicalStorage.lean`, `NearVM/MeteredHosts/StorageModelUsage.lean` | Actual canonical reads agree with raw storage; arbitrary fresh/replacement post-state storage and usage agree with finite model |
| General canonical metered write and original costs | `NearInterface/TrieCanonicalCost.lean`, `NearVM/MeteredHosts/{StorageCanonical,StorageCanonicalCost}.lean` | Actual reference/dereference plan derives complete metered write, gas/residual/usage/promises; original-context access, evicted-byte and replacement-register bounds; explicit nonzero nodes/proof check |
| General canonical body, budget and receipt refinement | `Skeleton/{CanonicalBody,CanonicalCost,CanonicalObservation,CanonicalReady,CanonicalSimulation,CanonicalReceiptSimulation,CanonicalBounded,CanonicalRefinement}.lean` | Accepted-resource calls over arbitrary canonical storage satisfy every pointwise refinement clause, with context-only gas bound, arbitrary original gas, both cell/stake outcomes, and no empty-base/selected-key premise; nonzero/proof/native/preparation remain explicit |
| Actual external trie charges | `NearVM/MeteredHosts/TrieCost.lean` | Kernel checked original-key bounds for successful reference lookup (2n+1 touches), value dereference (one touch), and their actual metered charges using original prices |
| Storage-stake acceptance/rejection | `Skeleton/EmptyStakeFailure.lean` | Kernel checked positive-deficit rollback with saved log and matching for both zero/positive cases on the empty-base slice |
| Trie access-count bounds | `NearInterface/TrieWalkCost.lean` | Kernel checked actual parser rejects empty extensions; successful lookup touches at most twice byte key length plus terminal node and optional value, with no witness-shape premise |
| Original-context sufficient-gas matching | `Skeleton/SuccessCost.lean` | Exact loading/opcode/four-host cost includes return-data receipt fees; original gasLimit gives credits, matching and used-gas bound without a stake/read-width premise |
| Symbolic empty-storage cost and total success gas | `Skeleton/{EmptyCost,SuccessGas}.lean` | Original-cost-table formula and used-gas bound with retained credits, loading, activation and receipt observation kernel checked; universal model bound remains open |
| General canonical all-resource refinement | `Skeleton/{CanonicalInputFailures,CanonicalOutputFailures,CanonicalFailureBounded,CanonicalArithmetic,CanonicalAllLimits}.lean` | Every pointwise refinement clause for arbitrary canonical storage and all resource/stake branches; no per-call prospective usage-room or accepting-limit premise; static protocol growth/read bounds, preparation, node exclusion and actual proof acceptance explicit |
| Unrestricted `Refines` | — | Open; all-resource general canonical pointwise clauses now checked; node/proof/protocol certificate obligations and SAF-67 remain |

The walking module uses `input`, `storage_write`, `log_utf8` and
`value_return` through the actual NEAR metered runtime and receipt boundary.
The harness tests both kinds of budget edges: varying the burn cap with
prepaid gas fixed, and varying prepaid gas with the protocol fixed. It checks
exact deterministic resource failures, invalid methods, storage-stake rollback,
and log prefixes. Neither those tests nor a parameterized `ContractModel`
constitute a universal refinement proof.

**Frontier:** certify the preparation, read-cost and growth bounds for the
pinned protocol; repair the recorded-proof-size input contract (SAF-67); resolve
reserved-zero node exclusion without an added cryptographic or WF assumption.
Actual canonical raw agreement, complete metered writes, context-only gas
bounds, fixed-context funded references, body/receipt replay and every pointwise
refinement clause now cover all resource branches over general canonical
storage. Native write room is derived from shared WF and a protocol-only growth
bound exactly where value validation accepts. Deployed wNEAR method contracts
(M3) and unrestricted `Refines` remain beyond this walking-module result.

Prepared validation and instantiation now cover arbitrary positive configured
memory sizes within the Wasm limit. `Memory` proves the exact key/log byte reads
without expanding zero-filled pages. `Startup` connects the actual `runAttempt`
pipeline to the prepared body; `Success` composes all fifteen opcodes and the
four actual hosts, leaving storage's local invocation/gas evidence explicit. `Execution` now
connects this to actual VM success, with the post-storage empty-promise
invariant explicit. `Fuel` discharges the default interpreter fuel requirement.
`SuccessExecution` now proves the actual public `execOn` success branch matches
the independent model step, using local storage, representation, accounting and
resource conditions. `StorageCredits` derives the exact reservation at the
storage call from original total credits. `EmptyStorage` instantiates that
frontier on a globally empty canonical base with no selected overlay key,
retaining the explicit proof-size check. `EmptySuccess` derives all storage
postconditions and proves receipt/model matching for that original-data slice.
`EmptyCost` derives its eight ordered storage precharges and symbolic cost.
`SuccessGas` proves the actual public run and receipt observation use no more
than the total execution budget, retaining residual credits; the observation
bound includes later boundary failures. `StorageFailure` closes the independent
key-length model failure with loading plus sixteen regular opcodes and exact
pre-value-read host charges. The value-length failure is now also lifted through actual public execution.
`LogFailure` proves count rejection after the completed write using the local
storage frontier/frame. `EmptyStakeFailure` handles both storage-stake outcomes.
`SuccessCost` derives a context-only sufficient cost (including each return-data
receiver) and matches/bounds the empty-base receipt directly from gasLimit; its
read-width check follows from gas coverage and WF, and no zero-deficit premise
is needed. Its upper-bound variant reserves the storage/output prefix even when
the return-length check rejects. `EmptyFailures` consequently derives actual
empty-base log-count and log-length rejection directly from original WF,
limits and gas coverage, retaining proof-size acceptance but no local storage
callback, return acceptance, usage-room or stake premise. `ReturnLengthFailure`
proves the final host rejection through public receipt matching, retaining the
saved log. `FailureCosts` bounds all three pre-storage rejection budgets by the
same original-data cost, without WF or trie assumptions.
`StorageFailureGas` additionally bounds actual receipt gas for key and value
rejection, including loading and activation. The combined
`execOn_empty_matches_modelStep_allLimits` matches every resource-limit and
stake branch under that one sufficient-gas bound, with original WF,
representation, preparation, empty base/absent key, usage room and proof-size
acceptance explicit. `OutputFailureGas` derives all remaining output-failure
used-gas bounds, and `EmptyBounded` assembles matching plus that bound for every
resource and stake branch. Its finite-set bridge is the actual RuntimeInterface;
`sufficientGasModel` chooses the proved cost as its gas field and supplies the
exact sufficient-gas implication for this explicitly restricted slice. The
lower-gas alternative is now assembled below. The canonical cost bound and
all-resource pointwise result are checked below; unrestricted refinement
still needs the explicit node, proof and protocol obligations discharged.
`ModelSafety` proves matched model branches cannot report interpreter limitations.
`InvalidMethod`
closes the complete unparsed-input clause without WF or gas hypotheses.
`TrieBranchConstructionLookup` connects actual branch construction to lookup;
`TrieWitnessTransfer` transfers an isolated child traversal through its actual
parent witness segment, with compatible aliases and ancestor safety explicit.
`TrieConstructionInvariant` discharges alias compatibility from the actual
public constructor collision loop. `TrieWitnessFuel` transfers the exact
successful raw lookup to the deduplicated final witness at its reduced default
fuel. `TrieNodeRank` supplies node-only ancestor descent using actual u64 usage
suffixes and strict parent/child usage; arbitrary value objects need not be
excluded. `TrieConstructionRanks` now proves that successful actual recursive
construction produces the ranked node certificate, including every selected
child from the actual branch loop. Every certified descendant has an actual
serialized binding and a bounded rank, with transport through final witness
deduplication. The decoded traversal is now connected to that certificate by
`TrieRankedLookup`. `TrieReadableConstruction` derives its readable tree from
actual constructor success, and `TrieEntryLookup` proves reference-only public
lookup agrees with the original byte-key entries. These proofs cover all
recursive node shapes and deduplicated witness fuel. Reserved-zero node roots
remain an explicit premise. `TrieEntryDereference` now retains original value
objects through actual recursion and collision-checked deduplication, derives
exact fetches, and proves full public lookup returns original byte-key values.
Value hashes need no nonzero premise. `TrieCanonicalLookup` connects these
constructor results to actual overlay reference/dereference operations and
materialized-view bytes, eliminating the base-lookup correctness callback.
Canonical build, unique overlays and explicit nonzero-node evidence suffice;
the shared WF predicate is unchanged.
`TrieCost` lifts successful lookup/dereference access bounds to the actual
cumulative counters and metered charges: at most 2n+1 reference-node touches
and one value touch, billed at no more than the larger original node price.
`BudgetSimulation` dispatches every actual body position, proves a closed
control/stack/installed-metadata invariant and log monotonicity for all actual
fuel prefixes. Enlarging internal counter limits preserves the complete guest
context. `Progress` additionally proves exact one-step source phase advancement and
excludes fuel exhaustion after sixteen body transitions for every gas amount,
including host/trie rejection. Activation charges preserve that structural bound.
`FunctionalInvariant` now closes those resources on every actual error-free
continuing step: nonview/fresh markers, original pre-write trie/configuration,
prepared memory, and register zero after input. Actual returning storage writes
supply the full frame, not a projected semantic callback. The actual validator
supplies the key bound before primitive readiness is required, so even rejecting
key limits fit this simulation. Runner charge errors use the gas alternative
immediately. Concrete `stepSimulation`, `runSimulation` and initialized-machine
comparison now give a whole-body matched-or-gas alternative with prefix logs
and no fuel error, allowing only internal counter limits to differ.

`StartupSimulation` now connects actual loading and activation to the body
simulation, including startup gas failures and the structural fuel bound.
`NearRuntime.BudgetObservation` transports matching and gas failures through
actual receipt checks and observation. `ReceiptSimulation.execOn_replay` therefore
proves that actual `execOn` equals its funded reference observation, or returns
out-of-gas with rollback and logs prefixing that reference observation. It needs
no sufficient-gas premise on the original execution.

`FundedEmpty` proves the funded body succeeds with the original guest context
fixed, under explicit resource acceptance and protocol arithmetic room.
`FundedObservation` now derives final storage representation and usage, proves
its actual checked reference matches the independent model for both stake
outcomes, and combines the two: `execOn_matches_or_gas` proves actual execution
matches the model or returns out-of-gas with rollback and a prefix of the model's
logs, for any original gas budget. `EmptyRefinement` transports this to the
exact finite-set runtime and assembles every clause appearing in `Refines` at
a context/storage point, including no interpreter limitation and invalid-call
rollback. It also derives the equivalence between original and storage-paid
recorded-proof checks. `FundedInputFailures` and `FundedOutputFailures` now
derive actual funded input/key/value and log-count/log-length/return-length
rejections with the same original guest context. `EmptyRefinement` combines
these branches, so no resource limit is assumed to accept. This is the
empty-base slice, with original WF/representation, preparation, native usage
room, read-cost width, absent key and recorded-proof acceptance explicit. The arithmetic premise must eventually
follow from certified pinned-protocol facts independent of the low context's
gas. Canonical all-resource assembly and recorder repair also remain open.

The canonical specialization now removes both the empty-base and selected-key
restrictions for accepted-resource calls. `TrieCanonicalStorage` derives exact
raw-list presence and dereferenced bytes from original WF and canonical reads.
`StorageCanonical` computes the actual ordered lookup/dereference plan and proves
both preparation and complete metered writes for fresh and replacing cells.
`TrieCanonicalCost` bounds cumulative node/value accesses; `StorageCanonicalCost`
bounds phase charges and the replacement register bill by original-context data.
`StorageModelUsage` proves final raw storage and model usage for both cell branches.

`CanonicalBody` derives the actual storage frontier and full sixteen-step body WP
from those facts. `CanonicalCost.saveCost` adds original-account/key node charges,
evicted-byte charges and replacement-register charges to `saveEmptyCost`; it
reads no execution, cache or old value. `CanonicalObservation` proves the actual
funded reference matches the model for either stake outcome. `CanonicalReady`,
`CanonicalSimulation` and `CanonicalReceiptSimulation` derive arbitrary-gas
whole-body and actual public receipt replay without empty-base assumptions.
`CanonicalBounded` proves sufficient original gas gives actual model matching
and used gas at most `saveCost`, including startup. `CanonicalRefinement` assembles
every pointwise `Refines` clause for the exact finite-set runtime on this
accepted-resource canonical slice.

`CanonicalInputFailures`, `CanonicalOutputFailures` and
`CanonicalFailureBounded` now extend actual funded-model agreement and the
original gas bound across every resource rejection on general canonical storage.
`CanonicalAllLimits.nearRuntime_refinement_clauses` assembles every pointwise
`Refines` clause without an accepting-resource, empty-base or selected-key
premise. `CanonicalArithmetic.GrowthRoom` is the protocol-only inequality
`1 + maxLengthStorageValue + numExtraBytesRecord ≤ maxGasBurnt`.
Shared WF and this inequality derive native usage room only in the final
accepted-value branch, so huge inputs rejected earlier need no prospective
write-room assumption.

The strongest result retains explicit `NonzeroNodes`, preparation, protocol
read-cost/growth bounds and recorded-proof acceptance on the **actual fetched
plan's staged write**, including warmed accounting/cache state. The arbitrary
proof observer is not assumed invariant under reads. Shared WF and operational
runtime behavior were not changed to make these premises true; the protocol
inequalities were not claimed as kernel-certified facts of the opaque JSON pin.

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
reserved-zero obligation remains open; recursive reference construction, traversal
and witness proofs are now checked subject to it.

The runtime currently does not enforce `maxNumberRegisters`; the skeleton
pins this observed limitation explicitly. Register-size limits are enforced.
This does not affect the default configuration's one-register example, but
must not be described as nearcore conformance for arbitrary register limits.

Validation for the walking-method checkpoint (2026-10-27): 130 proof modules were checked
transitively for axioms (5336 declarations, 3836 theorems, zero violations).
Standard Lake builds, the walking-skeleton checks, and blueprint
extraction/rendering pass. The full wNEAR audit covers 129 modules, 6244
declarations and 3443 theorems, permitting exactly the original refinement
module's open proof and its two dependent theorems. After merging latest main (including the Lean LSP skill and new stress
cases), all 56 differential scenarios pass. The earlier unchanged operational
baseline has all five builtin harness contracts and 211 adapter checks passing;
those two suites were not rerun. Lean LSP MCP diagnostics and axiom verification
pass for the startup, checked receipt replay and canonical reference lookup
theorems, including general canonical metered/body execution, model
observations, original-context gas bounds and all-resource canonical pointwise
refinement clauses, with protocol growth replacing per-call write room.
Both audits include this increment. The 56-scenario result is
from the preceding synced-main checkpoint; no runtime behavior changed here.

During the latest increment the original host checkout and its shared Git/cache
paths disappeared. Source work and pushes were preserved using isolated Git
metadata for the same PR branch. New modules were compiled directly by the
pinned Lean version using cached dependencies whose revisions all match the
package manifests; transitive audits use the unchanged `axiom-audit.py` script
generator with that explicit dependency path. The worktree cache link has since been redirected to that verified cache,
and standard Lake builds, skeleton checks and blueprint extraction/rendering
run again. Git registration remains broken; only source discovery uses isolated
Git metadata, while dependency Git operations inherit their normal environment.
The full audit uses the unchanged audit generator and normal Lake execution.
No operational code changed.

**Kernel protocol-pin obstruction:** `RuntimeConfig.parse` calls
`Lean.Json.parse`, whose `anyCore`, `objectCore` and string parser are opaque
`partial def` declarations in Lean 4.34.1. Even the closed proposition
`(Lean.Json.parse "{}").map (fun _ => true) = .ok true` fails kernel reduction.
Thus numeric facts about `wNearProtocolJson` cannot simply be certified by
`decide +kernel`; increasing heartbeats does not help. The relevant width
property `1 + maxLengthStorageValue + numExtraBytesRecord ≤ maxGasBurnt` is
arithmetically true for the native pinned JSON, but no kernel certificate was
claimed. A verified parser/certificate interface or a reviewed protocol pin
repair remains necessary; no compiler-trusted reduction or extra axiom was
introduced. Existing conditional protocols/resources remain explicit.

### M3. The first method, top-down

`ft_total_supply`, or another small view: its contract, proved from sorried
contracts of every function it calls, then those leaves proved. This fixes
the contract shape of 3.2, the first representation predicates and the
first automation.

*Exit:* one exported method's `Refines` clauses proved with no `sorry`.

Verified deployed-code targets (2026-10-27): `ft_total_supply` exports function
296, whose direct callees are 522, 520, 219, 155, 414, 96, 158, 779, 545,
and 68 twice. Function 414 calls only 566. Function 566 has type
`[i32, i64, i64] → []` and six instructions: store argument 2 at output+8,
then argument 1 at output. It has no calls or global accesses. Its
contract now owns a writable 16-byte output region and specifies both
little-endian stores, the outside-memory frame, normal void completion,
and exact body gas/residual credits. `Binary.StorePair` kernel-checks its
actual decoded body and signature. `Proofs.StorePair` proves the active-body
contract with arbitrary operand prefixes, caller frames and continuations;
its terminal specialization takes seven transitions, including free leave.
`NearVM.MeteredMemoryRules` supplies the bounds-based metered store rule.
`Proofs.StorePairEntry.invoke` composes actual `Exec.startWasm` activation
and `runInitialized`: with the installed typed-function/module/memory
lookups, in-bounds memory and sufficient credits, it returns void normally,
charges exactly 17 regular-operation units, retains residual/promise gas,
and preserves the body contract's memory and host frame. These are local
callee premises; no whole deployed-module instantiation theorem or complete
exported-method refinement is claimed.

The executable contract was validated before the semantic proof: 936 valid
calls pass, including 16 captured calls and unaligned, cross-page, boundary,
bit-pattern and random cases. Every call costs 17 regular-operation units
(11 activation plus six body instructions), or 13,986,852 gas under the
harness configuration. Three executed out-of-bounds probes fail as expected.
Six malformed-argument cases check contract preconditions only: raw
`Exec.startWasm` assumes caller-validated argument shape and may panic on
malformed locals. The complete builtin harness also passes: memcpy 713,
memset 153, bcmp 120, multi3 258 and allocator 301 calls.

The contracts for both 414 and 779 retain sequential aliasing semantics without
a separation premise. Next compose the remaining getter calls. The state-read
path uses `STATE` at address 1049788; SDK vtable dispatch, Borsh decoding,
JSON formatting and `value_return` remain real obligations of the top-level
getter.

`Binary.PackWords` pins f779's actual eight instructions. Its first load reads
source+8 and writes output+4; its second load reads source from the updated
memory and then writes output. `Harness.PackWords` validates that sequential
meaning over 411 cases, including 226 captured calls and three calls from
`ft_total_supply`, at exactly 17 operation units (nine activation plus eight
body). The final integrated harness passes all eight contracts, 3207 checked
inputs and 1000 captured calls. All 2906 non-allocator cases have exact gas;
the 301 allocator cases meet their conservative bound.
`Proofs.PackWords` now proves the actual body with arbitrary operand prefixes,
caller frames and continuations, followed by normal void completion at fuel
nine. Its memory contract retains the sequential overlap behavior and an exact
eight-byte footprint. `Proofs.PackWordsEntry.invoke` composes actual typed
activation and execution at exactly 17 operation units, with residual/promise
gas and the functional store/host frame preserved. Installed typed-function,
module and memory lookups, writable bounds and credits remain explicit local
callee premises. No exported-method refinement is claimed by these leaves.

The immediate caller now has executable validation too. `Binary.StorePairCaller`
checks f414's actual 29-instruction body, two declared locals and sole call to
566. `Harness.StorePairCaller` passes 315 calls (314 generated plus one captured
from `ft_total_supply`) at exactly 57 operation units: own activation 11,
own body 29, nested activation 11 and nested body six. Output, source and the
16-byte shadow-stack slot may overlap; the postcondition follows the actual
snapshot-to-scratch-to-output sequence. All globals, including the stack
pointer, are restored. Four executed memory/stack failures and five malformed
argument prechecks behave as expected. The full integrated harness passes.
`Proofs.StorePairCaller` now composes all 29 caller instructions, actual f566
entry/body/leave, and the final void return. The active body costs 46 units
and returns normally within 37 interpreter transitions. Its arbitrary-caller
contract retains the operand prefix, caller frames and enclosing labels.
`Proofs.StorePairCallerEntry.invoke` composes actual typed f414 activation and
this body: exactly 57 operation units, residual/promise gas, restored globals,
sequential scratch/output memory and all functional host resources. Source,
output and scratch may overlap. Installed function/module/global/memory facts,
the memory's 32-bit size bound, valid stack/output/source ranges and sufficient
call depth/credits stay explicit. `Memory.wf` alone does not imply that size
bound. This is a local callee contract, not a whole-module instantiation proof.

The accepted branch of deployed f158 (`Result::expect`) is now validated and
proved through actual entry and normal return. Its discriminant must differ
from one; the panic branch is outside this contract. The first copy reads eight
bytes at source+4 into output, then the final word is read at source+12 from
the updated memory and written at output+8. Source/output may overlap. The
stack pointer is restored modulo 2^32 with no lower-bound premise: this branch
never accesses its scratch slot. Its cost is exactly 36 operation units
(10 activation and 26 paid body instructions); the block instruction is free.
The integrated harness now passes nine contracts on 3429 checked inputs,
including 1007 captures. All 3128 non-allocator cases have exact gas, and 301
allocator cases meet their bound. The f158 subset contains 222 calls,
including overlapping outputs and wrapping stack pointers.

`Proofs.TotalSupply` now composes all 76 actual f296 instructions under eleven
named local callee contracts, explicit computed scalar-store boundaries and
structural memory/global/local invariants. `wp_body` admits an arbitrary code
continuation; `run_return` derives normal root return to the concrete final
store. No whole-body success equation or pure-instruction execution callback
is assumed. `Proofs.TotalSupplyEntry.invoke` adds actual typed initialization
and nine activation units: the total budget is 74 ordinary units plus the
sum of the eleven complete local call budgets. These local callee and
representation obligations remain open; this conditional body theorem does
not establish exported-method refinement.

`Binary.ImportLayout` proves actual metered resolution succeeds for all 48
imports and arbitrary configurations. `Wasm.LinkFunctionLookup`, host allocation
and `Binary.InstalledCallees` derive the concrete installed function addresses
and module slot from successful validation/linking. `Proofs.LoadedCallees`
connects these facts to all four proved callee invocation contracts and the
conditional getter invocation. Its installed-code invariant survives changes
to memory, globals and host while functions/modules are retained. Prepared
module validation and successful instantiation remain explicit; no whole-module
validation certificate has been established. An expensive direct candidate
was canceled and removed without accepting its result. The reusable checked
`Wasm.ValidateMemoryInvariant` instead proves actual instruction/body and
constant-expression validation is unchanged when memory counts agree, and
checks configurable memory limits from explicit page inequalities.

`Proofs.TotalSupplyCallees` now constructs the actual local call contracts for
three of the eleven sites: f414 (58 units, 38 steps including nested f566),
f158 accepted branch (37 units, 29 steps), and f779 (18 units, 10 steps).
These costs include the caller's opcode, unlike their root invocation costs.
They derive actual call, activation, body and free caller return, with installed
code corollaries. The eight remaining wrapper call sites still need contracts.
`Proofs.TotalSupplyBudget` derives burnt/used-gas bounds from the original store
and residual credits for the conditional complete getter, and carries the
local model-return/storage effects through its concrete final epilogue.

The loader/body checkpoint has a strict transitive audit of 162 modules,
6605 declarations and 4900 theorems with zero violations. The normal Lake
committed-source audit at that checkpoint includes 155 modules, 7126
declarations and 4126 theorems, tolerating exactly the original three
refinement-dependent declarations. The later budget/call-site adapters passed
MCP diagnostics/trust checks and focused builds; those two checkpoint audit
counts precede their addition.

`Proofs.TotalSupplyFrontier` integrates those three actual call-site proofs:
`RemainingCalls` contains exactly eight open execution contracts, and helper
resources contain installed code, local memory/global bounds, accepted tag
and concrete post-store equations. `invoke` and `gas_bounds` use this reduced
frontier; no three hidden callee-execution callbacks are included in resources.

`Binary.PreparedValidation` now proves actual prepared-module validation is
identical to original-module validation whenever initial pages ≤ maximum
pages ≤ 65536. It kernel-checks the original single memory declaration and
uses the generic structural invariance proof; success still requires the
original whole-module validation certificate. No 907-body reduction result
was accepted.

The terminal trait implementation f260, reached below the SDK's value-return
wrapper, now has a checked actual host-backed contract. Its three instructions
forward the two i64 arguments to deployed import20; actual resolution,
allocation and linking derive that import's metered `value_return` descriptor
and address. `Proofs.LoadedValueReturn.invoke` discharges both Wasm-method and
host-table lookups from the installed-code invariant. Exact root cost is
14 ordinary units plus the original host's base, memory-read and data-receipt
fees. The proof derives host execution from a fixed in-bounds span, return
length limit and credits, clears an earlier promise return, preserves all
memory and frames functional resources. Register-sentinel lengths are excluded.
`Proofs.ValueReturnValidation` is a reproducible executable check: 12 calls,
including seven captures and five fixtures with both same-account and other
return-data receivers, all match returned bytes and an independent exact-gas
formula. The `ft_total_supply` capture returns 26 bytes at exactly 2984984553
gas. This does not discharge f545/f456's thread-local, RefCell, vtable dispatch
and cleanup; the eight-wrapper-call frontier remains explicit.

The final M3 assembly/host checkpoint's strict transitive audit covers all
173 proof/support modules: 6953 declarations, 5140 theorems, zero violations. The
full working-tree audit covers 165 modules, 7415 declarations and 4317 theorems,
with exactly the three original refinement-dependent `sorryAx` declarations
tolerated and no other violations; its normal Lake build passes 1316 targets.
The focused final builds and Lean LSP diagnostics/trust checks pass for the
entry, actual local-call adapters, reduced frontier, original-store budget,
prepared-validation transport and loaded host-backed leaf. Blueprint
extraction/rendering passes (1451 targets). The integrated nine-contract
harness and the separate 12-case host-dispatch validation both pass; no
operational behavior changed.

The preceding three-callee checkpoint's strict transitive audit includes 147 modules,
5814 declarations and 4246 theorems with zero violations. LSP verification of
all entry/body code facts and contracts uses only the standard axiom basis.
The full working-tree audit covers 144 modules, 6634 declarations
and 3741 theorems, permitting exactly the original three refinement-dependent
`sorryAx` declarations. Normal Lake builds pass (1289 targets in this audit),
and blueprint extraction/rendering passes (1430 build targets). Both audits
include all three actual invocation contracts. No interpreter behavior changed.
The reusable rules now include actual direct Wasm call/return, entry activation,
local tee, global access, wrapping i32 arithmetic and bounds-derived i32/i64
loads and stores. The caller-state module separately proves the intended
46-unit body charges, global restoration and sequential memory footprint;
body execution is established separately by the instruction composition.

Actual `__multi3` (global index 954, local function 906, type index 8) is
another validated builtin frontier: 60 straight-line instructions, no calls
or loops, two i64 stores. The existing harness checks its modulo-2^128 product
contract and 80 regular-operation units (20 activation + 60 body; caller call
opcode separate). Kernel proof is still required: first symbolic execution,
footprint and exact gas, then the 32-bit limb/carry arithmetic connecting
its stored words to multiplication. These are executable/code facts and
proof targets, not a completed metered function contract.


Earlier M3 checkpoint: the actual accepted f155 `unwrapState` call is now
proved through its real f951 byte-copy loop, typed result and final drop.
The positive-count f951 call costs `(18*n + 17)` operation units and takes
`17*n + 12` steps, including caller opcode, activation and return; at forty
bytes this is 737 units / 692 steps. Root invocation costs 736 units and
requires exactly 691 steps. f155's complete local call costs 754 units /
702 steps (root 753 / 701). All source/output aliasing follows sequential
forward reads/writes. Native bounds, width, nonzero state tag, installed code
and depth remain structural premises. The executable unwrap suite passes 244
inputs including an initialized getter capture, five ABI prechecks and three
executed failure probes; exact fuel-boundary probes pass for both functions.

`TotalSupplyFrontier` now integrates four actual helpers and contains exactly
seven remaining local execution contracts: panic hook 522, interface setup 520,
state read 219, serialization 96, value return 545 and two vector drops 68. Its
helper resources contain no execution callbacks. Actual entry/body/return and
original-store gas bounds remain proved under that reduced interface.
`UnwrapStateCopy{State,Memory,Gas,Effects}` prove residual credits, exact loop
burn/reservations, unchanged caller/resource frames, the sequential memory
footprint and original-word preservation for disjoint ranges.
`UnwrapStateEffects` and `TotalSupplyRepresentation` derive the unwrapped,
copied and serializer-input U128 representations from the actual memory
operations, including wrapping pointer arithmetic.

The actual ten-instruction f456 dispatch fragment is now composed through
its real table call, f260 host method and saved-caller return: 24 ordinary
units plus concrete host fees, fourteen steps. Its seven captured-state tests
pass exact bytes, gas, memory and caller stack/frame checks. The loaded-code
bridge derives both Wasm/host descriptors and the original type vector;
table entry and memory-layout facts remain explicit. Kernel facts pin the
actual data word at vtable 1050188+92 to table index 58 and the active element
entry to f260; these are source facts, not an instantiation success theorem.

The real f430 nonnull path, f433 zero-status cleanup, f672 word swap and
f431 release through its nested f672 call now have normal-path proofs.
They retain resource frames and exact ordinary charges; f433 restores any
wrapping stack pointer. Reproducible validation covers 1262 captures across
six borrow helpers plus eight boundary fixtures. f429/f494 acquisition,
thread-local entry and the enclosing f456/f545 assembly remain open.

`Wasm.ValidateCertificate` factors the actual validator into static prelude
and per-function checks with kernel-checked composition. f566 has the first
bounded actual function-check certificate. Static type/import/function-table,
initializer and export checks are now certified independently of function
bodies and data payloads in `Binary.ValidationPrelude`. Whole-prelude assembly and the remaining 906 body
certificates remain open. A resource-heavy assembly candidate was removed;
its result is not accepted as a validation certificate.

This checkpoint uses the synced Lean LSP MCP skill for proof iteration.
The final strict transitive audit covers 204 modules, 7942 declarations and
5876 theorems with zero axiom violations. The normal Lake build passes 1347
jobs; blueprint extraction and rendering pass after 1468 build jobs.
The full working-tree audit covers 190 modules, 8286 declarations
and 4981 theorems, with exactly the original three refinement-dependent
`sorryAx` declarations and no additional violations. All new principal proofs
use only standard axioms; no operational runtime/model/WF changes are included.

The next M3 stage connects one decoded supply premise through all three
actual unwrap/copy/serializer-input boundaries (`TotalSupplyDataFlow`). The
actual initialized thread-local lookup is proved through f565 and f468,
including its type-1 indirect entry: 29 ordinary units and fifteen steps as
an indirect call. f468 returns its pointer+4 only after its actual status-one
load and comparison; the lazy f467 route remains outside this contract.
Captured validation checks 178 initialized calls each for f468/f565, exact
17/28 root operation units and 10/14 root steps. Twelve lazy captures per
function are counted separately, not included as accepted cases.

Actual f494 increment and f429 acquisition now include their real nested
f672 swap, signed guard and panic-skipping branch. The complete f429 local
call costs 72 units and 47 steps; sequential counter/borrow-record writes,
exact residual/promise credits and stack restoration are checked. Generic
select, bitwise-or and two-block exit rules support outer composition.
Successful loading derives both slot116→f565 and slot58→f260 in the same
actual initialized table. A table-preserving loaded-code invariant is
required after guest execution; code-only installation cannot imply table
contents. The f545 scalar slice setup now executes its actual six-instruction two-store
sequence and four argument instructions, and its actual memory writes establish
both zero-extended dispatch words and the complete outside-byte frame.

Separate whole-path capture checks cover seven f456 calls and seven f545
calls. They check exact returned bytes, gas, fuel boundaries, unchanged
storage usage, no returned promise and restored SP: f456 root247 ordinary
units plus host fees/160 steps; f545 root277 plus host fees/181 steps.
The accepted f456 body is now kernel-proved through the actual full chain:
237 ordinary units plus the concrete host fee, 159 active steps, and exact
residual credits. The two free block entries, typed nested returns, branch
out of both blocks, f433 status check and SP restoration are included.
`ValueReturnOuterPrefix`, `ValueReturnOuterBody`, `ValueReturnOuterDispatchTail`
and `ValueReturnOuterCall` split the computation into cached kernel theorems;
no callee execution callback remains in this accepted body. Actual local f456 entry and typed return are also proved: 248 ordinary
units plus the original host fee, 161 steps. The full f545 call now executes
its actual prefix, this actual f456 call and its epilogue: 278 ordinary units
plus `ValueReturnHost.cost` of the original host and dispatch length,
182 steps. `ValueReturnWrapperCall.calleeContract` has only initial heap/code
resources and layout ties, with no assumed post-store module/global lookup.

`TotalSupplyReturnFrontier` integrates the actual full f545 call. The getter
now has exactly six remaining local execution contracts: panic hook522,
interface setup520, state read219, serialization96, and the two vector drops68.
Five helper implementations are supplied internally (155/414/158/779/545).
Actual exported entry/body/return and original-store gas bounds remain checked
under the six-call interface and explicit scalar/representation resources.
Five redundant readiness fields (four computed memory lookups and the u64
sentinel inequality) were removed and replaced with derived lemmas.

`LinkDataLookup` and `LoadedValueReturnData` derive the two initialized memory
words (1050280→58, 1055020→116) from successful loading, retaining the 26 KB
initializer symbolically. Code-frame lemmas preserve the loaded table facts
through the known memory/host phases. `ValueReturnOuterLayout` derives the
actual borrow record and selected pointer and retains words outside the
counter/scratch footprint. Full payload equality with the original input is
proved in `ValueReturnPayloadFrame` under explicit span disjointness from
both scratch regions and the counter. The operational postcondition always
uses actual dispatch memory; original payload equality is not assumed under
arbitrary aliasing.

Final audits for the six-call checkpoint: strict transitive coverage of
241 modules, 9180 declarations and 6821 theorems with zero violations; full
working-tree coverage of 224 modules, 9373 declarations and 5811 theorems,
tolerating exactly the original three refinement-dependent `sorryAx`
declarations. The normal Lake build passes 1384 jobs and blueprint extraction/
rendering passes after 1478 build jobs. Principal new contracts, composition,
loader and frame theorems pass Lean LSP MCP verification with standard axioms.
No operational runtime, model or WF changes are included.

The next interface-installation checkpoint keeps the frontier at six contracts.
Captured first calls to f520/f463 have thread-local status zero, so the existing
status-one lookup contract cannot close this actual installation site. A separate
60-capture suite checks all twelve lazy calls each to f463, f467, f468, f520 and
f565, including installed receiver/vtable, initialized status, released counter,
exact gas and the one-less-fuel failure boundary. Root costs/steps are respectively
314/220, 81/64, 99/74, 327/225 and 110/78. These executable checks do not constitute
a complete lazy-path theorem or enlarge the integrated nine-contract harness.

`InterfaceInitialize` proves the actual type-0 table106 call to f564: thirteen
ordinary units and five steps, including activation and typed return. Successful
loading supplies the actual table entry and descriptor. The initializer writes
exactly eight zero bytes; the following scratch word remains its original value.
`InterfaceLazyBody`, `InterfaceLazySaved` and `InterfaceLazyFinish` prove the actual
f467 payload exchanges, status publication, sequential old-record writes and
complete thirteen-step result/old-status-zero/restore48 tail. Bounds and real
sequential reads remain explicit, retaining aliasing and wrapping arithmetic.
`InterfaceLazyPrefix` closes the two real argument loads and the actual
initializer call at fifteen units/seven steps, with derived memory, resource
and residual-credit facts. Full f467 composition and the lazy f468/f565 caller
adapters remain to assemble.

`InterfaceStack` generalizes the existing reserve/restore rules to any wrapping
UInt32 allocation amount. `InterfaceInstall` proves the real f464 empty-record
guard, its fourteen-unit/seven-step full local call, and exact adjacent
receiver/vtable writes. The nonempty-record drop branch still calls unproved
f465. `InterfaceSetBody`, `InterfaceSetPrefix` and `InterfaceSetInstallTail` prove
the setter's scalar stores, reserve32/save-arguments prefix and complete
23-step/thirty-unit borrow-copy/guard/install capsule. These are deployed
instruction proofs, with semantic continuations only after each complete phase;
no guest-execution callbacks or new axioms are introduced.
`InterfaceSetReleaseTail` closes its actual 47-step/seventy-one-unit release,
status-reset, two-block exit, f433 check and restore32 tail, including real
f442/f672 calls. `InterfaceBorrowState` proves the full exclusive release call
at thirty-six units/nineteen steps. `InterfaceBorrow` closes actual f492
exclusive acquisition through f672 at thirty-nine units/twenty-four steps as a
local call, plus f441's zero-counter/nonzero-pointer guard and sequential
record writes. Complete f441 composition remains open; its unverified trial
was withdrawn from project sources. Separate captured checks cover twelve f441,
twenty-three f442 and twenty-three f492 calls at their exact root costs.
An independent review of the lazy phases found no discrepancy in instruction
order, wrapping arithmetic, aliasing or the scope of the empty-status guard.

Final audits for the interface-phase checkpoint: strict transitive coverage of
264 modules, 10086 declarations and 7529 theorems with zero violations; full
working-tree coverage of 247 modules, 10201 declarations and 6441 theorems,
with exactly the same three original refinement-dependent `sorryAx`
declarations. The full source build passes 1407 jobs; blueprint extraction
and rendering pass after 1488 jobs, and the rendered six-call frontier was
checked. All new principal contracts pass Lean LSP MCP standard-axiom checks.
The full refinement goal remains open; no runtime, model or WF changes are made.

The following composition checkpoint closes actual first interface installation.
`InterfaceBorrowAcquireTail` and `InterfaceBorrowAcquire` compose real f441:
59 ordinary units/45 active steps and 71 units/47 steps as a full local call,
including actual f492/f672 exclusive acquisition, record writes and restore16.
Small generic store/continuation lemmas avoid expanding the whole concrete
state during kernel checking; they do not assume successful guest execution.

`InterfaceLazyComplete` proves the entire deployed f467 old-status-zero body:
70 units/63 active steps, including reserve48, the actual f564 indirect
initializer, sequential payload/status/old-record writes and normal return
preparation. `InterfaceLazyCall` adds typed call entry/return: 82 units/65 steps.
`ValueReturnLazyLookup` proves the actual lazy 565→468→467→564 chain from the
real status load, through the early return: 111 units/79 steps as an indirect
call. Its exact final memory, restored global array and code/table frames are
derived in `ValueReturnLazyFrame`; no post-call array lookup is supplied.
`InterfaceLazyNative` derives the lazy bounds and empty-old-state condition
from initial well-formed, width-bounded memory, cell/scratch spans, separation
and initial status zero. `InterfaceLazyReadback` derives final status one,
zero counter/receiver words, well-formedness and unchanged memory size/max.
It retains the untouched scratch word used for the third interface word.

`InterfaceSetCore` proves the complete actual 125-step/180-unit suffix using
an arbitrary post-lookup heap. `InterfaceSetLazyBody` composes setup, actual
lazy lookup and that suffix: 304 units/219 active steps; the full typed f463
call is 315 units/221 steps. The initialized alternative remains separately
proved at 222 units/155 active steps and 233 units/157 call steps. The real
f520 wrapper is now proved in `InterfaceInstallCall`: 318 units/224 active
steps and 328 units/226 steps for the complete local call. Its resources
contain original structural conditions and native/data predicates on the exact
sequential memory, without a callee-run or computed-array oracle.

`TotalSupplyInterfaceFrontier` supplies this actual f520 call alongside the
five previous implementations. The getter now has exactly **five remaining
local execution contracts**: panic hook522, state read219, serialization96,
and the two vector-drop68 sites. Actual entry/body/return and original-store
gas bounds remain checked through this five-call interface. Installed-code,
scalar/native/representation resources and whole-module validation remain
explicit; no complete exported-method refinement is claimed. An independent
review of full441, lazy lookup and both setter paths found no semantic defect
and reconciled the proof counts with the captured gas/fuel boundaries.
`InterfaceSetLazyNative` additionally derives initial saved-memory status and
lazy lookup bounds, plus post-lookup well-formedness, size and zero counter/
receiver words. Full `InterfaceSetLazyState.Bounds` still retains the later
record-copy and release-pointer data predicates; this constructor is not
claimed to discharge every setter obligation.

Final audits for the five-call checkpoint: strict transitive coverage of
294 modules, 10991 declarations and 8229 theorems with zero violations; full
working-tree coverage of 277 modules, 11074 declarations and 7109 theorems,
with exactly the original three refinement-dependent `sorryAx` declarations.
The full source build passes 1437 jobs. Blueprint extraction/rendering passes
after 1488 jobs, and the rendered current five-call frontier was checked.
Principal new call, memory and frontier theorems pass Lean LSP MCP standard-
axiom verification. No runtime, model or WF changes are included; the full
refinement goal remains open.

The next panic-setup checkpoint proves the accepted zero-size allocator path.
`PanicAllocateZero` executes actual f509, including the nested blocks and
zero-size branch: 11 ordinary units/14 active steps; its typed local call is
22 units/16 steps. The nonzero allocator branches are outside this contract.
`PanicAllocateBody` and `PanicAllocateCall` compose actual f508 reserve16,
argument preparation, f509 invocation, sequential two-word copy and SP restore:
45 units/39 active steps and 56 units/41 local-call steps. The second source
word is read after the first target write; the execution contract retains
arbitrary aliasing.

`PanicAllocatePointerBody` and `PanicAllocatePointerCall` compose actual f503:
75 units/61 active steps and 86 units/63 local-call steps. The returned pointer
one is derived from the actual memory writes, so the real nonzero guard skips
the failing allocation branch. `PanicAllocateNative` proves that the low
result word survives the adjacent high write without requiring scratch/output
separation. `PanicAllocatePointerNative` derives the nested spans from original
SP at least32 and SP within memory; static words above that SP retain their
initial values. `PanicHookNative` therefore derives all computed-memory guard
conditions for the following hook setter from original code/data, a stack below
the hook globals, and initial initialization/lock/old-vtable words zero.

`PanicHookSet` proves the actual first-hook f822 body, including its four
entered empty blocks, initial-flag and old-lock guards, four sequential
lock/vtable/receiver/unlock writes, old-vtable guard and explicit return:
31 ordinary units/35 active steps. Generic opaque pre-store capsules bound
kernel conversion without assuming a guest execution result. `PanicHookReadback`
derives exact installed receiver/vtable words, cleared lock, preserved
initialization word, well-formedness and unchanged memory size/max from
those real writes. The initialization-slow and old-hook-drop branches remain
outside this first-install contract.

`PanicHookBody` adds the actual typed f822 invocation (42 units/36 steps)
to the real f503 call, composing f522's complete body: 131 units/102 active
steps. `PanicHookCall` adds f522's opcode, activation and normal leave:
140 ordinary units/104 local-call steps, with exact gas and promise credits.
`TotalSupplyPanicFrontier` supplies this actual call alongside the six earlier
implementations. The getter now has **four remaining local execution
contracts**: state read219, serialization96 and the two vector-drop68 sites.
The public invocation and original-store gas bounds retain installed-code,
scalar/native/representation resources and whole-module validation premises.
An independent review found no functional or accounting defect in this
composition; no complete exported-method refinement is claimed.

The separate `PanicHookValidation` suite checks 60 accepted captures across
503/508/509/522/822, including exact root gas and fuel, one-less-fuel failure,
restored SP, output words, installed hook words and unchanged functional host
fields. Each allocator helper excludes four nonzero-allocation captures;
these cases are not claimed by its zero-size theorem. The integrated harness
baseline remains unchanged.

Final audits for the four-call panic checkpoint: strict transitive coverage
of 328 modules, 11849 declarations and 8846 theorems with zero violations;
full working-tree coverage of 311 modules, 11974 declarations and 7768 theorems,
with exactly the original three refinement-dependent `sorryAx` declarations.
The full source build passes 1471 jobs; blueprint extraction/rendering passes
1496 jobs, and the rendered current four-call frontier was checked. Principal
new allocator, hook, memory and frontier theorems pass Lean LSP MCP standard-
axiom verification. No runtime, model or WF changes are included; the full
refinement goal remains open.

The following vector-deallocation checkpoint follows both explicit getter
vector drops into the real wee_alloc previous-free coalescing path.
`DeallocateAlign` proves actual f568 checked ceiling division, including both
overflow guards and the nonzero denominator: 18 ordinary units/20 body steps,
29 units/21 local-call steps. Actual f570 composes its real f568 call:
41 units/25 local-call steps. Initial numeric bounds imply both guards, and
the returned result is `(a + 3) / 4`; the computed result is then actually
discarded by the deallocator. No arithmetic failure or call execution is
supplied as a semantic callback.

`DeallocateListSize` proves actual f576: 25 units/17 local-call steps, with
the header-size result and unsigned underflow guard derived from a native
initial header bound. `DeallocateListBody` and `DeallocateListCall` execute
actual f575 when both neighbor links are nonzero and the first link flag is
clear: 61 ordinary units/65 body steps and 72 units/67 local-call steps.
Both neighbor stores and the final low-bit clears use their actual sequential
memory snapshots, retaining arbitrary aliasing. Exact code/global/functional
host frames, memory lookups, gas, promise credits and residual credits follow
from those operations. `DeallocateListReadback` separately derives the final
zero byte from native flag and explicit separation hypotheses; it does not
claim that original-word readbacks survive arbitrary overlapping writes.

The empty-capacity f68 path is separately proved at 37 units/14 local-call
steps through the real empty f778 destructor and f747 branch. Positive-capacity
prefixes execute the actual typed f68→747→777→311→237 entries; their metadata
and native vector reads refer to the deployed code. Both explicit getter drop
captures have positive capacity and therefore require the concrete allocator
path, rather than the empty alternative.

`DeallocateValidation` checks every current `DeallocateCore.Native` data field
for its accepted captures, then compares exact gas, exact and one-less fuel,
whole sequential memory pages/max, restored SP and selected functional host
fields. It accepts 1589 captures across six functions: 28 f68, 124 f582,
124 f575, 531 f576, 385 f570 and 397 f568; 98 other captures are outside the
selected contracts. Both explicit `ft_total_supply` vector-drop sites satisfy
all checked native conditions. This separate suite does not enlarge the
integrated nine-contract harness baseline. Non-previous-free deallocator
paths and other unlink flag/link branches remain outside these contracts.

`DeallocateCoreBody` now proves the complete actual previous-free f582 body
through real f570/f568 alignment, f576 size checks and f575 unlink calls:
218 ordinary units/188 active steps. Its full typed local call costs
231 units/190 steps. `VectorDropPositive237Call` composes that actual allocator
at 246 units/196 local-call steps; the complete positive f68 chain through
778/747/777/311/237/582 costs 319 units/230 steps. Pure original code/vector
header facts and explicit sequential heap-native conditions remain premises;
no successful execution or computed post-array lookup is supplied as a callback.

`TotalSupplyVectorFrontier` discharges both explicit getter drop sites with
these real f68 contracts. Exactly **two local execution contracts remain**:
state read219 and serialization96. The getter assembly, public invocation and
original-store gas-bound corollaries retain their original structural, native,
loading and representation premises. Full exported-method refinement remains
open. All four frontier theorems passed Lean LSP MCP diagnostics and standard
axiom verification; the focused final build passed 1025 jobs.

Final audits for the two-call vector checkpoint: strict transitive coverage
387 modules / 13400 declarations / 10026 theorems, zero violations. Full
working-tree coverage 368 modules / 13541 declarations / 8965 theorems,
with exactly the original three `Proofs.Refinement` declarations using
`sorryAx` and no other violations. Full source build passes 1530 jobs;
blueprint extraction/rendering passes 1505 jobs, and its rendered two-call
frontier was checked. Independent review reconciles every nested call cost,
active-step count and depth-eight premise. No new sorry, native certificates,
custom axioms, operational runtime changes, model changes or WF changes.

The following state-read and serializer checkpoint discharges actual pieces
of both remaining whole-call obligations. `StateReadResult` proves the f498
present-tag guard and sequential twelve-byte copy, then `StateReadResultCall`
its complete typed local call: 27 ordinary units/18 steps. The high word is
read from the memory after the low eight-byte write, retaining arbitrary
aliasing and actual wrapped high addresses. Exact memory/code/functional-host,
gas and residual-credit frames follow from those operations.

`MeteredHosts.RegisterRead` derives the actual register_len length/sentinel
and whole-register read_register semantics, exact pre-call charges and
residual credits. `MemoryListRules` proves byte-level writeList readback,
well-formedness, unchanged size/max and the outside-interval frame; register
copying has five external charges, including memory writes. Typed installed
host WPs and resource transport use original memory/register data, rather
than assumed host outcomes. The actual f241/f240 guest forwarders cost
13 ordinary units plus base/4 local steps and 15 units plus the full copy
fee/5 local steps. Their root activation charges include i64 parameter widths.

`MeteredHosts.StorageRead` derives canonical successful and missing reads
from original WF/representation/nonzero-node/accounting/key/span/limit
resources. The actual order is lookup charges, recorded-proof check on the
looked-up trie, referenced-value charges and dereference, raw register update,
then register-write charges. Success returns one and missing returns zero;
misses leave all registers unchanged. Exact burnt gas, unchanged promise
reservations and residual credits are proved at both node-accounting modes.
The recorded-proof condition remains explicit and does not resolve SAF-67 or
the reserved-zero-node gap. `MeteredStorageReadRules` composes the real
installed host opcode. The accepted-hit f284 typed local forwarder costs
17 ordinary units plus the computed canonical read fee/6 steps; resource
frames derive its target register bytes and unchanged memory/code arrays.

Serializer helpers now have actual typed local contracts: f472 pair-store
17 units/8 steps; f365's accepted guard 22 units/15 steps; positive f321 drop
319 units/230 steps through the prior concrete allocator proof. Actual
table index92 resolves to f353. The typed f353→901 prefix reaches the real
f902 call with the original U128 words at 31 units/13 steps, without assuming
f902 execution. This is a prefix theorem, not a complete formatter call.
Full serialization still needs allocation, the f872 formatter engine and
the f902 decimal algorithm. State-read219 still needs its SDK wrappers,
register materialization/allocation and state representation composition.
The getter therefore retains exactly two whole-call obligations, 219 and96.

Separate checks cover 26 f498 captures; 43 each of f240/f241; serializer
f472/f365/f321 at 8/9/111 captures; and getter formatter-prefix captures.
Storage-read tests replay 19 captured inputs with fresh canonical accounting
at both node-billing modes plus explicit empty-storage absence fixtures:
38 hits and38 misses, exact pure-plan fees, registers, whole memory and fuel.
These augmented replays are distinct from unchanged captured-state checks;
none enlarge the integrated nine-contract harness baseline.

Final audits for the state/serializer checkpoint: strict transitive coverage
426 modules / 14393 declarations / 10752 theorems, zero violations. Full
working-tree coverage 392 modules / 14028 declarations / 9317 theorems,
with exactly the three original `Proofs.Refinement` declarations using
`sorryAx` and no others. Full source build passes 1567 jobs; blueprint
extraction/rendering passes 1511 jobs and the rendered scope was checked.
Principal proofs pass Lean LSP MCP standard-axiom checks; the transitive audit
also covers result projections whose per-theorem MCP check was inconclusive.
Independent review found no defect in charge ordering, aliasing or resource
scope. No runtime, model, WF, custom-axiom or native-certificate changes.
GitHub Actions did not start its latest jobs because the account has a
payment or spending-limit issue. Locally, the chain/library/replay build
passes 2154 jobs with `--wfail`, and the SDK build passes. Repository pin,
isolation and umbrella gates and four conformance-tool tests pass. The
281-test tooling run skipped15; its sole initial Git-discovery failure
passes when rerun with this checkout's recovered source metadata.

The allocation/SDK checkpoint proves further actual deployed-code pieces.
`MeteredWordRules` supplies typed scalar word/unary/conversion rules, and
`MeteredLabelRules` handles a taken branch over arbitrary intervening labels.
Actual f572 checks the original word bound and shifts by two (19 ordinary
units/12 local steps); f574 checks the original minimum size (17/9); the real
type13 indirect callback to f578 returns 16 (11/3). These proofs use ordinary
kernel arithmetic and standard axioms.

Layout leaves f751/f684 execute the normal alignment-one path, including
actual size reads before either output write: 44 units/36 local steps.
Wrappers f752/f685 execute their actual scratch setup, nested layout call,
64-bit copy and stack restoration: 78 units/61 local steps. Exact computed
memory, code, globals and gas frames retain arbitrary output/scratch overlap.
The leaf's output pair is proved `(size,1)`; explicit pair readback after the
wrapper's packed copy remains a separate representation lemma.

The actual f581 alignment/save prefix is checked at 47 units/31 steps.
Positive allocation f580 has a thirteen-op header fit guard, twelve-op split
initialization, ten-op header commit and eight-op tagged back-link store.
The actual indirect callback and f572 call cost 35 units/20 steps and derive 64.
All five split arithmetic/overflow guards are composed at 35 units/35 steps,
with their outcomes derived from the original `SplitNative` header interval.
No callee execution callback or future-memory lookup is assumed. Split and
tagged-link execution uses the current sequential memory, including reads
after earlier clears; preservation of an original header or a global heap
invariant is a separate framing obligation. A separate validation checks the
selected positive f580 branches at 273 units/236 fuel (words1/6) and 344/295
(words32, including a skipped candidate), with exact
whole memory and the computed nonzero pointer. Whole f580/f581 composition,
loop traversal/link controls and the 29-byte memory-growth branch remain open.

SDK prefix code now executes actual lookup565/468 and acquire429/494/672 at
114 ordinary units/77 steps, parameterized by the real scratch-local slot and
panic location. Its code, memory-shape, functional-host and exact gas frames
are proved from original resources. Actual f432 accepted return costs 26
units/17 local steps; its guard constrains the low32 bits of the status.
The record-copy/selection/nonzero call in f440 costs 28 units/21 steps. Its
register-length dispatch, release and return tail costs 99 units/64 steps plus
the host base fee. The complete accepted f440 body composes these actual stages
at 241 ordinary units/162 steps plus the original host base fee, with standard axioms only.
Its complete typed local-call adapter costs 254 ordinary units/164 steps
plus the original base fee, including actual activation at 12 units.
Readiness is required on the original store and canonical leaf/caller frame;
charge transport derives the entered resources. No callee execution outcome
is supplied. The fallback path and state-presence/decoder correctness remain
outside this initialized accepted branch.

Remaining state targets include SDK dispatchers459/435 and their callers.
Whole 219 still includes positive zeroed allocation, register materialization
and f161 deserialization. Whole 96 includes positive serializer allocation,
the general U128 decimal algorithm and formatter writer. Nonzero allocation
and payload-range claims must continue to follow from original heap data.

The allocation/SDK strict transitive audit covers 486 modules / 15890
declarations / 11818 theorems with zero violations. The full working-tree
audit covers 450 modules / 15566 declarations / 10425 theorems and exactly
the three original `Proofs.Refinement` declarations depending on `sorryAx`:
`WNear.withdraw_available_wasm`, `WNear.refines_wnear` and
`WNear.refines_wnear_exported`. No other violations occur. The full source build
passes 1626 jobs; blueprint extraction/rendering passes 1529 jobs and the
rendered dispatcher counts and remaining two-call frontier were checked.
Principal proofs pass Lean LSP MCP standard-axiom checks. Independent reviews
found no defect in deployed-code correspondence, activation/gas/fuel counts,
sequential aliasing or original-resource scope. No runtime, model, WF,
custom-axiom or native-certificate changes are included.

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
