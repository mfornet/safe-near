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

### 3.0 The metered logic (L1) — **Decided**

`near-lean/near-logic` (NearLogic). Recorded here so that the design is
not re-derived:

- **The machine.** The language's step is `mnext`, one step of
  `Wasm.Near.runMetered`: the instruction's charge, `Exec.step`, the
  activation charge of a frame it enters. `runMetered_steps` makes a run a
  sequence of these steps, and `runMetered_ending` reads adequacy back on
  how the run ends. A failed charge is an ending (`Ending.gas`), which
  proofs make impossible by holding credits.
- **The heap.** WasmLogic's locations and cells, with the host split: the
  host cell (`Loc.host`) holds the host with its gas counter, profile and
  `context.usedGas` erased (`erase`); `gasLoc` holds the counter and the
  profile. The state is `MStore`, a structure around the store, so that its
  state interpretation is not WasmLogic's (iris-lean keys state
  interpretations on the state type). Assertions, `Frame`, `Ctx` and `Post`
  are WasmLogic's.
- **Gas credits.** `credits C n` owns the gas cell and says `used + n ≤ C`,
  with the ceiling `C` below both limits. Credits are threaded, not split:
  a rule takes `credits C (cost + R)` and returns `credits C R`. The
  ceiling is where the method's gas bound enters: a method proved from
  `credits gasBound (gasBound - used₀)` uses at most `gasBound`.
- **Lifting.** `mwp_lift_plain` takes a step that leaves the host alone
  from facts about `Exec.step` only, so WasmLogic's side conditions are
  reused unchanged; `mwp_lift_host` takes a host call, which owns the host
  cell and pays the host function's own charges.

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

*Status: done* (`near-lean/near-logic`, PR #40), with no `sorry` and only
the standard axioms. `Examples/SkeletonComplete.lean`, `skel_refines`:

    Refines Near.Boundary.nearRuntime protocol (skelCode size codeOf) (skelModel size)

for any protocol with the limits the module needs (`SkelProtocol`: a
positive op cost, no prepare-limit error, 1024/2048 memory pages, room to
return 4 bytes), any code size and any `codeOf`. The test module is
smaller than planned: `get` returns `"ok"` through `value_return`, with no
storage write or log; those host functions come with M4 and M7. The chain:

- the metered language, both lifting lemmas, gas credits, host charges,
  fragments and their structural rules, the pure rules, host calls that
  read memory, `value_return`'s contract with exact gas, the entry
  function, adequacy with final cells (`get_adequate`);
- instantiation (`SkeletonModule.lean`): validation by `kernel_rfl`, the
  instantiated store from `Memory.writeBytes` lemmas, the data memory kept
  irreducible so nothing evaluates its pages;
- the run and the boundary (`SkeletonRun.lean`, `SkeletonRefines.lean`):
  `outcomeOfExecution` with no promises, `checkReceipts`, `observe` and the
  stake check, giving the enough-gas clause (`get_enough`);
- below the bound (`Relax.lean`, `RelaxStep.lean`, `RelaxRun.lean`,
  `Hosts/ValueReturnRelax.lean`, `SkeletonBelow.lean`): instructions carry
  any host (`instr_withHost`); charges under raised limits succeed with the
  same result; `value_return` respects raised limits (`RelaxFn`); a step
  and a run with raised limits follow the lower run unless it ends with a
  gas failure (`runMetered_relax`), with the host's limits, issue and logs
  kept along the way (`QuietHost`); so `get` under any gas fails for gas
  with no logs, or ends as with enough gas (`get_any`, `get_vm_any`);
- the other methods: not exported (`nearRuntime_not_exported`).

What carries over to wNEAR: `runMetered_relax` is generic; each host
function needs its `RelaxFn` lemma (the metered wrapper's part is shared
with `value_return`'s), and `QuietHost` becomes "the logs so far are a
prefix of the final ones" once `log_utf8` is linked. The protocol config
is still a hypothesis; wNEAR's statement fixes v86 through
`RuntimeConfig.parse`, to settle by M9.

### M3. The first method, top-down

`ft_total_supply`, or another small view: its contract, proved from sorried
contracts of every function it calls, then those leaves proved. This fixes
the contract shape of 3.2, the first representation predicates and the
first automation.

*Exit:* one exported method's `Refines` clauses proved with no `sorry`.

*Status: contracts being stated and stressed* (`Harness/TotalSupply.lean`).
`ft_total_supply` (296) calls, in order: `setup_panic_hook` (522),
`set_blockchain_interface` (520), `state_read` (219),
`unwrap_or_default` (155), the `FungibleToken` getter (414),
`serde_json::to_vec` (96), `Result::expect` (158) and `Vec::deref` (779).
Stated and passing the harness: 779, 155, 566 (`U128::from`, under 414),
414 and 158 with exact costs; 219 with the state's representation
(`total_supply : u128` at 0, `account_storage_usage : u64` at 16, the
`LookupMap` prefix as a `Vec` at 24, whose pointer is `Option`'s niche),
its cost left to M7; 96 (`to_vec` of a `U128`: `Ok` with the JSON string
of the decimal digits, checked on border values up to `2^128 - 1`), its
cost left to M5 (`core::fmt`). Open on this path: 520 and 522 (the
environment, global state: the ghost "environment set up" of the
contracts above is their postcondition), then the method's own contract,
whose postcondition is the model's step. Three of the harness's
catches so far came from this path (misstatement log, 3 to 5).

*Done for every method (PR #40, no `sorry`):*

- **The binary loads** (`Binary/Valid*.lean`, `Link.lean`,
  `Instance.lean`, `Run.lean`). Under v86's memory limits the prepared
  module validates: the kernel checks the 907 bodies in 22 files after
  `Validate.module` was split into `moduleContext` and `funcOk`. Its 48
  imports resolve to `wHosts`. It instantiates to the explicit store
  `wStore`, with config and host symbolic, by `kernel_rfl_all`.
  `Link.instantiateModuleOf` takes the module directly. The data segment
  is given by structural recursion (`dataInitK`), because the kernel
  cannot unfold `Array.ofFn` at 26 KB. `runAttempt_wnear`: on an exported
  method, loading fails for gas, or the method runs from `startW`.
- **Every host under raised gas limits** (`NearLogic/Hosts/*Relax.lean`,
  `Bridge/Hosts.lean`, `storeRelaxFns_wStore`). The metered wrapper
  reduces `RelaxFn` to the call after its charges (`metered_relax`). The
  charges before the call and the argument check ignore the limits for
  every imported name. `finishMeteredCall` commutes with raising them.
  The storage phase (`storageAux_rel`) is walked in step with tactics
  that keep the raised host folded as `relax H` (`bill_step`, `csplit`).

*Done since: the below-the-bound case with logs (`method_below`, any method of the binary), and the metered instruction rules (pure, memory, globals, control flow, Wasm calls with `MFunSpec`). Missing: `memory.grow`, tables, bulk memory.*

*Next: the below-the-bound case with logs.* For the skeleton,
`QuietHost` (no logs, no execution issue) carried the out-of-gas case.
wNEAR logs, so the lower run's final logs must be shown to be a prefix of
the raised run's. The plan:
1. Per host (`HostMono`): the logs only grow, and an execution issue is
   only ever recorded together with a trap. Then a running machine has no
   execution issue, and along a run the logs only grow (`runMetered_mono`).
2. Strengthen `GasTrap`/`GasTrapResult`: the lower trap's logs are a
   prefix of the raised call's result logs, and its execution issue is
   the input's. A charge failing before the call keeps the input logs; a
   failure in `finishMeteredCall` keeps the logs the call produced, which
   the raised call returns too.
3. Then `runMetered_relax`'s gas case gives: the lower final logs are a
   prefix of the raised final logs, and no execution issue.

The storage trie (`NearLogic/Trie.lean`, `storage_lookup`): on a canonical trie a lookup finds exactly the stored value, without error, keeps the data, and touches at most 2·|key| + 1 nodes. It assumes that no witness node hashes to the all-zero hash, which `walk` treats as the empty trie. That is a SHA-256 preimage fact: it can't be proved, so like SAF-67 it must become an assumption on the context (a `Context.WF` field or a hypothesis of `Refines`). Still left on this path: linking `entries.find?` to the VM host's `storage` through `trie_storage` and `toNearState`.

The allocator (M4, `Bridge/Functions/Alloc*.lean`): the heap invariant `heapInv` is designed and its bottom layer proved: the leaves, the `__rust_alloc`/`__rust_dealloc` entry shims, a metered `memory.grow` rule and `new_cell_for_free_list` (577). Not done yet: `alloc_first_fit` (580), `WeeAlloc::alloc` (581), `dealloc` (582), `Neighbors::remove` (575). Finding: wee_alloc 0.4.5's first-fit walk unlinks every free cell it passes. Such cells come back only by merging, so one walk takes at most 2F iterations, and an allocation that misses grows memory and succeeds.

Allocator progress: dealloc (575, 582, `__rust_dealloc` 311) proved against `heapInvFix` (`AllocDealloc.lean`); alloc proved on the paths a method takes until it frees anything: the empty list, then the single fresh cell (`f580_empty`, `f580_one`, `f581_fresh`, `f310_fresh`). Invariant fixes still to fold into AllocInv: the live clause (`Lives`), positive sizes, `next % 4 = 0`, `nextFree % 4 < 2`, and `addr + 12 ≤ next` instead of `+ 24`. Also, `p = 0` after a successful grow is possible when `align ≥ 16` and the slack is small, so the no-failure argument must assume `align ≤ 8` or enough slack. Left: packing the fresh-path specs into `heapInvFix`, and the general walk for F ≥ 1.

The remaining open point on this path is SAF-67 (`Context.WF` does not
constrain `storageProofSize`). Until it is decided, every storage-touching
method's `Refines` is false as stated.

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
