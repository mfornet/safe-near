# Proving the wNEAR refinement

The campaign that closes `refines_wnear_exported`
(`contracts/w-near/verification/Proofs/Refinement.lean`): the deployed
`contract.wasm` refines the wNEAR model, for every input, state, context and
amount of gas, with every hypothesis discharged by the kernel.

Items marked **Decided** are not re-opened without discussing first. Items
marked **Open** are for whoever reaches them to settle and record here.

**Current status and how to resume:** `wnear_refinement_status.md`.

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

Allocator progress: dealloc (575, 582, `__rust_dealloc` 311) proved against `heapInvFix` (`AllocDealloc.lean`); alloc proved on the paths a method takes until it frees anything: the empty list, then the single fresh cell (`f580_empty`, `f580_one`, `f581_fresh`, `f310_fresh`). The invariant fixes are folded into one `heapInv n maxP len live F` (`AllocInv.lean`): `Lives`, positive sizes, `next % 4 = 0`, `nextFree % 4 < 2`, `addr + 12 ≤ next`, disjoint cells, and an exact `len`. Dealloc is proved against it, and `__rust_alloc` on a heap with an empty free list (`f310_spec_fresh`). `p = 0` after a successful grow is possible when `align ≥ 16` and the slack is small. Left: alloc on the one-cell list a previous allocation leaves (sequences of allocations), alignment in the packed post, a limit-aware `memory.grow` rule to exclude `p = 0`, and the general walk for F ≥ 1.

Allocator, the general walk: `__rust_alloc` on `heapInv … F` for every `F` (`AllocWalkHeap.f310_spec_walk`, room under the limit, `align ≤ 8`) returns a block and `heapInv … ((p, size) :: live) (max F 1)` at `970 + 320·F` `regular_op_cost`s plus the grow (`f310_spec_three`: 1930 at `F = 3`, against 940 for `F ≤ 2`). 580's walk is a loop invariant over the heap model (`AllocWalk.inv3`, `inv7`, `f580_walk`): every iteration that does not end the walk removes a listed cell (a merge or an unlink), and 320 per cell pays for both. The invariant needed no new field. `VecWithCap.f310_roomG` gives the `RawVec` chain the allocation on any `F ≥ 1` at `costAllocF` (equal to `costAlloc` for `F ≤ 2`). The chain above it (`VecWithCap`, `FmtGrow`, `FmtSink`, `FmtString`, `ToString`, `ToVec`, `SerdeLeaves`) is stated on `okG` (any `F ≥ 1`), its costs (`costGrow`, `cost353`, `cost872`, `cost746`, `cost385`, `ToVec.cost96F`) taking `F` and charging `costAllocF cfg F`; the methods' bounds at `F ≤ 2` are unchanged (`costAllocF_le2`, `ToVec.cost96F_le2`).

SAF-67 is fixed (#42: the recorded proof is a budget, like gas). On top of it:

- **`storage_read` under the budget:** it needs room for its one lookup (`ProofBudget`), not a blanket bound.
- **The below-the-bound case:** `relax` also turns proof recording off, and a `RecordedStorageExceeded` trap counts as a resource error.
  - So the method chain (`method_vm_any`, `method_boundary`, their relational versions) needs `Pre` only of the host recording no proof (`eraseP`).
  - It needs `Pre` of the actual host only under `ProofRoom`.
- **Pending changes:** `storage_read` reads the receipt's pending changes from the overlay (`storage_lookup_view`, `viewVal`).
- **New `Context.WF` fields:** `trie_no_zero_hash` (the zero-hash assumption above), and `prospective_unique` and `committed_unique`.
  - The uniqueness fields are needed because `State.view` lets a later change win while a lookup takes the first.
  - `hostOf_storage_view` links the host's storage to the overlay's view.

*`ft_total_supply` on an initialized contract is done* (`ftTotalSupply_refines_init`, `Bridge/Methods/FtTotalSupplyPre.lean`, standard axioms only). Left on it:
- the uninitialized contract: `PanicOnDefault`, with the message "The contract is not initialized" (M5, panics);
- the code size, `CostsV86` and `LimitsV86`, all discharged at M9.

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

*Status (`ft_balance_of`, 297):* proved, no `sorry`: `env::input` (527, through 458 and
the trampoline 246; `EnvInput.lean`), the prologue's leaves `Option::expect` (157),
`SliceRead::new` (644), `Deserializer::new` (634), and `from_slice` (65) from any
specification of `from_trait` (66) (`ArgsLeaves.lean`); on the model's side, the canonical
input `{"account_id":"<a>"}` decodes to `ftBalanceOf a` (`BalanceOfArgs.lean`). Stated, not
proved: the rejecting half of the parser's contract, `FromSliceSpec.RejectContract`; the accepting
half, `AcceptContract` (66 against `Call.decode`, cost `(K0 + K1·len)·c + X`), is proved
(`acceptContract`, `f65_accept`) from the callees not proved yet (`AcceptCallees`: 169, 81, and 646
on keys with escapes); on an input without `\`, only 81 is left (`FromSliceNoEsc.acceptContract_noesc81`,
eighth round). Below 66 are 78/228 and about 200 functions (14 000 instructions), which
allocate and free: they need the allocator on any free list (M4), as does the rest of 297
(`LookupMap::get`, 293/415, after the parser's frees).

*The parser, mapped:* `notes/todo/wnear_m6_parser_map.md` lists the 202 functions below 66
by layer, with their sizes and roles, and which other methods' parsers share them.

* 137 functions are common to all nine argument parsers.
* `storage_balance_of`'s 52/222/191 are 66/228/193, instruction for instruction.
* The model and serde_json 1.0.60 were checked against each other on every acceptance
  point (whitespace, the two struct forms, duplicate and unknown fields, keys, escapes,
  surrogates, UTF-8, numbers, depth, trailing data). No disagreement was found.

*Proved since (no `sorry`):*

* The reader over the slice, `Bridge/Functions/SerdeRead.lean`. The input model is
  `rd n de ptr bs i`, the `SliceRead` at `de` over `bs` at position `i`. Proved:
  * `peek` (332), `eat_char` (333), `next_char` (324), `SliceRead::next` (637) and
    `peek_or_null` (329);
  * `parse_whitespace` (339), which skips `wsLen (bs.drop i)` bytes at `100 + 96·w`. Its
    link to the model is `skipWhitespace_eq`, which says the model drops the same bytes.
* Key matching, `Bridge/Functions/SerdeKey.lean`. Proved:
  * `bcmp` (953), whose result is 0 exactly when the bytes are equal;
  * slice equality (755/754), whose cost depends only on the second, known length;
  * `ft_balance_of`'s field visitor (194). It returns field 0 exactly on
    `BalanceOfArgs.keyBytes`, which `keyData_segment` shows sit at 1051092, and has a
    constant cost.
* The account-id validator, `Bridge/Functions/AccountIdValid.lean`: `is_valid_account_id`
  (554) returns 1 exactly when `validAccountIdBytes bs`, at `100 + 60·len`, and `into_iter`
  (673) is proved with it. The loop keeps
  `accountIdFormat true bs = accountIdFormat prev (bs.drop k)`, and `byte_cases` `decide`s
  over all 256 bytes the five ways a byte goes through the four tests.
* `from_utf8` (927) on ASCII input, `Bridge/Functions/FromUtf8.lean` (`f927_spec_ascii`):
  `Ok(&str)`, `(0, p, len)` at `out`, at `cost927 len = 100 + 100·len`. All three ASCII paths are
  proved: the unaligned step, the word loop and the byte loop.
  * `Utf8.utf8Ok` is Rust's validator on lists, one character at a time. The main loop's invariant
    `inv927` is already the general one, `utf8Ok bs = utf8Ok (bs.drop i)`, and the result
    `res927` is `Ok` exactly when `utf8Ok bs`. Only the non-ASCII branch (the width table at
    1071704, then the second-byte ranges) is left; it is excluded today by the hypothesis that every
    byte is below `0x80`.
  * `Utf8.utf8Ok_iff_isValidUTF8`: `utf8Ok` is exactly UTF-8 validity in Lean's sense
    (`ByteArray.IsValidUTF8`). So `fromUTF8?_isSome` holds: the model's `String.fromUTF8?`
    succeeds exactly when `utf8Ok`, and once the non-ASCII branch is proved, 927 accepts exactly
    what `stringBody` accepts.
  * The inner loops are entered at an ASCII byte not yet read. Their invariant `invA` holds `100`
    per byte after the current one, plus `F` at the entry byte or `O` past it. The larger `O` pays
    for an exit back to the main loop, which can only happen past the entry byte.
  * `word_ascii`: a passing word test (`(w0 | w1) & 0x80808080 = 0`) means eight ASCII bytes.
    The proof goes through `Nat.testBit` on bits 7, 15, 23 and 31.
* `parse_str` (646), the plain case, `Bridge/Functions/ParseStr.lean`:
  * `f646_spec_plain`. From the index `i`, the input holds a body of ASCII bytes with no escape,
    then `"`, and the scratch is empty. The result is `Ok(Reference::Borrowed(ptr + i,
    body.length))`, with the reader at `i + body.length + 1`. It costs
    `200 + 30·body.length + cost648 body.length`, about `130` per byte, with an 80-byte stack.
  * Below it: `f583_spec` (the range index) and `f648_spec_ascii` (`as_str`).
  * The ESCAPE table is `escTable`, which `escData_segment` reads off the data segment.
  * `plain_model` is the model side. On the same input, `stringBody` decodes the string whose bytes
    are `body` and leaves the same rest.
  * The outer loop runs once, since its back edge follows an escape, so its invariant is just the
    state at entry.
  * Not yet proved: escapes and the copied result (scratch non-empty: 613, 728), and the reject
    paths of 646 itself (EOF, a control byte; their error constructor is now proved, below).
* `from_utf8` (927) on any input, `Bridge/Functions/FromUtf8Gen.lean` (`f927_spec`): `Ok(&str)`
  exactly when `utf8Ok bs`, else `Err` with some 8 bytes of `Utf8Error`, at the same
  `cost927 len = 100 + 100·len`.
  * The width table at 1071704 is a resource, `utf8Width`, read off the data segment
    (`widthData_segment`).
  * The non-ASCII branch, one equation of `utf8Ok` per path of the code (`ok_bad0`, `ok_two`,
    `ok_three_*`, `ok_four_*`). The byte tests and the second `br_table`s are `decide`d over the
    256 bytes.
  * The main loop's invariant is `inv927` unchanged: a `w`-byte character is paid by its `w`
    bytes, and a rejection by the byte it fails at.
  * The proof is one declaration of about 400 steps and takes about four minutes to check.
* `as_str` and `parse_str` on UTF-8, `ParseStrUtf8.lean`:
  * `f648_spec_valid` is `as_str` on any `bs` with `utf8Ok bs`.
  * `f646_spec_utf8` is the borrowed case of `parse_str` on any body of plain bytes that is valid
    UTF-8.
  * `utf8_model` and `utf8_model_bad` are the model side. `stringBody` decodes exactly those
    bodies; on any other body its string is `none`.
* The error position, `SerdePosition.lean`. Proved:
  * `position_of_index` (645, with 609): some `(line, column)`, at most
    `cost645 idx = 200 + 50·idx`;
  * `position` (638): the same at the reader's index, at `cost638 i = 40 + cost645 i`.
* The syntax error constructor, `SerdeErrBox.lean`. The spec is loose, as the reject paths need.
  * The allocation at alignment 4, through `AllocWalk.f310_spec_walk` on a free list of any
    length: `alloc_impl` (625), `Global::allocate` (624) and `exchange_malloc` (590).
  * `Error::syntax` (639) fills a fresh 20-byte box.
  * `f647_spec` (`Deserializer::error`; 657 has the same code, `f657_eq`) gives `Err(box)` at
    `out`. The heap gains the box (`heapA`), and the cost is at most `costErr cfg F i`. That is
    linear in the index, plus a constant and the allocator's `cost310W cfg F 20 4`.
  * `f648_spec_bad` is `as_str` on bytes of the input that are not UTF-8: `from_utf8` fails, then
    `InvalidUnicodeCodePoint` (code 14) through 657. With `f648_spec_valid`, `as_str` is now
    specified on every input.
* `parse_str` (646) on every escape-free input, `ParseStrErr.lean`.
  * `f646_spec_noesc`. From the index `i` the input is `body ++ tail`: `body` the plain bytes the
    scan skips, `tail` empty or starting with a byte that stops the scan and is not `\`. The
    scratch is empty. The result `res646` has four cases:
    * `tail = []`: `Err(EofWhileParsingString)` (code 4, through 647), the reader at the end;
    * a control byte: the reader past it, `Err(ControlCharacterWhileParsingString)` (code 15);
    * `"` and `utf8Ok body`: `Ok(Borrowed(ptr + i, |body|))` (`ok646`), the heap unchanged;
    * `"` and not `utf8Ok body`: `Err(InvalidUnicodeCodePoint)` (648 → 657).
  * The cost `cost646` is `(330 + 30·|body| + cost927 |body|)·c`, plus `costErr cfg F (i + |body| + 1)`
    on a reject. The stack is 160 bytes.
  * `noesc_model`: on the same input, when 646 accepts, `stringBody` decodes the string whose bytes
    are `body`; when it rejects, `stringBody` decodes no string (`none` or `some (none, _)`).
  * The general proof is one scan loop whose exit splits four ways. The only case left in 646 is the
    escape (`\`), which goes through the scratch appends and 649.
* The errors that return the box, `SerdeErrRet.lean`: `error` (325, `f325_spec`, at most
  `costErr cfg F i`), `peek_position` (640, `f640_spec`: 645 at `min (i + 1) len`) and `peek_error`
  (322, `f322_spec`, at most `costErr cfg F (i + 1) + 20·c`).
* A `String` from a `&str`, `SerdeString.lean`, at alignment 1 on any free list:
  * `alloc_impl` (625, `f625_s`): `size = 0` gives the dangling pointer 1 and no allocation;
  * `Global::allocate` (624), the layout (607/608, the code of 684/685), `RawVec::allocate_in`
    (626, `f626_s`);
  * `to_owned` (618, `f618_s`): the bytes copied into the fresh block (951);
  * `visit_str` (633, `f633_s`): `Ok(String)`, `(0, p, c, c)`.
  * `heapS` is the heap after the allocation. The cost is a constant, the copy's and the allocator's
    `cost310W cfg F c 1`.
* `deserialize_str` (380), `SerdeDeStr.lean`. `f380_s`, from the reader's index `i`, with
  `j = i + wsLen (bs.drop i)`, covers two cases:
  * the input ends at `j`: `Err(EofWhileParsingValue)` through 322 (code 5);
  * a `"` at `j`, then an escape-free body (as for `f646_spec_noesc`): `eat_char` (333), the scratch
    cleared (`f343_s`, `f674_s`), 646, then on `Ok` the copy (633). The result `res380` is
    `Ok(String)` holding `body` in a fresh block when 646 accepts (`ok380`), else 646's `Err(box)`.
  * Another byte at `j` goes to `peek_invalid_type` (340), not proved; a hypothesis excludes it.
  * The cost `cost380` is `(350 + 96·w)·c`, plus 646's cost, plus either 633's (`60·c + cost618`)
    or an error bound. The stack is 208 bytes.
* `ValidAccountId::deserialize` (169), `SerdeAccountId.lean`: `f779_s` (`as_str`), `f502_valid` and
  `f501_valid` (`try_from` on a valid account id: `Ok(s)`), `f379_s` (the wrapper of 380), `f617_s`
  (the identity) and `f169_s`. The result is `res380` again, now for `Result<ValidAccountId>`. The
  hypothesis `hvalid` excludes a decoded string that is not a valid account id: its path (693 and
  479 in 502, then `to_string` 130, `Error::custom` 387 and the drop 151 in 169) is not proved. The
  stack is 256 bytes.

*Tactics notes from this round.*

* `mstep` does not cover `select`. Use `FromUtf8.mwpi_select'`, which gives
  `if c = 0 then b else a`.
* Credits must be `k * c + X` with a literal `k`, so rewrite and `generalize` the per-byte part
  before stepping.
* When an `mcall`'s cost is `(m + cost f) * c`, state `(m + cost f) * c = m * c + K` beforehand,
  because `omega` treats products as atoms.
* After `simp only [Post.mloop]` unfolds an outer loop's post, later goals carry the structure
  literal. `dsimp only` reduces its `.br 0` and `.normal` projections.
* Tactic macros (`local macro`, `hygiene false`) save repetition (`tail927`, `body10`, `word11`).
  In a context with contradictory hypotheses, though, an unreachable exit branch inside a macro
  failed with "type mismatch: Type / Prop". The fix is a variant macro (`after10x`) that closes
  that branch with `exfalso; omega`.
* Some failures show up only at the kernel, or as `whnf` timeouts, from what the step tactics'
  side conditions (`simp_all`, `omega`) do with the context. Seen this round:
  * A hypothesis that mentions the sign extension of a byte (`hs : sb b = s`), even wrapped in a
    `def`, made a single `mstep` time out. Derive the byte facts before `generalize`, so they are
    facts about `s`, and keep them packed (`FromUtf8Gen.Hide`).
  * A fact about a `br_table` index (`[…][(b.toUInt32 + k).toNat]?.getD d = 2`) in context sent
    `mpay` into a deep recursion. Rewriting with it inside the goal made the kernel recurse too.
    `FromUtf8Gen.mwpi_br_table_k` takes the label computed beforehand; clear the fact right after.
  * After an `mcall`, stepping on the subtraction the call leaves in `Hc` made the kernel recurse.
    Normalize the credits with `mcredits (k * c + X)` before the next `mstep`.
* `omega` fails on a subtraction whose operands contain a product such as `cost638 i * c`; it
  treats the whole subtraction as an atom. `generalize` the product to a variable first.
* A loop followed by more code in its block needs `iapply mwpi_cons` before
  `MemCpy.mwpi_loop0`.
* A persistent bundle of code cells in a `def` (`errCode`) is not persistent to `iintro #`.
  Destructure it with `icases … with ⟨#…⟩`. To pass it to `mcall`, `unfold` the definition in the
  specification's statement.
* Later notes (the parser's fourth round):
  * A bundle can also be made persistent with an instance (`SerdeDeStr` gives one for `errCode`).
    The bundle then stays whole in the context, and `mcall` finds it there; do not `unfold` it in
    the callee's specification.
  * `select` with values below its three operands: `iapply` does not unify `vs ++ [a, b, c]`
    with a literal stack. `SerdeErrRet.mwpi_select2` states it for two values below.
  * When `mcall` fails with an `omega` counterexample that does not mention the credits, the
    failing side condition may be the callee's address. Put `hm.funcs k (by decide)` for every
    callee in the context.
  * The cost side condition of `mcall` includes the activation, e.g. `(13 + cost554 m) * c` for
    554. State `(13 + cost554 m) * c = 13 * c + K` beforehand, with the right constant; a wrong
    constant leaves `omega` with two unrelated product atoms.
  * A branch on a literal value: `mstep_taken with decide` or `mstep_not_taken with decide`.
  * A callee whose postcondition is pure (617) leaves `HQ : ⌜rs = …⌝` in the Iris context, and its
    precondition goal is closed by `ipureintro; trivial`.
  * A loop proved once can split at its exit into several outcomes (`f646_spec_noesc`: EOF, a
    control byte, the quote). Generalize the outcome-dependent part of the credits (`if … then 0
    else costErr …`) into a variable, and rewrite its equation in each branch.

*The struct layer (fifth round).* Proved, no `sorry`:

* The model without its fuel, `JsonFuel.lean`. `value`, `elements` and `members` give the same
  result for any fuel from `2·len + 1` (`+ 2` for the last two): `fuel_stable`, `value_fuel`. The
  fuel-free `valueR`, `elementsR`, `membersR` unfold like the grammar (`valueR_eq`, `elementsR_eq`,
  `membersR_eq`, with the helpers `keyAt`, `colonAt`, `memberEnd`, `elemEnd`), and
  `parse_eq` restates `parse` with `valueR`.
* serde's struct machine, `SerdeStructModel.lean`. `fromSlice key dv ign` is the streaming
  deserializer of a one-field struct as 228/193/205/201/214/90/91/320 run it: the object form
  (`objLoop`: key, duplicate check, colon, `dv` or `ign`, then `,` or `}`; `{}` is a missing
  field) and the array form (one element, then `]`; `[]` is `invalid_length`), then only
  whitespace. The value readers are parameters:
  * `dv` must agree with `valueAs dec`, the model's `valueR` then the field decoder;
  * `ign` must agree with `valueSkip`, the model's `valueR`;
  * "agree" (`Agrees`) allows the reader to fail where the model succeeds with a rest that
    starts with a digit, which is how serde's early rejection of `01` differs from the model.
  `fromSlice_eq`: for every input, `fromSlice` is `(parse bs).bind (structFields [key])` then
  `required dec`. `decode_balanceOf`: so `Call.decode "ft_balance_of" bs` is
  `(fromSlice "account_id" dv ign bs).map ftBalanceOf`, for any such readers.
* `ignore_value` as an iterative machine, `IgnoreModel.lean`. `vSkip` is serde's skip of one
  value (the model's `valueR`, failing on `0` or `-0` followed by a digit). `closeAll stk` closes
  a stack of frames on the model's side (`contM`: `,` and more, or the closing bracket). The step
  equations are 81's loop body: `vSkip_arrE/M`, `vSkip_objE/M` (a value that opens a frame,
  then the closing bracket or the first element or member), `close_arr_comma`,
  `close_obj_comma`, `close_*_end`, `close_*_none`. `ignM` is the machine with fuel, its scalars
  (`sv`) and keys (`sk`) parameters; `ignM_spec`/`ignM_eq`: it reads exactly `vSkip`, and
  `ignM_agrees`: it agrees with `valueSkip`, as `fromSlice_eq` needs. The Wasm proof of 81 can
  take the equations as its loop invariant: at the value phase with frames `stk`, the result is
  `(vSkip rest).bind (closeAll stk)`; after a value in the frame `f`, `closeAll (f :: stk) rest`.
* The punctuation checks, `SerdeEnds.lean`: `end` (320, `f320_spec`), `parse_object_colon` (89,
  `f89_spec`), `end_map` (90, `f90_spec`). Whitespace (339), then the byte: 0 and the reader past
  it, or `peek_error`'s box (322). Cost `(200 + 96·w)·c`, plus `costErr cfg F (j + 1) + 20·c` on
  an error; stack 96. Tactic macros `end_head`, `store_code`, `err_call`, `err_end`, `eat_ok`,
  `ok_tail`; the byte tests `byte_is58`, `byte_is125`, `byte_is44`, `byte_is93`, `byte_is34`,
  `eq_is125`, `ne_is44`, `some_bit` (each `decide`d over the 256 bytes).
* `end_seq` (91), `SerdeEndSeq.lean` (`f91_spec`): `]` eaten and 0, or the box (EOF, `TrailingComma`
  after `,` then `]`, `TrailingCharacters`), the reader somewhere. Cost `(400 + 96·w + 96·w')·c`, `w'` the
  whitespace after a `,`, plus `costErr cfg F (len + 1) + 20·c` on an error (`costErr_mono`); stack 112.
* `next_value_seed`, `SerdeValueSeed.lean`: 201 (`f201_of_81`) and 205 (`f205_of_169`) from any
  specification of the value reader (81, 169) at the reader after the colon, given as a
  hypothesis in the style of `f65_of_66`. So they hold for today's escape-free 169 and for its
  generalization.

*Findings.* No disagreement between serde_json and the model on the struct layer:
`fromSlice_eq` is the "no discrepancy" check of the map, as a theorem, for any value readers that
agree with the model. The one difference, `01` in an ignored value (serde fails at the second
digit, the model one step later), changes no outcome inside a struct.

*Tooling notes from this round.*

* `mstep` counts `block` as a step: count the `block`s before a `br_if`, or `mstep_taken` lands on
  the wrong instruction ("could not step i64.const 0").
* A `br_if` side condition on a symbolic byte (`optByte (some b)`) failed with "internal exception
  #5" when stated through `optByte_some`. Generalize `optByte (some b) = ob` first; the side
  condition is then `Numeric.bool (Numeric.irelop64 IRelOp.ne (ob &&& k) c) ≠ 0`, closed by
  `rw [← hob]` and a `decide`d byte lemma.
* Keep the error's cost `X` generalized until the `mcall` of 322, then
  `generalize costErr cfg F (j + 1) = E at key hX; subst hX`: stepping with `costErr` itself in
  the credits made a later `mstep` fail.
* An `if` in the postcondition cannot be rewritten while it is under the `Post` binders; rewrite it
  at the end, when the goal is the bare postcondition. To open an `if` in an Iris hypothesis, apply a
  lemma (`resEnd_pos`, `resEnd_neg`) with `ihave`.
* Pure proofs over `NearInterface.Json`: `split` on a goal whose two sides match on the same
  discriminant splits both; for a `match` the equation lemmas cannot reduce (literal `UInt8`
  patterns), state a small lemma `… := by unfold f; rw [h]; rfl` (`keyAt_quote`, `valueR_objE`,
  `structDe_arrM`): `rfl` reduces it, `simp` and `dsimp` do not. `grind` closes the length
  side goals of `number`.

*The struct's accepting run (sixth round).* Proved, no `sorry`, the accepting half of 228 with the
callees not proved yet as hypotheses:

* `next_key_seed` (193), `SerdeNextKey.lean`. `f193_end`: `}` after the whitespace gives `Ok(None)`
  (`v &&& 0xFF01 = 512`), the reader at the `}`, cost `(200 + 96·w)·c`. `f193_key`: a key after
  `first`, or after `,` (`keyQ first bs i = some q`): 82 clears the scratch, 646 is the hypothesis
  `Spec646` (an `Ok` reference `(p, |kb|)` with `p ↦ kb` lent by a wand), 194 gives
  `fieldOf kb` (0 for `account_id`, 256 otherwise), `first` cleared; cost
  `(572 + 96·keyWs + cost194)·c + K646` (800 before the seventh round); stack 176.
  `f646_key_noesc` proves `Spec646` from `ParseStrErr.f646_spec_noesc` for an escape-free accepted
  key (`rd_lend` lends the key's bytes out of the input).
* `next_element_seed` (214), `SerdeSeqElem.lean`: `f214_first`, the struct's one element with
  `first = 1` and a byte `≠ ]`, 169 as the hypothesis `Spec169`; `Ok(Some(String))` at `out`; cost
  `(300 + 96·w)·c + K169`.
* 228 on the array form, `SerdeStructArr.lean` (`f228_arr`): `[`, 214, `]` (91), `Ok(a)` at `out`
  (`strRes`: the bytes, the block's rest, the heap lending `(p, cap)`); cost `costArr`
  (`1300·c`, three runs of whitespace, `K169`); stack 336. `Hyp169` is 169's accepting spec against
  any account-id reader `dv`; `spec169_of_hyp` gives 214's view of it.
* 228 on the object form, `SerdeStructObjRun.lean` (`f228_obj`), with `SerdeStructLoop.lean` (pure):
  * `loopRes` is `objLoop` seen from the binary's loop head (before the `,`); `loop_end` and
    `loop_member` are one iteration of the binary, by indices.
  * The loop invariant `inv228`: the members left (`loopRes … N first sA (bs.drop i)` reads `a`
    and leaves `rF`), the field read so far (`seenRes`: `None` at `s + 40`, or the string), the
    credits `objCost` for the rest. Each member is 193 then 205 (169) or 201 (81); `}` ends it,
    then 90 and `Ok(a)`.
  * Hypotheses: `Hyp646` (keys, heap unchanged), `Hyp169`, `Hyp81` (81 at 201's call, heap
    unchanged), and three pure suffix facts (`hdvs`, `higns`, `hstrs`: the readers return a suffix
    of the input; proved in the seventh round, `JsonSuffix`, `SerdeFromTrait.reader_facts`).
  * Cost `costObj`: `(400 + 96·w)·c`, `objCost` (per member `(942 + 96·(keyWs + w) + cost194)·c`,
    1200 before the seventh round, plus `K646` and `K169`/`K81`; `(300 + 96·w)·c` at the `}`), and
    `300·c`. Stack 336; `sp` 8-aligned.
* `key_iff`: the visitor's byte test is the model's key test (through `fromUTF8_toUTF8`).
* `Input::deserialize` (78), `SerdeStruct78.lean`: `structDe_cases` splits what `structDe` accepts into
  the two forms, and `f78_acc` is 78 on any input `structDe` accepts (`Ok(a)`, the reader past the
  struct), at `40·c + costS` (`costObj` plus the array form's `costArr`, a bound). Extra pure
  hypothesis: `dv [] = none`.

*Restrictions and findings of this round.*

* The heap is unchanged by 646 on keys and by 81 (`Hyp646`, `Hyp81`). That holds for escape-free
  keys (`f646_key_noesc`) and for an `ignore_value` that pushes no frame. Keys with escapes and
  nested ignored values grow the scratch from capacity 0 (an allocation), which these hypotheses
  exclude; generalizing means a heap that changes across the loop, in `inv228`'s `seenRes`.
* `FromTraitContract` (disagreement with the plan): it asks the cost `K0 + K1·len` on the rejecting
  side too, and it does not hand the parser the read-only data it reads: the `ESCAPE` table
  (1062392), the UTF-8 width table (1071704) and the field name (1051092). Both need a restatement:
  an accepting contract with these data resources (given back), and a rejecting one with a loose
  cost. Smaller: the proved specs need `ptr + len < 2^32` and `len + 1 < 2^28` (the statement has
  `≤` and `len < 2^28`), and a heap room `R` large enough for `roomFor4` (an error box's page).
  Restated in the seventh round (`AcceptContract`, `RejectContract`).
* `K1`: the accepting cost per byte is not bounded yet. `objCost` charges per member a constant
  (about `1550·c`, with `cost194 = 342`) plus `K646` and the value's `K`; a member takes at least
  5 bytes (`"":0,`), so the constant alone is about `310·c` per byte, plus `96` per whitespace byte
  and the string scan (646 about `130` per byte). `K1 ≲ 480` looks reachable for the canonical
  input but needs the bound proved against `objCost`, and short members are the worst case. Proved
  in the seventh round (`SerdeCost`), with a tighter member constant.

*The contract restated, 66, and the cost bound (seventh round).* Proved, no `sorry`:

* **The contract, split** (`FromSliceSpec.lean`, `FromSliceProof.lean`). `FromTraitContract` is gone.
  * `AcceptContract S K0 K1 X`: when `Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)`, 66
    returns `Ok(a)` (`okAt`) within `(K0 + K1 · len) · c + X`. Its premise `AcceptCallees` holds
    what is not proved yet: readers `dv`, `ign` that agree with the model, `Hyp646`, `Hyp169`,
    `Hyp81` at 66's `Deserializer` (`sp - 64`), and the bound `cost66 ≤ (K0 + K1·len)·c + X`.
    `X` is for the account's `String` allocation, which the allocator charges partly in other units
    (`linearOpBaseCost`, `linearOpUnitCost`) and in the free list's length.
  * `RejectContract S`: when `Call.decode … = none`, `Err(box)` (`errAt`) at some finite cost
    (`∃ K`). Stated, not proved. `Refines` needs only that a rejected input fails with no effects,
    and running out of gas is a failure (`method_vm_any`).
  * Both premises: the code, the instance and the memory limit (`codeCtx`, persistent); the
    read-only data (`roData`: `ESCAPE` at 1062392, the UTF-8 width table at 1071704, the field name at
    1051092), given back; `ptr + len < 2^32`, `len + 1 < 2^28`, `roomFor4 hl 2048 20`; the stack
    `S = 400` for 66 (416 at 65).
  * `acceptContract K0 K1 X : AcceptContract 400 K0 K1 X`, from `f66_dec`, with the code from the
    store (`code66_of`). `f65_accept`, `f65_reject`: either half at 65's call site (`f65_of_spec`,
    `45·c` more). `acceptCallees_noesc`: on an input with no `\` byte, `Hyp646` is proved
    (`SerdeKeyNoEsc.hyp646_noesc`, from `f646_key_noesc` at every key; `key_noesc` matches the
    model's key to the body 646 returns) and the cost bound follows from `SerdeCost`, so
    `AcceptCallees` needs only `Hyp169`, `Hyp81` and their linear bounds.
* **66** (`SerdeFromTrait.lean`). `f66_acc`: on `structDe … = some (a, r)` with
  `skipWhitespace r = []`, 66 (634, 78, 320, 68) returns `Ok(a)` at `(425 + 96·|r|)·c + costS`.
  `f747_zero`, `f68_zero`: the drop of a `Vec` of capacity 0 frees nothing (the scratch never grows on
  this path). `f66_dec` takes `Call.decode`'s acceptance instead (`decode_struct`) and discharges the
  pure facts from `Agrees` (`reader_facts`).
* **The pure facts** (`JsonSuffix.lean`): `skipWhitespace`, `stringBody` (with `hex4`,
  `unicodeEscape`), `number`, `value`/`elements`/`members`, `valueR`, `keyAt`, `colonAt`, `objLoop`
  and `structDe` return a suffix of their input (`drop_suf`: so `bs.drop (|bs| - |r|) = r`); a reader
  that agrees with the model returns a suffix (`agrees_suf`), reads nothing from `[]` (`agrees_nil`)
  and at least one byte (`agrees_strict`, from `value_strict`, `number_strict`).
* **The linear bound** (`SerdeCost.lean`). `Lin646 a b`, `Lin169 a b x`, `Lin81 a b`: a callee's cost
  is at most `a + b` per byte it reads (`+ x` for 169). `objCost_le`, by induction over the members:
  a member reads at least five bytes (the opening quote, its key's closing quote, the colon, a byte of
  its value, the comma or the `{`), so the loop costs at most `K1` per byte when `96, b646, b169, b81
  ≤ K1` and `942 + cost194 + a646 + b646 + a + b ≤ 5·K1` for `a, b` of 169 and of 81 (`hM169`,
  `hM81`). `cost66_le`: then `cost66 ≤ (1725 + a169 + K1·len)·c + x`. 169's fixed cost can go into
  `x` (`a169 = 0`): the field occurs once.
* **`costS`** charges only the form the input is in (it charged both the object and the array form,
  which doubled `K1`: after `{`, a key such as `"account_id"` is itself a valid account id, so `dv`
  succeeds there).
* **Tightened**: 193 at a key `800 → 572`, 228's per-member overhead `60 → 30`; the per-member
  constant of `objCost` is `942` (was `1200`). Lowered until the proof failed (193's checkpoints
  `mcredits` moved with it). Not tightened: 89/90/320's `200` (shared macros), 646's `330 + 30/byte`
  and 927's `100 + 100/byte` (another agent's files), `cost194 = 342` (the length-10 compare is
  charged for every key).

*Findings of this round.*

* **`Hyp169` could not hold** (statement). It asked one cost `K169 j` for every free-list bound `F`,
  but 169 allocates the account's `String`, and the allocator's walk is linear in the free list
  (`AllocWalk.walkCost cfg F = F·320·c + …`). So no `K169` existed, and `AcceptCallees` was
  unsatisfiable. Fixed: `Hyp169 … Fb` assumes `F ≤ Fb`; 228's loop keeps `F ≤ Fb` in `seenRes`
  while the field is not read (646 and 81 leave the heap unchanged); 78, 66 and `AcceptCallees` pass
  the heap's `F` at the entry.
* **The cost per argument byte.** `argumentByteGas` (400 Mgas) is 486 `regular_op_cost`s (822 756
  gas) per byte. The input's other per-byte charges take about 13 Mgas of it (whitespace measures
  92.5 Mgas per byte, of which 339 is at most `96` operations, 79 Mgas), so `K1 ≲ 470`.
  * Proved side (escape-free keys, `a646 = 300`, `b646 = 130`): `K1 ≥ 130`, `K1 ≥ b81`, `K1 ≥ b169`,
    and `1714 + a81 + b81 ≤ 5·K1` (`942 + 342 + 300 + 130 = 1714`). At `K1 = 470`: `a81 + b81 ≤ 636`
    and `b81 ≤ 470`. Before this round's tightening the member constant was `1972` (room `378`), and
    with a four-byte member (without `valueR_strict`) there was no room at all.
  * Measured side (`scenarios/27_arguments_cost.json`, `ft_balance_of` at `bound`, ~100 KB of
    arguments; Mgas per argument byte after the call's fixed 0.37 Tgas): `1,` in an ignored array
    275.5, `0,` 272, `[`…`]` 50 000 deep 263, `[0],` 262, top-level `"":0,` 248, `0.0,` 220,
    `"a":0,` 220, `0e0,` 211, `"":[],` 196, `{},` 186, `-0,` 185, `[],` 180, `"":"",` 172, `"":0,`
    inside an ignored object 169, `"",` 112, `null,` 112, whitespace 92.5. All pass at the model's
    bound: the worst is 275.5 Mgas (335 operations) per byte against 400. **No discrepancy**: the
    binary's true cost per byte stays within the model's bound, with a margin of 1.45×.
  * The proof has little room, though. 81 on a short scalar must be proved within about `636` for
    `a81 + b81`, and per byte of a long ignored array (the worst case, about 320 operations per byte
    for real) within `470`: 81's Wasm proof must keep its constants within about 1.4× of the real
    cost.

*`Hyp169`, and the pieces of 81 (eighth round).* Proved, no `sorry`, standard axioms only:

* **`Hyp169` on an input without `\`** (`SerdeAcctHyp.hyp169_noesc`), for the model's own reader
  `dv = valueAs account` (so `Agrees` is `rfl`), from `SerdeAccountId.f169_s`. `acct_noesc`: where the
  model reads an account id at `j`, the input is whitespace, `"`, the plain bytes `keyBody` (the
  account's UTF-8 bytes, valid, 2..64 of them) and `"` (`valueR_str`, `key_noesc`); so `ok380` holds
  and `res380`/`heapS` give `strRes` (the block `(p, |a|)`, an empty `block` after it).
  * **The heap room, restated.** After the `String`'s allocation the memory may have grown a page,
    and `strRes` asks room for an error box after it. `roomS m maxP := roomFor4 m maxP 20 ∧
    roomFor4 (m + 65536) maxP 20` (`SerdeStructArr`) is now `Hyp169`'s premise, carried by
    `seenRes`'s `None` case, `f228_obj`, `f228_arr`, `f78_acc`, `f66_acc`, `f66_dec` and
    `AcceptContract` (the rejecting contract keeps `roomFor4`). `room_down` gives back `roomFor4`.
  * Cost `K169 cfg bs Fb j`: 169's at the free-list bound `Fb` (`cost380_mono`). `lin169_noesc`:
    `Lin169` with `a = 0`, `b = 208` per byte read (`96` per whitespace byte; `30 + 100` for 646 and
    `from_utf8`, `60` for `is_valid_account_id`, `18` for `memcpy`, other agents' constants) and
    `x169 cfg Fb = (2656 + 320·Fb)·c + linearOpBaseCost + linearOpUnitCost`.
* **The contract with only `Hyp81` left** (`FromSliceNoEsc`): `code169_of`, `acceptCallees_noesc81`
  and `acceptContract_noesc81`: on an input without `\`, the accepting contract's conclusion at
  `(1725 + K1·len)·c + x169 cfg F`, from `Hyp81` (for a reader that agrees with the model) and
  `Lin81 a81 b81`, when `208 ≤ K1`, `b81 ≤ K1`, `1714 + a81 + b81 ≤ 5·K1` and `1714 + 208 ≤ 5·K1`
  (the account id's member: `K1 ≥ 385`).
* **The scratch in `tbl`.** 81 reads the scratch `Vec`'s pointer and capacity (84, 85), which 66 kept
  in its own frame. `tbl n de` now also holds `de + 12 ↦ 1` and `de + 16 ↦ 0` (as 634 leaves them);
  66 splits its `Vec` word into `tbl` before 78 and takes it back for 68.
* **81's callees** (not 81 itself):
  * `ignore_str` (650) on an escape-free string (`SerdeIgnStr.f650_noesc`): `0`, the reader past the
    `"`, at `(56 + 21·m)·c` (`21` is the scan's count, `20` fails); `str_noesc_shape`: the model's
    `stringBody` accepts exactly there.
  * The numbers, on the model's side (`SerdeNumModel`): `intR`, `afterInt`, `fracR`, `afterExp`,
    `expR` are the rests 83/86/87 leave; `vSkip_num`, `vSkip_neg`: wherever `IgnoreModel.vSkip`
    reads a number (at a digit, or after `-`), `intR` reads it with the same rest. The proof walks
    `number`'s code piece by piece (`numFE` is its tail verbatim, with its `do` join points; the first
    digit is split over its ten values so that the literal matches reduce).
  * `next_char_or_null` (88, `SerdeIgnNum.f88_spec`, `74·c`), `ignore_exponent` (87, `f87_acc`,
    `(300 + 127·m)·c`, `127` per digit, `125` fails), `ignore_decimal` (86, `f86_acc`,
    `(465 + 129·m)·c`, with 87's fixed part when there is an exponent).
  * `spec_extend` with the flag 0 (84, `SerdeIgnFrame.f84_none`, `120·c`) and `pop` on the empty
    scratch (85, `f85_empty`, `20·c`): what 81 does when no frame is pushed.

*Findings and tooling notes of this round.*

* **A call costs about 12 more** than the callee's own constant (`1` for `call`, the activation
  `(64 + locals' bytes + 7)/8`), and `peek_or_null` (329) is `65` with its own call of 332. So a digit
  in 83/86/87 costs `127` (329, 333, the tests and two activations). 83 peeks twice at the end of its
  integer part (once to test for a digit, once for `.`/`e`), so a one-digit value costs 83 alone about
  `300`. Estimated for 81 on the one-byte value `0` (prologue and 82, 339's `100`, the dispatch, 83, the
  pop 85, the epilogue, each call's `~12`): about `600`, within `a81 + b81 ≤ 636` (`K1 = 470`) but
  with little to spare; a value with a fraction or an exponent carries 86's or 87's fixed part (`465`,
  `300`) over at least two more bytes. Not proved: the numbers are estimates until 83 and 81 are.
* `mstep` treats a `br_if` and the pure instructions before it as one branch when it cannot step them
  separately: with a symbolic byte, step to the `br_if` and give the side condition as a precomputed
  fact (`mstep_taken with exact h`); a `rw` inside `with` fails with "internal exception #5". After an
  `mcall`, `mcredits` to a literal multiple of `c` plus atoms; generalize the per-digit product
  (`127 * (e - k) * c = Z0`) before stepping, or `omega` sees `(127·x + E)·c` as one atom.
* A callee's cost that is a function application (`cost87 m * c`) must be rewritten to literal
  multiples of `c` plus atoms before `mcall`, or the call's cost goal fails.

*`ignore_value` (81) on the shallow values, and the accepting contract with no hypothesis (ninth
round).* Proved, no `sorry`, standard axioms only:

* **Route (a), the shallow skip.** `Hyp81` asks the heap unchanged, which holds only when 81 pushes
  no frame (a second bracket inside a first grows the scratch from capacity 0, through 698/712–716
  and the allocator, and changes the heap across 228's loop). `IgnoreShallow.ign1` reads a scalar, or
  one `[`/`{` whose elements or members' values are scalars, with `IgnoreModel.ignM`'s steps at depth
  at most 1 (`scal`, `cont1 f n`, `open1 f n`). `ign1_sound`: `ign1` reads what `vSkip` reads;
  `structDe_mono`, `decode_of_shallow`: where serde's struct machine with `ign1R` reads `a` and then
  only whitespace, `Call.decode` reads `ftBalanceOf a`. Route (b) (scratch growth for any nesting) is
  not done.
* **323** (`SerdeIdent.f323_spec`): `parse_ident` against the literal bytes `identBytes` (`alserueull`,
  at 1048576), at `cost323 len = 72 + 75·len`. `tbl` and `roData` now hold `identBytes`; 66, 169's
  hypothesis and 228's loop carry it.
* **83** (`SerdeIgnInt.f83_acc`): against `SerdeNumModel.intR`, at `cost83 bs i rest`: `197`, `127` per
  integer digit (`intEnd`), and `tail83`: `20 + cost86 m` after a `.`, `20 + cost87 m` after `e`/`E`,
  `0` otherwise. The path decides the cost. `cost83_le`: `cost83 + 343 ≤ 197 + 470·bytes` (the
  one-digit number is the worst, `324`).
* **81** (`SerdeIgnValue.f81_shallow`): where `ign1` skips from `j` to `r`, on an input without `\`,
  `0`, the reader at `|bs| - |r|`, within `(166 + 470·(|bs| - |r| - j))·c`. The loops' invariants carry
  `470` per byte left plus a constant by state: `109` (the first value, after the prologue's `57`),
  `60` (a value inside the frame), `250`/`200` (just after `[`/`{`: the container's loop must break
  to a value without reading a byte), `75` (before an element), `0` (after a value, before a member's
  key: the key's bytes pay). The three blocks of a value, the container's loop and the break code
  are each proved once (`mwpi_split`: run a prefix to where it falls through, state that as a
  postcondition, then the rest), with macros for the six scalars (`vbody`), the scalar-done code
  (`sdIn`, `sdTop`), the brackets (`brPre`, `brTail`) and the close (`closeTail`). 85's pops always
  return `None` at depth 1, so the container's loop (`loop @6`) never repeats.
* **The contract** (`FromSliceShallow.acceptContract_shallow`): on an input without `\` where the
  shallow machine accepts (`structDe "account_id" (valueAs account) ign1R bs = some (a, r)`,
  `skipWhitespace r = []`), `Call.decode` reads `ftBalanceOf a`, and 66 returns `Ok(a)` within
  `(1725 + 470·len)·c + x169 cfg F`. No hypothesis left: `Hyp646` (escape-free keys), `Hyp169`
  (`hyp169_noesc`), `Hyp81` (`hyp81_shallow`, `K81s`, `lin81_shallow`: `a81 = 166`, `b81 = 470`), the cost
  (`cost66_struct`: `cost66_le` from `structDe` instead of `decode`, for readers that return
  suffixes).
* **`K1 = 470`**, at the bound: the member condition `942 + cost194 + 300 + 130 + a81 + b81 ≤ 5·K1`
  holds with equality (`1714 + 166 + 470 = 2350`). The account id's member: `1714 + 208 = 1922`.

*Findings and tooling notes of this round.*

* The proof's per-byte accounting fits `K1 = 470` without a structural change, but only just: the
  one-byte top-level number (`0`) costs 81 at most `166 + 470 = 636` (the prologue and 82 `57`, 339
  `113`, the dispatch about `60`, 83 `324 + 12`, the pop and the return about `45`). Calibration:
  lowering the first value's constant from `109` to `89` (as `a81 = 146` would) breaks both bracket
  paths and a top-level scalar path, so the slack is under `20·c`. 83's fixed part calibrates to
  `197` (`192` fails), 323's per byte to `75` (`70` fails).
  The slack left in the binary is the proof's: 339's `100`, 82's `30` (343's spec; the real cost is
  about half) and 84's `120` are loose bounds, which a tighter proof of them could recover.
* The scalar block, the container's loop and the break are long; proving each once needs the rule
  `mwpi_split` (`mwpi_seq` and `mwpi_wand` with a postcondition whose `normal` is the state where the
  prefix falls through). Without it, the container's loop would be proved once per scalar kind.
* `mstep` normalizes `k·c + X·c` into `(k + X)·c` when `X` is a product: generalize every per-byte
  product (`470 * (q - p) * c = Wp`) before stepping.
* Byte tests on a byte variable: rewrite the shifted byte first (`ob16`: `(optByte (some b) >>> 16)`
  is `b`, `band255`), then give each comparison as a precomputed fact (`t93`, `t125`, `t44`, `dig_lt`,
  `eqb_zero ∘ dig_ne`) by `decide` over the 256 bytes.
* A frame `fr81 …` must be unfolded (`simp only [fr81]`) before an `mcall`, or the callee's activation
  cost (from `entryLocals` of the frame's locals) does not reduce.
* `simp only` closes `1 = 1` conjuncts to `True`; state such goals with `show` instead.

*What is left for the parser's contract.*

* Deeper ignored values (route (b)): a bracket inside a bracket. 84 pushes onto the scratch, which
  grows from capacity 0 (698 → 716/714 → the allocator), so `Hyp81` must let the heap and the scratch's
  `(ptr, cap)` change, 228's loop and `tbl` must carry them, and 66's drop (68) must free a nonempty
  scratch. 81's proof would need a value loop with a stack of frames (`IgnoreModel.ignM` already
  gives the steps).
* Keys and account ids with escapes: `Hyp646` beyond escape-free keys, and 169's escape path (the
  escapes agent's 646).
* The rejecting half (`RejectContract`): 340, 165, 166, 177, 326, 92, the error paths of
  193/214/228/81/83/86/87/323/650, 642/643, 693/479/130/387/151, at some cost. Not started.
* The method's side: `heapInv` at 297's call with `F` bounded, the memory room `roomS` (a page for
  the account's `String`, then an error box), the per-byte budget (`K1 = 470` against the other
  per-byte charges, `K0 + X` in `computeGas`), and the restriction to shallow input (or route (b)).

*Plan for the rest of the parser's contract, bottom-up.*

1. **The rejection side needs no tight cost.** `Refines` asks only `RolledBack` for input
   that is not a call, and `method_vm_any` turns a run that runs out of gas into a gas
   failure. A reject path therefore needs a spec that ends in `Err` (then 881's panic) with
   *some* finite cost, say polynomial in `len`. The tight `K0 + K1·len` is needed only on
   the accepting path.
   * Done (seventh round): `AcceptContract` with the tight cost, `RejectContract` at some finite
     cost.
   * Error constructors can then be specified once, generically: they return a boxed
     `Error`, the heap invariant is kept, the cost is at most `E0 + E1·len`, and the output
     says nothing more. This applies to 322/325 (`position_of_index` is linear), 340, 642
     and 643 (`format!` through `core::fmt::write` 872 and the vtables of M5), and the
     drops 92/341/151.
   * Done for the syntax errors 647/657 (`SerdeErrBox.f647_spec`, with 638/645/609, 639, 590,
     624, 625): `Err(box)`, at most `costErr cfg F i`. Also done: 325, 322 and 640 (`SerdeErrRet`). Still to
     do: 340, 642/643 and the drops.
2. **Strings: `parse_str` (646) against `stringBody`.** Prove the spec in this order:
   * (a) the plain case: no escape, so the `Borrowed` slice, with `as_str` on bytes known to
     be UTF-8;
   * (b) escapes (649, 653, 605 and the scratch appends 613/614) against `unicodeEscape` and
     the simple escapes;
   * (c) the reject cases: a control byte, EOF, a bad escape, invalid UTF-8.

   `from_utf8` (927, 443 instructions) is the hardest leaf. Do its ASCII fast path first,
   which is enough for keys and account ids, then the general validator against
   `String.fromUTF8?`. The general one is needed because the model accepts any UTF-8 key
   for an unknown field.

   Done: the general validator (`FromUtf8Gen.f927_spec`), and `as_str` on every input
   (`f648_spec_valid`, `f648_spec_bad`).

   Done: (c) except a bad escape, with `ParseStrErr.f646_spec_noesc` on every escape-free input.
   Left: (b), the escapes. They need the scratch `Vec<u8>` to grow:
   * the chain is 613 → 588 → 589 → 623 → 630 → 631 (`grow_amortized`) → 627 (`finish_grow`), with
     608 and 628;
   * it is not the chain `VecGrow` proved: 631 and 627 differ from 716 and 714;
   * the first growth of the scratch starts from capacity 0, so 627 allocates (625 through 624, at
     alignment 1, now proved in `SerdeString`) instead of reallocating.

   Done since (no `sorry`), all but 646 itself:
   * The scratch's growth, `ScratchGrow.lean`. The buffer is `sbuf n maxP hl live F ptr cap bs`: `bs`
     then junk, no block when `cap = 0` (the dangling 1), else the lent block `(ptr, cap)`.
     * `f627_alloc` (624 on no current memory) and `f627_realloc` (312 on `Some(ptr, cap)`);
     * `f631_spec`: `growCap cap (len + k)`, both cases, the free list's bound `F + 2`, the memory grown
       or not (`grownLen`);
     * `f630_spec`, `f628_ok`, `f623_spec`, `f589_spec`: the reserve, through `capAfter`, `fAfter`,
       `hlAfter`, `costRes` (0 when the bytes fit), with `roomRes` for the growth;
     * `f614_spec` (push, `costApp`), `f588_spec` and `f613_spec` (append `k` bytes from memory,
       `costExt`, the copy 951).
   * The readers of `parse_escape`, `SerdeEscErr.lean`, `SerdeEscRead.lean`:
     * `f651_eq` (651 is 325's code), `f656_eq` (656 = 654), `f654_spec` (325 with the box packed
       `errPack p = (p << 32) | 1`);
     * `f655_spec` (`next_or_eof`): `Ok(b)` packed `okPack de b`, or the box at the end;
     * `f653_spec` (`decode_hex_escape`): `res653` on the model's `hex4`: `Ok(n)` (`hexPack n`), the
       reader 4 further, or a box; the table `hexTable` (`hexData_segment`), `hexAcc`, `hex4_eq`.
   * `encode_utf8` (605), `EncodeUtf8.lean`: `enc605 c` at the buffer, and `enc605_eq`: equal to
     `String.utf8EncodeChar (Char.ofNat c)` on a valid code point.
   * `parse_escape` (649), `ParseEscape.lean`, `f649_spec`, on every input:
     * `escDecode` (`EscModel.lean`) is the escape as the model decodes it, through the model's own
       `unicodeEscape`; `res649` is `0` with the escape's bytes appended to the scratch (614 or 605 +
       613) and the reader past the escape, or a box (`sbufE`: the scratch unchanged, the box allocated);
     * every path is covered: the 8 simple escapes, `\u` in the BMP, a lone trailing surrogate (17),
       a high surrogate then not `\`, not `u` (20), a bad second hex, a second surrogate that is not
       low (17), the pair; EOF at each read; an invalid escape (11);
     * the cost `cost649`: a constant, 8 error bounds, and the append's `costExt`.
   * The model side, `EscModel.lean` and `StrModel.lean`:
     * `stringBody_esc`: `stringBody` after a `\` follows `escDecode`;
     * `strRun l acc`, `parse_str`'s run (scan, append, escape) with outcomes `.ok bytes rest`, `.eof`,
       `.ctrl`, `.badEsc`, and `strRun_model`: `stringBody l acc.reverse` is
       `some (String.fromUTF8? bytes, rest)` on `.ok`, `none` otherwise;
     * `StrCost.lean`: `costRun` and `roomRun`, the cost and room of a run (per segment: scan,
       `cost927`, the appends' `costExt`, 649's bound, an error box).
   * **No disagreement** between serde_json 1.0.60 and the model on escapes. 649 rejects lone and reversed
     surrogates (`DC00..DFFF` first: 17; `D800..DBFF` not followed by `\u` + `DC00..DFFF`: 20 or 17),
     as `unicodeEscape` does; the pair's code point is always valid (the code's `char::from_u32` check,
     14, is unreachable), as the model's `isValidChar` check is.
   * **646 on every input**, `ParseStrEsc.lean`, `f646_spec`:
     * from the reader's index `i`, the scratch empty with any capacity (`sbuf … ptrS capS []`), the
       tables (`escTable`, `utf8Width`, `hexTable`); the result `resStr` by the run's outcome
       `strRun (bs.drop i) []`: `Ok(Borrowed(ptr + i, len))` when the string has no escape
       (`borrowed`), `Ok(Copied(p, len))` with the scratch holding the bytes otherwise, both when the
       bytes are UTF-8 (`as_str`); else `Err(box)` (`errStr`: the box after the scratch, `sbufE`);
     * the cost `costRun cfg F capS [] (bs.drop i) bs.length + 100·c`, with room `roomRun`; the stack
       192 bytes;
     * the outer loop `@7` runs once per escape; its invariant holds the reader at `j`, the scratch
       `acc` (`sbuf`), `strRun (bs.drop j) acc = strRun (bs.drop i) []`, `acc = [] ↔ j = i`, the bounds
       `|acc| ≤ j - i`, `cap ≤ max capS (2·|acc| + 8)`, `roomRun` and `costRun` credits;
     * at `"` with a non-empty scratch: 613 (the last plain bytes), 728, then 648 on the scratch
       (`f648_spec_bad_mem` is `as_str` on bytes anywhere in memory);
     * `str_model` (`StrModel`): on `.ok bytes rest`, `stringBody` decodes the string whose bytes are
       `bytes` when they are UTF-8, and `some (none, rest)` otherwise; on `.eof`, `.ctrl`, `.badEsc` it
       is `none`. With `resStr` this is the complete statement: `Ok` exactly when `stringBody` decodes
       a string, with the same bytes; `Err` exactly when it gives `none` or `some (none, _)`.
     * 649 is split into `f649_nu` (not `\u`), `f649_u0` (`\u` without a high surrogate) and
       `f649_u1` (a high surrogate), joined in `f649_spec`: one declaration took over an hour.
   * The earlier plan to bound the existing `costRun` linearly is superseded: its reserved
     error scans give a proved quadratic lower bound on accepted newline escapes
     (`StrCostLower.costRun_newlineEscapes_quadratic`, misstatement log entry 8).
     `SerdeEscSuccess` supplies constant-cost successful byte/hex readers;
     `ParseEscapeSuccess` uses them for simple and non-surrogate Unicode escapes;
     `ParseEscapeSurrogateSuccess` covers valid pairs. `ParseEscapeSuccessCost.f649_success`
     combines the three paths, with instruction cost at most 200 regular operations
     per encoded byte consumed (including the leading backslash), plus the separate
     scratch-growth/copy charge.
     `ParseStrSuccess.f646_success` now supplies the successful outer loop, charging
     UTF-8 validation once. `StrSuccessCostBound` separates linear instruction work
     from append charges; `ParseStrSuccessBound` exposes the callable bound.
     `ScratchAmortized.copyOps_linear` bounds all old-buffer reallocation copies.
     `ScratchFast` tightens fitting pushes and the slice-append reserve chain;
     `ParseEscapeFast` reduces simple-escape dispatch to 240 operations plus the
     capacity-sensitive push charge. The loop uses them with a 300-op segment reserve.
     `ParseStrSuccess.f646_success_fit` (`ParseStrFit.lean`) now meets 470 ops per consumed byte, including
     all append and UTF-8 work, when scratch capacity covers the unread input.
     `StrGrowthTrace` now connects the actual append sequence to copy, capacity,
     page and logarithmic growth-count bounds. `ParseStrSuccess.f646_success_growth` (`ParseStrGrowth.lean`)
     exposes the full call with the remaining closed `growthBudget` (initial free-list
     bound, growth count, copies and memory-growth fees). Borrowed strings no longer
     reserve a nonexistent terminal scratch append.
     `f646_success_traced` and `f646_success_growth_traced` retain the concrete
     trace endpoint in `resStrTraced`: copied results expose exact scratch
     capacity and allocator free-list bound, and memory length lies between the
     initial length and that length plus the trace's charged pages. The suffix
     invariant in `StrTraceResult` composes both appends at every escape and the
     final plain append. The old success interfaces follow by forgetting these
     additional facts; their preconditions and gas budgets are unchanged.
     Left: absorb this budget into the method allowance using the reachable heap
     invariant. Generalize the old heap-preserving struct-reader hypotheses for
     changing scratch state; do not assume a uniform bound for arbitrary initial
     free lists. `SerdeDeStrEsc.f380_copied_growth` now integrates the successful
     copied path through 646 and 633, retaining both scratch and the owned string
     in the allocator invariant. `SerdeAccountIdEsc.f379_copied` and
     `f169_copied_model` carry it through 379 and the valid-account-id conversion,
     starting from the model's decoded string. They require allocation room at
     the trace's maximum memory length and retain all growth/owned-copy charges.
     Their complete frames/depth premises are 240 bytes / `d + 32` for 379 and
     288 bytes / `d + 33` for 169. `SerdeValueState` now exposes that changing state
     at the sequence-element boundary. `SerdeSeqElemEsc.f214_copied` and
     `SerdeMapValueEsc.f205_copied` integrate the concrete reader into both value
     callers. Successful colon and closing-bracket contracts frame their caller's
     state through. `SerdeStructArrState.f228_arr_state` generalizes the array
     proof; `SerdeStructArrEsc.f228_arr_copied` instantiates it from the JSON
     model's decoded string, restoring 368 bytes and nesting depth, at `d + 35`.
     `SerdeScratchValueDrop.f68_value` now frees scratch while retaining the owned
     String and earlier live allocations, with the final allocator and memory
     bounds. `SerdeStruct78Esc`, `SerdeFromTraitEsc` and `FromSliceEsc` carry the
     copied array through the actual 78/66/65 entry and cleanup. The complete
     448-byte frame is restored, at `d + 38`; final whitespace is checked by a
     heap-independent successful 320 contract. `f65_arr_okAt` supplies the existing
     result shape under explicit shape/room/growth-cost premises. Left: the object
     loop and escaped keys; the full accepting contract needs hex-table ownership
     added to its read-only resources and reachable heap/room/gas bounds. The older
     no-escape interfaces are unchanged. General rejecting value paths remain open.

   `ignore_str` (650) and `ignore_escape` (652) are the same scan without UTF-8. Their spec
   is acceptance and the rest, as `stringBody` gives them, ignoring its first component.
3. **The value: `ValidAccountId`.**
   * `deserialize_str` (380): whitespace, then `"`, then `parse_str`, then `visit_str` (633
     → 618 → 626 `allocate_in` with the allocator, then `memcpy`). The `String` it returns
     lies in a fresh block.
   * `is_valid_account_id` (554) is done.
   * `TryFrom` (502); and 169 with the `Err` path, which drops the `String` (479) and
     formats the error through 130/387.
   * Done, on escape-free strings:
     * 380 (`SerdeDeStr.f380_s`) and 633/618/626 (`SerdeString`);
     * 502/501/169 on a valid account id or a failed string (`SerdeAccountId`).
   * Left:
     * a string with escapes (646's escape path);
     * a value at the field that is not a string (340);
     * the error for an invalid account id (693, 479, 130, 387, 151).
4. **Ignored values: `ignore_value` (81).**
   * First a pure Lean lemma. Define the iterative machine 81 implements, with an explicit
     stack of `[`/`{` frames, and prove it accepts exactly what `NearInterface.Json.value`
     accepts, with the same rest. The model is recursive, through `value`, `elements` and
     `members`.
   * Then the Wasm proof against the machine. The frame stack lives in the scratch `Vec`
     (84 push, 85 pop, growth 698/712–716), and it needs heap room of one byte per open
     bracket.
   * The numbers 83/86/87 go against `number`.
5. **The struct: `deserialize_struct` (228).**
   * Again first a pure Lean lemma. Define serde's struct machine: `{` or `[`; then
     `next_key_seed`, the field visitor, `next_value_seed`, a seen flag, `duplicate_field`
     and `missing_field`; then `end_map` or `end_seq`. Prove it agrees with
     `(parse bs).bind (structFields ["account_id"])` followed by `required account`. It must
     agree on acceptance and on the account, up to the trailing whitespace that `end` (320)
     checks. This lemma is the formal form of the "no discrepancy" check above.
   * Then the Wasm proofs of 193, 205/201, 89, 90/91, 214 and 228 against the machine. The
     loop invariant holds the `Option<ValidAccountId>` read so far: a lent heap block, or
     none.
   * The depth byte goes 128 → 127, and `RecursionLimitExceeded` is unreachable.
6. **66 itself:** done (seventh round): `f66_acc`, `acceptContract`, and the linear bound
   `SerdeCost.cost66_le`. `K1` is limited by the member constant over five bytes and by 81's cost per
   byte (see the findings of the seventh round): the room is about 1.4× the real cost. The rejecting
   half comes from step 1.
7. **The other methods.** Steps 1–4 are shared by every parser. Step 5 is one instance per
   struct; state it generically over the field list and the field visitor, so that 222,
   221, 224, 229 etc. come from the same proof. `U128` adds `u128::from_str_radix` (871,
   with `__multi3`). `bool` adds 167, then 323. `Option` adds 168–172.

**Rejection continuation (2026-10-29):** the rejecting contract's cost now precedes the gas
ceiling (misstatement 7). The former rejection WIP is active as `SerdeRej.lean`; its `f78_rej`
forwards a rejecting 228 specification. `SerdeRej.f68_scratch` (`SerdeScratchDrop.lean`)
frees an empty or grown scratch in 315 regular operations. `SerdeRej.f66_struct_rej` propagates
the struct error, frees its scratch and restores the complete frame at `1000*c + K F`.
`FromSliceSpec.struct_reject_uniform` and `f65_struct_reject_uniform` expose that branch through
the public parser contracts uniformly in the ceiling (65: `1045*c + K F`). These theorems
remain conditional on the actual 228 rejection proof; trailing-character errors are separate.
No claim that `RejectContract` is complete follows from these wrappers.

**Trailing/EOF continuation:** `SerdeRej.f66_trailing` now proves the trailing-character
branch after a successful struct, including both drops and stack restoration. The error
allocation's cost uses `AllocInv.heapInv_finite` (`AllocFinite.lean`), derived
from the free list's distinct addresses and the heap geometry. `FromSliceTrailing.lean`
provides uniform public contracts for 66 and 65. `SerdeStructEOF.lean` proves 228's actual
EOF rejection and discharges `Rej228` for whitespace-only input; `FromSliceEOF.lean`
connects that concrete case through 65 without an assumed parser-callee contract.
Other 228 error cases and integration of the general escaped/deep readers remain open.

**General object-key continuation (2026-10-29):** `SerdeKeyEsc.f646_key` now
adapts the general successful 646 reader to the existing key boundary by carrying
its additional 32 stack bytes in the abstract state. `f193_key_model` proves the
actual next-key call for borrowed or copied model-decoded keys, including scratch
length clearing, all three string tables, the 208-byte frame and the explicit growth
budget. `SerdeObjectState.keyState_reuse` exposes common returned scratch coordinates
and bounds; `parsed_capacity` preserves the next reader's capacity premise with the
sharper bound `max oldCapacity (max 8 (2 * finalUsed))`. `AllocLivePerm.heapInv_perm`
and `valueStorage_reuse` preserve the owned account-id String while reordering scratch
for subsequent keys. The next task is the actual changing-state object loop; its
value-reader interface must also cover a borrowed/plain value with already-grown
scratch. Deep ignored values/ignored escapes, full rejection and uniform reachable
room/gas bounds remain open. The completed-method count stays six.

**Unified value continuation (2026-10-29):** `SerdeValueReuse.f169_borrowed_model`
reuses the existing plain-reader body proof with scratch already in the live list,
framing its descriptor and spare bytes. `f169_model` now accepts every valid
model-decoded string through the borrowed or copied path and returns `ownedValue`,
with the String live and scratch reusable. `spec169_model`,
`SerdeMapValueReuse.f205_model` and `SerdeSeqElemReuse.f214_model` carry this through
both immediate value callers. `valueCost_le` places either branch under the existing
growth-aware copied-reader charge. The next task is the actual object loop, whose
state must unpack and update scratch coordinates after each member while retaining
the owned account-id allocation. The exact endpoint hidden in `ownedValue` cannot
be assumed unchanged after a later key grows scratch. The accepting method gas/room
bounds, deep ignored values/escapes and general rejection remain open; still six
completed exported methods under protocol premises.

**Changing-state object-loop continuation (2026-10-30):**
`SerdeStructObjState.f228_obj_state` proves the full actual object path with
cursor-indexed member state, allowing keys and ignored values to change heap and
scratch while preserving a saved account-id String. It restores all 368 stack
bytes and nesting depth, at the existing `objCost` and `d + 42`.
`SerdeEndMapSuccess.f90_close` frames the changed resources through the successful
closing `}`. `SerdeStructObjKeyState.keyHyp` and
`SerdeStructObjValueState.valueHyp` instantiate the concrete key and account-id
calls; their remaining `KeyConditions`/`ValueConditions` are pure room, charge and
reachable-state closure obligations. The concrete member state uses separate
`B`/`Bsaved` bounds before and after the one-time account-id allocation, so the
pure value closure does not demand repeated String allocations (misstatement 9).
Allocator alignment and positivity come from the actual scratch/heap invariant;
they are separate premises of room conditions, since numerical bounds are closed
over growth intervals containing unaligned integers (misstatement 10). The shared
state retains the literal table needed by ignored values, and the assembled theorem
accepts an additional persistent code context for that reader's callees
(misstatement 11).
`SerdeStructObjModelState.f228_obj_model`
assembles those readers with the actual loop. The ignored reader stays parameterized
by `Agrees ign valueSkip` (literal model skipping on malformed numeric prefixes
would be too strong). Remaining: prove reachable member-state bounds and the
ignored-reader transition, carry the object result through 78/66/65 cleanup, and
finish general rejection. The general key allowance (`500 + 470 * consumed`)
is 540 operations more than the old borrowed-key allowance at an empty key;
dense short members therefore need the tighter borrowed-key contract with grown
scratch framed through. Separate scratch-growth charges also still need absorption,
potentially using tighter successful instruction estimates. Full accepting coverage
and the seventh method remain open.

**Borrowed-key charge continuation (2026-10-30):** `SerdeKeyReuse` reuses
`f646_key_noesc` with allocated scratch framed through, selects that proof or
`SerdeKeyEsc.f646_key`, and carries the selected charge through the actual 193
call. The borrowed charge is exactly `300 + 130 * consumedBytes`; an empty key
therefore recovers the old 430-operation allowance even after an escaped member
has grown scratch. `keyCost_le` bounds the selected charge by the previous
allowance. `keyRoom` also removes hypothetical borrowed scratch appends from the
room obligations. The changing-state `KeyConditions`/`keyHyp` now use those
interfaces. This closes the borrowed-key obstruction described above; copied-key
charges, reachable bounds, ignored values, object wrappers and general rejection
remain open. No uniform accepting result or seventh method is claimed.

**Reusable shallow ignored-state continuation (2026-10-30):**
`SerdeIgnValue.f81_shallow_reuse` keeps arbitrary scratch pointer/capacity through
81's existing shallow proof; the original `f81_shallow` is its empty-scratch
specialization. `SerdeIgnReuse.f201_shallow` and `ignoreHyp` carry it through the
actual colon/value call and the changing-state object's member invariant,
framing heap/buffer bytes and any saved account-id String. The existing shallow
charge is unchanged. The global no-escape premise and shallow decoder remain;
this is not the complete ignored reader. Successful ignored escapes (652/650)
and allocating nested-frame pushes are the next reader steps, followed by the
remaining accepting room/gas bounds and object wrappers.

### M7. State and storage

Borsh encoding of the state, `LookupMap` keys, near-sdk's `env` wrappers
over registers and storage, against `Model/Storage.lean`; host contracts
for storage with worst-case trie charges.

### M8. Every method

The remaining 14 methods, roughly in order of size: the views; `new`,
`near_deposit`, `storage_*`; `ft_transfer`, `near_withdraw`;
`ft_transfer_call` and `ft_resolve_transfer` (promises, prepaid gas
arithmetic, promise results). A `refinement-stress` round before each.

*`storage_balance_bounds` (306) is done* (`storageBalanceBounds_refines_all`, `Bridge/Methods/StorageBalanceBoundsRefines.lean`, standard axioms only; on an uninitialized contract the `PanicOnDefault` panic). It returns `{"min":"N","max":"N"}` through `serde_json`'s struct serializer (108), proved on a generic output `Vec` (`SerdeStruct.outV`) with reusable pieces: `write_all` (`wa_out`), one-byte punctuation (`piece_out`, `pieceFn`), strings in a zero chunk of `ESCAPE` (`str_out`, `SerializeStr.f383_esc`), the first and later keys of a struct (`keyFirst_out`, `keyRest_out`, `keyFn`), a `U128` value into a non-empty `Vec` (`f385_out`), the `U128` and `Option<U128>` fields (`f384_first`, `f109_some`), the struct end (`f106_end`). The second `to_string` allocates on a free list of three cells (`costAllocF cfg 3`). The body (`StorageBalanceBoundsBody`: a 128-byte frame) copies `FtTotalSupply.segA`, `U128View.segCG` and `segBNoneG` for its offsets. Left: the code size, `CostsV86` and `LimitsV86` (M9).

*`near_deposit` (234) is in progress.* Proved (standard axioms only): `predecessor_account_id` (526, `PredecessorId.f526_spec`, with `String::from_utf8` 512 on `FromUtf8Gen.f927_spec` and `Result::expect` 499); `LookupMap::contains_key` (394/396, `LookupMapContains`); `get` (399/400) and `storage_read` (548) on `heapInv … F` (`LookupMapGet`, `StorageReadWrapF`); `insert_raw`/`insert` on a present key (391/401, `LookupMapInsertSome`, `writePost_reg`); `internal_unwrap_balance_of` (405), `internal_deposit` without overflow (406, `f406_ok`, the host as `Post406`, chained with `StorageReadPost.next`), `internal_register_account` on a new account (409, `f409_ok`), and the 128-bit checked add (`Add128`). The panic texts and the log's pieces in the data segment match the model (`"Deposit "`, `" NEAR to "`; `w_near.rs:15:9`, `:20:13`; `core_impl.rs:108:55`; `"Balance overflow"`). Left: the log (`alloc::fmt::format` 846 with two arguments, the `u128` and `String` `Display` through the table, `Formatter::pad`), the body 232 and the method 234 (state read/write, gas, `Refines`), and the panics through the Rust panic hook (`begin_panic` 664, `expect_failed` 879), which no method has needed yet.

*The log of `near_deposit` (and of every method that logs through `format!`), in progress.* Proved (standard axioms only), each parametric in its callees:
* `core::fmt::write` (872) on `fmt: None` with `k = pieces.len = args.len ≥ 1` (`FmtWriteN.f872_gen`): the callees and the arrays bundled in `Hyp872`, the writes as a family of states `St i`, the `Formatter` as `fmtrP` (`fmtr` and the precision tag). Split in `tail872_spec`/`iter872`/`f872_gen`: in one piece the loop body sent the kernel into a deep recursion.
* `Formatter::pad` (856) without width or precision, `<str as Display>` (923), `<String as Display>` (179, table entry 6) (`FmtStrPad`). The `u128` argument (table entry 5) is `FmtDisplay.f901_spec`.
* `alloc::fmt::format` (846) (`FmtFormat.f846_gen`): the capacity loop (`psum` of the piece lengths, `L ≥ 16` gives `cap = 2L`; 17 for `"Deposit "`/`" NEAR to "`), `__rust_alloc` on `heapInv … F` (`f310_roomG`), the `Arguments` copied, and 872 as a premise for the block returned.
* The `String` sink of 846 is not 759: the vtable 1066728's `write_str` is table entry 189, function 840, which appends with `spec_extend` 841 and grows through `finish_grow` 845 (other monomorphs than `FmtSink`'s and `VecGrow`'s). Proved: 840/841 with room (`StrSink`), 845 on a nonempty buffer (`StrGrow.f845_spec`, through `VecGrow.f312_spec`).

*The log is done* (standard axioms only): 841/840 without room through 845 (`StrSinkGrow.f841_grow`, `f840_grow`, 48 bytes of stack); `format!`'s `String` as a sink reallocated at most twice (`StrSinkMulti.ssink`: after `j ≤ 2` reallocs the free-list bound `fIt F j`, the memory at most `j` pages past `L0`, the capacity in `[c0·2^j, c0 + 2B + 8]`; `ssink_w`: `write_str` with room or grow, `B ≤ 4·c0`, the grow's worst price `gmax` on every write); `Hyp872` for the log (`DepositLog.hyp872_log`: the pieces through `ssink_w`, the `u128` through 901 with `ssink_w` as `sinkSpec`, the `String` through 179; `lSt i` the state after `i` writes, 192 bytes of stack below 872's frame) and `f872_log`; 846 on it (`f846_log`, capacity 34, `L0 = hl + 65536`); the whole end of 232 after 406 (`DepositTail.tail232_spec`, its code checked against the binary by `tail232_eq`): `ArgumentV1::new` (354, 745), the `Arguments` and arrays, 846, 779, `log_str` (546) of the text, the two drops (68), `sp += 144`, `return`; the heap left with `F' ≤ F + 4`, at most three pages grown, the account's block freed. The text is the model's (`NearDepositLog.logW_model`, `log_utf8String`). 272 bytes of stack below 232's frame.

*The panics through Rust's machinery are parameters* (`Methods/NearDepositPanics.lean`): `Spec664 … mp ml loc text` and `Spec879 …`, `MFunSpecT` facts of the shape of `PanicStr.f156_spec` (trap postcondition `panicked Cg h text`), with the caller-side resources `Pre sp h`, the cost `K h` and the depth `D` left to the specification; `DepositPanicSpecs` bundles the three call sites (664 at 1050492/34/1050540 and 1050556/21/1050580 in 232, 879 at 1053016/21/1053040 in 363). The payloads and locations in the data segment are checked against the model's texts (`payloadPositive_data`, `locPositive_data`, …).

Left for `near_deposit`: the body 232 before the tail (529, 526, 394, 418, the comparison, 409, 418, the subtraction, 406: the callee specs exist, the chain of `heapInv`/`LenIn` and of the host relations `StorageReadPost`/`StorageWritePost`/`Post406` must be threaded, as `NewBodyOk` does for `new`); the balance overflow through `panic_str` (521) needs 406's overflow path; 234 (522, 520, 219, 155, 232, 220, 68); the method level (`MethodRunsR` and adequacy, `AgreesWith` with the accounts map in `encodeState`, `hbound`, `hpre`, the premises from `Context.WF`). The tail needs `LogOk` for the text (UTF-8 validity, `LogFits`), from the predecessor's `utf8Ok` and the log limits.

The panic messages: Rust 1.51's `PanicInfo` `Display` is `panicked at '{payload}', {file}:{line}:{col}` (the pieces `"panicked at '"` and `"', "` are in the data segment), near-sdk 3.1's hook passes `info.to_string()` to `panic_utf8`, so `Panic.message`'s `rustPanic` texts for `requiresPositiveDeposit` (`src/w_near.rs:15:9`) and `depositTooSmall` (`:20:13`) are what the hook formats; not yet proved (664 → 662 → the hook → 872 with `fmt: Some` → `panic_utf8`). Reachability: `deposit` checks the balance before the supply; with `supply = Σ balances`, the balance overflow needs `b + amount ≥ 2^128`, the supply overflow another holder; both are reachable in the model, whose attached deposit is any `u128`. The subtraction overflow after registration (853) is unreachable: `storageMin ≤ amount` was checked against the same `storage_balance_bounds` (418 twice).

*`ft_metadata` (309) is done* (`ftMetadata_refines_all`, `Bridge/Methods/FtMetadataRefines.lean`, standard axioms only; on an uninitialized contract the `PanicOnDefault` panic). Its JSON is 138 bytes, the serializer's `Vec` 128: the write of the key `decimals` reallocates it. The grow path is generic: `__rust_realloc` (312 → 238 → 154, `VecGrow.f154_spec`) on any free list (`AllocWalk581.f581_spec_walk`), `finish_grow`/`grow_amortized` on a nonempty buffer (714, 716) and `write_all` without room (`VecGrow.f345_grow`, 80 bytes of stack). Above it, `WriteSink.WaSpec` specifies `write_all` on an abstract sink, and `WriteSink.vsink` (the `Vec` and its heap, before or after one doubling of the capacity) satisfies it (`vsink_wa`, room or grow, the grow's price charged on every write); the serde pieces are proved once over any sink (`SerdeSink`: `f346_s`, `f344_s`, `strFn_s`, `piece_s`, `keyRest_s`, the `u8` field `f105_s`). The struct (`MetadataStruct.f102_meta`) writes six fields with room (`MetadataFields`) and the `u8` field through `vsink`; the body (`FtMetadataInit`: `segM309`, `segC309`, `body309`) needs room for eight one-page grows (`HeapRoom8`) and 1024 bytes of stack. Left: the code size, `CostsV86` and `LimitsV86` (M9).

**Completion update, 2026-10-29 continuation:** `near_deposit` is done on all represented
states under the explicit protocol and code-size premises (`NearDepositMethod.nearDeposit_refines_all`,
`Bridge/Methods/NearDepositAll.lean`). This closes the earlier deposit/log progress entries above.
`NearDepositPre` discharges the host preconditions and proof budget; the panic and success
agreement files connect the exact messages, state, storage, usage and storage-stake check.
`NearDepositGas.hbound_initialized` discharges the remaining gas bound: at most 900009 regular
operations and 54 linear charges, non-trie work below 2.945 Tgas of the 4 Tgas compute allowance,
and two account writes plus the header write within `trieGas`. `CostsDepositV86` adds the v86
log and evicted-byte cost bounds and log-count lower bound to `CostsNewV86`; M9 pins them.
All six method refinements and the complete Bridge build pass the standard-axiom audit.
The sole explicit `sorry` remains `refines_wnear_exported`.

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
