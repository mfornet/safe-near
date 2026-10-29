# wNEAR refinement: status and how to resume

Campaign status on 2026-10-29; local continuation is active. Details are in `wnear_refinement_proof.md`: M3 for the first method, M6 for JSON arguments (the parser map is `wnear_m6_parser_map.md`), and M8 for the other methods.

`refines_wnear_exported` (`Proofs/Refinement.lean`) is still the only `sorry`. Every result below is proved with no `sorry`. Each depends only on `propext`, `Classical.choice` and `Quot.sound`: never use `bv_decide` or `native_decide`.

## Continuation on 2026-10-29: integration with main

Work continues on `codex/wnear-proof-continuation`, starting from PR head `1ea4077` and merging
`main` through `0457bcd` (#46). The harness and dependency-manifest merge conflicts are resolved. The
continuation is published to PR #40 after its validation gates pass.

- #44 moves the recorded-proof check after the value dereference. The repaired
  `NearLogic.prepareStorageCallAux_read` and its callers in `StorageRead.lean` require
  `readProofCost` (lookup plus value bytes) instead of only `lookupProofBound`.
- `lake build NearLogic` passes. The strict axiom audit (`audit/near-logic.json`) checks 56 modules,
  4619 declarations and 3467 theorems with zero violations. LSP also verifies
  `StorageReadWrap.f548_spec_host` with only standard axioms.
- The recipes, wNEAR CI workflow, runtime workflow and periodic checker now build `Bridge`;
  they also explicitly build and strictly audit `NearLogic`. The 16 targeted audit/periodic-check
  regression tests pass, including the new coverage test.
- State-read wrappers, `StateRead*` and initialized `ft_total_supply` are repaired and validated.
  `read_le_proofBound` accounts for the 29-byte state value using the existing model bound.
  `ftTotalSupply_refines_init` passes the LSP axiom check with only the standard three axioms.
  Absent-state reads and `storage_has_key` still need only lookup room.
- The repaired balance lookups and all four view proof files pass LSP diagnostics. The all-state
  theorems for `storage_minimum_balance`, `storage_balance_bounds` and `ft_metadata` pass LSP
  axiom verification with only standard axioms. The combined view build passed (1473 jobs),
  recorded in `/tmp/pr40-view-refinements-build.log`.
- The deposit read-budget integration build passed (1558 jobs): `InternalDeposit`,
  `InternalDepositOverflow`, `DepositBody234`, `NearDepositRuns`, and `NearDepositUninit`.
  The log is `/tmp/pr40-deposit-integration-build.log`.
- **New model agreement groundwork:** `NearDepositModel.lean` exposes every initialized deposit
  path through `nearDeposit_zero`, `nearDeposit_too_small`, `nearDeposit_registered`, and
  `nearDeposit_unregistered`. `nearDeposit_after_registration` separates the fee from minting;
  `deposit_registered_cases` exposes the balance-before-supply checks. The file builds, and
  `nearDeposit_unregistered` passes LSP axiom verification with only standard axioms.
  Keep storageMin symbolic: unfolding its multiplication by 10^19 during broad simplification
  caused excessive kernel work; the separate helper declarations avoid that.
- **Initialized deposit's functional frontier is now closed.** `NearDepositCases` connects
  all five pure classifier outcomes to the model. `NearDepositWords` connects the actual
  host's decoded deposit, predecessor balance, minimum and supply without truncation.
  `NearDepositPre` derives the complete `DepOk` from represented storage and the context,
  and proves `budDep ≤ proofBound` for both the actual and unrecorded comparison hosts.
  The explicit protocol premises are value size ≥ 29, log count ≥ 1, and usage growth
  `85 + numExtraBytesRecord ≤ maxGasBurnt`, alongside `CostsV86`/`LimitsV86`.
- `NearDepositPanicAgreement` proves all panic agreement obligations. `NearDepositEffects`
  flattens `Post234` to exact storage, key, usage and kept-field effects.
  `NearDepositMintWords`, `NearDepositMintModel`, `NearDepositStorageAgreement`, and
  `NearDepositUsageModel` connect the amount, log, header, final storage and usage to
  `mintedOutcome`. `NearDepositSuccessAgreement` includes the final storage-stake check.
- **`near_deposit` is now the sixth completed method refinement under protocol premises.**
  `NearDepositGas.hbound_initialized` discharges loading plus `costDep`: at most 900009
  regular operations, 54 linear-operation charges, host fees at most 2 Tgas, and the
  three write paths within `trieGas`. The non-trie allowance is at most 2.945 Tgas
  against `computeGas = 4 Tgas` under the stated v86 bounds and binary size.
  `NearDepositAll.nearDeposit_refines_all` combines initialized success/panics with the
  uninitialized case. The targeted build passed (1630 jobs), at
  `/tmp/pr40-deposit-all-build.log`. LSP verifies the gas-bound and all-state refinement
  theorems with only the standard three axioms.
- `NearDepositCostOps`, `NearDepositCostCalls`, `NearDepositCostPanics`,
  `NearDepositCostHosts`, `NearDepositCostBody`, and `NearDepositCostFees` separate bounded
  operation work from host fees and trie paths. `CostsDepositV86` extends `CostsNewV86`
  with the evicted-byte cost, log base/byte costs, and permission for at least one log.
  The added numeric bounds match `runtime_config_v86.json` (log count is 100). They are
  explicit protocol premises for M9, not new axioms or changes to the model.
- `lake build +Bridge.Functions.StateReadModel` passes (`/tmp/pr40-state-read-final.log`).
  An earlier concurrent build failed writing a read-only cached BorshFT.ilean; the local
  link was detached and the sequential build passed. Avoid overlapping builds of the same targets.
- Fixed the declared `Bridge` library's missing-root problem with `globs = ["Bridge.+"]`.
  The original full `lake build Bridge` passed (1679 jobs), including `ParseEscape` and
  `ParseStrEsc`, at `/tmp/pr40-full-bridge-build.log`. The current complete build through
  `just wnear-audit` also passed (2742 jobs, including all new deposit files, Model, Spec,
  Proofs, Differential and all three test executables), at `/tmp/pr40-final-wnear-audit.log`.
  The complete recipe exits successfully: the wNEAR audit checks 408 modules, 57240
  declarations and 52136 theorems. Its only three `sorryAx` dependencies are the original
  declarations in `Proofs.Refinement` (`refines_wnear_exported`, `refines_wnear`, and
  `withdraw_available_wasm`). All pinned statements match `STATEMENTS.md`.
- Current validation: strict NearLogic audit passes (56 modules, 4619 declarations,
  3467 theorems, zero violations); the Python suite runs 294 tests successfully (15 skipped); changed-source
  Lean style, toolchain, node-isolation and umbrella checks pass. The freshly rebuilt
  harness (20 contracts), adapter tests, and all 59 default scenarios pass. Evidence logs
  are `/tmp/pr40-final-python-tests.log` and `/tmp/pr40-continuation-{harness,adapter,scenarios}.log`.


## Parser rejection continuation

- `RejectContract` and `f65_reject` now choose their finite cost **before** the gas ceiling.
  The former `∀ Cg, ∃ K` statement was vacuous (`K = Cg + 1`); entry 7 of the misstatement log
  records the kernel-checked witness and the sweep.
- The former `SerdeRejDefs.lean.txt` WIP is now `Bridge/Functions/SerdeRej.lean`.
  Its scratch/result predicates and `f78_rej` are compiled proofs, conditional on `Rej228`.
- `SerdeRej.f68_scratch` (`SerdeScratchDrop.lean`) frees an empty or grown scratch at
  at most 315 regular operations, preserving all allocations live before parsing.
- `SerdeRej.f66_struct_rej` handles 66's struct-error branch, including scratch cleanup and
  complete stack restoration, at `1000 * regularOpCost + K F` from 228's rejecting contract.
- `FromSliceSpec.struct_reject_uniform` and `f65_struct_reject_uniform` connect that branch to
  the public 66/65 pre/postconditions at a fixed cost for **every** gas ceiling. 65's bound is
  `1045 * regularOpCost + K F`. `decode_reject_cases` splits model rejection into a struct
  failure or trailing non-whitespace.
- These are conditional building blocks, **not** a proof of the full rejecting contract.
  The continuation below adds the trailing branch and discharges 228's EOF case.
  The wrappers use `roomS`; the full rejection contract's heap-room assumptions still need
  validation when its callees are discharged.
- PR-wide whitespace findings are removed from `VecFromElem`, `VecWithCap`, `ParseStrEsc`
  and `StrRepeat`.
- Checkpoint `3bca68c` validation: `just wnear-audit` passes (2746 build jobs; 412 wNEAR modules, 57373
  declarations and 52261 theorems; only the three expected `Proofs.Refinement` sorry
  dependencies). Strict NearLogic remains at zero violations, and pinned statements match.
  The PR-wide Lean style check and `git diff --check origin/main` pass. Evidence:
  `/tmp/pr40-parser-final-audit.log` and `/tmp/pr40-parser-lean-style.log`.


## Trailing-character and EOF rejection continuation

- `AllocFinite.lean` proves `HeapModel.wf.freeList_length_le` and `heapInv_finite`:
  distinct free-cell addresses fit in the heap's byte length, so any existential
  free-list bound can be replaced by `2^32`. This supplies an error-only continuation
  with a fixed finite allocation cost after `strRes` has hidden its free-list bound.
- `SerdeRej.f66_trailing` (`SerdeTrailing.lean`) rejects non-whitespace after a parsed
  struct, drops the parsed account string and the empty scratch, and restores the
  complete frame. It assumes the existing struct-reading callees. Its bound is
  `(2000 + 96*rest.length)*c + costS + costErr(2^32, input.length + 1)`.
- `FromSliceSpec.trailing_reject_uniform` and `f65_trailing_reject_uniform`
  (`FromSliceTrailing.lean`) connect that path to the public parser contracts, with
  readers and costs fixed before **every** gas ceiling. 65 adds 45 regular operations.
- **Concrete rejecting case:** `SerdeRej.f228_eof` and `rej228_eof`
  (`SerdeStructEOF.lean`) prove that 228 rejects EOF after whitespace, by calling 322
  with `EofWhileParsingValue`. No parser-callee specification is assumed.
  `FromSliceSpec.f65_eof_reject_uniform` (`FromSliceEOF.lean`) carries this through
  228 → 78 → 66 → 65 for empty and whitespace-only arguments, using the actual
  instantiated code. `decode_eof` proves that the model rejects these inputs too.
- The full rejecting contract remains open for the other struct error cases.
  The accepted-prefix proof used by the trailing branch still needs the general
  escaped/deep-reader integration; this does not expand the shallow/no-escape accepting
  theorem's coverage by itself.
- Current validation: `just wnear-audit` passes (2751 build jobs; 417 wNEAR modules,
  57624 declarations and 52512 theorems; only the three expected open-refinement
  dependencies). Strict NearLogic has zero violations, and pinned statements match.
  PR-wide Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-trailing-final-audit.log` and `/tmp/pr40-trailing-lean-style.log`.

## Positioned errors and object-key EOF continuation

- `SerdePositionPositive.f645_pos`, `f638_pos`, and `f640_pos` strengthen the
  position-reader contracts with a nonzero line number. The loop invariant proves
  positivity from the actual byte scan; it is not a new parser premise.
- `SerdeErrorPositioned.f639_positioned`, `f325_positioned`, and `f322_positioned`
  retain the allocated error's twelve-byte code and its line/column words in
  `positionedBox`/`heapPos`, at the existing allocation and error cost bounds.
- `SerdeErrorPositioned.f327_positioned` and `f326_positioned`
  (`SerdeFixPosition.lean`) prove the actual `fix_position` path for an error whose
  line is already nonzero: the same box is returned and the stack is restored.
- `SerdeKeyReject.f193_eof` proves `next_key_seed` rejects EOF after whitespace
  with `EofWhileParsingObject`. It preserves the first-key flag, reader input,
  original live allocations and positioned error, and restores the full 176-byte
  stack footprint. Its uniform cost is
  `(600 + 96*wsLen(rest))*c + costErr(F, input.length + 1)`.
- The key-error, positioned peek-error, fix-position wrapper and positive position
  theorems pass Lean LSP axiom verification with only the standard three axioms.
  This is groundwork for 228's object-error branch; it does **not** yet discharge
  the public rejecting contract on an unfinished object such as `{`.
- Validation: `just wnear-audit` passes (2755 build jobs; 421 wNEAR modules,
  58443 declarations and 53322 theorems). Only the three expected open-refinement
  dependencies remain. The strict NearLogic audit has zero violations, and pinned
  statements match. PR-wide Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-positioned-final-audit.log` and `/tmp/pr40-positioned-lean-style.log`.

## Unfinished-object rejection continuation

- `SerdeErrorCode` strengthens syntax-error allocation and reader error contracts
  to retain the exact twelve input error-code bytes, with the existing cost and
  position bounds. `copy_code` proves the two Wasm copies preserve those bytes.
- `SerdeEndMapEOF.f90_eof` proves the closing-object check at EOF returns a
  positioned `EofWhileParsingObject` box with its tag retained.
- `SerdeErrorDrop.f92_syntax` proves drop glue for syntax-error tags above 1:
  there is no owned message to free, and the twenty-byte box is returned to the
  heap. Other live allocations are preserved.
- `SerdeRej.f228_obj_eof` and `rej228_obj_eof` prove the actual unfinished-object
  path. Serde creates the missing-key error, restores the nesting depth, then
  still runs the closing-object check. That check creates a second EOF error;
  228 frees it and returns the first through `fix_position`. The complete
  336-byte stack and empty scratch are restored. The two allocations use the
  existing `roomS` premise; their costs are fixed before the gas ceiling.
- `FromSliceSpec.decode_obj_eof` proves model rejection of the same inputs.
  `f65_obj_eof_reject_uniform` carries the concrete proof through 228 → 78 → 66 → 65,
  without assuming any parser-callee contract. This covers an opening `{`
  preceded and followed by arbitrary JSON whitespace.
- The remaining rejection branches, escaped accepting inputs and deep ignored
  values are still open. This does not complete `RejectContract` or a seventh
  method refinement.
- Validation: `just wnear-audit` passes (2760 build jobs; 426 wNEAR modules,
  59129 declarations and 53999 theorems). Only the three existing open-refinement
  dependencies remain; strict NearLogic has zero violations and statement pins
  match. The public parser theorem and the underlying 228 theorem pass LSP
  axiom verification with the standard three axioms. PR-wide Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-object-final-audit.log` and
  `/tmp/pr40-object-lean-style.log`.

## Accepting escaped-string cost continuation

- The existing all-outcome `costRun` cannot close the accepting linear gas bound.
  `StrCostLower.costRun_newlineEscapes_quadratic` proves a lower bound of
  `(800*n*n + 3400*n)*regularOpCost` for `n` newline escapes, with input length
  `2*n + 1`. `newlineEscapes_model` and `newlineEscapes_utf8` prove this family
  is accepted. The quadratic lower bound concerns the old conservative cost
  expression, not the binary's actual gas. Misstatement log entry 8 records the
  corrected proof plan; the general contracts and model gas bounds are unchanged.
- `SerdeEscSuccess.f655_some` proves `next_or_eof` on a present byte in at most
  100 regular operations, without allocator or stack-memory ownership.
  `f653_some` proves valid four-digit hex decoding in at most 300 regular
  operations, with no error-allocation room premise or error-cost reserve.
- `ParseEscapeSuccess.f649_nu_success` proves all successful simple escapes at
  `400*c + costExt`. `f649_u0_success` proves successful non-surrogate Unicode
  escapes at `900*c + costExt`. Both preserve the general reader/scratch result
  and restore the complete stack; neither reserves whole-input error scans.
- The Unicode success theorem passes LSP axiom verification with the standard
  three axioms; the quadratic lower bound uses only `propext` and `Quot.sound`.
- `ParseEscapeSurrogateSuccess.f649_u1_success` covers successful surrogate pairs at
  `2000*c + costExt`, preserving the same reader/scratch result and complete stack.
  `valid_high_tail` derives the required second escape and low surrogate from
  successful decoding. No error-allocation room premise or error reserve is used.
- `ParseEscapeSuccessCost.f649_success` combines all three successful paths.
  Its instruction allowance is bounded by `200*(m + 1)*regularOpCost` when the
  decoder consumes `m` bytes after the leading backslash; scratch growth/copying
  remains a separate `costExt` charge. This is an escape-level bound, not yet a
  linear bound for the complete string reader.
- LSP verifies the surrogate theorem, combined success contract and consumed-byte
  cost bound with only `propext`, `Classical.choice` and `Quot.sound`.
- Next: a success-specific 646 loop,
  final UTF-8 validation once, amortized scratch growth, and integration into
  380/169 and the argument contracts. Full parser rejection remains open too.
- Validation: `just wnear-audit` passes (2763 build jobs; 429 wNEAR modules,
  59857 declarations and 54713 theorems), with only the three existing
  open-refinement dependencies. Strict NearLogic has zero violations; statement
  pins, PR-wide Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-escape-success-final-audit.log` and `/tmp/pr40-escape-success-style.log`.

- Surrogate/combined-contract validation: `just wnear-audit` passes (2765 build
  jobs; 431 wNEAR modules, 60291 declarations and 55137 theorems). Only the three
  existing open-refinement dependencies remain. Strict NearLogic has zero
  violations; statement pins, PR-wide Lean style and whitespace checks pass.
  Evidence: `/tmp/pr40-surrogate-final-audit.log` and
  `/tmp/pr40-surrogate-style.log`.

## Methods

There are 15 exported methods; six now have complete per-call refinement proofs under their protocol premises.

| Method | Status | Top theorem |
|---|---|---|
| `ft_total_supply` (296) | done | `FtTotalSupplyAll.ftTotalSupply_refines_all` |
| `storage_minimum_balance` (231) | done | `StorageMinimumBalanceRefines.storageMinimumBalance_refines_all` |
| `storage_balance_bounds` (306) | done | `StorageBalanceBoundsRefines.storageBalanceBounds_refines_all` |
| `ft_metadata` (309) | done | `FtMetadataRefines.ftMetadata_refines_all` |
| `new` (290) | done | `NewRefines.newRefines_all` |
| `near_deposit` (234) | done | `NearDepositAll.nearDeposit_refines_all`, under `CostsV86`, `LimitsV86`, `CostsDepositV86`, the module protocol premises and code size. Gas, functional agreement and host preconditions are all discharged. |
| `ft_balance_of` (297) | argument layer, and the parser's accepting half for shallow input without escapes | see "Parser" below; the method level is not started |
| `storage_balance_of`, `storage_deposit`, `storage_withdraw`, `storage_unregister`, `near_withdraw`, `ft_transfer`, `ft_transfer_call`, `ft_resolve_transfer` | not started | they need the parser; `ft_transfer_call` and `ft_resolve_transfer` also need promises and promise results |

The premises left in the method theorems are the binary's code size and protocol 86's parameters:
- `CostsV86` and `LimitsV86` (in `FtTotalSupplyGas`/`FtTotalSupplyPre`);
- `CostsNewV86` (in `NewPanicsRefines`);
- `CostsDepositV86` (in `NearDepositCostFees`, extends `CostsNewV86`).

Every value in them is checked against `near-lean/vm/configs/runtime_config_v86.json`. M9 discharges them.

## Infrastructure in place

**Logic and the boundary.**
- SAF-67, the storage-proof budget (#42):
  - `relax` turns recording off;
  - the below-the-bound case uses `eraseP` (`Method.lean`, `Relational.lean`);
  - the trap clause in `runMetered_relaxL`.
- Calls that trap: `MFunSpecT`, `mwpi_call_host_trap`.
- The method-level panic framework: `Panics.lean`.

**Context.** New `Context.WF` fields:
- `trie_no_zero_hash`;
- `prospective_unique`;
- `committed_unique`.

**Host contracts** (`near-lean/near-logic/NearLogic/Hosts`), each with a `.next` lemma that carries the proof budget:
- `storage_read`, which reads through the overlay (`viewVal`, `storage_lookup_view`);
- `storage_write`, `storage_has_key`, `storage_remove`;
- `panic_utf8`, `log_utf8`;
- `attached_deposit`, `predecessor_account_id`, `storage_usage`.

**Allocator.** wee_alloc on a free list of any length (`AllocWalk*`). Reallocation is in `VecGrow`, the scratch buffer in `ScratchGrow`, the `String` sinks in `StrSink*` and `HookSink`.

**Formatting.**
- `core::fmt::write` with any number of arguments, including a trailing piece: `FmtWriteN`, `FmtWriteT`, `FmtWriteP`.
- `Formatter::pad`, and `fmt_u64` for values below 10⁴.
- `format!`.

**Panics.** Rust's panic path is unconditional:
- `begin_panic` (`PanicBeginFull.f664_full`);
- `expect_failed`, `core::panicking::panic` (`PanicFmtFull.f879_unc`, `f853_unc`);
- near-sdk's `panic_str` (`PanicStr`).

The texts are proved equal to the model's `Panic.message` (`PanicText`).

**Containers.** `LookupMap` get, insert and remove, and Borsh for the contract, `String` and `u128`.

**JSON arguments (M6).**
- **Pure layer.** serde's struct machine is proved equal to the model's `parse` followed by `structFields` (`SerdeStructModel.fromSlice_eq`, `decode_balanceOf`). `ignore_value` as an iterative machine is in `IgnoreModel`.
- **Strings.** `parse_str` and `parse_escape` hold on every input, against `stringBody` (`ParseStrEsc.f646_spec`, `str_model`). `from_utf8` agrees with `String.fromUTF8?`. `ParseEscape.lean` takes about 45 minutes to build.
- **Accepting half.** `FromSliceShallow.acceptContract_shallow`, at `K1 = 470` regular ops per argument byte:
  - it covers input without escapes, with ignored values at most one bracket deep;
  - its cost is `(1725 + 470·len)·c + x169`, with under `20·c` of slack;
  - the binary's measured worst case is 275.5 Mgas per byte against the model's 400 (`scenarios/27_arguments_cost.json`).

## Next steps

1. **The parser, finishing `ft_balance_of`'s argument contract.**
   1. `RejectContract`. A loose cost suffices. Use `fromSlice_eq` and the reject paths listed in M6. The outer struct-error and trailing-character paths are proved; 228's EOF case is discharged through 65. Finish the other 228 error cases, and integrate the general string/ignored-value readers.
   2. Escapes in the accepting half:
      - a success-specific string cost and amortized scratch-growth bound:
        the existing all-outcome `costRun` has a proved quadratic lower bound
        even on accepted newline escapes (`StrCostLower`);
      - 380 and 169 with the copied result;
      - `Hyp646` for escaped keys;
      - 652 (`ignore_escape`).
   3. Ignored values nested deeper: 84 grows the scratch from capacity 0, and `Hyp81` must allow changes to the heap and the scratch.
2. **`ft_balance_of`, method level.** Take the parser's contracts as parameters until they are proved. The argument layer is in `EnvInput` and `ArgsLeaves`, the balance read in `LookupMapGet`/`StorageReadWrapF`.
3. **The remaining methods**, in M8's order:
   - `storage_balance_of` (its parser is the same code as `ft_balance_of`'s);
   - `storage_*`, `near_withdraw`, `ft_transfer`;
   - then `ft_transfer_call` and `ft_resolve_transfer`, which need promise and promise-result host contracts.
4. **M9.** Assemble `refines_wnear_exported` and discharge the code size, `CostsV86`, `LimitsV86`, `CostsNewV86` and `CostsDepositV86`.

## Working notes

- **Running agents.** Agents work in their own worktrees and copy `.lake` from the main worktree. They must not launch helper agents: cleaning up a worktree once removed a sub-agent's worktree while it was still working.
- **Merging.** Always check the build's own exit status before pushing; piping it through `grep` hides failures.
- **Tactics.** The tactic pitfalls are collected in the M6 and M8 notes: `mcredits` resets, `Hide`, `mwpi_split`, deep-recursion workarounds.
- **Fixed by the `near_deposit` agent**:
  - **The digit table at 1070974 was owned twice,** by the log data and by the panic hook's location formatting. It is now passed separately to the panic sites.
  - **`GetFmt.getData` named the wrong table entry for the sink's `write_str`.** The vtable word at 1065692 is entry 166, not 165.
