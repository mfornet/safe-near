# wNEAR refinement: status and how to resume

Campaign status on 2026-10-30; local continuation is active. Details are in `wnear_refinement_proof.md`: M3 for the first method, M6 for JSON arguments (the parser map is `wnear_m6_parser_map.md`), and M8 for the other methods.

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
  `NearDepositMethod.nearDeposit_refines_all` combines initialized success/panics with the
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
- The next continuation below supplies the successful 646 loop and a copy
  amortization lemma. The complete accepting gas bound, reader integration and
  full parser rejection remain open.
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

## Successful string loop and amortized-copy continuation

- `StrSuccessCost` defines a success-only run cost. It uses the successful escape
  contracts, reserves no syntax errors, and charges UTF-8 validation only at the
  closing quote. The existing all-outcome contract and cost are unchanged.
- `ParseStrSuccess.f646_success` proves the actual 646 loop on every successful
  UTF-8 run, with arbitrary escapes and the original borrowed/copied `resStr`.
  It restores the complete 192-byte frame and all reader/scratch resources. It
  currently retains the existing conservative `roomRun` premise.
- `ParseStrSuccess.costRun_linear_work` bounds non-append work by
  `(400 + 450*consumed + 100*initialAccLength)*regularOpCost`, plus the separate
  recursive `appendCost`. `ParseStrSuccess.f646_success_linear` exposes the
  corresponding callable contract, including entry/exit work, at
  `(500 + 450*consumed)*regularOpCost + appendCost` from an empty scratch.
- `ScratchAmortized` follows the actual `capAfter` updates along arbitrary append
  lengths. `movedBytes_capacity` telescopes capacity increases; `movedBytes_linear`
  bounds all old-buffer copies by `2*finalUsed + 8` bytes. `copyOps_linear` includes
  memcpy's fixed overhead, bounding that component by `48*finalUsed + 192` regular
  operations. The trace's arithmetic premises are explicit.
- **The general accepting gas allowance is still open.** The 450-ops-per-byte
  component excludes append charges. The fitting case below now meets 470 with
  all append costs included; runs that grow the scratch still need a joint cost
  bound using the append trace and allocator/free-list work. Then integrate
  380/169 and escaped-key readers. No model gas allowance has been increased,
  and this is not a seventh method proof.

- Validation: `just wnear-audit` passes (2770 build jobs; 436 wNEAR modules,
  61095 declarations and 55896 theorems). The only tolerated dependencies on
  `sorryAx` remain the three existing declarations in `Proofs.Refinement`.
  Strict NearLogic has zero violations; statement pins, PR-wide Lean style and
  whitespace checks pass. LSP verifies `f646_success_linear` with the standard
  three axioms and `copyOps_linear` with only `propext` and `Quot.sound`.
  Evidence: `/tmp/pr40-str-success-final-audit.log` and
  `/tmp/pr40-str-success-style.log`.

## Tighter fitting paths and the 470-op accepting string contract

- `ScratchFast` proves fitting 630, 623, 589, 588 and 613. The final slice-append
  chain costs `180*c + MemCpy.cost(k)*c`, compared with `280*c + MemCpy.cost(k)*c`
  in the general contract. Direct 614 (`push`) costs 40 regular operations,
  compared with the general 260. `f613_fast` and `f614_fast` choose these fitting
  bounds and retain the existing growth bounds and exact functional postconditions.
- `ParseEscapeFast.f649_nu_fast` proves all eight successful simple escapes at
  `240*c + pushCost`, replacing `400*c + costExt`. Its generic `f649_fast` keeps
  the existing Unicode/surrogate proofs. Both the simple escape dispatch and
  the fitting push are now charged at their tighter bounds.
- The actual `ParseStrSuccess.f646_success` loop uses these contracts. Its segment
  reserve is reduced from 500 to 300 operations, and its public non-append bound
  is reduced from 550 to 450 operations per consumed byte, as recorded above.
- `costRun_fit` in `StrSuccessFitBound.lean` sums all fitting append charges jointly with
  escape dispatch and the single final UTF-8 validation. `ParseStrSuccess.f646_success_fit` in `ParseStrFit.lean`
  exposes the full callable contract at `(500 + 470*consumed)*c`, with the same
  borrowed/copied `resStr` and full 192-byte stack restoration. The explicit
  capacity premise covers all unread input, so this is the no-growth case. The
  existing conservative `roomRun` premise is retained. LSP verifies the callable
  theorem using only `propext`, `Classical.choice` and `Quot.sound`.
- Next: account for the initial scratch allocation and subsequent growths within
  the same 470-op budget, combining the append trace and allocator/free-list work.
  The argument reader still needs 380/169 integration and general rejection.

- Validation: `just wnear-audit` passes (2774 build jobs; 440 wNEAR modules,
  61364 declarations and 56157 theorems), with only the three existing
  `Proofs.Refinement` dependencies on the open theorem. Strict NearLogic has zero
  violations; statement pins, PR-wide Lean style and whitespace checks pass.
  LSP verifies `ParseStrSuccess.f646_success_fit` with the standard three axioms.
  Evidence: `/tmp/pr40-fast-fit-final-audit.log` and `/tmp/pr40-fast-fit-style.log`.

## Concrete allocation and growth accounting

- `baseAppend` in `StrSuccessCost` now charges a plain-byte append only at an
  escape or at the end of a copied string. The borrowed terminal path does not
  append, so its cost and trace no longer reserve an unused allocation. The
  actual loop proof and both previous cost bounds are repaired and checked.
- `ScratchGrowthTrace` follows `capAfter` and `fAfter` for each append. After `G`
  growths the allocator bound is exactly `F + 2*G`; summed walk bounds satisfy
  `walkBounds + G = F*G + G*G`. `extraCost` includes only growing reserves,
  retaining all allocator walks and memory-growth fees.
- `StrGrowthTrace.appendChunks` follows the actual plain/escape appends; borrowed
  strings have none. `appendChunks_valid` proves the trace arithmetic and final
  capacity/used-length bounds. All requested capacities total at most `4*N + 16`
  bytes; reallocation copies cost at most `48*N + 192` regular operations, with
  `N` the decoded byte length. Page charges are at most
  `(4*N + 16 + 66066*G) / 65536`. The growth-count certificate is
  `G = 0` or `8*2^(G-1) ≤ 2*N + 8`.
- `growthBudget cfg F G N` is zero when `G = 0`. Otherwise it is
  `(1790*G + 320*(F*G + G*G - G) + 36*N + 144)*regularOpCost`, plus
  `G*linearOpBaseCost` and the page-bound times `linearOpUnitCost`.
  `ParseStrSuccess.f646_success_growth` (`ParseStrGrowth.lean`) exposes the full
  successful binary call at `(500 + 470*consumed)*regularOpCost + growthBudget`,
  with the same borrowed/copied result, restored stack, and no capacity premise
  requiring the input to fit. Its existing `roomRun` and binary bounds remain
  explicit. LSP verifies this theorem and the growth-count certificate with the
  standard three axioms.
- **Still required:** absorb this explicit growth budget into the unchanged
  method allowance using the reachable parser heap/scratch invariant, and
  integrate 380/169 and the struct readers. `Hyp646` currently preserves heap
  length/free-list bounds and its borrowed-key instance is not a state-changing
  growth contract. Strengthen `resStr` to expose final capacity/free-list bounds
  from the trace (it currently hides these behind existentials), then carry
  changing scratch/heap state through the 193/228 integration. Also audit the
  borrowed-key consumer's 160-byte callee frame and `d + 16` premise against the
  general proof's 192-byte frame and `d + 30` premise.
  Do not assume a cost uniform in arbitrary initial `F`, or silently frame an
  unchanged heap through growth. Existing escape-free instances remain valid.
  General rejection and deeper ignored values are still open. This does not
  complete a seventh method refinement.

- Validation: `just wnear-audit` passes (2777 build jobs; 443 wNEAR modules,
  61554 declarations and 56309 theorems), with only the three existing
  open-refinement dependencies. Strict NearLogic has zero violations; statement
  pins, PR-wide Lean style and whitespace checks pass. The callable growth
  theorem and power certificate pass LSP axiom verification with the standard
  three axioms. Evidence: `/tmp/pr40-growth-accounting-final-audit.log` and
  `/tmp/pr40-growth-accounting-style.log`.


## Parser result continuation

- `StrTraceResult.resStrTraced` preserves the successful parser's concrete scratch
  trace endpoint. A copied result exposes exact final capacity and allocator
  free-list bound, plus lower/upper memory-length bounds. A borrowed result keeps
  the original scratch resources unchanged.
- `traceInv_escape` composes both appends at an escape; `traceInv_close` extracts
  the endpoint after the final plain append. These pure facts are threaded through
  the actual `f646_success_traced` Wasm loop. `f646_success_growth_traced` exposes
  the same result at the existing closed growth budget. The original two success
  interfaces follow by forgetting the additional information.
- The old key-reader `Hyp646` assumes an unchanged heap, a 160-byte callee frame,
  and a `d + 16` depth premise. The general escaped parser has changing scratch
  state, a 192-byte frame, and a `d + 30` depth premise. Generalize the reader and
  enclosing struct contracts before integrating it; the stronger result is the
  state information needed for that work. No seventh method is complete.
- Validation: `just wnear-audit` passes (2778 build jobs; 444 wNEAR modules,
  61570 declarations and 56321 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f646_success_growth_traced` with only
  the standard three axioms. Changed-source Lean style and whitespace checks pass.
  Evidence: `/tmp/pr40-trace-result-final-audit.log` and
  `/tmp/pr40-trace-result-style.log`.


## Copied value-reader continuation

- `SerdeDeStrEsc.f380_copied` proves the actual successful `deserialize_str` path
  through the general 646 parser and `StringVisitor::visit_str`. Scratch and the
  newly allocated owned `String` remain separate live allocations in one heap.
  The result retains the parser's capacity/free-list endpoint and memory bounds.
- `f380_copied_growth` exposes linear instruction work plus the closed scratch
  growth budget and the owned-string allocation/copy cost. `strRun_size` proves
  decoded bytes and the remaining suffix fit the encoded input, so no extra
  decoded-size premise is required. Allocation room is required at the maximum
  memory length charged by the trace; actual alignment and positivity come from
  the heap invariant, and `roomFor_le` transfers that room to the actual memory.
- `SerdeAccountIdEsc.f379_copied` and `f169_copied` carry this through the String
  wrapper and successful `ValidAccountId::try_from`. They restore complete 240-byte
  and 288-byte frames respectively, with depth premises `d + 32` and `d + 33`.
  `f169_copied_model` starts directly from the JSON model's decoded string and
  `validAccountIdBytes`; it derives the exact parser run and UTF-8 validity.
- These prove successful copied values under explicit reader-room, allocation-room
  and gas premises. The complete escaped accepting argument contract still needs
  changing-state struct-reader hypotheses, escaped keys, and absorption of the
  growth/owned-copy charges into the unchanged method allowance. Rejection and
  deep ignored values remain open; the completed-method count stays six.
- Validation: `just wnear-audit` passes (2780 build jobs; 446 wNEAR modules,
  62022 declarations and 56768 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f169_copied` and `f169_copied_model`
  with only the standard three axioms. Changed-source Lean style and whitespace
  checks pass. Evidence: `/tmp/pr40-copied-values-final-audit.log` and
  `/tmp/pr40-copied-values-style.log`.


## Changing-state struct continuation

- `SerdeValueState` separates scratch/heap ownership from the output descriptor
  and reader cursor. `scratchPre` allows any allocated scratch capacity;
  `valueStorage` retains both scratch and the owned account-id String, with exact
  parser endpoint facts and its memory-growth bound. `spec169_copied` instantiates
  the existing sequence-element callee boundary with this changing state.
- `SerdeSeqElemEsc.f214_copied` proves the first array element using that concrete
  account-id reader. `SerdeMapValueEsc.f205_copied` consumes the map colon and
  reads the copied account id. Both retain the returned scratch/heap state.
- `SerdeColonSuccess.f89_colon` and `f91_close` prove the actual successful
  punctuation paths with only reader/global resources. Heap, scratch and stack
  ownership are framed through; these paths neither allocate nor access their
  reserved stack memory. They retain the existing 200/400-operation allowances
  plus whitespace costs and require only `d + 2` call-depth room.
- `SerdeStructArrState.f228_arr_state` generalizes the array struct proof to an
  arbitrary changing-state element-reader pre/postcondition. The actual closing
  bracket check preserves the returned state and advances the reader. The full
  368-byte frame and nesting-depth byte are restored.
- `SerdeStructArrEsc.f228_arr_copied` instantiates that contract with the concrete
  JSON-model-facing escaped account-id reader, at `d + 35`. It accepts the array
  form with a copied valid account id under explicit parser/allocation room and
  growth/owned-copy gas charges. It does not assume the zero-capacity `tbl` or an
  unchanged heap after 169.
- Remaining integration: generalize the object's loop/key state, then carry the
  array/object results through scratch cleanup and the 78/66/65 wrappers. The
  scratch-drop contract uses membership and a remaining-live-list sublist premise,
  so retain the owned String through that interface rather than assuming scratch
  is the first live allocation. Absorb the explicit gas charges under reachable
  heap bounds. Full rejection and deep ignored values remain open; still six
  completed exported methods.
- Validation: `just wnear-audit` passes (2786 build jobs; 452 wNEAR modules,
  62545 declarations and 57287 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f228_arr_copied` with only the standard
  three axioms. Changed-source Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-struct-values-final-audit.log` and `/tmp/pr40-struct-values-style.log`.


## Copied-array entry and scratch cleanup continuation

- `SerdeScratchValueDrop.f68_value` proves the actual grown-scratch drop while
  retaining the owned String and every earlier live allocation. The live-list
  uniqueness invariant proves the two pointers differ, so erasing scratch removes
  its second entry rather than the String. The final free-list bound is exactly
  `max (endFreeBound F capS 0 chunks) 1 + 1`; memory growth includes the parser trace
  and the owned-string allocation. `cleanValue` retains these bounds.
- `SerdeEndSuccess.f320_eof` checks the final whitespace/end-of-input using only
  reader and global resources. The changed heap, scratch and stack are framed
  through, without requiring extra error-allocation room on this accepting path.
- `SerdeStruct78Esc.f78_arr_copied`, `SerdeFromTraitEsc.f66_arr_copied` and
  `FromSliceEsc.f65_arr_copied` carry the concrete array path through the actual
  78/66/65 calls. 66 constructs its own empty scratch, runs the array reader,
  checks the remaining whitespace, copies the result, frees grown scratch and
  restores its frame. The complete entry restores 448 bytes, preserves input and
  all three string tables, and returns only the owned String; its depth premise
  is `d + 38`.
- `FromSliceEsc.f65_arr_okAt` gives the existing public parser result shape for a
  model account id. This is a proved copied-array family under explicit shape,
  parser/allocation-room and growth/copy gas premises. It is not yet the uniform
  `AcceptContract` on every accepted input. The old contract's `roData` does not
  include the hex table; the general escaped path must carry that ownership.
- The 66 proof simplifies credits after each large call; leaving all nested
  subtraction expressions unnormalized caused a kernel recursion limit. The
  checked proof uses the same 700-operation local/end/drop allowance, plus final
  whitespace and `costArray`; 65 adds 45 operations. The uniform method allowance
  is unchanged and still needs the growth/copy charges absorbed.
- Remaining: object-loop/escaped-key state, deep ignored values, general parser
  rejection, and the reachable heap/room/gas bounds for the complete accepting
  contract. The copied-array cleanup and outer-wrapper integration are now done;
  no seventh exported-method refinement is claimed.
- Validation: `just wnear-audit` passes (2791 build jobs; 457 wNEAR modules,
  62822 declarations and 57562 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f65_arr_okAt` with only the standard
  three axioms. Changed-source Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-copied-array-entry-final-audit.log` and
  `/tmp/pr40-copied-array-entry-style.log`.

## General object-key and reusable-state continuation

- `SerdeKeyEsc.f646_key` adapts the general successful string reader to the existing
  `SerdeNextKey.Spec646` boundary. The extra 32 bytes required by the 192-byte parser
  frame travel through its abstract pre/post resources; `Spec646` and the original
  193 body proof remain reusable. The key's decoded bytes are lent to the field
  matcher, whether borrowed from input or copied into scratch.
- `SerdeKeyEsc.f193_key_model` proves the actual next-key call for any key decoded
  by `Json.stringBody`, on the first or subsequent member. It clears the physical
  scratch length, preserves input and all three string tables, restores the complete
  208-byte frame, and retains the concrete growth budget and returned scratch state.
  Both borrowed and copied paths accept arbitrary initial allocated scratch capacity.
- `sbuf_clear` forgets logical contents while retaining every byte as spare capacity;
  the next Wasm clear updates the descriptor length. `SerdeObjectState.keyState_reuse`
  exposes common existential scratch coordinates, memory-growth and free-list bounds.
  `parsed_capacity` proves the next reader's `cap < 2^25` premise. Its sharper trace
  bound is `max oldCapacity (max 8 (2 * finalUsed))`, avoiding the old additive-eight
  estimate at the input-size boundary.
- `AllocLivePerm.heapInv_perm` proves enumeration order is immaterial to the allocator's
  logical live list; it changes no physical cell. `SerdeObjectState.valueStorage_reuse`
  reorders scratch before the owned String and keeps the String's bytes, final allocator
  bound and parser-plus-owned-copy memory bound. This supplies reusable scratch after
  the account field has been read, while keeping every earlier live allocation.
- These close the concrete escaped-key reader and two resource transitions needed by
  the changing-state object invariant. The actual object loop is not yet generalized.
  A plain account-id value after an escaped key must also accept already-grown scratch;
  the existing copied-value theorem alone does not cover that borrowed path. Deep
  ignored values/ignored escapes, full rejection, reachable room and uniform gas bounds
  remain open. Six exported methods are complete under protocol premises.
- Next implementation route: instantiate `SerdeDeStr.f380_s` for a plain value with
  scratch already present in `live`, framing the scratch pointer/capacity and its
  spare bytes. Its existing no-escape parser does not touch those framed bytes.
  Normalize that borrowed result and the copied result to one owned-value/scratch
  boundary. The object loop then needs at least the larger value-reader stack
  footprint and costs indexed by the evolving scratch/allocator state; do not
  reset capacity between keys or sum growth charges as if each key started empty.
- Validation: `just wnear-audit` passes (2794 build jobs; 460 wNEAR modules,
  62879 declarations and 57616 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f193_key_model`, `parsed_capacity` and
  `valueStorage_reuse` with only the standard three axioms. Changed-source Lean
  style and whitespace checks pass. Evidence: `/tmp/pr40-key-state-final-audit.log`
  and `/tmp/pr40-key-state-style.log`.

## Unified value-reader continuation

- `SerdeValueReuse.f169_borrowed_model` proves a plain account-id value with scratch
  already allocated by an earlier escaped key. It instantiates the existing 169
  proof with scratch in the live list, frames its pointer/capacity/spare bytes and
  the hex table, and restores the same 288-byte frame as the copied path. The owned
  String remains distinct from scratch. No Wasm body is duplicated for that reader.
- `ownedValue` is the common returned resource: the String's bytes, descriptor facts,
  reusable scratch, exact parser endpoint capacity/free-list bound, and total memory
  growth including the owned copy. `heapS_reuse` and `valueStorage_owned` normalize
  the borrowed and copied allocation orders. The physical scratch length may remain
  existential; the next key or value reader clears it before reuse.
- `SerdeValueReuse.f169_model` now handles every valid model-decoded account-id string,
  whether borrowed/plain or copied/escaped, with arbitrary initial scratch capacity.
  It retains explicit reader-room and allocation-room premises. `spec169_model` adapts
  it to the existing sequence-element reader boundary.
- `SerdeMapValueReuse.f205_model` proves the actual colon-plus-value map call, while
  `SerdeSeqElemReuse.f214_model` proves the actual first array-element call. Both use
  the unified reader and return `ownedValue`, the reader cursor and all three string
  tables. The former requires a 288-byte frame; the latter restores all 304 bytes.
- `valueCost_le` proves both branches fit the existing growth-aware copied-reader
  charge. Borrowed strings have an empty append trace and zero scratch-growth charge;
  their String allocation/copy is still charged. The uniform method allowance remains
  unchanged, and its reachable heap/room/growth bounds are not yet discharged.
- Remaining: generalize the actual object loop around the key and unified value
  contracts, including ignored readers and the successful closing-object delimiter.
  After each member, unpack the returned scratch/heap coordinates into the evolving
  loop state. Do not retain `ownedValue` unchanged across later keys: its exact scratch
  endpoint describes the value read, and a later key can grow scratch again while the
  String remains live. Deep ignored values/ignored escapes and general rejection are
  still open. Six exported methods are complete under protocol premises.
- A possible control-proof interface is a member state `J i seen p cap`: keep heap,
  scratch and owned String bytes in `J`, with the loop's descriptor words separate.
  Abstract full 193/205/201 calls can move `J` from the entry cursor to the returned
  cursor while preserving or setting `seen`. This avoids assuming exact scratch
  endpoints remain fixed, and leaves uniform reachable-state cost bounds to the
  concrete reader instantiations. The existing object control proof and pure
  `loopRes`/`objCost` decomposition remain reusable.
- Validation: `just wnear-audit` passes (2797 build jobs; 463 wNEAR modules,
  62947 declarations and 57680 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `f169_model`, `f205_model`, `f214_model`
  and `valueCost_le` with only standard axioms. Changed-source Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-value-reuse-final-audit.log`
  and `/tmp/pr40-value-reuse-style.log`.

## Changing-state object-loop continuation (2026-10-30)

- `SerdeStructObjState.f228_obj_state` proves the actual object path of 228 with
  cursor-indexed member state `J`. Keys and ignored values may change heap/scratch
  resources, and the account-id reader installs a saved String. The loop preserves
  that String through later members, checks the closing `}`, restores depth 128 and
  returns the complete 368-byte frame. It uses the existing `loopRes`/`objCost`
  decomposition and the existing charge; its explicit depth premise is `d + 42`.
- `SerdeEndMapSuccess.f90_close` proves the successful closing-object check with
  only reader/global resources, at `(200 + 96 * whitespace) * regularOpCost` and
  `d + 2`. The changed heap, scratch and stack remain framed through that call.
- `SerdeStructObjKeyState.core` exposes reachable heap/scratch coordinates and
  owns the vtable, all three string tables, static field name and literal table
  needed by ignored values. `member` adds the
  saved String's bytes and live allocation. It uses separate bounds before and after
  the one account-id allocation; a single bound predicate would make the pure value
  closure demand hypothetical repeated String allocations. `seen_core` lends that state while
  retaining the loop's descriptor; `key_exact` preserves the exact endpoint on
  borrowed and copied paths; `member_mono` transports pure cursor bounds.
- `SerdeStructObjKeyState.keyHyp` discharges the loop's actual key-call hypothesis
  with `SerdeKeyEsc.f193_key_model`. `KeyConditions` asks only for room, the fixed
  charge bound and preservation of pure reachable-state bounds. The saved String
  and its descriptor remain live while the scratch allocation can change.
- `SerdeStructObjValueState.account_model` derives the quoted decoded string from
  the model's account reader, including escaped inputs. `valueHyp` discharges the
  loop's actual colon/value hypothesis using `SerdeMapValueReuse.f205_model`.
  `ValueConditions` asks only for room, charge and endpoint bounds, including the
  owned String's allocation. Both borrowed and copied values use this interface.
- `SerdeStructObjModelState.f228_obj_model` assembles the concrete key/value
  contracts with the actual loop and the model account reader. The remaining Wasm
  reader hypothesis is `IgnoreHyp`. Its ignored decoder is parameterized with
  `Agrees ign valueSkip`, rather than requiring literal model skipping on malformed
  numeric prefixes that serde can reject. This retains the existing usable model
  correspondence instead of assuming an unprovable ignored-reader contract.
  An additional persistent code context supplies the ignored reader's transitive
  callees; the successful key/value code bundle alone does not contain them.
- The general object-control integration is now proved. The public result is still
  conditional on `KeyConditions`, `ValueConditions`, monotone reachable bounds, an
  initial `member` state and the ignored-reader contract. Those obligations, deeply
  nested/escaped ignored values, object-state cleanup through 78/66/65 and general
  rejection remain open. This does not establish full `AcceptContract` or a seventh
  exported method refinement.
- Room predicates receive alignment and positivity from the actual allocator,
  via `scratch_alignment`, rather than requiring the pure interval-closed bounds
  to imply them. `alignment_not_interval` records the counterexample; misstatement
  entries 9–11 explain the interface corrections made before publication.
- Quantitative follow-up at this checkpoint (borrowed-key part closed below):
  `keyHyp` paid the general string allowance
  `500 + 470 * consumed` even for borrowed keys. The existing dense-member bound
  used `300 + 130 * consumed`: for an empty key the new conservative allowance is
  540 operations higher, so it does not fit the old 470-per-input-byte member
  arithmetic unchanged. Reuse the old no-escape key reader with allocated scratch
  framed through (as for the plain value), and choose that tighter charge on
  borrowed keys. Escaped strings also retain separate growth charges; their
  accepting instruction estimate may need tightening before the uniform method
  allowance can absorb them. No complete uniform gas bound is claimed here.
- Validation: `just wnear-audit` passes (2802 build jobs; 468 wNEAR modules,
  63521 declarations and 58237 theorems). Only the three existing dependencies on
  `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies the public object theorem, concrete
  key/value adapters and closing check with only standard axioms. Changed-source
  Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-object-loop-final-audit.log` and `/tmp/pr40-object-loop-style.log`.

## Borrowed-key charge continuation (2026-10-30)

- `SerdeKeyReuse.f646_key_borrowed` reuses `SerdeNextKey.f646_key_noesc`
  with any existing scratch allocation in the allocator's live list. It frames
  scratch's pointer/capacity/spare bytes, the hex table and the extra 32 stack
  bytes through the old reader, then rejoins the unchanged scratch. The key's
  input-backed bytes are lent only until the field matcher returns them.
- `f646_key` selects that borrowed proof or the existing general copied-key
  proof. `f193_key_model` carries the selected charge through the actual next-key
  call with the complete 208-byte frame and the existing reusable `keyState`.
  No Wasm body proof is duplicated and no scratch capacity is reset.
- `keyCost_borrowed` proves the borrowed charge is exactly
  `(300 + 130 * consumedBytes) * regularOpCost`. Thus an empty key has a
  430-operation allowance at this reader boundary, rather than the general 970.
  This restores the old borrowed-key contribution to dense-member arithmetic
  even when an earlier key or value allocated scratch. `keyCost_le` proves the
  selected charge never exceeds the previous growth-aware allowance.
- `keyRoom` asks only for the old reader's error-box room on a borrowed key;
  copied keys retain the general `roomRun` premise. `keyRoom_of_roomRun` proves
  the old general premise still suffices. Borrowed keys no longer need room for
  a hypothetical scratch append. The changing-state `KeyConditions` and
  `keyHyp` now use this room predicate and selected charge, so the assembled
  object theorem inherits them.
- Remaining: absorb copied-key growth/instruction charges, prove reachable
  heap/scratch bounds and the ignored-reader transition, carry object results
  through 78/66/65 cleanup, and complete general rejection. The unchanged
  uniform accepting contract and seventh method are still open.
- Validation: `just wnear-audit` passes (2803 build jobs; 469 wNEAR modules,
  63551 declarations and 58265 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies `SerdeKeyReuse.f193_key_model` and
  the assembled object theorem with only standard axioms. Changed-source Lean
  style and whitespace checks pass. Evidence: `/tmp/pr40-key-reuse-final-audit.log`
  and `/tmp/pr40-key-reuse-style.log`.

## Reusable scratch in shallow ignored values (2026-10-30)

- `SerdeIgnValue.scratchTables` parameterizes the scratch descriptor's pointer and
  capacity. `P81`, `inv4`, `contSt` and `brkSt` carry those coordinates through the
  existing shallow body proof. `f81_shallow_reuse` clears only the length, keeps
  pointer/capacity unchanged, and returns the complete 96-byte frame at the
  original `(166 + 470 * consumedBytes) * regularOpCost` allowance. The old
  `f81_shallow` follows as the `(1, 0)` specialization, preserving its callers.
- `SerdeIgnReuse.f201_shallow` proves the actual colon-plus-ignore call using the
  successful colon contract and generalized 81. It needs no allocator ownership
  or error allocation room on this accepted path. Scratch bytes, allocator cells,
  the hex table and a saved account-id String can remain framed through.
- `SerdeIgnReuse.ignoreHyp` supplies the changing-state loop's full ignored-call
  interface for `IgnoreShallow.ign1R`, with `cost81` fixed independently of the
  gas ceiling. It lends the descriptor and read-only tables from `core`, frames
  its allocator/buffer and the saved String, and reconstructs the same allocation
  state under the cursor-monotone `B` or `Bsaved` bound. All 304 caller stack
  bytes are returned. The shared literal table and additional persistent code
  context introduced with the object loop supply the reader's actual resources.
- Coverage remains shallow ignored values on inputs without escapes. This
  generalizes scratch ownership and discharges that family's state transition;
  it does not prove the full model-agreeing ignored reader, escaped/deep ignored
  values, the uniform accepting contract, general rejection or a seventh method.
  Next: prove successful 652/650 on escaped ignored strings, replace the global
  no-escape requirement at the two string branches, and generalize frame pushes
  for deeper nesting while retaining the changing allocator state. The escaped
  string reader must receive the hex table currently framed by `ignoreHyp`;
  carry it through 81’s invariant or a parameterized string-reader frame.
- Validation: `just wnear-audit` passes (2804 build jobs; 470 wNEAR modules,
  63588 declarations and 58299 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP's compiled-module axiom query verifies the
  generalized 81 theorem and retained specialization with only standard axioms;
  `ignoreHyp` also passes its individual axiom check. Changed-source Lean style
  and whitespace checks pass. Evidence: `/tmp/pr40-ignored-reuse-final-audit.log`
  and `/tmp/pr40-ignored-reuse-style.log`.

## Successful ignored escapes (2026-10-30)

- `SerdeHexSuccess.f653_some` proves successful four-digit hex decoding without
  owning a heap or allocator vtable. The actual 653 fast path needs only the
  instance, reader, global, 96-byte frame and hex table. It keeps the existing
  300-operation allowance and returns the packed value with the cursor advanced
  exactly four bytes. Error construction and allocation room are absent.
- `SerdeIgnoreEscape.f652_nu_success`, `f652_u0_success` and `f652_u1_success`
  prove the actual ignored-escape function for simple escapes, BMP Unicode and
  surrogate pairs. They preserve all 112 stack bytes and the hex table, need no
  allocator ownership, and return zero at cursor offsets 1, 5 and 11 after the
  leading backslash. Their instruction allowances are 400, 900 and 2000.
- `consumed_eq` proves those branch lengths equal the model's `escDecode`
  consumption. `f652_success` covers every model-accepted escape with that exact
  endpoint. `f652_success_linear` places its charge under
  `200 * (consumedBytes + 1) * regularOpCost`, including the leading backslash.
  The code predicate contains only the instance and successful callees 637/655/653.
- The pair proof establishes scalar range and surrogate-mask tests before the
  corresponding branches. Its large-mask step uses the explicit numeric rule
  with an abstract result, avoiding expensive generic simplification. No native
  decision procedure or additional axiom is used.
- Next is the full successful `ignore_str` loop (650), then removal of 81's
  no-escape premise. Preserve the model's `Option String`: ignored strings may
  have valid syntax but invalid raw UTF-8, and must not be restricted to `some s`.
  `strRun_model` can supply existential decoded bytes without a UTF-8 premise.
  The planned outer invariant tracks `strRun (bs.drop j) acc = .ok bytes rest`;
  the inner scan can reuse `SerdeIgnStr.inv650`. The complete stack includes
  650's 16 bytes plus 652's 112. Carry the hex table through the 81 invariant or
  an abstract successful string-reader frame. Deep frame pushes and their changing
  allocator state, uniform room/gas bounds, object wrappers and general rejection
  remain open. This does not complete `AcceptContract` or a seventh method.
- Validation: `just wnear-audit` passes (2806 build jobs; 472 wNEAR modules,
  64455 declarations and 59153 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP's compiled-module axiom queries verify the hex
  theorem and both combined escape theorems with only standard axioms.
  Changed-source Lean style and whitespace checks pass. Evidence:
  `/tmp/pr40-ignored-escapes-final-audit.log` and
  `/tmp/pr40-ignored-escapes-style.log`.

## Successful ignored strings (2026-10-30)

- `SerdeIgnoreString.f650_success` proves the actual 650 loop for every successful
  `strRun`, including arbitrary simple/Unicode escapes. The outer invariant tracks
  the remaining modeled run and accumulated decoded bytes; the inner loop reuses
  the existing plain-byte scan. The call returns zero at the exact model endpoint,
  preserves the ESCAPE/hex tables and reader input, and restores all 128 stack bytes.
- Its fixed charge is `(120 + 300 * consumedBytes) * regularOpCost`, independent
  of the gas ceiling. The escape branch pays for 652's successful linear contract,
  call activation and the next loop iteration. No allocator ownership, allocation
  room, error reserve or UTF-8 validation is required. The depth premise is `d + 14`.
- `strRun_of_stringBody` derives existential decoded bytes when the model returns
  `some (s, rest)` for any `s : Option String`. `f650_model` exposes the same
  contract directly at that model boundary. Thus skipped strings with invalid raw
  UTF-8 remain covered; the kernel also checks the witness `[255, 34]`, whose
  string body succeeds with `s = none` and an empty remainder.
- Next: integrate this boundary at 81's string-value and object-key branches,
  carry hex-table ownership through its invariant, and remove its global no-escape
  premise. 650 needs 128 bytes below 81's own 32-byte frame, so that integration
  must provide 160 bytes rather than the old 96-byte shallow footprint. The object
  adapter currently lends 304 bytes, but the complete frame must still be returned.
  Deep frame pushes, uniform heap/room/gas bounds, object wrappers and general
  rejection remain open. This does not complete `AcceptContract` or a seventh method.
- Validation: `just wnear-audit` passes (2807 build jobs; 473 wNEAR modules,
  64671 declarations and 59360 theorems). Only the three existing dependencies
  on `Proofs.Refinement` use `sorryAx`; strict NearLogic has zero violations and
  statement pins match. Lean MCP verifies both public contracts and the model
  helper with only the three standard axioms. Changed-source Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-ignore-string-final-audit.log`
  and `/tmp/pr40-ignore-string-style.log`.

## Escaped shallow ignored values (2026-10-30)

- `SerdeIgnValue.f81_shallow_core` refactors the existing body proof around a
  successful `StringHyp` and an explicit preserved resource frame. Both the
  scalar-string branch and ignored-object-key branch now use the model's
  `stringBody` endpoint rather than a no-escape split. The existing
  `f81_shallow_reuse` is recovered with the plain reader and an empty extra
  frame; its public 96-byte footprint, depth premise and charge are unchanged.
- `SerdeIgnValueEsc.stringHyp` discharges that boundary with the proved full
  successful 650. Its extra frame owns the hex table, successful callee code and
  64 additional stack bytes. `f81_shallow_escaped` therefore covers every
  successful `ign1` skip with arbitrary string escapes, including strings whose
  raw UTF-8 is invalid, without a global no-backslash premise. It preserves
  reusable scratch pointer/capacity and all three string tables, returns the exact
  reader endpoint and restores all 160 bytes. The depth premise is `d + 15`;
  the charge remains `(166 + 470 * consumedBytes) * regularOpCost`.
- `SerdeIgnReuseEsc.f201_shallow` carries the result through the actual colon
  and ignored-value call with a 160-byte frame and `d + 16`. `ignoreHyp` supplies
  the changing-state object loop's ignored-call interface for `ign1R`, now with
  arbitrary escaped strings. It lends the hex table, frames the scratch buffer,
  allocator and saved account-id String, and rejoins all 304 caller stack bytes.
  The existing `cost81` and cursor-monotone bound predicates are reused. There
  is no allocator-room or ignored-reader behavioral hypothesis in these two
  concrete adapter results.
- Lean MCP checks the public contracts, generic core and retained specialization
  with only the three standard axioms. The kernel also checks `ign1` witnesses
  for a newline escape, invalid raw UTF-8, and an object with a Unicode-escaped
  key and escaped string value. `just wnear-audit` passes (2809 build jobs;
  475 wNEAR modules, 64712 declarations and 59399 theorems), with only the three
  existing `Proofs.Refinement` dependencies on `sorryAx`. The strict NearLogic
  audit has zero violations; pinned statements, changed-source Lean style and
  whitespace checks pass. Evidence: `/tmp/pr40-escaped-ignore-final-audit.log`
  and `/tmp/pr40-escaped-ignore-style.log`.
- Remaining: scratch frame pushes/pops for deep ignored containers, the full
  model-agreeing ignored reader, reachable heap/room and uniform gas bounds,
  object wrappers through 78/66/65 and general rejection. `ign1R` is still the
  shallow decoder; it must not be treated as globally agreeing with `valueSkip`.
  This does not establish the full `AcceptContract` or a seventh method.

## First nested frame allocation and nonempty pop (2026-10-30)

- The frame push (84) reserves through 698/712/715/716/714/713, rather than the
  string reader's 589/623/630/631/627/624 chain. The existing `VecGrow` proofs
  covered nonempty buffers; `VecGrowZero` closes this chain's capacity-zero case.
  `f713_alloc` allocates positive byte capacity, `f714_alloc` proves the
  `None` current-memory path, and `f716_alloc` installs `growCap 0 k = max(8,k)`
  from zero capacity and length. Their stack footprints are 16, 32 and 64 bytes.
- `f715_alloc`, `f712_alloc` and `f698_alloc` carry that first allocation through
  the actual reserve wrappers for a positive request. 698 restores all 80 bytes,
  preserves the length at zero, installs the fresh pointer/capacity, and keeps
  every earlier live block. Its fixed charge is
  `480 * regularOpCost + SerdeString.costA cfg F (growCap 0 k)`, with `d + 12`.
  `costA` retains the allocator walk and page fees; no charge is selected from
  the gas ceiling. The explicit room premise is `roomFor` for the new capacity.
- `SerdeIgnFrameStack.f84_initial` proves the actual first frame push, with the
  flag 1 on `(ptr, cap, len) = (1,0,0)`. It allocates capacity 8, stores the frame
  byte, sets length to 1 and restores all 80 bytes. Its two-phase loop invariant
  proves that the byte is written once before the iterator exits. The result is
  `sbuf ... (max F 1) p 8 [byteOf b]`, with the exact allocator memory-growth
  alternative and all earlier live allocations retained. The charge is
  `600 * regularOpCost + costA cfg F 8`, and the depth premise is `d + 13`.
- `f85_nonempty` proves the actual nonempty pop: a buffer holding `bs ++ [b]`
  returns `Some b`, updates the length to `bs.length`, and retains the same
  capacity, memory length, free-list bound and live blocks in `sbuf ... bs`.
  The removed byte becomes the first spare byte. The leaf needs no stack/global
  ownership or allocation room and uses at most 50 regular operations.
- Lean MCP verifies all eight public contracts with only the three standard
  axioms. `just wnear-audit` passes (2811 build jobs; 477 wNEAR modules,
  65208 declarations and 59890 theorems), with only the three existing
  `Proofs.Refinement` dependencies on `sorryAx`. Strict NearLogic has zero
  violations; statement pins, changed-source Lean style and whitespace checks
  pass. Evidence: `/tmp/pr40-frame-stack-final-audit.log`,
  `/tmp/pr40-frame-stack-style.log` and `/tmp/pr40-frame-stack-final-style.log`.
- Next: combine fitting, capacity-zero and nonempty-growing reserves under a
  common `sbuf` contract, prove the general frame push, then extend 81's invariant
  to the complete `IgnoreModel.ignM` machine with a changing heap/frame stack.
  Its existing 160-byte footprint can cover the 80-byte reserve beneath its
  32-byte frame, as well as the larger 650 path. Bound actual frame growth/copies,
  retaining the saved account-id String. Full ignored-reader integration,
  uniform bounds, object wrappers, rejection and the seventh method remain open.

## Methods

There are 15 exported methods; six now have complete per-call refinement proofs under their protocol premises.

| Method | Status | Top theorem |
|---|---|---|
| `ft_total_supply` (296) | done | `FtTotalSupplyAll.ftTotalSupply_refines_all` |
| `storage_minimum_balance` (231) | done | `StorageMinimumBalanceRefines.storageMinimumBalance_refines_all` |
| `storage_balance_bounds` (306) | done | `StorageBalanceBoundsRefines.storageBalanceBounds_refines_all` |
| `ft_metadata` (309) | done | `FtMetadataRefines.ftMetadata_refines_all` |
| `new` (290) | done | `NewRefines.newRefines_all` |
| `near_deposit` (234) | done | `NearDepositMethod.nearDeposit_refines_all`, under `CostsV86`, `LimitsV86`, `CostsDepositV86`, the module protocol premises and code size. Gas, functional agreement and host preconditions are all discharged. |
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
      - absorb `growthBudget` into the unchanged allowance under the reachable
        heap/scratch invariant; use the concrete append trace and its logarithmic
        growth-count, copy and page bounds;
      - discharge `KeyConditions`/`ValueConditions` and the reachable member-state
        bounds of the proved changing-state object loop;
      - keep the all-outcome `costRun` separate: it has a proved quadratic lower
        bound even on accepted newline escapes (`StrCostLower`);
      - the copied array is integrated through 214/228/78/66/65, with scratch
        cleanup; carry the proved changing-state object result through 78/66/65
        and close general argument-contract bounds, including hex-table ownership;
      - instantiate the remaining ignored-reader state transition in that loop;
      - extend the escaped shallow 81 reader to deep frames, preserving its
        changing scratch/heap state and the complete stack footprint.
   3. Ignored values nested deeper: combine the proved first allocation and nonempty
      pop with fitting/reallocating pushes, then track the full scratch frame stack
      in 81. `Hyp81` must allow the resulting heap and scratch changes.
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
