# wNEAR refinement: status and how to resume

Snapshot when work paused on 2026-10-29. Details are in `wnear_refinement_proof.md`: M3 for the first method, M6 for JSON arguments (the parser map is `wnear_m6_parser_map.md`), and M8 for the other methods.

`refines_wnear_exported` (`Proofs/Refinement.lean`) is still the only `sorry`. Every result below is proved with no `sorry`. Each depends only on `propext`, `Classical.choice` and `Quot.sound`: never use `bv_decide` or `native_decide`.

## Continuation on 2026-10-29: integration with main

Work continues on `codex/wnear-proof-continuation`, starting from PR head `1ea4077` and merging
`main` at `1a615fc`. The harness and dependency-manifest merge conflicts are resolved. These
changes have not yet been pushed to PR #40.

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
- **`NearDepositRefines.nearDeposit_refines_init_of_bound` assembles the initialized
  method's complete per-call refinement clauses, conditional on loading plus `costDep`
  fitting the model's gas bound.** That quantitative bound is still open; this does not
  make `near_deposit` a sixth finished method. The targeted build passed (1603 jobs),
  at `/tmp/pr40-deposit-refines-build.log`. LSP verifies the new top theorem, precondition,
  storage, usage, success and panic agreement results with only the standard axioms.
- `lake build +Bridge.Functions.StateReadModel` passes (`/tmp/pr40-state-read-final.log`).
  An earlier concurrent build failed writing a read-only cached BorshFT.ilean; the local
  link was detached and the sequential build passed. Avoid overlapping builds of the same targets.
- Fixed the declared `Bridge` library's missing-root problem with `globs = ["Bridge.+"]`.
  A full `lake build Bridge` is running at `/tmp/pr40-full-bridge-build.log` (exec session
  `67253`, Lake PID `22895`; the long-running `ParseEscape.lean` compiler is PID `23455`).
  Its build graph predates the newest agreement files, which were built separately as
  dependencies of `NearDepositRefines`. Revalidate live process and exit status, then
  build the current complete library and run strict NearLogic/wNEAR audits and statement
  pins before pushing. No complete integrated-build pass is claimed yet.

## Methods

There are 15 exported methods.

| Method | Status | Top theorem |
|---|---|---|
| `ft_total_supply` (296) | done | `FtTotalSupplyAll.ftTotalSupply_refines_all` |
| `storage_minimum_balance` (231) | done | `StorageMinimumBalanceRefines.storageMinimumBalance_refines_all` |
| `storage_balance_bounds` (306) | done | `StorageBalanceBoundsRefines.storageBalanceBounds_refines_all` |
| `ft_metadata` (309) | done | `FtMetadataRefines.ftMetadata_refines_all` |
| `new` (290) | done | `NewRefines.newRefines_all` |
| `near_deposit` (234) | uninitialized refinement done; initialized agreement, premises and assembly done conditional on the gas bound | `NearDepositUninit.nearDeposit_refines_uninit`; `NearDepositRefines.nearDeposit_refines_init_of_bound`. Remaining: prove loading plus `NearDepositMethod.costDep` fits the model's bound, then assemble the all-state method theorem and discharge protocol premises in M9. |
| `ft_balance_of` (297) | argument layer, and the parser's accepting half for shallow input without escapes | see "Parser" below; the method level is not started |
| `storage_balance_of`, `storage_deposit`, `storage_withdraw`, `storage_unregister`, `near_withdraw`, `ft_transfer`, `ft_transfer_call`, `ft_resolve_transfer` | not started | they need the parser; `ft_transfer_call` and `ft_resolve_transfer` also need promises and promise results |

The premises left in the method theorems are the binary's code size and protocol 86's parameters:
- `CostsV86` and `LimitsV86` (in `FtTotalSupplyGas`/`FtTotalSupplyPre`);
- `CostsNewV86` (in `NewPanicsRefines`).

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

1. **`near_deposit`, the remaining gas bound.** Prove loading plus `costDep` is within the model's `computeGas + trieGas + returnDataGas 0` on every initialized path. Instantiate `nearDeposit_refines_init_of_bound`, then combine it with `nearDeposit_refines_uninit`. Template: `NewGas`; the functional and precondition obligations are already discharged.
2. **The parser, finishing `ft_balance_of`'s argument contract.**
   1. `RejectContract`. A loose cost suffices. Use `fromSlice_eq` and the reject paths listed in M6. A WIP of the definitions is in `notes/wip/wnear/SerdeRejDefs.lean.txt`.
   2. Escapes in the accepting half:
      - a closed linear bound on `costRun`;
      - 380 and 169 with the copied result;
      - `Hyp646` for escaped keys;
      - 652 (`ignore_escape`).
   3. Ignored values nested deeper: 84 grows the scratch from capacity 0, and `Hyp81` must allow changes to the heap and the scratch.
3. **`ft_balance_of`, method level.** Take the parser's contracts as parameters until they are proved. The argument layer is in `EnvInput` and `ArgsLeaves`, the balance read in `LookupMapGet`/`StorageReadWrapF`.
4. **The remaining methods**, in M8's order:
   - `storage_balance_of` (its parser is the same code as `ft_balance_of`'s);
   - `storage_*`, `near_withdraw`, `ft_transfer`;
   - then `ft_transfer_call` and `ft_resolve_transfer`, which need promise and promise-result host contracts.
5. **M9.** Assemble `refines_wnear_exported` and discharge the code size, `CostsV86`, `LimitsV86` and `CostsNewV86`.

## Working notes

- **Running agents.** Agents work in their own worktrees and copy `.lake` from the main worktree. They must not launch helper agents: cleaning up a worktree once removed a sub-agent's worktree while it was still working.
- **Merging.** Always check the build's own exit status before pushing; piping it through `grep` hides failures.
- **Tactics.** The tactic pitfalls are collected in the M6 and M8 notes: `mcredits` resets, `Hide`, `mwpi_split`, deep-recursion workarounds.
- **Fixed by the `near_deposit` agent**:
  - **The digit table at 1070974 was owned twice,** by the log data and by the panic hook's location formatting. It is now passed separately to the panic sites.
  - **`GetFmt.getData` named the wrong table entry for the sink's `write_str`.** The vtable word at 1065692 is entry 166, not 165.
