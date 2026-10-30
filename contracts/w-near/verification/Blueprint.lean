import Architect
import Architect.CollectUsed
import Proofs.Refinement
import Bridge.Functions.SerdeIgnClosing
import Bridge.Functions.SerdeIgnMemberBudget
import Bridge.Functions.SerdeStructObjModelState
import Bridge.Functions.FromSliceEsc
import Bridge.Functions.FromSliceSpec
import Bridge.Methods.FtBalanceOfModel
import Bridge.Functions.StorageReadNoneF
import Bridge.Functions.LookupMapGetNone
import Bridge.Functions.LookupMapGet399None
import Bridge.Functions.BalanceOfAbsent
import Bridge.Functions.BalanceOfCallerAbsent
import Bridge.Functions.BalanceOf297AbsentCall
import Bridge.Functions.BalanceOf297AbsentCopy
import Bridge.Functions.BalanceOf297Format
import Bridge.Functions.BalanceOf297Compose
import Bridge.Functions.BalanceOf297Expect
import Bridge.Functions.BalanceOf297ComposeExpect
import Bridge.Functions.BalanceOf297Return
import Bridge.Functions.BalanceOf297ComposeReturn
import Bridge.Functions.BalanceOf297Cleanup
import Bridge.Functions.BalanceOf297ComposeCleanup
import Bridge.Functions.BalanceOf297ArgumentCopy
import Bridge.Functions.BalanceOf297ParsedSuffix
import Bridge.Functions.BalanceOf297StateRead
import Bridge.Functions.BalanceOf297StateBridge
import Bridge.Functions.BalanceOf297ReadBudget
import Bridge.Functions.BalanceOf297ReadGas
import Bridge.Functions.BalanceOf297Room
import Bridge.Functions.BorshContractF
import Bridge.Functions.StateReadLenF
import Bridge.Functions.BalanceOf297RoomF
import Bridge.Functions.BalanceOf297ParserResult
import Bridge.Functions.BalanceOf297ParserPublicCompose
import Bridge.Functions.BalanceOf297CopiedCall
import Bridge.Functions.BalanceOf297CopiedBody
import Bridge.Functions.BalanceOf297InitialRoomCompose
import Bridge.Methods.FtBalanceOfAbsentCompose
import Bridge.Methods.FtBalanceOfInputBound

/-! The browsable proof frontier. Definitions marked Open state contracts, not proofs. -/

attribute [blueprint "frontier:exported"
  (title := /-- All exported runtime clauses -/)
  (statement := /-- All exported runtime clauses. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.refines_wnear_exported

attribute [blueprint "frontier:dispatch"
  (title := /-- Checked dispatch over all 15 methods -/)
  (statement := /-- Checked dispatch over all 15 methods. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.Exported.all_methods

attribute [blueprint "frontier:remaining"
  (title := /-- Nine remaining full method contracts -/)
  (statement := /-- Nine remaining full method contracts. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.Exported.Remaining

attribute [blueprint "frontier:binary-size"
  (title := /-- Embedded deployed code size -/)
  (statement := /-- Embedded deployed code size. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.deployed_code_size

attribute [blueprint "frontier:protocol-runtime"
  (title := /-- Pinned protocol: runtime -/)
  (statement := /-- Pinned protocol: runtime. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_runtime_obligation

attribute [blueprint "frontier:protocol-costs"
  (title := /-- Pinned protocol: costs -/)
  (statement := /-- Pinned protocol: costs. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_costs_obligation

attribute [blueprint "frontier:protocol-limits"
  (title := /-- Pinned protocol: limits -/)
  (statement := /-- Pinned protocol: limits. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_limits_obligation

attribute [blueprint "frontier:protocol-new_costs"
  (title := /-- Pinned protocol: new costs -/)
  (statement := /-- Pinned protocol: new costs. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_new_costs_obligation

attribute [blueprint "frontier:protocol-deposit_costs"
  (title := /-- Pinned protocol: deposit costs -/)
  (statement := /-- Pinned protocol: deposit costs. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_deposit_costs_obligation

attribute [blueprint "frontier:method-ft_total_supply"
  (title := /-- ft\_total\_supply -/)
  (statement := /-- ft\_total\_supply. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.ftTotalSupply_complete

attribute [blueprint "frontier:method-storage_minimum_balance"
  (title := /-- storage\_minimum\_balance -/)
  (statement := /-- storage\_minimum\_balance. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.storageMinimumBalance_complete

attribute [blueprint "frontier:method-storage_balance_bounds"
  (title := /-- storage\_balance\_bounds -/)
  (statement := /-- storage\_balance\_bounds. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.storageBalanceBounds_complete

attribute [blueprint "frontier:method-ft_metadata"
  (title := /-- ft\_metadata -/)
  (statement := /-- ft\_metadata. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.ftMetadata_complete

attribute [blueprint "frontier:method-new"
  (title := /-- new -/)
  (statement := /-- new. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.new_complete

attribute [blueprint "frontier:method-near_deposit"
  (title := /-- near\_deposit -/)
  (statement := /-- near\_deposit. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.nearDeposit_complete

attribute [blueprint "frontier:method-near_withdraw"
  (title := /-- near\_withdraw -/)
  (statement := /-- near\_withdraw. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.nearWithdraw_obligation

attribute [blueprint "frontier:method-ft_transfer"
  (title := /-- ft\_transfer -/)
  (statement := /-- ft\_transfer. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.ftTransfer_obligation

attribute [blueprint "frontier:method-ft_transfer_call"
  (title := /-- ft\_transfer\_call -/)
  (statement := /-- ft\_transfer\_call. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.ftTransferCall_obligation

attribute [blueprint "frontier:method-ft_balance_of"
  (title := /-- ft\_balance\_of -/)
  (statement := /-- ft\_balance\_of. Checked assembly remains conditional on the three named open execution, accepted-input and rejected-input obligations. -/)
  (notReady := true)]
  WNear.ftBalanceOf_obligation

attribute [blueprint "frontier:method-ft_resolve_transfer"
  (title := /-- ft\_resolve\_transfer -/)
  (statement := /-- ft\_resolve\_transfer. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.ftResolveTransfer_obligation

attribute [blueprint "frontier:method-storage_deposit"
  (title := /-- storage\_deposit -/)
  (statement := /-- storage\_deposit. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageDeposit_obligation

attribute [blueprint "frontier:method-storage_withdraw"
  (title := /-- storage\_withdraw -/)
  (statement := /-- storage\_withdraw. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageWithdraw_obligation

attribute [blueprint "frontier:method-storage_unregister"
  (title := /-- storage\_unregister -/)
  (statement := /-- storage\_unregister. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageUnregister_obligation

attribute [blueprint "frontier:method-storage_balance_of"
  (title := /-- storage\_balance\_of -/)
  (statement := /-- storage\_balance\_of. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageBalanceOf_obligation

attribute [blueprint "frontier:ignore-hyp"
  (title := /-- Full ignored-reader interface -/)
  (statement := /-- Full ignored-reader interface. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.IgnoreHyp

attribute [blueprint "frontier:key-conditions"
  (title := /-- Uniform reachable key bounds -/)
  (statement := /-- Uniform reachable key bounds. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjKeyState.KeyConditions

attribute [blueprint "frontier:value-conditions"
  (title := /-- Uniform reachable value bounds -/)
  (statement := /-- Uniform reachable value bounds. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjValueState.ValueConditions

attribute [blueprint "frontier:accept-parser"
  (title := /-- Uniform accepting argument contract -/)
  (statement := /-- Uniform accepting argument contract. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.FromSliceSpec.AcceptContract

attribute [blueprint "frontier:reject-parser"
  (title := /-- Uniform rejecting argument contract -/)
  (statement := /-- Uniform rejecting argument contract. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.FromSliceSpec.RejectContract

attribute [blueprint "frontier:object-parser"
  (title := /-- Changing-state object parser -/)
  (statement := /-- Changing-state object parser. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjModelState.f228_obj_model

attribute [blueprint "frontier:array-parser"
  (title := /-- Copied/escaped array parser wrapper -/)
  (statement := /-- Copied/escaped array parser wrapper. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.FromSliceEsc.f65_arr_okAt

attribute [blueprint "frontier:ignored-opening"
  (title := /-- Complete funded ignored-container opening -/)
  (statement := /-- Complete funded ignored-container opening. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnOpening.entry_funded

attribute [blueprint "frontier:ignored-closing"
  (title := /-- Complete funded nested close -/)
  (statement := /-- Complete funded nested close. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnClosing.funded_nonempty

attribute [blueprint "frontier:ignored-last-close"
  (title := /-- Complete funded final close -/)
  (statement := /-- Complete funded final close. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnClosing.funded_empty

attribute [blueprint "frontier:ignored-first"
  (title := /-- Complete funded first-member iteration -/)
  (statement := /-- Complete funded first-member iteration. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnMemberBudget.first_funded

attribute [blueprint "frontier:ignored-comma"
  (title := /-- Complete funded comma iteration -/)
  (statement := /-- Complete funded comma iteration. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnMemberBudget.comma_funded

attribute [blueprint "frontier:ignored-member"
  (title := /-- Funded array/key/colon tail -/)
  (statement := /-- Funded array/key/colon tail. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnMemberBudget.next_funded

attribute [blueprint "frontier:ignored-scalar"
  (title := /-- Complete scalar dispatch -/)
  (statement := /-- Complete scalar dispatch. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnScalar.scalar

attribute [blueprint "frontier:ignored-depth"
  (title := /-- Logical depth bounded by consumed bytes -/)
  (statement := /-- Logical depth bounded by consumed bytes. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnProgress.run_consumed

attribute [blueprint "frontier:ignored-reserve"
  (title := /-- Closing-byte reserve accounting -/)
  (statement := /-- Closing-byte reserve accounting. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnBudget.regular_reserve

attribute [blueprint "frontier:storage"
  (title := /-- Actual storage-read host contract -/)
  (statement := /-- Actual storage-read host contract. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.StorageReadWrap.f548_spec_host

attribute [blueprint "frontier:runtime-boundary"
  (title := /-- Runtime and rollback composition -/)
  (statement := /-- Runtime and rollback composition. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.method_boundary

attribute [blueprint "frontier:runtime-call"
  (title := /-- Per-call runtime refinement -/)
  (statement := /-- Per-call runtime refinement. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.method_refines_call

attribute [blueprint "frontier:scratch-room"
  (title := /-- Reachable scratch growth room -/)
  (statement := /-- Open verification obligation: derive this explicit allocation-room premise on all reachable states. -/)
  (notReady := true)]
  WNear.Binary.ScratchGrow.roomRes

attribute [blueprint "frontier:string-room"
  (title := /-- Reachable escaped-string growth room -/)
  (statement := /-- Open verification obligation: derive this explicit allocation-room premise on all reachable states. -/)
  (notReady := true)]
  WNear.Binary.ParseStr.roomRun

attribute [blueprint "frontier:owned-room"
  (title := /-- Reachable owned-string allocation room -/)
  (statement := /-- Open verification obligation: derive this explicit allocation-room premise on all reachable states. -/)
  (notReady := true)]
  WNear.Binary.VecFromElem.roomFor

attribute [blueprint "frontier:protocol-available"
  (title := /-- Pinned protocol parses successfully -/)
  (statement := /-- Open obligation: prove that the pinned protocol JSON actually parses before instantiating the deployed theorem. -/)
  (notReady := true)]
  WNear.PinnedProtocolAvailable

attribute [blueprint "frontier:ft-balance-model"
  (title := /-- Balance lookup and model boundary agreement -/)
  (statement := /-- For an arbitrary requested account, represented storage and decoded balance agree with the initialized model boundary result, including missing accounts and the storage-stake failure. Wasm execution and parsing remain open. -/)]
  WNear.Binary.FtBalanceOfMethod.account_lookup_and_step

attribute [blueprint "frontier:storage-read-absent"
  (title := /-- Absent storage read with allocator and trie accounting -/)
  (statement := /-- The actual storage-read wrapper returns None for an absent key and preserves the allocator bound under the metered host and trie-proof premises. Its LookupMap callers remain to be integrated. -/)]
  WNear.Binary.StorageReadWrapF.f548_noneF_host

attribute [blueprint "frontier:lookup-raw-absent"
  (title := /-- Absent LookupMap raw read -/)
  (statement := /-- The actual get_raw function constructs the storage key, executes the absent read and frees its temporary key; the reachable allocator-room obligation remains open. -/)
  (notReady := true)]
  WNear.Binary.LookupMapGet.f400_none

attribute [blueprint "frontier:lookup-heap-room"
  (title := /-- Reachable LookupMap allocation room -/)
  (statement := /-- Open obligation: derive the multi-allocation room predicate at reachable LookupMap calls. -/)
  (notReady := true)]
  WNear.Binary.LookupMapOps.HeapRoomK

attribute [blueprint "frontier:lookup-absent"
  (title := /-- Absent LookupMap get -/)
  (statement := /-- The actual get function composes the absent raw read, frees the Borsh key and returns None. Reachable multi-allocation room remains open. -/)
  (notReady := true)]
  WNear.Binary.LookupMapGet.f399_none

attribute [blueprint "frontier:balance-lookup-absent"
  (title := /-- Balance lookup for an absent account -/)
  (statement := /-- The actual balance lookup composes the absent LookupMap read, returns zero, frees the account string and preserves the host. Reachable allocation room remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOfAbsent.f415_none

attribute [blueprint "frontier:balance-caller-absent"
  (title := /-- Token balance caller for an absent account -/)
  (statement := /-- The actual token balance caller composes the absent balance lookup and returns zero. Reachable allocation room remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOfAbsent.f293_none

attribute [blueprint "frontier:balance-no-issue"
  (title := /-- Balance method execution safety -/)
  (statement := /-- Open obligation: exclude execution issues for every represented balance-method context, including rejected input. -/)
  (notReady := true)]
  WNear.ftBalanceOf_no_issue_obligation

attribute [blueprint "frontier:balance-accepted"
  (title := /-- Balance method accepted-input refinement -/)
  (statement := /-- Open obligation: prove the full refinement and arbitrary-resource clauses for accepted balance calls. -/)
  (notReady := true)]
  WNear.ftBalanceOf_accepted_obligation

attribute [blueprint "frontier:balance-rejected"
  (title := /-- Balance method rejected-input rollback -/)
  (statement := /-- Open obligation: prove rollback for rejected balance-method arguments. -/)
  (notReady := true)]
  WNear.ftBalanceOf_rejected_obligation

attribute [blueprint "frontier:balance-export-call-absent"
  (title := /-- Exported balance function: absent-account call segment -/)
  (statement := /-- The exact decoded instruction slice in function 297 composes the absent-account token balance caller; the complete method and reachable allocation room remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.call_absent

attribute [blueprint "frontier:balance-export-copy-zero"
  (title := /-- Exported balance function: copy zero result -/)
  (statement := /-- The exact decoded instructions copy the absent-account zero balance into the formatting input. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copy_zero

attribute [blueprint "frontier:balance-export-call-and-copy"
  (title := /-- Exported balance function: absent call and result copy -/)
  (statement := /-- The actual decoded function-297 slice composes the absent-account call with its following zero-result copy; reachable allocation room and the rest of the method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.call_and_copy_absent

attribute [blueprint "frontier:balance-export-format-zero"
  (title := /-- Exported balance function: serialize zero -/)
  (statement := /-- The exact decoded call serializes zero under explicit heap-room and frame premises; composition with the preceding slice remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.format_zero

attribute [blueprint "frontier:balance-export-call-copy-format"
  (title := /-- Exported balance function: absent call, copy and serialization -/)
  (statement := /-- The exact 29-instruction function-297 slice composes the absent balance call, its zero copy, and JSON serialization under four-growth room and explicit frame premises; the complete method and reachable room remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.call_copy_and_format_absent

attribute [blueprint "frontier:balance-export-expect-ok"
  (title := /-- Exported balance function: extract successful result -/)
  (statement := /-- The exact decoded function-297 instructions extract the successful serialized vector. -/)]
  WNear.Binary.BalanceOf297AbsentCall.expect_ok

attribute [blueprint "frontier:balance-export-through-expect"
  (title := /-- Exported balance function: absent balance through result extraction -/)
  (statement := /-- The actual 37-instruction slice composes the absent balance lookup, zero copy, serialization, and successful result extraction; reachable room and the complete method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.call_copy_format_and_expect_absent

attribute [blueprint "frontier:balance-export-return-vec"
  (title := /-- Exported balance function: return serialized vector -/)
  (statement := /-- The exact decoded instructions dereference a serialized vector and call value_return under explicit host, memory and return-length premises. -/)]
  WNear.Binary.BalanceOf297AbsentCall.return_vec

attribute [blueprint "frontier:balance-export-through-return"
  (title := /-- Exported balance function: absent balance through value return -/)
  (statement := /-- The exact 47-instruction slice composes the absent lookup through value_return of the JSON bytes for zero; reachable heap room, cleanup and the full method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.call_through_value_return_absent

attribute [blueprint "frontier:balance-export-cleanup"
  (title := /-- Exported balance function: vector cleanup and epilogue -/)
  (statement := /-- The exact decoded final instructions free the two owned vectors and restore the stack global. -/)]
  WNear.Binary.BalanceOf297AbsentCall.cleanup

attribute [blueprint "frontier:balance-export-through-cleanup"
  (title := /-- Exported balance function: absent balance through cleanup -/)
  (statement := /-- The exact 59-instruction suffix composes absent-account lookup through return of zero, both vector drops and stack restoration; reachable room, preceding argument and state setup and the full method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.call_through_cleanup_absent

attribute [blueprint "frontier:balance-export-argument-copy"
  (title := /-- Exported balance function: copy parsed account descriptor -/)
  (statement := /-- The exact decoded instructions copy the already parsed account string descriptor to the balance-call argument. -/)]
  WNear.Binary.BalanceOf297AbsentCall.argument_copy

attribute [blueprint "frontier:balance-export-parsed-suffix"
  (title := /-- Exported balance function: parsed absent account through cleanup -/)
  (statement := /-- The exact 71-instruction suffix composes the parsed account descriptor handoff through absent-account return and cleanup; parsing, state setup, reachable room and the full method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parsed_account_through_cleanup_absent

attribute [blueprint "frontier:balance-state-entry"
  (title := /-- State-read entry resources -/)
  (statement := /-- State-read entry resources include a heap free-list bound of one; their reachability from the preceding balance parser remains open. -/)
  (notReady := true)]
  WNear.Binary.StateRead.pre219

attribute [blueprint "frontier:balance-second-read"
  (title := /-- Absent balance read after state read -/)
  (statement := /-- Open second-read conditions following the state read: trie accounting, proof budget, absent key and gas bound. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterState

attribute [blueprint "frontier:balance-export-state-read"
  (title := /-- Exported balance function: state read and unwrap -/)
  (statement := /-- The exact decoded state-read and successful unwrap instructions compose under the stated entry and room conditions. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_read_and_unwrap

attribute [blueprint "frontier:balance-export-state-through-cleanup"
  (title := /-- Exported balance function: state read through absent balance cleanup -/)
  (statement := /-- The exact 82-instruction suffix composes model-state reading through absent balance return and cleanup, assuming state-entry resources, allocation room and the named second-read conditions; parsing and the complete method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_absent

attribute [blueprint "frontier:balance-second-read-gas"
  (title := /-- Balance-read gas bound after state read -/)
  (statement := /-- Open uniform gas bound for the absent-account lookup after state_read. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterState

attribute [blueprint "frontier:balance-second-read-from-budget"
  (title := /-- Derive second-read conditions from shared budget -/)
  (statement := /-- Canonical trie, storage link and a shared proof budget propagate across state_read; the separately named gas bound remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.balanceReadAfterState_of_budget

attribute [blueprint "frontier:balance-export-state-budget"
  (title := /-- Exported balance: state read through cleanup with shared budget -/)
  (statement := /-- The checked 82-instruction absent-account suffix now derives the second-read trie and proof-budget conditions from the initial state; parsed-entry resources, allocation room and post-read gas remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_of_budget

attribute [blueprint "frontier:balance-next-read-cost-preserved"
  (title := /-- Storage-read cost preserved after a read -/)
  (statement := /-- A storage read preserves the modeled cost of a subsequent read for any key. -/)]
  WNear.Binary.BalanceOf297AbsentCall.storageReadUse_after_read

attribute [blueprint "frontier:balance-second-read-exact-gas"
  (title := /-- Exact balance-read gas after state read -/)
  (statement := /-- The initial-state balance lookup cost is an exact bound after state_read, discharging the gas condition at that bound. -/)]
  WNear.Binary.BalanceOf297AbsentCall.balanceReadGasAfterState_exact

attribute [blueprint "frontier:balance-export-state-exact-gas"
  (title := /-- Exported balance: state read through cleanup with exact gas -/)
  (statement := /-- The checked 82-instruction absent-account suffix instantiates the post-read gas bound exactly; parser-entry resources, allocation room and the full method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_exact_gas

attribute [blueprint "frontier:balance-room-after-state"
  (title := /-- Derive allocation room after state read -/)
  (statement := /-- Six initial one-page growth slots imply the state-read allocation room and four slots after state_read; reachability of the initial bound remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.room_after_state

attribute [blueprint "frontier:balance-export-state-six-grows"
  (title := /-- Exported balance: state read through cleanup with six-growth budget -/)
  (statement := /-- The checked absent-account suffix derives every allocation-room requirement from a single six-growth entry bound; parser-entry resources and reachability of that bound remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_six_grows

attribute [blueprint "frontier:borsh-vec-free-bound"
  (title := /-- Vector copy with a general free-list bound -/)
  (statement := /-- The decoded deserializer preserves an explicitly bounded free list, under the stated allocation-room and execution-resource premises. The general-bound state reader now composes this deserialization chain. -/)
  (notReady := true)]
  WNear.Binary.BorshVecF.f374_spec

attribute [blueprint "frontier:borsh-bytes-reader-free-bound"
  (title := /-- Byte reader with a general free-list bound -/)
  (statement := /-- The decoded deserializer preserves an explicitly bounded free list, under the stated allocation-room and execution-resource premises. The general-bound state reader now composes this deserialization chain. -/)
  (notReady := true)]
  WNear.Binary.BorshBytesF.f316_spec

attribute [blueprint "frontier:borsh-bytes-free-bound"
  (title := /-- Byte deserializer with a general free-list bound -/)
  (statement := /-- The decoded deserializer preserves an explicitly bounded free list, under the stated allocation-room and execution-resource premises. The general-bound state reader now composes this deserialization chain. -/)
  (notReady := true)]
  WNear.Binary.BorshBytesF.f315_spec

attribute [blueprint "frontier:borsh-ft-free-bound"
  (title := /-- Fungible-token deserializer with a general free-list bound -/)
  (statement := /-- The decoded deserializer preserves an explicitly bounded free list, under the stated allocation-room and execution-resource premises. The general-bound state reader now composes this deserialization chain. -/)
  (notReady := true)]
  WNear.Binary.BorshFTF.f425_spec

attribute [blueprint "frontier:borsh-contract-reader-free-bound"
  (title := /-- Contract reader with a general free-list bound -/)
  (statement := /-- The decoded deserializer preserves an explicitly bounded free list, under the stated allocation-room and execution-resource premises. The general-bound state reader now composes this deserialization chain. -/)
  (notReady := true)]
  WNear.Binary.BorshContractF.f162_spec

attribute [blueprint "frontier:borsh-contract-free-bound"
  (title := /-- Contract slice deserializer with a general free-list bound -/)
  (statement := /-- The decoded deserializer preserves an explicitly bounded free list, under the stated allocation-room and execution-resource premises. The general-bound state reader now composes this deserialization chain. -/)
  (notReady := true)]
  WNear.Binary.BorshContractF.f161_spec

attribute [blueprint "frontier:state-entry-free-bound"
  (title := /-- State-read entry resources with a general free-list bound -/)
  (statement := /-- The general state-read entry requires owned heap resources with a supported bound. Establishing these resources from the parser remains open. -/)
  (notReady := true)]
  WNear.Binary.StateReadLenF.pre219F

attribute [blueprint "frontier:state-read-free-bound"
  (title := /-- State read with a general free-list bound -/)
  (statement := /-- The decoded state reader composes the general-bound storage reader and deserializer, and frees the temporary buffer, under explicit resource and host premises. -/)
  (notReady := true)]
  WNear.Binary.StateReadLenF.f219_spec_lenF

attribute [blueprint "frontier:state-read-model-free-bound"
  (title := /-- Model-state read with a general free-list bound -/)
  (statement := /-- The general-bound state-read theorem instantiated for the encoded model state and composed into the balance path; the parser handoff remains open. -/)
  (notReady := true)]
  WNear.Binary.StateReadLenF.f219_spec_model_lenF

attribute [blueprint "frontier:balance-state-read-free-bound"
  (title := /-- Function 297: state read and unwrap with general bound -/)
  (statement := /-- Function 297: state read and unwrap with general bound. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_read_and_unwrapF

attribute [blueprint "frontier:balance-next-read-free-bound"
  (title := /-- Second-read conditions with general bound -/)
  (statement := /-- Second-read conditions with general bound. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.BalanceReadAfterStateF

attribute [blueprint "frontier:balance-state-cleanup-free-bound"
  (title := /-- Function 297: state read through cleanup with general bound -/)
  (statement := /-- Function 297: state read through cleanup with general bound. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_absentF

attribute [blueprint "frontier:balance-next-gas-free-bound"
  (title := /-- Second-read gas condition with general bound -/)
  (statement := /-- Second-read gas condition with general bound. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.BalanceReadGasAfterStateF

attribute [blueprint "frontier:balance-next-budget-free-bound"
  (title := /-- Derive general-bound second-read conditions from budget -/)
  (statement := /-- Derive general-bound second-read conditions from budget. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.balanceReadAfterState_of_budgetF

attribute [blueprint "frontier:balance-state-budget-free-bound"
  (title := /-- Function 297: general-bound state path with shared budget -/)
  (statement := /-- Function 297: general-bound state path with shared budget. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_of_budgetF

attribute [blueprint "frontier:balance-next-exact-gas-free-bound"
  (title := /-- Exact second-read gas with general bound -/)
  (statement := /-- Exact second-read gas with general bound. The parser handoff and full accepted-call refinement remain open. -/)]
  WNear.Binary.BalanceOf297AbsentCall.balanceReadGasAfterState_exactF

attribute [blueprint "frontier:balance-state-exact-gas-free-bound"
  (title := /-- Function 297: general-bound state path with exact gas -/)
  (statement := /-- Function 297: general-bound state path with exact gas. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_exact_gasF

attribute [blueprint "frontier:balance-state-six-grows-free-bound"
  (title := /-- Function 297: general-bound state path with six-growth room -/)
  (statement := /-- Function 297: general-bound state path with six-growth room. The parser handoff and full accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.state_through_cleanup_six_growsF

attribute [blueprint "frontier:parser-owned-result"
  (title := /-- Successful parser owned result -/)
  (statement := /-- Owned decoded account and allocator state; obtaining this result for all accepted inputs remains conditional on the parser obligations. -/)
  (notReady := true)]
  WNear.Binary.FromSliceSpec.okAt

attribute [blueprint "frontier:parser-owned-resources"
  (title := /-- Extract balance resources from parser result -/)
  (statement := /-- Successful parser result and owned input allocation; proves account bounds, capacity and live-list order, but does not establish heap room or gas. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parser_result_resources

attribute [blueprint "frontier:balance-parser-handoff"
  (title := /-- Function 297: success branch and input-vector drop -/)
  (statement := /-- Decoded success tag and descriptors, owned input buffer, heap invariant and explicit Wasm execution resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.parser_handoff

attribute [blueprint "frontier:balance-parser-through-cleanup"
  (title := /-- Function 297: parser success through absent balance cleanup -/)
  (statement := /-- Decoded successful parser descriptor and input vector, owned account, six-growth room, canonical trie, shared proof budget, exact lookup gas and execution resources; deriving all entry resources and gas from the parser remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parser_through_cleanup

attribute [blueprint "frontier:parser-fixed-result"
  (title := /-- Successful parser result with explicit heap witnesses -/)
  (statement := /-- The same owned parser result with its actual heap length and free-list bound exposed; the parser must produce such a result. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.okAtFixed

attribute [blueprint "frontier:parser-expose-heap"
  (title := /-- Expose the successful parser heap witnesses -/)
  (statement := /-- The public parser result entails its fixed-witness representation. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.okAt_expose

attribute [blueprint "frontier:parser-fixed-resources"
  (title := /-- Extract account resources at fixed parser heap -/)
  (statement := /-- The fixed-witness parser result supplies account bounds, owned bytes and input-first allocation order. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parser_fixed_resources

attribute [blueprint "frontier:parser-fixed-through-cleanup"
  (title := /-- Function 297: fixed parser result through absent cleanup -/)
  (statement := /-- A successful parser result at a known heap, six-growth room, gas, input ownership, trie and frame premises. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parser_fixed_through_cleanup

attribute [blueprint "frontier:parser-post-budget"
  (title := /-- Post-parser room and gas at the actual heap -/)
  (statement := /-- Open resource condition: at each actual exposed parser heap, preserve the owned parser result and establish six-growth room and a sufficient gas bound. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.ParserPostBudget

attribute [blueprint "frontier:parser-public-through-cleanup"
  (title := /-- Function 297: public parser result through absent cleanup -/)
  (statement := /-- Public successful parser result, explicit post-parser room and gas obligation, owned input vector, trie, and frame and host premises. The full parser and accepted-call refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parser_result_through_cleanup

attribute [blueprint "frontier:array-parser-copied-core"
  (title := /-- Function 65: copied-array parser with allocator bounds -/)
  (statement := /-- Concrete escaped copied-array path, explicit parser growth, valid account, reader, heap and room premises. -/)
  (notReady := true)]
  WNear.Binary.FromSliceEsc.f65_arr_copied

attribute [blueprint "frontier:copied-parser-room"
  (title := /-- Derive balance room from copied parser growth -/)
  (statement := /-- Copied parser cleanup resources and an initial parser-growth-plus-six room allowance; returns the actual heap witnesses and six-growth room. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.copied_result_room

attribute [blueprint "frontier:copied-parser-with-room"
  (title := /-- Function 65: copied-array parser preserving balance room -/)
  (statement := /-- Concrete copied-array parser, parser room and allocation assumptions, and initial parser-growth-plus-six allowance. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.f65_arr_copied_room

attribute [blueprint "frontier:balance-copied-parser-through-cleanup"
  (title := /-- Function 297: copied-array parser call through absent cleanup -/)
  (statement := /-- Specific copied/escaped array input and actual function 65 call, initial parser-growth-plus-six room, parser allocation bounds, trie, shared proof budget, host and frame resources; other input cases and full method remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.copied_parser_call_through_cleanup

attribute [blueprint "frontier:balance-input-deref-setup"
  (title := /-- Function 297: dereference input and prepare parser arguments -/)
  (statement := /-- Decoded input vector descriptor, frame, installed code and execution resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.deref_and_parser_setup

attribute [blueprint "frontier:balance-input-deref-through-cleanup"
  (title := /-- Function 297: dereference through copied-array balance cleanup -/)
  (statement := /-- Concrete copied-array input, parser and heap room, trie, input ownership and host/frame premises. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.deref_copied_parser_through_cleanup

attribute [blueprint "frontier:balance-input-expect"
  (title := /-- Function 297: unwrap present input vector -/)
  (statement := /-- Present input option, non-null pointer, installed code and execution resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.input_expect

attribute [blueprint "frontier:balance-input-expect-through-cleanup"
  (title := /-- Function 297: input unwrap through copied-array cleanup -/)
  (statement := /-- Concrete copied-array input, present input vector, parser and heap room, trie and host/frame premises. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.expect_deref_parser_through_cleanup

attribute [blueprint "frontier:balance-input-through-cleanup"
  (title := /-- Function 297: input call through copied-array cleanup -/)
  (statement := /-- Input call arguments prepared, input register limit and allocation room, copied-array parser room, initial input-plus-parser-plus-six growth budget, trie, host and frame premises. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.input_copied_parser_through_cleanup

attribute [blueprint "frontier:balance-input-setup-through-cleanup"
  (title := /-- Function 297: input setup through copied-array cleanup -/)
  (statement := /-- Installed interface, concrete copied-array input, input and parser room, initial growth budget, trie, host and frame premises. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.input_setup_through_cleanup

attribute [blueprint "frontier:balance-method-prologue"
  (title := /-- Function 297: frame and interface prologue -/)
  (statement := /-- Decoded frame, panic hook and blockchain interface setup under installed code and initial memory resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.prologue297

attribute [blueprint "frontier:balance-copied-absent-body"
  (title := /-- Function 297: complete body for copied-array absent account -/)
  (statement := /-- Entire decoded function body for the copied-string array and absent-account path, conditional on input shape, parser and heap room, trie, host, gas and initial frame/static resources. The full accepted/rejected method contract remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body

attribute [blueprint "frontier:input-register-room"
  (title := /-- Input register and allocation room -/)
  (statement := /-- The input register is nonempty, bounded and has room for its allocation; its establishment from the external environment remains open. -/)
  (notReady := true)]
  WNear.Binary.ReadRegister.RegOk

attribute [blueprint "frontier:input-read"
  (title := /-- Environment input and register read -/)
  (statement := /-- The decoded input reader calls the host and returns the input in an owned vector, under the explicit register-room and interface premises. -/)
  (notReady := true)]
  WNear.Binary.EnvInput.f527_spec

attribute [blueprint "frontier:initial-input-copy-room"
  (title := /-- Initial budget supplies input and account-copy room -/)
  (statement := /-- A nonempty bounded input and initial combined growth budget imply input register room and account-copy room at either possible post-input heap. These are conclusions, while the initial budget remains a premise. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.initial_input_and_copy_room

attribute [blueprint "frontier:balance-copied-body-initial-room"
  (title := /-- Function 297: copied-array absent account from initial room -/)
  (statement := /-- Entire decoded body for a copied-string array and absent account, deriving input and account-copy room from the initial combined budget. Parser room, input shape, trie, host, gas and frame conditions remain premises; the full method remains open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_room

attribute [blueprint "frontier:ft-balance-absent-model"
  (title := /-- Absent account gives zero in the boundary model -/)
  (statement := /-- A well-formed represented state, absent account record, and zero storage deficit imply the model returns zero. -/)]
  WNear.Binary.FtBalanceOfMethod.absent_step_zero

attribute [blueprint "frontier:balance-copied-absent-model-composition"
  (title := /-- Copied-array absent execution and model agreement -/)
  (statement := /-- Checked conjunction of the absent-account model result and complete decoded body execution, sharing the absent storage key. Parser room, input shape, represented state, zero deficit, trie, host, gas and frame premises remain explicit; this is not the complete method refinement. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_model_agreement

attribute [blueprint "frontier:protocol-burn-limit"
  (title := /-- Protocol burn-limit upper bound -/)
  (statement := /-- The protocol max gas burnt is at most 10^15. Instantiation from the pinned protocol remains open. -/)
  (notReady := true)]
  WNear.Binary.FtBalanceOfMethod.BurnLimitV86

attribute [blueprint "frontier:balance-argument-charge"
  (title := /-- Accepted-call gas pays the argument byte charge -/)
  (statement := /-- The actual resource-sufficient ft_balance_of gas premise bounds the model charge for all argument bytes. -/)]
  WNear.Binary.FtBalanceOfMethod.argument_charge_le_limit

attribute [blueprint "frontier:balance-argument-length"
  (title := /-- Resource-sufficient balance input size -/)
  (statement := /-- The accepted-call gas premise and named protocol burn-limit bound imply the input is shorter than 2^24 bytes; the pinned burn limit remains open. -/)
  (notReady := true)]
  WNear.Binary.FtBalanceOfMethod.argument_length_lt_2_24

attribute [blueprint "frontier:balance-copied-body-gas-bound"
  (title := /-- Copied-array absent body from caller gas bound -/)
  (statement := /-- The full decoded copied-array absent-account path derives its input length from the accepted-call gas condition, matching model and binary inputs, and the named protocol burn limit. Parser room, heap budget, gas, host, trie and frame conditions remain explicit; arbitrary-resource and full method refinement remain open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_gas_bound
