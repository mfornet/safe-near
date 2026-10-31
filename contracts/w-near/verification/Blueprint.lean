import Architect
import Bridge.Methods.FtBalanceOfObjectCase
import Bridge.Functions.SerdeObjectNoEsc
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
import Bridge.Functions.BalanceOf297ParserRoom
import Bridge.Methods.FtBalanceOfAbsentCompose
import Bridge.Methods.FtBalanceOfInputBound
import Bridge.Methods.ContextInputDomain
import Bridge.Methods.FtBalanceOfCodeCompose
import Bridge.Methods.FtBalanceOfInitialAdequacy
import Bridge.Methods.FtBalanceOfCopiedCase
import Bridge.Methods.FtBalanceOfArrayCase

/-! The browsable proof frontier. Definitions marked Open state contracts, not proofs. -/

attribute [blueprint "frontier:exported-clauses"
  (title := /-- Full exported-method interface -/)
  (statement := /-- Exact all-exported contract consumed by global composition. This is an interface, not an additional admission. -/)
  (notReady := true)]
  WNear.Binary.Exported.Clauses

attribute [blueprint "frontier:exported-clauses-assembly"
  (title := /-- Assemble exported-method interface -/)
  (statement := /-- Assemble exported-method interface. Exact unresolved interfaces remain dependencies. -/)
  (notReady := true)]
  WNear.Binary.Exported.all_clauses

attribute [blueprint "frontier:global-composition"
  (title := /-- Global refinement from exported clauses -/)
  (statement := /-- No sorryAx. Conditional on the exact exported interface; the non-exported branch is proved by export and boundary rollback facts. -/)
  (notReady := true)]
  WNear.refines_wnear_of_clauses

attribute [blueprint "frontier:global-with-obligations"
  (title := /-- Global refinement with named remaining obligations -/)
  (statement := /-- No sorryAx. Reviewed environmental premises and all nine remaining method contracts are explicit hypotheses. Does not instantiate them or the pinned protocol parse witness. -/)
  (notReady := true)]
  WNear.refines_wnear_with_obligations

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
  (statement := /-- Conditional checked assembly with the initialized absent-account array branch proved for both borrowed and copied valid strings. The exact complementary safety/accepted-case obligations, rejected-input rollback and other method/protocol obligations remain unresolved. -/)
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
  (statement := /-- Conditional checked assembly with the initialized absent-account array branch proved for both borrowed and copied valid strings. The exact complementary safety/accepted-case obligations, rejected-input rollback and other method/protocol obligations remain unresolved. -/)
  (notReady := true)]
  WNear.ftBalanceOf_no_issue_obligation

attribute [blueprint "frontier:balance-accepted"
  (title := /-- ft_balance_of: accepted-call refinement -/)
  (statement := /-- Conditional checked assembly with the initialized absent-account array branch proved for both borrowed and copied valid strings. The exact complementary safety/accepted-case obligations, rejected-input rollback and other method/protocol obligations remain unresolved. -/)
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
  (statement := /-- The exact decoded call serializes zero under explicit heap-room and frame premises; the preceding slice is composed by the checked call-copy-format theorem, with its explicit resource premises. -/)
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
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-parser-through-cleanup. Its displayed type premises and readiness remain unchanged. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.copied_parser_call_through_cleanup

attribute [blueprint "frontier:balance-input-deref-setup"
  (title := /-- Function 297: dereference input and prepare parser arguments -/)
  (statement := /-- Decoded input vector descriptor, frame, installed code and execution resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.deref_and_parser_setup

attribute [blueprint "frontier:balance-input-deref-through-cleanup"
  (title := /-- Function 297: dereference through copied-array balance cleanup -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-deref-through-cleanup. Its displayed type premises and readiness remain unchanged. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.deref_copied_parser_through_cleanup

attribute [blueprint "frontier:balance-input-expect"
  (title := /-- Function 297: unwrap present input vector -/)
  (statement := /-- Present input option, non-null pointer, installed code and execution resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.input_expect

attribute [blueprint "frontier:balance-input-expect-through-cleanup"
  (title := /-- Function 297: input unwrap through copied-array cleanup -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-expect-through-cleanup. Its displayed type premises and readiness remain unchanged. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.expect_deref_parser_through_cleanup

attribute [blueprint "frontier:balance-input-through-cleanup"
  (title := /-- Function 297: input call through copied-array cleanup -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-input-through-cleanup. Its displayed type premises and readiness remain unchanged. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.input_copied_parser_through_cleanup

attribute [blueprint "frontier:balance-input-setup-through-cleanup"
  (title := /-- Function 297: input setup through copied-array cleanup -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-input-setup-through-cleanup. Its displayed type premises and readiness remain unchanged. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.input_setup_through_cleanup

attribute [blueprint "frontier:balance-method-prologue"
  (title := /-- Function 297: frame and interface prologue -/)
  (statement := /-- Decoded frame, panic hook and blockchain interface setup under installed code and initial memory resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.prologue297

attribute [blueprint "frontier:balance-copied-absent-body"
  (title := /-- Function 297: complete body for copied-array absent account -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-absent-body. Its displayed type premises and readiness remain unchanged. -/)
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
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-body-initial-room. Its displayed type premises and readiness remain unchanged. -/)
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

attribute [blueprint "frontier:context-wf-with-args"
  (title := /-- Receipt-valid argument replacement -/)
  (statement := /-- Replacing arguments preserves Context.WF provided the replacement satisfies the incoming receipt argument limit. This is the explicitly reviewed domain restriction. -/)]
  WNear.Binary.InputDomain.wf_with_args

attribute [blueprint "frontier:context-wf-bounded-args"
  (title := /-- Context.WF bounds incoming arguments -/)
  (statement := /-- Every well-formed context satisfies the protocol argument-length limit, as required by incoming receipt action validation. -/)]
  WNear.Binary.InputDomain.wf_arguments_bounded

attribute [blueprint "frontier:validated-actions-arguments"
  (title := /-- Runtime validation supplies argument bound -/)
  (statement := /-- Successful runtime validateActions bounds the arguments of every function-call action in that list. This supplies the new WF premise, not the other WF fields or a proof of incoming receipt processing. -/)]
  WNear.Binary.InputDomain.validated_actions_arguments

attribute [blueprint "frontier:protocol-input-limit-order"
  (title := /-- Protocol argument limit fits register limit -/)
  (statement := /-- The protocol maxArgumentsLength is at most maxRegisterSize. Instantiating this relation from the pinned JSON remains open. -/)
  (notReady := true)]
  WNear.Binary.InputDomain.InputLimitsOrdered

attribute [blueprint "frontier:receipt-input-register-bound"
  (title := /-- Receipt-valid inputs fit the register -/)
  (statement := /-- Context.WF and the explicit maxArgumentsLength ≤ maxRegisterSize protocol relation bound input by the register limit. Instantiating the relation from pinned JSON remains open. -/)
  (notReady := true)]
  WNear.Binary.InputDomain.wf_input_fits_register

attribute [blueprint "frontier:no-input-mismatch-witness"
  (title := /-- Receipt domain excludes oversized witness -/)
  (statement := /-- No historical oversized-input mismatch witness satisfies Context.WF when the protocol argument limit is at most its register limit. This does not prove general parsing, arbitrary-resource behavior or the pinned protocol relation. -/)
  (notReady := true)]
  WNear.Binary.InputDomain.no_mismatch_witness

attribute [blueprint "frontier:receipt-input-register-returns"
  (title := /-- Receipt-valid input host call returns -/)
  (statement := /-- The actual input host operation returns after writing register 0 when its input and configuration match the receipt-valid boundary context and the explicit protocol limit relation holds. Surrounding gas charging is separate. -/)
  (notReady := true)]
  WNear.Binary.InputDomain.wf_input_register_returns

attribute [blueprint "frontier:input-register-trap"
  (title := /-- Oversized input traps at register 0 -/)
  (statement := /-- The exact input host operation traps when the input exceeds the configured register limit. The complete binary execution is not proved here. -/)]
  WNear.Binary.InputDomain.input_register_limit_trap

attribute [blueprint "frontier:input-panic-obstruction"
  (title := /-- Input panic contradicts accepted-call observations -/)
  (statement := /-- Given accepted parsing, model success and the binary input-limit panic, the unchanged Exported.At clause is false. These observation premises still require instantiation. -/)]
  WNear.Binary.InputDomain.not_at_of_input_panic

attribute [blueprint "frontier:short-string-room"
  (title := /-- All reserve room for successful short strings -/)
  (statement := /-- A successful run with at most 64 decoded bytes, bounded initial capacity and a numerical page allowance supplies all roomRun reserves, including error boxes. These are derived conclusions; the numerical allowance is explicit. -/)
  (notReady := true)]
  WNear.Binary.ParseStrRoom.roomRun_short

attribute [blueprint "frontier:model-short-string-room"
  (title := /-- Model-accepted short string supplies parser room -/)
  (statement := /-- The exact JSON stringBody acceptance and decoded-byte bound instantiate the complete roomRun contract under a 131-page initial allowance, including arbitrary valid escapes. -/)
  (notReady := true)]
  WNear.Binary.ParseStrRoom.roomRun_of_short_stringBody

attribute [blueprint "frontier:copied-account-parser-pages"
  (title := /-- Copied account parser uses at most six growth pages -/)
  (statement := /-- The account-id validity bound and existing concrete append trace prove at most five scratch growth pages and one owned-string page. The bounded input and exact model decode are explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_parser_pages_le

attribute [blueprint "frontier:input-allocation-pages"
  (title := /-- Bounded input allocation uses at most 257 pages -/)
  (statement := /-- The actual wee_alloc cell-page calculation, under the existing input bound below 2^24 bytes. -/)]
  WNear.Binary.BalanceOf297AbsentCall.input_pages_le

attribute [blueprint "frontier:initial-memory-parser-room"
  (title := /-- Instantiated memory supplies input and parser allowance -/)
  (statement := /-- Derives the input-plus-131 page allowance at InitialState.memLen = 1024 pages under maxP = 2048. HeapRoomK occurs as the derived conclusion, not an assumed room contract. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.initial_memory_room

attribute [blueprint "frontier:initial-combined-parser-room"
  (title := /-- Initial budget supplies parser and downstream room -/)
  (statement := /-- The initial input-plus-131 allowance implies the old body budget and roomRun at both possible post-input memory sizes. General roomRun remains Open outside this specific short-account instance. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.initial_parser_and_body_room

attribute [blueprint "frontier:balance-copied-body-initial-memory"
  (title := /-- Function 297: copied-array absent body at initial memory -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-body-initial-memory. Its displayed type premises and readiness remain unchanged. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_memory

attribute [blueprint "frontier:balance-code-input"
  (title := /-- Initial store: balance input code -/)
  (statement := /-- Extracts the exact input code resources from the instantiated persistent function cells, module instance and memory limit. No code-availability verification hypothesis remains for this component. -/)]
  WNear.Binary.InitialState.code297_input_of

attribute [blueprint "frontier:balance-code-parser"
  (title := /-- Initial store: balance parser code -/)
  (statement := /-- Extracts the exact parser code resources from the instantiated persistent function cells, module instance and memory limit. No code-availability verification hypothesis remains for this component. -/)]
  WNear.Binary.InitialState.code297_parser_of

attribute [blueprint "frontier:balance-code-lookup"
  (title := /-- Initial store: balance lookup code -/)
  (statement := /-- Extracts the exact lookup code resources from the instantiated persistent function cells, module instance and memory limit. No code-availability verification hypothesis remains for this component. -/)]
  WNear.Binary.InitialState.code297_lookup_of

attribute [blueprint "frontier:balance-code-return"
  (title := /-- Initial store: balance return code -/)
  (statement := /-- Extracts the exact return code resources from the instantiated persistent function cells, module instance and memory limit. No code-availability verification hypothesis remains for this component. -/)]
  WNear.Binary.InitialState.code297_return_of

attribute [blueprint "frontier:balance-code-interface"
  (title := /-- Initial store: balance interface code -/)
  (statement := /-- Extracts the exact interface code resources from the instantiated persistent function cells, module instance and memory limit. No code-availability verification hypothesis remains for this component. -/)]
  WNear.Binary.InitialState.code297_interface_of

attribute [blueprint "frontier:balance-code-assembled"
  (title := /-- Initial store: complete copied-balance code -/)
  (statement := /-- Checked assembly of every code component required by the copied-array absent-account body. -/)]
  WNear.Binary.InitialState.code297_of

attribute [blueprint "frontier:balance-code-start-split"
  (title := /-- Split initial store: extract balance code -/)
  (statement := /-- Persists the initial function cells and derives the code while preserving table, memory, host, gas and global ownership. -/)]
  WNear.Binary.InitialState.startCode297_gen

attribute [blueprint "frontier:balance-code-start"
  (title := /-- Whole initial store: extract balance code -/)
  (statement := /-- Starts from ownership of the actual instantiated store and derives the code, retaining raw table and memory resources. Static/frame carving and the full method boundary remain to be composed. -/)]
  WNear.Binary.InitialState.startCode297

attribute [blueprint "frontier:balance-copied-body-store-code"
  (title := /-- Function 297: copied body with actual store code -/)
  (statement := /-- Instantiates the code and module interface in the complete copied-array absent-account body. Table/static/frame/heap/host ownership, exact input and absent key, trie/proof budget, runtime limits and gas remain explicit. Does not yet consume whole-store entry ownership or prove an external MethodClause. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_store_code

attribute [blueprint "frontier:balance-initial-table"
  (title := /-- Initial balance table entries -/)
  (statement := /-- Selects the exact table cells once, including input entry 44, alongside the interface, allocator and formatting entries. No duplicated linear ownership. -/)]
  WNear.Binary.InitialState.table297Of

attribute [blueprint "frontier:balance-initial-input-slot"
  (title := /-- Input vtable word from binary data -/)
  (statement := /-- The input vtable word is the actual data-segment word at 1050224. -/)]
  WNear.Binary.InitialState.seg_v36

attribute [blueprint "frontier:balance-initial-frame"
  (title := /-- Initial balance frame cells -/)
  (statement := /-- Carves the 752-byte initial stack region into the 592-byte lower stack and exact zeroed body buffers and words. Unused gaps are discarded. -/)]
  WNear.Binary.InitialState.frame297_of

attribute [blueprint "frontier:balance-initial-memory"
  (title := /-- Balance memory resources from initial image -/)
  (statement := /-- Carves the frame, interface and allocator words, state key, parser tables, UTF-8 table, formatter tables and zeroed statics from one owned memory image. -/)]
  WNear.Binary.InitialState.memRes297

attribute [blueprint "frontier:balance-initial-statics"
  (title := /-- Assemble initialized balance statics -/)
  (statement := /-- Combines the carved memory with table ownership and memory length/limit, deriving the empty initial heap invariant and retaining the input/parser resources. -/)]
  WNear.Binary.InitialState.statics297P

attribute [blueprint "frontier:balance-initial-start-split"
  (title := /-- Split initial store to all balance resources -/)
  (statement := /-- Derives code, frame, static, heap, table, host and gas resources from the separated initial store. All linear cells are extracted once. -/)]
  WNear.Binary.InitialState.startRes297_gen

attribute [blueprint "frontier:balance-initial-start"
  (title := /-- Whole initial store to balance resources -/)
  (statement := /-- Checked composition from ownership of the actual instantiated store to every resource used by the copied-array absent-account body. -/)]
  WNear.Binary.InitialState.startRes297

attribute [blueprint "frontier:balance-initial-body"
  (title := /-- Copied body with initialized resources -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-initial-body. Its displayed type premises and readiness remain unchanged. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_resources

attribute [blueprint "frontier:balance-initial-store-body"
  (title := /-- Initial store supplies the copied body -/)
  (statement := /-- Derives all body resources from the whole instantiated store, funding credits from that store gas cell under an explicit budget and gas-limit premises. This is an update to the decoded-body Hoare contract, not a full external method clause. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_body_initial_store

attribute [blueprint "frontier:balance-end-observations"
  (title := /-- Ending balance cells imply host and gas observations -/)
  (statement := /-- Extracts both storage-read effects, final host return of quoted zero and the gas bound from the owned ending host/gas cells. -/)]
  WNear.Binary.BalanceOf297AbsentCall.endCells297_ends

attribute [blueprint "frontier:balance-decoded-entry"
  (title := /-- Actual decoded function 297 -/)
  (statement := /-- Kernel-checked function index and decoded body correspondence. -/)]
  WNear.Binary.BalanceOf297AbsentCall.f297_frame

attribute [blueprint "frontier:balance-entry-thread"
  (title := /-- Actual balance entry thread -/)
  (statement := /-- The actual initialized entry thread has the four proved local defaults and the decoded function-297 body. -/)]
  WNear.Binary.BalanceOf297AbsentCall.startW_thread297

attribute [blueprint "frontier:balance-entry-activation"
  (title := /-- Balance activation costs eleven regular operations -/)
  (statement := /-- Checks the eleven regular operations of the actual entry frame. The copied MethodRunsR and model-gas composition now include this charge. -/)]
  WNear.Binary.BalanceOf297AbsentCall.entryCost_297

attribute [blueprint "frontier:balance-entry-adequacy"
  (title := /-- Balance entry: ending-run adequacy -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-entry-adequacy. Its displayed type premises and readiness remain unchanged. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_adequate

attribute [blueprint "frontier:balance-entry-host"
  (title := /-- Balance entry: ending-run host and gas -/)
  (statement := /-- Connects the actual initialized entry thread to both storage-read effects, final host return of quoted zero and bounded used gas for runs that end. Exact input, absent key, host/trie/proof budget, runtime limits and body gas premises remain. No full external method clause is discharged. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_adequate_host

attribute [blueprint "frontier:balance-encoded-account-bound"
  (title := /-- Encoded valid account consumes at most 769 bytes -/)
  (statement := /-- Derives the encoded bound from actual parser recursion, Unicode escapes and the valid decoded account length. Long whitespace is charged separately. -/)]
  WNear.Binary.BalanceOf297AbsentCall.account_encoded_le769

attribute [blueprint "frontier:balance-parser-growth-bound"
  (title := /-- Copied parser has at most five growth allocations -/)
  (statement := /-- Bounds actual scratch growth for a valid account, including escaped source strings. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_growth_count_le5

attribute [blueprint "frontier:balance-parser-cost-bound"
  (title := /-- Copied parser numerical gas bound -/)
  (statement := /-- The exact copied-array parser cost, including trailing whitespace, is at most 300 billion gas plus 80 million per input byte under reviewed costs. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_parser_cost_le300b

attribute [blueprint "frontier:balance-body-cost-bound"
  (title := /-- Initialized balance body numerical gas bound -/)
  (statement := /-- The exact body cost is bounded by 400 billion gas plus 100 million per input byte plus the explicit host charges. Includes input, parsing, state read, absent lookup, return and cleanup. -/)]
  WNear.Binary.BalanceOf297AbsentCall.initial_body_cost_le

attribute [blueprint "frontier:balance-host-cost-bound"
  (title := /-- Balance host charges numerical bound -/)
  (statement := /-- Bounds actual input/register/storage/return host charges by 200 billion plus 10 million per input byte, the two trie reads and three returned bytes. Does not assume trie storage charges are disabled. -/)]
  WNear.Binary.BalanceOf297AbsentCall.initial_host_cost_le

attribute [blueprint "frontier:balance-trie-cost-bound"
  (title := /-- Two actual reads fit the model trie allowance -/)
  (statement := /-- Both actual storage reads fit the model cold/cached trie-node budget for the maximum account key. -/)]
  WNear.Binary.BalanceOf297AbsentCall.initial_body_trie_le

attribute [blueprint "frontier:balance-total-model-gas"
  (title := /-- Loading, activation and body fit model gas -/)
  (statement := /-- Funds the exact initialized-body cost, loading and eleven activation operations from the original model gas allowance. No separate gas-budget verification obligation remains for this case. -/)]
  WNear.Binary.BalanceOf297AbsentCall.initial_total_cost_le_model

attribute [blueprint "frontier:balance-copied-runs"
  (title := /-- Actual copied balance MethodRunsR -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-runs. Its displayed type premises and readiness remain unchanged. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_runs

attribute [blueprint "frontier:balance-copied-model-agreement"
  (title := /-- Copied absent result agrees with model -/)
  (statement := /-- Derives agreement from represented state and both actual storage-read postconditions, including receipt storage-stake failure. No additional no-deficit assumption. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_agreement_of_represents

attribute [blueprint "frontier:balance-copied-entry-pre"
  (title := /-- Context supplies copied entry resources -/)
  (statement := /-- Instantiates input, key/register/return limits, canonical trie, storage view, two-read proof budget and absent storage facts from Context.WF and reviewed runtime limits. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_entry_pre_of

attribute [blueprint "frontier:balance-copied-entry-at"
  (title := /-- Recorded and unrecorded entry instances -/)
  (statement := /-- Supplies both entry instances used by boundary composition. Sufficient recorded proof room supplies the budget; unrecorded execution needs no recorded budget. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_entry_at_of_ctx

attribute [blueprint "frontier:balance-copied-case-refinement"
  (title := /-- Copied array, absent account: full receipt refinement -/)
  (statement := /-- The original copied-only statement is preserved exactly and proved by checked specialization of balance-array-case-refinement. Its displayed type premises and readiness remain unchanged. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_array_absent_refines_init

attribute [blueprint "frontier:balance-copied-case-accepted"
  (title := /-- Completed case supplies accepted-call assembly -/)
  (statement := /-- Packages the proved case in the unchanged accepted-call result shape under reviewed Environment. Its caller is the full accepted-call composition, which remains Conditional. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_case_accepted

attribute [blueprint "frontier:balance-other-accepted"
  (title := /-- ft_balance_of: remaining accepted cases -/)
  (statement := /-- Preserves the previous remaining-case statement and performs a checked split on the broader completed array case. Borrowed and copied strings in that case are proved; its precise complement is still Open. This assembly remains Conditional. -/)
  (notReady := true)]
  WNear.ftBalanceOf_other_accepted_obligation

attribute [blueprint "frontier:balance-copied-case-safety"
  (title := /-- Completed copied case supplies execution safety -/)
  (statement := /-- Extracts execution safety from the complete copied-array absent-account receipt result under reviewed Environment. Integrated into the unchanged general execution-safety assembly. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_case_no_issue

attribute [blueprint "frontier:balance-other-no-issue"
  (title := /-- ft_balance_of: remaining execution-safety contexts -/)
  (statement := /-- Preserves the previous remaining-case statement and performs a checked split on the broader completed array case. Borrowed and copied strings in that case are proved; its precise complement is still Open. This assembly remains Conditional. -/)
  (notReady := true)]
  WNear.ftBalanceOf_other_no_issue_obligation

attribute [blueprint "frontier:array-value-reader"
  (title := /-- Shared account-id reader: borrowed or copied -/)
  (statement := /-- Reuses the existing model-decoded account-id reader with arbitrary reusable scratch. Its explicit parser and allocation-room premises remain named dependencies until the initialized instance supplies them. -/)
  (notReady := true)]
  WNear.Binary.SerdeValueReuse.spec169_model

attribute [blueprint "frontier:array-value-cost-bound"
  (title := /-- Both string paths fit the existing value gas charge -/)
  (statement := /-- The shared borrowed/copied reader charge is bounded by the existing copied-reader charge. No gas allowance or old cost definition changes. -/)]
  WNear.Binary.SerdeValueReuse.valueCost_le

attribute [blueprint "frontier:array-scratch-drop"
  (title := /-- Scratch cleanup preserves the free-list bound -/)
  (statement := /-- The actual vector drop preserves every earlier live allocation and returns a checked free-list bound F+1 for either empty or allocated scratch. Empty scratch uses the permitted monotonic bound. -/)]
  WNear.Binary.SerdeValueReuse.f68_scratch_exact

attribute [blueprint "frontier:array-owned-drop"
  (title := /-- Owned value survives either scratch cleanup path -/)
  (statement := /-- Carries the common reader result through the actual scratch drop, retaining the exact parser/copy growth allowance and the owned account string. -/)]
  WNear.Binary.SerdeValueReuse.f68_owned_value

attribute [blueprint "frontier:array-struct-reader"
  (title := /-- Array struct reads either valid string path -/)
  (statement := /-- Instantiates the changing-state array-struct contract with the existing shared account-id reader and its owned value. General parser/allocation room remains explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructArrModel.f228_arr_model

attribute [blueprint "frontier:array-wrapper-reader"
  (title := /-- Deserialize wrapper for both string paths -/)
  (statement := /-- Checked function-78 wrapper for the common valid-array result and reusable scratch state. -/)
  (notReady := true)]
  WNear.Binary.SerdeStruct78Model.f78_arr_model

attribute [blueprint "frontier:array-parser-cost-domination"
  (title := /-- Common array charge fits the previous bound -/)
  (statement := /-- Lifts the shared value-reader cost inequality to the full array-struct cost, under the exact successful model decode. -/)]
  WNear.Binary.SerdeStruct78Model.costArray_le

attribute [blueprint "frontier:array-from-trait-reader"
  (title := /-- from_trait restores either successful array path -/)
  (statement := /-- Executes the real deserializer construction, array reader, trailing-input check and scratch cleanup; restores the full frame and retains the owned String and concrete heap bounds. -/)
  (notReady := true)]
  WNear.Binary.SerdeFromTraitModel.f66_arr_model

attribute [blueprint "frontier:array-from-slice-reader"
  (title := /-- from_slice accepts both valid string paths -/)
  (statement := /-- Connects the actual function-65 entry to the common array result and exact cleanup bounds. -/)
  (notReady := true)]
  WNear.Binary.FromSliceModel.f65_arr_model

attribute [blueprint "frontier:array-parser-model-core"
  (title := /-- Both array paths use the unchanged parser budget -/)
  (statement := /-- Funds the common function-65 proof from the original parser gas allowance using the proved cost domination. No gas statement is weakened. -/)
  (notReady := true)]
  WNear.Binary.FromSliceModel.f65_arr_model_bound

attribute [blueprint "frontier:array-parser-with-room"
  (title := /-- Both array paths supply balance-entry resources -/)
  (statement := /-- Derives error-box room from the existing growth-plus-six allowance, invokes the common parser with the unchanged budget, and retains the exact owned account and downstream heap room. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.f65_arr_model_room

attribute [blueprint "frontier:balance-array-parser-through-cleanup"
  (title := /-- Balance parser call through cleanup for both array paths -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.array_parser_call_through_cleanup

attribute [blueprint "frontier:balance-array-deref-through-cleanup"
  (title := /-- Balance input dereference through common array cleanup -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.array_deref_parser_through_cleanup

attribute [blueprint "frontier:balance-array-expect-through-cleanup"
  (title := /-- Balance input unwrap through common array cleanup -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.array_expect_deref_parser_through_cleanup

attribute [blueprint "frontier:balance-array-input-through-cleanup"
  (title := /-- Balance input read through common array cleanup -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.array_input_parser_through_cleanup

attribute [blueprint "frontier:balance-array-input-setup-through-cleanup"
  (title := /-- Balance input setup through common array cleanup -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.array_input_setup_through_cleanup

attribute [blueprint "frontier:balance-array-absent-body"
  (title := /-- Whole balance body for either valid array string path -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.array_absent_body

attribute [blueprint "frontier:balance-array-body-initial-room"
  (title := /-- Both array paths from the combined initial allowance -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_room

attribute [blueprint "frontier:balance-array-body-initial-memory"
  (title := /-- Initial memory supplies both array paths -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_memory

attribute [blueprint "frontier:balance-array-initial-body"
  (title := /-- Initial code, frame and statics supply both array paths -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.array_absent_body_initial_resources

attribute [blueprint "frontier:balance-array-entry-adequacy"
  (title := /-- Ending-run adequacy for either array string path -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.array_absent_adequate

attribute [blueprint "frontier:balance-array-runs"
  (title := /-- Metered MethodRunsR for either array string path -/)
  (statement := /-- Checked generalization to borrowed and copied valid strings in the exact array/absent-account branch. The existing copied-only statement is retained as a checked specialization. All displayed resource and environmental premises remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.array_absent_runs

attribute [blueprint "frontier:balance-array-case-refinement"
  (title := /-- Valid array, absent account: full receipt refinement -/)
  (statement := /-- Proven full receipt result for initialized represented state, an unregistered account and any valid model-decoded string in the exact array grammar, with input length below 2^24. Covers borrowed and copied strings, execution safety, sufficient-resource Matches with the unchanged model gas bound, and arbitrary-resource Matches or rollback. Context and represented storage instantiate the entry/trie/proof-budget and model-agreement contracts. Other input/state cases remain unresolved. -/)]
  WNear.Binary.BalanceOf297AbsentCall.array_absent_refines_init

attribute [blueprint "frontier:balance-array-case-accepted"
  (title := /-- All valid array strings supply accepted-call assembly -/)
  (statement := /-- Projects the proved receipt case into the original accepted-call result shape. Both string paths are connected through checked composition to the Conditional accepted-call callers. -/)]
  WNear.Binary.BalanceOf297AbsentCall.array_case_accepted

attribute [blueprint "frontier:balance-array-case-safety"
  (title := /-- All valid array strings supply execution-safety assembly -/)
  (statement := /-- Projects execution safety from the proved full receipt case and connects it to the Conditional general safety callers. -/)]
  WNear.Binary.BalanceOf297AbsentCall.array_case_no_issue

attribute [blueprint "frontier:balance-copied-case-in-array"
  (title := /-- Previous copied case lies inside the completed array case -/)
  (statement := /-- Kernel-checked containment of the old case predicate in the new broader case. Both predicate bodies are pinned; the remaining leaves exclude this entire broader case. -/)]
  WNear.Binary.BalanceOf297AbsentCall.copied_case_is_array_case

attribute [blueprint "frontier:balance-outside-array-accepted"
  (title := /-- ft_balance_of: accepted outside the completed array case -/)
  (statement := /-- Preserves the exact previous outside-array statement and performs a checked split on the new complete object case. The new exact complementary obligation remains Open, so this assembly remains Conditional. -/)
  (notReady := true)]
  WNear.ftBalanceOf_outside_array_absent_accepted_obligation

attribute [blueprint "frontier:balance-outside-array-no-issue"
  (title := /-- ft_balance_of: safety outside the completed array case -/)
  (statement := /-- Preserves the exact previous outside-array statement and performs a checked split on the new complete object case. The new exact complementary obligation remains Open, so this assembly remains Conditional. -/)
  (notReady := true)]
  WNear.ftBalanceOf_outside_array_absent_no_issue_obligation

attribute [blueprint "frontier:object-noesc-keys-before"
  (title := /-- Escape-free object keys before the value -/)
  (statement := /-- Concrete cursor-independent empty-scratch instance. Key behavior and cost are proved; the numerical heap reserve is explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.keys_before

attribute [blueprint "frontier:object-noesc-keys-saved"
  (title := /-- Escape-free object keys retain the saved string -/)
  (statement := /-- Concrete instance after at most one allocation page, preserving the saved account and empty scratch. Its general heap reserve stays explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.keys_saved

attribute [blueprint "frontier:object-noesc-values"
  (title := /-- Escape-free object account value bounds -/)
  (statement := /-- Instantiates the exact ValueConditions with an account of at most 64 decoded bytes, zero scratch growth, at most one allocation page and free-list bound max F0 1. The unchanged K169 cost is proved by allocator monotonicity. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.values

attribute [blueprint "frontier:object-shallow-ignore"
  (title := /-- Shallow ignored values preserve reusable state -/)
  (statement := /-- Existing concrete ignore-reader proof: shallow ignored values preserve both the scratch descriptor and a retained account String. This is an input-restricted IgnoreHyp instance, not a proof of the general obligation. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnReuse.ignoreHyp

attribute [blueprint "frontier:object-noesc-initial-room"
  (title := /-- Initial memory supplies the object loop reserve -/)
  (statement := /-- Derives the 132-page parser reserve after the input allocation from the actual 1024-page initial memory, 2048-page maximum and existing input bound below 2^24. This numerical instance does not construct linear method resources. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.initial_room

attribute [blueprint "frontier:object-noesc-loop"
  (title := /-- Object loop with concrete escape-free reader instances -/)
  (statement := /-- The actual function-228 loop composes the concrete keys, account value and shallow ignore reader. No reader verification hypothesis is assumed. Conditional on the explicit HeapRoomK 132 reserve and required linear parser resources; not full method refinement. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.f228_obj_noesc

attribute [blueprint "frontier:object-noesc-loop-initial"
  (title := /-- Escape-free object loop at instantiated memory -/)
  (statement := /-- Kernel-checked actual function-228 loop with numerical room discharged from initial/input memory sizes, concrete key/value/ignore instances, exact owned String and restored frame. Requires the stated linear code, tables and parser resources. Integrated reader instances reach this loop; ownership construction and functions 78/66/65 into the method remain open. -/)]
  WNear.Binary.SerdeObjectNoEsc.f228_obj_initial_room

attribute [blueprint "frontier:object-wrapper-reader"
  (title := /-- Object loop through the actual 78 wrapper -/)
  (statement := /-- Consumes the proved initial-memory object loop with no reader verification hypothesis. Retains the exact saved account and empty scratch. -/)]
  WNear.Binary.SerdeObjectNoEsc.f78_obj_initial_room

attribute [blueprint "frontier:object-from-trait-reader"
  (title := /-- Object from_trait restores its full frame -/)
  (statement := /-- Actual deserializer construction, object read, trailing-input check and empty scratch drop. Retains owned bytes, at most one allocation page and free-list bound max F 1 + 1. -/)]
  WNear.Binary.SerdeObjectNoEsc.f66_obj_model

attribute [blueprint "frontier:object-from-slice-reader"
  (title := /-- Object from_slice restores all 448 bytes -/)
  (statement := /-- The actual function-65 entry composes the object reader and restores its frame. Extra object static resources are retained explicitly. -/)]
  WNear.Binary.SerdeObjectNoEsc.f65_obj_model

attribute [blueprint "frontier:object-result-room"
  (title := /-- Object result supplies fixed owned account resources -/)
  (statement := /-- Converts the concrete owned String and one-page growth into the exact balance handoff; its general seven-page room premise remains explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.object_result_room

attribute [blueprint "frontier:object-parser-with-room"
  (title := /-- Object parser instantiates the balance handoff -/)
  (statement := /-- Derives every parser/result reserve from actual initial/input memory sizes. Its conclusion is an instance of the named fixed-result and room interfaces, not a proof of those general interfaces. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.f65_obj_room

attribute [blueprint "frontier:parser-call-contract"
  (title := /-- Exact parser-call composition interface -/)
  (statement := /-- Successful function-65 specification consumed at the balance parser call: parser cost, owned account, six-growth result room and retained linear resources. The concrete object provider supplies this interface for its stated domain; the general contract remains Open. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.ParserCallContract

attribute [blueprint "frontier:parser-provider-through-cleanup"
  (title := /-- Parser provider through checked balance cleanup -/)
  (statement := /-- Shared actual parser-call-to-cleanup composition. Conditional on the exact named parser-call interface, with explicit gas, returned free-list bound and retained linear resources. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parser_provider_through_cleanup

attribute [blueprint "frontier:object-parser-instance"
  (title := /-- Concrete object parser-call instance -/)
  (statement := /-- Instantiates the named parser-call interface from the actual object parser and initial-memory reserve. No admitted parser behavior; the conclusion remains marked Conditional as an input-restricted contract instance. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.parser_contract

attribute [blueprint "frontier:object-parser-through-cleanup"
  (title := /-- Object parser through balance cleanup -/)
  (statement := /-- Checked composition through the actual function-297 instructions. Object parser code and static bytes are retained linearly; input/state, resource and environmental premises remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_parser_through_cleanup

attribute [blueprint "frontier:object-deref-through-cleanup"
  (title := /-- Object input dereference through cleanup -/)
  (statement := /-- Checked composition through the actual function-297 instructions. Object parser code and static bytes are retained linearly; input/state, resource and environmental premises remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_deref_parser_through_cleanup

attribute [blueprint "frontier:object-expect-through-cleanup"
  (title := /-- Object input unwrap through cleanup -/)
  (statement := /-- Checked composition through the actual function-297 instructions. Object parser code and static bytes are retained linearly; input/state, resource and environmental premises remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_expect_deref_parser_through_cleanup

attribute [blueprint "frontier:object-input-through-cleanup"
  (title := /-- Object input host through cleanup -/)
  (statement := /-- Checked composition through the actual function-297 instructions. Object parser code and static bytes are retained linearly; input/state, resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.object_input_parser_through_cleanup

attribute [blueprint "frontier:object-input-setup-through-cleanup"
  (title := /-- Object input setup through cleanup -/)
  (statement := /-- Checked composition through the actual function-297 instructions. Object parser code and static bytes are retained linearly; input/state, resource and environmental premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.object_input_setup_through_cleanup

attribute [blueprint "frontier:object-absent-body"
  (title := /-- Whole object absent-account method body -/)
  (statement := /-- Checked specialization of the shared whole-body composition using the concrete object parser family and actual retained code resources. Original statement, depth bound, gas, memory and host premises are preserved; the uniform parser family is instantiated, while RegOk remains explicit until initial-resource composition. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.object_absent_body

attribute [blueprint "frontier:object-initial-memory"
  (title := /-- Initial memory retains both object static slices -/)
  (statement := /-- Carves key-name and identifier bytes together with the existing frame and statics from the whole initialized memory once. No recovery or duplication of discarded linear memory. -/)]
  WNear.Binary.InitialState.memRes297Obj

attribute [blueprint "frontier:object-initial-ignore-code"
  (title := /-- Instantiated functions supply ignored-reader code -/)
  (statement := /-- Kernel-checks every actual function address/body needed by the shallow ignore reader against the instantiated function cells. -/)]
  WNear.Binary.InitialState.ignored_code_of

attribute [blueprint "frontier:object-initial-store"
  (title := /-- Whole initial store supplies object resources -/)
  (statement := /-- Extracts the full method code, ignored-reader code, frame, table entries and both object static byte slices from the owned initial store. -/)]
  WNear.Binary.InitialState.startRes297Obj

attribute [blueprint "frontier:object-initial-body"
  (title := /-- Whole object body from actual initial resources -/)
  (statement := /-- Instantiates the actual frame and input register room from initial memory. No unresolved parser/allocator hypothesis remains in this closed body instance. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_absent_body_initial_resources

attribute [blueprint "frontier:object-entry-adequacy"
  (title := /-- Object entry-thread execution adequacy -/)
  (statement := /-- Ending-run adequacy of the complete object/absent-account body from the whole actual initialized store, with explicit metered budget. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_absent_adequate

attribute [blueprint "frontier:object-runs"
  (title := /-- Metered object MethodRunsR -/)
  (statement := /-- Connects the 11-operation activation charge and actual method body to the existing two-storage-read/zero-return postcondition, for the exact code and initialized resources. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_absent_runs

attribute [blueprint "frontier:object-parser-linear-gas"
  (title := /-- Object parser linear operation bound -/)
  (statement := /-- Proves the existing object parser charge is bounded by (2215 + 470 * input bytes) regular operations plus the single account allocation charge, using the existing key/value/ignore cost bounds. -/)]
  WNear.Binary.SerdeObjectNoEsc.parser_cost_linear

attribute [blueprint "frontier:object-body-gas"
  (title := /-- Complete object body gas bound -/)
  (statement := /-- The actual object body fits 100 billion gas plus 397500000 per input byte and explicit host charges. Retains all input, parser, allocator, storage and return charges. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_body_cost_le

attribute [blueprint "frontier:object-host-gas"
  (title := /-- Sharper object host byte bound -/)
  (statement := /-- Proves the shared input/read/return host charges fit 200 billion gas plus 3 million per input byte and explicit trie/return-data charges, under the existing reviewed CostsV86 premises. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_host_cost_le

attribute [blueprint "frontier:object-total-model-gas"
  (title := /-- Object loading, activation and body fit model gas -/)
  (statement := /-- For inputs up to 4 MiB, the complete deployed charge fits the unchanged model allowance. The input-size bound is explicit; no stronger protocol bound is silently inferred from WProtocol. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_total_cost_le_model

attribute [blueprint "frontier:balance-object-case-refinement"
  (title := /-- Escape-free object, absent account: receipt refinement -/)
  (statement := /-- Proven full receipt result for initialized represented state, an unregistered account, escape-free object input up to 4 MiB, shallow ignored values and trailing whitespace only. Proves no executionIssue, sufficient-resource Matches and original gas bound, and arbitrary-resource Matches or resource failure with rollback and log prefix. Context/storage instantiate the entry, trie/proof budget and model agreement. Other input/state cases remain unresolved. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_absent_refines_init

attribute [blueprint "frontier:balance-object-case-accepted"
  (title := /-- Object case supplies accepted-call assembly -/)
  (statement := /-- Projects the complete receipt theorem into the accepted-call assembly. The exact case predicate is pinned and its callers remain Conditional. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_case_accepted

attribute [blueprint "frontier:balance-object-case-safety"
  (title := /-- Object case supplies execution-safety assembly -/)
  (statement := /-- Projects execution safety for the exact object/absent-account case into checked callers. This does not establish general rejection or other state cases. -/)]
  WNear.Binary.BalanceOf297AbsentCall.object_case_no_issue

attribute [blueprint "frontier:balance-outside-array-object-no-issue"
  (title := /-- ft_balance_of: safety outside completed array/object cases -/)
  (statement := /-- Precise complement of the completed initialized absent-account cases. Escaped objects, ignored values outside the shallow domain, objects above 4 MiB under other protocol contexts, registered/uninitialized states and other inputs remain Open. -/)
  (notReady := true)]
  WNear.ftBalanceOf_outside_array_object_absent_no_issue_obligation

attribute [blueprint "frontier:balance-outside-array-object-accepted"
  (title := /-- ft_balance_of: accepted outside completed array/object cases -/)
  (statement := /-- Precise complement of the completed initialized absent-account cases. Escaped objects, ignored values outside the shallow domain, objects above 4 MiB under other protocol contexts, registered/uninitialized states and other inputs remain Open. -/)
  (notReady := true)]
  WNear.ftBalanceOf_outside_array_object_absent_accepted_obligation

attribute [blueprint "frontier:parser-family"
  (title := /-- Uniform parser provider at actual balance call sites -/)
  (statement := /-- Exact successful-parser family: all credit budgets, call depths with 45 levels reserved, aligned stack pointers with 448 bytes, output/input pointers and initial-or-grown input heap states. Retains key/identifier bytes and declares parser gas and returned free-list bound. This interface is Open in general; it does not assert every accepted input satisfies it. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.ParserFamily

attribute [blueprint "frontier:provider-deref-through-cleanup"
  (title := /-- Parser provider through input dereference -/)
  (statement := /-- Checked actual function-297 composition from a uniform successful parser provider through storage lookup, zero-balance return and cleanup. Parser cost and output free-list bound remain explicit parameters. The provider family remains an unresolved dependency unless concretely instantiated. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_deref_parser_through_cleanup

attribute [blueprint "frontier:provider-expect-through-cleanup"
  (title := /-- Parser provider through option unwrap -/)
  (statement := /-- Checked actual function-297 composition from a uniform successful parser provider through storage lookup, zero-balance return and cleanup. Parser cost and output free-list bound remain explicit parameters. The provider family remains an unresolved dependency unless concretely instantiated. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_expect_deref_parser_through_cleanup

attribute [blueprint "frontier:provider-input-through-cleanup"
  (title := /-- Parser provider through actual input allocation -/)
  (statement := /-- Checked actual function-297 composition from a uniform successful parser provider through storage lookup, zero-balance return and cleanup. Parser cost and output free-list bound remain explicit parameters. The provider family remains an unresolved dependency unless concretely instantiated. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_input_parser_through_cleanup

attribute [blueprint "frontier:provider-input-setup-through-cleanup"
  (title := /-- Parser provider through input setup -/)
  (statement := /-- Checked actual function-297 composition from a uniform successful parser provider through storage lookup, zero-balance return and cleanup. Parser cost and output free-list bound remain explicit parameters. The provider family remains an unresolved dependency unless concretely instantiated. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_input_setup_through_cleanup

attribute [blueprint "frontier:provider-absent-body"
  (title := /-- Whole absent-account body from a parser provider -/)
  (statement := /-- Checked actual function-297 composition from a uniform successful parser provider through storage lookup, zero-balance return and cleanup. Parser cost and output free-list bound remain explicit parameters. The provider family remains an unresolved dependency unless concretely instantiated. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_absent_body

attribute [blueprint "frontier:object-parser-family-instance"
  (title := /-- Object parser instantiates every reachable parser call -/)
  (statement := /-- The escape-free object parser supplies the uniform family for its explicit shallow-ignore/trailing-whitespace domain, with exact parser cost and free-list bound max F 1 + 1. This is an input-restricted instance, not discharge of the general parser family. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.parser_family
