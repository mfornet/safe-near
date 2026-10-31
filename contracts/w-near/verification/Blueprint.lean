import Bridge.Methods.FtBalanceOfWeightedLinearGas
import Bridge.Methods.FtBalanceOfSmallGeneralObject
import Bridge.Methods.FtBalanceOfProviderLinearGas
import Bridge.Functions.SerdeMixedPrefix
import Bridge.Functions.SerdeBundledRate
import Bridge.Functions.SerdeAccountBudget
import Bridge.Functions.SerdeBundledSelected
import Bridge.Functions.SerdeBundledWork
import Bridge.Functions.SerdePrefixSelectedKey
import Bridge.Functions.SerdeObjectPrefix
import Bridge.Functions.SerdeObjectProviderPrecise
import Bridge.Functions.SerdeObjectLedgerGas
import Bridge.Functions.SerdeObjectLedgerProvider
import Bridge.Functions.SerdeObjectLedgerComposition
import Bridge.Functions.SerdeObjectCostComposition
import Bridge.Functions.SerdeObjectKeyCoverage
import Bridge.Functions.SerdeIgnObjectV86
import Bridge.Functions.SerdeIgnObject
import Bridge.Functions.SerdeIgnLoop
import Bridge.Functions.ScratchMixedTrace
import Bridge.Functions.SerdeIgnMachineTrace
import Bridge.Functions.SerdeKeyArgumentGas
import Bridge.Functions.SerdeKeyTraceCost
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
  (statement := /-- The original object MethodRunsR statement is now a checked specialization of actual-code provider execution using the concrete object provider; activation, costs and postcondition are unchanged. -/)]
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
  (statement := /-- Proven full receipt refinement for initialized represented state, an unregistered account, escape-free object input up to 4 MiB, shallow ignored values and trailing whitespace. The concrete object parser/resource/gas plan is instantiated through checked actual-code receipt composition. Original observations and gas are unchanged; other cases remain unresolved. -/)]
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
  (statement := /-- Preserves the exact original full-domain statement. A checked split now directly integrates the completed <=10000-byte full general-object case, then the existing actual-code parser-plan composition. Exact complementary parser/input/state and protocol obligations remain Open; this assembly stays Conditional. -/)
  (notReady := true)]
  WNear.ftBalanceOf_outside_array_object_absent_no_issue_obligation

attribute [blueprint "frontier:balance-outside-array-object-accepted"
  (title := /-- ft_balance_of: accepted outside completed array/object cases -/)
  (statement := /-- Preserves the exact original full-domain statement. A checked split now directly integrates the completed <=10000-byte full general-object case, then the existing actual-code parser-plan composition. Exact complementary parser/input/state and protocol obligations remain Open; this assembly stays Conditional. -/)
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

attribute [blueprint "frontier:provider-initial-store"
  (title := /-- Initial store retains the full parser code context -/)
  (statement := /-- Persists the actual instantiated function cells, instance and memory limit before carving memory once. Supplies the full source code context together with the existing body code, frame, statics and host resources. -/)]
  WNear.Binary.InitialState.startRes297Provider

attribute [blueprint "frontier:object-parser-code-context"
  (title := /-- Actual source code supplies the concrete object parser -/)
  (statement := /-- Extracts the concrete object parser code from the full instantiated code context, using checked parser/return function-cell projections and the ignored-reader code. -/)]
  WNear.Binary.SerdeObjectNoEsc.parser_code_of_context

attribute [blueprint "frontier:parser-family-code-transport"
  (title := /-- Parser family follows checked code entailment -/)
  (statement := /-- Transports the exact parser family along an Iris entailment between persistent code contexts. The parser-family premise remains explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.parser_family_mono

attribute [blueprint "frontier:deployed-parser-provider"
  (title := /-- Parser provider over the actual deployed code context -/)
  (statement := /-- Uniform successful parser family over every initial host state and actual proof-model instance, with code supplied by funcCells in wStore. Parser gas and returned free-list bound are explicit. General accepted inputs still need a concrete instance. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.DeployedParserProvider

attribute [blueprint "frontier:object-deployed-parser-provider"
  (title := /-- Object parser supplies the actual-code provider -/)
  (statement := /-- Concrete escape-free/shallow-object provider, transported from the checked object family to the whole instantiated code context for every entry host state. The output is an input-restricted provider instance. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectNoEsc.deployed_parser_provider

attribute [blueprint "frontier:provider-initial-body"
  (title := /-- Provider body closes input allocation room -/)
  (statement := /-- Derives RegOk from actual initial memory and positive bounded input, then composes the full provider-based body. The precise uniform parser family remains explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_absent_body_initial_resources

attribute [blueprint "frontier:provider-entry-adequacy"
  (title := /-- Actual-code provider entry adequacy -/)
  (statement := /-- Adequacy from the complete actual initialized store. The store retains the full parser code context, and the body consumes the exact family at its actual input allocation state. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_absent_adequate

attribute [blueprint "frontier:provider-runs"
  (title := /-- Actual-code provider metered MethodRunsR -/)
  (statement := /-- Composes the actual eleven-operation activation charge, entry adequacy and the two-read/zero-return postcondition. Uniform actual-code parser execution remains a named obligation. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_absent_runs

attribute [blueprint "frontier:provider-model-budget"
  (title := /-- Whole provider execution fits the original model budget -/)
  (statement := /-- Exact budget obligation for loading, activation and provider body, including parser cost, allocator cleanup, host input/storage/return and trie charges. The original model gas bound is unchanged. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.ProviderModelBudget

attribute [blueprint "frontier:provider-receipt-obligations"
  (title := /-- Provider execution reaches complete receipt refinement -/)
  (statement := /-- Checked safety, sufficient-resource Matches and used-gas bound, plus arbitrary-resource Matches or failure with rollback/log prefix. The actual-code provider and original model-budget obligation remain explicit; entry and model agreement are supplied by the caller. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_absent_refines_with_obligations

attribute [blueprint "frontier:provider-receipt-initial"
  (title := /-- Represented initialized state closes runtime premises -/)
  (statement := /-- Derives the actual entry, storage/trie/proof-budget and model agreement from Context.WF and represented initialized state with an absent account. Only parser execution and its whole-method model budget remain explicit. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_absent_refines_init

attribute [blueprint "frontier:absent-parser-plan"
  (title := /-- Coupled parser, resource and model-gas witness -/)
  (statement := /-- A single parseGas/outF witness must satisfy positive input below 2^24 bytes, actual-code successful parser execution and the unchanged complete model budget. The witness is shared because the budget depends on that same parser cost/free-list bound; this is not another receipt-refinement assumption. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.AbsentParserPlan

attribute [blueprint "frontier:provider-plan-receipt-obligations"
  (title := /-- Parser plan through checked receipt composition -/)
  (statement := /-- Consumes the exact parser/resource/gas plan and composes the completed actual-code method and receipt result. The plan remains Open unless concretely instantiated. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_plan_refines_with_obligations

attribute [blueprint "frontier:provider-plan-receipt-initial"
  (title := /-- Parser plan closes initialized absent-account receipt -/)
  (statement := /-- The top-level reusable receipt composition for initialized represented state and an unregistered account. Context, entry, trie/proof budget and model agreement are checked; parser/resource/gas correctness remains exactly the named plan. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_plan_refines_init

attribute [blueprint "frontier:object-provider-plan"
  (title := /-- Object parser and gas instantiate the complete plan -/)
  (statement := /-- Supplies the shared cost/free-list witness from the actual object provider and proved complete loading/body/trie/return gas bound. Its explicit domain is escape-free objects up to 4 MiB with shallow ignored values; no general parsing obligation is discharged. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.object_provider_plan

attribute [blueprint "frontier:balance-absent-parser-plan"
  (title := /-- Accepted absent-account inputs: parser/resource/gas witness -/)
  (statement := /-- Preserves the exact prior plan statement. Checked construction now proves accepted-input positivity and derives size through Context.WF plus the named pinned ceiling. Only the numerical protocol ceiling and actual parser/gas witness are admitted; every dependent assembly remains Conditional. -/)
  (notReady := true)]
  WNear.ftBalanceOf_absent_parser_plan_obligation

attribute [blueprint "frontier:balance-other-state-accepted"
  (title := /-- Accepted calls outside initialized absent-account state -/)
  (statement := /-- Exact complementary accepted-input/state obligation after excluding every initialized/unregistered-account call as well as both completed cases. Registered/uninitialized behavior remains Open. -/)
  (notReady := true)]
  WNear.ftBalanceOf_other_state_accepted_obligation

attribute [blueprint "frontier:balance-other-input-state-safety"
  (title := /-- Safety outside accepted initialized absent-account calls -/)
  (statement := /-- Exact safety complement: excludes every accepted initialized/unregistered-account context and both completed cases. Rejected input, registered/uninitialized states and remaining safety behavior stay Open. -/)
  (notReady := true)]
  WNear.ftBalanceOf_other_input_state_no_issue_obligation

attribute [blueprint "frontier:key-traced-reader"
  (title := /-- Key reader retains segment and allocator charges -/)
  (statement := /-- Actual function-646 key handoff with the successful string-loop charge and exact scratch endpoint. Room for reachable escaped-string allocation remains explicit; no universal parser-room instance is asserted. -/)
  (notReady := true)]
  WNear.Binary.SerdeKeyEsc.f646_key_traced

attribute [blueprint "frontier:key-traced-cost-domination"
  (title := /-- Traced key charge fits the unchanged public envelope -/)
  (statement := /-- Proves the previous key charge bounds the retained segment/allocation cost for every bounded successful model key. No original key or method gas statement changes. -/)]
  WNear.Binary.SerdeKeyEsc.tracedCost_le_keyCost

attribute [blueprint "frontier:key-growth-reader"
  (title := /-- Existing key contract specializes the traced reader -/)
  (statement := /-- Preserves the exact old key-reader statement. It is now checked composition of the traced key call and cost domination; the general escaped-string room premise remains unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeKeyEsc.f646_key

attribute [blueprint "frontier:scratch-reuse-free-bound"
  (title := /-- Scratch clears retain the evolving free-list bound -/)
  (statement := /-- Across arbitrary append batches starting with used length zero, the free-list bound is initial F plus twice the total actual growth count. Clearing never resets it. -/)]
  WNear.Binary.ScratchReuseTrace.endFreeBound_eq

attribute [blueprint "frontier:scratch-reuse-walks"
  (title := /-- Allocator walks across reused scratch -/)
  (statement := /-- Exact summed allocator-walk identity across clears, retaining the initial F term and the global growth-count square. No constant free-list bound is invented. -/)]
  WNear.Binary.ScratchReuseTrace.walks_eq

attribute [blueprint "frontier:scratch-reuse-copying"
  (title := /-- Copying across clears is paid by peak use -/)
  (statement := /-- Capacity increases telescope across batches. Total old bytes copied are bounded by twice peak used length plus eight, independent of the number of clears. -/)]
  WNear.Binary.ScratchReuseTrace.movedBytes_peak

attribute [blueprint "frontier:scratch-reuse-pages"
  (title := /-- Allocator page requests across reused scratch -/)
  (statement := /-- All page requests are bounded by allocated capacity plus per-growth rounding/header overhead. This is a pure bound under explicit arithmetic trace validity; it does not assume every reserve actually grows memory. -/)]
  WNear.Binary.ScratchReuseTrace.pages_scaled

attribute [blueprint "frontier:scratch-reuse-budget"
  (title := /-- Global scratch reserve budget across keys -/)
  (statement := /-- The complete sum of reserve charges retains changing allocator walks, copied bytes, requested pages and base/unit memory fees. The budget uses one global growth count and peak use rather than a fresh buffer at every key. -/)]
  WNear.Binary.ScratchReuseTrace.extraCost_budget

attribute [blueprint "frontier:scratch-reuse-growth-power"
  (title := /-- Clears do not restart geometric growth -/)
  (statement := /-- A positive global growth count has a power-of-two capacity certificate bounded by peak use. Repeated clears preserve capacity, so each key cannot be charged as a fresh geometric allocation series. -/)]
  WNear.Binary.ScratchReuseTrace.growthCount_peak

attribute [blueprint "frontier:key-series-growth"
  (title := /-- Successive traced key calls share scratch accounting -/)
  (statement := /-- The retained key-reader cost sums to ordinary string work plus the actual globally evolving allocation reserve. This models consecutive key calls with scratch clears; it does not include account allocation or ignored-container operations. -/)]
  WNear.Binary.SerdeKeyEsc.seriesCost_growth

attribute [blueprint "frontier:key-series-valid"
  (title := /-- Model-decoded keys discharge append-trace validity -/)
  (statement := /-- Every successful model key in a bounded input supplies the arithmetic validity and capacity bound of its actual append chunks, carried from one key to the next. No trace-validity obligation is left in the model corollary. -/)]
  WNear.Binary.SerdeKeyEsc.keyBatches_valid

attribute [blueprint "frontier:key-series-input-budget"
  (title := /-- Model keys supply the global reuse budget -/)
  (statement := /-- Discharges arithmetic validity and bounds peak decoded scratch use by the whole input length. The resulting key-only cost bound retains its actual global growth count. Connecting the complete object trace and fitting the unchanged model gas remain unresolved. -/)]
  WNear.Binary.SerdeKeyEsc.seriesCost_budget_model

attribute [blueprint "frontier:key-series-growth-count"
  (title := /-- Model key series supplies a logarithmic growth certificate -/)
  (statement := /-- A bounded successful model key sequence has zero growth or a global power-of-two growth certificate bounded by input length, including arbitrary intervening clears. -/)]
  WNear.Binary.SerdeKeyEsc.keyBatches_growthCount

attribute [blueprint "frontier:balance-input-nonempty"
  (title := /-- Every accepted balance call has nonempty input -/)
  (statement := /-- Kernel-checks that the model decoder rejects the empty byte list, then derives positivity for every accepted ft_balance_of call. No parser/provider or protocol hypothesis is assumed. -/)]
  WNear.Binary.BalanceOf297AbsentCall.accepted_balance_input_nonempty

attribute [blueprint "frontier:argument-limit-v86"
  (title := /-- Pinned argument ceiling needed by parser bounds -/)
  (statement := /-- Exact numerical protocol contract: maxArgumentsLength is at most 4194304 bytes. The pinned JSON implication is separately Open; Context.WF alone does not discharge it. -/)
  (notReady := true)]
  WNear.Binary.InputDomain.ArgumentLimitV86

attribute [blueprint "frontier:receipt-small-arguments"
  (title := /-- Reviewed receipt bound composes with the argument ceiling -/)
  (statement := /-- Context.WF supplies the incoming argument-length bound. The explicit protocol ceiling then bounds actual arguments by 4 MiB; that numerical protocol instance is not silently assumed. -/)
  (notReady := true)]
  WNear.Binary.InputDomain.wf_arguments_small

attribute [blueprint "frontier:balance-accepted-input-bounds"
  (title := /-- Accepted input supplies parser positivity and length -/)
  (statement := /-- Combines proved accepted-input nonemptiness and the reviewed incoming receipt domain. Positivity is discharged; the pinned numerical ceiling remains explicit. -/)
  (notReady := true)]
  WNear.Binary.InputDomain.accepted_balance_input_bounds

attribute [blueprint "frontier:absent-plan-input-composition"
  (title := /-- Parser plan closes its input-domain components -/)
  (statement := /-- Constructs the original exact parser plan from a shared provider/gas witness, proved accepted-input positivity and the explicit protocol ceiling. The provider, original model budget and pinned ceiling remain named dependencies. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.absent_plan_of_parser_cost

attribute [blueprint "frontier:pinned-arguments-limit"
  (title := /-- Pinned JSON implies the 4 MiB argument ceiling -/)
  (statement := /-- Precise remaining protocol field obligation. This does not provide the protocol parse witness, runtime premises or any other field proof. -/)
  (notReady := true)]
  WNear.pinned_arguments_obligation

attribute [blueprint "frontier:balance-absent-parser-cost"
  (title := /-- Accepted absent-parser cost: checked small case and explicit complement -/)
  (statement := /-- The exact original statement is preserved. Checked case split constructs actual parser provider and original funding for the completed <=10000-byte full general-object case; only the explicitly excluded complement remains admitted. This composition is Conditional and retains every protocol/domain premise. -/)
  (notReady := true)]
  WNear.ftBalanceOf_absent_parser_cost_obligation

attribute [blueprint "frontier:string-escape-work-sharp"
  (title := /-- Successful escapes fit 433 operations per encoded byte -/)
  (statement := /-- Strengthens the existing successful-escape work bound while retaining the actual scratch reserve charge. Includes simple escapes, Unicode and surrogate pairs; no model gas change. -/)]
  WNear.Binary.ParseStrSuccess.escape_growth_charge_sharp

attribute [blueprint "frontier:string-work-sharp"
  (title := /-- Successful string work sharpens 470 to 433 operations per byte -/)
  (statement := /-- Proves the stronger linear bound on the existing successful string-loop charge, including fitting appends and final UTF-8. Every actual allocation/growth cost remains in the separate evolving trace. The deployed model allowance is unchanged. -/)]
  WNear.Binary.ParseStrSuccess.costRun_growth_sharp

attribute [blueprint "frontier:key-growth-count-v86"
  (title := /-- Bounded input permits at most 21 global key-scratch growths -/)
  (statement := /-- Derives a concrete growth-count bound from the checked power certificate and explicit 4 MiB input size. Clears and repeated keys do not restart growth. The pinned protocol field implication remains separately Open. -/)]
  WNear.Binary.SerdeKeyEsc.keyBatches_growthCount_v86

attribute [blueprint "frontier:key-peak-consumed"
  (title := /-- Peak key scratch is paid by consumed key bytes -/)
  (statement := /-- Successful model keys bound peak scratch use by the sum of their consumed source slices, including their closing quotes. This does not assert those slices cover the whole object input. -/)]
  WNear.Binary.SerdeKeyEsc.keyBatches_peak_consumed

attribute [blueprint "frontier:scratch-reuse-budget-v86"
  (title := /-- Reviewed costs close the global key reserve formula -/)
  (statement := /-- For initial free-list bound one and at most 21 growths, the proved reserve formula fits 200 billion gas plus 37 times the reviewed operation price per peak byte. This is the numeric reserve ceiling; full method gas remains unresolved. -/)]
  WNear.Binary.SerdeKeyEsc.reserve_budget_v86

attribute [blueprint "frontier:key-argument-slice-gas"
  (title := /-- Key-only cost fits the original argument-byte allowance -/)
  (statement := /-- Proves the key-only sequence is bounded by a fixed 200-billion-gas reserve plus the unchanged model argumentByteGas for consumed key bytes and two structural bytes per key. Uses actual reused capacity/free-list accounting and reviewed CostsV86. Full input coverage of this slice, account/ignored-container operations and other runtime charges remain Open. -/)]
  WNear.Binary.SerdeKeyEsc.seriesCost_argument_gas

attribute [blueprint "frontier:scratch-mixed-free-bound"
  (title := /-- One allocator bound across mixed scratch segments -/)
  (statement := /-- Every segment carries the actual ending allocator bound into the next; clears retain allocation. The final bound is F plus twice the global growth count. -/)]
  WNear.Binary.ScratchMixedTrace.endFreeBound_eq

attribute [blueprint "frontier:scratch-mixed-walks"
  (title := /-- Exact allocator walks across strings and frame stacks -/)
  (statement := /-- The exact F*G + G*G - G walk sum composes string appends and frame pushes/pops. Capacity and F never restart at a clear. -/)]
  WNear.Binary.ScratchMixedTrace.walks_eq

attribute [blueprint "frontier:scratch-mixed-capacity"
  (title := /-- Mixed scratch capacity follows peak use -/)
  (statement := /-- The final capacity is bounded by the initial capacity or twice the global high-water use plus eight. Each append/frame segment has its existing exact transition and validity conditions. -/)]
  WNear.Binary.ScratchMixedTrace.endCap_capacity

attribute [blueprint "frontier:scratch-mixed-copying"
  (title := /-- Mixed scratch copying telescopes across clears -/)
  (statement := /-- Old bytes copied across all string and frame growths are at most twice the global peak plus eight. Pops and clears retain capacity. -/)]
  WNear.Binary.ScratchMixedTrace.movedBytes_peak

attribute [blueprint "frontier:scratch-mixed-allocation"
  (title := /-- Mixed requested allocations telescope -/)
  (statement := /-- All requested allocation capacities sum to at most four times the global peak plus sixteen, with initial capacity cancelling out. This is not yet a full HeapRoomK6 instance. -/)]
  WNear.Binary.ScratchMixedTrace.allocatedBytes_peak

attribute [blueprint "frontier:scratch-mixed-pages"
  (title := /-- Mixed growth retains page rounding and headers -/)
  (statement := /-- Requested pages retain every growth header and rounding charge, including growths after pops and clears. -/)]
  WNear.Binary.ScratchMixedTrace.pages_scaled

attribute [blueprint "frontier:scratch-mixed-cost"
  (title := /-- Actual mixed reserve costs are retained -/)
  (statement := /-- The combined reserve charge includes changing allocator walks, old-byte copying, requested pages, and base/unit memory fees for both actual segment models. -/)]
  WNear.Binary.ScratchMixedTrace.extraCost_le

attribute [blueprint "frontier:scratch-mixed-budget"
  (title := /-- One global reserve budget for strings and frame stacks -/)
  (statement := /-- Composes append and frame-stack accounting into one global reserve bound. Valid requires the existing arithmetic bounds of each actual segment; it supplies no full parser or ignored-value Wasm implementation. -/)]
  WNear.Binary.ScratchMixedTrace.extraCost_budget

attribute [blueprint "frontier:scratch-mixed-frame-budget"
  (title := /-- Frame-only reserve is a mixed-trace instance -/)
  (statement := /-- Instantiates mixed validity from the existing frame trace validity and explicit initial/final capacity bounds. -/)]
  WNear.Binary.ScratchMixedTrace.frames_budget

attribute [blueprint "frontier:scratch-mixed-frame-domination"
  (title := /-- Mixed reserve preserves the old frame allowance -/)
  (statement := /-- The tighter exact walk sum is bounded by the existing frame budget; its public allowance is unchanged. -/)]
  WNear.Binary.ScratchMixedTrace.budget_le_frame_budget

attribute [blueprint "frontier:scratch-append-mixed-valid"
  (title := /-- String batches instantiate mixed validity -/)
  (statement := /-- Checked embedding of existing string-only batches as append segments. Original capacity and allocator transitions are preserved exactly. -/)]
  WNear.Binary.ScratchReuseTrace.mixed_valid

attribute [blueprint "frontier:scratch-append-mixed-growth"
  (title := /-- String embedding preserves global growth count -/)
  (statement := /-- Checked embedding of existing string-only batches as append segments. Original capacity and allocator transitions are preserved exactly. -/)]
  WNear.Binary.ScratchReuseTrace.mixed_growthCount

attribute [blueprint "frontier:scratch-append-mixed-peak"
  (title := /-- String embedding preserves high-water use -/)
  (statement := /-- Checked embedding of existing string-only batches as append segments. Original capacity and allocator transitions are preserved exactly. -/)]
  WNear.Binary.ScratchReuseTrace.mixed_peak

attribute [blueprint "frontier:scratch-append-mixed-cost"
  (title := /-- String embedding preserves actual reserve charge -/)
  (statement := /-- Checked embedding of existing string-only batches as append segments. Original capacity and allocator transitions are preserved exactly. -/)]
  WNear.Binary.ScratchReuseTrace.mixed_extraCost

attribute [blueprint "frontier:ignore-machine-trace-valid"
  (title := /-- Successful ignored values produce valid physical stack traces -/)
  (statement := /-- The existing pure ignored-value machine yields the actual physical push/pop trace, an empty final frame vector, and peak/push bounds in consumed input. This is a model trace theorem; the complete function-81 Wasm proof remains Open. -/)]
  WNear.Binary.SerdeIgnMachineTrace.trace_valid

attribute [blueprint "frontier:ignore-machine-mixed-budget"
  (title := /-- Successful ignored values instantiate the mixed reserve -/)
  (statement := /-- Instantiates the stronger mixed reserve for the actual pure-machine frame trace and bounds its high-water use by consumed input. Full ignored-value execution and whole-object trace assembly remain unresolved. -/)]
  WNear.Binary.SerdeIgnMachineTrace.trace_mixed_budget

attribute [blueprint "frontier:ignore-machine-trace-budget"
  (title := /-- Existing ignored-value budget composes from mixed reserve -/)
  (statement := /-- The old successful ignored-value trace budget is now a checked specialization of the mixed reserve, preserving its original statement and allowance. -/)]
  WNear.Binary.SerdeIgnMachineTrace.trace_budget

attribute [blueprint "frontier:ignored-pop-prefix"
  (title := /-- Real pops retain the exact original trace prefix -/)
  (statement := /-- Extends the exact removed-frame prefix and its false-operation prefix after one saved-frame pop. Initialization is checked inside the loop proof. -/)]
  WNear.Binary.SerdeIgnLoop.Pops.step

attribute [blueprint "frontier:ignored-container-iteration"
  (title := /-- Shared invariant for the actual container iteration -/)
  (statement := /-- Composes nested/final close and first/comma iteration proofs. Retains actual saved-frame contents, cursor, remaining trace, allocator state and single gas-credit ownership. -/)]
  WNear.Binary.SerdeIgnLoop.iteration

attribute [blueprint "frontier:ignored-container-loop"
  (title := /-- Complete actual ignored-container loop -/)
  (statement := /-- The real loop consumes one entry charge, establishes its invariant from a successful pure-machine continuation, and preserves exact pop prefixes. Its checked exits are first-member, comma-member or final success. This is not the outer value loop. -/)]
  WNear.Binary.SerdeIgnLoop.loop

attribute [blueprint "frontier:ignored-container-phase"
  (title := /-- Actual container block retains its rejecting tail -/)
  (statement := /-- Composes the complete loop with the real enclosing block and post-loop guard. Every successful path bypasses the unchanged rejecting bytecode and establishes a member continuation or the actual success branch. -/)]
  WNear.Binary.SerdeIgnLoop.phase

attribute [blueprint "frontier:ignored-suffix-code"
  (title := /-- Container/member suffix is exact deployed bytecode -/)
  (statement := /-- Kernel equality identifies the composed suffix with all actual decoded function-81 value-loop instructions after its successful value-dispatch prefix. -/)]
  WNear.Binary.SerdeIgnLoop.suffixCode_at

attribute [blueprint "frontier:ignored-container-suffix"
  (title := /-- Container and full member path compose to the next value -/)
  (statement := /-- The full actual container/member suffix composes through the funded array/key/colon path. It enters the next value loop or takes the real success branch, preserving exact remaining trace, cursor, caller resources and retained allocation. -/)]
  WNear.Binary.SerdeIgnLoop.suffix

attribute [blueprint "frontier:ignored-decoded-suffix"
  (title := /-- Suffix contract is connected to deployed function 81 -/)
  (statement := /-- Uses checked equality to apply the container/member suffix contract directly to the actual decoded function body. Full value-entry/outer-loop/cleanup composition, growth room, original full-method gas and IgnoreHyp remain unresolved. -/)]
  WNear.Binary.SerdeIgnLoop.decoded_suffix

attribute [blueprint "frontier:ignored-pending-entry"
  (title := /-- Pending scalar entry of the actual value loop -/)
  (statement := /-- Pays the actual peek, presence and pending-scalar instructions and preserves the remaining trace, frame stack and resource budget. -/)]
  WNear.Binary.SerdeIgnValueEntry.pending_entry

attribute [blueprint "frontier:ignored-top-entry"
  (title := /-- Top scalar takes the actual success branch -/)
  (statement := /-- Checks the complete scalar entry prefix and real success branch with an empty pending stack. -/)]
  WNear.Binary.SerdeIgnValueEntry.top_entry

attribute [blueprint "frontier:ignored-opening-entry"
  (title := /-- Container opening enters the shared value invariant -/)
  (statement := /-- Reuses the checked opening proof with the full 128-byte value-loop frame and exact allocation transition. Growth room remains an explicit premise. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnValueEntry.opening_entry128

attribute [blueprint "frontier:ignored-trace-room"
  (title := /-- Room for every actual growth in an ignored-value trace -/)
  (statement := /-- Exact remaining room obligation along the successful trace, quantified over each permitted actual heap transition. No concrete reachable-state instance is claimed. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.Room

attribute [blueprint "frontier:ignored-heap-trace"
  (title := /-- Heap trace follows actual saved-frame growth -/)
  (statement := /-- Constructs the precise allocation-history relation through a saved frame, including the actual heap transition and retained capacity. -/)]
  WNear.Binary.SerdeIgnExecution.heap_save

attribute [blueprint "frontier:ignored-value-iteration"
  (title := /-- Complete deployed ignored-value iteration -/)
  (statement := /-- Composes scalar/opening entries with the actual container/member suffix. Room for the whole remaining trace is an unresolved explicit dependency. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.value_iteration

attribute [blueprint "frontier:ignored-value-loop"
  (title := /-- Complete deployed outer ignored-value loop -/)
  (statement := /-- Establishes and preserves one gas-credit invariant with exact cursor, pending frames, remaining trace, allocation endpoints and heap history. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.value_loop

attribute [blueprint "frontier:ignored-main"
  (title := /-- Ignored-value loop reaches actual cleanup and return -/)
  (statement := /-- Retains both rejecting tails and checks the real enclosing branches, success and cleanup. Conditional on trace growth room. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.main

attribute [blueprint "frontier:ignored-raw-prologue"
  (title := /-- Actual ignored-reader prologue clears scratch length -/)
  (statement := /-- Checks the actual prologue from raw scratch ownership with arbitrary old length. It clears that word before interpreting the empty pending stack. -/)]
  WNear.Binary.SerdeIgnExecution.start_raw

attribute [blueprint "frontier:ignored-full-reader"
  (title := /-- Full actual ignored-reader execution -/)
  (statement := /-- Complete deployed function 81, including prologue, loops, retained rejecting tails and cleanup. Returns the precise successful endpoint and heap history, with explicit remaining growth-room obligation. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.f81_core

attribute [blueprint "frontier:ignored-traced-reader"
  (title := /-- Successful syntax trace instantiates full function 81 -/)
  (statement := /-- Instantiates the complete reader using the successful pure syntax trace and derived frame validity. Growth room remains unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.f81_traced

attribute [blueprint "frontier:ignored-colon-reader"
  (title := /-- Actual colon caller composes with full ignored reader -/)
  (statement := /-- Checks function 201 against the real colon and full function-81 contracts, retaining actual heap history, allocation endpoints and cost. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.f201_traced

attribute [blueprint "frontier:ignored-member-conditions"
  (title := /-- Reachable ignored-member room, gas and state closure -/)
  (statement := /-- For each successful reachable member trace: supplies Room, fits the actual reader cost into the chosen allowance, and closes the caller bounds along its exact HeapTrace. Still Open for concrete B, Bsaved and K. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.IgnoreConditions

attribute [blueprint "frontier:ignored-hyp-instance"
  (title := /-- IgnoreHyp constructed from actual reader and named closure -/)
  (statement := /-- Instantiates the existing IgnoreHyp interface with the checked deployed reader. Conditional on IgnoreConditions for current and saved bounds; does not discharge the general IgnoreHyp interface. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.ignoreHyp

attribute [blueprint "frontier:ignored-object-composition"
  (title := /-- General object loop uses the actual ignored reader -/)
  (statement := /-- Constructs IgnoreHyp and composes it into the existing general object-loop proof. KeyConditions, ValueConditions and ignored-member room/gas/state closure remain explicit unresolved dependencies. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.object_loop

attribute [blueprint "frontier:ignored-room-pages"
  (title := /-- Requested-page budget constructs trace room -/)
  (statement := /-- Constructs Room by induction over actual reserve transitions from a total requested-page budget, positive aligned heap and address/page ceiling. Conditional classification reflects Room in its conclusion; the constructor has no admission. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.room_of_pages

attribute [blueprint "frontier:ignored-heap-pages"
  (title := /-- Actual heap trace preserves alignment and obeys page budget -/)
  (statement := /-- Bounds every permitted actual final heap between its initial length and initial length plus requested pages, and preserves its page residue. No arbitrary final-heap assumption. -/)]
  WNear.Binary.SerdeIgnExecution.heap_pages_bound

attribute [blueprint "frontier:ignored-capacity-v86"
  (title := /-- Successful 4 MiB values preserve the object capacity ceiling -/)
  (statement := /-- A successful full syntax trace with initial capacity below 2^25 has final capacity below 2^25. Uses the actual retained-capacity/peak bound; no caller closure assumption. -/)]
  WNear.Binary.SerdeIgnExecution.trace_end_cap_v86

attribute [blueprint "frontier:ignored-pages-v86"
  (title := /-- Successful 4 MiB values request at most 18,362,816 bytes of pages -/)
  (statement := /-- Derives at most 24 growths from valid capacity doubling, then bounds exact page requests using the successful trace peak. This is a pure bound under explicit input/capacity premises, not protocol instantiation. -/)]
  WNear.Binary.SerdeIgnExecution.trace_pages_v86

attribute [blueprint "frontier:ignored-room-v86"
  (title := /-- Concrete trace-room instance for an aligned 96 MiB heap -/)
  (statement := /-- Constructs Room under the 2,048-page ceiling for a successful value up to 4 MiB starting at a positive aligned heap no larger than 96 MiB. Whole-object establishment of the starting heap bound is not claimed. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnExecution.room_v86

attribute [blueprint "frontier:ignored-reader-pages"
  (title := /-- Full deployed reader instantiated from a physical page budget -/)
  (statement := /-- Instantiates the full actual reader by constructing its Room argument from explicit page, positivity and alignment bounds. The scoped operational contract has no remaining Room hypothesis. -/)]
  WNear.Binary.SerdeIgnExecution.f81_traced_of_pages

attribute [blueprint "frontier:ignored-reader-v86"
  (title := /-- Full reader with concrete input and starting-heap bounds -/)
  (statement := /-- Full deployed f81 contract for successful values up to 4 MiB and a positive aligned starting heap at most 96 MiB under 2,048 pages. Room is constructed, not assumed. Whole-method reachable-heap and protocol instantiation remain separate Open obligations. -/)]
  WNear.Binary.SerdeIgnExecution.f81_traced_v86

attribute [blueprint "frontier:ignored-colon-v86"
  (title := /-- Real colon caller uses the concrete-room full reader -/)
  (statement := /-- Composes the actual colon function directly with the concrete-room f81 contract. Retains exact cost, cursor, heap trace and owned allocation endpoints under the explicit input/starting-heap bounds. -/)]
  WNear.Binary.SerdeIgnExecution.f201_traced_v86

attribute [blueprint "frontier:ignored-reachable-conditions"
  (title := /-- Remaining physically reachable ignored-member conditions -/)
  (statement := /-- For actual positive aligned scratch heaps: establishes the 96 MiB starting-heap ceiling, reader cost allowance and exact HeapTrace closure of B/Bsaved. These three whole-object obligations remain Open. Room and final capacity are derived by the new constructor. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.ReachableIgnoreConditions

attribute [blueprint "frontier:ignored-reachable-hyp"
  (title := /-- IgnoreHyp uses actual memory alignment and constructed room -/)
  (statement := /-- Reads alignment/positivity from owned scratch, constructs reader room, and proves final capacity. Conditional on ReachableIgnoreConditions for current and saved bounds. Preserves the original IgnoreHyp interface. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.ignoreHyp_v86

attribute [blueprint "frontier:ignored-reachable-object"
  (title := /-- General object caller integrates concrete ignored-reader room -/)
  (statement := /-- Constructs IgnoreHyp with actual scratch alignment and concrete reader room, then applies the general object loop. Remains Conditional on reachable heap/gas/state closure, KeyConditions and ValueConditions. No global or full-method obligation is declared closed. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.object_loop_v86

attribute [blueprint "frontier:object-key-cover"
  (title := /-- Object key charges occupy disjoint input bytes -/)
  (statement := /-- For the exact key/cursor path, raw key-body bytes plus two structural bytes per key fit the consumed object-loop input. Includes escapes and UTF-8; no theorem about all parser costs is asserted. -/)]
  WNear.Binary.SerdeObjectCoverage.key_walk_coverage

attribute [blueprint "frontier:object-key-models"
  (title := /-- Every extracted object key satisfies the string model -/)
  (statement := /-- The ordered path supplies the exact successful stringBody model at every recorded absolute key cursor. -/)]
  WNear.Binary.SerdeObjectCoverage.key_walk_models

attribute [blueprint "frontier:object-key-path"
  (title := /-- Successful general object loop yields the actual key path -/)
  (statement := /-- Extracts an ordered KeyWalk from every successful model object loop, including account fields, escaped keys and arbitrary successful ignored values. Value suffixes and actual colon consumption ensure nonoverlap. -/)]
  WNear.Binary.SerdeObjectCoverage.loop_keys

attribute [blueprint "frontier:object-key-gas"
  (title := /-- Actual object keys instantiate the key argument-gas slice -/)
  (statement := /-- Combines the actual successful loop path, key model witnesses, disjoint coverage and the existing key-sequence bound using the unchanged argumentByteGas coefficient. This key-only scratch sequence still does not include interleaved frame/account allocation or all parser operations. -/)]
  WNear.Binary.SerdeObjectCoverage.loop_key_argument_budget

attribute [blueprint "frontier:object-key-opening"
  (title := /-- Full object opening supplies the checked key path -/)
  (statement := /-- Instantiates key-path extraction at the same actual opening cursor and objLoop premise used by the composed object-parser contract. -/)]
  WNear.Binary.SerdeObjectCoverage.object_keys

attribute [blueprint "frontier:object-key-hyp"
  (title := /-- Generic changing-state key call interface -/)
  (statement := /-- The generic key-call premise remains Open; the concrete key constructor supplies it assuming named KeyConditions. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.KeyHyp

attribute [blueprint "frontier:object-value-hyp"
  (title := /-- Generic changing-state account-value call interface -/)
  (statement := /-- The generic account-value premise remains Open; the concrete value constructor supplies it assuming named ValueConditions. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.ValueHyp

attribute [blueprint "frontier:object-close-hyp"
  (title := /-- Physical final-brace state handoff -/)
  (statement := /-- State transport only from the pre-close cursor through whitespace and the actual final closing brace. The concrete prefix-state instance remains unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.CloseHyp

attribute [blueprint "frontier:object-loop-closing"
  (title := /-- Actual object loop needs only the final-brace handoff -/)
  (statement := /-- The unchanged public f228 contract is now a checked composition of the phase-aware actual loop and four explicit phase-independent adapters. Every existing parser/receipt caller uses this composition. Original key/value/ignore/close interfaces remain explicit unresolved dependencies. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.f228_obj_state_closing

attribute [blueprint "frontier:object-loop-monotone"
  (title := /-- Original object loop is a checked compatibility result -/)
  (statement := /-- The original public statement is unchanged and now composes from the closing-only loop by deriving its final-brace premise from the old general cursor-monotonicity hypothesis. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.f228_obj_state

attribute [blueprint "frontier:object-closing-conditions"
  (title := /-- Pure bounds close only at the actual final brace -/)
  (statement := /-- The precise remaining pure bound transport for current and saved member states. It does not require those states to be monotone across every input position. Concrete prefix-state instances remain Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjModelState.ClosingConditions

attribute [blueprint "frontier:object-closing-adapter"
  (title := /-- Legacy monotonicity instantiates the narrower closing premise -/)
  (statement := /-- A checked adapter preserves old public APIs. The generic ClosingConditions family remains Open for the actual prefix states needed by the full parser proof. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjModelState.closing_of_mono

attribute [blueprint "frontier:object-member-closing"
  (title := /-- Owned member state crosses the physical final brace -/)
  (statement := /-- Transports the actual scratch, heap, tables and retained account allocation using the named current/saved closing conditions. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjModelState.member_closing

attribute [blueprint "frontier:object-model-closing"
  (title := /-- Concrete key/value readers feed the closing-only object loop -/)
  (statement := /-- Constructs key and value call contracts and the final-brace handoff, then applies the actual loop. IgnoreHyp, KeyConditions, ValueConditions and ClosingConditions remain unresolved in this generic interface. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjModelState.f228_obj_model_closing

attribute [blueprint "frontier:object-key-fuel"
  (title := /-- Actual key path fits the successful model fuel -/)
  (statement := /-- Strengthens key-path extraction with an exact fuel bound, allowing its cost recurrence to follow every actual key/value call. -/)]
  WNear.Binary.SerdeObjectCoverage.loop_keys_fuel

attribute [blueprint "frontier:object-key-component"
  (title := /-- Exact key component of the object-loop cost -/)
  (statement := /-- For the value-linked ordered key path, objCost equals the sum of its key allowances plus objCost with key allowances set to zero. All residual charges are retained. -/)]
  WNear.Binary.SerdeObjectCoverage.objCost_key_component

attribute [blueprint "frontier:object-key-cost-path"
  (title := /-- Successful model supplies exact key charges and coverage -/)
  (statement := /-- Combines fuel-bounded extraction, successful key models, disjoint raw-byte coverage and the exact key/residual cost equation. -/)]
  WNear.Binary.SerdeObjectCoverage.loop_keys_cost

attribute [blueprint "frontier:object-cost-key-component"
  (title := /-- Complete object cost splits at the actual opening cursor -/)
  (statement := /-- Extends the exact key-charge equation through the real object prologue/exit cost interface, retaining all other charges. -/)]
  WNear.Binary.SerdeObjectCoverage.object_key_cost

attribute [blueprint "frontier:ignored-object-closing"
  (title := /-- Concrete-room reader feeds the precise closing assembly -/)
  (statement := /-- Uses the actual f81/f201 reader and constructs IgnoreHyp, with only the precise final-brace transport required of B/Bsaved. Key/value, reachable heap/gas/state and closing conditions remain Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.object_loop_v86_closing

attribute [blueprint "frontier:ignored-object-key-cost"
  (title := /-- Actual object Wasm contract exposes exact key/residual cost -/)
  (statement := /-- Composes the concrete-room object reader with the proved model key path and exact cost equality. The Wasm budget is equal to its previous cost, now visibly key charges plus residual charges. Total mixed allocation/parser gas domination remains unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.object_loop_v86_key_cost

attribute [blueprint "frontier:mixed-growth-power"
  (title := /-- Mixed retained capacity pays every growth -/)
  (statement := /-- The first allocation is at least eight bytes and every later growth doubles across string/frame segments. -/)]
  WNear.Binary.ScratchMixedTrace.growth_power

attribute [blueprint "frontier:mixed-growth-v86"
  (title := /-- One global growth bound across mixed scratch use -/)
  (statement := /-- At most 21 scratch growths from empty capacity when the mixed high-water length is at most 4 MiB. No per-member reset. -/)]
  WNear.Binary.ScratchMixedTrace.growth_v86

attribute [blueprint "frontier:mixed-pages-v86"
  (title := /-- One global requested-page bound for mixed scratch -/)
  (statement := /-- Bounds scratch page bytes by 18,164,618 under the 4 MiB high-water premise. -/)]
  WNear.Binary.ScratchMixedTrace.pages_v86

attribute [blueprint "frontier:mixed-account-page"
  (title := /-- A valid account allocation requests at most one page -/)
  (statement := /-- Instantiates the allocator page bound from the actual model AccountId UTF-8 length ceiling. -/)]
  WNear.Binary.SerdeObjectMixedTrace.account_id_page

attribute [blueprint "frontier:mixed-segment-model-bounds"
  (title := /-- Successful reader models bound each scratch segment -/)
  (statement := /-- Successful string/frame models establish actual trace validity, retained capacity below 2^25 and peak below the bounded input length. -/)]
  WNear.Binary.SerdeObjectMixedTrace.segment_bounds

attribute [blueprint "frontier:mixed-batches-model-bounds"
  (title := /-- Successful mixed segments preserve one retained scratch -/)
  (statement := /-- Carries validity/capacity across the complete model segment sequence with one global peak, including the account string. -/)]
  WNear.Binary.SerdeObjectMixedTrace.batches_bounds

attribute [blueprint "frontier:mixed-model-pages"
  (title := /-- Successful mixed models instantiate the page bound -/)
  (statement := /-- Any retained sequence of successful segments from a 4 MiB input satisfies the global scratch page bound. -/)]
  WNear.Binary.SerdeObjectMixedTrace.scratch_pages

attribute [blueprint "frontier:mixed-call-path"
  (title := /-- Every actual key/value step supplies its scratch segments -/)
  (statement := /-- Expands the value-linked key path into ordered key appends, account-string appends or ignored-frame traces, preserving exact endpoints and counting account calls. -/)]
  WNear.Binary.SerdeObjectMixedTrace.expand_key_walk

attribute [blueprint "frontier:mixed-call-models"
  (title := /-- Every ordered call segment has a successful model -/)
  (statement := /-- Projects actual string/ignored models from the ordered call trace; arbitrary invented scratch segments are not admitted. -/)]
  WNear.Binary.SerdeObjectMixedTrace.call_trace_models

attribute [blueprint "frontier:mixed-account-calls"
  (title := /-- Successful object loops allocate at most one account -/)
  (statement := /-- The successful model duplicate check bounds account-field calls, including the already-seen case. -/)]
  WNear.Binary.SerdeObjectMixedTrace.loop_keys_account

attribute [blueprint "frontier:mixed-loop-pages"
  (title := /-- Complete successful object model has one allocation-page budget -/)
  (statement := /-- Extracts the ordered complete scratch trace and at most one account call. Scratch page bytes plus one page per account call are bounded by 18,230,154. This remains a model trace until its reader resource contracts are instantiated. -/)]
  WNear.Binary.SerdeObjectMixedTrace.loop_total_pages

attribute [blueprint "frontier:object-ledger-initial"
  (title := /-- Empty scratch establishes the concrete ledger -/)
  (statement := /-- Initializes one retained scratch history and no saved-account allocation. -/)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.initial

attribute [blueprint "frontier:object-ledger-ceiling"
  (title := /-- The mixed ledger bounds every reachable heap -/)
  (statement := /-- From the explicit initial heap budget, all ledger states remain at most 96 MiB, including the saved account slot. B does not assume alignment of hypothetical interval lengths. -/)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.heap_ceiling

attribute [blueprint "frontier:object-ledger-segment"
  (title := /-- Actual segment effects preserve the heap/capacity ledger -/)
  (statement := /-- Appends a successful segment, retaining exact capacity/free-bound transitions and accumulating actual requested pages plus the account slot. -/)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.segment

attribute [blueprint "frontier:object-ledger-ignored-state"
  (title := /-- The actual ignored heap history closes the ledger -/)
  (statement := /-- Uses the exact returned HeapTrace to instantiate the segment ledger and preserve all endpoint resource bounds. -/)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.ignored

attribute [blueprint "frontier:object-ledger-closing"
  (title := /-- The ledger constructs final-brace closing transport -/)
  (statement := /-- Constructs ClosingConditions for this concrete invariant. The generic closing interface remains Open for other states. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.closing

attribute [blueprint "frontier:object-ignore-charges"
  (title := /-- Remaining ignored-reader gas allowance -/)
  (statement := /-- Only the actual ignored-reader cost versus chosen K remains in this contract; ledger room/heap/state transport is constructed separately. It remains Open until the original parser budget supplies K. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.IgnoreCharges

attribute [blueprint "frontier:object-key-room-charges"
  (title := /-- Remaining key-reader room and gas allowance -/)
  (statement := /-- Exact reachable key room and charge obligations after ledger state closure has been proved. The original model allowance is unchanged. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.KeyRoomCharges

attribute [blueprint "frontier:object-value-room-charges"
  (title := /-- Remaining account-reader room and gas allowance -/)
  (statement := /-- Exact error/string/account-allocation room and charge obligations; final state transport is supplied by the ledger. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ValueRoomCharges

attribute [blueprint "frontier:object-ledger-ignore"
  (title := /-- Ledger constructs reachable ignored-reader conditions -/)
  (statement := /-- Instantiates the reachable heap ceiling and exact ignored state closure. Conditional on the explicitly named ignored gas allowance and initial numeric heap bound. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.ignore_conditions

attribute [blueprint "frontier:object-ledger-key"
  (title := /-- Ledger constructs the key closure contract -/)
  (statement := /-- Proves the actual retained key capacity/free-bound and heap endpoint closure, leaving only named key room/charge obligations. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.key_conditions

attribute [blueprint "frontier:object-ledger-value"
  (title := /-- Ledger constructs account-value state closure -/)
  (statement := /-- Preserves retained scratch and adds the one owned account slot; max free-bound is stable from a positive initial bound. Room and cost remain explicit named obligations. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.value_conditions

attribute [blueprint "frontier:object-ledger-setup"
  (title := /-- Initial heap/free-bound ledger instance -/)
  (statement := /-- The actual input pipeline still must establish baseHL+18,230,154 <= 96 MiB and a positive initial free bound. No Environment or method domain is strengthened. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.LedgerSetup

attribute [blueprint "frontier:object-ledger-reader"
  (title := /-- Concrete ledger instantiates the actual object reader -/)
  (statement := /-- Constructs key/value/ignore/closing contracts and composes the existing actual Wasm key/residual contract. The named initial ledger setup and room/gas obligations remain Open, so this result is Conditional. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.object_loop_ledger

attribute [blueprint "frontier:object-ledger-member"
  (title := /-- Actual raw scratch resources initialize the ledger member -/)
  (statement := /-- Constructs the initial member invariant from owned empty scratch, allocator tables and actual byte tables. No ledger witness is assumed. -/)]
  WNear.Binary.SerdeObjectMixedTrace.member_initial

attribute [blueprint "frontier:object-ledger-initial-reader"
  (title := /-- Raw initial resources feed the ledger object Wasm contract -/)
  (statement := /-- Composes raw member initialization with the actual object reader, retaining its equal key/residual budget and postcondition. Initial pipeline setup, remaining room/gas and the complete parser budget remain unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.object_loop_ledger_initial

attribute [blueprint "frontier:ledger-wrapper-generic"
  (title := /-- Actual object wrapper preserves any checked callee -/)
  (statement := /-- Proves the decoded f78 wrapper with one gas-credit cell and an explicit call-depth bound. The generic callee is an owned checked specification, not an admission. -/)]
  WNear.Binary.SerdeObjectMixedTrace.f78_of_object_spec

attribute [blueprint "frontier:ledger-key-wrapper"
  (title := /-- Ledger key/residual reader reaches f78 -/)
  (statement := /-- Composes the published raw-resource f228 contract through the actual f78 call, preserving the exact key/residual allowance and all named unresolved setup/room/gas contracts. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f78_ledger_initial

attribute [blueprint "frontier:ledger-cost-wrapper"
  (title := /-- Ledger object reader with original cost recurrence -/)
  (statement := /-- Builds the same concrete ledger reader and raw initializer through f78 at the unchanged object-cost recurrence. Uses checked closing/key/value/ignore instances; all setup/room/gas obligations remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f78_ledger_initial_cost

attribute [blueprint "frontier:ledger-scratch-cleanup"
  (title := /-- Actual cleanup frees empty or retained scratch -/)
  (statement := /-- The actual f68 drop handles capacity zero and nonzero uniformly within 315 regular-operation gas, preserves the exact original live list and returns a free-list bound F+1. No assumption that successful scratch capacity is zero. -/)]
  WNear.Binary.SerdeObjectMixedTrace.f68_retained_scratch

attribute [blueprint "frontier:ledger-final-bounds"
  (title := /-- Ledger bounds survive the complete object -/)
  (statement := /-- Successful retained segments bound total heap growth by 18,230,154 bytes and the free-list bound by baseF+42, independently of a per-member scratch reset. -/)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.final_bounds

attribute [blueprint "frontier:ledger-from-trait"
  (title := /-- General object parser reaches actual f66 cleanup -/)
  (statement := /-- Checked f66 execution includes initial deserializer resources, f78, trailing EOF/whitespace, output moves and actual retained scratch cleanup. It returns only the account allocation; room/gas and setup instances remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f66_ledger_object

attribute [blueprint "frontier:ledger-from-slice"
  (title := /-- General object slice entry reaches cleanup -/)
  (statement := /-- Actual f65 composes f66, restores the 448-byte caller stack, and preserves input/static resources. It does not discharge reader charges or original model gas. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f65_ledger_object

attribute [blueprint "frontier:ledger-result-room"
  (title := /-- Ledger account result supplies balance execution room -/)
  (statement := /-- Actual owned heap alignment/positivity and the ledger ceiling yield six pages of balance execution room. The generic LedgerSetup and fixed-result interface remain explicit in this constructor. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_result_room

attribute [blueprint "frontier:ledger-from-slice-room"
  (title := /-- Slice parser returns the exact balance handoff -/)
  (statement := /-- Composes f65 with six-page result room and a uniform baseF+43 free-list bound after the actual scratch drop. All original reader/setup contracts remain visible. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f65_ledger_room

attribute [blueprint "frontier:ledger-parser-call"
  (title := /-- General object supplies the shared parser-call contract -/)
  (statement := /-- Packages the actual slice parser and retained resources into the existing ParserCallContract used by the full balance pipeline. Its named verification contracts are not discharged by this packaging. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_parser_contract

attribute [blueprint "frontier:ledger-container-code"
  (title := /-- Full container code comes from the instantiated store -/)
  (statement := /-- Constructs all ignored-container, reserve, reallocation and escape function-cell resources directly from actual codeCtx. The projection uses kernel checked binary function cells. -/)]
  WNear.Binary.SerdeObjectMixedTrace.ignored_member_code_of_context

attribute [blueprint "frontier:ledger-parser-code"
  (title := /-- General parser code comes from the instantiated store -/)
  (statement := /-- Combines the reviewed existing parser code projection with the full container code projection; no function-code premise is assumed externally. -/)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_parser_code_of_context

attribute [blueprint "frontier:ledger-input-bounds"
  (title := /-- Actual input allocation establishes ledger setup bounds -/)
  (statement := /-- For inputs at most 4 MiB, initial memory or the real input allocation requests at most 65 pages and establishes the ledger heap ceiling. A positive initial free bound supplies the remaining setup conjunct; the deployed provider instantiates F=1. No environment/model premise is strengthened. -/)]
  WNear.Binary.SerdeObjectMixedTrace.input_ledger_bounds

attribute [blueprint "frontier:ledger-parser-family"
  (title := /-- General parser family instantiates initial ledger setup -/)
  (statement := /-- All real input allocation outcomes instantiate LedgerSetup numerically from the input bound. The returned shared family remains Conditional on named key/value room/gas and ignored gas contracts for those heap instances. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_parser_family

attribute [blueprint "frontier:ledger-deployed-provider"
  (title := /-- General parser supplies the actual-code deployed provider -/)
  (statement := /-- Transports the full object family from actual codeCtx for every entry host state. Instantiates initial F=1 and output F=44; reader room/gas remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_deployed_parser_provider

attribute [blueprint "frontier:ledger-provider-plan"
  (title := /-- General object couples execution and original model budget -/)
  (statement := /-- The selected K functions determine both actual parser execution and the same ProviderModelBudget witness. No new budget or weaker observation is substituted. All charge contracts and whole-method budget remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_provider_plan

attribute [blueprint "frontier:ledger-receipt"
  (title := /-- General object reaches checked full receipt refinement -/)
  (statement := /-- Composes the concrete object provider plan through the existing initialized absent-account receipt theorem: safety, sufficient-resource Matches/used gas, arbitrary-resource Matches or rollback/log-prefix resource failure. It remains Conditional on named reader charges, unchanged ProviderModelBudget and reviewed protocol/environment premises. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_refines_init

attribute [blueprint "frontier:string-page-reserve"
  (title := /-- Requested pages cover every reserve heap outcome -/)
  (statement := /-- Constructs reserve room and all permitted next-heap room instances from a page allowance, with alignment/positivity and 32-bit limits explicit. Generic room interfaces remain visible. -/)
  (notReady := true)]
  WNear.Binary.ParseStrRoom.reserve_pages_room

attribute [blueprint "frontier:string-page-run"
  (title := /-- A successful string page trace supplies recursive room -/)
  (statement := /-- Constructs roomRun for every growth/error-box prefix of a successful raw string run. The conservative borrowed-tail reserve is represented explicitly; this generic page-allowance premise is not assumed in concrete ledger room. -/)
  (notReady := true)]
  WNear.Binary.ParseStrRoom.roomRun_pages

attribute [blueprint "frontier:string-room-trace"
  (title := /-- Copied-string room trace is the actual append trace -/)
  (statement := /-- A successful copied string, or a nonempty prior accumulator, has exactly the real appendChunks reserve trace. Escape output positivity establishes the recursive copied state. -/)]
  WNear.Binary.ParseStrRoom.roomChunks_copied

attribute [blueprint "frontier:string-any-short"
  (title := /-- Short strings have room with any retained capacity -/)
  (statement := /-- Removes the old capacity-at-most-128 restriction: a non-fitting short reserve itself forces the old capacity small, while larger retained capacities fit. Generic initial page room remains explicit. -/)
  (notReady := true)]
  WNear.Binary.ParseStrRoom.roomRun_short_any

attribute [blueprint "frontier:ledger-reader-pages"
  (title := /-- Every ledger string suffix fits the global page bound -/)
  (statement := /-- Extends the retained model ledger by the actual successful string segment, bounding that reader alone by the global 18,164,618 requested-page bytes. Does not reset capacity or charge the entire prefix again. -/)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.append_pages_bound

attribute [blueprint "frontier:ledger-account-room"
  (title := /-- Concrete ledger constructs all account reader room -/)
  (statement := /-- Ledger heap ceiling, owned alignment/positivity, account length and actual append pages construct error-box, string and account-allocation room. This is a checked constructor of the generic room interfaces, with no reader-room hypothesis. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.account_room

attribute [blueprint "frontier:object-value-gas"
  (title := /-- Remaining account reader gas allowance -/)
  (statement := /-- Only the exact actual valueCost versus the chosen K remains here. Concrete error/string/account-allocation room is constructed from the ledger; no room or state closure premise is hidden in this contract. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ValueGasCharges

attribute [blueprint "frontier:ledger-value-gas-charges"
  (title := /-- Account room/gas interface from ledger room and gas -/)
  (statement := /-- Instantiates the old ValueRoomCharges with checked ledger room and only the named ValueGasCharges obligation. The gas obligation remains Open until the original parser budget chooses K. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.value_charges

attribute [blueprint "frontier:ledger-key-room"
  (title := /-- Concrete ledger supplies successful key reader room -/)
  (statement := /-- Borrowed keys use the existing no-allocation error-room contract. Copied keys use the actual append trace and the global ledger page bound to construct every reserve/error-box room instance. No key-room premise is assumed. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.key_room

attribute [blueprint "frontier:object-key-gas-obligation"
  (title := /-- Remaining key reader gas allowance -/)
  (statement := /-- Only the exact keyCost versus the selected per-cursor K remains. Concrete key room is proved from the actual ledger; the gas witness is still unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.KeyGasCharges

attribute [blueprint "frontier:ledger-key-gas-charges"
  (title := /-- Key room/gas interface from ledger room and gas -/)
  (statement := /-- Instantiates old KeyRoomCharges from concrete ledger key room and the named KeyGasCharges. It does not prove gas domination or alter the old interface. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.key_charges

attribute [blueprint "frontier:ledger-gas-family"
  (title := /-- Shared parser family needs only reader gas obligations -/)
  (statement := /-- Constructs the old key/value room/gas hypotheses for every real initial/input heap before invoking the existing actual parser family. Remaining reader obligations are gas-only; whole-model gas is not supplied here. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_gas_parser_family

attribute [blueprint "frontier:ledger-gas-provider"
  (title := /-- Actual-code provider with reader room instantiated -/)
  (statement := /-- Uses actual instantiated function cells and the shared family with checked reader room. Initial F=1/output F=44 and the same real parser cost are retained. Key/value/ignored gas remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_gas_deployed_parser_provider

attribute [blueprint "frontier:ledger-gas-plan"
  (title := /-- Original-budget plan from the gas-only reader frontier -/)
  (statement := /-- Couples the same selected K costs and actual provider with unchanged ProviderModelBudget. Concrete reader room is constructed, while all reader gas and the whole-method budget remain unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_gas_provider_plan

attribute [blueprint "frontier:ledger-gas-receipt"
  (title := /-- Full receipt composition with reader room discharged -/)
  (statement := /-- Checked initialized absent-account receipt refinement now assumes only named reader gas and the original whole-model budget, plus reviewed protocol/environment premises. It proves the same safety, sufficient-resource Matches/used gas and arbitrary-resource rollback/log-prefix alternatives conditionally. No room predicate is a remaining reader hypothesis. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_gas_refines_init

attribute [blueprint "frontier:precise-key-cost-compat"
  (title := /-- Actual key cost fits the preserved legacy allowance -/)
  (statement := /-- The borrowed fast charge is unchanged. The copied actual trace charge is bounded by the old keyCost, preserving all old public statements. -/)]
  WNear.Binary.SerdeKeyReuse.preciseCost_le_keyCost

attribute [blueprint "frontier:precise-key-work"
  (title := /-- Precise keys retain 433-op work and actual growth -/)
  (statement := /-- Bounds successful borrowed/copied key work by 500+433 operations per consumed byte plus the real retained-capacity extraCost. It does not substitute the legacy 470-op growth envelope or prove the whole model budget. -/)]
  WNear.Binary.SerdeKeyReuse.preciseCost_growth_sharp

attribute [blueprint "frontier:precise-key-reader"
  (title := /-- Actual f646 key reader at its trace cost -/)
  (statement := /-- Selects the existing borrowed fast reader or actual copied traced reader, retaining the exact key/scratch resource result and explicit physical room. -/)
  (notReady := true)]
  WNear.Binary.SerdeKeyReuse.f646_key_precise

attribute [blueprint "frontier:precise-next-key-reader"
  (title := /-- Actual f193 composes the precise key reader -/)
  (statement := /-- The next-key function keeps its original stack, cursor, result classification and scratch endpoints while consuming the actual key trace charge. -/)
  (notReady := true)]
  WNear.Binary.SerdeKeyReuse.f193_key_model_precise

attribute [blueprint "frontier:precise-key-conditions"
  (title := /-- Precise key gas, room and state contract -/)
  (statement := /-- Exact key interface for arbitrary caller bounds: physical room, preciseCost versus K, and state closure at the actual capacity/free-bound endpoint. This generic interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjKeyState.PreciseKeyConditions

attribute [blueprint "frontier:precise-key-hyp"
  (title := /-- Precise concrete keys supply the object-loop hypothesis -/)
  (statement := /-- Constructs the existing object KeyHyp from the actual precise f193 reader and named PreciseKeyConditions for before/saved states. No new gas-credit ownership is added. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjKeyState.keyHyp_precise

attribute [blueprint "frontier:precise-object-closing"
  (title := /-- Object model composes precise key charges -/)
  (statement := /-- Actual f228 composition uses the precise key hypothesis with the same value, ignored-reader, closing and cursor/resource results. Those named interfaces remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjModelState.f228_obj_model_closing_precise

attribute [blueprint "frontier:precise-ignored-object"
  (title := /-- Full ignored reader feeds the precise object model -/)
  (statement := /-- The checked full ignored-reader constructor and precise key model compose at the unchanged costObj recurrence, with reachable state, value and closing obligations visible. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnObject.object_loop_v86_closing_precise

attribute [blueprint "frontier:precise-key-gas"
  (title := /-- Remaining precise key trace-gas allowance -/)
  (statement := /-- Only the actual borrowed/copied preciseCost against selected per-cursor K remains. It is still Open; the coarse ledger does not by itself provide the prefix-specific reuse/gas witness. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.PreciseKeyGasCharges

attribute [blueprint "frontier:precise-ledger-keys"
  (title := /-- Ledger room/state plus precise key gas -/)
  (statement := /-- Constructs precise key room and exact ledger state transport; only PreciseKeyGasCharges is assumed for the chosen K. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.Ledger.precise_key_conditions

attribute [blueprint "frontier:precise-ledger-wrapper"
  (title := /-- Precise key object reader reaches f78 -/)
  (statement := /-- Actual object and wrapper code compose with raw scratch initialization, checked room/state, precise key gas, account/ignored gas and explicit LedgerSetup. The original recurrence and output ownership are retained. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f78_ledger_precise_cost

attribute [blueprint "frontier:precise-from-trait"
  (title := /-- Precise key allowance survives f66 and cleanup -/)
  (statement := /-- Actual f66 carries precise key costs through EOF/whitespace checking, result moves and retained scratch cleanup, with the same concrete account result and bounds. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f66_ledger_precise

attribute [blueprint "frontier:precise-from-slice"
  (title := /-- Precise parser reaches actual slice entry -/)
  (statement := /-- Actual f65 composes the precise f66 contract, restores its full caller frame and preserves input/static resources without changing public observations. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f65_ledger_precise

attribute [blueprint "frontier:precise-from-slice-room"
  (title := /-- Precise slice parser supplies balance room -/)
  (statement := /-- The same checked concrete owned-account handoff supplies six pages of balance room and the retained output free bound after precise-key parsing. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.f65_ledger_precise_room

attribute [blueprint "frontier:precise-parser-call"
  (title := /-- Precise cost supplies the shared parser-call interface -/)
  (statement := /-- Packages the actual precise-key slice contract in the unchanged ParserCallContract used by the whole balance execution pipeline. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_precise_parser_contract

attribute [blueprint "frontier:precise-parser-family"
  (title := /-- Shared family instantiates precise reader room and setup -/)
  (statement := /-- Real input heap outcomes instantiate setup numerically; remaining reader hypotheses are precise key, account and ignored gas witnesses. No legacy key allowance is assumed in this family. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_precise_parser_family

attribute [blueprint "frontier:precise-deployed-provider"
  (title := /-- Actual-code provider with precise key costs -/)
  (statement := /-- Transports the precise family from actual persistent function cells for every entry host state, with the same parser cost recurrence and output free bound 44. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_precise_deployed_parser_provider

attribute [blueprint "frontier:precise-provider-plan"
  (title := /-- Actual precise parser couples to the original model budget -/)
  (statement := /-- The same K functions and precise actual provider are coupled to unchanged ProviderModelBudget. Reader gas and the whole-method budget remain Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_precise_provider_plan

attribute [blueprint "frontier:precise-receipt"
  (title := /-- Full receipt refinement with precise key allowance -/)
  (statement := /-- Checked initialized absent-account receipt composition retains safety, sufficient-resource Matches/used gas, and arbitrary-resource Matches or resource-failure rollback/log-prefix. Precise key gas, value/ignored gas and the original whole-model budget remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.ledger_precise_refines_init

attribute [blueprint "frontier:precise-key-conditions-compat"
  (title := /-- Legacy key conditions imply precise conditions -/)
  (statement := /-- Checked compatibility uses actual preciseCost domination; it preserves the old interface and does not claim its unresolved gas/closure obligations are discharged. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjKeyState.precise_conditions_of_legacy

attribute [blueprint "frontier:precise-key-gas-compat"
  (title := /-- Legacy key gas implies the precise gas contract -/)
  (statement := /-- The existing legacy gas witness suffices for the sharper actual reader. The reverse implication and gas domination within the original model allowance are not assumed. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.precise_gas_of_legacy

attribute [blueprint "frontier:prefix-value-model"
  (title := /-- Actual value segments supply the retained scratch model -/)
  (statement := /-- Known-account strings and unknown-key ignored traces each construct the corresponding modeled segment at the exact input endpoint. -/)]
  WNear.Binary.SerdeObjectMixedTrace.value_segment_model

attribute [blueprint "frontier:phase-key-hyp"
  (title := /-- Key reader records its pending field -/)
  (statement := /-- The exact key name indexes the post-key resource state. A concrete phase-aware reader instance is still required. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhase.KeyHyp

attribute [blueprint "frontier:phase-value-hyp"
  (title := /-- Account reader consumes the known field phase -/)
  (statement := /-- The value reader requires pending account_id and returns to the next-member phase. This general reader interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhase.ValueHyp

attribute [blueprint "frontier:phase-ignore-hyp"
  (title := /-- Ignored reader consumes a different pending field -/)
  (statement := /-- The ignore branch receives the actual pending key and its inequality with account_id. Its concrete phase-aware state/gas instance remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhase.IgnoreHyp

attribute [blueprint "frontier:phase-close-hyp"
  (title := /-- Brace transports the member phase to done -/)
  (statement := /-- The final brace carries member resources to the done phase at the exact cursor. The general closing interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhase.CloseHyp

attribute [blueprint "frontier:phase-object-loop"
  (title := /-- Actual object loop preserves field phases -/)
  (statement := /-- The deployed f228 loop records the exact parsed field, transports equality in the account branch and supplies inequality in ignored branches. The original gas recurrence and single credit cell are retained. Named key/value/ignore/close instances remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhase.f228_obj_state_closing

attribute [blueprint "frontier:phase-key-compat"
  (title := /-- Existing key contracts instantiate phase-independent states -/)
  (statement := /-- Checked adapter supplies the phase-aware key interface when the existing state ignores its phase. Both general interfaces remain Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.phase_key_hyp

attribute [blueprint "frontier:phase-value-compat"
  (title := /-- Existing account contracts instantiate phase-independent states -/)
  (statement := /-- Checked adapter supplies the known-field interface from the original universal account contract without claiming its remaining instances proved. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.phase_value_hyp

attribute [blueprint "frontier:phase-ignore-compat"
  (title := /-- Existing ignore contracts instantiate unknown-key phases -/)
  (statement := /-- The original universal ignore contract supplies each actual unknown-key branch at a phase-independent state. It retains all existing unresolved reader hypotheses. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.phase_ignore_hyp

attribute [blueprint "frontier:phase-close-compat"
  (title := /-- Existing brace transport instantiates phase closing -/)
  (statement := /-- The exact original CloseHyp supplies member-to-done transport for a phase-independent state. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.phase_close_hyp

attribute [blueprint "frontier:prefix-models"
  (title := /-- Actual prefixes retain modeled scratch segments -/)
  (statement := /-- The phase-indexed prefix relation records actual key/colon/value models, the pending key, duplicate-account condition, exact cursor, retained segment history and saved-account flag. Every segment is modeled. This does not yet supply physical reader instances or a gas budget. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.models

attribute [blueprint "frontier:prefix-ledger"
  (title := /-- Exact prefix specializes the coarse physical ledger -/)
  (statement := /-- Given exact retained capacity/free-list endpoints and the existing physical heap bound, the modeled prefix supplies the original Ledger without weakening its statement. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.ledger

attribute [blueprint "frontier:prefix-initial"
  (title := /-- Prefix starts at the exact initial member cursor -/)
  (statement := /-- The empty scratch history starts only at the initial member phase and its specified cursor; the unchanged coarse physical initializer is retained. -/)]
  WNear.Binary.SerdeObjectPrefix.initial_ledger

attribute [blueprint "frontier:prefix-first-exact"
  (title := /-- First-member phase cannot recur at another cursor -/)
  (statement := /-- Every first-member prefix has the initial cursor, empty retained history and no saved account. It does not establish the later deterministic prefix or gas witness. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.first_exact

attribute [blueprint "frontier:prefix-pending-key"
  (title := /-- Pending field comes from the exact preceding key read -/)
  (statement := /-- Every value phase exposes its actual preceding key model, saved-account state and retained-history extension. Physical reader constructors and deterministic prefix gas remain missing. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.pending_key

attribute [blueprint "frontier:prefix-reader-lens"
  (title := /-- Phase reader lends and restores exact owned state -/)
  (statement := /-- The saved descriptor retains account bytes while the parser core moves between explicitly chosen phases. No credit cell is added. -/)]
  WNear.Binary.SerdeStructObjPhaseReaders.seen_core

attribute [blueprint "frontier:prefix-reader-key-conditions"
  (title := /-- Phase key room, gas and closure contract -/)
  (statement := /-- Requires the actual pending-key state transition and precise trace charge. A concrete prefix constructor is checked below; the general interface stays Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.KeyConditions

attribute [blueprint "frontier:prefix-reader-value-conditions"
  (title := /-- Phase account room, gas and closure contract -/)
  (statement := /-- Consumes pending account_id, actual accepted value model and exact allocator endpoints. Its general instances remain Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.ValueConditions

attribute [blueprint "frontier:prefix-reader-ignore-conditions"
  (title := /-- Phase ignored-reader reachable contract -/)
  (statement := /-- Consumes the actual unknown key and preserves the retained state at the next-member phase. Its general instances remain Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.IgnoreConditions

attribute [blueprint "frontier:prefix-reader-close-conditions"
  (title := /-- Phase final-brace bounds contract -/)
  (statement := /-- Exact member-to-done bound transport. Concrete prefixes construct it; the general interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.ClosingConditions

attribute [blueprint "frontier:prefix-reader-key"
  (title := /-- Actual precise key reader records its field phase -/)
  (statement := /-- The actual f193 contract builds the phase-aware key hypothesis from named pure room/gas/endpoint conditions. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.keyHyp

attribute [blueprint "frontier:prefix-reader-value"
  (title := /-- Actual account reader uses pending account_id -/)
  (statement := /-- Actual f205/model/owned-string proof constructs the known-field phase call with its actual model and endpoint conditions. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.valueHyp

attribute [blueprint "frontier:prefix-reader-ignore"
  (title := /-- Full actual ignored reader moves its unknown-key phase -/)
  (statement := /-- The actual f201/full f81 constructor supplies reader room and capacity while named phase gas/state conditions remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.ignoreHyp_v86

attribute [blueprint "frontier:prefix-reader-closing"
  (title := /-- Owned member resources survive phase closing -/)
  (statement := /-- Physical member/core transport follows the named final-brace conditions without changing owned account bytes. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.member_closing

attribute [blueprint "frontier:prefix-reader-object"
  (title := /-- Actual loop composes phase-aware key and value readers -/)
  (statement := /-- Concrete actual key and account readers feed the checked field-phase loop; ignored and closing instances remain named. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.f228_obj_model_closing

attribute [blueprint "frontier:prefix-reader-full-object"
  (title := /-- Full actual ignored reader feeds the phase-aware loop -/)
  (statement := /-- All actual reader behavior and loop branches compose at unchanged costObj. Pure phase reader conditions remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.object_loop_v86_closing

attribute [blueprint "frontier:prefix-bound-forget"
  (title := /-- Actual prefix coordinates imply the physical ledger -/)
  (statement := /-- The exact successful prefix and retained capacity/free bound imply the unchanged coarse Ledger. This is a pure implication. -/)]
  WNear.Binary.SerdeObjectPrefix.Bound.forget

attribute [blueprint "frontier:prefix-bound-initial"
  (title := /-- Exact physical prefix starts at the initial cursor -/)
  (statement := /-- Initial empty scratch is available at the first-member phase and specified body cursor only. -/)]
  WNear.Binary.SerdeObjectPrefix.Bound.initial

attribute [blueprint "frontier:prefix-bound-segment"
  (title := /-- Physical prefix extends one actual segment -/)
  (statement := /-- Preserves exact retained capacity/free state and physical page bounds while extending an actual phase transition. -/)]
  WNear.Binary.SerdeObjectPrefix.Bound.segment

attribute [blueprint "frontier:prefix-bound-close"
  (title := /-- Actual prefix constructs final-brace conditions -/)
  (statement := /-- The recorded brace transition supplies member-to-done bounds with the same retained history. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.closing

attribute [blueprint "frontier:prefix-key-gas"
  (title := /-- Remaining prefix key gas allowance -/)
  (statement := /-- Only the actual precise key trace charge at a reachable member prefix must fit K. The selected exact charge instance is constructed below; the generic interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.KeyGasCharges

attribute [blueprint "frontier:prefix-value-gas"
  (title := /-- Remaining prefix account gas allowance -/)
  (statement := /-- Only the actual accepted account charge at its known-field prefix must fit K. Generic and selected-charge funding remain unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.ValueGasCharges

attribute [blueprint "frontier:prefix-ignore-gas"
  (title := /-- Remaining prefix ignored gas allowance -/)
  (statement := /-- Only the actual unknown-field reader charge at its prefix must fit K; the selected instance and whole-model budget remain unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.IgnoreGasCharges

attribute [blueprint "frontier:prefix-bound-key"
  (title := /-- Prefix room and state leave only key gas -/)
  (statement := /-- Actual prefix history supplies physical key room and exact post-key state, assuming only the selected K allowance. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.key_conditions

attribute [blueprint "frontier:prefix-bound-value"
  (title := /-- Prefix account room and state leave only value gas -/)
  (statement := /-- Uses actual accepted value models, the one account allocation and positive base free bound to construct all physical conditions. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.value_conditions

attribute [blueprint "frontier:prefix-bound-ignore"
  (title := /-- Prefix ignored room and state leave only ignored gas -/)
  (statement := /-- Actual unknown-key models, full heap trace and retained prefix supply room and state closure. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.ignore_conditions

attribute [blueprint "frontier:prefix-actual-loop"
  (title := /-- Actual object loop with exact prefix gas contracts -/)
  (statement := /-- All physical reader and closing conditions are constructed from the actual prefix. The original recurrence retains only selected key/value/ignore gas and physical setup premises. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.object_loop_prefix

attribute [blueprint "frontier:prefix-core-forget"
  (title := /-- Owned prefix core supplies original ledger resources -/)
  (statement := /-- Forgets only the pure prefix witness while retaining every owned parser and allocator resource. -/)]
  WNear.Binary.SerdeObjectPrefix.core_forget

attribute [blueprint "frontier:prefix-member-forget"
  (title := /-- Owned prefix member supplies original result ownership -/)
  (statement := /-- Keeps the saved account descriptor and bytes while passing exact physical resources to existing cleanup callers. -/)]
  WNear.Binary.SerdeObjectPrefix.member_forget

attribute [blueprint "frontier:prefix-member-initial"
  (title := /-- Raw empty scratch initializes owned prefix state -/)
  (statement := /-- Instantiates the first-member prefix at its exact cursor from actual stack-independent parser/scratch resources. -/)]
  WNear.Binary.SerdeObjectPrefix.member_initial

attribute [blueprint "frontier:prefix-wrapper"
  (title := /-- Actual prefix object reaches f78 and original ownership -/)
  (statement := /-- Actual f78 wrapper composes raw initialization, the phase-aware object and checked physical state handoff. Selected gas and setup remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f78_prefix_cost

attribute [blueprint "frontier:prefix-from-trait"
  (title := /-- Actual prefix costs survive f66 and scratch cleanup -/)
  (statement := /-- Checks EOF/trailing whitespace, result moves and retained scratch drop with the unchanged cost recurrence and owned account result. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f66_prefix

attribute [blueprint "frontier:prefix-from-slice"
  (title := /-- Actual prefix parser restores its slice caller -/)
  (statement := /-- The actual f65 slice entry composes the prefix f66 contract with unchanged frames, resources and observations. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f65_prefix

attribute [blueprint "frontier:prefix-from-slice-room"
  (title := /-- Prefix parser supplies balance execution room -/)
  (statement := /-- The original checked owned-account handoff supplies balance room and output free bound. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f65_prefix_room

attribute [blueprint "frontier:prefix-parser-call"
  (title := /-- Prefix parser supplies the shared call contract -/)
  (statement := /-- Packages actual prefix parsing for the shared balance pipeline. Reader gas and setup remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.prefix_parser_contract

attribute [blueprint "frontier:prefix-parser-family"
  (title := /-- Actual initial memory instantiates prefix setup -/)
  (statement := /-- Input allocation outcomes construct physical setup. Remaining reader premises are the three prefix gas allowances. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.prefix_parser_family

attribute [blueprint "frontier:prefix-deployed-provider"
  (title := /-- Actual-code provider retains prefix costs -/)
  (statement := /-- Persistent function cells instantiate the same prefix parser family, retaining output F=44. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.prefix_deployed_parser_provider

attribute [blueprint "frontier:prefix-provider-plan"
  (title := /-- Prefix provider couples to original model budget -/)
  (statement := /-- The same K functions and actual provider are coupled to unchanged ProviderModelBudget. Total funding is still Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.prefix_provider_plan

attribute [blueprint "frontier:prefix-receipt"
  (title := /-- Full receipt refinement from actual prefix parser -/)
  (statement := /-- Safety, sufficient-resource Matches/used gas and arbitrary-resource Matches-or-failure rollback/log-prefix compose with original observations. Prefix gas and model budget remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.prefix_refines_init

attribute [blueprint "frontier:prefix-progress"
  (title := /-- Every retained segment advances the cursor -/)
  (statement := /-- Actual key/value transitions bound retained history by consumed bytes. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.progress

attribute [blueprint "frontier:prefix-history-length"
  (title := /-- Retained prefix history fits consumed bytes -/)
  (statement := /-- The actual prefix has finitely many segments within the consumed input. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.history_length

attribute [blueprint "frontier:prefix-step-key"
  (title := /-- Functional trace matches actual key transition -/)
  (statement := /-- The actual key model determines the value phase, exact cursor, retained string segment and saved flag. -/)]
  WNear.Binary.SerdeObjectPrefix.step_key

attribute [blueprint "frontier:prefix-step-close"
  (title := /-- Functional trace matches final brace -/)
  (statement := /-- The actual brace determines the done phase and exact cursor without adding scratch history. -/)]
  WNear.Binary.SerdeObjectPrefix.step_close

attribute [blueprint "frontier:prefix-step-value"
  (title := /-- Functional trace matches account or ignored value -/)
  (statement := /-- Actual accepted account and ignored models determine the next phase, exact scratch segment and saved flag. -/)]
  WNear.Binary.SerdeObjectPrefix.step_value

attribute [blueprint "frontier:prefix-canonical"
  (title := /-- Every actual prefix lies on one functional trace -/)
  (statement := /-- Maps the actual history to its exact functional trace index. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.canonical_trace

attribute [blueprint "frontier:prefix-before-succ"
  (title := /-- Strict cursor order extends one trace step -/)
  (statement := /-- A previous trace state and strict cursor advance transport every earlier cursor bound. -/)]
  WNear.Binary.SerdeObjectPrefix.before_succ

attribute [blueprint "frontier:prefix-before-index"
  (title := /-- Earlier actual trace states have smaller cursors -/)
  (statement := /-- Strict cursor ordering excludes recurrent states at a reached cursor. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.before_index

attribute [blueprint "frontier:prefix-cursor-unique"
  (title := /-- Reached cursor uniquely determines phase and history -/)
  (statement := /-- The actual cursor determines its phase, retained scratch history and saved-account flag. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.unique_at_cursor

attribute [blueprint "frontier:prefix-key-no-later"
  (title := /-- Key body cannot recur at a later member prefix -/)
  (statement := /-- The next key phase lies at or beyond q, while any member quoting that q must precede q. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.key_no_later_start

attribute [blueprint "frontier:prefix-key-history"
  (title := /-- Key charge index uniquely determines retained history -/)
  (statement := /-- The actual key-body q determines exact scratch history and saved-account state, even when comparing different member cursors. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.key_history_unique

attribute [blueprint "frontier:prefix-key-selected-cost"
  (title := /-- Selected key charge equals every actual witness -/)
  (statement := /-- Classical selection of the unique actual prefix yields its exact preciseCost; this does not bound the sum by the whole model allowance. -/)]
  WNear.Binary.SerdeObjectPrefix.selectedKeyCost_of_witness

attribute [blueprint "frontier:prefix-selected-key-instance"
  (title := /-- Selected exact key charge instantiates prefix key gas -/)
  (statement := /-- For each saved state, the unique retained history supplies KeyGasCharges for selectedKeyCost. The generic interface remains Open and total model funding remains missing. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.selected_key_charges

attribute [blueprint "frontier:prefix-selected-key-receipt"
  (title := /-- Selected key charge reaches full receipt refinement -/)
  (statement := /-- Instantiates both actual key hypotheses at selectedKeyCost. Full receipt observations remain Conditional on value/ignored gas and the unchanged whole-model budget; no generic key gas witness is assumed. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.selected_key_refines_init

attribute [blueprint "frontier:field-length-755"
  (title := /-- Actual slice length mismatch costs 30 operations -/)
  (statement := /-- The actual f755 mismatch branch returns false without calling the byte comparator, preserving both owned slices. -/)]
  WNear.Binary.SerdeKeyTight.f755_length_ne

attribute [blueprint "frontier:field-length-754"
  (title := /-- Actual equality wrapper mismatch costs 50 operations -/)
  (statement := /-- The actual f754 wrapper composes the 30-operation slice mismatch result. -/)]
  WNear.Binary.SerdeKeyTight.f754_length_ne

attribute [blueprint "frontier:field-length-194"
  (title := /-- Actual field length mismatch costs 80 operations -/)
  (statement := /-- The actual f194 visitor returns ignore on every decoded length other than ten; it retains both key buffers. -/)]
  WNear.Binary.SerdeKeyTight.f194_length_ne

attribute [blueprint "frontier:field-visitor"
  (title := /-- Field visitor uses its actual length path -/)
  (statement := /-- The same original field result is proved at 80 operations for non-ten-byte keys and the preserved 342 allowance otherwise. -/)]
  WNear.Binary.SerdeKeyTight.f194_precise

attribute [blueprint "frontier:field-cost-compat"
  (title := /-- Field-specific charge preserves the legacy allowance -/)
  (statement := /-- Every fieldCost is at most the original pinned cost194; no previous public contract changes. -/)]
  WNear.Binary.SerdeKeyTight.fieldCost_le_legacy

attribute [blueprint "frontier:field-next-key"
  (title := /-- Actual next-key loop uses precise field classification -/)
  (statement := /-- The actual f193 key path composes its Spec646 resource premise and the field-specific visitor without changing state or field result. -/)]
  WNear.Binary.SerdeNextKeyTight.f193_key_precise_field

attribute [blueprint "frontier:field-key-model"
  (title := /-- Precise string and field reading compose at f193 -/)
  (statement := /-- Actual precise f646 reading supplies the next-key contract; physical reader room remains explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeKeyReuse.f193_key_model_precise_field

attribute [blueprint "frontier:bundled-key-conditions"
  (title := /-- Bundled key gas, room and state conditions -/)
  (statement := /-- Requires actual string plus field work to fit the unchanged classification base plus K, with exact physical room and endpoint closure. This generic interface stays Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.BundledKeyConditions

attribute [blueprint "frontier:bundled-key-hyp"
  (title := /-- Actual field-aware keys feed the unchanged loop hypothesis -/)
  (statement := /-- A single credit cell funds the actual key/field sum from the existing classification base plus selected K; no credit is added to member state. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.keyHyp_bundled

attribute [blueprint "frontier:bundled-key-funding"
  (title := /-- Classification base plus remainder funds actual key work -/)
  (statement := /-- Natural subtraction defines a nonnegative key remainder. The unchanged cost194 base plus it funds the actual reader and field charge. -/)]
  WNear.Binary.SerdeKeyReuse.bundledCost_funds_reader_and_field

attribute [blueprint "frontier:bundled-key-compat"
  (title := /-- Bundled remainder is no larger than the old key charge -/)
  (statement := /-- The actual field-specific allowance is bounded by the original cost194, so the remaining charge preserves the earlier preciseCost upper bound. -/)]
  WNear.Binary.SerdeKeyReuse.bundledCost_le_preciseCost

attribute [blueprint "frontier:bundled-key-gas"
  (title := /-- Remaining bundled prefix key allowance -/)
  (statement := /-- Only actual string plus field work versus the unchanged base plus K is required. The exact selected-cost instance is checked below; the general interface stays Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.BundledKeyGasCharges

attribute [blueprint "frontier:bundled-bound-key"
  (title := /-- Exact prefix constructs bundled key physical conditions -/)
  (statement := /-- Physical room and state transport are constructed from the actual prefix; only the named bundled gas allowance is assumed. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.bundled_key_conditions

attribute [blueprint "frontier:bundled-selected-key-cost"
  (title := /-- Selected bundled key charge agrees with every witness -/)
  (statement := /-- Unique actual key history fixes capacity, free state and decoded field, yielding the exact nonnegative bundled charge. -/)]
  WNear.Binary.SerdeObjectPrefix.selectedBundledKeyCost_of_witness

attribute [blueprint "frontier:bundled-selected-key-instance"
  (title := /-- Selected bundled key charge instantiates both saved states -/)
  (statement := /-- The exact selected remainder and unchanged classification base fund every actual prefix key call. The generic interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.selected_bundled_key_charges

attribute [blueprint "frontier:value-charge-no-later"
  (title := /-- Value charge index cannot recur at a later prefix -/)
  (statement := /-- An actual successful value reaches or passes its charge index, while any caller of that index must precede it. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.value_no_later_start

attribute [blueprint "frontier:value-charge-unique"
  (title := /-- Value-start index uniquely determines actual caller state -/)
  (statement := /-- Functional trace ordering fixes the pending key, cursor, retained history and saved flag for successful calls at the same value start. -/)]
  WNear.Binary.SerdeObjectPrefix.Prefix.value_start_unique

attribute [blueprint "frontier:value-witness-next"
  (title := /-- Actual account witness extends the prefix -/)
  (statement := /-- The accepted account model supplies its exact string segment and saved-account transition. -/)]
  WNear.Binary.SerdeObjectPrefix.ValueWitness.next

attribute [blueprint "frontier:value-witness-history"
  (title := /-- Account charge witnesses retain one exact history -/)
  (statement := /-- Actual account models and prefix ordering fix the scratch coordinates at a value charge index. -/)]
  WNear.Binary.SerdeObjectPrefix.ValueWitness.history_unique

attribute [blueprint "frontier:selected-value-cost"
  (title := /-- Selected account charge agrees with actual accepted calls -/)
  (statement := /-- The selected exact account allowance uses the unique retained history and actual account/rest result. This does not fund the whole model budget. -/)]
  WNear.Binary.SerdeObjectPrefix.selectedValueCost_of_witness

attribute [blueprint "frontier:selected-value-instance"
  (title := /-- Selected account charge instantiates prefix value gas -/)
  (statement := /-- Constructs the generic prefix value-gas interface for the selected exact function. The general interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.selected_value_charges

attribute [blueprint "frontier:ignore-witness-next"
  (title := /-- Actual ignored witness extends its unknown-key prefix -/)
  (statement := /-- The actual successful ignored trace supplies its frame segment and preserves the saved account. -/)]
  WNear.Binary.SerdeObjectPrefix.IgnoreWitness.next

attribute [blueprint "frontier:ignore-witness-history"
  (title := /-- Ignored charge witnesses retain one exact history -/)
  (statement := /-- Unknown-field trace models and prefix ordering fix the scratch coordinates at the ignored value start. -/)]
  WNear.Binary.SerdeObjectPrefix.IgnoreWitness.history_unique

attribute [blueprint "frontier:selected-ignore-cost"
  (title := /-- Selected ignored charge agrees with actual successful traces -/)
  (statement := /-- The unique prefix and deterministic ignored trace fix the exact frame/growth allowance. Total original-model funding remains missing. -/)]
  WNear.Binary.SerdeObjectPrefix.selectedIgnoreCost_of_witness

attribute [blueprint "frontier:selected-ignore-instance"
  (title := /-- Selected ignored charge instantiates both saved states -/)
  (statement := /-- Constructs the generic ignored-gas interface from actual retained history and trace, with no new behavioral or room premise. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.selected_ignore_charges

attribute [blueprint "frontier:fully-selected-receipt"
  (title := /-- Exact reader charges reach full receipt refinement -/)
  (statement := /-- All three generic reader-gas premises are instantiated. The full receipt result remains Conditional on the unchanged ProviderModelBudget and protocol/domain premises. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.fully_selected_refines_init

attribute [blueprint "frontier:string-work-tight"
  (title := /-- Successful string work has a 200-operation base -/)
  (statement := /-- The same raw successful costRun is bounded by 200+433 consumed-byte work plus 100 per initial accumulator byte and actual retained growth. Old 400-base statements are unchanged. -/)]
  WNear.Binary.ParseStrSuccess.costRun_growth_tight

attribute [blueprint "frontier:bundled-model-loop"
  (title := /-- Phase loop uses the actual bundled key reader -/)
  (statement := /-- Concrete field-aware keys and existing actual account/ignored interfaces feed the unchanged loop and costObj. Named pure conditions remain visible. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.f228_obj_model_closing_bundled

attribute [blueprint "frontier:bundled-full-loop"
  (title := /-- Full ignored reader composes with bundled keys -/)
  (statement := /-- Actual key/value/ignored behavior composes at the unchanged recurrence and one gas cell. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.object_loop_v86_closing_bundled

attribute [blueprint "frontier:bundled-actual-loop"
  (title := /-- Exact prefix builds the actual bundled object loop -/)
  (statement := /-- Prefix room, state and brace instances feed the full actual reader. Only selected gas and existing physical setup remain. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.object_loop_bundled

attribute [blueprint "frontier:bundled-wrapper"
  (title := /-- Actual bundled object reaches f78 ownership -/)
  (statement := /-- Raw scratch initialization and original resource handoff connect bundled parsing to the unchanged wrapper. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f78_bundled_cost

attribute [blueprint "frontier:bundled-from-trait"
  (title := /-- Bundled charges survive f66 and scratch cleanup -/)
  (statement := /-- Checks EOF/whitespace, result moves and actual retained scratch drop with unchanged output ownership. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f66_bundled

attribute [blueprint "frontier:bundled-from-slice"
  (title := /-- Bundled parser restores the slice caller -/)
  (statement := /-- The actual f65 entry composes bundled f66 and restores original frames, static/input resources and observations. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f65_bundled

attribute [blueprint "frontier:bundled-from-slice-room"
  (title := /-- Bundled parser supplies balance room -/)
  (statement := /-- The unchanged owned-account handoff supplies balance execution room and final free bound. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f65_bundled_room

attribute [blueprint "frontier:bundled-parser-call"
  (title := /-- Bundled parsing supplies the shared parser contract -/)
  (statement := /-- Packages the actual parser for the existing balance execution pipeline. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_parser_contract

attribute [blueprint "frontier:bundled-parser-family"
  (title := /-- Actual input memory instantiates bundled setup -/)
  (statement := /-- Permitted input allocation outcomes construct physical setup; reader allowances remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_parser_family

attribute [blueprint "frontier:bundled-deployed-provider"
  (title := /-- Actual code supplies the bundled provider -/)
  (statement := /-- Persistent function cells connect the actual parser family to the shared entry pipeline with output F=44. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_deployed_parser_provider

attribute [blueprint "frontier:bundled-provider-plan"
  (title := /-- Bundled provider retains the original whole-model budget -/)
  (statement := /-- The actual provider and same costObj recurrence are coupled to unchanged ProviderModelBudget. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_provider_plan

attribute [blueprint "frontier:bundled-receipt"
  (title := /-- Bundled actual parsing reaches full receipt refinement -/)
  (statement := /-- Retains safety, sufficient-resource Matches/used gas and arbitrary-resource Matches-or-failure rollback/log-prefix. Named gas/model-budget premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_refines_init

attribute [blueprint "frontier:fully-bundled-receipt"
  (title := /-- All exact reader charges reach the original-budget receipt -/)
  (statement := /-- Instantiates both bundled key states, account gas and both ignored states from their actual unique histories. Only unchanged whole-model funding and protocol/domain premises remain. Total gas is not claimed proved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.fully_bundled_refines_init

attribute [blueprint "frontier:key-work-tight"
  (title := /-- Same actual key charge has a 300-operation base -/)
  (statement := /-- The successful borrowed/copied preciseCost is bounded by 300+433 operations per consumed byte plus actual growth. This improves a bound without altering raw charge or existing statements. -/)]
  WNear.Binary.SerdeKeyReuse.preciseCost_growth_tight

attribute [blueprint "frontier:bundled-key-work"
  (title := /-- Bundled key/classification work keeps actual length cost -/)
  (statement := /-- The unchanged classification base plus net key charge fits 642+433n work for ten-byte keys or 380+433n otherwise, plus actual retained growth. -/)]
  WNear.Binary.SerdeKeyReuse.bundledCost_growth_tight

attribute [blueprint "frontier:ignored-member-work"
  (title := /-- Unknown-member regular work fits 486 operations per byte -/)
  (statement := /-- Key, actual field classification, object control and ignored regular work fit 486 times key/value consumed bytes plus three structural bytes. Actual scratch growth remains separate; global disjoint coverage and total model funding are not claimed. -/)]
  WNear.Binary.SerdeKeyReuse.ignored_member_regular_budget

attribute [blueprint "frontier:regular-byte-rate"
  (title := /-- Reviewed operation bound funds the byte rate -/)
  (statement := /-- 486 regular operations fit the unchanged 400-million-gas argument-byte coefficient under the explicit reviewed op bound 822756. This does not instantiate pinned protocol costs or fund actual growth. -/)]
  WNear.Binary.SerdeKeyReuse.regular_byte_rate

attribute [blueprint "frontier:trace-prefix-end"
  (title := /-- Complete actual trace extends the retained prefix -/)
  (statement := /-- Every successful member trace extends its actual pending prefix through the final brace. The precise remaining account-slot premise prevents duplicates. -/)]
  WNear.Binary.SerdeObjectMixedTrace.CallTrace.prefix_end

attribute [blueprint "frontier:member-input-partition"
  (title := /-- Actual member slices exactly partition consumed input -/)
  (statement := /-- Key body, value, both whitespace regions and punctuation are disjoint and cover exactly the successful member input. -/)]
  WNear.Binary.SerdeObjectMixedTrace.member_consumed_exact

attribute [blueprint "frontier:trace-value-end"
  (title := /-- Value endpoint agrees with its actual reader -/)
  (statement := /-- Successful account and ignored-segment witnesses agree with the pure endpoint used for input accounting. -/)]
  WNear.Binary.SerdeObjectMixedTrace.ValueSegment.end_eq

attribute [blueprint "frontier:trace-input-partition"
  (title := /-- Complete call trace has exact consumed-byte work -/)
  (statement := /-- The recursively followed actual key/value endpoints partition the full consumed input, including closing whitespace and brace. -/)]
  WNear.Binary.SerdeObjectMixedTrace.CallTrace.input_work

attribute [blueprint "frontier:loop-prefix-input"
  (title := /-- Actual initial loop supplies prefix and exact input partition -/)
  (statement := /-- Successful initial object-loop models construct complete retained prefixes, at most one account, exact byte coverage and the existing total page bound. -/)]
  WNear.Binary.SerdeObjectMixedTrace.loop_prefix_input

attribute [blueprint "frontier:copied-key-minimum"
  (title := /-- Copied keys consume an escape and final quote -/)
  (statement := /-- Every successful nonborrowed string consumes at least three source bytes, proved through the actual escape decoder and recursive string progress. -/)]
  WNear.Binary.SerdeKeyReuse.copied_consumed

attribute [blueprint "frontier:bundled-borrowed-work"
  (title := /-- Borrowed bundled work retains its 130-operation byte rate -/)
  (statement := /-- The same selected raw key allowance and actual classification cost fit their fast-path bound without growth. -/)]
  WNear.Binary.SerdeKeyReuse.bundledCost_borrowed_tight

attribute [blueprint "frontier:ignored-member-work-470"
  (title := /-- Unknown-member regular work fits 470 operations per byte -/)
  (statement := /-- Borrowed fast work and the minimum copied-key size sharpen the complete key/classification/loop/ignored regular bound. Actual retained growth stays separate; whole-method funding remains Open. -/)]
  WNear.Binary.SerdeKeyReuse.ignored_member_regular_budget_470

attribute [blueprint "frontier:account-growth-budget"
  (title := /-- Account scratch reserve has a concrete scalar bound -/)
  (statement := /-- The existing growthBudget is at most 400 billion gas under explicit F<=43, G<=21, decoded bytes<=64 and reviewed Wasm cost bounds. These premises are instantiated from actual prefixes below. -/)]
  WNear.Binary.SerdeObjectPrefix.account_growth_budget_le

attribute [blueprint "frontier:account-copy-budget"
  (title := /-- Account owned allocation has a concrete scalar bound -/)
  (statement := /-- The actual cost618 is at most 30 billion gas under explicit F<=85, decoded bytes<=64 and reviewed Wasm cost bounds. -/)]
  WNear.Binary.SerdeObjectPrefix.account_owned_copy_budget_le

attribute [blueprint "frontier:mixed-growth-append"
  (title := /-- Mixed growth count composes along retained capacities -/)
  (statement := /-- Appending histories preserves the exact evolving capacity; no per-member reset is introduced. -/)]
  WNear.Binary.SerdeObjectPrefix.mixed_growth_append

attribute [blueprint "frontier:prefix-account-resources"
  (title := /-- Actual pending account supplies allocator bounds -/)
  (statement := /-- Prefix models extended with the actual successful account string derive F<=43 and its segment G<=21 from the single mixed history. -/)]
  WNear.Binary.SerdeObjectPrefix.Bound.account_resources

attribute [blueprint "frontier:account-value-charge-bound"
  (title := /-- Actual account charge fits byte work plus one fixed reserve -/)
  (statement := /-- The unchanged borrowed/copied valueCost fits (166+470*consumed) operations plus 500 billion gas. Successful parse/UTF8, allocator and reviewed Wasm cost premises remain explicit. -/)]
  WNear.Binary.SerdeObjectPrefix.account_value_charge_le

attribute [blueprint "frontier:prefix-account-value-bound"
  (title := /-- Actual prefix instantiates account allocator budget -/)
  (statement := /-- Actual pending account and successful model supply decoded size and allocator bounds; only the explicit reviewed Wasm cost ceilings remain. -/)]
  WNear.Binary.SerdeObjectPrefix.Bound.account_value_charge

attribute [blueprint "frontier:selected-account-value-bound"
  (title := /-- Receipt-selected account charge has the concrete bound -/)
  (statement := /-- The exact selectedValueCost used by fully_bundled_refines_init agrees with any actual value witness and fits byte work plus 500 billion gas. Whole-method summation and protocol instantiation remain unresolved. -/)]
  WNear.Binary.SerdeObjectPrefix.selectedValueCost_account_bound

attribute [blueprint "frontier:provider-suffix-44"
  (title := /-- Actual suffix is funded after retained parser allocation -/)
  (statement := /-- Additive cost bounds support output free bound up to 44 using the same actual state read, absent lookup and return suffix. All previous 32-bound statements remain unchanged. -/)]
  WNear.Binary.BalanceOf297AbsentCall.suffix64_cost_le

attribute [blueprint "frontier:provider-body-linear"
  (title := /-- Parser linear allowance funds actual provider body -/)
  (statement := /-- Input setup and exact suffix composition yield fixed 1.2 trillion plus 397.5 million per byte and actual host charges. Parser allowance, reviewed protocol costs and F<=44 remain explicit. -/)]
  WNear.Binary.BalanceOf297AbsentCall.provider_body_linear_cost

attribute [blueprint "frontier:provider-budget-from-linear"
  (title := /-- Loading and host composition establish original model budget -/)
  (statement := /-- From parser<=1 trillion+(2215+470*inputbytes)*regularOpCost, CostsV86, deployed size bound and actual storage premises, checked loading/input/suffix/host/trie composition proves unchanged ProviderModelBudget. No model gas or observation is changed. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.provider_model_budget_of_parser_linear

attribute [blueprint "frontier:selected-parser-linear-budget"
  (title := /-- Exact remaining selected parser inequality -/)
  (statement := /-- For the same concrete bundled key/account/ignored charges used by the receipt, ledgerParserCost must fit 1 trillion+(2215+470*inputbytes)*regularOpCost. Complete trace summation, retained growth funding and account reserve composition remain unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.SelectedParserLinearBudget

attribute [blueprint "frontier:linear-bundled-receipt"
  (title := /-- Parser linear obligation reaches full original-budget receipt -/)
  (statement := /-- Actual representation and absent-account storage instantiate host premises. Checked linear funding constructs ProviderModelBudget and feeds the full selected-reader receipt. Exact parser inequality and unchanged protocol/domain premises remain unresolved. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.linear_bundled_refines_init

attribute [blueprint "frontier:trace-original-cost"
  (title := /-- Original object cost equals its complete actual trace -/)
  (statement := /-- The same costObj recurrence equals traceCost over actual successful key/value endpoints when trace length fits model fuel. -/)]
  WNear.Binary.SerdeObjectMixedTrace.CallTrace.objCost_eq

attribute [blueprint "frontier:trace-selected-value-bound"
  (title := /-- Both selected value branches fit one common growth sum -/)
  (statement := /-- Account and ignored witnesses agree with exact selected allowances. Account reserve is conditional on the actual account branch; all growth follows retained history. -/)]
  WNear.Binary.SerdeObjectMixedTrace.ValueSegment.selected_charge

attribute [blueprint "frontier:trace-selected-member-bound"
  (title := /-- Actual selected member charge fits disjoint bytes -/)
  (statement := /-- Combines the 470-operation bundled key bound, exact selected value allowance, actual whitespace and complete member input partition. Growth is retained and the account reserve is conditional on its branch. -/)]
  WNear.Binary.SerdeObjectMixedTrace.member_selected_charge

attribute [blueprint "frontier:trace-selected-total-bound"
  (title := /-- Full selected trace sums bytes, one account and retained growth -/)
  (statement := /-- The complete exact selected trace is bounded by disjoint consumed bytes, 500 billion gas per actual account (at most one) and one evolving mixed scratch history. -/)]
  WNear.Binary.SerdeObjectMixedTrace.CallTrace.selected_cost_le

attribute [blueprint "frontier:trace-fuel-account"
  (title := /-- Actual object model supplies fuel and account slots together -/)
  (statement := /-- The same ordered actual key path simultaneously fits model fuel and has at most one account including saved state. -/)]
  WNear.Binary.SerdeObjectMixedTrace.loop_keys_fuel_account

attribute [blueprint "frontier:loop-selected-cost-bound"
  (title := /-- Actual original object recurrence receives the trace bound -/)
  (statement := /-- Model fuel/account slots instantiate exact costObj equality and the complete selected-trace sum, without resetting scratch. -/)]
  WNear.Binary.SerdeObjectMixedTrace.loop_selected_cost_le

attribute [blueprint "frontier:selected-parser-cost-bound"
  (title := /-- Actual parser cost retains one mixed growth term -/)
  (statement := /-- Original ledgerParserCost fits (2215+470*inputbytes) operations plus one 500-billion account reserve and actual extraCost of a complete model history. -/)]
  WNear.Binary.SerdeObjectMixedTrace.selected_parser_cost_le

attribute [blueprint "frontier:mixed-small-growth-budget"
  (title := /-- Mixed growth is funded for actual histories up to 10000 bytes -/)
  (statement := /-- Under reviewed Wasm ceilings, peak<=10000 and global growth<=21 bound the same actual mixed extraCost by 500 billion gas. No full-4-MiB growth claim is made. -/)]
  WNear.Binary.SerdeObjectMixedTrace.mixed_growth_small_budget

attribute [blueprint "frontier:small-selected-parser-budget"
  (title := /-- Exact selected parser inequality is instantiated up to 10000 bytes -/)
  (statement := /-- All successful general-object inputs up to 10000 bytes fund the same exact SelectedParserLinearBudget. This scoped constructor does not discharge the generic full-domain interface. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectMixedTrace.selected_parser_linear_small

attribute [blueprint "frontier:small-general-provider-plan"
  (title := /-- Small general objects construct actual provider and original budget -/)
  (statement := /-- Instantiates all selected reader allowances and proves original whole-model funding, producing the existing actual-code parser plan under explicit storage/protocol/size premises. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.small_bundled_plan

attribute [blueprint "frontier:small-general-receipt"
  (title := /-- General objects up to 10000 bytes have full receipt refinement -/)
  (statement := /-- Instantiates the exact parser inequality and full initialized absent-account receipt. Escapes and complete nested ignored values are supported. Same safety/used gas/Matches/resource-failure/rollback/log-prefix claims under unchanged protocol/domain premises; no abstract gas premise remains. -/)]
  WNear.Binary.SerdeObjectPrefix.small_bundled_refines_init

attribute [blueprint "frontier:small-general-accepted"
  (title := /-- Small general-object case supplies accepted-call clauses -/)
  (statement := /-- Exact scoped input/state case instantiates full receipt refinement with the reviewed exported environment. Larger inputs and other states remain unresolved. -/)]
  WNear.Binary.BalanceOf297AbsentCall.small_general_object_case_accepted

attribute [blueprint "frontier:small-general-safety"
  (title := /-- Small general-object case supplies execution safety -/)
  (statement := /-- The same checked scoped case provides no execution issue under reviewed environment and representation. -/)]
  WNear.Binary.BalanceOf297AbsentCall.small_general_object_case_no_issue

attribute [blueprint "frontier:small-general-parser-cost"
  (title := /-- Small case fills the original actual-provider/cost interface -/)
  (statement := /-- Representation and scoped input/state models construct actual parser provider and original model budget in the exact conclusion shape used by the remaining absent-parser frontier. -/)
  (notReady := true)]
  WNear.Binary.BalanceOf297AbsentCall.small_general_parser_cost

attribute [blueprint "frontier:balance-absent-parser-complement"
  (title := /-- Exact remaining absent-parser inputs outside the checked small object case -/)
  (statement := /-- Same actual-code provider and unchanged whole-model budget must be supplied for accepted initialized/unregistered inputs outside all three completed array, escape-free object and <=10000-byte full general-object cases. The explicit negated SmallGeneralObjectAbsentCase premise is part of this audited statement. This obligation is Open; no full-domain funding is claimed. -/)
  (notReady := true)]
  WNear.ftBalanceOf_absent_parser_complement_obligation

attribute [blueprint "frontier:weighted-close-dispatch"
  (title := /-- Actual closing dispatch costs 30 operations -/)
  (statement := /-- The unchanged binary closing dispatch executes within 30 regular operations; no code, environmental premise or observation changes. -/)]
  WNear.Binary.SerdeIgnContainer.dispatch_close_tight

attribute [blueprint "frontier:weighted-close-block"
  (title := /-- Checked tighter closing block nonempty -/)
  (statement := /-- Composes the exact unchanged dispatch and physical pop path; tighter actual work preserves all returned resources and model endpoints. -/)]
  WNear.Binary.SerdeIgnClosing.block_nonempty_tight

attribute [blueprint "frontier:weighted-close-empty-block"
  (title := /-- Checked tighter closing block empty -/)
  (statement := /-- Composes the exact unchanged dispatch and physical pop path; tighter actual work preserves all returned resources and model endpoints. -/)]
  WNear.Binary.SerdeIgnClosing.block_empty_tight

attribute [blueprint "frontier:weighted-close-step"
  (title := /-- Checked tighter closing iteration nonempty -/)
  (statement := /-- Composes the exact unchanged dispatch and physical pop path; tighter actual work preserves all returned resources and model endpoints. -/)]
  WNear.Binary.SerdeIgnClosing.iteration_nonempty_tight

attribute [blueprint "frontier:weighted-close-last-step"
  (title := /-- Checked tighter closing iteration empty -/)
  (statement := /-- Composes the exact unchanged dispatch and physical pop path; tighter actual work preserves all returned resources and model endpoints. -/)]
  WNear.Binary.SerdeIgnClosing.iteration_empty_tight

attribute [blueprint "frontier:weighted-push-bound"
  (title := /-- Actual trace pushes fit consumed input -/)
  (statement := /-- Derives the number of future frame pushes from the real successful machine run. No abstract bound is assumed. -/)]
  WNear.Binary.SerdeIgnWeightedBudget.pushes_le_remaining

attribute [blueprint "frontier:weighted-reserve"
  (title := /-- Discounted reserve covers actual depth -/)
  (statement := /-- The weighted potential keeps the 470-byte rate, reserves 184 per depth and discounts 74 per actual frame push. Guards prove natural subtraction does not discard required work. -/)]
  WNear.Binary.SerdeIgnWeightedBudget.regular_reserve

attribute [blueprint "frontier:weighted-close-funded"
  (title := /-- Weighted reserve funds a real non-final close -/)
  (statement := /-- Exact pending trace pop preserves the push discount while releasing the checked depth reserve. -/)]
  WNear.Binary.SerdeIgnClosing.funded_nonempty_weighted

attribute [blueprint "frontier:weighted-close-last-funded"
  (title := /-- Weighted reserve funds the final close -/)
  (statement := /-- The empty pending trace returns the same resources with the tighter checked closing cost. -/)]
  WNear.Binary.SerdeIgnClosing.funded_empty_weighted

attribute [blueprint "frontier:weighted-opening"
  (title := /-- Actual opening consumes exactly its trace push -/)
  (statement := /-- Physical frame save, scratch growth and model determinism thread the 74-operation discount through the real opening block. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnOpening.entry_funded_weighted

attribute [blueprint "frontier:weighted-scalar-entry"
  (title := /-- Scalar entry preserves the weighted reserve -/)
  (statement := /-- Original 470-per-byte scalar allowance remains unchanged; exact remaining trace supplies the discount and depth guards. -/)]
  WNear.Binary.SerdeIgnValueEntry.pending_entry_weighted

attribute [blueprint "frontier:weighted-object-member"
  (title := /-- Actual object member retains the push discount -/)
  (statement := /-- Real key/string and colon transitions preserve the same future operations and retained scratch history. -/)]
  WNear.Binary.SerdeIgnMember.object_traced_weighted

attribute [blueprint "frontier:weighted-next-member"
  (title := /-- Both member branches preserve weighted funding -/)
  (statement := /-- Actual array and object member paths return the exact value model and discounted reserve. -/)]
  WNear.Binary.SerdeIgnMember.next_traced_weighted

attribute [blueprint "frontier:weighted-next-funded"
  (title := /-- Checked weighted next member -/)
  (statement := /-- The real member transition retains exactly one credit resource and the push count of its returned successful model. -/)]
  WNear.Binary.SerdeIgnMemberBudget.next_funded_weighted

attribute [blueprint "frontier:weighted-first-funded"
  (title := /-- Checked weighted first member -/)
  (statement := /-- The real member transition retains exactly one credit resource and the push count of its returned successful model. -/)]
  WNear.Binary.SerdeIgnMemberBudget.first_funded_weighted

attribute [blueprint "frontier:weighted-comma-funded"
  (title := /-- Checked weighted comma member -/)
  (statement := /-- The real member transition retains exactly one credit resource and the push count of its returned successful model. -/)]
  WNear.Binary.SerdeIgnMemberBudget.comma_funded_weighted

attribute [blueprint "frontier:weighted-loop-iteration"
  (title := /-- Actual container iteration uses the weighted frontier -/)
  (statement := /-- Composes checked close, first and comma transitions over the same binary iteration and exact model. -/)]
  WNear.Binary.SerdeIgnWeightedLoop.iteration

attribute [blueprint "frontier:weighted-loop"
  (title := /-- Actual container loop retains frame savings -/)
  (statement := /-- Checked loop invariant follows actual remaining input, depth and trace pushes without duplicating credits. -/)]
  WNear.Binary.SerdeIgnWeightedLoop.loop

attribute [blueprint "frontier:weighted-loop-phase"
  (title := /-- Weighted container phase reaches its callers -/)
  (statement := /-- The actual exit/error tail composes the weighted loop and preserves all rejected tails. -/)]
  WNear.Binary.SerdeIgnWeightedLoop.phase

attribute [blueprint "frontier:weighted-loop-suffix"
  (title := /-- Weighted phase composes into the actual member suffix -/)
  (statement := /-- Real phase and member paths return the precise pending value model and ownership. -/)]
  WNear.Binary.SerdeIgnWeightedLoop.suffix

attribute [blueprint "frontier:weighted-decoded-suffix"
  (title := /-- Weighted suffix is the deployed instruction slice -/)
  (statement := /-- The checked binary slice identity connects the weighted suffix proof to the deployed reader. -/)]
  WNear.Binary.SerdeIgnWeightedLoop.decoded_suffix

attribute [blueprint "frontier:weighted-opening-stack"
  (title := /-- Opening adapts to the actual reader stack -/)
  (statement := /-- Retains the exact scratch state and one credit resource while composing the weighted opening. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnValueEntry.opening_entry128_weighted

attribute [blueprint "frontier:weighted-value-continuation"
  (title := /-- Actual reader continuation carries discounted work -/)
  (statement := /-- Composes the weighted opening stack and decoded suffix with exact heap/model endpoints. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.continue_suffix

attribute [blueprint "frontier:weighted-value-iteration"
  (title := /-- Actual value iteration handles scalar and container paths -/)
  (statement := /-- Unchanged scalar blocks and weighted container continuation preserve the exact successful model. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.value_iteration

attribute [blueprint "frontier:weighted-value-loop"
  (title := /-- Actual value loop accumulates trace discounts -/)
  (statement := /-- The complete real loop retains the selected trace push discount and physical heap history. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.value_loop

attribute [blueprint "frontier:weighted-main"
  (title := /-- Actual main reader funds its full suffix -/)
  (statement := /-- Complete body including rejecting tails and success cleanup composes the discounted value loop. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.main

attribute [blueprint "frontier:weighted-reader-core"
  (title := /-- Full reader subtracts 74 operations per actual push -/)
  (statement := /-- Real prologue, main loop and success return prove (166+470*consumed-74*pushes)*op plus actual retained growth. All original resources and endpoints remain intact. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.f81_core

attribute [blueprint "frontier:weighted-reader"
  (title := /-- Actual f81 reader receives the exact push-count charge -/)
  (statement := /-- Trace validity instantiates the full binary reader with the same depth, room, ownership and endpoint claims. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.f81_traced

attribute [blueprint "frontier:weighted-colon-reader"
  (title := /-- Actual colon wrapper uses the discounted f81 contract -/)
  (statement := /-- The actual f201 path composes the existing colon reader and full weighted f81. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.f201_traced

attribute [blueprint "frontier:weighted-room-equality"
  (title := /-- Weighted and original physical room coincide -/)
  (statement := /-- Structural equality preserves the exact original scratch reserve requirements. This equality explicitly mentions the generic named room interface and is conservatively Conditional. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnWeightedExecution.room_eq

attribute [blueprint "frontier:weighted-heap-equality"
  (title := /-- Weighted and original heap traces coincide -/)
  (statement := /-- Structural equality preserves every actual heap transition and endpoint. -/)]
  WNear.Binary.SerdeIgnWeightedExecution.heapTrace_eq

attribute [blueprint "frontier:weighted-colon-v86"
  (title := /-- Full 4 MiB room bounds instantiate weighted f201 -/)
  (statement := /-- Original v86 page bounds and exact room/heap equality instantiate actual f201 under unchanged input/heap ceilings. -/)]
  WNear.Binary.SerdeIgnExecution.f201_weighted_v86

attribute [blueprint "frontier:weighted-ignore-conditions"
  (title := /-- Exact discounted phase ignore obligation -/)
  (statement := /-- For physically reachable phases, provide actual heap ceiling, weighted gas charge and exact returned phase closure. This generic contract remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.WeightedIgnoreConditions

attribute [blueprint "frontier:weighted-ignore-hyp"
  (title := /-- Weighted actual reader constructs the existing IgnoreHyp -/)
  (statement := /-- Composes real f201 with exact phase conditions into the original phase IgnoreHyp. Those named generic phase conditions remain unresolved until concretely instantiated. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.ignoreHyp_weighted_v86

attribute [blueprint "frontier:weighted-prefix-gas"
  (title := /-- Exact discounted reachable-prefix gas obligation -/)
  (statement := /-- The charge is (166+470*consumed-74*actual trace pushes)*op plus actual retained scratch growth. This generic interface remains Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.WeightedIgnoreGasCharges

attribute [blueprint "frontier:weighted-prefix-conditions"
  (title := /-- Actual prefix supplies weighted phase endpoints -/)
  (statement := /-- Original ledger heap ceiling, exact value segment and heap trace instantiate closure; the explicitly named weighted gas charge is still required. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.weighted_ignore_conditions

attribute [blueprint "frontier:weighted-selected-cost"
  (title := /-- Selected discounted cost agrees with every actual witness -/)
  (statement := /-- Canonical prefix history and deterministic returned trace select the exact lower charge with the actual retained allocator/capacity coordinates. -/)]
  WNear.Binary.SerdeObjectPrefix.selectedWeightedIgnoreCost_of_witness

attribute [blueprint "frontier:weighted-selected-instance"
  (title := /-- Concrete selected charge fills weighted gas interface -/)
  (statement := /-- Actual prefix witness instantiates the weighted ignore gas function for both saved-account states. This does not prove global model funding. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.Bound.selected_weighted_ignore_charges

attribute [blueprint "frontier:weighted-object-phase"
  (title := /-- Actual f228 composes weighted ignore and existing readers -/)
  (statement := /-- Uses the original generic phase theorem with unchanged bundled key/account readers and the actual weighted IgnoreHyp constructor. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjPhaseReaders.object_loop_v86_closing_bundled_weighted

attribute [blueprint "frontier:weighted-object-loop"
  (title := /-- Prefix object loop reaches weighted actual f228 -/)
  (statement := /-- Checked prefix/key/value/closing conditions compose the exact weighted object phase. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.object_loop_bundled_weighted

attribute [blueprint "frontier:weighted-object-wrapper"
  (title := /-- Actual object wrapper retains discounted charges -/)
  (statement := /-- Connects weighted actual object execution through the existing wrapper with exact return ownership. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f78_bundled_cost_weighted

attribute [blueprint "frontier:weighted-parser-trait"
  (title := /-- Actual weighted f66 bundled -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f66_bundled_weighted

attribute [blueprint "frontier:weighted-parser-slice"
  (title := /-- Actual weighted f65 bundled -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f65_bundled_weighted

attribute [blueprint "frontier:weighted-parser-room"
  (title := /-- Actual weighted f65 bundled room -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.f65_bundled_room_weighted

attribute [blueprint "frontier:weighted-parser-call"
  (title := /-- Actual weighted bundled parser contract -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_parser_contract_weighted

attribute [blueprint "frontier:weighted-parser-family"
  (title := /-- Actual weighted bundled parser family -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_parser_family_weighted

attribute [blueprint "frontier:weighted-deployed-provider"
  (title := /-- Actual weighted bundled deployed parser provider -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_deployed_parser_provider_weighted

attribute [blueprint "frontier:weighted-provider-plan"
  (title := /-- Actual weighted bundled provider plan -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_provider_plan_weighted

attribute [blueprint "frontier:weighted-receipt"
  (title := /-- Actual weighted bundled refines init -/)
  (statement := /-- Composes the checked discounted parser route with the original runtime interface and gas/receipt claims. Exact named gas, model, environment and domain premises remain explicit. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.bundled_refines_init_weighted

attribute [blueprint "frontier:weighted-selected-receipt"
  (title := /-- Concrete weighted readers reach full initialized receipt -/)
  (statement := /-- Instantiates bundled key/account/weighted ignore gas functions and the actual deployed provider. Full unchanged receipt still requires the exact original ProviderModelBudget. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.fully_weighted_bundled_refines_init

attribute [blueprint "frontier:weighted-parser-linear-budget"
  (title := /-- Remaining weighted whole-input parser inequality -/)
  (statement := /-- The actual weighted ledgerParserCost must fit 1 trillion+(2215+470*input bytes)*op over the full domain. Frame discounts must fund retained mixed growth; this precise obligation is Open. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.SelectedWeightedParserLinearBudget

attribute [blueprint "frontier:weighted-linear-receipt"
  (title := /-- Weighted linear funding composes into full receipt -/)
  (statement := /-- Original loading/input/storage/host/suffix composition builds ProviderModelBudget from the exact named weighted parser inequality, then checked concrete readers reach full initialized absent-account refinement. This remains Conditional. -/)
  (notReady := true)]
  WNear.Binary.SerdeObjectPrefix.weighted_linear_bundled_refines_init
